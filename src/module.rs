//! Single and multi-crate compilation orchestration.
//!
//! This module provides `CrateCompiler`, a struct that coordinates loading,
//! name resolution, and type inference across one or more crates.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use thiserror::Error;
use vfs::{PhysicalFS, VfsPath};

use crate::analysis::inference::{Inferrer, TypeError, TypedCrate};
use crate::analysis::name_table::NameTable;
use crate::analysis::resolver::{CrateId, GlobalName, GlobalType, ResolutionError, Resolver};
use crate::driver::{self, LoadError};
use crate::ir::closure;
use crate::manifest::{Manifest, ManifestError};

/// Errors that can occur during crate compilation.
#[derive(Debug, Error)]
pub enum CompileError {
    #[error("failed to load crate: {0}")]
    Load(#[from] LoadError),

    #[error("name resolution failed: {0}")]
    Resolution(#[from] ResolutionError),

    #[error("type inference failed: {0}")]
    Type(#[from] TypeError),

    #[error("path error: {0}")]
    Path(String),

    #[error("manifest error: {0}")]
    Manifest(#[from] ManifestError),

    #[error("dependency cycle detected")]
    DependencyCycle,
}

/// Compiler for tygr crates.
///
/// Holds shared state (resolver, inferrer, name table) that accumulates
/// across multiple crate compilations.
pub struct CrateCompiler {
    resolver: Resolver,
    inferrer: Inferrer,
    name_table: NameTable,
    next_crate_id: CrateId,
    /// Map from canonical manifest path to CrateId (avoid recompiling)
    compiled_crates: HashMap<PathBuf, CrateId>,
}

impl Default for CrateCompiler {
    fn default() -> Self {
        Self::new()
    }
}

impl CrateCompiler {
    /// Create a new crate compiler.
    pub fn new() -> Self {
        Self {
            resolver: Resolver::new(),
            inferrer: Inferrer::new(),
            name_table: NameTable::new(),
            next_crate_id: CrateId(0),
            compiled_crates: HashMap::new(),
        }
    }

    /// Get the accumulated name table (for error reporting).
    pub fn name_table(&self) -> &NameTable {
        &self.name_table
    }

    /// Get next available GlobalName ID (for IR passes).
    pub fn next_name(&self) -> GlobalName {
        GlobalName {
            krate: Some(self.next_crate_id),
            name: self.resolver.next_name_id(),
        }
    }

    /// Get next available GlobalType ID (for IR passes).
    pub fn next_type_name(&self) -> GlobalType {
        GlobalType {
            krate: Some(self.next_crate_id),
            name: self.resolver.next_type_name_id(),
        }
    }

    /// Allocate and return the next crate ID.
    fn alloc_crate_id(&mut self) -> CrateId {
        let id = self.next_crate_id;
        self.next_crate_id = CrateId(self.next_crate_id.0 + 1);
        id
    }

    /// Compile a single crate from a root file path.
    ///
    /// The path should be the crate root (e.g., lib.tygr or main.tygr).
    /// This function handles the full pipeline: loading, resolution, and type inference.
    /// State is accumulated in the compiler for use across multiple crates.
    pub fn compile_crate(&mut self, path: &Path) -> Result<TypedCrate, CompileError> {
        // Convert path to VFS path
        let root_path = path
            .canonicalize()
            .map_err(|e| CompileError::Path(format!("cannot canonicalize path: {}", e)))?;

        let root_dir = root_path
            .parent()
            .ok_or_else(|| CompileError::Path("path has no parent directory".to_string()))?;

        let fs = PhysicalFS::new(root_dir);
        let vfs_root = VfsPath::new(fs);

        let file_name = root_path
            .file_name()
            .and_then(|n| n.to_str())
            .ok_or_else(|| CompileError::Path("invalid file name".to_string()))?;

        let vfs_file = vfs_root
            .join(file_name)
            .map_err(|e| CompileError::Path(format!("VFS error: {}", e)))?;

        let krate = driver::load_module(&vfs_root, &vfs_file)?;
        let crate_id = self.alloc_crate_id();

        let extern_prelude = HashMap::new(); // Empty for now, will be populated for multi-crate
        let resolve_ctx = self
            .resolver
            .resolve_crate(crate_id, krate, extern_prelude)?;

        let prepared = self.resolver.prepare_crate(crate_id);

        let local_table = resolve_ctx.into_local_name_table();
        self.name_table.add(Some(crate_id), local_table);

        let env = HashMap::new();
        let (typed_crate, _final_env) = self.inferrer.infer_crate(prepared, env)?;

        Ok(typed_crate)
    }

    /// Compile a crate to closure IR.
    ///
    /// This runs the full pipeline from source to closure-converted IR,
    /// ready for the constructor pass.
    pub fn compile_to_closure_ir(&mut self, path: &Path) -> Result<closure::Program, CompileError> {
        let typed = self.compile_crate(path)?;

        let mut converter = closure::Converter::new(self.next_name(), self.next_type_name());

        for var in typed.variants {
            converter.register_variant(var);
        }

        let program = converter.convert_program(typed.groups);

        Ok(program)
    }

    /// Compile a crate to constructor IR.
    ///
    /// This runs the full pipeline including the constructor pass.
    pub fn compile_to_constructor_ir(
        &mut self,
        path: &Path,
    ) -> Result<crate::ir::constructor::Program, CompileError> {
        let closure_program = self.compile_to_closure_ir(path)?;

        let mut converter = crate::ir::constructor::Converter::new(closure_program.next_name);
        let constructor_program = converter.convert_program(closure_program);

        Ok(constructor_program)
    }

    /// Compile a project from its Tygr.toml manifest.
    ///
    /// Automatically compiles dependencies first (topologically sorted) and builds extern_prelude.
    /// Returns the TypedCrate for the root project.
    pub fn compile_project(&mut self, manifest_path: &Path) -> Result<TypedCrate, CompileError> {
        use petgraph::algo::toposort;
        use petgraph::graph::{DiGraph, NodeIndex};

        // Canonicalize manifest path
        let manifest_path = manifest_path
            .canonicalize()
            .map_err(|e| CompileError::Path(format!("cannot canonicalize manifest: {}", e)))?;

        // If already compiled, we can't return the TypedCrate again (it was consumed),
        // but we shouldn't hit this case for the root project.
        if self.compiled_crates.contains_key(&manifest_path) {
            return Err(CompileError::Path("project already compiled".to_string()));
        }

        // Build dependency graph: nodes are canonical manifest paths
        let mut graph: DiGraph<PathBuf, String> = DiGraph::new();
        let mut path_to_idx: HashMap<PathBuf, NodeIndex> = HashMap::new();
        let mut idx_to_manifest: HashMap<NodeIndex, Manifest> = HashMap::new();

        // Stack for DFS traversal of manifests
        let mut stack = vec![manifest_path.clone()];

        while let Some(current_path) = stack.pop() {
            if path_to_idx.contains_key(&current_path) {
                continue;
            }

            let manifest = Manifest::load(&current_path)?;
            let idx = graph.add_node(current_path.clone());
            path_to_idx.insert(current_path.clone(), idx);
            idx_to_manifest.insert(idx, manifest.clone());

            // Get the directory containing this manifest
            let manifest_dir = current_path.parent().ok_or_else(|| {
                CompileError::Path("manifest has no parent directory".to_string())
            })?;

            // Process dependencies
            for (alias, dep_rel_path) in &manifest.dependencies {
                // Resolve dependency path relative to manifest directory
                let dep_manifest_path = manifest_dir
                    .join(dep_rel_path)
                    .join("Tygr.toml")
                    .canonicalize()
                    .map_err(|e| {
                        CompileError::Path(format!(
                            "cannot resolve dependency '{}' at '{}': {}",
                            alias, dep_rel_path, e
                        ))
                    })?;

                // Check if already compiled
                if !self.compiled_crates.contains_key(&dep_manifest_path) {
                    stack.push(dep_manifest_path.clone());
                }

                // We'll add edges after all nodes are discovered
            }
        }

        // Second pass: add edges (dependency -> dependent, for toposort order)
        // toposort returns nodes in order such that for every edge (u, v), u comes before v
        // We want dependencies compiled first, so edge direction: dependency -> dependent
        for (path, &idx) in &path_to_idx {
            let manifest = &idx_to_manifest[&idx];
            let manifest_dir = path.parent().unwrap();

            for (alias, dep_rel_path) in &manifest.dependencies {
                let dep_manifest_path = manifest_dir
                    .join(dep_rel_path)
                    .join("Tygr.toml")
                    .canonicalize()
                    .unwrap();

                // Check if dep is already compiled
                if let Some(&dep_idx) = path_to_idx.get(&dep_manifest_path) {
                    // Validate: dependency must be a library
                    let dep_manifest = &idx_to_manifest[&dep_idx];
                    if !dep_manifest.is_library() {
                        return Err(CompileError::Manifest(ManifestError::BinaryDependency(
                            alias.clone(),
                        )));
                    }
                    // Edge from dependency to dependent (dep should be compiled first)
                    graph.add_edge(dep_idx, idx, alias.clone());
                }
                // If dep is already compiled, no need to add to graph
            }
        }

        // Topological sort
        let sorted = toposort(&graph, None).map_err(|_| CompileError::DependencyCycle)?;

        // Compile in topological order, building extern_prelude maps
        let mut typed_crates: HashMap<PathBuf, TypedCrate> = HashMap::new();

        for idx in sorted {
            let path = &graph[idx];

            // Skip if already compiled (from previous compile_project calls)
            if self.compiled_crates.contains_key(path) {
                continue;
            }

            let manifest = &idx_to_manifest[&idx];
            let manifest_dir = path.parent().unwrap();
            let crate_root = manifest.crate_root(manifest_dir);

            // Build extern_prelude for this crate
            let mut extern_prelude = HashMap::new();
            for (alias, dep_rel_path) in &manifest.dependencies {
                let dep_manifest_path = manifest_dir
                    .join(dep_rel_path)
                    .join("Tygr.toml")
                    .canonicalize()
                    .unwrap();

                // Look up the CrateId - either from this compilation or previous
                let crate_id = self
                    .compiled_crates
                    .get(&dep_manifest_path)
                    .copied()
                    .expect("dependency should be compiled before dependent");
                extern_prelude.insert(alias.clone(), crate_id);
            }

            // Compile this crate
            let typed = self.compile_crate_with_prelude(&crate_root, extern_prelude)?;

            // Record the canonical path -> CrateId mapping
            // Note: typed.crate_id gives us the ID we just allocated
            // We need to get it from the resolver or track it differently
            // Actually, compile_crate_with_prelude already allocates the ID internally
            // Let's store it before the last typed_crate is consumed

            typed_crates.insert(path.clone(), typed);
        }

        // Return the root project's TypedCrate
        typed_crates
            .remove(&manifest_path)
            .ok_or_else(|| CompileError::Path("root project not compiled".to_string()))
    }

    /// Compile a crate with an explicit extern_prelude.
    ///
    /// Similar to compile_crate but allows specifying dependencies.
    fn compile_crate_with_prelude(
        &mut self,
        path: &Path,
        extern_prelude: HashMap<String, CrateId>,
    ) -> Result<TypedCrate, CompileError> {
        // Convert path to VFS path
        let root_path = path
            .canonicalize()
            .map_err(|e| CompileError::Path(format!("cannot canonicalize path: {}", e)))?;

        let root_dir = root_path
            .parent()
            .ok_or_else(|| CompileError::Path("path has no parent directory".to_string()))?;

        let fs = PhysicalFS::new(root_dir);
        let vfs_root = VfsPath::new(fs);

        let file_name = root_path
            .file_name()
            .and_then(|n| n.to_str())
            .ok_or_else(|| CompileError::Path("invalid file name".to_string()))?;

        let vfs_file = vfs_root
            .join(file_name)
            .map_err(|e| CompileError::Path(format!("VFS error: {}", e)))?;

        let krate = driver::load_module(&vfs_root, &vfs_file)?;
        let crate_id = self.alloc_crate_id();

        // Store the mapping from crate root path to crate id
        // We need the manifest path, not the crate root. Go up from src/
        if let Some(src_dir) = root_path.parent() {
            if let Some(project_dir) = src_dir.parent() {
                let manifest_path = project_dir.join("Tygr.toml");
                if manifest_path.exists() {
                    if let Ok(canonical) = manifest_path.canonicalize() {
                        self.compiled_crates.insert(canonical, crate_id);
                    }
                }
            }
        }

        let resolve_ctx = self
            .resolver
            .resolve_crate(crate_id, krate, extern_prelude)?;

        let prepared = self.resolver.prepare_crate(crate_id);

        let local_table = resolve_ctx.into_local_name_table();
        self.name_table.add(Some(crate_id), local_table);

        let env = HashMap::new();
        let (typed_crate, _final_env) = self.inferrer.infer_crate(prepared, env)?;

        Ok(typed_crate)
    }
}
