//! Single and multi-crate compilation orchestration.
//!
//! This module provides `CrateCompiler`, a struct that coordinates loading,
//! name resolution, and type inference across one or more crates.

pub mod format;

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use thiserror::Error;
use vfs::{PhysicalFS, VfsPath};

use crate::analysis::inference::unbound::{UnboundTypeVarError, UnboundVarChecker};
use crate::analysis::inference::{Environment, Inferrer, TypeError, TypedCrate};
use crate::analysis::name_table::NameTable;
use crate::analysis::resolver::{CrateId, GlobalName, GlobalType, ResolutionError, Resolver};
use crate::driver::{self, LoadError};
use crate::manifest::{Manifest, ManifestError};
use crate::sources::FileSources;

/// Errors that can occur during crate compilation.
#[derive(Debug, Error)]
pub enum CompileError {
    #[error("failed to load crate: {0}")]
    Load(#[from] LoadError),

    #[error("name resolution failed: {0}")]
    Resolution(#[from] ResolutionError),

    #[error("type inference failed: {0}")]
    Type(#[from] TypeError),

    #[error("unbound type variable: {0}")]
    UnboundTypeVar(#[from] UnboundTypeVarError),

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
    /// Accumulated source files for all crates (for error reporting)
    sources: FileSources,
    /// Accumulated type environment (type schemes of exported definitions)
    env: Environment,
}

impl Default for CrateCompiler {
    fn default() -> Self {
        Self::new()
    }
}

impl CrateCompiler {
    /// Create a new crate compiler.
    pub fn new() -> Self {
        let resolver = Resolver::new();
        Self {
            name_table: NameTable::with_global(resolver.initial_name_table()),
            resolver,
            inferrer: Inferrer::new(),
            next_crate_id: CrateId(0),
            compiled_crates: HashMap::new(),
            sources: FileSources::new(),
            env: Environment::new(),
        }
    }

    /// Get the accumulated source files (for error reporting).
    pub fn sources(&self) -> &FileSources {
        &self.sources
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

    /// Compile a project from its Tygr.toml manifest.
    ///
    /// Automatically compiles dependencies first (topologically sorted) and builds extern_prelude.
    /// Returns the TypedCrate for the root project and all its dependencies in topological order.
    pub fn compile_project(
        &mut self,
        manifest_path: &Path,
    ) -> Result<Vec<TypedCrate>, CompileError> {
        use petgraph::algo::toposort;
        use petgraph::graph::{DiGraph, NodeIndex};

        // Canonicalize manifest path
        let manifest_path = manifest_path
            .canonicalize()
            .map_err(|e| CompileError::Path(format!("cannot canonicalize manifest: {}", e)))?;

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
            }
        }

        // Second pass: add edges (dependency -> dependent, for toposort order)
        for (path, &idx) in &path_to_idx {
            let manifest = &idx_to_manifest[&idx];
            let manifest_dir = path.parent().unwrap();

            for (alias, dep_rel_path) in &manifest.dependencies {
                let dep_manifest_path = manifest_dir
                    .join(dep_rel_path)
                    .join("Tygr.toml")
                    .canonicalize()
                    .unwrap();

                // Check if dep is in our current graph
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
            }
        }

        // Topological sort
        let sorted = toposort(&graph, None).map_err(|_| CompileError::DependencyCycle)?;

        // Compile in topological order, building extern_prelude maps
        let mut all_typed_crates = Vec::new();

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
            let typed = self.compile_crate(&crate_root, extern_prelude)?;
            all_typed_crates.push(typed);
        }

        Ok(all_typed_crates)
    }

    /// Compile a crate.
    fn compile_crate(
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

        let krate = driver::load_module(&vfs_root, &vfs_file, &mut self.sources)?;
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

        let (typed_crate, final_env) = self.inferrer.infer_crate(prepared, self.env.clone())?;

        // Check for unbound type variables
        let unbound_errors = UnboundVarChecker::new().check_crate(&typed_crate);
        if let Some(error) = unbound_errors.into_iter().next() {
            return Err(CompileError::UnboundTypeVar(error));
        }

        self.env = final_env;

        Ok(typed_crate)
    }

    /// Compile a single-file program from source code directly.
    ///
    /// This treats the source as a degenerate crate with no submodules.
    pub fn compile_source(
        &mut self,
        source: String,
        file_name: &str,
        extern_prelude: HashMap<String, CrateId>,
    ) -> Result<TypedCrate, CompileError> {
        let krate = driver::load_from_source(source, file_name, &mut self.sources)?;
        let crate_id = self.alloc_crate_id();

        let resolve_ctx = self
            .resolver
            .resolve_crate(crate_id, krate, extern_prelude)?;

        let prepared = self.resolver.prepare_crate(crate_id);

        let local_table = resolve_ctx.into_local_name_table();
        self.name_table.add(Some(crate_id), local_table);

        let (typed_crate, final_env) = self.inferrer.infer_crate(prepared, self.env.clone())?;

        // Check for unbound type variables
        let unbound_errors = UnboundVarChecker::new().check_crate(&typed_crate);
        if let Some(error) = unbound_errors.into_iter().next() {
            return Err(CompileError::UnboundTypeVar(error));
        }

        self.env = final_env;

        Ok(typed_crate)
    }

    /// Compile a TypedCrate to a specific IR stage.
    pub fn compile_to<S: crate::ir::stage::IrStage>(&self, typed: TypedCrate) -> S::Output {
        S::convert(typed, self.next_name())
    }

    /// Compile all crates to a specific whole-program IR stage.
    pub fn compile_program_to<S: crate::ir::stage::ProgramStage>(
        &self,
        crates: Vec<TypedCrate>,
        main_name: GlobalName,
    ) -> S::Output {
        use crate::ir::stage::AnfStage;
        let anf_crates: Vec<_> = crates
            .into_iter()
            .map(|c| self.compile_to::<AnfStage>(c))
            .collect();
        S::convert(anf_crates, main_name)
    }
}
