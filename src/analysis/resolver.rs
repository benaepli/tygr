mod ast;
pub use ast::*;

use crate::analysis::dependencies::{reorder_definitions, reorder_type_definitions};
use crate::analysis::name_table::LocalNameTable;
use crate::analysis::prepared::{PreparedCrate, PreparedTypeDefinition};
use crate::builtin::{BUILTIN_TYPES, BUILTINS, BuiltinFn, TYPE_BASE};
use crate::driver::{Crate, ModuleId};
use crate::parser::{
    Annotation, AnnotationKind, Declaration, Definition, Expr, ExprKind, Generic, ModuleDecl, Path,
    Pattern, PatternKind, SourceId, Span, Statement, StatementKind, TypeAlias, UseDecl, Variant,
};
use bimap::BiMap;
use std::collections::{HashMap, HashSet};
use thiserror::Error;

#[derive(Error, Debug, PartialEq, Clone)]
pub enum ResolutionError {
    #[error("variable `{0}` not found")]
    VariableNotFound(Path, Span),
    #[error("variable `{0}` is bound more than once in the same pattern")]
    DuplicateBinding(String, Span),
    #[error("type alias `{0}` is already defined")]
    DuplicateTypeAlias(String, Span),
    #[error("type alias `{0}` expects {1} type argument(s), but {2} were provided")]
    WrongNumberOfTypeArguments(String, usize, usize, Span),
    #[error("field `{0}` appears more than once in record")]
    DuplicateRecordField(String, Span),
    #[error("variant type `{0}` is already defined")]
    DuplicateVariant(String, Span),
    #[error("constructor `{0}` is already defined")]
    DuplicateConstructor(String, Span),
    #[error("constructor `{0}` not found")]
    ConstructorNotFound(String, Span),
    #[error("`super` goes past the crate root")]
    SuperPastRoot(Span),
    #[error("module `{0}` not found")]
    ModuleNotFound(String, Span),
    #[error("item `{0}` is private")]
    PrivateItemAccess(String, Span),
}

type Scope = HashMap<String, GlobalName>;
type TypeScope = HashMap<String, GlobalType>;

#[derive(Debug)]
pub struct ResolveContext {
    crate_id: Option<CrateId>,
    module_id: Option<ModuleId>,
    next_id: Name,
    next_type: TypeName,

    name_origins: HashMap<Name, String>,
    type_name_origins: HashMap<TypeName, String>,
}

impl Default for ResolveContext {
    fn default() -> Self {
        Self::new()
    }
}

impl ResolveContext {
    fn new() -> Self {
        Self {
            crate_id: None,
            module_id: None,
            next_id: Name(0),
            next_type: TYPE_BASE,
            name_origins: HashMap::new(),
            type_name_origins: HashMap::new(),
        }
    }

    fn new_name(&mut self, original_name: String) -> Name {
        let id = self.next_id;
        self.next_id = Name(self.next_id.0 + 1);
        self.name_origins.insert(id, original_name);
        id
    }

    fn new_id(&mut self, original_name: String) -> TypeName {
        let id = self.next_type;
        self.next_type = TypeName(self.next_type.0 + 1);
        self.type_name_origins.insert(id, original_name);
        id
    }

    pub fn into_local_name_table(self) -> LocalNameTable {
        LocalNameTable::with_maps(self.name_origins, self.type_name_origins)
    }
}

#[derive(Debug, Default)]
struct ScopeContext {
    scopes: Vec<Scope>,
    type_scopes: Vec<TypeScope>,
    builtins: HashMap<Name, BuiltinFn>,
    global_aliases: HashMap<String, TypeName>,
    global_variants: HashMap<String, TypeName>,
    global_constructors: HashMap<String, (TypeName, Name)>,

    world: World,
}

impl ScopeContext {
    fn new() -> Self {
        Self {
            scopes: vec![],
            type_scopes: vec![],
            builtins: HashMap::new(),
            global_aliases: HashMap::new(),
            global_variants: HashMap::new(),
            global_constructors: HashMap::new(),
            world: World::default(),
        }
    }
}

pub struct Resolver {
    global_ctx: ResolveContext,
    scope_ctx: ScopeContext,
}

impl Default for Resolver {
    fn default() -> Self {
        Self::new()
    }
}

impl Resolver {
    pub fn new() -> Self {
        let mut ctx = ResolveContext::new();
        let mut scope_ctx = ScopeContext::new();

        // Store builtin type names
        for (type_name_str, type_name_id) in BUILTIN_TYPES.entries() {
            ctx.type_name_origins
                .insert(*type_name_id, type_name_str.to_string());
        }

        let mut global = Scope::new();
        for (keyword, builtin) in BUILTINS.entries() {
            let name_id = ctx.new_name(keyword.to_string());
            global.insert(
                keyword.to_string(),
                GlobalName {
                    krate: None,
                    name: name_id,
                },
            );
            scope_ctx.builtins.insert(name_id, builtin.clone());
        }
        scope_ctx.scopes.push(global);

        Self {
            global_ctx: ctx,
            scope_ctx,
        }
    }

    /// Register a custom function name in the global scope.
    /// Returns the assigned Name ID, or an error if the name already exists.
    pub fn register_global_custom(&mut self, name: &str) -> Result<Name, ResolutionError> {
        if self.scope_ctx.scopes[0].contains_key(name) {
            return Err(ResolutionError::DuplicateBinding(
                name.to_string(),
                Span {
                    context: SourceId::SYNTHETIC,
                    start: 0,
                    end: 0,
                },
            ));
        }
        let id = self.global_ctx.new_name(name.to_string());
        self.scope_ctx.scopes[0].insert(
            name.to_string(),
            GlobalName {
                krate: None,
                name: id,
            },
        );
        Ok(id)
    }

    fn resolve_annotation(
        ctx: &ResolveContext,
        scope_ctx: &mut ScopeContext,
        annot: Annotation,
    ) -> Result<ResolvedAnnotation, ResolutionError> {
        let span = annot.span;
        match annot.kind {
            AnnotationKind::Var(path) => {
                if let Some(name) = path.simple() {
                    // Check type scopes first (generic parameters)
                    for scope in scope_ctx.type_scopes.iter().rev() {
                        if let Some(id) = scope.get(name) {
                            return Ok(ResolvedAnnotation::new(
                                ResolvedAnnotationKind::Var(*id),
                                span,
                            ));
                        }
                    }

                    // Check builtins
                    if let Some(id) = BUILTIN_TYPES.get(name) {
                        return Ok(ResolvedAnnotation::new(
                            ResolvedAnnotationKind::Var(GlobalType {
                                krate: None,
                                name: *id,
                            }),
                            span,
                        ));
                    } else if let Some(id) = scope_ctx.global_aliases.get(name) {
                        return Ok(ResolvedAnnotation::new(
                            ResolvedAnnotationKind::Alias(GlobalType {
                                krate: None,
                                name: *id,
                            }),
                            span,
                        ));
                    } else if let Some(id) = scope_ctx.global_variants.get(name) {
                        return Ok(ResolvedAnnotation::new(
                            ResolvedAnnotationKind::Var(GlobalType {
                                krate: None,
                                name: *id,
                            }),
                            span,
                        ));
                    }
                }

                // Check crates via world
                if let (Some(c_id), Some(m_id)) = (ctx.crate_id, ctx.module_id) {
                    match scope_ctx
                        .world
                        .resolve(c_id, m_id, path.clone(), Namespace::Type)
                    {
                        Ok(Resolution::Variant(gt)) => {
                            return Ok(ResolvedAnnotation::new(
                                ResolvedAnnotationKind::Var(gt),
                                span,
                            ));
                        }
                        Ok(Resolution::TypeAlias(gt)) => {
                            return Ok(ResolvedAnnotation::new(
                                ResolvedAnnotationKind::Alias(gt),
                                span,
                            ));
                        }
                        Err(e) => return Err(e),
                        _ => {}
                    }
                }

                Err(ResolutionError::VariableNotFound(path, span))
            }

            AnnotationKind::App(lhs, rhs) => {
                let r_lhs = Self::resolve_annotation(ctx, scope_ctx, *lhs)?;
                let r_rhs = Self::resolve_annotation(ctx, scope_ctx, *rhs)?;
                Ok(ResolvedAnnotation::new(
                    ResolvedAnnotationKind::App(Box::new(r_lhs), Box::new(r_rhs)),
                    span,
                ))
            }

            AnnotationKind::Pair(lhs, rhs) => {
                let r_lhs = Self::resolve_annotation(ctx, scope_ctx, *lhs)?;
                let r_rhs = Self::resolve_annotation(ctx, scope_ctx, *rhs)?;
                Ok(ResolvedAnnotation::new(
                    ResolvedAnnotationKind::Pair(Box::new(r_lhs), Box::new(r_rhs)),
                    span,
                ))
            }

            AnnotationKind::Lambda(param, ret) => {
                let r_param = Self::resolve_annotation(ctx, scope_ctx, *param)?;
                let r_ret = Self::resolve_annotation(ctx, scope_ctx, *ret)?;
                Ok(ResolvedAnnotation::new(
                    ResolvedAnnotationKind::Lambda(Box::new(r_param), Box::new(r_ret)),
                    span,
                ))
            }

            AnnotationKind::Record(m) => {
                let mut resolved = HashMap::new();
                for (k, v) in m.into_iter() {
                    if resolved.contains_key(&k) {
                        return Err(ResolutionError::DuplicateRecordField(k, span));
                    }
                    resolved.insert(k, Self::resolve_annotation(ctx, scope_ctx, v)?);
                }
                Ok(ResolvedAnnotation::new(
                    ResolvedAnnotationKind::Record(resolved),
                    span,
                ))
            }
        }
    }

    pub fn declare_global_type_alias(
        &mut self,
        alias: &TypeAlias,
    ) -> Result<TypeName, ResolutionError> {
        if self.scope_ctx.global_aliases.contains_key(&alias.name) {
            return Err(ResolutionError::DuplicateTypeAlias(
                alias.name.clone(),
                alias.span,
            ));
        }

        let id = self.global_ctx.new_id(alias.name.clone());
        self.scope_ctx.global_aliases.insert(alias.name.clone(), id);
        Ok(id)
    }

    pub fn define_global_type_alias(
        &mut self,
        alias: TypeAlias,
    ) -> Result<ResolvedTypeAlias, ResolutionError> {
        let id = *self
            .scope_ctx
            .global_aliases
            .get(&alias.name)
            .ok_or_else(|| {
                ResolutionError::VariableNotFound(
                    Path {
                        base: None,
                        segments: vec![alias.name.clone()],
                        span: alias.span,
                    },
                    alias.span,
                )
            })?;

        let mut type_scope = HashMap::new();
        let mut generic_ids = Vec::new();

        for generic in alias.generics {
            let id = GlobalType {
                krate: None,
                name: self.global_ctx.new_id(generic.name.clone()),
            };
            type_scope.insert(generic.name, id);
            generic_ids.push(id);
        }

        self.scope_ctx.type_scopes.push(type_scope);
        let resolved_body =
            Self::resolve_annotation(&self.global_ctx, &mut self.scope_ctx, alias.body)?;
        self.scope_ctx.type_scopes.pop();

        Ok(ResolvedTypeAlias {
            name: GlobalType {
                krate: None,
                name: id,
            },
            type_params: generic_ids,
            body: resolved_body,
        })
    }

    pub fn declare_global_variant(&mut self, variant: &Variant) -> Result<(), ResolutionError> {
        if self.scope_ctx.global_variants.contains_key(&variant.name) {
            return Err(ResolutionError::DuplicateVariant(
                variant.name.clone(),
                variant.span,
            ));
        }
        let def_id = self.global_ctx.new_id(variant.name.clone());
        self.scope_ctx
            .global_variants
            .insert(variant.name.clone(), def_id);
        Ok(())
    }

    pub fn define_global_variant(
        &mut self,
        variant: Variant,
    ) -> Result<ResolvedVariant, ResolutionError> {
        let def_id = *self
            .scope_ctx
            .global_variants
            .get(&variant.name)
            .expect("Variant name should have been declared");

        let mut constructors = HashMap::new();
        let mut type_scope = HashMap::new();
        let mut generic_ids = Vec::new();

        for generic in variant.generics.clone() {
            let id = GlobalType {
                krate: None,
                name: self.global_ctx.new_id(generic.name.clone()),
            };
            type_scope.insert(generic.name, id);
            generic_ids.push(id);
        }
        self.scope_ctx.type_scopes.push(type_scope);
        for (name, constructor) in variant.constructors.into_iter() {
            if self.scope_ctx.global_constructors.contains_key(&name) {
                return Err(ResolutionError::DuplicateConstructor(
                    name,
                    constructor.span,
                ));
            }

            let name_id = self.global_ctx.new_name(name.clone());
            let resolved_annotation = match constructor.annotation {
                Some(annot) => Some(Self::resolve_annotation(
                    &self.global_ctx,
                    &mut self.scope_ctx,
                    annot,
                )?),
                None => None,
            };
            constructors.insert(
                GlobalName {
                    krate: None,
                    name: name_id,
                },
                ResolvedConstructor {
                    name: GlobalName {
                        krate: None,
                        name: name_id,
                    },
                    annotation: resolved_annotation,
                    span: constructor.span,
                },
            );
            self.scope_ctx
                .global_constructors
                .insert(name, (def_id, name_id));
        }
        self.scope_ctx.type_scopes.pop();
        Ok(ResolvedVariant {
            name: GlobalType {
                krate: None,
                name: def_id,
            },
            type_params: generic_ids,
            constructors,
            span: variant.span,
        })
    }

    pub fn declare_global_definition(&mut self, def: &Definition) -> Result<(), ResolutionError> {
        if self.scope_ctx.scopes[0].contains_key(&def.name) {
            return Err(ResolutionError::DuplicateBinding(
                def.name.clone(),
                def.span,
            ));
        }

        let id = GlobalName {
            krate: None,
            name: self.global_ctx.new_name(def.name.clone()),
        };
        self.scope_ctx.scopes[0].insert(def.name.clone(), id);
        Ok(())
    }

    pub fn define_global_definition(
        &mut self,
        def: Definition,
    ) -> Result<ResolvedDefinition, ResolutionError> {
        let name_id = *self.scope_ctx.scopes[0]
            .get(&def.name)
            .expect("Definition name should have been declared");

        let mut type_scope = HashMap::new();
        let mut generic_ids = Vec::new();

        for generic in def.generics {
            let id = GlobalType {
                krate: None,
                name: self.global_ctx.new_id(generic.name.clone()),
            };
            type_scope.insert(generic.name, id);
            generic_ids.push(id);
        }

        self.scope_ctx.type_scopes.push(type_scope);
        let resolved_annot = if let Some(annot) = def.annotation {
            Some(Self::resolve_annotation(
                &self.global_ctx,
                &mut self.scope_ctx,
                annot,
            )?)
        } else {
            None
        };
        let (resolved_expr, _free_vars) =
            Self::analyze(&mut self.global_ctx, &mut self.scope_ctx, def.expr)?;
        self.scope_ctx.type_scopes.pop();

        Ok(ResolvedDefinition {
            name: (name_id, def.name),
            expr: Box::new(resolved_expr),
            type_params: generic_ids,
            annotation: resolved_annot,
            span: def.span,
        })
    }

    fn declare_def(
        &mut self,
        resolved_crate: &mut CrateDefMap,
        resolved_module: &mut ResolvedModuleData,
        def: Definition,
    ) -> Result<(), ResolutionError> {
        if resolved_module.definitions.contains_key(&def.name) {
            return Err(ResolutionError::DuplicateBinding(
                def.name.clone(),
                def.span,
            ));
        }
        let name_id = self.global_ctx.new_name(def.name.clone());
        resolved_module.definitions.insert(
            def.name.clone(),
            (
                resolved_crate.crate_id,
                DefinitionInfo::Definition(name_id),
                def.vis.clone(),
            ),
        );
        resolved_crate
            .defs_to_resolve
            .insert(name_id, (def, resolved_module.id));
        Ok(())
    }

    fn declare_type_alias(
        &mut self,
        resolved_crate: &mut CrateDefMap,
        resolved_module: &mut ResolvedModuleData,
        alias: TypeAlias,
    ) -> Result<(), ResolutionError> {
        if resolved_module.types.contains_key(&alias.name) {
            return Err(ResolutionError::DuplicateTypeAlias(
                alias.name.clone(),
                alias.span,
            ));
        }

        let id = self.global_ctx.new_id(alias.name.clone());

        resolved_module.types.insert(
            alias.name.clone(),
            (
                resolved_crate.crate_id,
                TypeInfo::Alias(id),
                alias.vis.clone(),
            ),
        );

        resolved_crate
            .aliases_to_resolve
            .insert(id, (alias, resolved_module.id));
        Ok(())
    }

    fn declare_variant(
        &mut self,
        resolved_crate: &mut CrateDefMap,
        resolved_module: &mut ResolvedModuleData,
        variant: Variant,
    ) -> Result<(), ResolutionError> {
        if resolved_module.types.contains_key(&variant.name) {
            return Err(ResolutionError::DuplicateVariant(
                variant.name.clone(),
                variant.span,
            ));
        }

        let id = self.global_ctx.new_id(variant.name.clone());

        resolved_module.types.insert(
            variant.name.clone(),
            (
                resolved_crate.crate_id,
                TypeInfo::Variant(id),
                variant.vis.clone(),
            ),
        );

        // Register each constructor in the definitions map and collect name mappings
        let mut ctor_name_map = HashMap::new();
        for (ctor_name, ctor) in &variant.constructors {
            if resolved_module.definitions.contains_key(ctor_name) {
                return Err(ResolutionError::DuplicateConstructor(
                    ctor_name.clone(),
                    ctor.span,
                ));
            }
            let ctor_id = self.global_ctx.new_name(ctor_name.clone());
            ctor_name_map.insert(ctor_name.clone(), ctor_id);
            resolved_module.definitions.insert(
                ctor_name.clone(),
                (
                    resolved_crate.crate_id,
                    DefinitionInfo::Constructor(id, ctor_id),
                    variant.vis.clone(),
                ),
            );
        }

        resolved_crate
            .variants_to_resolve
            .insert(id, (variant, resolved_module.id, ctor_name_map));

        Ok(())
    }

    fn declare_module(
        &mut self,
        resolved_crate: &CrateDefMap,
        resolved_module: &mut ResolvedModuleData,
        module_decl: ModuleDecl,
        module_paths: &BiMap<Vec<String>, ModuleId>,
    ) -> Result<(), ResolutionError> {
        let parent_path = module_paths
            .get_by_right(&resolved_module.id)
            .expect("Parent module ID must be present in driver paths");

        let mut child_path = parent_path.clone();
        child_path.push(module_decl.name.clone());

        let child_module_id = module_paths
            .get_by_left(&child_path)
            .expect("Child module found in AST but not loaded by driver");

        if resolved_module.modules.contains_key(&module_decl.name) {
            return Err(ResolutionError::DuplicateBinding(
                module_decl.name.clone(),
                module_decl.span,
            ));
        }

        resolved_module.modules.insert(
            module_decl.name,
            (resolved_crate.crate_id, *child_module_id, module_decl.vis),
        );

        Ok(())
    }

    fn import_resolution(
        resolved_crate: &mut CrateDefMap,
        import: &UnresolvedImport,
        resolution: Resolution,
    ) -> Result<(), ResolutionError> {
        let module_data = resolved_crate
            .modules
            .get_mut(&import.module_id)
            .expect("Module ID from import must exist");

        let name = match &import.alias {
            Some(a) => a.clone(),
            None => import
                .path
                .segments
                .last()
                .expect("Import path cannot be empty")
                .clone(),
        };
        let get_crate = |k: Option<CrateId>| k.unwrap_or(resolved_crate.crate_id);

        match resolution {
            Resolution::Def(gn) => {
                if module_data.definitions.contains_key(&name) {
                    return Err(ResolutionError::DuplicateBinding(name, import.span));
                }
                module_data.definitions.insert(
                    name,
                    (
                        get_crate(gn.krate),
                        DefinitionInfo::Definition(gn.name),
                        import.vis,
                    ),
                );
            }
            Resolution::Constructor(gt, gn) => {
                if module_data.definitions.contains_key(&name) {
                    return Err(ResolutionError::DuplicateConstructor(name, import.span));
                }
                module_data.definitions.insert(
                    name,
                    (
                        get_crate(gt.krate),
                        DefinitionInfo::Constructor(gt.name, gn.name),
                        import.vis,
                    ),
                );
            }
            Resolution::Variant(gt) => {
                if module_data.types.contains_key(&name) {
                    return Err(ResolutionError::DuplicateVariant(name, import.span));
                }
                module_data.types.insert(
                    name,
                    (get_crate(gt.krate), TypeInfo::Variant(gt.name), import.vis),
                );
            }
            Resolution::TypeAlias(gt) => {
                if module_data.types.contains_key(&name) {
                    return Err(ResolutionError::DuplicateTypeAlias(name, import.span));
                }
                module_data.types.insert(
                    name,
                    (get_crate(gt.krate), TypeInfo::Alias(gt.name), import.vis),
                );
            }
            Resolution::Module(c, m) => {
                if module_data.modules.contains_key(&name) {
                    return Err(ResolutionError::DuplicateBinding(name, import.span));
                }
                module_data.modules.insert(name, (c, m, import.vis));
            }
        }
        Ok(())
    }

    fn resolve_imports(&mut self, resolved: &mut CrateDefMap) -> Result<(), ResolutionError> {
        loop {
            let mut progress = false;
            let pending_imports = std::mem::take(&mut resolved.unresolved_imports);
            let mut next_imports = Vec::new();

            self.scope_ctx
                .world
                .crates
                .insert(resolved.crate_id, resolved.clone());

            for import in pending_imports {
                let mut resolved_this_pass = false;

                // Try resolving in Value Namespace
                if let Ok(res) = self.scope_ctx.world.resolve(
                    resolved.crate_id,
                    import.module_id,
                    import.path.clone(),
                    Namespace::Value,
                ) {
                    Self::import_resolution(resolved, &import, res)?;
                    resolved_this_pass = true;
                }

                // Try resolving in Type namespace
                if let Ok(res) = self.scope_ctx.world.resolve(
                    resolved.crate_id,
                    import.module_id,
                    import.path.clone(),
                    Namespace::Type,
                ) {
                    Self::import_resolution(resolved, &import, res)?;
                    resolved_this_pass = true;
                }

                if resolved_this_pass {
                    progress = true;
                } else {
                    next_imports.push(import);
                }
            }

            resolved.unresolved_imports = next_imports;

            if resolved.unresolved_imports.is_empty() {
                break;
            }

            if !progress {
                let import = &resolved.unresolved_imports[0];
                return Err(ResolutionError::VariableNotFound(
                    import.path.clone(),
                    import.span,
                ));
            }
        }

        Ok(())
    }

    fn resolve_bodies(
        &mut self,
        resolved: &mut CrateDefMap,
    ) -> Result<ResolveContext, ResolutionError> {
        let mut ctx = ResolveContext {
            crate_id: Some(resolved.crate_id),
            ..Default::default()
        };

        for (id, (alias, mod_id)) in resolved.aliases_to_resolve.drain() {
            ctx.module_id = Some(mod_id);

            let mut type_params = Vec::new();
            self.scope_ctx.type_scopes.push(HashMap::new());

            for generic in alias.generics {
                let gid = GlobalType {
                    krate: Some(resolved.crate_id),
                    name: ctx.new_id(generic.name.clone()),
                };
                self.scope_ctx
                    .type_scopes
                    .last_mut()
                    .unwrap()
                    .insert(generic.name, gid);
                type_params.push(gid);
            }

            let body = Self::resolve_annotation(&mut ctx, &mut self.scope_ctx, alias.body)?;
            self.scope_ctx.type_scopes.pop();

            resolved.types.insert(
                id,
                ResolvedTypeDefinition::Alias(ResolvedTypeAlias {
                    name: GlobalType {
                        krate: Some(resolved.crate_id),
                        name: id,
                    },
                    type_params,
                    body,
                }),
            );
        }

        // Resolve variants
        for (id, (variant, mod_id, ctor_map)) in resolved.variants_to_resolve.drain() {
            ctx.module_id = Some(mod_id);

            let mut type_params = Vec::new();
            self.scope_ctx.type_scopes.push(HashMap::new());

            for generic in variant.generics {
                let gid = GlobalType {
                    krate: Some(resolved.crate_id),
                    name: ctx.new_id(generic.name.clone()),
                };
                self.scope_ctx
                    .type_scopes
                    .last_mut()
                    .unwrap()
                    .insert(generic.name, gid);
                type_params.push(gid);
            }

            let mut constructors = HashMap::new();
            for (name, ctor) in variant.constructors {
                let ctor_name_id = ctor_map[&name];
                let gn = GlobalName {
                    krate: Some(resolved.crate_id),
                    name: ctor_name_id,
                };

                let annotation = if let Some(a) = ctor.annotation {
                    Some(Self::resolve_annotation(&mut ctx, &mut self.scope_ctx, a)?)
                } else {
                    None
                };

                let resolved_ctor = ResolvedConstructor {
                    name: gn,
                    annotation,
                    span: ctor.span,
                };

                constructors.insert(gn, resolved_ctor);

                // Register the constructor as a value definition
                resolved.definitions.insert(
                    ctor_name_id,
                    ResolvedValueDefinition::Constructor(
                        GlobalType {
                            krate: Some(resolved.crate_id),
                            name: id,
                        },
                        gn,
                    ),
                );
            }

            self.scope_ctx.type_scopes.pop();

            resolved.types.insert(
                id,
                ResolvedTypeDefinition::Variant(ResolvedVariant {
                    name: GlobalType {
                        krate: Some(resolved.crate_id),
                        name: id,
                    },
                    type_params,
                    constructors,
                    span: variant.span,
                }),
            );
        }

        // Resolve definitions
        for (id, (def, mod_id)) in resolved.defs_to_resolve.drain() {
            ctx.module_id = Some(mod_id);

            let mut type_params = Vec::new();
            self.scope_ctx.type_scopes.push(HashMap::new());

            for generic in def.generics {
                let gid = GlobalType {
                    krate: Some(resolved.crate_id),
                    name: ctx.new_id(generic.name.clone()),
                };
                self.scope_ctx
                    .type_scopes
                    .last_mut()
                    .unwrap()
                    .insert(generic.name, gid);
                type_params.push(gid);
            }

            let annotation = if let Some(a) = def.annotation {
                Some(Self::resolve_annotation(&mut ctx, &mut self.scope_ctx, a)?)
            } else {
                None
            };

            debug_assert_eq!(self.scope_ctx.scopes.len(), 1, "Scope stack leaked!");

            let (expr, _free) = Self::analyze(&mut self.global_ctx, &mut self.scope_ctx, def.expr)?;
            self.scope_ctx.type_scopes.pop();
            resolved.definitions.insert(
                id,
                ResolvedValueDefinition::Definition(ResolvedDefinition {
                    name: (
                        GlobalName {
                            krate: Some(resolved.crate_id),
                            name: id,
                        },
                        def.name,
                    ),
                    expr: Box::new(expr),
                    type_params,
                    annotation,
                    span: def.span,
                }),
            );
        }

        Ok(ctx)
    }

    pub fn resolve_crate(
        &mut self,
        id: CrateId,
        mut krate: Crate,
        extern_prelude: ExternPrelude,
    ) -> Result<ResolveContext, ResolutionError> {
        // We use two phases. First is declaration.
        let mut resolved = CrateDefMap {
            crate_id: id,
            modules: Default::default(),
            root: krate.root_module,
            extern_prelude,
            definitions: Default::default(),
            types: Default::default(),
            defs_to_resolve: Default::default(),
            variants_to_resolve: Default::default(),
            aliases_to_resolve: Default::default(),
            unresolved_imports: Vec::new(),
        };
        for (module_id, module) in krate.modules.drain() {
            let mut resolved_module = ResolvedModuleData {
                id: module_id,
                parent: module.parent,
                definitions: Default::default(),
                types: Default::default(),
                modules: Default::default(),
                scope: module.scope,
            };
            let module_paths = &krate.module_paths;

            for def in module.ast {
                match def {
                    Declaration::Def(def) => {
                        self.declare_def(&mut resolved, &mut resolved_module, def)?
                    }
                    Declaration::Variant(variant) => {
                        self.declare_variant(&mut resolved, &mut resolved_module, variant)?
                    }
                    Declaration::TypeAlias(alias) => {
                        self.declare_type_alias(&mut resolved, &mut resolved_module, alias)?
                    }
                    Declaration::Module(module_decl) => self.declare_module(
                        &mut resolved,
                        &mut resolved_module,
                        module_decl,
                        module_paths,
                    )?,
                    Declaration::Use(UseDecl {
                        path,
                        alias,
                        vis,
                        span,
                    }) => resolved.unresolved_imports.push(UnresolvedImport {
                        module_id,
                        path,
                        alias,
                        vis,
                        span,
                    }),
                }
            }

            resolved.modules.insert(module_id, resolved_module);
        }

        // Second pass: definition
        self.resolve_imports(&mut resolved)?;
        let ctx = self.resolve_bodies(&mut resolved)?;

        self.scope_ctx.world.crates.insert(id, resolved);
        Ok(ctx)
    }

    pub fn resolve_global_statement(
        &mut self,
        stmt: Statement,
    ) -> Result<ResolvedStatement, ResolutionError> {
        let span = stmt.span;
        match stmt.kind {
            StatementKind::Let(pattern, value, generics, annot) => {
                let mut new_type_scope = HashMap::new();
                let mut resolved_generics = Vec::new();
                for generic in generics {
                    let id = GlobalType {
                        krate: None,
                        name: self.global_ctx.new_id(generic.name.clone()),
                    };
                    new_type_scope.insert(generic.name.clone(), id);
                    resolved_generics.push(id);
                }
                self.scope_ctx.type_scopes.push(new_type_scope);

                let resolved_annot = if let Some(a) = annot {
                    Some(Self::resolve_annotation(
                        &self.global_ctx,
                        &mut self.scope_ctx,
                        a,
                    )?)
                } else {
                    None
                };
                let (resolved_value, _free_in_value) =
                    Self::analyze(&mut self.global_ctx, &mut self.scope_ctx, *value)?;
                let scope_idx = self.scope_ctx.scopes.len() - 1;
                let mut pattern_scope = HashMap::new();
                let resolved_pattern = Self::analyze_pattern(
                    &mut self.global_ctx,
                    &mut self.scope_ctx,
                    pattern,
                    &mut pattern_scope,
                )?;

                for (name, id) in pattern_scope {
                    self.scope_ctx.scopes[scope_idx].insert(name, id);
                }
                self.scope_ctx.type_scopes.pop();
                Ok(ResolvedStatement {
                    pattern: resolved_pattern,
                    value: Box::new(resolved_value),
                    value_type: resolved_annot,
                    type_params: resolved_generics,
                    span,
                })
            }
            StatementKind::Expr(expr) => {
                let (resolved_expr, _free_in_expr) =
                    Self::analyze(&mut self.global_ctx, &mut self.scope_ctx, *expr)?;
                Ok(ResolvedStatement {
                    pattern: ResolvedPattern::new(ResolvedPatternKind::Wildcard, span),
                    value: Box::new(resolved_expr),
                    value_type: None,
                    type_params: vec![],
                    span,
                })
            }
        }
    }

    fn desugar_let_to_block(
        pattern: Pattern,
        value: Box<Expr>,
        body: Box<Expr>,
        generics: Vec<Generic>,
        annot: Option<Annotation>,
        span: Span,
    ) -> Expr {
        let stmt = Statement {
            kind: StatementKind::Let(pattern, value, generics, annot),
            span,
        };
        Expr::new(ExprKind::Block(vec![stmt], Some(body)), span)
    }

    fn analyze_pattern(
        ctx: &mut ResolveContext,
        scope_ctx: &mut ScopeContext,
        pat: Pattern,
        scope: &mut Scope,
    ) -> Result<ResolvedPattern, ResolutionError> {
        let span = pat.span;
        match pat.kind {
            PatternKind::Var(name) => {
                let new_id = GlobalName {
                    krate: ctx.crate_id,
                    name: ctx.new_name(name.clone()),
                };
                if scope.insert(name.clone(), new_id).is_some() {
                    return Err(ResolutionError::DuplicateBinding(name, span));
                }
                Ok(ResolvedPattern::new(ResolvedPatternKind::Var(new_id), span))
            }
            PatternKind::Pair(p1, p2) => {
                let resolved_p1 = Self::analyze_pattern(ctx, scope_ctx, *p1, scope)?;
                let resolved_p2 = Self::analyze_pattern(ctx, scope_ctx, *p2, scope)?;

                let kind = ResolvedPatternKind::Pair(Box::new(resolved_p1), Box::new(resolved_p2));
                Ok(ResolvedPattern::new(kind, span))
            }
            PatternKind::Unit => Ok(ResolvedPattern::new(ResolvedPatternKind::Unit, span)),
            PatternKind::Wildcard => Ok(ResolvedPattern::new(ResolvedPatternKind::Wildcard, span)),
            PatternKind::Cons(p1, p2) => {
                let resolved_p1 = Self::analyze_pattern(ctx, scope_ctx, *p1, scope)?;
                let resolved_p2 = Self::analyze_pattern(ctx, scope_ctx, *p2, scope)?;

                let kind = ResolvedPatternKind::Cons(Box::new(resolved_p1), Box::new(resolved_p2));
                Ok(ResolvedPattern::new(kind, span))
            }
            PatternKind::EmptyList => {
                Ok(ResolvedPattern::new(ResolvedPatternKind::EmptyList, span))
            }
            PatternKind::Constructor(name, pat) => {
                let Some((variant_id, ctor_id)) = scope_ctx.global_constructors.get(&name).cloned()
                else {
                    return Err(ResolutionError::ConstructorNotFound(name, span));
                };
                let resolved = match pat {
                    Some(p) => Some(Box::new(Self::analyze_pattern(ctx, scope_ctx, *p, scope)?)),
                    None => None,
                };
                Ok(ResolvedPattern::new(
                    ResolvedPatternKind::Constructor(
                        GlobalType {
                            krate: None,
                            name: variant_id,
                        },
                        GlobalName {
                            krate: None,
                            name: ctor_id,
                        },
                        resolved,
                    ),
                    span,
                ))
            }
            PatternKind::Record(fields) => {
                let mut resolved = HashMap::new();
                for (field_name, field_pattern) in fields {
                    if resolved.contains_key(&field_name) {
                        return Err(ResolutionError::DuplicateRecordField(
                            field_name.clone(),
                            span,
                        ));
                    }
                    resolved.insert(
                        field_name,
                        Self::analyze_pattern(ctx, scope_ctx, field_pattern, scope)?,
                    );
                }
                Ok(ResolvedPattern::new(
                    ResolvedPatternKind::Record(resolved),
                    span,
                ))
            }
        }
    }

    fn resolve_local_statement(
        ctx: &mut ResolveContext,
        scope_ctx: &mut ScopeContext,
        stmt: Statement,
    ) -> Result<(ResolvedStatement, HashSet<GlobalName>), ResolutionError> {
        let span = stmt.span;
        match stmt.kind {
            StatementKind::Let(pattern, value, generics, annot) => {
                let mut new_type_scope = HashMap::new();
                let mut resolved_generics = Vec::new();

                for generic in generics {
                    let id = GlobalType {
                        krate: ctx.crate_id,
                        name: ctx.new_id(generic.name.clone()),
                    };
                    new_type_scope.insert(generic.name.clone(), id);
                    resolved_generics.push(id);
                }
                scope_ctx.type_scopes.push(new_type_scope);

                let resolved_annot = if let Some(a) = annot {
                    Some(Self::resolve_annotation(ctx, scope_ctx, a)?)
                } else {
                    None
                };

                let (resolved_value, free_in_value) = Self::analyze(ctx, scope_ctx, *value)?;
                let mut pattern_scope = HashMap::new();
                let resolved_pattern =
                    Self::analyze_pattern(ctx, scope_ctx, pattern, &mut pattern_scope)?;

                let current_scope = scope_ctx
                    .scopes
                    .last_mut()
                    .expect("No scope to bind variable into");
                for (name, id) in pattern_scope {
                    if current_scope.insert(name.clone(), id).is_some() {
                        return Err(ResolutionError::DuplicateBinding(name, span));
                    }
                }

                scope_ctx.type_scopes.pop();

                Ok((
                    ResolvedStatement {
                        pattern: resolved_pattern,
                        value: Box::new(resolved_value),
                        value_type: resolved_annot,
                        type_params: resolved_generics,
                        span,
                    },
                    free_in_value,
                ))
            }

            StatementKind::Expr(expr) => {
                let (resolved_expr, free_in_expr) = Self::analyze(ctx, scope_ctx, *expr)?;

                Ok((
                    ResolvedStatement {
                        pattern: ResolvedPattern::new(ResolvedPatternKind::Wildcard, span),
                        value: Box::new(resolved_expr),
                        value_type: None,
                        type_params: vec![],
                        span,
                    },
                    free_in_expr,
                ))
            }
        }
    }

    fn analyze(
        ctx: &mut ResolveContext,
        scope_ctx: &mut ScopeContext,
        expr: Expr,
    ) -> Result<(Resolved, HashSet<GlobalName>), ResolutionError> {
        let span = expr.span;
        match expr.kind {
            ExprKind::Var(path) => {
                // We first check in scopes and globals
                if let Some(name) = path.simple() {
                    for scope in scope_ctx.scopes.iter().rev() {
                        if let Some(id) = scope.get(name) {
                            if let Some(builtin) = scope_ctx.builtins.get(&id.name) {
                                return Ok((
                                    Resolved::new(ResolvedKind::Builtin(builtin.clone()), span),
                                    HashSet::new(),
                                ));
                            } else {
                                let mut free = HashSet::new();
                                free.insert(*id);
                                return Ok((Resolved::new(ResolvedKind::Var(*id), span), free));
                            }
                        }
                    }
                    if let Some((variant_id, ctor_id)) =
                        scope_ctx.global_constructors.get(name).cloned()
                    {
                        return Ok((
                            Resolved::new(
                                ResolvedKind::Constructor(
                                    GlobalType {
                                        krate: None,
                                        name: variant_id,
                                    },
                                    GlobalName {
                                        krate: None,
                                        name: ctor_id,
                                    },
                                ),
                                span,
                            ),
                            HashSet::new(),
                        ));
                    }
                }

                // Next, we check crates
                if let (Some(c_id), Some(m_id)) = (ctx.crate_id, ctx.module_id) {
                    match scope_ctx
                        .world
                        .resolve(c_id, m_id, path.clone(), Namespace::Value)
                    {
                        Ok(Resolution::Def(gn)) => {
                            return Ok((
                                Resolved::new(ResolvedKind::Var(gn), span),
                                HashSet::new(),
                            ));
                        }
                        Ok(Resolution::Constructor(gt, gn)) => {
                            return Ok((
                                Resolved::new(ResolvedKind::Constructor(gt, gn), span),
                                HashSet::new(),
                            ));
                        }
                        Err(e) => return Err(e),
                        _ => {}
                    }
                }

                Err(ResolutionError::VariableNotFound(path, span))
            }

            ExprKind::IntLit(i) => {
                Ok((Resolved::new(ResolvedKind::IntLit(i), span), HashSet::new()))
            }
            ExprKind::FloatLit(d) => Ok((
                Resolved::new(ResolvedKind::FloatLit(d), span),
                HashSet::new(),
            )),
            ExprKind::BoolLit(b) => Ok((
                Resolved::new(ResolvedKind::BoolLit(b), span),
                HashSet::new(),
            )),
            ExprKind::StringLit(s) => Ok((
                Resolved::new(ResolvedKind::StringLit(s), span),
                HashSet::new(),
            )),
            ExprKind::UnitLit => Ok((Resolved::new(ResolvedKind::UnitLit, span), HashSet::new())),
            ExprKind::PairLit(first, second) => {
                let (resolved_first, free_first) = Self::analyze(ctx, scope_ctx, *first)?;
                let (resolved_second, free_second) = Self::analyze(ctx, scope_ctx, *second)?;
                let all_free = free_first.union(&free_second).cloned().collect();
                Ok((
                    Resolved::new(
                        ResolvedKind::PairLit(Box::new(resolved_first), Box::new(resolved_second)),
                        span,
                    ),
                    all_free,
                ))
            }
            ExprKind::RecordLit(s) => {
                let mut resolved = HashMap::new();
                let mut all_free = HashSet::new();
                for (k, v) in s.into_iter() {
                    if resolved.contains_key(&k) {
                        return Err(ResolutionError::DuplicateRecordField(k, span));
                    }
                    let (r, v) = Self::analyze(ctx, scope_ctx, v)?;
                    resolved.insert(k, r);
                    all_free = all_free.union(&v).cloned().collect();
                }
                Ok((
                    Resolved::new(ResolvedKind::RecordLit(resolved), span),
                    all_free,
                ))
            }
            ExprKind::BinOp(op, a, b) => {
                let (resolved_a, free_a) = Self::analyze(ctx, scope_ctx, *a)?;
                let (resolved_b, free_b) = Self::analyze(ctx, scope_ctx, *b)?;
                let all = free_a.union(&free_b).cloned().collect();
                Ok((
                    Resolved::new(
                        ResolvedKind::BinOp(op, Box::new(resolved_a), Box::new(resolved_b)),
                        span,
                    ),
                    all,
                ))
            }
            ExprKind::RecRecord(fields) => {
                let mut all_free = HashSet::new();
                let mut new_scope = HashMap::new();
                let mut name_to_string = HashMap::new();

                // Pre-declare all labels in a new scope to allow for mutual recursion
                for (name_str, _) in &fields {
                    if new_scope.contains_key(name_str) {
                        return Err(ResolutionError::DuplicateRecordField(
                            name_str.clone(),
                            span,
                        ));
                    }
                    let id = GlobalName {
                        krate: None,
                        name: ctx.new_name(name_str.clone()),
                    };
                    new_scope.insert(name_str.clone(), id);
                    name_to_string.insert(id, name_str.clone());
                }

                scope_ctx.scopes.push(new_scope.clone());
                let mut resolved_fields = HashMap::new();

                for (name_str, expr) in fields {
                    let (resolved_expr, free_vars) = Self::analyze(ctx, scope_ctx, expr)?;
                    let name_id = *new_scope.get(&name_str).unwrap();
                    resolved_fields.insert(name_str, (name_id, resolved_expr));
                    all_free.extend(free_vars);
                }
                scope_ctx.scopes.pop();

                for name_id in new_scope.values() {
                    all_free.remove(name_id);
                }

                Ok((
                    Resolved::new(ResolvedKind::RecRecord(resolved_fields), span),
                    all_free,
                ))
            }
            ExprKind::App(func, arg) => {
                let (resolved_func, free_func) = Self::analyze(ctx, scope_ctx, *func)?;
                let (resolved_arg, free_arg) = Self::analyze(ctx, scope_ctx, *arg)?;
                let all = free_func.union(&free_arg).cloned().collect();
                Ok((
                    Resolved::new(
                        ResolvedKind::App(Box::new(resolved_func), Box::new(resolved_arg)),
                        span,
                    ),
                    all,
                ))
            }
            ExprKind::If(condition, consequent, alternative) => {
                let (resolved_condition, free_condition) =
                    Self::analyze(ctx, scope_ctx, *condition)?;
                let (resolved_consequent, free_consequent) =
                    Self::analyze(ctx, scope_ctx, *consequent)?;
                let (resolved_alternative, free_alternative) =
                    Self::analyze(ctx, scope_ctx, *alternative)?;

                let all_free = free_condition
                    .union(&free_consequent)
                    .cloned()
                    .collect::<HashSet<_>>()
                    .union(&free_alternative)
                    .cloned()
                    .collect();

                Ok((
                    Resolved::new(
                        ResolvedKind::If(
                            Box::new(resolved_condition),
                            Box::new(resolved_consequent),
                            Box::new(resolved_alternative),
                        ),
                        span,
                    ),
                    all_free,
                ))
            }

            ExprKind::Let(pattern, value, body, generics, annot) => {
                let block_expr =
                    Self::desugar_let_to_block(pattern, value, body, generics, annot, span);
                Self::analyze(ctx, scope_ctx, block_expr)
            }

            ExprKind::Lambda(param_pattern, body, annot) => {
                let resolved_annot = if let Some(a) = annot {
                    Some(Self::resolve_annotation(ctx, scope_ctx, a)?)
                } else {
                    None
                };

                let mut new_scope = HashMap::new();
                let resolved =
                    Self::analyze_pattern(ctx, scope_ctx, param_pattern, &mut new_scope)?;

                scope_ctx.scopes.push(new_scope.clone());
                let (resolved_body, mut free_in_body) = Self::analyze(ctx, scope_ctx, *body)?;
                scope_ctx.scopes.pop();

                for &name_id in new_scope.values() {
                    free_in_body.remove(&name_id);
                }

                Ok((
                    Resolved::new(
                        ResolvedKind::Lambda {
                            param: resolved,
                            body: Box::new(resolved_body),
                            captures: free_in_body.clone(),
                            param_type: resolved_annot,
                        },
                        span,
                    ),
                    free_in_body,
                ))
            }

            ExprKind::Cons(first, second) => {
                let (resolved_first, free_first) = Self::analyze(ctx, scope_ctx, *first)?;
                let (resolved_second, free_second) = Self::analyze(ctx, scope_ctx, *second)?;
                let all_free = free_first.union(&free_second).cloned().collect();
                Ok((
                    Resolved::new(
                        ResolvedKind::Cons(Box::new(resolved_first), Box::new(resolved_second)),
                        span,
                    ),
                    all_free,
                ))
            }
            ExprKind::EmptyListLit => Ok((
                Resolved::new(ResolvedKind::EmptyListLit, span),
                HashSet::new(),
            )),
            ExprKind::Match(expr, branches) => {
                let (resolved_expr, free_expr) = Self::analyze(ctx, scope_ctx, *expr)?;

                let mut all_free = free_expr;
                let mut resolved_branches = Vec::new();

                for branch in branches {
                    let mut new_scope = HashMap::new();
                    let resolved_pattern =
                        Self::analyze_pattern(ctx, scope_ctx, branch.pattern, &mut new_scope)?;

                    scope_ctx.scopes.push(new_scope.clone());
                    let (resolved_body, mut free_in_body) =
                        Self::analyze(ctx, scope_ctx, branch.expr)?;
                    scope_ctx.scopes.pop();

                    for name_id in new_scope.values() {
                        free_in_body.remove(name_id);
                    }

                    all_free = all_free.union(&free_in_body).cloned().collect();

                    resolved_branches.push(ResolvedMatchBranch {
                        pattern: resolved_pattern,
                        expr: Box::new(resolved_body),
                        span: branch.span,
                    });
                }

                Ok((
                    Resolved::new(
                        ResolvedKind::Match(Box::new(resolved_expr), resolved_branches),
                        span,
                    ),
                    all_free,
                ))
            }
            ExprKind::FieldAccess(expr, field) => {
                let (resolved, free) = Self::analyze(ctx, scope_ctx, *expr)?;
                Ok((
                    Resolved::new(ResolvedKind::FieldAccess(Box::new(resolved), field), span),
                    free,
                ))
            }
            ExprKind::Block(statements, tail) => {
                let mut all_free = HashSet::new();
                let mut resolved_statements = Vec::new();
                let block_scope = HashMap::new();

                scope_ctx.scopes.push(block_scope);

                for stmt in statements {
                    let (resolved_stmt, free_in_stmt) =
                        Self::resolve_local_statement(ctx, scope_ctx, stmt)?;
                    all_free.extend(free_in_stmt);
                    resolved_statements.push(resolved_stmt);
                }

                let resolved_tail = if let Some(tail_expr) = tail {
                    let (resolved, free) = Self::analyze(ctx, scope_ctx, *tail_expr)?;
                    all_free.extend(free);
                    Some(Box::new(resolved))
                } else {
                    None
                };

                let block_scope = scope_ctx.scopes.pop().unwrap();
                for name_id in block_scope.values() {
                    all_free.remove(name_id);
                }

                Ok((
                    Resolved::new(
                        ResolvedKind::Block(resolved_statements, resolved_tail),
                        span,
                    ),
                    all_free,
                ))
            }
        }
    }

    pub fn snapshot_local_name_table(&self) -> crate::analysis::name_table::LocalNameTable {
        crate::analysis::name_table::LocalNameTable::with_maps(
            self.global_ctx.name_origins.clone(),
            self.global_ctx.type_name_origins.clone(),
        )
    }

    /// Extract the LocalNameTable from this resolver.
    /// This consumes the resolver's name origin maps and returns them as a LocalNameTable
    /// for use in error formatting and debugging.
    pub fn into_local_name_table(self) -> crate::analysis::name_table::LocalNameTable {
        crate::analysis::name_table::LocalNameTable::with_maps(
            self.global_ctx.name_origins,
            self.global_ctx.type_name_origins,
        )
    }

    pub fn next_name_id(&self) -> Name {
        self.global_ctx.next_id
    }

    pub fn next_type_name_id(&self) -> TypeName {
        self.global_ctx.next_type
    }

    /// Prepare a resolved crate for type inference by extracting and ordering definitions.
    pub fn prepare_crate(&self, crate_id: CrateId) -> PreparedCrate {
        let crate_def_map = &self.scope_ctx.world.crates[&crate_id];

        // Extract type definitions (aliases + variants)
        let mut type_defs = Vec::new();
        for (_, type_def) in &crate_def_map.types {
            match type_def {
                ResolvedTypeDefinition::Alias(alias) => {
                    type_defs.push(PreparedTypeDefinition::Alias(alias.clone()));
                }
                ResolvedTypeDefinition::Variant(variant) => {
                    type_defs.push(PreparedTypeDefinition::Variant(variant.clone()));
                }
            }
        }
        let type_groups = reorder_type_definitions(type_defs);

        // Extract value definitions (not constructors)
        let mut value_defs = Vec::new();
        for (_, value_def) in &crate_def_map.definitions {
            if let ResolvedValueDefinition::Definition(def) = value_def {
                value_defs.push(def.clone());
            }
        }
        let definition_groups = reorder_definitions(value_defs);

        PreparedCrate {
            crate_id,
            type_groups,
            definition_groups,
        }
    }
}
