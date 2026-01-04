mod ast;
pub use ast::*;

use crate::builtin::{BUILTIN_TYPES, BUILTINS, BuiltinFn, TYPE_BASE};
use crate::driver::Crate;
use crate::parser::{
    Annotation, AnnotationKind, Declaration, Definition, Expr, ExprKind, Generic, ModuleDecl, Path,
    Pattern, PatternKind, SourceId, Span, Statement, StatementKind, TypeAlias, UseDecl, Variant,
};
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
}

type Scope = HashMap<String, GlobalName>;
type TypeScope = HashMap<String, GlobalType>;

struct ResolveContext {
    crate_id: Option<CrateId>,
    next_id: Name,
    next_type: TypeName,

    name_origins: HashMap<Name, String>,
    type_name_origins: HashMap<TypeName, String>,
}

impl ResolveContext {
    fn new() -> Self {
        Self {
            crate_id: None,
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
}

struct ScopeContext {
    scopes: Vec<Scope>,
    type_scopes: Vec<TypeScope>,
    builtins: HashMap<Name, BuiltinFn>,
    global_aliases: HashMap<String, TypeName>,
    global_variants: HashMap<String, TypeName>,
    global_constructors: HashMap<String, (TypeName, Name)>,
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
        }
    }
}

pub struct Resolver {
    ctx: ResolveContext,
    scope_ctx: ScopeContext,
    world: World,
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
            ctx,
            scope_ctx,
            world: World::default(),
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
        let id = self.ctx.new_name(name.to_string());
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
                Err(ResolutionError::VariableNotFound(path, span))
            }

            AnnotationKind::App(lhs, rhs) => {
                let r_lhs = Self::resolve_annotation(scope_ctx, *lhs)?;
                let r_rhs = Self::resolve_annotation(scope_ctx, *rhs)?;
                Ok(ResolvedAnnotation::new(
                    ResolvedAnnotationKind::App(Box::new(r_lhs), Box::new(r_rhs)),
                    span,
                ))
            }

            AnnotationKind::Pair(lhs, rhs) => {
                let r_lhs = Self::resolve_annotation(scope_ctx, *lhs)?;
                let r_rhs = Self::resolve_annotation(scope_ctx, *rhs)?;
                Ok(ResolvedAnnotation::new(
                    ResolvedAnnotationKind::Pair(Box::new(r_lhs), Box::new(r_rhs)),
                    span,
                ))
            }

            AnnotationKind::Lambda(param, ret) => {
                let r_param = Self::resolve_annotation(scope_ctx, *param)?;
                let r_ret = Self::resolve_annotation(scope_ctx, *ret)?;
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
                    resolved.insert(k, Self::resolve_annotation(scope_ctx, v)?);
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

        let id = self.ctx.new_id(alias.name.clone());
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
                name: self.ctx.new_id(generic.name.clone()),
            };
            type_scope.insert(generic.name, id);
            generic_ids.push(id);
        }

        self.scope_ctx.type_scopes.push(type_scope);
        let resolved_body = Self::resolve_annotation(&mut self.scope_ctx, alias.body)?;
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
        let def_id = self.ctx.new_id(variant.name.clone());
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
                name: self.ctx.new_id(generic.name.clone()),
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

            let name_id = self.ctx.new_name(name.clone());
            let resolved_annotation = match constructor.annotation {
                Some(annot) => Some(Self::resolve_annotation(&mut self.scope_ctx, annot)?),
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
            name: self.ctx.new_name(def.name.clone()),
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
                name: self.ctx.new_id(generic.name.clone()),
            };
            type_scope.insert(generic.name, id);
            generic_ids.push(id);
        }

        self.scope_ctx.type_scopes.push(type_scope);
        let resolved_annot = if let Some(annot) = def.annotation {
            Some(Self::resolve_annotation(&mut self.scope_ctx, annot)?)
        } else {
            None
        };
        let (resolved_expr, _free_vars) =
            Self::analyze(&mut self.ctx, &mut self.scope_ctx, def.expr)?;
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
        let name_id = self.ctx.new_name(def.name.clone());
        resolved_module.definitions.insert(
            def.name.clone(),
            (resolved_crate.crate_id, name_id, def.vis.clone()),
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
        crate_id: CrateId,
    ) -> Result<(), ResolutionError> {
        if resolved_module.types.contains_key(&alias.name) {
            return Err(ResolutionError::DuplicateTypeAlias(
                alias.name.clone(),
                alias.span,
            ));
        }

        let id = self.ctx.new_id(alias.name.clone());

        resolved_module
            .types
            .insert(alias.name.clone(), (crate_id, id, alias.vis.clone()));

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
        crate_id: CrateId,
    ) -> Result<(), ResolutionError> {
        if resolved_module.types.contains_key(&variant.name) {
            return Err(ResolutionError::DuplicateVariant(
                variant.name.clone(),
                variant.span,
            ));
        }

        let id = self.ctx.new_id(variant.name.clone());

        resolved_module
            .types
            .insert(variant.name.clone(), (crate_id, id, variant.vis.clone()));

        resolved_crate
            .variants_to_resolve
            .insert(id, (variant, resolved_module.id));
        Ok(())
    }

    fn declare_module(
        &mut self,
        resolved_crate: &CrateDefMap,
        resolved_module: &mut ResolvedModuleData,
        module_decl: ModuleDecl,
    ) {
    }

    pub fn resolve_crate(
        &mut self,
        id: CrateId,
        mut krate: Crate,
        extern_prelude: ExternPrelude,
    ) -> Result<(), ResolutionError> {
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

            for def in module.ast {
                match def {
                    Declaration::Def(def) => {
                        self.declare_def(&mut resolved, &mut resolved_module, def)?
                    }
                    Declaration::Variant(_) => {}
                    Declaration::TypeAlias(_) => {}
                    Declaration::Module(module_decl) => {
                        self.declare_module(&mut resolved, &mut resolved_module, module_decl)
                    }
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
        Ok(())
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
                        name: self.ctx.new_id(generic.name.clone()),
                    };
                    new_type_scope.insert(generic.name.clone(), id);
                    resolved_generics.push(id);
                }
                self.scope_ctx.type_scopes.push(new_type_scope);

                let resolved_annot = if let Some(a) = annot {
                    Some(Self::resolve_annotation(&mut self.scope_ctx, a)?)
                } else {
                    None
                };
                let (resolved_value, _free_in_value) =
                    Self::analyze(&mut self.ctx, &mut self.scope_ctx, *value)?;
                let scope_idx = self.scope_ctx.scopes.len() - 1;
                let mut pattern_scope = HashMap::new();
                let resolved_pattern = Self::analyze_pattern(
                    &mut self.ctx,
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
                    Self::analyze(&mut self.ctx, &mut self.scope_ctx, *expr)?;
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
                    Some(Self::resolve_annotation(scope_ctx, a)?)
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
                if let Some(name) = path.simple() {
                    for scope in scope_ctx.scopes.iter().rev() {
                        if let Some(id) = scope.get(name) {
                            if let Some(builtin) = scope_ctx.builtins.get(&id.name) {
                                // TODO: only for global scope
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
                    Some(Self::resolve_annotation(scope_ctx, a)?)
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

    pub fn snapshot_name_table(&self) -> crate::analysis::name_table::NameTable {
        crate::analysis::name_table::NameTable::with_maps(
            self.ctx.name_origins.clone(),
            self.ctx.type_name_origins.clone(),
        )
    }

    /// Extract the NameTable from this resolver.
    /// This consumes the resolver's name origin maps and returns them as a NameTable
    /// for use in error formatting and debugging.
    pub fn into_name_table(self) -> crate::analysis::name_table::NameTable {
        crate::analysis::name_table::NameTable::with_maps(
            self.ctx.name_origins,
            self.ctx.type_name_origins,
        )
    }

    pub fn next_name_id(&self) -> Name {
        self.ctx.next_id
    }

    pub fn next_type_name_id(&self) -> TypeName {
        self.ctx.next_type
    }
}
