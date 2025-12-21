use crate::builtin::{BUILTIN_TYPES, BUILTINS, BuiltinFn, TYPE_BASE};
use crate::parser::{
    Annotation, AnnotationKind, BinOp, Expr, ExprKind, Pattern, PatternKind, Span, TypeAlias,
    Variant,
};
use std::collections::{HashMap, HashSet};
use std::fmt;
use thiserror::Error;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Name(pub usize);

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeName(pub usize);

impl fmt::Display for TypeName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedConstructor {
    pub annotation: ResolvedAnnotation,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedVariant {
    pub name: TypeName,
    pub type_params: Vec<TypeName>,
    pub constructors: HashMap<Name, ResolvedConstructor>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ResolvedPatternKind {
    Var(Name),
    Unit,
    Pair(Box<ResolvedPattern>, Box<ResolvedPattern>),
    Wildcard,
    Cons(Box<ResolvedPattern>, Box<ResolvedPattern>),
    EmptyList,
    Record(HashMap<String, ResolvedPattern>),
    Constructor(TypeName, Name, Box<ResolvedPattern>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedPattern {
    pub kind: ResolvedPatternKind,
    pub span: Span,
}

impl ResolvedPattern {
    fn new(kind: ResolvedPatternKind, span: Span) -> Self {
        ResolvedPattern { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedMatchBranch {
    pub pattern: ResolvedPattern,
    pub expr: Box<Resolved>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Resolved {
    pub kind: ResolvedKind,
    pub span: Span,
}

impl Resolved {
    fn new(kind: ResolvedKind, span: Span) -> Self {
        Resolved { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ResolvedAnnotationKind {
    Var(TypeName),
    App(Box<ResolvedAnnotation>, Box<ResolvedAnnotation>),
    Pair(Box<ResolvedAnnotation>, Box<ResolvedAnnotation>),
    Lambda(Box<ResolvedAnnotation>, Box<ResolvedAnnotation>),
    Record(HashMap<String, ResolvedAnnotation>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedAnnotation {
    pub kind: ResolvedAnnotationKind,
    pub span: Span,
}

impl ResolvedAnnotation {
    fn new(kind: ResolvedAnnotationKind, span: Span) -> Self {
        ResolvedAnnotation { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ResolvedKind {
    Var(Name),
    Lambda {
        param: ResolvedPattern,
        body: Box<Resolved>,
        captures: HashSet<Name>,
        param_type: Option<ResolvedAnnotation>,
    },
    App(Box<Resolved>, Box<Resolved>),
    Let {
        pattern: ResolvedPattern,
        value: Box<Resolved>,
        body: Box<Resolved>,
        value_type: Option<ResolvedAnnotation>,
        type_params: Vec<TypeName>,
    },
    Fix(Box<Resolved>),
    If(Box<Resolved>, Box<Resolved>, Box<Resolved>),
    Match(Box<Resolved>, Vec<ResolvedMatchBranch>),
    Cons(Box<Resolved>, Box<Resolved>),

    UnitLit,
    PairLit(Box<Resolved>, Box<Resolved>),
    IntLit(i64),
    FloatLit(f64),
    BoolLit(bool),
    StringLit(String),
    EmptyListLit,
    RecordLit(HashMap<String, Resolved>),

    BinOp(BinOp, Box<Resolved>, Box<Resolved>),
    RecRecord(HashMap<String, (Name, Resolved)>),
    FieldAccess(Box<Resolved>, String),

    Builtin(BuiltinFn),
    Constructor(TypeName, Name),
}

#[derive(Error, Debug, PartialEq, Clone)]
pub enum ResolutionError {
    #[error("variable `{0}` not found")]
    VariableNotFound(String, Span),
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

type Scope = HashMap<String, Name>;
type TypeScope = HashMap<String, TypeName>;

#[derive(Debug, Clone)]
struct TypeAliasEntry {
    generics: Vec<TypeName>,
    body: ResolvedAnnotation,
}

enum Partial {
    Done(ResolvedAnnotation),
    Alias {
        name: String,
        body: ResolvedAnnotation,
        pending: Vec<TypeName>,
        subs: HashMap<TypeName, ResolvedAnnotation>,
        total: usize,
    },
}

impl Partial {
    fn finalize(self, span: Span) -> Result<ResolvedAnnotation, ResolutionError> {
        match self {
            Partial::Done(r) => Ok(r),
            Partial::Alias {
                name,
                pending,
                total,
                ..
            } => {
                let provided = total - pending.len();
                Err(ResolutionError::WrongNumberOfTypeArguments(
                    name, total, provided, span,
                ))
            }
        }
    }
}

pub struct Resolver {
    scopes: Vec<Scope>,
    next_id: Name,
    builtins: HashMap<Name, BuiltinFn>,

    type_scopes: Vec<TypeScope>,
    next_type: TypeName,

    type_aliases: HashMap<String, TypeAliasEntry>,

    variants: HashMap<String, TypeName>,
    constructors: HashMap<String, (TypeName, Name)>,

    // Name preservation for error messages
    name_origins: HashMap<Name, String>,
    type_name_origins: HashMap<TypeName, String>,
}

impl Resolver {
    pub fn new() -> Self {
        let mut resolver = Self {
            scopes: vec![],
            next_id: Name(0),
            builtins: HashMap::new(),

            type_scopes: vec![],
            next_type: TYPE_BASE,

            type_aliases: HashMap::new(),

            variants: HashMap::new(),
            constructors: HashMap::new(),

            name_origins: HashMap::new(),
            type_name_origins: HashMap::new(),
        };

        // Store builtin type names
        for (type_name_str, type_name_id) in BUILTIN_TYPES.entries() {
            resolver
                .type_name_origins
                .insert(*type_name_id, type_name_str.to_string());
        }

        let mut global = Scope::new();
        for (keyword, builtin) in BUILTINS.entries() {
            let name_id = resolver.new_name();
            global.insert(keyword.to_string(), name_id);
            resolver.builtins.insert(name_id, builtin.clone());
            resolver.name_origins.insert(name_id, keyword.to_string());
        }
        resolver.scopes.push(global);
        resolver
    }

    fn instantiate_alias(
        &self,
        template: &ResolvedAnnotation,
        substitutions: &HashMap<TypeName, ResolvedAnnotation>,
    ) -> ResolvedAnnotation {
        let span = template.span;
        let kind = match &template.kind {
            ResolvedAnnotationKind::Var(id) => {
                if let Some(replacement) = substitutions.get(id) {
                    return replacement.clone();
                }
                ResolvedAnnotationKind::Var(*id)
            }
            ResolvedAnnotationKind::App(lhs, rhs) => ResolvedAnnotationKind::App(
                Box::new(self.instantiate_alias(lhs, substitutions)),
                Box::new(self.instantiate_alias(rhs, substitutions)),
            ),
            ResolvedAnnotationKind::Pair(lhs, rhs) => ResolvedAnnotationKind::Pair(
                Box::new(self.instantiate_alias(lhs, substitutions)),
                Box::new(self.instantiate_alias(rhs, substitutions)),
            ),
            ResolvedAnnotationKind::Lambda(param, ret) => ResolvedAnnotationKind::Lambda(
                Box::new(self.instantiate_alias(param, substitutions)),
                Box::new(self.instantiate_alias(ret, substitutions)),
            ),
            ResolvedAnnotationKind::Record(m) => ResolvedAnnotationKind::Record(
                m.iter()
                    .map(|(k, v)| (k.clone(), self.instantiate_alias(v, substitutions)))
                    .collect(),
            ),
        };
        ResolvedAnnotation::new(kind, span)
    }

    fn new_name(&mut self) -> Name {
        let id = self.next_id;
        self.next_id = Name(self.next_id.0 + 1);
        id
    }

    fn new_id(&mut self) -> TypeName {
        let id = self.next_type;
        self.next_type = TypeName(self.next_type.0 + 1);
        id
    }

    fn resolve_annotation(&mut self, annot: Annotation) -> Result<Partial, ResolutionError> {
        let span = annot.span;

        match annot.kind {
            AnnotationKind::Var(name) => {
                for scope in self.type_scopes.iter().rev() {
                    if let Some(id) = scope.get(&name) {
                        return Ok(Partial::Done(ResolvedAnnotation::new(
                            ResolvedAnnotationKind::Var(*id),
                            span,
                        )));
                    }
                }

                if let Some(id) = BUILTIN_TYPES.get(&name) {
                    Ok(Partial::Done(ResolvedAnnotation::new(
                        ResolvedAnnotationKind::Var(*id),
                        span,
                    )))
                } else if let Some(alias) = self.type_aliases.get(&name).cloned() {
                    if alias.generics.is_empty() {
                        Ok(Partial::Done(alias.body))
                    } else {
                        let total = alias.generics.len();
                        Ok(Partial::Alias {
                            name: name.clone(),
                            body: alias.body,
                            pending: alias.generics,
                            subs: HashMap::new(),
                            total,
                        })
                    }
                } else if let Some(id) = self.variants.get(&name) {
                    Ok(Partial::Done(ResolvedAnnotation::new(
                        ResolvedAnnotationKind::Var(*id),
                        span,
                    )))
                } else {
                    return Err(ResolutionError::VariableNotFound(name, span));
                }
            }

            AnnotationKind::App(lhs, rhs) => match self.resolve_annotation(*lhs)? {
                Partial::Alias {
                    name,
                    body,
                    mut pending,
                    mut subs,
                    total,
                } => {
                    let arg = self.resolve_annotation(*rhs)?.finalize(span)?;
                    subs.insert(pending.remove(0), arg);

                    if pending.is_empty() {
                        Ok(Partial::Done(self.instantiate_alias(&body, &subs)))
                    } else {
                        Ok(Partial::Alias {
                            name,
                            body,
                            pending,
                            subs,
                            total,
                        })
                    }
                }
                Partial::Done(lhs) => {
                    let rhs = self.resolve_annotation(*rhs)?.finalize(span)?;
                    Ok(Partial::Done(ResolvedAnnotation::new(
                        ResolvedAnnotationKind::App(Box::new(lhs), Box::new(rhs)),
                        span,
                    )))
                }
            },

            AnnotationKind::Pair(lhs, rhs) => {
                let r_lhs = self.resolve_annotation(*lhs)?.finalize(span)?;
                let r_rhs = self.resolve_annotation(*rhs)?.finalize(span)?;
                Ok(Partial::Done(ResolvedAnnotation::new(
                    ResolvedAnnotationKind::Pair(Box::new(r_lhs), Box::new(r_rhs)),
                    span,
                )))
            }

            AnnotationKind::Lambda(param, ret) => {
                let r_param = self.resolve_annotation(*param)?.finalize(span)?;
                let r_ret = self.resolve_annotation(*ret)?.finalize(span)?;
                Ok(Partial::Done(ResolvedAnnotation::new(
                    ResolvedAnnotationKind::Lambda(Box::new(r_param), Box::new(r_ret)),
                    span,
                )))
            }
            AnnotationKind::Record(m) => {
                let mut resolved = HashMap::new();
                for (k, v) in m.into_iter() {
                    if resolved.contains_key(&k) {
                        return Err(ResolutionError::DuplicateRecordField(k, span));
                    }
                    resolved.insert(k, self.resolve_annotation(v)?.finalize(span)?);
                }
                Ok(Partial::Done(ResolvedAnnotation::new(
                    ResolvedAnnotationKind::Record(resolved),
                    span,
                )))
            }
        }
    }

    pub fn resolve_type_alias(&mut self, alias: TypeAlias) -> Result<(), ResolutionError> {
        if self.type_aliases.contains_key(&alias.name) {
            return Err(ResolutionError::DuplicateTypeAlias(alias.name, alias.span));
        }

        let mut type_scope = HashMap::new();
        let mut generic_ids = Vec::new();

        for generic in alias.generics {
            let id = self.new_id();
            type_scope.insert(generic.name, id);
            generic_ids.push(id);
        }

        self.type_scopes.push(type_scope);
        let resolved_body = self.resolve_annotation(alias.body)?.finalize(alias.span)?;
        self.type_scopes.pop();

        let entry = TypeAliasEntry {
            generics: generic_ids,
            body: resolved_body,
        };

        self.type_aliases.insert(alias.name, entry);
        Ok(())
    }

    pub fn declare_variant(&mut self, variant: &Variant) -> Result<(), ResolutionError> {
        if self.variants.contains_key(&variant.name) {
            return Err(ResolutionError::DuplicateVariant(
                variant.name.clone(),
                variant.span,
            ));
        }
        let def_id = self.new_id();
        self.variants.insert(variant.name.clone(), def_id);
        self.type_name_origins.insert(def_id, variant.name.clone());
        Ok(())
    }

    pub fn define_variant(&mut self, variant: Variant) -> Result<ResolvedVariant, ResolutionError> {
        let def_id = *self
            .variants
            .get(&variant.name)
            .expect("Variant name should have been declared");

        let mut constructors = HashMap::new();
        let mut type_scope = HashMap::new();
        let mut generic_ids = Vec::new();

        for generic in variant.generics.clone() {
            let id = self.new_id();
            self.type_name_origins.insert(id, generic.name.clone());
            type_scope.insert(generic.name, id);
            generic_ids.push(id);
        }
        self.type_scopes.push(type_scope);
        for (name, constructor) in variant.constructors.into_iter() {
            if self.constructors.contains_key(&name) {
                return Err(ResolutionError::DuplicateConstructor(
                    name,
                    constructor.span,
                ));
            }

            let name_id = self.new_name();
            self.name_origins.insert(name_id, name.clone());
            constructors.insert(
                name_id,
                ResolvedConstructor {
                    annotation: self
                        .resolve_annotation(constructor.annotation)?
                        .finalize(variant.span)?,
                    span: constructor.span,
                },
            );
            self.constructors.insert(name, (def_id, name_id));
        }
        self.type_scopes.pop();
        Ok(ResolvedVariant {
            name: def_id,
            type_params: generic_ids,
            constructors,
            span: variant.span,
        })
    }

    pub fn resolve(&mut self, expr: Expr) -> Result<Resolved, ResolutionError> {
        let (resolved, _) = self.analyze(expr)?;
        Ok(resolved)
    }

    fn analyze_pattern(
        &mut self,
        pat: Pattern,
        scope: &mut Scope,
    ) -> Result<ResolvedPattern, ResolutionError> {
        let span = pat.span;
        match pat.kind {
            PatternKind::Var(name) => {
                let new_id = self.new_name();
                self.name_origins.insert(new_id, name.clone());
                if scope.insert(name.clone(), new_id).is_some() {
                    return Err(ResolutionError::DuplicateBinding(name, span));
                }
                Ok(ResolvedPattern::new(ResolvedPatternKind::Var(new_id), span))
            }
            PatternKind::Pair(p1, p2) => {
                let resolved_p1 = self.analyze_pattern(*p1, scope)?;
                let resolved_p2 = self.analyze_pattern(*p2, scope)?;

                let kind = ResolvedPatternKind::Pair(Box::new(resolved_p1), Box::new(resolved_p2));
                Ok(ResolvedPattern::new(kind, span))
            }
            PatternKind::Unit => Ok(ResolvedPattern::new(ResolvedPatternKind::Unit, span)),
            PatternKind::Wildcard => Ok(ResolvedPattern::new(ResolvedPatternKind::Wildcard, span)),
            PatternKind::Cons(p1, p2) => {
                let resolved_p1 = self.analyze_pattern(*p1, scope)?;
                let resolved_p2 = self.analyze_pattern(*p2, scope)?;

                let kind = ResolvedPatternKind::Cons(Box::new(resolved_p1), Box::new(resolved_p2));
                Ok(ResolvedPattern::new(kind, span))
            }
            PatternKind::EmptyList => {
                Ok(ResolvedPattern::new(ResolvedPatternKind::EmptyList, span))
            }
            PatternKind::Constructor(name, pat) => {
                let Some((variant_id, ctor_id)) = self.constructors.get(&name).cloned() else {
                    return Err(ResolutionError::ConstructorNotFound(name, span));
                };
                let resolved = self.analyze_pattern(*pat, scope)?;
                Ok(ResolvedPattern::new(
                    ResolvedPatternKind::Constructor(variant_id, ctor_id, Box::new(resolved)),
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
                    resolved.insert(field_name, self.analyze_pattern(field_pattern, scope)?);
                }
                Ok(ResolvedPattern::new(
                    ResolvedPatternKind::Record(resolved),
                    span,
                ))
            }
        }
    }

    fn analyze(&mut self, expr: Expr) -> Result<(Resolved, HashSet<Name>), ResolutionError> {
        let span = expr.span;
        match expr.kind {
            ExprKind::Var(name) => {
                for scope in self.scopes.iter().rev() {
                    if let Some(id) = scope.get(&name) {
                        if let Some(builtin) = self.builtins.get(id) {
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
                if let Some((variant_id, ctor_id)) = self.constructors.get(&name).cloned() {
                    return Ok((
                        Resolved::new(ResolvedKind::Constructor(variant_id, ctor_id), span),
                        HashSet::new(),
                    ));
                }
                Err(ResolutionError::VariableNotFound(name, span))
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
                let (resolved_first, free_first) = self.analyze(*first)?;
                let (resolved_second, free_second) = self.analyze(*second)?;
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
                    let (r, v) = self.analyze(v)?;
                    resolved.insert(k, r);
                    all_free = all_free.union(&v).cloned().collect();
                }
                Ok((
                    Resolved::new(ResolvedKind::RecordLit(resolved), span),
                    all_free,
                ))
            }
            ExprKind::BinOp(op, a, b) => {
                let (resolved_a, free_a) = self.analyze(*a)?;
                let (resolved_b, free_b) = self.analyze(*b)?;
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
                    let new_id = self.new_name();
                    self.name_origins.insert(new_id, name_str.clone());
                    new_scope.insert(name_str.clone(), new_id);
                    name_to_string.insert(new_id, name_str.clone());
                }

                self.scopes.push(new_scope.clone());
                let mut resolved_fields = HashMap::new();

                for (name_str, expr) in fields {
                    let (resolved_expr, free_vars) = self.analyze(expr)?;
                    let name_id = *new_scope.get(&name_str).unwrap();
                    resolved_fields.insert(name_str, (name_id, resolved_expr));
                    all_free.extend(free_vars);
                }
                self.scopes.pop();

                for name_id in new_scope.values() {
                    all_free.remove(name_id);
                }

                Ok((
                    Resolved::new(ResolvedKind::RecRecord(resolved_fields), span),
                    all_free,
                ))
            }
            ExprKind::App(func, arg) => {
                let (resolved_func, free_func) = self.analyze(*func)?;
                let (resolved_arg, free_arg) = self.analyze(*arg)?;
                let all = free_func.union(&free_arg).cloned().collect();
                Ok((
                    Resolved::new(
                        ResolvedKind::App(Box::new(resolved_func), Box::new(resolved_arg)),
                        span,
                    ),
                    all,
                ))
            }
            ExprKind::Fix(e) => {
                let (resolved, free) = self.analyze(*e)?;
                Ok((
                    Resolved::new(ResolvedKind::Fix(Box::new(resolved)), span),
                    free,
                ))
            }
            ExprKind::If(condition, consequent, alternative) => {
                let (resolved_condition, free_condition) = self.analyze(*condition)?;
                let (resolved_consequent, free_consequent) = self.analyze(*consequent)?;
                let (resolved_alternative, free_alternative) = self.analyze(*alternative)?;

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
                let mut new_type_scope = HashMap::new();
                let mut resolved_generics = Vec::new();
                for generic in generics {
                    let id = self.new_id();
                    new_type_scope.insert(generic.name.clone(), id);
                    resolved_generics.push(id);
                }
                self.type_scopes.push(new_type_scope);
                let resolved_annot = if let Some(a) = annot {
                    let span = a.span;
                    Some(self.resolve_annotation(a)?.finalize(span)?)
                } else {
                    None
                };

                let (resolved_value, free_in_value) = self.analyze(*value)?;

                let mut new_scope = HashMap::new();
                let resolved = self.analyze_pattern(pattern, &mut new_scope)?;

                self.scopes.push(new_scope.clone());
                let (resolved_body, mut free_in_body) = self.analyze(*body)?;
                self.scopes.pop();

                for name_id in new_scope.values() {
                    free_in_body.remove(name_id);
                }

                let all_free = free_in_value.union(&free_in_body).cloned().collect();

                self.type_scopes.pop();
                Ok((
                    Resolved::new(
                        ResolvedKind::Let {
                            pattern: resolved,
                            value: Box::new(resolved_value),
                            body: Box::new(resolved_body),
                            value_type: resolved_annot,
                            type_params: resolved_generics,
                        },
                        span,
                    ),
                    all_free,
                ))
            }

            ExprKind::Lambda(param_pattern, body, annot) => {
                let resolved_annot = if let Some(a) = annot {
                    let span = a.span;
                    Some(self.resolve_annotation(a)?.finalize(span)?)
                } else {
                    None
                };

                let mut new_scope = HashMap::new();
                let resolved = self.analyze_pattern(param_pattern, &mut new_scope)?;

                self.scopes.push(new_scope.clone());
                let (resolved_body, mut free_in_body) = self.analyze(*body)?;
                self.scopes.pop();

                for name_id in new_scope.values() {
                    free_in_body.remove(name_id);
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
                let (resolved_first, free_first) = self.analyze(*first)?;
                let (resolved_second, free_second) = self.analyze(*second)?;
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
                let (resolved_expr, free_expr) = self.analyze(*expr)?;

                let mut all_free = free_expr;
                let mut resolved_branches = Vec::new();

                for branch in branches {
                    let mut new_scope = HashMap::new();
                    let resolved_pattern = self.analyze_pattern(branch.pattern, &mut new_scope)?;

                    self.scopes.push(new_scope.clone());
                    let (resolved_body, mut free_in_body) = self.analyze(branch.expr)?;
                    self.scopes.pop();

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
                let (resolved, free) = self.analyze(*expr)?;
                Ok((
                    Resolved::new(ResolvedKind::FieldAccess(Box::new(resolved), field), span),
                    free,
                ))
            }
        }
    }

    /// Extract the NameTable from this resolver.
    /// This consumes the resolver's name origin maps and returns them as a NameTable
    /// for use in error formatting and debugging.
    pub fn into_name_table(self) -> crate::analysis::name_table::NameTable {
        crate::analysis::name_table::NameTable::with_maps(self.name_origins, self.type_name_origins)
    }
}
