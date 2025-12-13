use crate::builtin::{BUILTIN_TYPES, BUILTINS, BuiltinFn, TYPE_BASE};
use crate::parser::{
    Adt, Annotation, AnnotationKind, BinOp, Expr, ExprKind, Generic, Pattern, PatternKind, Span,
    TypeAlias,
};
use std::collections::{HashMap, HashSet};
use std::fmt;
use thiserror::Error;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Name(pub usize);

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DefID(pub usize);

impl fmt::Display for DefID {
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
pub struct ResolvedAdt {
    pub name: DefID,
    pub generics: Vec<Generic>,
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
    Var(DefID),
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
        type_params: Vec<DefID>,
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
    FieldAccess(Box<Resolved>, String),

    Builtin(BuiltinFn),
    Constructor(DefID, Name),
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
}

type Scope = HashMap<String, Name>;
type TypeScope = HashMap<String, DefID>;

#[derive(Debug, Clone)]
struct TypeAliasEntry {
    generics: Vec<DefID>,
    body: ResolvedAnnotation,
}

enum Partial {
    Done(ResolvedAnnotation),
    Alias {
        name: String,
        body: ResolvedAnnotation,
        pending: Vec<DefID>,
        subs: HashMap<DefID, ResolvedAnnotation>,
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
    next_type: DefID,

    type_aliases: HashMap<String, TypeAliasEntry>,

    adts: HashMap<String, DefID>,
    constructors: HashMap<String, (DefID, Name)>,
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

            adts: HashMap::new(),
            constructors: HashMap::new(),
        };

        let mut global = Scope::new();
        for (keyword, builtin) in BUILTINS.entries() {
            let name_id = resolver.new_name();
            global.insert(keyword.to_string(), name_id);
            resolver.builtins.insert(name_id, builtin.clone());
        }
        resolver.scopes.push(global);
        resolver
    }

    fn instantiate_alias(
        &self,
        template: &ResolvedAnnotation,
        substitutions: &HashMap<DefID, ResolvedAnnotation>,
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

    fn new_id(&mut self) -> DefID {
        let id = self.next_type;
        self.next_type = DefID(self.next_type.0 + 1);
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
                } else if let Some(id) = self.adts.get(&name) {
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

    fn resolve_adt(&mut self, adt: Adt) -> Result<ResolvedAdt, ResolutionError> {
        if self.adts.contains_key(&adt.name) {
            // TODO
        }
        let def_id = self.new_id();
        self.adts.insert(adt.name, def_id);

        let mut constructors = HashMap::new();

        let mut type_scope = HashMap::new();
        let mut generic_ids = Vec::new();

        for generic in adt.generics.clone() {
            let id = self.new_id();
            type_scope.insert(generic.name, id);
            generic_ids.push(id);
        }
        self.type_scopes.push(type_scope);
        for (name, constructor) in adt.constructors.into_iter() {
            if self.constructors.contains_key(&name) {
                // TODO
            }

            let name_id = self.new_name();
            constructors.insert(
                name_id,
                ResolvedConstructor {
                    annotation: self
                        .resolve_annotation(constructor.annotation)?
                        .finalize(adt.span)?,
                    span: constructor.span,
                },
            );
            self.constructors.insert(name, (def_id, name_id));
        }
        self.type_scopes.pop();
        Ok(ResolvedAdt {
            name: def_id,
            generics: adt.generics,
            constructors,
            span: adt.span,
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
            PatternKind::Constructor(_, _) => todo!(),
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
                if let Some((adt_id, ctor_id)) = self.constructors.get(&name).cloned() {
                    return Ok((
                        Resolved::new(ResolvedKind::Constructor(adt_id, ctor_id), span),
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
}
