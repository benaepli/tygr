use crate::builtin::{BUILTINS, BuiltinFn};
use crate::parser::{BinOp, Expr, ExprKind, Pattern, PatternKind, Span};
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
pub enum ResolvedKind {
    Var(Name),
    Lambda {
        param: ResolvedPattern,
        body: Box<Resolved>,
        captures: HashSet<Name>,
    },
    App(Box<Resolved>, Box<Resolved>),
    Let {
        pattern: ResolvedPattern,
        value: Box<Resolved>,
        body: Box<Resolved>,
    },
    Fix(Box<Resolved>),
    If(Box<Resolved>, Box<Resolved>, Box<Resolved>),
    Cons(Box<Resolved>, Box<Resolved>),

    UnitLit,
    PairLit(Box<Resolved>, Box<Resolved>),
    IntLit(i64),
    FloatLit(f64),
    BoolLit(bool),
    StringLit(String),
    EmptyListLit,

    BinOp(BinOp, Box<Resolved>, Box<Resolved>),

    Builtin(BuiltinFn),
}

#[derive(Error, Debug, PartialEq, Clone)]
pub enum ResolutionError {
    #[error("variable `{0}` not found")]
    VariableNotFound(String, Span),
    #[error("variable `{0}` is bound more than once in the same pattern")]
    DuplicateBinding(String, Span),
}

type Scope = HashMap<String, Name>;

pub struct Resolver {
    scopes: Vec<Scope>,
    next_id: Name,
    builtins: HashMap<Name, BuiltinFn>,
}

impl Resolver {
    pub fn new() -> Self {
        let mut resolver = Self {
            scopes: vec![],
            next_id: Name(0),
            builtins: HashMap::new(),
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

    fn new_name(&mut self) -> Name {
        let id = self.next_id;
        self.next_id = Name(self.next_id.0 + 1);
        id
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
            PatternKind::EmptyList => Ok(ResolvedPattern::new(ResolvedPatternKind::EmptyList, span)),
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

            ExprKind::Let(pattern, value, body) => {
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
                Ok((
                    Resolved::new(
                        ResolvedKind::Let {
                            pattern: resolved,
                            value: Box::new(resolved_value),
                            body: Box::new(resolved_body),
                        },
                        span,
                    ),
                    all_free,
                ))
            }

            ExprKind::Lambda(param_pattern, body) => {
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
            ExprKind::EmptyListLit => Ok((Resolved::new(ResolvedKind::EmptyListLit, span), HashSet::new())),
        }
    }
}
