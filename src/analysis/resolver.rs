use std::collections::{HashMap, HashSet};
use thiserror::Error;
use crate::parser::{BinOp, Expr, UnaryOp};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Name(pub usize);

#[derive(Debug, Clone, PartialEq)]
pub enum Resolved {
    Var(Name),
    Lambda {
        param: Name,
        body: Box<Resolved>,
        captures: HashSet<Name>,
    },
    App(Box<Resolved>, Box<Resolved>),
    Let {
        name: Name,
        value: Box<Resolved>,
        body: Box<Resolved>,
    },
    Fix(Box<Resolved>),
    If(Box<Resolved>, Box<Resolved>, Option<Box<Resolved>>),

    IntLit(i64),
    DoubleLit(f64),
    BoolLit(bool),

    BinOp(BinOp, Box<Resolved>, Box<Resolved>),
    UnaryOp(UnaryOp, Box<Resolved>),
}

#[derive(Error, Debug, PartialEq, Clone)]
pub enum ResolutionError {
    #[error("variable `{0}` not found")]
    VariableNotFound(String),
}

type Scope = HashMap<String, Name>;

pub struct Resolver {
    scopes: Vec<Scope>,
    next_id: Name,
}

impl Resolver {
    pub fn new() -> Self {
        Self {
            scopes: vec![],
            next_id: Name(0),
        }
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

    fn analyze(&mut self, expr: Expr) -> Result<(Resolved, HashSet<Name>), ResolutionError> {
        match expr {
            Expr::Var(name) => {
                for scope in self.scopes.iter().rev() {
                    if let Some(id) = scope.get(&name) {
                        let mut free = HashSet::new();
                        free.insert(*id);
                        return Ok((Resolved::Var(*id), free));
                    }
                }
                Err(ResolutionError::VariableNotFound(name))
            }

            Expr::IntLit(i) => Ok((Resolved::IntLit(i), HashSet::new())),
            Expr::DoubleLit(d) => Ok((Resolved::DoubleLit(d), HashSet::new())),
            Expr::BoolLit(b) => Ok((Resolved::BoolLit(b), HashSet::new())),

            Expr::BinOp(op, a, b) => {
                let (resolved_a, free_a) = self.analyze(*a)?;
                let (resolved_b, free_b) = self.analyze(*b)?;
                let all = free_a.union(&free_b).cloned().collect();
                Ok((
                    Resolved::BinOp(op, Box::new(resolved_a), Box::new(resolved_b)),
                    all,
                ))
            }
            Expr::UnaryOp(op, operand) => {
                let (resolved_operand, free) = self.analyze(*operand)?;
                Ok((Resolved::UnaryOp(op, Box::new(resolved_operand)), free))
            }
            Expr::App(func, arg) => {
                let (resolved_func, free_func) = self.analyze(*func)?;
                let (resolved_arg, free_arg) = self.analyze(*arg)?;
                let all = free_func.union(&free_arg).cloned().collect();
                Ok((
                    Resolved::App(Box::new(resolved_func), Box::new(resolved_arg)),
                    all,
                ))
            }
            Expr::Fix(e) => {
                let (resolved, free) = self.analyze(*e)?;
                Ok((Resolved::Fix(Box::new(resolved)), free))
            }
            Expr::If(condition, consequent, alternative) => {
                let (resolved_condition, free_condition) = self.analyze(*condition)?;
                let (resolved_consequent, free_consequent) = self.analyze(*consequent)?;

                let (resolved_alternative, all_free) = if let Some(alt) = alternative {
                    let (resolved_alt, free_alt) = self.analyze(*alt)?;
                    let all = free_condition
                        .union(&free_consequent)
                        .cloned()
                        .collect::<HashSet<_>>()
                        .union(&free_alt)
                        .cloned()
                        .collect();
                    (Some(Box::new(resolved_alt)), all)
                } else {
                    let all = free_condition.union(&free_consequent).cloned().collect();
                    (None, all)
                };

                Ok((
                    Resolved::If(
                        Box::new(resolved_condition),
                        Box::new(resolved_consequent),
                        resolved_alternative,
                    ),
                    all_free,
                ))
            }

            Expr::Let(name, value, body) => {
                let (resolved_value, free_in_value) = self.analyze(*value)?;
                let new_id = self.new_name();

                let mut new_scope = HashMap::new();
                new_scope.insert(name, new_id);
                self.scopes.push(new_scope);

                let (resolved_body, mut free_in_body) = self.analyze(*body)?;
                self.scopes.pop();

                free_in_body.remove(&new_id);
                let all_free = free_in_value.union(&free_in_body).cloned().collect();
                Ok((
                    Resolved::Let {
                        name: new_id,
                        value: Box::new(resolved_value),
                        body: Box::new(resolved_body),
                    },
                    all_free,
                ))
            }
            Expr::Lambda(param, body) => {
                let param_id = self.new_name();

                let mut new_scope = HashMap::new();
                new_scope.insert(param, param_id);
                self.scopes.push(new_scope);

                let (resolved_body, mut free_in_body) = self.analyze(*body)?;
                self.scopes.pop();

                free_in_body.remove(&param_id);

                Ok((
                    Resolved::Lambda {
                        param: param_id,
                        body: Box::new(resolved_body),
                        captures: free_in_body.clone(),
                    },
                    free_in_body,
                ))
            }
        }
    }
}
