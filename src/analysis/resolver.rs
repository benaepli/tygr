use crate::builtin::{BUILTINS, BuiltinFn};
use crate::parser::{BinOp, Expr};
use std::collections::{HashMap, HashSet};
use thiserror::Error;

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
    If(Box<Resolved>, Box<Resolved>, Box<Resolved>),

    IntLit(i64),
    DoubleLit(f64),
    BoolLit(bool),
    StringLit(String),

    BinOp(BinOp, Box<Resolved>, Box<Resolved>),

    Builtin(BuiltinFn),
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

    fn analyze(&mut self, expr: Expr) -> Result<(Resolved, HashSet<Name>), ResolutionError> {
        match expr {
            Expr::Var(name) => {
                for scope in self.scopes.iter().rev() {
                    if let Some(id) = scope.get(&name) {
                        if let Some(builtin) = self.builtins.get(id) {
                            return Ok((Resolved::Builtin(builtin.clone()), HashSet::new()));
                        } else {
                            let mut free = HashSet::new();
                            free.insert(*id);
                            return Ok((Resolved::Var(*id), free));
                        }
                    }
                }
                Err(ResolutionError::VariableNotFound(name))
            }

            Expr::IntLit(i) => Ok((Resolved::IntLit(i), HashSet::new())),
            Expr::DoubleLit(d) => Ok((Resolved::DoubleLit(d), HashSet::new())),
            Expr::BoolLit(b) => Ok((Resolved::BoolLit(b), HashSet::new())),
            Expr::StringLit(s) => Ok((Resolved::StringLit(s), HashSet::new())),

            Expr::BinOp(op, a, b) => {
                let (resolved_a, free_a) = self.analyze(*a)?;
                let (resolved_b, free_b) = self.analyze(*b)?;
                let all = free_a.union(&free_b).cloned().collect();
                Ok((
                    Resolved::BinOp(op, Box::new(resolved_a), Box::new(resolved_b)),
                    all,
                ))
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
                let (resolved_alternative, free_alternative) = self.analyze(*alternative)?;

                let all_free = free_condition
                    .union(&free_consequent)
                    .cloned()
                    .collect::<HashSet<_>>()
                    .union(&free_alternative)
                    .cloned()
                    .collect();

                Ok((
                    Resolved::If(
                        Box::new(resolved_condition),
                        Box::new(resolved_consequent),
                        Box::new(resolved_alternative),
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
