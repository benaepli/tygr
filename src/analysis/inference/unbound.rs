use crate::analysis::inference::{
    Type, TypeID, TypeKind, TypeScheme, Typed, TypedCrate, TypedDefinition, TypedGroup, TypedKind,
};
use crate::parser::Span;
use std::collections::HashSet;
use thiserror::Error;

#[derive(Debug, Clone, Error)]
#[error("unbound type variable")]
pub struct UnboundTypeVarError {
    pub span: Span,
    pub unbound_var: TypeID,
}

#[derive(Debug, Clone, Default)]
pub struct UnboundVarChecker {
    errors: Vec<UnboundTypeVarError>,
}

impl UnboundVarChecker {
    pub fn new() -> Self {
        Self { errors: Vec::new() }
    }

    pub fn check_crate(mut self, krate: &TypedCrate) -> Vec<UnboundTypeVarError> {
        for group in &krate.groups {
            match group {
                TypedGroup::NonRecursive(def) => self.check_definition(def),
                TypedGroup::Recursive(defs) => {
                    for def in defs {
                        self.check_definition(def);
                    }
                }
            }
        }
        self.errors
    }

    fn check_definition(&mut self, def: &TypedDefinition) {
        self.check_scheme(&def.scheme, def.span);
        self.check_expr(&def.expr);
    }

    fn check_expr(&mut self, expr: &Typed) {
        match &expr.kind {
            TypedKind::Block(stmts, tail) => {
                for stmt in stmts {
                    for (_name, scheme) in &stmt.bindings {
                        self.check_scheme(scheme, stmt.span);
                    }
                    self.check_expr(&stmt.value);
                }
                if let Some(tail_expr) = tail {
                    self.check_expr(tail_expr);
                }
            }
            TypedKind::Lambda { body, .. } => self.check_expr(body),
            TypedKind::App(f, arg) => {
                self.check_expr(f);
                self.check_expr(arg);
            }
            TypedKind::If(cond, cons, alt) => {
                self.check_expr(cond);
                self.check_expr(cons);
                self.check_expr(alt);
            }
            TypedKind::Match(target, branches) => {
                self.check_expr(target);
                for branch in branches {
                    self.check_expr(&branch.expr);
                }
            }
            TypedKind::Cons(h, t) | TypedKind::PairLit(h, t) | TypedKind::BinOp(_, h, t) => {
                self.check_expr(h);
                self.check_expr(t);
            }
            TypedKind::RecordLit(fields) => {
                for expr in fields.values() {
                    self.check_expr(expr);
                }
            }
            TypedKind::RecRecord(fields) => {
                for (_, expr) in fields.values() {
                    self.check_expr(expr);
                }
            }
            TypedKind::FieldAccess(expr, _) => self.check_expr(expr),
            TypedKind::Var(_)
            | TypedKind::IntLit(_)
            | TypedKind::FloatLit(_)
            | TypedKind::BoolLit(_)
            | TypedKind::StringLit(_)
            | TypedKind::UnitLit
            | TypedKind::EmptyListLit
            | TypedKind::Builtin(_)
            | TypedKind::Constructor { .. } => {}
        }
    }

    fn check_scheme(&mut self, scheme: &TypeScheme, span: Span) {
        let mut used_vars = HashSet::new();
        self.collect_vars(&scheme.ty, &mut used_vars);

        let bound_vars: HashSet<TypeID> = scheme.vars.iter().map(|(id, _)| *id).collect();

        for used_var in used_vars {
            if !bound_vars.contains(&used_var) {
                self.errors.push(UnboundTypeVarError {
                    span,
                    unbound_var: used_var,
                });
            }
        }
    }

    fn collect_vars(&self, ty: &Type, vars: &mut HashSet<TypeID>) {
        match &ty.ty {
            TypeKind::Var(id) => {
                vars.insert(*id);
            }
            TypeKind::App(lhs, rhs) | TypeKind::Pair(lhs, rhs) | TypeKind::Function(lhs, rhs) => {
                self.collect_vars(lhs, vars);
                self.collect_vars(rhs, vars);
            }
            TypeKind::Record(fields) => {
                for field_ty in fields.values() {
                    self.collect_vars(field_ty, vars);
                }
            }
            TypeKind::AliasHead(_, args) => {
                for arg in args {
                    self.collect_vars(arg, vars);
                }
            }
            TypeKind::Con(_) => {}
        }
    }
}
