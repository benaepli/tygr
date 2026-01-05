use crate::analysis::inference::{Type, TypeScheme};
use crate::analysis::resolver::{CrateId, GlobalName};
use crate::builtin::BuiltinFn;
use crate::ir::constructor::{self, Pattern, PatternKind};
use crate::ir::direct::closure::VariantDef;
use crate::parser::BinOp;
use std::collections::{BTreeMap, HashSet};
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct Crate {
    pub crate_id: CrateId,
    pub groups: Vec<Cluster>,
    pub variants: Vec<VariantDef>,
    pub next_name: GlobalName,
}

#[derive(Debug, Clone)]
pub enum Cluster {
    Recursive(Vec<Def>),
    NonRecursive(Def),
}

#[derive(Debug, Clone)]
pub struct Def {
    pub name: GlobalName,
    pub expr: Expr,
    pub ty: Rc<Type>,
    pub scheme: TypeScheme,
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub ty: Rc<Type>,
}

#[derive(Debug, Clone)]
pub struct MatchBranch {
    pub pattern: Pattern,
    pub body: Box<Expr>,
    pub scrutinee_scheme: Option<TypeScheme>,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Let {
        name: GlobalName,
        scheme: TypeScheme,
        val: Box<Expr>,
        body: Box<Expr>,
    },
    Var {
        name: GlobalName,
        instantiation: Vec<Rc<Type>>,
    },
    Lambda {
        param: GlobalName,
        body: Box<Expr>,
        captures: HashSet<GlobalName>,
    },
    App(Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<MatchBranch>),

    UnitLit,
    PairLit(Box<Expr>, Box<Expr>),
    IntLit(i64),
    FloatLit(f64),
    BoolLit(bool),
    StringLit(String),
    EmptyListLit,
    RecordLit(BTreeMap<String, Expr>),
    Cons(Box<Expr>, Box<Expr>),
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    RecRecord(BTreeMap<String, (GlobalName, Expr)>),
    FieldAccess(Box<Expr>, String),
    Builtin {
        fun: BuiltinFn,
        instantiation: Vec<Rc<Type>>,
    },
    Pack {
        tag: u32,
        payload: Option<Box<Expr>>,
        instantiation: Vec<Rc<Type>>,
    },
}

pub fn convert(c: constructor::Crate) -> Crate {
    let groups = c.groups.into_iter().map(convert_cluster).collect();
    Crate {
        crate_id: c.crate_id,
        groups,
        variants: c.variants,
        next_name: c.next_name,
    }
}

fn convert_cluster(c: constructor::Cluster) -> Cluster {
    match c {
        constructor::Cluster::NonRecursive(d) => Cluster::NonRecursive(convert_def(d)),
        constructor::Cluster::Recursive(ds) => {
            Cluster::Recursive(ds.into_iter().map(convert_def).collect())
        }
    }
}

fn convert_def(d: constructor::Def) -> Def {
    Def {
        name: d.name,
        expr: convert_expr(d.expr),
        ty: d.ty,
        scheme: d.scheme,
    }
}

fn convert_expr(e: constructor::Expr) -> Expr {
    let kind = match e.kind {
        constructor::ExprKind::Block(stmts, final_expr) => {
            return convert_block(stmts, final_expr, e.ty);
        }

        constructor::ExprKind::Match(scrutinee, branches) => {
            let new_branches = branches
                .into_iter()
                .map(|b| MatchBranch {
                    pattern: b.pattern,
                    body: Box::new(convert_expr(*b.body)),
                    scrutinee_scheme: None,
                })
                .collect();
            ExprKind::Match(Box::new(convert_expr(*scrutinee)), new_branches)
        }
        constructor::ExprKind::Lambda {
            param,
            body,
            captures,
        } => ExprKind::Lambda {
            param,
            body: Box::new(convert_expr(*body)),
            captures,
        },
        constructor::ExprKind::App(f, a) => {
            ExprKind::App(Box::new(convert_expr(*f)), Box::new(convert_expr(*a)))
        }
        constructor::ExprKind::If(c, t, e) => ExprKind::If(
            Box::new(convert_expr(*c)),
            Box::new(convert_expr(*t)),
            Box::new(convert_expr(*e)),
        ),
        constructor::ExprKind::PairLit(a, b) => {
            ExprKind::PairLit(Box::new(convert_expr(*a)), Box::new(convert_expr(*b)))
        }
        constructor::ExprKind::Cons(h, t) => {
            ExprKind::Cons(Box::new(convert_expr(*h)), Box::new(convert_expr(*t)))
        }
        constructor::ExprKind::BinOp(op, l, r) => {
            ExprKind::BinOp(op, Box::new(convert_expr(*l)), Box::new(convert_expr(*r)))
        }
        constructor::ExprKind::RecordLit(fields) => {
            let fields = fields
                .into_iter()
                .map(|(k, v)| (k, convert_expr(v)))
                .collect();
            ExprKind::RecordLit(fields)
        }
        constructor::ExprKind::RecRecord(fields) => {
            let fields = fields
                .into_iter()
                .map(|(k, (n, v))| (k, (n, convert_expr(v))))
                .collect();
            ExprKind::RecRecord(fields)
        }
        constructor::ExprKind::FieldAccess(expr, field) => {
            ExprKind::FieldAccess(Box::new(convert_expr(*expr)), field)
        }
        constructor::ExprKind::Pack {
            tag,
            payload,
            instantiation,
        } => ExprKind::Pack {
            tag,
            payload: payload.map(|p| Box::new(convert_expr(*p))),
            instantiation,
        },
        constructor::ExprKind::Var {
            name,
            instantiation,
        } => ExprKind::Var {
            name,
            instantiation,
        },
        constructor::ExprKind::UnitLit => ExprKind::UnitLit,
        constructor::ExprKind::IntLit(x) => ExprKind::IntLit(x),
        constructor::ExprKind::FloatLit(x) => ExprKind::FloatLit(x),
        constructor::ExprKind::BoolLit(x) => ExprKind::BoolLit(x),
        constructor::ExprKind::StringLit(x) => ExprKind::StringLit(x),
        constructor::ExprKind::EmptyListLit => ExprKind::EmptyListLit,
        constructor::ExprKind::Builtin { fun, instantiation } => {
            ExprKind::Builtin { fun, instantiation }
        }
    };

    Expr { kind, ty: e.ty }
}

/// folds statements from right to left (or creates a nested tree structure)
fn convert_block(
    stmts: Vec<constructor::Stmt>,
    final_expr: Option<Box<constructor::Expr>>,
    block_ty: Rc<Type>,
) -> Expr {
    let mut current_body = match final_expr {
        Some(e) => convert_expr(*e),
        None => Expr {
            kind: ExprKind::UnitLit,
            ty: block_ty,
        },
    };

    for stmt in stmts.into_iter().rev() {
        let value = convert_expr(*stmt.value);
        let pat = stmt.pattern;

        match pat.kind {
            PatternKind::Var(name) => {
                let scheme = stmt
                    .bindings
                    .into_iter()
                    .next()
                    .expect("Var pattern must have exactly one binding")
                    .1;
                let ty = current_body.ty.clone();
                current_body = Expr {
                    kind: ExprKind::Let {
                        name,
                        scheme,
                        val: Box::new(value),
                        body: Box::new(current_body),
                    },
                    ty,
                };
            }
            _ => {
                let ty = current_body.ty.clone();
                current_body = Expr {
                    kind: ExprKind::Match(
                        Box::new(value),
                        vec![MatchBranch {
                            pattern: pat,
                            body: Box::new(current_body),
                            scrutinee_scheme: Some(stmt.scheme),
                        }],
                    ),
                    ty,
                };
            }
        }
    }

    current_body
}
