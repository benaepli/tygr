use crate::analysis::inference::{Type, TypeKind, TypeScheme};
use crate::analysis::resolver::{CrateId, GlobalName};
use crate::builtin::BuiltinFn;
use crate::ir::decision_tree;
use crate::ir::decision_tree::ExprKind;
use crate::parser::BinOp;
use std::collections::BTreeMap;
use std::rc::Rc;

fn get_param_type(ty: &Rc<Type>) -> Rc<Type> {
    match &ty.ty {
        TypeKind::Function(param, _) => param.clone(),
        _ => panic!("get_param_type called on non-function type: {:?}", ty),
    }
}

#[derive(Debug, Clone)]
pub struct Crate {
    pub crate_id: CrateId,
    pub globals: Vec<Decl>,
    pub next_name: GlobalName,
}

#[derive(Debug, Clone)]
pub enum Decl {
    /// A monomorphic value: let x: ty = exp
    MonoVal {
        name: GlobalName,
        ty: Rc<Type>,
        expr: PrimExpr,
    },
    PolyVal {
        name: GlobalName,
        scheme: TypeScheme,
        ty: Rc<Type>,
        expr: Box<Expr>,
    },
    Rec {
        defs: Vec<Decl>,
    },
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub decls: Vec<Decl>,
    pub result: Atom, // The return value of the block
    pub ty: Rc<Type>,
}

#[derive(Debug, Clone)]
pub enum Atom {
    /// Reference to a MonoVal or a specialized PolyVal
    Var {
        name: GlobalName,
        inst: Vec<Rc<Type>>,
    },
    IntLit(i64),
    BoolLit(bool),
    FloatLit(f64),
    StringLit(String),
    UnitLit,
    EmptyListLit,
}

#[derive(Debug, Clone)]
pub struct SwitchBranch {
    pub tag: u32,
    pub body: Expr,
}

#[derive(Debug, Clone)]
pub enum PrimExpr {
    Atom(Atom),
    Pair {
        left: Atom,
        right: Atom,
    },
    Record(BTreeMap<String, Atom>),
    App {
        func: Atom,
        arg: Atom,
    },
    Lambda {
        param: GlobalName,
        param_ty: Rc<Type>,
        body: Box<Expr>,
        captures: Vec<GlobalName>,
    },
    Pack {
        tag: u32,
        instantiation: Vec<Rc<Type>>,
        payload: Option<Atom>,
    },
    BinOp(BinOp, Atom, Atom),
    Switch {
        scrutinee: Atom,
        branches: Vec<SwitchBranch>,
        default: Option<Box<Expr>>,
    },
    If(Atom, Box<Expr>, Box<Expr>),
    Cons {
        head: Atom,
        tail: Atom,
    },
    RecRecord(BTreeMap<String, (GlobalName, Atom)>),
    FieldAccess(Atom, String),
    Fst(Atom),
    Snd(Atom),
    Builtin {
        fun: BuiltinFn,
        instantiation: Vec<Rc<Type>>,
    },
    UnpackTag(Atom),
    UnpackPayload(Atom),
}

struct Converter {
    current_name: GlobalName,
}

impl Converter {
    pub fn new(base_id: GlobalName) -> Self {
        Self {
            current_name: base_id,
        }
    }

    fn new_name(&mut self) -> GlobalName {
        let id = self.current_name;
        self.current_name.name.0 += 1;
        id
    }

    pub fn lower_definition(&mut self, def: decision_tree::Def) -> Decl {
        let decision_tree::Def {
            name,
            expr,
            ty,
            scheme,
        } = def;
        let expr = Box::new(self.lower_expr(expr));
        Decl::PolyVal {
            name,
            scheme,
            ty,
            expr,
        }
    }

    fn lower_expr(&mut self, expr: decision_tree::Expr) -> Expr {
        let mut decs = Vec::new();
        let ty = expr.ty.clone();
        let result = self.lower_to_atom(&mut decs, expr);
        Expr {
            decls: decs,
            result,
            ty,
        }
    }

    fn lower_to_atom(self: &mut Self, decls: &mut Vec<Decl>, expr: decision_tree::Expr) -> Atom {
        let ty = expr.ty;
        let expr = match expr.kind {
            ExprKind::UnitLit => {
                return Atom::UnitLit;
            }
            ExprKind::IntLit(i) => {
                return Atom::IntLit(i);
            }
            ExprKind::FloatLit(f) => {
                return Atom::FloatLit(f);
            }
            ExprKind::BoolLit(b) => {
                return Atom::BoolLit(b);
            }
            ExprKind::StringLit(s) => {
                return Atom::StringLit(s);
            }
            ExprKind::EmptyListLit => {
                return Atom::EmptyListLit;
            }
            ExprKind::Var {
                name,
                instantiation: inst,
            } => {
                return Atom::Var { name, inst };
            }
            ExprKind::Let {
                name,
                scheme,
                val,
                body,
            } => {
                let ty = val.ty.clone();
                let val = self.lower_expr(*val);
                decls.push(Decl::PolyVal {
                    name,
                    scheme,
                    ty,
                    expr: Box::new(val),
                });
                return self.lower_to_atom(decls, *body);
            }
            ExprKind::PairLit(left, right) => {
                let left_atom = self.lower_to_atom(decls, *left);
                let right_atom = self.lower_to_atom(decls, *right);
                PrimExpr::Pair {
                    left: left_atom,
                    right: right_atom,
                }
            }
            ExprKind::RecordLit(fields) => {
                let atoms = fields
                    .into_iter()
                    .map(|(name, expr)| (name, self.lower_to_atom(decls, expr)))
                    .collect();
                PrimExpr::Record(atoms)
            }
            ExprKind::Lambda {
                param,
                body,
                captures,
            } => {
                let param_ty = get_param_type(&ty);
                let lowered_body = self.lower_expr(*body);
                let captures_vec = captures.into_iter().collect();
                PrimExpr::Lambda {
                    param,
                    param_ty,
                    body: Box::new(lowered_body),
                    captures: captures_vec,
                }
            }
            ExprKind::App(func, arg) => {
                let func = self.lower_to_atom(decls, *func);
                let arg = self.lower_to_atom(decls, *arg);
                PrimExpr::App { func, arg }
            }
            ExprKind::If(condition, consequent, alternative) => {
                let condition = self.lower_to_atom(decls, *condition);
                let consequent = Box::new(self.lower_expr(*consequent));
                let alternative = Box::new(self.lower_expr(*alternative));
                PrimExpr::If(condition, consequent, alternative)
            }
            ExprKind::Switch {
                scrutinee,
                branches,
                default,
            } => {
                let scrutinee_atom = self.lower_to_atom(decls, *scrutinee);
                let branches = branches
                    .into_iter()
                    .map(|b| SwitchBranch {
                        tag: b.tag,
                        body: self.lower_expr(*b.body),
                    })
                    .collect();
                let default = default.map(|d| Box::new(self.lower_expr(*d)));
                PrimExpr::Switch {
                    scrutinee: scrutinee_atom,
                    branches,
                    default,
                }
            }
            ExprKind::Cons(head, tail) => {
                let head_atom = self.lower_to_atom(decls, *head);
                let tail_atom = self.lower_to_atom(decls, *tail);
                PrimExpr::Cons {
                    head: head_atom,
                    tail: tail_atom,
                }
            }
            ExprKind::BinOp(op, left, right) => {
                let left_atom = self.lower_to_atom(decls, *left);
                let right_atom = self.lower_to_atom(decls, *right);
                PrimExpr::BinOp(op, left_atom, right_atom)
            }
            ExprKind::RecRecord(fields) => {
                let atoms = fields
                    .into_iter()
                    .map(|(name, (gname, expr))| (name, (gname, self.lower_to_atom(decls, expr))))
                    .collect();
                PrimExpr::RecRecord(atoms)
            }
            ExprKind::FieldAccess(record, field) => {
                let record_atom = self.lower_to_atom(decls, *record);
                PrimExpr::FieldAccess(record_atom, field)
            }
            ExprKind::Fst(pair) => {
                let pair_atom = self.lower_to_atom(decls, *pair);
                PrimExpr::Fst(pair_atom)
            }
            ExprKind::Snd(pair) => {
                let pair_atom = self.lower_to_atom(decls, *pair);
                PrimExpr::Snd(pair_atom)
            }
            ExprKind::Builtin { fun, instantiation } => PrimExpr::Builtin { fun, instantiation },
            ExprKind::Pack {
                tag,
                payload,
                instantiation,
            } => {
                let payload_atom = payload.map(|p| self.lower_to_atom(decls, *p));
                PrimExpr::Pack {
                    tag,
                    instantiation,
                    payload: payload_atom,
                }
            }
            ExprKind::UnpackTag(expr) => {
                let atom = self.lower_to_atom(decls, *expr);
                PrimExpr::UnpackTag(atom)
            }
            ExprKind::UnpackPayload(expr) => {
                let atom = self.lower_to_atom(decls, *expr);
                PrimExpr::UnpackPayload(atom)
            }
        };
        let name = self.new_name();
        decls.push(Decl::MonoVal { name, ty, expr });
        Atom::Var { name, inst: vec![] }
    }

    pub fn lower_cluster(&mut self, cluster: decision_tree::Cluster) -> Decl {
        match cluster {
            decision_tree::Cluster::NonRecursive(def) => self.lower_definition(def),
            decision_tree::Cluster::Recursive(defs) => {
                let lowered_defs = defs
                    .into_iter()
                    .map(|def| self.lower_definition(def))
                    .collect();
                Decl::Rec { defs: lowered_defs }
            }
        }
    }
}

pub fn lower_crate(c: decision_tree::Crate) -> Crate {
    let mut converter = Converter::new(c.next_name);
    let globals = c
        .groups
        .into_iter()
        .map(|cluster| converter.lower_cluster(cluster))
        .collect();

    Crate {
        crate_id: c.crate_id,
        globals,
        next_name: converter.current_name,
    }
}
