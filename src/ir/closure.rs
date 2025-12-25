use crate::analysis::inference::{Type, TypeID, TypeKind};
use crate::analysis::resolver::{Name, TypeName};
use crate::builtin::BuiltinFn;
use crate::parser::BinOp;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone)]
pub struct Program {
    pub clusters: Vec<Cluster>,
}

#[derive(Debug, Clone)]
pub enum Cluster {
    Recursive(Vec<Definition>),
    NonRecursive(Definition),
}

#[derive(Debug, Clone)]
pub enum Definition {
    Struct(StructDef),
    Function(FuncDef),
    Global(GlobalDef),
}

#[derive(Debug, Clone)]
pub struct StructDef {
    pub name: TypeName,
    pub fields: Vec<(String, Type)>,
}

#[derive(Debug, Clone)]
pub struct FuncDef {
    pub name: Name,
    pub param: Name,
    pub env_param: Name,      // The name given to the self/env pointer
    pub env_struct: TypeName, // The specific struct type this function expects
    pub body: Expr,
    pub ret_ty: Type,
}

#[derive(Debug, Clone)]
pub struct GlobalDef {
    pub name: Name,
    pub ty: Type,
    pub val: Expr,
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct Stmt {
    pub pattern: Pattern,
    pub value: Box<Expr>,
}

#[derive(Debug, Clone)]
pub struct MatchBranch {
    pub pattern: Pattern,
    pub body: Box<Expr>,
}

#[derive(Debug, Clone)]
pub struct Pattern {
    pub kind: PatternKind,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub enum PatternKind {
    Var(Name),
    Unit,
    Pair(Box<Pattern>, Box<Pattern>),
    Wildcard,
    Cons(Box<Pattern>, Box<Pattern>),
    EmptyList,
    Record(BTreeMap<String, Pattern>),
    Constructor(TypeName, Name, Box<Pattern>),
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Local(Name),
    Global(Name),
    EnvAccess {
        field: String,
    },
    MakeClosure {
        fn_ref: Name,
        env_struct: TypeName,
        captures: Vec<(String, Expr)>,
    },
    CallClosure {
        closure: Box<Expr>,
        arg: Box<Expr>,
    },

    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<MatchBranch>),
    Block(Vec<Stmt>, Option<Box<Expr>>),

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
    RecRecord(BTreeMap<String, (Name, Expr)>),
    FieldAccess(Box<Expr>, String),

    Builtin(BuiltinFn),
    Constructor(TypeName, Name),
}

fn collect_free_type_vars(ty: &Type, set: &mut BTreeSet<TypeID>) {
    match &ty.ty {
        TypeKind::Var(id) => {
            set.insert(*id);
        }
        TypeKind::App(lhs, rhs) => {
            collect_free_type_vars(lhs, set);
            collect_free_type_vars(rhs, set);
        }
        TypeKind::Function(arg, ret) => {
            collect_free_type_vars(arg, set);
            collect_free_type_vars(ret, set);
        }
        TypeKind::Pair(a, b) => {
            collect_free_type_vars(a, set);
            collect_free_type_vars(b, set);
        }
        TypeKind::Record(fields) => {
            for t in fields.values() {
                collect_free_type_vars(t, set);
            }
        }
        TypeKind::Con(_) => {}
    }
}
