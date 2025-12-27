use crate::analysis::inference::{Type, TypeID};
use crate::analysis::resolver::{Name, TypeName};
use crate::builtin::BuiltinFn;
use crate::parser::BinOp;
use std::collections::BTreeMap;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct Program {
    pub clusters: Vec<Cluster>,
    pub structs: Vec<StructDef>,
    pub functions: Vec<FuncDef>,
    pub globals: Vec<GlobalDef>,
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
    pub type_params: Vec<TypeID>,
    pub fields: Vec<(Name, Rc<Type>)>,
}

#[derive(Debug, Clone)]
pub struct FuncDef {
    pub name: Name,
    pub type_params: Vec<TypeID>,
    pub param: Name,
    pub env_param: Name,
    pub env_struct: TypeName,
    pub body: Expr,
    pub ret_ty: Rc<Type>,
}

#[derive(Debug, Clone)]
pub struct GlobalDef {
    pub name: Name,
    pub ty: Rc<Type>,
    pub val: Expr,
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub ty: Rc<Type>,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Let { name: Name, val: Expr },
    Expr(Expr),
}

#[derive(Debug, Clone)]
pub struct SwitchBranch {
    pub tag: u32,
    pub body: Box<Expr>,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Local(Name),
    Global(Name),
    EnvAccess {
        field: Name,
    },
    MakeClosure {
        fn_ref: Name,
        env_struct: TypeName,
        captures: Vec<(Name, Expr)>,
    },
    CallClosure {
        closure: Box<Expr>,
        arg: Box<Expr>,
    },
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Switch {
        scrutinee: Box<Expr>,
        branches: Vec<SwitchBranch>,
        default: Option<Box<Expr>>,
    },
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

    Pack {
        tag: u32,
        payload: Option<Box<Expr>>,
    },
    UnpackTag(Box<Expr>),
    UnpackPayload(Box<Expr>),
}
