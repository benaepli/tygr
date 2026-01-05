use crate::analysis::inference::{Type, TypeID};
use crate::analysis::resolver::GlobalName;
use crate::parser::BinOp;
use std::collections::BTreeMap;
use std::rc::Rc;

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
        tyvars: Vec<TypeID>,
        ty: Rc<Type>,
        expr: Box<XmlExpr>,
    },
}

#[derive(Debug, Clone)]
pub struct XmlExpr {
    pub decs: Vec<Decl>,
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
pub struct XmlSwitchBranch {
    pub tag: u32,
    pub body: XmlExpr,
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
        body: Box<XmlExpr>,
    },
    Pack {
        tag: u32,
        instantiation: Vec<Rc<Type>>,
        payload: Option<Atom>,
    },
    BinOp(BinOp, Atom, Atom),
    Switch {
        scrutinee: Atom,
        branches: Vec<XmlSwitchBranch>,
        default: Option<Box<XmlExpr>>,
    },
}
