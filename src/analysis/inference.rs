use crate::analysis::resolver::{Name, Resolved};
use crate::parser::{BinOp, UnaryOp};
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::rc::Rc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeID(pub usize);

#[derive(Debug, Clone)]
pub struct TypeScheme {
    pub vars: Vec<TypeID>,
    pub ty: Rc<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Int,
    Double,
    Bool,
    Var(TypeID),
    Function(Rc<Type>, Rc<Type>),
}

pub struct Typed {
    pub kind: TypedKind,
    pub ty: Rc<Type>,
}

pub enum TypedKind {
    Var(Name),
    Lambda {
        param: Name,
        body: Box<Typed>,
        captures: HashSet<Name>,
    },
    App(Box<Typed>, Box<Typed>),
    Let {
        name: Name,
        value: Box<Typed>,
        body: Box<Typed>,
    },
    Fix(Box<Typed>),
    If(Box<Typed>, Box<Typed>, Option<Box<Typed>>),

    IntLit(i64),
    DoubleLit(f64),
    BoolLit(bool),

    BinOp(BinOp, Box<Typed>, Box<Typed>),
    UnaryOp(UnaryOp, Box<Typed>),
}

type Environment = HashMap<Name, TypeScheme>;
type Substitution = HashMap<TypeID, Rc<Type>>;

pub struct Inferrer {
    next_var: TypeID,
}

impl Inferrer {
    fn new_type(&mut self) -> Rc<Type> {
        let id = self.next_var.0;
        self.next_var.0 += 1;
        Rc::new(Type::Var(TypeID(id)))
    }
}
