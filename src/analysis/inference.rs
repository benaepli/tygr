use crate::analysis::resolver::{Name, Resolved};
use crate::builtin::BuiltinFn;
use crate::parser::BinOp;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::ops::Sub;
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
    Float,
    Bool,
    String,
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
    If(Box<Typed>, Box<Typed>, Box<Typed>),

    IntLit(i64),
    FloatLit(f64),
    BoolLit(bool),
    StringLit(String),

    BinOp(BinOp, Box<Typed>, Box<Typed>),

    Builtin(BuiltinFn),
}

type Environment = HashMap<Name, TypeScheme>;
type Substitution = HashMap<TypeID, Rc<Type>>;

pub struct Inferrer {
    substitution: Substitution,
    next_var: TypeID,
}

#[derive(Debug)]
pub enum TypeError {
    Mismatch(Rc<Type>, Rc<Type>),
    OccursCheck(TypeID, Rc<Type>),
    UnboundVariable(Name),
}

impl Inferrer {
    pub fn new() -> Self {
        let inferrer = Self {
            substitution: HashMap::new(),
            next_var: TypeID(0),
        };
        

        inferrer
    }

    fn new_type(&mut self) -> Rc<Type> {
        let id = self.next_var.0;
        self.next_var.0 += 1;
        Rc::new(Type::Var(TypeID(id)))
    }

    fn infer(&mut self, env: &Environment, expr: Resolved) -> Result<Typed, TypeError> {
        todo!()
    }
}
