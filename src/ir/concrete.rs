use crate::analysis::resolver::{Name, TypeName};
use crate::builtin::BuiltinFn;
use crate::parser::{BinOp, Span};
use std::collections::{BTreeMap, HashSet};
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum ConcreteType {
    Con(TypeName),
    App(Rc<ConcreteType>, Rc<ConcreteType>),
    Function(Rc<ConcreteType>, Rc<ConcreteType>),
    Pair(Rc<ConcreteType>, Rc<ConcreteType>),
    Record(BTreeMap<String, Rc<ConcreteType>>),
}

impl ConcreteType {
    pub fn simple(name: TypeName) -> Rc<Self> {
        Rc::new(Self::Con(name))
    }
}

#[derive(Debug, Clone)]
pub struct ConcretePattern {
    pub kind: ConcretePatternKind,
    pub ty: Rc<ConcreteType>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ConcretePatternKind {
    Var { name: Name },
    Unit,
    Pair(Box<ConcretePattern>, Box<ConcretePattern>),
    Wildcard,
    Cons(Box<ConcretePattern>, Box<ConcretePattern>),
    EmptyList,
    Record(BTreeMap<String, ConcretePattern>),
    Constructor(TypeName, Name, Box<ConcretePattern>),
}

#[derive(Debug, Clone)]
pub struct ConcreteMatchPattern {
    pub pattern: ConcretePattern,
    pub expr: Box<ConcreteTyped>,
    pub ty: Rc<ConcreteType>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ConcreteGroup {
    NonRecursive(ConcreteDefinition),
    Recursive(Vec<ConcreteDefinition>),
}

#[derive(Debug, Clone)]
pub struct ConcreteDefinition {
    pub name: (Name, String),
    pub expr: Box<ConcreteTyped>,
    pub ty: Rc<ConcreteType>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ConcreteStatementKind {
    Let {
        pattern: ConcretePattern,
        value: Box<ConcreteTyped>,
    },
    Expr(Box<ConcreteTyped>),
}

#[derive(Debug, Clone)]
pub struct ConcreteStatement {
    pub kind: ConcreteStatementKind,
    pub ty: Rc<ConcreteType>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ConcreteTyped {
    pub kind: ConcreteTypedKind,
    pub ty: Rc<ConcreteType>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ConcreteTypedKind {
    Var(Name),
    Lambda {
        param: ConcretePattern,
        body: Box<ConcreteTyped>,
        captures: HashSet<Name>,
    },
    App(Box<ConcreteTyped>, Box<ConcreteTyped>),
    Let {
        name: ConcretePattern,
        value: Box<ConcreteTyped>,
        body: Box<ConcreteTyped>,
    },
    If(Box<ConcreteTyped>, Box<ConcreteTyped>, Box<ConcreteTyped>),
    Match(Box<ConcreteTyped>, Vec<ConcreteMatchPattern>),
    Block(Vec<ConcreteStatement>, Option<Box<ConcreteTyped>>),
    Cons(Box<ConcreteTyped>, Box<ConcreteTyped>),
    UnitLit,
    PairLit(Box<ConcreteTyped>, Box<ConcreteTyped>),
    IntLit(i64),
    FloatLit(f64),
    BoolLit(bool),
    StringLit(String),
    EmptyListLit,
    RecordLit(BTreeMap<String, ConcreteTyped>),
    BinOp(BinOp, Box<ConcreteTyped>, Box<ConcreteTyped>),
    RecRecord(BTreeMap<String, (Name, ConcreteTyped)>),
    FieldAccess(Box<ConcreteTyped>, String),
    Builtin(BuiltinFn),
    Constructor(TypeName, Name),
}
