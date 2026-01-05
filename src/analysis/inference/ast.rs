use crate::analysis::name_table::NameTable;
use crate::analysis::resolver::{CrateId, GlobalName, GlobalType, TypeName};
use crate::builtin::BuiltinFn;
use crate::ir::direct::closure::VariantDef;
use crate::parser::{BinOp, Span};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Kind {
    Star,
    Arrow(Rc<Kind>, Rc<Kind>),
    Var(KindID),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct KindID(pub usize);

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize, PartialOrd, Ord,
)]
pub struct TypeID(pub usize);

impl fmt::Display for TypeID {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct TypeScheme {
    pub vars: Vec<(TypeID, Rc<Kind>)>,
    pub ty: Rc<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Type {
    pub ty: TypeKind,
    pub kind: Rc<Kind>,
}

impl Type {
    pub fn new(ty: TypeKind, kind: Rc<Kind>) -> Rc<Self> {
        Rc::new(Self { ty, kind })
    }

    pub fn simple(name: TypeName) -> Rc<Self> {
        Self::new(
            TypeKind::Con(GlobalType { krate: None, name }),
            Rc::new(Kind::Star),
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum TypeKind {
    Var(TypeID),
    Con(GlobalType),
    App(Rc<Type>, Rc<Type>),
    AliasHead(GlobalType, Vec<Rc<Type>>), // alias name and args applied so far

    Function(Rc<Type>, Rc<Type>),
    Pair(Rc<Type>, Rc<Type>),
    Record(BTreeMap<String, Rc<Type>>),
}

pub struct TypeDisplay<'a> {
    pub ty: Rc<Type>,
    pub name_table: &'a NameTable,
}

impl<'a> TypeDisplay<'a> {
    pub fn new(ty: Rc<Type>, name_table: &'a NameTable) -> Self {
        Self { ty, name_table }
    }
}

impl<'a> fmt::Display for TypeDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.ty.as_ref().ty {
            TypeKind::Var(id) => write!(f, "{}", id),
            TypeKind::Con(id) => write!(f, "{}", self.name_table.lookup_type_name(id)),
            TypeKind::App(lhs, rhs) => {
                let lhs_display = TypeDisplay::new(lhs.clone(), self.name_table);
                let rhs_display = TypeDisplay::new(rhs.clone(), self.name_table);
                write!(f, "{}[{}]", lhs_display, rhs_display)
            }
            TypeKind::AliasHead(gt, args) => {
                write!(f, "{}", self.name_table.lookup_type_name(gt))?;
                for arg in args {
                    let arg_display = TypeDisplay::new(arg.clone(), self.name_table);
                    write!(f, "[{}]", arg_display)?;
                }
                Ok(())
            }
            TypeKind::Pair(a, b) => {
                let a_display = TypeDisplay::new(a.clone(), self.name_table);
                let b_display = TypeDisplay::new(b.clone(), self.name_table);
                write!(f, "({} * {})", a_display, b_display)
            }
            TypeKind::Function(arg, ret) => {
                let arg_display = TypeDisplay::new(arg.clone(), self.name_table);
                let ret_display = TypeDisplay::new(ret.clone(), self.name_table);
                match arg.as_ref().ty {
                    TypeKind::Function(_, _) => write!(f, "({}) -> {}", arg_display, ret_display),
                    _ => write!(f, "{} -> {}", arg_display, ret_display),
                }
            }
            TypeKind::Record(fields) => {
                write!(f, "{{ ")?;
                let mut first = true;
                for (name, ty) in fields {
                    if !first {
                        write!(f, ", ")?;
                    }
                    let ty_display = TypeDisplay::new(ty.clone(), self.name_table);
                    write!(f, "{}: {}", name, ty_display)?;
                    first = false;
                }
                write!(f, " }}")
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypedPattern {
    pub kind: TypedPatternKind,
    pub ty: Rc<Type>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum TypedPatternKind {
    Var { name: GlobalName },
    Unit,
    Pair(Box<TypedPattern>, Box<TypedPattern>),
    Wildcard,
    Cons(Box<TypedPattern>, Box<TypedPattern>),
    EmptyList,
    Record(BTreeMap<String, TypedPattern>),
    Constructor(GlobalType, GlobalName, Option<Box<TypedPattern>>),
}

#[derive(Debug, Clone)]
pub struct TypedMatchPattern {
    pub pattern: TypedPattern,
    pub expr: Box<Typed>,
    pub ty: Rc<Type>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum TypedGroup {
    NonRecursive(TypedDefinition),
    Recursive(Vec<TypedDefinition>),
}

/// A typed crate ready for code generation.
#[derive(Debug, Clone)]
pub struct TypedCrate {
    pub crate_id: CrateId,
    pub groups: Vec<TypedGroup>,
    pub variants: Vec<VariantDef>,
}

#[derive(Debug, Clone)]
pub struct TypedDefinition {
    pub name: (GlobalName, String),
    pub expr: Box<Typed>,
    pub ty: Rc<Type>,
    pub scheme: TypeScheme,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct TypedStatement {
    pub pattern: TypedPattern,
    pub value: Box<Typed>,
    pub ty: Rc<Type>,
    pub scheme: TypeScheme,
    pub bindings: Vec<(GlobalName, TypeScheme)>, // Maps names bound in the pattern to a scheme
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Typed {
    pub kind: TypedKind,
    pub ty: Rc<Type>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum TypedKind {
    Var {
        name: GlobalName,
        /// The concrete types applied to the generic parameters of the variable's scheme.
        instantiation: Vec<Rc<Type>>,
    },
    Lambda {
        param: TypedPattern,
        body: Box<Typed>,
        captures: HashSet<GlobalName>,
    },
    App(Box<Typed>, Box<Typed>),
    If(Box<Typed>, Box<Typed>, Box<Typed>),
    Match(Box<Typed>, Vec<TypedMatchPattern>),
    Block(Vec<TypedStatement>, Option<Box<Typed>>),
    Cons(Box<Typed>, Box<Typed>),

    UnitLit,
    PairLit(Box<Typed>, Box<Typed>),
    IntLit(i64),
    FloatLit(f64),
    BoolLit(bool),
    StringLit(String),
    EmptyListLit,
    RecordLit(BTreeMap<String, Typed>),

    BinOp(BinOp, Box<Typed>, Box<Typed>),
    RecRecord(BTreeMap<String, (GlobalName, Typed)>),
    FieldAccess(Box<Typed>, String),

    Builtin {
        fun: BuiltinFn,
        instantiation: Vec<Rc<Type>>,
    },
    Constructor {
        variant: GlobalType,
        ctor: GlobalName,
        nullary: bool,
        instantiation: Vec<Rc<Type>>,
    },
}

#[derive(Debug, Clone)]
pub struct TypedVariant {
    pub schemes: HashMap<GlobalName, TypeScheme>,
    pub ty: Rc<Type>,
    pub definition: VariantDef,
}
