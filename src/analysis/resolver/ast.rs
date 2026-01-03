use crate::builtin::BuiltinFn;
use crate::driver::{CrateId, ModuleId};
use crate::parser::{BinOp, Span, Visibility};
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub struct Name(pub usize);

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize, PartialOrd, Ord,
)]
pub struct TypeName(pub usize);

impl fmt::Display for TypeName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedConstructor {
    pub annotation: Option<ResolvedAnnotation>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedVariant {
    pub name: TypeName,
    pub type_params: Vec<TypeName>,
    pub constructors: HashMap<Name, ResolvedConstructor>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedDefinition {
    pub name: (Name, String),
    pub expr: Box<Resolved>,
    pub generics: Vec<TypeName>,
    pub annotation: Option<ResolvedAnnotation>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ResolvedPatternKind {
    Var(Name),
    Unit,
    Pair(Box<ResolvedPattern>, Box<ResolvedPattern>),
    Wildcard,
    Cons(Box<ResolvedPattern>, Box<ResolvedPattern>),
    EmptyList,
    Record(HashMap<String, ResolvedPattern>),
    Constructor(TypeName, Name, Option<Box<ResolvedPattern>>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedPattern {
    pub kind: ResolvedPatternKind,
    pub span: Span,
}

impl ResolvedPattern {
    fn new(kind: ResolvedPatternKind, span: Span) -> Self {
        ResolvedPattern { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedMatchBranch {
    pub pattern: ResolvedPattern,
    pub expr: Box<Resolved>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Resolved {
    pub kind: ResolvedKind,
    pub span: Span,
}

impl Resolved {
    fn new(kind: ResolvedKind, span: Span) -> Self {
        Resolved { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ResolvedAnnotationKind {
    Var(TypeName),
    Alias(String),
    App(Box<ResolvedAnnotation>, Box<ResolvedAnnotation>),
    Pair(Box<ResolvedAnnotation>, Box<ResolvedAnnotation>),
    Lambda(Box<ResolvedAnnotation>, Box<ResolvedAnnotation>),
    Record(HashMap<String, ResolvedAnnotation>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedAnnotation {
    pub kind: ResolvedAnnotationKind,
    pub span: Span,
}

impl ResolvedAnnotation {
    fn new(kind: ResolvedAnnotationKind, span: Span) -> Self {
        ResolvedAnnotation { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedStatement {
    pub pattern: ResolvedPattern,
    pub value: Box<Resolved>,
    pub value_type: Option<ResolvedAnnotation>,
    pub type_params: Vec<TypeName>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ResolvedKind {
    Var(Name),
    Lambda {
        param: ResolvedPattern,
        body: Box<Resolved>,
        captures: HashSet<Name>,
        param_type: Option<ResolvedAnnotation>,
    },
    App(Box<Resolved>, Box<Resolved>),
    If(Box<Resolved>, Box<Resolved>, Box<Resolved>),
    Match(Box<Resolved>, Vec<ResolvedMatchBranch>),
    Block(Vec<ResolvedStatement>, Option<Box<Resolved>>),
    Cons(Box<Resolved>, Box<Resolved>),

    UnitLit,
    PairLit(Box<Resolved>, Box<Resolved>),
    IntLit(i64),
    FloatLit(f64),
    BoolLit(bool),
    StringLit(String),
    EmptyListLit,
    RecordLit(HashMap<String, Resolved>),

    BinOp(BinOp, Box<Resolved>, Box<Resolved>),
    RecRecord(HashMap<String, (Name, Resolved)>),
    FieldAccess(Box<Resolved>, String),

    Builtin(BuiltinFn),
    Constructor(TypeName, Name),
}

impl ResolvedKind {
    pub fn is_syntactic_value(&self) -> bool {
        match self {
            ResolvedKind::Var(_)
            | ResolvedKind::Lambda { .. }
            | ResolvedKind::IntLit(_)
            | ResolvedKind::FloatLit(_)
            | ResolvedKind::BoolLit(_)
            | ResolvedKind::StringLit(_)
            | ResolvedKind::UnitLit
            | ResolvedKind::EmptyListLit
            | ResolvedKind::Constructor(_, _) => true,

            ResolvedKind::PairLit(a, b) => {
                a.kind.is_syntactic_value() && b.kind.is_syntactic_value()
            }
            ResolvedKind::Cons(h, t) => h.kind.is_syntactic_value() && t.kind.is_syntactic_value(),
            ResolvedKind::RecordLit(fields) => fields.values().all(|v| v.kind.is_syntactic_value()),

            ResolvedKind::App(_, _)
            | ResolvedKind::If(_, _, _)
            | ResolvedKind::Match(_, _)
            | ResolvedKind::Block(_, _)
            | ResolvedKind::BinOp(_, _, _)
            | ResolvedKind::Builtin(_)
            | ResolvedKind::FieldAccess(_, _) => false,
            ResolvedKind::RecRecord(_) => true,
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeAliasEntry {
    pub generics: Vec<TypeName>,
    pub body: ResolvedAnnotation,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedModuleData {
    pub id: ModuleId,
    pub parent: Option<ModuleId>,

    pub definitions: HashMap<String, (Resolution, Visibility)>,
    pub modules: HashMap<String, (Resolution, Visibility)>,
    pub types: HashMap<String, (Resolution, Visibility)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Resolution {
    Def(Name),
    Module(ModuleId),
    Type(TypeName),
    Crate(CrateId),
}

pub struct CrateGraph {
    pub crates: HashMap<CrateId, DefMap>,
    pub dependencies: HashMap<CrateId, Vec<(String, CrateId)>>,
}

pub struct DefMap {
    pub crate_id: CrateId,
    pub modules: Vec<ResolvedModuleData>,
    pub root: ModuleId,

    pub extern_prelude: HashMap<String, CrateId>,
}
