use chumsky::prelude::SimpleSpan;
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct SourceId(pub usize);

impl SourceId {
    pub const SYNTHETIC: SourceId = SourceId(0);
}

pub type Span = SimpleSpan<usize, SourceId>;

#[derive(Debug, Clone, PartialEq)]
pub enum BinOp {
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq)]
pub enum PatternKind {
    Var(String),
    Unit,
    Pair(Box<Pattern>, Box<Pattern>),
    Wildcard,
    Cons(Box<Pattern>, Box<Pattern>),
    EmptyList,
    Record(Vec<(String, Pattern)>),
    Constructor(String, Option<Box<Pattern>>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}

impl Pattern {
    pub(crate) fn new(kind: PatternKind, span: Span) -> Self {
        Pattern { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum AnnotationKind {
    Var(Path),
    App(Box<Annotation>, Box<Annotation>),
    Pair(Box<Annotation>, Box<Annotation>),
    Lambda(Box<Annotation>, Box<Annotation>),
    Record(Vec<(String, Annotation)>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Annotation {
    pub kind: AnnotationKind,
    pub span: Span,
}

impl Annotation {
    pub(crate) fn new(kind: AnnotationKind, span: Span) -> Self {
        Annotation { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Generic {
    pub name: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeAlias {
    pub name: String,
    pub vis: Visibility,
    pub generics: Vec<Generic>,
    pub body: Annotation,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Constructor {
    pub annotation: Option<Annotation>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Variant {
    pub name: String,
    pub vis: Visibility,
    pub generics: Vec<Generic>,
    pub constructors: Vec<(String, Constructor)>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ReplStatement {
    Statement(Statement),
    Variant(Variant),
    Type(TypeAlias),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Definition {
    pub name: String,
    pub vis: Visibility,
    pub expr: Expr,
    pub generics: Vec<Generic>,
    pub annotation: Option<Annotation>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum PathBase {
    Crate,
    Super(usize),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Visibility {
    Public,
    Private,
}

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub struct Path {
    pub base: Option<PathBase>,
    pub segments: Vec<String>,
    pub span: Span,
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.base {
            Some(PathBase::Crate) => write!(f, "crate::")?,
            Some(PathBase::Super(n)) => {
                for _ in 0..*n {
                    write!(f, "super::")?;
                }
            }
            None => {}
        }
        write!(f, "{}", self.segments.join("::"))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Declaration {
    Def(Definition),
    Variant(Variant),
    Type(TypeAlias),
    Module(ModuleDecl),
    Use(UseDecl),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ModuleDecl {
    pub name: String,
    pub vis: Visibility,
    // None = "mod foo", Some = "mod foo { ... }"
    pub body: Option<Vec<Declaration>>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct UseDecl {
    pub path: Path,
    pub alias: Option<String>, // use a::b as c
    pub vis: Visibility,       // pub use a::b
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchBranch {
    pub pattern: Pattern,
    pub expr: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum StatementKind {
    Let(Pattern, Box<Expr>, Vec<Generic>, Option<Annotation>),
    Expr(Box<Expr>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Statement {
    pub kind: StatementKind,
    pub span: Span,
}

impl Statement {
    pub(crate) fn new(kind: StatementKind, span: Span) -> Self {
        Statement { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

impl Expr {
    pub(crate) fn new(kind: ExprKind, span: Span) -> Self {
        Expr { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    Var(Path),
    Lambda(Pattern, Box<Expr>, Option<Annotation>), // Annotation is for the parameter type.
    App(Box<Expr>, Box<Expr>),
    Let(
        Pattern,
        Box<Expr>,
        Box<Expr>,
        Vec<Generic>,
        Option<Annotation>,
    ),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<MatchBranch>),
    Block(Vec<Statement>, Option<Box<Expr>>),

    UnitLit,
    PairLit(Box<Expr>, Box<Expr>),
    IntLit(i64),
    FloatLit(f64),
    BoolLit(bool),
    StringLit(String),
    EmptyListLit,
    RecordLit(Vec<(String, Expr)>),

    BinOp(BinOp, Box<Expr>, Box<Expr>),
    RecRecord(Vec<(String, Expr)>),
    Cons(Box<Expr>, Box<Expr>),
    FieldAccess(Box<Expr>, String),
}
