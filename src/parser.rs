/// A program is a list of declarations with a name and an expression.
/// In other words, each declaration is of the form `let name = value`.
pub struct Declaration {
    pub name: String,
    pub value: Expr,
}

pub enum BinOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Equal,
    NotEqual,
    LessEqual,
    GreaterEqual,
    Less,
    Greater,
}

pub enum Expr {
    Var(String),
    Lambda(String, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
    Fix(Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),

    IntLit(i64),
    DoubleLit(f64),
    BoolLit(bool),

    BinOp(BinOp, Box<Expr>, Box<Expr>),
}

pub struct Parser {}
