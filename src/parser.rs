use crate::lexer::Token;
use thiserror::Error;

/// A program is a list of declarations with a name and an expression.
/// In other words, a program contains declarations of the form `let name = value`.
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

pub struct Parser<'a> {
    input: &'a [Token],
    current: usize,
    must_recover: bool,
}

/// Errors that can occur during parsing.
#[derive(Error, Debug, PartialEq)]
pub enum ParseError {
    #[error("unexpected token")]
    UnexpectedToken(usize),
    #[error("unexpected eof")]
    UnexpectedEOF,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a [Token]) -> Self {
        Self {
            input,
            current: 0,
            must_recover: false,
        }
    }

    fn recover(&mut self) {
        if !self.must_recover {
            return;
        }
        
        self.current += 1;
        while self.current < self.input.len() {
            match self.input[self.current] {
                Token::Let => break,
                Token::Fn => break,
                Token::If => break,
                Token::Fix => break,
                _ => {
                    self.current += 1;
                }
            }
        }

        self.must_recover = false;
    }
}

impl<'a> Iterator for Parser<'a> {
    type Item = Result<Declaration, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.recover();
        None
    }
}
