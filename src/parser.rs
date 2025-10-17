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
    And,
    Or,
}

fn to_op(token: &Token) -> BinOp {
    match token {
        Token::Plus => BinOp::Add,
        Token::Minus => BinOp::Subtract,
        Token::Star => BinOp::Multiply,
        Token::Slash => BinOp::Divide,
        Token::EqualEqual => BinOp::Equal,
        Token::BangEqual => BinOp::NotEqual,
        Token::Less => BinOp::LessEqual,
        Token::Greater => BinOp::Greater,
        Token::LessEqual => BinOp::LessEqual,
        Token::GreaterEqual => BinOp::GreaterEqual,
        Token::And => BinOp::And,
        Token::Or => BinOp::Or,
        _ => panic!("no valid token conversion found"),
    }
}

pub enum UnaryOp {
    Negate,
    Not,
}

pub enum Expr {
    Var(String),
    Lambda(String, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
    Fix(Box<Expr>),
    If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),

    IntLit(i64),
    DoubleLit(f64),
    BoolLit(bool),

    BinOp(BinOp, Box<Expr>, Box<Expr>),
    UnaryOp(UnaryOp, Box<Expr>)
}

pub struct Parser<'a> {
    input: &'a [Token],
    current: usize,
    must_recover: bool,
}

/// Errors that can occur during parsing.
#[derive(Error, Debug, PartialEq)]
pub enum ParseError {
    #[error("expected let")]
    ExpectedLet(usize),
    #[error("expected identifier")]
    ExpectedIdentifier(usize),
    #[error("expected assignment")]
    ExpectedAssignment(usize),
    #[error("expected in")]
    ExpectedIn(usize),
    #[error("expected then")]
    ExpectedThen(usize),
    #[error("expected lambda operator")]
    ExpectedLambda(usize),
    #[error("expected right parenthesis")]
    ExpectedRightParen,
    #[error("unexpected token")]
    UnexpectedToken,
}

fn is_unary_start(token: &Token) -> bool {
    match token {
        Token::LeftParen
        | Token::Identifier(_)
        | Token::Bang
        | Token::Minus
        | Token::Integer(_)
        | Token::Double(_) => true,
        _ => false,
    }
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a [Token]) -> Self {
        Self {
            input,
            current: 0,
            must_recover: false,
        }
    }

    fn peek(&self) -> Option<&Token> {
        self.input.get(self.current)
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

    fn expr(&mut self) -> Result<Expr, ParseError> {
        match self.peek() {
            Some(Token::Let) => self.let_expr(),
            Some(Token::If) => self.if_expr(),
            Some(Token::Lambda) => self.lambda_expr(),
            _ => self.expr_or(),
        }
    }

    fn let_expr(&mut self) -> Result<Expr, ParseError> {
        self.current += 1;

        let id = match self.peek() {
            Some(Token::Identifier(id)) => id.clone(),
            _ => return Err(ParseError::ExpectedIdentifier(self.current)),
        };
        self.current += 1;

        let e1 = self.expr()?;
        match self.peek() {
            Some(Token::In) => self.current += 1,
            _ => return Err(ParseError::ExpectedIn(self.current)),
        }
        let e2 = self.expr()?;
        Ok(Expr::Let(id, Box::new(e1), Box::new(e2)))
    }

    fn if_expr(&mut self) -> Result<Expr, ParseError> {
        self.current += 1;

        let cnd = self.expr()?;
        match self.peek() {
            Some(Token::Then) => {
                self.current += 1;
            }
            _ => return Err(ParseError::ExpectedThen(self.current)),
        }
        let csq = self.expr()?;
        let alt = match self.peek() {
            Some(Token::Else) => {
                self.current += 1;
                Some(Box::new(self.expr()?))
            }
            _ => None,
        };
        Ok(Expr::If(Box::new(cnd), Box::new(csq), alt))
    }

    fn lambda_expr(&mut self) -> Result<Expr, ParseError> {
        self.current += 1;

        let identifier = match self.peek() {
            Some(Token::Identifier(id)) => id.clone(),
            _ => return Err(ParseError::ExpectedIdentifier(self.current)),
        };
        self.current += 1;

        match self.peek() {
            Some(Token::Lambda) => {
                self.current += 1;
            }
            _ => return Err(ParseError::ExpectedLambda(self.current)),
        }
        Ok(Expr::Lambda(identifier, Box::new(self.expr()?)))
    }

    fn expr_or(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.expr_and()?;
        loop {
            match self.peek() {
                Some(Token::Or) => {
                    self.current += 1;
                }
                _ => return Ok(left),
            }
            let right = self.expr_and()?;
            left = Expr::BinOp(BinOp::Or, Box::new(left), Box::new(right));
        }
    }

    fn expr_and(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.expr_compare()?;
        loop {
            match self.peek() {
                Some(Token::And) => {
                    self.current += 1;
                }
                _ => return Ok(left),
            }
            let right = self.expr_compare()?;
            left = Expr::BinOp(BinOp::And, Box::new(left), Box::new(right));
        }
    }

    fn expr_compare(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.expr_term()?;
        loop {
            let op = match self.peek() {
                Some(Token::EqualEqual)
                | Some(Token::GreaterEqual)
                | Some(Token::LessEqual)
                | Some(Token::Greater)
                | Some(Token::Less) => {
                    let op = to_op(self.peek().unwrap());
                    self.current += 1;
                    op
                }
                _ => return Ok(left),
            };
            let right = self.expr_term()?;
            left = Expr::BinOp(op, Box::new(left), Box::new(right));
        }
    }

    fn expr_term(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.expr_factor()?;
        loop {
            let op = match self.peek() {
                Some(Token::Plus) | Some(Token::Minus) => {
                    let op = to_op(self.peek().unwrap());
                    self.current += 1;
                    op
                }
                _ => return Ok(left),
            };
            let right = self.expr_factor()?;
            left = Expr::BinOp(op, Box::new(left), Box::new(right));
        }
    }

    fn expr_factor(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.expr_apply()?;
        loop {
            let op = match self.peek() {
                Some(Token::Star) | Some(Token::Slash) => {
                    let op = to_op(self.peek().unwrap());
                    self.current += 1;
                    op
                }
                _ => return Ok(left),
            };
            let right = self.expr_apply()?;
            left = Expr::BinOp(op, Box::new(left), Box::new(right));
        }
    }

    fn expr_apply(&mut self) -> Result<Expr, ParseError> {
        let mut left = match self.peek() {
            Some(Token::Fix) => {
                self.current += 1;
                Expr::Fix(Box::new(self.expr_unary()?))
            }
            _ => self.expr_unary()?,
        };
        loop {
            match self.peek() {
                Some(token) if is_unary_start(token) => {
                    left = Expr::App(Box::new(left), Box::new(self.expr_unary()?));
                }
                _ => return Ok(left),
            }
        }
    }

    fn expr_unary(&mut self) -> Result<Expr, ParseError> {
        match self.peek() {
            Some(Token::Minus) => {
                self.current += 1;
                Ok(Expr::UnaryOp(UnaryOp::Negate, Box::new(self.expr_simple()?)))
            }
            Some(Token::Bang) => {
                self.current += 1;
                Ok(Expr::UnaryOp(UnaryOp::Not, Box::new(self.expr_simple()?)))
            }
            _ => self.expr_simple(),
        }
    }
    
    fn expr_simple(&mut self) -> Result<Expr, ParseError> {
        match self.peek() {
            Some(Token::Integer(i)) => Ok(Expr::IntLit(*i)),
            Some(Token::Boolean(b)) => Ok(Expr::BoolLit(*b)),
            Some(Token::Double(d)) => Ok(Expr::DoubleLit(*d)),
            Some(Token::Identifier(s)) => Ok(Expr::Var(s.clone())),
            Some(Token::LeftParen) => {
                self.current += 1;
                let expr = self.expr()?;
                match self.peek() {
                    Some(Token::RightParen) => {
                        self.current += 1;
                        Ok(expr)
                    }
                    _ => Err(ParseError::ExpectedRightParen),
                }
            }
            _ => Err(ParseError::UnexpectedToken)
        }
    }
}

impl<'a> Iterator for Parser<'a> {
    type Item = Result<Declaration, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.recover();

        match self.peek() {
            None => return None,
            Some(Token::Let) => {
                self.current += 1;
            }
            _ => return Some(Err(ParseError::ExpectedLet(self.current))),
        }

        let identifier = match self.peek() {
            Some(Token::Identifier(id)) => id.clone(),
            _ => return Some(Err(ParseError::ExpectedIdentifier(self.current))),
        };
        self.current += 1;

        match self.peek() {
            Some(Token::Equal) => {
                self.current += 1;
            }
            _ => return Some(Err(ParseError::ExpectedAssignment(self.current))),
        }
        let expr = self.expr();
        match expr {
            Ok(e) => Some(Ok(Declaration {
                name: identifier,
                value: e,
            })),
            Err(e) => Some(Err(e)),
        }
    }
}
