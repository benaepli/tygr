pub mod format;

use crate::lexer::Token;
use chumsky::prelude::*;

/// A program is a list of declarations with a name and an expression.
/// In other words, a program contains declarations of the form `let name = value`.
#[derive(Debug, Clone, PartialEq)]
pub struct Declaration {
    pub name: String,
    pub value: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BinOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    AddFloat,
    SubtractFloat,
    MultiplyFloat,
    DivideFloat,
    Equal,
    NotEqual,
    LessEqual,
    GreaterEqual,
    Less,
    Greater,
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq)]
pub enum UnaryOp {
    Negate,
    NegateFloat,
    Not,
}

#[derive(Debug, Clone, PartialEq)]
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
    UnaryOp(UnaryOp, Box<Expr>),
}

pub fn expr<'a>() -> impl Parser<'a, &'a [Token], Expr, extra::Err<Rich<'a, Token>>> {
    recursive(|expr| {
        let simple = {
            let atom = select! {
                Token::Integer(i) => Expr::IntLit(i),
                Token::Double(d) => Expr::DoubleLit(d),
                Token::Boolean(b) => Expr::BoolLit(b),
                Token::Identifier(s) => Expr::Var(s.clone()),
            };

            let paren_expr = expr
                .clone()
                .delimited_by(just(Token::LeftParen), just(Token::RightParen));

            choice((paren_expr, atom))
        };

        let unary = recursive(|unary| {
            choice((
                just(Token::Minus)
                    .ignore_then(unary.clone())
                    .map(|e| Expr::UnaryOp(UnaryOp::Negate, Box::new(e))),
                just(Token::MinusDot)
                    .ignore_then(unary.clone())
                    .map(|e| Expr::UnaryOp(UnaryOp::NegateFloat, Box::new(e))),
                just(Token::Bang)
                    .ignore_then(unary.clone())
                    .map(|e| Expr::UnaryOp(UnaryOp::Not, Box::new(e))),
                simple,
            ))
        });

        let apply = {
            let fix_or_unary = choice((
                just(Token::Fix)
                    .ignore_then(unary.clone())
                    .map(|e| Expr::Fix(Box::new(e))),
                unary.clone(),
            ));

            fix_or_unary.clone().foldl(unary.repeated(), |func, arg| {
                Expr::App(Box::new(func), Box::new(arg))
            })
        };

        let factor = apply.clone().foldl(
            choice((
                just(Token::Star).to(BinOp::Multiply),
                just(Token::Slash).to(BinOp::Divide),
                just(Token::StarDot).to(BinOp::MultiplyFloat),
                just(Token::SlashDot).to(BinOp::DivideFloat),
            ))
            .then(apply)
            .repeated(),
            |left, (op, right)| Expr::BinOp(op, Box::new(left), Box::new(right)),
        );

        let term = factor.clone().foldl(
            choice((
                just(Token::Plus).to(BinOp::Add),
                just(Token::Minus).to(BinOp::Subtract),
                just(Token::PlusDot).to(BinOp::AddFloat),
                just(Token::MinusDot).to(BinOp::SubtractFloat),
            ))
            .then(factor)
            .repeated(),
            |left, (op, right)| Expr::BinOp(op, Box::new(left), Box::new(right)),
        );

        let compare = term
            .clone()
            .then(
                choice((
                    just(Token::EqualEqual).to(BinOp::Equal),
                    just(Token::BangEqual).to(BinOp::NotEqual),
                    just(Token::LessEqual).to(BinOp::LessEqual),
                    just(Token::GreaterEqual).to(BinOp::GreaterEqual),
                    just(Token::Less).to(BinOp::Less),
                    just(Token::Greater).to(BinOp::Greater),
                ))
                .then(term)
                .or_not(),
            )
            .map(|(left, op_right_opt)| match op_right_opt {
                Some((op, right)) => Expr::BinOp(op, Box::new(left), Box::new(right)),
                None => left,
            });

        let and = compare.clone().foldl(
            just(Token::And).ignore_then(compare).repeated(),
            |left, right| Expr::BinOp(BinOp::And, Box::new(left), Box::new(right)),
        );

        let or = and.clone().foldl(
            just(Token::Or).ignore_then(and).repeated(),
            |left, right| Expr::BinOp(BinOp::Or, Box::new(left), Box::new(right)),
        );

        let let_expr = just(Token::Let)
            .ignore_then(select! { Token::Identifier(s) => s.clone() })
            .then(expr.clone())
            .then_ignore(just(Token::In))
            .then(expr.clone())
            .map(|((id, e1), e2)| Expr::Let(id, Box::new(e1), Box::new(e2)));

        let if_expr = just(Token::If)
            .ignore_then(expr.clone())
            .then_ignore(just(Token::Then))
            .then(expr.clone())
            .then_ignore(just(Token::Else))
            .then(expr.clone())
            .map(|((cnd, csq), alt)| Expr::If(Box::new(cnd), Box::new(csq), Box::new(alt)));

        let lambda_expr = just(Token::Fn)
            .ignore_then(select! { Token::Identifier(s) => s.clone() })
            .then_ignore(just(Token::Lambda))
            .then(expr.clone())
            .map(|(id, e)| Expr::Lambda(id, Box::new(e)));

        choice((let_expr, if_expr, lambda_expr, or))
    })
}

pub fn declaration<'a>() -> impl Parser<'a, &'a [Token], Declaration, extra::Err<Rich<'a, Token>>> {
    just(Token::Let)
        .ignore_then(select! { Token::Identifier(s) => s.clone() })
        .then_ignore(just(Token::Equal))
        .then(expr())
        .map(|(name, value)| Declaration { name, value })
}

pub fn program<'a>() -> impl Parser<'a, &'a [Token], Vec<Declaration>, extra::Err<Rich<'a, Token>>>
{
    declaration()
        .repeated()
        .collect::<Vec<_>>()
        .then_ignore(end())
}
