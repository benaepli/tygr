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
    And,
    Or,
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
    StringLit(String),

    BinOp(BinOp, Box<Expr>, Box<Expr>),
}

fn build_bin_op<'a, OP, P>(
    op_parser: OP,
    next_parser: P,
) -> impl Parser<'a, &'a [Token], Expr, extra::Err<Rich<'a, Token>>> + Clone
where
    OP: Parser<'a, &'a [Token], Expr, extra::Err<Rich<'a, Token>>> + Clone,
    P: Parser<'a, &'a [Token], Expr, extra::Err<Rich<'a, Token>>> + Clone,
{
    next_parser.clone().foldl(
        op_parser.then(next_parser).repeated(),
        |left, (op_fn, right)| {
            let func = Expr::App(Box::new(op_fn), Box::new(left));
            Expr::App(Box::new(func), Box::new(right))
        },
    )
}

pub fn expr<'a>() -> impl Parser<'a, &'a [Token], Expr, extra::Err<Rich<'a, Token>>> {
    recursive(|expr| {
        let simple = {
            let atom = select! {
                Token::Integer(i) => Expr::IntLit(i),
                Token::Double(d) => Expr::DoubleLit(d),
                Token::Boolean(b) => Expr::BoolLit(b),
                Token::String(s) => Expr::StringLit(s.clone()),
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
                    .to(Expr::Var("~".to_string()))
                    .then(unary.clone())
                    .map(|(op_fn, val)| Expr::App(Box::new(op_fn), Box::new(val))),
                just(Token::MinusDot)
                    .to(Expr::Var("~.".to_string()))
                    .then(unary.clone())
                    .map(|(op_fn, val)| Expr::App(Box::new(op_fn), Box::new(val))),
                just(Token::Bang)
                    .to(Expr::Var("!".to_string()))
                    .then(unary.clone())
                    .map(|(op_fn, val)| Expr::App(Box::new(op_fn), Box::new(val))),
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

        let factor = {
            let op = choice((
                just(Token::Star).to(Expr::Var("*".to_string())),
                just(Token::Slash).to(Expr::Var("/".to_string())),
                just(Token::StarDot).to(Expr::Var("*.".to_string())),
                just(Token::SlashDot).to(Expr::Var("/.".to_string())),
            ));
            build_bin_op(op, apply)
        };

        let term = {
            let op = choice((
                just(Token::Plus).to(Expr::Var("+".to_string())),
                just(Token::Minus).to(Expr::Var("-".to_string())),
                just(Token::PlusDot).to(Expr::Var("+.".to_string())),
                just(Token::MinusDot).to(Expr::Var("-.".to_string())),
            ));
            build_bin_op(op, factor)
        };

        let concat = {
            let op = just(Token::Caret).to(Expr::Var("^".to_string()));
            build_bin_op(op, term)
        };

        let compare = concat
            .clone()
            .then(
                choice((
                    just(Token::EqualEqual).to(Expr::Var("==".to_string())),
                    just(Token::BangEqual).to(Expr::Var("!=".to_string())),
                    just(Token::LessEqual).to(Expr::Var("<=".to_string())),
                    just(Token::GreaterEqual).to(Expr::Var(">=".to_string())),
                    just(Token::Less).to(Expr::Var("<".to_string())),
                    just(Token::Greater).to(Expr::Var(">".to_string())),
                    just(Token::EqualEqualDot).to(Expr::Var("==.".to_string())),
                    just(Token::BangEqualDot).to(Expr::Var("!=.".to_string())),
                    just(Token::GreaterEqualDot).to(Expr::Var(">=.".to_string())),
                    just(Token::LessEqualDot).to(Expr::Var("<=.".to_string())),
                    just(Token::GreaterDot).to(Expr::Var(">.".to_string())),
                    just(Token::LessDot).to(Expr::Var("<.".to_string())),
                    just(Token::EqualEqualB).to(Expr::Var("==b".to_string())),
                    just(Token::BangEqualB).to(Expr::Var("!=b".to_string())),
                ))
                .then(concat)
                .or_not(),
            )
            .map(|(left, op_right_opt)| match op_right_opt {
                Some((op_fn, right)) => {
                    let func = Expr::App(Box::new(op_fn), Box::new(left));
                    Expr::App(Box::new(func), Box::new(right))
                }
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
