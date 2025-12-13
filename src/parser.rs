pub mod format;

use crate::lexer::{Token, TokenKind};
use chumsky::input::BorrowInput;
use chumsky::prelude::*;
use chumsky::span::SimpleSpan;

pub type Span = SimpleSpan<usize>;

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
    Constructor(String, Box<Pattern>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}

impl Pattern {
    fn new(kind: PatternKind, span: Span) -> Self {
        Pattern { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum AnnotationKind {
    Var(String),
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
    fn new(kind: AnnotationKind, span: Span) -> Self {
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
    pub generics: Vec<Generic>,
    pub body: Annotation,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Constructor {
    pub annotation: Annotation,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Adt {
    pub name: String,
    pub generics: Vec<Generic>,
    pub constructors: Vec<(String, Constructor)>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LetDeclaration {
    pub pattern: Pattern,
    pub value: Expr,
    pub generics: Vec<Generic>,
    pub annotation: Option<Annotation>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Declaration {
    Let(LetDeclaration),
    Adt(Adt),
    Type(TypeAlias),
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchBranch {
    pub pattern: Pattern,
    pub expr: Expr,
    pub span: Span,
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
    Var(String),
    Lambda(Pattern, Box<Expr>, Option<Annotation>), // Annotation is for the parameter type.
    App(Box<Expr>, Box<Expr>),
    Let(
        Pattern,
        Box<Expr>,
        Box<Expr>,
        Vec<Generic>,
        Option<Annotation>,
    ),
    Fix(Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<MatchBranch>),

    UnitLit,
    PairLit(Box<Expr>, Box<Expr>),
    IntLit(i64),
    FloatLit(f64),
    BoolLit(bool),
    StringLit(String),
    EmptyListLit,
    RecordLit(Vec<(String, Expr)>),

    BinOp(BinOp, Box<Expr>, Box<Expr>),
    Cons(Box<Expr>, Box<Expr>),
    FieldAccess(Box<Expr>, String),
}

fn build_bin_op<'a, I, OP, P>(
    op_parser: OP,
    next_parser: P,
) -> impl Parser<'a, I, Expr, extra::Err<Rich<'a, TokenKind>>> + Clone
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
    OP: Parser<'a, I, String, extra::Err<Rich<'a, TokenKind>>> + Clone,
    P: Parser<'a, I, Expr, extra::Err<Rich<'a, TokenKind>>> + Clone,
{
    next_parser.clone().foldl(
        op_parser.then(next_parser).repeated(),
        |left, (op_name, right)| {
            let span = left.span.union(right.span);
            let op_fn = Expr::new(ExprKind::Var(op_name), span);
            let func = Expr::new(ExprKind::App(Box::new(op_fn), Box::new(left)), span);
            Expr::new(ExprKind::App(Box::new(func), Box::new(right)), span)
        },
    )
}

fn pattern<'a, I>() -> impl Parser<'a, I, Pattern, extra::Err<Rich<'a, TokenKind>>> + Clone
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    recursive(|pat| {
        let items = pat
            .clone()
            .separated_by(just(TokenKind::Comma))
            .collect::<Vec<_>>();
        let tuple_pat = items
            .delimited_by(just(TokenKind::LeftParen), just(TokenKind::RightParen))
            .map_with(|mut pats: Vec<Pattern>, e| {
                if pats.is_empty() {
                    Pattern::new(PatternKind::Unit, e.span())
                } else {
                    let last = pats.pop().unwrap();
                    pats.into_iter().rfold(last, |acc, p| {
                        let span = p.span.union(acc.span);
                        Pattern::new(PatternKind::Pair(Box::new(p), Box::new(acc)), span)
                    })
                }
            });

        let ident_pat = select! { TokenKind::Identifier(s) => s }
            .then(tuple_pat.clone().or_not())
            .map_with(|(name, arg_opt), e| match arg_opt {
                Some(arg) => Pattern::new(PatternKind::Constructor(name, Box::new(arg)), e.span()),
                None => Pattern::new(PatternKind::Var(name), e.span()),
            });

        let atom = choice((
            ident_pat,
            just(TokenKind::Underscore)
                .to(PatternKind::Wildcard)
                .map_with(|k, e| Pattern::new(k, e.span())),
            just(TokenKind::LeftBracket)
                .then(just(TokenKind::RightBracket))
                .to(PatternKind::EmptyList)
                .map_with(|k, e| Pattern::new(k, e.span())),
            tuple_pat,
        ));

        let cons_pat = atom
            .clone()
            .then(just(TokenKind::Cons).ignore_then(pat).or_not())
            .map_with(|(head, tail_opt), _| match tail_opt {
                Some(tail) => {
                    let span = head.span.union(tail.span);
                    Pattern::new(PatternKind::Cons(Box::new(head), Box::new(tail)), span)
                }
                None => head,
            });

        cons_pat
    })
}

fn annotation<'a, I>() -> impl Parser<'a, I, Annotation, extra::Err<Rich<'a, TokenKind>>> + Clone
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    recursive(|annot| {
        let simple = {
            let atom = select! {
                TokenKind::Identifier(s) => AnnotationKind::Var(s),
            }
            .map_with(|kind, e| Annotation::new(kind, e.span()));

            let paren = just(TokenKind::LeftParen)
                .ignore_then(annot.clone())
                .then_ignore(just(TokenKind::RightParen));

            let ident = select! { TokenKind::Identifier(s) => s.clone() };

            let field = ident
                .clone()
                .then_ignore(just(TokenKind::Colon))
                .then(annot.clone())
                .map(|(name, typ)| (name, typ));

            let record = field
                .separated_by(just(TokenKind::Comma))
                .allow_trailing()
                .collect::<Vec<_>>()
                .delimited_by(just(TokenKind::LeftBrace), just(TokenKind::RightBrace))
                .map_with(|fields, e| Annotation::new(AnnotationKind::Record(fields), e.span()));

            choice((record, atom, paren))
        };

        let apply_parser = just(TokenKind::LeftBracket)
            .ignore_then(annot.clone())
            .then_ignore(just(TokenKind::RightBracket));

        let apply = simple
            .clone()
            .foldl_with(apply_parser.repeated(), |arg1, arg2, extra| {
                Annotation::new(
                    AnnotationKind::App(Box::new(arg1), Box::new(arg2)),
                    extra.span(),
                )
            });

        let product = apply.clone().foldl_with(
            just(TokenKind::Star).ignore_then(apply).repeated(),
            |fst, snd, extra| {
                Annotation::new(
                    AnnotationKind::Pair(Box::new(fst), Box::new(snd)),
                    extra.span(),
                )
            },
        );

        let arrow = product
            .clone()
            .separated_by(just(TokenKind::RightArrow))
            .at_least(1)
            .collect::<Vec<_>>()
            .map(|items| {
                let mut iter = items.into_iter().rev();
                let last = iter.next().unwrap();
                iter.fold(last, |snd, fst| {
                    let span = snd.span.union(fst.span);
                    Annotation::new(AnnotationKind::Lambda(Box::new(fst), Box::new(snd)), span)
                })
            });

        arrow
    })
}

fn generics<'a, I>() -> impl Parser<'a, I, Vec<Generic>, extra::Err<Rich<'a, TokenKind>>> + Clone
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    just(TokenKind::LeftBracket)
        .ignore_then(select! {
            TokenKind::Identifier(s) => s
        })
        .then_ignore(just(TokenKind::RightBracket))
        .map_with(|s, extra| Generic {
            name: s,
            span: extra.span(),
        })
        .repeated()
        .at_least(1)
        .collect::<Vec<_>>()
        .or_not()
        .map(|generics| generics.unwrap_or_default())
}

fn expr<'a, I>() -> impl Parser<'a, I, Expr, extra::Err<Rich<'a, TokenKind>>>
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    recursive(|expr| {
        let annotation_with_colon = just(TokenKind::Colon).ignore_then(annotation());
        let ident = select! { TokenKind::Identifier(s) => s.clone() };

        let simple = {
            let atom = choice((
                select! {
                    TokenKind::Integer(i) => ExprKind::IntLit(i),
                    TokenKind::Float(d) => ExprKind::FloatLit(d),
                    TokenKind::Boolean(b) => ExprKind::BoolLit(b),
                    TokenKind::String(s) => ExprKind::StringLit(s.clone()),
                    TokenKind::Identifier(s) => ExprKind::Var(s.clone()),
                },
                just(TokenKind::LeftBracket)
                    .then(just(TokenKind::RightBracket))
                    .to(ExprKind::EmptyListLit),
            ))
            .map_with(|kind, e| Expr::new(kind, e.span()));

            let items = expr
                .clone()
                .separated_by(just(TokenKind::Comma))
                .at_least(0)
                .collect::<Vec<_>>();

            let paren_expr = items
                .delimited_by(just(TokenKind::LeftParen), just(TokenKind::RightParen))
                .map_with(|mut expressions: Vec<Expr>, e| {
                    if expressions.is_empty() {
                        Expr::new(ExprKind::UnitLit, e.span())
                    } else if expressions.len() == 1 {
                        expressions.pop().unwrap()
                    } else {
                        let last = expressions.pop().unwrap();
                        expressions.into_iter().rfold(last, |acc, next| {
                            let span = next.span.union(acc.span);
                            Expr::new(ExprKind::PairLit(Box::new(next), Box::new(acc)), span)
                        })
                    }
                });

            let field = ident
                .clone()
                .then_ignore(just(TokenKind::Colon))
                .then(expr.clone())
                .map(|(name, value)| (name, value));

            let record_lit = field
                .separated_by(just(TokenKind::Comma))
                .allow_trailing()
                .collect::<Vec<_>>()
                .delimited_by(just(TokenKind::LeftBrace), just(TokenKind::RightBrace))
                .map_with(|fields, e| Expr::new(ExprKind::RecordLit(fields), e.span()));

            choice((record_lit, paren_expr, atom))
        };

        #[derive(Clone)]
        enum PostfixOp {
            FieldAccess(String, Span),
        }

        let postfix_op = just(TokenKind::Dot)
            .ignore_then(ident.clone())
            .map_with(|name, e| PostfixOp::FieldAccess(name, e.span()));

        let postfix = simple.foldl(postfix_op.repeated(), |lhs, op| match op {
            PostfixOp::FieldAccess(name, op_span) => {
                let span = lhs.span.union(op_span);
                Expr::new(ExprKind::FieldAccess(Box::new(lhs), name), span)
            }
        });

        let unary = recursive(|unary| {
            choice((
                just(TokenKind::Minus)
                    .map_with(|_, e| Expr::new(ExprKind::Var("~".to_string()), e.span()))
                    .then(unary.clone())
                    .map_with(|(op_fn, val), e| {
                        Expr::new(ExprKind::App(Box::new(op_fn), Box::new(val)), e.span())
                    }),
                just(TokenKind::MinusDot)
                    .map_with(|_, e| Expr::new(ExprKind::Var("~.".to_string()), e.span()))
                    .then(unary.clone())
                    .map_with(|(op_fn, val), e| {
                        Expr::new(ExprKind::App(Box::new(op_fn), Box::new(val)), e.span())
                    }),
                just(TokenKind::Bang)
                    .map_with(|_, e| Expr::new(ExprKind::Var("!".to_string()), e.span()))
                    .then(unary.clone())
                    .map_with(|(op_fn, val), e| {
                        Expr::new(ExprKind::App(Box::new(op_fn), Box::new(val)), e.span())
                    }),
                postfix.clone(),
            ))
        });

        let apply = {
            let fix_or_unary = choice((
                just(TokenKind::Fix)
                    .ignore_then(unary.clone())
                    .map_with(|e, extra| Expr::new(ExprKind::Fix(Box::new(e)), extra.span())),
                unary.clone(),
            ));

            fix_or_unary.clone().foldl(postfix.repeated(), |func, arg| {
                let span = func.span.union(arg.span);
                Expr::new(ExprKind::App(Box::new(func), Box::new(arg)), span)
            })
        };

        let factor = {
            let op = choice((
                just(TokenKind::Star).to("*".to_string()),
                just(TokenKind::Slash).to("/".to_string()),
                just(TokenKind::StarDot).to("*.".to_string()),
                just(TokenKind::SlashDot).to("/.".to_string()),
            ));
            build_bin_op(op, apply)
        };

        let term = {
            let op = choice((
                just(TokenKind::Plus).to("+".to_string()),
                just(TokenKind::Minus).to("-".to_string()),
                just(TokenKind::PlusDot).to("+.".to_string()),
                just(TokenKind::MinusDot).to("-.".to_string()),
            ));
            build_bin_op(op, factor)
        };

        let concat = {
            let op = just(TokenKind::Caret).to("^".to_string());
            build_bin_op(op, term)
        };

        let cons = concat
            .clone()
            .separated_by(just(TokenKind::Cons))
            .at_least(1)
            .collect::<Vec<_>>()
            .map(|items| {
                let mut iter = items.into_iter().rev();
                let last = iter.next().unwrap();
                iter.fold(last, |tail, head| {
                    let span = head.span.union(tail.span);
                    Expr::new(ExprKind::Cons(Box::new(head), Box::new(tail)), span)
                })
            });

        let compare = cons
            .clone()
            .then(
                choice((
                    just(TokenKind::EqualEqual).to("==".to_string()),
                    just(TokenKind::BangEqual).to("!=".to_string()),
                    just(TokenKind::LessEqual).to("<=".to_string()),
                    just(TokenKind::GreaterEqual).to(">=".to_string()),
                    just(TokenKind::Less).to("<".to_string()),
                    just(TokenKind::Greater).to(">".to_string()),
                    just(TokenKind::EqualEqualDot).to("==.".to_string()),
                    just(TokenKind::BangEqualDot).to("!=.".to_string()),
                    just(TokenKind::GreaterEqualDot).to(">=.".to_string()),
                    just(TokenKind::LessEqualDot).to("<=.".to_string()),
                    just(TokenKind::GreaterDot).to(">.".to_string()),
                    just(TokenKind::LessDot).to("<.".to_string()),
                    just(TokenKind::EqualEqualB).to("==b".to_string()),
                    just(TokenKind::BangEqualB).to("!=b".to_string()),
                ))
                .then(cons)
                .or_not(),
            )
            .map(|(left, op_right_opt)| match op_right_opt {
                Some((op_name, right)) => {
                    let span = left.span.union(right.span);
                    let op_fn = Expr::new(ExprKind::Var(op_name), span);
                    let func = Expr::new(ExprKind::App(Box::new(op_fn), Box::new(left)), span);
                    Expr::new(ExprKind::App(Box::new(func), Box::new(right)), span)
                }
                None => left,
            });

        let and = compare.clone().foldl(
            just(TokenKind::And).ignore_then(compare).repeated(),
            |left, right| {
                let span = left.span.union(right.span);
                Expr::new(
                    ExprKind::BinOp(BinOp::And, Box::new(left), Box::new(right)),
                    span,
                )
            },
        );

        let or = and.clone().foldl(
            just(TokenKind::Or).ignore_then(and).repeated(),
            |left, right| {
                let span = left.span.union(right.span);
                Expr::new(
                    ExprKind::BinOp(BinOp::Or, Box::new(left), Box::new(right)),
                    span,
                )
            },
        );

        let let_expr = just(TokenKind::Let)
            .ignore_then(pattern())
            .then(generics())
            .then(annotation_with_colon.clone().or_not())
            .then_ignore(just(TokenKind::Equal))
            .then(expr.clone())
            .then_ignore(just(TokenKind::In))
            .then(expr.clone())
            .map_with(|((((pat, generics), annot), e1), e2), e| {
                Expr::new(
                    ExprKind::Let(pat, Box::new(e1), Box::new(e2), generics, annot),
                    e.span(),
                )
            });

        let if_expr = just(TokenKind::If)
            .ignore_then(expr.clone())
            .then_ignore(just(TokenKind::Then))
            .then(expr.clone())
            .then_ignore(just(TokenKind::Else))
            .then(expr.clone())
            .map_with(|((cnd, csq), alt), e| {
                Expr::new(
                    ExprKind::If(Box::new(cnd), Box::new(csq), Box::new(alt)),
                    e.span(),
                )
            });

        let lambda_expr = just(TokenKind::Fn)
            .ignore_then(pattern())
            .then(annotation_with_colon.clone().or_not())
            .then_ignore(just(TokenKind::Lambda))
            .then(expr.clone())
            .map_with(|((pat, annot), e), extra| {
                Expr::new(ExprKind::Lambda(pat, Box::new(e), annot), extra.span())
            });

        let match_branch = just(TokenKind::Pipe)
            .ignore_then(pattern())
            .then_ignore(just(TokenKind::Lambda))
            .then(expr.clone())
            .map_with(|(pattern, expr), extra| MatchBranch {
                pattern,
                expr,
                span: extra.span(),
            });

        let match_expr = just(TokenKind::Match)
            .ignore_then(expr.clone())
            .then_ignore(just(TokenKind::With))
            .then(match_branch.repeated().at_least(1).collect::<Vec<_>>())
            .map_with(|(expr, others), extra| {
                Expr::new(ExprKind::Match(Box::new(expr), others), extra.span())
            });

        choice((let_expr, if_expr, lambda_expr, match_expr, or))
    })
}

fn type_alias<'a, I>() -> impl Parser<'a, I, TypeAlias, extra::Err<Rich<'a, TokenKind>>>
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    just(TokenKind::Type)
        .ignore_then(select! { TokenKind::Identifier(s) => s })
        .then(generics())
        .then_ignore(just(TokenKind::Equal))
        .then(annotation())
        .map_with(|((name, generics), body), extra| TypeAlias {
            name,
            generics,
            body,
            span: extra.span(),
        })
}

fn adt<'a, I>() -> impl Parser<'a, I, Adt, extra::Err<Rich<'a, TokenKind>>>
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    let constructor = select! { TokenKind::Identifier(s) => s }
        .then(
            annotation()
                .delimited_by(just(TokenKind::LeftParen), just(TokenKind::RightParen))
                .or_not(),
        )
        .map_with(|(name, annot_opt), extra| {
            let annotation = annot_opt.unwrap_or_else(|| {
                Annotation::new(AnnotationKind::Var("unit".to_string()), extra.span())
            });
            (
                name,
                Constructor {
                    annotation,
                    span: extra.span(),
                },
            )
        });

    just(TokenKind::Enum)
        .ignore_then(select! { TokenKind::Identifier(s) => s })
        .then(generics())
        .then_ignore(just(TokenKind::Equal))
        .then_ignore(just(TokenKind::Pipe).or_not())
        .then(
            constructor
                .separated_by(just(TokenKind::Pipe))
                .at_least(1)
                .collect::<Vec<_>>(),
        )
        .map_with(|((name, generics), constructors), extra| Adt {
            name,
            generics,
            constructors,
            span: extra.span(),
        })
}

fn let_declaration<'a, I>() -> impl Parser<'a, I, LetDeclaration, extra::Err<Rich<'a, TokenKind>>>
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    just(TokenKind::Let)
        .ignore_then(pattern())
        .then(generics())
        .then(just(TokenKind::Colon).ignore_then(annotation()).or_not())
        .then_ignore(just(TokenKind::Equal))
        .then(expr())
        .map_with(
            |(((pattern, generics), annotation), value), extra| LetDeclaration {
                pattern,
                value,
                generics,
                annotation,
                span: extra.span(),
            },
        )
}

fn declaration<'a, I>() -> impl Parser<'a, I, Declaration, extra::Err<Rich<'a, TokenKind>>>
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    choice((
        type_alias().map(|t| Declaration::Type(t)),
        adt().map(|a| Declaration::Adt(a)),
        let_declaration().map(|l| Declaration::Let(l)),
    ))
}

pub fn program<'a, I>() -> impl Parser<'a, I, Vec<Declaration>, extra::Err<Rich<'a, TokenKind>>>
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    declaration()
        .repeated()
        .collect::<Vec<_>>()
        .then_ignore(end())
}

fn make_input(
    eoi: SimpleSpan,
    tokens: &[Token],
) -> impl BorrowInput<'_, Token = TokenKind, Span = SimpleSpan> + Clone {
    tokens.map(eoi, |t| (&t.kind, &t.span))
}

pub fn parse_program(tokens: &'_ [Token]) -> ParseResult<Vec<Declaration>, Rich<'_, TokenKind>> {
    let len = tokens.last().map(|t| t.span.end()).unwrap_or(0);
    let input = make_input((0..len).into(), &tokens);

    program().parse(input)
}
