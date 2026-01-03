mod ast;
pub mod format;
pub use ast::*;

use crate::lexer::{Token, TokenKind};
use chumsky::input::BorrowInput;
use chumsky::prelude::*;
use chumsky::span::SimpleSpan;

fn ident<'a, I>() -> impl Parser<'a, I, String, extra::Err<Rich<'a, TokenKind>>> + Clone
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    select! { TokenKind::Identifier(s) => s }
}

fn path<'a, I>() -> impl Parser<'a, I, Path, extra::Err<Rich<'a, TokenKind>>> + Clone
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    let base = choice((
        just(TokenKind::Crate)
            .then_ignore(just(TokenKind::Cons))
            .to(Some(PathBase::Crate)),
        just(TokenKind::Super)
            .then_ignore(just(TokenKind::Cons))
            .repeated()
            .at_least(1)
            .count()
            .map(|count| Some(PathBase::Super(count))),
        empty().to(None),
    ));

    base.then(
        ident()
            .separated_by(just(TokenKind::Cons))
            .at_least(1)
            .collect::<Vec<_>>(),
    )
    .map_with(|(base, segments), e| Path {
        base,
        segments,
        span: e.span(),
    })
}

/// Helper to create a plain path from a single string (for operators, etc.)
fn plain_path(name: String, span: Span) -> Path {
    Path {
        base: None,
        segments: vec![name],
        span,
    }
}

fn visibility<'a, I>() -> impl Parser<'a, I, Visibility, extra::Err<Rich<'a, TokenKind>>> + Clone
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    just(TokenKind::Pub)
        .to(Visibility::Public)
        .or_not()
        .map(|opt| opt.unwrap_or(Visibility::Private))
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
            let op_fn = Expr::new(ExprKind::Var(plain_path(op_name, span)), span);
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

        let ident_pat = ident()
            .then(tuple_pat.clone().or_not())
            .map_with(|(name, arg_opt), e| match arg_opt {
                Some(arg) => Pattern::new(
                    PatternKind::Constructor(name, Some(Box::new(arg))),
                    e.span(),
                ),
                None => {
                    let is_capitalized = name.chars().next().map_or(false, |c| c.is_uppercase());

                    if is_capitalized {
                        Pattern::new(PatternKind::Constructor(name, None), e.span())
                    } else {
                        Pattern::new(PatternKind::Var(name), e.span())
                    }
                }
            });

        let record_field = ident()
            .then(just(TokenKind::Colon).ignore_then(pat.clone()).or_not())
            .map_with(|(name, pat_opt), e| match pat_opt {
                Some(p) => (name, p),
                None => (name.clone(), Pattern::new(PatternKind::Var(name), e.span())),
            });

        let record_pat = record_field
            .separated_by(just(TokenKind::Comma))
            .allow_trailing()
            .collect()
            .delimited_by(just(TokenKind::LeftBrace), just(TokenKind::RightBrace))
            .map_with(|fields, e| Pattern::new(PatternKind::Record(fields), e.span()));

        let atom = choice((
            ident_pat,
            record_pat,
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
            let atom = path().map_with(|p, e| Annotation::new(AnnotationKind::Var(p), e.span()));

            let field = ident()
                .then_ignore(just(TokenKind::Colon))
                .then(annot.clone())
                .map(|(name, typ)| (name, typ));

            let record = field
                .separated_by(just(TokenKind::Comma))
                .allow_trailing()
                .collect::<Vec<_>>()
                .delimited_by(just(TokenKind::LeftBrace), just(TokenKind::RightBrace))
                .map_with(|fields, e| Annotation::new(AnnotationKind::Record(fields), e.span()));

            let items = annot
                .clone()
                .separated_by(just(TokenKind::Comma))
                .collect::<Vec<_>>();

            let tuple = items
                .delimited_by(just(TokenKind::LeftParen), just(TokenKind::RightParen))
                .map_with(|mut annots: Vec<Annotation>, _e| {
                    if annots.len() == 1 {
                        annots.pop().unwrap()
                    } else {
                        let last = annots.pop().unwrap();
                        annots.into_iter().rfold(last, |acc, a| {
                            let span = a.span.union(acc.span);
                            Annotation::new(AnnotationKind::Pair(Box::new(a), Box::new(acc)), span)
                        })
                    }
                });

            choice((record, atom, tuple))
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

        let arrow = apply
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
        .ignore_then(ident())
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

fn param<'a, I>()
-> impl Parser<'a, I, (Pattern, Option<Annotation>), extra::Err<Rich<'a, TokenKind>>> + Clone
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    pattern().then(just(TokenKind::Colon).ignore_then(annotation()).or_not())
}

fn let_binding<'a, I, P>(
    expr_parser: P,
) -> impl Parser<
    'a,
    I,
    (Pattern, Expr, Vec<Generic>, Option<Annotation>),
    extra::Err<Rich<'a, TokenKind>>,
> + Clone
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
    P: Parser<'a, I, Expr, extra::Err<Rich<'a, TokenKind>>> + Clone,
{
    just(TokenKind::Let)
        .ignore_then(just(TokenKind::Rec).or_not())
        .then(pattern())
        .then(generics())
        .then(just(TokenKind::Colon).ignore_then(annotation()).or_not())
        .then(
            param()
                .then(
                    just(TokenKind::Comma)
                        .ignore_then(param())
                        .repeated()
                        .collect::<Vec<_>>(),
                )
                .map(|(first, mut rest)| {
                    let mut args = vec![first];
                    args.append(&mut rest);
                    args
                })
                .or_not(),
        )
        .then_ignore(just(TokenKind::Equal))
        .then(expr_parser)
        .map_with(
            |(((((rec_token, pat), generics), annot), params_opt), val), e| {
                let span = e.span();
                let mut value_expr = if let Some(params) = params_opt {
                    let mut iter = params.into_iter().rev();
                    let (last_pat, last_annot) = iter.next().unwrap();
                    let inner =
                        Expr::new(ExprKind::Lambda(last_pat, Box::new(val), last_annot), span);
                    iter.fold(inner, |acc, (p, a)| {
                        Expr::new(ExprKind::Lambda(p, Box::new(acc), a), span)
                    })
                } else {
                    val
                };
                if rec_token.is_some()
                    && let PatternKind::Var(name) = &pat.kind
                {
                    let rec_node =
                        Expr::new(ExprKind::RecRecord(vec![(name.clone(), value_expr)]), span);
                    value_expr = Expr::new(
                        ExprKind::FieldAccess(Box::new(rec_node), name.clone()),
                        span,
                    );
                }

                (pat, value_expr, generics, annot)
            },
        )
}

fn expr<'a, I>() -> impl Parser<'a, I, Expr, extra::Err<Rich<'a, TokenKind>>> + Clone
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    recursive(|expr| {
        let field = ident()
            .then(just(TokenKind::Colon).ignore_then(expr.clone()).or_not())
            .map_with(|(name, value_opt), e| match value_opt {
                Some(value) => (name, value),
                None => {
                    let span = e.span();
                    (
                        name.clone(),
                        Expr::new(ExprKind::Var(plain_path(name, span)), span),
                    )
                }
            });

        let simple = {
            let literals = choice((
                select! {
                    TokenKind::Integer(i) => ExprKind::IntLit(i),
                    TokenKind::Float(d) => ExprKind::FloatLit(d),
                    TokenKind::Boolean(b) => ExprKind::BoolLit(b),
                    TokenKind::String(s) => ExprKind::StringLit(s.clone()),
                },
                just(TokenKind::LeftBracket)
                    .then(just(TokenKind::RightBracket))
                    .to(ExprKind::EmptyListLit),
            ))
            .map_with(|kind, e| Expr::new(kind, e.span()));

            let var_expr = path().map_with(|p, e| Expr::new(ExprKind::Var(p), e.span()));

            let atom = choice((literals, var_expr));

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

            let record_lit = field
                .clone()
                .separated_by(just(TokenKind::Comma))
                .allow_trailing()
                .collect::<Vec<_>>()
                .delimited_by(just(TokenKind::LeftBrace), just(TokenKind::RightBrace))
                .map_with(|fields, e| Expr::new(ExprKind::RecordLit(fields), e.span()));

            let block = statement(expr.clone())
                .then_ignore(just(TokenKind::Semicolon))
                .repeated()
                .collect::<Vec<_>>()
                .then(expr.clone().or_not())
                .delimited_by(just(TokenKind::LeftBrace), just(TokenKind::RightBrace))
                .map_with(|(stmts, end_expr), e| {
                    Expr::new(ExprKind::Block(stmts, end_expr.map(Box::new)), e.span())
                });
            choice((block, record_lit, paren_expr, atom))
        };

        #[derive(Clone)]
        enum PostfixOp {
            FieldAccess(String, Span),
        }

        let postfix_op = just(TokenKind::Dot)
            .ignore_then(ident())
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
                    .map_with(|_, e| {
                        let span = e.span();
                        Expr::new(ExprKind::Var(plain_path("~".to_string(), span)), span)
                    })
                    .then(unary.clone())
                    .map_with(|(op_fn, val), e| {
                        Expr::new(ExprKind::App(Box::new(op_fn), Box::new(val)), e.span())
                    }),
                just(TokenKind::MinusDot)
                    .map_with(|_, e| {
                        let span = e.span();
                        Expr::new(ExprKind::Var(plain_path("~.".to_string(), span)), span)
                    })
                    .then(unary.clone())
                    .map_with(|(op_fn, val), e| {
                        Expr::new(ExprKind::App(Box::new(op_fn), Box::new(val)), e.span())
                    }),
                just(TokenKind::Bang)
                    .map_with(|_, e| {
                        let span = e.span();
                        Expr::new(ExprKind::Var(plain_path("!".to_string(), span)), span)
                    })
                    .then(unary.clone())
                    .map_with(|(op_fn, val), e| {
                        Expr::new(ExprKind::App(Box::new(op_fn), Box::new(val)), e.span())
                    }),
                postfix.clone(),
            ))
        });

        let apply = {
            unary.clone().foldl(postfix.repeated(), |func, arg| {
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
                    let op_fn = Expr::new(ExprKind::Var(plain_path(op_name, span)), span);
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

        let let_expr = let_binding(expr.clone())
            .then_ignore(just(TokenKind::In))
            .then(expr.clone())
            .map_with(|((pat, val, generics, annot), body), e| {
                Expr::new(
                    ExprKind::Let(pat, Box::new(val), Box::new(body), generics, annot),
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
            .ignore_then(
                param()
                    .separated_by(just(TokenKind::Comma))
                    .at_least(1)
                    .collect::<Vec<_>>(),
            )
            .then_ignore(just(TokenKind::Lambda))
            .then(expr.clone())
            .map_with(|(params, body), extra| {
                let mut iter = params.into_iter().rev();
                let (last_pat, last_annot) = iter.next().unwrap();

                let span = extra.span();
                let inner = Expr::new(ExprKind::Lambda(last_pat, Box::new(body), last_annot), span);

                iter.fold(inner, |acc, (p, annot)| {
                    let span = p.span.union(acc.span);
                    Expr::new(ExprKind::Lambda(p, Box::new(acc), annot), span)
                })
            });

        let rec_expr = just(TokenKind::Rec).ignore_then(choice((
            field
                .clone()
                .separated_by(just(TokenKind::Comma))
                .allow_trailing()
                .collect::<Vec<_>>()
                .delimited_by(just(TokenKind::LeftBrace), just(TokenKind::RightBrace))
                .map_with(|fields, e| Expr::new(ExprKind::RecRecord(fields), e.span())),
            ident()
                .then(
                    just(TokenKind::Comma)
                        .ignore_then(
                            param()
                                .separated_by(just(TokenKind::Comma))
                                .at_least(1)
                                .collect::<Vec<_>>(),
                        )
                        .or_not(),
                )
                .then_ignore(just(TokenKind::Lambda))
                .then(expr.clone())
                .map_with(|((name, params_opt), body), e| {
                    let span = e.span();
                    let params = params_opt.unwrap_or_default();

                    let func_body = if params.is_empty() {
                        body
                    } else {
                        let mut iter = params.into_iter().rev();
                        let (last_pat, last_annot) = iter.next().unwrap();
                        let inner =
                            Expr::new(ExprKind::Lambda(last_pat, Box::new(body), last_annot), span);
                        iter.fold(inner, |acc, (p, annot)| {
                            let s = p.span.union(acc.span);
                            Expr::new(ExprKind::Lambda(p, Box::new(acc), annot), s)
                        })
                    };

                    let rec_node =
                        Expr::new(ExprKind::RecRecord(vec![(name.clone(), func_body)]), span);
                    Expr::new(ExprKind::FieldAccess(Box::new(rec_node), name), span)
                }),
        )));

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

        choice((let_expr, if_expr, lambda_expr, match_expr, rec_expr, or))
    })
}

fn type_alias<'a, I>() -> impl Parser<'a, I, TypeAlias, extra::Err<Rich<'a, TokenKind>>> + Clone
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    visibility()
        .then_ignore(just(TokenKind::Type))
        .then(ident())
        .then(generics())
        .then_ignore(just(TokenKind::Equal))
        .then(annotation())
        .map_with(|(((vis, name), generics), body), extra| TypeAlias {
            name,
            vis,
            generics,
            body,
            span: extra.span(),
        })
}

fn variant<'a, I>() -> impl Parser<'a, I, Variant, extra::Err<Rich<'a, TokenKind>>> + Clone
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    let constructor = ident()
        .then(
            annotation()
                .delimited_by(just(TokenKind::LeftParen), just(TokenKind::RightParen))
                .or_not(),
        )
        .map_with(|(name, annot_opt), extra| {
            (
                name,
                Constructor {
                    annotation: annot_opt,
                    span: extra.span(),
                },
            )
        });

    visibility()
        .then_ignore(just(TokenKind::Enum))
        .then(ident())
        .then(generics())
        .then_ignore(just(TokenKind::Equal))
        .then_ignore(just(TokenKind::Pipe).or_not())
        .then(
            constructor
                .separated_by(just(TokenKind::Pipe))
                .at_least(1)
                .collect::<Vec<_>>(),
        )
        .map_with(|(((vis, name), generics), constructors), extra| Variant {
            name,
            vis,
            generics,
            constructors,
            span: extra.span(),
        })
}

fn statement<'a, I, P>(
    expr_parser: P,
) -> impl Parser<'a, I, Statement, extra::Err<Rich<'a, TokenKind>>> + Clone
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
    P: Parser<'a, I, Expr, extra::Err<Rich<'a, TokenKind>>> + Clone,
{
    choice((
        expr_parser
            .clone()
            .map_with(|ex, e| Statement::new(StatementKind::Expr(Box::new(ex)), e.span())),
        let_binding(expr_parser).map_with(|(pat, val, generics, annot), e| {
            Statement::new(
                StatementKind::Let(pat, Box::new(val), generics, annot),
                e.span(),
            )
        }),
    ))
}

fn def<'a, I, P>(
    expr_parser: P,
) -> impl Parser<'a, I, Definition, extra::Err<Rich<'a, TokenKind>>> + Clone
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
    P: Parser<'a, I, Expr, extra::Err<Rich<'a, TokenKind>>> + Clone,
{
    visibility()
        .then_ignore(just(TokenKind::Def))
        .then(ident())
        .then(generics())
        .then(just(TokenKind::Colon).ignore_then(annotation()).or_not())
        .then(
            param()
                .then(
                    just(TokenKind::Comma)
                        .ignore_then(param())
                        .repeated()
                        .collect::<Vec<_>>(),
                )
                .map(|(first, mut rest)| {
                    let mut args = vec![first];
                    args.append(&mut rest);
                    args
                })
                .or_not(),
        )
        .then_ignore(just(TokenKind::Equal))
        .then(expr_parser)
        .map_with(|(((((vis, name), generics), annot), params_opt), val), e| {
            let span = e.span();
            let value_expr = if let Some(params) = params_opt {
                let mut iter = params.into_iter().rev();
                let (last_pat, last_annot) = iter.next().unwrap();
                let inner = Expr::new(ExprKind::Lambda(last_pat, Box::new(val), last_annot), span);
                iter.fold(inner, |acc, (p, a)| {
                    Expr::new(ExprKind::Lambda(p, Box::new(acc), a), span)
                })
            } else {
                val
            };

            Definition {
                name,
                vis,
                expr: value_expr,
                generics,
                annotation: annot,
                span,
            }
        })
}

fn use_decl<'a, I>() -> impl Parser<'a, I, UseDecl, extra::Err<Rich<'a, TokenKind>>> + Clone
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    visibility()
        .then_ignore(just(TokenKind::Use))
        .then(path())
        .then(just(TokenKind::As).ignore_then(ident()).or_not())
        .map_with(|((vis, path), alias), e| UseDecl {
            path,
            alias,
            vis,
            span: e.span(),
        })
}

pub fn repl<'a, I>() -> impl Parser<'a, I, ReplStatement, extra::Err<Rich<'a, TokenKind>>>
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    choice((
        type_alias().map(ReplStatement::Type),
        variant().map(ReplStatement::Variant),
        statement(expr()).map(ReplStatement::Statement),
    ))
}

pub fn declaration<'a, I>() -> impl Parser<'a, I, Declaration, extra::Err<Rich<'a, TokenKind>>>
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    recursive(|decl| {
        let module_decl = visibility()
            .then_ignore(just(TokenKind::Mod))
            .then(ident())
            .then(
                decl.repeated()
                    .collect::<Vec<_>>()
                    .delimited_by(just(TokenKind::LeftBrace), just(TokenKind::RightBrace))
                    .or_not(),
            )
            .map_with(|((vis, name), body), e| ModuleDecl {
                name,
                vis,
                body,
                span: e.span(),
            });

        choice((
            use_decl().map(Declaration::Use),
            module_decl.map(Declaration::Module),
            type_alias().map(Declaration::Type),
            variant().map(Declaration::Variant),
            def(expr()).map(Declaration::Def),
        ))
    })
}

pub fn script<'a, I>() -> impl Parser<'a, I, Vec<ReplStatement>, extra::Err<Rich<'a, TokenKind>>>
where
    I: BorrowInput<'a, Token = TokenKind, Span = SimpleSpan> + Clone,
{
    repl().repeated().collect::<Vec<_>>().then_ignore(end())
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

pub fn make_input(
    eoi: SimpleSpan,
    tokens: &[Token],
) -> impl BorrowInput<'_, Token = TokenKind, Span = SimpleSpan> + Clone {
    tokens.map(eoi, |t| (&t.kind, &t.span))
}

pub fn parse_script(tokens: &'_ [Token]) -> ParseResult<Vec<ReplStatement>, Rich<'_, TokenKind>> {
    let len = tokens.last().map(|t| t.span.end()).unwrap_or(0);
    let input = make_input((0..len).into(), tokens);

    script().parse(input)
}

pub fn parse_program(tokens: &'_ [Token]) -> ParseResult<Vec<Declaration>, Rich<'_, TokenKind>> {
    let len = tokens.last().map(|t| t.span.end()).unwrap_or(0);
    let input = make_input((0..len).into(), tokens);

    program().parse(input)
}
