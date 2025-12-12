pub mod format;
pub mod inference;
pub mod resolver;

use crate::parser::{Expr, ExprKind, LetDeclaration, Pattern, PatternKind};
use chumsky::span::Span;

fn pattern_to_expr(pattern: &Pattern) -> Expr {
    let kind = match &pattern.kind {
        PatternKind::Var(name) => ExprKind::Var(name.clone()),
        PatternKind::Unit => ExprKind::UnitLit,
        PatternKind::Wildcard => ExprKind::UnitLit,
        PatternKind::Pair(p1, p2) => {
            let e1 = Box::new(pattern_to_expr(p1));
            let e2 = Box::new(pattern_to_expr(p2));
            ExprKind::PairLit(e1, e2)
        }
        PatternKind::Cons(p1, p2) => {
            let e1 = Box::new(pattern_to_expr(p1));
            let e2 = Box::new(pattern_to_expr(p2));
            ExprKind::Cons(e1, e2)
        }
        PatternKind::EmptyList => ExprKind::EmptyListLit,
    };
    Expr {
        kind,
        span: pattern.span,
    }
}

pub fn desugar(mut declarations: Vec<LetDeclaration>) -> Option<Expr> {
    let last = declarations.pop()?;
    let last_span = last.pattern.span.union(last.value.span);

    let final_expr = pattern_to_expr(&last.pattern);

    let mut result = Expr {
        kind: ExprKind::Let(
            last.pattern,
            Box::new(last.value),
            Box::new(final_expr),
            last.generics,
            last.annotation,
        ),
        span: last_span,
    };

    for declaration in declarations.into_iter().rev() {
        let decl_span = declaration.pattern.span.union(declaration.value.span);
        result = Expr {
            kind: ExprKind::Let(
                declaration.pattern,
                Box::new(declaration.value),
                Box::new(result),
                declaration.generics,
                declaration.annotation,
            ),
            span: decl_span,
        };
    }

    Some(result)
}
