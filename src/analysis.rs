pub mod format;
pub mod inference;
pub mod name_table;
pub mod resolver;

use crate::parser::{Expr, ExprKind, Pattern, PatternKind};

pub fn pattern_to_expr(pattern: &Pattern) -> Expr {
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
        PatternKind::Record(fields) => {
            let expr_fields = fields
                .iter()
                .map(|(name, pat)| (name.clone(), pattern_to_expr(pat)))
                .collect();
            ExprKind::RecordLit(expr_fields)
        }
        PatternKind::Constructor(name, e) => ExprKind::App(
            Box::new(Expr::new(ExprKind::Var(name.clone()), pattern.span)),
            Box::new(pattern_to_expr(e)),
        ),
    };
    Expr {
        kind,
        span: pattern.span,
    }
}
