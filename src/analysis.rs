pub mod dependencies;
pub mod format;
pub mod inference;
pub mod main_function;
pub mod name_table;
pub mod resolver;

use crate::parser::{Definition, Expr, ExprKind, Pattern, PatternKind, Span};

#[derive(Debug, Clone)]
pub enum InitialAnalysisError {
    NonStaticDefinition(String, Span),
}

pub fn check_static_definitions(definitions: &[Definition]) -> Result<(), InitialAnalysisError> {
    for definition in definitions {
        if !is_static(&definition.expr) {
            return Err(InitialAnalysisError::NonStaticDefinition(
                definition.name.clone(),
                definition.span,
            ));
        }
    }
    Ok(())
}

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
        PatternKind::Constructor(name, e) => match e {
            Some(inner) => ExprKind::App(
                Box::new(Expr::new(ExprKind::Var(name.clone()), pattern.span)),
                Box::new(pattern_to_expr(inner)),
            ),
            None => ExprKind::Var(name.clone()),
        },
    };
    Expr {
        kind,
        span: pattern.span,
    }
}

pub fn is_static(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::IntLit(_)
        | ExprKind::FloatLit(_)
        | ExprKind::BoolLit(_)
        | ExprKind::StringLit(_)
        | ExprKind::UnitLit
        | ExprKind::EmptyListLit => true,

        ExprKind::Lambda(..) => true,

        ExprKind::PairLit(a, b) => is_static(a) && is_static(b),
        ExprKind::Cons(head, tail) => is_static(head) && is_static(tail),
        ExprKind::RecordLit(fields) => fields.iter().all(|(_, e)| is_static(e)),

        ExprKind::App(..)
        | ExprKind::If(..)
        | ExprKind::Match(..)
        | ExprKind::Let(..)
        | ExprKind::Block(..)
        | ExprKind::BinOp(..) => false,

        ExprKind::Var(_) => true,
        ExprKind::RecRecord(_) => false,
        ExprKind::FieldAccess(_, _) => false,
    }
}
