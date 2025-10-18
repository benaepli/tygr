pub mod resolver;
pub mod inference;

use crate::parser::{Declaration, Expr, ExprKind};

pub fn desugar(mut declarations: Vec<Declaration>) -> Option<Expr> {
    let last = declarations.pop()?;
    let last_span = last.value.span;
    let mut result = Expr {
        kind: ExprKind::Let(
            last.name.clone(),
            Box::new(last.value),
            Box::new(Expr {
                kind: ExprKind::Var(last.name),
                span: last_span,
            }),
        ),
        span: last_span,
    };

    for declaration in declarations.into_iter().rev() {
        let decl_span = declaration.value.span;
        result = Expr {
            kind: ExprKind::Let(
                declaration.name,
                Box::new(declaration.value),
                Box::new(result),
            ),
            span: decl_span,
        };
    }
    Some(result)
}
