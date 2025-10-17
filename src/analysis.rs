pub mod resolver;
pub mod inference;

use crate::parser::{Declaration, Expr};

pub fn desugar(mut declarations: Vec<Declaration>) -> Option<Expr> {
    let last = declarations.pop()?;
    let mut result = Expr::Let(
        last.name.clone(),
        Box::new(last.value),
        Box::new(Expr::Var(last.name)),
    );

    for declaration in declarations.into_iter().rev() {
        result = Expr::Let(
            declaration.name,
            Box::new(declaration.value),
            Box::new(result),
        );
    }
    Some(result)
}
