use crate::lexer::{Lexer, Span, SpannedToken, Token};
use crate::parser::program;
use crate::{lexer, parser};
use chumsky::Parser;
use std::collections::HashMap;

fn map_tokens(input: &[SpannedToken]) -> (Vec<Token>, HashMap<usize, Span>) {
    input
        .iter()
        .enumerate()
        .map(|(i, spanned)| (spanned.token.clone(), (i, spanned.span)))
        .unzip()
}

pub fn compile(input: &str, name: &str) -> Result<(), anyhow::Error> {
    let mut lexer = Lexer::new(input);
    let (lexed, errors) = lexer.collect_all();
    lexer::format::report_errors(input, &errors, name)?;
    if !errors.is_empty() {
        return Err(errors[0].clone().into());
    }
    let (tokens, indices) = map_tokens(&lexed);
    let parser = program();
    let parsed = parser.parse(&tokens);
    if parsed.has_errors() {
        parser::format::report_errors(input, parsed.errors(), &indices, name)?;
    }

    dbg!(parsed.output());
    Ok(())
}
