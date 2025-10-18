use crate::analysis::desugar;
use crate::analysis::resolver::Resolver;
use crate::lexer::{Lexer, TokenKind};
use crate::parser::{Span, program, parse_program};
use crate::{lexer, parser};
use anyhow::anyhow;
use chumsky::Parser;

pub fn compile(input: &str, name: &str) -> Result<(), anyhow::Error> {
    let mut lexer = Lexer::new(input);
    let (lexed, errors) = lexer.collect_all();
    lexer::format::report_errors(input, &errors, name)?;
    if !errors.is_empty() {
        return Err(errors[0].clone().into());
    }
    let parsed = parse_program(&lexed);
    if parsed.has_errors() {
        parser::format::report_errors(input, parsed.errors(), name)?;
        return Ok(());
    }
    let output = match parsed.into_output() {
        None => return Err(anyhow!("no output generated")),
        Some(v) => v,
    };
    let desugared = match desugar(output) {
        Some(e) => e,
        None => return Err(anyhow!("non-empty file expected")),
    };
    let mut resolver = Resolver::new();
    let resolved = resolver.resolve(desugared)?;
    dbg!(resolved);
    Ok(())
}
