use crate::analysis::desugar;
use crate::analysis::format::{report_resolution_errors, report_type_errors};
use crate::analysis::inference::Inferrer;
use crate::analysis::resolver::Resolver;
use crate::lexer::Lexer;
use crate::parser::parse_program;
use crate::{lexer, parser};
use anyhow::anyhow;

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
    let resolved = match resolver.resolve(desugared) {
        Err(e) => {
            report_resolution_errors(input, &[e], name)?;
            return Ok(());
        }
        Ok(r) => r,
    };
    let mut inferrer = Inferrer::new();
    let typed = match inferrer.infer(resolved) {
        Err(e) => {
            report_type_errors(input, &[e], name)?;
            return Ok(());
        }
        Ok(t) => t,
    };
    dbg!(typed);

    // dbg!(resolved);
    Ok(())
}
