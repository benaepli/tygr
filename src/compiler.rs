use crate::analysis::format::{report_resolution_errors, report_type_errors};
use crate::analysis::inference::{Environment, Inferrer, TypedStatement};
use crate::analysis::name_table::NameTable;
use crate::analysis::resolver::Resolver;
use crate::lexer;
use crate::lexer::Lexer;
use crate::parser::{ReplStatement, SourceId, Statement, TypeAlias, Variant, parse_script};
use crate::sources::FileSources;
use anyhow::anyhow;
use codespan_reporting::term::WriteStyle;

fn split_statements(decls: Vec<ReplStatement>) -> (Vec<Statement>, Vec<Variant>, Vec<TypeAlias>) {
    let mut statements = Vec::new();
    let mut variants = Vec::new();
    let mut type_aliases = Vec::new();

    for decl in decls {
        match decl {
            ReplStatement::Statement(l) => statements.push(l),
            ReplStatement::Variant(v) => variants.push(v),
            ReplStatement::Type(t) => type_aliases.push(t),
        }
    }

    (statements, variants, type_aliases)
}

pub fn compile_script(
    input: &str,
    name: &str,
    writer: &mut impl WriteStyle,
) -> Result<(Vec<TypedStatement>, NameTable), anyhow::Error> {
    let files = FileSources::single(name, input);

    let mut lexer = Lexer::new(input, SourceId::SYNTHETIC);
    let (lexed, errors) = lexer.collect_all();
    lexer::format::report_errors(writer, &files, &errors)?;
    if !errors.is_empty() {
        return Err(errors[0].clone().into());
    }
    let parsed = parse_script(&lexed);
    if parsed.has_errors() {
        crate::parser::format::report_errors(writer, &files, parsed.errors())?;
        return Err(anyhow!("parsing error"));
    }
    let output = match parsed.into_output() {
        None => return Err(anyhow!("no output generated")),
        Some(v) => v,
    };

    let (statements, variants, aliases) = split_statements(output);
    let mut resolver = Resolver::new();
    for variant in &variants {
        if let Err(e) = resolver.declare_global_variant(variant) {
            report_resolution_errors(writer, &files, &[e])?;
            return Err(anyhow!("resolution error"));
        }
    }
    for alias in &aliases {
        if let Err(e) = resolver.declare_global_type_alias(alias) {
            report_resolution_errors(writer, &files, &[e])?;
            return Err(anyhow!("resolution error"));
        }
    }
    let mut resolved_aliases = Vec::new();
    for alias in aliases {
        match resolver.define_global_type_alias(alias) {
            Err(e) => {
                report_resolution_errors(writer, &files, &[e])?;
                return Err(anyhow!("resolution error"));
            }
            Ok(r) => resolved_aliases.push(r),
        }
    }
    let mut resolved_variants = Vec::new();
    for variant in variants {
        match resolver.define_global_variant(variant) {
            Err(e) => {
                report_resolution_errors(writer, &files, &[e])?;
                return Err(anyhow!("resolution error"));
            }
            Ok(v) => resolved_variants.push(v),
        }
    }
    let mut resolved_statements = Vec::new();
    for stmt in statements {
        match resolver.resolve_global_statement(stmt) {
            Err(e) => {
                report_resolution_errors(writer, &files, &[e])?;
                return Err(anyhow!("resolution error"));
            }
            Ok(r) => resolved_statements.push(r),
        }
    }

    let name_table = NameTable::with_global(resolver.into_local_name_table());

    let mut inferrer = Inferrer::new();
    for alias in resolved_aliases {
        match inferrer.register_alias(alias) {
            Err(e) => {
                report_type_errors(writer, &files, &[e], &name_table)?;
                return Err(anyhow!("type inference error"));
            }
            Ok(_) => {}
        }
    }
    for variant in resolved_variants {
        match inferrer.register_variant(variant) {
            Err(e) => {
                report_type_errors(writer, &files, &[e], &name_table)?;
                return Err(anyhow!("type inference error"));
            }
            Ok(t) => t,
        }
    }
    let mut env = Environment::new();
    let mut typed_statements = Vec::new();
    for stmt in resolved_statements {
        match inferrer.infer_global_statement(&mut env, stmt) {
            Err(e) => {
                report_type_errors(writer, &files, &[e], &name_table)?;
                return Err(anyhow!("type inference error"));
            }
            Ok(t) => typed_statements.push(t),
        }
    }

    Ok((typed_statements, name_table))
}
