use crate::analysis::check_static_definitions;
use crate::analysis::dependencies::reorder_definitions;
use crate::analysis::format::{
    report_initial_analysis_errors, report_resolution_errors, report_type_errors,
};
use crate::analysis::inference::{Environment, Inferrer, TypedGroup, TypedStatement};
use crate::analysis::name_table::NameTable;
use crate::analysis::resolver::{Name, Resolver, TypeName};
use crate::ir::closure::{Converter, Program, VariantDef};
use crate::lexer::Lexer;
use crate::parser::{
    Declaration, Definition, ReplStatement, Statement, TypeAlias, Variant, parse_program,
    parse_script,
};
use crate::{lexer, parser};
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

fn split_program(decls: Vec<Declaration>) -> (Vec<Definition>, Vec<Variant>, Vec<TypeAlias>) {
    let mut definitions = Vec::new();
    let mut variants = Vec::new();
    let mut type_aliases = Vec::new();

    for decl in decls {
        match decl {
            Declaration::Def(d) => definitions.push(d),
            Declaration::Variant(v) => variants.push(v),
            Declaration::Type(t) => type_aliases.push(t),
        }
    }

    (definitions, variants, type_aliases)
}

pub fn compile_script(
    input: &str,
    name: &str,
    writer: &mut impl WriteStyle,
) -> Result<(Vec<TypedStatement>, NameTable), anyhow::Error> {
    let mut lexer = Lexer::new(input);
    let (lexed, errors) = lexer.collect_all();
    lexer::format::report_errors(writer, input, &errors, name)?;
    if !errors.is_empty() {
        return Err(errors[0].clone().into());
    }
    let parsed = parse_script(&lexed);
    if parsed.has_errors() {
        parser::format::report_errors(writer, input, parsed.errors(), name)?;
        return Err(anyhow!("parsing error"));
    }
    let output = match parsed.into_output() {
        None => return Err(anyhow!("no output generated")),
        Some(v) => v,
    };

    let (statements, variants, aliases) = split_statements(output);
    let mut resolver = Resolver::new();
    for variant in &variants {
        if let Err(e) = resolver.declare_variant(variant) {
            report_resolution_errors(writer, input, &[e], name)?;
            return Err(anyhow!("resolution error"));
        }
    }
    for alias in aliases {
        match resolver.resolve_type_alias(alias) {
            Err(e) => {
                report_resolution_errors(writer, input, &[e], name)?;
                return Err(anyhow!("resolution error"));
            }
            Ok(r) => r,
        }
    }
    let mut resolved_variants = Vec::new();
    for variant in variants {
        match resolver.define_variant(variant) {
            Err(e) => {
                report_resolution_errors(writer, input, &[e], name)?;
                return Err(anyhow!("resolution error"));
            }
            Ok(v) => resolved_variants.push(v),
        }
    }
    let mut resolved_statements = Vec::new();
    for stmt in statements {
        match resolver.resolve_global_statement(stmt) {
            Err(e) => {
                report_resolution_errors(writer, input, &[e], name)?;
                return Err(anyhow!("resolution error"));
            }
            Ok(r) => resolved_statements.push(r),
        }
    }

    let name_table = resolver.into_name_table();

    let mut inferrer = Inferrer::new();
    for variant in resolved_variants {
        match inferrer.register_variant(variant) {
            Err(e) => {
                report_type_errors(writer, input, &[e], name, &name_table)?;
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
                report_type_errors(writer, input, &[e], name, &name_table)?;
                return Err(anyhow!("type inference error"));
            }
            Ok(t) => typed_statements.push(t),
        }
    }

    Ok((typed_statements, name_table))
}

pub struct TypedProgram {
    pub groups: Vec<TypedGroup>,
    pub variants: Vec<VariantDef>,
    pub name_table: NameTable,
    pub next_name: Name,
    pub next_type_name: TypeName,
}

pub fn compile_typed_program(
    input: &str,
    name: &str,
    writer: &mut impl WriteStyle,
) -> Result<TypedProgram, anyhow::Error> {
    let mut lexer = Lexer::new(input);
    let (lexed, errors) = lexer.collect_all();
    lexer::format::report_errors(writer, input, &errors, name)?;
    if !errors.is_empty() {
        return Err(errors[0].clone().into());
    }
    let parsed = parse_program(&lexed);
    if parsed.has_errors() {
        parser::format::report_errors(writer, input, parsed.errors(), name)?;
        return Err(anyhow!("parsing error"));
    }
    let output = match parsed.into_output() {
        None => return Err(anyhow!("no output generated")),
        Some(v) => v,
    };

    let (definitions, variants, aliases) = split_program(output);
    if let Err(e) = check_static_definitions(&definitions) {
        report_initial_analysis_errors(writer, input, &[e], name)?;
        return Err(anyhow!("initial analysis error"));
    }

    let mut resolver = Resolver::new();
    for variant in &variants {
        if let Err(e) = resolver.declare_variant(variant) {
            report_resolution_errors(writer, input, &[e], name)?;
            return Err(anyhow!("resolution error"));
        }
    }
    for alias in aliases {
        match resolver.resolve_type_alias(alias) {
            Err(e) => {
                report_resolution_errors(writer, input, &[e], name)?;
                return Err(anyhow!("resolution error"));
            }
            Ok(r) => r,
        }
    }
    let mut resolved_variants = Vec::new();
    for variant in variants {
        match resolver.define_variant(variant) {
            Err(e) => {
                report_resolution_errors(writer, input, &[e], name)?;
                return Err(anyhow!("resolution error"));
            }
            Ok(v) => resolved_variants.push(v),
        }
    }
    for definition in &definitions {
        if let Err(e) = resolver.declare_definition(definition) {
            report_resolution_errors(writer, input, &[e], name)?;
            return Err(anyhow!("resolution error"));
        }
    }
    let mut resolved_definitions = Vec::new();
    for definition in definitions {
        match resolver.resolve_definition(definition) {
            Err(e) => {
                report_resolution_errors(writer, input, &[e], name)?;
                return Err(anyhow!("resolution error"));
            }
            Ok(d) => resolved_definitions.push(d),
        }
    }
    let reordered = reorder_definitions(resolved_definitions);

    let next_name = resolver.next_name_id();
    let next_type_name = resolver.next_type_name_id();
    let name_table = resolver.into_name_table();
    let mut inferrer = Inferrer::new();
    for variant in resolved_variants {
        match inferrer.register_variant(variant) {
            Err(e) => {
                report_type_errors(writer, input, &[e], name, &name_table)?;
                return Err(anyhow!("type inference error"));
            }
            Ok(t) => t,
        }
    }
    let env = Environment::default();
    let (groups, _) = match inferrer.infer_definitions(reordered, env) {
        Err(e) => {
            report_type_errors(writer, input, &[e], name, &name_table)?;
            return Err(anyhow!("type inference error"));
        }
        Ok(t) => t,
    };

    Ok(TypedProgram {
        groups,
        variants: inferrer.get_variant_definitions(),
        name_table,
        next_name,
        next_type_name,
    })
}

pub fn compile_program(
    input: &str,
    name: &str,
    writer: &mut impl WriteStyle,
) -> Result<(Program, NameTable), anyhow::Error> {
    let typed = compile_typed_program(input, name, writer)?;
    let mut converter = Converter::new(typed.next_name, typed.next_type_name);
    for var in typed.variants {
        converter.register_variant(var);
    }
    let program = converter.convert_program(typed.groups);
    Ok((program, typed.name_table))
}
