use crate::analysis::check_static_definitions;
use crate::analysis::dependencies::reorder_definitions;
use crate::analysis::format::{
    report_initial_analysis_errors, report_resolution_errors, report_type_errors,
};
use crate::analysis::inference::{Environment, Inferrer, TypedGroup, TypedStatement};
use crate::analysis::name_table::NameTable;
use crate::analysis::resolver::{GlobalName, GlobalType, Name, Resolver, TypeName};
use crate::ir::closure::{Converter, Program, VariantDef};
use crate::lexer::Lexer;
use crate::parser::{
    Declaration, Definition, ReplStatement, SourceId, Statement, TypeAlias, Variant, parse_program,
    parse_script,
};
use crate::sources::FileSources;
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
            Declaration::TypeAlias(t) => type_aliases.push(t),
            _ => {}
        }
    }

    (definitions, variants, type_aliases)
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
        parser::format::report_errors(writer, &files, parsed.errors())?;
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
    let files = FileSources::single(name, input);

    let mut lexer = Lexer::new(input, SourceId::SYNTHETIC);
    let (lexed, errors) = lexer.collect_all();
    lexer::format::report_errors(writer, &files, &errors)?;
    if !errors.is_empty() {
        return Err(errors[0].clone().into());
    }
    let parsed = parse_program(&lexed);
    if parsed.has_errors() {
        parser::format::report_errors(writer, &files, parsed.errors())?;
        return Err(anyhow!("parsing error"));
    }
    let output = match parsed.into_output() {
        None => return Err(anyhow!("no output generated")),
        Some(v) => v,
    };

    let (definitions, variants, aliases) = split_program(output);
    if let Err(e) = check_static_definitions(&definitions) {
        report_initial_analysis_errors(writer, &files, &[e])?;
        return Err(anyhow!("initial analysis error"));
    }

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
            Ok(a) => resolved_aliases.push(a),
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
    for definition in &definitions {
        if let Err(e) = resolver.declare_global_definition(definition) {
            report_resolution_errors(writer, &files, &[e])?;
            return Err(anyhow!("resolution error"));
        }
    }
    let mut resolved_definitions = Vec::new();
    for definition in definitions {
        match resolver.define_global_definition(definition) {
            Err(e) => {
                report_resolution_errors(writer, &files, &[e])?;
                return Err(anyhow!("resolution error"));
            }
            Ok(d) => resolved_definitions.push(d),
        }
    }
    let reordered = reorder_definitions(resolved_definitions);

    let next_name = resolver.next_name_id();
    let next_type_name = resolver.next_type_name_id();
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
    let env = Environment::default();
    let (groups, _) = match inferrer.infer_definitions(reordered, env) {
        Err(e) => {
            report_type_errors(writer, &files, &[e], &name_table)?;
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

pub fn compile_closure_program(
    input: &str,
    name: &str,
    writer: &mut impl WriteStyle,
) -> Result<(Program, NameTable), anyhow::Error> {
    let typed = compile_typed_program(input, name, writer)?;
    let mut converter = Converter::new(
        GlobalName {
            krate: None,
            name: typed.next_name,
        },
        GlobalType {
            krate: None,
            name: typed.next_type_name,
        },
    );
    for var in typed.variants {
        converter.register_variant(var);
    }
    let program = converter.convert_program(typed.groups);
    Ok((program, typed.name_table))
}

pub fn compile_constructor_program(
    input: &str,
    name: &str,
    writer: &mut impl WriteStyle,
) -> Result<(crate::ir::constructor::Program, NameTable), anyhow::Error> {
    let (closure_program, name_table) = compile_closure_program(input, name, writer)?;
    let mut converter = crate::ir::constructor::Converter::new(closure_program.next_name);
    let constructor_program = converter.convert_program(closure_program);
    Ok((constructor_program, name_table))
}
