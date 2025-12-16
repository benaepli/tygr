use crate::analysis::desugar;
use crate::analysis::format::{report_resolution_errors, report_type_errors};
use crate::analysis::inference::{Inferrer, Typed};
use crate::analysis::name_table::NameTable;
use crate::analysis::resolver::Resolver;
use crate::lexer::Lexer;
use crate::parser::{
    Declaration, Expr, ExprKind, LetDeclaration, Span, TypeAlias, Variant, parse_program,
};
use crate::{lexer, parser};
use anyhow::anyhow;

fn split_declarations(
    decls: Vec<Declaration>,
) -> (Vec<LetDeclaration>, Vec<Variant>, Vec<TypeAlias>) {
    let mut let_decls = Vec::new();
    let mut variants = Vec::new();
    let mut type_aliases = Vec::new();

    for decl in decls {
        match decl {
            Declaration::Let(l) => let_decls.push(l),
            Declaration::Variant(v) => variants.push(v),
            Declaration::Type(t) => type_aliases.push(t),
        }
    }

    (let_decls, variants, type_aliases)
}

pub fn compile(input: &str, name: &str) -> Result<(Typed, NameTable), anyhow::Error> {
    let mut lexer = Lexer::new(input);
    let (lexed, errors) = lexer.collect_all();
    lexer::format::report_errors(input, &errors, name)?;
    if !errors.is_empty() {
        return Err(errors[0].clone().into());
    }
    let parsed = parse_program(&lexed);
    if parsed.has_errors() {
        parser::format::report_errors(input, parsed.errors(), name)?;
        return Err(anyhow!("parsing error"));
    }
    let output = match parsed.into_output() {
        None => return Err(anyhow!("no output generated")),
        Some(v) => v,
    };

    let (declarations, variants, aliases) = split_declarations(output);
    let desugared = desugar(declarations).unwrap_or_else(|| Expr {
        kind: ExprKind::UnitLit,
        span: Span {
            context: (),
            start: 0,
            end: 0,
        },
    });
    let mut resolver = Resolver::new();
    for variant in &variants {
        if let Err(e) = resolver.declare_variant(variant) {
            report_resolution_errors(input, &[e], name)?;
            return Err(anyhow!("resolution error"));
        }
    }
    for alias in aliases {
        match resolver.resolve_type_alias(alias) {
            Err(e) => {
                report_resolution_errors(input, &[e], name)?;
                return Err(anyhow!("resolution error"));
            }
            Ok(r) => r,
        }
    }
    let mut resolved_variants = Vec::new();
    for variant in variants {
        match resolver.define_variant(variant) {
            Err(e) => {
                report_resolution_errors(input, &[e], name)?;
                return Err(anyhow!("resolution error"));
            }
            Ok(v) => resolved_variants.push(v),
        }
    }
    let resolved = match resolver.resolve(desugared) {
        Err(e) => {
            report_resolution_errors(input, &[e], name)?;
            return Err(anyhow!("resolution error"));
        }
        Ok(r) => r,
    };

    let name_table = resolver.into_name_table();

    let mut inferrer = Inferrer::new();
    for variant in resolved_variants {
        match inferrer.register_variant(variant) {
            Err(e) => {
                report_type_errors(input, &[e], name, &name_table)?;
                return Err(anyhow!("type inference error"));
            }
            Ok(t) => t,
        }
    }

    let typed = match inferrer.infer(resolved) {
        Err(e) => {
            report_type_errors(input, &[e], name, &name_table)?;
            return Err(anyhow!("type inference error"));
        }
        Ok(t) => t,
    };
    Ok((typed, name_table))
}
