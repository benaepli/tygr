use crate::analysis::desugar;
use crate::analysis::format::{report_resolution_errors, report_type_errors};
use crate::analysis::inference::{Inferrer, Typed};
use crate::analysis::resolver::Resolver;
use crate::lexer::Lexer;
use crate::parser::{
    Adt, Declaration, Expr, ExprKind, LetDeclaration, Span, TypeAlias, parse_program,
};
use crate::{lexer, parser};
use anyhow::anyhow;

fn split_declarations(decls: Vec<Declaration>) -> (Vec<LetDeclaration>, Vec<Adt>, Vec<TypeAlias>) {
    let mut let_decls = Vec::new();
    let mut adts = Vec::new();
    let mut type_aliases = Vec::new();

    for decl in decls {
        match decl {
            Declaration::Let(l) => let_decls.push(l),
            Declaration::Adt(a) => adts.push(a),
            Declaration::Type(t) => type_aliases.push(t),
        }
    }

    (let_decls, adts, type_aliases)
}

pub fn compile(input: &str, name: &str) -> Result<Typed, anyhow::Error> {
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

    let (declarations, adts, aliases) = split_declarations(output);
    let desugared = desugar(declarations).unwrap_or_else(|| Expr {
        kind: ExprKind::UnitLit,
        span: Span {
            context: (),
            start: 0,
            end: 0,
        },
    });
    let mut resolver = Resolver::new();
    for alias in aliases {
        match resolver.resolve_type_alias(alias) {
            Err(e) => {
                report_resolution_errors(input, &[e], name)?;
                return Err(anyhow!("resolution error"));
            }
            Ok(r) => r,
        }
    }
    let mut resolved_adts = Vec::new();
    for adt in adts {
        match resolver.resolve_adt(adt) {
            Err(e) => {
                report_resolution_errors(input, &[e], name)?;
                return Err(anyhow!("resolution error"));
            }
            Ok(a) => resolved_adts.push(a),
        }
    }
    let resolved = match resolver.resolve(desugared) {
        Err(e) => {
            report_resolution_errors(input, &[e], name)?;
            return Err(anyhow!("resolution error"));
        }
        Ok(r) => r,
    };

    let mut inferrer = Inferrer::new();
    for adt in resolved_adts {
        inferrer.register_adt(adt);
    }

    let typed = match inferrer.infer(resolved) {
        Err(e) => {
            report_type_errors(input, &[e], name)?;
            return Err(anyhow!("type inference error"));
        }
        Ok(t) => t,
    };
    Ok(typed)
}
