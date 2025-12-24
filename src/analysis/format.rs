use crate::analysis::inference::{TypeDisplay, TypeError};
use crate::analysis::name_table::NameTable;
use crate::analysis::resolver::ResolutionError;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term;
use codespan_reporting::term::WriteStyle;

pub fn report_resolution_errors(
    writer: &mut impl WriteStyle,
    source: &str,
    errors: &[ResolutionError],
    filename: &str,
) -> Result<(), codespan_reporting::files::Error> {
    let mut files = SimpleFiles::new();
    let file_id = files.add(filename, source);

    let config = term::Config::default();

    for error in errors {
        let diagnostic = match error {
            ResolutionError::VariableNotFound(name, span) => Diagnostic::error()
                .with_message(format!("variable `{}` not found", name))
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end)
                        .with_message("not found in this scope"),
                ])
                .with_notes(vec!["variables must be defined before use".to_string()]),
            ResolutionError::DuplicateBinding(name, span) => Diagnostic::error()
                .with_message(format!("variable `{}` is bound more than once", name))
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end).with_message("duplicate binding"),
                ])
                .with_notes(vec![
                    "each variable can only be bound once in a pattern".to_string(),
                ]),
            ResolutionError::DuplicateTypeAlias(name, span) => Diagnostic::error()
                .with_message(format!("type alias `{}` is already defined", name))
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end)
                        .with_message("duplicate type alias definition"),
                ])
                .with_notes(vec!["each type alias can only be defined once".to_string()]),
            ResolutionError::WrongNumberOfTypeArguments(name, expected, found, span) => {
                Diagnostic::error()
                    .with_message(format!("wrong number of type arguments for `{}`", name))
                    .with_labels(vec![
                        Label::primary(file_id, span.start..span.end).with_message(format!(
                            "expected {} type argument(s), found {}",
                            expected, found
                        )),
                    ])
                    .with_notes(vec![format!(
                        "type alias `{}` requires exactly {} type argument(s)",
                        name, expected
                    )])
            }
            ResolutionError::DuplicateRecordField(name, span) => Diagnostic::error()
                .with_message(format!("field `{}` appears more than once in record", name))
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end).with_message("duplicate field"),
                ])
                .with_notes(vec![
                    "each field can only appear once in a record".to_string(),
                ]),
            ResolutionError::DuplicateVariant(name, span) => Diagnostic::error()
                .with_message(format!("variant type `{}` is already defined", name))
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end)
                        .with_message("duplicate variant type definition"),
                ])
                .with_notes(vec![
                    "each variant type can only be defined once".to_string(),
                ]),
            ResolutionError::DuplicateConstructor(name, span) => Diagnostic::error()
                .with_message(format!("constructor `{}` is already defined", name))
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end)
                        .with_message("duplicate constructor"),
                ])
                .with_notes(vec![
                    "constructor names must be unique across all types".to_string(),
                ]),
            ResolutionError::ConstructorNotFound(name, span) => Diagnostic::error()
                .with_message(format!("constructor `{}` not found", name))
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end)
                        .with_message("not found in this scope"),
                ])
                .with_notes(vec!["constructors must be defined before use".to_string()]),
        };

        term::emit_to_write_style(writer, &config, &files, &diagnostic)?;
    }

    Ok(())
}

pub fn report_type_errors(
    writer: &mut impl WriteStyle,
    source: &str,
    errors: &[TypeError],
    filename: &str,
    name_table: &NameTable,
) -> Result<(), codespan_reporting::files::Error> {
    let mut files = SimpleFiles::new();
    let file_id = files.add(filename, source);

    let config = term::Config::default();

    for error in errors {
        let diagnostic = match error {
            TypeError::Mismatch(found, expected, span) => Diagnostic::error()
                .with_message("type mismatch")
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end).with_message(format!(
                        "expected type `{}`, found type `{}`",
                        TypeDisplay::new(expected.clone(), name_table),
                        TypeDisplay::new(found.clone(), name_table)
                    )),
                ]),
            TypeError::OccursCheck(var, ty, span) => Diagnostic::error()
                .with_message("infinite type detected")
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end)
                        .with_message(format!("recursive type: `'{}` occurs in `{}`", var, TypeDisplay::new(ty.clone(), name_table))),
                ]),
            TypeError::UnboundVariable(name, span) => {
                let display_name = name_table.lookup_name(name);
                Diagnostic::error()
                    .with_message(format!("unbound variable `{}`", display_name))
                    .with_labels(vec![
                        Label::primary(file_id, span.start..span.end)
                            .with_message("not found in this scope"),
                    ])
            }
            TypeError::RecordFieldMismatch(t1, t2, span) => Diagnostic::error()
                .with_message("record field mismatch")
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end).with_message(format!(
                        "records have different fields: `{}` vs `{}`",
                        TypeDisplay::new(t1.clone(), name_table),
                        TypeDisplay::new(t2.clone(), name_table)
                    )),
                ])
                .with_notes(vec![
                    "records must have exactly the same field names to unify".to_string(),
                ]),
            TypeError::FieldAccessOnNonRecord(ty, span) => Diagnostic::error()
                .with_message("field access on non-record type")
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end)
                        .with_message(format!("cannot access field on type `{}`", TypeDisplay::new(ty.clone(), name_table))),
                ])
                .with_notes(vec![
                    "field access is only allowed on record types".to_string(),
                ]),
            TypeError::VariantNotFound(variant_id, span) => {
                let type_name = name_table.lookup_type_name(variant_id);
                Diagnostic::error()
                    .with_message("variant type not found")
                    .with_labels(vec![
                        Label::primary(file_id, span.start..span.end)
                            .with_message(format!("type `{}` not found in inference context", type_name)),
                    ])
                    .with_notes(vec![
                        "this is an internal error - the variant type should have been registered during resolution".to_string(),
                    ])
            }
            TypeError::ConstructorNotFound(variant_id, ctor_id, span) => {
                let variant_name = name_table.lookup_type_name(variant_id);
                let ctor_name = name_table.lookup_name(ctor_id);
                Diagnostic::error()
                    .with_message("constructor not found in type")
                    .with_labels(vec![
                        Label::primary(file_id, span.start..span.end)
                            .with_message(format!("constructor `{}` not found in type `{}`", ctor_name, variant_name)),
                    ])
                    .with_notes(vec![
                        "this is an internal error - the constructor should have been registered with the variant type".to_string(),
                    ])
            }
            TypeError::InvalidConstructorType(span) => Diagnostic::error()
                .with_message("invalid constructor type")
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end)
                        .with_message("expected constructor to have function type"),
                ])
                .with_notes(vec![
                    "constructors must have function types that take an argument and return the variant type".to_string(),
                ]),
            TypeError::KindMismatch(found, expected, span) => Diagnostic::error()
                .with_message("kind mismatch")
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end).with_message(format!(
                        "expected kind `{:?}`, found kind `{:?}`",
                        expected, found
                    )),
                ])
                .with_notes(vec![
                    "kinds must match when unifying types".to_string(),
                ]),
        };

        term::emit_to_write_style(writer, &config, &files, &diagnostic)?;
    }

    Ok(())
}
