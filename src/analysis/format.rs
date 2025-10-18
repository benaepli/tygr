use crate::analysis::inference::TypeError;
use crate::analysis::resolver::ResolutionError;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};

pub fn report_resolution_errors(
    source: &str,
    errors: &[ResolutionError],
    filename: &str,
) -> Result<(), codespan_reporting::files::Error> {
    let mut files = SimpleFiles::new();
    let file_id = files.add(filename, source);

    let writer = StandardStream::stderr(ColorChoice::Auto);
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
        };

        term::emit_to_write_style(&mut writer.lock(), &config, &files, &diagnostic)?;
    }

    Ok(())
}

pub fn report_type_errors(
    source: &str,
    errors: &[TypeError],
    filename: &str,
) -> Result<(), codespan_reporting::files::Error> {
    let mut files = SimpleFiles::new();
    let file_id = files.add(filename, source);

    let writer = StandardStream::stderr(ColorChoice::Auto);
    let config = term::Config::default();

    for error in errors {
        let diagnostic = match error {
            TypeError::Mismatch(expected, found, span) => Diagnostic::error()
                .with_message("type mismatch")
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end).with_message(format!(
                        "expected type `{}`, found type `{}`",
                        expected, found
                    )),
                ]),
            TypeError::OccursCheck(var, ty, span) => Diagnostic::error()
                .with_message("infinite type detected")
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end)
                        .with_message(format!("recursive type: `'{}` occurs in `{}`", var, ty)),
                ]),
            TypeError::UnboundVariable(name, span) => Diagnostic::error()
                .with_message(format!("unbound variable `{}`", name))
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end)
                        .with_message("not found in this scope"),
                ]),
        };

        term::emit_to_write_style(&mut writer.lock(), &config, &files, &diagnostic)?;
    }

    Ok(())
}
