use crate::lexer::LexError;
use crate::sources::FileSources;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::term;
use codespan_reporting::term::WriteStyle;

/// Reports lexer errors using codespan-reporting.
///
/// This function takes a FileSources and a list of lexer errors, and prints
/// nicely formatted error messages with source code context to the provided writer.
pub fn report_errors(
    writer: &mut impl WriteStyle,
    files: &FileSources,
    errors: &[LexError],
) -> Result<(), codespan_reporting::files::Error> {
    let config = term::Config::default();

    for error in errors {
        let diagnostic = match error {
            LexError::UnexpectedChar(pos, source_id) => Diagnostic::error()
                .with_message("unexpected character")
                .with_labels(vec![
                    Label::primary(*source_id, *pos..*pos + 1)
                        .with_message("this character is not valid here"),
                ]),
            LexError::UnterminatedString(pos, source_id) => Diagnostic::error()
                .with_message("unterminated string literal")
                .with_labels(vec![
                    Label::primary(*source_id, *pos..*pos + 1)
                        .with_message("string starts here but is never closed"),
                ])
                .with_notes(vec![
                    "string literals must be terminated with a closing quote".to_string(),
                ]),
        };

        term::emit_to_write_style(writer, &config, files, &diagnostic)?;
    }

    Ok(())
}
