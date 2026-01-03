use crate::lexer::TokenKind;
use crate::parser::Span;
use chumsky::prelude::Rich;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term;
use codespan_reporting::term::WriteStyle;

pub fn report_errors<'a, F>(
    writer: &mut impl WriteStyle,
    source: &str,
    errors: F,
    filename: &str,
) -> Result<(), codespan_reporting::files::Error>
where
    F: Iterator<Item = &'a Rich<'a, TokenKind, Span>>,
{
    let mut files = SimpleFiles::new();
    let file_id = files.add(filename, source);

    let config = term::Config::default();

    for error in errors {
        let span = error.span();
        let diagnostic = Diagnostic::error()
            .with_message(error.to_string())
            .with_labels(vec![
                Label::primary(file_id, span.start..span.end).with_message(error.to_string()),
            ]);
        term::emit_to_write_style(writer, &config, &files, &diagnostic)?;
    }

    Ok(())
}
