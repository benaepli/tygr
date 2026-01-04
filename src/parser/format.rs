use crate::lexer::TokenKind;
use crate::parser::Span;
use crate::sources::FileSources;
use chumsky::prelude::Rich;
use chumsky::span::Span as _;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::term;
use codespan_reporting::term::WriteStyle;

pub fn report_errors<'a, F>(
    writer: &mut impl WriteStyle,
    files: &FileSources,
    errors: F,
) -> Result<(), codespan_reporting::files::Error>
where
    F: Iterator<Item = &'a Rich<'a, TokenKind, Span>>,
{
    let config = term::Config::default();

    for error in errors {
        let span = error.span();
        let diagnostic = Diagnostic::error()
            .with_message(error.to_string())
            .with_labels(vec![
                Label::primary(span.context(), span.start..span.end)
                    .with_message(error.to_string()),
            ]);
        term::emit_to_write_style(writer, &config, files, &diagnostic)?;
    }

    Ok(())
}
