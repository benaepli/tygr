use crate::lexer::{Span, Token};
use chumsky::prelude::Rich;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use std::collections::HashMap;

pub fn report_errors<'a, F>(
    source: &str,
    errors: F,
    map: &HashMap<usize, Span>,
    filename: &str,
) -> Result<(), codespan_reporting::files::Error>
where
    F: Iterator<Item = &'a Rich<'a, Token>>,
{
    let mut files = SimpleFiles::new();
    let file_id = files.add(filename, source);

    let writer = StandardStream::stderr(ColorChoice::Auto);
    let config = term::Config::default();

    for error in errors {
        let span = match map.get(&error.span().start) {
            None => Span {
                start: source.len(),
                end: source.len(),
            },
            Some(s) => *s,
        };
        let diagnostic = Diagnostic::error()
            .with_message(error.to_string())
            .with_labels(vec![
                Label::primary(file_id, span.start..span.end).with_message(error.to_string()),
            ]);
        term::emit_to_io_write(&mut writer.lock(), &config, &files, &diagnostic)?;
    }

    Ok(())
}
