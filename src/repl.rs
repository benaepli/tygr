use crate::analysis::format::{report_resolution_errors, report_type_errors};
use crate::analysis::inference;
use crate::analysis::inference::Inferrer;
use crate::analysis::resolver::Resolver;
use crate::interpreter::{ValueDisplay, eval_statement};
use crate::lexer::Lexer;
use crate::parser::{ReplStatement, make_input};
use crate::{interpreter, lexer, parser};
use chumsky::Parser;
use codespan_reporting::term::termcolor::{Color, ColorSpec, WriteColor};
use colored::Colorize;
#[cfg(feature = "cli")]
use rustyline::DefaultEditor;
#[cfg(feature = "cli")]
use rustyline::error::ReadlineError;

#[derive(Default)]
pub struct Repl {
    resolver: Resolver,
    inferrer: Inferrer,
    type_env: inference::Environment,
    pub runtime_env: interpreter::Environment,
}

impl Repl {
    #[cfg(feature = "cli")]
    pub fn run(&mut self) {
        println!("{} v{}", "Tygr REPL".bold().cyan(), "0.1.0".dimmed());
        println!("Type 'exit' or press Ctrl+D to quit.\n");

        let mut rl = DefaultEditor::new().expect("Failed to initialize readline");
        let mut writer = termcolor::StandardStream::stdout(termcolor::ColorChoice::Auto);

        loop {
            let prompt = format!("{} ", "tygr>".bold().magenta());
            let readline = rl.readline(&prompt);

            match readline {
                Ok(line) => {
                    let trimmed = line.trim();
                    if trimmed.is_empty() {
                        continue;
                    }
                    if trimmed == "exit" {
                        break;
                    }
                    let _ = rl.add_history_entry(trimmed);
                    self.process_line(trimmed, &mut writer);
                    println!();
                }
                Err(ReadlineError::Interrupted) => {
                    continue;
                }
                Err(ReadlineError::Eof) => {
                    break;
                }
                Err(err) => {
                    eprintln!("{}: {:?}", "Error".red().bold(), err);
                    break;
                }
            }
        }
    }

    pub fn process_line(&mut self, source: &str, writer: &mut impl WriteColor) {
        let name = "<repl>";

        let mut lexer = Lexer::new(source);
        let (tokens, lex_errors) = lexer.collect_all();
        if !lex_errors.is_empty() {
            let _ = lexer::format::report_errors(writer, source, &lex_errors, name);
            return;
        }

        let input = make_input((0..source.len()).into(), &tokens);
        let Ok(decl) = parser::repl().parse(input).into_result().map_err(|e| {
            let _ = parser::format::report_errors(writer, source, e.iter(), name);
        }) else {
            return;
        };

        self.execute_declaration(source, name, decl, writer);
    }

    fn execute_declaration(
        &mut self,
        source: &str,
        name: &str,
        decl: ReplStatement,
        writer: &mut impl WriteColor,
    ) {
        let name_table = self.resolver.snapshot_name_table();

        match decl {
            ReplStatement::Type(t) => {
                if let Err(e) = self.resolver.resolve_type_alias(t) {
                    let _ = report_resolution_errors(writer, source, &[e], name);
                }
            }

            ReplStatement::Variant(v) => {
                let res = self
                    .resolver
                    .declare_variant(&v)
                    .and_then(|_| self.resolver.define_variant(v));

                match res {
                    Err(e) => {
                        let _ = report_resolution_errors(writer, source, &[e], name);
                    }
                    Ok(resolved) => {
                        if let Err(e) = self.inferrer.register_variant(resolved) {
                            let _ = report_type_errors(writer, source, &[e], name, &name_table);
                        }
                    }
                }
            }

            ReplStatement::Statement(stmt) => self.execute_statement(source, name, stmt, writer),
        }
    }

    fn execute_statement(
        &mut self,
        source: &str,
        name: &str,
        stmt: parser::Statement,
        writer: &mut impl WriteColor,
    ) {
        let resolved = match self.resolver.resolve_global_statement(stmt) {
            Ok(s) => s,
            Err(e) => {
                let _ = report_resolution_errors(writer, source, &[e], name);
                return;
            }
        };

        let typed = match self
            .inferrer
            .infer_global_statement(&mut self.type_env, resolved)
        {
            Ok(s) => s,
            Err(e) => {
                let nt = self.resolver.snapshot_name_table();
                let _ = report_type_errors(writer, source, &[e], name, &nt);
                return;
            }
        };

        match eval_statement(&mut self.runtime_env, &typed) {
            Ok(val) => {
                let nt = self.resolver.snapshot_name_table();
                let _ = write!(writer, "  ");
                let _ =
                    writer.set_color(ColorSpec::new().set_fg(Some(Color::Green)).set_bold(true));
                let _ = write!(writer, "=>");
                let _ = writer.reset();
                let _ = writeln!(writer, " {}", ValueDisplay::new(&val, &nt));
            }
            Err(e) => {
                let _ = write!(writer, "  ");
                let _ = writer.set_color(ColorSpec::new().set_fg(Some(Color::Red)).set_bold(true));
                let _ = write!(writer, "Runtime error:");
                let _ = writer.reset();
                let _ = writeln!(writer, " {}", e);
            }
        }
    }
}
