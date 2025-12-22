use crate::analysis::format::{report_resolution_errors, report_type_errors};
use crate::analysis::inference;
use crate::analysis::inference::Inferrer;
use crate::analysis::resolver::Resolver;
use crate::interpreter::{ValueDisplay, eval_statement};
use crate::lexer::Lexer;
use crate::parser::{ReplStatement, make_input};
use crate::{interpreter, lexer, parser};
use chumsky::Parser;
use colored::*;
use rustyline::DefaultEditor;
use rustyline::error::ReadlineError;

#[derive(Default)]
pub struct Repl {
    resolver: Resolver,
    inferrer: Inferrer,
    type_env: inference::Environment,
    runtime_env: interpreter::Environment,
}

impl Repl {
    pub fn run(&mut self) {
        println!("{} v{}", "Tygr REPL".bold().cyan(), "0.1.0".dimmed());
        println!("Type 'exit' or press Ctrl+D to quit.\n");

        let mut rl = DefaultEditor::new().expect("Failed to initialize readline");

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
                    self.process_line(trimmed);
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

    pub fn process_line(&mut self, source: &str) {
        let name = "<repl>";

        let mut lexer = Lexer::new(source);
        let (tokens, lex_errors) = lexer.collect_all();
        if !lex_errors.is_empty() {
            let _ = lexer::format::report_errors(source, &lex_errors, name);
            return;
        }

        let input = make_input((0..source.len()).into(), &tokens);
        let Ok(decl) = parser::repl().parse(input).into_result().map_err(|e| {
            let _ = parser::format::report_errors(source, e.iter(), name);
        }) else {
            return;
        };

        self.execute_declaration(source, name, decl);
    }

    fn execute_declaration(&mut self, source: &str, name: &str, decl: ReplStatement) {
        let name_table = self.resolver.snapshot_name_table();

        match decl {
            ReplStatement::Type(t) => {
                if let Err(e) = self.resolver.resolve_type_alias(t) {
                    let _ = report_resolution_errors(source, &[e], name);
                }
            }

            ReplStatement::Variant(v) => {
                let res = self
                    .resolver
                    .declare_variant(&v)
                    .and_then(|_| self.resolver.define_variant(v));

                match res {
                    Err(e) => {
                        let _ = report_resolution_errors(source, &[e], name);
                    }
                    Ok(resolved) => {
                        if let Err(e) = self.inferrer.register_variant(resolved) {
                            let _ = report_type_errors(source, &[e], name, &name_table);
                        }
                    }
                }
            }

            ReplStatement::Statement(stmt) => self.execute_statement(source, name, stmt),
        }
    }

    fn execute_statement(&mut self, source: &str, name: &str, stmt: parser::Statement) {
        let resolved = match self.resolver.resolve_global_statement(stmt) {
            Ok(s) => s,
            Err(e) => {
                let _ = report_resolution_errors(source, &[e], name);
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
                let _ = report_type_errors(source, &[e], name, &nt);
                return;
            }
        };

        match eval_statement(&mut self.runtime_env, &typed) {
            Ok(val) => {
                let nt = self.resolver.snapshot_name_table();
                println!("  {} {}", "=>".green().bold(), ValueDisplay::new(&val, &nt));
            }
            Err(e) => println!("  {} {}", "Runtime error:".red().bold(), e),
        }
    }
}
