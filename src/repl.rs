use chumsky::Parser;
use std::io;
use std::io::Write;
use crate::analysis::format::{report_resolution_errors, report_type_errors};
use crate::interpreter::{eval_statement, ValueDisplay};
use crate::{interpreter, lexer, parser};
use crate::analysis::inference;
use crate::analysis::inference::Inferrer;
use crate::analysis::resolver::Resolver;
use crate::lexer::Lexer;
use crate::parser::{make_input, Declaration};

pub struct Repl {
    resolver: Resolver,
    inferrer: Inferrer,
    type_env: inference::Environment,
    runtime_env: interpreter::Environment,
}

impl Repl {
    pub fn new() -> Self {
        Self {
            resolver: Resolver::new(),
            inferrer: Inferrer::new(),
            type_env: inference::Environment::new(),
            runtime_env: interpreter::Environment::new(),
        }
    }

    pub fn run(&mut self) {
        println!("Tygr REPL v0.1.0");
        println!("Type 'exit' to quit.");

        let stdin = io::stdin();
        let mut stdout = io::stdout();

        loop {
            print!("> ");
            if let Err(e) = stdout.flush() {
                eprintln!("Error flushing stdout: {}", e);
                break;
            }

            let mut input = String::new();
            if stdin.read_line(&mut input).is_err() {
                break;
            }

            let trimmed = input.trim();
            if trimmed.is_empty() {
                continue;
            }
            if trimmed == "exit" {
                break;
            }

            self.process_line(trimmed);
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

        let len = source.len();
        let input = make_input((0..len).into(), &tokens);
        let parser = parser::declaration();

        match parser.parse(input).into_result() {
            Ok(decl) => {
                let name_table = self.resolver.snapshot_name_table();

                match decl {
                    Declaration::Type(t) => {
                        if let Err(e) = self.resolver.resolve_type_alias(t) {
                            let _ = report_resolution_errors(source, &[e], name);
                        }
                    }

                    Declaration::Variant(v) => {
                        if let Err(e) = self.resolver.declare_variant(&v) {
                            let _ = report_resolution_errors(source, &[e], name);
                            return;
                        }
                        match self.resolver.define_variant(v) {
                            Err(e) => {
                                let _ = report_resolution_errors(source, &[e], name);
                            }
                            Ok(resolved_variant) => {
                                if let Err(e) = self.inferrer.register_variant(resolved_variant) {
                                    let _ = report_type_errors(source, &[e], name, &name_table);
                                }
                            }
                        }
                    }

                    Declaration::Statement(stmt) => {
                        match self.resolver.resolve_global_statement(stmt) {
                            Err(e) => {
                                let _ = report_resolution_errors(source, &[e], name);
                            }
                            Ok(resolved_stmt) => {
                                match self.inferrer.infer_global_statement(&mut self.type_env, resolved_stmt) {
                                    Err(e) => {
                                        let nt = self.resolver.snapshot_name_table();
                                        let _ = report_type_errors(source, &[e], name, &nt);
                                    }
                                    Ok(typed_stmt) => {
                                        match eval_statement(&mut self.runtime_env, &typed_stmt) {
                                            Ok(val) => {
                                                let nt = self.resolver.snapshot_name_table();
                                                println!("{}", ValueDisplay::new(&val, &nt));
                                            }
                                            Err(e) => println!("Runtime Error: {}", e),
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            Err(parse_errors) => {
                let _ = parser::format::report_errors(source, parse_errors.iter(), name);
            }
        }
    }
}