use crate::analysis::format::{report_resolution_errors, report_type_errors};
use crate::analysis::inference;
use crate::analysis::inference::Inferrer;
use crate::analysis::name_table::{LocalNameTable, NameTable};
use crate::analysis::resolver::{GlobalName, ResolutionError, Resolver};
use crate::custom::{CustomFn, CustomFnRegistry};
use crate::interpreter::{Value, ValueDisplay, eval_statement};
use crate::lexer::Lexer;
use crate::parser::{ReplStatement, SourceId, Span, make_input};
use crate::sources::FileSources;
use crate::visualize::typed::TypedAstVisualizer;
use crate::{interpreter, lexer, parser};
use chumsky::Parser;
use codespan_reporting::term::termcolor::{Color, ColorSpec, WriteColor};
use colored::Colorize;
#[cfg(feature = "cli")]
use rustyline::DefaultEditor;
#[cfg(feature = "cli")]
use rustyline::error::ReadlineError;
use std::rc::Rc;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ReplError {
    #[error("Failed to register custom function '{name}': {source}")]
    CustomFunctionRegistration {
        name: String,
        #[source]
        source: ResolutionError,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ReplMode {
    #[default]
    Normal,
    Ast,
}

pub struct Repl {
    resolver: Resolver,
    inferrer: Inferrer,
    type_env: inference::Environment,
    pub runtime_env: interpreter::Environment,
    custom_fns: CustomFnRegistry,
    mode: ReplMode,
}

impl Default for Repl {
    fn default() -> Self {
        Self::new()
    }
}

impl Repl {
    pub fn new() -> Self {
        Self {
            resolver: Resolver::default(),
            inferrer: Inferrer::default(),
            type_env: inference::Environment::new(),
            runtime_env: interpreter::Environment::default(),
            custom_fns: CustomFnRegistry::new(),
            mode: ReplMode::default(),
        }
    }

    pub fn set_mode(&mut self, mode: ReplMode) {
        self.mode = mode;
    }

    pub fn mode(&self) -> ReplMode {
        self.mode
    }

    pub fn snapshot_local_name_table(&self) -> LocalNameTable {
        self.resolver.snapshot_local_name_table()
    }

    pub fn register_custom_fn(&mut self, func: impl CustomFn) -> Result<(), ReplError> {
        let name_str = func.name().to_string();
        let scheme = func.type_scheme();
        let func = Rc::new(func);

        let name_id = self
            .resolver
            .register_global_custom(&name_str)
            .map_err(|source| ReplError::CustomFunctionRegistration {
                name: name_str.clone(),
                source,
            })?;

        self.inferrer.register_custom_type(
            GlobalName {
                krate: None,
                name: name_id,
            },
            scheme.clone(),
        );
        self.type_env.insert(
            GlobalName {
                krate: None,
                name: name_id,
            },
            scheme,
        );
        let custom_id = self.custom_fns.register(name_id, func);
        self.runtime_env.insert(
            GlobalName {
                krate: None,
                name: name_id,
            },
            Rc::new(Value::Custom(custom_id)),
        );

        Ok(())
    }

    #[cfg(feature = "cli")]
    pub fn run(&mut self) {
        println!("{} v{}", "Tygr REPL".bold().cyan(), "0.1.0".dimmed());
        println!("Type 'exit' or press Ctrl+D to quit.");
        println!("Commands: :ast (toggle AST mode), :mode (show current mode)\n");

        let mut rl = DefaultEditor::new().expect("Failed to initialize readline");
        let mut writer = termcolor::StandardStream::stdout(termcolor::ColorChoice::Auto);

        loop {
            let mode_indicator = match self.mode {
                ReplMode::Normal => "",
                ReplMode::Ast => "[ast]",
            };
            let prompt = format!("{}{} ", mode_indicator.dimmed(), "tygr>".bold().magenta());
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
                    if self.handle_command(trimmed, &mut writer) {
                        continue;
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

    fn handle_command(&mut self, input: &str, writer: &mut impl WriteColor) -> bool {
        if !input.starts_with(':') {
            return false;
        }

        match input {
            ":ast" => {
                self.mode = match self.mode {
                    ReplMode::Normal => {
                        let _ = writeln!(
                            writer,
                            "  {} AST visualization mode",
                            "Enabled".green().bold()
                        );
                        ReplMode::Ast
                    }
                    ReplMode::Ast => {
                        let _ = writeln!(
                            writer,
                            "  {} AST visualization mode",
                            "Disabled".yellow().bold()
                        );
                        ReplMode::Normal
                    }
                };
                true
            }
            ":mode" => {
                let mode_str = match self.mode {
                    ReplMode::Normal => "Normal",
                    ReplMode::Ast => "AST",
                };
                let _ = writeln!(writer, "  Current mode: {}", mode_str.cyan());
                true
            }
            ":help" => {
                let _ = writeln!(writer, "  {}", "Available commands:".bold());
                let _ = writeln!(
                    writer,
                    "    {} - Toggle AST visualization mode",
                    ":ast".cyan()
                );
                let _ = writeln!(writer, "    {} - Show current mode", ":mode".cyan());
                let _ = writeln!(writer, "    {} - Show this help", ":help".cyan());
                let _ = writeln!(writer, "    {} - Exit the REPL", "exit".cyan());
                true
            }
            _ => {
                let _ = writeln!(
                    writer,
                    "  {}: Unknown command '{}'",
                    "Error".red().bold(),
                    input
                );
                let _ = writeln!(writer, "  Type {} for available commands", ":help".cyan());
                true
            }
        }
    }

    pub fn process_line(&mut self, source: &str, writer: &mut impl WriteColor) {
        let name = "<repl>";
        let files = FileSources::single(name, source);

        let mut lexer = Lexer::new(source, SourceId::SYNTHETIC);
        let (tokens, lex_errors) = lexer.collect_all();
        if !lex_errors.is_empty() {
            let _ = lexer::format::report_errors(writer, &files, &lex_errors);
            return;
        }

        let input = make_input(
            Span {
                context: SourceId::SYNTHETIC,
                start: 0,
                end: source.len(),
            },
            &tokens,
        );
        let Ok(decl) = parser::repl().parse(input).into_result().map_err(|e| {
            let _ = parser::format::report_errors(writer, &files, e.iter());
        }) else {
            return;
        };

        self.execute_declaration(&files, decl, writer);
    }

    fn execute_declaration(
        &mut self,
        files: &FileSources,
        decl: ReplStatement,
        writer: &mut impl WriteColor,
    ) {
        let name_table = NameTable::with_global(self.resolver.snapshot_local_name_table());

        match decl {
            ReplStatement::Type(t) => {
                let res = self
                    .resolver
                    .declare_global_type_alias(&t)
                    .and_then(|_| self.resolver.define_global_type_alias(t));

                match res {
                    Err(e) => {
                        let _ = report_resolution_errors(writer, files, &[e]);
                    }
                    Ok(resolved) => {
                        if let Err(e) = self.inferrer.register_alias(resolved) {
                            let _ = report_type_errors(writer, files, &[e], &name_table);
                        }
                    }
                }
            }

            ReplStatement::Variant(v) => {
                let res = self
                    .resolver
                    .declare_global_variant(&v)
                    .and_then(|_| self.resolver.define_global_variant(v));

                match res {
                    Err(e) => {
                        let _ = report_resolution_errors(writer, files, &[e]);
                    }
                    Ok(resolved) => {
                        if let Err(e) = self.inferrer.register_variant(resolved) {
                            let _ = report_type_errors(writer, files, &[e], &name_table);
                        }
                    }
                }
            }

            ReplStatement::Statement(stmt) => self.execute_statement(files, stmt, writer),
        }
    }

    fn execute_statement(
        &mut self,
        files: &FileSources,
        stmt: parser::Statement,
        writer: &mut impl WriteColor,
    ) {
        let resolved = match self.resolver.resolve_global_statement(stmt) {
            Ok(s) => s,
            Err(e) => {
                let _ = report_resolution_errors(writer, files, &[e]);
                return;
            }
        };

        let typed = match self
            .inferrer
            .infer_global_statement(&mut self.type_env, resolved)
        {
            Ok(s) => s,
            Err(e) => {
                let nt = NameTable::with_global(self.resolver.snapshot_local_name_table());
                let _ = report_type_errors(writer, files, &[e], &nt);
                return;
            }
        };

        if self.mode == ReplMode::Ast {
            let nt = NameTable::with_global(self.resolver.snapshot_local_name_table());
            let mut visualizer = TypedAstVisualizer::new(&nt);
            let ast_output = visualizer.visualize_statement(&typed);
            let _ = writer.set_color(ColorSpec::new().set_fg(Some(Color::Cyan)));
            let _ = writeln!(writer, "{}", ast_output);
            let _ = writer.reset();
        }

        match eval_statement(&mut self.runtime_env, &typed, &self.custom_fns) {
            Ok(val) => {
                let nt = NameTable::with_global(self.resolver.snapshot_local_name_table());
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
