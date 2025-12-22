use clap::Parser;
use std::fs;
use std::path::PathBuf;
use std::process;
use tygr::compiler::compile_script;
use tygr::interpreter;
use tygr::interpreter::{ValueDisplay, eval_statement};
use tygr::repl::Repl;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Cli {
    /// The path to the script file to run. If omitted, starts a REPL.
    #[arg(required = false)]
    file_path: Option<PathBuf>,
}

fn main() {
    let cli = Cli::parse();

    match cli.file_path {
        Some(path) => run_script(path),
        None => Repl::default().run(),
    }
}

fn run_script(path: PathBuf) {
    let filename_str = path.display().to_string();

    let input = match fs::read_to_string(&path) {
        Ok(contents) => contents,
        Err(e) => {
            eprintln!("Error reading file '{}': {}", filename_str, e);
            process::exit(1);
        }
    };

    let (typed, name_table) = match compile_script(&input, &filename_str) {
        Err(e) => {
            eprintln!("Terminating with error: {}", e);
            return;
        }
        Ok(c) => c,
    };

    let mut env = interpreter::Environment::new();
    let mut last_result = None;

    for stmt in typed {
        match eval_statement(&mut env, &stmt) {
            Ok(result) => last_result = Some(result),
            Err(e) => {
                eprintln!("Runtime error: {}", e);
                process::exit(1);
            }
        }
    }

    if let Some(result) = last_result {
        println!(
            "Program result: {}",
            ValueDisplay::new(&result, &name_table)
        );
    }
}
