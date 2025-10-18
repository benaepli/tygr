use clap::Parser;
use std::fs;
use std::path::PathBuf;
use std::process;
use tygr::compiler::compile;
use tygr::interpreter::run;

/// A custom interpreter for a simple language
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Cli {
    /// The path to the script file to run
    #[arg(required = true)]
    file_path: PathBuf,
}

fn main() {
    let cli = Cli::parse();
    let filename_str = cli.file_path.display().to_string();

    let input = match fs::read_to_string(&cli.file_path) {
        Ok(contents) => contents,
        Err(e) => {
            eprintln!("Error reading file '{}': {}", filename_str, e);
            process::exit(1);
        }
    };

    let compiled = match compile(&input, &filename_str) {
        Err(e) => {
            eprintln!("Terminating with error: {}", e);
            return;
        }
        Ok(c) => c,
    };

    match run(&compiled) {
        Ok(result) => println!("Program result: {}", result),
        Err(e) => {
            eprintln!("Runtime error: {}", e);
            process::exit(1);
        }
    }
}
