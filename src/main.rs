use clap::Parser;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use std::fs;
use std::path::PathBuf;
use std::process;
use tygr::analysis::main_function::find_and_verify_main;
use tygr::compiler::{
    compile_closure_program, compile_constructor_program, compile_script, compile_typed_program,
};
use tygr::custom::CustomFnRegistry;
use tygr::interpreter;
use tygr::interpreter::{ValueDisplay, eval_groups, eval_statement, run_main};
use tygr::repl::Repl;
use tygr::visualize::closure::visualize_closure_ir;
use tygr::visualize::constructor::visualize_constructor_ir;
use tygr::visualize::typed::TypedAstVisualizer;

use tygr::manifest::{Manifest, ProjectType};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(clap::Subcommand, Debug)]
enum Commands {
    /// Starts a REPL.
    Repl,

    /// Runs a Tygr file as a script.
    Script {
        /// The path to the script file.
        file: PathBuf,
    },

    /// Visualizes a compilation stage for a program.
    Visualize {
        /// The stage to visualize.
        stage: Stage,
        /// The path to the program file.
        file: PathBuf,
    },

    /// Runs a Tygr program (via manifest or direct file).
    Run {
        /// Run a specific file as a program (bypass manifest).
        #[arg(long)]
        file: Option<PathBuf>,
    },
}

#[derive(Clone, Debug, clap::ValueEnum)]
enum Stage {
    Typed,
    Closure,
    Constructor,
}

fn read_file(path: &PathBuf) -> String {
    fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("Error reading file '{}': {}", path.display(), e);
        process::exit(1);
    })
}

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Some(Commands::Repl) | None => Repl::default().run(),
        Some(Commands::Script { file }) => run_script(&file),
        Some(Commands::Visualize { stage, file }) => match stage {
            Stage::Typed => visualize_typed(&file, true),
            Stage::Closure => visualize_closure(&file),
            Stage::Constructor => visualize_constructor(&file),
        },
        Some(Commands::Run { file }) => match file {
            Some(path) => run_program(&path),
            None => {
                let current_dir = std::env::current_dir().unwrap_or_else(|e| {
                    eprintln!("Error getting current directory: {}", e);
                    process::exit(1);
                });
                let manifest_path = current_dir.join("Tygr.toml");
                match Manifest::load(&manifest_path) {
                    Ok(manifest) => {
                        if manifest.project_type() != ProjectType::Binary {
                            eprintln!(
                                "Error: Project is not a binary. Only binary projects can be run."
                            );
                            process::exit(1);
                        }
                        let root = manifest.crate_root(&current_dir);
                        run_program(&root);
                    }
                    Err(e) => {
                        eprintln!(
                            "Error: Tygr.toml not found in current directory, and no --file provided.\n{}",
                            e
                        );
                        process::exit(1);
                    }
                }
            }
        },
    }
}

fn run_program(path: &PathBuf) {
    let filename_str = path.display().to_string();
    let input = read_file(path);

    let mut writer = StandardStream::stderr(ColorChoice::Auto);
    let typed = match compile_typed_program(&input, &filename_str, &mut writer) {
        Err(e) => {
            eprintln!("Terminating with error: {}", e);
            process::exit(1);
        }
        Ok(c) => c,
    };
    let groups = typed.groups;
    let name_table = typed.name_table;

    let main_name = match find_and_verify_main(&groups, &name_table) {
        Ok(name) => name,
        Err(e) => {
            eprintln!("Error: {}", e);
            process::exit(1);
        }
    };

    let mut env = interpreter::Environment::new();
    let custom_fns = CustomFnRegistry::new();

    if let Err(e) = eval_groups(&mut env, groups, &custom_fns) {
        eprintln!("Runtime error: {}", e);
        process::exit(1);
    }

    match run_main(&mut env, main_name, &custom_fns) {
        Ok(result) => {
            println!(
                "Program result: {}",
                ValueDisplay::new(&result, &name_table)
            );
        }
        Err(e) => {
            eprintln!("Runtime error: {}", e);
            process::exit(1);
        }
    }
}

fn visualize_closure(path: &PathBuf) {
    let filename_str = path.display().to_string();
    let input = read_file(path);

    let mut writer = StandardStream::stderr(ColorChoice::Auto);
    let (program, name_table) = match compile_closure_program(&input, &filename_str, &mut writer) {
        Err(e) => {
            eprintln!("Terminating with error: {}", e);
            process::exit(1);
        }
        Ok(c) => c,
    };

    println!("{}", visualize_closure_ir(&program, &name_table));
}

fn visualize_constructor(path: &PathBuf) {
    let filename_str = path.display().to_string();
    let input = read_file(path);

    let mut writer = StandardStream::stderr(ColorChoice::Auto);
    let (program, name_table) =
        match compile_constructor_program(&input, &filename_str, &mut writer) {
            Err(e) => {
                eprintln!("Terminating with error: {}", e);
                process::exit(1);
            }
            Ok(c) => c,
        };

    println!("{}", visualize_constructor_ir(&program, &name_table));
}

fn visualize_typed(path: &PathBuf, is_program: bool) {
    let filename_str = path.display().to_string();
    let input = read_file(path);
    let mut writer = StandardStream::stderr(ColorChoice::Auto);

    if is_program {
        let typed = match compile_typed_program(&input, &filename_str, &mut writer) {
            Err(e) => {
                eprintln!("Terminating with error: {}", e);
                process::exit(1);
            }
            Ok(c) => c,
        };
        let mut visualizer = TypedAstVisualizer::new(&typed.name_table);
        for group in &typed.groups {
            println!("{}", visualizer.visualize_group(group));
        }
    } else {
        let (typed, name_table) = match compile_script(&input, &filename_str, &mut writer) {
            Err(e) => {
                eprintln!("Terminating with error: {}", e);
                process::exit(1);
            }
            Ok(c) => c,
        };
        let mut visualizer = TypedAstVisualizer::new(&name_table);
        for stmt in &typed {
            println!("{}", visualizer.visualize_statement(stmt));
        }
    }
}

fn run_script(path: &PathBuf) {
    let filename_str = path.display().to_string();
    let input = read_file(path);

    let mut writer = StandardStream::stderr(ColorChoice::Auto);
    let (typed, name_table) = match compile_script(&input, &filename_str, &mut writer) {
        Err(e) => {
            eprintln!("Terminating with error: {}", e);
            process::exit(1);
        }
        Ok(c) => c,
    };

    let mut env = interpreter::Environment::new();
    let custom_fns = CustomFnRegistry::new();
    let mut last_result = None;

    for stmt in typed {
        match eval_statement(&mut env, &stmt, &custom_fns) {
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
