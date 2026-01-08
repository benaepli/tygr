use clap::Parser;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::process;
use tygr::analysis::main_function::find_and_verify_main;
use tygr::compiler::compile_script;
use tygr::custom::CustomFnRegistry;
use tygr::interpreter;
use tygr::interpreter::{ValueDisplay, eval_groups, eval_statement, run_main};
use tygr::ir::stage::{
    AnfStage, ConstructorStage, DecisionTreeStage, MonomorphizedStage, PatternStage,
};
use tygr::manifest::{Manifest, ProjectType};
use tygr::module::CrateCompiler;
use tygr::repl::Repl;
use tygr::visualize::{anf, constructor, decision_tree, pattern, typed};

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
        /// The path to the program file. If omitted, uses the current project's Tygr.toml.
        file: Option<PathBuf>,
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
    Constructor,
    Pattern,
    DecisionTree,
    Anf,
    Monomorphized,
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
        Some(Commands::Visualize { stage, file }) => match file {
            Some(path) => visualize_file(&path, stage),
            None => visualize_project(stage),
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
                        run_project(&manifest_path);
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

fn compile_file(path: &PathBuf) -> (tygr::analysis::inference::TypedCrate, CrateCompiler) {
    let input = read_file(path);
    let mut compiler = CrateCompiler::new();
    let mut writer = StandardStream::stderr(ColorChoice::Auto);

    match compiler.compile_source(input, path.to_string_lossy().as_ref(), HashMap::new()) {
        Ok(typed) => (typed, compiler),
        Err(e) => {
            let _ = tygr::module::format::report_compile_error(&mut writer, &compiler, &e);
            process::exit(1);
        }
    }
}

fn run_program(path: &PathBuf) {
    let (typed, compiler) = compile_file(path);
    let name_table = compiler.name_table();

    let main_name = match find_and_verify_main(&typed.groups, name_table) {
        Ok(name) => name,
        Err(e) => {
            eprintln!("Error: {}", e);
            process::exit(1);
        }
    };

    let mut env = interpreter::Environment::new();
    let custom_fns = CustomFnRegistry::new();

    if let Err(e) = eval_groups(&mut env, typed.groups, &custom_fns) {
        eprintln!("Runtime error: {}", e);
        process::exit(1);
    }

    match run_main(&mut env, main_name, &custom_fns) {
        Ok(result) => {
            println!("Program result: {}", ValueDisplay::new(&result, name_table));
        }
        Err(e) => {
            eprintln!("Runtime error: {}", e);
            process::exit(1);
        }
    }
}

fn visualize_file(path: &PathBuf, stage: Stage) {
    let (typed, compiler) = compile_file(path);
    let name_table = compiler.name_table();

    let output = match stage {
        Stage::Typed => typed::visualize_crate(&typed, name_table),
        Stage::Constructor => {
            let ir = compiler.compile_to::<ConstructorStage>(typed);
            constructor::visualize_crate(&ir, name_table)
        }
        Stage::Pattern => {
            let ir = compiler.compile_to::<PatternStage>(typed);
            pattern::visualize_crate(&ir, name_table)
        }
        Stage::DecisionTree => {
            let ir = compiler.compile_to::<DecisionTreeStage>(typed);
            decision_tree::visualize_crate(&ir, name_table)
        }
        Stage::Anf => {
            let ir = compiler.compile_to::<AnfStage>(typed);
            anf::visualize_crate(&ir, name_table)
        }
        Stage::Monomorphized => {
            let main_name = match find_and_verify_main(&typed.groups, name_table) {
                Ok(name) => name,
                Err(e) => {
                    eprintln!("Error: {}", e);
                    process::exit(1);
                }
            };
            let ir = compiler.compile_program_to::<MonomorphizedStage>(vec![typed], main_name);
            anf::visualize_program(&ir, name_table)
        }
    };

    println!("{}", output);
}

fn visualize_project(stage: Stage) {
    let current_dir = std::env::current_dir().unwrap_or_else(|e| {
        eprintln!("Error getting current directory: {}", e);
        process::exit(1);
    });
    let manifest_path = current_dir.join("Tygr.toml");

    if !manifest_path.exists() {
        eprintln!("Error: Tygr.toml not found in current directory, and no file provided.");
        process::exit(1);
    }

    let mut compiler = CrateCompiler::new();
    let mut writer = StandardStream::stderr(ColorChoice::Auto);

    let crates = match compiler.compile_project(&manifest_path) {
        Err(e) => {
            let _ = tygr::module::format::report_compile_error(&mut writer, &compiler, &e);
            process::exit(1);
        }
        Ok(c) => c,
    };

    let name_table = compiler.name_table();

    // For monomorphized stage, we need all crates and the main function
    if let Stage::Monomorphized = stage {
        let root_crate = crates
            .last()
            .expect("at least one crate should be compiled");
        let main_name = match find_and_verify_main(&root_crate.groups, name_table) {
            Ok(name) => name,
            Err(e) => {
                eprintln!("Error: {}", e);
                process::exit(1);
            }
        };
        let ir = compiler.compile_program_to::<MonomorphizedStage>(crates, main_name);
        let output = anf::visualize_program(&ir, name_table);
        println!("{}", output);
        return;
    }

    // Visualize the root crate (the last one compiled)
    let typed = crates
        .into_iter()
        .last()
        .expect("at least one crate should be compiled");

    let output = match stage {
        Stage::Typed => typed::visualize_crate(&typed, name_table),
        Stage::Constructor => {
            let ir = compiler.compile_to::<ConstructorStage>(typed);
            constructor::visualize_crate(&ir, name_table)
        }
        Stage::Pattern => {
            let ir = compiler.compile_to::<PatternStage>(typed);
            pattern::visualize_crate(&ir, name_table)
        }
        Stage::DecisionTree => {
            let ir = compiler.compile_to::<DecisionTreeStage>(typed);
            decision_tree::visualize_crate(&ir, name_table)
        }
        Stage::Anf => {
            let ir = compiler.compile_to::<AnfStage>(typed);
            anf::visualize_crate(&ir, name_table)
        }
        Stage::Monomorphized => unreachable!(), // Handled above
    };
    println!("{}", output);
}

fn run_script(path: &PathBuf) {
    let input = read_file(path);

    let mut writer = StandardStream::stderr(ColorChoice::Auto);
    let (typed, name_table) = match compile_script(&input, &path.to_string_lossy(), &mut writer) {
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

fn run_project(manifest_path: &PathBuf) {
    let mut compiler = CrateCompiler::new();
    let mut writer = StandardStream::stderr(ColorChoice::Auto);

    let crates = match compiler.compile_project(manifest_path) {
        Err(e) => {
            let _ = tygr::module::format::report_compile_error(&mut writer, &compiler, &e);
            process::exit(1);
        }
        Ok(c) => c,
    };

    let mut env = interpreter::Environment::new();
    let custom_fns = CustomFnRegistry::new();

    // Evaluate all crates in order. The last one is the root binary crate.
    for krate in &crates {
        if let Err(e) = eval_groups(&mut env, krate.groups.clone(), &custom_fns) {
            eprintln!("Runtime error (crate {}): {}", krate.crate_id.0, e);
            process::exit(1);
        }
    }

    let root_crate = crates
        .last()
        .expect("at least one crate should be compiled");
    let name_table = compiler.name_table();

    let main_name = match find_and_verify_main(&root_crate.groups, name_table) {
        Ok(name) => name,
        Err(e) => {
            eprintln!("Error: {}", e);
            process::exit(1);
        }
    };

    match interpreter::run_main(&mut env, main_name, &custom_fns) {
        Ok(result) => {
            println!("Program result: {}", ValueDisplay::new(&result, name_table));
        }
        Err(e) => {
            eprintln!("Runtime error: {}", e);
            process::exit(1);
        }
    }
}
