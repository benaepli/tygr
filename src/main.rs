use clap::Parser;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use std::fs;
use std::path::PathBuf;
use std::process;
use tygr::analysis::main_function::find_and_verify_main;
use tygr::compiler::{compile_constructor_program, compile_closure_program, compile_script, compile_typed_program};
use tygr::custom::CustomFnRegistry;
use tygr::interpreter;
use tygr::interpreter::{ValueDisplay, eval_groups, eval_statement, run_main};
use tygr::repl::Repl;
use tygr::visualize::closure::visualize_closure_ir;
use tygr::visualize::constructor::visualize_constructor_ir;
use tygr::visualize::typed::TypedAstVisualizer;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Cli {
    /// The path to the file to run. If omitted, starts a REPL.
    #[arg(required = false)]
    file_path: Option<PathBuf>,

    /// Run as a program (with a main function) instead of a script.
    #[arg(short, long)]
    program: bool,

    /// Visualize a compilation stage instead of running.
    #[arg(long, value_name = "STAGE")]
    visualize: Option<Stage>,
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

    match cli.file_path {
        Some(path) => match cli.visualize {
            Some(Stage::Typed) => visualize_typed(&path, cli.program),
            Some(Stage::Closure) => visualize_closure(&path),
            Some(Stage::Constructor) => visualize_constructor(&path),
            None if cli.program => run_program(&path),
            None => run_script(&path),
        },
        None => Repl::default().run(),
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
    let (program, name_table) = match compile_constructor_program(&input, &filename_str, &mut writer) {
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
