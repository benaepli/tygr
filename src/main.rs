use clap::Parser;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use std::fs;
use std::path::PathBuf;
use std::process;
use tygr::analysis::main_function::find_and_verify_main;
use tygr::compiler::{compile_program, compile_script, compile_typed_program};
use tygr::custom::CustomFnRegistry;
use tygr::interpreter;
use tygr::interpreter::{ValueDisplay, eval_groups, eval_statement, run_main};
use tygr::repl::Repl;
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

    /// Visualize the closure-converted IR (only for programs).
    #[arg(long)]
    visualize_closure: bool,

    /// Visualize the typed AST.
    #[arg(long)]
    visualize_typed: bool,
}

fn main() {
    let cli = Cli::parse();

    match cli.file_path {
        Some(path) => {
            if cli.visualize_closure {
                visualize_closure(path)
            } else if cli.visualize_typed {
                if cli.program {
                    visualize_typed_program(path)
                } else {
                    visualize_typed_script(path)
                }
            } else if cli.program {
                run_program(path)
            } else {
                run_script(path)
            }
        }
        None => Repl::default().run(),
    }
}

fn run_program(path: PathBuf) {
    let filename_str = path.display().to_string();

    let input = match fs::read_to_string(&path) {
        Ok(contents) => contents,
        Err(e) => {
            eprintln!("Error reading file '{}': {}", filename_str, e);
            process::exit(1);
        }
    };

    let mut writer = StandardStream::stderr(ColorChoice::Auto);
    let typed = match compile_typed_program(&input, &filename_str, &mut writer) {
        Err(e) => {
            eprintln!("Terminating with error: {}", e);
            return;
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

fn visualize_closure(path: PathBuf) {
    use tygr::visualize::closure::visualize_closure_ir;

    let filename_str = path.display().to_string();

    let input = match fs::read_to_string(&path) {
        Ok(contents) => contents,
        Err(e) => {
            eprintln!("Error reading file '{}': {}", filename_str, e);
            process::exit(1);
        }
    };

    let mut writer = StandardStream::stderr(ColorChoice::Auto);
    let (program, name_table) = match compile_program(&input, &filename_str, &mut writer) {
        Err(e) => {
            eprintln!("Terminating with error: {}", e);
            return;
        }
        Ok(c) => c,
    };

    println!("{}", visualize_closure_ir(&program, &name_table));
}

fn visualize_typed_program(path: PathBuf) {
    let filename_str = path.display().to_string();

    let input = match fs::read_to_string(&path) {
        Ok(contents) => contents,
        Err(e) => {
            eprintln!("Error reading file '{}': {}", filename_str, e);
            process::exit(1);
        }
    };

    let mut writer = StandardStream::stderr(ColorChoice::Auto);
    let typed = match compile_typed_program(&input, &filename_str, &mut writer) {
        Err(e) => {
            eprintln!("Terminating with error: {}", e);
            return;
        }
        Ok(c) => c,
    };

    let mut visualizer = TypedAstVisualizer::new(&typed.name_table);
    for group in &typed.groups {
        println!("{}", visualizer.visualize_group(group));
    }
}

fn visualize_typed_script(path: PathBuf) {
    let filename_str = path.display().to_string();

    let input = match fs::read_to_string(&path) {
        Ok(contents) => contents,
        Err(e) => {
            eprintln!("Error reading file '{}': {}", filename_str, e);
            process::exit(1);
        }
    };

    let mut writer = StandardStream::stderr(ColorChoice::Auto);
    let (typed, name_table) = match compile_script(&input, &filename_str, &mut writer) {
        Err(e) => {
            eprintln!("Terminating with error: {}", e);
            return;
        }
        Ok(c) => c,
    };

    let mut visualizer = TypedAstVisualizer::new(&name_table);
    for stmt in &typed {
        println!("{}", visualizer.visualize_statement(stmt));
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

    let mut writer = StandardStream::stderr(ColorChoice::Auto);
    let (typed, name_table) = match compile_script(&input, &filename_str, &mut writer) {
        Err(e) => {
            eprintln!("Terminating with error: {}", e);
            return;
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
