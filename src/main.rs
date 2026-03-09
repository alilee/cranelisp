// cranelisp: pipeline orchestration, batch mode, REPL.

use std::path::Path;
use std::process;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    match parse_args(&args) {
        RunMode::Repl => cranelisp::repl::run_repl(),
        RunMode::RunFile(path) => run_file(&path),
        RunMode::Error(msg) => {
            eprintln!("error: {msg}");
            eprintln!("usage: cranelisp [--run <file.cl>]");
            process::exit(1);
        }
    }
}

/// Parsed command-line mode.
enum RunMode {
    /// Start the interactive REPL (no arguments).
    Repl,
    /// Compile and execute a source file.
    RunFile(String),
    /// Invalid arguments.
    Error(String),
}

/// Parse command-line arguments.
///
/// Supported forms:
///   cranelisp              -> REPL
///   cranelisp --run file   -> batch compile and execute
fn parse_args(args: &[String]) -> RunMode {
    match args.len() {
        1 => RunMode::Repl,
        3 if args[1] == "--run" => RunMode::RunFile(args[2].clone()),
        _ => {
            if args.len() >= 2 && args[1] == "--run" {
                RunMode::Error("--run requires a file argument".to_string())
            } else {
                RunMode::Error(format!("unexpected argument: {}", args[1]))
            }
        }
    }
}

/// Compile and execute a source file via the module graph pipeline.
fn run_file(path: &str) {
    let file_path = Path::new(path);

    if !file_path.exists() {
        eprintln!("error: file not found: {path}");
        process::exit(1);
    }

    let project_root = file_path.parent().unwrap_or(Path::new("."));
    let lib_dirs = cranelisp::pipeline::assemble_lib_dirs(project_root);
    match cranelisp::pipeline::compile_module_graph(file_path, &lib_dirs) {
        Ok(result) => {
            // Print warnings to stderr.
            for w in &result.warnings {
                eprintln!("warning: {}", w.message);
            }

            // Print the result value to stdout (for batch mode).
            let display = cranelisp::repl::format_result(result.value, &result.ty);
            println!("{display}");

            // Determine exit code from the result.
            let exit_code = cranelisp::pipeline::determine_exit_code(result.value, &result.ty);
            if exit_code != 0 {
                process::exit(exit_code);
            }
        }
        Err(e) => {
            eprintln!("error: {e}");
            process::exit(1);
        }
    }
}
