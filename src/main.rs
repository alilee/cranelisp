// cranelisp: pipeline orchestration, batch mode, REPL.

use std::path::Path;
use std::process;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    match parse_args(&args) {
        RunMode::Repl => cranelisp::repl::run_repl(),
        RunMode::RunFile { path, no_cache } => run_file(&path, no_cache),
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
    RunFile {
        path: String,
        /// When true, skip module cache checking and writing.
        no_cache: bool,
    },
    /// Invalid arguments.
    Error(String),
}

/// Parse command-line arguments.
///
/// Supported forms:
///   cranelisp                       -> REPL
///   cranelisp --run file            -> batch compile and execute
///   cranelisp --no-cache --run file -> batch compile without module caching
fn parse_args(args: &[String]) -> RunMode {
    let mut no_cache = false;
    let mut run_file: Option<String> = None;
    let mut i = 1;

    while i < args.len() {
        match args[i].as_str() {
            "--no-cache" => {
                no_cache = true;
                i += 1;
            }
            "--run" => {
                if i + 1 < args.len() {
                    run_file = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    return RunMode::Error("--run requires a file argument".to_string());
                }
            }
            other => {
                return RunMode::Error(format!("unexpected argument: {other}"));
            }
        }
    }

    match run_file {
        Some(path) => RunMode::RunFile { path, no_cache },
        None if no_cache => {
            RunMode::Error("--no-cache requires --run <file>".to_string())
        }
        None => RunMode::Repl,
    }
}

/// Compile and execute a source file via the module graph pipeline.
fn run_file(path: &str, no_cache: bool) {
    let file_path = Path::new(path);

    if !file_path.exists() {
        eprintln!("error: file not found: {path}");
        process::exit(1);
    }

    // Project root = entry file's parent directory (spec §8.11.2).
    // Lib directories are configured externally via CRANELISP_LIB or
    // project config (spec §8.11.3). assemble_lib_dirs applies the
    // SHOULD-level {project_root}/stdlib/ fallback.
    let project_root = file_path.parent().unwrap_or(Path::new("."));
    let lib_dirs = cranelisp::pipeline::assemble_lib_dirs(project_root);
    let cache_config = if no_cache {
        cranelisp::pipeline::CacheConfig::Disabled
    } else {
        cranelisp::pipeline::CacheConfig::Enabled {
            cache_dir: project_root.join(".cranelisp-cache"),
        }
    };
    match cranelisp::pipeline::compile_module_graph_cached(file_path, &lib_dirs, &cache_config) {
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
