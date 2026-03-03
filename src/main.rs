use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process;

use cranelisp::error::format_error;

/// Resolve a CLI entry path: append `.cl` if no extension, create file if missing.
fn resolve_entry_path(raw: &str) -> PathBuf {
    let path = Path::new(raw);
    let path = if path.extension().is_none() {
        path.with_extension("cl")
    } else {
        path.to_path_buf()
    };
    if !path.exists() {
        if let Err(e) = fs::File::create(&path) {
            eprintln!("Error: cannot create '{}': {}", path.display(), e);
            process::exit(1);
        }
    }
    path
}

fn main() {
    let args: Vec<String> = env::args().collect();

    // Parse flags
    let mut positional = Vec::new();
    let mut run_mode = false;
    let mut exe_output: Option<String> = None;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--cwd" => {
                if i + 1 >= args.len() {
                    eprintln!("Error: --cwd requires a directory argument");
                    process::exit(1);
                }
                let dir = &args[i + 1];
                if let Err(e) = env::set_current_dir(dir) {
                    eprintln!("Error: cannot change to directory '{}': {}", dir, e);
                    process::exit(1);
                }
                i += 2;
            }
            "--run" => {
                run_mode = true;
                i += 1;
            }
            "--exe" => {
                // Optional output path: --exe [path]
                // If next arg exists and doesn't look like a flag or .cl file, consume it
                if i + 1 < args.len()
                    && !args[i + 1].starts_with('-')
                    && !args[i + 1].ends_with(".cl")
                {
                    exe_output = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    exe_output = Some(String::new()); // derive from entry path
                    i += 1;
                }
            }
            _ => {
                positional.push(&args[i]);
                i += 1;
            }
        }
    }

    if let Some(output) = exe_output {
        // cranelisp --exe [output] [file.cl]
        let entry_path = match positional.len() {
            0 => resolve_entry_path("user.cl"),
            1 => resolve_entry_path(positional[0]),
            _ => {
                eprintln!("Usage: cranelisp --exe [output] [file.cl]");
                process::exit(1);
            }
        };
        let output_path = if output.is_empty() {
            // Derive from entry: same directory, same stem, no extension
            entry_path.with_extension("")
        } else {
            PathBuf::from(&output)
        };
        build_exe(&entry_path, &output_path);
    } else {
        match (run_mode, positional.len()) {
            // cranelisp -- bare REPL
            (false, 0) => cranelisp::repl::run(),
            // cranelisp foo.cl -- REPL with file
            // cranelisp some/dir -- REPL rooted in directory
            (false, 1) => {
                let raw = positional[0];
                let path = Path::new(raw);
                if path.is_dir() || raw.ends_with('/') {
                    if !path.exists() {
                        if let Err(e) = fs::create_dir_all(path) {
                            eprintln!("Error: cannot create directory '{}': {}", path.display(), e);
                            process::exit(1);
                        }
                    }
                    cranelisp::repl::run_with_dir(path);
                } else {
                    cranelisp::repl::run_with_file(&resolve_entry_path(raw));
                }
            }
            // cranelisp --run foo.cl -- batch mode
            // cranelisp --run some/dir -- batch mode with user.cl in directory
            (true, 1) => {
                let raw = positional[0];
                let path = Path::new(raw);
                if path.is_dir() || raw.ends_with('/') {
                    if !path.exists() {
                        if let Err(e) = fs::create_dir_all(path) {
                            eprintln!("Error: cannot create directory '{}': {}", path.display(), e);
                            process::exit(1);
                        }
                    }
                    run_batch(&resolve_entry_path(
                        &path.join("user").to_string_lossy(),
                    ));
                } else {
                    run_batch(&resolve_entry_path(raw));
                }
            }
            // cranelisp --run -- batch mode with user.cl in CWD
            (true, 0) => run_batch(&resolve_entry_path("user.cl")),
            _ => {
                eprintln!("Usage: cranelisp [--run] [--exe <output>] [--cwd <dir>] [file.cl]");
                process::exit(1);
            }
        }
    }
}

fn run_batch(path: &Path) {
    if let Err(e) = cranelisp::batch::run_project(path) {
        // Read source for error context formatting
        let source = fs::read_to_string(path).unwrap_or_default();
        eprintln!("{}", format_error(&source, &e));
        process::exit(1);
    }
}

fn build_exe(entry_path: &Path, output_path: &Path) {
    if let Err(e) = cranelisp::batch::build_executable(entry_path, output_path) {
        let source = fs::read_to_string(entry_path).unwrap_or_default();
        eprintln!("{}", format_error(&source, &e));
        process::exit(1);
    }
}
