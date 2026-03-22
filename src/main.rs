// cranelisp: pipeline orchestration, batch mode, REPL.

use std::path::Path;
use std::process;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    match parse_args(&args) {
        RunMode::Repl => cranelisp::repl::run_repl(),
        RunMode::RunFile { path, no_cache } => run_file(&path, no_cache),
        RunMode::Link { path } => link_file(&path),
        RunMode::Error(msg) => {
            eprintln!("error: {msg}");
            eprintln!("usage: cranelisp [--run <file.cl>] [--link <file.cl>]");
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
    /// Compile and link a source file into a standalone executable.
    Link { path: String },
    /// Invalid arguments.
    Error(String),
}

/// Parse command-line arguments.
///
/// Supported forms:
///   cranelisp                       -> REPL
///   cranelisp --run file            -> batch compile and execute
///   cranelisp --no-cache --run file -> batch compile without module caching
///   cranelisp --link file           -> compile and link into standalone executable
fn parse_args(args: &[String]) -> RunMode {
    let mut no_cache = false;
    let mut run_file: Option<String> = None;
    let mut link_file: Option<String> = None;
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
            "--link" => {
                if i + 1 < args.len() {
                    link_file = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    return RunMode::Error("--link requires a file argument".to_string());
                }
            }
            other => {
                return RunMode::Error(format!("unexpected argument: {other}"));
            }
        }
    }

    // Validate mutually exclusive modes.
    if run_file.is_some() && link_file.is_some() {
        return RunMode::Error("--run and --link cannot be used together".to_string());
    }

    if let Some(path) = link_file {
        if no_cache {
            return RunMode::Error(
                "--no-cache is not supported with --link (linking requires cached .o files)"
                    .to_string(),
            );
        }
        return RunMode::Link { path };
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

    // Project root = current working directory (the directory from which the
    // user invokes the compiler). This is the natural location for stdlib/,
    // .cranelisp-cache/, and project configuration files.
    // Fixes FIXME(/int) on design/int/pipeline-convergence.md:345.
    let project_root = &std::env::current_dir().unwrap_or_else(|_| std::path::PathBuf::from("."));
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

/// Compile and link a source file into a standalone executable.
///
/// Per design/backend/executable-generation.md:
/// 1. Compile the module graph (producing cached .o files)
/// 2. Validate that entry module has a `main` function
/// 3. Generate a startup stub .o
/// 4. Link all .o files + runtime bundle into a native executable
fn link_file(path: &str) {
    let file_path = Path::new(path);

    if !file_path.exists() {
        eprintln!("error: file not found: {path}");
        process::exit(1);
    }

    let project_root = &std::env::current_dir().unwrap_or_else(|_| std::path::PathBuf::from("."));
    let lib_dirs = cranelisp::pipeline::assemble_lib_dirs(project_root);
    let cache_dir = project_root.join(".cranelisp-cache");

    // Step 1: Compile the module graph (produces cached .o files, no execution).
    let compile_result = match cranelisp::pipeline::compile_for_link(
        file_path,
        &lib_dirs,
        &cache_dir,
    ) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error: {e}");
            process::exit(1);
        }
    };

    // Print warnings.
    for w in &compile_result.warnings {
        eprintln!("warning: {}", w.message);
    }

    // Step 2: Validate main function in entry module.
    let main_return = match cranelisp::exe::validate_main(&compile_result.entry_symbols) {
        Ok(kind) => kind,
        Err(e) => {
            eprintln!("error: {e}");
            process::exit(1);
        }
    };

    // Step 3: Generate startup stub .o
    let platform_manifest_names =
        cranelisp::exe::collect_platform_manifest_names(&compile_result.module_structures);
    let main_returns_io = main_return == cranelisp::exe::MainReturnKind::Io;
    let startup_bytes =
        match cranelisp::exe::generate_startup_object(&platform_manifest_names, main_returns_io) {
            Ok(bytes) => bytes,
            Err(e) => {
                eprintln!("error: failed to generate startup stub: {e}");
                process::exit(1);
            }
        };

    // Write startup stub to a temp file.
    let startup_o_path = cache_dir.join("_startup.o");
    if let Err(e) = std::fs::create_dir_all(&cache_dir) {
        eprintln!("error: cannot create cache directory: {e}");
        process::exit(1);
    }
    if let Err(e) = std::fs::write(&startup_o_path, &startup_bytes) {
        eprintln!("error: cannot write startup stub: {e}");
        process::exit(1);
    }

    // Step 4: Locate the runtime bundle library.
    let bundle_lib = match cranelisp::exe::find_bundle_lib() {
        Ok(p) => p,
        Err(e) => {
            eprintln!("error: {e}");
            process::exit(1);
        }
    };

    // Step 5: Collect platform rlibs.
    let platform_rlibs =
        cranelisp::exe::find_platform_rlibs(&compile_result.module_structures);

    // Step 6: Derive output path from entry file stem (in current directory).
    let output_path = std::path::PathBuf::from(
        file_path.file_stem().unwrap_or(std::ffi::OsStr::new("a.out")),
    );
    if let Err(e) = cranelisp::exe::link_executable(
        &output_path,
        &compile_result.module_o_paths,
        &startup_o_path,
        &bundle_lib,
        &platform_rlibs,
    ) {
        eprintln!("error: {e}");
        process::exit(1);
    }

    eprintln!(
        "; Linked: {}",
        output_path.display()
    );
}
