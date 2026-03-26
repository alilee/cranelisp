// cranelisp: pipeline orchestration, batch mode, REPL.

use std::path::Path;
use std::process;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (mode, no_color) = parse_args(&args);
    cranelisp::style::init_color(no_color);
    match mode {
        RunMode::Repl => cranelisp::repl::run_repl(),
        RunMode::RunFile { path, no_cache } => run_file(&path, no_cache),
        RunMode::Link { path } => link_file(&path),
        RunMode::Error(msg) => {
            eprintln!("error: {msg}");
            eprintln!("usage: cranelisp [--run <file.cl>] [--link <file.cl>] [--no-color]");
            process::exit(1);
        }
    }
}

enum RunMode { Repl, RunFile { path: String, no_cache: bool }, Link { path: String }, Error(String) }

fn parse_args(args: &[String]) -> (RunMode, bool) {
    let mut no_cache = false;
    let mut no_color = false;
    let mut run_file: Option<String> = None;
    let mut link_file: Option<String> = None;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--no-cache" => { no_cache = true; i += 1; }
            "--no-color" => { no_color = true; i += 1; }
            "--run" => { if i+1 < args.len() { run_file = Some(args[i+1].clone()); i += 2; } else { return (RunMode::Error("--run requires a file argument".into()), no_color); } }
            "--link" => { if i+1 < args.len() { link_file = Some(args[i+1].clone()); i += 2; } else { return (RunMode::Error("--link requires a file argument".into()), no_color); } }
            other => { return (RunMode::Error(format!("unexpected argument: {other}")), no_color); }
        }
    }
    if run_file.is_some() && link_file.is_some() { return (RunMode::Error("--run and --link cannot be used together".into()), no_color); }
    if let Some(path) = link_file {
        if no_cache { return (RunMode::Error("--no-cache is not supported with --link".into()), no_color); }
        return (RunMode::Link { path }, no_color);
    }
    let mode = match run_file {
        Some(path) => RunMode::RunFile { path, no_cache },
        None if no_cache => RunMode::Error("--no-cache requires --run <file>".into()),
        None => RunMode::Repl,
    };
    (mode, no_color)
}

fn run_file(path: &str, _no_cache: bool) {
    let file_path = Path::new(path);
    if !file_path.exists() { eprintln!("error: file not found: {path}"); process::exit(1); }
    let project_root = &std::env::current_dir().unwrap_or_else(|_| std::path::PathBuf::from("."));
    let lib_dirs = cranelisp::pipeline::assemble_lib_dirs(project_root);

    match cranelisp::pipeline_v2::run_batch_v2(file_path, &lib_dirs) {
        Ok(result) => {
            for w in &result.warnings { eprintln!("warning: {}", w.message); }
            let display = cranelisp::repl::format_result(result.value, &result.ty);
            println!("{display}");
            let exit_code = cranelisp::pipeline::determine_exit_code(result.value, &result.ty);
            if exit_code != 0 { process::exit(exit_code); }
        }
        Err(e) => { eprintln!("error: {e}"); process::exit(1); }
    }
}

fn link_file(path: &str) {
    let file_path = Path::new(path);
    if !file_path.exists() { eprintln!("error: file not found: {path}"); process::exit(1); }
    let project_root = &std::env::current_dir().unwrap_or_else(|_| std::path::PathBuf::from("."));
    let lib_dirs = cranelisp::pipeline::assemble_lib_dirs(project_root);
    let cache_dir = project_root.join(".cranelisp-cache");
    let compile_result = match cranelisp::pipeline_v2::compile_for_link_v2(file_path, &lib_dirs, &cache_dir) { Ok(r) => r, Err(e) => { eprintln!("error: {e}"); process::exit(1); } };
    for w in &compile_result.warnings { eprintln!("warning: {}", w.message); }
    let main_return = match cranelisp::exe::validate_main(&compile_result.entry_symbols) { Ok(kind) => kind, Err(e) => { eprintln!("error: {e}"); process::exit(1); } };
    let platform_manifest_names = cranelisp::exe::collect_platform_manifest_names(&compile_result.module_structures);
    let main_returns_io = main_return == cranelisp::exe::MainReturnKind::Io;
    let startup_bytes = match cranelisp::exe::generate_startup_object(&platform_manifest_names, main_returns_io) { Ok(bytes) => bytes, Err(e) => { eprintln!("error: {e}"); process::exit(1); } };
    let startup_o_path = cache_dir.join("_startup.o");
    if let Err(e) = std::fs::create_dir_all(&cache_dir) { eprintln!("error: {e}"); process::exit(1); }
    if let Err(e) = std::fs::write(&startup_o_path, &startup_bytes) { eprintln!("error: {e}"); process::exit(1); }
    let bundle_lib = match cranelisp::exe::find_bundle_lib() { Ok(p) => p, Err(e) => { eprintln!("error: {e}"); process::exit(1); } };
    let platform_rlibs = cranelisp::exe::find_platform_rlibs(&compile_result.module_structures);
    let output_path = std::path::PathBuf::from(file_path.file_stem().unwrap_or(std::ffi::OsStr::new("a.out")));
    if let Err(e) = cranelisp::exe::link_executable(&output_path, &compile_result.module_o_paths, &startup_o_path, &bundle_lib, &platform_rlibs) { eprintln!("error: {e}"); process::exit(1); }
    eprintln!("; Linked: {}", output_path.display());
}
