// cranelisp: pipeline orchestration, batch mode, REPL.

use std::path::{Path, PathBuf};
use std::process;

use cranelisp_types::{
    CodegenTarget, CompileContext, CranelispError, ModuleFullPath, ModuleStrategy, Span, Symbol,
    Type, Warning,
};

use cranelisp::pipeline::CompilationSession;
use cranelisp::pipeline_v2::{compile_unit, CodegenItem};

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
    match run_file_inner(path) {
        Ok(()) => {}
        Err(e) => {
            eprintln!("error: {e}");
            process::exit(1);
        }
    }
}

fn run_file_inner(path: &str) -> Result<(), CranelispError> {
    let file_path = Path::new(path);
    if !file_path.exists() {
        return Err(CranelispError::ModuleError {
            message: format!("file not found: {path}"),
            file: Some(file_path.to_path_buf()),
            span: Span::SYNTHETIC,
        });
    }
    let project_root = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let lib_dirs = cranelisp::pipeline::assemble_lib_dirs(&project_root);

    // Step 1: Canonicalize entry path, derive module name.
    let entry_path = file_path.canonicalize().map_err(|e| CranelispError::ModuleError {
        message: format!("cannot canonicalize '{}': {}", file_path.display(), e),
        file: Some(file_path.to_path_buf()),
        span: Span::SYNTHETIC,
    })?;
    let module_name = entry_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("main");
    let entry_module = ModuleFullPath::from(module_name);

    // Step 2: Create session, set lib_dirs (entry parent dir + provided dirs).
    let mut session = CompilationSession::new();
    session.interactive = true;
    let entry_dir = entry_path.parent().map(|p| p.to_path_buf());
    let mut all_lib_dirs: Vec<PathBuf> = Vec::new();
    if let Some(dir) = &entry_dir {
        all_lib_dirs.push(dir.clone());
    }
    all_lib_dirs.extend(lib_dirs.iter().cloned());
    session.lib_dirs = all_lib_dirs;
    session.project_root = entry_dir.unwrap_or_else(|| PathBuf::from("."));

    // Step 3: Read entry file source.
    let entry_source = std::fs::read_to_string(&entry_path).map_err(|e| {
        CranelispError::ModuleError {
            message: format!("cannot read '{}': {}", entry_path.display(), e),
            file: Some(entry_path.clone()),
            span: Span::SYNTHETIC,
        }
    })?;

    // Step 4: Compile via compile_unit (prelude auto-loaded inside).
    let entry_ctx = CompileContext {
        module: entry_module,
        strategy: ModuleStrategy::Additive,
        codegen_target: CodegenTarget::JitAndCache,
    };
    let unit_result = compile_unit(&mut session, &entry_source, &entry_ctx)?;
    let unit_warnings = unit_result.warnings.clone();
    session.inmem_queue.push(CodegenItem {
        ctx: entry_ctx,
        unit_result,
    });
    let mut codegen_results = session.flush_inmem_queue()?;
    let result = match codegen_results.pop() {
        Some(r) => r,
        None => unreachable!("invariant: flush_inmem_queue must return one result per queued item"),
    };

    // Step 5: Verify `main` exists in the GOT.
    let main_sym = Symbol::from("main");
    let qualified_main = Symbol::from(format!("{}/main", module_name));
    let main_exists = session.inmem_worker.got_state.def_codegen.contains_key(&main_sym)
        || session.inmem_worker.got_state.def_codegen.contains_key(&qualified_main);
    if !main_exists {
        return Err(CranelispError::ModuleError {
            message:
                "entry module has no `main` function — batch mode requires (defn main [] ...)"
                    .into(),
            file: Some(entry_path),
            span: Span::SYNTHETIC,
        });
    }

    // Step 6: Extract result value.
    let raw_value = result.value.ok_or_else(|| CranelispError::ModuleError {
        message: "entry module produced no result value".into(),
        file: Some(entry_path.clone()),
        span: Span::SYNTHETIC,
    })?;
    let result_type = result.result_type.unwrap_or(Type::Int);

    // Step 7: If main returns IO, run the IO trampoline.
    let (value, ty) = if result_type.is_io() {
        let inner_value = cranelisp_runtime::run_io_trampoline(raw_value);
        let inner_type = result_type.io_inner_type();
        (inner_value, inner_type)
    } else {
        (raw_value, result_type)
    };

    // Display warnings and result.
    let mut all_warnings = unit_warnings;
    all_warnings.extend(result.warnings);
    for w in &all_warnings {
        eprintln!("warning: {}", w.message);
    }
    let display = cranelisp::repl::format_result(value, &ty);
    println!("{display}");
    let exit_code = cranelisp::pipeline::determine_exit_code(value, &ty);
    if exit_code != 0 {
        process::exit(exit_code);
    }
    Ok(())
}

fn link_file(path: &str) {
    match link_file_inner(path) {
        Ok(()) => {}
        Err(e) => {
            eprintln!("error: {e}");
            process::exit(1);
        }
    }
}

fn link_file_inner(path: &str) -> Result<(), CranelispError> {
    let file_path = Path::new(path);
    if !file_path.exists() {
        return Err(CranelispError::ModuleError {
            message: format!("file not found: {path}"),
            file: Some(file_path.to_path_buf()),
            span: Span::SYNTHETIC,
        });
    }
    let project_root = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let lib_dirs = cranelisp::pipeline::assemble_lib_dirs(&project_root);
    let cache_dir = project_root.join(".cranelisp-cache");

    // Step 1: Discover module graph from entry file, topological sort.
    let graph = cranelisp::pipeline::discover_module_graph(file_path, &lib_dirs)?;
    let order = cranelisp::pipeline::toposort(&graph)?;

    // Step 2: Canonicalize entry path, create session with caching.
    let entry_path = file_path.canonicalize().map_err(|e| CranelispError::ModuleError {
        message: format!("cannot canonicalize '{}': {}", file_path.display(), e),
        file: Some(file_path.to_path_buf()),
        span: Span::SYNTHETIC,
    })?;
    std::fs::create_dir_all(&cache_dir).map_err(|e| CranelispError::ModuleError {
        message: format!("cannot create cache dir '{}': {}", cache_dir.display(), e),
        file: None,
        span: Span::SYNTHETIC,
    })?;

    let mut session = CompilationSession::new_with_cache(cache_dir.clone());
    session.interactive = true;
    let entry_dir = entry_path.parent().map(|p| p.to_path_buf());
    let mut all_lib_dirs: Vec<PathBuf> = Vec::new();
    if let Some(dir) = &entry_dir {
        all_lib_dirs.push(dir.clone());
    }
    all_lib_dirs.extend(lib_dirs.iter().cloned());
    session.lib_dirs = all_lib_dirs;
    session.project_root = entry_dir.unwrap_or_else(|| PathBuf::from("."));

    let mut all_warnings: Vec<Warning> = Vec::new();

    // Step 3: Compile each module in topo order via compile_unit.
    for module_path in &order {
        let node = &graph.nodes[module_path];
        let source = std::fs::read_to_string(&node.file_path).map_err(|e| {
            CranelispError::ModuleError {
                message: format!("cannot read '{}': {}", node.file_path.display(), e),
                file: Some(node.file_path.clone()),
                span: Span::SYNTHETIC,
            }
        })?;

        let ctx = CompileContext {
            module: module_path.clone(),
            strategy: ModuleStrategy::Replace,
            codegen_target: CodegenTarget::JitAndCache,
        };

        let unit_result = compile_unit(&mut session, &source, &ctx)?;
        all_warnings.extend(unit_result.warnings.clone());
        session.object_queue.push(CodegenItem {
            ctx,
            unit_result,
        });
        let codegen_results = session.flush_object_queue()?;
        for codegen_result in codegen_results {
            all_warnings.extend(codegen_result.warnings);
        }
    }

    // Step 4: Flush background .o writes to ensure all files are on disk.
    session.flush_cache_writes();
    let module_o_paths = session.object_worker.compiled_o_paths.clone();

    // Step 5: Collect entry module's symbol table and module structures.
    session.tc.set_current_module(graph.entry.clone());
    let entry_symbols = session.tc.symbol_table().clone();
    let module_structures = session.object_worker.compiled_module_structures.clone();

    // Display warnings.
    for w in &all_warnings {
        eprintln!("warning: {}", w.message);
    }

    // Step 6: Validate main, generate startup, link executable.
    let main_return = cranelisp::exe::validate_main(&entry_symbols)?;
    let platform_manifest_names =
        cranelisp::exe::collect_platform_manifest_names(&module_structures);
    let main_returns_io = main_return == cranelisp::exe::MainReturnKind::Io;
    let startup_bytes =
        cranelisp::exe::generate_startup_object(&platform_manifest_names, main_returns_io)?;
    let startup_o_path = cache_dir.join("_startup.o");
    std::fs::create_dir_all(&cache_dir).map_err(|e| CranelispError::ModuleError {
        message: format!("cannot create cache dir '{}': {}", cache_dir.display(), e),
        file: None,
        span: Span::SYNTHETIC,
    })?;
    std::fs::write(&startup_o_path, &startup_bytes).map_err(|e| CranelispError::ModuleError {
        message: format!("cannot write startup object: {}", e),
        file: Some(startup_o_path.clone()),
        span: Span::SYNTHETIC,
    })?;
    let bundle_lib = cranelisp::exe::find_bundle_lib()?;
    let platform_rlibs = cranelisp::exe::find_platform_rlibs(&module_structures);
    let output_path =
        PathBuf::from(file_path.file_stem().unwrap_or(std::ffi::OsStr::new("a.out")));
    cranelisp::exe::link_executable(
        &output_path,
        &module_o_paths,
        &startup_o_path,
        &bundle_lib,
        &platform_rlibs,
    )?;
    eprintln!("; Linked: {}", output_path.display());
    Ok(())
}
