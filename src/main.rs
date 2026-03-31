// cranelisp main: pipeline-v3.md §2.2 structure.
//
// Three modes: Run (--run), Link (--link), Repl (default).
// Run and Link compile an entry file; Repl delegates to run_repl().

use std::path::{Path, PathBuf};
use std::process;

use cranelisp_types::{
    CodegenBehaviour, CompileContext, CranelispError, ModuleFullPath, ModuleStrategy, Span,
    Type, Warning,
};

use cranelisp::session::CompilationSession;

// ---------------------------------------------------------------------------
// Action enum (pipeline-v3.md §2.1)
// ---------------------------------------------------------------------------

enum Action {
    Run,
    Link,
    Repl,
}

// ---------------------------------------------------------------------------
// Settings (pipeline-v3.md §11)
// ---------------------------------------------------------------------------

struct Settings {
    no_color: bool,
    #[allow(dead_code)] // Wave 3: cache-hit loading uses this
    no_cache: bool,
    /// When true, use the v4 CompilerSession path (pipeline-v4-roadmap Step 0).
    v4: bool,
}

// ---------------------------------------------------------------------------
// Main (pipeline-v3.md §2.2)
// ---------------------------------------------------------------------------

fn main() {
    let (action, entry_module_path, settings) = parse_args();
    cranelisp::style::init_color(settings.no_color);

    // v4 pipeline path (pipeline-v4-roadmap Step 0).
    if settings.v4 {
        if let Err(e) = v4_main(action, &entry_module_path, &settings) {
            eprintln!("error: {e}");
            process::exit(1);
        }
        return;
    }

    // Link and REPL modes have their own session and compilation flow.
    match action {
        Action::Link => {
            if let Err(e) = link_mode(&entry_module_path) {
                eprintln!("error: {e}");
                process::exit(1);
            }
            return;
        }
        Action::Repl => {
            // REPL creates its own session with prelude loading and
            // persistence (user.cl restore). See repl/mod.rs run_repl().
            cranelisp::repl::run_repl();
            return;
        }
        Action::Run => {} // fall through to batch compilation below
    }

    // --- Batch (Run) mode ---

    let entry_module_name = slug(&entry_module_path);
    let project_root = base_dir(&entry_module_path);

    let mut s = new_session(&project_root, &entry_module_path);

    let src = match read_file(&entry_module_path) {
        Ok(src) => src,
        Err(e) => {
            eprintln!("error: {e}");
            process::exit(1);
        }
    };

    let ctx = CompileContext {
        module: ModuleFullPath::from(entry_module_name.as_str()),
        codegen: CodegenBehaviour::InMemoryAndObject,
    };

    let unit_result = match s.compile_unit(&src, &ctx, ModuleStrategy::Replace) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error: {e}");
            process::exit(1);
        }
    };
    let unit_warnings = unit_result.warnings.clone();
    s.send_codegen(unit_result, ctx.clone());

    s.spawn_hot_inmem_codegen();
    s.spawn_nice_object_codegen();

    if let Err(e) = run_mode(&mut s, &ctx, unit_warnings) {
        eprintln!("error: {e}");
        process::exit(1);
    }
}

// ---------------------------------------------------------------------------
// Run mode (pipeline-v3.md §8)
// ---------------------------------------------------------------------------

fn run_mode(
    s: &mut CompilationSession,
    ctx: &CompileContext,
    unit_warnings: Vec<Warning>,
) -> Result<(), CranelispError> {
    // hot_flush_in_mem_queue: blocks until all GOT slots populated.
    let codegen_results = s.hot_flush_in_mem_queue()?;
    s.shutdown_codegen();

    let result = match codegen_results.into_iter().last() {
        Some(r) => r,
        None => return Err(CranelispError::ModuleError {
            message: "no codegen result".into(),
            file: None,
            span: Span::SYNTHETIC,
        }),
    };

    // Verify main exists.
    let module_name = ctx.module.as_ref();
    let main_sym = cranelisp_types::Symbol::from("main");
    let qualified_main = cranelisp_types::Symbol::from(format!("{}/main", module_name));
    let main_exists = s.inmem_worker.got_state.def_codegen.contains_key(&main_sym)
        || s.inmem_worker.got_state.def_codegen.contains_key(&qualified_main);
    if !main_exists {
        return Err(CranelispError::ModuleError {
            message: "entry module has no `main` function — batch mode requires (defn main [] ...)".into(),
            file: None,
            span: Span::SYNTHETIC,
        });
    }

    let raw_value = result.value.ok_or_else(|| CranelispError::ModuleError {
        message: "entry module produced no result value".into(),
        file: None,
        span: Span::SYNTHETIC,
    })?;
    let result_type = result.result_type.unwrap_or(Type::Int);

    // IO trampoline.
    let (value, ty) = if result_type.is_io() {
        let inner_value = cranelisp_runtime::run_io_trampoline(raw_value);
        let inner_type = result_type.io_inner_type();
        (inner_value, inner_type)
    } else {
        (raw_value, result_type)
    };

    // hot_flush_object_queue: blocks until all .o written.
    s.hot_flush_object_queue()?;

    // Display warnings and result.
    let mut all_warnings = unit_warnings;
    all_warnings.extend(result.warnings);
    for w in &all_warnings {
        eprintln!("warning: {}", w.message);
    }
    let display = cranelisp::repl::format_result(value, &ty);
    println!("{display}");

    let exit_code = cranelisp::session::determine_exit_code(value, &ty);
    if exit_code != 0 {
        process::exit(exit_code);
    }
    Ok(())
}

// Concurrent codegen stubs (spawn_hot_inmem_codegen, spawn_nice_object_codegen,
// hot_flush_in_mem_queue, hot_flush_object_queue) live in session.rs as methods
// on CompilationSession. Wave 2 replaces them with real thread pool implementations.

// ---------------------------------------------------------------------------
// v4 pipeline main (pipeline-v4-roadmap Step 0)
// ---------------------------------------------------------------------------

/// The v4 main flow, delegating through CompilerSession to the old path.
///
/// Reachable via `--v4` CLI flag. Produces identical output to the old main
/// for all modes (Run, Link, Repl).
fn v4_main(
    action: Action,
    entry_module_path: &Path,
    settings: &Settings,
) -> Result<(), CranelispError> {
    match action {
        Action::Repl => {
            // REPL with v4 eval: same REPL experience (slash commands, display,
            // line editing) but eval routes through process_module_forms(Additive)
            // instead of compile_unit (Step 7).
            cranelisp::repl::run_repl_v4();
            Ok(())
        }
        Action::Link => {
            let project_root =
                std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
            let cache_dir = project_root.join(".cranelisp-cache");
            let mut s = cranelisp::session_v4::CompilerSession::new_for_link(
                project_root,
                entry_module_path,
                cache_dir,
            )?;
            s.run_with_nice_workers(1, |s| {
                s.link(entry_module_path)?;
                Ok(())
            })?;
            Ok(())
        }
        Action::Run => {
            let entry_module_name = slug(entry_module_path);
            let project_root = base_dir(entry_module_path);

            let mut s = cranelisp::session_v4::CompilerSession::new(
                settings.no_color,
                project_root,
                entry_module_path,
            );

            let (value, ty, unit_warnings) = s.run_with_nice_workers(
                1,
                |s| {
                    let src = read_file(entry_module_path)?;
                    let unit_warnings = s.register_module(
                        &entry_module_name, &src, entry_module_path,
                    )?;
                    let (value, ty) = s.trampoline(&entry_module_name)?;
                    Ok((value, ty, unit_warnings))
                },
            )?;

            // Display warnings and result.
            for w in &unit_warnings {
                eprintln!("warning: {}", w.message);
            }
            let display = cranelisp::repl::format_result(value, &ty);
            println!("{display}");

            let exit_code = cranelisp::session::determine_exit_code(value, &ty);
            if exit_code != 0 {
                process::exit(exit_code);
            }
            Ok(())
        }
    }
}

// ---------------------------------------------------------------------------
// Argument parsing
// ---------------------------------------------------------------------------

fn parse_args() -> (Action, PathBuf, Settings) {
    let args: Vec<String> = std::env::args().collect();
    let mut no_color = false;
    let mut no_cache = false;
    let mut v4 = false;
    let mut run_file: Option<String> = None;
    let mut link_file: Option<String> = None;
    let mut i = 1;

    while i < args.len() {
        match args[i].as_str() {
            "--no-cache" => { no_cache = true; i += 1; }
            "--no-color" => { no_color = true; i += 1; }
            "--v4" => { v4 = true; i += 1; }
            "--run" => {
                if i + 1 < args.len() {
                    run_file = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    eprintln!("error: --run requires a file argument");
                    process::exit(1);
                }
            }
            "--link" => {
                if i + 1 < args.len() {
                    link_file = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    eprintln!("error: --link requires a file argument");
                    process::exit(1);
                }
            }
            other => {
                eprintln!("error: unexpected argument: {other}");
                eprintln!("usage: cranelisp [--run <file.cl>] [--link <file.cl>] [--no-color] [--v4]");
                process::exit(1);
            }
        }
    }

    let settings = Settings { no_color, no_cache, v4 };

    if run_file.is_some() && link_file.is_some() {
        eprintln!("error: --run and --link cannot be used together");
        process::exit(1);
    }

    if let Some(path) = link_file {
        return (Action::Link, PathBuf::from(path), settings);
    }

    match run_file {
        Some(path) => (Action::Run, PathBuf::from(path), settings),
        None => (Action::Repl, PathBuf::from("user.cl"), settings),
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Derive module name from file path (file stem).
fn slug(path: &Path) -> String {
    path.file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("main")
        .to_string()
}

/// Derive project root from file path (parent directory).
fn base_dir(path: &Path) -> PathBuf {
    path.parent()
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|| std::env::current_dir().unwrap_or_else(|_| PathBuf::from(".")))
}

/// Read source file.
fn read_file(path: &Path) -> Result<String, CranelispError> {
    if !path.exists() {
        return Err(CranelispError::ModuleError {
            message: format!("file not found: {}", path.display()),
            file: Some(path.to_path_buf()),
            span: Span::SYNTHETIC,
        });
    }
    std::fs::read_to_string(path).map_err(|e| CranelispError::ModuleError {
        message: format!("cannot read '{}': {}", path.display(), e),
        file: Some(path.to_path_buf()),
        span: Span::SYNTHETIC,
    })
}

/// Create a new compilation session with lib_dirs set up.
fn new_session(project_root: &Path, entry_path: &Path) -> CompilationSession {
    let lib_dirs = cranelisp::session::assemble_lib_dirs(project_root);

    let mut session = CompilationSession::new_async();
    session.interactive = true;

    let entry_dir = entry_path
        .canonicalize()
        .ok()
        .and_then(|p| p.parent().map(|d| d.to_path_buf()));

    let mut all_lib_dirs: Vec<PathBuf> = Vec::new();
    if let Some(dir) = &entry_dir {
        all_lib_dirs.push(dir.clone());
    }
    all_lib_dirs.extend(lib_dirs.iter().cloned());
    session.lib_dirs = all_lib_dirs;
    session.project_root = entry_dir.unwrap_or_else(|| project_root.to_path_buf());

    session
}

/// Link mode: compile all modules in dependency order, then link to executable.
///
/// Uses the module graph discovery + topo sort from pipeline.rs, then
/// compiles each module via compile_unit + send_codegen + flush_codegen
/// (reusing the existing link path logic). The object worker generates
/// .o files; the linker assembles them into an executable.
fn link_mode(entry_path: &Path) -> Result<(), CranelispError> {
    use cranelisp::session::CompilationSession;
    use cranelisp_types::{CodegenBehaviour, CompileContext, ModuleStrategy, Warning};

    let project_root = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let lib_dirs = cranelisp::session::assemble_lib_dirs(&project_root);
    let cache_dir = project_root.join(".cranelisp-cache");

    // Step 1: Discover module graph and topological sort.
    let graph = cranelisp::pipeline::discover_module_graph(entry_path, &lib_dirs)?;
    let order = cranelisp::pipeline::toposort(&graph)?;

    // Step 2: Create async session with caching.
    let canonical_entry = entry_path.canonicalize().map_err(|e| CranelispError::ModuleError {
        message: format!("cannot canonicalize '{}': {}", entry_path.display(), e),
        file: Some(entry_path.to_path_buf()),
        span: Span::SYNTHETIC,
    })?;
    std::fs::create_dir_all(&cache_dir).map_err(|e| CranelispError::ModuleError {
        message: format!("cannot create cache dir '{}': {}", cache_dir.display(), e),
        file: None,
        span: Span::SYNTHETIC,
    })?;

    let mut session = CompilationSession::new_async_with_cache(cache_dir.clone());
    session.interactive = true;
    setup_lib_dirs(&mut session, &canonical_entry, &lib_dirs);

    let mut all_warnings: Vec<Warning> = Vec::new();

    // Step 3: Compile each module in topo order.
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
            codegen: CodegenBehaviour::InMemoryAndObject,
        };

        let unit_result = session.compile_unit(&source, &ctx, ModuleStrategy::Replace)?;
        all_warnings.extend(unit_result.warnings.clone());
        session.send_codegen(unit_result, ctx);
        let codegen_results = session.flush_codegen()?;
        for codegen_result in codegen_results {
            all_warnings.extend(codegen_result.warnings);
        }
    }

    // Step 4: Shut down workers, flush .o writes.
    session.shutdown_codegen();
    session.flush_cache_writes();
    let module_o_paths = session.object_worker.compiled_o_paths.clone();

    // Step 5: Validate main, generate startup, link executable.
    session.tc.set_current_module(graph.entry.clone());
    let entry_symbols = session.tc.symbol_table().clone();
    let module_structures = session.object_worker.compiled_module_structures.clone();

    for w in &all_warnings {
        eprintln!("warning: {}", w.message);
    }

    let main_return = cranelisp::exe::validate_main(&entry_symbols)?;
    let platform_names = cranelisp::exe::collect_platform_manifest_names(&module_structures);
    let main_returns_io = main_return == cranelisp::exe::MainReturnKind::Io;
    let startup_bytes = cranelisp::exe::generate_startup_object(&platform_names, main_returns_io)?;
    let startup_o_path = cache_dir.join("_startup.o");
    std::fs::write(&startup_o_path, &startup_bytes).map_err(|e| CranelispError::ModuleError {
        message: format!("cannot write startup object: {}", e),
        file: Some(startup_o_path.clone()),
        span: Span::SYNTHETIC,
    })?;
    let bundle_lib = cranelisp::exe::find_bundle_lib()?;
    let platform_rlibs = cranelisp::exe::find_platform_rlibs(&module_structures);
    let output_path = PathBuf::from(
        entry_path
            .file_stem()
            .unwrap_or(std::ffi::OsStr::new("a.out")),
    );
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

/// Set up lib_dirs on a session from an entry path and base lib_dirs.
fn setup_lib_dirs(
    session: &mut cranelisp::session::CompilationSession,
    canonical_entry: &Path,
    lib_dirs: &[PathBuf],
) {
    let entry_dir = canonical_entry.parent().map(|p| p.to_path_buf());
    let mut all_lib_dirs: Vec<PathBuf> = Vec::new();
    if let Some(dir) = &entry_dir {
        all_lib_dirs.push(dir.clone());
    }
    all_lib_dirs.extend(lib_dirs.iter().cloned());
    session.lib_dirs = all_lib_dirs;
    session.project_root = entry_dir.unwrap_or_else(|| PathBuf::from("."));
}
