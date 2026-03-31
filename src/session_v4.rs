// CompilerSession: v4 pipeline session (pipeline-v4.md §5, roadmap Steps 0-7).
//
// Wraps the existing CompilationSession. Batch compilation goes through the v4
// scheduler-driven path with lazy dependency discovery (Step 5). REPL eval
// routes through process_module_forms(Additive) with serial per-form processing
// (Step 7).

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::sync::{Arc, Mutex};

use cranelisp_types::{
    CheckResult, CodegenBehaviour, CompileContext, CranelispError,
    ModuleFullPath, ModuleStrategy, ModuleStructure, Span, Symbol,
    SymbolTable, TopLevel, Type, Warning,
};

use crate::platform_registry::PlatformRegistry;
use crate::scheduler::CompileScheduler;
use crate::session::CompilationSession;
use crate::worker::WorkerContext;

// ---------------------------------------------------------------------------
// CommandResult (pipeline-v4.md §6.1)
// ---------------------------------------------------------------------------

/// Result of processing a REPL input line through `process_commands`.
///
/// Mirrors the v4 design: slash commands are handled inline, blank/comment
/// lines produce Nothing, and source text is returned for compilation.
pub enum CommandResult {
    /// Blank line, comment, or side-effect-only command (e.g., /quit).
    Nothing,
    /// Command that produces displayable output (e.g., /sig, /list).
    Final(String),
    /// Raw source text to submit for compilation.
    Compile(String),
}

// ---------------------------------------------------------------------------
// CompilerSession (pipeline-v4.md §5)
// ---------------------------------------------------------------------------

/// Snapshot of typecheck + program data for a module, stored by the priority
/// worker after codegen so that nice workers can compile the `.o` file.
pub struct ObjectCodegenInput {
    pub check_result: CheckResult,
    pub program: Vec<TopLevel>,
    /// Cross-module function signatures accumulated up to this module.
    /// Each entry is (qualified_name, param_count).
    pub cross_module_func_sigs: Vec<(Symbol, usize)>,
    /// Cloned symbol table for .meta.json serialization.
    pub symbol_table: SymbolTable,
    /// Module structure for .meta.json serialization.
    pub module_structure: ModuleStructure,
}

/// Thread-safe state shared between the main thread and nice worker threads.
///
/// Separated from `CompilerSession` so that nice workers can hold `&SharedState`
/// while the main thread retains `&mut CompilerSession` for priority worker
/// operations. All fields are inherently thread-safe (Mutex, AtomicBool,
/// read-only after construction).
pub struct SharedState {
    /// Compilation scheduler. Tracks module lifecycle and coordinates
    /// work items. Internal Mutex + condvars for thread-safe access.
    pub scheduler: CompileScheduler,

    /// Cache directory for .o and .meta.json output (Step 10).
    /// None when caching is disabled (e.g., `--run` without `--link`).
    pub cache_dir: Option<PathBuf>,

    /// Collected .o file paths written by nice workers (Step 10).
    /// Used by `--link` to pass all .o files to the system linker.
    pub compiled_o_paths: Mutex<Vec<PathBuf>>,

    /// Flag for nice worker priority promotion during hot flush (Step 10).
    /// When set to true, nice workers self-promote to normal OS priority.
    pub promote_nice_workers: AtomicBool,

    /// Module data for nice worker .o compilation. Populated by the priority
    /// worker after in-memory codegen completes; consumed by nice workers.
    pub object_codegen_inputs: Mutex<HashMap<ModuleFullPath, ObjectCodegenInput>>,
}

/// The v4 compiler session — the permanent session type for scheduler-driven
/// concurrent compilation.
///
/// Currently wraps `CompilationSession` and delegates all operations to the
/// old path. Each roadmap step progressively replaces delegation with native
/// v4 logic. The `--v4` CLI flag enables this session for testing.
pub struct CompilerSession {
    /// The wrapped old-path session. Removed when all delegation is replaced.
    inner: CompilationSession,

    /// Thread-safe state shared with nice worker threads. Wrapped in Arc
    /// so workers get an independent clone — no aliasing between `&mut self`
    /// (used by priority worker operations) and the shared reference held
    /// by nice workers. All SharedState fields are inherently thread-safe
    /// (Mutex, AtomicBool, read-only).
    pub shared: Arc<SharedState>,

    /// Project root directory (read-only after construction).
    pub project_root: PathBuf,

    /// Unified platform function registry (Step 8).
    /// Populated during platform loading, read-only during codegen.
    pub platform_registry: PlatformRegistry,
}

impl CompilerSession {
    /// Create a new v4 session wrapping the existing compilation path.
    ///
    /// Sets up lib_dirs, project_root, and interactive mode on the inner
    /// session, matching the old `new_session()` helper in main.rs.
    pub fn new(
        _no_color: bool,
        project_root: PathBuf,
        entry_path: &Path,
    ) -> Self {
        let lib_dirs = crate::session::assemble_lib_dirs(&project_root);

        // Use sync mode so the v4 worker loop can write directly to
        // inmem_worker's GOT state (async mode puts a dummy on the session).
        let mut inner = CompilationSession::new();
        inner.interactive = true;

        let entry_dir = entry_path
            .canonicalize()
            .ok()
            .and_then(|p| p.parent().map(|d| d.to_path_buf()));

        let mut all_lib_dirs: Vec<PathBuf> = Vec::new();
        if let Some(dir) = &entry_dir {
            all_lib_dirs.push(dir.clone());
        }
        all_lib_dirs.extend(lib_dirs);
        inner.lib_dirs = all_lib_dirs;
        inner.project_root = entry_dir.unwrap_or_else(|| project_root.clone());

        let cache_dir = project_root.join(".cranelisp-cache");
        let _ = std::fs::create_dir_all(&cache_dir);

        CompilerSession {
            inner,
            shared: Arc::new(SharedState {
                scheduler: CompileScheduler::new(),
                cache_dir: Some(cache_dir),
                compiled_o_paths: Mutex::new(Vec::new()),
                promote_nice_workers: AtomicBool::new(false),
                object_codegen_inputs: Mutex::new(HashMap::new()),
            }),
            project_root,
            platform_registry: PlatformRegistry::new(),
        }
    }

    /// Create a v4 session for link mode with caching enabled.
    pub fn new_for_link(
        project_root: PathBuf,
        entry_path: &Path,
        cache_dir: PathBuf,
    ) -> Result<Self, CranelispError> {
        let lib_dirs = crate::session::assemble_lib_dirs(&project_root);

        let canonical_entry = entry_path.canonicalize().map_err(|e| {
            CranelispError::ModuleError {
                message: format!("cannot canonicalize '{}': {}", entry_path.display(), e),
                file: Some(entry_path.to_path_buf()),
                span: Span::SYNTHETIC,
            }
        })?;

        std::fs::create_dir_all(&cache_dir).map_err(|e| CranelispError::ModuleError {
            message: format!("cannot create cache dir '{}': {}", cache_dir.display(), e),
            file: None,
            span: Span::SYNTHETIC,
        })?;

        let mut inner = CompilationSession::new_async_with_cache(cache_dir.clone());
        inner.interactive = true;

        let entry_dir = canonical_entry.parent().map(|p| p.to_path_buf());
        let mut all_lib_dirs: Vec<PathBuf> = Vec::new();
        if let Some(dir) = &entry_dir {
            all_lib_dirs.push(dir.clone());
        }
        all_lib_dirs.extend(lib_dirs);
        inner.lib_dirs = all_lib_dirs;
        inner.project_root = entry_dir.unwrap_or_else(|| project_root.clone());

        Ok(CompilerSession {
            inner,
            shared: Arc::new(SharedState {
                scheduler: CompileScheduler::new(),
                cache_dir: Some(cache_dir),
                compiled_o_paths: Mutex::new(Vec::new()),
                promote_nice_workers: AtomicBool::new(false),
                object_codegen_inputs: Mutex::new(HashMap::new()),
            }),
            project_root,
            platform_registry: PlatformRegistry::new(),
        })
    }

    /// Register a module for compilation via the v4 scheduler-driven path.
    ///
    /// All programs go through the v4 path with lazy dependency discovery.
    /// The C2 filter and old delegation path are deleted (Step 5).
    ///
    /// Returns warnings from compilation. Codegen results are available
    /// via GOT after `scheduler.wait_inmem_complete()`.
    pub fn register_module(
        &mut self,
        module_name: &str,
        source: &str,
        _entry_module_path: &Path,
    ) -> Result<Vec<Warning>, CranelispError> {
        let module = ModuleFullPath::from(module_name);
        let sexps = cranelisp_frontend::parse(source)?;

        // Register module with scheduler (entry module, not delaying others).
        self.shared.scheduler.register_module(module.clone(), false);

        // Build sexp map for the worker loop.
        let mut module_sexps = HashMap::new();
        module_sexps.insert(module.clone(), sexps);

        // Extract shared codegen state from InMemWorkerState for the worker loop.
        // This bridges the old InMemWorkerState with the new SharedCodegenState
        // + WorkerJitState types. After the loop, state is synced back.
        let mut shared_codegen =
            crate::session::SharedCodegenState::extract_from(&mut self.inner.inmem_worker);
        let mut worker_jit = crate::session::WorkerJitState::new();

        // Build WorkerContext bundling all worker parameters.
        let mut ctx = WorkerContext {
            tc: &mut self.inner.tc,
            scheduler: &self.shared.scheduler,
            shared_codegen: &mut shared_codegen,
            worker_jit: &mut worker_jit,
            platform_registry: &mut self.platform_registry,
            lib_dirs: &self.inner.lib_dirs,
            project_root: &self.inner.project_root,
            object_codegen_stash: Some(&self.shared.object_codegen_inputs),
        };

        // Run the priority worker loop inline (single-threaded).
        let loop_result = crate::worker::priority_worker_loop(
            &mut ctx,
            &mut module_sexps,
        );

        // Drain per-worker JIT state to shared before syncing back.
        worker_jit.drain_to_shared(&mut shared_codegen);

        // Sync shared codegen state back to InMemWorkerState.
        shared_codegen.sync_back_to(&mut self.inner.inmem_worker);

        // Propagate any error from the worker loop.
        loop_result?;

        // Check scheduler completion.
        self.shared.scheduler.wait_inmem_complete()?;

        // Register module aliases for GOT lookup by unqualified name.
        crate::session::register_module_aliases_filtered(
            &mut self.inner.inmem_worker,
            &module,
            None,
        );

        Ok(Vec::new())
    }

    /// Process REPL slash commands and blank/comment detection.
    ///
    /// Delegates to the existing REPL command dispatch. In v4, this remains
    /// a thin layer per pipeline-v4.md §6.1.
    pub fn process_commands(&self, _src: &str) -> CommandResult {
        // The REPL's command dispatch is tightly coupled to ReplSession, not
        // CompilationSession. For Step 0 delegation, the v4 REPL main loop
        // delegates directly to run_repl() instead of going through this method.
        // This method exists for the v4 API surface and will be filled in
        // when the REPL is migrated to v4 (Step 7+).
        CommandResult::Nothing
    }

    /// Execute the entry module's main function via the trampoline.
    ///
    /// For the v4 scheduler path: GOT is already populated by the worker
    /// loop. For the old path: flushes codegen queue first.
    ///
    /// Looks up `main` in the GOT, calls it, and runs the IO trampoline
    /// if the return type is IO.
    pub fn trampoline(
        &mut self,
        module_name: &str,
    ) -> Result<(i64, Type), CranelispError> {
        // Flush old-path codegen queue (no-op if queue is empty, i.e. v4 path).
        let _ = self.inner.hot_flush_in_mem_queue()?;
        self.inner.shutdown_codegen();

        // Look up main in GOT.
        let main_sym = cranelisp_types::Symbol::from("main");
        let qualified_main =
            cranelisp_types::Symbol::from(format!("{}/main", module_name));

        let code_ptr = self.lookup_main_code_ptr(&main_sym, &qualified_main)?;
        let result_type = self.lookup_main_return_type(module_name);

        // Clear any stale runtime error.
        let _ = cranelisp_runtime::panic::take_runtime_error();

        // Call main.
        // SAFETY: `code_ptr` is non-null — returned from `lookup_main_code_ptr`
        // which errors on None. It points to finalized JIT code compiled by
        // Cranelift via `compile_and_register_defn`. The compiled function uses
        // the `extern "C" fn() -> i64` calling convention (zero-arg defn with
        // i64 return), matching the transmute target type.
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
        let raw_value = func();

        // Check for runtime panics.
        if let Some(err) = cranelisp_runtime::panic::take_runtime_error() {
            return Err(CranelispError::CodegenError {
                message: format!("runtime panic: {}", err),
                span: Span::SYNTHETIC,
            });
        }

        // IO trampoline.
        if result_type.is_io() {
            let inner_value = cranelisp_runtime::run_io_trampoline(raw_value);
            let inner_type = result_type.io_inner_type();
            Ok((inner_value, inner_type))
        } else {
            Ok((raw_value, result_type))
        }
    }

    /// Look up the code pointer for `main` in the GOT.
    fn lookup_main_code_ptr(
        &self,
        main_sym: &cranelisp_types::Symbol,
        qualified_main: &cranelisp_types::Symbol,
    ) -> Result<*const u8, CranelispError> {
        let got = &self.inner.inmem_worker.got_state;

        // Try unqualified name first, then qualified.
        if let Some(entry) = got.def_codegen.get(main_sym) {
            if let Some(ptr) = entry.code_ptr {
                return Ok(ptr);
            }
        }
        if let Some(entry) = got.def_codegen.get(qualified_main) {
            if let Some(ptr) = entry.code_ptr {
                return Ok(ptr);
            }
        }

        Err(CranelispError::ModuleError {
            message: "entry module has no `main` function — batch mode requires (defn main [] ...)"
                .into(),
            file: None,
            span: Span::SYNTHETIC,
        })
    }

    /// Look up the return type of `main` from the typechecker.
    fn lookup_main_return_type(&self, module_name: &str) -> Type {
        let module_path = ModuleFullPath::from(module_name);
        let main_sym = Symbol::from("main");

        if let Some(table) = self.inner.tc.module_table(&module_path) {
            if let Some(cranelisp_types::ModuleEntry::Def { scheme, .. }) =
                table.get(main_sym.as_ref())
            {
                if let Type::Fn(_, ret) = &scheme.ty {
                    return *ret.clone();
                }
            }
        }
        Type::Int
    }

    /// Link all compiled modules into an executable.
    ///
    /// Delegates to the old link path. In v4, this will use the scheduler's
    /// module tracking to collect .o files (Step 9+).
    pub fn link(
        &mut self,
        entry_path: &Path,
    ) -> Result<(), CranelispError> {
        // The old link_mode is a standalone function in main.rs that creates
        // its own session. For Step 0, we delegate by using the inner session
        // fields directly, matching the old link_mode logic.
        let graph = crate::pipeline::discover_module_graph(
            entry_path,
            &self.inner.lib_dirs,
        )?;
        let order = crate::pipeline::toposort(&graph)?;

        let mut all_warnings: Vec<Warning> = Vec::new();

        // Compile each module in topo order.
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

            let unit_result =
                self.inner.compile_unit(&source, &ctx, ModuleStrategy::Replace)?;
            all_warnings.extend(unit_result.warnings.clone());
            self.inner.send_codegen(unit_result, ctx);
            let codegen_results = self.inner.flush_codegen()?;
            for cr in codegen_results {
                all_warnings.extend(cr.warnings);
            }
        }

        // Shut down workers, flush .o writes.
        self.inner.shutdown_codegen();
        self.inner.flush_cache_writes();
        let module_o_paths = self.inner.object_worker.compiled_o_paths.clone();

        // Validate main, generate startup, link executable.
        self.inner.tc.set_current_module(graph.entry.clone());
        let entry_symbols = self.inner.tc.symbol_table().clone();
        let module_structures = self.inner.object_worker.compiled_module_structures.clone();

        for w in &all_warnings {
            eprintln!("warning: {}", w.message);
        }

        let cache_dir = self.project_root.join(".cranelisp-cache");
        let main_return = crate::exe::validate_main(&entry_symbols)?;
        let platform_names =
            crate::exe::collect_platform_manifest_names(&module_structures);
        let main_returns_io = main_return == crate::exe::MainReturnKind::Io;
        let startup_bytes =
            crate::exe::generate_startup_object(&platform_names, main_returns_io)?;
        let startup_o_path = cache_dir.join("_startup.o");
        std::fs::write(&startup_o_path, &startup_bytes).map_err(|e| {
            CranelispError::ModuleError {
                message: format!("cannot write startup object: {}", e),
                file: Some(startup_o_path.clone()),
                span: Span::SYNTHETIC,
            }
        })?;
        let bundle_lib = crate::exe::find_bundle_lib()?;
        let platform_rlibs = crate::exe::find_platform_rlibs(&module_structures);
        let output_path = PathBuf::from(
            entry_path
                .file_stem()
                .unwrap_or(std::ffi::OsStr::new("a.out")),
        );
        crate::exe::link_executable(
            &output_path,
            &module_o_paths,
            &startup_o_path,
            &bundle_lib,
            &platform_rlibs,
        )?;
        eprintln!("; Linked: {}", output_path.display());
        Ok(())
    }

    /// Spawn priority worker threads for typecheck + JIT codegen.
    ///
    /// No-op for Step 3: the worker loop runs inline on the calling thread.
    /// Replaced by real thread spawning in Step 11.
    pub fn spawn_priority_workers(&self, _n: usize) {
        // Step 3: worker loop runs inline via priority_worker_loop().
    }

    /// Run a closure with nice worker threads active.
    ///
    /// Spawns `n` nice workers in a scoped thread pool, runs the closure
    /// on the calling thread, signals shutdown, and joins all workers.
    ///
    /// Workers receive an `Arc<SharedState>` clone, eliminating aliasing
    /// between the workers' shared reference and the `&mut self` used by
    /// the closure for priority worker operations.
    pub fn run_with_nice_workers<T>(
        &mut self,
        n: usize,
        f: impl FnOnce(&mut Self) -> Result<T, CranelispError>,
    ) -> Result<T, CranelispError> {
        // Clone the Arc for nice workers. Workers hold Arc<SharedState>
        // independently — no aliasing with &mut self.
        let shared_arc = Arc::clone(&self.shared);

        std::thread::scope(|scope| {
            spawn_nice_workers(scope, &shared_arc, n);
            let result = f(self);
            // Wait for nice workers to finish .o compilation before shutdown.
            // Promotes workers to normal priority so object codegen completes
            // promptly (especially important for --link).
            let _ = self.wait_object_complete();
            self.shared.scheduler.shutdown();
            result
        })
    }

    /// Wait until all registered modules have object codegen complete.
    ///
    /// Promotes nice workers to normal priority before blocking, ensuring
    /// object codegen completes promptly (e.g., before linking). Wakes
    /// the `object_work_available` condvar so workers observe the promotion
    /// flag on their next loop iteration.
    pub fn wait_object_complete(
        &self,
    ) -> Result<(), crate::scheduler::SchedulerError> {
        // Promote nice workers so object codegen runs at full speed.
        self.shared.promote_nice_workers.store(
            true,
            std::sync::atomic::Ordering::Release,
        );
        // Wake workers so they observe the promotion flag.
        self.shared.scheduler.wake_object_workers();

        self.shared.scheduler.wait_object_complete()
    }

    /// Shut down the session: signal workers to drain and exit.
    ///
    /// Sets the scheduler shutdown flag and wakes all condvars so nice
    /// workers observe shutdown and return. Scoped threads are joined
    /// automatically when the scope exits.
    pub fn shutdown(&mut self) {
        self.shared.scheduler.shutdown();
        // Inner session's Drop handles legacy codegen worker shutdown.
    }
}

// ---------------------------------------------------------------------------
// Nice worker spawning + loop (Step 10)
// ---------------------------------------------------------------------------

/// Spawn nice (low-priority) worker threads inside a `std::thread::scope`.
///
/// Takes `&Arc<SharedState>` and clones the Arc for each worker thread.
/// Workers hold independent Arc references — no aliasing with the caller's
/// `&mut CompilerSession`.
///
/// Workers park on the scheduler's `object_work_available` condvar and wake
/// when modules reach TypecheckDone or on shutdown. The scope guarantees
/// all threads join before it exits.
///
/// # Panics
///
/// Panics if the OS fails to spawn a thread. This is a setup-time
/// invariant: if the OS cannot create threads, the compiler cannot
/// function.
pub fn spawn_nice_workers<'scope, 'env>(
    scope: &'scope std::thread::Scope<'scope, 'env>,
    shared: &'env Arc<SharedState>,
    n: usize,
) {
    for i in 0..n {
        let worker_shared = Arc::clone(shared);
        std::thread::Builder::new()
            .name(format!("nice-worker-{}", i))
            .spawn_scoped(scope, move || {
                nice_worker_loop(&worker_shared);
            })
            .expect("failed to spawn nice worker thread");
    }
}

/// Main loop for nice (low-priority) worker threads.
///
/// Runs at reduced OS scheduling priority. Claims TypecheckDone modules
/// from the scheduler, compiles them to `.o` files via Cranelift
/// ObjectModule, writes the `.o` to the cache directory, and appends
/// the path to `shared.compiled_o_paths` for the linker.
///
/// When caching is disabled (`shared.cache_dir` is None) or no
/// `ObjectCodegenInput` is available for a module, the worker skips
/// `.o` compilation and just marks the module as object-complete.
///
/// The loop parks on `scheduler.take_object_codegen()` (condvar-based)
/// when no work is available, and exits on shutdown.
fn nice_worker_loop(shared: &SharedState) {
    // Set below-normal OS scheduling priority (best-effort).
    crate::thread_util::set_nice_priority();

    loop {
        // Check for priority promotion (hot flush before --link).
        if shared.promote_nice_workers.load(
            std::sync::atomic::Ordering::Relaxed,
        ) {
            crate::thread_util::set_normal_priority();
        }

        // Park until a TypecheckDone module with object_done == false
        // is available, or shutdown is signaled.
        let module = match shared.scheduler.take_object_codegen() {
            Some(m) => m,
            None => return, // Shutdown signaled.
        };

        // Attempt .o compilation if caching is enabled.
        if let Some(cache_dir) = &shared.cache_dir {
            compile_module_object(shared, &module, cache_dir);
        }

        // Notify scheduler that object codegen is done for this module.
        shared.scheduler.notify_object_codegen_complete(&module);
    }
}

/// Compile a single module to `.o` and `.meta.json` files in the cache directory.
///
/// Retrieves the module's `ObjectCodegenInput` (stashed by the priority worker),
/// builds an `ObjectCompileInput`, calls `compile_module_to_object()`, writes
/// the `.o` bytes, builds `CacheMetadata`, and writes `.meta.json`. Appends the
/// `.o` path to `shared.compiled_o_paths`.
///
/// Errors are logged to stderr and do not halt the worker — the module is still
/// marked object-complete so the scheduler lifecycle proceeds.
fn compile_module_object(
    shared: &SharedState,
    module: &ModuleFullPath,
    cache_dir: &Path,
) {
    use cranelisp_backend::cache;

    // Take the stashed input (lock briefly, remove entry to release memory).
    let input = {
        let mut inputs = shared.object_codegen_inputs.lock()
            .unwrap_or_else(|e| e.into_inner());
        inputs.remove(module)
    };

    let Some(input) = input else {
        // No data stashed — module may have had no compilable defns.
        return;
    };

    // Skip modules with no compilable defns (types-only, imports-only).
    if !crate::session::has_compilable_defns(&input.program) {
        return;
    }

    // Build the ObjectCompileInput from the stashed data.
    let object_input = crate::pipeline::build_object_compile_input(
        module,
        Some(&input.program),
        Some(&input.check_result),
        &input.cross_module_func_sigs,
    );

    // Compile to .o bytes via Cranelift ObjectModule.
    let obj_bytes = match cache::compile_module_to_object(&object_input) {
        Ok(bytes) => bytes,
        Err(e) => {
            eprintln!("nice-worker: .o compilation failed for {}: {}", module, e.message());
            return;
        }
    };

    // Write .o and .meta.json files to cache directory.
    let (meta_path, o_path) = cache::module_cache_path(cache_dir, module);

    // Ensure parent directory exists.
    if let Some(parent) = o_path.parent()
        && let Err(e) = std::fs::create_dir_all(parent)
    {
        eprintln!("nice-worker: cannot create cache dir '{}': {}", parent.display(), e);
        return;
    }

    if let Err(e) = std::fs::write(&o_path, &obj_bytes) {
        eprintln!("nice-worker: cannot write '{}': {}", o_path.display(), e);
        return;
    }

    // Build and write .meta.json for cache-hit restoration.
    let codegen_state = crate::pipeline::build_codegen_state_for_cache(
        &input.program,
        &input.check_result,
    );
    let metadata = cache::CacheMetadata {
        symbol_table: input.symbol_table,
        module_structure: input.module_structure,
        codegen_state,
    };
    if let Err(e) = cache::write_cached_metadata(&meta_path, &metadata) {
        eprintln!("nice-worker: .meta.json write failed for {}: {}", module, e.message());
        // Continue — the .o file was written successfully.
    }

    // Append the .o path for the linker.
    if let Ok(mut paths) = shared.compiled_o_paths.lock() {
        paths.push(o_path);
    }
}

