// CompilerSession: v4 pipeline session (pipeline-v4.md §5, roadmap Steps 0-7).
//
// Wraps the existing CompilationSession. Batch compilation goes through the v4
// scheduler-driven path with lazy dependency discovery (Step 5). REPL eval
// routes through process_module_forms(Additive) with serial per-form processing
// (Step 7).

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use cranelisp_types::{
    CodegenBehaviour, CompileContext, CranelispError,
    ModuleFullPath, ModuleStrategy, Span, Symbol,
    Type, Warning,
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

/// The v4 compiler session — the permanent session type for scheduler-driven
/// concurrent compilation.
///
/// Currently wraps `CompilationSession` and delegates all operations to the
/// old path. Each roadmap step progressively replaces delegation with native
/// v4 logic. The `--v4` CLI flag enables this session for testing.
pub struct CompilerSession {
    /// The wrapped old-path session. Removed when all delegation is replaced.
    inner: CompilationSession,

    /// Compilation scheduler (Step 2+). Tracks module lifecycle and
    /// coordinates work items for the priority worker loop.
    pub scheduler: CompileScheduler,

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

        CompilerSession {
            inner,
            scheduler: CompileScheduler::new(),
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

        let mut inner = CompilationSession::new_async_with_cache(cache_dir);
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
            scheduler: CompileScheduler::new(),
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
        self.scheduler.register_module(module.clone(), false);

        // Build sexp map for the worker loop.
        let mut module_sexps = HashMap::new();
        module_sexps.insert(module.clone(), sexps);

        // Build WorkerContext bundling all worker parameters.
        let mut ctx = WorkerContext {
            tc: &mut self.inner.tc,
            scheduler: &mut self.scheduler,
            inmem_worker: &mut self.inner.inmem_worker,
            platform_registry: &mut self.platform_registry,
            lib_dirs: &self.inner.lib_dirs,
            project_root: &self.inner.project_root,
        };

        // Run the priority worker loop inline (single-threaded).
        crate::worker::priority_worker_loop(
            &mut ctx,
            &mut module_sexps,
        )?;

        // Check scheduler completion.
        self.scheduler.wait_inmem_complete()?;

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

    /// Spawn nice (low-priority) worker threads for object file codegen.
    ///
    /// No-op for Step 3: object codegen deferred to Step 10.
    pub fn spawn_nice_workers(&self, _n: usize) {
        // Step 10: nice workers for .o codegen.
    }

    /// Shut down the session: stop workers, flush caches.
    ///
    /// Currently a no-op — the inner session handles cleanup via Drop.
    /// In v4, this will signal workers to drain and join (Step 3+).
    pub fn shutdown(&mut self) {
        // Inner session's Drop handles codegen worker shutdown.
    }
}

