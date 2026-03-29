// CompilerSession: v4 pipeline session skeleton (pipeline-v4.md §5, roadmap Step 0).
//
// Wraps the existing CompilationSession, delegating all methods to the old
// path. This is the permanent v4 session type — it starts as pure delegation
// and progressively replaces internals across Steps 1-15 of the roadmap.
//
// All methods that will eventually be replaced with scheduler-driven logic
// are marked with comments indicating which roadmap step replaces them.

use std::path::{Path, PathBuf};

use cranelisp_types::{
    CodegenBehaviour, CompileContext, CranelispError, ModuleFullPath, ModuleStrategy,
    ModuleStructure, Span, Type, Warning,
};

use crate::pipeline::{CodegenResult, CompileUnitResult};
use crate::session::CompilationSession;

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
// Scheduler stub (pipeline-v4.md §5 — replaced in Step 3+)
// ---------------------------------------------------------------------------

/// Placeholder scheduler that provides no-op wait methods.
///
/// The real `CompileScheduler` (Steps 3-5) tracks module lifecycle, priority
/// codegen queues, and worker coordination. This stub lets the v4 main flow
/// compile without the scheduler infrastructure.
pub struct SchedulerStub;

impl SchedulerStub {
    /// Wait for all in-memory (JIT) codegen to complete.
    ///
    /// No-op: the old path runs codegen synchronously before returning.
    /// Replaced by real scheduler in Step 3.
    pub fn wait_inmem_complete(&self) -> Result<(), CranelispError> {
        Ok(())
    }

    /// Wait for all object-file (.o) codegen to complete.
    ///
    /// No-op: the old path flushes cache writes synchronously.
    /// Replaced by real scheduler in Step 3.
    pub fn wait_object_complete(&self) -> Result<(), CranelispError> {
        Ok(())
    }
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

    /// Placeholder scheduler (replaced in Steps 3-5).
    pub scheduler: SchedulerStub,

    /// Project root directory (read-only after construction).
    pub project_root: PathBuf,
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

        let mut inner = CompilationSession::new_async();
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
            scheduler: SchedulerStub,
            project_root,
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
            scheduler: SchedulerStub,
            project_root,
        })
    }

    /// Register a module for compilation.
    ///
    /// Delegates to the old path: reads the source file, calls `compile_unit`
    /// + `send_codegen`. In v4, this will register the module with the
    /// scheduler for worker-driven processing (Step 3).
    pub fn register_module(
        &mut self,
        module_name: &str,
        source: &str,
        _entry_module_path: &Path,
    ) -> Result<(CompileUnitResult, Vec<Warning>), CranelispError> {
        let module_full_path = ModuleFullPath::from(module_name);

        let ctx = CompileContext {
            module: module_full_path,
            codegen: CodegenBehaviour::InMemoryAndObject,
        };

        let unit_result = self
            .inner
            .compile_unit(source, &ctx, ModuleStrategy::Replace)?;
        let warnings = unit_result.warnings.clone();
        self.inner.send_codegen(unit_result, ctx.clone());

        // Re-read the unit_result for the caller by compiling again? No —
        // we need to return something useful. The old main.rs kept unit_result
        // before sending codegen. Restructure: compile, clone warnings, send,
        // then return a synthetic result for the caller.
        //
        // Actually, the caller only needs the warnings and to know the module
        // was registered. Return the warnings.
        //
        // For run_mode, the caller needs the codegen results from flush.
        // That comes from wait_inmem_complete / flush_codegen.

        // FIXME(/int): I-3 — returns synthetic empty CompileUnitResult with ModuleFullPath::from("").
        // Misleading return type when only warnings are used. Step 3 replaces this delegation path.
        // Return empty CompileUnitResult — the real data was sent to codegen.
        // Callers that need codegen results use wait_inmem_complete().
        Ok((
            CompileUnitResult {
                program: Vec::new(),
                module_structure: ModuleStructure {
                    path: ModuleFullPath::from(""),
                    file_path: None,
                    mod_decls: Vec::new(),
                    import_specs: Vec::new(),
                    export_specs: Vec::new(),
                    platform_specs: Vec::new(),
                    impl_sexps: Vec::new(),
                    impls: Vec::new(),
                    dll_path: None,
                },
                check_result: empty_check_result(),
                source: String::new(),
                warnings: Vec::new(),
            },
            warnings,
        ))
    }

    /// Evaluate source text (REPL input).
    ///
    /// Delegates to the old path: `compile_unit` + `codegen_and_execute`.
    /// In v4, this will submit forms to the scheduler with Additive strategy
    /// and compile the trailing expression as a temporary closure (Step 7).
    pub fn eval(&mut self, source: &str) -> Result<Option<CodegenResult>, CranelispError> {
        let module = self.inner.tc.current_module_path().clone();
        let ctx = CompileContext {
            module,
            codegen: CodegenBehaviour::InMemoryAndObject,
        };

        let unit_result = self
            .inner
            .compile_unit(source, &ctx, ModuleStrategy::Additive)?;
        self.inner.send_codegen(unit_result, ctx);
        let results = self.inner.flush_codegen()?;
        Ok(results.into_iter().last())
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
    /// Delegates to the old path: looks up `main` in the GOT, calls it,
    /// and runs the IO trampoline if the return type is IO.
    pub fn trampoline(
        &mut self,
        module_name: &str,
    ) -> Result<(i64, Type), CranelispError> {
        // Flush codegen first to populate GOT slots.
        let codegen_results = self.inner.hot_flush_in_mem_queue()?;
        self.inner.shutdown_codegen();

        let result = codegen_results.into_iter().last().ok_or_else(|| {
            CranelispError::ModuleError {
                message: "no codegen result".into(),
                file: None,
                span: Span::SYNTHETIC,
            }
        })?;

        // Verify main exists.
        let main_sym = cranelisp_types::Symbol::from("main");
        let qualified_main =
            cranelisp_types::Symbol::from(format!("{}/main", module_name));
        let main_exists = self
            .inner
            .inmem_worker
            .got_state
            .def_codegen
            .contains_key(&main_sym)
            || self
                .inner
                .inmem_worker
                .got_state
                .def_codegen
                .contains_key(&qualified_main);

        if !main_exists {
            return Err(CranelispError::ModuleError {
                message: "entry module has no `main` function — batch mode requires (defn main [] ...)"
                    .into(),
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
        if result_type.is_io() {
            let inner_value = cranelisp_runtime::run_io_trampoline(raw_value);
            let inner_type = result_type.io_inner_type();
            Ok((inner_value, inner_type))
        } else {
            Ok((raw_value, result_type))
        }
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
    /// Not yet implemented — will be filled in Step 3 (scheduler).
    pub fn spawn_priority_workers(&self, _n: usize) {
        todo!("Step 3: spawn priority workers for typecheck + JIT codegen")
    }

    /// Spawn nice (low-priority) worker threads for object file codegen.
    ///
    /// Not yet implemented — will be filled in Step 3 (scheduler).
    pub fn spawn_nice_workers(&self, _n: usize) {
        todo!("Step 3: spawn nice workers for .o codegen")
    }

    /// Shut down the session: stop workers, flush caches.
    ///
    /// Currently a no-op — the inner session handles cleanup via Drop.
    /// In v4, this will signal workers to drain and join (Step 3+).
    pub fn shutdown(&mut self) {
        // Inner session's Drop handles codegen worker shutdown.
    }
}

/// Construct an empty CheckResult (used by register_module's synthetic return).
fn empty_check_result() -> cranelisp_types::CheckResult {
    cranelisp_types::CheckResult {
        method_resolutions: Default::default(),
        constrained_fn_names: Default::default(),
        mono_defns: Vec::new(),
        expr_types: Default::default(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
        type_defs: Default::default(),
        constructor_to_type: Default::default(),
        display: None,
    }
}
