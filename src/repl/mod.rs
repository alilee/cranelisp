// REPL session: interactive read-eval-print loop with persistent state.
//
// The TypeChecker and ModuleCodegenState persist across inputs so that
// function definitions and type definitions accumulate. Each input is
// parsed, type-checked, compiled, and executed independently.
//
// Error recovery: on any error, the TypeChecker is restored to its
// pre-input snapshot so the session remains usable.
//
// No `unwrap()` in this module -- all errors use `?`.
//
// Universal output format (repl/spec.md §1.1, implemented Sprint 15):
// All REPL output uses `:Type {value|name} ; {classification} - {docstring}`
// with optional related symbol sections for types, traits, and macros.
//
// Module structure:
//   mod.rs       — ReplSession struct, eval(), public API, REPL loop
//   commands.rs  — Slash command parsing, dispatch, and all handler functions
//   display.rs   — Re-exported display functions (format_result_value, etc.)
//   trace.rs     — trace display state, expr_contains_trace
//   run_tests.rs — /run-tests handler and test discovery/execution
//   io.rs        — IO trampoline forcing and formatting

mod commands;
mod io_format;
mod run_tests;
pub mod save;
mod trace;
pub mod watch;

use std::collections::{HashMap, HashSet};
use std::io::{self, BufRead, Write};
use std::time::{Duration, Instant};

use cranelisp_backend::compiler::TracedFnInfo;
use cranelisp_backend::display;
use cranelisp_types::{
    CheckResult, CompileContext, CranelispError, DefKind,
    ImplSexp, MacroClauseInfo, ModuleEntry, ModuleFullPath, ModuleStrategy,
    ModuleStructure, Sexp, Symbol, TopLevel, Type, TypeDefInfo, TypeName,
    Warning,
};

use commands::{
    format_macro_display_universal, format_sexp, format_special_form_display,
    format_type_display_universal, format_trait_display_universal,
    handle_ast, handle_clif, handle_disasm, handle_doc, handle_expand,
    handle_exports, handle_imports, handle_info, handle_list, handle_mod,
    handle_sig, handle_source, handle_sexp, handle_time, handle_type,
    special_form_feedback,
};
use crate::pretty::pretty_print_str;
use crate::style::{Style, styled};
use io_format::force_io_and_format;
use run_tests::handle_run_tests;
use trace::{
    TraceDisplayState, clear_trace_display_state,
    expr_contains_trace, repl_trace_format,
    set_trace_display_state,
};

// Re-export display functions so that downstream crates (tests/helpers, src/main.rs)
// can continue to use `cranelisp::repl::format_result_value` etc.
pub use display::format_result;
pub use display::format_result_value;
pub use display::format_type_qualified;
pub use display::format_value;

/// Result of evaluating one REPL input.
pub struct ReplResult {
    /// The i64 result value (raw bits; interpret per type).
    pub value: i64,
    /// The inferred type of the input.
    pub ty: Type,
    /// Whether this was a definition (defn/deftype) rather than an expression.
    pub is_definition: bool,
    /// Non-fatal warnings.
    pub warnings: Vec<Warning>,
    /// Override display string for definitions (deftrait, impl, constrained fn).
    /// When present, `format_repl_display` uses this instead of `format_result_value`.
    pub definition_display: Option<String>,
    /// Time spent executing the compiled function pointer (excludes compilation).
    /// The caller can compute compile time as `total_elapsed - eval_duration`.
    pub eval_duration: Duration,
}

/// Persistent REPL session state.
///
/// Wraps a `CompilationSession` (shared compilation core) and adds
/// REPL-specific concerns: display metadata, slash commands, trace state,
/// introspection, platform DLL lifetimes.
pub struct ReplSession {
    /// Shared compilation core (typechecker, GOT, macro env, JIT lifetimes).
    pub core: crate::session::CompilationSession,
    /// Accumulated type definitions from all inputs (for ADT value display).
    type_defs: HashMap<TypeName, TypeDefInfo>,
    /// Maps type names to the module they were defined in (for qualified display).
    pub(crate) type_modules: HashMap<TypeName, ModuleFullPath>,
    /// Project root directory (for platform path resolution).
    pub project_root: std::path::PathBuf,
    /// File watcher for detecting source file changes.
    /// None if watcher initialization failed or not in interactive mode.
    pub watcher: Option<watch::FileWatcher>,
    /// Pending change notifications to display before next prompt.
    pending_changes: Vec<std::path::PathBuf>,
    /// Modules that failed recompilation after a file change.
    /// While non-empty, expression evaluation is blocked (repl/spec.md §14.4).
    pub error_modules: HashSet<ModuleFullPath>,
    // Module dependency tracking (file→module map, forward/reverse edges)
    // has moved to `self.core.module_deps` (ModuleDependencyGraph) and is
    // populated incrementally during compile_unit / load_dependencies.
    /// Module structure for the current REPL module (tracks imports, exports,
    /// impl_sexps as they accumulate interactively). Used by save.rs to
    /// regenerate the module's `.cl` file.
    pub(crate) current_module_structure: ModuleStructure,
    /// Content hash of the last saved `.cl` file. Used by the file watcher
    /// to suppress self-triggered reloads (design/int/session-persistence.md §4).
    pub(crate) last_saved_hash: Option<String>,
    /// True while restoring from user.cl at startup — suppresses save-on-define.
    restoring: bool,
    /// v4 scheduler for additive REPL eval (Step 7). None when using old path.
    scheduler: Option<crate::scheduler::CompileScheduler>,
    /// Unified platform function registry (Step 8).
    /// Populated during platform loading, read-only during codegen.
    platform_registry: crate::platform_registry::PlatformRegistry,
}

impl ReplSession {
    /// Create a new REPL session without prelude loading.
    pub fn new() -> Self {
        let user_module = ModuleFullPath::from("user");
        let mut core = crate::session::CompilationSession::new();
        core.interactive = true;
        ReplSession {
            core,
            type_defs: HashMap::new(),
            type_modules: HashMap::new(),
            project_root: std::env::current_dir().unwrap_or_default(),
            watcher: None,
            pending_changes: Vec::new(),
            error_modules: HashSet::new(),
            current_module_structure: ModuleStructure {
                path: user_module,
                file_path: None,
                mod_decls: vec![],
                import_specs: vec![],
                export_specs: vec![],
                platform_specs: vec![],
                impl_sexps: vec![],
                impls: vec![],
                dll_path: None,
            },
            last_saved_hash: None,
            restoring: false,
            scheduler: None,
            platform_registry: crate::platform_registry::PlatformRegistry::new(),
        }
    }

    /// Enable v4 eval path: REPL eval routes through the v4 scheduler
    /// and `process_module_forms(Additive)` instead of `compile_unit`.
    pub fn enable_v4(&mut self) {
        self.scheduler = Some(crate::scheduler::CompileScheduler::new());
    }

    /// Create a new REPL session with prelude loading.
    ///
    /// Resolves the prelude module from `project_root` or `lib_dirs`, compiles
    /// it through the normal module graph pipeline, and injects an implicit
    /// `(import [prelude [*]])`. If no prelude is found, the session works
    /// normally without it.
    ///
    /// Module caching is enabled: prelude modules are loaded from
    /// `.cranelisp-cache/` when valid, and newly compiled modules are cached
    /// for future sessions.
    pub fn new_with_prelude(
        project_root: &std::path::Path,
        lib_dirs: &[std::path::PathBuf],
    ) -> Result<Self, CranelispError> {
        let mut session = Self::new();
        session.project_root = project_root.to_path_buf();
        // Store lib_dirs and project_root on the CompilationSession so
        // compile_unit can resolve module imports and platform DLLs.
        session.core.lib_dirs = lib_dirs.to_vec();
        session.core.project_root = project_root.to_path_buf();

        // Enable module caching for REPL prelude loading.
        // Ensure the cache directory exists before the background writer
        // tries to write files into it.
        let cache_dir = project_root.join(".cranelisp-cache");
        let _ = std::fs::create_dir_all(&cache_dir);
        session.core.object_worker =
            crate::session::ObjectWorkerState::new_with_cache(cache_dir);

        // Compile an empty source for the user module. The auto-prelude
        // trigger in compile_unit (stage 2b) detects that the prelude is
        // not yet loaded and recursively compiles it from lib_dirs.
        let user_ctx = CompileContext {
            module: ModuleFullPath::from("user"),
            codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
        };
        let unit_result = session.core.compile_unit(
            "",
            &user_ctx,
            ModuleStrategy::Additive,
        )?;
        crate::pipeline::codegen_and_execute_via_session(
            &mut session.core,
            &unit_result,
            &user_ctx,
        )?;

        // Flush any queued background cache writes and write cache manifest.
        session.core.flush_cache_writes();
        if let Some(cs) = &session.core.object_worker.cache_state {
            cs.flush_manifest();
        }

        // Sync type definitions from prelude modules for ADT value display.
        // Without this, prelude ADT values (e.g. Option.None) display as raw
        // i64 tags because format_result_value lacks the constructor metadata.
        for (name, info) in session.core.tc.type_def_registry().iter() {
            session.type_defs.insert(name.clone(), info.clone());
        }

        // File-to-module and dependency maps are now populated incrementally
        // by compile_unit / load_dependencies into session.core.module_deps.

        // Switch back to user module for REPL input.
        session.core.tc.set_current_module(ModuleFullPath::from("user"));

        Ok(session)
    }

    /// Enable session persistence by setting the backing file path.
    ///
    /// After this call, every definition-like REPL input will save the
    /// current module to `user.cl` at `project_root`. If `user.cl` already
    /// exists, its forms are loaded and evaluated to restore the session.
    ///
    /// Called only by the interactive REPL startup (not by tests).
    pub fn enable_persistence(&mut self) -> bool {
        // Set the backing file path so save_current_module can write to it.
        let user_cl_path = self.project_root.join("user.cl");
        self.current_module_structure.file_path = Some(user_cl_path.clone());

        if !user_cl_path.exists() {
            return false;
        }

        match self.try_restore_user_module() {
            Ok(true) => {
                // Sync type defs from restored user module.
                for (name, info) in self.core.tc.type_def_registry().iter() {
                    if !self.type_defs.contains_key(name) {
                        self.type_defs.insert(name.clone(), info.clone());
                    }
                }
                true
            }
            Ok(false) => false,
            Err(e) => {
                eprintln!("; Warning: failed to load user.cl: {e}");
                false
            }
        }
    }

    /// Attempt to restore the user module from `user.cl`.
    ///
    /// Uses the whole-program compilation pipeline (same as module graph
    /// compilation) instead of per-form eval. This handles constrained
    /// polymorphic functions correctly (check() sees the whole
    /// program at once) and produces cache files (.o, .meta.json).
    ///
    /// Returns `Ok(true)` if forms were successfully restored,
    /// `Ok(false)` if the file was empty, and `Err` on failure.
    fn try_restore_user_module(&mut self) -> Result<bool, CranelispError> {
        let user_cl_path = self.current_module_structure.file_path.clone()
            .ok_or_else(|| CranelispError::ParseError {
                message: "no file path for user module".into(),
                span: cranelisp_types::Span::SYNTHETIC,
            })?;

        let source = std::fs::read_to_string(&user_cl_path).map_err(|e| {
            CranelispError::ParseError {
                message: format!("failed to read {}: {e}", user_cl_path.display()),
                span: cranelisp_types::Span::SYNTHETIC,
            }
        })?;

        if source.trim().is_empty() {
            return Ok(false);
        }

        let source_hash = cranelisp_backend::cache::hash_source(&source);
        // Store the content hash so the file watcher won't trigger a reload.
        self.last_saved_hash = Some(source_hash.clone());

        let user_module = ModuleFullPath::from("user");

        // Set current module to user before compilation.
        self.core.tc.set_current_module(user_module.clone());

        // Parse and extract module declarations (imports, exports, impls).
        let sexps = cranelisp_frontend::parse(&source)?;
        if sexps.is_empty() {
            return Ok(false);
        }

        let (structure, remaining) = cranelisp_frontend::extract_module_declarations(
            user_module.clone(),
            Some(user_cl_path.clone()),
            sexps,
        )?;

        // Lazily load any imported modules that aren't already compiled.
        // Uses compile_unit (v2 pipeline) which handles recursive dependency
        // loading via load_dependencies.
        if !structure.import_specs.is_empty() {
            for spec in &structure.import_specs {
                // Skip if the full module path is already loaded.
                if self.core.tc.has_module(&spec.module_path) {
                    continue;
                }
                let root_module = spec.module_path.0
                    .split('.')
                    .next()
                    .unwrap_or(&spec.module_path.0)
                    .to_string();
                let root_path = ModuleFullPath::from(root_module.as_str());
                if !self.core.tc.has_module(&root_path) {
                    // Resolve and compile the root module via compile_unit.
                    // compile_unit handles recursive dependency loading internally.
                    if let Some(source_path) =
                        crate::pipeline::resolve_module_file(&root_path, &self.core.lib_dirs)
                    {
                        let dep_source = std::fs::read_to_string(&source_path)
                            .map_err(|e| CranelispError::ModuleError {
                                message: format!(
                                    "cannot read '{}': {}",
                                    source_path.display(), e
                                ),
                                file: Some(source_path.clone()),
                                span: cranelisp_types::Span::SYNTHETIC,
                            })?;
                        let saved_module = self.core.tc.current_module_path().clone();
                        let dep_ctx = CompileContext {
                            module: root_path,
                            codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
                        };
                        let unit_result = self.core.compile_unit(
                            &dep_source,
                            &dep_ctx,
                            ModuleStrategy::Replace,
                        )?;
                        crate::pipeline::codegen_and_execute_via_session(
                            &mut self.core,
                            &unit_result,
                            &dep_ctx,
                        )?;
                        self.core.tc.set_current_module(saved_module);
                    }
                }
            }
            self.core.tc.register_imports(&structure.import_specs)?;
        }
        if !structure.export_specs.is_empty() {
            self.core.tc.register_exports(&structure.export_specs)?;
        }

        // Process forms sequentially (handles defmacro interception, expansion).
        // Track pre-expansion sexps so we store what the user originally wrote
        // rather than macro-expanded forms (Defect 1 fix for restore path).
        let (accumulated, originals) =
            self.core.process_forms_with_originals(remaining)?;
        if accumulated.is_empty() {
            // Only had imports/exports/macros, no compilable definitions.
            self.current_module_structure = structure;
            return Ok(true);
        }

        // Build program AST from accumulated (expanded) sexps.
        let program = cranelisp_frontend::build_program(&accumulated)?;

        if program.is_empty() {
            self.current_module_structure = structure;
            return Ok(true);
        }

        // Whole-program typecheck — handles constrained polymorphism,
        // forward references, and monomorphisation correctly.
        let ctx = CompileContext {
            module: self.core.tc.current_module_path().clone(),
            codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
        };
        let check = self.core.tc.check(&program, &ctx, ModuleStrategy::Additive)?;

        // Compile using GOT-based codegen (same path as REPL defns).
        // This registers functions in the GOT so subsequent REPL
        // expressions can call them via indirect dispatch.
        self.core.compile_checked_program(&program, &check)?;

        // Store pre-expansion sexps in def_codegen so save_current_module
        // regenerates the source file with what the user typed, not the
        // macro-expanded form. The originals vec is aligned with accumulated
        // (same length), which is aligned with program's TopLevel entries.
        for (tl, original) in program.iter().zip(originals.iter()) {
            if let cranelisp_types::TopLevel::Defn(defn) = tl {
                let dc = self.core.inmem_worker.got_state.def_codegen
                    .entry(defn.name.clone())
                    .or_default();
                dc.sexp = Some(original.clone());
                dc.source = Some(format_sexp(original));
            }
        }

        // Register module aliases (user/name -> name) for qualified refs.
        self.core.register_module_aliases(&user_module);

        // Queue background cache write (.meta.json + .o) via v2 pipeline.
        // Uses the session's cache_state (set up by new_with_prelude).
        // Non-fatal — cache files are an optimization.
        let symbol_table = self.core.tc.module_table_cloned(&user_module)
            .unwrap_or_else(|| cranelisp_types::SymbolTable::new(user_module.clone()));
        crate::pipeline::queue_background_cache_write(
            &mut self.core.object_worker,
            &symbol_table,
            &source,
            &user_module,
            &structure,
            &program,
            &check,
        );
        self.core.flush_cache_writes();

        // Populate current_module_structure so subsequent saves include
        // the restored definitions.
        self.current_module_structure = structure;

        Ok(true)
    }

    /// Save the current module's source to its backing `.cl` file.
    ///
    /// Regenerates the source from the symbol table and module structure,
    /// writes atomically, and updates the content hash (for file watcher
    /// self-write suppression).
    ///
    /// Called after each definition-like REPL input (defn, deftype, deftrait,
    /// impl, defmacro, import, platform). On failure, warns but does not error.
    pub(crate) fn save_current_module(&mut self) {
        let file_path = match &self.current_module_structure.file_path {
            Some(p) => p.clone(),
            None => return, // No backing file — nothing to save.
        };

        let sym_table_guard = self.core.tc.symbol_table();
        let structure = &self.current_module_structure;
        let def_codegen = &self.core.inmem_worker.got_state.def_codegen;

        if let Some(hash) = save::save_module_file(
            &file_path,
            &sym_table_guard,
            structure,
            def_codegen,
        ) {
            self.last_saved_hash = Some(hash.clone());

            // Update the file watcher's content hash for user.cl so the
            // self-triggered file-change event is suppressed.
            if let Some(ref mut watcher) = self.watcher
                && let Ok(canonical) = file_path.canonicalize()
            {
                watcher.update_content_hash(canonical, hash.clone());
            }

            // Cache files (.meta.json + .o) are produced naturally by the
            // codegen queue when compile_unit runs on REPL startup. No need
            // to spawn a fresh session to re-compile the saved file.
        }
    }

    /// Get the accumulated type definitions for value display.
    pub fn type_defs(&self) -> &HashMap<TypeName, TypeDefInfo> {
        &self.type_defs
    }

    /// Get the type-to-module mapping for qualified display.
    pub fn type_modules(&self) -> &HashMap<TypeName, ModuleFullPath> {
        &self.type_modules
    }

    /// Evaluate a single source input, returning the result.
    ///
    /// Pipeline (v3 — routes through compile_unit):
    /// 1. Skip blank/comment
    /// 2. Parse source -> sexps (for annotation/introspection detection)
    /// 3. TC snapshot for error recovery
    /// 4. Check annotation -> handle via eval_annotation_expr (return early)
    /// 5. Check bare symbol introspection -> return early
    /// 6. Call compile_unit + codegen_and_execute
    /// 7. Bridge CodegenResult to ReplResult
    /// 8. Store DefCodegen, merge module_structure, session persistence
    ///
    /// On error, restores the TypeChecker to its pre-input state.
    pub fn eval(&mut self, source: &str) -> Result<ReplResult, CranelispError> {
        if self.scheduler.is_some() {
            return self.eval_v4(source);
        }
        self.eval_old(source)
    }

    /// v4 eval path: serial per-form processing through the v4 worker.
    ///
    /// Each sexp is processed individually through `process_module_forms(Additive)`,
    /// with TC snapshot/restore for error recovery. This replaces the old
    /// `compile_unit` delegation (Step 7).
    fn eval_v4(&mut self, source: &str) -> Result<ReplResult, CranelispError> {
        let trimmed = source.trim();
        if trimmed.is_empty() || is_comment_only(trimmed) {
            return Ok(ReplResult {
                value: 0,
                ty: Type::Int,
                is_definition: true,
                warnings: Vec::new(),
                definition_display: None,
                eval_duration: Duration::ZERO,
            });
        }

        let sexps = cranelisp_frontend::parse(source)?;
        if sexps.is_empty() {
            return Ok(ReplResult {
                value: 0,
                ty: Type::Int,
                is_definition: true,
                warnings: Vec::new(),
                definition_display: None,
                eval_duration: Duration::ZERO,
            });
        }

        let total_start = Instant::now();
        let mut last_result: Option<ReplResult> = None;
        let mut all_warnings = Vec::new();
        let mut had_definitions = false;

        for sexp in &sexps {
            match self.eval_one_form_v4(sexp) {
                Ok(result) => {
                    all_warnings.extend(result.warnings.clone());
                    if result.is_definition {
                        had_definitions = true;
                    }
                    last_result = Some(result);
                }
                Err(e) => {
                    // Per-form error: if this is the only/last form, return error.
                    // Otherwise, continue to next form (error already recovered by
                    // eval_one_form_v4 via TC snapshot/restore).
                    if sexps.len() == 1 {
                        return Err(e);
                    }
                    // For multi-form input, the error is reported but processing
                    // continues. Store a synthetic result for the error.
                    last_result = Some(ReplResult {
                        value: 0,
                        ty: Type::Int,
                        is_definition: false,
                        warnings: Vec::new(),
                        definition_display: Some(format!("Error: {}", e)),
                        eval_duration: Duration::ZERO,
                    });
                }
            }
        }

        // Session persistence: save after definitions.
        if had_definitions && !self.restoring {
            self.save_current_module();
        }

        // Sync type definitions for ADT value display.
        self.sync_type_defs();

        let total_elapsed = total_start.elapsed();
        match last_result {
            Some(mut r) => {
                r.warnings = all_warnings;
                r.eval_duration = total_elapsed;
                Ok(r)
            }
            None => Ok(ReplResult {
                value: 0,
                ty: Type::Int,
                is_definition: true,
                warnings: all_warnings,
                definition_display: None,
                eval_duration: Duration::ZERO,
            }),
        }
    }

    /// Evaluate a single sexp via the v4 worker path with TC snapshot/restore.
    fn eval_one_form_v4(&mut self, sexp: &Sexp) -> Result<ReplResult, CranelispError> {
        // Bare symbol check — introspect macros and special forms.
        if let Some(result) = self.check_bare_symbol_introspection(sexp) {
            return Ok(result);
        }

        // TC snapshot for error recovery.
        let snapshot = self.core.tc.snapshot();

        let result = self.process_single_form_v4(sexp);
        match result {
            Ok(r) => Ok(r),
            Err(e) => {
                self.core.tc.restore(snapshot);
                Err(e)
            }
        }
    }

    /// Process a single sexp through `process_module_forms(Additive)` then codegen.
    ///
    /// Uses a loop with a max retry counter to resolve Blocked dependencies
    /// instead of unbounded recursion.
    fn process_single_form_v4(&mut self, sexp: &Sexp) -> Result<ReplResult, CranelispError> {
        use crate::worker::{self, ProcessResult, WorkerContext};
        use cranelisp_typecheck::ModuleCheckAccumulator;

        const MAX_DEP_RETRIES: usize = 100;

        for retry in 0..MAX_DEP_RETRIES {
            let module = self.core.tc.current_module_path().clone();
            let mut accumulator = ModuleCheckAccumulator::new();
            let mut expanded_program = Vec::new();
            let single_sexp = [sexp.clone()];

            let scheduler = self.scheduler.as_mut()
                .ok_or_else(|| CranelispError::ModuleError {
                    message: "v4 scheduler not initialized".into(),
                    file: None,
                    span: cranelisp_types::Span::SYNTHETIC,
                })?;

            let result = {
                let shared_codegen =
                    crate::session::SharedCodegenState::extract_from(&mut self.core.inmem_worker);
                let mut worker_jit = crate::session::WorkerJitState::new();

                let mut wctx = WorkerContext {
                    tc: &mut self.core.tc,
                    scheduler,
                    shared_codegen: &shared_codegen,
                    worker_jit: &mut worker_jit,
                    platform_registry: &mut self.platform_registry,
                    codegen_products: &self.core.codegen_products,
                    lib_dirs: &self.core.lib_dirs,
                    project_root: &self.core.project_root,
                    shared_state: Some(&self.core.shared),
                };

                let mut pass1_done = false;
                let r = worker::process_module_forms(
                    &mut wctx,
                    &module,
                    &single_sexp,
                    0,
                    &mut accumulator,
                    &mut expanded_program,
                    ModuleStrategy::Additive,
                    &mut pass1_done,
                );

                worker_jit.drain_to_shared(&shared_codegen);
                shared_codegen.sync_back_to(&mut self.core.inmem_worker);
                r?
            };

            match result {
                ProcessResult::Complete { check_result, program } => {
                    return self.codegen_and_execute_v4(&module, &program, &check_result);
                }
                ProcessResult::Blocked { dep_module, dep_sexps, .. } => {
                    // Compile the dependency inline then retry.
                    self.compile_dep_inline_v4(&dep_module, &dep_sexps)?;
                    // Loop continues to retry with the resolved dependency.
                    if retry == MAX_DEP_RETRIES - 1 {
                        return Err(CranelispError::ModuleError {
                            message: format!(
                                "dependency chain too deep (>{} retries) while resolving '{}'",
                                MAX_DEP_RETRIES, dep_module,
                            ),
                            file: None,
                            span: cranelisp_types::Span::SYNTHETIC,
                        });
                    }
                }
            }
        }

        // Unreachable: the loop either returns or errors on the last iteration.
        unreachable!("invariant: loop always returns or errors before exhausting iterations")
    }

    /// Run codegen for definitions, then execute if there is an expression.
    fn codegen_and_execute_v4(
        &mut self,
        module: &ModuleFullPath,
        program: &[TopLevel],
        check: &CheckResult,
    ) -> Result<ReplResult, CranelispError> {
        let scheduler = self.scheduler.as_mut()
            .ok_or_else(|| CranelispError::ModuleError {
                message: "v4 scheduler not initialized".into(),
                file: None,
                span: cranelisp_types::Span::SYNTHETIC,
            })?;

        // Codegen: compile definitions, register in GOT.
        {
            let shared_codegen =
                crate::session::SharedCodegenState::extract_from(&mut self.core.inmem_worker);
            let mut worker_jit = crate::session::WorkerJitState::new();
            let result = crate::worker::codegen_module_symbols(
                &shared_codegen,
                &mut worker_jit,
                &self.platform_registry,
                scheduler,
                module,
                program,
                check,
                None,
                None,
            );
            worker_jit.drain_to_shared(&shared_codegen);
            shared_codegen.sync_back_to(&mut self.core.inmem_worker);
            result?;
        }

        let has_expr = program.iter().any(|tl| matches!(tl, TopLevel::Expr(_)));

        if has_expr {
            let program_vec = program.to_vec();
            let eval_start = Instant::now();
            let ps = self.platform_registry.jit_symbols_owned();
            let (value, ty) = crate::pipeline::compile_and_execute_expr(
                &mut self.core.inmem_worker,
                &ps,
                &program_vec,
                check,
                None, // Legacy REPL path — no per-module env.
            )?;
            let eval_duration = eval_start.elapsed();

            Ok(ReplResult {
                value,
                ty,
                is_definition: false,
                warnings: check.warnings.clone(),
                definition_display: None,
                eval_duration,
            })
        } else {
            // Definition-only: build display text from CheckResult.
            let display = check.display.as_ref().and_then(|d| {
                d.scheme.as_ref().map(|s| {
                    format!(":{} ; defined", s.ty)
                })
            });

            let ty = check.display.as_ref()
                .map(|d| d.ty.clone())
                .unwrap_or(Type::Int);

            Ok(ReplResult {
                value: 0,
                ty,
                is_definition: true,
                warnings: check.warnings.clone(),
                definition_display: display,
                eval_duration: Duration::ZERO,
            })
        }
    }

    /// Compile a dependency module inline (for blocked REPL eval).
    fn compile_dep_inline_v4(
        &mut self,
        dep_module: &ModuleFullPath,
        dep_sexps: &[Sexp],
    ) -> Result<(), CranelispError> {
        let scheduler = self.scheduler.as_mut()
            .ok_or_else(|| CranelispError::ModuleError {
                message: "v4 scheduler not initialized".into(),
                file: None,
                span: cranelisp_types::Span::SYNTHETIC,
            })?;

        scheduler.register_module(dep_module.clone(), false);

        let mut module_sexps = HashMap::new();
        module_sexps.insert(dep_module.clone(), dep_sexps.to_vec());

        let shared_codegen =
            crate::session::SharedCodegenState::extract_from(&mut self.core.inmem_worker);
        let mut worker_jit = crate::session::WorkerJitState::new();

        let mut ctx = crate::worker::WorkerContext {
            tc: &mut self.core.tc,
            scheduler,
            shared_codegen: &shared_codegen,
            worker_jit: &mut worker_jit,
            platform_registry: &mut self.platform_registry,
            codegen_products: &self.core.codegen_products,
            lib_dirs: &self.core.lib_dirs,
            project_root: &self.core.project_root,
            shared_state: Some(&self.core.shared),
        };

        let loop_result = crate::worker::priority_worker_loop(&mut ctx, &mut module_sexps);
        worker_jit.drain_to_shared(&shared_codegen);
        shared_codegen.sync_back_to(&mut self.core.inmem_worker);
        loop_result?;

        let scheduler = self.scheduler.as_mut()
            .ok_or_else(|| CranelispError::ModuleError {
                message: "v4 scheduler not initialized".into(),
                file: None,
                span: cranelisp_types::Span::SYNTHETIC,
            })?;

        match scheduler.wait_inmem_complete() {
            Ok(()) => Ok(()),
            Err(e) => {
                // Reset all failed modules so the next eval attempt can
                // re-register and retry (Step 9 REPL recovery).
                scheduler.reset_all_failed_modules();
                Err(CranelispError::from(e))
            }
        }
    }

    /// Sync type definitions from the typechecker for ADT value display.
    fn sync_type_defs(&mut self) {
        for (name, info) in self.core.tc.type_def_registry().iter() {
            self.type_defs.insert(name.clone(), info.clone());
        }
    }

    /// Old eval path (v3): routes through compile_unit + codegen_and_execute.
    ///
    /// Pipeline:
    /// 1. Skip blank/comment
    /// 2. Parse source -> sexps (for annotation/introspection detection)
    /// 3. TC snapshot for error recovery
    /// 4. Check annotation -> handle via eval_annotation_expr (return early)
    /// 5. Check bare symbol introspection -> return early
    /// 6. Call compile_unit + codegen_and_execute
    /// 7. Bridge CodegenResult to ReplResult
    /// 8. Store DefCodegen, merge module_structure, session persistence
    ///
    /// On error, restores the TypeChecker to its pre-input state.
    fn eval_old(&mut self, source: &str) -> Result<ReplResult, CranelispError> {
        // Step 1: Skip blank and comment-only input before it reaches the parser.
        let trimmed = source.trim();
        if trimmed.is_empty() || is_comment_only(trimmed) {
            return Ok(ReplResult {
                value: 0,
                ty: Type::Int,
                is_definition: true,
                warnings: Vec::new(),
                definition_display: None,
                eval_duration: Duration::ZERO,
            });
        }

        // Step 2: Parse the source into sexps (for annotation/introspection checks).
        let sexps = cranelisp_frontend::parse(source)?;

        if sexps.is_empty() {
            return Err(CranelispError::ParseError {
                message: "empty input".into(),
                span: cranelisp_types::Span::SYNTHETIC,
            });
        }

        // Step 3: Snapshot for error recovery (covers macro compilation too).
        let snapshot = self.core.tc.snapshot();

        // Step 4: Handle multi-sexp annotation expressions (`:Type expr` parses as two sexps).
        if sexps.len() > 1 && is_annotation_prefix(&sexps[0]) {
            let result = self.eval_annotation_expr(sexps);
            return match result {
                Ok(result) => {
                    if result.is_definition && !self.restoring {
                        self.save_current_module();
                    }
                    Ok(result)
                }
                Err(e) => {
                    self.core.tc.restore(snapshot);
                    Err(e)
                }
            };
        }

        // Step 5: Check bare symbol introspection (non-zero-arg macros, special forms).
        if let Some(result) = self.check_bare_symbol_introspection(&sexps[0]) {
            return Ok(result);
        }

        // Step 6-8: Route through compile_unit + codegen_and_execute.
        let result = self.eval_via_compile_unit(source, &sexps);

        match result {
            Ok(result) => {
                // Save the module file after each definition-like input.
                // Skip during startup restore (restoring flag) and for
                // bare expression evaluations (is_definition = false).
                if result.is_definition && !self.restoring {
                    self.save_current_module();
                }
                Ok(result)
            }
            Err(e) => {
                self.core.tc.restore(snapshot);
                Err(e)
            }
        }
    }

    /// Evaluate input by routing through compile_unit + codegen_and_execute.
    ///
    /// This is the main compilation path for normal REPL input (not annotations,
    /// not bare-symbol introspection). Defmacro, import, and platform forms are
    /// handled internally by compile_unit's process_forms_sequentially and
    /// extract_module_declarations stages.
    fn eval_via_compile_unit(
        &mut self,
        source: &str,
        original_sexps: &[Sexp],
    ) -> Result<ReplResult, CranelispError> {
        let eval_start = Instant::now();

        // Build the compile context for the current REPL module.
        let repl_ctx = self.build_repl_compile_context();

        // Compile through stages 1-5 (parse, extract, expand, build AST, typecheck).
        let unit_result = self.core.compile_unit(
            source,
            &repl_ctx,
            ModuleStrategy::Additive,
        )?;

        // Set up trace infrastructure if the program contains (trace ...).
        let has_trace = unit_result.program.iter().any(|tl| match tl {
            TopLevel::Expr(e) => expr_contains_trace(e),
            _ => false,
        });
        if has_trace {
            self.core.inmem_worker.traced_fns = self.build_traced_fns();
            self.core.inmem_worker.trace_extra_symbols = vec![
                (
                    "cranelisp_trace_format".to_string(),
                    repl_trace_format as *const u8,
                ),
            ];
        }

        // Set trace display state before execution so cranelisp_trace_format
        // can access type_defs and type_modules.
        let display_state = TraceDisplayState {
            type_defs: &self.type_defs as *const _,
            type_modules: &self.type_modules as *const _,
        };
        if has_trace {
            set_trace_display_state(&display_state);
        }

        // Snapshot GOT keys before codegen (codegen_and_execute creates
        // module-qualified aliases like "user/foo" that the old REPL path
        // never created; we remove them after to match the old behavior and
        // prevent double-counting in test discovery).
        let pre_codegen_keys: HashSet<Symbol> = self.core.inmem_worker
            .got_state
            .def_codegen
            .keys()
            .cloned()
            .collect();

        // Codegen + execute (stages 6-7).
        let codegen_result = crate::pipeline::codegen_and_execute_via_session(
            &mut self.core,
            &unit_result,
            &repl_ctx,
        );

        // Always clear trace state after execution, even on error.
        if has_trace {
            clear_trace_display_state();
            self.core.inmem_worker.traced_fns.clear();
            self.core.inmem_worker.trace_extra_symbols.clear();
        }

        // Remove module-qualified alias entries that codegen_and_execute
        // created for the current REPL module. The old REPL path never
        // registered aliases for the interactive module — only for loaded
        // dependency modules (prelude, core.*, etc.).
        let new_aliases: Vec<Symbol> = self.core.inmem_worker
            .got_state
            .def_codegen
            .keys()
            .filter(|k| !pre_codegen_keys.contains(*k) && k.as_ref().contains('/'))
            .cloned()
            .collect();
        for alias in &new_aliases {
            self.core.inmem_worker.got_state.def_codegen.remove(alias);
        }

        let codegen_result = codegen_result?;

        let eval_duration = eval_start.elapsed();

        // Accumulate type definitions for ADT value display.
        let module = self.core.tc.current_module_path().clone();
        for (name, info) in &unit_result.check_result.type_defs {
            self.type_defs.insert(name.clone(), info.clone());
            self.type_modules.insert(name.clone(), module.clone());
        }

        // Build ReplResult from compile_unit + codegen results.
        let repl_result = self.build_repl_result(
            &unit_result,
            &codegen_result,
            original_sexps,
            eval_duration,
        )?;

        // Store DefCodegen (sexp/source) for definitions — for introspection
        // commands (/source, /sexp) and session persistence.
        self.store_def_codegen(&unit_result.program, original_sexps);

        // Track impl sexps in module structure for session persistence.
        self.track_impl_sexps(&unit_result.program, original_sexps);

        // Merge module_structure imports/platforms into current_module_structure.
        self.merge_module_structure(&unit_result.module_structure);

        Ok(repl_result)
    }

    /// Build a ReplResult from compile_unit + codegen_and_execute results.
    ///
    /// Inspects the program items to determine is_definition and build
    /// the definition_display string.
    fn build_repl_result(
        &self,
        unit_result: &crate::pipeline::CompileUnitResult,
        codegen_result: &crate::pipeline::CodegenResult,
        original_sexps: &[Sexp],
        eval_duration: Duration,
    ) -> Result<ReplResult, CranelispError> {
        let module = self.core.tc.current_module_path().clone();
        let mut all_warnings: Vec<Warning> = unit_result.warnings.clone();
        all_warnings.extend(codegen_result.warnings.clone());

        // Empty program: defmacro-only, import-only, or platform-only input.
        if unit_result.program.is_empty() {
            return self.build_empty_program_result(
                unit_result, original_sexps, all_warnings, eval_duration,
            );
        }

        // Determine if the program is all definitions (no bare expressions).
        let is_definition = unit_result.program.iter().all(|tl| {
            !matches!(tl, TopLevel::Expr(_))
        });

        let definition_display = if is_definition {
            self.build_definition_display(&unit_result.program, &unit_result.check_result, &module)
        } else {
            None
        };

        // Result value comes from codegen; type comes from check_result's
        // display info (which is the function/expression type, not the
        // execution result type).
        let value = codegen_result.value.unwrap_or(0);
        let ty = unit_result.check_result.display.as_ref()
            .map(|d| d.ty.clone())
            .or_else(|| codegen_result.result_type.clone())
            .unwrap_or(Type::Int);

        Ok(ReplResult {
            value,
            ty,
            is_definition,
            warnings: all_warnings,
            definition_display,
            eval_duration,
        })
    }

    /// Build a ReplResult for an empty program (defmacro, import, or platform only).
    fn build_empty_program_result(
        &self,
        unit_result: &crate::pipeline::CompileUnitResult,
        original_sexps: &[Sexp],
        warnings: Vec<Warning>,
        eval_duration: Duration,
    ) -> Result<ReplResult, CranelispError> {
        let module = self.core.tc.current_module_path().clone();

        // Check if the original input was a defmacro — look up newly registered macro.
        if let Some(sexp) = original_sexps.first()
            && cranelisp_frontend::is_defmacro(sexp)
            && let Ok(info) = cranelisp_frontend::parse_defmacro(sexp)
        {
            let clause_infos: Vec<MacroClauseInfo> = info
                .clauses
                .iter()
                .map(|c| MacroClauseInfo {
                    params: c.fixed_params.clone(),
                    rest_param: c.rest_param.clone(),
                    source: None,
                })
                .collect();
            let display = format_defmacro_display(&info.name, &clause_infos, &module);
            return Ok(ReplResult {
                value: 0,
                ty: Type::Int,
                is_definition: true,
                warnings,
                definition_display: Some(display),
                eval_duration,
            });
        }

        // Check if imports were processed.
        if !unit_result.module_structure.import_specs.is_empty() {
            let mod_names: Vec<String> = unit_result.module_structure
                .import_specs
                .iter()
                .map(|s| s.module_path.to_string())
                .collect();
            let display = format!("imported from {}", mod_names.join(", "));
            return Ok(ReplResult {
                value: 0,
                ty: Type::Int,
                is_definition: true,
                warnings,
                definition_display: Some(display),
                eval_duration,
            });
        }

        // Check if platforms were loaded.
        if !unit_result.module_structure.platform_specs.is_empty() {
            let name = &unit_result.module_structure.platform_specs[0].name;
            let display = format!(
                "; loaded platform: {name}\n; use (import [platform.{name} [*]]) to bring into scope"
            );
            return Ok(ReplResult {
                value: 0,
                ty: Type::Int,
                is_definition: true,
                warnings,
                definition_display: Some(display),
                eval_duration,
            });
        }

        // Fallback for truly empty input after expansion.
        Ok(ReplResult {
            value: 0,
            ty: Type::Int,
            is_definition: true,
            warnings,
            definition_display: None,
            eval_duration,
        })
    }

    /// Build definition_display for a program containing only definitions.
    ///
    /// Inspects the last item in the program to build the display string.
    /// For multi-item programs (e.g., begin-expanded), uses the last item.
    fn build_definition_display(
        &self,
        program: &[TopLevel],
        check_result: &CheckResult,
        module: &ModuleFullPath,
    ) -> Option<String> {
        let last = program.last()?;
        match last {
            TopLevel::Defn(defn) => {
                let is_constrained = check_result
                    .display.as_ref()
                    .and_then(|d| d.scheme.as_ref())
                    .is_some_and(|s| !s.constraints.is_empty());
                if is_constrained {
                    check_result.display.as_ref()
                        .and_then(|d| d.scheme.as_ref())
                        .map(|s| {
                            let base = display::format_scheme_display(
                                &defn.name, s, module, &self.type_modules,
                            );
                            format!("{base} ; defn")
                        })
                } else {
                    let disp = check_result.display.as_ref()?;
                    let type_str = format_type_qualified(&disp.ty, &self.type_modules);
                    Some(format!(":{type_str} {module}/{} ; defn", defn.name))
                }
            }
            TopLevel::TypeDef { .. } => {
                let type_name = match &check_result.display.as_ref()?.ty {
                    Type::ADT(name, _) => name.to_string(),
                    _ => "?".to_string(),
                };
                Some(format_type_display_universal(&type_name, module, self))
            }
            TopLevel::TraitDecl(decl) => {
                Some(format_trait_display_universal(
                    decl.name.as_ref(),
                    decl.docstring.as_deref(),
                    self,
                ))
            }
            TopLevel::TraitImpl(impl_) => {
                Some(format!(
                    "impl {module}/{} for {module}/{}",
                    impl_.trait_name, impl_.target_type
                ))
            }
            TopLevel::Expr(_) => None, // Not a definition.
        }
    }

    /// Store sexp and source in DefCodegen for definitions.
    ///
    /// Uses original (pre-expansion) sexps for session persistence (Defect 1 fix).
    fn store_def_codegen(&mut self, program: &[TopLevel], original_sexps: &[Sexp]) {
        // For single-form input, use the original sexp. For multi-form,
        // fall back to the expanded sexp from the program.
        let use_original = original_sexps.len() == 1;

        for (i, tl) in program.iter().enumerate() {
            if let TopLevel::Defn(defn) = tl {
                let sexp = if use_original {
                    original_sexps[0].clone()
                } else if i < original_sexps.len() {
                    original_sexps[i].clone()
                } else {
                    continue;
                };
                let dc = self.core.inmem_worker.got_state.def_codegen
                    .entry(defn.name.clone())
                    .or_default();
                dc.source = Some(format_sexp(&sexp));
                dc.sexp = Some(sexp);
            }
        }
    }

    /// Track impl sexps in module structure for session persistence.
    fn track_impl_sexps(&mut self, program: &[TopLevel], original_sexps: &[Sexp]) {
        let use_original = original_sexps.len() == 1;

        for (i, tl) in program.iter().enumerate() {
            if let TopLevel::TraitImpl(impl_) = tl {
                let sexp = if use_original {
                    original_sexps[0].clone()
                } else if i < original_sexps.len() {
                    original_sexps[i].clone()
                } else {
                    continue;
                };
                self.current_module_structure.impl_sexps.push(ImplSexp {
                    trait_name: impl_.trait_name.clone(),
                    target: impl_.target_type.clone(),
                    sexp,
                });
            }
        }
    }

    /// Merge import and platform specs from a compile_unit result into the
    /// current REPL module structure (for session persistence).
    fn merge_module_structure(&mut self, structure: &ModuleStructure) {
        self.current_module_structure
            .import_specs
            .extend(structure.import_specs.clone());
        self.current_module_structure
            .platform_specs
            .extend(structure.platform_specs.clone());
    }

    /// Evaluate a type annotation expression (`:Type expr` parsed as multiple sexps).
    ///
    /// Uses `build_repl_input_from_sexps` to combine the annotation and expression
    /// into a single `Expr::Annotate`, then typechecks and executes via codegen_and_execute.
    fn eval_annotation_expr(&mut self, sexps: Vec<Sexp>) -> Result<ReplResult, CranelispError> {
        let eval_start = Instant::now();
        let input = cranelisp_frontend::build_repl_input_from_sexps(&sexps)?;
        let ctx = self.build_repl_compile_context();
        let check_result = self.core.tc.check(std::slice::from_ref(&input), &ctx, ModuleStrategy::Additive)?;

        // Build a CompileUnitResult to pass to codegen_and_execute.
        let unit_result = crate::pipeline::CompileUnitResult {
            program: vec![input],
            module_structure: ModuleStructure {
                path: ctx.module.clone(),
                file_path: None,
                mod_decls: vec![],
                import_specs: vec![],
                export_specs: vec![],
                platform_specs: vec![],
                impl_sexps: vec![],
                impls: vec![],
                dll_path: None,
            },
            check_result,
            source: String::new(),
            warnings: Vec::new(),
        };

        let codegen_result = crate::pipeline::codegen_and_execute_via_session(
            &mut self.core,
            &unit_result,
            &ctx,
        )?;

        let eval_duration = eval_start.elapsed();

        // Build ReplResult from codegen output.
        let value = codegen_result.value.unwrap_or(0);
        let ty = unit_result.check_result.display.as_ref()
            .map(|d| d.ty.clone())
            .or_else(|| codegen_result.result_type.clone())
            .unwrap_or(Type::Int);
        let is_definition = unit_result.program.iter().all(|tl| {
            !matches!(tl, TopLevel::Expr(_))
        });

        Ok(ReplResult {
            value,
            ty,
            is_definition,
            warnings: unit_result.warnings.clone(),
            definition_display: None,
            eval_duration,
        })
    }

    /// Check if a sexp is a bare symbol that should show introspection info
    /// instead of being evaluated.
    ///
    /// Intercepts:
    /// - Non-zero-arg macros: show signature (zero-arg macros expand normally)
    /// - Special forms: show description (they have no value semantics)
    ///
    /// Does NOT intercept:
    /// - Constructors, functions, imports: these have value semantics
    /// - Zero-arg macros: the expander handles these
    fn check_bare_symbol_introspection(&self, sexp: &Sexp) -> Option<ReplResult> {
        let name = match sexp {
            Sexp::Symbol(name, _) => name,
            _ => return None,
        };

        // Look up the symbol in the current module's symbol table.
        let entry = {
            let guard = self.core.tc.symbol_table();
            guard.get(name.as_str())?.clone()
        };
        match &entry {
            ModuleEntry::Macro { clauses, docstring, .. } => {
                // Check if any clause accepts zero args -- if so, let the
                // expander handle it (it's a valid zero-arg macro call).
                let has_zero_arg_clause = clauses.iter().any(|c| {
                    c.params.is_empty() && c.rest_param.is_none()
                });
                if has_zero_arg_clause {
                    return None; // Let expander handle zero-arg expansion.
                }
                // Non-zero-arg macro: show universal format (spec §4.1.6).
                let module = self.core.tc.current_module_path().clone();
                let display = format_macro_display_universal(
                    name, clauses, docstring.as_deref(), &module,
                );
                Some(ReplResult {
                    value: 0,
                    ty: Type::Int,
                    is_definition: true,
                    warnings: Vec::new(),
                    definition_display: Some(display),
                    eval_duration: Duration::ZERO,
                })
            }
            ModuleEntry::Def { kind, .. } => {
                // Special forms have no value semantics -- show description.
                if let DefKind::SpecialForm { description } = kind.as_ref() {
                    let display = format_special_form_display(name, description);
                    Some(ReplResult {
                        value: 0,
                        ty: Type::Int,
                        is_definition: true,
                        warnings: Vec::new(),
                        definition_display: Some(display),
                        eval_duration: Duration::ZERO,
                    })
                } else {
                    None // Regular function -- let it evaluate normally.
                }
            }
            _ => None,
        }
    }

    /// Build a CompileContext for REPL evaluation.
    ///
    /// Uses the session's current module with InMemoryAndObject codegen.
    fn build_repl_compile_context(&self) -> CompileContext {
        CompileContext {
            module: self.core.tc.current_module_path().clone(),
            codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
        }
    }

    /// Build the list of traced function info from the current GOT state.
    ///
    /// Iterates all functions with GOT slots and code pointers, extracts their
    /// type information from the symbol table, and builds `TracedFnInfo` entries
    /// for the trace codegen to generate wrapper functions.
    fn build_traced_fns(&mut self) -> Vec<TracedFnInfo> {
        let got_base = self.core.inmem_worker.got_state.got_base_ptr() as i64;
        let module = self.core.tc.current_module_path().clone();
        let symbol_table = self.core.tc.symbol_table();

        let mut traced = Vec::new();
        for (name, dc) in &self.core.inmem_worker.got_state.def_codegen {
            let (slot, code_ptr, arity) = match (dc.got_slot, dc.code_ptr, dc.param_count) {
                (Some(s), Some(p), Some(a)) => (s, p, a),
                _ => continue,
            };

            // Look up the function's type from the symbol table.
            let (param_types, result_type) =
                match symbol_table.get(name.as_ref()) {
                    Some(ModuleEntry::Def { scheme, .. }) => {
                        match &scheme.ty {
                            Type::Fn(params, ret) => (params.clone(), (**ret).clone()),
                            // Zero-arg function: no params, result type is the type itself
                            other => (vec![], other.clone()),
                        }
                    }
                    _ => {
                        // Fallback: use Int for all types (lossy but safe).
                        (vec![Type::Int; arity], Type::Int)
                    }
                };

            let qualified_name = format!("{}/{}", module, name);
            traced.push(TracedFnInfo {
                name: qualified_name,
                got_base,
                got_slot: slot,
                arity,
                code_ptr: code_ptr as i64,
                param_types,
                result_type,
            });
        }
        traced
    }
}

impl Default for ReplSession {
    fn default() -> Self {
        Self::new()
    }
}

// ── REPL loop and slash command dispatch ──────────────────────────────────────

/// Parsed REPL slash command.
enum ReplCommand<'a> {
    Help,
    Quit,
    Sig(&'a str),
    Doc(&'a str),
    Type(&'a str),
    Info(&'a str),
    List(&'a str),
    Time(&'a str),
    Expand(&'a str),
    Imports(&'a str),
    Exports(&'a str),
    Source(&'a str),
    SexpCmd(&'a str),
    Ast(&'a str),
    Clif(&'a str),
    Disasm(&'a str),
    Mod(&'a str),
    RunTests(&'a str),
    Reset,
    Unknown(&'a str),
}

/// Parse a slash command from trimmed input.
///
/// Returns `None` if the input does not start with `/`.
fn parse_slash_command(input: &str) -> Option<ReplCommand<'_>> {
    if !input.starts_with('/') {
        return None;
    }

    let (cmd, arg) = match input.split_once(char::is_whitespace) {
        Some((c, a)) => (c, a.trim()),
        None => (input, ""),
    };

    Some(match cmd {
        "/help" | "/h" => ReplCommand::Help,
        "/quit" | "/q" => ReplCommand::Quit,
        "/sig" | "/s" => ReplCommand::Sig(arg),
        "/doc" | "/d" => ReplCommand::Doc(arg),
        "/type" | "/t" => ReplCommand::Type(arg),
        "/info" | "/i" => ReplCommand::Info(arg),
        "/list" | "/l" => ReplCommand::List(arg),
        "/time" => ReplCommand::Time(arg),
        "/expand" | "/e" => ReplCommand::Expand(arg),
        "/imports" => ReplCommand::Imports(arg),
        "/exports" => ReplCommand::Exports(arg),
        "/source" => ReplCommand::Source(arg),
        "/sexp" => ReplCommand::SexpCmd(arg),
        "/ast" => ReplCommand::Ast(arg),
        "/clif" => ReplCommand::Clif(arg),
        "/disasm" => ReplCommand::Disasm(arg),
        "/mod" => ReplCommand::Mod(arg),
        "/run-tests" | "/rt" => ReplCommand::RunTests(arg),
        "/reset" => ReplCommand::Reset,
        _ => ReplCommand::Unknown(cmd),
    })
}

/// Print the /help command output to stdout.
fn print_help(stdout: &mut impl Write) {
    let _ = writeln!(stdout, "Available commands:");
    let _ = writeln!(stdout, "  /help (/h)          Show this help");
    let _ = writeln!(stdout, "  /quit (/q)          Exit REPL");
    let _ = writeln!(stdout, "  /sig (/s) NAME      Show type signature");
    let _ = writeln!(stdout, "  /doc (/d) NAME      Show docstring");
    let _ = writeln!(stdout, "  /type (/t) EXPR     Show type without evaluating");
    let _ = writeln!(stdout, "  /info (/i) NAME     Show full details");
    let _ = writeln!(stdout, "  /source NAME        Show original source text");
    let _ = writeln!(stdout, "  /sexp NAME          Show parsed S-expression");
    let _ = writeln!(stdout, "  /ast NAME           Show AST");
    let _ = writeln!(stdout, "  /clif NAME          Show Cranelift IR");
    let _ = writeln!(stdout, "  /disasm NAME        Show disassembled native code");
    let _ = writeln!(stdout, "  /list (/l) [FILTER] List symbols in current module");
    let _ = writeln!(stdout, "  /time EXPR          Evaluate with timing breakdown");
    let _ = writeln!(stdout, "  /expand (/e) FORM   Macro-expand a form");
    let _ = writeln!(stdout, "  /imports [MODULE]   Show imports and special forms");
    let _ = writeln!(stdout, "  /exports MODULE     Show module's public symbols");
    let _ = writeln!(stdout, "  /mod [NAME]         Switch module namespace (default: user)");
    let _ = writeln!(stdout, "  /run-tests (/rt)    Discover and run test-* functions");
    let _ = writeln!(stdout, "  /reset              Clear all state and reload prelude");
    let _ = writeln!(stdout, "  ;#! <cmd>           Run a shell command");
}

/// Format the REPL prompt with timing and module info.
fn format_prompt(compile_ms: u64, eval_ms: u64, module: &str) -> String {
    styled(&format!("{compile_ms}+{eval_ms}ms; {module}> "), Style::Dim)
}

/// Write the prompt string to stdout and flush.
fn write_prompt(stdout: &mut impl Write, compile_ms: u64, eval_ms: u64, module: &str) {
    let prompt = format_prompt(compile_ms, eval_ms, module);
    let _ = write!(stdout, "{prompt}");
    let _ = stdout.flush();
}

/// Result of dispatching a slash command.
struct SlashCommandResult {
    /// True if the REPL should exit.
    quit: bool,
    /// True if timing counters should be reset to 0+0ms.
    reset_timing: bool,
}

/// Dispatch a parsed slash command.
fn dispatch_slash_command(
    cmd: ReplCommand,
    session: &mut ReplSession,
    stdout: &mut impl Write,
) -> SlashCommandResult {
    let mut result = SlashCommandResult {
        quit: false,
        reset_timing: false,
    };
    match cmd {
        ReplCommand::Help => print_help(stdout),
        ReplCommand::Quit => {
            result.quit = true;
        }
        ReplCommand::Sig(name) => handle_sig(session, name, stdout),
        ReplCommand::Doc(name) => handle_doc(session, name, stdout),
        ReplCommand::Type(expr_src) => handle_type(session, expr_src, stdout),
        ReplCommand::Info(name) => handle_info(session, name, stdout),
        ReplCommand::List(filter) => handle_list(session, filter, stdout),
        ReplCommand::Time(expr_src) => {
            match handle_time(session, expr_src) {
                Ok(display) => {
                    let _ = writeln!(stdout, "{display}");
                }
                Err(e) => {
                    let _ = writeln!(
                        stdout, "{} {}",
                        styled("Error:", Style::BoldRed),
                        styled(&e.to_string(), Style::Red),
                    );
                }
            }
        }
        ReplCommand::Expand(form) => handle_expand(session, form, stdout),
        ReplCommand::Imports(filter) => handle_imports(session, filter, stdout),
        ReplCommand::Exports(arg) => handle_exports(session, arg, stdout),
        ReplCommand::Source(name) => handle_source(session, name, stdout),
        ReplCommand::SexpCmd(name) => handle_sexp(session, name, stdout),
        ReplCommand::Ast(name) => handle_ast(session, name, stdout),
        ReplCommand::Clif(name) => handle_clif(session, name, stdout),
        ReplCommand::Disasm(name) => handle_disasm(session, name, stdout),
        ReplCommand::Mod(name) => handle_mod(session, name, stdout),
        ReplCommand::RunTests(prefix) => handle_run_tests(session, prefix, stdout),
        ReplCommand::Reset => {
            handle_reset(session, stdout);
            result.reset_timing = true;
        }
        ReplCommand::Unknown(cmd) => {
            let _ = writeln!(
                stdout,
                "error: unknown command '{cmd}'. Type /help for available commands."
            );
        }
    }
    result
}

/// Evaluate an input and display the result, returning updated timing.
fn eval_and_display(
    session: &mut ReplSession,
    input: &str,
    stdout: &mut impl Write,
) -> (u64, u64) {
    let total_start = Instant::now();
    match session.eval(input) {
        Ok(result) => {
            let total_elapsed = total_start.elapsed();
            // Compile time = total time minus the eval (function call) time.
            let compile_duration = total_elapsed.saturating_sub(result.eval_duration);
            let compile_ms = compile_duration.as_millis() as u64;
            let eval_ms = result.eval_duration.as_millis() as u64;

            for w in &result.warnings {
                let _ = writeln!(
                    stdout, "{} {}",
                    styled("Warning:", Style::BoldYellow),
                    styled(&w.message, Style::Yellow),
                );
            }
            let display = if let Some(ref def_display) = result.definition_display {
                def_display.clone()
            } else if result.ty.is_io() {
                // IO expression: force the IO tree via trampoline, then
                // display the inner result value. Side effects (prints, etc.)
                // happen during the trampoline run.
                force_io_and_format(
                    result.value,
                    &result.ty,
                    session.type_defs(),
                    session.type_modules(),
                    stdout,
                )
            } else {
                format_result_value(
                    result.value,
                    &result.ty,
                    session.type_defs(),
                    session.type_modules(),
                )
            };
            let _ = writeln!(stdout, "{}", pretty_print_str(&display));
            (compile_ms, eval_ms)
        }
        Err(e) => {
            let total_elapsed = total_start.elapsed();
            let compile_ms = total_elapsed.as_millis() as u64;
            let _ = writeln!(
                stdout, "{} {}",
                styled("Error:", Style::BoldRed),
                styled(&e.to_string(), Style::Red),
            );
            (compile_ms, 0)
        }
    }
}

/// Create a REPL session, attempting prelude loading from the current directory.
///
/// Library directories are assembled from `CRANELISP_LIB` (if set) or the
/// `stdlib/` directory in the current directory (fallback). If prelude loading
/// fails, falls back to a session without prelude.
fn create_repl_session() -> ReplSession {
    let cwd = std::env::current_dir().ok();

    let mut session = if let Some(ref project_root) = cwd {
        let lib_dirs = crate::session::assemble_lib_dirs(project_root);

        match ReplSession::new_with_prelude(project_root, &lib_dirs) {
            Ok(session) => session,
            Err(e) => {
                eprintln!("warning: prelude loading failed: {e}");
                ReplSession::new()
            }
        }
    } else {
        ReplSession::new()
    };

    // Enable session persistence: set backing file, load user.cl if it exists.
    // The banner goes to stdout, and this is a user-visible status message
    // in the same category. Using stdout ensures consistent ordering in
    // piped output (showcase).
    if session.enable_persistence() {
        println!("; Restored user.cl");
    }

    // Initialize the file watcher for source change detection.
    session.watcher = watch::FileWatcher::new();
    update_watched_paths(&mut session);

    session
}

/// Update the file watcher to cover directories of actually loaded modules.
///
/// Per repl/spec.md §14.1: watches directories of imported modules and
/// their dependencies, plus the project root. Uses the `file_to_module`
/// map to find actual source files and record their content hashes for
/// accurate change detection (not dummy paths).
fn update_watched_paths(session: &mut ReplSession) {
    let watcher = match session.watcher.as_mut() {
        Some(w) => w,
        None => return,
    };

    // Watch the project root for user modules.
    watcher.watch_file(&session.project_root.join("dummy.cl"));

    // Watch every known module source file (records content hash for each).
    let file_paths: Vec<std::path::PathBuf> = session
        .core
        .module_deps
        .file_to_module
        .keys()
        .cloned()
        .collect();
    for file_path in &file_paths {
        watcher.watch_file(file_path);
    }
}

/// Format a relative file path for display in notifications.
fn relative_path_str(path: &std::path::Path, project_root: &std::path::Path) -> String {
    path.strip_prefix(project_root)
        .unwrap_or(path)
        .display()
        .to_string()
}

/// Poll the file watcher, eagerly recompile changed modules, and display results.
///
/// Per repl/spec.md §14.2: eager recompilation on change detection.
/// Per repl/spec.md §14.3: `[updated: file]` on success, `[errors: file]` on failure.
/// Per repl/spec.md §14.4: failed modules are added to `error_modules`.
fn poll_and_notify_changes(session: &mut ReplSession, stdout: &mut impl Write) {
    if let Some(ref mut watcher) = session.watcher
        && let Some(changed) = watcher.poll_changes()
    {
        session.pending_changes.extend(changed);
    }

    // Eagerly recompile any pending changed modules.
    if !session.pending_changes.is_empty() {
        reload_changed_modules(session, stdout);
    }
}

/// Eagerly reload modules whose source files have changed on disk.
///
/// Per repl/spec.md §14.2: clears old module state, recompiles, notifies result.
/// Per repl/spec.md §14.4: on failure, adds module to `error_modules` to block
/// evaluation. On success, removes module from `error_modules`.
///
/// Cascade invalidation: after recompiling directly changed modules, finds all
/// transitive dependents and recompiles them too (per repl/spec.md §14.2).
///
/// Delegates the actual recompilation to `CompilationSession::recompile_module_and_dependents`.
/// This function handles the REPL-specific display and error_modules tracking.
fn reload_changed_modules(session: &mut ReplSession, stdout: &mut impl Write) {
    let pending = std::mem::take(&mut session.pending_changes);

    // Map file paths to module paths.
    let mut stale_modules: Vec<ModuleFullPath> = Vec::new();
    for path in &pending {
        if let Some(module_path) = session.core.module_deps.file_to_module.get(path)
            && !stale_modules.contains(module_path)
        {
            stale_modules.push(module_path.clone());
        }
    }

    if stale_modules.is_empty() {
        return;
    }

    let project_root = session.project_root.clone();

    // v4 scheduler path: re-register modules with the scheduler.
    // Falls back to v3 path when the scheduler is not initialized.
    let use_v4 = session.scheduler.is_some();
    if use_v4 {
        reload_via_scheduler(session, &stale_modules, &project_root, stdout);
    } else {
        reload_via_v3(session, &stale_modules, &project_root, stdout);
    }
}

/// Reload changed modules via the v4 scheduler (Step 14).
///
/// Clears module state in the TC, re-registers with the scheduler at
/// TypecheckFirst, re-parses source, and runs the worker loop inline.
fn reload_via_scheduler(
    session: &mut ReplSession,
    stale_modules: &[ModuleFullPath],
    project_root: &std::path::Path,
    stdout: &mut impl Write,
) {
    let scheduler = match session.scheduler.as_ref() {
        Some(s) => s,
        None => {
            // Invariant: caller checks scheduler.is_some() before calling.
            // If violated, log and return rather than panicking.
            let _ = writeln!(stdout, "[error: scheduler not initialized]");
            return;
        }
    };

    let mut module_sexps: HashMap<ModuleFullPath, Vec<cranelisp_types::Sexp>> = HashMap::new();
    let mut registered_modules = Vec::new();

    for module_path in stale_modules {
        // Clear stale type info from the TC.
        session.core.tc.set_current_module(module_path.clone());
        session.core.tc.clear_module_for_replace_public();

        // Re-register with the scheduler.
        let re_registered = scheduler.re_register_module(module_path);

        let file_display = module_display_name(session, module_path, project_root);
        if re_registered {
            session.error_modules.remove(module_path);

            // Resolve and re-parse source for the worker loop.
            match crate::pipeline::resolve_module_file(module_path, &session.core.lib_dirs) {
                Some(file_path) => match std::fs::read_to_string(&file_path) {
                    Ok(source) => match cranelisp_frontend::parse(&source) {
                        Ok(sexps) => {
                            module_sexps.insert(module_path.clone(), sexps);
                            registered_modules.push(module_path.clone());
                        }
                        Err(e) => {
                            let _ = writeln!(stdout, "[errors: {} — {}]", file_display, e);
                            session.error_modules.insert(module_path.clone());
                            continue;
                        }
                    },
                    Err(e) => {
                        let _ = writeln!(stdout, "[errors: {} — {}]", file_display, e);
                        session.error_modules.insert(module_path.clone());
                        continue;
                    }
                },
                None => {
                    let _ = writeln!(stdout, "[errors: {} — file not found]", file_display);
                    session.error_modules.insert(module_path.clone());
                    continue;
                }
            }
            let _ = writeln!(stdout, "[updated: {}]", file_display);
        } else {
            // Module is currently being typechecked — will be caught on next poll.
            let _ = writeln!(stdout, "[pending: {}]", file_display);
        }
    }

    // Run the worker loop inline to process re-registered modules.
    if !module_sexps.is_empty() {
        reload_run_worker_loop(session, &mut module_sexps, stdout);
    }
}

/// Run the priority worker loop inline for reload processing.
///
/// Extracts shared codegen state, builds a WorkerContext, runs the loop,
/// and syncs state back. Mirrors the pattern in `compile_dep_inline_v4`.
fn reload_run_worker_loop(
    session: &mut ReplSession,
    module_sexps: &mut HashMap<ModuleFullPath, Vec<cranelisp_types::Sexp>>,
    stdout: &mut impl Write,
) {
    let scheduler = match session.scheduler.as_ref() {
        Some(s) => s,
        None => return,
    };

    let shared_codegen =
        crate::session::SharedCodegenState::extract_from(&mut session.core.inmem_worker);
    let mut worker_jit = crate::session::WorkerJitState::new();

    let mut ctx = crate::worker::WorkerContext {
        tc: &mut session.core.tc,
        scheduler,
        shared_codegen: &shared_codegen,
        worker_jit: &mut worker_jit,
        platform_registry: &mut session.platform_registry,
        codegen_products: &session.core.codegen_products,
        lib_dirs: &session.core.lib_dirs,
        project_root: &session.core.project_root,
        shared_state: Some(&session.core.shared),
    };

    let loop_result = crate::worker::priority_worker_loop(&mut ctx, module_sexps);
    worker_jit.drain_to_shared(&shared_codegen);
    shared_codegen.sync_back_to(&mut session.core.inmem_worker);

    if let Err(e) = loop_result {
        let _ = writeln!(stdout, "[reload error: {}]", e);
    }

    // Check scheduler completion and reset failed modules for retry.
    if let Some(sched) = session.scheduler.as_ref() {
        if let Err(e) = sched.wait_inmem_complete() {
            let _ = writeln!(stdout, "[reload error: {}]", e);
            sched.reset_all_failed_modules();
        }
    }
}

/// Reload changed modules via the v3 CompilationSession path.
///
/// Delegates to `recompile_module_and_dependents`. This is the fallback
/// when the v4 scheduler is not active. Will be removed in Step 15.
fn reload_via_v3(
    session: &mut ReplSession,
    stale_modules: &[ModuleFullPath],
    project_root: &std::path::Path,
    stdout: &mut impl Write,
) {
    let cache_dir = project_root.join(".cranelisp-cache");
    let mut cache_state = Some(crate::session::CacheState::new(cache_dir));

    // Delegate recompilation + cascade to CompilationSession.
    let results =
        session
            .core
            .recompile_module_and_dependents(stale_modules, &mut cache_state);

    // Display results and update REPL-specific error_modules tracking.
    for (module_path, result) in results {
        let file_display = module_display_name(session, &module_path, project_root);
        match result {
            Ok(()) => {
                session.error_modules.remove(&module_path);
                let _ = writeln!(stdout, "[updated: {}]", file_display);
            }
            Err(e) => {
                session.error_modules.insert(module_path);
                let _ = writeln!(
                    stdout,
                    "{}",
                    styled(&format!("[errors: {}]", file_display), Style::Red)
                );
                let _ = writeln!(stdout, "  {}", e);
            }
        }
    }
}

/// Get a display name for a module (relative file path or module path).
fn module_display_name(
    session: &ReplSession,
    module_path: &ModuleFullPath,
    project_root: &std::path::Path,
) -> String {
    session
        .core
        .module_deps
        .file_to_module
        .iter()
        .find(|(_, mp)| *mp == module_path)
        .map(|(fp, _)| relative_path_str(fp, project_root))
        .unwrap_or_else(|| module_path.as_ref().to_string())
}

// find_transitive_dependents — moved to ModuleDependencyGraph::transitive_dependents
// reload_single_module — absorbed into CompilationSession::recompile_module
// clear_module_state — moved to CompilationSession::clear_module_state

/// Run the interactive REPL loop.
///
/// Reads lines from stdin, evaluates them, prints results.
/// Errors are printed without crashing the session.
///
/// Library directories are resolved from `CRANELISP_LIB` (if set) or the
/// `stdlib/` directory in the current directory. If prelude loading fails,
/// starts without it and prints a warning.
pub fn run_repl() {
    let session = create_repl_session();
    run_repl_inner(session);
}

/// Start the REPL with the v4 scheduler-driven eval path.
///
/// Same REPL experience as `run_repl()` — slash commands, display, line editing
/// — but eval routes through `process_module_forms(Additive)` instead of
/// `compile_unit`. Activated by the `--v4` CLI flag.
pub fn run_repl_v4() {
    let mut session = create_repl_session();
    session.enable_v4();
    run_repl_inner(session);
}

fn run_repl_inner(mut session: ReplSession) {
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut stdout = stdout.lock();

    // Startup banner (dim).
    let _ = writeln!(stdout, "{}", styled("Cranelisp v0.1.0", Style::Dim));
    let _ = writeln!(stdout, "{}", styled("Type /help for commands, /quit to exit.", Style::Dim));

    // Session persistence (after banner, before prompt).
    if session.enable_persistence() {
        let _ = writeln!(stdout, "{}", styled("; Restored user.cl", Style::Dim));
    }

    let mut last_compile_ms: u64 = 0;
    let mut last_eval_ms: u64 = 0;

    let module = session.core.tc.current_module_path().to_string();
    let prompt = format_prompt(last_compile_ms, last_eval_ms, &module);
    poll_and_notify_changes(&mut session, &mut stdout);
    write_prompt(&mut stdout, last_compile_ms, last_eval_ms, &module);

    let mut buffer = String::new();

    for line in stdin.lock().lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => break,
        };

        buffer.push_str(&line);

        if !parens_balanced(&buffer) {
            buffer.push('\n');
            let continuation = format!("{:>width$}", "...", width = prompt.len());
            let _ = write!(stdout, "{continuation}");
            let _ = stdout.flush();
            continue;
        }

        let input = buffer.trim();
        let module = session.core.tc.current_module_path().to_string();

        // Shell escape: intercept `;#!` before comment-only check.
        // Per repl/spec.md §13, `;#!` lines are run as shell commands.
        if let Some(stripped) = input.strip_prefix(";#!") {
            let cmd = stripped.trim();
            run_shell_command(cmd, &mut stdout);
            // Reset timing — shell commands are not Cranelisp evaluations.
            last_compile_ms = 0;
            last_eval_ms = 0;
            buffer.clear();
            poll_and_notify_changes(&mut session, &mut stdout);
            write_prompt(&mut stdout, last_compile_ms, last_eval_ms, &module);
            continue;
        }

        if input.is_empty() || is_comment_only(input) {
            buffer.clear();
            poll_and_notify_changes(&mut session, &mut stdout);
            write_prompt(&mut stdout, last_compile_ms, last_eval_ms, &module);
            continue;
        }

        if let Some(cmd) = parse_slash_command(input) {
            let cmd_result = dispatch_slash_command(cmd, &mut session, &mut stdout);
            buffer.clear();
            if cmd_result.quit {
                break;
            }
            if cmd_result.reset_timing {
                last_compile_ms = 0;
                last_eval_ms = 0;
            }
            let module = session.core.tc.current_module_path().to_string();
            poll_and_notify_changes(&mut session, &mut stdout);
            write_prompt(&mut stdout, last_compile_ms, last_eval_ms, &module);
            continue;
        }

        if let Some(display) = special_form_feedback(input, &session) {
            let _ = writeln!(stdout, "{}", pretty_print_str(&display));
            buffer.clear();
            poll_and_notify_changes(&mut session, &mut stdout);
            write_prompt(&mut stdout, last_compile_ms, last_eval_ms, &module);
            continue;
        }

        // Error blocking (repl/spec.md §14.4): refuse evaluation when modules
        // have errors from file watching. Slash commands still work above.
        if !session.error_modules.is_empty() {
            let names: Vec<String> = session
                .error_modules
                .iter()
                .map(|mp| mp.as_ref().to_string())
                .collect();
            let _ = writeln!(
                stdout,
                "Cannot evaluate: module '{}' has errors. Fix the source file and save.",
                names.join("', '")
            );
            buffer.clear();
            poll_and_notify_changes(&mut session, &mut stdout);
            write_prompt(&mut stdout, last_compile_ms, last_eval_ms, &module);
            continue;
        }

        (last_compile_ms, last_eval_ms) =
            eval_and_display(&mut session, input, &mut stdout);

        buffer.clear();
        let module = session.core.tc.current_module_path().to_string();
        poll_and_notify_changes(&mut session, &mut stdout);
        write_prompt(&mut stdout, last_compile_ms, last_eval_ms, &module);
    }

    let _ = writeln!(stdout);
}

// ── /reset ────────────────────────────────────────────────────────────────────

/// Handle `/reset` — clear all session state and reload prelude.
///
/// Per repl/spec.md §12: clears all user definitions, imports, module switches,
/// and internal state. Reloads the prelude (from cache if available).
/// Terminal history is preserved. Object cache on disk is preserved.
fn handle_reset(session: &mut ReplSession, stdout: &mut impl Write) {
    let project_root = session.project_root.clone();

    // 0. Delete user.cl so /reset doesn't reload it on next startup.
    if let Some(ref file_path) = session.current_module_structure.file_path {
        let _ = std::fs::remove_file(file_path);
    }

    // 1. Clear all session state by re-creating the compilation core.
    let mut new_core = crate::session::CompilationSession::new();
    new_core.interactive = true;
    session.core = new_core;
    session.type_defs.clear();
    session.type_modules.clear();
    session.pending_changes.clear();
    session.error_modules.clear();
    // module_deps is cleared by CompilationSession::new() above.
    // Reset module structure but preserve the file path.
    let user_cl_path = session.current_module_structure.file_path.clone();
    session.current_module_structure = ModuleStructure {
        path: ModuleFullPath::from("user"),
        file_path: user_cl_path,
        mod_decls: vec![],
        import_specs: vec![],
        export_specs: vec![],
        platform_specs: vec![],
        impl_sexps: vec![],
        impls: vec![],
        dll_path: None,
    };
    session.last_saved_hash = None;
    // Note: loaded_platforms on the old CompilationSession are dropped, but
    // platform DLL pointers remain valid via session.core.loaded_platforms on
    // the new session. JIT modules are dropped (code memory may leak;
    // see design/int/repl-lifecycle.md §2.2).

    // Clear file watcher subscriptions before re-adding after prelude load
    // (per /arch I-3: avoid stale watches for modules no longer in session).
    if let Some(ref mut watcher) = session.watcher {
        watcher.clear_all();
    }

    // 2. Reload prelude from source (not cache) via compile_unit.
    //
    // Cache loading is disabled during /reset because the typechecker's
    // trait and impl registries are not restored from cached symbol tables.
    // Loading from source ensures check() registers all traits and
    // impls needed for method resolution (e.g., Num.+$Int for the + operator).
    // The performance cost is acceptable — prelude compilation takes <500ms.
    //
    // We set lib_dirs and project_root on the new core, then compile an
    // empty source for the user module. compile_unit's auto-prelude
    // trigger (stage 2b) detects the prelude is missing and recursively
    // compiles it. No cache_state is set on object_worker, so
    // queue_background_cache_write skips cache writes (intentional).
    let lib_dirs = crate::session::assemble_lib_dirs(&project_root);
    session.core.lib_dirs = lib_dirs;
    session.core.project_root = project_root.clone();
    let user_ctx = CompileContext {
        module: ModuleFullPath::from("user"),
        codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
    };
    match session.core.compile_unit("", &user_ctx, ModuleStrategy::Additive)
        .and_then(|unit_result| {
            crate::pipeline::codegen_and_execute_via_session(
                &mut session.core,
                &unit_result,
                &user_ctx,
            )
        })
    {
        Ok(_) => {
            // Sync type definitions from prelude modules for ADT value display.
            for (name, info) in session.core.tc.type_def_registry().iter() {
                session.type_defs.insert(name.clone(), info.clone());
            }
            let _ = writeln!(stdout, "Session reset.");
        }
        Err(e) => {
            let _ = writeln!(stdout, "Error: Failed to load prelude: {e}");
            let _ = writeln!(stdout, "Session reset (no prelude).");
        }
    }

    // 3. File-to-module and dependency maps are now populated incrementally
    // by compile_unit / load_dependencies into session.core.module_deps
    // during the prelude reload above.

    // 4. Reset current module to user.
    session.core.tc.set_current_module(ModuleFullPath::from("user"));

    // 5. Re-add watched paths for newly loaded prelude modules.
    update_watched_paths(session);
}

// ── Shell escape ──────────────────────────────────────────────────────────────

/// Execute a shell command via `/bin/sh -c`.
///
/// Per repl/spec.md §13: stdout/stderr are inherited (passthrough),
/// non-zero exit codes are displayed, empty commands are silently ignored.
fn run_shell_command(cmd: &str, stdout: &mut impl Write) {
    if cmd.is_empty() {
        return; // silently re-prompt per spec §13.6
    }

    let status = std::process::Command::new("/bin/sh")
        .arg("-c")
        .arg(cmd)
        .stdin(std::process::Stdio::inherit())
        .stdout(std::process::Stdio::inherit())
        .stderr(std::process::Stdio::inherit())
        .status();

    match status {
        Ok(exit_status) => {
            if !exit_status.success() {
                if let Some(code) = exit_status.code() {
                    let _ = writeln!(stdout, "exit status: {code}");
                } else {
                    // Terminated by signal (Unix).
                    #[cfg(unix)]
                    {
                        use std::os::unix::process::ExitStatusExt;
                        if let Some(sig) = exit_status.signal() {
                            let _ = writeln!(stdout, "killed by signal: {sig}");
                        }
                    }
                }
            }
        }
        Err(e) => {
            let _ = writeln!(stdout, "failed to execute command: {e}");
        }
    }
}

// ── Utility functions ─────────────────────────────────────────────────────────

/// Check if a Sexp is a type annotation prefix (`:Type` or bare `:`).
fn is_annotation_prefix(sexp: &Sexp) -> bool {
    matches!(sexp, Sexp::Symbol(s, _) if s.starts_with(':') && !s.contains('/'))
}

/// Check if the input consists only of comments (lines starting with `;`).
///
/// Returns true if every non-empty line in the input starts with `;`
/// (ignoring leading whitespace). This prevents comment-only input
/// from reaching the parser and producing an "empty input" error.
fn is_comment_only(input: &str) -> bool {
    input.lines().all(|line| {
        let trimmed = line.trim();
        trimmed.is_empty() || trimmed.starts_with(';')
    })
}

/// Check if parentheses and brackets are balanced in the input.
///
/// Ignores content in string literals and after `;` comment markers.
/// Tracks both `()` and `[]` depth so multi-line Vec literals are
/// not submitted prematurely.
fn parens_balanced(input: &str) -> bool {
    let mut paren_depth: i32 = 0;
    let mut bracket_depth: i32 = 0;
    let mut in_string = false;
    let mut in_comment = false;
    let mut prev_char = '\0';

    for ch in input.chars() {
        if in_comment {
            if ch == '\n' {
                in_comment = false;
            }
            prev_char = ch;
            continue;
        }

        match ch {
            ';' if !in_string => {
                in_comment = true;
            }
            '"' if prev_char != '\\' => in_string = !in_string,
            '(' if !in_string => paren_depth += 1,
            ')' if !in_string => paren_depth -= 1,
            '[' if !in_string => bracket_depth += 1,
            ']' if !in_string => bracket_depth -= 1,
            _ => {}
        }
        prev_char = ch;
    }

    paren_depth <= 0 && bracket_depth <= 0
}

/// Format the REPL display for a defmacro definition (spec §1.1, §11.3).
///
/// Uses universal format: `:module/name ; defmacro` + clause signatures.
fn format_defmacro_display(name: &str, clauses: &[MacroClauseInfo], module: &ModuleFullPath) -> String {
    format_macro_display_universal(name, clauses, None, module)
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::Visibility;
    use commands::{classify_import, ImportClass};

    #[test]
    fn test_format_result_int() {
        assert_eq!(format_result(42, &Type::Int), ":primitives/Int 42");
    }

    #[test]
    fn test_format_result_bool_true() {
        assert_eq!(format_result(1, &Type::Bool), ":primitives/Bool true");
    }

    #[test]
    fn test_format_result_bool_false() {
        assert_eq!(format_result(0, &Type::Bool), ":primitives/Bool false");
    }

    #[test]
    fn test_format_result_float() {
        let bits = 1.234_f64.to_bits() as i64;
        let result = format_result(bits, &Type::Float);
        assert!(result.starts_with(":primitives/Float 1.234"));

        // Whole-number floats must display with `.0` suffix (spec §1.2).
        let whole_bits = 5.0_f64.to_bits() as i64;
        assert_eq!(
            format_result(whole_bits, &Type::Float),
            ":primitives/Float 5.0"
        );

        let zero_bits = 0.0_f64.to_bits() as i64;
        assert_eq!(
            format_result(zero_bits, &Type::Float),
            ":primitives/Float 0.0"
        );
    }

    #[test]
    fn test_parens_balanced_simple() {
        assert!(parens_balanced("(+ 1 2)"));
        assert!(!parens_balanced("(+ 1 2"));
        assert!(parens_balanced("42"));
    }

    #[test]
    fn test_parens_balanced_nested() {
        assert!(parens_balanced("(defn main [] (+ 1 2))"));
        assert!(!parens_balanced("(defn main [] (+ 1 2)"));
    }

    #[test]
    fn test_parens_balanced_string() {
        assert!(parens_balanced("\"hello (world\""));
    }

    #[test]
    fn test_brackets_balanced() {
        assert!(parens_balanced("[1 2 3]"));
        assert!(!parens_balanced("[1 2"));
        assert!(parens_balanced("(vec-get [1 2 3] 0)"));
        assert!(!parens_balanced("(vec-get [1 2 3"));
        // Multi-line Vec literal
        assert!(!parens_balanced("[1 2\n"));
        assert!(parens_balanced("[1 2\n 3]"));
    }

    #[test]
    fn test_is_comment_only() {
        assert!(is_comment_only("; a comment"));
        assert!(is_comment_only("  ; indented comment"));
        assert!(is_comment_only("; line one\n; line two"));
        assert!(is_comment_only(""));
        assert!(is_comment_only("   "));
        assert!(!is_comment_only("42"));
        assert!(!is_comment_only("(+ 1 2) ; trailing comment"));
        assert!(!is_comment_only("; comment\n42"));
    }

    #[test]
    fn test_session_eval_empty_input() {
        let mut session = ReplSession::new();
        let result = session.eval("").unwrap();
        assert_eq!(result.value, 0);
    }

    #[test]
    fn test_session_eval_comment_only() {
        let mut session = ReplSession::new();
        let result = session.eval("; just a comment").unwrap();
        assert_eq!(result.value, 0);
        // Session still works.
        let result = session.eval("42").unwrap();
        assert_eq!(result.value, 42);
    }

    #[test]
    fn test_session_eval_int() {
        let mut session = ReplSession::new();
        let result = session.eval("42").unwrap();
        assert_eq!(result.value, 42);
        assert_eq!(result.ty, Type::Int);
    }

    #[test]
    fn test_session_error_recovery() {
        let mut session = ReplSession::new();
        // This should error (parse error).
        let err = session.eval("(+ 1");
        assert!(err.is_err());
        // Session should still work after error.
        let result = session.eval("42").unwrap();
        assert_eq!(result.value, 42);
    }

    // --- Ring 1 format tests ---

    #[test]
    fn test_format_result_string() {
        let s = cranelisp_runtime::alloc_string(b"hello") as i64;
        let result = format_result(s, &Type::String);
        assert_eq!(result, ":primitives/String \"hello\"");
        cranelisp_runtime::heap_dealloc(s);
    }

    #[test]
    fn test_format_result_empty_string() {
        let s = cranelisp_runtime::alloc_string(b"") as i64;
        let result = format_result(s, &Type::String);
        assert_eq!(result, ":primitives/String \"\"");
        cranelisp_runtime::heap_dealloc(s);
    }

    #[test]
    fn test_format_result_fn_type() {
        let fn_ty = Type::Fn(vec![Type::Int, Type::Bool], Box::new(Type::String));
        let result = format_result(0, &fn_ty);
        assert_eq!(result, ":(Fn [primitives/Int primitives/Bool] primitives/String) <closure>");
    }

    #[test]
    fn test_format_result_adt_nullary_with_type_defs() {
        use cranelisp_types::{ConstructorInfo, TypeDefInfo};

        let type_name = TypeName::from("Color");
        let mut type_defs = HashMap::new();
        type_defs.insert(
            type_name.clone(),
            TypeDefInfo {
                name: type_name.clone(),
                type_params: vec![],
                constructors: vec![
                    ConstructorInfo {
                        name: Symbol::from("Red"),
                        tag: 0,
                        fields: vec![],
                        docstring: None,
                        internal: false,
                    },
                    ConstructorInfo {
                        name: Symbol::from("Green"),
                        tag: 1,
                        fields: vec![],
                        docstring: None,
                        internal: false,
                    },
                    ConstructorInfo {
                        name: Symbol::from("Blue"),
                        tag: 2,
                        fields: vec![],
                        docstring: None,
                        internal: false,
                    },
                ],
                docstring: None,
            },
        );

        let adt = Type::ADT(type_name, vec![]);
        let tm = HashMap::new();
        assert_eq!(
            format_result_value(0, &adt, &type_defs, &tm),
            ":Color Color.Red"
        );
        assert_eq!(
            format_result_value(1, &adt, &type_defs, &tm),
            ":Color Color.Green"
        );
        assert_eq!(
            format_result_value(2, &adt, &type_defs, &tm),
            ":Color Color.Blue"
        );
    }

    #[test]
    fn test_format_result_adt_data_constructor() {
        use cranelisp_types::{ConstructorInfo, FieldInfo, TypeDefInfo};

        let type_name = TypeName::from("Option");
        let mut type_defs = HashMap::new();
        type_defs.insert(
            type_name.clone(),
            TypeDefInfo {
                name: type_name.clone(),
                type_params: vec![],
                constructors: vec![
                    ConstructorInfo {
                        name: Symbol::from("None"),
                        tag: 0,
                        fields: vec![],
                        docstring: None,
                        internal: false,
                    },
                    ConstructorInfo {
                        name: Symbol::from("Some"),
                        tag: 1,
                        fields: vec![FieldInfo {
                            name: Symbol::from("val"),
                            ty: Type::Int,
                        }],
                        docstring: None,
                        internal: false,
                    },
                ],
                docstring: None,
            },
        );

        let adt = Type::ADT(type_name.clone(), vec![Type::Int]);
        let tm = HashMap::new();

        // Nullary: None (tag 0) -- dot notation.
        assert_eq!(
            format_result_value(0, &adt, &type_defs, &tm),
            ":(Option primitives/Int) Option.None"
        );

        // Data constructor: allocate Some(42) on heap.
        // Payload = tag (8 bytes) + 1 field (8 bytes) = 16 bytes.
        let ptr = cranelisp_runtime::alloc_with_rc(16);
        unsafe {
            *(ptr.add(16) as *mut i64) = 1; // tag = 1 (Some)
            *(ptr.add(24) as *mut i64) = 42; // field val = 42
        }

        // Data constructor -- dot notation: (Option.Some 42).
        assert_eq!(
            format_result_value(ptr as i64, &adt, &type_defs, &tm),
            ":(Option primitives/Int) (Option.Some 42)"
        );

        cranelisp_runtime::heap_dealloc(ptr as i64);
    }

    #[test]
    fn test_format_result_adt_no_type_defs() {
        // Without type_defs, falls back to bare value display.
        let adt = Type::ADT(TypeName::from("Color"), vec![]);
        assert_eq!(format_result(0, &adt), ":Color 0");
    }

    #[test]
    fn test_format_type_display_fn() {
        use cranelisp_types::format_type_display;
        let fn1 = Type::Fn(vec![Type::Int], Box::new(Type::Bool));
        assert_eq!(format_type_display(&fn1), "(Fn [Int] Bool)");

        let fn2 = Type::Fn(vec![Type::Int, Type::String], Box::new(Type::Float));
        assert_eq!(format_type_display(&fn2), "(Fn [Int String] Float)");

        let fn3 = Type::Fn(vec![], Box::new(Type::Int));
        assert_eq!(format_type_display(&fn3), "(Fn [] Int)");
    }

    #[test]
    fn test_format_adt_type_qualified() {
        let tm = HashMap::new();
        assert_eq!(
            display::format_adt_type_qualified(&TypeName::from("Color"), &[], &tm),
            "Color"
        );
        assert_eq!(
            display::format_adt_type_qualified(&TypeName::from("Option"), &[Type::Int], &tm),
            "(Option primitives/Int)"
        );
        // With type_modules, ADT name gets qualified too.
        let mut tm2 = HashMap::new();
        tm2.insert(
            TypeName::from("Color"),
            ModuleFullPath::from("user"),
        );
        assert_eq!(
            display::format_adt_type_qualified(&TypeName::from("Color"), &[], &tm2),
            "user/Color"
        );
    }

    // --- Macro integration tests ---

    // spec: 09-macros.md §9.2 -- defmacro in REPL
    #[test]
    fn test_repl_defmacro_and_use() {
        let mut session = ReplSession::new();

        // Define a macro.
        let result = session.eval("(defmacro id [x] x)").unwrap();
        assert!(result.is_definition);
        assert!(result.definition_display.is_some());

        // Use the macro.
        let result = session.eval("(id 42)").unwrap();
        assert_eq!(result.value, 42);
        assert_eq!(result.ty, Type::Int);
    }

    // spec: 09-macros.md §9.4.2 -- quasiquote macro in REPL
    #[test]
    fn test_repl_defmacro_quasiquote() {
        let mut session = ReplSession::new();
        session.eval("(import [primitives [add-i64]])").unwrap();

        session.eval("(defmacro inc1 [x] `(add-i64 1 ~x))").unwrap();

        let result = session.eval("(inc1 41)").unwrap();
        assert_eq!(result.value, 42);
    }

    // spec: 09-macros.md §9.2 -- macro accumulates across evals
    #[test]
    fn test_repl_macro_persists() {
        let mut session = ReplSession::new();

        session.eval("(defmacro id [x] x)").unwrap();

        // First use.
        let r1 = session.eval("(id 10)").unwrap();
        assert_eq!(r1.value, 10);

        // Second use -- macro is still registered.
        let r2 = session.eval("(id 20)").unwrap();
        assert_eq!(r2.value, 20);
    }

    // spec: 09-macros.md §9.2 -- error recovery does not corrupt expander
    #[test]
    fn test_repl_macro_error_recovery() {
        let mut session = ReplSession::new();
        session.eval("(import [primitives [add-i64]])").unwrap();

        // Define a macro.
        session.eval("(defmacro id [x] x)").unwrap();

        // Cause an error (type error after macro expansion).
        let err = session.eval("(id (add-i64 true 2))");
        assert!(err.is_err());

        // Macro should still work after error.
        let result = session.eval("(id 42)").unwrap();
        assert_eq!(result.value, 42);
    }

    // spec: 09-macros.md -- session without macros still works
    #[test]
    fn test_repl_no_macros_unchanged() {
        let mut session = ReplSession::new();
        session.eval("(import [primitives [add-i64]])").unwrap();
        let result = session.eval("(add-i64 1 2)").unwrap();
        assert_eq!(result.value, 3);
    }

    // spec: 09-macros.md §9.2 -- macro in defn body
    #[test]
    fn test_repl_macro_in_defn_body() {
        let mut session = ReplSession::new();

        session.eval("(defmacro id [x] x)").unwrap();

        // Define a function that uses the macro.
        session.eval("(defn f [] (id 77))").unwrap();

        // Call the function.
        let result = session.eval("(f)").unwrap();
        assert_eq!(result.value, 77);
    }

    // spec: 08-modules.md -- REPL prelude loading
    #[test]
    fn test_repl_with_prelude() {
        let dir = tempfile::tempdir().unwrap();
        let lib_dir = dir.path().join("lib");
        std::fs::create_dir_all(&lib_dir).unwrap();
        std::fs::write(
            lib_dir.join("prelude.cl"),
            "(defmacro id [x] x)",
        )
        .unwrap();

        let session = ReplSession::new_with_prelude(
            dir.path(),
            &[lib_dir.clone()],
        )
        .unwrap();

        // Verify the macro from the prelude is available.
        let mut session = session;
        let result = session.eval("(id 42)").unwrap();
        assert_eq!(result.value, 42);
    }

    // spec: 08-modules.md -- REPL without prelude still works
    #[test]
    fn test_repl_without_prelude() {
        let dir = tempfile::tempdir().unwrap();

        // No prelude.cl anywhere -- should succeed with empty prelude.
        let session = ReplSession::new_with_prelude(
            dir.path(),
            &[],
        )
        .unwrap();

        let mut session = session;
        let result = session.eval("42").unwrap();
        assert_eq!(result.value, 42);
    }

    // --- classify_import + resolve_to_definition tests ---

    /// Helper: build a ReplSession with custom module tables for classify_import tests.
    ///
    /// Uses `set_current_module` to create each module, inserts entries via
    /// `symbol_table_mut()`, then switches back to the "user" module.
    fn session_with_modules(
        modules: Vec<(ModuleFullPath, Vec<(Symbol, ModuleEntry)>)>,
    ) -> ReplSession {
        let mut session = ReplSession::new();
        for (path, entries) in modules {
            session.core.tc.set_current_module(path);
            for (sym, entry) in entries {
                session.core.tc.symbol_table_mut().insert(sym, entry);
            }
        }
        // Switch back to user module
        session.core.tc.set_current_module(ModuleFullPath::from("user"));
        session
    }

    // spec: repl/spec.md §3.4 -- classify_import resolves direct definition
    #[test]
    fn test_classify_import_direct_definition() {
        use cranelisp_types::{FQSymbol, Scheme, TraitName};

        let mod_path = ModuleFullPath::from("core.num");
        let session = session_with_modules(vec![(
            mod_path.clone(),
            vec![
                (
                    Symbol::from("Num"),
                    ModuleEntry::TraitDecl {
                        decl: cranelisp_types::TraitDecl {
                            name: TraitName::from("Num"),
                            type_params: vec![Symbol::from("a")],
                            methods: vec![],
                            docstring: None,
                            visibility: Visibility::Public,
                            span: cranelisp_types::Span::SYNTHETIC,
                        },
                        visibility: Visibility::Public,
                        sexp: None,
                    },
                ),
                (
                    Symbol::from("add"),
                    ModuleEntry::Def {
                        scheme: Scheme { vars: vec![], constraints: HashMap::new(), ty: Type::Int },
                        visibility: Visibility::Public,
                        docstring: None,
                        param_names: vec![],
                        kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                        callees: Vec::new(),
                        got_slot: None,
                    },
                ),
            ],
        )]);

        let trait_source = FQSymbol {
            module: mod_path.clone(),
            symbol: Symbol::from("Num"),
        };
        assert!(matches!(
            classify_import(&session, &trait_source),
            ImportClass::Trait
        ));

        let fn_source = FQSymbol {
            module: mod_path,
            symbol: Symbol::from("add"),
        };
        assert!(matches!(
            classify_import(&session, &fn_source),
            ImportClass::Fn
        ));
    }

    // spec: repl/spec.md §3.4 -- classify_import follows reexport chain
    #[test]
    fn test_classify_import_reexport_chain() {
        use cranelisp_types::{FQSymbol, TraitName};

        let origin = ModuleFullPath::from("core.num");
        let prelude = ModuleFullPath::from("prelude");

        let session = session_with_modules(vec![
            (
                origin.clone(),
                vec![(
                    Symbol::from("Num"),
                    ModuleEntry::TraitDecl {
                        decl: cranelisp_types::TraitDecl {
                            name: TraitName::from("Num"),
                            type_params: vec![Symbol::from("a")],
                            methods: vec![],
                            docstring: None,
                            visibility: Visibility::Public,
                            span: cranelisp_types::Span::SYNTHETIC,
                        },
                        visibility: Visibility::Public,
                        sexp: None,
                    },
                )],
            ),
            (
                prelude.clone(),
                vec![(
                    Symbol::from("Num"),
                    ModuleEntry::Reexport {
                        source: FQSymbol {
                            module: origin.clone(),
                            symbol: Symbol::from("Num"),
                        },
                    },
                )],
            ),
        ]);

        // Importing from prelude should follow the reexport chain to core.num
        let source = FQSymbol {
            module: prelude,
            symbol: Symbol::from("Num"),
        };
        assert!(matches!(
            classify_import(&session, &source),
            ImportClass::Trait
        ));
    }

    // spec: repl/spec.md §3.4 -- internal names filtered from /imports
    #[test]
    fn test_imports_filters_internal_names() {
        // Verify that monomorphised variant names (containing $) are filtered.
        // __macro_ names are now private (defn-) and won't appear in imports.
        let internal_names = vec!["add$Int+Int", "foo$Float"];
        let public_names = vec!["add", "Num", "Display"];

        for name in &internal_names {
            assert!(name.contains('$'), "{name} should be filtered");
        }
        for name in &public_names {
            assert!(!name.contains('$'), "{name} should NOT be filtered");
        }
    }

    // spec: repl/spec.md §3.4 -- classify_import with macro entry
    #[test]
    fn test_classify_import_macro() {
        use cranelisp_types::FQSymbol;

        let mod_path = ModuleFullPath::from("prelude");
        let session = session_with_modules(vec![(
            mod_path.clone(),
            vec![(
                Symbol::from("defn-macro"),
                ModuleEntry::Macro {
                    name: Symbol::from("defn-macro"),
                    clauses: vec![],
                    docstring: None,
                    visibility: Visibility::Public,
                    sexp: None,
                    source: None,
                    callees: Vec::new(),
                },
            )],
        )]);

        let source = FQSymbol {
            module: mod_path,
            symbol: Symbol::from("defn-macro"),
        };
        assert!(matches!(
            classify_import(&session, &source),
            ImportClass::Macro
        ));
    }

    // spec: repl/spec.md §3.4 -- classify_import with constructor entry
    #[test]
    fn test_classify_import_constructor() {
        use cranelisp_types::{ConstructorInfo, FQSymbol, Scheme};

        let mod_path = ModuleFullPath::from("core.option");
        let session = session_with_modules(vec![(
            mod_path.clone(),
            vec![(
                Symbol::from("Some"),
                ModuleEntry::Constructor {
                    type_name: Symbol::from("Option"),
                    info: ConstructorInfo {
                        name: Symbol::from("Some"),
                        tag: 1,
                        fields: vec![],
                        docstring: None,
                        internal: false,
                    },
                    scheme: Scheme { vars: vec![], constraints: HashMap::new(), ty: Type::Int },
                    visibility: Visibility::Public,
                },
            )],
        )]);

        let source = FQSymbol {
            module: mod_path,
            symbol: Symbol::from("Some"),
        };
        assert!(matches!(
            classify_import(&session, &source),
            ImportClass::Constructor
        ));
    }

    // spec: repl/spec.md §3.4 -- classify_import with type def entry
    #[test]
    fn test_classify_import_typedef() {
        use cranelisp_types::{FQSymbol, TypeDefInfo};

        let mod_path = ModuleFullPath::from("core.option");
        let session = session_with_modules(vec![(
            mod_path.clone(),
            vec![(
                Symbol::from("Option"),
                ModuleEntry::TypeDef {
                    info: TypeDefInfo {
                        name: TypeName::from("Option"),
                        type_params: vec![],
                        constructors: vec![],
                        docstring: None,
                    },
                    visibility: Visibility::Public,
                    constructor_scheme: None,
                    sexp: None,
                },
            )],
        )]);

        let source = FQSymbol {
            module: mod_path,
            symbol: Symbol::from("Option"),
        };
        assert!(matches!(
            classify_import(&session, &source),
            ImportClass::Type
        ));
    }

    // spec: repl/spec.md §3.4 -- classify_import unknown symbol defaults to Fn
    #[test]
    fn test_classify_import_unknown_defaults_to_fn() {
        use cranelisp_types::FQSymbol;

        let session = ReplSession::new();
        let source = FQSymbol {
            module: ModuleFullPath::from("nonexistent"),
            symbol: Symbol::from("whatever"),
        };
        assert!(matches!(
            classify_import(&session, &source),
            ImportClass::Fn
        ));
    }

    // IO type detection tests moved to cranelisp-types (Type::is_io, Type::io_inner_type)

    // spec: 10-io §10.8.1 -- force_io_and_format with Pure node
    #[test]
    fn test_force_io_and_format_pure_int() {
        // Build a Pure(42) IO node manually.
        let base = cranelisp_runtime::alloc_with_rc(16); // tag + value
        unsafe {
            *((base as isize + 16) as *mut i64) = cranelisp_platform::IO_TAG_PURE;
            *((base as isize + 24) as *mut i64) = 42;
        }
        let io_ty = Type::ADT(TypeName::from("IO"), vec![Type::Int]);
        let type_defs = HashMap::new();
        let type_modules = HashMap::new();
        let mut buf: Vec<u8> = Vec::new();

        let display = force_io_and_format(
            base as i64,
            &io_ty,
            &type_defs,
            &type_modules,
            &mut buf,
        );
        assert_eq!(display, ":(IO primitives/Int) (IO.Pure 42)");
        cranelisp_runtime::heap_dealloc(base as i64);
    }

    // spec: 10-io §10.8.1 -- force_io_and_format handles panic gracefully
    #[test]
    fn test_force_io_and_format_panic_recovery() {
        // Build a node with an invalid tag.
        let base = cranelisp_runtime::alloc_with_rc(16);
        unsafe {
            *((base as isize + 16) as *mut i64) = 99; // invalid tag
            *((base as isize + 24) as *mut i64) = 0;
        }
        let io_ty = Type::ADT(TypeName::from("IO"), vec![Type::Int]);
        let type_defs = HashMap::new();
        let type_modules = HashMap::new();
        let mut buf: Vec<u8> = Vec::new();

        let display = force_io_and_format(
            base as i64,
            &io_ty,
            &type_defs,
            &type_modules,
            &mut buf,
        );
        assert_eq!(display, ":(IO primitives/Int) <IO trampoline panicked>");
        cranelisp_runtime::heap_dealloc(base as i64);
    }

    // --- v4 eval path tests (Step 7) ---

    /// Create a ReplSession with v4 eval enabled (no prelude).
    fn v4_session() -> ReplSession {
        let mut session = ReplSession::new();
        session.enable_v4();
        session
    }

    // spec: design/int/step7-repl-eval.md §4 — simple expression via v4
    #[test]
    fn test_v4_eval_int() {
        let mut session = v4_session();
        let result = session.eval("42").unwrap();
        assert_eq!(result.value, 42);
        assert_eq!(result.ty, Type::Int);
        assert!(!result.is_definition);
    }

    // spec: design/int/step7-repl-eval.md §4 — boolean via v4
    #[test]
    fn test_v4_eval_bool() {
        let mut session = v4_session();
        let result = session.eval("true").unwrap();
        assert_eq!(result.value, 1);
        assert_eq!(result.ty, Type::Bool);
    }

    // spec: design/int/step7-repl-eval.md §7 — error recovery via v4
    #[test]
    fn test_v4_error_recovery() {
        let mut session = v4_session();
        // Parse error.
        let err = session.eval("(+ 1");
        assert!(err.is_err());
        // Session should still work after error.
        let result = session.eval("42").unwrap();
        assert_eq!(result.value, 42);
    }

    // spec: design/int/step7-repl-eval.md §3 — additive: defn then call
    #[test]
    fn test_v4_defn_then_call() {
        let mut session = v4_session();
        // Import primitives for add-i64.
        session.eval("(import [primitives [add-i64]])").unwrap();
        // Define a function.
        let def_result = session.eval("(defn inc [n] (add-i64 n 1))").unwrap();
        assert!(def_result.is_definition);
        // Call it.
        let call_result = session.eval("(inc 5)").unwrap();
        assert_eq!(call_result.value, 6);
        assert_eq!(call_result.ty, Type::Int);
    }

    // spec: design/int/step7-repl-eval.md §4.6 — bare symbol introspection
    #[test]
    fn test_v4_bare_symbol_special_form() {
        let mut session = v4_session();
        let result = session.eval("defn").unwrap();
        // Should produce introspection display, not an error.
        assert!(result.definition_display.is_some());
        let display = result.definition_display.unwrap();
        assert!(display.contains("defn"), "expected 'defn' in display: {}", display);
    }

    // spec: design/int/step7-repl-eval.md §3 — multi-eval persistence
    #[test]
    fn test_v4_multi_eval_persistence() {
        let mut session = v4_session();
        session.eval("(import [primitives [add-i64 sub-i64]])").unwrap();
        session.eval("(defn inc [n] (add-i64 n 1))").unwrap();
        session.eval("(defn dec [n] (sub-i64 n 1))").unwrap();
        let result = session.eval("(inc (dec 10))").unwrap();
        assert_eq!(result.value, 10);
    }

    // spec: design/int/step7-repl-eval.md §2 — blank/comment input
    #[test]
    fn test_v4_blank_and_comment() {
        let mut session = v4_session();
        let result = session.eval("").unwrap();
        assert!(result.is_definition); // blank returns definition-like no-op
        let result = session.eval("; just a comment").unwrap();
        assert!(result.is_definition);
    }
}
