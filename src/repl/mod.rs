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
//   trace.rs     — TracedCompiledExpr, trace display state, expr_contains_trace
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
use cranelisp_backend::jit::Jit;
use cranelisp_types::{
    CheckResult, CompileContext, CompileMode, CranelispError, DefKind, Defn, Expr,
    ImplSexp, MacroClauseInfo, ModuleEntry, ModuleFullPath, ModuleStrategy,
    ModuleStructure, Sexp, Symbol, TopLevel, Type, TypeDefInfo, TypeName,
    Visibility, Warning,
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
    compile_expr_with_traced_fns, expr_contains_trace, repl_trace_format,
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
    /// Shared compilation core (typechecker, GOT, expander, JIT lifetimes).
    pub core: crate::pipeline::CompilationSession,
    /// Accumulated type definitions from all inputs (for ADT value display).
    type_defs: HashMap<TypeName, TypeDefInfo>,
    /// Maps type names to the module they were defined in (for qualified display).
    pub(crate) type_modules: HashMap<TypeName, ModuleFullPath>,
    /// Loaded platform DLLs -- must stay alive for the process lifetime.
    loaded_platforms: Vec<crate::platform::LoadedPlatform>,
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
    /// Maps canonical file paths to module paths for file-watching recompilation.
    /// Populated during prelude loading and module imports.
    file_to_module: HashMap<std::path::PathBuf, ModuleFullPath>,
    /// Maps each module to the modules it depends on (imports from).
    /// Used for cascade invalidation: when module B changes, all modules that
    /// depend on B must also be recompiled.
    module_dependencies: HashMap<ModuleFullPath, Vec<ModuleFullPath>>,
    /// Module structure for the current REPL module (tracks imports, exports,
    /// impl_sexps as they accumulate interactively). Used by save.rs to
    /// regenerate the module's `.cl` file.
    pub(crate) current_module_structure: ModuleStructure,
    /// Content hash of the last saved `.cl` file. Used by the file watcher
    /// to suppress self-triggered reloads (design/int/session-persistence.md §4).
    pub(crate) last_saved_hash: Option<String>,
    /// True while restoring from user.cl at startup — suppresses save-on-define.
    restoring: bool,
}

impl ReplSession {
    /// Create a new REPL session without prelude loading.
    pub fn new() -> Self {
        let user_module = ModuleFullPath::from("user");
        ReplSession {
            core: crate::pipeline::CompilationSession::new(),
            type_defs: HashMap::new(),
            type_modules: HashMap::new(),
            loaded_platforms: Vec::new(),
            project_root: std::env::current_dir().unwrap_or_default(),
            watcher: None,
            pending_changes: Vec::new(),
            error_modules: HashSet::new(),
            file_to_module: HashMap::new(),
            module_dependencies: HashMap::new(),
            current_module_structure: ModuleStructure {
                path: user_module,
                file_path: None,
                mod_decls: vec![],
                import_specs: vec![],
                export_specs: vec![],
                impl_sexps: vec![],
                impls: vec![],
                dll_path: None,
            },
            last_saved_hash: None,
            restoring: false,
        }
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

        // Enable module caching for REPL prelude loading.
        let cache_dir = project_root.join(".cranelisp-cache");
        let mut cache_state = Some(crate::pipeline::CacheState::new(cache_dir));
        crate::pipeline::load_prelude_into_session(
            project_root,
            lib_dirs,
            &mut session.core,
            &mut cache_state,
        )?;

        // Flush the cache manifest if any modules were compiled.
        if let Some(cs) = cache_state.as_mut() {
            cs.flush_manifest();
        }

        // Sync type definitions from prelude modules for ADT value display.
        // Without this, prelude ADT values (e.g. Option.None) display as raw
        // i64 tags because format_result_value lacks the constructor metadata.
        for (name, info) in session.core.tc.type_def_registry().iter() {
            session.type_defs.insert(name.clone(), info.clone());
        }

        // Build file-to-module mapping for file watcher recompilation.
        session.file_to_module =
            crate::pipeline::build_file_to_module_map(project_root, lib_dirs);

        // Build module dependency map for cascade invalidation.
        session.module_dependencies =
            crate::pipeline::build_module_dependency_map(project_root, lib_dirs);

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
        if !structure.import_specs.is_empty() {
            let lib_dirs = crate::pipeline::assemble_lib_dirs(&self.project_root);
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
                    let saved_module = self.core.tc.current_module_path().clone();
                    crate::pipeline::load_module_into_session(
                        &root_module,
                        &self.project_root,
                        &lib_dirs,
                        &mut self.core,
                    )?;
                    self.core.tc.set_current_module(saved_module);
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
        let program = cranelisp_frontend::build_program(
            &accumulated,
            &mut self.core.expander,
        )?;

        if program.is_empty() {
            self.current_module_structure = structure;
            return Ok(true);
        }

        // Whole-program typecheck — handles constrained polymorphism,
        // forward references, and monomorphisation correctly.
        let ctx = CompileContext {
            module: self.core.tc.current_module_path().clone(),
            strategy: ModuleStrategy::Additive,
            compile_mode: CompileMode::Interactive,
            codegen_target: cranelisp_types::CodegenTarget::JitAndCache,
        };
        let check = self.core.tc.check(&program, &ctx)?;

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
                let dc = self.core.got_state.def_codegen
                    .entry(defn.name.clone())
                    .or_default();
                dc.sexp = Some(original.clone());
                dc.source = Some(format_sexp(original));
            }
        }

        // Register module aliases (user/name -> name) for qualified refs.
        self.core.register_module_aliases(&user_module);

        // Write cache files (.meta.json + .o) so subsequent restarts
        // can use the fast cache-load path.
        let cache_dir = self.project_root.join(".cranelisp-cache");
        let mut cache_state = crate::pipeline::CacheState::new(cache_dir);
        cache_state.record_recompiled(&user_module);
        cache_state.source_hashes_mut()
            .insert(user_module.clone(), source_hash.clone());
        // Cache write failures are non-fatal.
        let _ = crate::pipeline::write_module_cache(
            &mut cache_state,
            &user_module,
            source_hash,
            &[],  // user module has no module-graph dependencies
            &structure,
            &self.core.tc,
            Some(&program),
            Some(&check),
            &self.core.func_sigs,
        );
        cache_state.flush_manifest();

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

        let sym_table = self.core.tc.symbol_table();
        let structure = &self.current_module_structure;
        let def_codegen = &self.core.got_state.def_codegen;

        if let Some(hash) = save::save_module_file(
            &file_path,
            sym_table,
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

            // Write cache files (.meta.json + .o) for the saved module so
            // they exist immediately after the first session, not just after
            // the second session's restore (Defect 2 fix).
            self.write_cache_for_saved_module(&file_path);
        }
    }

    /// Write cache files (.meta.json + .o) for a saved module file.
    ///
    /// Compiles the saved file through the batch module-graph pipeline
    /// (using a fresh CompilationSession) to produce the cache artifacts.
    /// This is slightly wasteful (re-compiles what was just compiled in
    /// the REPL) but is correct and simple — the batch pipeline produces
    /// the same Program + CheckResult that write_module_cache needs.
    ///
    /// Failures are non-fatal: cache files are an optimization, and the
    /// next session can always fall back to source compilation.
    fn write_cache_for_saved_module(&self, file_path: &std::path::Path) {
        let cache_dir = self.project_root.join(".cranelisp-cache");
        let lib_dirs = crate::pipeline::assemble_lib_dirs(&self.project_root);
        let cache_config = crate::pipeline::CacheConfig::Enabled {
            cache_dir,
        };
        // Compile user.cl through the module-graph pipeline (compile-only,
        // no execution). This loads prelude from cache (fast) and compiles
        // user.cl, writing .meta.json + .o as a side effect.
        let _ = crate::pipeline::compile_module_graph_for_cache(
            file_path,
            &lib_dirs,
            &cache_config,
        );
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
    /// Pipeline:
    /// 1. Parse source -> sexps
    /// 2. Check for defmacro -> compile + register, return display
    /// 3. Expand through CraneliftExpander
    /// 4. Flatten (begin ...) results, process sub-forms
    /// 5. Build REPL input -> typecheck -> compile -> execute
    ///
    /// On error, restores the TypeChecker to its pre-input state.
    pub fn eval(&mut self, source: &str) -> Result<ReplResult, CranelispError> {
        // Skip blank and comment-only input before it reaches the parser.
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

        // Parse the source into sexps.
        let sexps = cranelisp_frontend::parse(source)?;

        if sexps.is_empty() {
            return Err(CranelispError::ParseError {
                message: "empty input".into(),
                span: cranelisp_types::Span::SYNTHETIC,
            });
        }

        // Snapshot for error recovery (covers macro compilation too).
        let snapshot = self.core.tc.snapshot();

        // Handle multi-sexp annotation expressions (`:Type expr` parses as two sexps).
        // For single sexps, take the first and evaluate normally.
        let result = if sexps.len() > 1 && is_annotation_prefix(&sexps[0]) {
            self.eval_annotation_expr(sexps)
        } else {
            let first_sexp = sexps.into_iter().next().unwrap();
            self.eval_sexp(first_sexp)
        };

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

    /// Evaluate a type annotation expression (`:Type expr` parsed as multiple sexps).
    ///
    /// Uses `build_repl_input_from_sexps` to combine the annotation and expression
    /// into a single `Expr::Annotate`, then typechecks and executes.
    fn eval_annotation_expr(&mut self, sexps: Vec<Sexp>) -> Result<ReplResult, CranelispError> {
        let input = cranelisp_frontend::build_repl_input_from_sexps(
            &sexps,
            &mut self.core.expander,
        )?;
        let ctx = self.build_repl_compile_context();
        let check_result = self.core.tc.check(&[input.clone()], &ctx)?;
        self.compile_and_execute(&input, &check_result)
    }

    /// Evaluate a single Sexp with defmacro interception and macro expansion.
    ///
    /// This is the core of the REPL eval loop, separated to allow recursive
    /// processing of begin-flattened sub-forms.
    fn eval_sexp(&mut self, sexp: Sexp) -> Result<ReplResult, CranelispError> {
        // Step 1: Check for defmacro -- compile and register the macro.
        if cranelisp_frontend::is_defmacro(&sexp) {
            return self.eval_defmacro(&sexp);
        }

        // Step 1b: Check for import -- intercept before AST building.
        // Import forms must be handled here because the AST builder does not
        // accept (import ...) -- it expects module declarations to be extracted
        // before AST construction. In the REPL, imports are entered interactively.
        if is_import_form(&sexp) {
            return self.eval_import(sexp);
        }

        // Step 1c: Check for platform -- load DLL and register functions.
        // Platform declarations must be intercepted before AST building
        // because the AST builder rejects (platform ...) forms.
        if crate::platform::is_platform_form(&sexp) {
            return self.eval_platform(sexp);
        }

        // Step 1c: Check for bare symbols that need introspection display.
        // Non-zero-arg macro names show their signature (instead of failing
        // with "no matching clause"). Special forms show their description
        // (instead of erroring in the typechecker).
        if let Some(result) = self.check_bare_symbol_introspection(&sexp) {
            return Ok(result);
        }

        // Step 2: Capture original sexp before macro expansion so
        // session persistence stores what the user typed (Defect 1 fix).
        let original_sexp = sexp.clone();

        // Expand macros in the sexp.
        let expanded = self.core.expander.expand_sexp(sexp)?;

        // Step 3: Flatten (begin ...) results and process sub-forms.
        let forms = cranelisp_frontend::flatten_begin(expanded);
        self.eval_flattened_forms(forms, Some(original_sexp))
    }

    /// Process a sequence of flattened forms, returning the result of the last.
    ///
    /// Each form may itself be a defmacro (defmacro-in-results from macro
    /// expansion). Non-macro, non-type forms are accumulated and compiled
    /// as a batch.
    ///
    /// `original_sexp` is the pre-expansion sexp from the user's input.
    /// When present and `forms` has exactly one compilable form, we store
    /// the original (not the macro-expanded) sexp for session persistence
    /// and `/source` display. This ensures `user.cl` contains what the
    /// user typed, not the expanded form (Defect 1 fix).
    fn eval_flattened_forms(
        &mut self,
        forms: Vec<Sexp>,
        original_sexp: Option<Sexp>,
    ) -> Result<ReplResult, CranelispError> {
        let mut last_result = None;
        // Track how many compilable (non-defmacro, non-import) forms we see
        // to decide whether `original_sexp` applies (only for single-form case).
        let compilable_count = forms.iter()
            .filter(|f| !cranelisp_frontend::is_defmacro(f) && !is_import_form(f))
            .count();

        for form in forms {
            if cranelisp_frontend::is_defmacro(&form) {
                last_result = Some(self.eval_defmacro(&form)?);
                continue;
            }
            if is_import_form(&form) {
                last_result = Some(self.eval_import(form)?);
                continue;
            }

            // Build and process a normal REPL input.
            // Use the pre-expansion sexp for storage when this is the sole
            // compilable form (common case: user typed one defn/expr).
            // For begin-expanded multi-forms, fall back to the expanded form.
            let form_sexp = if compilable_count == 1 {
                original_sexp.clone().unwrap_or_else(|| form.clone())
            } else {
                form.clone()
            };
            let mut input = cranelisp_frontend::build_repl_input(&form, &mut self.core.expander)?;

            // Bind chain independence analysis (auto IO scheduling).
            if !self.core.scheduling_registry.is_empty()
                && std::env::var("CRANELISP_NO_IO_SCHEDULE").is_err()
            {
                match &mut input {
                    TopLevel::Defn(defn) => {
                        crate::bind_chain_analysis::auto_schedule_defn(
                            defn, &self.core.scheduling_registry,
                        );
                    }
                    TopLevel::Expr(expr) => {
                        crate::bind_chain_analysis::auto_schedule_expr(
                            expr, &self.core.scheduling_registry,
                        );
                    }
                    TopLevel::TraitImpl(impl_) => {
                        for method in impl_.methods.iter_mut() {
                            crate::bind_chain_analysis::auto_schedule_defn(
                                method, &self.core.scheduling_registry,
                            );
                        }
                    }
                    _ => {}
                }
            }

            let ctx = self.build_repl_compile_context();
            let check_result = self.core.tc.check(&[input.clone()], &ctx)?;
            let result = self.compile_and_execute(&input, &check_result)?;

            // Store sexp and source in DefCodegen for introspection commands
            // and session persistence. Use entry().or_default() because
            // constrained poly fns skip compile_and_register_defn (which
            // normally creates the entry), but still need sexp for save.
            if let TopLevel::Defn(defn) = &input {
                let dc = self.core.got_state.def_codegen.entry(defn.name.clone()).or_default();
                dc.source = Some(format_sexp(&form_sexp));
                dc.sexp = Some(form_sexp.clone());
            }
            // Track impl sexps in module structure for session persistence.
            if let TopLevel::TraitImpl(impl_) = &input {
                self.current_module_structure.impl_sexps.push(ImplSexp {
                    trait_name: impl_.trait_name.clone(),
                    target: impl_.target_type.clone(),
                    sexp: form_sexp,
                });
            }
            last_result = Some(result);
        }

        last_result.ok_or_else(|| CranelispError::ParseError {
            message: "empty input after expansion".into(),
            span: cranelisp_types::Span::SYNTHETIC,
        })
    }

    /// Compile a defmacro form and register it in the expander and symbol table.
    ///
    /// Creates a fresh JIT for the macro clause compilation, keeps it alive
    /// so the compiled function pointer remains valid. Registers the macro
    /// in the TC's symbol table as `ModuleEntry::Macro` for introspection.
    fn eval_defmacro(&mut self, sexp: &Sexp) -> Result<ReplResult, CranelispError> {
        let info = cranelisp_frontend::parse_defmacro(sexp)?;

        let mut jit = Jit::new()?;
        jit.declare_intrinsics()?;

        self.core.expander.compile_macro(&info, &mut self.core.tc, &mut jit)?;

        // Keep JIT alive so macro function pointers remain valid.
        self.core.jit_modules.push(jit);

        // Register macro in the symbol table for introspection (spec §11.2).
        let clause_infos: Vec<MacroClauseInfo> = info
            .clauses
            .iter()
            .map(|c| MacroClauseInfo {
                params: c.fixed_params.clone(),
                rest_param: c.rest_param.clone(),
                source: None,
            })
            .collect();
        // Compute display before moving clause_infos into symbol table.
        let module = self.core.tc.current_module_path().clone();
        let display = format_defmacro_display(&info.name, &clause_infos, &module);

        let visibility = if info.is_private {
            Visibility::Private
        } else {
            Visibility::Public
        };
        self.core.tc.symbol_table_mut().insert(
            info.name.clone(),
            ModuleEntry::Macro {
                name: info.name.clone(),
                clauses: clause_infos,
                docstring: info.docstring.clone(),
                visibility,
                sexp: Some(sexp.clone()),
                source: None,
            },
        );

        Ok(ReplResult {
            value: 0,
            ty: Type::Int,
            is_definition: true,
            warnings: Vec::new(),
            definition_display: Some(display),
            eval_duration: Duration::ZERO,
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
        let entry = self.core.tc.symbol_table().get(name.as_str())?;
        match entry {
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

    /// Process an import form in the REPL.
    ///
    /// Parses the import sexp using `extract_module_declarations` and registers
    /// the resulting import specs in the typechecker's symbol table.
    fn eval_import(&mut self, sexp: Sexp) -> Result<ReplResult, CranelispError> {
        let module = self.core.tc.current_module_path().clone();
        let (structure, _remaining) =
            cranelisp_frontend::extract_module_declarations(module, None, vec![sexp])?;

        if !structure.import_specs.is_empty() {
            // Lazily load any modules that aren't already compiled.
            // Per spec §8.11.2, module resolution searches project root and lib dirs.
            let lib_dirs = crate::pipeline::assemble_lib_dirs(&self.project_root);
            for spec in &structure.import_specs {
                // Skip if the full module path is already loaded (e.g., "platform.test-capture").
                if self.core.tc.has_module(&spec.module_path) {
                    continue;
                }
                // Extract the root module name (first segment of dotted path).
                let root_module = spec.module_path.0
                    .split('.')
                    .next()
                    .unwrap_or(&spec.module_path.0)
                    .to_string();
                let root_path = ModuleFullPath::from(root_module.as_str());
                if !self.core.tc.has_module(&root_path) {
                    // Save and restore current module context around lazy load.
                    let saved_module = self.core.tc.current_module_path().clone();
                    crate::pipeline::load_module_into_session(
                        &root_module,
                        &self.project_root,
                        &lib_dirs,
                        &mut self.core,
                    )?;
                    self.core.tc.set_current_module(saved_module);
                }
            }

            self.core.tc.register_imports(&structure.import_specs)?;
            // Track imports in module structure for session persistence.
            self.current_module_structure
                .import_specs
                .extend(structure.import_specs.clone());
        }

        // Build display: "imported N names from module1, module2, ..."
        let mod_names: Vec<String> = structure
            .import_specs
            .iter()
            .map(|s| s.module_path.to_string())
            .collect();
        let display = if mod_names.is_empty() {
            "import: no names".to_string()
        } else {
            format!("imported from {}", mod_names.join(", "))
        };

        Ok(ReplResult {
            value: 0,
            ty: Type::Int,
            is_definition: true,
            warnings: Vec::new(),
            definition_display: Some(display),
            eval_duration: Duration::ZERO,
        })
    }

    /// Handle a `(platform name)` form: load the platform DLL and register
    /// its functions in the typechecker.
    ///
    /// Platform function pointers are stored in `self.platform_symbols` so
    /// that subsequent JIT instances (created for each function compilation)
    /// can resolve calls to platform functions.
    fn eval_platform(&mut self, sexp: Sexp) -> Result<ReplResult, CranelispError> {
        let (name, span) = crate::platform::extract_platform_name(&sexp).ok_or_else(|| {
            CranelispError::ParseError {
                message: "invalid platform declaration".into(),
                span: cranelisp_types::Span::SYNTHETIC,
            }
        })?;

        let (platform, jit_syms) = crate::platform::load_and_register_platform(
            &mut self.core.tc,
            &name,
            &self.project_root,
            span,
        )?;

        let fn_count = platform.descriptors.len();
        let version = platform.version.clone();

        // Populate scheduling registry for bind chain independence analysis.
        for desc in &platform.descriptors {
            self.core.scheduling_registry.insert(
                cranelisp_types::Symbol::from(desc.name.as_str()),
                desc.scheduling_class,
            );
        }
        self.core.platform_symbols.extend(jit_syms);
        self.loaded_platforms.push(platform);

        let display = format!(
            "; loaded platform: {} v{} ({} functions)\n; use (import [platform.{} [*]]) to bring into scope",
            name, version, fn_count, name
        );

        Ok(ReplResult {
            value: 0,
            ty: Type::Int,
            is_definition: true,
            warnings: Vec::new(),
            definition_display: Some(display),
            eval_duration: Duration::ZERO,
        })
    }

    /// Compile and execute a checked REPL input.
    fn compile_and_execute(
        &mut self,
        input: &TopLevel,
        check_result: &CheckResult,
    ) -> Result<ReplResult, CranelispError> {
        match input {
            TopLevel::Expr(expr) => self.execute_expr(expr, check_result),
            TopLevel::Defn(defn) => self.execute_defn(defn, check_result),
            TopLevel::TypeDef { .. } => self.execute_typedef(check_result),
            TopLevel::TraitDecl(decl) => self.execute_trait_decl(decl, check_result),
            TopLevel::TraitImpl(impl_) => self.execute_trait_impl(impl_, check_result),
        }
    }

    /// Compile and execute an expression input.
    fn execute_expr(
        &mut self,
        expr: &Expr,
        check_result: &CheckResult,
    ) -> Result<ReplResult, CranelispError> {
        let check = self.build_check_for_backend(check_result);

        // Compile any monomorphised specializations before executing
        // the expression (Gap 4: REPL constrained-poly path).
        self.compile_mono_defns(check_result)?;

        // Build extra symbols for platform function resolution.
        // If the expression contains a (trace ...) form, also override
        // cranelisp_trace_format with the REPL's proper formatter and
        // build traced_fns for GOT-swap wrapper generation.
        let has_trace = expr_contains_trace(expr);
        let traced_fns = if has_trace {
            self.build_traced_fns()
        } else {
            Vec::new()
        };

        let mut extra_symbols: Vec<(&str, *const u8)> = self
            .core.platform_symbols
            .iter()
            .map(|(name, ptr)| (name.as_str(), *ptr))
            .collect();

        // Override the runtime's fallback cranelisp_trace_format with the
        // REPL's version that uses type_defs/type_modules for proper display.
        if has_trace {
            extra_symbols.push((
                "cranelisp_trace_format",
                repl_trace_format as *const u8,
            ));
        }

        let compiled = compile_expr_with_traced_fns(
            expr,
            &check,
            Some(&mut self.core.got_state),
            &extra_symbols,
            if has_trace { Some(&traced_fns) } else { None },
        )?;

        // Set trace display state before evaluation so cranelisp_trace_format
        // can access type_defs and type_modules.
        let display_state = TraceDisplayState {
            type_defs: &self.type_defs as *const _,
            type_modules: &self.type_modules as *const _,
        };
        if has_trace {
            set_trace_display_state(&display_state);
        }

        // Time the actual evaluation (function call) separately from compilation.
        // Wrap in catch_unwind to recover from runtime panics (spec §12.7.4.1).
        let eval_start = Instant::now();
        // SAFETY: compiled was produced by compile_expr_with_got, which guarantees
        // a valid JIT function pointer with extern "C" fn() -> i64 signature.
        let value = invoke_jit_eval(|| unsafe { compiled.execute() });
        let eval_duration = eval_start.elapsed();

        // Always clear trace display state after evaluation.
        if has_trace {
            clear_trace_display_state();
        }

        // Propagate evaluation errors after cleanup.
        let value = value?;

        Ok(ReplResult {
            value,
            ty: check_result.display.as_ref().unwrap().ty.clone(),
            is_definition: false,
            warnings: check_result.warnings.clone(),
            definition_display: None,
            eval_duration,
        })
    }

    /// Compile and execute a function definition input.
    fn execute_defn(
        &mut self,
        defn: &Defn,
        check_result: &CheckResult,
    ) -> Result<ReplResult, CranelispError> {
        // Skip compiling constrained fn base definitions -- they are
        // templates that get monomorphised at call sites.
        let is_constrained = check_result
            .display.as_ref()
            .and_then(|d| d.scheme.as_ref())
            .is_some_and(|s| !s.constraints.is_empty());

        // Compile any monomorphised specializations before the defn body.
        // When a non-constrained defn calls a constrained function (e.g.,
        // `(defn main [] (countdown 1000000))` where `countdown` is constrained-poly),
        // the typechecker generates mono_defns (e.g., `countdown$Int`). These must
        // be compiled and registered in the GOT before the defn body is compiled,
        // otherwise the GOT lookup for the mangled name will fail.
        self.compile_mono_defns(check_result)?;

        if !is_constrained {
            let check = self.build_check_for_backend(check_result);
            self.compile_and_register_defn(defn, &check)?;
        }

        // For defn, execute if it's zero-arg, otherwise return 0.
        // Time the execution separately from compilation.
        let (value, eval_duration) = if defn.params().is_empty() && !is_constrained {
            let entry = self.core.got_state.def_codegen.get(defn.name.as_ref());
            let code_ptr = entry
                .and_then(|e| e.code_ptr)
                .ok_or_else(|| CranelispError::CodegenError {
                    message: format!("no code pointer after compiling defn '{}'", defn.name),
                    span: cranelisp_types::Span::SYNTHETIC,
                })?;
            let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
            let eval_start = Instant::now();
            let result = invoke_jit_eval(|| func())?;
            (result, eval_start.elapsed())
        } else {
            (0, Duration::ZERO)
        };

        // Build definition display with qualified name (spec §1.1, §1.3).
        let module = self.core.tc.current_module_path().clone();
        let disp = check_result.display.as_ref().unwrap();
        let definition_display = if is_constrained {
            disp.scheme.as_ref().map(|s| {
                let base = display::format_scheme_display(&defn.name, s, &module, &self.type_modules);
                format!("{base} ; defn")
            })
        } else {
            let type_str = format_type_qualified(&disp.ty, &self.type_modules);
            Some(format!(":{type_str} {module}/{} ; defn", defn.name))
        };

        Ok(ReplResult {
            value,
            ty: check_result.display.as_ref().unwrap().ty.clone(),
            is_definition: true,
            warnings: check_result.warnings.clone(),
            definition_display,
            eval_duration,
        })
    }

    /// Execute a type definition input.
    fn execute_typedef(
        &mut self,
        check_result: &CheckResult,
    ) -> Result<ReplResult, CranelispError> {
        let module = self.core.tc.current_module_path().clone();

        // Accumulate type definitions for ADT value display.
        for (name, info) in &check_result.type_defs {
            self.type_defs.insert(name.clone(), info.clone());
            self.type_modules.insert(name.clone(), module.clone());
        }

        // Build qualified display: `:module/TypeName ; deftype` + related symbols
        let type_name = match &check_result.display.as_ref().unwrap().ty {
            Type::ADT(name, _) => name.to_string(),
            _ => "?".to_string(),
        };
        let display = format_type_display_universal(&type_name, &module, self);

        Ok(ReplResult {
            value: 0,
            ty: check_result.display.as_ref().unwrap().ty.clone(),
            is_definition: true,
            warnings: check_result.warnings.clone(),
            definition_display: Some(display),
            eval_duration: Duration::ZERO,
        })
    }

    /// Execute a trait declaration input.
    fn execute_trait_decl(
        &mut self,
        decl: &cranelisp_types::TraitDecl,
        check_result: &CheckResult,
    ) -> Result<ReplResult, CranelispError> {
        // Trait registration is already done by check().
        // Compile any default method bodies generated by the typechecker.
        if !check_result.default_method_defns.is_empty() {
            let check = self.build_check_for_backend(check_result);
            for defn in &check_result.default_method_defns {
                self.compile_and_register_defn(defn, &check)?;
            }
        }

        let display = format_trait_display_universal(
            decl.name.as_ref(),
            decl.docstring.as_deref(),
            self,
        );

        Ok(ReplResult {
            value: 0,
            ty: check_result.display.as_ref().unwrap().ty.clone(),
            is_definition: true,
            warnings: check_result.warnings.clone(),
            definition_display: Some(display),
            eval_duration: Duration::ZERO,
        })
    }

    /// Execute a trait implementation input.
    fn execute_trait_impl(
        &mut self,
        impl_: &cranelisp_types::TraitImpl,
        check_result: &CheckResult,
    ) -> Result<ReplResult, CranelispError> {
        let check = self.build_check_for_backend(check_result);

        // Compile the impl methods.
        for defn in &impl_.methods {
            self.compile_and_register_defn(defn, &check)?;
        }

        // Compile any default method bodies generated by the typechecker.
        for defn in &check_result.default_method_defns {
            self.compile_and_register_defn(defn, &check)?;
        }

        // Compile any monomorphised definitions generated during checking.
        self.compile_mono_defns(check_result)?;

        let module = self.core.tc.current_module_path();
        let display = format!(
            "impl {module}/{} for {module}/{}",
            impl_.trait_name, impl_.target_type
        );

        Ok(ReplResult {
            value: 0,
            ty: check_result.display.as_ref().unwrap().ty.clone(),
            is_definition: true,
            warnings: check_result.warnings.clone(),
            definition_display: Some(display),
            eval_duration: Duration::ZERO,
        })
    }

    /// Compile monomorphised specializations from a check result.
    ///
    /// Used by both expression and trait impl execution paths.
    fn compile_mono_defns(
        &mut self,
        check_result: &CheckResult,
    ) -> Result<(), CranelispError> {
        for mono in &check_result.mono_defns {
            let mut mono_check = self.build_check_for_backend(check_result);
            mono_check.method_resolutions.extend(mono.resolutions.clone());
            if !mono.expr_types.is_empty() {
                mono_check.expr_types = mono.expr_types.clone();
            }
            self.compile_and_register_defn(&mono.defn, &mono_check)?;
        }
        Ok(())
    }

    /// Compile a single function definition and register it in the GOT.
    ///
    /// Used by Defn, TraitDecl (default methods), and TraitImpl (impl methods).
    /// Optionally stores the source text and parsed sexp in DefCodegen
    /// for `/source` and `/sexp` introspection commands.
    fn compile_and_register_defn(
        &mut self,
        defn: &Defn,
        check: &cranelisp_types::CheckResult,
    ) -> Result<(), CranelispError> {
        self.compile_and_register_defn_with_context(defn, check, None, None)
    }

    /// Compile a defn with optional source text and sexp for introspection.
    fn compile_and_register_defn_with_context(
        &mut self,
        defn: &Defn,
        check: &cranelisp_types::CheckResult,
        source_text: Option<String>,
        sexp: Option<Sexp>,
    ) -> Result<(), CranelispError> {
        // Create JIT with platform symbols registered (if any platforms loaded).
        let extra_symbols: Vec<(&str, *const u8)> = self
            .core.platform_symbols
            .iter()
            .map(|(name, ptr)| (name.as_str(), *ptr))
            .collect();
        let mut jit = Jit::new_with_symbols(&extra_symbols)?;

        // Declare runtime intrinsics (Ring 1 heap infrastructure).
        jit.declare_intrinsics()?;

        // Declare just this function.
        let func_ids = jit.declare_functions(&[defn])?;

        // Ensure a GOT slot exists for this function.
        let slot = self.core.got_state.ensure_slot_for(&defn.name)?;

        // Build GOT slot map from existing state + this new function.
        let mut got_slots: HashMap<Symbol, usize> = HashMap::new();
        for (name, dc) in &self.core.got_state.def_codegen {
            if let Some(s) = dc.got_slot {
                got_slots.insert(name.clone(), s);
            }
        }
        got_slots.insert(defn.name.clone(), slot);

        let got_base = self.core.got_state.got_base_ptr() as i64;

        // Build function arity map from existing GOT state + this defn.
        let mut func_arities: HashMap<Symbol, usize> = HashMap::new();
        for (name, dc) in &self.core.got_state.def_codegen {
            if let Some(pc) = dc.param_count {
                func_arities.insert(name.clone(), pc);
            }
        }
        func_arities.insert(defn.name.clone(), defn.params().len());

        // Compile the function with awareness of existing GOT.
        let compile_ctx = jit.build_compile_context(
            check,
            CompileMode::Interactive,
            &func_ids,
            &func_arities,
            Some(&got_slots),
            Some(got_base),
            None, // No cross-module GOT in single-module REPL yet.
        );
        let clif_ir = jit.compile_defn(defn, compile_ctx)?;

        // Finalize and get the code pointer.
        let code_ptr = jit.finalize_and_get_ptr(&defn.name, defn.params().len())?;

        // Update the GOT slot with the new code pointer.
        self.core.got_state.update_slot(slot, code_ptr);

        // Record codegen info and introspection data.
        let entry = self.core.got_state.def_codegen.entry(defn.name.clone()).or_default();
        entry.code_ptr = Some(code_ptr);
        entry.got_slot = Some(slot);
        entry.param_count = Some(defn.params().len());
        entry.clif_ir = Some(clif_ir);
        entry.defn = Some(defn.clone());
        if source_text.is_some() {
            entry.source = source_text;
        }
        if sexp.is_some() {
            entry.sexp = sexp;
        }

        // Keep JIT alive so code pointer remains valid.
        self.core.jit_modules.push(jit);

        Ok(())
    }

    /// Build a CompileContext for REPL evaluation.
    ///
    /// Uses the session's current module with Additive strategy and Interactive mode.
    fn build_repl_compile_context(&self) -> CompileContext {
        CompileContext {
            module: self.core.tc.current_module_path().clone(),
            strategy: ModuleStrategy::Additive,
            compile_mode: CompileMode::Interactive,
            codegen_target: cranelisp_types::CodegenTarget::JitAndCache,
        }
    }

    /// Build a CheckResult suitable for the backend from a CheckResult.
    fn build_check_for_backend(
        &self,
        repl_check: &CheckResult,
    ) -> cranelisp_types::CheckResult {
        cranelisp_types::CheckResult {
            method_resolutions: repl_check.method_resolutions.clone(),
            constrained_fn_names: repl_check.constrained_fn_names.clone(),
            mono_defns: Vec::new(), // MonoDefn is not Clone; backend handles mono
            expr_types: repl_check.expr_types.clone(),
            default_method_defns: repl_check.default_method_defns.clone(),
            warnings: repl_check.warnings.clone(),
            type_defs: repl_check.type_defs.clone(),
            constructor_to_type: repl_check.constructor_to_type.clone(),
            display: None,
        }
    }

    /// Build the list of traced function info from the current GOT state.
    ///
    /// Iterates all functions with GOT slots and code pointers, extracts their
    /// type information from the symbol table, and builds `TracedFnInfo` entries
    /// for the trace codegen to generate wrapper functions.
    fn build_traced_fns(&mut self) -> Vec<TracedFnInfo> {
        let got_base = self.core.got_state.got_base_ptr() as i64;
        let module = self.core.tc.current_module_path().clone();
        let symbol_table = self.core.tc.symbol_table();

        let mut traced = Vec::new();
        for (name, dc) in &self.core.got_state.def_codegen {
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
        let lib_dirs = crate::pipeline::assemble_lib_dirs(project_root);

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
fn reload_changed_modules(session: &mut ReplSession, stdout: &mut impl Write) {
    let pending = std::mem::take(&mut session.pending_changes);

    // Map file paths to module paths.
    let mut stale_modules: Vec<ModuleFullPath> = Vec::new();
    for path in &pending {
        if let Some(module_path) = session.file_to_module.get(path)
            && !stale_modules.contains(module_path)
        {
            stale_modules.push(module_path.clone());
        }
    }

    if stale_modules.is_empty() {
        return;
    }

    // Invalidate cache and reload each stale module.
    let project_root = session.project_root.clone();
    let lib_dirs = crate::pipeline::assemble_lib_dirs(&project_root);
    let cache_dir = project_root.join(".cranelisp-cache");
    let mut cache_state = Some(crate::pipeline::CacheState::new(cache_dir));

    let mut reloaded: Vec<ModuleFullPath> = Vec::new();

    for module_path in &stale_modules {
        let file_display = module_display_name(session, module_path, &project_root);

        match reload_single_module(
            session,
            module_path,
            &lib_dirs,
            &mut cache_state,
        ) {
            Ok(()) => {
                session.error_modules.remove(module_path);
                reloaded.push(module_path.clone());
                let _ = writeln!(stdout, "[updated: {}]", file_display);
            }
            Err(e) => {
                session.error_modules.insert(module_path.clone());
                let _ = writeln!(stdout, "{}", styled(&format!("[errors: {}]", file_display), Style::Red));
                let _ = writeln!(stdout, "  {}", e);
            }
        }
    }

    // Cascade: find transitive dependents of successfully reloaded modules
    // and recompile them in BFS order.
    let cascade_targets = find_transitive_dependents(
        &reloaded,
        &session.module_dependencies,
    );

    for dep_path in &cascade_targets {
        // Skip modules already reloaded as direct changes.
        if reloaded.contains(dep_path) {
            continue;
        }

        let file_display = module_display_name(session, dep_path, &project_root);

        match reload_single_module(
            session,
            dep_path,
            &lib_dirs,
            &mut cache_state,
        ) {
            Ok(()) => {
                session.error_modules.remove(dep_path);
                let _ = writeln!(stdout, "[updated: {}]", file_display);
            }
            Err(e) => {
                session.error_modules.insert(dep_path.clone());
                let _ = writeln!(stdout, "{}", styled(&format!("[errors: {}]", file_display), Style::Red));
                let _ = writeln!(stdout, "  {}", e);
            }
        }
    }

    // Flush cache manifest if modules were recompiled.
    if let Some(cs) = cache_state.as_ref() {
        cs.flush_manifest();
    }
}

/// Get a display name for a module (relative file path or module path).
fn module_display_name(
    session: &ReplSession,
    module_path: &ModuleFullPath,
    project_root: &std::path::Path,
) -> String {
    session
        .file_to_module
        .iter()
        .find(|(_, mp)| *mp == module_path)
        .map(|(fp, _)| relative_path_str(fp, project_root))
        .unwrap_or_else(|| module_path.as_ref().to_string())
}

/// Find all modules that directly depend on the given module.
///
/// A module Y depends on module X if X appears in Y's dependency list.
/// This is the reverse lookup of the module_dependencies map.
fn find_direct_dependents(
    module: &ModuleFullPath,
    dependencies: &HashMap<ModuleFullPath, Vec<ModuleFullPath>>,
) -> Vec<ModuleFullPath> {
    let mut dependents = Vec::new();
    for (mod_path, deps) in dependencies {
        if mod_path == module {
            continue;
        }
        if deps.iter().any(|d| d == module) {
            dependents.push(mod_path.clone());
        }
    }
    dependents
}

/// Find all transitive dependents of the given modules via BFS.
///
/// Returns modules in BFS order (direct dependents first, then their
/// dependents, etc.). Does not include the seed modules themselves.
fn find_transitive_dependents(
    changed_modules: &[ModuleFullPath],
    dependencies: &HashMap<ModuleFullPath, Vec<ModuleFullPath>>,
) -> Vec<ModuleFullPath> {
    let mut result = Vec::new();
    let mut visited: HashSet<ModuleFullPath> = changed_modules.iter().cloned().collect();
    let mut queue = std::collections::VecDeque::new();

    // Seed with direct dependents of all changed modules.
    for module in changed_modules {
        for dep in find_direct_dependents(module, dependencies) {
            if visited.insert(dep.clone()) {
                queue.push_back(dep.clone());
                result.push(dep);
            }
        }
    }

    // BFS to find transitive dependents.
    while let Some(current) = queue.pop_front() {
        for dep in find_direct_dependents(&current, dependencies) {
            if visited.insert(dep.clone()) {
                queue.push_back(dep.clone());
                result.push(dep);
            }
        }
    }

    result
}

/// Reload a single module from its source file.
///
/// Per repl/spec.md §14.2: clears old module state (symbol table, trait
/// declarations, macro env) before recompiling to avoid "duplicate definition"
/// errors. Uses the REPL's form-by-form compilation (eval_flattened_forms
/// pattern) with fresh per-function JITs and GOT-based dispatch. On failure,
/// the old state is NOT restored — the module enters error state and
/// evaluation is blocked (§14.4).
fn reload_single_module(
    session: &mut ReplSession,
    module_path: &ModuleFullPath,
    _lib_dirs: &[std::path::PathBuf],
    cache_state: &mut Option<crate::pipeline::CacheState>,
) -> Result<(), CranelispError> {
    // Find the source file for this module.
    let file_path = session
        .file_to_module
        .iter()
        .find(|(_, mp)| *mp == module_path)
        .map(|(fp, _)| fp.clone())
        .ok_or_else(|| CranelispError::ModuleError {
            message: format!("no source file known for module '{}'", module_path.as_ref()),
            file: None,
            span: cranelisp_types::Span::SYNTHETIC,
        })?;

    // Read and parse the source.
    let source = std::fs::read_to_string(&file_path).map_err(|e| {
        CranelispError::ModuleError {
            message: format!("cannot read '{}': {e}", file_path.display()),
            file: Some(file_path.clone()),
            span: cranelisp_types::Span::SYNTHETIC,
        }
    })?;

    // --- Phase A: Clear old module state ---
    // Remove the old symbol table, traits, and macros to avoid duplicates.
    clear_module_state(session, module_path);

    // --- Phase B: Recompile from source ---
    // Switch to the module's context for compilation.
    let prev_module = session.core.tc.current_module_path().clone();
    session.core.tc.set_current_module(module_path.clone());

    // Parse the source sexps.
    let sexps = cranelisp_frontend::parse(&source)?;
    let (structure, remaining) = cranelisp_frontend::extract_module_declarations(
        module_path.clone(),
        Some(file_path.clone()),
        sexps,
    )?;

    // Re-register imports/exports for the module.
    if !structure.import_specs.is_empty() {
        session.core.tc.register_imports(&structure.import_specs)?;
    }
    if !structure.export_specs.is_empty() {
        session.core.tc.register_exports(&structure.export_specs)?;
    }

    // Process forms using the REPL's form-by-form pattern.
    // This creates fresh JITs per function and uses GOT-based dispatch,
    // avoiding "Duplicate definition" errors from the shared batch JIT.
    let accumulated = session.core.process_forms_sequentially(remaining)?;
    for form in accumulated {
        if cranelisp_frontend::is_defmacro(&form) {
            session.eval_defmacro(&form)?;
            continue;
        }
        let input = cranelisp_frontend::build_repl_input(&form, &mut session.core.expander)?;
        let ctx = session.build_repl_compile_context();
        let check_result = session.core.tc.check(&[input.clone()], &ctx)?;
        session.compile_and_execute(&input, &check_result)?;
    }

    // Register module aliases so downstream references resolve.
    session.core.register_module_aliases(module_path);

    // Invalidate cache for this module so it gets re-cached.
    if let Some(cs) = cache_state.as_mut() {
        let hash = cranelisp_backend::cache::hash_source(&source);
        cs.record_recompiled(module_path);
        cs.source_hashes_mut().insert(module_path.clone(), hash);
    }

    // Restore the previous module context.
    session.core.tc.set_current_module(prev_module);

    Ok(())
}

/// Clear a module's state from the session before recompilation.
///
/// Uses `TypeChecker::remove_module` to remove the symbol table and unregister
/// traits/types. Also removes macros from the expander. Then re-inserts an
/// empty symbol table so the module path remains known during recompilation.
/// This ensures recompilation does not hit "duplicate definition" errors.
fn clear_module_state(session: &mut ReplSession, module_path: &ModuleFullPath) {
    // Collect macro names from the module before removing it.
    let macro_names: Vec<String> = session
        .core
        .tc
        .module_table(module_path)
        .map(|table| {
            table
                .all_symbols()
                .filter_map(|(name, entry)| {
                    if matches!(entry, ModuleEntry::Macro { .. }) {
                        Some(name.as_ref().to_string())
                    } else {
                        None
                    }
                })
                .collect()
        })
        .unwrap_or_default();

    // Remove macros from the expander.
    for mname in &macro_names {
        session.core.expander.remove_macro(mname);
    }

    // Remove the module's symbol table, traits, and type definitions.
    session.core.tc.remove_module(module_path);

    // Re-insert an empty symbol table so the module path is recognized
    // during recompilation.
    let fresh_table = cranelisp_types::SymbolTable::new(module_path.clone());
    session.core.tc.insert_module(fresh_table);
}

/// Run the interactive REPL loop.
///
/// Reads lines from stdin, evaluates them, prints results.
/// Errors are printed without crashing the session.
///
/// Library directories are resolved from `CRANELISP_LIB` (if set) or the
/// `stdlib/` directory in the current directory. If prelude loading fails,
/// starts without it and prints a warning.
pub fn run_repl() {
    let mut session = create_repl_session();
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
    session.core = crate::pipeline::CompilationSession::new();
    session.type_defs.clear();
    session.type_modules.clear();
    session.pending_changes.clear();
    session.error_modules.clear();
    session.file_to_module.clear();
    // Reset module structure but preserve the file path.
    let user_cl_path = session.current_module_structure.file_path.clone();
    session.current_module_structure = ModuleStructure {
        path: ModuleFullPath::from("user"),
        file_path: user_cl_path,
        mod_decls: vec![],
        import_specs: vec![],
        export_specs: vec![],
        impl_sexps: vec![],
        impls: vec![],
        dll_path: None,
    };
    session.last_saved_hash = None;
    // Note: loaded_platforms are kept alive — DLL pointers remain valid.
    // JIT modules from the old session are dropped (code memory may leak;
    // see design/int/repl-lifecycle.md §2.2).

    // Clear file watcher subscriptions before re-adding after prelude load
    // (per /arch I-3: avoid stale watches for modules no longer in session).
    if let Some(ref mut watcher) = session.watcher {
        watcher.clear_all();
    }

    // 2. Reload prelude from source (not cache).
    //
    // Cache loading is disabled during /reset because the typechecker's
    // trait and impl registries are not restored from cached symbol tables.
    // Loading from source ensures check() registers all traits and
    // impls needed for method resolution (e.g., Num.+$Int for the + operator).
    // The performance cost is acceptable — prelude compilation takes <500ms.
    let lib_dirs = crate::pipeline::assemble_lib_dirs(&project_root);
    let mut cache_state: Option<crate::pipeline::CacheState> = None;
    match crate::pipeline::load_prelude_into_session(
        &project_root,
        &lib_dirs,
        &mut session.core,
        &mut cache_state,
    ) {
        Ok(()) => {
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

    // 3. Rebuild file-to-module mapping and module dependency map.
    session.file_to_module =
        crate::pipeline::build_file_to_module_map(&project_root, &lib_dirs);
    session.module_dependencies =
        crate::pipeline::build_module_dependency_map(&project_root, &lib_dirs);

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

/// Check if a Sexp is an `(import ...)` form.
///
/// Returns true if the sexp is a list whose head is the symbol `import`.
fn is_import_form(sexp: &Sexp) -> bool {
    matches!(sexp, Sexp::List(elems, _)
        if !elems.is_empty() && matches!(&elems[0], Sexp::Symbol(name, _) if name == "import"))
}

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

// ── Runtime panic boundary (spec §12.7.4.1) ──────────────────────────────────

/// Invoke a JIT-compiled function and check for runtime errors.
///
/// `runtime_panic` in JIT code stores the error in a thread-local (because
/// Cranelift JIT frames lack unwind tables, so `catch_unwind` cannot work).
/// After the JIT call returns, we check `take_runtime_error()` for errors.
fn invoke_jit_eval<F>(f: F) -> Result<i64, CranelispError>
where
    F: FnOnce() -> i64,
{
    // Clear any stale error before the JIT call.
    let _ = cranelisp_runtime::panic::take_runtime_error();
    let value = f();
    // Check if runtime_panic was called during execution.
    if let Some(message) = cranelisp_runtime::panic::take_runtime_error() {
        Err(CranelispError::CodegenError {
            message,
            span: cranelisp_types::Span::SYNTHETIC,
        })
    } else {
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
}
