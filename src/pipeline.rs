// Pipeline orchestration: source text -> parse -> build -> typecheck -> codegen -> execute.
//
// Two modes:
//   1. Single-file batch: `compile_and_run()` — compiles one source string.
//   2. Multi-file batch: `compile_module_graph()` — discovers modules, toposorts, compiles in order.
//
// Both modes use `CompilationSession` for the core compilation loop:
//   parse -> expand (defmacro interception) -> build AST -> typecheck -> codegen -> GOT register.
//
// No `unwrap()` in this module -- all errors use `?`.

use std::collections::{HashMap, VecDeque};
use std::path::{Path, PathBuf};

use cranelisp_types::{
    CheckResult, CompileMode, CranelispError, Defn, MacroClauseInfo, ModuleEntry, ModuleFullPath,
    ModuleStructure, Program, ReplCheckResult, ReplInput, Sexp, Span, Symbol, Type, Visibility,
    Warning,
};

use cranelisp_backend::cache;

use crate::expander::CraneliftExpander;

// ---------------------------------------------------------------------------
// Cache configuration
// ---------------------------------------------------------------------------

/// Configuration for module caching.
///
/// Controls whether the pipeline checks/writes the `.cranelisp-cache/` directory.
/// `--no-cache` CLI flag produces `Disabled`.
pub enum CacheConfig {
    /// Caching disabled (e.g., `--no-cache` flag).
    Disabled,
    /// Caching enabled with the given cache directory.
    Enabled { cache_dir: PathBuf },
}

impl CacheConfig {
    /// Returns the cache directory if caching is enabled.
    fn cache_dir(&self) -> Option<&Path> {
        match self {
            CacheConfig::Disabled => None,
            CacheConfig::Enabled { cache_dir } => Some(cache_dir),
        }
    }
}

/// Mutable cache state carried through a compilation session.
///
/// Accumulates manifest updates as modules are compiled; writes the
/// final manifest on completion.
pub struct CacheState {
    /// The cache manifest (loaded from disk or freshly created).
    manifest: cache::CacheManifest,
    /// The cache directory path.
    cache_dir: PathBuf,
    /// Source hashes for modules compiled in this session.
    /// Used as dependency hashes for downstream modules.
    source_hashes: HashMap<ModuleFullPath, String>,
    /// Whether the manifest has been modified and needs writing.
    dirty: bool,
    /// Modules that were recompiled (cache miss) in this session.
    /// Used for cascade invalidation: if a dependency was recompiled,
    /// all its dependents must also recompile.
    recompiled: std::collections::HashSet<ModuleFullPath>,
}

impl CacheState {
    /// Initialize cache state: load existing manifest or create a new one.
    pub fn new(cache_dir: PathBuf) -> Self {
        let manifest = cache::read_manifest(&cache_dir)
            .unwrap_or_else(cache::CacheManifest::new_for_host);
        CacheState {
            manifest,
            cache_dir,
            source_hashes: HashMap::new(),
            dirty: false,
            recompiled: std::collections::HashSet::new(),
        }
    }

    /// Check if a module's cache is valid.
    ///
    /// Returns `true` if the module can be loaded from cache.
    /// Returns `false` on cache miss or if the manifest is globally invalid.
    ///
    /// `dependencies` is the list of this module's direct dependencies from
    /// the module graph. Only these are checked for cascade invalidation.
    fn is_cache_valid(
        &self,
        module_path: &ModuleFullPath,
        source_hash: &str,
        dependencies: &[ModuleFullPath],
    ) -> bool {
        // Cascade invalidation: if any of this module's dependencies was
        // recompiled, this module must also recompile.
        if self.has_recompiled_dependency(dependencies) {
            return false;
        }
        let dep_hashes = self.dependency_hashes_for(dependencies);
        match cache::check_manifest(&self.manifest, module_path, source_hash, &dep_hashes) {
            Ok(valid) => valid,
            Err(_reason) => false, // Global invalidation — treat as miss
        }
    }

    /// Check whether any of this module's direct dependencies was recompiled.
    ///
    /// Only checks the given dependency list (from the module graph) against
    /// the set of modules recompiled in this session.
    fn has_recompiled_dependency(&self, dependencies: &[ModuleFullPath]) -> bool {
        dependencies.iter().any(|dep| self.recompiled.contains(dep))
    }

    /// Record that a module was recompiled (cache miss).
    pub fn record_recompiled(&mut self, module_path: &ModuleFullPath) {
        self.recompiled.insert(module_path.clone());
    }

    /// Mutable access to source hashes for external recompilation tracking.
    pub fn source_hashes_mut(&mut self) -> &mut HashMap<ModuleFullPath, String> {
        &mut self.source_hashes
    }

    /// Build the dependency hash map for a module from its actual dependencies.
    ///
    /// Only includes hashes for modules that are direct dependencies of this
    /// module (from the module graph), rather than all previously compiled modules.
    fn dependency_hashes_for(
        &self,
        dependencies: &[ModuleFullPath],
    ) -> HashMap<ModuleFullPath, String> {
        dependencies
            .iter()
            .filter_map(|dep| {
                self.source_hashes
                    .get(dep)
                    .map(|hash| (dep.clone(), hash.clone()))
            })
            .collect()
    }

    /// Record that a module was compiled with the given source hash,
    /// and update the manifest entry.
    ///
    /// `dependencies` is the module's direct dependency list from the
    /// module graph. Only these modules' hashes are recorded in the manifest.
    fn record_compiled_module(
        &mut self,
        module_path: &ModuleFullPath,
        source_hash: String,
        dependencies: &[ModuleFullPath],
    ) {
        // Build dependency hashes from actual dependencies only.
        let dep_hashes: HashMap<String, String> = dependencies
            .iter()
            .filter_map(|dep| {
                self.source_hashes
                    .get(dep)
                    .map(|hash| (dep.0.clone(), hash.clone()))
            })
            .collect();
        self.manifest
            .upsert_module(module_path, source_hash.clone(), dep_hashes);
        self.source_hashes
            .insert(module_path.clone(), source_hash);
        self.dirty = true;
    }

    /// Write the manifest to disk if it was modified.
    fn flush(&self) -> Result<(), CranelispError> {
        if self.dirty {
            cache::write_manifest(&self.cache_dir, &self.manifest)?;
        }
        Ok(())
    }

    /// Flush the manifest to disk (public entry point for REPL cache integration).
    ///
    /// Writes the manifest if any modules were compiled during this session.
    /// Silently swallows errors (REPL should not crash on cache write failure).
    pub fn flush_manifest(&self) {
        let _ = self.flush();
    }
}

// ---------------------------------------------------------------------------
// CompilationSession: shared compilation core for both batch and REPL
// ---------------------------------------------------------------------------

/// Shared compilation state that both batch and REPL paths use.
///
/// Holds the persistent state needed to compile forms one at a time:
/// the typechecker, macro expander, GOT state, JIT lifetime management,
/// and platform symbols.
///
/// `ReplSession` wraps a `CompilationSession` and adds REPL-specific
/// concerns (display metadata, slash commands, trace state, introspection).
pub struct CompilationSession {
    /// Type checker state (persists across forms).
    pub tc: cranelisp_typecheck::TypeChecker,
    /// Backend GOT state (persists across forms for function redefinition).
    pub got_state: cranelisp_backend::got::ModuleCodegenState,
    /// Macro expander (persists across forms — macros accumulate).
    pub expander: CraneliftExpander,
    /// JIT instances that must stay alive (their code is referenced via GOT).
    /// Each defn/macro compilation creates a new JIT; we keep them alive here.
    pub jit_modules: Vec<cranelisp_backend::jit::Jit>,
    /// Platform function pointers for JIT symbol registration.
    /// Each entry is (jit_name, function_pointer). Passed to
    /// `Jit::new_with_symbols()` when creating JIT instances.
    pub platform_symbols: Vec<(String, *const u8)>,
    /// Shared JIT for batch module compilation (direct calls, TCO).
    /// Created lazily when `compile_module_batch` is first called.
    pub batch_jit: Option<cranelisp_backend::jit::Jit>,
    /// Accumulated function signatures for cross-module resolution in batch mode.
    pub func_sigs: Vec<(Symbol, usize)>,
    /// Function pointers loaded from cached `.o` files via the Linker.
    /// These are registered as extra symbols when the batch JIT is created,
    /// so downstream modules can call cached functions via direct calls.
    pub cached_symbols: Vec<(String, *const u8)>,
    /// Linker for loading cached `.o` files. Must stay alive so that
    /// mmap'd code regions remain valid for the duration of execution.
    pub linker: Option<cache::Linker>,
}

impl CompilationSession {
    /// Create a new compilation session with default state.
    pub fn new() -> Self {
        CompilationSession {
            tc: cranelisp_typecheck::TypeChecker::new(),
            got_state: cranelisp_backend::got::ModuleCodegenState::new(),
            expander: CraneliftExpander::new(),
            jit_modules: Vec::new(),
            platform_symbols: Vec::new(),
            batch_jit: None,
            func_sigs: Vec::new(),
            cached_symbols: Vec::new(),
            linker: None,
        }
    }

    /// Process sexps sequentially with defmacro interception and macro expansion.
    ///
    /// Per pipeline-orchestration.md §2:
    /// - `defmacro` forms are compiled and registered in the expander
    /// - Remaining forms are expanded through the macro expander
    /// - `(begin ...)` results are flattened
    /// - Non-macro forms are accumulated
    ///
    /// Returns the accumulated sexps ready for AST building.
    pub fn process_forms_sequentially(
        &mut self,
        sexps: Vec<Sexp>,
    ) -> Result<Vec<Sexp>, CranelispError> {
        let mut accumulated: Vec<Sexp> = Vec::new();
        for sexp in sexps {
            self.process_single_form(sexp, &mut accumulated)?;
        }
        Ok(accumulated)
    }

    /// Like `process_forms_sequentially` but also returns pre-expansion
    /// sexps paired with each expanded form.
    ///
    /// For forms that don't expand through begin (the common case), the
    /// original sexp is paired with the expanded form. For begin-expanded
    /// forms, each sub-form is paired with itself (expanded, since there
    /// is no single original that maps to each sub-form).
    ///
    /// Returns `(expanded_sexps, original_sexps)` where both vecs have
    /// the same length.
    pub fn process_forms_with_originals(
        &mut self,
        sexps: Vec<Sexp>,
    ) -> Result<(Vec<Sexp>, Vec<Sexp>), CranelispError> {
        let mut expanded: Vec<Sexp> = Vec::new();
        let mut originals: Vec<Sexp> = Vec::new();
        for sexp in sexps {
            let original = sexp.clone();
            let count_before = expanded.len();
            self.process_single_form(sexp, &mut expanded)?;
            let count_after = expanded.len();
            let added = count_after - count_before;
            if added == 1 {
                // Single form: pair with original (pre-expansion) sexp.
                originals.push(original);
            } else {
                // Begin-expanded: multiple sub-forms from one original.
                // Each sub-form uses its own (expanded) sexp as original.
                for i in count_before..count_after {
                    originals.push(expanded[i].clone());
                }
            }
        }
        Ok((expanded, originals))
    }

    /// Process sexps and build the AST program in one step.
    ///
    /// Convenience method that calls `process_forms_sequentially` then
    /// `build_program` on the accumulated sexps.
    pub fn process_and_build_program(
        &mut self,
        sexps: Vec<Sexp>,
    ) -> Result<Program, CranelispError> {
        let accumulated = self.process_forms_sequentially(sexps)?;
        cranelisp_frontend::build_program(&accumulated, &mut self.expander)
    }

    /// Process a single Sexp form: intercept defmacro, expand macros, flatten begin.
    ///
    /// Accumulated non-macro forms are pushed to `out`.
    fn process_single_form(
        &mut self,
        sexp: Sexp,
        out: &mut Vec<Sexp>,
    ) -> Result<(), CranelispError> {
        // Intercept defmacro before expansion.
        if cranelisp_frontend::is_defmacro(&sexp) {
            self.compile_and_register_macro(&sexp)?;
            return Ok(());
        }

        // Expand macros in the sexp.
        let expanded = self.expander.expand_sexp(sexp)?;

        // Flatten (begin ...) results and process each sub-form.
        let forms = cranelisp_frontend::flatten_begin(expanded);
        for form in forms {
            if cranelisp_frontend::is_defmacro(&form) {
                // defmacro-in-results: a macro expansion produced a defmacro.
                self.compile_and_register_macro(&form)?;
            } else {
                out.push(form);
            }
        }

        Ok(())
    }

    /// Compile a defmacro sexp and register it in the expander.
    ///
    /// Creates a fresh JIT for each macro compilation. The JIT is stored in
    /// `jit_modules` to keep the compiled function pointers alive.
    pub fn compile_and_register_macro(
        &mut self,
        sexp: &Sexp,
    ) -> Result<(), CranelispError> {
        let info = cranelisp_frontend::parse_defmacro(sexp)?;

        let mut jit = cranelisp_backend::jit::Jit::new()?;
        jit.declare_intrinsics()?;

        self.expander.compile_macro(&info, &mut self.tc, &mut jit)?;

        // Keep JIT alive so macro function pointers remain valid.
        self.jit_modules.push(jit);

        // Register macro in the current module's symbol table so it is visible
        // to cross-module imports (e.g., `(import [fn.threading [-> ->>]])`).
        let clause_infos: Vec<MacroClauseInfo> = info
            .clauses
            .iter()
            .map(|c| MacroClauseInfo {
                params: c.fixed_params.clone(),
                rest_param: c.rest_param.clone(),
                source: None,
            })
            .collect();
        let visibility = if info.is_private {
            Visibility::Private
        } else {
            Visibility::Public
        };
        self.tc.symbol_table_mut().insert(
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

        Ok(())
    }

    /// Compile a single form through the full pipeline:
    /// build AST -> typecheck -> compile defn into GOT -> return result.
    ///
    /// This is the per-form compilation core shared by both batch and REPL.
    /// The form should already be macro-expanded and defmacro-filtered
    /// (i.e., the output of `process_forms_sequentially`).
    pub fn compile_form(
        &mut self,
        form: &Sexp,
    ) -> Result<FormResult, CranelispError> {
        let input = cranelisp_frontend::build_repl_input(form, &mut self.expander)?;
        let check_result = self.tc.check_repl_input(&input)?;
        let warnings = check_result.warnings.clone();

        match &input {
            ReplInput::Expr(expr) => {
                // Compile mono defns first (constrained poly path).
                self.compile_mono_defns(&check_result)?;

                let check = build_check_for_backend(&check_result);
                let extra_syms: Vec<(&str, *const u8)> = self.platform_symbols
                    .iter()
                    .map(|(name, ptr)| (name.as_str(), *ptr))
                    .collect();
                let compiled = cranelisp_backend::compile_expr_with_got_and_symbols(
                    expr,
                    &check,
                    CompileMode::Interactive,
                    Some(&mut self.got_state),
                    &extra_syms,
                )?;

                // SAFETY: compiled code was just generated and finalized by our JIT.
                let value = unsafe { compiled.execute() };

                Ok(FormResult {
                    value,
                    ty: check_result.ty.clone(),
                    is_definition: false,
                    warnings,
                })
            }
            ReplInput::Defn(defn) => {
                // Skip compiling constrained fn base definitions -- they are
                // templates that get monomorphised at call sites.
                let is_constrained = check_result
                    .scheme
                    .as_ref()
                    .is_some_and(|s| !s.constraints.is_empty());

                // Compile monomorphised specializations BEFORE the defn body,
                // because the body may call constrained functions that need
                // their specializations already registered in the GOT.
                self.compile_mono_defns(&check_result)?;

                if !is_constrained {
                    let check = build_check_for_backend(&check_result);
                    self.compile_and_register_defn(defn, &check)?;
                }

                // Execute zero-arg defns and return the body's result type.
                let (value, result_ty) = if defn.params.is_empty() && !is_constrained {
                    let entry = self.got_state.def_codegen.get(defn.name.as_ref());
                    let code_ptr = entry
                        .and_then(|e| e.code_ptr)
                        .ok_or_else(|| CranelispError::CodegenError {
                            message: format!(
                                "no code pointer after compiling defn '{}'",
                                defn.name
                            ),
                            span: Span::SYNTHETIC,
                        })?;
                    let func: extern "C" fn() -> i64 =
                        unsafe { std::mem::transmute(code_ptr) };
                    // For zero-arg defns, the result type is the return type,
                    // not the function type (Fn [] T -> T).
                    let ret_ty = match &check_result.ty {
                        Type::Fn(_, ret) => (**ret).clone(),
                        other => other.clone(),
                    };
                    (func(), ret_ty)
                } else {
                    (0, check_result.ty.clone())
                };

                Ok(FormResult {
                    value,
                    ty: result_ty,
                    is_definition: true,
                    warnings,
                })
            }
            ReplInput::TypeDef { .. } => {
                Ok(FormResult {
                    value: 0,
                    ty: check_result.ty.clone(),
                    is_definition: true,
                    warnings,
                })
            }
            ReplInput::DefnMulti { span, .. } => Err(CranelispError::TypeError {
                message: "multi-signature functions not supported in Ring 0".into(),
                span: *span,
            }),
            ReplInput::TraitDecl(_decl) => {
                // Compile default method bodies.
                if !check_result.default_method_defns.is_empty() {
                    let check = build_check_for_backend(&check_result);
                    for defn in &check_result.default_method_defns {
                        self.compile_and_register_defn(defn, &check)?;
                    }
                }

                Ok(FormResult {
                    value: 0,
                    ty: check_result.ty.clone(),
                    is_definition: true,
                    warnings,
                })
            }
            ReplInput::TraitImpl(impl_) => {
                let check = build_check_for_backend(&check_result);

                // Compile impl methods.
                for defn in &impl_.methods {
                    self.compile_and_register_defn(defn, &check)?;
                }

                // Compile default method bodies.
                for defn in &check_result.default_method_defns {
                    self.compile_and_register_defn(defn, &check)?;
                }

                // Compile monomorphised specializations.
                self.compile_mono_defns(&check_result)?;

                Ok(FormResult {
                    value: 0,
                    ty: check_result.ty.clone(),
                    is_definition: true,
                    warnings,
                })
            }
        }
    }

    /// Compile a single function definition and register it in the GOT.
    pub fn compile_and_register_defn(
        &mut self,
        defn: &Defn,
        check: &CheckResult,
    ) -> Result<(), CranelispError> {
        // Create JIT with platform symbols registered (if any).
        let extra_symbols = self.extra_symbols_slice();
        let mut jit = cranelisp_backend::jit::Jit::new_with_symbols(&extra_symbols)?;

        // Declare runtime intrinsics (Ring 1 heap infrastructure).
        jit.declare_intrinsics()?;

        // Declare just this function.
        let func_ids = jit.declare_functions(&[defn])?;

        // Ensure a GOT slot exists for this function.
        let slot = self.got_state.ensure_slot_for(&defn.name)?;

        // Build GOT slot map from existing state + this new function.
        let mut got_slots: HashMap<Symbol, usize> = HashMap::new();
        for (name, dc) in &self.got_state.def_codegen {
            if let Some(s) = dc.got_slot {
                got_slots.insert(name.clone(), s);
            }
        }
        got_slots.insert(defn.name.clone(), slot);

        let got_base = self.got_state.got_base_ptr() as i64;

        // Build function arity map from existing GOT state + this defn.
        let mut func_arities: HashMap<Symbol, usize> = HashMap::new();
        for (name, dc) in &self.got_state.def_codegen {
            if let Some(pc) = dc.param_count {
                func_arities.insert(name.clone(), pc);
            }
        }
        func_arities.insert(defn.name.clone(), defn.params.len());

        // Compile the function with awareness of existing GOT.
        let compile_ctx = jit.build_compile_context(
            check,
            CompileMode::Interactive,
            &func_ids,
            &func_arities,
            Some(&got_slots),
            Some(got_base),
            None,
        );
        let _clif_ir = jit.compile_defn(defn, compile_ctx)?;

        // Finalize and get the code pointer.
        let code_ptr = jit.finalize_and_get_ptr(&defn.name, defn.params.len())?;

        // Update the GOT slot with the new code pointer.
        self.got_state.update_slot(slot, code_ptr);

        // Record codegen info.
        let entry = self.got_state.def_codegen.entry(defn.name.clone()).or_default();
        entry.code_ptr = Some(code_ptr);
        entry.got_slot = Some(slot);
        entry.param_count = Some(defn.params.len());
        entry.defn = Some(defn.clone());

        // Keep JIT alive so code pointer remains valid.
        self.jit_modules.push(jit);

        Ok(())
    }

    /// Compile monomorphised specializations from a check result.
    fn compile_mono_defns(
        &mut self,
        check_result: &ReplCheckResult,
    ) -> Result<(), CranelispError> {
        for mono in &check_result.mono_defns {
            let mut mono_check = build_check_for_backend(check_result);
            mono_check.method_resolutions.extend(mono.resolutions.clone());
            if !mono.expr_types.is_empty() {
                mono_check.expr_types = mono.expr_types.clone();
            }
            self.compile_and_register_defn(&mono.defn, &mono_check)?;
        }
        Ok(())
    }

    /// Ensure the shared batch JIT is initialized.
    ///
    /// Creates it lazily with platform symbols and intrinsics. Called before
    /// any batch module compilation.
    pub fn ensure_batch_jit(&mut self) -> Result<(), CranelispError> {
        if self.batch_jit.is_none() {
            let mut extra_symbols = self.extra_symbols_slice();
            // Include function pointers from cached .o files so the JIT
            // can resolve cross-module calls to cached functions.
            let cached_refs: Vec<(&str, *const u8)> = self
                .cached_symbols
                .iter()
                .map(|(name, ptr)| (name.as_str(), *ptr))
                .collect();
            extra_symbols.extend(cached_refs);
            let mut jit = cranelisp_backend::jit::Jit::new_with_symbols(&extra_symbols)?;
            jit.declare_intrinsics()?;
            self.batch_jit = Some(jit);
        }
        Ok(())
    }

    /// Compile a module's program using batch codegen (direct calls, TCO).
    ///
    /// Uses the shared batch JIT with `compile_module_program` for correct
    /// cross-module resolution, forward references, and tail call optimization.
    /// This is the right path for module graph compilation (prelude loading,
    /// multi-file batch).
    ///
    /// Returns warnings from codegen.
    pub fn compile_module_batch(
        &mut self,
        module_path: &ModuleFullPath,
        program: &Program,
        check: &CheckResult,
    ) -> Result<Vec<Warning>, CranelispError> {
        self.ensure_batch_jit()?;

        if !has_compilable_defns(program) {
            return Ok(Vec::new());
        }

        // Take the JIT out temporarily to avoid borrow conflict with func_sigs.
        let mut jit = self.batch_jit.take()
            .unwrap_or_else(|| unreachable!("invariant: batch_jit set by ensure_batch_jit"));
        let module_info = cranelisp_backend::compile_module_program(
            program,
            check,
            CompileMode::Batch,
            &mut jit,
            &self.func_sigs,
            module_path.as_ref(),
        )?;
        self.batch_jit = Some(jit);

        accumulate_func_sigs(module_path, &module_info.func_signatures, &mut self.func_sigs);

        Ok(module_info.warnings)
    }

    /// Finalize the shared batch JIT after all modules are compiled.
    ///
    /// Must be called after all `compile_module_batch` calls and before
    /// executing any compiled code.
    pub fn finalize_batch_jit(&mut self) -> Result<(), CranelispError> {
        if let Some(ref mut jit) = self.batch_jit {
            jit.finalize()?;
        }
        Ok(())
    }

    /// Get a function pointer from the batch JIT by name.
    pub fn batch_jit_get_ptr(
        &mut self,
        name: &Symbol,
        param_count: usize,
    ) -> Result<*const u8, CranelispError> {
        let jit = self.batch_jit.as_mut().ok_or_else(|| CranelispError::CodegenError {
            message: "batch JIT not initialized".into(),
            span: Span::SYNTHETIC,
        })?;
        jit.get_ptr_by_name(name, param_count)
    }

    /// Register GOT aliases for a module's compiled functions.
    ///
    /// After compiling a module's forms, register qualified aliases so that
    /// downstream modules can reference functions via module-qualified names
    /// like `helper/val` or `main.helper/val`. Each alias points to the same
    /// GOT slot as the bare function name.
    pub fn register_module_aliases(&mut self, module_path: &ModuleFullPath) {
        let mod_str: &str = module_path.as_ref();

        // Collect existing (name, slot, param_count) entries first to avoid borrow issues.
        let entries: Vec<(Symbol, usize, Option<usize>)> = self
            .got_state
            .def_codegen
            .iter()
            .filter_map(|(name, dc)| {
                dc.got_slot.map(|slot| (name.clone(), slot, dc.param_count))
            })
            .collect();

        for (name, slot, param_count) in &entries {
            let code_ptr = self.got_state.get_slot(*slot).unwrap_or(std::ptr::null());

            for alias_str in generate_module_aliases(mod_str, name.as_ref()) {
                let qualified = Symbol::from(alias_str);
                self.register_got_alias(&qualified, *slot, code_ptr, *param_count);
            }
        }
    }

    /// Register a GOT alias: an alternative name pointing to an existing GOT slot.
    fn register_got_alias(
        &mut self,
        alias: &Symbol,
        slot: usize,
        code_ptr: *const u8,
        param_count: Option<usize>,
    ) {
        // Only register if the alias doesn't already exist.
        if self.got_state.def_codegen.contains_key(alias.as_ref()) {
            return;
        }
        let entry = self.got_state.def_codegen.entry(alias.clone()).or_default();
        entry.got_slot = Some(slot);
        entry.code_ptr = if !code_ptr.is_null() { Some(code_ptr) } else { None };
        entry.param_count = param_count;
    }

    /// Compile a whole-program check result into the GOT, one defn at a time.
    ///
    /// Used for module compilation where `check_program` handles forward
    /// references via its two-pass approach, then we compile each defn
    /// individually into the GOT (unified codegen path).
    pub fn compile_checked_program(
        &mut self,
        program: &Program,
        check: &CheckResult,
    ) -> Result<Option<FormResult>, CranelispError> {
        use cranelisp_types::TopLevel;

        let mut last_result: Option<FormResult> = None;

        // Pre-register all defn names in GOT for forward references.
        for tl in program.iter() {
            match tl {
                TopLevel::Defn(defn) => {
                    self.got_state.ensure_slot_for(&defn.name)?;
                }
                TopLevel::TraitImpl(impl_) => {
                    for method in &impl_.methods {
                        self.got_state.ensure_slot_for(&method.name)?;
                    }
                }
                _ => {}
            }
        }

        // Compile default method bodies.
        for defn in &check.default_method_defns {
            self.compile_and_register_defn(defn, check)?;
        }

        // Compile mono specializations with per-specialization resolutions.
        for mono in &check.mono_defns {
            let mut merged = check.method_resolutions.clone();
            merged.extend(mono.resolutions.clone());
            let expr_types = if mono.expr_types.is_empty() {
                check.expr_types.clone()
            } else {
                mono.expr_types.clone()
            };
            let mono_check = CheckResult {
                method_resolutions: merged,
                constrained_fn_names: check.constrained_fn_names.clone(),
                mono_defns: Vec::new(),
                expr_types,
                default_method_defns: Vec::new(),
                warnings: Vec::new(),
                type_defs: check.type_defs.clone(),
                constructor_to_type: check.constructor_to_type.clone(),
            };
            self.compile_and_register_defn(&mono.defn, &mono_check)?;
        }

        // Compile each regular defn (skipping constrained fn base definitions).
        for tl in program.iter() {
            match tl {
                TopLevel::Defn(defn) => {
                    if check.constrained_fn_names.contains(&defn.name) {
                        continue; // Skip constrained fn base defs — templates only
                    }
                    self.compile_and_register_defn(defn, check)?;

                    // Execute zero-arg defns.
                    let (value, result_ty) = if defn.params.is_empty() {
                        let entry = self.got_state.def_codegen.get(defn.name.as_ref());
                        let code_ptr = entry
                            .and_then(|e| e.code_ptr)
                            .ok_or_else(|| CranelispError::CodegenError {
                                message: format!(
                                    "no code pointer after compiling defn '{}'",
                                    defn.name
                                ),
                                span: Span::SYNTHETIC,
                            })?;
                        let func: extern "C" fn() -> i64 =
                            unsafe { std::mem::transmute(code_ptr) };
                        // Determine return type from expr_types.
                        let ret_ty = check
                            .expr_types
                            .get(&defn.body.span())
                            .cloned()
                            .unwrap_or(Type::Int);
                        (func(), ret_ty)
                    } else {
                        (0, Type::Int)
                    };
                    last_result = Some(FormResult {
                        value,
                        ty: result_ty,
                        is_definition: true,
                        warnings: Vec::new(),
                    });
                }
                TopLevel::TraitImpl(impl_) => {
                    for method in &impl_.methods {
                        self.compile_and_register_defn(method, check)?;
                    }
                }
                _ => {
                    // TypeDef, TraitDecl — handled by typechecker, no codegen needed.
                }
            }
        }

        Ok(last_result)
    }

    /// Build a slice of extra JIT symbols from platform_symbols.
    fn extra_symbols_slice(&self) -> Vec<(&str, *const u8)> {
        self.platform_symbols
            .iter()
            .map(|(name, ptr)| (name.as_str(), *ptr))
            .collect()
    }
}

impl Default for CompilationSession {
    fn default() -> Self {
        Self::new()
    }
}

/// Result of compiling a single form via `CompilationSession::compile_form`.
pub struct FormResult {
    /// The i64 result value (raw bits; interpret per type).
    pub value: i64,
    /// The inferred type of the form.
    pub ty: Type,
    /// Whether this was a definition (defn/deftype/trait) rather than an expression.
    pub is_definition: bool,
    /// Non-fatal warnings.
    pub warnings: Vec<Warning>,
}

/// Build a CheckResult suitable for the backend from a ReplCheckResult.
pub fn build_check_for_backend(repl_check: &ReplCheckResult) -> CheckResult {
    CheckResult {
        method_resolutions: repl_check.method_resolutions.clone(),
        constrained_fn_names: repl_check.constrained_fn_names.clone(),
        mono_defns: Vec::new(),
        expr_types: repl_check.expr_types.clone(),
        default_method_defns: repl_check.default_method_defns.clone(),
        warnings: repl_check.warnings.clone(),
        type_defs: repl_check.type_defs.clone(),
        constructor_to_type: repl_check.constructor_to_type.clone(),
    }
}

// ---------------------------------------------------------------------------
// Single-file batch pipeline (existing)
// ---------------------------------------------------------------------------

/// Result of compiling and executing a source program.
pub struct PipelineResult {
    /// The i64 result value (raw bits; interpret per type).
    pub value: i64,
    /// The inferred type of the last expression or main function's return.
    pub ty: Type,
    /// Non-fatal warnings accumulated during compilation.
    pub warnings: Vec<Warning>,
}

/// Compile and execute source text in batch mode.
///
/// Uses whole-program typecheck + codegen for correctness (TCO detection,
/// forward references, direct calls). Macro processing uses CompilationSession
/// for the shared defmacro interception logic.
///
/// Pipeline stages:
/// 1. Parse source -> Vec<Sexp>
/// 2. Sequential form processing: defmacro interception, expansion, begin flattening
/// 3. Type check accumulated forms -> CheckResult (whole-program)
/// 4. Codegen -> CompiledProgram (whole-program, direct calls)
/// 5. Execute -> i64
pub fn compile_and_run(
    source: &str,
    mode: CompileMode,
) -> Result<PipelineResult, CranelispError> {
    // Stage 1: Parse
    let sexps = cranelisp_frontend::parse(source)?;

    // Stage 2: Process forms through CompilationSession (macro expansion).
    let mut session = CompilationSession::new();
    let program = session.process_and_build_program(sexps)?;

    // Stage 3: Whole-program type check (handles forward refs, TCO detection).
    let check = session.tc.check_program(&program)?;

    // Determine the result type from the last defn's return type.
    let result_type = infer_result_type(&program, &check);

    // Accumulate warnings from typecheck and codegen.
    let mut all_warnings: Vec<Warning> = check.warnings.clone();

    // Stage 4: Whole-program codegen (direct calls, TCO).
    let compiled = cranelisp_backend::compile_program(&program, &check, mode)?;
    all_warnings.extend(compiled.warnings.iter().cloned());

    // Stage 5: Execute
    // SAFETY: compiled code was just generated and finalized by our JIT.
    let value = unsafe { compiled.execute()? };

    Ok(PipelineResult {
        value,
        ty: result_type,
        warnings: all_warnings,
    })
}

/// Determine the result type from the last zero-arg function in the program.
/// This mirrors the backend's entry_fn selection: last zero-arg defn.
fn infer_result_type(program: &Program, check: &CheckResult) -> Type {
    use cranelisp_types::TopLevel;

    // Find the last zero-arg defn (same logic as backend entry_fn).
    let last_nullary = program.iter().rev().find_map(|tl| match tl {
        TopLevel::Defn(defn) if defn.params.is_empty() => Some(defn),
        _ => None,
    });

    if let Some(defn) = last_nullary {
        // Look up the resolved return type from expr_types or method_resolutions.
        if let Some(ty) = check.expr_types.get(&defn.body.span()) {
            return ty.clone();
        }
    }

    // Fallback: Int (convention for unknown result types).
    Type::Int
}

// ---------------------------------------------------------------------------
// Multi-file module graph pipeline
// ---------------------------------------------------------------------------

/// A node in the module dependency graph.
#[derive(Debug, Clone)]
pub struct ModuleNode {
    /// Module's full dotted path (e.g., "util", "core.math").
    pub path: ModuleFullPath,
    /// Filesystem path to the .cl source file.
    pub file_path: PathBuf,
    /// Modules this module depends on (declared via `mod`).
    pub dependencies: Vec<ModuleFullPath>,
}

/// The complete module dependency graph for a project.
#[derive(Debug)]
pub struct ModuleGraph {
    /// All modules, keyed by full path.
    pub nodes: HashMap<ModuleFullPath, ModuleNode>,
    /// The entry module's path.
    pub entry: ModuleFullPath,
    /// Project root directory (parent of the entry file).
    pub project_root: PathBuf,
    /// Library directories for module resolution (searched in order after project root).
    pub lib_dirs: Vec<PathBuf>,
}

/// Result of compiling a module graph for linking (no execution).
pub struct LinkCompileResult {
    /// All module `.o` file paths in the cache, in topological order.
    pub module_o_paths: Vec<PathBuf>,
    /// The entry module's symbol table (for `validate_main`).
    pub entry_symbols: cranelisp_types::SymbolTable,
    /// Module structures from the graph (for platform rlib discovery).
    pub module_structures: Vec<(ModuleFullPath, cranelisp_types::ModuleStructure)>,
    /// Non-fatal warnings accumulated during compilation.
    pub warnings: Vec<Warning>,
}

/// Result of compiling a multi-file module graph (compile + execute).
pub struct CompiledModuleGraph {
    /// The i64 result value from executing the entry module's entry point.
    pub value: i64,
    /// The inferred type of the entry point's return value.
    pub ty: Type,
    /// Non-fatal warnings accumulated during compilation.
    pub warnings: Vec<Warning>,
}

/// Result of compiling a module graph without executing it.
///
/// Contains the compiled session and entry point info needed by callers
/// that want to execute separately (batch mode) or not at all (cache write).
struct CompiledGraphSession {
    session: CompilationSession,
    entry_defn_name: Option<Symbol>,
    entry_result_type: Type,
    warnings: Vec<Warning>,
}

/// Discover the module dependency graph starting from an entry file.
///
/// Parses each file to extract `(mod name)` declarations, resolves file paths
/// per spec section 8.2.5, and recurses into submodules. Detects circular
/// dependencies.
///
/// `lib_dirs` provides library search paths for module resolution (searched in
/// order after the project root). Pass `&[]` to disable library resolution
/// (e.g. in tests with controlled fixtures).
pub fn discover_module_graph(
    entry: &Path,
    lib_dirs: &[PathBuf],
) -> Result<ModuleGraph, CranelispError> {
    let entry = entry.canonicalize().map_err(|e| CranelispError::ModuleError {
        message: format!("cannot resolve entry file '{}': {}", entry.display(), e),
        file: Some(entry.to_path_buf()),
        span: Span::SYNTHETIC,
    })?;

    let project_root = entry.parent().ok_or_else(|| CranelispError::ModuleError {
        message: "entry file has no parent directory".to_string(),
        file: Some(entry.clone()),
        span: Span::SYNTHETIC,
    })?.to_path_buf();

    // Derive module name from entry file stem.
    let entry_stem = entry
        .file_stem()
        .and_then(|s| s.to_str())
        .ok_or_else(|| CranelispError::ModuleError {
            message: "entry file has no valid stem".to_string(),
            file: Some(entry.clone()),
            span: Span::SYNTHETIC,
        })?;
    let entry_path = ModuleFullPath::from(entry_stem);

    let mut graph = ModuleGraph {
        nodes: HashMap::new(),
        entry: entry_path.clone(),
        project_root: project_root.clone(),
        lib_dirs: lib_dirs.to_vec(),
    };

    // BFS/DFS discovery with cycle detection.
    let mut visiting: Vec<ModuleFullPath> = Vec::new();
    discover_module_recursive(
        &entry_path,
        &entry,
        &project_root,
        &graph.lib_dirs,
        &mut graph.nodes,
        &mut visiting,
    )?;

    Ok(graph)
}

/// Recursively discover a module and its submodules.
///
/// `visiting` tracks the current discovery path for cycle detection.
fn discover_module_recursive(
    module_path: &ModuleFullPath,
    file_path: &Path,
    project_root: &Path,
    lib_dirs: &[PathBuf],
    nodes: &mut HashMap<ModuleFullPath, ModuleNode>,
    visiting: &mut Vec<ModuleFullPath>,
) -> Result<(), CranelispError> {
    // Cycle detection: if we're already visiting this module, we have a cycle.
    if visiting.contains(module_path) {
        let cycle_start = visiting.iter().position(|p| p == module_path).unwrap_or(0);
        let cycle: Vec<String> = visiting[cycle_start..]
            .iter()
            .map(|p| p.to_string())
            .collect();
        return Err(CranelispError::ModuleError {
            message: format!(
                "circular module dependency: {} -> {}",
                cycle.join(" -> "),
                module_path
            ),
            file: Some(file_path.to_path_buf()),
            span: Span::SYNTHETIC,
        });
    }

    // Already discovered (not a cycle, just already processed).
    if nodes.contains_key(module_path) {
        return Ok(());
    }

    visiting.push(module_path.clone());

    // Parse the file to extract module declarations.
    let source = std::fs::read_to_string(file_path).map_err(|e| CranelispError::ModuleError {
        message: format!("cannot read '{}': {}", file_path.display(), e),
        file: Some(file_path.to_path_buf()),
        span: Span::SYNTHETIC,
    })?;

    let sexps = cranelisp_frontend::parse(&source).map_err(|e| CranelispError::ModuleError {
        message: format!("parse error in '{}': {}", file_path.display(), e),
        file: Some(file_path.to_path_buf()),
        span: e.span(),
    })?;

    let (structure, _remaining) = cranelisp_frontend::extract_module_declarations(
        module_path.clone(),
        Some(file_path.to_path_buf()),
        sexps,
    )?;

    // Resolve submodule file paths and recurse.
    let mut dependencies = Vec::new();

    for mod_decl in &structure.mod_decls {
        // Handle inline submodules: they would need file extraction first.
        // For now, we only support file-based submodules.
        if mod_decl.inline_body.is_some() {
            // TODO: Extract inline module body to a file per spec section 8.2.2.
            // For now, skip inline modules — they need file creation before discovery.
            continue;
        }

        let submod_name = &mod_decl.name;

        // Build the child module's full path.
        let child_path = if module_path.0.is_empty() {
            ModuleFullPath::from(submod_name.as_ref())
        } else {
            ModuleFullPath::from(format!("{}.{}", module_path, submod_name))
        };

        // Resolve file per spec section 8.2.5:
        // 1. Child directory: {parent_dir}/{stem}/{name}.cl
        // 2. Sibling file: {parent_dir}/{name}.cl
        let resolved = resolve_submodule_file(
            file_path,
            submod_name.as_ref(),
            project_root,
            lib_dirs,
        )?;

        dependencies.push(child_path.clone());

        // Recurse into the submodule.
        discover_module_recursive(
            &child_path,
            &resolved,
            project_root,
            lib_dirs,
            nodes,
            visiting,
        )?;
    }

    // Also discover modules referenced by import specs (spec §8.10.1).
    // Import paths may reference modules not declared via (mod ...).
    discover_import_dependencies(
        &structure,
        module_path,
        file_path,
        project_root,
        lib_dirs,
        nodes,
        visiting,
        &mut dependencies,
    )?;

    // Register this module in the graph.
    nodes.insert(
        module_path.clone(),
        ModuleNode {
            path: module_path.clone(),
            file_path: file_path.to_path_buf(),
            dependencies,
        },
    );

    visiting.pop();
    Ok(())
}

/// Synthetic modules seeded by the compiler (no corresponding files).
const SYNTHETIC_MODULES: &[&str] = &["primitives", "macros"];

/// Discover modules referenced by import and export specs that aren't already in the graph.
///
/// Import and export specs reference modules by their full dotted path (e.g., "util",
/// "core.option"). This function resolves the root module name and discovers
/// it if not already known. Synthetic modules (`primitives`, `macros`) and
/// `super` references are skipped — they have no files.
///
/// Export specs are included in discovery so that re-export-only modules
/// (like the prelude) can reference root-level domain modules without
/// needing separate import declarations.
fn discover_import_dependencies(
    structure: &ModuleStructure,
    module_path: &ModuleFullPath,
    file_path: &Path,
    project_root: &Path,
    lib_dirs: &[PathBuf],
    nodes: &mut HashMap<ModuleFullPath, ModuleNode>,
    visiting: &mut Vec<ModuleFullPath>,
    dependencies: &mut Vec<ModuleFullPath>,
) -> Result<(), CranelispError> {
    // Discover modules referenced by import and export specs.
    // Both are included so that re-export-only modules (like the prelude)
    // trigger discovery of their referenced domain modules.
    let all_module_paths = structure
        .import_specs
        .iter()
        .map(|s| &s.module_path)
        .chain(structure.export_specs.iter().map(|s| &s.module_path));
    for ref_module_path in all_module_paths {
        let ref_path: &str = ref_module_path.as_ref();

        // Skip synthetic modules — they are compiler-seeded with no files.
        if is_synthetic_or_special(ref_path) {
            continue;
        }

        // Extract the root module name (first component before any dot).
        // E.g., "core.option" -> "core", "util" -> "util".
        let root_name = ref_path.split('.').next().unwrap_or(ref_path);

        // The path may be relative (bare name) or prefixed with the
        // current module path (e.g., "main.util" when current is "main").
        // Check both the bare path and a child-qualified version.
        let candidate_path = if module_path.0.is_empty() {
            ModuleFullPath::from(root_name)
        } else {
            // Check if the path already starts with the module path prefix.
            let mod_prefix = format!("{}.", module_path);
            if ref_path.starts_with(&mod_prefix) {
                // Already fully qualified relative to this module — use as-is.
                ref_module_path.clone()
            } else {
                // Bare name — resolve as a root-level module.
                ModuleFullPath::from(root_name)
            }
        };

        // Always record the dependency edge (even if the module was already
        // discovered by another path). Without this, the toposort may place
        // the depended-on module AFTER the dependent module.
        if dependencies.contains(&candidate_path) {
            // Already in this module's dependency list — skip.
            continue;
        }

        if nodes.contains_key(&candidate_path) {
            // Module already discovered by another path — record the
            // dependency edge but don't re-discover.
            dependencies.push(candidate_path.clone());
            continue;
        }

        // Try to resolve the module file.
        let resolved = match resolve_submodule_file(
            file_path,
            root_name,
            project_root,
            lib_dirs,
        ) {
            Ok(path) => path,
            Err(_) => {
                // Module file not found — it might be compiled later or be
                // a qualified reference to an already-loaded module. Skip
                // silently; the typechecker will produce a proper error if
                // the import cannot be resolved.
                continue;
            }
        };

        dependencies.push(candidate_path.clone());

        // Recurse into the discovered module.
        discover_module_recursive(
            &candidate_path,
            &resolved,
            project_root,
            lib_dirs,
            nodes,
            visiting,
        )?;
    }

    Ok(())
}

/// Check if a module path refers to a synthetic or special module.
///
/// Synthetic modules (`primitives`, `macros`) are compiler-seeded.
/// `super` is a relative reference to the parent module.
/// `prelude` is loaded separately via `load_prelude`.
fn is_synthetic_or_special(module_path: &str) -> bool {
    let root = module_path.split('.').next().unwrap_or(module_path);
    SYNTHETIC_MODULES.contains(&root) || root == "super" || root == "prelude"
}

/// Resolve a submodule's file path per spec section 8.2.5 and 8.11.2.
///
/// Search order:
/// 1. Child directory: `{parent_dir}/{stem}/{name}.cl`
/// 2. Sibling file: `{parent_dir}/{name}.cl`
/// 3. Project root: `{project_root}/{name}.cl`
/// 4. Lib directories: `{lib_dir}/{name}.cl` (each dir in order)
fn resolve_submodule_file(
    parent_file: &Path,
    name: &str,
    project_root: &Path,
    lib_dirs: &[PathBuf],
) -> Result<PathBuf, CranelispError> {
    let parent_dir = parent_file.parent().unwrap_or(Path::new("."));
    let stem = parent_file
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("");

    let filename = format!("{name}.cl");

    // 1. Child directory: {parent_dir}/{stem}/{name}.cl
    let child = parent_dir.join(stem).join(&filename);
    if child.is_file() {
        return Ok(child);
    }

    // 2. Sibling file: {parent_dir}/{name}.cl
    let sibling = parent_dir.join(&filename);
    if sibling.is_file() {
        return Ok(sibling);
    }

    // 3. Project root: {project_root}/{name}.cl (if different from parent_dir)
    if parent_dir != project_root {
        let root_file = project_root.join(&filename);
        if root_file.is_file() {
            return Ok(root_file);
        }
    }

    // 4. Lib directories: {lib_dir}/{name}.cl (each dir in order)
    for lib_dir in lib_dirs {
        let lib_file = lib_dir.join(&filename);
        if lib_file.is_file() {
            return Ok(lib_file);
        }
    }

    Err(CranelispError::ModuleError {
        message: format!(
            "cannot find module '{}' (searched child dir '{}/{}/', sibling '{}/{}', \
             project root, and lib directories)",
            name, parent_dir.display(), stem, parent_dir.display(), filename
        ),
        file: Some(parent_file.to_path_buf()),
        span: Span::SYNTHETIC,
    })
}

/// Topological sort of the module graph using Kahn's algorithm.
///
/// Returns modules in compilation order: leaves (no dependencies) first,
/// entry module last.
pub fn toposort(graph: &ModuleGraph) -> Result<Vec<ModuleFullPath>, CranelispError> {
    // Build in-degree map.
    let mut in_degree: HashMap<ModuleFullPath, usize> = HashMap::new();
    let mut adj: HashMap<ModuleFullPath, Vec<ModuleFullPath>> = HashMap::new();

    for (path, node) in &graph.nodes {
        in_degree.entry(path.clone()).or_insert(0);
        for dep in &node.dependencies {
            // dep -> path: if dep is a dependency, it must be compiled before path.
            // So path has an incoming edge from dep.
            adj.entry(dep.clone()).or_default().push(path.clone());
            *in_degree.entry(path.clone()).or_insert(0) += 1;
        }
    }

    // Seed queue with zero in-degree nodes.
    let mut queue: VecDeque<ModuleFullPath> = in_degree
        .iter()
        .filter(|(_, deg)| **deg == 0)
        .map(|(path, _)| path.clone())
        .collect();

    let mut sorted = Vec::with_capacity(graph.nodes.len());

    while let Some(current) = queue.pop_front() {
        sorted.push(current.clone());

        if let Some(dependents) = adj.get(&current) {
            for dependent in dependents {
                if let Some(deg) = in_degree.get_mut(dependent) {
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push_back(dependent.clone());
                    }
                }
            }
        }
    }

    if sorted.len() != graph.nodes.len() {
        // Remaining nodes form a cycle (should have been caught earlier, but guard here).
        let remaining: Vec<String> = graph
            .nodes
            .keys()
            .filter(|k| !sorted.iter().any(|s| s == *k))
            .map(|k| k.to_string())
            .collect();
        return Err(CranelispError::ModuleError {
            message: format!("circular dependency among modules: {}", remaining.join(", ")),
            file: None,
            span: Span::SYNTHETIC,
        });
    }

    Ok(sorted)
}

/// Parse source and extract module declarations (imports/exports/mods).
///
/// Phase 1 of module compilation: no TypeChecker interaction. Returns the
/// raw source text, module structure (import specs, exports, submodule
/// declarations) and the remaining unprocessed sexps. The caller must
/// register imports with the TypeChecker BEFORE processing the remaining
/// sexps (Phase 2), because `process_forms_sequentially` compiles
/// `defmacro` forms that may reference imported names.
///
/// Returns source text for cache key computation (SHA-256 hash).
fn parse_and_extract_module_with_source(
    module_path: &ModuleFullPath,
    node: &ModuleNode,
) -> Result<(String, ModuleStructure, Vec<Sexp>), CranelispError> {
    let source = read_module_source(node)?;

    let sexps = cranelisp_frontend::parse(&source)?;

    let (structure, remaining) = cranelisp_frontend::extract_module_declarations(
        module_path.clone(),
        Some(node.file_path.clone()),
        sexps,
    )?;

    Ok((source, structure, remaining))
}

/// Read a module's source file without parsing.
///
/// Used by the cache-hit path to compute the source hash without
/// the overhead of parsing and extracting declarations.
fn read_module_source(node: &ModuleNode) -> Result<String, CranelispError> {
    std::fs::read_to_string(&node.file_path).map_err(|e| {
        CranelispError::ModuleError {
            message: format!("cannot read '{}': {}", node.file_path.display(), e),
            file: Some(node.file_path.clone()),
            span: Span::SYNTHETIC,
        }
    })
}

/// Attempt to restore a module from cache.
///
/// On cache hit (manifest valid + `.meta.json` readable), restores the
/// module's symbol table into the typechecker. If a valid `.o` file
/// exists, loads it via the Linker to get function code pointers and
/// registers them as cached symbols for the batch JIT.
///
/// Returns `true` if the cache hit succeeded and the module was fully
/// restored (compilation can be skipped).
fn try_restore_from_cache(
    cache_state: &mut CacheState,
    module_path: &ModuleFullPath,
    source_hash: &str,
    dependencies: &[ModuleFullPath],
    session: &mut CompilationSession,
) -> Result<bool, CranelispError> {
    if !cache_state.is_cache_valid(module_path, source_hash, dependencies) {
        return Ok(false);
    }

    // Load the full cached module (metadata + .o check) from disk.
    let cached = match cache::try_load_cached_module(&cache_state.cache_dir, module_path)? {
        Some(c) => c,
        None => return Ok(false), // .meta.json missing or corrupt — cache miss
    };

    // Restore the symbol table into the typechecker. This makes the module's
    // types, traits, constructors, and function signatures visible to
    // downstream modules that import from it.
    //
    // The cached symbol table already contains Import/Reexport entries from
    // when it was originally compiled, so we do NOT need to re-run
    // register_imports/register_exports. The table is a complete snapshot.
    session.tc.restore_cached_module(cached.metadata.symbol_table.clone());

    // Restore trait impl registrations from the codegen state's mangled method
    // names. During fresh compilation, register_trait_impl populates impl_registry;
    // on cache restore we reconstruct it from names like "Num.+$Int".
    let mangled_names: Vec<String> = cached.codegen_state()
        .got_slots
        .keys()
        .map(|s| s.as_ref().to_string())
        .collect();
    session.tc.restore_cached_impls(&mangled_names);

    // If a valid .o file exists, load it via the Linker and register
    // function pointers for the batch JIT.
    if cached.has_object {
        load_cached_object_into_session(module_path, &cached, session)?;
    }

    // Record source hash for dependency tracking of downstream modules.
    cache_state
        .source_hashes
        .insert(module_path.clone(), source_hash.to_string());

    Ok(true)
}

/// Re-compile defmacro forms from a cached module's source.
///
/// When a module is loaded from cache, its symbol table (including
/// `ModuleEntry::Macro` entries) is restored, but the actual macro
/// functions are not compiled. Downstream modules that use these macros
/// (e.g., `str`, `list`, `do`) will fail at expansion time because the
/// expander has no function pointers for them.
///
/// This function re-parses the module source, extracts defmacro forms,
/// and compiles them into the session's expander. Non-macro forms are
/// skipped — the module's compiled code is already available from cache.
fn recompile_macros_for_cached_module(
    module_path: &ModuleFullPath,
    node: &ModuleNode,
    session: &mut CompilationSession,
) -> Result<(), CranelispError> {
    let source = read_module_source(node)?;
    let sexps = cranelisp_frontend::parse(&source)?;
    if sexps.is_empty() {
        return Ok(());
    }

    let (_structure, remaining) = cranelisp_frontend::extract_module_declarations(
        module_path.clone(),
        Some(node.file_path.clone()),
        sexps,
    )?;

    // Set module context so macro compilation sees the right imports.
    let saved_module = session.tc.current_module_path().clone();
    session.tc.set_current_module(module_path.clone());

    // Compile only defmacro forms; skip everything else.
    for sexp in remaining {
        if cranelisp_frontend::is_defmacro(&sexp) {
            session.compile_and_register_macro(&sexp)?;
        }
    }

    session.tc.set_current_module(saved_module);
    Ok(())
}

/// Load a cached module's `.o` file and register function pointers.
///
/// Creates the Linker (if not yet created), registers intrinsic symbols
/// and previously-loaded cached function symbols, then loads the `.o`
/// file. The resulting function pointers are accumulated in
/// `session.cached_symbols` so the batch JIT can resolve cross-module
/// calls to these cached functions.
fn load_cached_object_into_session(
    module_path: &ModuleFullPath,
    cached: &cache::CachedModule,
    session: &mut CompilationSession,
) -> Result<(), CranelispError> {
    // Initialize the Linker on first use and register all intrinsic symbols.
    if session.linker.is_none() {
        let mut linker = cache::Linker::new()?;
        register_intrinsics_on_linker(&mut linker);
        // Register platform symbols (DLL functions).
        for (name, ptr) in &session.platform_symbols {
            linker.register_symbol(name, *ptr);
        }
        session.linker = Some(linker);
    }

    // Register any previously-loaded cached function symbols so this
    // module's .o can call functions from earlier cached modules.
    let linker = session.linker.as_mut()
        .unwrap_or_else(|| unreachable!("invariant: linker just initialized"));
    for (name, ptr) in &session.cached_symbols {
        linker.register_symbol(name, *ptr);
    }

    // Load the .o file and get function name -> code pointer map.
    let fn_addrs = cache::load_cached_object(linker, cached)?;

    // Collect function signatures from the codegen state for cross-module
    // resolution, and register function pointers as cached symbols.
    let codegen_state = cached.codegen_state();
    for (fn_name, &slot) in &codegen_state.got_slots {
        let fn_name_str: &str = fn_name.as_ref();
        let param_count = codegen_state
            .def_entries
            .get(fn_name)
            .and_then(|e| e.param_count)
            .unwrap_or(0);

        // Register in func_sigs for batch JIT cross-module resolution.
        session.func_sigs.push((fn_name.clone(), param_count));

        // If we got a code pointer from the .o file, register it as a
        // cached symbol for the batch JIT AND in the GOT for REPL-mode
        // indirect calls. Without GOT registration, /reset + cache load
        // fails because REPL-compiled code uses GOT-indirect calls.
        if let Some(code_ptr) = fn_addrs.get(fn_name_str) {
            session.cached_symbols.push((fn_name_str.to_string(), *code_ptr));
            // Register in GOT so REPL code can call this function.
            let got_slot = session.got_state.ensure_slot_for(fn_name)?;
            session.got_state.update_slot(got_slot, *code_ptr);
        }

        // Suppress unused variable warning — slot is from the cached
        // codegen state and identifies the function's GOT position in
        // the original compilation.
        let _ = slot;
    }

    // Register qualified aliases for this module's functions using the
    // shared alias generation logic.
    let mod_str: &str = module_path.as_ref();
    let alias_entries: Vec<(Symbol, usize)> = codegen_state
        .got_slots
        .keys()
        .map(|fn_name| {
            let pc = codegen_state
                .def_entries
                .get(fn_name)
                .and_then(|e| e.param_count)
                .unwrap_or(0);
            (fn_name.clone(), pc)
        })
        .collect();
    accumulate_func_sigs(module_path, &alias_entries, &mut session.func_sigs);

    // Also register qualified aliases as cached symbols and GOT slots.
    for (fn_name, _pc) in &alias_entries {
        let fn_name_str: &str = fn_name.as_ref();
        if let Some(code_ptr) = fn_addrs.get(fn_name_str) {
            for alias in generate_module_aliases(mod_str, fn_name_str) {
                session.cached_symbols.push((alias.clone(), *code_ptr));
                // Register alias in GOT for REPL-mode indirect calls.
                let alias_sym = Symbol::from(alias.as_str());
                let got_slot = session.got_state.ensure_slot_for(&alias_sym)?;
                session.got_state.update_slot(got_slot, *code_ptr);
            }
        }
    }

    Ok(())
}

/// Register all runtime and primitive intrinsic symbols on the Linker.
///
/// Delegates to `cranelisp_backend::jit::intrinsic_symbols()` — the single
/// source of truth for intrinsic name/pointer mappings.
fn register_intrinsics_on_linker(linker: &mut cache::Linker) {
    for sym in cranelisp_backend::jit::intrinsic_symbols() {
        linker.register_symbol(sym.name, sym.ptr);
    }
}

/// Write cache files for a compiled module: `.meta.json` and `.o`.
///
/// Builds `CacheMetadata` from the typechecker's symbol table and the
/// module structure, then writes both the metadata and object file via
/// `process_cache_packet`.
///
/// `program` and `check` are needed to build the `ObjectCompileInput`
/// for `.o` compilation. Pass `None` for `program` if the module has
/// no compilable definitions (empty modules, type-only modules).
pub(crate) fn write_module_cache(
    cache_state: &mut CacheState,
    module_path: &ModuleFullPath,
    source_hash: String,
    dependencies: &[ModuleFullPath],
    structure: &ModuleStructure,
    tc: &cranelisp_typecheck::TypeChecker,
    program: Option<&Program>,
    check: Option<&CheckResult>,
    func_sigs: &[(Symbol, usize)],
) -> Result<(), CranelispError> {
    // Build the CacheMetadata from current typechecker state.
    let symbol_table = tc.module_table(module_path)
        .cloned()
        .unwrap_or_else(|| cranelisp_types::SymbolTable::new(module_path.clone()));

    // Build codegen state from program info (for .o reconstruction on load).
    let codegen_state = build_codegen_state_for_cache(program, check);

    let metadata = cache::CacheMetadata {
        symbol_table,
        module_structure: structure.clone(),
        codegen_state,
    };

    // Build the ObjectCompileInput if there are compilable definitions.
    let object_input = build_object_compile_input(
        module_path, program, check, func_sigs,
    );

    // Build and process the cache packet (writes .meta.json + .o).
    let dep_hashes: HashMap<String, String> = dependencies
        .iter()
        .filter_map(|dep| {
            cache_state
                .source_hashes
                .get(dep)
                .map(|hash| (dep.0.clone(), hash.clone()))
        })
        .collect();

    let packet = cache::build_cache_packet(
        &cache_state.cache_dir,
        module_path,
        &source_hash,
        false, // is_stdlib: determined by context, not critical for correctness
        dep_hashes,
        &metadata,
        object_input,
    )?;
    cache::process_cache_packet(&packet)?;

    // Record in manifest.
    cache_state.record_compiled_module(module_path, source_hash, dependencies);

    Ok(())
}

/// Build `CacheCodegenState` from a program's definitions.
///
/// Records GOT slot assignments and function parameter counts so the
/// cache-load path can reconstruct the batch JIT's symbol table.
fn build_codegen_state_for_cache(
    program: Option<&Program>,
    check: Option<&CheckResult>,
) -> cache::CacheCodegenState {
    use cranelisp_types::TopLevel;

    let mut got_slots: HashMap<Symbol, usize> = HashMap::new();
    let mut def_entries: HashMap<Symbol, cache::SerializedDefEntry> = HashMap::new();
    let mut next_slot: usize = 0;

    if let Some(prog) = program {
        for tl in prog.iter() {
            if let TopLevel::Defn(defn) = tl {
                // Skip constrained fn base definitions.
                if let Some(ch) = check {
                    if ch.constrained_fn_names.contains(&defn.name) {
                        continue;
                    }
                }
                let slot = next_slot;
                next_slot += 1;
                got_slots.insert(defn.name.clone(), slot);
                def_entries.insert(
                    defn.name.clone(),
                    cache::SerializedDefEntry {
                        got_slot: Some(slot),
                        source: None,
                        sexp: None,
                        defn: Some(defn.clone()),
                        param_count: Some(defn.params.len()),
                    },
                );
            }
            // TraitImpl methods have unmangled names; mangled versions
            // are in check.default_method_defns, collected below.
        }

        // Also include monomorphised specializations.
        if let Some(ch) = check {
            for mono in &ch.mono_defns {
                let slot = next_slot;
                next_slot += 1;
                got_slots.insert(mono.defn.name.clone(), slot);
                def_entries.insert(
                    mono.defn.name.clone(),
                    cache::SerializedDefEntry {
                        got_slot: Some(slot),
                        source: None,
                        sexp: None,
                        defn: Some(mono.defn.clone()),
                        param_count: Some(mono.defn.params.len()),
                    },
                );
            }
            for defn in &ch.default_method_defns {
                let slot = next_slot;
                next_slot += 1;
                got_slots.insert(defn.name.clone(), slot);
                def_entries.insert(
                    defn.name.clone(),
                    cache::SerializedDefEntry {
                        got_slot: Some(slot),
                        source: None,
                        sexp: None,
                        defn: Some(defn.clone()),
                        param_count: Some(defn.params.len()),
                    },
                );
            }
        }
    }

    cache::CacheCodegenState {
        got_slots,
        next_got_slot: next_slot,
        def_entries,
    }
}

/// Collected defns with slot assignments for `.o` compilation.
struct CollectedDefns {
    defns: Vec<(Defn, cranelisp_types::Scheme)>,
    fn_slot_assignments: HashMap<Symbol, cache::object::FnSlotInfo>,
    next_slot: usize,
}

/// Collect defns (functions, trait methods, mono specializations, default methods)
/// from a program and check result, assigning GOT slots to each.
fn collect_defns_for_cache(
    program: Option<&Program>,
    check: Option<&CheckResult>,
) -> CollectedDefns {
    use cranelisp_types::TopLevel;

    let mut defns: Vec<(Defn, cranelisp_types::Scheme)> = Vec::new();
    let mut fn_slot_assignments: HashMap<Symbol, cache::object::FnSlotInfo> = HashMap::new();
    let mut next_slot: usize = 0;

    let Some(prog) = program else {
        return CollectedDefns { defns, fn_slot_assignments, next_slot };
    };

    for tl in prog.iter() {
        match tl {
            TopLevel::Defn(defn) => {
                // Skip constrained fn base definitions.
                if let Some(ch) = check {
                    if ch.constrained_fn_names.contains(&defn.name) {
                        continue;
                    }
                }
                let scheme = scheme_for_defn(defn, check);
                let slot = next_slot;
                next_slot += 1;
                fn_slot_assignments.insert(
                    defn.name.clone(),
                    cache::object::FnSlotInfo {
                        slot,
                        param_count: defn.params.len(),
                    },
                );
                defns.push((defn.clone(), scheme));
            }
            // TraitImpl methods have unmangled names (e.g., "+"). The mangled
            // versions ("Num.+$Int") are in check.default_method_defns and are
            // collected below. Skipping TraitImpl here avoids DuplicateDefinition
            // errors in the object compilation path.
            _ => {}
        }
    }

    // Also include monomorphised specializations and default methods.
    if let Some(ch) = check {
        for mono in &ch.mono_defns {
            let scheme = scheme_for_defn(&mono.defn, Some(ch));
            let slot = next_slot;
            next_slot += 1;
            fn_slot_assignments.insert(
                mono.defn.name.clone(),
                cache::object::FnSlotInfo {
                    slot,
                    param_count: mono.defn.params.len(),
                },
            );
            defns.push((mono.defn.clone(), scheme));
        }
        for defn in &ch.default_method_defns {
            let scheme = scheme_for_defn(defn, Some(ch));
            let slot = next_slot;
            next_slot += 1;
            fn_slot_assignments.insert(
                defn.name.clone(),
                cache::object::FnSlotInfo {
                    slot,
                    param_count: defn.params.len(),
                },
            );
            defns.push((defn.clone(), scheme));
        }
    }

    CollectedDefns { defns, fn_slot_assignments, next_slot }
}

/// Build a `Scheme` for a defn using real types from the `CheckResult`.
///
/// The typechecker records the full `Type::Fn(params, ret)` at `defn.span`
/// in `expr_types`. This function looks it up to get precise parameter and
/// return types. Falls back to `Type::Int` placeholder if the type is not
/// recorded (e.g., when `check` is `None`).
fn scheme_for_defn(defn: &Defn, check: Option<&CheckResult>) -> cranelisp_types::Scheme {
    let ty = check
        .and_then(|ch| ch.expr_types.get(&defn.span))
        .cloned()
        .unwrap_or_else(|| {
            // Fallback: construct a placeholder Fn type.
            Type::Fn(
                defn.params.iter().map(|_| Type::Int).collect(),
                Box::new(Type::Int),
            )
        });
    cranelisp_types::Scheme {
        vars: vec![],
        constraints: HashMap::new(),
        ty,
    }
}

/// Collected cross-module function references for `.o` import declarations.
struct CrossModuleRefs {
    fn_to_module: HashMap<Symbol, ModuleFullPath>,
    cross_module_fns: Vec<(Symbol, usize)>,
}

/// Map external function references to their source modules and collect
/// cross-module function signatures for ObjectModule import declarations.
///
/// Prior `func_sigs` entries represent functions from earlier modules
/// that this module might call.
fn collect_cross_module_refs(
    func_sigs: &[(Symbol, usize)],
) -> CrossModuleRefs {
    let mut fn_to_module: HashMap<Symbol, ModuleFullPath> = HashMap::new();
    let mut cross_module_fns: Vec<(Symbol, usize)> = Vec::new();

    for (name, param_count) in func_sigs {
        // Extract module path from qualified names (e.g., "core.num/+" -> "core.num").
        if let Some(slash) = name.as_ref().find('/') {
            let mod_part = &name.as_ref()[..slash];
            fn_to_module.insert(name.clone(), ModuleFullPath::from(mod_part));
        }
        // Include all prior functions as potential cross-module references.
        // The ObjectModule compiler uses these to declare imports so the linker
        // can resolve cross-module calls (both qualified and bare imported names).
        cross_module_fns.push((name.clone(), *param_count));
    }

    CrossModuleRefs { fn_to_module, cross_module_fns }
}

/// Build `ObjectCompileInput` for `.o` file compilation.
///
/// Collects defns with their inferred schemes from the program and check
/// result, builds the intrinsic table, and assembles fn_slot_assignments
/// and fn_to_module maps.
fn build_object_compile_input(
    module_path: &ModuleFullPath,
    program: Option<&Program>,
    check: Option<&CheckResult>,
    func_sigs: &[(Symbol, usize)],
) -> cache::ObjectCompileInput {
    let collected = collect_defns_for_cache(program, check);
    let cross_refs = collect_cross_module_refs(func_sigs);
    let intrinsics = build_intrinsic_table();

    cache::ObjectCompileInput {
        module_path: module_path.clone(),
        defns: collected.defns,
        method_resolutions: check
            .map(|ch| ch.method_resolutions.clone())
            .unwrap_or_default(),
        fn_slot_assignments: collected.fn_slot_assignments,
        fn_to_module: cross_refs.fn_to_module,
        intrinsics,
        type_defs: check
            .map(|ch| ch.type_defs.clone())
            .unwrap_or_default(),
        constructor_to_type: check
            .map(|ch| ch.constructor_to_type.clone())
            .unwrap_or_default(),
        expr_types: check
            .map(|ch| ch.expr_types.clone())
            .unwrap_or_default(),
        next_got_slot: collected.next_slot,
        cross_module_fns: cross_refs.cross_module_fns,
    }
}

/// Build the `IntrinsicTable` listing all runtime and primitive functions
/// that compiled code may reference.
///
/// Delegates to `cranelisp_backend::jit::intrinsic_symbols()` — the single
/// source of truth for intrinsic name/pointer/param-count mappings.
fn build_intrinsic_table() -> cache::IntrinsicTable {
    let mut table = cache::IntrinsicTable::new();

    for sym in cranelisp_backend::jit::intrinsic_symbols() {
        let entry = cache::IntrinsicEntry {
            user_name: Symbol::from(sym.name),
            jit_name: sym.name.to_string(),
            param_count: sym.param_count,
        };
        if sym.is_runtime {
            table.runtime_fns.push(entry);
        } else {
            table.primitive_fns.push(entry);
        }
    }

    table
}

/// Assemble the list of library directories for module resolution.
///
/// Per spec section 8.11.2, lib directory locations are specified by:
/// 1. `CRANELISP_LIB` environment variable (colon-separated list of paths)
/// 2. Fallback: `{project_root}/stdlib/` if it exists and `CRANELISP_LIB` is not set
///
/// When `CRANELISP_LIB` is set (even to empty), the fallback is NOT used — the
/// env var takes full control of the library search path.
///
// NOTE: spec/08-modules.md §8.11 says lib dirs come from (1) Cranelisp.toml
// project config and (2) CRANELISP_LIB env var. Cranelisp.toml is Ring 4 scope.
// Current implementation (CRANELISP_LIB → stdlib/ fallback) is correct for
// Ring 0–3. The stdlib/ fallback is a practical default, not spec-mandated.
// Ring 4 will add Cranelisp.toml support.
pub fn assemble_lib_dirs(project_root: &Path) -> Vec<PathBuf> {
    if let Ok(env_val) = std::env::var("CRANELISP_LIB") {
        // CRANELISP_LIB is set: split on ':' and collect non-empty paths.
        return env_val
            .split(':')
            .filter(|s| !s.is_empty())
            .map(PathBuf::from)
            .collect();
    }

    // Fallback: {project_root}/stdlib/ if it exists.
    let candidate = project_root.join("stdlib");
    if candidate.is_dir() {
        vec![candidate]
    } else {
        Vec::new()
    }
}

/// Load a module (and its transitive dependencies) from disk into an existing
/// CompilationSession.
///
/// Used by the REPL to lazily compile modules referenced by `(import ...)` that
/// are not already loaded. Discovers the module graph rooted at the given file,
/// compiles each dependency in topological order using the GOT-based codegen
/// path (same as REPL per-form compilation), so that functions are callable
/// from subsequent REPL expressions.
///
/// Modules already present in the session's typechecker are skipped (not recompiled).
pub fn load_module_into_session(
    module_name: &str,
    project_root: &Path,
    lib_dirs: &[PathBuf],
    session: &mut CompilationSession,
) -> Result<(), CranelispError> {
    // Resolve the module file using the same search order as batch mode.
    let filename = format!("{module_name}.cl");

    // Search order: project root, then lib dirs.
    let file_path = {
        let root_file = project_root.join(&filename);
        if root_file.is_file() {
            root_file
        } else {
            let mut found = None;
            for lib_dir in lib_dirs {
                let lib_file = lib_dir.join(&filename);
                if lib_file.is_file() {
                    found = Some(lib_file);
                    break;
                }
            }
            found.ok_or_else(|| CranelispError::ModuleError {
                message: format!(
                    "cannot find module '{}' (searched project root '{}' and lib directories)",
                    module_name, project_root.display()
                ),
                file: None,
                span: Span::SYNTHETIC,
            })?
        }
    };

    // Discover the module graph rooted at this file.
    let graph = discover_module_graph(&file_path, lib_dirs)?;
    let order = toposort(&graph)?;

    // Check whether a prelude was loaded so we can inject implicit imports.
    let prelude_loaded = session.tc.has_module(&ModuleFullPath::from("prelude"));

    // Compile each module in topological order, skipping already-loaded modules.
    for module_path in &order {
        if session.tc.has_module(module_path) {
            continue;
        }

        let node = &graph.nodes[module_path];
        let (_source, structure, remaining_sexps) =
            parse_and_extract_module_with_source(module_path, node)?;

        // Set up module context.
        session.tc.set_current_module(module_path.clone());

        // Inject implicit prelude import for non-prelude modules.
        if prelude_loaded {
            inject_prelude_import(&mut session.tc)?;
        }

        if !structure.import_specs.is_empty() {
            session.tc.register_imports(&structure.import_specs)?;
        }
        if !structure.export_specs.is_empty() {
            session.tc.register_exports(&structure.export_specs)?;
        }

        // Process forms (defmacro compilation happens here).
        let accumulated = session.process_forms_sequentially(remaining_sexps)?;

        // Build program AST.
        let program = cranelisp_frontend::build_program(
            &accumulated,
            &mut session.expander,
        )?;

        if program.is_empty() {
            continue;
        }

        // Typecheck.
        let check = session.tc.check_program(&program)?;

        // Compile into the GOT (same path as REPL per-form compilation).
        // This ensures functions are callable from subsequent REPL expressions
        // via GOT-indirect calling.
        session.compile_checked_program(&program, &check)?;

        // Register module-qualified aliases so imports can resolve.
        session.register_module_aliases(module_path);
    }

    Ok(())
}

/// Resolve the prelude module file, if it exists.
///
/// Search order (matching normal module resolution per spec §8.11.2):
/// 1. Project root: `{project_root}/prelude.cl`
/// 2. Lib directories: `{lib_dir}/prelude.cl` (each dir in order)
///
/// Returns `None` if no prelude file is found. The system works
/// without a prelude — named primitives remain available.
pub fn resolve_prelude(
    project_root: &Path,
    lib_dirs: &[PathBuf],
) -> Option<PathBuf> {
    // 1. Project root (local prelude overrides lib prelude).
    let root_prelude = project_root.join("prelude.cl");
    if root_prelude.is_file() {
        return Some(root_prelude);
    }

    // 2. Lib directories (in order).
    for lib_dir in lib_dirs {
        let lib_prelude = lib_dir.join("prelude.cl");
        if lib_prelude.is_file() {
            return Some(lib_prelude);
        }
    }

    None
}

/// Build a mapping from canonical file paths to module paths.
///
/// Discovers the module graph starting from the prelude file and returns
/// a mapping for all modules. Used by the REPL file watcher to map
/// changed files to module paths for recompilation.
pub fn build_file_to_module_map(
    project_root: &Path,
    lib_dirs: &[PathBuf],
) -> HashMap<PathBuf, ModuleFullPath> {
    let mut map = HashMap::new();
    let prelude_file = match resolve_prelude(project_root, lib_dirs) {
        Some(f) => f,
        None => return map,
    };
    if let Ok(graph) = discover_module_graph(&prelude_file, lib_dirs) {
        for (module_path, node) in &graph.nodes {
            if let Ok(canonical) = node.file_path.canonicalize() {
                map.insert(canonical, module_path.clone());
            }
        }
    }
    map
}

/// Build a module dependency map from the module graph discovered during prelude loading.
///
/// Returns a map from each module to the modules it depends on (its imports).
/// This is used by the REPL file watcher to cascade-invalidate dependents when
/// a module's source changes.
pub fn build_module_dependency_map(
    project_root: &Path,
    lib_dirs: &[PathBuf],
) -> HashMap<ModuleFullPath, Vec<ModuleFullPath>> {
    let mut map = HashMap::new();
    let prelude_file = match resolve_prelude(project_root, lib_dirs) {
        Some(f) => f,
        None => return map,
    };
    if let Ok(graph) = discover_module_graph(&prelude_file, lib_dirs) {
        for (module_path, node) in &graph.nodes {
            map.insert(module_path.clone(), node.dependencies.clone());
        }
    }
    map
}

/// Load and compile the prelude module into a CompilationSession.
///
/// Discovers the prelude module graph, compiles each module through the
/// per-form pipeline (same path as REPL and batch), and injects an
/// implicit `(import [prelude [*]])` into the "user" module.
///
/// The prelude is NOT special — it is ordinary user code resolved through
/// normal module resolution. The only special behavior is the implicit import.
pub fn load_prelude_into_session(
    project_root: &Path,
    lib_dirs: &[PathBuf],
    session: &mut CompilationSession,
    cache_state: &mut Option<CacheState>,  // None = caching disabled
) -> Result<(), CranelispError> {
    let prelude_file = match resolve_prelude(project_root, lib_dirs) {
        Some(f) => f,
        None => return Ok(()),
    };

    // Discover the prelude module graph.
    let graph = discover_module_graph(&prelude_file, lib_dirs)?;
    let order = toposort(&graph)?;

    // Two-pass approach: first try all cache loads, then compile misses.
    // This ensures all cached function pointers are registered before the
    // batch JIT is created (JIT symbols must be registered at creation time).
    let mut cache_misses: Vec<(ModuleFullPath, Option<String>)> = Vec::new();
    for module_path in &order {
        let node = &graph.nodes[module_path];

        // Compute source hash for cache checking (requires reading the file).
        let source_hash = if cache_state.is_some() {
            let source = read_module_source(node)?;
            Some(cache::hash_source(&source))
        } else {
            None
        };

        // Cache-hit path: try to restore from cache before parsing.
        let mut cache_hit = false;
        if let Some(hash) = source_hash.as_ref() {
            if let Some(cs) = cache_state.as_mut() {
                if try_restore_from_cache(cs, module_path, hash, &node.dependencies, session)? {
                    cache_hit = true;
                    // Re-compile macros from cached modules so the expander
                    // has function pointers for downstream macro expansion
                    // (e.g., user.cl using `str`, `list`, `do`, etc.).
                    recompile_macros_for_cached_module(module_path, node, session)?;
                } else {
                    cs.record_recompiled(module_path);
                }
            }
        }

        if !cache_hit {
            cache_misses.push((module_path.clone(), source_hash));
        }
    }

    // Pass 2: compile cache misses (batch JIT created here with all cached symbols).
    for (module_path, source_hash) in cache_misses {
        let node = &graph.nodes[&module_path];
        let (_source, structure, remaining_sexps) =
            parse_and_extract_module_with_source(&module_path, node)?;

        // Record the source hash for dependency tracking.
        if let (Some(cs), Some(hash)) = (cache_state.as_mut(), &source_hash) {
            cs.source_hashes.insert(module_path.clone(), hash.clone());
        }

        // Set up module context BEFORE processing forms.
        session.tc.set_current_module(module_path.clone());
        if !structure.import_specs.is_empty() {
            session.tc.register_imports(&structure.import_specs)?;
        }
        if !structure.export_specs.is_empty() {
            session.tc.register_exports(&structure.export_specs)?;
        }

        // Process forms (defmacro compilation happens here, needs imports).
        let accumulated = session.process_forms_sequentially(remaining_sexps)?;

        // Build program AST from accumulated sexps.
        let program = cranelisp_frontend::build_program(
            &accumulated,
            &mut session.expander,
        )?;

        if program.is_empty() {
            if let (Some(cs), Some(hash)) = (cache_state.as_mut(), source_hash) {
                // Cache write failures are non-fatal — worst case is no caching.
                let _ = write_module_cache(
                    cs, &module_path, hash, &node.dependencies, &structure, &session.tc,
                    None, None, &session.func_sigs,
                );
            }
            continue;
        }

        // Typecheck (whole-program, handles forward references).
        let check = session.tc.check_program(&program)?;

        // Compile module using batch codegen (direct calls, TCO).
        session.compile_module_batch(&module_path, &program, &check)?;

        // Write cache metadata and .o file after successful compilation.
        // Cache write failures are non-fatal — worst case is no caching.
        if let (Some(cs), Some(hash)) = (cache_state.as_mut(), source_hash) {
            let _ = write_module_cache(
                cs, &module_path, hash, &node.dependencies, &structure, &session.tc,
                Some(&program), Some(&check), &session.func_sigs,
            );
        }
    }

    // Finalize the shared batch JIT (resolves all cross-references).
    session.finalize_batch_jit()?;

    // Inject implicit (import [prelude [*]]) into the "user" module.
    let user_module = ModuleFullPath::from("user");
    session.tc.set_current_module(user_module);

    let prelude_module = ModuleFullPath::from("prelude");
    let import_spec = cranelisp_types::ImportSpec {
        module_path: prelude_module,
        alias: None,
        names: cranelisp_types::ImportNames::Glob,
        span: Span::SYNTHETIC,
    };
    session.tc.register_imports(&[import_spec])?;

    Ok(())
}

/// Inject an implicit `(import [prelude [*]])` into the typechecker's current
/// module, unless the current module IS "prelude" (to avoid self-import).
///
/// Per spec §8.8.1, all non-prelude modules receive this implicit import so
/// that prelude-defined traits and macros are available without explicit import.
fn inject_prelude_import(
    tc: &mut cranelisp_typecheck::TypeChecker,
) -> Result<(), CranelispError> {
    let prelude_path = ModuleFullPath::from("prelude");

    // Don't self-import prelude into itself.
    if tc.current_module_path() == &prelude_path {
        return Ok(());
    }

    // Register the implicit glob import. Duplicate same-source imports are
    // silently deduplicated by insert_imports_detecting_ambiguity, so this
    // is safe to call even if the module already has a prelude import
    // (e.g., "user" which received one from load_prelude).
    let import_spec = cranelisp_types::ImportSpec {
        module_path: prelude_path,
        alias: None,
        names: cranelisp_types::ImportNames::Glob,
        span: Span::SYNTHETIC,
    };
    tc.register_imports(&[import_spec])
}

/// Determine the process exit code from the already-unwrapped inner value.
///
/// The caller is responsible for extracting the inner value from any IO wrapper
/// (via the trampoline) before calling this function. This function receives
/// the unwrapped inner type, not the IO-wrapped type.
///
/// Per spec section 10.6.1:
/// - If the inner type is `Int`, use the integer value as the exit code.
/// - Otherwise, exit code is 0.
pub fn determine_exit_code(value: i64, inner_ty: &Type) -> i32 {
    match inner_ty {
        Type::Int => value as i32,
        _ => 0,
    }
}

/// Compile a multi-file module graph and execute the entry point.
///
/// Convenience wrapper that compiles with caching disabled.
/// Result of compiling a single module within the module graph.
struct SingleModuleResult {
    /// Warnings accumulated during compilation.
    warnings: Vec<Warning>,
    /// If this was the entry module and it has a defn, the entry point name and result type.
    entry_info: Option<(Symbol, Type)>,
}

/// Compile (or restore from cache) a single module within the graph.
///
/// Handles cache-hit restoration, full compilation (parse, typecheck, codegen),
/// and cache-write. Returns warnings and optional entry point info.
fn compile_single_module(
    module_path: &ModuleFullPath,
    node: &ModuleNode,
    is_entry: bool,
    prelude_loaded: bool,
    session: &mut CompilationSession,
    cache_state: &mut Option<CacheState>,
) -> Result<SingleModuleResult, CranelispError> {
    let mut warnings: Vec<Warning> = Vec::new();

    // Compute source hash for cache checking.
    let source_hash = if cache_state.is_some() {
        let source = read_module_source(node)?;
        Some(cache::hash_source(&source))
    } else {
        None
    };

    // Cache-hit path: try to restore from cache before parsing.
    // Note: entry module is never restored from cache — it must
    // always be compiled so its entry point is in the JIT.
    if !is_entry {
        if let Some(hash) = source_hash.as_ref() {
            if let Some(cs) = cache_state.as_mut() {
                if try_restore_from_cache(cs, module_path, hash, &node.dependencies, session)? {
                    // Re-compile macros from cached modules so the expander
                    // has function pointers for downstream macro expansion.
                    recompile_macros_for_cached_module(module_path, node, session)?;
                    // Cache hit — module restored. Inject prelude import
                    // so downstream modules see prelude symbols through this one.
                    if prelude_loaded {
                        session.tc.set_current_module(module_path.clone());
                        inject_prelude_import(&mut session.tc)?;
                    }
                    return Ok(SingleModuleResult { warnings, entry_info: None });
                }
                // Cache miss — fall through to full compilation.
                cs.record_recompiled(module_path);
            }
        }
    } else if let Some(hash) = source_hash.as_ref() {
        if let Some(cs) = cache_state.as_mut() {
            // Entry module: record source hash but always recompile.
            cs.source_hashes.insert(module_path.clone(), hash.clone());
            cs.record_recompiled(module_path);
        }
    }

    // Cache miss: full compilation path.
    let (_source, structure, remaining_sexps) =
        parse_and_extract_module_with_source(module_path, node)?;

    // Record source hash for dependency tracking.
    if let (Some(cs), Some(hash)) = (cache_state.as_mut(), &source_hash) {
        cs.source_hashes.insert(module_path.clone(), hash.clone());
    }

    // Phase 2: Set up module context BEFORE processing forms.
    session.tc.set_current_module(module_path.clone());

    // Inject implicit (import [prelude [*]]) for non-prelude modules (spec §8.8.1).
    if prelude_loaded {
        inject_prelude_import(&mut session.tc)?;
    }

    if !structure.import_specs.is_empty() {
        session.tc.register_imports(&structure.import_specs)?;
    }
    if !structure.export_specs.is_empty() {
        session.tc.register_exports(&structure.export_specs)?;
    }

    // Filter out (platform ...) forms — they were handled during pre-scan.
    let remaining_sexps = filter_platform_forms(remaining_sexps);

    // Phase 3: Process forms (defmacro compilation happens here, needs imports).
    let accumulated = session.process_forms_sequentially(remaining_sexps)?;

    // Phase 4: Build program AST from accumulated sexps.
    let program = cranelisp_frontend::build_program(
        &accumulated,
        &mut session.expander,
    )?;

    if program.is_empty() {
        // Write cache for empty modules (dependency tracking).
        if let (Some(cs), Some(hash)) = (cache_state.as_mut(), source_hash) {
            write_module_cache(
                cs, module_path, hash, &node.dependencies, &structure, &session.tc,
                None, None, &session.func_sigs,
            )?;
        }
        return Ok(SingleModuleResult { warnings, entry_info: None });
    }

    // Phase 5: Typecheck (whole-program, handles forward references).
    let check = session.tc.check_program(&program)?;
    warnings.extend(check.warnings.iter().cloned());

    // Phase 6: Compile module using batch codegen (direct calls, TCO).
    let module_warnings = session.compile_module_batch(module_path, &program, &check)?;
    warnings.extend(module_warnings);

    // Phase 7: Write cache files (.meta.json + .o) after successful compilation.
    if let (Some(cs), Some(hash)) = (cache_state.as_mut(), source_hash) {
        write_module_cache(
            cs, module_path, hash, &node.dependencies, &structure, &session.tc,
            Some(&program), Some(&check), &session.func_sigs,
        )?;
    }

    // Track entry point info.
    let entry_info = if is_entry {
        find_entry_defn(&program).map(|name| {
            let ty = infer_result_type(&program, &check);
            (name, ty)
        })
    } else {
        None
    };

    Ok(SingleModuleResult { warnings, entry_info })
}

/// Used by tests and callers that do not need caching.
pub fn compile_module_graph(
    entry: &Path,
    lib_dirs: &[PathBuf],
) -> Result<CompiledModuleGraph, CranelispError> {
    compile_module_graph_cached(entry, lib_dirs, &CacheConfig::Disabled)
}

/// Compile a multi-file module graph without executing it.
///
/// This is the core compilation pipeline shared by batch mode, cache writing,
/// and linking. It compiles all modules, finalizes the JIT, and flushes
/// the cache, but does NOT execute the entry point.
///
/// Pipeline:
/// 1. Discover module graph from entry file
/// 2. Topological sort (dependencies first)
/// 3. Load prelude (if available)
/// 4. For each module: parse, extract declarations, set up imports,
///    sequential form processing (defmacro interception, expansion),
///    per-form typecheck + codegen via GOT-indirect calling
/// 5. Finalize JIT and flush cache
///
/// The `cache_config` parameter controls module caching. When enabled,
/// the pipeline checks `.cranelisp-cache/` for valid cached metadata
/// before compiling each module, and writes cache entries after successful
/// compilation. See `design/backend/module-caching.md` §8.
fn compile_graph_only(
    entry: &Path,
    lib_dirs: &[PathBuf],
    cache_config: &CacheConfig,
) -> Result<CompiledGraphSession, CranelispError> {
    let graph = discover_module_graph(entry, lib_dirs)?;
    let order = toposort(&graph)?;

    let mut all_warnings: Vec<Warning> = Vec::new();
    let mut session = CompilationSession::new();

    // Initialize cache state if caching is enabled.
    let mut cache_state = cache_config
        .cache_dir()
        .map(|dir| CacheState::new(dir.to_path_buf()));

    // Pre-scan entry module for (platform ...) declarations.
    // Platform DLLs must be loaded before compilation so their function
    // pointers are available as JIT symbols.
    let mut loaded_platforms: Vec<crate::platform::LoadedPlatform> = Vec::new();

    let entry_node = &graph.nodes[&graph.entry];
    let platform_names = scan_for_platform_decls(entry_node)?;
    for (name, span) in &platform_names {
        let (platform, jit_syms) = crate::platform::load_and_register_platform(
            &mut session.tc,
            name,
            &graph.project_root,
            *span,
        )?;
        session.platform_symbols.extend(jit_syms);
        loaded_platforms.push(platform);
    }

    // Load prelude if available (optional — system works without it).
    load_prelude_into_session(
        &graph.project_root,
        &graph.lib_dirs,
        &mut session,
        &mut cache_state,
    )?;

    let mut entry_defn_name: Option<Symbol> = None;
    let mut entry_result_type = Type::Int;

    // Check whether a prelude was loaded so we can inject implicit imports
    // into each module in the graph (spec §8.8.1).
    let prelude_loaded = session.tc.has_module(&ModuleFullPath::from("prelude"));

    // Two-pass approach: first try all cache loads, then compile misses.
    // This ensures all cached function pointers are registered before the
    // batch JIT is created (JIT symbols must be registered at creation time).
    let mut compile_list: Vec<ModuleFullPath> = Vec::new();
    for module_path in &order {
        let is_entry = module_path == &graph.entry;
        let node = &graph.nodes[module_path];

        // Entry module is always compiled (never cached).
        if is_entry {
            // Record source hash for dependency tracking.
            if let Some(cs) = cache_state.as_mut() {
                let source = read_module_source(node)?;
                let hash = cache::hash_source(&source);
                cs.source_hashes.insert(module_path.clone(), hash);
                cs.record_recompiled(module_path);
            }
            compile_list.push(module_path.clone());
            continue;
        }

        // Try cache load for non-entry modules.
        let mut cache_hit = false;
        if let Some(cs) = cache_state.as_mut() {
            let source = read_module_source(node)?;
            let hash = cache::hash_source(&source);
            if try_restore_from_cache(cs, module_path, &hash, &node.dependencies, &mut session)? {
                cache_hit = true;
                // Re-compile macros from cached modules so the expander
                // has function pointers for downstream macro expansion.
                recompile_macros_for_cached_module(module_path, node, &mut session)?;
                if prelude_loaded {
                    session.tc.set_current_module(module_path.clone());
                    inject_prelude_import(&mut session.tc)?;
                }
            } else {
                cs.record_recompiled(module_path);
                cs.source_hashes.insert(module_path.clone(), hash);
            }
        }

        if !cache_hit {
            compile_list.push(module_path.clone());
        }
    }

    // Pass 2: compile cache misses.
    for module_path in &compile_list {
        let is_entry = module_path == &graph.entry;
        let result = compile_single_module(
            module_path,
            &graph.nodes[module_path],
            is_entry,
            prelude_loaded,
            &mut session,
            &mut cache_state,
        )?;
        all_warnings.extend(result.warnings);
        if is_entry {
            if let Some((name, ty)) = result.entry_info {
                // Qualify the entry name with the module path to match the
                // JIT symbol name (all functions are prefixed with their
                // module path in the shared JIT).
                let qualified = Symbol::from(format!(
                    "{}/{}",
                    module_path.as_ref(),
                    name.as_ref()
                ));
                entry_defn_name = Some(qualified);
                entry_result_type = ty;
            }
        }
    }

    // Finalize the shared batch JIT (resolves all cross-references).
    session.finalize_batch_jit()?;

    // Flush the cache manifest to disk.
    if let Some(cs) = &cache_state {
        cs.flush()?;
    }

    Ok(CompiledGraphSession {
        session,
        entry_defn_name,
        entry_result_type,
        warnings: all_warnings,
    })
}

/// Compile a multi-file module graph and execute the entry point.
///
/// Calls `compile_graph_only` to compile, then locates and executes the
/// entry module's `main` function. Batch mode requires a `main` function
/// in the entry module (per repl/spec.md §0.2).
pub fn compile_module_graph_cached(
    entry: &Path,
    lib_dirs: &[PathBuf],
    cache_config: &CacheConfig,
) -> Result<CompiledModuleGraph, CranelispError> {
    let mut compiled = compile_graph_only(entry, lib_dirs, cache_config)?;

    // Execute the entry module's entry point.
    // Per repl/spec.md §0.2, `main` is required in the entry module.
    let name = compiled.entry_defn_name.ok_or_else(|| CranelispError::ModuleError {
        message: "entry module has no `main` function — batch mode requires (defn main [] ...)".into(),
        file: Some(entry.to_path_buf()),
        span: Span::SYNTHETIC,
    })?;

    let entry_ptr = compiled.session.batch_jit_get_ptr(&name, 0)?;
    // SAFETY: compiled code was just generated and finalized by our JIT.
    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(entry_ptr) };
    let raw_value = func();

    let (value, ty) = if compiled.entry_result_type.is_io() {
        let inner_value = cranelisp_runtime::run_io_trampoline(raw_value);
        let inner_type = compiled.entry_result_type.io_inner_type();
        (inner_value, inner_type)
    } else {
        (raw_value, compiled.entry_result_type)
    };

    Ok(CompiledModuleGraph {
        value,
        ty,
        warnings: compiled.warnings,
    })
}

/// Compile a module graph for caching only, without executing.
///
/// Used by the REPL to write cache files for `user.cl` without
/// triggering execution of any `main` function it may contain.
pub fn compile_module_graph_for_cache(
    entry: &Path,
    lib_dirs: &[PathBuf],
    cache_config: &CacheConfig,
) -> Result<(), CranelispError> {
    let _compiled = compile_graph_only(entry, lib_dirs, cache_config)?;
    Ok(())
}

/// Compile a module graph for linking into a standalone executable.
///
/// Same as `compile_module_graph_cached` but does NOT execute the entry module.
/// Instead returns the `.o` file paths and entry module symbol table needed for
/// `validate_main`, `generate_startup_object`, and `link_executable`.
///
/// Caching is always enabled (linking requires `.o` files in the cache).
pub fn compile_for_link(
    entry: &Path,
    lib_dirs: &[PathBuf],
    cache_dir: &Path,
) -> Result<LinkCompileResult, CranelispError> {
    let graph = discover_module_graph(entry, lib_dirs)?;
    let order = toposort(&graph)?;

    let mut all_warnings: Vec<Warning> = Vec::new();
    let mut session = CompilationSession::new();
    let mut cache_state = Some(CacheState::new(cache_dir.to_path_buf()));

    // Pre-scan entry module for (platform ...) declarations.
    let mut loaded_platforms: Vec<crate::platform::LoadedPlatform> = Vec::new();
    let entry_node = &graph.nodes[&graph.entry];
    let platform_names = scan_for_platform_decls(entry_node)?;
    for (name, span) in &platform_names {
        let (platform, jit_syms) = crate::platform::load_and_register_platform(
            &mut session.tc,
            name,
            &graph.project_root,
            *span,
        )?;
        session.platform_symbols.extend(jit_syms);
        loaded_platforms.push(platform);
    }

    // Load prelude if available.
    load_prelude_into_session(
        &graph.project_root,
        &graph.lib_dirs,
        &mut session,
        &mut cache_state,
    )?;

    let prelude_loaded = session.tc.has_module(&ModuleFullPath::from("prelude"));

    // Two-pass: cache loads then compile misses (same as compile_module_graph_cached).
    let mut compile_list: Vec<ModuleFullPath> = Vec::new();
    for module_path in &order {
        let is_entry = module_path == &graph.entry;
        let node = &graph.nodes[module_path];

        if is_entry {
            if let Some(cs) = cache_state.as_mut() {
                let source = read_module_source(node)?;
                let hash = cache::hash_source(&source);
                cs.source_hashes.insert(module_path.clone(), hash);
                cs.record_recompiled(module_path);
            }
            compile_list.push(module_path.clone());
            continue;
        }

        let mut cache_hit = false;
        if let Some(cs) = cache_state.as_mut() {
            let source = read_module_source(node)?;
            let hash = cache::hash_source(&source);
            if try_restore_from_cache(cs, module_path, &hash, &node.dependencies, &mut session)? {
                cache_hit = true;
                // Re-compile macros from cached modules so the expander
                // has function pointers for downstream macro expansion.
                recompile_macros_for_cached_module(module_path, node, &mut session)?;
                if prelude_loaded {
                    session.tc.set_current_module(module_path.clone());
                    inject_prelude_import(&mut session.tc)?;
                }
            } else {
                cs.record_recompiled(module_path);
                cs.source_hashes.insert(module_path.clone(), hash);
            }
        }

        if !cache_hit {
            compile_list.push(module_path.clone());
        }
    }

    // Compile cache misses.
    for module_path in &compile_list {
        let is_entry = module_path == &graph.entry;
        let result = compile_single_module(
            module_path,
            &graph.nodes[module_path],
            is_entry,
            prelude_loaded,
            &mut session,
            &mut cache_state,
        )?;
        all_warnings.extend(result.warnings);
    }

    // Finalize JIT (needed for cache writing).
    session.finalize_batch_jit()?;

    // Flush the cache manifest.
    if let Some(cs) = &cache_state {
        cs.flush()?;
    }

    // Collect .o paths from the cache for all modules in the graph.
    let mut module_o_paths: Vec<PathBuf> = Vec::new();
    for module_path in &order {
        let (_meta_path, o_path) = cache::module_cache_path(cache_dir, module_path);
        if o_path.exists() {
            module_o_paths.push(o_path);
        }
        // Macro-only modules may not have .o files — skip silently.
    }

    // Also collect .o paths from prelude modules (they're in the cache too).
    let prelude_modules = collect_prelude_module_paths(&graph.project_root, lib_dirs);
    for module_path in &prelude_modules {
        let (_meta_path, o_path) = cache::module_cache_path(cache_dir, module_path);
        if o_path.exists() && !module_o_paths.contains(&o_path) {
            module_o_paths.push(o_path);
        }
    }

    // Get the entry module's symbol table for validate_main.
    session.tc.set_current_module(graph.entry.clone());
    let entry_symbols = session.tc.symbol_table().clone();

    // Collect module structures for platform rlib discovery.
    let module_structures: Vec<(ModuleFullPath, cranelisp_types::ModuleStructure)> = graph
        .nodes
        .iter()
        .filter_map(|(mp, node)| {
            let source = std::fs::read_to_string(&node.file_path).ok()?;
            let sexps = cranelisp_frontend::parse(&source).ok()?;
            let (structure, _) = cranelisp_frontend::extract_module_declarations(
                mp.clone(),
                Some(node.file_path.clone()),
                sexps,
            )
            .ok()?;
            Some((mp.clone(), structure))
        })
        .collect();

    Ok(LinkCompileResult {
        module_o_paths,
        entry_symbols,
        module_structures,
        warnings: all_warnings,
    })
}

/// Collect module paths for all prelude modules.
fn collect_prelude_module_paths(
    project_root: &Path,
    lib_dirs: &[PathBuf],
) -> Vec<ModuleFullPath> {
    let prelude_file = match resolve_prelude(project_root, lib_dirs) {
        Some(f) => f,
        None => return Vec::new(),
    };
    match discover_module_graph(&prelude_file, lib_dirs) {
        Ok(graph) => {
            toposort(&graph).unwrap_or_default()
        }
        Err(_) => Vec::new(),
    }
}

/// Scan a module node's source for `(platform name)` declarations.
///
/// Parses the source file and returns all platform declaration names
/// with their spans. These are extracted at the pipeline level (not
/// the frontend's `extract_module_declarations`) to keep platform
/// loading in the integration layer.
fn scan_for_platform_decls(
    node: &ModuleNode,
) -> Result<Vec<(String, Span)>, CranelispError> {
    let source = std::fs::read_to_string(&node.file_path).map_err(|e| {
        CranelispError::ModuleError {
            message: format!("cannot read '{}': {}", node.file_path.display(), e),
            file: Some(node.file_path.clone()),
            span: Span::SYNTHETIC,
        }
    })?;

    let sexps = cranelisp_frontend::parse(&source)?;
    let mut platform_decls = Vec::new();

    for sexp in &sexps {
        if let Some((name, span)) = crate::platform::extract_platform_name(sexp) {
            platform_decls.push((name, span));
        }
    }

    Ok(platform_decls)
}

/// Filter out `(platform ...)` forms from a list of sexps.
///
/// Platform declarations are processed during pre-scan, before the
/// compilation loop. The remaining sexps must not contain them since
/// the AST builder rejects `(platform ...)`.
fn filter_platform_forms(sexps: Vec<Sexp>) -> Vec<Sexp> {
    sexps
        .into_iter()
        .filter(|s| !crate::platform::is_platform_form(s))
        .collect()
}

/// Generate all module-qualified alias names for a function.
///
/// For module path "main.mid.leaf" and function "value", produces:
///   - "mid.leaf/value" (each dot-suffix)
///   - "main.mid.leaf/value" (full path, only for dotted modules)
///   - "leaf/value" (last component, if different from bare name)
///
/// Used by `register_module_aliases` (GOT), `load_cached_object_into_session`
/// (cached symbols), and `accumulate_func_sigs` (batch JIT).
fn generate_module_aliases(mod_str: &str, fn_name: &str) -> Vec<String> {
    let mut aliases = Vec::new();

    // Suffix aliases at every dot boundary: "mid.leaf/value", etc.
    for (idx, _) in mod_str.match_indices('.') {
        let suffix = &mod_str[idx + 1..];
        aliases.push(format!("{}/{}", suffix, fn_name));
    }

    // Full module path alias (only for dotted modules to avoid duplication).
    if mod_str.contains('.') {
        aliases.push(format!("{}/{}", mod_str, fn_name));
    }

    // Last-component alias: "leaf/value".
    let last_component = mod_str.rsplit('.').next().unwrap_or(mod_str);
    let short_qualified = format!("{}/{}", last_component, fn_name);
    if short_qualified != fn_name {
        aliases.push(short_qualified);
    }

    aliases
}

/// Register qualified function name aliases for cross-module resolution.
///
/// After compiling a module, its function signatures need to be available
/// to downstream modules under qualified names (e.g., "util/helper",
/// "main.util/helper" for module "main.util").
fn accumulate_func_sigs(
    module_path: &ModuleFullPath,
    func_signatures: &[(Symbol, usize)],
    all_func_sigs: &mut Vec<(Symbol, usize)>,
) {
    let mod_str: &str = module_path.as_ref();
    for (name, arity) in func_signatures {
        // Push the JIT-visible name (may be module-qualified if there was a
        // collision, or bare if no collision).
        all_func_sigs.push((name.clone(), *arity));

        // Extract the bare function name for alias generation.
        // If the name is already qualified ("module/fn"), extract the fn part.
        let bare_name = if let Some(slash_pos) = name.as_ref().rfind('/') {
            &name.as_ref()[slash_pos + 1..]
        } else {
            name.as_ref()
        };
        for alias in generate_module_aliases(mod_str, bare_name) {
            // Skip aliases that match the primary JIT name (already pushed).
            let alias_sym = Symbol::from(alias.as_str());
            if alias_sym != *name {
                all_func_sigs.push((alias_sym, *arity));
            }
        }
    }
}

/// Find the last zero-arg defn in a program (the entry point).
/// Find the `main` function in a program for batch mode entry point.
///
/// Per repl/spec.md §0.2, `--run` requires a zero-argument `main` function
/// in the entry module.
fn find_entry_defn(program: &Program) -> Option<Symbol> {
    use cranelisp_types::TopLevel;
    program.iter().find_map(|tl| {
        if let TopLevel::Defn(defn) = tl
            && defn.params.is_empty()
            && defn.name.0 == "main"
        {
            return Some(defn.name.clone());
        }
        None
    })
}

/// Check whether a program has any defns or trait impls that need codegen.
fn has_compilable_defns(program: &[cranelisp_types::TopLevel]) -> bool {
    use cranelisp_types::TopLevel;
    program.iter().any(|tl| matches!(tl, TopLevel::Defn(_) | TopLevel::DefnMulti { .. } | TopLevel::TraitImpl(_)))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // --- IO type detection (now on Type methods, tested in cranelisp-types) ---

    // spec: 10-io §10.6.1 — determine_exit_code for Int result
    #[test]
    fn test_determine_exit_code_int() {
        assert_eq!(determine_exit_code(0, &Type::Int), 0);
        assert_eq!(determine_exit_code(42, &Type::Int), 42);
        assert_eq!(determine_exit_code(1, &Type::Int), 1);
    }

    // spec: 10-io §10.6.1 — determine_exit_code for non-Int result
    #[test]
    fn test_determine_exit_code_non_int() {
        assert_eq!(determine_exit_code(42, &Type::String), 0);
        assert_eq!(determine_exit_code(42, &Type::Bool), 0);
    }

    // --- Single-file pipeline tests (existing) ---

    #[test]
    fn test_pipeline_simple_int() {
        let result = compile_and_run("(defn main [] 42)", CompileMode::Batch).unwrap();
        assert_eq!(result.value, 42);
        assert_eq!(result.ty, Type::Int);
    }

    #[test]
    fn test_pipeline_bool_true() {
        let result = compile_and_run("(defn main [] true)", CompileMode::Batch).unwrap();
        assert_eq!(result.value, 1);
        assert_eq!(result.ty, Type::Bool);
    }

    #[test]
    fn test_pipeline_parse_error() {
        let result = compile_and_run("(defn main [] ", CompileMode::Batch);
        assert!(result.is_err());
    }

    #[test]
    fn test_pipeline_interactive_mode() {
        let result = compile_and_run("(defn main [] 42)", CompileMode::Interactive).unwrap();
        assert_eq!(result.value, 42);
    }

    // --- Module graph discovery tests ---

    #[test]
    fn test_discover_single_file() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(defn main [] 42)").unwrap();

        let graph = discover_module_graph(&entry, &[]).unwrap();
        assert_eq!(graph.nodes.len(), 1);
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main")));
        assert_eq!(graph.entry, ModuleFullPath::from("main"));
    }

    #[test]
    fn test_discover_with_submodule() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod util)\n(defn main [] 42)").unwrap();

        // Create sibling module file.
        let util_file = dir.path().join("util.cl");
        std::fs::write(&util_file, "(defn helper [] 1)").unwrap();

        let graph = discover_module_graph(&entry, &[]).unwrap();
        assert_eq!(graph.nodes.len(), 2);
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main")));
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main.util")));
    }

    #[test]
    fn test_discover_child_directory_priority() {
        // Per spec 8.2.5: child directory is searched before sibling.
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("app.cl");
        std::fs::write(&entry, "(mod handler)").unwrap();

        // Create child directory version.
        let child_dir = dir.path().join("app");
        std::fs::create_dir_all(&child_dir).unwrap();
        std::fs::write(child_dir.join("handler.cl"), "(defn handle [] 1)").unwrap();

        // Also create sibling version (should be ignored).
        std::fs::write(dir.path().join("handler.cl"), "(defn handle [] 2)").unwrap();

        let graph = discover_module_graph(&entry, &[]).unwrap();
        let handler_node = &graph.nodes[&ModuleFullPath::from("app.handler")];
        // Should resolve to child directory version.
        assert!(handler_node.file_path.to_str().unwrap().contains("app/handler.cl"));
    }

    #[test]
    fn test_discover_missing_module_error() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod nonexistent)").unwrap();

        let result = discover_module_graph(&entry, &[]);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.message().contains("cannot find module 'nonexistent'"));
    }

    #[test]
    fn test_discover_circular_dependency() {
        let dir = tempfile::tempdir().unwrap();
        let a_file = dir.path().join("a.cl");
        let b_file = dir.path().join("b.cl");

        // a.cl declares mod b, b.cl declares mod a -> cycle.
        // But note: (mod b) in a.cl makes b a submodule of a,
        // and (mod a) in b.cl would look for a submodule of b, not create a cycle
        // in the same way. Let's create the actual cycle structure:
        let a_dir = dir.path().join("a");
        let b_dir = dir.path().join("b");
        std::fs::create_dir_all(&a_dir).unwrap();
        std::fs::create_dir_all(&b_dir).unwrap();

        std::fs::write(&a_file, "(mod b)").unwrap();
        // b is at a/b.cl and declares (mod a) which would look for a/b/a.cl
        // This doesn't create a true cycle as discovered because each path is unique.
        // To get a real cycle we need to be more creative.
        // Actually, cycles are caught in the toposort if they manage to form,
        // or in discover_module_recursive if the same ModuleFullPath is visited twice.
        // Let's test the toposort cycle detection instead.

        // Clean up and just test toposort cycle detection.
        let mut nodes = HashMap::new();
        nodes.insert(
            ModuleFullPath::from("a"),
            ModuleNode {
                path: ModuleFullPath::from("a"),
                file_path: a_file.clone(),
                dependencies: vec![ModuleFullPath::from("b")],
            },
        );
        nodes.insert(
            ModuleFullPath::from("b"),
            ModuleNode {
                path: ModuleFullPath::from("b"),
                file_path: b_file.clone(),
                dependencies: vec![ModuleFullPath::from("a")],
            },
        );
        let graph = ModuleGraph {
            nodes,
            entry: ModuleFullPath::from("a"),
            project_root: dir.path().to_path_buf(),
            lib_dirs: Vec::new(),
        };

        let result = toposort(&graph);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.message().contains("circular dependency"));
    }

    #[test]
    fn test_toposort_order() {
        // c depends on nothing, b depends on c, a depends on b and c.
        let mut nodes = HashMap::new();
        nodes.insert(
            ModuleFullPath::from("a"),
            ModuleNode {
                path: ModuleFullPath::from("a"),
                file_path: PathBuf::from("a.cl"),
                dependencies: vec![
                    ModuleFullPath::from("b"),
                    ModuleFullPath::from("c"),
                ],
            },
        );
        nodes.insert(
            ModuleFullPath::from("b"),
            ModuleNode {
                path: ModuleFullPath::from("b"),
                file_path: PathBuf::from("b.cl"),
                dependencies: vec![ModuleFullPath::from("c")],
            },
        );
        nodes.insert(
            ModuleFullPath::from("c"),
            ModuleNode {
                path: ModuleFullPath::from("c"),
                file_path: PathBuf::from("c.cl"),
                dependencies: vec![],
            },
        );

        let graph = ModuleGraph {
            nodes,
            entry: ModuleFullPath::from("a"),
            project_root: PathBuf::from("."),
            lib_dirs: Vec::new(),
        };

        let order = toposort(&graph).unwrap();
        assert_eq!(order.len(), 3);

        // c must come before b, b must come before a.
        let pos_a = order.iter().position(|p| p == "a").unwrap();
        let pos_b = order.iter().position(|p| p == "b").unwrap();
        let pos_c = order.iter().position(|p| p == "c").unwrap();
        assert!(pos_c < pos_b);
        assert!(pos_b < pos_a);
    }

    #[test]
    fn test_toposort_single_node() {
        let mut nodes = HashMap::new();
        nodes.insert(
            ModuleFullPath::from("main"),
            ModuleNode {
                path: ModuleFullPath::from("main"),
                file_path: PathBuf::from("main.cl"),
                dependencies: vec![],
            },
        );

        let graph = ModuleGraph {
            nodes,
            entry: ModuleFullPath::from("main"),
            project_root: PathBuf::from("."),
            lib_dirs: Vec::new(),
        };

        let order = toposort(&graph).unwrap();
        assert_eq!(order, vec![ModuleFullPath::from("main")]);
    }

    // --- compile_module_graph tests ---

    #[test]
    fn test_compile_single_file_project() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(defn main [] 42)").unwrap();

        let result = compile_module_graph(&entry, &[]).unwrap();
        assert_eq!(result.value, 42);
        assert_eq!(result.ty, Type::Int);
    }

    #[test]
    fn test_compile_file_not_found() {
        let result = compile_module_graph(Path::new("/nonexistent/path/main.cl"), &[]);
        assert!(result.is_err());
    }

    #[test]
    fn test_resolve_sibling_module() {
        let dir = tempfile::tempdir().unwrap();

        // Create entry file that declares a submodule.
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod util)\n(defn main [] 99)").unwrap();

        // Create the sibling module (util.cl).
        let util_file = dir.path().join("util.cl");
        std::fs::write(&util_file, "(defn helper [] 1)").unwrap();

        // Discovery should find both modules.
        let graph = discover_module_graph(&entry, &[]).unwrap();
        assert_eq!(graph.nodes.len(), 2);

        // Toposort should put util before main.
        let order = toposort(&graph).unwrap();
        let pos_main = order.iter().position(|p| p == "main").unwrap();
        let pos_util = order.iter().position(|p| p == "main.util").unwrap();
        assert!(pos_util < pos_main);
    }

    #[test]
    fn test_resolve_lib_module() {
        let dir = tempfile::tempdir().unwrap();

        // Create entry file.
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod helper)\n(defn main [] 1)").unwrap();

        // Create lib/ directory with the module.
        let stdlib_dir = dir.path().join("lib");
        std::fs::create_dir_all(&stdlib_dir).unwrap();
        std::fs::write(stdlib_dir.join("helper.cl"), "(defn help [] 2)").unwrap();

        let graph = discover_module_graph(&entry, &[stdlib_dir.clone()]).unwrap();
        assert_eq!(graph.nodes.len(), 2);
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main.helper")));
    }

    #[test]
    fn test_nested_submodules() {
        let dir = tempfile::tempdir().unwrap();

        // main.cl -> mod a -> a has mod b
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod a)\n(defn main [] 1)").unwrap();

        // a.cl (sibling of main.cl)
        let a_file = dir.path().join("a.cl");
        std::fs::write(&a_file, "(mod b)").unwrap();

        // a/b.cl (child directory of a)
        let a_dir = dir.path().join("a");
        std::fs::create_dir_all(&a_dir).unwrap();
        std::fs::write(a_dir.join("b.cl"), "(defn leaf [] 3)").unwrap();

        let graph = discover_module_graph(&entry, &[]).unwrap();
        assert_eq!(graph.nodes.len(), 3);
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main")));
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main.a")));
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main.a.b")));

        // Toposort: b before a before main.
        let order = toposort(&graph).unwrap();
        let pos_main = order.iter().position(|p| p == "main").unwrap();
        let pos_a = order.iter().position(|p| p == "main.a").unwrap();
        let pos_b = order.iter().position(|p| p == "main.a.b").unwrap();
        assert!(pos_b < pos_a);
        assert!(pos_a < pos_main);
    }

    #[test]
    fn test_cross_module_import_resolution() {
        // This test documents the limitation that compile_module_graph
        // does not yet wire cross-module imports. When a module imports
        // a symbol from another module, the import is not resolved.
        //
        // To fix: after compiling each non-entry module, register its
        // exports so downstream modules can resolve imports against them.
        let dir = tempfile::tempdir().unwrap();

        let entry = dir.path().join("main.cl");
        std::fs::write(
            &entry,
            "(mod util)\n(import [main.util [helper]])\n(defn main [] (helper))",
        )
        .unwrap();

        let util_file = dir.path().join("util.cl");
        std::fs::write(&util_file, "(defn helper [] 42)").unwrap();

        let result = compile_module_graph(&entry, &[]).unwrap();
        assert_eq!(result.value, 42);
    }

    // --- Macro integration tests ---

    // spec: 09-macros.md §9.2 — defmacro in batch pipeline
    #[test]
    fn test_batch_defmacro_identity() {
        // Define a macro and use it in the same file.
        let source = r#"
            (defmacro id [x] x)
            (defn main [] (id 42))
        "#;
        let result = compile_and_run(source, CompileMode::Batch).unwrap();
        assert_eq!(result.value, 42);
    }

    // spec: 09-macros.md §9.4.2 — quasiquote macro in batch pipeline
    #[test]
    fn test_batch_defmacro_quasiquote() {
        let source = r#"
            (defmacro inc1 [x] `(primitives/add-i64 1 ~x))
            (defn main [] (inc1 41))
        "#;
        let result = compile_and_run(source, CompileMode::Batch).unwrap();
        assert_eq!(result.value, 42);
    }

    // spec: 09-macros.md §9.2 — multiple macros, later uses earlier
    #[test]
    fn test_batch_macro_uses_earlier_macro() {
        let source = r#"
            (defmacro id [x] x)
            (defmacro id2 [x] (id x))
            (defn main [] (id2 99))
        "#;
        let result = compile_and_run(source, CompileMode::Batch).unwrap();
        assert_eq!(result.value, 99);
    }

    // spec: 09-macros.md §9.2.6 — multi-clause macro dispatch
    #[test]
    fn test_batch_multi_clause_macro() {
        let source = r#"
            (defmacro pick ([x] x) ([x y] x))
            (defn main [] (pick 77))
        "#;
        let result = compile_and_run(source, CompileMode::Batch).unwrap();
        assert_eq!(result.value, 77);
    }

    // spec: 09-macros.md — no macros: pipeline still works
    #[test]
    fn test_batch_no_macros_unchanged() {
        let source = "(defn main [] (primitives/add-i64 1 2))";
        let result = compile_and_run(source, CompileMode::Batch).unwrap();
        assert_eq!(result.value, 3);
    }

    // spec: 09-macros.md §9.2 — defmacro in module graph pipeline
    #[test]
    fn test_module_graph_defmacro() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(
            &entry,
            "(defmacro id [x] x)\n(defn main [] (id 42))",
        )
        .unwrap();

        let result = compile_module_graph(&entry, &[]).unwrap();
        assert_eq!(result.value, 42);
    }

    // --- Prelude loading tests ---

    // spec: 08-modules.md — prelude loading from lib/
    #[test]
    fn test_prelude_loading_from_lib() {
        let dir = tempfile::tempdir().unwrap();

        // Create lib/prelude.cl with a simple macro.
        let stdlib_dir = dir.path().join("lib");
        std::fs::create_dir_all(&stdlib_dir).unwrap();
        std::fs::write(
            stdlib_dir.join("prelude.cl"),
            "(defmacro id [x] x)",
        )
        .unwrap();

        // Entry file uses the macro from the prelude.
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(defn main [] (id 55))").unwrap();

        let result = compile_module_graph(&entry, &[stdlib_dir.clone()]).unwrap();
        assert_eq!(result.value, 55);
    }

    // spec: 08-modules.md — system works without prelude
    #[test]
    fn test_no_prelude_still_works() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(defn main [] 42)").unwrap();

        // No lib/ directory, no prelude.
        let result = compile_module_graph(&entry, &[]).unwrap();
        assert_eq!(result.value, 42);
    }

    // spec: 08-modules.md — prelude resolution: project root overrides lib/
    #[test]
    fn test_prelude_project_root_overrides_lib() {
        let dir = tempfile::tempdir().unwrap();

        // Create lib/prelude.cl with one macro.
        let stdlib_dir = dir.path().join("lib");
        std::fs::create_dir_all(&stdlib_dir).unwrap();
        std::fs::write(
            stdlib_dir.join("prelude.cl"),
            "(defmacro id [x] `(add-i64 100 ~x))",
        )
        .unwrap();

        // Create project root prelude.cl with different behavior.
        std::fs::write(
            dir.path().join("prelude.cl"),
            "(defmacro id [x] x)",
        )
        .unwrap();

        // Entry file uses the macro — should get the project root version.
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(defn main [] (id 42))").unwrap();

        let result = compile_module_graph(&entry, &[stdlib_dir.clone()]).unwrap();
        // Project root prelude: (id 42) -> 42
        // Lib prelude: (id 42) -> (add-i64 100 42) -> 142
        assert_eq!(result.value, 42);
    }

    // spec: 08-modules.md — resolve_prelude returns None when no prelude exists
    #[test]
    fn test_resolve_prelude_none() {
        let dir = tempfile::tempdir().unwrap();
        let result = resolve_prelude(dir.path(), &[]);
        assert!(result.is_none());
    }

    // spec: 08-modules.md — resolve_prelude finds lib/ prelude
    #[test]
    fn test_resolve_prelude_from_lib() {
        let dir = tempfile::tempdir().unwrap();
        let stdlib_dir = dir.path().join("lib");
        std::fs::create_dir_all(&stdlib_dir).unwrap();
        std::fs::write(stdlib_dir.join("prelude.cl"), "").unwrap();

        let result = resolve_prelude(dir.path(), &[stdlib_dir.clone()]);
        assert!(result.is_some());
        assert!(result.unwrap().ends_with("prelude.cl"));
    }

    // spec: 08-modules.md — resolve_prelude prefers project root
    #[test]
    fn test_resolve_prelude_project_root_priority() {
        let dir = tempfile::tempdir().unwrap();
        let stdlib_dir = dir.path().join("lib");
        std::fs::create_dir_all(&stdlib_dir).unwrap();
        std::fs::write(stdlib_dir.join("prelude.cl"), "").unwrap();
        std::fs::write(dir.path().join("prelude.cl"), "").unwrap();

        let result = resolve_prelude(dir.path(), &[stdlib_dir.clone()]);
        assert!(result.is_some());
        // Should be the project root version, not lib/.
        let path = result.unwrap();
        assert!(!path.to_str().unwrap().contains("lib"));
    }

    // --- assemble_lib_dirs tests ---

    // spec: 08-modules.md §8.11.2 — fallback to {project_root}/stdlib/
    #[test]
    fn test_assemble_lib_dirs_fallback_stdlib() {
        // When CRANELISP_LIB is not set, falls back to {project_root}/stdlib/.
        let dir = tempfile::tempdir().unwrap();
        let stdlib = dir.path().join("stdlib");
        std::fs::create_dir_all(&stdlib).unwrap();

        // Temporarily remove CRANELISP_LIB if it is set.
        // SAFETY: Test-only; env var manipulation is not thread-safe but
        // acceptable in unit tests.
        let saved = std::env::var("CRANELISP_LIB").ok();
        unsafe { std::env::remove_var("CRANELISP_LIB"); }

        let dirs = assemble_lib_dirs(dir.path());

        // Restore.
        if let Some(val) = saved {
            unsafe { std::env::set_var("CRANELISP_LIB", val); }
        }

        assert_eq!(dirs.len(), 1);
        assert_eq!(dirs[0], stdlib);
    }

    // spec: 08-modules.md §8.11.2 — no stdlib dir, no env var -> empty
    #[test]
    fn test_assemble_lib_dirs_empty_fallback() {
        let dir = tempfile::tempdir().unwrap();
        // No stdlib/ directory exists.

        // SAFETY: Test-only; env var manipulation is not thread-safe.
        let saved = std::env::var("CRANELISP_LIB").ok();
        unsafe { std::env::remove_var("CRANELISP_LIB"); }

        let dirs = assemble_lib_dirs(dir.path());

        if let Some(val) = saved {
            unsafe { std::env::set_var("CRANELISP_LIB", val); }
        }

        assert!(dirs.is_empty());
    }

    // spec: 08-modules.md §8.11.2 — CRANELISP_LIB overrides fallback
    #[test]
    fn test_assemble_lib_dirs_env_var() {
        let dir = tempfile::tempdir().unwrap();
        let lib_a = dir.path().join("lib_a");
        let lib_b = dir.path().join("lib_b");
        std::fs::create_dir_all(&lib_a).unwrap();
        std::fs::create_dir_all(&lib_b).unwrap();

        // Also create stdlib/ — should be IGNORED when CRANELISP_LIB is set.
        let stdlib = dir.path().join("stdlib");
        std::fs::create_dir_all(&stdlib).unwrap();

        // SAFETY: Test-only; env var manipulation is not thread-safe.
        let saved = std::env::var("CRANELISP_LIB").ok();
        let env_val = format!("{}:{}", lib_a.display(), lib_b.display());
        unsafe { std::env::set_var("CRANELISP_LIB", &env_val); }

        let dirs = assemble_lib_dirs(dir.path());

        // Restore.
        if let Some(val) = saved {
            unsafe { std::env::set_var("CRANELISP_LIB", val); }
        } else {
            unsafe { std::env::remove_var("CRANELISP_LIB"); }
        }

        assert_eq!(dirs.len(), 2);
        assert_eq!(dirs[0], lib_a);
        assert_eq!(dirs[1], lib_b);
    }

    // spec: 08-modules.md §8.11.2 — CRANELISP_LIB empty string -> no dirs
    #[test]
    fn test_assemble_lib_dirs_env_var_empty() {
        let dir = tempfile::tempdir().unwrap();
        // Create stdlib/ — should be IGNORED when CRANELISP_LIB is set (even empty).
        let stdlib = dir.path().join("stdlib");
        std::fs::create_dir_all(&stdlib).unwrap();

        // SAFETY: Test-only; env var manipulation is not thread-safe.
        let saved = std::env::var("CRANELISP_LIB").ok();
        unsafe { std::env::set_var("CRANELISP_LIB", ""); }

        let dirs = assemble_lib_dirs(dir.path());

        if let Some(val) = saved {
            unsafe { std::env::set_var("CRANELISP_LIB", val); }
        } else {
            unsafe { std::env::remove_var("CRANELISP_LIB"); }
        }

        assert!(dirs.is_empty());
    }

    // spec: 08-modules.md §8.11.2 — module found via CRANELISP_LIB
    #[test]
    fn test_module_resolution_via_cranelisp_lib() {
        let dir = tempfile::tempdir().unwrap();

        // Create entry file.
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod helper)\n(defn main [] 1)").unwrap();

        // Create a separate lib directory with the module.
        let lib_dir = dir.path().join("mylibs");
        std::fs::create_dir_all(&lib_dir).unwrap();
        std::fs::write(lib_dir.join("helper.cl"), "(defn help [] 2)").unwrap();

        // Pass lib_dir explicitly (same as what assemble_lib_dirs would produce).
        let graph = discover_module_graph(&entry, &[lib_dir]).unwrap();
        assert_eq!(graph.nodes.len(), 2);
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main.helper")));
    }

    // spec: 08-modules.md §8.11.2 — multiple lib dirs, first match wins
    #[test]
    fn test_multiple_lib_dirs_first_wins() {
        let dir = tempfile::tempdir().unwrap();

        // Create entry file that uses a macro from prelude.
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod helper)\n(defn main [] (helper/val))").unwrap();

        // Two lib directories with the same module name.
        let lib_first = dir.path().join("first");
        let lib_second = dir.path().join("second");
        std::fs::create_dir_all(&lib_first).unwrap();
        std::fs::create_dir_all(&lib_second).unwrap();
        std::fs::write(lib_first.join("helper.cl"), "(defn val [] 100)").unwrap();
        std::fs::write(lib_second.join("helper.cl"), "(defn val [] 200)").unwrap();

        // First lib dir should win.
        let result = compile_module_graph(&entry, &[lib_first, lib_second]).unwrap();
        assert_eq!(result.value, 100, "first lib dir should take precedence");
    }
}
