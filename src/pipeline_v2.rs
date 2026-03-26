// Pipeline v2: unified compilation pipeline.
//
// `compile_unit()` is the single entry point for all compilation:
// batch programs, REPL forms, and module loading all flow through
// the same stages with the same types. Mode differences are expressed
// via `CompileContext` parameters.
//
// Stages:
//   1. Parse:       &str -> Vec<Sexp>
//   2. Extract:     Vec<Sexp> -> (ModuleStructure, Vec<Sexp>)
//   2b. Recursive module loading for unresolved imports
//   2c. Prelude import injection + register imports/exports
//   2d. Filter platform forms
//   3. Expand:      Vec<Sexp> -> Vec<Sexp>  (defmacro interception + macro expansion)
//   4. Build AST:   Vec<Sexp> -> Vec<TopLevel>
//   4b. Bind chain analysis (auto IO scheduling)
//   5. Typecheck:   Vec<TopLevel> -> CheckResult  (unified multi-pass)
//   6. Codegen:     TopLevel + CheckResult -> JIT (mode-dependent)
//   7. Execute:     call entry fn -> i64          (mode-dependent)

use std::path::PathBuf;

use cranelisp_types::{
    CheckResult, CodegenTarget, CompileContext, CompileMode, CranelispError, ModuleFullPath,
    ModuleStrategy, Span, Type, Warning,
};

use crate::pipeline::CompilationSession;

// ---------------------------------------------------------------------------
// Result types
// ---------------------------------------------------------------------------

/// Result of compiling a unit through stages 1-5 of the v2 pipeline.
///
/// Contains the typechecked program and module structure, ready for
/// codegen via `codegen_and_execute()`. Does NOT contain execution
/// results — those come from `CodegenResult`.
pub struct CompileUnitResult {
    /// The built program (Vec<TopLevel>) from stage 4.
    pub program: Vec<cranelisp_types::TopLevel>,

    /// Module structure extracted at stage 2 (imports, exports, submodules).
    pub module_structure: cranelisp_types::ModuleStructure,

    /// The typecheck result (method resolutions, expr_types, display info, etc.).
    /// Needed by callers for display formatting and introspection.
    pub check_result: CheckResult,

    /// Source text that was compiled. Needed by `codegen_and_execute()`
    /// for background cache writes.
    pub source: String,

    /// All warnings accumulated during stages 1-5.
    pub warnings: Vec<Warning>,
}

/// Result of codegen + execution (stages 6-7).
///
/// Produced by `codegen_and_execute()` after compiling and optionally
/// executing the program from a `CompileUnitResult`.
pub struct CodegenResult {
    /// If execution occurred, the raw i64 result value.
    /// None when the unit was a module load (no execution) or contained
    /// only type/trait definitions with no entry point.
    pub value: Option<i64>,

    /// Inferred type of the executed expression or entry function's return.
    /// None when no execution occurred.
    pub result_type: Option<Type>,

    /// Warnings accumulated during codegen.
    pub warnings: Vec<Warning>,
}

/// Construct an empty `CheckResult` for modules with no compilable forms.
fn empty_check_result() -> CheckResult {
    CheckResult {
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

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Compile a unit of source through the unified v2 pipeline.
///
/// Takes source text (`&str`) and a `CompileContext` that specifies the
/// target module, integration strategy, and codegen mode. Owns all seven
/// pipeline stages from parse through execute.
///
/// # Pipeline stages
///
/// 1. **Parse** — `cranelisp_frontend::parse(source)` → `Vec<Sexp>`
/// 2. **Extract** — `extract_module_declarations()` → `(ModuleStructure, Vec<Sexp>)`.
///    Registers imports/exports. Imports of uncompiled modules trigger
///    recursive `compile_unit()` calls via `session.lib_dirs`.
/// 3. **Expand** — `process_forms_sequentially()`: defmacro interception,
///    macro expansion, begin-flattening → `Vec<Sexp>`
/// 4. **Build AST** — `build_program()` → `Vec<TopLevel>`
/// 4b. **Bind chain analysis** — auto IO scheduling between build and typecheck
/// 5. **Typecheck** — `TypeChecker::check()` → `CheckResult`
/// 6. **Codegen** — mode-dependent: batch (direct calls) or interactive (GOT-indirect)
/// 7. **Execute** — mode-dependent: call entry fn, or return for display
///
/// # Errors
///
/// Returns `CranelispError` for parse, type, or codegen errors.
/// Non-fatal diagnostics are accumulated in `CompileUnitResult::warnings`.
pub fn compile_unit(
    session: &mut CompilationSession,
    source: &str,
    ctx: &CompileContext,
) -> Result<CompileUnitResult, CranelispError> {
    // Cycle detection: check if this module is already on the compile stack.
    check_cycle(session, &ctx.module)?;
    session.compile_stack.push(ctx.module.clone());

    let result = compile_unit_inner(session, source, ctx);

    // Always pop the compile stack, even on error.
    session.compile_stack.pop();

    result
}

/// Inner implementation of `compile_unit()`, separated so the compile_stack
/// pop happens in the outer function regardless of success/failure.
fn compile_unit_inner(
    session: &mut CompilationSession,
    source: &str,
    ctx: &CompileContext,
) -> Result<CompileUnitResult, CranelispError> {
    // Stage 1: Parse source text into sexps.
    let sexps = cranelisp_frontend::parse(source)?;

    // Stage 2: Extract module declarations (mod, import, export, platform).
    let (structure, remaining) = cranelisp_frontend::extract_module_declarations(
        ctx.module.clone(),
        None,
        sexps,
    )?;

    // Stage 2b: Recursive module loading for unresolved imports.
    load_dependencies(session, &structure.import_specs, ctx.compile_mode, ctx.codegen_target)?;

    // Stage 2c: Prelude import injection + register imports/exports.
    // Set the current module BEFORE registering imports so that
    // inject_prelude_import and register_imports target the correct module.
    // This is needed when compile_unit is called recursively for a dependency
    // (e.g., loading num.int from REPL context where current_module is "user").
    session.tc.set_current_module(ctx.module.clone());

    let prelude_path = ModuleFullPath::from("prelude");
    if session.tc.has_module(&prelude_path) && ctx.module != prelude_path {
        crate::pipeline::inject_prelude_import(&mut session.tc)?;
    }
    if !structure.import_specs.is_empty() {
        session.tc.register_imports(&structure.import_specs)?;
    }
    if !structure.export_specs.is_empty() {
        session.tc.register_exports(&structure.export_specs)?;
    }

    // Stage 2d: Filter platform forms from the remaining sexps.
    // Only filter when platform loading has been configured (non-empty
    // platform_symbols). In test mode (compile_and_run with no platform
    // setup), platform forms flow through to the AST builder where they
    // produce proper error messages.
    let remaining = if !session.platform_symbols.is_empty() {
        crate::pipeline::filter_platform_forms(remaining)
    } else {
        remaining
    };

    // Stage 3: Expand (defmacro interception + macro expansion + begin-flatten).
    let accumulated = session.process_forms_sequentially(remaining)?;

    // Handle empty programs (type/trait-only modules with no remaining forms
    // after extraction and expansion — all forms were module declarations
    // or defmacros).
    if accumulated.is_empty() {
        return Ok(CompileUnitResult {
            program: Vec::new(),
            module_structure: structure,
            check_result: empty_check_result(),
            source: source.to_string(),
            warnings: Vec::new(),
        });
    }

    // Stage 4: Build AST from expanded sexps.
    let mut program = cranelisp_frontend::build_program(&accumulated, &mut session.expander)?;

    // Stage 4b: Bind chain analysis (auto IO scheduling).
    if !session.scheduling_registry.is_empty()
        && std::env::var("CRANELISP_NO_IO_SCHEDULE").is_err()
    {
        crate::pipeline::apply_bind_chain_analysis(&mut program, &session.scheduling_registry);
    }

    // Stage 5: Unified multi-pass typecheck.
    // Always use Additive strategy for check() because compile_unit_inner
    // has already handled module setup: set_current_module, prelude injection,
    // and import registration (stages 2b-2c). Using Replace here would clear
    // those registrations. Module state clearing for file reloads is handled
    // by the caller (e.g., reload_single_module clears before compile_unit).
    let check_ctx = if ctx.strategy == ModuleStrategy::Replace {
        CompileContext {
            module: ctx.module.clone(),
            strategy: ModuleStrategy::Additive,
            compile_mode: ctx.compile_mode,
            codegen_target: ctx.codegen_target,
        }
    } else {
        ctx.clone()
    };
    let check_result = session.tc.check(&program, &check_ctx)?;

    let all_warnings: Vec<Warning> = check_result.warnings.clone();

    Ok(CompileUnitResult {
        program,
        module_structure: structure,
        check_result,
        source: source.to_string(),
        warnings: all_warnings,
    })
}

// ---------------------------------------------------------------------------
// Codegen + execute (stages 6-7)
// ---------------------------------------------------------------------------

/// Execute codegen and optional execution for a compiled unit.
///
/// Takes a `CompileUnitResult` from `compile_unit()` (stages 1-5) and
/// performs stages 6-7: codegen dispatch, module alias registration,
/// background cache write, module structure recording, and func_sigs
/// accumulation.
///
/// This function borrows `CompileUnitResult` — it does not consume it,
/// so callers can inspect `check_result` and `warnings` afterward.
pub fn codegen_and_execute(
    session: &mut CompilationSession,
    unit_result: &CompileUnitResult,
    ctx: &CompileContext,
) -> Result<CodegenResult, CranelispError> {
    // Early return for empty programs (no codegen needed).
    if unit_result.program.is_empty() {
        return Ok(CodegenResult {
            value: None,
            result_type: None,
            warnings: Vec::new(),
        });
    }

    // Snapshot pre-existing GOT entries so that register_module_aliases
    // only aliases new entries from this module (not all entries from
    // previously loaded modules — that causes exponential alias growth).
    let pre_existing: std::collections::HashSet<cranelisp_types::Symbol> = session
        .got_state
        .def_codegen
        .keys()
        .cloned()
        .collect();

    let mut codegen_warnings: Vec<Warning> = Vec::new();

    // Stages 6-7: Codegen and execute, mode-dependent.
    let (value, result_type) = match ctx.compile_mode {
        CompileMode::Batch => {
            compile_and_execute_batch(
                &unit_result.program,
                &unit_result.check_result,
                &mut codegen_warnings,
            )?
        }
        CompileMode::Interactive => {
            compile_and_execute_interactive(
                session,
                &unit_result.program,
                &unit_result.check_result,
                &mut codegen_warnings,
            )?
        }
        CompileMode::Release => {
            return Err(CranelispError::CodegenError {
                message: "Release compile mode not yet implemented".into(),
                span: Span::SYNTHETIC,
            });
        }
    };

    // Register module aliases after successful Interactive-mode compilation.
    if ctx.compile_mode == CompileMode::Interactive {
        session.register_module_aliases_filtered(&ctx.module, Some(&pre_existing));
    }

    // Stage 6b: Background .o + .meta.json write (JitAndCache only).
    if ctx.codegen_target == CodegenTarget::JitAndCache {
        queue_background_cache_write(
            session,
            &unit_result.source,
            &ctx.module,
            &unit_result.module_structure,
            &unit_result.program,
            &unit_result.check_result,
        );
    }

    // Record module structure for --link (both targets).
    session
        .compiled_module_structures
        .push((ctx.module.clone(), unit_result.module_structure.clone()));

    // Accumulate cross-module func_sigs from this module's definitions.
    accumulate_func_sigs_from_program(
        &ctx.module,
        &unit_result.program,
        &unit_result.check_result,
        &mut session.cross_module_func_sigs,
    );

    Ok(CodegenResult {
        value,
        result_type,
        warnings: codegen_warnings,
    })
}

// ---------------------------------------------------------------------------
// Cycle detection
// ---------------------------------------------------------------------------

/// Check if a module is already on the compile stack (circular dependency).
fn check_cycle(
    session: &CompilationSession,
    module: &ModuleFullPath,
) -> Result<(), CranelispError> {
    if session.compile_stack.contains(module) {
        let cycle: Vec<String> = session
            .compile_stack
            .iter()
            .map(|m| m.to_string())
            .collect();
        return Err(CranelispError::ModuleError {
            message: format!(
                "circular dependency detected: {} -> {}",
                cycle.join(" -> "),
                module
            ),
            file: None,
            span: Span::SYNTHETIC,
        });
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Recursive module loading
// ---------------------------------------------------------------------------

/// Load all uncompiled dependencies for a module's import list.
///
/// For each import, if the module is not yet compiled, resolve its source
/// file via `session.lib_dirs`, read it, and compile it recursively via
/// `compile_unit()`. If lib_dirs is empty (test mode), unresolved imports
/// are silently skipped — they will fail during typecheck with a proper
/// "unresolved symbol" error.
fn load_dependencies(
    session: &mut CompilationSession,
    import_specs: &[cranelisp_types::ImportSpec],
    compile_mode: CompileMode,
    codegen_target: CodegenTarget,
) -> Result<(), CranelispError> {
    for spec in import_specs {
        let dep_module = &spec.module_path;

        // Skip if already compiled or is a builtin module.
        if session.tc.has_module(dep_module) {
            continue;
        }

        // Try to resolve the module source file.
        if let Some(dep_source_path) = resolve_module_path(dep_module, &session.lib_dirs) {
            let dep_source =
                std::fs::read_to_string(&dep_source_path).map_err(|e| {
                    CranelispError::ModuleError {
                        message: format!(
                            "cannot read '{}': {}",
                            dep_source_path.display(),
                            e
                        ),
                        file: Some(dep_source_path.clone()),
                        span: Span::SYNTHETIC,
                    }
                })?;

            let dep_ctx = CompileContext {
                module: dep_module.clone(),
                strategy: ModuleStrategy::Replace,
                compile_mode,
                codegen_target,
            };

            // Recursive call — cycle detection happens inside compile_unit().
            let unit_result = compile_unit(session, &dep_source, &dep_ctx)?;
            codegen_and_execute(session, &unit_result, &dep_ctx)?;
        }
        // If resolve returns None: import will fail during typecheck
        // (unresolved symbol). This is the test-mode path when lib_dirs is empty.
    }
    Ok(())
}

/// Resolve a dotted module path to a filesystem path.
///
/// Converts "core.option" → "core/option.cl" and searches each directory
/// in `lib_dirs`. Returns None if the module cannot be found.
///
/// Public alias for use by callers that need to resolve module files
/// outside of compile_unit() (e.g., try_restore_user_module).
pub fn resolve_module_file(
    module: &ModuleFullPath,
    lib_dirs: &[PathBuf],
) -> Option<PathBuf> {
    resolve_module_path(module, lib_dirs)
}

/// Resolve a dotted module path to a filesystem path.
///
/// Converts "core.option" → "core/option.cl" and searches each directory
/// in `lib_dirs`. Returns None if the module cannot be found.
fn resolve_module_path(
    module: &ModuleFullPath,
    lib_dirs: &[PathBuf],
) -> Option<PathBuf> {
    // Convert dotted module path to relative file path: "core.option" → "core/option.cl"
    let relative = format!("{}.cl", module.as_ref().replace('.', "/"));

    for dir in lib_dirs {
        let candidate = dir.join(&relative);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Batch mode: whole-program codegen with direct calls
// ---------------------------------------------------------------------------

/// Compile and execute in batch mode (direct calls, whole-program).
///
/// Returns `(Option<value>, Option<result_type>)`.
fn compile_and_execute_batch(
    program: &cranelisp_types::Program,
    check: &CheckResult,
    warnings: &mut Vec<Warning>,
) -> Result<(Option<i64>, Option<Type>), CranelispError> {
    let compiled = cranelisp_backend::compile_program(program, check, CompileMode::Batch)?;
    warnings.extend(compiled.warnings.iter().cloned());

    // Determine the result type from the last zero-arg defn.
    let result_type = infer_batch_result_type(program, check);

    // SAFETY: compiled code was just generated and finalized by our JIT.
    let value = unsafe { compiled.execute()? };

    Ok((Some(value), Some(result_type)))
}

// ---------------------------------------------------------------------------
// Interactive mode: GOT-indirect per-defn compilation
// ---------------------------------------------------------------------------

/// Compile and execute in interactive mode (GOT-indirect calls).
///
/// Compiles definitions via the session's GOT state and compiles/executes
/// any bare expressions.
///
/// Returns `(Option<value>, Option<result_type>)`.
fn compile_and_execute_interactive(
    session: &mut CompilationSession,
    program: &cranelisp_types::Program,
    check: &CheckResult,
    warnings: &mut Vec<Warning>,
) -> Result<(Option<i64>, Option<Type>), CranelispError> {
    use cranelisp_types::TopLevel;

    // Separate expressions from definitions. `compile_checked_program`
    // handles Defn/TraitImpl/TypeDef/TraitDecl but skips Expr.
    let has_expr = program.iter().any(|tl| matches!(tl, TopLevel::Expr(_)));

    // Clear any stale runtime error before executing JIT code.
    let _ = cranelisp_runtime::panic::take_runtime_error();

    // Compile definitions first (GOT registration, mono defns, etc.).
    let form_result = session.compile_checked_program(program, check)?;

    // Check for runtime panics (e.g., checked division by zero in zero-arg defns).
    check_runtime_panic()?;

    if let Some(ref result) = form_result {
        warnings.extend(result.warnings.iter().cloned());
    }

    // If there are bare expressions, compile and execute them.
    if has_expr {
        let (value, ty) = compile_and_execute_expr(session, program, check)?;
        // Check for runtime panics from expression execution.
        check_runtime_panic()?;
        return Ok((Some(value), Some(ty)));
    }

    let value = form_result.as_ref().map(|r| r.value);
    let result_type = form_result.map(|r| r.ty);
    Ok((value, result_type))
}

/// Compile and execute a bare expression in interactive mode.
///
/// Finds the last `TopLevel::Expr` in the program, compiles it via
/// `compile_expr_with_got_and_symbols`, and executes it.
fn compile_and_execute_expr(
    session: &mut CompilationSession,
    program: &cranelisp_types::Program,
    check: &CheckResult,
) -> Result<(i64, Type), CranelispError> {
    use cranelisp_types::TopLevel;

    // Find the last expression in the program.
    let expr = program.iter().rev().find_map(|tl| {
        if let TopLevel::Expr(e) = tl { Some(e) } else { None }
    }).ok_or_else(|| CranelispError::CodegenError {
        message: "no expression found in program".into(),
        span: Span::SYNTHETIC,
    })?;

    // Determine the result type from display info or expr_types.
    let ty = check.display.as_ref()
        .map(|d| d.ty.clone())
        .or_else(|| check.expr_types.get(&expr.span()).cloned())
        .unwrap_or(Type::Int);

    if session.traced_fns.is_empty() {
        // Normal (non-trace) path.
        let extra_syms: Vec<(&str, *const u8)> = session.platform_symbols
            .iter()
            .map(|(name, ptr)| (name.as_str(), *ptr))
            .collect();

        let compiled = cranelisp_backend::compile_expr_with_got_and_symbols(
            expr,
            check,
            CompileMode::Interactive,
            Some(&mut session.got_state),
            &extra_syms,
        )?;

        // SAFETY: compiled code was just generated and finalized by our JIT.
        let value = unsafe { compiled.execute() };
        Ok((value, ty))
    } else {
        // Trace-aware path.
        let value = compile_and_execute_expr_with_trace(session, expr, check)?;
        Ok((value, ty))
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Determine the result type from the last zero-arg function in a batch program.
///
/// Mirrors the backend's entry_fn selection: last zero-arg defn.
fn infer_batch_result_type(
    program: &cranelisp_types::Program,
    check: &CheckResult,
) -> Type {
    use cranelisp_types::TopLevel;

    let last_nullary = program.iter().rev().find_map(|tl| match tl {
        TopLevel::Defn(defn) if !defn.is_multi_sig() && defn.params().is_empty() => Some(defn),
        _ => None,
    });

    if let Some(defn) = last_nullary {
        if let Some(ty) = check.expr_types.get(&defn.body().span()) {
            return ty.clone();
        }
    }

    // Fallback: Int (convention for unknown result types).
    Type::Int
}

/// Check if a runtime panic was signaled during JIT execution.
///
/// Runtime panics (e.g., checked division by zero) are stored in a thread-local
/// rather than Rust-panicking (spec §12.7.4.1). This function checks and clears
/// the error, converting it to a CranelispError.
fn check_runtime_panic() -> Result<(), CranelispError> {
    if let Some(message) = cranelisp_runtime::panic::take_runtime_error() {
        Err(CranelispError::CodegenError {
            message,
            span: Span::SYNTHETIC,
        })
    } else {
        Ok(())
    }
}

/// Compile and execute an expression with trace support.
///
/// Sets traced_fns on the compile context so that trace forms
/// can generate GOT-swap wrappers. The JIT is kept alive in the session's
/// jit_modules so wrapper code pointers remain valid.
fn compile_and_execute_expr_with_trace(
    session: &mut CompilationSession,
    expr: &cranelisp_types::Expr,
    check: &CheckResult,
) -> Result<i64, CranelispError> {
    use cranelisp_types::{Defn, DefnVariant, Symbol, Visibility};
    use std::collections::HashMap;

    let mut extra_syms: Vec<(&str, *const u8)> = session.platform_symbols
        .iter()
        .map(|(name, ptr)| (name.as_str(), *ptr))
        .collect();
    for (name, ptr) in &session.trace_extra_symbols {
        extra_syms.push((name.as_str(), *ptr));
    }

    let mut jit = cranelisp_backend::jit::Jit::new_with_symbols(&extra_syms)?;
    jit.declare_intrinsics()?;

    let wrapper_name = Symbol::from("__repl_expr__");
    let wrapper_defn = Defn {
        name: wrapper_name.clone(),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            param_annotations: vec![],
            body: expr.clone(),
            span: expr.span(),
        }],
        visibility: Visibility::Public,
        span: expr.span(),
    };

    let func_ids = jit.declare_functions(&[&wrapper_defn])?;

    let mut got_slots: HashMap<Symbol, usize> = HashMap::new();
    let mut func_arities: HashMap<Symbol, usize> = HashMap::new();
    for (name, dc) in &session.got_state.def_codegen {
        if let Some(slot) = dc.got_slot {
            got_slots.insert(name.clone(), slot);
        }
        if let Some(pc) = dc.param_count {
            func_arities.insert(name.clone(), pc);
        }
    }
    let got_base = session.got_state.got_base_ptr() as i64;

    let mut compile_ctx = jit.build_compile_context(
        check,
        CompileMode::Interactive,
        &func_ids,
        &func_arities,
        Some(&got_slots),
        Some(got_base),
        None,
    );

    compile_ctx.traced_fns = Some(&session.traced_fns);

    jit.compile_defn(&wrapper_defn, compile_ctx)?;
    let code_ptr = jit.finalize_and_get_ptr(&wrapper_name, 0)?;

    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
    let value = func();

    session.jit_modules.push(jit);

    Ok(value)
}

// ---------------------------------------------------------------------------
// Batch mode: run a file via compile_unit()
// ---------------------------------------------------------------------------

/// Run a batch program through the v2 pipeline (compile_unit for everything).
///
/// All compilation — prelude, dependencies, and entry file — goes through
/// `compile_unit()`. No v1 batch paths are used.
///
/// # Steps
/// 1. Canonicalize entry path, derive module name
/// 2. Create session, set lib_dirs
/// 3. Pre-scan entry file for platform declarations
/// 4. Load prelude via compile_unit
/// 5. Load entry file via compile_unit
/// 6. Verify `main` exists, handle IO trampoline
/// 7. Return CompiledModuleGraph
pub fn run_batch_v2(
    entry: &std::path::Path,
    lib_dirs: &[PathBuf],
) -> Result<crate::pipeline::CompiledModuleGraph, CranelispError> {
    use cranelisp_types::Symbol;

    // Step 1: Canonicalize entry path, derive module name from file stem.
    let entry_path = entry.canonicalize().map_err(|e| CranelispError::ModuleError {
        message: format!("cannot canonicalize '{}': {}", entry.display(), e),
        file: Some(entry.to_path_buf()),
        span: Span::SYNTHETIC,
    })?;

    let module_name = entry_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("main");
    let entry_module = ModuleFullPath::from(module_name);

    // Step 2: Create session, set lib_dirs (entry parent dir + provided dirs).
    let mut session = crate::pipeline::CompilationSession::new();
    let entry_dir = entry_path.parent().map(|p| p.to_path_buf());
    let mut all_lib_dirs: Vec<PathBuf> = Vec::new();
    if let Some(dir) = &entry_dir {
        all_lib_dirs.push(dir.clone());
    }
    all_lib_dirs.extend(lib_dirs.iter().cloned());
    session.lib_dirs = all_lib_dirs;

    // Derive project_root from entry file's parent directory.
    let project_root = entry_dir.unwrap_or_else(|| PathBuf::from("."));

    // Step 3: Pre-scan entry file for (platform ...) declarations.
    let entry_source = std::fs::read_to_string(&entry_path).map_err(|e| {
        CranelispError::ModuleError {
            message: format!("cannot read '{}': {}", entry_path.display(), e),
            file: Some(entry_path.clone()),
            span: Span::SYNTHETIC,
        }
    })?;

    let prescan_sexps = cranelisp_frontend::parse(&entry_source)?;
    for sexp in &prescan_sexps {
        if let Some((name, span)) = crate::platform::extract_platform_name(sexp) {
            let (platform, jit_syms) = crate::platform::load_and_register_platform(
                &mut session.tc,
                &name,
                &project_root,
                span,
            )?;
            for desc in &platform.descriptors {
                session.scheduling_registry.insert(
                    Symbol::from(desc.name.as_str()),
                    desc.scheduling_class,
                );
            }
            session.platform_symbols.extend(jit_syms);
        }
    }

    // Step 4: Load prelude via compile_unit.
    if let Some(prelude_path) = crate::pipeline::resolve_prelude(&project_root, &session.lib_dirs)
    {
        let prelude_source =
            std::fs::read_to_string(&prelude_path).map_err(|e| CranelispError::ModuleError {
                message: format!("cannot read prelude '{}': {}", prelude_path.display(), e),
                file: Some(prelude_path.clone()),
                span: Span::SYNTHETIC,
            })?;

        // The prelude is a pure re-export shell: it has (export ...) forms
        // referencing domain modules (compare.eq, num.num, etc.) that must
        // be loaded before the prelude's exports can be registered. Pre-load
        // all export target modules via compile_unit.
        let prelude_sexps = cranelisp_frontend::parse(&prelude_source)?;
        let (prelude_structure, _) = cranelisp_frontend::extract_module_declarations(
            ModuleFullPath::from("prelude"),
            None,
            prelude_sexps,
        )?;

        for export_spec in &prelude_structure.export_specs {
            let dep_module = &export_spec.module_path;
            if session.tc.has_module(dep_module) {
                continue;
            }
            if let Some(dep_path) = resolve_module_file(dep_module, &session.lib_dirs) {
                let dep_source = std::fs::read_to_string(&dep_path).map_err(|e| {
                    CranelispError::ModuleError {
                        message: format!("cannot read '{}': {}", dep_path.display(), e),
                        file: Some(dep_path.clone()),
                        span: Span::SYNTHETIC,
                    }
                })?;
                let dep_ctx = CompileContext {
                    module: dep_module.clone(),
                    strategy: ModuleStrategy::Replace,
                    compile_mode: CompileMode::Interactive,
                    codegen_target: CodegenTarget::JitAndCache,
                };
                let dep_result = compile_unit(&mut session, &dep_source, &dep_ctx)?;
                codegen_and_execute(&mut session, &dep_result, &dep_ctx)?;
            }
        }

        let prelude_ctx = CompileContext {
            module: ModuleFullPath::from("prelude"),
            strategy: ModuleStrategy::Replace,
            compile_mode: CompileMode::Interactive,
            codegen_target: CodegenTarget::JitAndCache,
        };

        let prelude_result = compile_unit(&mut session, &prelude_source, &prelude_ctx)?;
        codegen_and_execute(&mut session, &prelude_result, &prelude_ctx)?;
    }

    // Step 5: Load entry file via compile_unit.
    let entry_ctx = CompileContext {
        module: entry_module.clone(),
        strategy: ModuleStrategy::Additive,
        compile_mode: CompileMode::Interactive,
        codegen_target: CodegenTarget::JitAndCache,
    };

    let unit_result = compile_unit(&mut session, &entry_source, &entry_ctx)?;
    let result = codegen_and_execute(&mut session, &unit_result, &entry_ctx)?;

    // Step 6: Verify `main` exists in the GOT.
    // compile_unit in Interactive mode auto-executes zero-arg defns, so
    // `main` has already been called. We need to verify it exists and
    // get its return value/type.
    let main_sym = Symbol::from("main");
    let qualified_main = Symbol::from(format!("{}/main", module_name));

    let main_exists = session.got_state.def_codegen.contains_key(&main_sym)
        || session.got_state.def_codegen.contains_key(&qualified_main);

    if !main_exists {
        return Err(CranelispError::ModuleError {
            message:
                "entry module has no `main` function — batch mode requires (defn main [] ...)"
                    .into(),
            file: Some(entry_path),
            span: Span::SYNTHETIC,
        });
    }

    // The value and type come from codegen_and_execute's result (which executed
    // all zero-arg defns including main via Interactive mode).
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

    // Combine warnings from typecheck (unit_result) and codegen (result).
    let mut all_warnings = unit_result.warnings;
    all_warnings.extend(result.warnings);

    Ok(crate::pipeline::CompiledModuleGraph {
        value,
        ty,
        warnings: all_warnings,
    })
}

// ---------------------------------------------------------------------------
// Link mode: compile via compile_unit() with background .o generation
// ---------------------------------------------------------------------------

/// Compile a project for linking via the v2 pipeline.
///
/// All compilation goes through `compile_unit()` with caching enabled.
/// Each module's `.o` file is written via stage 6b (background cache writer).
/// After all modules are compiled, the cache writer is flushed to ensure
/// all `.o` files are on disk before the system linker is invoked.
///
/// See design/arch/pipeline-v2.md §16.4.3.
///
/// # Steps
/// 1. Discover module graph from entry file, topological sort
/// 2. Create session with cache, set lib_dirs
/// 3. Pre-scan entry file for platform declarations
/// 4. Load prelude and its dependencies via compile_unit (JitAndCache)
/// 5. Load each module in topo order via compile_unit (JitAndCache)
/// 6. Flush background .o writes, collect paths
/// 7. Return LinkCompileResult for link_file()
pub fn compile_for_link_v2(
    entry: &std::path::Path,
    lib_dirs: &[std::path::PathBuf],
    cache_dir: &std::path::Path,
) -> Result<crate::pipeline::LinkCompileResult, CranelispError> {
    use cranelisp_types::Symbol;
    use std::path::PathBuf;

    // Step 1: Discover module graph from entry file.
    let graph = crate::pipeline::discover_module_graph(entry, lib_dirs)?;
    let order = crate::pipeline::toposort(&graph)?;

    // Step 2: Create session with caching enabled.
    let entry_path = entry.canonicalize().map_err(|e| CranelispError::ModuleError {
        message: format!("cannot canonicalize '{}': {}", entry.display(), e),
        file: Some(entry.to_path_buf()),
        span: Span::SYNTHETIC,
    })?;

    std::fs::create_dir_all(cache_dir).map_err(|e| CranelispError::ModuleError {
        message: format!("cannot create cache dir '{}': {}", cache_dir.display(), e),
        file: None,
        span: Span::SYNTHETIC,
    })?;

    let mut session = crate::pipeline::CompilationSession::new_with_cache(cache_dir.to_path_buf());
    let entry_dir = entry_path.parent().map(|p| p.to_path_buf());
    let mut all_lib_dirs: Vec<PathBuf> = Vec::new();
    if let Some(dir) = &entry_dir {
        all_lib_dirs.push(dir.clone());
    }
    all_lib_dirs.extend(lib_dirs.iter().cloned());
    session.lib_dirs = all_lib_dirs;

    let project_root = entry_dir.unwrap_or_else(|| PathBuf::from("."));

    // Step 3: Pre-scan entry file for (platform ...) declarations.
    let entry_source = std::fs::read_to_string(&entry_path).map_err(|e| {
        CranelispError::ModuleError {
            message: format!("cannot read '{}': {}", entry_path.display(), e),
            file: Some(entry_path.clone()),
            span: Span::SYNTHETIC,
        }
    })?;

    let prescan_sexps = cranelisp_frontend::parse(&entry_source)?;
    for sexp in &prescan_sexps {
        if let Some((name, span)) = crate::platform::extract_platform_name(sexp) {
            let (platform, jit_syms) = crate::platform::load_and_register_platform(
                &mut session.tc,
                &name,
                &project_root,
                span,
            )?;
            for desc in &platform.descriptors {
                session.scheduling_registry.insert(
                    Symbol::from(desc.name.as_str()),
                    desc.scheduling_class,
                );
            }
            session.platform_symbols.extend(jit_syms);
        }
    }

    let mut all_warnings: Vec<Warning> = Vec::new();

    // Step 4: Load prelude and its dependencies via compile_unit (JitAndCache).
    // The prelude is compiled in Interactive+JitAndCache mode so its functions
    // are JIT-compiled and .o files are queued in the background.
    load_prelude_for_link(
        &project_root,
        &session.lib_dirs.clone(),
        &mut session,
        &mut all_warnings,
    )?;

    // Step 5: Load each module in topo order via compile_unit (JitAndCache).
    // Since we process in topological order, all dependencies are loaded
    // before the module that depends on them, so compile_unit won't
    // recurse for already-loaded deps.
    // Using JitAndCache mode: compile_unit() JIT-compiles (stage 6a) and
    // queues background .o writes (stage 6b) for each module.
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
            compile_mode: CompileMode::Interactive,
            codegen_target: CodegenTarget::JitAndCache,
        };

        let unit_result = compile_unit(&mut session, &source, &ctx)?;
        let codegen_result = codegen_and_execute(&mut session, &unit_result, &ctx)?;
        all_warnings.extend(unit_result.warnings);
        all_warnings.extend(codegen_result.warnings);
    }

    // Step 6: Flush background .o writes to ensure all files are on disk.
    session.flush_cache_writes();

    // Collect .o paths written during compilation.
    let module_o_paths = session.compiled_o_paths.clone();

    // Step 7: Collect entry module's symbol table and module structures.
    session.tc.set_current_module(graph.entry.clone());
    let entry_symbols = session.tc.symbol_table().clone();

    let module_structures = session.compiled_module_structures.clone();

    Ok(crate::pipeline::LinkCompileResult {
        module_o_paths,
        entry_symbols,
        module_structures,
        warnings: all_warnings,
    })
}

/// Load prelude and its dependencies via compile_unit for --link.
fn load_prelude_for_link(
    project_root: &std::path::Path,
    lib_dirs: &[std::path::PathBuf],
    session: &mut CompilationSession,
    all_warnings: &mut Vec<Warning>,
) -> Result<(), CranelispError> {
    let prelude_path = match crate::pipeline::resolve_prelude(project_root, lib_dirs) {
        Some(f) => f,
        None => return Ok(()),
    };

    let prelude_source =
        std::fs::read_to_string(&prelude_path).map_err(|e| CranelispError::ModuleError {
            message: format!("cannot read prelude '{}': {}", prelude_path.display(), e),
            file: Some(prelude_path.clone()),
            span: Span::SYNTHETIC,
        })?;

    // Pre-load all prelude export target modules via compile_unit.
    let prelude_sexps = cranelisp_frontend::parse(&prelude_source)?;
    let (prelude_structure, _) = cranelisp_frontend::extract_module_declarations(
        ModuleFullPath::from("prelude"),
        None,
        prelude_sexps,
    )?;

    for export_spec in &prelude_structure.export_specs {
        let dep_module = &export_spec.module_path;
        if session.tc.has_module(dep_module) {
            continue;
        }
        if let Some(dep_path) = resolve_module_file(dep_module, lib_dirs) {
            let dep_source = std::fs::read_to_string(&dep_path).map_err(|e| {
                CranelispError::ModuleError {
                    message: format!("cannot read '{}': {}", dep_path.display(), e),
                    file: Some(dep_path.clone()),
                    span: Span::SYNTHETIC,
                }
            })?;
            let dep_ctx = CompileContext {
                module: dep_module.clone(),
                strategy: ModuleStrategy::Replace,
                compile_mode: CompileMode::Interactive,
                codegen_target: CodegenTarget::JitAndCache,
            };
            let unit_result = compile_unit(session, &dep_source, &dep_ctx)?;
            let codegen_result = codegen_and_execute(session, &unit_result, &dep_ctx)?;
            all_warnings.extend(unit_result.warnings);
            all_warnings.extend(codegen_result.warnings);
        }
    }

    // Compile the prelude itself.
    let prelude_ctx = CompileContext {
        module: ModuleFullPath::from("prelude"),
        strategy: ModuleStrategy::Replace,
        compile_mode: CompileMode::Interactive,
        codegen_target: CodegenTarget::JitAndCache,
    };
    let prelude_unit = compile_unit(session, &prelude_source, &prelude_ctx)?;
    let prelude_codegen = codegen_and_execute(session, &prelude_unit, &prelude_ctx)?;
    all_warnings.extend(prelude_unit.warnings);
    all_warnings.extend(prelude_codegen.warnings);

    Ok(())
}

// ---------------------------------------------------------------------------
// Stage 6b: Background .o writer integration
// ---------------------------------------------------------------------------

/// Queue a background .o + .meta.json write for a module (JitAndCache only).
///
/// Builds the `CacheWritePacket` from in-scope pipeline state and sends it
/// to the `CacheWriter` background thread. Non-blocking — `compile_unit()`
/// returns immediately without waiting for the write.
///
/// See design/arch/pipeline-v2.md §16.2, §16.4.1, §16.12.
fn queue_background_cache_write(
    session: &mut CompilationSession,
    source: &str,
    module_path: &ModuleFullPath,
    structure: &cranelisp_types::ModuleStructure,
    program: &cranelisp_types::Program,
    check_result: &CheckResult,
) {
    use cranelisp_backend::cache;
    use std::collections::HashMap;

    // Only write if caching is enabled (cache_state + cache_writer both present).
    let (cache_state, cache_writer) = match (&session.cache_state, &mut session.cache_writer) {
        (Some(cs), Some(cw)) => (cs, cw),
        _ => return,
    };

    // Skip if program has no compilable definitions.
    if !crate::pipeline::has_compilable_defns(program) {
        return;
    }

    // Build ObjectCompileInput from program + check_result + session state.
    let object_input = crate::pipeline::build_object_compile_input(
        module_path,
        Some(program),
        Some(check_result),
        &session.cross_module_func_sigs,
    );

    // Build CacheCodegenState from the program.
    let codegen_state = build_codegen_state_for_cache(program, check_result);

    // Build CacheMetadata.
    let symbol_table = session.tc.module_table(module_path)
        .cloned()
        .unwrap_or_else(|| cranelisp_types::SymbolTable::new(module_path.clone()));

    let metadata = cache::CacheMetadata {
        symbol_table,
        module_structure: structure.clone(),
        codegen_state,
    };

    // Source hash for manifest tracking.
    let source_hash = cache::hash_source(source);

    // Dependency hashes (empty for now — full dependency tracking is a follow-up).
    let dep_hashes: HashMap<String, String> = HashMap::new();

    // Build the cache packet.
    let packet = match cache::build_cache_packet(
        &cache_state.cache_dir(),
        module_path,
        &source_hash,
        false, // is_stdlib
        dep_hashes,
        &metadata,
        object_input,
    ) {
        Ok(p) => p,
        Err(e) => {
            // Cache packet build failure is non-fatal.
            eprintln!("cache: failed to build packet for {}: {}", module_path, e.message());
            return;
        }
    };

    // Deterministic .o path for recording.
    let (_meta_path, o_path) = cache::module_cache_path(&cache_state.cache_dir(), module_path);
    session.compiled_o_paths.push(o_path);

    // Queue the write on the background thread.
    cache_writer.queue_write(module_path.clone(), packet);
}

/// Build `CacheCodegenState` from a program's definitions.
///
/// Records GOT slot assignments and function parameter counts so the
/// cache-load path can reconstruct the batch JIT's symbol table.
fn build_codegen_state_for_cache(
    program: &cranelisp_types::Program,
    check: &CheckResult,
) -> cranelisp_backend::cache::CacheCodegenState {
    use cranelisp_types::TopLevel;
    use std::collections::HashMap;

    let mut got_slots: HashMap<cranelisp_types::Symbol, usize> = HashMap::new();
    let mut def_entries: HashMap<cranelisp_types::Symbol, cranelisp_backend::cache::SerializedDefEntry> = HashMap::new();
    let mut next_slot: usize = 0;

    for tl in program.iter() {
        if let TopLevel::Defn(defn) = tl {
            // Skip constrained fn base definitions.
            if check.constrained_fn_names.contains(&defn.name) {
                continue;
            }
            let slot = next_slot;
            next_slot += 1;
            got_slots.insert(defn.name.clone(), slot);
            def_entries.insert(
                defn.name.clone(),
                cranelisp_backend::cache::SerializedDefEntry {
                    got_slot: Some(slot),
                    source: None,
                    sexp: None,
                    defn: Some(defn.clone()),
                    param_count: Some(defn.params().len()),
                },
            );
        }
    }

    // Also include monomorphised specializations and default methods.
    for mono in &check.mono_defns {
        let slot = next_slot;
        next_slot += 1;
        got_slots.insert(mono.defn.name.clone(), slot);
        def_entries.insert(
            mono.defn.name.clone(),
            cranelisp_backend::cache::SerializedDefEntry {
                got_slot: Some(slot),
                source: None,
                sexp: None,
                defn: Some(mono.defn.clone()),
                param_count: Some(mono.defn.params().len()),
            },
        );
    }
    for defn in &check.default_method_defns {
        let slot = next_slot;
        next_slot += 1;
        got_slots.insert(defn.name.clone(), slot);
        def_entries.insert(
            defn.name.clone(),
            cranelisp_backend::cache::SerializedDefEntry {
                got_slot: Some(slot),
                source: None,
                sexp: None,
                defn: Some(defn.clone()),
                param_count: Some(defn.params().len()),
            },
        );
    }

    cranelisp_backend::cache::CacheCodegenState {
        got_slots,
        next_got_slot: next_slot,
        def_entries,
    }
}

/// Accumulate function signatures from a module's program and check result.
///
/// Extracts function names and arities from the program's defns and
/// adds them to the cumulative func_sigs list for use as cross-module
/// references by later modules.
fn accumulate_func_sigs_from_program(
    module_path: &ModuleFullPath,
    program: &cranelisp_types::Program,
    check: &CheckResult,
    func_sigs: &mut Vec<(cranelisp_types::Symbol, usize)>,
) {
    use cranelisp_types::TopLevel;

    for tl in program.iter() {
        if let TopLevel::Defn(defn) = tl {
            // Skip constrained fn base definitions.
            if check.constrained_fn_names.contains(&defn.name) {
                continue;
            }
            let param_count = defn.params().len();
            // Add both bare name and module-qualified name.
            func_sigs.push((defn.name.clone(), param_count));
            let qualified = cranelisp_types::Symbol::from(
                format!("{}/{}", module_path, defn.name)
            );
            func_sigs.push((qualified, param_count));
        }
    }

    // Also include monomorphised specializations.
    for mono in &check.mono_defns {
        let param_count = mono.defn.params().len();
        func_sigs.push((mono.defn.name.clone(), param_count));
    }
    for defn in &check.default_method_defns {
        let param_count = defn.params().len();
        func_sigs.push((defn.name.clone(), param_count));
    }
}

// NOTE: write_object_file_sync() for ObjectOnly mode (stage 6a) is deferred.
// When CodegenTarget::ObjectOnly support is added to compile_unit()'s codegen
// dispatch, it will compile directly to .o via compile_module_to_object()
// instead of JIT. For now, --link uses JitAndCache + flush (stage 6b).

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{CompileContext, CompileMode, ModuleFullPath, ModuleStrategy};

    /// Helper: build a batch compile context targeting the "user" module.
    ///
    /// Uses Additive strategy because the "user" module is pre-populated
    /// with builtins by TypeChecker::new(). Replace would wipe those.
    fn batch_ctx() -> CompileContext {
        CompileContext {
            module: ModuleFullPath::from("user"),
            strategy: ModuleStrategy::Additive,
            compile_mode: CompileMode::Batch,
            codegen_target: CodegenTarget::JitAndCache,
        }
    }

    /// Helper: build an additive (REPL-like) compile context.
    fn additive_ctx() -> CompileContext {
        CompileContext {
            module: ModuleFullPath::from("user"),
            strategy: ModuleStrategy::Additive,
            compile_mode: CompileMode::Interactive,
            codegen_target: CodegenTarget::JitAndCache,
        }
    }

    // spec: design/arch/pipeline-v2.md §2 — unified pipeline stages
    #[test]
    fn batch_defn_main_returns_value() {
        let mut session = CompilationSession::new();
        let ctx = batch_ctx();
        let unit_result = compile_unit(&mut session, "(defn main [] (if true 3 0))", &ctx)
            .expect("compile_unit failed");
        let codegen_result = codegen_and_execute(&mut session, &unit_result, &ctx)
            .expect("codegen_and_execute failed");

        assert_eq!(codegen_result.value, Some(3));
    }

    // spec: design/arch/pipeline-v2.md §5.5 — Expr handling via synthetic defn
    #[test]
    fn additive_bare_expression() {
        let mut session = CompilationSession::new();
        let ctx = additive_ctx();
        let unit_result = compile_unit(&mut session, "(if true 3 0)", &ctx)
            .expect("compile_unit failed");
        let codegen_result = codegen_and_execute(&mut session, &unit_result, &ctx)
            .expect("codegen_and_execute failed");

        assert_eq!(codegen_result.value, Some(3));
    }

    // spec: design/arch/pipeline-v2.md §8.7 — defmacro in source followed by usage
    #[test]
    fn defmacro_followed_by_usage() {
        // Uses quasiquote macro with qualified primitive name.
        let source = r#"
            (defmacro wrap [x] `(primitives/add-i64 1 ~x))
            (defn main [] (wrap 41))
        "#;
        let mut session = CompilationSession::new();
        let ctx = batch_ctx();
        let unit_result = compile_unit(&mut session, source, &ctx)
            .expect("compile_unit failed");
        let codegen_result = codegen_and_execute(&mut session, &unit_result, &ctx)
            .expect("codegen_and_execute failed");

        assert_eq!(codegen_result.value, Some(42));
    }

    // spec: design/arch/pipeline-v2.md §8.3 — cycle detection
    #[test]
    fn cycle_detection_reports_error() {
        let session = CompilationSession::new();
        let module = ModuleFullPath::from("alpha");

        // Simulate: alpha is already on the compile stack.
        let mut session_with_cycle = session;
        session_with_cycle.compile_stack.push(module.clone());

        let err = check_cycle(&session_with_cycle, &module);
        assert!(err.is_err(), "expected circular dependency error");
        let msg = err.unwrap_err().message().to_string();
        assert!(
            msg.contains("circular dependency"),
            "error should mention circular dependency, got: {msg}"
        );
    }

    // spec: design/arch/pipeline-v2.md §8.3 — non-cyclic no false positive
    #[test]
    fn non_cyclic_no_false_positive() {
        let session = CompilationSession::new();
        let mut session_with_stack = session;
        session_with_stack
            .compile_stack
            .push(ModuleFullPath::from("alpha"));

        // beta is not on the stack, so no cycle.
        let result = check_cycle(&session_with_stack, &ModuleFullPath::from("beta"));
        assert!(result.is_ok(), "should not report cycle for different module");
    }
}
