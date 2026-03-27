// Pipeline v2: unified compilation pipeline.
//
// `compile_unit()` is the single entry point for all compilation:
// batch programs, REPL forms, and module loading all flow through
// the same stages with the same types. Mode differences are expressed
// via `CompileContext` parameters.
//
// Stages:
//   1. Parse:       &str -> Vec<Sexp>
//   2a. Extract:    Vec<Sexp> -> (ModuleStructure, Vec<Sexp>)
//   2b. Auto-prelude trigger (recursive compile_unit for prelude if needed)
//   2c. Recursive module loading for unresolved imports + exports
//   2d. (unused — reserved)
//   2e. Prelude import injection + register imports/exports
//   2f. Load platform DLLs from module declarations
//   3. Expand:      Vec<Sexp> -> Vec<Sexp>  (defmacro interception + macro expansion)
//   4. Build AST:   Vec<Sexp> -> Vec<TopLevel>
//   4b. Bind chain analysis (auto IO scheduling)
//   5. Typecheck:   Vec<TopLevel> -> CheckResult  (unified multi-pass)
//   6. Codegen:     TopLevel + CheckResult -> JIT (mode-dependent)
//   7. Execute:     call entry fn -> i64          (mode-dependent)

use std::path::PathBuf;

use cranelisp_types::{
    CheckResult, CodegenTarget, CompileContext, CranelispError, ModuleFullPath,
    ModuleStrategy, Span, Symbol, Type, Warning,
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

/// An item queued for codegen (stages 6-7).
///
/// Captures everything needed to call `codegen_and_execute()` for a single
/// compilation unit. Callers push items to the session's `inmem_queue` or
/// `object_queue`, then call the corresponding flush method.
pub struct CodegenItem {
    /// The compile context (module, strategy, codegen target).
    pub ctx: CompileContext,
    /// The stages 1-5 result, ready for codegen.
    pub unit_result: CompileUnitResult,
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

    // Stage 2a-post: Register file→module mapping for the current module.
    // Only for file-backed modules (resolve via lib_dirs). Inline test
    // sources won't resolve and are skipped.
    if let Some(resolved) = resolve_module_path(&ctx.module, &session.lib_dirs) {
        if let Ok(canonical) = resolved.canonicalize() {
            session.module_deps.register_file(canonical, ctx.module.clone());
        }
    }

    // Stage 2b: Auto-load prelude if needed.
    // When a non-prelude module is compiled and the prelude hasn't been loaded
    // yet, resolve and compile it recursively. The prelude's own
    // load_dependencies call (inside its recursive compile_unit) handles
    // loading its export-target modules (core.numerics, core.formats, etc.)
    // because load_dependencies now covers both imports and exports.
    let prelude_path = ModuleFullPath::from("prelude");
    let needs_prelude = !session.tc.has_module(&prelude_path)
        && ctx.module != prelude_path
        && !session.compile_stack.contains(&prelude_path)
        && !session.lib_dirs.is_empty();
    if let Some(prelude_file) =
        needs_prelude.then(|| crate::pipeline::resolve_prelude(&session.project_root, &session.lib_dirs)).flatten()
    {
        let prelude_source = std::fs::read_to_string(&prelude_file).map_err(|e| {
            CranelispError::ModuleError {
                message: format!(
                    "cannot read prelude '{}': {}",
                    prelude_file.display(),
                    e
                ),
                file: Some(prelude_file.clone()),
                span: Span::SYNTHETIC,
            }
        })?;
        let prelude_ctx = CompileContext {
            module: ModuleFullPath::from("prelude"),
            strategy: ModuleStrategy::Replace,
            codegen_target: ctx.codegen_target, // inherit caller's target
        };
        let prelude_result = compile_unit(session, &prelude_source, &prelude_ctx)?;
        codegen_and_execute_via_session(session, &prelude_result, &prelude_ctx)?;

        // Register prelude dependency edge for the current module.
        session.module_deps.register_edge(&ctx.module, &prelude_path);
    }

    // Stage 2c: Recursive module loading for unresolved imports and exports.
    load_dependencies(session, &structure, ctx.codegen_target)?;

    // Stage 2e: Prelude import injection + register imports/exports.
    // Set the current module BEFORE registering imports so that
    // inject_prelude_import and register_imports target the correct module.
    // This is needed when compile_unit is called recursively for a dependency
    // (e.g., loading num.int from REPL context where current_module is "user").
    session.tc.set_current_module(ctx.module.clone());

    if session.tc.has_module(&prelude_path) && ctx.module != prelude_path {
        crate::pipeline::inject_prelude_import(&mut session.tc)?;
    }
    if !structure.import_specs.is_empty() {
        session.tc.register_imports(&structure.import_specs)?;
    }
    if !structure.export_specs.is_empty() {
        session.tc.register_exports(&structure.export_specs)?;
    }

    // Stage 2f: Load platform DLLs declared in this module.
    // Platform forms are extracted by extract_module_declarations (not in
    // `remaining`), so no filtering is needed.
    for platform_spec in &structure.platform_specs {
        let (platform, jit_syms) = crate::platform::load_and_register_platform(
            &mut session.tc,
            &platform_spec.name,
            &session.project_root,
            platform_spec.span,
        )?;
        for desc in &platform.descriptors {
            session.scheduling_registry.insert(
                Symbol::from(desc.name.as_str()),
                desc.scheduling_class,
            );
        }
        session.platform_symbols.extend(jit_syms);
        session.loaded_platforms.push(platform);
    }

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

/// Everything codegen needs, extracted from CompilationSession at the call site.
///
/// Must be Send so it can move to the codegen worker thread (Step 11 async mode).
/// The symbol_table is pre-cloned from the TypeChecker because tc is not Send.
pub struct CodegenPacket {
    /// The compile context (module, strategy, codegen target).
    pub ctx: CompileContext,
    /// The stages 1-5 result, ready for codegen.
    pub unit_result: CompileUnitResult,
    /// Whether to use GOT-indirect calls (interactive/REPL mode).
    pub interactive: bool,
    /// Platform function pointers for JIT symbol registration.
    pub platform_symbols: Vec<(String, *const u8)>,
    /// Pre-cloned symbol table for the module (used by cache writes).
    /// Cloned from tc at the call site because tc is not Send.
    pub symbol_table: cranelisp_types::SymbolTable,
}

// SAFETY: CodegenPacket contains raw *const u8 pointers (in platform_symbols)
// that are function pointers into loaded DLLs. These pointers are valid for
// the process lifetime and are only read (never written) by the codegen path.
unsafe impl Send for CodegenPacket {}

/// Execute codegen and optional execution for a compiled unit.
///
/// Takes a `CompileUnitResult` from `compile_unit()` (stages 1-5) and
/// performs stages 6-7: codegen dispatch, module alias registration,
/// background cache write, module structure recording, and func_sigs
/// accumulation.
///
/// This is the free-function form that takes decomposed worker state
/// instead of `&mut CompilationSession`. Used by both the synchronous
/// fallback path and the async codegen worker thread.
/// Execute codegen via a pre-built `CodegenPacket`.
///
/// Used by the codegen worker thread (async mode) where all data has been
/// pre-cloned into a Send-able packet. For synchronous callers, prefer
/// `codegen_and_execute_via_session` which avoids cloning.
pub fn codegen_and_execute(
    inmem_worker: &mut crate::pipeline::InMemWorkerState,
    object_worker: &mut crate::pipeline::ObjectWorkerState,
    packet: &CodegenPacket,
) -> Result<CodegenResult, CranelispError> {
    codegen_and_execute_decomposed(
        inmem_worker,
        object_worker,
        &packet.platform_symbols,
        packet.interactive,
        &packet.symbol_table,
        &packet.unit_result,
        &packet.ctx,
    )
}

/// Convenience wrapper: call `codegen_and_execute` using session fields.
///
/// Decomposes `CompilationSession` into its constituent parts and calls
/// the free-function form. No cloning — borrows session fields directly.
pub fn codegen_and_execute_via_session(
    session: &mut CompilationSession,
    unit_result: &CompileUnitResult,
    ctx: &CompileContext,
) -> Result<CodegenResult, CranelispError> {
    let symbol_table = session.tc.module_table(&ctx.module)
        .cloned()
        .unwrap_or_else(|| cranelisp_types::SymbolTable::new(ctx.module.clone()));

    codegen_and_execute_decomposed(
        &mut session.inmem_worker,
        &mut session.object_worker,
        &session.platform_symbols,
        session.interactive,
        &symbol_table,
        unit_result,
        ctx,
    )
}

/// Execute codegen using decomposed session fields (no packet cloning).
///
/// This is the core implementation shared by `codegen_and_execute_via_session`
/// (synchronous) and the codegen worker thread (async, via `CodegenPacket`).
fn codegen_and_execute_decomposed(
    inmem_worker: &mut crate::pipeline::InMemWorkerState,
    object_worker: &mut crate::pipeline::ObjectWorkerState,
    platform_symbols: &[(String, *const u8)],
    interactive: bool,
    symbol_table: &cranelisp_types::SymbolTable,
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
    let pre_existing: std::collections::HashSet<cranelisp_types::Symbol> = inmem_worker
        .got_state
        .def_codegen
        .keys()
        .cloned()
        .collect();

    let mut codegen_warnings: Vec<Warning> = Vec::new();

    // Stages 6-7: Codegen and execute.
    let (value, result_type) = if interactive {
        compile_and_execute_interactive(
            inmem_worker,
            platform_symbols,
            &unit_result.program,
            &unit_result.check_result,
            &mut codegen_warnings,
        )?
    } else {
        compile_and_execute_batch(
            &unit_result.program,
            &unit_result.check_result,
            &mut codegen_warnings,
        )?
    };

    // Register module aliases after successful interactive-mode compilation.
    if interactive {
        crate::pipeline::register_module_aliases_filtered(
            inmem_worker,
            &ctx.module,
            Some(&pre_existing),
        );
    }

    // Stage 6b: Background .o + .meta.json write (JitAndCache only).
    if ctx.codegen_target == CodegenTarget::JitAndCache {
        queue_background_cache_write(
            object_worker,
            symbol_table,
            &unit_result.source,
            &ctx.module,
            &unit_result.module_structure,
            &unit_result.program,
            &unit_result.check_result,
        );
    }

    // Record module structure for --link (both targets).
    object_worker
        .compiled_module_structures
        .push((ctx.module.clone(), unit_result.module_structure.clone()));

    // Accumulate cross-module func_sigs from this module's definitions.
    accumulate_func_sigs_from_program(
        &ctx.module,
        &unit_result.program,
        &unit_result.check_result,
        &mut object_worker.cross_module_func_sigs,
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

/// Load all uncompiled dependencies for a module's imports and exports.
///
/// Iterates the union of import and export module paths. For each, if the
/// module is not yet compiled, resolve its source file via `session.lib_dirs`,
/// read it, and compile it recursively via `compile_unit()`. Export targets
/// are included because re-export shells (like prelude) need their target
/// modules compiled before exports can be registered.
///
/// If lib_dirs is empty (test mode), unresolved deps are silently skipped —
/// they will fail during typecheck with a proper "unresolved symbol" error.
fn load_dependencies(
    session: &mut CompilationSession,
    structure: &cranelisp_types::ModuleStructure,
    codegen_target: CodegenTarget,
) -> Result<(), CranelispError> {
    // Collect module paths from both imports and exports (duplicates filtered by has_module check).
    let dep_modules: Vec<ModuleFullPath> = structure
        .import_specs
        .iter()
        .map(|s| s.module_path.clone())
        .chain(structure.export_specs.iter().map(|s| s.module_path.clone()))
        .collect();

    let parent_module = &structure.path;

    for dep_module in &dep_modules {
        // Register the dependency edge (even for already-compiled modules).
        session.module_deps.register_edge(parent_module, dep_module);

        // Skip compilation if already compiled or is a builtin module.
        if session.tc.has_module(dep_module) {
            continue;
        }

        // Try to resolve the module source file.
        if let Some(dep_source_path) = resolve_module_path(dep_module, &session.lib_dirs) {
            // Register file→module mapping (canonical path when possible).
            if let Ok(canonical) = dep_source_path.canonicalize() {
                session.module_deps.register_file(canonical, dep_module.clone());
            }

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
                codegen_target,
            };

            // Recursive call — cycle detection happens inside compile_unit().
            let unit_result = compile_unit(session, &dep_source, &dep_ctx)?;
            // Queue codegen for this dependency. In async mode (Step 11),
            // codegen runs on a worker thread overlapping with the next
            // compile_unit call. In sync mode, it buffers until flush.
            session.send_codegen(unit_result, dep_ctx);
        }
        // If resolve returns None: import will fail during typecheck
        // (unresolved symbol). This is the test-mode path when lib_dirs is empty.
    }
    // Flush all queued codegen. In async mode, this blocks until the
    // worker thread has processed all items. In sync mode, it executes
    // them sequentially now.
    session.flush_codegen()?;
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
    let compiled = cranelisp_backend::compile_program(program, check, false)?;
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
/// Compiles definitions via the GOT state and compiles/executes
/// any bare expressions.
///
/// Returns `(Option<value>, Option<result_type>)`.
fn compile_and_execute_interactive(
    inmem_worker: &mut crate::pipeline::InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
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
    let form_result = compile_checked_program(inmem_worker, platform_symbols, program, check)?;

    // Check for runtime panics (e.g., checked division by zero in zero-arg defns).
    check_runtime_panic()?;

    if let Some(ref result) = form_result {
        warnings.extend(result.warnings.iter().cloned());
    }

    // If there are bare expressions, compile and execute them.
    if has_expr {
        let (value, ty) = compile_and_execute_expr(inmem_worker, platform_symbols, program, check)?;
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
    inmem_worker: &mut crate::pipeline::InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
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

    if inmem_worker.traced_fns.is_empty() {
        // Normal (non-trace) path.
        let extra_syms: Vec<(&str, *const u8)> = platform_symbols
            .iter()
            .map(|(name, ptr)| (name.as_str(), *ptr))
            .collect();

        let compiled = cranelisp_backend::compile_expr_with_got_and_symbols(
            expr,
            check,
            Some(&mut inmem_worker.got_state),
            &extra_syms,
        )?;

        // SAFETY: compiled code was just generated and finalized by our JIT.
        let value = unsafe { compiled.execute() };
        Ok((value, ty))
    } else {
        // Trace-aware path.
        let value = compile_and_execute_expr_with_trace(inmem_worker, platform_symbols, expr, check)?;
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
/// can generate GOT-swap wrappers. The JIT is kept alive in the
/// jit_modules so wrapper code pointers remain valid.
fn compile_and_execute_expr_with_trace(
    inmem_worker: &mut crate::pipeline::InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    expr: &cranelisp_types::Expr,
    check: &CheckResult,
) -> Result<i64, CranelispError> {
    use cranelisp_types::{Defn, DefnVariant, Symbol, Visibility};
    use std::collections::HashMap;

    let mut extra_syms: Vec<(&str, *const u8)> = platform_symbols
        .iter()
        .map(|(name, ptr)| (name.as_str(), *ptr))
        .collect();
    for (name, ptr) in &inmem_worker.trace_extra_symbols {
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
    for (name, dc) in &inmem_worker.got_state.def_codegen {
        if let Some(slot) = dc.got_slot {
            got_slots.insert(name.clone(), slot);
        }
        if let Some(pc) = dc.param_count {
            func_arities.insert(name.clone(), pc);
        }
    }
    let got_base = inmem_worker.got_state.got_base_ptr() as i64;

    let mut compile_ctx = jit.build_compile_context(
        check,
        &func_ids,
        &func_arities,
        Some(&got_slots),
        Some(got_base),
        None,
    );

    compile_ctx.traced_fns = Some(&inmem_worker.traced_fns);

    jit.compile_defn(&wrapper_defn, compile_ctx)?;
    let code_ptr = jit.finalize_and_get_ptr(&wrapper_name, 0)?;

    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
    let value = func();

    inmem_worker.jit_modules.push(jit);

    Ok(value)
}

// ---------------------------------------------------------------------------
// Interactive mode: GOT-based per-defn compilation (free functions)
// ---------------------------------------------------------------------------

/// Compile a whole-program check result into the GOT, one defn at a time.
///
/// Free-function form of `CompilationSession::compile_checked_program`.
/// Takes `InMemWorkerState` and `platform_symbols` directly so it can
/// run on the codegen worker thread.
pub fn compile_checked_program(
    inmem_worker: &mut crate::pipeline::InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    program: &cranelisp_types::Program,
    check: &CheckResult,
) -> Result<Option<crate::pipeline::FormResult>, CranelispError> {
    use cranelisp_types::TopLevel;

    let mut last_result: Option<crate::pipeline::FormResult> = None;

    // Pre-register all defn names in GOT for forward references.
    for tl in program.iter() {
        match tl {
            TopLevel::Defn(defn) => {
                inmem_worker.got_state.ensure_slot_for(&defn.name)?;
            }
            TopLevel::TraitImpl(impl_) => {
                for method in &impl_.methods {
                    inmem_worker.got_state.ensure_slot_for(&method.name)?;
                }
            }
            _ => {}
        }
    }

    // Compile default method bodies.
    for defn in &check.default_method_defns {
        compile_and_register_defn(inmem_worker, platform_symbols, defn, check)?;
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
            display: None,
        };
        compile_and_register_defn(inmem_worker, platform_symbols, &mono.defn, &mono_check)?;
    }

    // Compile each regular defn (skipping constrained fn base definitions).
    for tl in program.iter() {
        match tl {
            TopLevel::Defn(defn) => {
                if check.constrained_fn_names.contains(&defn.name) {
                    continue; // Skip constrained fn base defs — templates only
                }
                compile_and_register_defn(inmem_worker, platform_symbols, defn, check)?;

                // Execute zero-arg defns.
                let (value, result_ty) = if defn.params().is_empty() {
                    let entry = inmem_worker.got_state.def_codegen.get(defn.name.as_ref());
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
                        .get(&defn.body().span())
                        .cloned()
                        .unwrap_or(Type::Int);
                    (func(), ret_ty)
                } else {
                    (0, Type::Int)
                };
                last_result = Some(crate::pipeline::FormResult {
                    value,
                    ty: result_ty,
                    is_definition: true,
                    warnings: Vec::new(),
                });
            }
            TopLevel::TraitImpl(impl_) => {
                for method in &impl_.methods {
                    compile_and_register_defn(inmem_worker, platform_symbols, method, check)?;
                }
            }
            _ => {
                // TypeDef, TraitDecl — handled by typechecker, no codegen needed.
            }
        }
    }

    Ok(last_result)
}

/// Compile a single function definition and register it in the GOT.
///
/// Free-function form of `CompilationSession::compile_and_register_defn`.
/// Takes `InMemWorkerState` and `platform_symbols` directly.
pub fn compile_and_register_defn(
    inmem_worker: &mut crate::pipeline::InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    defn: &cranelisp_types::Defn,
    check: &CheckResult,
) -> Result<(), CranelispError> {
    use std::collections::HashMap;

    // Create JIT with platform symbols registered (if any).
    let extra_symbols: Vec<(&str, *const u8)> = platform_symbols
        .iter()
        .map(|(name, ptr)| (name.as_str(), *ptr))
        .collect();
    let mut jit = cranelisp_backend::jit::Jit::new_with_symbols(&extra_symbols)?;

    // Declare runtime intrinsics (Ring 1 heap infrastructure).
    jit.declare_intrinsics()?;

    // Declare just this function.
    let func_ids = jit.declare_functions(&[defn])?;

    // Ensure a GOT slot exists for this function.
    let slot = inmem_worker.got_state.ensure_slot_for(&defn.name)?;

    // Build GOT slot map from existing state + this new function.
    let mut got_slots: HashMap<Symbol, usize> = HashMap::new();
    for (name, dc) in &inmem_worker.got_state.def_codegen {
        if let Some(s) = dc.got_slot {
            got_slots.insert(name.clone(), s);
        }
    }
    got_slots.insert(defn.name.clone(), slot);

    let got_base = inmem_worker.got_state.got_base_ptr() as i64;

    // Build function arity map from existing GOT state + this defn.
    let mut func_arities: HashMap<Symbol, usize> = HashMap::new();
    for (name, dc) in &inmem_worker.got_state.def_codegen {
        if let Some(pc) = dc.param_count {
            func_arities.insert(name.clone(), pc);
        }
    }
    func_arities.insert(defn.name.clone(), defn.params().len());

    // Compile the function with awareness of existing GOT.
    let compile_ctx = jit.build_compile_context(
        check,
        &func_ids,
        &func_arities,
        Some(&got_slots),
        Some(got_base),
        None,
    );
    let _clif_ir = jit.compile_defn(defn, compile_ctx)?;

    // Finalize and get the code pointer.
    let code_ptr = jit.finalize_and_get_ptr(&defn.name, defn.params().len())?;

    // Update the GOT slot with the new code pointer.
    inmem_worker.got_state.update_slot(slot, code_ptr);

    // Record codegen info.
    let entry = inmem_worker.got_state.def_codegen.entry(defn.name.clone()).or_default();
    entry.code_ptr = Some(code_ptr);
    entry.got_slot = Some(slot);
    entry.param_count = Some(defn.params().len());
    entry.defn = Some(defn.clone());

    // Keep JIT alive so code pointer remains valid.
    inmem_worker.jit_modules.push(jit);

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
/// Takes decomposed worker state and a pre-cloned symbol table instead of
/// `&mut CompilationSession`, so it can run on the codegen worker thread.
///
/// See design/arch/pipeline-v2.md §16.2, §16.4.1, §16.12.
pub fn queue_background_cache_write(
    object_worker: &mut crate::pipeline::ObjectWorkerState,
    symbol_table: &cranelisp_types::SymbolTable,
    source: &str,
    module_path: &ModuleFullPath,
    structure: &cranelisp_types::ModuleStructure,
    program: &cranelisp_types::Program,
    check_result: &CheckResult,
) {
    use cranelisp_backend::cache;
    use std::collections::HashMap;

    // Only write if caching is enabled (cache_state + cache_writer both present).
    if object_worker.cache_state.is_none() || object_worker.cache_writer.is_none() {
        return;
    }

    // Skip if program has no compilable definitions.
    if !crate::pipeline::has_compilable_defns(program) {
        return;
    }

    // Build ObjectCompileInput from program + check_result + worker state.
    let object_input = crate::pipeline::build_object_compile_input(
        module_path,
        Some(program),
        Some(check_result),
        &object_worker.cross_module_func_sigs,
    );

    // Build CacheCodegenState from the program.
    let codegen_state = build_codegen_state_for_cache(program, check_result);

    // Build CacheMetadata using the pre-cloned symbol table.
    let metadata = cache::CacheMetadata {
        symbol_table: symbol_table.clone(),
        module_structure: structure.clone(),
        codegen_state,
    };

    // Source hash for manifest tracking.
    let source_hash = cache::hash_source(source);

    // Dependency hashes (empty for now — full dependency tracking is a follow-up).
    let dep_hashes: HashMap<String, String> = HashMap::new();

    // Get cache_dir from cache_state (existence already verified above).
    let cache_dir = object_worker.cache_state.as_ref()
        .expect("invariant: cache_state checked above")
        .cache_dir()
        .to_path_buf();

    // Build the cache packet.
    let packet = match cache::build_cache_packet(
        &cache_dir,
        module_path,
        &source_hash,
        false, // is_stdlib
        dep_hashes.clone(),
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
    let (_meta_path, o_path) = cache::module_cache_path(&cache_dir, module_path);
    object_worker.compiled_o_paths.push(o_path);

    // Update cache manifest with source hash for this module.
    if let Some(cs) = object_worker.cache_state.as_mut() {
        cs.record_module(module_path, source_hash, dep_hashes);
    }

    // Queue the write on the background thread.
    object_worker.cache_writer.as_mut()
        .expect("invariant: cache_writer checked above")
        .queue_write(module_path.clone(), packet);
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
    use cranelisp_types::{CompileContext, ModuleFullPath, ModuleStrategy};

    // Compile-time Send assertions (Step 11: concurrent codegen worker).
    // These verify that the types we need to send to the worker thread
    // actually implement Send. A compilation failure here means a field
    // was added that contains a non-Send type (e.g., Rc, raw pointer
    // without unsafe impl Send).
    fn _assert_send<T: Send>() {}

    #[allow(dead_code)]
    fn _send_assertions() {
        _assert_send::<CodegenPacket>();
        _assert_send::<CompileUnitResult>();
        _assert_send::<CompileContext>();
        _assert_send::<CheckResult>();
        _assert_send::<CodegenResult>();
        _assert_send::<crate::pipeline::InMemWorkerState>();
        _assert_send::<crate::pipeline::ObjectWorkerState>();
    }

    /// Helper: build a batch compile context targeting the "user" module.
    ///
    /// Uses Additive strategy because the "user" module is pre-populated
    /// with builtins by TypeChecker::new(). Replace would wipe those.
    fn batch_ctx() -> CompileContext {
        CompileContext {
            module: ModuleFullPath::from("user"),
            strategy: ModuleStrategy::Additive,
            codegen_target: CodegenTarget::JitAndCache,
        }
    }

    /// Helper: build an additive (REPL-like) compile context.
    fn additive_ctx() -> CompileContext {
        CompileContext {
            module: ModuleFullPath::from("user"),
            strategy: ModuleStrategy::Additive,
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
        let codegen_result = codegen_and_execute_via_session(&mut session, &unit_result, &ctx)
            .expect("codegen_and_execute failed");

        assert_eq!(codegen_result.value, Some(3));
    }

    // spec: design/arch/pipeline-v2.md §5.5 — Expr handling via synthetic defn
    #[test]
    fn additive_bare_expression() {
        let mut session = CompilationSession::new();
        session.interactive = true;
        let ctx = additive_ctx();
        let unit_result = compile_unit(&mut session, "(if true 3 0)", &ctx)
            .expect("compile_unit failed");
        let codegen_result = codegen_and_execute_via_session(&mut session, &unit_result, &ctx)
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
        let codegen_result = codegen_and_execute_via_session(&mut session, &unit_result, &ctx)
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
