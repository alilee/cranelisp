// Worker functions for the v4 scheduler-driven pipeline (Step 3).
//
// `process_module_forms` — drives two-pass typecheck for a single module.
// `codegen_module_symbols` — post-typecheck codegen sweep.
// `priority_worker_loop` — dispatches work items from the scheduler.

use std::collections::HashMap;

use cranelisp_types::{
    CheckResult, CranelispError, Defn, ImportSpec, ModuleFullPath,
    ModuleStrategy, NoOpExpander, Sexp, Span, Symbol, TopLevel,
};

use cranelisp_typecheck::{CheckPass, ModuleCheckAccumulator};

use crate::pipeline::compile_and_register_defn;
use crate::scheduler::{CompileScheduler, PriorityWork};
use crate::session::InMemWorkerState;

// ---------------------------------------------------------------------------
// process_module_forms — two-pass per-form typecheck (C1)
// ---------------------------------------------------------------------------

/// Expand, build AST, and typecheck all forms in a module from pre-parsed sexps.
///
/// Drives the two-pass iteration required by Algorithm W:
/// - Pass 1 (Register): register type defs, trait decls, signatures.
/// - Pass 2 (CheckBody): check function bodies, detect constraints.
///
/// On success, notifies the scheduler of each typechecked symbol and
/// calls `notify_typecheck_done`. On error, calls `notify_module_failed`.
///
/// Accepts pre-parsed sexps to avoid redundant parsing (the caller may
/// have already parsed the source for C2 qualification filtering).
pub fn process_module_forms(
    tc: &mut cranelisp_typecheck::TypeChecker,
    scheduler: &mut CompileScheduler,
    module: &ModuleFullPath,
    sexps: Vec<Sexp>,
) -> Result<(CheckResult, Vec<TopLevel>), CranelispError> {
    // Stage 3: Expand (identity for Step 3 — no macros in scope).
    // Stage 4: Build AST from sexps.
    let expander = NoOpExpander;
    let program = cranelisp_frontend::build_program(&sexps, &expander)?;

    // Wrap Expr variants as synthetic zero-arg Defns (matching check() behavior).
    let working_program = wrap_exprs_as_defns(&program);

    // Set active module and clear for replace.
    tc.set_current_module(module.clone());
    tc.clear_module_for_replace_public();

    // Inject wildcard import of primitives module (C3: no prelude, but
    // primitives like add-i64 must be accessible).
    inject_primitives_import(tc)?;

    // Create per-module accumulator.
    let mut accumulator = ModuleCheckAccumulator::new();

    // Pass 1: Register all forms in source order.
    pass1_register(tc, module, &working_program, &mut accumulator)?;

    // Register default method defns from Pass 1 TraitImpl processing.
    let defaults = register_default_methods(tc, module, &mut accumulator)?;
    accumulator.default_method_defns = defaults;

    // Pass 2: Check bodies for all forms.
    pass2_check_bodies(tc, scheduler, module, &working_program, &mut accumulator)?;

    // Check bodies of default method defns too.
    let defaults_for_body: Vec<Defn> = accumulator.default_method_defns.clone();
    for defn in &defaults_for_body {
        let form = TopLevel::Defn(defn.clone());
        let result = tc.check_form(module, &form, CheckPass::CheckBody, &mut accumulator)?;
        tc.merge_form_result(module, &mut accumulator, result);
    }

    // Finalize: run post-passes and build CheckResult.
    let mut check_result = tc.finalize_check_result(
        module,
        &mut accumulator,
        &working_program,
        ModuleStrategy::Replace,
    )?;

    // Populate display info.
    check_result.display = tc.compute_display_info_public(&program, &accumulator.defn_type_vars);

    scheduler.notify_typecheck_done(module);

    Ok((check_result, program))
}

/// Pass 1: register all forms' type signatures in source order.
fn pass1_register(
    tc: &mut cranelisp_typecheck::TypeChecker,
    module: &ModuleFullPath,
    working_program: &[TopLevel],
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    for form in working_program {
        let result = tc.check_form(module, form, CheckPass::Register, accumulator)?;
        tc.merge_form_result(module, accumulator, result);
    }
    Ok(())
}

/// Register default method defns generated during Pass 1 TraitImpl processing.
fn register_default_methods(
    tc: &mut cranelisp_typecheck::TypeChecker,
    module: &ModuleFullPath,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<Vec<Defn>, CranelispError> {
    let defaults: Vec<Defn> = std::mem::take(&mut accumulator.default_method_defns);
    for defn in &defaults {
        let form = TopLevel::Defn(defn.clone());
        let result = tc.check_form(module, &form, CheckPass::Register, accumulator)?;
        tc.merge_form_result(module, accumulator, result);
    }
    Ok(defaults)
}

/// Pass 2: check all form bodies, notifying scheduler after each defn.
fn pass2_check_bodies(
    tc: &mut cranelisp_typecheck::TypeChecker,
    scheduler: &mut CompileScheduler,
    module: &ModuleFullPath,
    working_program: &[TopLevel],
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    for form in working_program {
        let result = tc.check_form(module, form, CheckPass::CheckBody, accumulator)?;
        tc.merge_form_result(module, accumulator, result);

        // Notify scheduler for each defn symbol typechecked.
        if let TopLevel::Defn(defn) = form {
            scheduler.notify_symbol_typechecked(module, &defn.name);
        }
    }
    Ok(())
}

/// Inject a wildcard import of the `primitives` module into the current module.
///
/// For the v4 scheduler path (C3: no prelude injection), modules still need
/// access to named primitives (add-i64, sub-i64, etc.). This injects
/// `(import [primitives [*]])` so primitives are available by bare name.
fn inject_primitives_import(
    tc: &mut cranelisp_typecheck::TypeChecker,
) -> Result<(), CranelispError> {
    let import_spec = ImportSpec {
        module_path: ModuleFullPath::from("primitives"),
        alias: None,
        names: cranelisp_types::ImportNames::Glob,
        span: Span::SYNTHETIC,
    };
    tc.register_imports(&[import_spec])
}

/// Wrap `Expr` variants as synthetic zero-arg `Defn` named `__expr`.
/// Mirrors `TypeChecker::wrap_exprs_as_defns`.
fn wrap_exprs_as_defns(program: &[TopLevel]) -> Vec<TopLevel> {
    use cranelisp_types::{DefnVariant, Visibility};

    let mut working = Vec::with_capacity(program.len());
    for top in program {
        match top {
            TopLevel::Expr(expr) => {
                let span = expr.span();
                let wrapper_span = Span::new(
                    span.start.saturating_sub(1),
                    span.end.saturating_add(1),
                );
                let synthetic_defn = Defn {
                    name: Symbol::from("__expr"),
                    docstring: None,
                    variants: vec![DefnVariant {
                        params: vec![],
                        param_annotations: vec![],
                        body: expr.clone(),
                        span,
                    }],
                    visibility: Visibility::Public,
                    span: wrapper_span,
                };
                working.push(TopLevel::Defn(synthetic_defn));
            }
            other => working.push(other.clone()),
        }
    }
    working
}

// ---------------------------------------------------------------------------
// codegen_module_symbols — post-typecheck codegen sweep (W2)
// ---------------------------------------------------------------------------

/// Compile all symbols from a typechecked module and register in GOT.
///
/// Iterates the program's definitions, compiles each via `compile_and_register_defn`,
/// and notifies the scheduler. Returns the last defn's execution result (for
/// zero-arg defns like `main`).
pub fn codegen_module_symbols(
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    scheduler: &mut CompileScheduler,
    module: &ModuleFullPath,
    program: &[TopLevel],
    check: &CheckResult,
) -> Result<(), CranelispError> {
    // Pre-register all defn names in GOT for forward references.
    pre_register_got_slots(inmem_worker, program)?;

    // Compile default method bodies.
    for defn in &check.default_method_defns {
        compile_and_register_defn(inmem_worker, platform_symbols, defn, check)?;
    }

    // Compile mono specializations with per-specialization resolutions.
    compile_mono_defns(inmem_worker, platform_symbols, check)?;

    // Compile each regular defn.
    let defn_names = compile_regular_defns(inmem_worker, platform_symbols, program, check)?;

    // Notify scheduler for each compiled symbol.
    let total = defn_names.len();
    for (i, name) in defn_names.iter().enumerate() {
        let is_last = i + 1 == total;
        scheduler.notify_inmem_codegen_complete(module, name, is_last);
    }

    // If no defns were compiled, mark inmem done anyway.
    if total == 0 {
        let dummy = Symbol::from("__empty_module");
        scheduler.notify_inmem_codegen_complete(module, &dummy, true);
    }

    Ok(())
}

/// Pre-register GOT slots for all definitions in the program.
fn pre_register_got_slots(
    inmem_worker: &mut InMemWorkerState,
    program: &[TopLevel],
) -> Result<(), CranelispError> {
    for tl in program {
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
    Ok(())
}

/// Compile monomorphised specializations.
fn compile_mono_defns(
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    check: &CheckResult,
) -> Result<(), CranelispError> {
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
    Ok(())
}

/// Compile regular defns (skipping constrained fn base definitions).
/// Returns the list of compiled symbol names.
fn compile_regular_defns(
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    program: &[TopLevel],
    check: &CheckResult,
) -> Result<Vec<Symbol>, CranelispError> {
    let mut compiled_names = Vec::new();

    for tl in program {
        match tl {
            TopLevel::Defn(defn) => {
                if check.constrained_fn_names.contains(&defn.name) {
                    continue;
                }
                compile_and_register_defn(inmem_worker, platform_symbols, defn, check)?;
                compiled_names.push(defn.name.clone());

                // Note: zero-arg defns (e.g., `main`) are NOT executed here.
                // The codegen sweep only compiles and registers code pointers
                // in the GOT. Execution is done separately by `trampoline`.
            }
            TopLevel::TraitImpl(impl_) => {
                for method in &impl_.methods {
                    compile_and_register_defn(
                        inmem_worker,
                        platform_symbols,
                        method,
                        check,
                    )?;
                    compiled_names.push(method.name.clone());
                }
            }
            _ => {}
        }
    }

    Ok(compiled_names)
}


// ---------------------------------------------------------------------------
// priority_worker_loop — dispatch scheduler work items
// ---------------------------------------------------------------------------

/// Main worker loop: pull work from the scheduler and process it.
///
/// Returns when `take_priority_work` returns None (all work done or shutdown).
/// After typecheck, performs a codegen sweep (W2 approach).
///
/// Accepts pre-parsed sexps per module to avoid redundant parsing.
pub fn priority_worker_loop(
    tc: &mut cranelisp_typecheck::TypeChecker,
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    scheduler: &mut CompileScheduler,
    module_sexps: &mut HashMap<ModuleFullPath, Vec<Sexp>>,
) -> Result<(), CranelispError> {
    loop {
        let work = scheduler.take_priority_work();
        match work {
            Some(PriorityWork::Typecheck(module)) => {
                let sexps = module_sexps.remove(&module).ok_or_else(|| {
                    CranelispError::ModuleError {
                        message: format!("no parsed sexps for module '{}'", module),
                        file: None,
                        span: Span::SYNTHETIC,
                    }
                })?;

                match process_module_forms(tc, scheduler, &module, sexps) {
                    Ok((check_result, program)) => {
                        // Post-typecheck codegen sweep (W2).
                        codegen_module_symbols(
                            inmem_worker,
                            platform_symbols,
                            scheduler,
                            &module,
                            &program,
                            &check_result,
                        )?;
                    }
                    Err(e) => {
                        scheduler.notify_module_failed(&module, e);
                    }
                }
            }
            Some(PriorityWork::BlockingJitCodegen(_module, _symbol)) => {
                // Not needed in Step 3 — macro codegen deferred to Step 4.
                // The priority queue is empty for Step 3 programs.
            }
            Some(PriorityWork::JitCodegen(_module, _symbol)) => {
                // Not needed in Step 3 — level 4 deferred.
            }
            None => break,
        }
    }
    Ok(())
}
