// Worker functions for the v4 scheduler-driven pipeline (Steps 3-4).
//
// `process_module_forms` — drives two-pass typecheck for a single module,
//   with per-sexp macro expansion interleaved in Pass 2 (Step 4).
// `codegen_module_symbols` — post-typecheck codegen sweep.
// `priority_worker_loop` — dispatches work items from the scheduler.

use std::collections::HashMap;

use cranelisp_types::{
    CheckResult, CranelispError, Defn, ImportSpec, MacroClauseInfo,
    ModuleEntry, ModuleFullPath, ModuleStrategy, NoOpExpander, Sexp, Span, Symbol,
    TopLevel, Visibility,
};

use cranelisp_typecheck::{CheckPass, ModuleCheckAccumulator};

use crate::expander::{
    self, MacroClauseEntry, MacroEntry,
};
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
///   Defmacro forms are parsed and registered in the module table.
/// - Pass 2 (CheckBody): per-sexp expand-then-check. Macro calls are
///   expanded inline (compiling macro deps on demand).
///
/// On success, notifies the scheduler of each typechecked symbol and
/// calls `notify_typecheck_done`. On error, calls `notify_module_failed`.
///
/// Accepts pre-parsed sexps to avoid redundant parsing (the caller may
/// have already parsed the source for C2 qualification filtering).
pub fn process_module_forms(
    tc: &mut cranelisp_typecheck::TypeChecker,
    scheduler: &mut CompileScheduler,
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    module: &ModuleFullPath,
    sexps: Vec<Sexp>,
) -> Result<(CheckResult, Vec<TopLevel>), CranelispError> {
    // Set active module and clear for replace.
    tc.set_current_module(module.clone());
    tc.clear_module_for_replace_public();

    // Inject wildcard import of primitives module (C3: no prelude, but
    // primitives like add-i64 must be accessible).
    inject_primitives_import(tc)?;

    // Also inject macros module so Sexp constructors are available.
    inject_macros_import(tc)?;

    // Build AST from all sexps (with NoOpExpander — no expansion in Pass 1).
    let expander = NoOpExpander;

    // Separate defmacro forms from regular forms for Pass 1 registration.
    // Defmacro forms are registered directly in the module table; other
    // forms go through normal build_top_level + check_form(Register).
    let mut regular_sexps: Vec<Sexp> = Vec::new();
    let mut macro_infos: Vec<(Symbol, cranelisp_frontend::DefmacroInfo, Sexp)> = Vec::new();

    for sexp in &sexps {
        if cranelisp_frontend::is_defmacro(sexp) {
            let info = cranelisp_frontend::parse_defmacro(sexp)?;
            macro_infos.push((info.name.clone(), info, sexp.clone()));
        } else {
            regular_sexps.push(sexp.clone());
        }
    }

    // Build AST for regular (non-macro) forms.
    let program = cranelisp_frontend::build_program(&regular_sexps, &expander)?;

    // Wrap Expr variants as synthetic zero-arg Defns (matching check() behavior).
    let working_program = wrap_exprs_as_defns(&program);

    // Create per-module accumulator.
    let mut accumulator = ModuleCheckAccumulator::new();

    // Pass 1: Register all regular forms in source order.
    pass1_register(tc, module, &working_program, &mut accumulator)?;

    // Pass 1: Register macros in the module table.
    for (name, info, sexp) in &macro_infos {
        register_macro_in_module(tc, name, info, sexp)?;
    }

    // Register default method defns from Pass 1 TraitImpl processing.
    let defaults = register_default_methods(tc, module, &mut accumulator)?;
    accumulator.default_method_defns = defaults;

    // Pass 2: Per-sexp expand-then-check. Returns the expanded program
    // (forms with macro calls replaced by their expansions).
    let expanded_program = pass2_check_bodies_with_expansion(
        tc, scheduler, inmem_worker, platform_symbols,
        module, &sexps, &macro_infos, &mut accumulator,
    )?;

    // Use the expanded program for finalization and codegen.
    let final_working = wrap_exprs_as_defns(&expanded_program);

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
        &final_working,
        ModuleStrategy::Replace,
    )?;

    // Populate display info.
    check_result.display =
        tc.compute_display_info_public(&expanded_program, &accumulator.defn_type_vars);

    scheduler.notify_typecheck_done(module);

    Ok((check_result, expanded_program))
}

/// Register a defmacro in the module table (Pass 1).
///
/// Parses clause info and stores it as `ModuleEntry::Macro` with the
/// original sexp for later compilation. No codegen — deferred until
/// first use.
fn register_macro_in_module(
    tc: &mut cranelisp_typecheck::TypeChecker,
    name: &Symbol,
    info: &cranelisp_frontend::DefmacroInfo,
    sexp: &Sexp,
) -> Result<(), CranelispError> {
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
    tc.symbol_table_mut().insert(
        name.clone(),
        ModuleEntry::Macro {
            name: name.clone(),
            clauses: clause_infos,
            docstring: info.docstring.clone(),
            visibility,
            sexp: Some(sexp.clone()),
            source: None,
            callees: Vec::new(),
        },
    );
    Ok(())
}

/// Pass 2: per-sexp expand-then-check, with inline macro compilation.
///
/// Iterates sexps in source order. For each:
/// - If defmacro: skip (already registered in Pass 1).
/// - Otherwise: try expand (compile macro deps inline if needed),
///   build AST from the (possibly expanded) sexp, then typecheck body.
#[allow(clippy::too_many_arguments)]
fn pass2_check_bodies_with_expansion(
    tc: &mut cranelisp_typecheck::TypeChecker,
    scheduler: &mut CompileScheduler,
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    module: &ModuleFullPath,
    sexps: &[Sexp],
    macro_infos: &[(Symbol, cranelisp_frontend::DefmacroInfo, Sexp)],
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<Vec<TopLevel>, CranelispError> {
    let macro_names: Vec<&str> = macro_infos.iter().map(|(n, _, _)| n.as_ref()).collect();
    let expander = NoOpExpander;
    let mut expanded_program: Vec<TopLevel> = Vec::new();

    for sexp in sexps {
        if cranelisp_frontend::is_defmacro(sexp) {
            continue;
        }

        // Try macro expansion on the raw sexp.
        let effective_sexp = try_expand_for_pass2(
            sexp, module, tc, scheduler, inmem_worker, platform_symbols,
            macro_infos, &macro_names, accumulator,
        )?;

        // Build AST from the (possibly expanded) sexp.
        // If expansion produced a (begin ...), flatten into multiple forms.
        let sexp_to_build = match &effective_sexp {
            Some(expanded) => expanded,
            None => sexp,
        };

        let flattened = cranelisp_frontend::flatten_begin(sexp_to_build.clone());

        let built = cranelisp_frontend::build_program(
            &flattened, &expander,
        )?;
        let working = wrap_exprs_as_defns(&built);

        // Register signatures first (Pass 1) for any new forms from expansion.
        // This is needed when begin-splicing introduces new defns.
        for form in &working {
            let result =
                tc.check_form(module, form, CheckPass::Register, accumulator)?;
            tc.merge_form_result(module, accumulator, result);
        }

        // Typecheck body for each form produced (Pass 2).
        for form in &working {
            let result =
                tc.check_form(module, form, CheckPass::CheckBody, accumulator)?;
            tc.merge_form_result(module, accumulator, result);

            if let TopLevel::Defn(defn) = form {
                scheduler.notify_symbol_typechecked(module, &defn.name);
            }
        }

        // Collect expanded forms for the returned program.
        expanded_program.extend(built);
    }
    Ok(expanded_program)
}

// ---------------------------------------------------------------------------
// Macro expansion for Pass 2
// ---------------------------------------------------------------------------

/// Attempt to expand macros in a sexp tree.
///
/// Walks the sexp tree looking for macro calls. If any macros need
/// compilation, compiles them inline first (only transitive deps of
/// the called macros, not all macros). Returns Ok(Some(expanded))
/// if any expansion occurred, Ok(None) if the sexp contains no macro calls.
#[allow(clippy::too_many_arguments)]
fn try_expand_for_pass2(
    sexp: &Sexp,
    module: &ModuleFullPath,
    tc: &mut cranelisp_typecheck::TypeChecker,
    scheduler: &mut CompileScheduler,
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    macro_infos: &[(Symbol, cranelisp_frontend::DefmacroInfo, Sexp)],
    macro_names: &[&str],
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<Option<Sexp>, CranelispError> {
    // Check if this sexp tree contains any macro calls at all.
    if !sexp_contains_macro_call(sexp, macro_names) {
        return Ok(None);
    }

    // Compile macros called in this sexp and their transitive uncompiled
    // dependencies. Because recursive expansion may produce calls to macros
    // not visible in the original sexp (e.g., macro A expands to a call to
    // macro B), we also compile any macros that appear in transitive callees
    // of the directly-called macros. All remaining macros are compiled on
    // demand if recursive expansion encounters them.
    let called_macros = collect_called_macros(sexp, macro_names);
    for macro_name in &called_macros {
        if let Some((_name, info, _)) = macro_infos.iter().find(|(n, _, _)| n.as_ref() == *macro_name) {
            compile_macro_if_needed(
                tc, scheduler, inmem_worker, platform_symbols,
                module, info, sexp.span(), accumulator,
            )?;
        }
    }

    // Recursive expansion may produce calls to macros not directly called
    // in the original sexp. Ensure all registered macros are compiled so
    // expand_sexp_recursive can find their function pointers.
    for (_name, info, _) in macro_infos {
        compile_macro_if_needed(
            tc, scheduler, inmem_worker, platform_symbols,
            module, info, sexp.span(), accumulator,
        )?;
    }

    // Build the full macro map for expansion (includes all compiled macros
    // so recursive expansion can find macros produced by other macros).
    let all_macros = build_all_macro_entries(inmem_worker, macro_infos)?;

    // Expand recursively throughout the entire sexp tree.
    let expanded = expander::expand_sexp_recursive(sexp.clone(), &all_macros, 0)?;

    Ok(Some(expanded))
}

/// Collect the names of macros directly called in a sexp tree.
fn collect_called_macros<'a>(sexp: &Sexp, macro_names: &[&'a str]) -> Vec<&'a str> {
    let mut found = Vec::new();
    collect_called_macros_inner(sexp, macro_names, &mut found);
    found
}

fn collect_called_macros_inner<'a>(sexp: &Sexp, macro_names: &[&'a str], found: &mut Vec<&'a str>) {
    match sexp {
        Sexp::List(children, _) if !children.is_empty() => {
            if let Sexp::Symbol(name, _) = &children[0]
                && let Some(&m) = macro_names.iter().find(|&&m| m == name.as_str())
                && !found.contains(&m)
            {
                found.push(m);
            }
            for c in children {
                collect_called_macros_inner(c, macro_names, found);
            }
        }
        Sexp::Symbol(name, _) => {
            if let Some(&m) = macro_names.iter().find(|&&m| m == name.as_str())
                && !found.contains(&m)
            {
                found.push(m);
            }
        }
        Sexp::Bracket(children, _) => {
            for c in children {
                collect_called_macros_inner(c, macro_names, found);
            }
        }
        _ => {}
    }
}

/// Check if a sexp tree contains any call to a known macro.
fn sexp_contains_macro_call(sexp: &Sexp, macro_names: &[&str]) -> bool {
    match sexp {
        Sexp::List(children, _) if !children.is_empty() => {
            if let Sexp::Symbol(name, _) = &children[0]
                && macro_names.contains(&name.as_str())
            {
                return true;
            }
            children.iter().any(|c| sexp_contains_macro_call(c, macro_names))
        }
        Sexp::Symbol(name, _) => {
            // Bare symbol that is a zero-arg macro.
            macro_names.contains(&name.as_str())
        }
        Sexp::Bracket(children, _) => {
            children.iter().any(|c| sexp_contains_macro_call(c, macro_names))
        }
        _ => false,
    }
}



/// Compile all clauses of a macro if any clause lacks a function pointer.
///
/// Before compiling macro clauses, walks the transitive callees of the
/// macro (from `ModuleEntry.callees`) and compiles any uncompiled
/// dependencies first. Notifies the scheduler after each symbol is compiled.
#[allow(clippy::too_many_arguments)]
fn compile_macro_if_needed(
    tc: &mut cranelisp_typecheck::TypeChecker,
    scheduler: &mut CompileScheduler,
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    module: &ModuleFullPath,
    info: &cranelisp_frontend::DefmacroInfo,
    span: Span,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    // Check if all clauses already have function pointers.
    let all_compiled = info.clauses.iter().enumerate().all(|(idx, _)| {
        let clause_name = macro_clause_jit_name(&info.name, idx);
        has_code_ptr(inmem_worker, &clause_name)
    });

    if all_compiled {
        return Ok(());
    }

    // Walk transitive callees and compile uncompiled deps first.
    let uncompiled_deps = collect_transitive_uncompiled_deps(tc, inmem_worker, module, &info.name);
    for (dep_module, dep_symbol) in &uncompiled_deps {
        // Look up the defn from the symbol table and compile it.
        // For now, deps are in the same module (Step 4 single-module mode).
        let _dep_module = dep_module; // will be used in Step 5+ cross-module
        compile_dep_symbol_inline(
            tc, inmem_worker, platform_symbols,
            dep_symbol, accumulator,
        )?;
        scheduler.notify_inmem_codegen_complete(module, dep_symbol, false);
    }

    // Compile each clause that is not yet compiled.
    let total_clauses = info.clauses.len();
    for (clause_idx, clause) in info.clauses.iter().enumerate() {
        let clause_name = macro_clause_jit_name(&info.name, clause_idx);
        if has_code_ptr(inmem_worker, &clause_name) {
            continue;
        }

        compile_macro_clause_inline(
            tc, inmem_worker, platform_symbols,
            &info.name, clause_idx, clause, span,
            accumulator,
        )?;
        let is_last = clause_idx + 1 == total_clauses;
        scheduler.notify_inmem_codegen_complete(module, &clause_name, is_last);
    }

    Ok(())
}

/// Walk the transitive closure of a symbol's callees via the TC symbol table.
///
/// Returns the symbols that do not yet have compiled code pointers in the GOT.
/// The result is in dependency order (callees before callers) suitable for
/// sequential compilation.
fn collect_transitive_uncompiled_deps(
    tc: &cranelisp_typecheck::TypeChecker,
    inmem_worker: &InMemWorkerState,
    module: &ModuleFullPath,
    start_symbol: &Symbol,
) -> Vec<(ModuleFullPath, Symbol)> {
    use std::collections::HashSet;
    use std::collections::VecDeque;

    let mut visited: HashSet<(ModuleFullPath, Symbol)> = HashSet::new();
    let mut queue: VecDeque<(ModuleFullPath, Symbol)> = VecDeque::new();
    let mut result: Vec<(ModuleFullPath, Symbol)> = Vec::new();

    // Seed with the starting symbol's callees.
    if let Some(table) = tc.module_table(module)
        && let Some(entry) = table.get(start_symbol.as_ref())
    {
        for callee in entry.callees() {
            let key = (callee.module.clone(), callee.symbol.clone());
            if visited.insert(key.clone()) {
                queue.push_back(key);
            }
        }
    }

    // BFS walk.
    while let Some((dep_mod, dep_sym)) = queue.pop_front() {
        // Look up this symbol's own callees and enqueue them.
        if let Some(table) = tc.module_table(&dep_mod)
            && let Some(entry) = table.get(dep_sym.as_ref())
        {
            for callee in entry.callees() {
                let key = (callee.module.clone(), callee.symbol.clone());
                if visited.insert(key.clone()) {
                    queue.push_back(key);
                }
            }
        }
        // Only include if uncompiled.
        if !has_code_ptr(inmem_worker, &dep_sym) {
            result.push((dep_mod, dep_sym));
        }
    }

    result
}

/// Compile a dependency symbol inline using the accumulated check state.
///
/// Looks up the defn from the accumulated data (it has been typechecked
/// in Pass 2 already since deps are defined before the macro) and
/// compiles it via `compile_and_register_defn`.
fn compile_dep_symbol_inline(
    tc: &cranelisp_typecheck::TypeChecker,
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    symbol: &Symbol,
    accumulator: &ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    // Build a partial CheckResult from the accumulator for codegen.
    let check = build_check_from_accumulator(tc, accumulator);

    // Look up the defn from the symbol table.
    let table = tc.symbol_table();
    let entry = table.get(symbol.as_ref()).ok_or_else(|| CranelispError::MacroError {
        message: format!("inline compile: symbol '{}' not found in module table", symbol),
        span: Span::SYNTHETIC,
    })?;

    // For Def entries, we need the defn AST. But the symbol table only stores
    // the scheme, not the AST. The defn should be available from the program
    // forms being processed. For now, this handles the case where the defn is
    // available from got_state (already registered but not yet compiled).
    // In practice, macro deps are typically compiled via the codegen sweep,
    // and this path handles rare cases of forward-referenced helpers.
    let _ = entry;

    // The defn was already typechecked; we need its AST for compilation.
    // Look it up from the GOT state's stored defns.
    let defn = inmem_worker
        .got_state
        .def_codegen
        .get(symbol)
        .and_then(|dc| dc.defn.as_ref())
        .cloned();

    if let Some(defn) = defn {
        compile_and_register_defn(inmem_worker, platform_symbols, &defn, &check)?;
    }
    // If not found in GOT defns, the symbol may be a builtin/primitive
    // that is always available — nothing to compile.

    Ok(())
}

/// Build a CheckResult from the accumulator's current state.
///
/// Used for inline macro compilation. Mono defns and default methods are
/// not needed for macro clause codegen, so they are left empty.
/// Type defs and constructor_to_type are snapshotted from the TC registry
/// (required for Sexp constructor codegen in macro clause bodies).
fn build_check_from_accumulator(
    tc: &cranelisp_typecheck::TypeChecker,
    accumulator: &ModuleCheckAccumulator,
) -> CheckResult {
    let (type_defs, constructor_to_type) = tc.snapshot_type_defs();
    CheckResult {
        method_resolutions: accumulator.method_resolutions.clone(),
        constrained_fn_names: accumulator.constrained_fn_names.clone(),
        mono_defns: Vec::new(),
        expr_types: accumulator.expr_types.clone(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
        type_defs,
        constructor_to_type,
        display: None,
    }
}

/// Compile a single macro clause inline using the worker's shared state.
///
/// Mirrors `compile_single_clause` from expander.rs but uses the worker's
/// JIT lifetime management and GOT registration instead of creating an
/// isolated JIT per clause. Uses `check_form` (per-form API) instead of
/// the monolithic `tc.check()`.
#[allow(clippy::too_many_arguments)]
fn compile_macro_clause_inline(
    tc: &mut cranelisp_typecheck::TypeChecker,
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    macro_name: &Symbol,
    clause_idx: usize,
    clause: &cranelisp_frontend::MacroClause,
    span: Span,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    // Step 1: Synthesize the defn Sexp.
    let synth_sexp = cranelisp_frontend::synthesize_macro_clause_defn(
        macro_name.as_ref(),
        clause_idx,
        clause,
        span,
    );

    // Step 2: Expand quasiquotes.
    let expanded_sexp = cranelisp_frontend::expand_quasiquotes(&synth_sexp)?;

    // Step 3: Build AST with NoOpExpander (macro clause bodies use
    // quasiquote constructs, not other macros).
    let expander = NoOpExpander;
    let program = cranelisp_frontend::build_program(&[expanded_sexp], &expander)?;

    // Step 4: Typecheck using per-form check_form API (Register + CheckBody).
    let module = tc.current_module_path().clone();
    for form in &program {
        let result = tc.check_form(&module, form, CheckPass::Register, accumulator)?;
        tc.merge_form_result(&module, accumulator, result);
    }
    for form in &program {
        let result = tc.check_form(&module, form, CheckPass::CheckBody, accumulator)?;
        tc.merge_form_result(&module, accumulator, result);
    }

    // Build a CheckResult from the accumulator for codegen.
    let check = build_check_from_accumulator(tc, accumulator);

    // Step 5: Extract the defn and compile it.
    let defn = program
        .iter()
        .find_map(|tl| match tl {
            TopLevel::Defn(d) => Some(d),
            _ => None,
        })
        .ok_or_else(|| CranelispError::MacroError {
            message: format!(
                "macro clause {} for '{}' produced no defn",
                clause_idx, macro_name
            ),
            span,
        })?;

    // Compile using a special JIT that disables dealloc for macro code.
    compile_macro_defn_no_dealloc(inmem_worker, platform_symbols, defn, &check)?;

    Ok(())
}

/// Compile a macro clause defn with dealloc disabled.
///
/// Macro functions build throwaway Sexp trees that are marshalled back to
/// the compiler. Disabling dealloc prevents use-after-free on unmarshal.
fn compile_macro_defn_no_dealloc(
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    defn: &Defn,
    check: &CheckResult,
) -> Result<(), CranelispError> {
    let extra_symbols: Vec<(&str, *const u8)> = platform_symbols
        .iter()
        .map(|(name, ptr)| (name.as_str(), *ptr))
        .collect();
    let mut jit = cranelisp_backend::jit::Jit::new_with_symbols(&extra_symbols)?;
    jit.declare_intrinsics()?;

    let func_ids = jit.declare_functions(&[defn])?;
    let func_arities: HashMap<Symbol, usize> =
        func_ids.keys().map(|n| (n.clone(), defn.params().len())).collect();

    // Build compile context with dealloc disabled.
    let mut compile_ctx = jit.build_compile_context(
        check,
        &func_ids,
        &func_arities,
        None,
        None,
        None,
    );
    compile_ctx.dealloc_func_id = None;
    jit.compile_defn(defn, compile_ctx)?;

    let ptr = jit.finalize_and_get_ptr(&defn.name, defn.params().len())?;

    // Register in GOT.
    let slot = inmem_worker.got_state.ensure_slot_for(&defn.name)?;
    inmem_worker.got_state.update_slot(slot, ptr);

    let entry = inmem_worker.got_state.def_codegen.entry(defn.name.clone()).or_default();
    entry.code_ptr = Some(ptr);
    entry.got_slot = Some(slot);
    entry.param_count = Some(defn.params().len());
    entry.defn = Some(defn.clone());

    // Keep JIT alive so the function pointer remains valid.
    inmem_worker.jit_modules.push(jit);

    Ok(())
}

// ---------------------------------------------------------------------------
// Macro entry helpers
// ---------------------------------------------------------------------------

/// Generate the JIT symbol name for a macro clause function.
///
/// Must match the naming convention in `synthesize_macro_clause_defn`:
/// `__macro_{name}_clause_{idx}`.
fn macro_clause_jit_name(macro_name: &Symbol, clause_idx: usize) -> Symbol {
    Symbol::from(format!("__macro_{}_clause_{}", macro_name, clause_idx))
}

/// Check if a symbol has a compiled code pointer in the GOT.
fn has_code_ptr(inmem_worker: &InMemWorkerState, name: &Symbol) -> bool {
    inmem_worker
        .got_state
        .def_codegen
        .get(name)
        .and_then(|dc| dc.code_ptr)
        .is_some()
}

/// Build a `MacroEntry` from GOT function pointers for a macro.
///
/// Used after inline compilation to construct the entry needed by
/// `invoke_clause` and `find_matching_clause`.
fn build_macro_entry_from_got(
    inmem_worker: &InMemWorkerState,
    info: &cranelisp_frontend::DefmacroInfo,
) -> Result<MacroEntry, CranelispError> {
    let mut clauses = Vec::new();

    for (idx, clause) in info.clauses.iter().enumerate() {
        let clause_name = macro_clause_jit_name(&info.name, idx);
        let code_ptr = inmem_worker
            .got_state
            .def_codegen
            .get(&clause_name)
            .and_then(|dc| dc.code_ptr)
            .ok_or_else(|| CranelispError::MacroError {
                message: format!(
                    "macro clause '{}' not compiled (expected in GOT)",
                    clause_name
                ),
                span: info.span,
            })?;

        clauses.push(MacroClauseEntry {
            func_ptr: code_ptr,
            params: clause.fixed_params.clone(),
            rest_param: clause.rest_param.clone(),
        });
    }

    Ok(MacroEntry {
        clauses,
        docstring: info.docstring.clone(),
    })
}

/// Build a macro map for all macros in the module (for recursive expansion).
fn build_all_macro_entries(
    inmem_worker: &InMemWorkerState,
    macro_infos: &[(Symbol, cranelisp_frontend::DefmacroInfo, Sexp)],
) -> Result<HashMap<Symbol, MacroEntry>, CranelispError> {
    let mut map = HashMap::new();
    for (name, info, _) in macro_infos {
        // Only include macros that have been compiled.
        let all_compiled = info.clauses.iter().enumerate().all(|(idx, _)| {
            let clause_name = macro_clause_jit_name(name, idx);
            has_code_ptr(inmem_worker, &clause_name)
        });
        if all_compiled {
            let entry = build_macro_entry_from_got(inmem_worker, info)?;
            map.insert(name.clone(), entry);
        }
    }
    Ok(map)
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

/// Inject a wildcard import of the `macros` module into the current module.
///
/// Macros need Sexp constructors (SexpSym, SexpInt, SCons, SNil, etc.)
/// which live in the synthetic `macros` module.
fn inject_macros_import(
    tc: &mut cranelisp_typecheck::TypeChecker,
) -> Result<(), CranelispError> {
    let import_spec = ImportSpec {
        module_path: ModuleFullPath::from("macros"),
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

                match process_module_forms(
                    tc, scheduler, inmem_worker, platform_symbols,
                    &module, sexps,
                ) {
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
                // Step 4: macro deps compiled inline in process_module_forms.
                // Step 5+: cross-module macro deps dispatched here.
                unreachable!(
                    "BlockingJitCodegen not expected in Step 4 single-module mode"
                );
            }
            Some(PriorityWork::JitCodegen(_module, _symbol)) => {
                // Not needed in Step 3 — level 4 deferred.
            }
            None => break,
        }
    }
    Ok(())
}
