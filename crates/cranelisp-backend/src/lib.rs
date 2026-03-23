// cranelisp-backend: Cranelift IR codegen, JIT, RC emission, caching, linking.
//
// Public API:
// - compile_program: batch compilation of a full program
// - compile_expr_with_got: compile a single expression, returning CompiledExpr (REPL)
// - compile_and_run_expr_with_got: compile and execute a single expression (REPL, convenience)
// - Jit, ModuleCodegenState: exposed for REPL session management
// - build_isa: ISA construction for JIT and ObjectModule (re-exported from cache::object)

pub mod cache;

// Re-export build_isa at the crate root for convenient access.
// This is the single ISA construction point (architecture decision 7).
pub use cache::object::build_isa;
pub mod codegen_types;
pub mod exe;
pub mod compiler;
pub mod display;
pub mod got;
pub mod heap;
pub mod jit;
pub mod operators;

use std::collections::HashMap;

use cranelift_module::FuncId;

use cranelisp_types::{
    CheckResult, CompileMode, CranelispError, Defn, Expr, Program, Span, Symbol, TopLevel,
    Warning,
};

use crate::jit::Jit;

/// Result of setting up interactive GOT: (slot_assignments, codegen_state).
type InteractiveGotResult = (Option<HashMap<Symbol, usize>>, Option<got::ModuleCodegenState>);

/// Result of compiling a batch program. Holds the JIT and entry point
/// so the caller can execute and then drop the JIT.
pub struct CompiledProgram {
    // Kept alive so JIT-compiled code pointers remain valid.
    #[allow(dead_code)]
    jit: Jit,
    entry_ptr: *const u8,
    // Kept alive for Interactive mode GOT lifetime.
    #[allow(dead_code)]
    _got_state: Option<got::ModuleCodegenState>,
    /// Warnings accumulated during codegen.
    pub warnings: Vec<Warning>,
}

impl CompiledProgram {
    /// Execute the compiled program.
    ///
    /// # Safety
    ///
    /// The entry_ptr must point to valid JIT-compiled code with the signature
    /// `extern "C" fn() -> i64`. This is guaranteed when CompiledProgram was
    /// produced by `compile_program`.
    pub unsafe fn execute(&self) -> Result<i64, CranelispError> {
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(self.entry_ptr) };
        Ok(func())
    }
}

/// Result of compiling a single REPL expression. Holds the JIT alive so
/// the caller can execute the compiled function pointer at its leisure.
/// This enables the caller to separately time compilation and evaluation.
pub struct CompiledExpr {
    // Kept alive so the compiled function pointer remains valid.
    #[allow(dead_code)]
    jit: Jit,
    func_ptr: *const u8,
}

impl CompiledExpr {
    /// Execute the compiled expression and return the i64 result.
    ///
    /// # Safety
    ///
    /// The func_ptr must point to valid JIT-compiled code with the signature
    /// `extern "C" fn() -> i64`. This is guaranteed when CompiledExpr was
    /// produced by `compile_expr_with_got`.
    pub unsafe fn execute(&self) -> i64 {
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(self.func_ptr) };
        func()
    }
}

/// Collected defn references and their metadata, produced by the first phase
/// of `compile_program`.
struct CollectedDefns<'a> {
    /// Regular (non-constrained) defns from the program.
    defns: Vec<&'a Defn>,
    /// Extra defns owned by this struct (default method impls + mono specializations).
    extra_defns: Vec<Defn>,
    /// Function IDs declared in the JIT module.
    /// Maps **bare** function names to FuncIds (for codegen lookup).
    func_ids: HashMap<Symbol, FuncId>,
    /// Function parameter counts for closure wrapper generation.
    func_arities: HashMap<Symbol, usize>,
    /// Maps bare function names to the JIT-visible (possibly module-qualified) names.
    /// Empty when no prefix is used (single-module compilation).
    jit_names: HashMap<Symbol, Symbol>,
}

/// Compile a batch program: declare all functions, compile them, finalize.
///
/// The last zero-arg function in the program is the entry point.
/// Returns a CompiledProgram that can be executed.
pub fn compile_program(
    program: &Program,
    check: &CheckResult,
    mode: CompileMode,
) -> Result<CompiledProgram, CranelispError> {
    let mut jit = Jit::new()?;
    jit.declare_intrinsics()?;

    // Phase 1: Collect defns, declare functions, build arity map.
    let collected = collect_and_declare_defns(program, check, &mut jit, None)?;

    // Phase 2: Set up GOT for Interactive mode.
    let (got_slots, mut got_state) =
        setup_interactive_got(&collected, mode)?;

    let got_base_ptr = got_state.as_mut().map(|s| s.got_base_ptr() as i64);

    // Build the compilation context once for all functions.
    // No cross-module GOT for single-module compile_program.
    let compile_ctx = jit.build_compile_context(
        check, mode, &collected.func_ids, &collected.func_arities,
        got_slots.as_ref(), got_base_ptr, None,
    );

    // Compile each regular function.
    for defn in &collected.defns {
        jit.compile_defn(defn, compile_ctx)?;
    }

    // Compile default method defns with the main resolutions.
    for defn in &check.default_method_defns {
        jit.compile_defn(defn, compile_ctx)?;
    }

    // Compile mono specializations with their per-specialization resolutions.
    compile_mono_defns(
        &mut jit, check, mode, &collected.func_ids, &collected.func_arities,
        got_slots.as_ref(), got_base_ptr,
    )?;

    // Phase 3: Find entry, finalize JIT, populate GOT, build result.
    find_entry_and_finalize(
        &collected.defns, jit, &collected.func_ids,
        got_slots, got_state,
    )
}

/// Phase 1: Collect all defns from the program (skipping constrained fn base
/// definitions), collect extra defns (default methods + mono specializations),
/// declare all functions in the JIT, and build the arity map.
///
/// When `jit_prefix` is Some, function names are prefixed with `"{prefix}/"`
/// in the JIT to avoid collisions in a shared multi-module JIT. The returned
/// `func_ids` still maps bare names to FuncIds for the current module's codegen.
fn collect_and_declare_defns<'a>(
    program: &'a Program,
    check: &CheckResult,
    jit: &mut Jit,
    jit_prefix: Option<&str>,
) -> Result<CollectedDefns<'a>, CranelispError> {
    // Collect regular defns, skipping constrained fn base definitions.
    // Constrained fns are templates — only their monomorphised specializations
    // (in check.mono_defns) are compiled.
    let defns: Vec<&Defn> = program
        .iter()
        .filter_map(|tl| match tl {
            TopLevel::Defn(defn) => {
                if check.constrained_fn_names.contains(&defn.name) {
                    None // Skip constrained fn base defs — templates only
                } else {
                    Some(defn)
                }
            }
            _ => None,
        })
        .collect();

    // Collect additional defns: default method impls and mono specializations.
    let extra_defns = collect_extra_defns(check);

    if defns.is_empty() && extra_defns.is_empty() {
        return Err(CranelispError::CodegenError {
            message: "no function definitions in program".into(),
            span: Span::SYNTHETIC,
        });
    }

    // Build full list of defn references for declaration.
    let mut all_defn_refs: Vec<&Defn> = defns.clone();
    for d in &extra_defns {
        all_defn_refs.push(d);
    }

    // Declare all functions first (so they can reference each other).
    // When a prefix is provided, JIT symbol names are module-qualified to
    // avoid collisions, but func_ids maps bare names for codegen.
    let (func_ids, jit_names) = if let Some(prefix) = jit_prefix {
        jit.declare_functions_prefixed(&all_defn_refs, prefix)?
    } else {
        let ids = jit.declare_functions(&all_defn_refs)?;
        (ids, HashMap::new())
    };

    // Build function arity map for named-function-as-value closure wrappers.
    let func_arities: HashMap<Symbol, usize> = all_defn_refs
        .iter()
        .map(|d| (d.name.clone(), d.params.len()))
        .collect();

    Ok(CollectedDefns { defns, extra_defns, func_ids, func_arities, jit_names })
}

/// Phase 2: In Interactive mode, set up a temporary GOT so GOT-indirect calls
/// work. In Batch/Release mode, returns (None, None).
fn setup_interactive_got(
    collected: &CollectedDefns<'_>,
    mode: CompileMode,
) -> Result<InteractiveGotResult, CranelispError> {
    if mode == CompileMode::Interactive {
        let mut state = got::ModuleCodegenState::new();
        let mut slots = HashMap::new();

        // Build the combined iterator over regular + extra defns.
        let all_names = collected.defns.iter().map(|d| &d.name)
            .chain(collected.extra_defns.iter().map(|d| &d.name));

        for name in all_names {
            let slot = state.ensure_slot_for(name)?;
            slots.insert(name.clone(), slot);
        }
        Ok((Some(slots), Some(state)))
    } else {
        Ok((None, None))
    }
}

/// Phase 3: Find the last zero-arg defn as entry point, finalize the JIT,
/// populate GOT slots (Interactive mode), and build the CompiledProgram.
fn find_entry_and_finalize(
    defns: &[&Defn],
    mut jit: Jit,
    func_ids: &HashMap<Symbol, FuncId>,
    got_slots: Option<HashMap<Symbol, usize>>,
    mut got_state: Option<got::ModuleCodegenState>,
) -> Result<CompiledProgram, CranelispError> {
    // Find the entry function (last zero-arg defn).
    let entry_defn = defns
        .iter()
        .rev()
        .find(|d| d.params.is_empty())
        .ok_or_else(|| CranelispError::CodegenError {
            message: "no zero-arg function to use as entry point".into(),
            span: Span::SYNTHETIC,
        })?;

    let entry_ptr = jit.finalize_and_get_ptr(&entry_defn.name, 0)?;

    // In Interactive mode, populate GOT slots with finalized function pointers.
    if let (Some(slots), Some(state)) = (&got_slots, &mut got_state) {
        for (name, &slot) in slots {
            if let Some(&func_id) = func_ids.get(name) {
                let ptr = jit.get_finalized_ptr(func_id);
                state.update_slot(slot, ptr);
            }
        }
    }

    Ok(CompiledProgram {
        jit,
        entry_ptr,
        // Keep GOT state alive alongside the JIT so code pointers remain valid.
        _got_state: got_state,
        warnings: Vec::new(),
    })
}

/// Collect extra defns from CheckResult: default method impls and mono specializations.
///
/// These are additional functions that need to be declared and compiled alongside
/// the regular program defns.
fn collect_extra_defns(check: &CheckResult) -> Vec<Defn> {
    let mut extras = Vec::new();
    for d in &check.default_method_defns {
        extras.push(d.clone());
    }
    for mono in &check.mono_defns {
        extras.push(mono.defn.clone());
    }
    extras
}

/// Compile monomorphised specializations with their per-specialization resolutions.
///
/// Each MonoDefn carries its own method_resolutions (from the specific type
/// instantiation). We build a temporary CheckResult overlay for each one.
fn compile_mono_defns(
    jit: &mut Jit,
    check: &CheckResult,
    mode: CompileMode,
    func_ids: &HashMap<Symbol, FuncId>,
    func_arities: &HashMap<Symbol, usize>,
    got_slots: Option<&HashMap<Symbol, usize>>,
    got_base_ptr: Option<i64>,
) -> Result<(), CranelispError> {
    for mono in &check.mono_defns {
        // Merge base resolutions with per-specialization resolutions.
        let mut merged = check.method_resolutions.clone();
        merged.extend(mono.resolutions.clone());

        // I5 fix: Use the per-mono expr_types subset instead of cloning the
        // full program expr_types map. Falls back to the full map if the
        // per-mono subset is empty (before /typecheck populates it).
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

        let ctx = jit.build_compile_context(
            &mono_check, mode, func_ids, func_arities, got_slots, got_base_ptr, None,
        );
        jit.compile_defn(&mono.defn, ctx)?;
    }
    Ok(())
}

/// Result of compiling a module's program into a shared JIT.
///
/// Holds function name/arity pairs for symbols that downstream
/// modules may need to reference.
pub struct CompiledModuleInfo {
    /// Function names and their param counts (for downstream import declarations).
    pub func_signatures: Vec<(Symbol, usize)>,
    /// Warnings accumulated during codegen.
    pub warnings: Vec<Warning>,
}

/// Compile a module's program into an existing shared JIT (no finalize).
///
/// Used by the multi-module pipeline: all modules compile into one JIT,
/// which is finalized once after all modules are compiled. This allows
/// cross-module function calls to resolve via shared JIT symbol tables.
///
/// `module_prefix` is the module path (e.g., `"core.list"` or `"main"`).
/// Function names are prefixed with `"{module_prefix}/"` in the JIT to
/// avoid name collisions between modules (e.g., stdlib `fold` vs user `fold`).
///
/// `prior_funcs` lists `(name, param_count)` from previously-compiled
/// dependency modules. Names are module-qualified (e.g., `"core.list/fold"`).
pub fn compile_module_program(
    program: &Program,
    check: &CheckResult,
    mode: CompileMode,
    jit: &mut Jit,
    prior_funcs: &[(Symbol, usize)],
    module_prefix: &str,
) -> Result<CompiledModuleInfo, CranelispError> {
    // Phase 1: Collect defns, declare them with module-qualified names in
    // the shared JIT to avoid collisions. The returned func_ids map bare
    // names to FuncIds for this module's codegen.
    let collected = collect_and_declare_defns(
        program, check, jit, Some(module_prefix),
    )?;

    // Build merged func_ids from this module + prior dependencies.
    // The current module's func_ids maps bare names → FuncIds.
    // Prior funcs are module-qualified (e.g., "core.list/fold") or aliases
    // (e.g., "list/fold") that refer to the same underlying function.
    let mut merged_func_ids = collected.func_ids.clone();

    for (name, param_count) in prior_funcs {
        if merged_func_ids.contains_key(name) {
            continue; // Already declared (e.g., current module defines same name)
        }

        // Check if this is an alias for a function already in merged_func_ids.
        // Aliases share the same bare name (e.g., "list/fold" and "core.list/fold"
        // both have bare name "fold"). If the bare name is already mapped, reuse
        // that FuncId instead of declaring a new import (which would create an
        // unresolvable Import function in the JIT).
        if let Some(slash_pos) = name.as_ref().rfind('/') {
            let bare_name = Symbol::from(&name.as_ref()[slash_pos + 1..]);
            if let Some(&existing_func_id) = merged_func_ids.get(&bare_name) {
                merged_func_ids.insert(name.clone(), existing_func_id);
                continue;
            }
        }

        // Declare as an imported function in the shared JIT.
        // The qualified name (e.g., "core.list/fold") matches an existing
        // JIT symbol from the prior module's prefixed declaration.
        jit.declare_imported_functions(
            &[(name.clone(), *param_count)],
            &mut merged_func_ids,
        )?;

        // Also register the bare name (after the last '/') in func_ids,
        // since the AST uses bare names for imported functions. Only add
        // if the current module doesn't already define a function with
        // that bare name (local definitions shadow imports).
        if let Some(slash_pos) = name.as_ref().rfind('/') {
            let bare_name = Symbol::from(&name.as_ref()[slash_pos + 1..]);
            if !merged_func_ids.contains_key(&bare_name) {
                let func_id = *merged_func_ids.get(name)
                    .expect("just declared");
                merged_func_ids.insert(bare_name, func_id);
            }
        }
    }

    let mut merged_arities: HashMap<Symbol, usize> = collected.func_arities.clone();
    for (name, count) in prior_funcs {
        merged_arities.insert(name.clone(), *count);
        // Also register bare-name arities for codegen lookup.
        if let Some(slash_pos) = name.as_ref().rfind('/') {
            let bare_name = Symbol::from(&name.as_ref()[slash_pos + 1..]);
            merged_arities.entry(bare_name).or_insert(*count);
        }
    }

    // Build compile context with merged symbol tables.
    let compile_ctx = jit.build_compile_context(
        check, mode, &merged_func_ids, &merged_arities,
        None, None, None,
    );

    // Compile each regular function.
    for defn in &collected.defns {
        jit.compile_defn(defn, compile_ctx)?;
    }

    // Compile default method defns.
    for defn in &check.default_method_defns {
        jit.compile_defn(defn, compile_ctx)?;
    }

    // Compile mono specializations.
    compile_mono_defns(
        jit, check, mode, &merged_func_ids, &merged_arities,
        None, None,
    )?;

    // Collect this module's function signatures for downstream modules.
    // Use the JIT-visible names (which may be module-qualified if there
    // was a collision with a prior module's function of the same name).
    let func_signatures: Vec<(Symbol, usize)> = collected
        .func_arities
        .iter()
        .map(|(name, arity)| {
            let jit_name = collected.jit_names.get(name)
                .cloned()
                .unwrap_or_else(|| name.clone());
            (jit_name, *arity)
        })
        .collect();

    Ok(CompiledModuleInfo {
        func_signatures,
        warnings: Vec::new(),
    })
}

/// Compile a single expression into a `CompiledExpr` without executing it.
///
/// Wraps the expression in a synthetic zero-arg function and compiles it.
/// The caller can then call `CompiledExpr::execute()` to run it. This
/// separation enables the caller to time compilation and evaluation independently.
///
/// If `got_state` is provided, GOT-indirect calls are used.
pub fn compile_expr_with_got(
    expr: &Expr,
    check: &CheckResult,
    mode: CompileMode,
    got_state: Option<&mut got::ModuleCodegenState>,
) -> Result<CompiledExpr, CranelispError> {
    compile_expr_with_got_and_symbols(expr, check, mode, got_state, &[])
}

/// Compile an expression using GOT-indirect calls, with extra JIT symbols.
///
/// Same as `compile_expr_with_got` but accepts additional symbols (e.g.,
/// platform function pointers) to register in the JIT.
pub fn compile_expr_with_got_and_symbols(
    expr: &Expr,
    check: &CheckResult,
    mode: CompileMode,
    got_state: Option<&mut got::ModuleCodegenState>,
    extra_symbols: &[(&str, *const u8)],
) -> Result<CompiledExpr, CranelispError> {
    let mut jit = Jit::new_with_symbols(extra_symbols)?;

    // Declare runtime intrinsics (Ring 1 heap infrastructure).
    jit.declare_intrinsics()?;

    // Wrap expression in a synthetic zero-arg function.
    let wrapper_name = Symbol::from("__repl_expr__");
    let wrapper_defn = Defn {
        name: wrapper_name.clone(),
        params: vec![],
        param_annotations: vec![],
        visibility: cranelisp_types::Visibility::Public,
        body: expr.clone(),
        docstring: None,
        span: expr.span(),
    };

    let func_ids = jit.declare_functions(&[&wrapper_defn])?;

    // Get GOT info and function arities if available.
    let (got_slots, got_base_ptr, func_arities) = if let Some(state) = got_state {
        let mut slots: HashMap<Symbol, usize> = HashMap::new();
        let mut arities: HashMap<Symbol, usize> = HashMap::new();
        for (name, dc) in &state.def_codegen {
            if let Some(slot) = dc.got_slot {
                slots.insert(name.clone(), slot);
            }
            if let Some(pc) = dc.param_count {
                arities.insert(name.clone(), pc);
            }
        }
        let base = state.got_base_ptr() as i64;
        (Some(slots), Some(base), arities)
    } else {
        (None, None, HashMap::new())
    };

    let compile_ctx = jit.build_compile_context(
        check,
        mode,
        &func_ids,
        &func_arities,
        got_slots.as_ref(),
        got_base_ptr,
        None, // No cross-module GOT for single-expression compilation.
    );

    jit.compile_defn(&wrapper_defn, compile_ctx)?;

    let code_ptr = jit.finalize_and_get_ptr(&wrapper_name, 0)?;

    Ok(CompiledExpr {
        jit,
        func_ptr: code_ptr,
    })
}

/// Compile and execute a single expression in Interactive mode (convenience wrapper).
///
/// Wraps the expression in a synthetic zero-arg function, compiles it,
/// executes it, and returns the i64 result.
///
/// If `got_state` is provided, GOT-indirect calls are used.
pub fn compile_and_run_expr_with_got(
    expr: &Expr,
    check: &CheckResult,
    mode: CompileMode,
    got_state: Option<&mut got::ModuleCodegenState>,
) -> Result<i64, CranelispError> {
    let compiled = compile_expr_with_got(expr, check, mode, got_state)?;
    // SAFETY: compiled was produced by compile_expr_with_got immediately above.
    Ok(unsafe { compiled.execute() })
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{
        CheckResult, CompileMode, Defn, Expr, Span, Symbol, TopLevel,
    };
    use std::collections::{HashMap, HashSet};

    fn empty_check() -> CheckResult {
        CheckResult {
            method_resolutions: HashMap::new(),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        }
    }

    // spec: 05-definitions §5.1 — single defn compiles and executes via JIT
    #[test]
    fn test_compile_program_simple() {
        let defn = Defn {
            name: Symbol::from("main"),
            params: vec![],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::IntLit {
                value: 42,
                span: Span::new(0, 2),
            },
            docstring: None,
            span: Span::new(0, 20),
        };

        let program: Program = vec![TopLevel::Defn(defn)];
        let check = empty_check();

        let compiled = compile_program(&program, &check, CompileMode::Batch).unwrap();
        let value = unsafe { compiled.execute().unwrap() };
        assert_eq!(value, 42);
    }

    // spec: 12-runtime §12.6 — batch mode requires main entry point
    #[test]
    fn test_compile_program_no_defns() {
        let program: Program = vec![];
        let check = empty_check();

        let result = compile_program(&program, &check, CompileMode::Batch);
        assert!(result.is_err());
    }

    // spec: 04-expressions §4.1.1 — integer literal codegen
    #[test]
    fn test_compile_and_run_expr() {
        let expr = Expr::IntLit {
            value: 99,
            span: Span::new(0, 2),
        };
        let check = empty_check();

        let value = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None).unwrap();
        assert_eq!(value, 99);
    }

    // spec: 05-definitions §5.1 — defn compiles in interactive (REPL) mode
    #[test]
    fn test_compile_program_interactive_mode() {
        let defn = Defn {
            name: Symbol::from("main"),
            params: vec![],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::IntLit {
                value: 7,
                span: Span::new(0, 1),
            },
            docstring: None,
            span: Span::new(0, 20),
        };

        let program: Program = vec![TopLevel::Defn(defn)];
        let check = empty_check();

        let compiled = compile_program(&program, &check, CompileMode::Interactive).unwrap();
        let value = unsafe { compiled.execute().unwrap() };
        assert_eq!(value, 7);
    }

    // spec: 04-expressions §4.1.1 — integer literal codegen with GOT state
    #[test]
    fn test_compile_and_run_expr_with_got_state() {
        let expr = Expr::IntLit {
            value: 55,
            span: Span::new(0, 2),
        };
        let check = empty_check();
        let mut got = got::ModuleCodegenState::new();

        let value = compile_and_run_expr_with_got(
            &expr,
            &check,
            CompileMode::Interactive,
            Some(&mut got),
        ).unwrap();
        assert_eq!(value, 55);
    }

    // spec: 05-definitions §5.13.1 — multiple function definitions compile together
    #[test]
    fn test_compile_program_multiple_defns() {
        // Two functions: helper and main. Main returns 100.
        let helper = Defn {
            name: Symbol::from("helper"),
            params: vec![Symbol::from("x")],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::Var {
                name: Symbol::from("x"),
                span: Span::new(20, 21),
            },
            docstring: None,
            span: Span::new(10, 30),
        };

        let main_defn = Defn {
            name: Symbol::from("main"),
            params: vec![],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::IntLit {
                value: 100,
                span: Span::new(40, 43),
            },
            docstring: None,
            span: Span::new(35, 50),
        };

        let program: Program = vec![TopLevel::Defn(helper), TopLevel::Defn(main_defn)];
        let check = empty_check();

        let compiled = compile_program(&program, &check, CompileMode::Batch).unwrap();
        let value = unsafe { compiled.execute().unwrap() };
        assert_eq!(value, 100);
    }

    // spec: 04-expressions §4.1.3 — boolean literal codegen
    #[test]
    fn test_compile_and_run_expr_bool() {
        let expr = Expr::BoolLit {
            value: true,
            span: Span::new(0, 4),
        };
        let check = empty_check();

        let value = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None).unwrap();
        assert_eq!(value, 1);
    }

    // --- Ring 1 tests ---

    // spec: 04-expressions §4.1.4 — string literal codegen, heap allocation
    #[test]
    fn test_compile_string_literal() {
        let expr = Expr::StringLit {
            value: "hello".to_string(),
            span: Span::new(0, 7),
        };
        let check = empty_check();

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "string literal should compile: {result:?}");
        let ptr = result.unwrap();
        // ptr should be a heap pointer (> NULLARY_TAG_THRESHOLD)
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Read back the string content via runtime API.
        let s = unsafe { cranelisp_runtime::read_string_as_str(ptr) };
        assert_eq!(s, "hello");

        // Clean up the allocation.
        cranelisp_runtime::heap_dealloc(ptr);
    }

    // spec: 04-expressions §4.1.4 — empty string literal codegen
    #[test]
    fn test_compile_empty_string_literal() {
        let expr = Expr::StringLit {
            value: String::new(),
            span: Span::new(0, 2),
        };
        let check = empty_check();

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "empty string should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        let s = unsafe { cranelisp_runtime::read_string_as_str(ptr) };
        assert_eq!(s, "");

        cranelisp_runtime::heap_dealloc(ptr);
    }

    // spec: 12-runtime §12.1.4 — data constructor heap layout [tag | fields]
    #[test]
    fn test_compile_adt_data_constructor() {
        use cranelisp_types::{ConstructorInfo, FieldInfo, Type, TypeDefInfo, TypeName};

        // Define Option type with None (tag 0) and Some (tag 1, one field).
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

        let mut constructor_to_type = HashMap::new();
        constructor_to_type.insert(Symbol::from("None"), type_name.clone());
        constructor_to_type.insert(Symbol::from("Some"), type_name.clone());

        // Expression: (Some 42)
        let some_span = Span::new(0, 10);
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("Some"),
                span: Span::new(1, 5),
            }),
            args: vec![Expr::IntLit {
                value: 42,
                span: Span::new(6, 8),
            }],
            span: some_span,
        };

        let check = CheckResult {
            method_resolutions: HashMap::new(),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs,
            constructor_to_type,
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "ADT constructor should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Verify the heap layout: [header(16) | tag(1) | field(42)]
        unsafe {
            let base = ptr as *const u8;
            let tag = *(base.add(16) as *const i64);
            assert_eq!(tag, 1, "tag should be 1 for Some");
            let val = *(base.add(24) as *const i64);
            assert_eq!(val, 42, "field should be 42");
        }

        cranelisp_runtime::heap_dealloc(ptr);
    }

    // spec: 04-expressions §4.8 — match expression with constructor patterns and field extraction
    #[test]
    fn test_compile_match_with_fields() {
        use cranelisp_types::{
            ConstructorInfo, FieldInfo, MatchArm, Pattern, Type, TypeDefInfo, TypeName,
        };

        // Option type as above.
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

        let mut constructor_to_type = HashMap::new();
        constructor_to_type.insert(Symbol::from("None"), type_name.clone());
        constructor_to_type.insert(Symbol::from("Some"), type_name.clone());

        // (match (Some 99) [(Some x) x (None) 0])
        let some_span = Span::new(10, 20);
        let match_span = Span::new(0, 50);
        let scrutinee = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("Some"),
                span: Span::new(11, 15),
            }),
            args: vec![Expr::IntLit {
                value: 99,
                span: Span::new(16, 18),
            }],
            span: some_span,
        };

        let expr = Expr::Match {
            scrutinee: Box::new(scrutinee),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("Some"),
                        bindings: vec![Symbol::from("x")],
                        span: Span::new(22, 30),
                    },
                    body: Expr::Var {
                        name: Symbol::from("x"),
                        span: Span::new(31, 32),
                    },
                    span: Span::new(22, 32),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("None"),
                        bindings: vec![],
                        span: Span::new(34, 40),
                    },
                    body: Expr::IntLit {
                        value: 0,
                        span: Span::new(41, 42),
                    },
                    span: Span::new(34, 42),
                },
            ],
            span: match_span,
            compiler_generated: false,
        };

        let check = CheckResult {
            method_resolutions: HashMap::new(),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs,
            constructor_to_type,
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "match with fields should compile: {result:?}");
        assert_eq!(result.unwrap(), 99, "match should extract field value");
    }

    // spec: 04-expressions §4.5 — lambda capture, closure allocation, and indirect call
    #[test]
    fn test_compile_lambda_closure() {
        // (let [n 5] ((fn [x] (+ n x)) 10))
        // This tests: lambda capture of 'n', closure allocation, closure call.
        use cranelisp_types::ResolvedCall;

        let add_span = Span::new(30, 37);
        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            add_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("add-i64"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("n"),
                Expr::IntLit {
                    value: 5,
                    span: Span::new(5, 6),
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Lambda {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![],
                    body: Box::new(Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("+"),
                            span: Span::new(31, 32),
                        }),
                        args: vec![
                            Expr::Var {
                                name: Symbol::from("n"),
                                span: Span::new(33, 34),
                            },
                            Expr::Var {
                                name: Symbol::from("x"),
                                span: Span::new(35, 36),
                            },
                        ],
                        span: add_span,
                    }),
                    span: Span::new(10, 40),
                }),
                args: vec![Expr::IntLit {
                    value: 10,
                    span: Span::new(42, 44),
                }],
                span: Span::new(10, 45),
            }),
            span: Span::new(0, 46),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "closure should compile: {result:?}");
        assert_eq!(result.unwrap(), 15, "5 + 10 = 15");
    }

    // --- Vec codegen tests ---

    // spec: 04-expressions §4.10 — empty Vec literal codegen
    #[test]
    fn test_compile_empty_vec_literal() {
        let expr = Expr::VecLit {
            elements: vec![],
            span: Span::new(0, 2),
        };
        let check = empty_check();

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "empty vec literal should compile: {result:?}");
        let ptr = result.unwrap();
        // ptr should be a heap pointer (> NULLARY_TAG_THRESHOLD)
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Verify len == 0.
        assert_eq!(cranelisp_runtime::vec_len(ptr), 0);

        // Clean up.
        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: 04-expressions §4.10 — Vec literal with integer elements
    #[test]
    fn test_compile_vec_literal_with_ints() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 10, span: Span::new(1, 3) },
                Expr::IntLit { value: 20, span: Span::new(4, 6) },
                Expr::IntLit { value: 30, span: Span::new(7, 9) },
            ],
            span: Span::new(0, 10),
        };
        let check = empty_check();

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec literal should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Verify len == 3.
        assert_eq!(cranelisp_runtime::vec_len(ptr), 3);

        // Verify element values from data buffer.
        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(heap::HeapVec::DATA_PTR_OFFSET as usize) as *const *const i64);
            assert_eq!(*data_ptr, 10);
            assert_eq!(*data_ptr.add(1), 20);
            assert_eq!(*data_ptr.add(2), 30);
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: 04-expressions §4.10 — single-element Vec literal
    #[test]
    fn test_compile_vec_literal_single_element() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 42, span: Span::new(1, 3) },
            ],
            span: Span::new(0, 4),
        };
        let check = empty_check();

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "single-element vec should compile: {result:?}");
        let ptr = result.unwrap();

        assert_eq!(cranelisp_runtime::vec_len(ptr), 1);

        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(32) as *const *const i64);
            assert_eq!(*data_ptr, 42);
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: 04-expressions §4.10 — Vec literal with boolean elements
    #[test]
    fn test_compile_vec_literal_with_bool_elements() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::BoolLit { value: true, span: Span::new(1, 5) },
                Expr::BoolLit { value: false, span: Span::new(6, 11) },
            ],
            span: Span::new(0, 12),
        };
        let check = empty_check();

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "bool vec should compile: {result:?}");
        let ptr = result.unwrap();
        assert_eq!(cranelisp_runtime::vec_len(ptr), 2);

        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(32) as *const *const i64);
            assert_eq!(*data_ptr, 1); // true
            assert_eq!(*data_ptr.add(1), 0); // false
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: appendix-a-builtins §A.3 — vec-len inline primitive codegen
    #[test]
    fn test_compile_vec_len_inline() {
        use cranelisp_types::ResolvedCall;

        // (vec-len [10 20 30])
        let vec_span = Span::new(10, 20);
        let apply_span = Span::new(0, 25);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            apply_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1, 8),
            }),
            args: vec![Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 10, span: Span::new(11, 13) },
                    Expr::IntLit { value: 20, span: Span::new(14, 16) },
                    Expr::IntLit { value: 30, span: Span::new(17, 19) },
                ],
                span: vec_span,
            }],
            span: apply_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec-len should compile: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    // spec: appendix-a-builtins §A.3 — vec-get bounds-checked index codegen
    #[test]
    fn test_compile_vec_get_inline() {
        use cranelisp_types::ResolvedCall;

        // (let [v [10 20 30]] (vec-get v 1))
        let vec_span = Span::new(8, 18);
        let get_span = Span::new(21, 35);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 10, span: Span::new(9, 11) },
                        Expr::IntLit { value: 20, span: Span::new(12, 14) },
                        Expr::IntLit { value: 30, span: Span::new(15, 17) },
                    ],
                    span: vec_span,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(22, 29),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(30, 31),
                    },
                    Expr::IntLit { value: 1, span: Span::new(32, 33) },
                ],
                span: get_span,
            }),
            span: Span::new(0, 36),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec-get should compile: {result:?}");
        assert_eq!(result.unwrap(), 20);
    }

    // spec: appendix-a-builtins §A.3 — vec-get index 0 boundary
    #[test]
    fn test_compile_vec_get_first_element() {
        use cranelisp_types::ResolvedCall;

        let vec_span = Span::new(100, 110);
        let get_span = Span::new(120, 135);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 100, span: Span::new(101, 104) },
                        Expr::IntLit { value: 200, span: Span::new(105, 108) },
                    ],
                    span: vec_span,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(121, 128),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(129, 130),
                    },
                    Expr::IntLit { value: 0, span: Span::new(131, 132) },
                ],
                span: get_span,
            }),
            span: Span::new(99, 136),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec-get index 0 should work: {result:?}");
        assert_eq!(result.unwrap(), 100);
    }

    // spec: appendix-a-builtins §A.3 — vec-get last index boundary
    #[test]
    fn test_compile_vec_get_last_element() {
        use cranelisp_types::ResolvedCall;

        let vec_span = Span::new(200, 210);
        let get_span = Span::new(220, 235);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: Span::new(201, 202) },
                        Expr::IntLit { value: 2, span: Span::new(203, 204) },
                        Expr::IntLit { value: 3, span: Span::new(205, 206) },
                    ],
                    span: vec_span,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(221, 228),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(229, 230),
                    },
                    Expr::IntLit { value: 2, span: Span::new(231, 232) },
                ],
                span: get_span,
            }),
            span: Span::new(199, 236),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec-get last index should work: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 12-runtime §12.3.3 — vec-set copy-on-write path codegen
    #[test]
    fn test_compile_vec_set_copy_path() {
        use cranelisp_types::ResolvedCall;

        // (let [v [10 20 30]] (vec-len (vec-set v 1 99)))
        // Since v is used twice (vec-set and vec-len), vec-set takes the copy path.
        let vec_span = Span::new(300, 310);
        let set_span = Span::new(320, 340);
        let len_span = Span::new(315, 345);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            set_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-set"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 10, span: Span::new(301, 303) },
                        Expr::IntLit { value: 20, span: Span::new(304, 306) },
                        Expr::IntLit { value: 30, span: Span::new(307, 309) },
                    ],
                    span: vec_span,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-len"),
                    span: Span::new(316, 323),
                }),
                args: vec![Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("vec-set"),
                        span: Span::new(321, 328),
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("v"),
                            span: Span::new(329, 330),
                        },
                        Expr::IntLit { value: 1, span: Span::new(331, 332) },
                        Expr::IntLit { value: 99, span: Span::new(333, 335) },
                    ],
                    span: set_span,
                }],
                span: len_span,
            }),
            span: Span::new(299, 346),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec-set should compile: {result:?}");
        // vec-set returns a new Vec with same length.
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 12-runtime §12.3.3 — vec-push copy-on-write path codegen
    #[test]
    fn test_compile_vec_push_copy_path() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-push [10 20] 30))
        let vec_span = Span::new(400, 410);
        let push_span = Span::new(415, 435);
        let len_span = Span::new(410, 440);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            push_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-push"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(411, 418),
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-push"),
                    span: Span::new(416, 424),
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![
                            Expr::IntLit { value: 10, span: Span::new(401, 403) },
                            Expr::IntLit { value: 20, span: Span::new(404, 406) },
                        ],
                        span: vec_span,
                    },
                    Expr::IntLit { value: 30, span: Span::new(425, 427) },
                ],
                span: push_span,
            }],
            span: len_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec-push should compile: {result:?}");
        // [10 20] pushed 30 -> len 3
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 04-expressions §4.3, §4.10 — Vec literal bound in let, accessed via vec-len
    #[test]
    fn test_compile_vec_literal_in_let() {
        // (let [v [1 2 3]] (vec-len v))
        use cranelisp_types::ResolvedCall;

        let vec_span = Span::new(500, 510);
        let len_span = Span::new(515, 530);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: Span::new(501, 502) },
                        Expr::IntLit { value: 2, span: Span::new(503, 504) },
                        Expr::IntLit { value: 3, span: Span::new(505, 506) },
                    ],
                    span: vec_span,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-len"),
                    span: Span::new(516, 523),
                }),
                args: vec![Expr::Var {
                    name: Symbol::from("v"),
                    span: Span::new(524, 525),
                }],
                span: len_span,
            }),
            span: Span::new(499, 531),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec in let should compile: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 04-expressions §4.10, §4.11 — Vec literal with computed elements, left-to-right eval
    #[test]
    fn test_compile_vec_literal_with_computed_elements() {
        use cranelisp_types::ResolvedCall;

        // [1 (+ 2 3) 10]
        let add_span = Span::new(603, 610);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            add_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("add-i64"),
            },
        );

        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 1, span: Span::new(601, 602) },
                Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("+"),
                        span: Span::new(604, 605),
                    }),
                    args: vec![
                        Expr::IntLit { value: 2, span: Span::new(606, 607) },
                        Expr::IntLit { value: 3, span: Span::new(608, 609) },
                    ],
                    span: add_span,
                },
                Expr::IntLit { value: 10, span: Span::new(611, 613) },
            ],
            span: Span::new(600, 614),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec with computed elements should compile: {result:?}");
        let ptr = result.unwrap();

        assert_eq!(cranelisp_runtime::vec_len(ptr), 3);
        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(32) as *const *const i64);
            assert_eq!(*data_ptr, 1);
            assert_eq!(*data_ptr.add(1), 5); // 2 + 3
            assert_eq!(*data_ptr.add(2), 10);
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: 05-definitions §5.1, 04-expressions §4.10 — Vec literal as function return value
    #[test]
    fn test_compile_vec_in_function_defn() {
        // (defn make-vec [] [1 2 3])
        // Returns a Vec literal.
        let defn = Defn {
            name: Symbol::from("make-vec"),
            params: vec![],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 1, span: Span::new(701, 702) },
                    Expr::IntLit { value: 2, span: Span::new(703, 704) },
                    Expr::IntLit { value: 3, span: Span::new(705, 706) },
                ],
                span: Span::new(700, 707),
            },
            docstring: None,
            span: Span::new(700, 710),
        };

        let program: Program = vec![TopLevel::Defn(defn)];
        let check = empty_check();

        let compiled = compile_program(&program, &check, CompileMode::Batch).unwrap();
        let ptr = unsafe { compiled.execute().unwrap() };
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");
        assert_eq!(cranelisp_runtime::vec_len(ptr), 3);

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: appendix-a-builtins §A.3 — vec-get returns correct element value
    #[test]
    fn test_compile_vec_get_verify_value() {
        use cranelisp_types::ResolvedCall;

        // (let [v [100 200 300]] (vec-get v 2))
        let vec_span = Span::new(808, 818);
        let get_span = Span::new(821, 840);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 100, span: Span::new(809, 812) },
                        Expr::IntLit { value: 200, span: Span::new(813, 816) },
                        Expr::IntLit { value: 300, span: Span::new(817, 820) },
                    ],
                    span: vec_span,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(822, 829),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(830, 831),
                    },
                    Expr::IntLit { value: 2, span: Span::new(832, 833) },
                ],
                span: get_span,
            }),
            span: Span::new(807, 841),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec-get value should compile: {result:?}");
        assert_eq!(result.unwrap(), 300);
    }

    // spec: 12-runtime §12.3.3 — vec-push on temporary Vec (COW in-place path)
    #[test]
    fn test_compile_vec_push_on_temp() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-push [1] 2))
        // vec-push on a temporary VecLit — will take COW path (temp = unique).
        let vec_span = Span::new(900, 905);
        let push_span = Span::new(910, 925);
        let len_span = Span::new(905, 930);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            push_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-push"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(906, 913),
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-push"),
                    span: Span::new(911, 919),
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![
                            Expr::IntLit { value: 1, span: Span::new(901, 902) },
                        ],
                        span: vec_span,
                    },
                    Expr::IntLit { value: 2, span: Span::new(920, 921) },
                ],
                span: push_span,
            }],
            span: len_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec-push on temp should compile: {result:?}");
        assert_eq!(result.unwrap(), 2);
    }

    // spec: 12-runtime §12.3.3 — vec-set on temporary Vec (COW in-place path)
    #[test]
    fn test_compile_vec_set_on_temp() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-set [10 20 30] 0 99))
        let vec_span = Span::new(1000, 1010);
        let set_span = Span::new(1015, 1035);
        let len_span = Span::new(1010, 1040);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            set_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-set"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1011, 1018),
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-set"),
                    span: Span::new(1016, 1023),
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![
                            Expr::IntLit { value: 10, span: Span::new(1001, 1003) },
                            Expr::IntLit { value: 20, span: Span::new(1004, 1006) },
                            Expr::IntLit { value: 30, span: Span::new(1007, 1009) },
                        ],
                        span: vec_span,
                    },
                    Expr::IntLit { value: 0, span: Span::new(1024, 1025) },
                    Expr::IntLit { value: 99, span: Span::new(1026, 1028) },
                ],
                span: set_span,
            }],
            span: len_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec-set on temp should compile: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 04-expressions §4.10 — Vec literal in interactive (REPL) mode
    #[test]
    fn test_compile_vec_literal_interactive_mode() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 42, span: Span::new(1101, 1103) },
            ],
            span: Span::new(1100, 1104),
        };
        let check = empty_check();
        let mut got = got::ModuleCodegenState::new();

        let result = compile_and_run_expr_with_got(
            &expr, &check, CompileMode::Interactive, Some(&mut got),
        );
        assert!(result.is_ok(), "vec in interactive mode should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024);
        assert_eq!(cranelisp_runtime::vec_len(ptr), 1);

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: appendix-a-builtins §A.3 — vec-len on empty Vec returns 0
    #[test]
    fn test_compile_vec_empty_len() {
        use cranelisp_types::ResolvedCall;

        // (vec-len [])
        let vec_span = Span::new(1200, 1202);
        let len_span = Span::new(1195, 1210);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1196, 1203),
            }),
            args: vec![Expr::VecLit {
                elements: vec![],
                span: vec_span,
            }],
            span: len_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "empty vec len should compile: {result:?}");
        assert_eq!(result.unwrap(), 0);
    }

    // spec: appendix-a-builtins §A.3 — vec-push on empty Vec
    #[test]
    fn test_compile_vec_push_empty_vec() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-push [] 42))
        let vec_span = Span::new(1300, 1302);
        let push_span = Span::new(1305, 1320);
        let len_span = Span::new(1300, 1325);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            push_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-push"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1301, 1308),
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-push"),
                    span: Span::new(1306, 1314),
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![],
                        span: vec_span,
                    },
                    Expr::IntLit { value: 42, span: Span::new(1315, 1317) },
                ],
                span: push_span,
            }],
            span: len_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "push to empty vec should compile: {result:?}");
        assert_eq!(result.unwrap(), 1);
    }

    // spec: appendix-a-builtins §A.3 — vec-len on empty Vec (duplicate boundary check)
    #[test]
    fn test_compile_vec_len_empty_vec() {
        use cranelisp_types::ResolvedCall;

        let len_span = Span::new(1400, 1420);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1401, 1408),
            }),
            args: vec![Expr::VecLit {
                elements: vec![],
                span: Span::new(1409, 1411),
            }],
            span: len_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 0);
    }

    // spec: 04-expressions §4.10 — nested Vec literals (Vec of Vecs)
    #[test]
    fn test_compile_nested_vec_literals() {
        // [[1 2] [3 4]] — a Vec of Vecs (nested heap values)
        let expr = Expr::VecLit {
            elements: vec![
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: Span::new(1502, 1503) },
                        Expr::IntLit { value: 2, span: Span::new(1504, 1505) },
                    ],
                    span: Span::new(1501, 1506),
                },
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 3, span: Span::new(1508, 1509) },
                        Expr::IntLit { value: 4, span: Span::new(1510, 1511) },
                    ],
                    span: Span::new(1507, 1512),
                },
            ],
            span: Span::new(1500, 1513),
        };
        let check = empty_check();

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "nested vec should compile: {result:?}");
        let outer_ptr = result.unwrap();
        assert!(outer_ptr > 1024);
        assert_eq!(cranelisp_runtime::vec_len(outer_ptr), 2);

        // First inner vec.
        unsafe {
            let base = outer_ptr as *const u8;
            let data = *(base.add(32) as *const *const i64);
            let inner1 = *data;
            assert!(inner1 > 1024, "inner vec should be heap pointer");
            assert_eq!(cranelisp_runtime::vec_len(inner1), 2);
        }

        // Clean up (inner vecs need manual cleanup since no drop glue yet).
        unsafe {
            let base = outer_ptr as *const u8;
            let data = *(base.add(32) as *const *const i64);
            cranelisp_runtime::vec_drop(*data, 0);
            cranelisp_runtime::vec_drop(*data.add(1), 0);
        }
        cranelisp_runtime::vec_drop(outer_ptr, 0);
    }

    // spec: 04-expressions §4.10 — large Vec literal (10 elements)
    #[test]
    fn test_compile_vec_large_literal() {
        // [0 1 2 3 4 5 6 7 8 9] — 10 elements
        let elements: Vec<Expr> = (0..10)
            .map(|i| Expr::IntLit {
                value: i,
                span: Span::new(1600 + (i as u32) * 2, 1602 + (i as u32) * 2),
            })
            .collect();

        let expr = Expr::VecLit {
            elements,
            span: Span::new(1600, 1620),
        };
        let check = empty_check();

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "large vec should compile: {result:?}");
        let ptr = result.unwrap();
        assert_eq!(cranelisp_runtime::vec_len(ptr), 10);

        unsafe {
            let base = ptr as *const u8;
            let data = *(base.add(32) as *const *const i64);
            for i in 0..10 {
                assert_eq!(*data.add(i), i as i64);
            }
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // --- Ring 2A: TraitMethod dispatch tests ---

    // spec: 07-traits §7.7, appendix-a-builtins §A.3 — Num.+ trait dispatch inlines to add-i64
    #[test]
    fn test_trait_method_dispatch_inline_add() {
        // (+ 3 4) resolved as TraitMethod Num.+ on Int → should inline as iadd.
        let apply_span = Span::new(100, 110);
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: Span::new(101, 102),
            }),
            args: vec![
                Expr::IntLit { value: 3, span: Span::new(103, 104) },
                Expr::IntLit { value: 4, span: Span::new(105, 106) },
            ],
            span: apply_span,
        };

        let mut check = empty_check();
        check.method_resolutions.insert(
            apply_span,
            cranelisp_types::ResolvedCall::TraitMethod {
                trait_name: cranelisp_types::TraitName::from("Num"),
                method_name: Symbol::from("+"),
                impl_type: cranelisp_types::TypeName::from("Int"),
                mangled_name: cranelisp_types::JitSymbol::from("Num.+$Int"),
            },
        );

        let value = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None)
            .expect("TraitMethod inline add should compile");
        assert_eq!(value, 7);
    }

    // spec: 07-traits §7.7, appendix-a-builtins §A.3 — Eq.= trait dispatch on Bool
    #[test]
    fn test_trait_method_dispatch_eq_bool() {
        // (= true true) resolved as TraitMethod Eq.= on Bool → eq-bool.
        let apply_span = Span::new(200, 210);
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("="),
                span: Span::new(201, 202),
            }),
            args: vec![
                Expr::BoolLit { value: true, span: Span::new(203, 207) },
                Expr::BoolLit { value: true, span: Span::new(208, 212) },
            ],
            span: apply_span,
        };

        let mut check = empty_check();
        check.method_resolutions.insert(
            apply_span,
            cranelisp_types::ResolvedCall::TraitMethod {
                trait_name: cranelisp_types::TraitName::from("Eq"),
                method_name: Symbol::from("="),
                impl_type: cranelisp_types::TypeName::from("Bool"),
                mangled_name: cranelisp_types::JitSymbol::from("Eq.=$Bool"),
            },
        );

        let value = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None)
            .expect("TraitMethod eq-bool should compile");
        assert_eq!(value, 1); // true == true → true (1)
    }

    // spec: 07-traits §7.7 — constrained polymorphic fn skipped at definition, monomorphised at call
    #[test]
    fn test_constrained_fn_skipped_in_compile_program() {
        // A constrained fn should be skipped (not compiled).
        let defn = Defn {
            name: Symbol::from("add"),
            params: vec![Symbol::from("x"), Symbol::from("y")],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::IntLit { value: 0, span: Span::new(10, 11) },
            docstring: None,
            span: Span::new(0, 20),
        };

        let main_defn = Defn {
            name: Symbol::from("main"),
            params: vec![],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::IntLit { value: 42, span: Span::new(30, 32) },
            docstring: None,
            span: Span::new(25, 40),
        };

        let program: Program = vec![
            TopLevel::Defn(defn),
            TopLevel::Defn(main_defn),
        ];

        let mut check = empty_check();
        // Mark "add" as constrained — should be skipped during compilation.
        check.constrained_fn_names.insert(Symbol::from("add"));

        let compiled = compile_program(&program, &check, CompileMode::Batch)
            .expect("should compile with constrained fn skipped");
        let value = unsafe { compiled.execute().unwrap() };
        assert_eq!(value, 42);
    }

    // spec: 07-traits §7.7 — no default method defns produces empty extras
    #[test]
    fn test_collect_extra_defns_empty() {
        let check = empty_check();
        let extras = collect_extra_defns(&check);
        assert!(extras.is_empty());
    }

    // spec: 07-traits §7.7 — default trait methods collected as extra defns
    #[test]
    fn test_collect_extra_defns_with_defaults() {
        let mut check = empty_check();
        check.default_method_defns.push(Defn {
            name: Symbol::from("!="),
            params: vec![Symbol::from("x"), Symbol::from("y")],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::IntLit { value: 0, span: Span::new(0, 1) },
            docstring: None,
            span: Span::new(0, 10),
        });

        let extras = collect_extra_defns(&check);
        assert_eq!(extras.len(), 1);
        assert_eq!(extras[0].name, Symbol::from("!="));
    }

    // --- Cross-module GOT tests ---

    // spec: 08-modules §8.3, 12-runtime §12.2.1 — cross-module function call via GOT indirection
    #[test]
    fn test_cross_module_got_call() {
        use cranelisp_types::ModuleFullPath;

        // Step 1: Compile a function "add42" in module A's GOT.
        let add42_defn = Defn {
            name: Symbol::from("add42"),
            params: vec![Symbol::from("x")],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::IntLit {
                value: 42,
                span: Span::new(0, 2),
            },
            docstring: None,
            span: Span::new(0, 20),
        };

        let mut mod_a_got = got::ModuleCodegenState::new();
        let add42_slot = mod_a_got.ensure_slot_for(&Symbol::from("add42")).unwrap();
        mod_a_got
            .def_codegen
            .entry(Symbol::from("add42"))
            .or_default()
            .param_count = Some(1);

        // Compile and finalize add42 in its own JIT.
        let check = empty_check();
        let mut jit_a = Jit::new().unwrap();
        jit_a.declare_intrinsics().unwrap();
        let func_ids_a = jit_a.declare_functions(&[&add42_defn]).unwrap();
        let arities_a: HashMap<Symbol, usize> = vec![(Symbol::from("add42"), 1)].into_iter().collect();
        let mut slots_a = HashMap::new();
        slots_a.insert(Symbol::from("add42"), add42_slot);
        let got_base_a = mod_a_got.got_base_ptr() as i64;
        let ctx_a = jit_a.build_compile_context(
            &check, CompileMode::Interactive, &func_ids_a, &arities_a,
            Some(&slots_a), Some(got_base_a), None,
        );
        jit_a.compile_defn(&add42_defn, ctx_a).unwrap();
        let add42_ptr = jit_a.finalize_and_get_ptr(&Symbol::from("add42"), 1).unwrap();
        mod_a_got.update_slot(add42_slot, add42_ptr);

        // Step 2: Compile a caller expression that calls "add42" via cross-module GOT.
        // The expression is just `(add42 10)` which should return 42 (our stub ignores x).
        let caller_expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add42"),
                span: Span::new(100, 105),
            }),
            args: vec![Expr::IntLit {
                value: 10,
                span: Span::new(106, 108),
            }],
            span: Span::new(100, 109),
        };

        // Build cross-module GOT mapping: add42 -> module A's GOT.
        let mut xmod_got: HashMap<(ModuleFullPath, Symbol), (i64, usize)> = HashMap::new();
        xmod_got.insert(
            (ModuleFullPath::from("module_a"), Symbol::from("add42")),
            (got_base_a, add42_slot),
        );

        // Compile the caller using cross_module_got.
        let wrapper_name = Symbol::from("__test_caller__");
        let wrapper_defn = Defn {
            name: wrapper_name.clone(),
            params: vec![],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: caller_expr,
            docstring: None,
            span: Span::new(100, 120),
        };

        let mut jit_b = Jit::new().unwrap();
        jit_b.declare_intrinsics().unwrap();
        let func_ids_b = jit_b.declare_functions(&[&wrapper_defn]).unwrap();
        let arities_b: HashMap<Symbol, usize> = vec![
            (wrapper_name.clone(), 0),
            (Symbol::from("add42"), 1),
        ].into_iter().collect();

        // No local GOT slots for add42 -- it's cross-module only.
        let mut local_slots = HashMap::new();
        let mut local_got = got::ModuleCodegenState::new();
        let wrapper_slot = local_got.ensure_slot_for(&wrapper_name).unwrap();
        local_slots.insert(wrapper_name.clone(), wrapper_slot);
        let got_base_b = local_got.got_base_ptr() as i64;

        let ctx_b = jit_b.build_compile_context(
            &check, CompileMode::Interactive, &func_ids_b, &arities_b,
            Some(&local_slots), Some(got_base_b), Some(&xmod_got),
        );
        jit_b.compile_defn(&wrapper_defn, ctx_b).unwrap();
        let caller_ptr = jit_b.finalize_and_get_ptr(&wrapper_name, 0).unwrap();

        // Execute: should call add42 from module A's GOT and return 42.
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(caller_ptr) };
        let result = func();
        assert_eq!(result, 42, "cross-module GOT call should return add42's result");
    }

    // --- Cross-eval mono defn GOT tests ---

    // spec: 07-traits §7.7, 12-runtime §12.2 — mono defn compiled in prior eval
    // is callable via GOT from a subsequent eval's defn.
    //
    // Simulates the REPL scenario where a constrained-poly function
    // (e.g., `countdown`) is defined in eval 1, then called in eval 2
    // (e.g., `(defn main [] (countdown 1000000))`). The monomorphised
    // specialization (`countdown$Int`) must be compiled and registered
    // in the GOT before the calling defn is compiled.
    #[test]
    fn test_mono_defn_got_callable_across_evals() {
        // Step 1: Compile a "mono defn" (identity$Int) and register in GOT.
        // This simulates compile_mono_defns producing countdown$Int.
        let mono_defn = Defn {
            name: Symbol::from("identity$Int"),
            params: vec![Symbol::from("x")],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::Var {
                name: Symbol::from("x"),
                span: Span::new(10, 11),
            },
            docstring: None,
            span: Span::new(0, 20),
        };

        let mut got_state = got::ModuleCodegenState::new();
        let mono_slot = got_state.ensure_slot_for(&Symbol::from("identity$Int")).unwrap();

        // Compile mono defn in its own JIT (as compile_and_register_defn does).
        let check = empty_check();
        let mut jit1 = Jit::new().unwrap();
        jit1.declare_intrinsics().unwrap();
        let func_ids1 = jit1.declare_functions(&[&mono_defn]).unwrap();

        let mut got_slots: HashMap<Symbol, usize> = HashMap::new();
        got_slots.insert(Symbol::from("identity$Int"), mono_slot);
        let got_base = got_state.got_base_ptr() as i64;

        let arities1: HashMap<Symbol, usize> =
            vec![(Symbol::from("identity$Int"), 1)].into_iter().collect();

        let ctx1 = jit1.build_compile_context(
            &check, CompileMode::Interactive, &func_ids1, &arities1,
            Some(&got_slots), Some(got_base), None,
        );
        jit1.compile_defn(&mono_defn, ctx1).unwrap();
        let mono_ptr = jit1.finalize_and_get_ptr(&Symbol::from("identity$Int"), 1).unwrap();
        got_state.update_slot(mono_slot, mono_ptr);
        got_state.def_codegen.entry(Symbol::from("identity$Int")).or_default().code_ptr = Some(mono_ptr);
        got_state.def_codegen.entry(Symbol::from("identity$Int")).or_default().param_count = Some(1);

        // Step 2: Compile a "main" defn that calls identity$Int via SigDispatch.
        // The call `(identity 99)` is resolved to identity$Int by the typechecker.
        let call_span = Span::new(100, 115);
        let main_body = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("identity"),
                span: Span::new(101, 109),
            }),
            args: vec![Expr::IntLit {
                value: 99,
                span: Span::new(110, 112),
            }],
            span: call_span,
        };

        let main_defn = Defn {
            name: Symbol::from("main"),
            params: vec![],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: main_body,
            docstring: None,
            span: Span::new(95, 120),
        };

        // Set up method_resolutions with SigDispatch for the call.
        let mut check2 = empty_check();
        check2.method_resolutions.insert(
            call_span,
            cranelisp_types::ResolvedCall::SigDispatch {
                mangled_name: cranelisp_types::JitSymbol::from("identity$Int"),
            },
        );

        let main_slot = got_state.ensure_slot_for(&Symbol::from("main")).unwrap();

        // Build got_slots from the GOT state (as compile_and_register_defn does).
        let mut got_slots2: HashMap<Symbol, usize> = HashMap::new();
        for (name, dc) in &got_state.def_codegen {
            if let Some(s) = dc.got_slot {
                got_slots2.insert(name.clone(), s);
            }
        }
        got_slots2.insert(Symbol::from("main"), main_slot);
        let got_base2 = got_state.got_base_ptr() as i64;

        let mut arities2: HashMap<Symbol, usize> = HashMap::new();
        for (name, dc) in &got_state.def_codegen {
            if let Some(pc) = dc.param_count {
                arities2.insert(name.clone(), pc);
            }
        }
        arities2.insert(Symbol::from("main"), 0);

        let mut jit2 = Jit::new().unwrap();
        jit2.declare_intrinsics().unwrap();
        let func_ids2 = jit2.declare_functions(&[&main_defn]).unwrap();

        let ctx2 = jit2.build_compile_context(
            &check2, CompileMode::Interactive, &func_ids2, &arities2,
            Some(&got_slots2), Some(got_base2), None,
        );
        jit2.compile_defn(&main_defn, ctx2).unwrap();
        let main_ptr = jit2.finalize_and_get_ptr(&Symbol::from("main"), 0).unwrap();

        // Execute main: should call identity$Int(99) and return 99.
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(main_ptr) };
        let result = func();
        assert_eq!(result, 99, "cross-eval GOT call to mono defn should work");
    }

    // spec: 12-runtime §12.5, 07-traits §7.7 — TCO for monomorphised self-recursive call
    //
    // When a constrained-poly function like `countdown` is monomorphised to
    // `countdown$Int`, the body contains a self-recursive call `(countdown ...)`
    // that the typechecker resolves to `SigDispatch { mangled_name: "countdown$Int" }`.
    // The backend's TCO check must recognize this as self-recursion.
    //
    // This test compiles a simple recursive function and verifies it completes
    // without stack overflow (1M iterations would blow the stack without TCO).
    #[test]
    fn test_mono_defn_self_recursive_tco() {
        // countdown$Int: (defn countdown$Int [n] (if (= n 0) 0 (countdown$Int (- n 1))))
        // Simplified: use intrinsic primitives instead of trait dispatch.
        let n_span = Span::new(10, 11);
        let zero_span = Span::new(20, 21);
        let eq_span = Span::new(30, 40);
        let sub_span = Span::new(50, 60);
        let recurse_span = Span::new(70, 90);
        let if_span = Span::new(5, 95);
        let result_span = Span::new(92, 93);

        // Build: (if (eq-i64 n 0) 0 (countdown$Int (sub-i64 n 1)))
        let cond = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("eq-i64"),
                span: Span::new(31, 37),
            }),
            args: vec![
                Expr::Var { name: Symbol::from("n"), span: n_span },
                Expr::IntLit { value: 0, span: zero_span },
            ],
            span: eq_span,
        };

        let sub_call = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("sub-i64"),
                span: Span::new(51, 58),
            }),
            args: vec![
                Expr::Var { name: Symbol::from("n"), span: Span::new(55, 56) },
                Expr::IntLit { value: 1, span: Span::new(57, 58) },
            ],
            span: sub_span,
        };

        // The recursive call: callee is "countdown" (original name),
        // but it's resolved to countdown$Int via SigDispatch.
        let recurse = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("countdown"),
                span: Span::new(71, 80),
            }),
            args: vec![sub_call],
            span: recurse_span,
        };

        let body = Expr::If {
            cond: Box::new(cond),
            then_branch: Box::new(Expr::IntLit { value: 0, span: result_span }),
            else_branch: Box::new(recurse),
            span: if_span,
        };

        let countdown_defn = Defn {
            name: Symbol::from("countdown$Int"),
            params: vec![Symbol::from("n")],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body,
            docstring: None,
            span: Span::new(0, 100),
        };

        // Set up method resolutions:
        // - eq_span: BuiltinFn("eq-i64") for the equality check
        // - sub_span: BuiltinFn("sub-i64") for the subtraction
        // - recurse_span: SigDispatch("countdown$Int") for the self-recursive call
        let mut check = empty_check();
        check.method_resolutions.insert(
            eq_span,
            cranelisp_types::ResolvedCall::BuiltinFn {
                name: Symbol::from("eq-i64"),
            },
        );
        check.method_resolutions.insert(
            sub_span,
            cranelisp_types::ResolvedCall::BuiltinFn {
                name: Symbol::from("sub-i64"),
            },
        );
        check.method_resolutions.insert(
            recurse_span,
            cranelisp_types::ResolvedCall::SigDispatch {
                mangled_name: cranelisp_types::JitSymbol::from("countdown$Int"),
            },
        );

        // Compile in Interactive mode with GOT.
        let mut got_state = got::ModuleCodegenState::new();
        let slot = got_state.ensure_slot_for(&Symbol::from("countdown$Int")).unwrap();

        let mut jit = Jit::new().unwrap();
        jit.declare_intrinsics().unwrap();
        let func_ids = jit.declare_functions(&[&countdown_defn]).unwrap();

        let mut got_slots: HashMap<Symbol, usize> = HashMap::new();
        got_slots.insert(Symbol::from("countdown$Int"), slot);
        let got_base = got_state.got_base_ptr() as i64;

        let arities: HashMap<Symbol, usize> =
            vec![(Symbol::from("countdown$Int"), 1)].into_iter().collect();

        let ctx = jit.build_compile_context(
            &check, CompileMode::Interactive, &func_ids, &arities,
            Some(&got_slots), Some(got_base), None,
        );
        jit.compile_defn(&countdown_defn, ctx).unwrap();
        let countdown_ptr = jit.finalize_and_get_ptr(&Symbol::from("countdown$Int"), 1).unwrap();
        got_state.update_slot(slot, countdown_ptr);

        // Call with 1_000_000 — without TCO this would stack overflow.
        let func: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(countdown_ptr) };
        let result = func(1_000_000);
        assert_eq!(result, 0, "TCO should allow 1M recursive calls without stack overflow");
    }

    // --- compile_module_program tests ---

    // spec: 08-modules §8.3 — two modules with same-named function in shared JIT
    // Regression test: previously caused "Duplicate definition" error when
    // both modules defined a function with the same bare name (e.g., "fold").
    #[test]
    fn test_shared_jit_name_collision_avoided() {
        // Module A defines "val" returning 100.
        let val_a = Defn {
            name: Symbol::from("val"),
            params: vec![],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::IntLit { value: 100, span: Span::new(0, 3) },
            docstring: None,
            span: Span::new(0, 20),
        };
        let program_a: Program = vec![TopLevel::Defn(val_a)];
        let check_a = empty_check();

        // Module B also defines "val" returning 200.
        let val_b = Defn {
            name: Symbol::from("val"),
            params: vec![],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::IntLit { value: 200, span: Span::new(100, 103) },
            docstring: None,
            span: Span::new(100, 120),
        };
        // Module B also defines "main" that calls its own "val".
        let main_b = Defn {
            name: Symbol::from("main"),
            params: vec![],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("val"),
                    span: Span::new(130, 133),
                }),
                args: vec![],
                span: Span::new(130, 135),
            },
            docstring: None,
            span: Span::new(125, 140),
        };
        let program_b: Program = vec![
            TopLevel::Defn(val_b),
            TopLevel::Defn(main_b),
        ];
        let check_b = empty_check();

        // Compile both modules into one shared JIT.
        let mut jit = jit::Jit::new().unwrap();
        jit.declare_intrinsics().unwrap();

        // Compile module A with prefix "mod_a".
        let info_a = compile_module_program(
            &program_a, &check_a, CompileMode::Batch,
            &mut jit, &[], "mod_a",
        ).expect("module A should compile");

        // Build prior_funcs from module A's output (simulating accumulate_func_sigs).
        let mut prior_funcs: Vec<(Symbol, usize)> = Vec::new();
        for (name, arity) in &info_a.func_signatures {
            prior_funcs.push((name.clone(), *arity));
        }

        // Compile module B with prefix "mod_b" — should NOT fail with
        // "Duplicate definition" error.
        let _info_b = compile_module_program(
            &program_b, &check_b, CompileMode::Batch,
            &mut jit, &prior_funcs, "mod_b",
        ).expect("module B should compile without name collision");

        // Finalize the shared JIT.
        jit.finalize().expect("JIT finalization should succeed");

        // Module B's "main" calls its own "val" which returns 200.
        let main_ptr = jit.get_ptr_by_name(
            &Symbol::from("mod_b/main"), 0,
        ).expect("mod_b/main should be findable");
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(main_ptr) };
        let result = func();
        assert_eq!(result, 200, "module B's main should call its own val (200), not module A's (100)");

        // Module A's "val" should also be accessible by its qualified name.
        let val_a_ptr = jit.get_ptr_by_name(
            &Symbol::from("mod_a/val"), 0,
        ).expect("mod_a/val should be findable");
        let func_a: extern "C" fn() -> i64 = unsafe { std::mem::transmute(val_a_ptr) };
        let result_a = func_a();
        assert_eq!(result_a, 100, "module A's val should return 100");
    }
}
