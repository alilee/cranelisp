// Pipeline: shared compilation functions used by the v4 pipeline.
//
// This module provides:
// - Module file resolution
// - Expression compilation and execution (REPL eval)

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use cranelisp_types::{
    CranelispError, ModuleFullPath,
    Program, Span, Type,
};

// ---------------------------------------------------------------------------
// Module file resolution
// ---------------------------------------------------------------------------

/// Resolve a module name to a `.cl` file path.
///
/// Search order per spec §8.11.2:
/// 1. Project root — `{project_root}/{name}.cl`
/// 2. Lib directories — `{lib_dir}/{name}.cl` for each lib dir, in order
///
/// Tier 1 (submodule of current module) is handled by the caller — submodules
/// are already registered in the TypeChecker via `(mod name)` and don't need
/// file search.
pub fn resolve_module_file(
    module: &ModuleFullPath,
    project_root: &Path,
    lib_dirs: &[PathBuf],
) -> Option<PathBuf> {
    let relative = format!("{}.cl", module.as_ref().replace('.', "/"));

    // Tier 2: project root.
    let root_candidate = project_root.join(&relative);
    if root_candidate.is_file() {
        return Some(root_candidate);
    }

    // Tier 3: lib directories.
    for dir in lib_dirs {
        let candidate = dir.join(&relative);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Expression compilation (REPL eval path)
// ---------------------------------------------------------------------------

// FIXME(/int): Sprint 56 Wave 3 — the `program: &Program` parameter below is
// a leftover from the pre-Wave-2 code path. The new path pulls `__expr` from
// `symbol_tables` (Wave 0 installs it there as a synthetic Defn with
// `ast: Some(...)`), and the `program` fallback is kept only for
// "backward compatibility with callers that hand-build programs without
// going through `wrap_exprs_as_defns`". No production caller exercises the
// fallback today — `session_v4.rs:1574` passes `program_vec` but the symbol
// table always has `__expr` installed first. Audit call sites, confirm the
// fallback is dead, then remove `program: &Program` from the signature (and
// the `program_vec` construction upstream). Wave 3 audit did not edit this to
// keep this investigation read-only.
#[allow(clippy::too_many_arguments)]
pub fn compile_and_execute_expr(
    jit_symbols: &[(String, *const u8)],
    got_data_defs: &[(String, *const u8)],
    program: &Program,
    display: Option<&cranelisp_types::DisplayInfo>,
    traced_fns: &[cranelisp_backend::compiler::TracedFnInfo],
    trace_extra_symbols: &[(String, *const u8)],
    symbol_tables: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    current_module: ModuleFullPath,
) -> Result<(i64, Type), CranelispError> {
    use cranelisp_types::TopLevel;

    // Sprint 56 Wave 2: pull the annotated expression body from the symbol
    // table entry for `__expr` (Wave 0 registers it as a synthetic defn with
    // `ast: Some(...)`), falling back to the program's `TopLevel::Expr` for
    // backward compatibility with callers that hand-build programs without
    // going through `wrap_exprs_as_defns`. The symbol-table body carries the
    // post-pass resolution annotations (SigDispatch for Overloaded-base
    // calls, auto-curry resolutions) that the program's TopLevel::Expr lacks.
    let expr_owned: Option<cranelisp_types::Expr> = symbol_tables
        .get(&current_module)
        .and_then(|t| match t.get("__expr") {
            Some(cranelisp_types::ModuleEntry::Def { ast: Some(defn), .. }) => {
                Some(defn.body().clone())
            }
            _ => None,
        });
    let expr_ref: &cranelisp_types::Expr = if let Some(ref e) = expr_owned {
        e
    } else {
        program
            .iter()
            .rev()
            .find_map(|tl| if let TopLevel::Expr(e) = tl { Some(e) } else { None })
            .ok_or_else(|| CranelispError::CodegenError {
                message: "no expression found in program".into(),
                span: Span::SYNTHETIC,
            })?
    };
    let expr = expr_ref;

    // Get the type from display info or from the AST node's inferred_type.
    let ty = display
        .map(|d| d.ty.clone())
        .or_else(|| expr.inferred_type().cloned())
        .unwrap_or(Type::Int);

    if traced_fns.is_empty() {
        use cranelisp_types::{Defn, DefnVariant, Symbol, Visibility};

        let extra_syms: Vec<(&str, *const u8)> = jit_symbols
            .iter()
            .map(|(name, ptr)| (name.as_str(), *ptr))
            .collect();

        let mut jit = cranelisp_backend::jit::Jit::new_with_symbols(&extra_syms)?;
        jit.declare_intrinsics()?;

        // Define GOT base literal pool entries as data in the JIT module.
        for (name, ptr) in got_data_defs {
            jit.define_got_data(name, *ptr)?;
        }

        let wrapper_name = Symbol::from("__repl_expr__");
        // Use a synthetic wrapper span that nests the expr span so the
        // typecheck's pre-eval resolution annotations (keyed by expr.span())
        // survive through codegen.
        let wrapper_span = expr.span();
        let wrapper_defn = Defn {
            name: wrapper_name.clone(),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: expr.clone(),
                span: wrapper_span,
            }],
            visibility: Visibility::Public,
            span: wrapper_span,
        };

        let func_ids = jit.declare_functions(&[&wrapper_defn])?;
        let empty_arities: HashMap<Symbol, usize> = HashMap::new();

        let compile_ctx = jit.build_compile_context(
            &func_ids,
            &empty_arities,
            symbol_tables,
            current_module.clone(),
        );

        jit.compile_defn(&wrapper_defn, compile_ctx)?;
        let code_ptr = jit.finalize_and_get_ptr(&wrapper_name, 0)?;

        // SAFETY: compiled code was just generated and finalized by our JIT.
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
        // Clear any stale error before the JIT call.
        let _ = cranelisp_runtime::panic::take_runtime_error();
        let value = func();

        // Check thread-local error flag (set by runtime_panic in JIT code).
        if let Some(msg) = cranelisp_runtime::panic::take_runtime_error() {
            return Err(CranelispError::CodegenError {
                message: format!("runtime error: {msg}"),
                span: expr.span(),
            });
        }
        Ok((value, ty))
    } else {
        let value = compile_and_execute_expr_with_trace(
            jit_symbols, got_data_defs, expr, traced_fns, trace_extra_symbols,
            symbol_tables, current_module.clone(),
        )?;
        Ok((value, ty))
    }
}

#[allow(clippy::too_many_arguments)]
fn compile_and_execute_expr_with_trace(
    jit_symbols: &[(String, *const u8)],
    got_data_defs: &[(String, *const u8)],
    expr: &cranelisp_types::Expr,
    traced_fns: &[cranelisp_backend::compiler::TracedFnInfo],
    trace_extra_symbols: &[(String, *const u8)],
    symbol_tables: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    current_module: ModuleFullPath,
) -> Result<i64, CranelispError> {
    use cranelisp_types::{Defn, DefnVariant, Symbol, Visibility};

    let mut extra_syms: Vec<(&str, *const u8)> = jit_symbols
        .iter()
        .map(|(name, ptr)| (name.as_str(), *ptr))
        .collect();
    for (name, ptr) in trace_extra_symbols {
        extra_syms.push((name.as_str(), *ptr));
    }

    let mut jit = cranelisp_backend::jit::Jit::new_with_symbols(&extra_syms)?;
    jit.declare_intrinsics()?;

    // Define GOT base literal pool entries as data in the JIT module.
    for (name, ptr) in got_data_defs {
        jit.define_got_data(name, *ptr)?;
    }

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
    let empty_arities: HashMap<Symbol, usize> = HashMap::new();

    let mut compile_ctx = jit.build_compile_context(
        &func_ids,
        &empty_arities,
        symbol_tables,
        current_module.clone(),
    );

    compile_ctx.traced_fns = Some(traced_fns);

    jit.compile_defn(&wrapper_defn, compile_ctx)?;
    let code_ptr = jit.finalize_and_get_ptr(&wrapper_name, 0)?;

    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
    // Clear any stale error before the JIT call.
    let _ = cranelisp_runtime::panic::take_runtime_error();
    let value = func();

    // Check thread-local error flag (set by runtime_panic in JIT code).
    if let Some(msg) = cranelisp_runtime::panic::take_runtime_error() {
        return Err(CranelispError::CodegenError {
            message: format!("runtime error: {msg}"),
            span: expr.span(),
        });
    }

    Ok(value)
}
