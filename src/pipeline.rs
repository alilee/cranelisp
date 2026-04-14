// Pipeline: shared compilation functions used by the v4 pipeline.
//
// This module provides:
// - Module file resolution
// - Expression compilation and execution (REPL eval)
// - Per-defn GOT registration (worker codegen)

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use cranelisp_types::{
    CheckResult, CranelispError, Defn, FQSymbol, ModuleFullPath,
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

#[allow(clippy::too_many_arguments)]
pub fn compile_and_execute_expr(
    jit_symbols: &[(String, *const u8)],
    got_data_defs: &[(String, *const u8)],
    program: &Program,
    check: &CheckResult,
    env: &dyn cranelisp_backend::compiler::CompilationEnv,
    traced_fns: &[cranelisp_backend::compiler::TracedFnInfo],
    trace_extra_symbols: &[(String, *const u8)],
    symbol_tables: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    current_module: ModuleFullPath,
) -> Result<(i64, Type), CranelispError> {
    use cranelisp_types::TopLevel;

    let expr = program.iter().rev().find_map(|tl| {
        if let TopLevel::Expr(e) = tl { Some(e) } else { None }
    }).ok_or_else(|| CranelispError::CodegenError {
        message: "no expression found in program".into(),
        span: Span::SYNTHETIC,
    })?;

    let ty = check.display.as_ref()
        .map(|d| d.ty.clone())
        .or_else(|| check.expr_types.get(&expr.span()).cloned())
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
            check,
            &func_ids,
            &empty_arities,
            symbol_tables,
            current_module.clone(),
        );
        compile_ctx.env = Some(env);

        jit.compile_defn(&wrapper_defn, compile_ctx)?;
        let code_ptr = jit.finalize_and_get_ptr(&wrapper_name, 0)?;

        // SAFETY: compiled code was just generated and finalized by our JIT.
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
        let value = func();
        Ok((value, ty))
    } else {
        let value = compile_and_execute_expr_with_trace(
            jit_symbols, got_data_defs, expr, check, env, traced_fns, trace_extra_symbols,
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
    check: &CheckResult,
    env: &dyn cranelisp_backend::compiler::CompilationEnv,
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
        check,
        &func_ids,
        &empty_arities,
        symbol_tables,
        current_module.clone(),
    );

    compile_ctx.env = Some(env);
    compile_ctx.traced_fns = Some(traced_fns);

    jit.compile_defn(&wrapper_defn, compile_ctx)?;
    let code_ptr = jit.finalize_and_get_ptr(&wrapper_name, 0)?;

    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
    let value = func();

    // JIT goes out of scope here, but the code was already executed.
    // No need to keep it alive — expression results are immediate values.

    Ok(value)
}

// ---------------------------------------------------------------------------
// Per-defn GOT registration (worker codegen path)
// ---------------------------------------------------------------------------

/// Compile a single function definition and register it in the GOT.
///
/// Writes `Code { jit, ptr }` to `codegen_products` (target state DashMap).
/// GOT slot resolution goes through `env` (SessionCompilationEnv).
/// If `introspection` is provided, populates CLIF IR, AST, disasm, and code_size.
#[allow(clippy::too_many_arguments)]
pub fn compile_and_register_defn_shared(
    jit_symbols: &[(String, *const u8)],
    got_data_defs: &[(String, *const u8)],
    defn: &Defn,
    check: &CheckResult,
    env: &dyn cranelisp_backend::compiler::CompilationEnv,
    module_got: &std::sync::Arc<cranelisp_backend::got::GotTable>,
    codegen_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::CodegenProduct>,
    introspection: Option<&dashmap::DashMap<FQSymbol, crate::session_v4::Introspection>>,
    module: &ModuleFullPath,
    disable_dealloc: bool,
    symbol_tables: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
) -> Result<(), CranelispError> {
    let extra_symbols: Vec<(&str, *const u8)> = jit_symbols
        .iter()
        .map(|(name, ptr)| (name.as_str(), *ptr))
        .collect();
    let mut jit = cranelisp_backend::jit::Jit::new_with_symbols(&extra_symbols)?;

    jit.declare_intrinsics()?;

    // Define GOT base literal pool entries as data in the JIT module.
    for (name, ptr) in got_data_defs {
        jit.define_got_data(name, *ptr)?;
    }

    let func_ids = jit.declare_functions(&[defn])?;

    let slot = env.resolve_got(&defn.name)
        .map(|(_, s)| s)
        .ok_or_else(|| CranelispError::CodegenError {
            message: format!("no pre-assigned GOT slot for function: {}", defn.name),
            span: defn.span,
        })?;

    let func_arities = std::collections::HashMap::new();
    let mut compile_ctx = jit.build_compile_context(
        check,
        &func_ids,
        &func_arities,
        symbol_tables,
        module.clone(),
    );
    compile_ctx.env = Some(env);
    if disable_dealloc {
        compile_ctx.dealloc_func_id = None;
    }
    let artifacts = jit.compile_defn(defn, compile_ctx)?;

    let code_ptr = jit.finalize_and_get_ptr(&defn.name, defn.params().len())?;

    // Write code pointer to module's GOT table.
    module_got.store_slot(slot, code_ptr);

    // Write Code to codegen_products.
    let product = codegen_products.entry(module.clone()).or_default();
    product.code.insert(
        defn.name.clone(),
        crate::session_v4::Code { jit, ptr: code_ptr },
    );

    // Populate introspection data (REPL-only).
    if let Some(intr_map) = introspection {
        let fq = FQSymbol {
            module: module.clone(),
            symbol: defn.name.clone(),
        };
        let mut entry = intr_map.entry(fq).or_default();
        entry.clif_ir = Some(artifacts.clif_ir);
        entry.disasm = artifacts.disasm;
        entry.code_size = artifacts.code_size;
    }

    Ok(())
}


