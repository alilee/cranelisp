// Pipeline: shared compilation functions used by the v4 pipeline.
//
// This module provides:
// - Module file resolution
// - Expression compilation and execution (REPL eval)
// - Per-defn GOT registration (worker codegen)
// - Cache state construction
// - Object compilation helpers

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use cranelisp_types::{
    CheckResult, CranelispError, Defn, FQSymbol, ModuleFullPath,
    Program, Span, Symbol, Type,
};

use cranelisp_backend::cache;

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
        let extra_syms: Vec<(&str, *const u8)> = jit_symbols
            .iter()
            .map(|(name, ptr)| (name.as_str(), *ptr))
            .collect();

        let compiled = cranelisp_backend::compile_expr_with_got_and_symbols(
            expr,
            check,
            &extra_syms,
            got_data_defs,
            Some(env),
            symbol_tables,
            current_module.clone(),
        )?;

        // SAFETY: compiled code was just generated and finalized by our JIT.
        let value = unsafe { compiled.execute() };
        Ok((value, ty))
    } else {
        let value = compile_and_execute_expr_with_trace(
            jit_symbols, got_data_defs, expr, check, env, traced_fns, trace_extra_symbols,
            symbol_tables, current_module.clone(),
        )?;
        Ok((value, ty))
    }
}

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


// ---------------------------------------------------------------------------
// Object compilation helpers
// ---------------------------------------------------------------------------

pub(crate) struct CollectedDefns {
    defns: Vec<(Defn, cranelisp_types::Scheme)>,
    fn_slot_assignments: HashMap<Symbol, cache::object::FnSlotInfo>,
    next_slot: usize,
}

pub(crate) fn collect_defns_for_cache(
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
        if let TopLevel::Defn(defn) = tl {
            if let Some(ch) = check
                && ch.constrained_fn_names.contains(&defn.name)
            {
                continue;
            }
            let scheme = scheme_for_defn(defn, check);
            let slot = next_slot;
            next_slot += 1;
            fn_slot_assignments.insert(
                defn.name.clone(),
                cache::object::FnSlotInfo {
                    slot,
                    param_count: defn.params().len(),
                },
            );
            defns.push((defn.clone(), scheme));
        }
    }

    if let Some(ch) = check {
        for mono in &ch.mono_defns {
            let scheme = scheme_for_defn(&mono.defn, Some(ch));
            let slot = next_slot;
            next_slot += 1;
            fn_slot_assignments.insert(
                mono.defn.name.clone(),
                cache::object::FnSlotInfo {
                    slot,
                    param_count: mono.defn.params().len(),
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
                    param_count: defn.params().len(),
                },
            );
            defns.push((defn.clone(), scheme));
        }
    }

    CollectedDefns { defns, fn_slot_assignments, next_slot }
}

pub(crate) fn scheme_for_defn(defn: &Defn, check: Option<&CheckResult>) -> cranelisp_types::Scheme {
    let ty = check
        .and_then(|ch| ch.expr_types.get(&defn.span))
        .cloned()
        .unwrap_or_else(|| {
            Type::Fn(
                defn.params().iter().map(|_| Type::Int).collect(),
                Box::new(Type::Int),
            )
        });
    cranelisp_types::Scheme {
        vars: vec![],
        constraints: HashMap::new(),
        ty,
    }
}

pub(crate) struct CrossModuleRefs {
    fn_to_module: HashMap<Symbol, ModuleFullPath>,
    cross_module_fns: Vec<(Symbol, usize)>,
}

pub(crate) fn collect_cross_module_refs(
    func_sigs: &[(Symbol, usize)],
) -> CrossModuleRefs {
    let mut fn_to_module: HashMap<Symbol, ModuleFullPath> = HashMap::new();
    let mut cross_module_fns: Vec<(Symbol, usize)> = Vec::new();

    for (name, param_count) in func_sigs {
        if let Some(slash) = name.as_ref().find('/') {
            let mod_part = &name.as_ref()[..slash];
            fn_to_module.insert(name.clone(), ModuleFullPath::from(mod_part));
        }
        cross_module_fns.push((name.clone(), *param_count));
    }

    CrossModuleRefs { fn_to_module, cross_module_fns }
}

pub(crate) fn build_object_compile_input(
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
        expr_types: check
            .map(|ch| ch.expr_types.clone())
            .unwrap_or_default(),
        next_got_slot: collected.next_slot,
        cross_module_fns: cross_refs.cross_module_fns,
    }
}

pub(crate) fn build_intrinsic_table() -> cache::IntrinsicTable {
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
