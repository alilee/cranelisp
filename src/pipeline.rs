// Pipeline: shared compilation functions used by the v4 pipeline.
//
// This module provides:
// - Module file resolution
// - Expression compilation and execution (REPL eval)
// - Per-defn GOT registration (worker codegen)
// - Cache state construction
// - Module graph discovery and topological sort
// - Object compilation helpers

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use cranelisp_types::{
    CheckResult, CranelispError, Defn, ModuleFullPath,
    Program, Span, Symbol, Type,
};

use cranelisp_backend::cache;

use crate::session::InMemWorkerState;

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
    inmem_worker: &mut InMemWorkerState,
    jit_symbols: &[(String, *const u8)],
    program: &Program,
    check: &CheckResult,
    env: Option<&dyn cranelisp_backend::compiler::CompilationEnv>,
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

    if inmem_worker.traced_fns.is_empty() {
        let extra_syms: Vec<(&str, *const u8)> = jit_symbols
            .iter()
            .map(|(name, ptr)| (name.as_str(), *ptr))
            .collect();

        let got_state = if env.is_some() { None } else { Some(&mut inmem_worker.got_state) };

        let compiled = cranelisp_backend::compile_expr_with_got_and_symbols(
            expr,
            check,
            got_state,
            &extra_syms,
            env,
        )?;

        // SAFETY: compiled code was just generated and finalized by our JIT.
        let value = unsafe { compiled.execute() };
        Ok((value, ty))
    } else {
        let value = compile_and_execute_expr_with_trace(inmem_worker, jit_symbols, expr, check, env)?;
        Ok((value, ty))
    }
}

fn compile_and_execute_expr_with_trace(
    inmem_worker: &mut InMemWorkerState,
    jit_symbols: &[(String, *const u8)],
    expr: &cranelisp_types::Expr,
    check: &CheckResult,
    env: Option<&dyn cranelisp_backend::compiler::CompilationEnv>,
) -> Result<i64, CranelispError> {
    use cranelisp_types::{Defn, DefnVariant, Symbol, Visibility};
    use std::collections::HashMap;

    let mut extra_syms: Vec<(&str, *const u8)> = jit_symbols
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

    // When env is provided, skip GOT snapshot — env handles resolution live.
    let (got_slots, got_base, func_arities) = if env.is_some() {
        (HashMap::new(), 0i64, HashMap::new())
    } else {
        let mut gs: HashMap<Symbol, usize> = HashMap::new();
        let mut fa: HashMap<Symbol, usize> = HashMap::new();
        for (name, dc) in &inmem_worker.got_state.def_codegen {
            if let Some(slot) = dc.got_slot {
                gs.insert(name.clone(), slot);
            }
            if let Some(pc) = dc.param_count {
                fa.insert(name.clone(), pc);
            }
        }
        let base = inmem_worker.got_state.got_base_ptr() as i64;
        (gs, base, fa)
    };

    let mut compile_ctx = jit.build_compile_context(
        check,
        &func_ids,
        &func_arities,
        if env.is_some() { None } else { Some(&got_slots) },
        if env.is_some() { None } else { Some(got_base) },
        None,
    );

    compile_ctx.env = env;
    compile_ctx.traced_fns = Some(&inmem_worker.traced_fns);

    jit.compile_defn(&wrapper_defn, compile_ctx)?;
    let code_ptr = jit.finalize_and_get_ptr(&wrapper_name, 0)?;

    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
    let value = func();

    inmem_worker.jit_modules.push(jit);

    Ok(value)
}

// ---------------------------------------------------------------------------
// Per-defn GOT registration (worker codegen path)
// ---------------------------------------------------------------------------

/// Compile a single function definition and register it in the GOT.
///
/// Writes `Code { jit, ptr }` to `codegen_products` (target state DashMap).
/// GOT slot resolution goes through `env` (SessionCompilationEnv).
pub fn compile_and_register_defn_shared(
    jit_symbols: &[(String, *const u8)],
    defn: &Defn,
    check: &CheckResult,
    env: &dyn cranelisp_backend::compiler::CompilationEnv,
    module_got: &std::sync::Arc<cranelisp_backend::got::GotTable>,
    codegen_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::CodegenProduct>,
    module: &ModuleFullPath,
    disable_dealloc: bool,
) -> Result<(), CranelispError> {
    let extra_symbols: Vec<(&str, *const u8)> = jit_symbols
        .iter()
        .map(|(name, ptr)| (name.as_str(), *ptr))
        .collect();
    let mut jit = cranelisp_backend::jit::Jit::new_with_symbols(&extra_symbols)?;

    jit.declare_intrinsics()?;

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
        None,
        None,
        None,
    );
    compile_ctx.env = Some(env);
    if disable_dealloc {
        compile_ctx.dealloc_func_id = None;
    }
    let _clif_ir = jit.compile_defn(defn, compile_ctx)?;

    let code_ptr = jit.finalize_and_get_ptr(&defn.name, defn.params().len())?;

    // Write code pointer to module's GOT table.
    module_got.store_slot(slot, code_ptr);

    // Write Code to codegen_products.
    let product = codegen_products.entry(module.clone()).or_insert_with(|| {
        crate::session_v4::CodegenProduct {
            linker: None,
            code: dashmap::DashMap::new(),
            got: None,
            got_base: std::ptr::null(),
        }
    });
    product.code.insert(
        defn.name.clone(),
        crate::session_v4::Code { jit, ptr: code_ptr },
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// Cache state construction
// ---------------------------------------------------------------------------

pub fn build_codegen_state_for_cache(
    program: &Program,
    check: &CheckResult,
) -> cranelisp_backend::cache::CacheCodegenState {
    use cranelisp_types::TopLevel;
    use std::collections::HashMap;

    let mut got_slots: HashMap<Symbol, usize> = HashMap::new();
    let mut def_entries: HashMap<Symbol, cranelisp_backend::cache::SerializedDefEntry> = HashMap::new();
    let mut next_slot: usize = 0;

    for tl in program.iter() {
        if let TopLevel::Defn(defn) = tl {
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

// ---------------------------------------------------------------------------
// Multi-file module graph discovery
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

/// Discover the module dependency graph starting from an entry file.
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

fn discover_module_recursive(
    module_path: &ModuleFullPath,
    file_path: &Path,
    project_root: &Path,
    lib_dirs: &[PathBuf],
    nodes: &mut HashMap<ModuleFullPath, ModuleNode>,
    visiting: &mut Vec<ModuleFullPath>,
) -> Result<(), CranelispError> {
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

    if nodes.contains_key(module_path) {
        return Ok(());
    }

    visiting.push(module_path.clone());

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

    let mut dependencies = Vec::new();

    for mod_decl in &structure.mod_decls {
        if mod_decl.inline_body.is_some() {
            continue;
        }

        let submod_name = &mod_decl.name;

        let child_path = if module_path.0.is_empty() {
            ModuleFullPath::from(submod_name.as_ref())
        } else {
            ModuleFullPath::from(format!("{}.{}", module_path, submod_name))
        };

        let resolved = resolve_submodule_file(
            file_path,
            submod_name.as_ref(),
            project_root,
            lib_dirs,
        )?;

        dependencies.push(child_path.clone());

        discover_module_recursive(
            &child_path,
            &resolved,
            project_root,
            lib_dirs,
            nodes,
            visiting,
        )?;
    }

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

#[allow(clippy::too_many_arguments)]
fn discover_import_dependencies(
    structure: &cranelisp_types::ModuleStructure,
    module_path: &ModuleFullPath,
    file_path: &Path,
    project_root: &Path,
    lib_dirs: &[PathBuf],
    nodes: &mut HashMap<ModuleFullPath, ModuleNode>,
    visiting: &mut Vec<ModuleFullPath>,
    dependencies: &mut Vec<ModuleFullPath>,
) -> Result<(), CranelispError> {
    let all_module_paths = structure
        .import_specs
        .iter()
        .map(|s| &s.module_path)
        .chain(structure.export_specs.iter().map(|s| &s.module_path));
    for ref_module_path in all_module_paths {
        let ref_path: &str = ref_module_path.as_ref();

        if is_synthetic_or_special(ref_path) {
            continue;
        }

        let root_name = ref_path.split('.').next().unwrap_or(ref_path);

        let candidate_path = if module_path.0.is_empty() {
            ModuleFullPath::from(root_name)
        } else {
            let mod_prefix = format!("{}.", module_path);
            if ref_path.starts_with(&mod_prefix) {
                ref_module_path.clone()
            } else {
                ModuleFullPath::from(root_name)
            }
        };

        if dependencies.contains(&candidate_path) {
            continue;
        }

        if nodes.contains_key(&candidate_path) {
            dependencies.push(candidate_path.clone());
            continue;
        }

        let resolved = match resolve_submodule_file(
            file_path,
            root_name,
            project_root,
            lib_dirs,
        ) {
            Ok(path) => path,
            Err(_) => {
                continue;
            }
        };

        dependencies.push(candidate_path.clone());

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

fn is_synthetic_or_special(module_path: &str) -> bool {
    let root = module_path.split('.').next().unwrap_or(module_path);
    SYNTHETIC_MODULES.contains(&root) || root == "super" || root == "prelude"
}

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

    // 3. Project root: {project_root}/{name}.cl
    if parent_dir != project_root {
        let root_file = project_root.join(&filename);
        if root_file.is_file() {
            return Ok(root_file);
        }
    }

    // 4. Lib directories: {lib_dir}/{name}.cl
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
pub fn toposort(graph: &ModuleGraph) -> Result<Vec<ModuleFullPath>, CranelispError> {
    use std::collections::VecDeque;

    let mut in_degree: HashMap<ModuleFullPath, usize> = HashMap::new();
    let mut adj: HashMap<ModuleFullPath, Vec<ModuleFullPath>> = HashMap::new();

    for (path, node) in &graph.nodes {
        in_degree.entry(path.clone()).or_insert(0);
        for dep in &node.dependencies {
            adj.entry(dep.clone()).or_default().push(path.clone());
            *in_degree.entry(path.clone()).or_insert(0) += 1;
        }
    }

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
