// Pipeline orchestration: source text -> parse -> build -> typecheck -> codegen -> execute.
//
// Two modes:
//   1. Single-file batch: `compile_and_run()` — compiles one source string.
//   2. Multi-file batch: `compile_module_graph()` — discovers modules, toposorts, compiles in order.
//
// No `unwrap()` in this module -- all errors use `?`.

use std::collections::{HashMap, VecDeque};
use std::path::{Path, PathBuf};

use cranelisp_types::{
    CheckResult, CompileMode, CranelispError, MacroClauseInfo, ModuleEntry, ModuleFullPath,
    ModuleStructure, Program, Sexp, Span, Type, Visibility, Warning,
};

use crate::expander::CraneliftExpander;

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
/// Pipeline stages:
/// 1. Parse source -> Vec<Sexp>
/// 2. Sequential form processing: defmacro interception, expansion, begin flattening
/// 3. Type check accumulated forms -> CheckResult
/// 4. Codegen -> CompiledProgram
/// 5. Execute -> i64
pub fn compile_and_run(
    source: &str,
    mode: CompileMode,
) -> Result<PipelineResult, CranelispError> {
    // Stage 1: Parse
    let sexps = cranelisp_frontend::parse(source)?;

    // Stage 2: Sequential form processing with macro expansion.
    let mut expander = CraneliftExpander::new();
    let mut tc = cranelisp_typecheck::TypeChecker::new();
    let mut jit_modules: Vec<cranelisp_backend::jit::Jit> = Vec::new();
    let program = process_forms_sequentially(
        sexps,
        &mut expander,
        &mut tc,
        &mut jit_modules,
    )?;

    // Stage 3: Type check
    let check = tc.check_program(&program)?;

    // Determine the result type from the last defn's return type.
    let result_type = infer_result_type(&program, &check);

    // Accumulate warnings from typecheck and codegen.
    let mut all_warnings: Vec<Warning> = check.warnings.clone();

    // Stage 4: Codegen
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
        // The defn's body span should have its type recorded.
        if let Some(ty) = check.expr_types.get(&defn.body.span()) {
            return ty.clone();
        }
    }

    // Fallback: Int (convention for unknown result types).
    Type::Int
}

// ---------------------------------------------------------------------------
// Sequential form processing (shared by batch and module graph pipelines)
// ---------------------------------------------------------------------------

/// Process sexps sequentially with defmacro interception and macro expansion.
///
/// Per pipeline-orchestration.md §2:
/// - `defmacro` forms are compiled and registered in the expander
/// - Remaining forms are expanded through the macro expander
/// - `(begin ...)` results are flattened
/// - Non-macro, non-type-def forms are accumulated for batch compilation
///
/// Returns the accumulated program (Vec<TopLevel>) ready for typechecking.
fn process_forms_sequentially(
    sexps: Vec<Sexp>,
    expander: &mut CraneliftExpander,
    tc: &mut cranelisp_typecheck::TypeChecker,
    jit_modules: &mut Vec<cranelisp_backend::jit::Jit>,
) -> Result<Program, CranelispError> {
    let mut accumulated: Vec<Sexp> = Vec::new();

    for sexp in sexps {
        process_single_form(sexp, expander, tc, jit_modules, &mut accumulated)?;
    }

    // Build the AST from all accumulated non-macro forms.
    cranelisp_frontend::build_program(&accumulated, expander)
}

/// Process a single Sexp form: intercept defmacro, expand macros, flatten begin.
///
/// Accumulated non-macro forms are pushed to `out`.
fn process_single_form(
    sexp: Sexp,
    expander: &mut CraneliftExpander,
    tc: &mut cranelisp_typecheck::TypeChecker,
    jit_modules: &mut Vec<cranelisp_backend::jit::Jit>,
    out: &mut Vec<Sexp>,
) -> Result<(), CranelispError> {
    // Intercept defmacro before expansion.
    if cranelisp_frontend::is_defmacro(&sexp) {
        compile_and_register_macro(&sexp, expander, tc, jit_modules)?;
        return Ok(());
    }

    // Expand macros in the sexp.
    let expanded = expander.expand_sexp(sexp)?;

    // Flatten (begin ...) results and process each sub-form.
    let forms = cranelisp_frontend::flatten_begin(expanded);
    for form in forms {
        if cranelisp_frontend::is_defmacro(&form) {
            // defmacro-in-results: a macro expansion produced a defmacro.
            compile_and_register_macro(&form, expander, tc, jit_modules)?;
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
fn compile_and_register_macro(
    sexp: &Sexp,
    expander: &mut CraneliftExpander,
    tc: &mut cranelisp_typecheck::TypeChecker,
    jit_modules: &mut Vec<cranelisp_backend::jit::Jit>,
) -> Result<(), CranelispError> {
    let info = cranelisp_frontend::parse_defmacro(sexp)?;

    let mut jit = cranelisp_backend::jit::Jit::new()?;
    jit.declare_intrinsics()?;

    expander.compile_macro(&info, tc, &mut jit)?;

    // Keep JIT alive so macro function pointers remain valid.
    jit_modules.push(jit);

    // Register macro in the current module's symbol table so it is visible
    // to cross-module imports (e.g., `(import [fn.threading [-> ->>]])`).
    // Without this, macros are only in the expander's MacroEnv and cannot
    // be found by the typechecker's module resolution.
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

/// Result of compiling a multi-file module graph.
pub struct CompiledModuleGraph {
    /// The i64 result value from executing the entry module's entry point.
    pub value: i64,
    /// The inferred type of the entry point's return value.
    pub ty: Type,
    /// Non-fatal warnings accumulated during compilation.
    pub warnings: Vec<Warning>,
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

/// Discover modules referenced by import specs that aren't already in the graph.
///
/// Import specs reference modules by their full dotted path (e.g., "util",
/// "core.option"). This function resolves the root module name and discovers
/// it if not already known. Synthetic modules (`primitives`, `macros`) and
/// `super` references are skipped — they have no files.
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
    for import_spec in &structure.import_specs {
        let import_path: &str = import_spec.module_path.as_ref();

        // Skip synthetic modules — they are compiler-seeded with no files.
        if is_synthetic_or_special(import_path) {
            continue;
        }

        // Extract the root module name (first component before any dot).
        // E.g., "core.option" -> "core", "util" -> "util".
        let root_name = import_path.split('.').next().unwrap_or(import_path);

        // The import path may be relative (bare name) or prefixed with the
        // current module path (e.g., "main.util" when current is "main").
        // Check both the bare import path and a child-qualified version.
        let candidate_path = if module_path.0.is_empty() {
            ModuleFullPath::from(root_name)
        } else {
            // Check if the import path already starts with the module path prefix.
            let mod_prefix = format!("{}.", module_path);
            if import_path.starts_with(&mod_prefix) {
                // Already fully qualified relative to this module — use as-is.
                import_spec.module_path.clone()
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
/// module structure (import specs, exports, submodule declarations) and the
/// remaining unprocessed sexps. The caller must register imports with the
/// TypeChecker BEFORE processing the remaining sexps (Phase 2), because
/// `process_forms_sequentially` compiles `defmacro` forms that may reference
/// imported names.
fn parse_and_extract_module(
    module_path: &ModuleFullPath,
    node: &ModuleNode,
) -> Result<(ModuleStructure, Vec<Sexp>), CranelispError> {
    let source = std::fs::read_to_string(&node.file_path).map_err(|e| {
        CranelispError::ModuleError {
            message: format!("cannot read '{}': {}", node.file_path.display(), e),
            file: Some(node.file_path.clone()),
            span: Span::SYNTHETIC,
        }
    })?;

    let sexps = cranelisp_frontend::parse(&source)?;

    cranelisp_frontend::extract_module_declarations(
        module_path.clone(),
        Some(node.file_path.clone()),
        sexps,
    )
}

/// Accumulate function signatures from a compiled module, including
/// qualified aliases for submodule functions.
fn accumulate_func_sigs(
    module_path: &ModuleFullPath,
    func_signatures: &[(cranelisp_types::Symbol, usize)],
    all_func_sigs: &mut Vec<(cranelisp_types::Symbol, usize)>,
) {
    for (name, arity) in func_signatures {
        all_func_sigs.push((name.clone(), *arity));

        // For submodule functions, register qualified aliases at every suffix
        // of the dotted module path. E.g., module "main.mid.leaf" function
        // "value" gets aliases:
        //   "leaf/value"          — last component (child-relative ref)
        //   "mid.leaf/value"      — two-component suffix
        //   "main.mid.leaf/value" — full absolute path
        // This allows both child-relative refs like (leaf/value) and
        // fully-qualified refs like (main.mid.leaf/value) to resolve at
        // codegen time (spec §8.5.1).
        let mod_str: &str = module_path.as_ref();
        for (idx, _) in mod_str.match_indices('.') {
            let suffix = &mod_str[idx + 1..];
            let qualified =
                cranelisp_types::Symbol::from(format!("{}/{}", suffix, name));
            all_func_sigs.push((qualified, *arity));
        }
        // Also register the full module path as an alias (for absolute refs).
        if mod_str.contains('.') {
            let qualified =
                cranelisp_types::Symbol::from(format!("{}/{}", mod_str, name));
            all_func_sigs.push((qualified, *arity));
        }
    }
}

/// Find the last zero-arg defn in a program (the entry point).
fn find_entry_defn(program: &Program) -> Option<cranelisp_types::Symbol> {
    program.iter().rev().find_map(|tl| {
        if let cranelisp_types::TopLevel::Defn(defn) = tl
            && defn.params.is_empty()
        {
            return Some(defn.name.clone());
        }
        None
    })
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

/// Load and compile the prelude module, if found.
///
/// This compiles the prelude through the normal `compile_module_graph` pipeline
/// and injects an implicit `(import [prelude [*]])` into the current module.
///
/// The prelude is NOT special — it is ordinary user code resolved through
/// normal module resolution. The only special behavior is the implicit import.
///
/// Returns the JIT modules to keep alive (for macro function pointers).
/// The function modifies `tc`, `expander`, and `jit` in place.
pub fn load_prelude(
    project_root: &Path,
    lib_dirs: &[PathBuf],
    tc: &mut cranelisp_typecheck::TypeChecker,
    expander: &mut CraneliftExpander,
    jit: &mut cranelisp_backend::jit::Jit,
    all_func_sigs: &mut Vec<(cranelisp_types::Symbol, usize)>,
) -> Result<Vec<cranelisp_backend::jit::Jit>, CranelispError> {
    let prelude_file = match resolve_prelude(project_root, lib_dirs) {
        Some(f) => f,
        None => return Ok(Vec::new()),
    };

    // Discover the prelude module graph.
    let graph = discover_module_graph(&prelude_file, lib_dirs)?;
    let order = toposort(&graph)?;

    let mut macro_jit_modules: Vec<cranelisp_backend::jit::Jit> = Vec::new();

    for module_path in &order {
        let node = &graph.nodes[module_path];

        // Phase 1: Parse and extract declarations (no tc interaction).
        let (structure, remaining_sexps) = parse_and_extract_module(module_path, node)?;

        // Phase 2: Set up module context BEFORE processing forms.
        tc.set_current_module(module_path.clone());
        if !structure.import_specs.is_empty() {
            tc.register_imports(&structure.import_specs)?;
        }

        // Phase 3: Process forms (defmacro compilation happens here, needs imports).
        let program =
            process_forms_sequentially(remaining_sexps, expander, tc, &mut macro_jit_modules)?;

        // Phase 4: Typecheck and compile.
        if program.is_empty() {
            continue;
        }

        let check = tc.check_program(&program)?;

        // Skip codegen for modules with no compilable definitions (e.g.,
        // type-only or trait-only modules). Typechecking still registers
        // types and traits in the TC.
        if has_compilable_defns(&program) {
            let module_info = cranelisp_backend::compile_module_program(
                &program,
                &check,
                CompileMode::Batch,
                jit,
                all_func_sigs,
            )?;

            accumulate_func_sigs(module_path, &module_info.func_signatures, all_func_sigs);
        }
    }

    // Inject implicit (import [prelude [*]]) into the "user" module.
    // After the loop above, tc.current_module is the last module in toposort
    // (i.e. "prelude"), so we must switch to "user" before registering the
    // import — otherwise it becomes a self-import no-op on "prelude".
    let user_module = ModuleFullPath::from("user");
    tc.set_current_module(user_module);

    let prelude_module = ModuleFullPath::from("prelude");
    let import_spec = cranelisp_types::ImportSpec {
        module_path: prelude_module,
        alias: None,
        names: cranelisp_types::ImportNames::Glob,
        span: Span::SYNTHETIC,
    };
    tc.register_imports(&[import_spec])?;

    Ok(macro_jit_modules)
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

/// Compile a multi-file module graph and execute the entry point.
///
/// Pipeline:
/// 1. Discover module graph from entry file
/// 2. Topological sort (dependencies first)
/// 3. For each module in order: parse, extract declarations, process imports,
///    sequential form processing (defmacro interception, expansion),
///    build AST, type-check, compile into shared JIT
/// 4. Finalize the shared JIT once all modules are compiled
/// 5. Execute the entry module's last zero-arg defn
pub fn compile_module_graph(
    entry: &Path,
    lib_dirs: &[PathBuf],
) -> Result<CompiledModuleGraph, CranelispError> {
    let graph = discover_module_graph(entry, lib_dirs)?;
    let order = toposort(&graph)?;

    let mut all_warnings: Vec<Warning> = Vec::new();
    let mut tc = cranelisp_typecheck::TypeChecker::new();
    let mut expander = CraneliftExpander::new();
    let mut macro_jit_modules: Vec<cranelisp_backend::jit::Jit> = Vec::new();
    let mut jit = cranelisp_backend::jit::Jit::new()?;
    jit.declare_intrinsics()?;

    let mut all_func_sigs: Vec<(cranelisp_types::Symbol, usize)> = Vec::new();

    // Load prelude if available (optional — system works without it).
    let prelude_jits = load_prelude(
        &graph.project_root,
        &graph.lib_dirs,
        &mut tc,
        &mut expander,
        &mut jit,
        &mut all_func_sigs,
    )?;
    macro_jit_modules.extend(prelude_jits);

    let mut entry_defn_name: Option<cranelisp_types::Symbol> = None;
    let mut entry_result_type = Type::Int;

    // Check whether a prelude was loaded so we can inject implicit imports
    // into each module in the graph (spec §8.8.1).
    let prelude_loaded = tc.has_module(&ModuleFullPath::from("prelude"));

    for module_path in &order {
        let node = &graph.nodes[module_path];

        // Phase 1: Parse and extract declarations (no tc interaction).
        let (structure, remaining_sexps) = parse_and_extract_module(module_path, node)?;

        // Phase 2: Set up module context BEFORE processing forms.
        tc.set_current_module(module_path.clone());

        // Inject implicit (import [prelude [*]]) for non-prelude modules
        // (spec §8.8.1). load_prelude() already injects into "user", but
        // batch entry modules have a different path (e.g. "main" for main.cl)
        // and need it too for prelude traits to resolve.
        if prelude_loaded {
            inject_prelude_import(&mut tc)?;
        }

        if !structure.import_specs.is_empty() {
            tc.register_imports(&structure.import_specs)?;
        }

        // Phase 3: Process forms (defmacro compilation happens here, needs imports).
        let program = process_forms_sequentially(
            remaining_sexps,
            &mut expander,
            &mut tc,
            &mut macro_jit_modules,
        )?;

        // Phase 4: Typecheck and compile.
        if program.is_empty() {
            continue;
        }

        let check = tc.check_program(&program)?;
        all_warnings.extend(check.warnings.iter().cloned());

        let result_type = infer_result_type(&program, &check);

        // Skip codegen for modules with no compilable definitions (e.g.,
        // type-only or trait-only modules like fn/option.cl).
        if has_compilable_defns(&program) {
            let module_info = cranelisp_backend::compile_module_program(
                &program,
                &check,
                CompileMode::Batch,
                &mut jit,
                &all_func_sigs,
            )?;
            all_warnings.extend(module_info.warnings);

            accumulate_func_sigs(module_path, &module_info.func_signatures, &mut all_func_sigs);
        }

        if module_path == &graph.entry
            && let Some(name) = find_entry_defn(&program)
        {
            entry_defn_name = Some(name);
            entry_result_type = result_type;
        }
    }

    // Finalize the shared JIT (resolves all cross-references).
    jit.finalize()?;

    // Execute the entry module's entry point.
    let (value, ty) = if let Some(ref name) = entry_defn_name {
        let entry_ptr = jit.get_ptr_by_name(name, 0)?;
        // SAFETY: compiled code was just generated and finalized by our JIT.
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(entry_ptr) };
        let value = func();
        (value, entry_result_type)
    } else {
        (0, Type::Int)
    };

    Ok(CompiledModuleGraph {
        value,
        ty,
        warnings: all_warnings,
    })
}

/// Check whether a program has any definitions that require codegen.
///
/// Modules with only type definitions or trait declarations (no function
/// bodies) should skip codegen — the typechecker has already registered
/// their types/traits. This avoids "no function definitions in program"
/// errors from the backend.
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
            (defmacro inc1 [x] `(add-i64 1 ~x))
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
        let source = "(defn main [] (add-i64 1 2))";
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
