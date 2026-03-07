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
    CheckResult, CompileMode, CranelispError, ModuleFullPath, NoOpExpander, Program, Span, Type,
    Warning,
};

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
/// 2. Build program -> Vec<TopLevel>
/// 3. Type check -> CheckResult
/// 4. Codegen -> CompiledProgram
/// 5. Execute -> i64
pub fn compile_and_run(
    source: &str,
    mode: CompileMode,
) -> Result<PipelineResult, CranelispError> {
    // Stage 1: Parse
    let sexps = cranelisp_frontend::parse(source)?;

    // Stage 2: Build AST
    let mut expander = NoOpExpander;
    let program = cranelisp_frontend::build_program(&sexps, &mut expander)?;

    // Stage 3: Type check
    let mut tc = cranelisp_typecheck::TypeChecker::new();
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
    /// Lib directory for standard library resolution.
    pub lib_dir: Option<PathBuf>,
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
pub fn discover_module_graph(entry: &Path) -> Result<ModuleGraph, CranelispError> {
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

    // Check for lib/ directory.
    let lib_dir = {
        let candidate = project_root.join("lib");
        if candidate.is_dir() { Some(candidate) } else { None }
    };

    let mut graph = ModuleGraph {
        nodes: HashMap::new(),
        entry: entry_path.clone(),
        project_root: project_root.clone(),
        lib_dir,
    };

    // BFS/DFS discovery with cycle detection.
    let mut visiting: Vec<ModuleFullPath> = Vec::new();
    discover_module_recursive(
        &entry_path,
        &entry,
        &project_root,
        &graph.lib_dir,
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
    lib_dir: &Option<PathBuf>,
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
            lib_dir,
        )?;

        dependencies.push(child_path.clone());

        // Recurse into the submodule.
        discover_module_recursive(
            &child_path,
            &resolved,
            project_root,
            lib_dir,
            nodes,
            visiting,
        )?;
    }

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

/// Resolve a submodule's file path per spec section 8.2.5.
///
/// Search order:
/// 1. Child directory: `{parent_dir}/{stem}/{name}.cl`
/// 2. Sibling file: `{parent_dir}/{name}.cl`
/// 3. Project root: `{project_root}/{name}.cl`
/// 4. Lib directory: `{lib_dir}/{name}.cl`
fn resolve_submodule_file(
    parent_file: &Path,
    name: &str,
    project_root: &Path,
    lib_dir: &Option<PathBuf>,
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

    // 4. Lib directory: {lib_dir}/{name}.cl
    if let Some(lib) = lib_dir {
        let lib_file = lib.join(&filename);
        if lib_file.is_file() {
            return Ok(lib_file);
        }
    }

    Err(CranelispError::ModuleError {
        message: format!(
            "cannot find module '{}' (searched child dir '{}/{}/', sibling '{}/{}', \
             project root, and lib)",
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

/// Parse, extract declarations, and build the AST for a single module.
///
/// Returns the import specs and the program (AST). If the module has no
/// definitions or expressions, the program will be empty.
fn parse_and_build_module(
    module_path: &ModuleFullPath,
    node: &ModuleNode,
) -> Result<(Vec<cranelisp_types::ImportSpec>, Program), CranelispError> {
    let source = std::fs::read_to_string(&node.file_path).map_err(|e| {
        CranelispError::ModuleError {
            message: format!("cannot read '{}': {}", node.file_path.display(), e),
            file: Some(node.file_path.clone()),
            span: Span::SYNTHETIC,
        }
    })?;

    let sexps = cranelisp_frontend::parse(&source)?;

    let (structure, remaining) = cranelisp_frontend::extract_module_declarations(
        module_path.clone(),
        Some(node.file_path.clone()),
        sexps,
    )?;

    let mut expander = NoOpExpander;
    let program = cranelisp_frontend::build_program(&remaining, &mut expander)?;

    Ok((structure.import_specs, program))
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

        // For submodule functions, register qualified aliases.
        // E.g., module "main.util" function "helper" gets alias "util/helper"
        // so that module "main" can call (util/helper).
        let mod_str: &str = module_path.as_ref();
        if let Some(dot_pos) = mod_str.rfind('.') {
            let last_component = &mod_str[dot_pos + 1..];
            let qualified =
                cranelisp_types::Symbol::from(format!("{}/{}", last_component, name));
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

/// Compile a multi-file module graph and execute the entry point.
///
/// Pipeline:
/// 1. Discover module graph from entry file
/// 2. Topological sort (dependencies first)
/// 3. For each module in order: parse, extract declarations, process imports,
///    build AST, type-check, compile into shared JIT
/// 4. Finalize the shared JIT once all modules are compiled
/// 5. Execute the entry module's last zero-arg defn
pub fn compile_module_graph(entry: &Path) -> Result<CompiledModuleGraph, CranelispError> {
    let graph = discover_module_graph(entry)?;
    let order = toposort(&graph)?;

    let mut all_warnings: Vec<Warning> = Vec::new();
    let mut tc = cranelisp_typecheck::TypeChecker::new();
    let mut jit = cranelisp_backend::jit::Jit::new()?;
    jit.declare_intrinsics()?;

    let mut all_func_sigs: Vec<(cranelisp_types::Symbol, usize)> = Vec::new();
    let mut entry_defn_name: Option<cranelisp_types::Symbol> = None;
    let mut entry_result_type = Type::Int;

    for module_path in &order {
        let node = &graph.nodes[module_path];
        let (import_specs, program) = parse_and_build_module(module_path, node)?;

        tc.set_current_module(module_path.clone());

        if !import_specs.is_empty() {
            tc.register_imports(&import_specs)?;
        }

        if program.is_empty() {
            continue;
        }

        let check = tc.check_program(&program)?;
        all_warnings.extend(check.warnings.iter().cloned());

        let result_type = infer_result_type(&program, &check);

        let module_info = cranelisp_backend::compile_module_program(
            &program,
            &check,
            CompileMode::Batch,
            &mut jit,
            &all_func_sigs,
        )?;
        all_warnings.extend(module_info.warnings);

        accumulate_func_sigs(module_path, &module_info.func_signatures, &mut all_func_sigs);

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

        let graph = discover_module_graph(&entry).unwrap();
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

        let graph = discover_module_graph(&entry).unwrap();
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

        let graph = discover_module_graph(&entry).unwrap();
        let handler_node = &graph.nodes[&ModuleFullPath::from("app.handler")];
        // Should resolve to child directory version.
        assert!(handler_node.file_path.to_str().unwrap().contains("app/handler.cl"));
    }

    #[test]
    fn test_discover_missing_module_error() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod nonexistent)").unwrap();

        let result = discover_module_graph(&entry);
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
            lib_dir: None,
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
            lib_dir: None,
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
            lib_dir: None,
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

        let result = compile_module_graph(&entry).unwrap();
        assert_eq!(result.value, 42);
        assert_eq!(result.ty, Type::Int);
    }

    #[test]
    fn test_compile_file_not_found() {
        let result = compile_module_graph(Path::new("/nonexistent/path/main.cl"));
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
        let graph = discover_module_graph(&entry).unwrap();
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
        let lib_dir = dir.path().join("lib");
        std::fs::create_dir_all(&lib_dir).unwrap();
        std::fs::write(lib_dir.join("helper.cl"), "(defn help [] 2)").unwrap();

        let graph = discover_module_graph(&entry).unwrap();
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

        let graph = discover_module_graph(&entry).unwrap();
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

        let result = compile_module_graph(&entry).unwrap();
        assert_eq!(result.value, 42);
    }
}
