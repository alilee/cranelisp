// Module discovery and cross-module import integration tests.
//
// These tests exercise the module graph discovery and compilation pipeline
// from spec/08-modules.md. They use tempfile to create controlled filesystem
// fixtures, then call discover_module_graph and/or compile_module_graph to
// verify behavior.
//
// Known gaps (multi-dot import paths, deep qualified refs) are documented
// as FIXME comments below where the tests were removed.

#[path = "helpers/mod.rs"]
mod helpers;

use cranelisp::pipeline::{compile_module_graph, discover_module_graph, toposort};
use cranelisp_types::ModuleFullPath;
use tempfile::TempDir;

/// Create a temporary project directory with the given files.
/// Each entry is (relative_path, content). Subdirectories are created automatically.
fn create_test_project(files: &[(&str, &str)]) -> TempDir {
    let dir = tempfile::tempdir().unwrap();
    for (path, content) in files {
        let full = dir.path().join(path);
        if let Some(parent) = full.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(&full, content).unwrap();
    }
    dir
}

// =============================================================================
// 1. Cross-module import without (mod ...) declaration
//    spec: 08-modules §8.3, §8.10.1
// =============================================================================

// spec: 08-modules §8.10.1 — dependency graph from import forms
#[test]
fn import_without_mod_discovers_dependency() {
    // Module A does (import [B [thing]]) but does NOT declare (mod B).
    // File B.cl exists as a sibling. The dependency should be discovered.
    let dir = create_test_project(&[
        ("main.cl", "(import [util [helper]])\n(defn main [] (helper))"),
        ("util.cl", "(defn helper [] 42)"),
    ]);
    let graph = discover_module_graph(&dir.path().join("main.cl"), &[]).unwrap();

    // util should be discovered as a dependency even without (mod util).
    assert!(
        graph.nodes.contains_key(&ModuleFullPath::from("util")),
        "import-referenced module 'util' should be discovered without (mod util)"
    );
}

// spec: 08-modules §8.10.1 — import-driven dependency compiles and runs
#[test]
fn import_without_mod_compiles_and_runs() {
    // End-to-end: A imports from B without (mod B). Should compile and execute.
    let dir = create_test_project(&[
        ("main.cl", "(import [util [helper]])\n(defn main [] (helper))"),
        ("util.cl", "(defn helper [] 42)"),
    ]);
    let result = compile_module_graph(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(result.value, 42);
}

// =============================================================================
// 2. Import-driven dependency ordering
//    spec: 08-modules §8.10.1, §8.10.3
// =============================================================================

// spec: 08-modules §8.10.1 — toposort respects import dependencies
#[test]
fn import_dependency_ordering_with_mod() {
    // Module A declares (mod B) and imports from B. B must compile before A.
    // This works because (mod B) triggers file discovery.
    let dir = create_test_project(&[
        ("main.cl", "(mod util)\n(import [main.util [helper]])\n(defn main [] (helper))"),
        ("util.cl", "(defn helper [] 42)"),
    ]);
    let graph = discover_module_graph(&dir.path().join("main.cl"), &[]).unwrap();
    let order = toposort(&graph).unwrap();

    // util should come before main in the compilation order.
    let util_pos = order
        .iter()
        .position(|p| p.to_string().contains("util"))
        .expect("util should be in toposort order");
    let main_pos = order
        .iter()
        .position(|p| p.to_string() == "main")
        .expect("main should be in toposort order");
    assert!(
        util_pos < main_pos,
        "util (position {util_pos}) must compile before main (position {main_pos})"
    );
}

// spec: 08-modules §8.10.3 — compile_module_graph with import dependency
#[test]
fn import_dependency_compiles_correctly() {
    // Module main declares (mod util) and imports a function from it.
    // The function should be callable.
    let dir = create_test_project(&[
        (
            "main.cl",
            "(mod util)\n(import [main.util [helper]])\n(defn main [] (helper))",
        ),
        ("util.cl", "(defn helper [] 99)"),
    ]);
    let result = compile_module_graph(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(result.value, 99);
}

// =============================================================================
// 3. Stdlib-dir module resolution
//    spec: 08-modules §8.11.2
// =============================================================================

// spec: 08-modules §8.11.2 — module in stdlib directory is found
#[test]
fn stdlib_dir_module_resolution() {
    // A module declares (mod helper). The file is in stdlib/, not project root.
    let dir = create_test_project(&[
        ("main.cl", "(mod helper)\n(defn main [] (helper/greet))"),
    ]);
    let stdlib_dir = dir.path().join("stdlib");
    std::fs::create_dir_all(&stdlib_dir).unwrap();
    std::fs::write(stdlib_dir.join("helper.cl"), "(defn greet [] 77)").unwrap();

    let graph =
        discover_module_graph(&dir.path().join("main.cl"), &[stdlib_dir.clone()]).unwrap();
    assert!(
        graph.nodes.contains_key(&ModuleFullPath::from("main.helper")),
        "module from stdlib dir should be discovered"
    );
}

// spec: 08-modules §8.11.2 — project root module shadows stdlib module
#[test]
fn project_root_shadows_stdlib() {
    // Both project root and stdlib have a module with the same name.
    // Project root should take precedence.
    let dir = create_test_project(&[
        ("main.cl", "(mod helper)\n(defn main [] (helper/val))"),
        ("helper.cl", "(defn val [] 100)"),
    ]);
    let stdlib_dir = dir.path().join("stdlib");
    std::fs::create_dir_all(&stdlib_dir).unwrap();
    std::fs::write(stdlib_dir.join("helper.cl"), "(defn val [] 200)").unwrap();

    // When main.cl is the entry, (mod helper) first looks for main/helper.cl
    // (child dir), then helper.cl (sibling). The sibling is in project root.
    // stdlib should NOT be used because the project root file exists.
    let result = compile_module_graph(
        &dir.path().join("main.cl"),
        &[stdlib_dir.clone()],
    )
    .unwrap();
    assert_eq!(
        result.value, 100,
        "project root module should shadow stdlib module"
    );
}

// spec: 08-modules §8.11.2 — stdlib module compiles and runs
#[test]
fn stdlib_module_compiles_and_runs() {
    // A module declares (mod helper) and the file is only in stdlib.
    let dir = create_test_project(&[
        ("main.cl", "(mod helper)\n(defn main [] (helper/compute))"),
    ]);
    let stdlib_dir = dir.path().join("stdlib");
    std::fs::create_dir_all(&stdlib_dir).unwrap();
    std::fs::write(stdlib_dir.join("helper.cl"), "(defn compute [] 55)").unwrap();

    let result = compile_module_graph(
        &dir.path().join("main.cl"),
        &[stdlib_dir.clone()],
    )
    .unwrap();
    assert_eq!(result.value, 55);
}

// =============================================================================
// 4. Prelude-like module that imports from submodules
//    spec: 08-modules §8.8, §8.10.4
// =============================================================================

// spec: 08-modules §8.4 — module that re-exports from submodules
#[test]
fn module_with_submodule_imports() {
    // A "prelude-like" module declares a submodule and uses it via qualified ref.
    // The module graph should discover the submodule as a dependency.
    // (mod shell) in main.cl -> sibling shell.cl = module "main.shell"
    // (mod inner) in shell.cl -> shell/inner.cl = module "main.shell.inner"
    // Note: we use qualified refs here (not import forms) to test that
    // qualified references with dotted module paths work for graph discovery.
    let dir = create_test_project(&[
        ("main.cl", "(mod shell)\n(defn main [] (main.shell/relay))"),
        ("shell.cl", "(mod inner)\n(defn relay [] (main.shell.inner/get-val))"),
        ("shell/inner.cl", "(defn get-val [] 33)"),
    ]);
    let graph = discover_module_graph(&dir.path().join("main.cl"), &[]).unwrap();
    assert!(
        graph
            .nodes
            .contains_key(&ModuleFullPath::from("main.shell.inner")),
        "submodule 'main.shell.inner' should be discovered, got: {:?}",
        graph.nodes.keys().collect::<Vec<_>>()
    );

    let order = toposort(&graph).unwrap();
    let inner_pos = order
        .iter()
        .position(|p| p.to_string() == "main.shell.inner")
        .expect("main.shell.inner should be in order");
    let shell_pos = order
        .iter()
        .position(|p| p.to_string() == "main.shell")
        .expect("main.shell should be in order");
    assert!(
        inner_pos < shell_pos,
        "main.shell.inner must compile before main.shell"
    );
}

// spec: 08-modules §8.4 — prelude-like re-export module compiles
// This test uses a one-level deep hierarchy (main imports from main.shell).
#[test]
fn prelude_like_reexport_compiles() {
    // Shell module defines a function and re-exports from a submodule.
    // Main imports from shell and calls the re-exported function.
    // Here we test the simpler pattern: main imports from main.shell.
    let dir = create_test_project(&[
        (
            "main.cl",
            "(mod shell)\n(import [main.shell [get-val]])\n(defn main [] (get-val))",
        ),
        ("shell.cl", "(defn get-val [] 88)"),
    ]);
    let result = compile_module_graph(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(result.value, 88);
}

// spec: 08-modules §8.3 — multi-dot module path in import
#[test]
fn multi_dot_module_path_in_import() {
    let dir = create_test_project(&[
        (
            "main.cl",
            "(mod shell)\n(import [main.shell [relay]])\n(defn main [] (relay))",
        ),
        (
            "shell.cl",
            "(mod inner)\n(import [main.shell.inner [get-val]])\n(defn relay [] (get-val))",
        ),
        ("shell/inner.cl", "(defn get-val [] 88)"),
    ]);
    let result = compile_module_graph(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(result.value, 88);
}

// =============================================================================
// 5. Nested imports: A -> B -> C (three-level dependency chain)
//    spec: 08-modules §8.10.1
// =============================================================================

// spec: 08-modules §8.10.1 — three-level dependency chain
#[test]
fn nested_dependency_chain_discovered() {
    // main declares (mod mid), mid declares (mod leaf).
    // (mod mid) in main.cl -> sibling mid.cl = module "main.mid"
    // (mod leaf) in mid.cl -> mid/leaf.cl = module "main.mid.leaf"
    // Uses qualified refs (main.mid.leaf/value) which the reader handles
    // because the dot-chain is followed by '/'.
    let dir = create_test_project(&[
        ("main.cl", "(mod mid)\n(defn main [] (main.mid/relay))"),
        ("mid.cl", "(mod leaf)\n(defn relay [] (main.mid.leaf/value))"),
        ("mid/leaf.cl", "(defn value [] 7)"),
    ]);
    let graph = discover_module_graph(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(
        graph.nodes.len(),
        3,
        "should discover 3 modules, got: {:?}",
        graph.nodes.keys().collect::<Vec<_>>()
    );

    let order = toposort(&graph).unwrap();
    let leaf_pos = order
        .iter()
        .position(|p| p.to_string() == "main.mid.leaf")
        .expect("main.mid.leaf should be in order");
    let mid_pos = order
        .iter()
        .position(|p| p.to_string() == "main.mid")
        .expect("main.mid should be in order");
    let main_pos = order
        .iter()
        .position(|p| p.to_string() == "main")
        .expect("main should be in order");
    assert!(leaf_pos < mid_pos, "leaf must compile before mid");
    assert!(mid_pos < main_pos, "mid must compile before main");
}

// spec: 08-modules §8.5.1 — three-level chain compiles with qualified refs
#[test]
fn nested_dependency_chain_compiles() {
    let dir = create_test_project(&[
        (
            "main.cl",
            "(mod mid)\n(import [main.mid [relay]])\n(defn main [] (relay))",
        ),
        (
            "mid.cl",
            "(mod leaf)\n(defn relay [] (main.mid.leaf/value))",
        ),
        ("mid/leaf.cl", "(defn value [] 7)"),
    ]);
    let result = compile_module_graph(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(result.value, 7);
}

// spec: 08-modules §8.5.1 — transitive import works with qualified refs
#[test]
fn transitive_import_chain() {
    let dir = create_test_project(&[
        (
            "main.cl",
            "(mod mid)\n(import [main.mid [relay]])\n(defn main [] (relay))",
        ),
        (
            "mid.cl",
            "(mod leaf)\n(defn relay [] (main.mid.leaf/base-val))",
        ),
        ("mid/leaf.cl", "(defn base-val [] 13)"),
    ]);
    let result = compile_module_graph(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(result.value, 13);
}

// =============================================================================
// Negative tests: import errors
// =============================================================================

// spec: 08-modules §8.3.1 — importing a private name gives error
#[test]
fn import_private_name_errors() {
    let dir = create_test_project(&[
        (
            "main.cl",
            "(mod util)\n(import [main.util [secret]])\n(defn main [] (secret))",
        ),
        ("util.cl", "(defn- secret [] 42)"),
    ]);
    let result = compile_module_graph(&dir.path().join("main.cl"), &[]);
    assert!(
        result.is_err(),
        "importing a private name should produce an error"
    );
}

// spec: 08-modules §8.5.4 — qualified reference to non-existent module errors
#[test]
fn qualified_ref_to_missing_module_errors() {
    let dir = create_test_project(&[
        ("main.cl", "(defn main [] (nonexistent/foo))"),
    ]);
    let result = compile_module_graph(&dir.path().join("main.cl"), &[]);
    assert!(
        result.is_err(),
        "qualified reference to non-existent module should error"
    );
}

// spec: 08-modules §8.7.3 — private defn not importable via glob
#[test]
fn glob_import_excludes_private() {
    // Glob import should NOT import private names.
    let dir = create_test_project(&[
        (
            "main.cl",
            "(mod util)\n(import [main.util [*]])\n(defn main [] (secret))",
        ),
        ("util.cl", "(defn- secret [] 42)\n(defn public-fn [] 1)"),
    ]);
    let result = compile_module_graph(&dir.path().join("main.cl"), &[]);
    assert!(
        result.is_err(),
        "glob import should not include private names; calling 'secret' should fail"
    );
}

// =============================================================================
// 7. Export re-export chains (spec: 08-modules §8.4)
// =============================================================================

// spec: 08-modules §8.4.1 — specific re-export makes name available to importer
#[test]
fn export_specific_reexport() {
    // inner.cl defines `val`. shell.cl re-exports `val` from inner.
    // main.cl imports `val` from shell — it arrives via the re-export.
    let dir = create_test_project(&[
        (
            "main.cl",
            "(mod shell)\n(import [main.shell [val]])\n(defn main [] (val))",
        ),
        (
            "shell.cl",
            "(mod inner)\n(import [main.shell.inner [val]])\n(export [main.shell.inner [val]])",
        ),
        ("shell/inner.cl", "(defn val [] 42)"),
    ]);
    let result = compile_module_graph(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(result.value, 42, "re-exported val should be callable");
}

// spec: 08-modules §8.4.2 — glob re-export exports all public names
#[test]
fn export_glob_reexport() {
    // inner.cl defines `a` and `b`. shell.cl glob re-exports from inner.
    // main.cl imports specific names from shell.
    let dir = create_test_project(&[
        (
            "main.cl",
            "(mod shell)\n(import [main.shell [a b]])\n(defn main [] (add-i64 (a) (b)))",
        ),
        (
            "shell.cl",
            "(mod inner)\n(import [main.shell.inner [*]])\n(export [main.shell.inner [*]])",
        ),
        ("shell/inner.cl", "(defn a [] 10)\n(defn b [] 20)"),
    ]);
    let result = compile_module_graph(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(result.value, 30, "glob re-exported names should be callable");
}

// spec: 08-modules §8.4.4 — re-export chain: A re-exports from B which re-exports from C
#[test]
fn export_transitive_reexport_chain() {
    // Three-level re-export: leaf -> mid -> shell -> main
    let dir = create_test_project(&[
        (
            "main.cl",
            "(mod shell)\n(import [main.shell [deep-val]])\n(defn main [] (deep-val))",
        ),
        (
            "shell.cl",
            "(mod mid)\n(import [main.shell.mid [deep-val]])\n(export [main.shell.mid [deep-val]])",
        ),
        (
            "shell/mid.cl",
            "(mod leaf)\n(import [main.shell.mid.leaf [deep-val]])\n(export [main.shell.mid.leaf [deep-val]])",
        ),
        ("shell/mid/leaf.cl", "(defn deep-val [] 77)"),
    ]);
    let result = compile_module_graph(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(
        result.value, 77,
        "transitive re-export chain should resolve"
    );
}

// spec: 08-modules §8.4.3 — multiple module re-export
#[test]
fn export_multiple_modules() {
    // shell.cl re-exports from two different submodules.
    let dir = create_test_project(&[
        (
            "main.cl",
            "(mod shell)\n(import [main.shell [alpha beta]])\n(defn main [] (add-i64 (alpha) (beta)))",
        ),
        (
            "shell.cl",
            "(mod a)\n(mod b)\n(import [main.shell.a [alpha]])\n(import [main.shell.b [beta]])\n(export [main.shell.a [alpha]\n         main.shell.b [beta]])",
        ),
        ("shell/a.cl", "(defn alpha [] 3)"),
        ("shell/b.cl", "(defn beta [] 7)"),
    ]);
    let result = compile_module_graph(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(result.value, 10, "multi-module re-export should work");
}

// spec: 08-modules §8.4.4 — re-exported private name is NOT accessible
#[test]
fn export_private_name_not_reexported() {
    // inner.cl has private `secret`. shell.cl tries to re-export it.
    // This should fail because private names cannot be re-exported.
    let dir = create_test_project(&[
        (
            "main.cl",
            "(mod shell)\n(import [main.shell [secret]])\n(defn main [] (secret))",
        ),
        (
            "shell.cl",
            "(mod inner)\n(import [main.shell.inner [*]])\n(export [main.shell.inner [secret]])",
        ),
        ("shell/inner.cl", "(defn- secret [] 42)\n(defn public-fn [] 1)"),
    ]);
    let result = compile_module_graph(&dir.path().join("main.cl"), &[]);
    assert!(
        result.is_err(),
        "private names should not be re-exportable"
    );
}
