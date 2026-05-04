// QUARANTINED — Sprint 64 Wave 5 test-port. Not built or run by Cargo.
// FIXME: design/arch/fixmes/0138-harvest-tests-legacy-modules.md
// Owning crate: crates/cranelisp-frontend (module_extract)
// Owning skill: /frontend (module discovery internals)
// Quarantined: 2026-05-04
//
// This file's assertions test Rust-internal state with no clean e2e
// equivalent (or the language-behaviour subset has been carried forward
// into the spec-section files). Harvest into `#[cfg(test)]` unit tests
// inside the owning crate per memory/feedback_unit_tests_with_dev.md and
// memory/project_test_strategy.md. Source preserved verbatim; translation
// may require dev-dependency adjustments and import rewrites.

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

use tempfile::TempDir;

// discover_module_graph and toposort were removed from pipeline.rs.
// Tests below that depended on them are commented out. Tests using
// helpers::batch_run_file (end-to-end) are unaffected.

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
// DISABLED: discover_module_graph removed from pipeline.rs
// #[test]
// fn import_without_mod_discovers_dependency() { ... }

// spec: 08-modules §8.10.1 — import-driven dependency compiles and runs
#[test]
fn import_without_mod_compiles_and_runs() {
    // End-to-end: A imports from B without (mod B). Should compile and execute.
    let dir = create_test_project(&[
        ("main.cl", "(import [util [helper]])\n(defn main [] (helper))"),
        ("util.cl", "(defn helper [] 42)"),
    ]);
    let (value, _ty) = helpers::batch_run_file(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(value, 42);
}

// =============================================================================
// 2. Import-driven dependency ordering
//    spec: 08-modules §8.10.1, §8.10.3
// =============================================================================

// spec: 08-modules §8.10.1 — toposort respects import dependencies
// DISABLED: discover_module_graph/toposort removed from pipeline.rs
// #[test]
// fn import_dependency_ordering_with_mod() { ... }

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
        ("main/util.cl", "(defn helper [] 99)"),
    ]);
    let (value, _ty) = helpers::batch_run_file(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(value, 99);
}

// =============================================================================
// 3. Stdlib-dir module resolution
//    spec: 08-modules §8.11.2
// =============================================================================

// spec: 08-modules §8.11.2 — module in stdlib directory is found
// DISABLED: discover_module_graph removed from pipeline.rs
// #[test]
// fn stdlib_dir_module_resolution() { ... }

// spec: 08-modules §8.11.2 — project root module shadows stdlib module
#[test]
fn project_root_shadows_stdlib() {
    // Both project root and stdlib have a module with the same name.
    // Project root should take precedence.
    let dir = create_test_project(&[
        ("main.cl", "(mod helper)\n(defn main [] (helper/val))"),
        ("main/helper.cl", "(defn val [] 100)"),
    ]);
    let stdlib_dir = dir.path().join("stdlib");
    std::fs::create_dir_all(stdlib_dir.join("main")).unwrap();
    std::fs::write(stdlib_dir.join("main/helper.cl"), "(defn val [] 200)").unwrap();

    // (mod helper) in main.cl resolves to main/helper.cl (child dir only).
    // Project root file should take precedence over stdlib.
    let (value, _ty) = helpers::batch_run_file(
        &dir.path().join("main.cl"),
        std::slice::from_ref(&stdlib_dir),
    )
    .unwrap();
    assert_eq!(
        value, 100,
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
    std::fs::create_dir_all(stdlib_dir.join("main")).unwrap();
    std::fs::write(stdlib_dir.join("main/helper.cl"), "(defn compute [] 55)").unwrap();

    let (value, _ty) = helpers::batch_run_file(
        &dir.path().join("main.cl"),
        std::slice::from_ref(&stdlib_dir),
    )
    .unwrap();
    assert_eq!(value, 55);
}

// =============================================================================
// 4. Prelude-like module that imports from submodules
//    spec: 08-modules §8.8, §8.10.4
// =============================================================================

// spec: 08-modules §8.4 — module that re-exports from submodules
// DISABLED: discover_module_graph/toposort removed from pipeline.rs
// #[test]
// fn module_with_submodule_imports() { ... }

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
        ("main/shell.cl", "(defn get-val [] 88)"),
    ]);
    let (value, _ty) = helpers::batch_run_file(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(value, 88);
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
            "main/shell.cl",
            "(mod inner)\n(import [main.shell.inner [get-val]])\n(defn relay [] (get-val))",
        ),
        ("main/shell/inner.cl", "(defn get-val [] 88)"),
    ]);
    let (value, _ty) = helpers::batch_run_file(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(value, 88);
}

// =============================================================================
// 5. Nested imports: A -> B -> C (three-level dependency chain)
//    spec: 08-modules §8.10.1
// =============================================================================

// spec: 08-modules §8.10.1 — three-level dependency chain
// DISABLED: discover_module_graph/toposort removed from pipeline.rs
// #[test]
// fn nested_dependency_chain_discovered() { ... }

// spec: 08-modules §8.5.1 — three-level chain compiles with qualified refs
#[test]
fn nested_dependency_chain_compiles() {
    let dir = create_test_project(&[
        (
            "main.cl",
            "(mod mid)\n(import [main.mid [relay]])\n(defn main [] (relay))",
        ),
        (
            "main/mid.cl",
            "(mod leaf)\n(defn relay [] (main.mid.leaf/value))",
        ),
        ("main/mid/leaf.cl", "(defn value [] 7)"),
    ]);
    let (value, _ty) = helpers::batch_run_file(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(value, 7);
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
            "main/mid.cl",
            "(mod leaf)\n(defn relay [] (main.mid.leaf/base-val))",
        ),
        ("main/mid/leaf.cl", "(defn base-val [] 13)"),
    ]);
    let (value, _ty) = helpers::batch_run_file(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(value, 13);
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
        ("main/util.cl", "(defn- secret [] 42)"),
    ]);
    let result = helpers::batch_run_file(&dir.path().join("main.cl"), &[]);
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
    let result = helpers::batch_run_file(&dir.path().join("main.cl"), &[]);
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
        ("main/util.cl", "(defn- secret [] 42)\n(defn public-fn [] 1)"),
    ]);
    let result = helpers::batch_run_file(&dir.path().join("main.cl"), &[]);
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
            "main/shell.cl",
            "(mod inner)\n(import [main.shell.inner [val]])\n(export [main.shell.inner [val]])",
        ),
        ("main/shell/inner.cl", "(defn val [] 42)"),
    ]);
    let (value, _ty) = helpers::batch_run_file(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(value, 42, "re-exported val should be callable");
}

// spec: 08-modules §8.4.2 — glob re-export exports all public names
#[test]
fn export_glob_reexport() {
    // inner.cl defines `a` and `b`. shell.cl glob re-exports from inner.
    // main.cl imports specific names from shell.
    let dir = create_test_project(&[
        (
            "main.cl",
            "(import [primitives [add-i64]])\n(mod shell)\n(import [main.shell [a b]])\n(defn main [] (add-i64 (a) (b)))",
        ),
        (
            "main/shell.cl",
            "(mod inner)\n(import [main.shell.inner [*]])\n(export [main.shell.inner [*]])",
        ),
        ("main/shell/inner.cl", "(defn a [] 10)\n(defn b [] 20)"),
    ]);
    let (value, _ty) = helpers::batch_run_file(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(value, 30, "glob re-exported names should be callable");
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
            "main/shell.cl",
            "(mod mid)\n(import [main.shell.mid [deep-val]])\n(export [main.shell.mid [deep-val]])",
        ),
        (
            "main/shell/mid.cl",
            "(mod leaf)\n(import [main.shell.mid.leaf [deep-val]])\n(export [main.shell.mid.leaf [deep-val]])",
        ),
        ("main/shell/mid/leaf.cl", "(defn deep-val [] 77)"),
    ]);
    let (value, _ty) = helpers::batch_run_file(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(
        value, 77,
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
            "(import [primitives [add-i64]])\n(mod shell)\n(import [main.shell [alpha beta]])\n(defn main [] (add-i64 (alpha) (beta)))",
        ),
        (
            "main/shell.cl",
            "(mod a)\n(mod b)\n(import [main.shell.a [alpha]])\n(import [main.shell.b [beta]])\n(export [main.shell.a [alpha]\n         main.shell.b [beta]])",
        ),
        ("main/shell/a.cl", "(defn alpha [] 3)"),
        ("main/shell/b.cl", "(defn beta [] 7)"),
    ]);
    let (value, _ty) = helpers::batch_run_file(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(value, 10, "multi-module re-export should work");
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
            "main/shell.cl",
            "(mod inner)\n(import [main.shell.inner [*]])\n(export [main.shell.inner [secret]])",
        ),
        ("main/shell/inner.cl", "(defn- secret [] 42)\n(defn public-fn [] 1)"),
    ]);
    let result = helpers::batch_run_file(&dir.path().join("main.cl"), &[]);
    assert!(
        result.is_err(),
        "private names should not be re-exportable"
    );
}

// spec: 08-modules §8.3 — imported function used as higher-order argument (batch)
// Batch pipeline handles this correctly.
#[test]
fn imported_function_as_higher_order_argument() {
    let dir = create_test_project(&[
        (
            "main.cl",
            "(mod helper)\n(import [main.helper [double]])\n(defn apply-fn [f x] (f x))\n(defn main [] (apply-fn double 21))",
        ),
        (
            "main/helper.cl",
            "(import [primitives [add-i64]])\n(defn double [x] (add-i64 x x))",
        ),
    ]);
    let result = helpers::batch_run_file(&dir.path().join("main.cl"), &[]);
    assert!(result.is_ok(), "imported fn as higher-order arg should compile: {}",
        result.as_ref().err().map(|e| format!("{e}")).unwrap_or_default());
    let (value, _ty) = result.unwrap();
    assert_eq!(value, 42);
}

// =============================================================================
// 8. Super-import (spec: 08-modules §8.3.7)
//
// `super` in an `import` module path resolves to the parent of the containing
// module (strip the last `.` component). It is rewritten at frontend capture
// time (arch Decision 30); downstream stages never see the literal "super".
// Using `super` in a top-level (root) module MUST produce a compile-time error.
// =============================================================================

// spec: 08-modules §8.3.7 — super import rewrites to parent path end-to-end.
// Child module `proj.child` uses `(import [super [*]])` to pull all public
// names from `proj`. The child's resolved imports MUST name the parent
// path absolutely after the rewrite — no lingering "super" literal is visible
// post-frontend.
//
// The child is used as the entry module so the parent does NOT import or
// qualify-ref into the child — this avoids the §8.3.7 known mutual-import
// deadlock while still exercising the super→parent rewrite end-to-end.
#[test]
fn super_import_rewrites_to_parent_end_to_end() {
    use cranelisp_types::{ModuleEntry, ModuleFullPath};

    // Parent `proj.cl` defines `parent-val`. Child `proj/child.cl` uses
    // `(import [super [*]])` and defines `main` that returns the parent's
    // value — demonstrating the rewrite resolves to the parent.
    let dir = create_test_project(&[
        (
            "proj.cl",
            "(defn parent-val [] 42)",
        ),
        (
            "proj/child.cl",
            "(import [super [*]])\n(defn main [] (parent-val))",
        ),
    ]);

    // Drive the pipeline via a session with proj.child as the entry module.
    // The module-name is fully qualified ("proj.child") so frontend sees the
    // correct containing_module and rewrites super → "proj".
    let mut session = helpers::ReplSession::new_for_file(
        &dir.path().join("proj.cl"),
        &[],
    )
    .expect("session setup");
    session
        .register_module("proj.child")
        .expect("proj.child should register — super must rewrite to parent");

    // Child compiles and its `main` can call the parent's `parent-val` —
    // proving super resolved to the parent module at every stage.
    let (value, _ty) = session
        .trampoline("proj.child")
        .expect("proj.child main should run — super rewrite makes parent-val visible");
    assert_eq!(
        value, 42,
        "child's main should return parent-val via super-rewritten import"
    );

    // Verify the rewrite is invisible downstream: no ModuleEntry::Import on
    // proj.child has source.module == "super". The rewrite MUST have replaced
    // the literal string with the parent path during frontend extraction
    // (Decision 30: rewrite at capture time in parse_import_entries).
    let child_path = ModuleFullPath::from("proj.child");
    let child_tbl = session
        .symbol_tables()
        .get(&child_path)
        .expect("child module should be registered in symbol_tables");
    let mut saw_parent_import = false;
    for (_sym, entry) in child_tbl.all_symbols() {
        if let ModuleEntry::Import { source } = entry {
            let src_mod = source.module.as_ref();
            assert_ne!(
                src_mod, "super",
                "super MUST be rewritten — no Import entry may carry the literal 'super'"
            );
            if src_mod == "proj" {
                saw_parent_import = true;
            }
        }
    }
    assert!(
        saw_parent_import,
        "child's resolved imports should name parent absolutely ('proj'), confirming super→parent rewrite applied"
    );
}

// spec: 08-modules §8.3.7 — `super` in a top-level (root) module MUST produce
// a compile-time error. Negative path per spec §8.3.7 final MUST clause.
#[test]
fn super_import_at_root_is_rejected_neg() {
    // Root module `root.cl` has no parent — a `super` import cannot resolve.
    let dir = create_test_project(&[
        (
            "root.cl",
            "(import [super [*]])\n(defn main [] 0)",
        ),
    ]);
    let result = helpers::batch_run_file(&dir.path().join("root.cl"), &[]);
    assert!(
        result.is_err(),
        "super in root module MUST be rejected per spec §8.3.7"
    );
    // Match by substring — frontend error reads:
    //   "'super' import used in top-level module 'root' (no parent)"
    let err = result.unwrap_err();
    let msg = err.message();
    assert!(
        msg.contains("super"),
        "error message should name 'super', got: {msg}"
    );
    assert!(
        msg.contains("top-level") || msg.contains("no parent"),
        "error message should explain the no-parent condition, got: {msg}"
    );
}
