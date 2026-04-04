// Exemplar-style integration tests: multi-module batch compilation.
//
// These tests validate multi-module batch compilation via compile_module_graph.
// They exercise cross-module imports, inline test submodules, and prelude macro
// availability in batch files.
//
// NOTE: Full exemplar module compilation (grid.cl, solver.cl, etc.) is blocked
// by two issues:
// 1. `:Vec` type annotation resolution — Vec is a compiler builtin not
//    registered as a user-visible type for annotations.
// 2. Prelude trait operator resolution — `load_prelude` injects `(import
//    [prelude [*]])` into the "user" module, but batch entry files get a
//    module path derived from their filename (e.g. "main"), not "user".
//    Macros work (global in expander), but trait methods don't resolve.

mod helpers;

use std::path::Path;

fn stdlib_dir() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("stdlib")
}

// =============================================================================
// Multi-module batch compilation
// =============================================================================

// spec: spec/08-modules.md §8.2 — const macro works in batch files via prelude
#[test]
fn exemplar_batch_const_macro() {
    let dir = tempfile::tempdir().unwrap();
    let entry = dir.path().join("main.cl");
    std::fs::write(
        &entry,
        "(const SIZE 9)\n(defn main [] SIZE)",
    )
    .unwrap();
    let (value, _ty) = helpers::batch_run_file(&entry, &[stdlib_dir()]).unwrap();
    assert_eq!(value, 9);
}

// spec: spec/08-modules.md §8.10.1 — cross-module import resolves correctly
#[test]
fn exemplar_batch_cross_module_import() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(
        dir.path().join("util.cl"),
        "(defn helper [] 42)",
    )
    .unwrap();
    let entry = dir.path().join("main.cl");
    std::fs::write(
        &entry,
        "(import [util [helper]])\n(defn main [] (helper))",
    )
    .unwrap();
    let (value, _ty) = helpers::batch_run_file(&entry, &[stdlib_dir()]).unwrap();
    assert_eq!(value, 42);
}

// spec: spec/08-modules.md §8.10.1 — cross-module with ADT types
#[test]
fn exemplar_batch_cross_module_adt() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(
        dir.path().join("types.cl"),
        "(deftype Color Red Green Blue)\n(defn color-val [:Color c] (match c [Red 1 Green 2 Blue 3]))",
    )
    .unwrap();
    let entry = dir.path().join("main.cl");
    std::fs::write(
        &entry,
        "(import [types [Color Red Green Blue color-val]])\n(defn main [] (add-i64 (color-val Red) (color-val Blue)))",
    )
    .unwrap();
    let (value, _ty) = helpers::batch_run_file(&entry, &[stdlib_dir()]).unwrap();
    assert_eq!(value, 4); // 1 + 3
}
