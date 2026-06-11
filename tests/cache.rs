// cache.rs — Module cache e2e tests (Sprint 64 Wave 2 Batch 1)
//
// Carries forward the language-behaviour assertions from the legacy
// `tests/cache.rs` (~55 tests, 2073 LOC) and merges in the
// `tests/cache_seed.rs` Wave-1 isolation seed. Rust-internal assertions
// (direct `cranelisp_backend::cache::*` API construction, `SymbolTable`
// inspection through `cache::load_meta`, manifest field tampering) are
// quarantined to `tests/legacy/cache.rs` for harvest into
// `cranelisp-backend` unit tests via FIXME 0120.
//
// Discipline:
//   - Each test runs the `cranelisp` binary as a subprocess via the
//     `Cranelisp` builder; cache state is observed through `tmp_exists`,
//     `read_tmp`, exit code, and the `run_again()` cache-hit pattern.
//   - All tests use a fresh `tempfile::TempDir` by construction (the
//     harness's per-builder cwd) — no checked-in path is ever touched.
//   - The binary exit code carries `main`'s i64 return value; cache-hit
//     vs. fresh-build parity is asserted on both exit code AND tmpdir
//     state (manifest/.meta.json/.o presence + mtime preservation on
//     unchanged modules).

#[path = "helpers/mod.rs"]
mod helpers;

use std::fs;
use std::time::{Duration, SystemTime};

use helpers::e2e::Cranelisp;

// =============================================================================
// Helpers
// =============================================================================

/// Build a per-test program: drop one or more files into the cwd. Each entry is
/// `(rel_path, contents)`. Returns the builder ready for `.run("main.cl")`
/// (or whichever entry the test wants).
fn project(files: &[(&str, &str)]) -> Cranelisp {
    let mut c = Cranelisp::new();
    for (path, contents) in files {
        c = c.file(path, contents);
    }
    c
}

/// Read the mtime of a path under the test tmpdir.
fn mtime(out: &helpers::e2e::CrOutput, rel: &str) -> SystemTime {
    let full = out.tmpdir.join(rel);
    fs::metadata(&full)
        .unwrap_or_else(|e| panic!("mtime: stat {} failed: {e}", full.display()))
        .modified()
        .unwrap_or_else(|e| panic!("mtime: modified {} failed: {e}", full.display()))
}

/// Sleep just long enough that subsequent file rewrites would bump mtime.
fn nap_for_mtime() {
    std::thread::sleep(Duration::from_millis(50));
}

// =============================================================================
// Cache directory layout — Phase 1 §2 seed (merged from cache_seed.rs)
// =============================================================================

/// spec: design/backend/module-caching.md §10 (Edge Cases — Prelude caching) —
/// cache lives under project_root's `.cranelisp-cache/` (= the per-test TempDir).
#[test]
fn cache_lives_under_project_root() {
    let out = Cranelisp::new()
        .run("user.cl")
        .with_prelude(helpers::e2e::PreludeVariant::PrimitivesOnly)
        .user("(defn main [] 0)")
        .output()
        .assert_ok();

    assert!(
        out.tmp_exists(".cranelisp-cache"),
        "cache must materialise under project_root (= TempDir); got tmpdir={}, stdout={:?}",
        out.tmpdir.display(),
        out.stdout
    );
}

// =============================================================================
// Single-file sanity & artefact emission
// =============================================================================

// spec: design/backend/module-caching.md §5 — single-file compile with caching works
#[test]
fn cache_single_file_sanity() {
    project(&[("main.cl", "(defn main [] 42)")])
        .run("main.cl")
        .output()
        .assert_exit(42);
}

// spec: design/backend/module-caching.md §5 — .o file generated after cached compile
#[test]
fn cache_object_file_loadable() {
    let out = project(&[(
        "main.cl",
        "(import [primitives [add-i64]])\n(defn double [x] (add-i64 x x))\n(defn main [] (double 21))",
    )])
    .run("main.cl")
    .output()
    .assert_exit(42);

    assert!(out.tmp_exists(".cranelisp-cache/main.meta.json"));
    assert!(out.tmp_exists(".cranelisp-cache/main.o"));
    assert!(out.tmp_exists(".cranelisp-cache/manifest.json"));
    let obj_size = fs::metadata(out.tmpdir.join(".cranelisp-cache/main.o"))
        .unwrap()
        .len();
    assert!(obj_size > 0, ".o file should be non-empty (got {obj_size} bytes)");
}

// =============================================================================
// Cache-hit equivalence
// =============================================================================

// spec: design/backend/module-caching.md §8 — cached module equals fresh compile
#[test]
fn cache_load_fresh_compile_equivalence() {
    let fresh = project(&[(
        "main.cl",
        "(import [primitives [add-i64]])\n(defn double [x] (add-i64 x x))\n(defn main [] (double 21))",
    )])
    .run("main.cl")
    .output()
    .assert_exit(42);

    fresh
        .run_again()
        .run("main.cl")
        .output()
        .assert_exit(42);
}

// spec: design/backend/module-caching.md §8 — install_module_scope shared path
#[test]
fn cache_load_imports_macros_traits_installed() {
    let fresh = project(&[(
        "main.cl",
        "(import [primitives [add-i64]])\n(defn helper [x] (add-i64 x 1))\n(defn main [] (helper 9))",
    )])
    .run("main.cl")
    .output()
    .assert_exit(10);

    fresh
        .run_again()
        .run("main.cl")
        .output()
        .assert_exit(10);
}

// spec: design/backend/module-caching.md §8 — pipeline cache hit second compile
#[test]
fn cache_pipeline_hit_second_compile() {
    let first = project(&[("main.cl", "(defn val [] 77)\n(defn main [] (val))")])
        .run("main.cl")
        .output()
        .assert_exit(77);

    assert!(first.tmp_exists(".cranelisp-cache/main.meta.json"));

    first
        .run_again()
        .run("main.cl")
        .output()
        .assert_exit(77);
}

// spec: design/backend/module-caching.md §8 — pipeline cache miss on source change
#[test]
fn cache_pipeline_miss_on_source_change() {
    let first = project(&[("main.cl", "(defn val [] 100)\n(defn main [] (val))")])
        .run("main.cl")
        .output()
        .assert_exit(100);

    let second = first.run_again().file(
        "main.cl",
        "(defn val [] 123)\n(defn main [] (val))",
    );

    second.run("main.cl").output().assert_exit(123);
}

// spec: design/backend/module-caching.md §3 — pipeline transitive invalidation cascade
// (e2e shape: dep change cascades through the pipeline; observable as the
// dependent producing the new value rather than a stale-cache value.)
#[test]
fn cache_invalidation_transitive_pipeline() {
    let first = project(&[("main.cl", "(defn base [] 10)\n(defn main [] (base))")])
        .run("main.cl")
        .output()
        .assert_exit(10);

    first
        .run_again()
        .file("main.cl", "(defn base [] 20)\n(defn main [] (base))")
        .run("main.cl")
        .output()
        .assert_exit(20);
}

// =============================================================================
// Multi-module cache integration
// =============================================================================

// spec: design/backend/module-caching.md §8 — multi-module cache hit with cross-module call
#[test]
fn cache_multi_module_hit_cross_module_call() {
    let fresh = project(&[
        (
            "main.cl",
            "(import [util [helper]])\n(defn main [] (helper 21))",
        ),
        (
            "util.cl",
            "(import [primitives [add-i64]])\n(defn helper [x] (add-i64 x x))",
        ),
    ])
    .run("main.cl")
    .output()
    .assert_exit(42);

    assert!(fresh.tmp_exists(".cranelisp-cache/manifest.json"));
    assert!(fresh.tmp_exists(".cranelisp-cache/util.meta.json"));
    assert!(fresh.tmp_exists(".cranelisp-cache/util.o"));

    fresh
        .run_again()
        .run("main.cl")
        .output()
        .assert_exit(42);
}

// spec: design/backend/module-caching.md §8 — multi-module cache hit with transitive imports
//
// Regression guard for `--run main.cl` over a project whose entry module
// carries `(mod ...)` declarations: the `--run` driver discovers the entry's
// `(mod ...)` declarations before checking for `main`, then serves the whole
// graph from the disk cache on the second run.
#[test]
fn cache_multi_module_transitive_imports() {
    let fresh = project(&[
        (
            "main.cl",
            "(mod mid)\n(import [main.mid [relay]])\n(defn main [] (relay))",
        ),
        (
            "main/mid.cl",
            "(mod leaf)\n(import [main.mid.leaf [base-val]])\n(defn relay [] (base-val))",
        ),
        ("main/mid/leaf.cl", "(defn base-val [] 77)"),
    ])
    .run("main.cl")
    .output()
    .assert_exit(77);

    assert!(
        fresh.tmp_exists(".cranelisp-cache/main"),
        "submodule cache directory should exist for main/"
    );

    fresh
        .run_again()
        .run("main.cl")
        .output()
        .assert_exit(77);
}

// spec: design/backend/module-caching.md §6 — multi-module cache invalidation on dep change
#[test]
fn cache_multi_module_invalidation_dependency_change() {
    let first = project(&[
        (
            "main.cl",
            "(import [util [helper]])\n(defn main [] (helper 10))",
        ),
        (
            "util.cl",
            "(import [primitives [add-i64]])\n(defn helper [x] (add-i64 x 1))",
        ),
    ])
    .run("main.cl")
    .output()
    .assert_exit(11);

    first
        .run_again()
        .file(
            "util.cl",
            "(import [primitives [add-i64]])\n(defn helper [x] (add-i64 x x))",
        )
        .run("main.cl")
        .output()
        .assert_exit(20);
}

// spec: design/backend/module-caching.md §6 — unchanged dep stays cached (mtime preserved)
#[test]
fn cache_multi_module_unchanged_dep_stays_cached() {
    let first = project(&[
        (
            "main.cl",
            "(import [util [helper]])\n(defn main [] (helper 5))",
        ),
        (
            "util.cl",
            "(import [primitives [add-i64]])\n(defn helper [x] (add-i64 x x))",
        ),
    ])
    .run("main.cl")
    .output()
    .assert_exit(10);

    let mtime1 = mtime(&first, ".cranelisp-cache/util.meta.json");
    nap_for_mtime();

    let second = first
        .run_again()
        .file(
            "main.cl",
            "(import [util [helper]])\n(defn main [] (helper 7))",
        )
        .run("main.cl")
        .output()
        .assert_exit(14);

    let mtime2 = mtime(&second, ".cranelisp-cache/util.meta.json");
    assert_eq!(
        mtime1, mtime2,
        "util's .meta.json must NOT be rewritten when util's source is unchanged"
    );
}

// spec: design/backend/module-caching.md §8 — multi-module with multiple imports from one dep
#[test]
fn cache_multi_module_multiple_imports() {
    let fresh = project(&[
        (
            "main.cl",
            "(import [util [add-one double]])\n(defn main [] (add-one (double 10)))",
        ),
        (
            "util.cl",
            "(import [primitives [add-i64]])\n\
             (defn add-one [x] (add-i64 x 1))\n\
             (defn double [x] (add-i64 x x))",
        ),
    ])
    .run("main.cl")
    .output()
    .assert_exit(21);

    fresh.run_again().run("main.cl").output().assert_exit(21);
}

// spec: design/backend/module-caching.md §8 — main imports from two independent modules
#[test]
fn cache_multi_module_two_deps() {
    let fresh = project(&[
        (
            "main.cl",
            "(import [math [square]])\n\
             (import [constants [base-val]])\n\
             (defn main [] (square (base-val)))",
        ),
        (
            "math.cl",
            "(import [primitives [mul-i64]])\n(defn square [x] (mul-i64 x x))",
        ),
        ("constants.cl", "(defn base-val [] 7)"),
    ])
    .run("main.cl")
    .output()
    .assert_exit(49);

    assert!(fresh.tmp_exists(".cranelisp-cache/math.meta.json"));
    assert!(fresh.tmp_exists(".cranelisp-cache/constants.meta.json"));

    let second = fresh.run_again().run("main.cl").output().assert_exit(49);

    // Change one dep; the other stays cached and main re-runs with new value.
    second
        .run_again()
        .file("constants.cl", "(defn base-val [] 3)")
        .run("main.cl")
        .output()
        .assert_exit(9);
}

// =============================================================================
// Prelude caching
// =============================================================================

// spec: design/backend/module-caching.md §10 — prelude cached on first build
#[test]
fn cache_prelude_modules_cached() {
    let first = project(&[
        ("main.cl", "(defn main [] 42)"),
        ("prelude.cl", "(defn id [x] x)"),
    ])
    .run("main.cl")
    .output()
    .assert_exit(42);

    assert!(first.tmp_exists(".cranelisp-cache/prelude.meta.json"));

    let mtime1 = mtime(&first, ".cranelisp-cache/prelude.meta.json");
    nap_for_mtime();

    let second = first
        .run_again()
        .run("main.cl")
        .output()
        .assert_exit(42);

    let mtime2 = mtime(&second, ".cranelisp-cache/prelude.meta.json");
    assert_eq!(
        mtime1, mtime2,
        "prelude .meta.json must not be rewritten on cache hit"
    );
}

// spec: design/backend/module-caching.md §10 — prelude change invalidates user module
#[test]
fn cache_prelude_change_invalidates_user_module() {
    let first = project(&[
        ("main.cl", "(defn main [] 42)"),
        ("prelude.cl", "(defn id [x] x)"),
    ])
    .run("main.cl")
    .output()
    .assert_exit(42);

    first
        .run_again()
        .file("prelude.cl", "(defn id [x] x)\n(defn const [x y] x)")
        .run("main.cl")
        .output()
        .assert_exit(42);
}

// spec: design/backend/module-caching.md §8 — multi-module with prelude works
#[test]
fn cache_multi_module_with_prelude() {
    let fresh = project(&[
        (
            "main.cl",
            "(import [util [helper]])\n(defn main [] (helper 5))",
        ),
        (
            "util.cl",
            "(import [primitives [add-i64]])\n(defn helper [x] (add-i64 x x))",
        ),
        ("prelude.cl", "(defn id [x] x)"),
    ])
    .run("main.cl")
    .output()
    .assert_exit(10);

    fresh.run_again().run("main.cl").output().assert_exit(10);
}

// =============================================================================
// REPL restart / --link cache reuse
// =============================================================================

// spec: design/backend/module-caching.md §10 — REPL restart cache hit (helper.meta.json mtime preserved)
#[test]
fn cache_repl_restart_cache_hit() {
    let first = project(&[
        (
            "main.cl",
            "(import [helper [add-one]])\n(defn main [] (add-one 41))",
        ),
        (
            "helper.cl",
            "(import [primitives [add-i64]])\n(defn add-one [x] (add-i64 x 1))",
        ),
    ])
    .run("main.cl")
    .output()
    .assert_exit(42);

    assert!(first.tmp_exists(".cranelisp-cache/helper.meta.json"));
    let m1 = mtime(&first, ".cranelisp-cache/helper.meta.json");
    nap_for_mtime();

    let second = first
        .run_again()
        .run("main.cl")
        .output()
        .assert_exit(42);

    let m2 = mtime(&second, ".cranelisp-cache/helper.meta.json");
    assert_eq!(m1, m2, "helper .meta.json must not be rewritten on REPL-restart cache hit");
}

// spec: design/backend/module-caching.md §10 — incremental monomorphisation (cached dep usable)
#[test]
fn cache_repl_incremental_monomorphisation() {
    let first = project(&[
        (
            "main.cl",
            "(import [math [double]])\n(defn main [] (double 21))",
        ),
        (
            "math.cl",
            "(import [primitives [add-i64]])\n(defn double [x] (add-i64 x x))",
        ),
    ])
    .run("main.cl")
    .output()
    .assert_exit(42);

    first
        .run_again()
        .file(
            "main.cl",
            "(import [math [double]])\n(defn main [] (double 10))",
        )
        .run("main.cl")
        .output()
        .assert_exit(20);
}

// spec: design/backend/module-caching.md §11 — quick-build links cached .o files (mtime preserved)
#[test]
fn cache_quick_build_links_cached_objects() {
    let first = project(&[
        (
            "main.cl",
            "(import [helper [double]])\n(defn main [] (double 21))",
        ),
        (
            "helper.cl",
            "(import [primitives [add-i64]])\n(defn double [x] (add-i64 x x))",
        ),
    ])
    .run("main.cl")
    .output()
    .assert_exit(42);

    assert!(first.tmp_exists(".cranelisp-cache/helper.o"));
    let helper_obj_size = fs::metadata(first.tmpdir.join(".cranelisp-cache/helper.o"))
        .unwrap()
        .len();
    assert!(helper_obj_size > 0);

    let m1 = mtime(&first, ".cranelisp-cache/helper.o");
    nap_for_mtime();

    let second = first
        .run_again()
        .run("main.cl")
        .output()
        .assert_exit(42);

    let m2 = mtime(&second, ".cranelisp-cache/helper.o");
    assert_eq!(m1, m2, "helper.o must not be rewritten on cache hit");
}

// spec: design/backend/module-caching.md §11 — cold-start (no cache present) produces correct result
#[test]
fn cache_quick_build_fallback_on_missing_cache() {
    let out = project(&[
        (
            "main.cl",
            "(import [helper [triple]])\n(defn main [] (triple 14))",
        ),
        (
            "helper.cl",
            "(import [primitives [add-i64]])\n(defn triple [x] (add-i64 x (add-i64 x x)))",
        ),
    ])
    .run("main.cl")
    .output()
    .assert_exit(42);

    assert!(out.tmp_exists(".cranelisp-cache/manifest.json"));
    assert!(out.tmp_exists(".cranelisp-cache/helper.meta.json"));
}

// =============================================================================
// Round-trip observable equivalence (G.11 — runtime parity only; structural
// SymbolTable inspection is internal-API, quarantined.)
// =============================================================================

// spec: design/backend/module-caching.md §14 — single-module round-trip
#[test]
fn cache_round_trip_single_module_observable_equivalence() {
    let fresh = project(&[("main.cl", "(defn main [] 99)")])
        .run("main.cl")
        .output()
        .assert_exit(99);

    assert!(fresh.tmp_exists(".cranelisp-cache/main.meta.json"));

    fresh
        .run_again()
        .run("main.cl")
        .output()
        .assert_exit(99);
}

// spec: design/backend/module-caching.md §14 — multi-module round-trip with cross-module call
#[test]
fn cache_round_trip_multi_module_observable_equivalence() {
    let fresh = project(&[
        (
            "main.cl",
            "(import [util [helper]])\n(defn main [] (helper 21))",
        ),
        (
            "util.cl",
            "(import [primitives [add-i64]])\n(defn helper [x] (add-i64 x x))",
        ),
    ])
    .run("main.cl")
    .output()
    .assert_exit(42);

    assert!(fresh.tmp_exists(".cranelisp-cache/util.meta.json"));

    fresh
        .run_again()
        .run("main.cl")
        .output()
        .assert_exit(42);
}

// spec: design/backend/module-caching.md §14.4 — cache invalidation on dep change is observable
#[test]
fn cache_invalidation_on_dep_change_e2e() {
    let first = project(&[
        ("main.cl", "(import [dep [val]])\n(defn main [] (val))"),
        ("dep.cl", "(defn val [] 11)"),
    ])
    .run("main.cl")
    .output()
    .assert_exit(11);

    assert!(first.tmp_exists(".cranelisp-cache/dep.meta.json"));

    first
        .run_again()
        .file("dep.cl", "(defn val [] 22)")
        .run("main.cl")
        .output()
        .assert_exit(22);
}

// =============================================================================
// REPL-mode cache integration — Wave 6 batch 2 Part A carry-forward
//
// Per `tests/plan/wave-6-batch-2-audit.md` §4: the existing
// `cache_repl_restart_cache_hit` and `cache_repl_incremental_monomorphisation`
// cover the *batch-mode* (`--run`) cache restart flow. The legacy
// `tests/sprint23.rs::cache_repl_*` cluster covers the *interactive REPL
// session* (stdin-driven) cache write/load/reset surface — a distinct
// angle preserved per Wave 5.5/5.6 multi-angle rule. `cache_writer_survives_reset`
// is the sole `/reset`-+-cache test in the codebase.
//
// SPRINT 78 WAVE 4 (/qa) NOTE — the three TestStandard-prelude tests below
// (`cache_repl_writes_manifest_on_prelude_load`,
//  `cache_repl_second_session_loads_prelude_from_cache`,
//  `cache_repl_writer_survives_slash_reset`) are currently RED, but NOT on a
// stdlib coupling: they use the QA-owned `PreludeVariant::TestStandard` fixture
// (`tests/fixtures/preludes/test-standard.cl`), which loads NO real workspace
// stdlib, so there is nothing to decouple. They fail at the FIRST session on a
// genuine TRAIT-OPERATOR codegen defect: `(+ N M)` against a prelude that
// declares `Num`/`impl Num Int` raises `undefined function: +`
// ("codegen failed for /"). The SAME defect reds ~12 tests in
// `tests/spec_07_traits.rs` (`operator_plus_int`, `operator_plus_float`,
// `trait_impl_body_uses_operator`, `constrained_polymorphism_int_then_float`,
// …) — those carry the minimal repro. The cache trio are downstream
// casualties: the empty-prelude / plain-fn cache siblings
// (`cache_repl_empty_prelude_session_2_evaluates_literal`,
//  `cache_repl_minimal_plain_fn_prelude_restored_on_session_2`) PASS, proving
// the cache-hit machinery is fine and the failure is the prelude's operator
// dispatch, not the cache. Left failing-not-ignored; resolution is a compiler
// skill (/typecheck or /backend, trait-operator dispatch), NOT a /qa change.
// FIXME 0312 mis-attributed these to the stdlib glob collision.
// =============================================================================

// spec: design/int/repl-lifecycle.md §4.1 — Cache Write After Module Compilation.
//       repl/spec.md §14.7 — Interaction with Object Cache.
//   When the REPL compiles prelude modules at startup (here the
//   TestStandard fixture prelude), `.cranelisp-cache/manifest.json`
//   is materialised in the project_root (= per-test TempDir).
//
// (carry: legacy/sprint23.rs::cache_repl_writes_on_import)
#[test]
fn cache_repl_writes_manifest_on_prelude_load() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(helpers::e2e::PreludeVariant::TestStandard)
        .stdin("(+ 1 2)\n/quit\n")
        .output();

    assert!(
        out.stdout.contains("3"),
        "prelude operator should evaluate: stdout={:?}",
        out.stdout
    );
    assert!(
        out.tmp_exists(".cranelisp-cache/manifest.json"),
        "cache manifest should exist after REPL startup with prelude; tmpdir={}",
        out.tmpdir.display()
    );
}

// spec: design/int/repl-lifecycle.md §4.2 — Cache Load on Startup/Reset.
//       repl/spec.md §14.7 — Interaction with Object Cache.
//   Two REPL sessions in the same project root: first populates cache,
//   second loads prelude from cache. Both produce identical results.
//
//   Note: legacy header documents Sprint 59 Workstream A resolution —
//   the cache-hit arm of `inject_prelude_if_needed` now calls
//   `register_imports` on the user-module check state with an
//   `ImportNames::Glob` spec for `prelude`, matching the fresh-compile
//   arm. This test guards that resolution.
//
// (carry: legacy/sprint23.rs::cache_repl_loads_on_startup)
#[test]
fn cache_repl_second_session_loads_prelude_from_cache() {
    let first = Cranelisp::new()
        .repl()
        .with_prelude(helpers::e2e::PreludeVariant::TestStandard)
        .stdin("(+ 40 2)\n/quit\n")
        .output();

    assert!(
        first.stdout.contains("42"),
        "first session should evaluate via prelude: stdout={:?}",
        first.stdout
    );
    assert!(
        first.tmp_exists(".cranelisp-cache/manifest.json"),
        "cache must materialise after first session"
    );

    // Second session — same TempDir, prelude from cache.
    let second = first
        .run_again()
        .repl()
        .with_prelude(helpers::e2e::PreludeVariant::TestStandard)
        .stdin("(+ 40 2)\n/quit\n")
        .output();

    assert!(
        second.stdout.contains("42"),
        "second session (cache loaded) should also produce 42: stdout={:?}",
        second.stdout
    );
}

// spec: design/int/repl-lifecycle.md §2.3 — Prelude Reload After Reset.
//       design/int/repl-lifecycle.md §4.2 — Cache Load on Startup/Reset.
//   After `/reset`, the prelude reload still produces working state and
//   the cache survives across the reset. This is the ONLY `/reset`+cache
//   integration test in the suite.
//
// (carry: legacy/sprint23.rs::cache_writer_survives_reset)
#[test]
fn cache_repl_writer_survives_slash_reset() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(helpers::e2e::PreludeVariant::TestStandard)
        .stdin("(+ 3 4)\n/reset\n(+ 5 6)\n/quit\n")
        .output();

    assert!(
        out.stdout.contains("7"),
        "before /reset, (+ 3 4) should produce 7: stdout={:?}",
        out.stdout
    );
    assert!(
        out.stdout.contains("11"),
        "after /reset, (+ 5 6) should produce 11 (prelude reloaded): stdout={:?}",
        out.stdout
    );
    assert!(
        out.tmp_exists(".cranelisp-cache/manifest.json"),
        "cache manifest must survive /reset"
    );
}

// =============================================================================
// Sprint 59 Workstream A — cache-hit prelude-restoration regression guards.
//
// Sibling tests to `cache_repl_second_session_loads_prelude_from_cache` (which
// uses TestStandard prelude — operators + traits + ADTs). These two reductions
// partition the discrimination axis the original Sprint 59 bug investigation
// needed:
//
//   - Plain prelude (single defn, no operators / traits / impls): if session 2
//     fails to call it, the bug is universal across binding shapes.
//   - Empty prelude (no symbols at all): exercises only the cache-hit
//     module-load pathway. If session 2 fails on a literal, the bug is at the
//     module level, not the symbol-rebinding level.
//
// Carried from `tests/legacy/sprint59_cache_repro.rs` per Wave 6 batch 3 audit
// (tests/plan/wave-6-batch-3-audit.md). Headed by FIXME 0145.
// =============================================================================

// spec: design/int/repl-lifecycle.md §4.2 — Cache Load on Startup/Reset.
//       repl/spec.md §15.2 — session-persistence cache-hit symbol restoration.
//   Reduction A: smallest possible prelude — single plain `(defn f [] 42)`.
//   No traits, no impls, no operators. If session 2 cannot call `f`,
//   cache-hit prelude restoration is broken for EVERY binding type — not
//   just operator/trait machinery. Per the Wave 6 batch 3 audit
//   (tests/plan/wave-6-batch-3-audit.md).
//
// REGRESSION-GUARD: Sprint 59 Workstream A. The legacy test header documents
//   `design/int/cache-prelude-restoration-repro.md` as the diagnosis anchor.
//
// (carry: legacy/sprint59_cache_repro.rs::s59_cache_hit_plain_prelude_fn_not_restored)
#[test]
fn cache_repl_minimal_plain_fn_prelude_restored_on_session_2() {
    // Drop a single-defn prelude under a per-test lib dir; route CRANELISP_LIB
    // there so the binary auto-discovers it.
    let first = Cranelisp::new()
        .repl()
        .file("lib/prelude.cl", "(defn f [] 42)\n")
        .lib_dir("lib")
        .stdin("(f)\n/quit\n")
        .output();

    assert!(
        first.stdout.contains("42"),
        "session 1 should print 42 (fresh compile): stdout={:?}",
        first.stdout
    );
    assert!(
        first.tmp_exists(".cranelisp-cache/manifest.json"),
        "session 1 should populate cache manifest for a prelude with at least one export"
    );

    // Session 2 — same TempDir, prelude resolves via cache hit.
    let second = first
        .run_again()
        .repl()
        .lib_dir("lib")
        .stdin("(f)\n/quit\n")
        .output();

    assert!(
        second.stdout.contains("42"),
        "session 2 (cache hit) should also print 42; stdout={:?} stderr={:?}",
        second.stdout,
        second.stderr
    );
}

// spec: design/int/repl-lifecycle.md §4.2 — Cache Load on Startup/Reset.
//       repl/spec.md §15.2 — empty-prelude pathway (negative control).
//   Reduction B: empty prelude — no bindings to rebind. Exercises only the
//   cache-hit module-load pathway. If this fails, the bug is at the
//   module-load level (not symbol rebinding). Negative-control rung.
//
// REGRESSION-GUARD: Sprint 59 Workstream A — discriminator probe.
//
// (carry: legacy/sprint59_cache_repro.rs::s59_cache_hit_empty_prelude_basic_eval_works)
#[test]
fn cache_repl_empty_prelude_session_2_evaluates_literal() {
    let first = Cranelisp::new()
        .repl()
        .file("lib/prelude.cl", ";; empty\n")
        .lib_dir("lib")
        .stdin("42\n/quit\n")
        .output();

    assert!(
        first.stdout.contains("42"),
        "session 1 should print 42: stdout={:?}",
        first.stdout
    );

    // Session 2 — same TempDir, empty prelude reloaded from cache.
    let second = first
        .run_again()
        .repl()
        .lib_dir("lib")
        .stdin("42\n/quit\n")
        .output();

    assert!(
        second.stdout.contains("42"),
        "session 2 with empty prelude should also print 42; stdout={:?} stderr={:?}",
        second.stdout,
        second.stderr
    );
}

// =============================================================================
// Sprint 60 Workstream C — `.meta.json` build_id field
// =============================================================================
//
// Three regression guards covering the user-surface invariant of the
// build-id cache invalidation extension. Unit-tier coverage for the
// serialise/deserialise path lives in
// `crates/cranelisp-backend/src/cache/serialize.rs`
// (`build_id_round_trip_succeeds`, `stale_build_id_produces_build_id_mismatch`,
// `missing_build_id_field_routes_cache_stale`); these e2e tests prove
// the user-surface invariant fires through the binary subprocess.
// Carry from Wave 6 batch 4 audit (tests/plan/wave-6-batch-4-audit.md).

/// Trivial single-file program used by the build_id tests below. `main`
/// returns 0 (spec §12.6) so `assert_ok()` is the right assertion.
const BUILD_ID_SRC: &str = "(import [primitives [add-i64]])\n(defn double [x] (add-i64 x x))\n(defn main [] (double 0))";

/// Extract the `build_id` string from the raw `.meta.json` text. Returns
/// `None` if the field is absent. Narrow parser — looks for
/// `"build_id":"..."` as a top-level field; avoids a serde_json dep.
fn extract_build_id(meta_text: &str) -> Option<String> {
    let needle = "\"build_id\":";
    let idx = meta_text.find(needle)?;
    let after = &meta_text[idx + needle.len()..];
    let after = after.trim_start();
    let after = after.strip_prefix('"')?;
    let end = after.find('"')?;
    Some(after[..end].to_string())
}

/// Rewrite the `build_id` field's value in raw JSON text. Panics if the
/// field is absent — caller must ensure presence first.
fn set_build_id(meta_text: &str, new_value: &str) -> String {
    let needle = "\"build_id\":";
    let idx = meta_text
        .find(needle)
        .expect("meta text must contain build_id field for set_build_id");
    let before = &meta_text[..idx + needle.len()];
    let after = &meta_text[idx + needle.len()..];
    let after_trim = after.trim_start();
    assert!(
        after_trim.starts_with('"'),
        "build_id value must be a JSON string; got: {after:.60}…"
    );
    let val_start = after.len() - after_trim.len() + 1;
    let rest = &after[val_start..];
    let end = rest
        .find('"')
        .expect("unterminated build_id value in meta.json");
    let suffix = &rest[end..]; // starts with closing `"`
    format!("{before}\"{new_value}{suffix}")
}

/// Remove the `build_id` field (and trailing comma if present) for the
/// pre-Sprint-60 shape simulation.
fn remove_build_id(meta_text: &str) -> String {
    let needle = "\"build_id\":";
    let idx = meta_text
        .find(needle)
        .expect("meta text must contain build_id field for remove_build_id");
    let after = &meta_text[idx + needle.len()..];
    let after_trim_offset = after.len() - after.trim_start().len();
    let val = &after[after_trim_offset + 1..]; // skip opening quote
    let end_quote = val
        .find('"')
        .expect("unterminated build_id value in meta.json");
    let mut end_idx = idx + needle.len() + after_trim_offset + 1 + end_quote + 1;
    let tail = &meta_text[end_idx..];
    if tail.trim_start().starts_with(',') {
        let ws = tail.len() - tail.trim_start().len();
        end_idx += ws + 1 /* the comma */;
        let after_comma = &meta_text[end_idx..];
        let ws2 = after_comma.len() - after_comma.trim_start().len();
        end_idx += ws2;
    }
    format!("{}{}", &meta_text[..idx], &meta_text[end_idx..])
}

// spec: design/backend/module-caching.md §4 — Serialization Format.
//   First compile populates `.meta.json` with a non-empty build_id, and
//   schema_version remains co-present (additive, not substitutive — Sprint
//   60 Architecture Review Condition 3).
//
// REGRESSION-GUARD: Sprint 60 Workstream C — write-side e2e wrapper
//   around unit `build_id_round_trip_succeeds` in
//   crates/cranelisp-backend/src/cache/serialize.rs.
//
// (carry: legacy/sprint60_cache_build_marker.rs::cache_meta_carries_build_id_after_first_compile)
#[test]
fn cache_meta_carries_build_id_after_first_compile() {
    let out = Cranelisp::new()
        .run("main.cl")
        .file("main.cl", BUILD_ID_SRC)
        .output()
        .assert_ok();

    let meta_path = out.tmpdir.join(".cranelisp-cache").join("main.meta.json");
    assert!(
        meta_path.exists(),
        "main.meta.json must be written under .cranelisp-cache/"
    );
    let text = fs::read_to_string(&meta_path).expect("read main.meta.json");
    let build_id = extract_build_id(&text).unwrap_or_else(|| {
        panic!("meta.json must carry a build_id field; got:\n{text}")
    });
    assert!(
        !build_id.is_empty(),
        "build_id must be non-empty; meta=\n{text}"
    );
    // Negative guard: schema_version must remain alongside build_id.
    // Additive (Sprint 60 Architecture Review Condition 3), not substitutive.
    assert!(
        text.contains("\"schema_version\":"),
        "schema_version must remain alongside build_id; meta=\n{text}"
    );
}

// spec: design/backend/module-caching.md §6 — Cache Invalidation Strategy.
//   Tampering with build_id forces a fresh build on the next compile:
//   second compile MUST succeed, and meta.build_id MUST be re-stamped to
//   the original (proving the cache miss + re-emit path ran rather than
//   silently honouring the stale meta).
//
// REGRESSION-GUARD: Sprint 60 Workstream C — invalidation-side e2e
//   wrapper around unit `stale_build_id_produces_build_id_mismatch`.
//
// (carry: legacy/sprint60_cache_build_marker.rs::cache_meta_with_stale_build_id_triggers_recompile)
#[test]
fn cache_meta_with_stale_build_id_triggers_recompile() {
    let first = Cranelisp::new()
        .run("main.cl")
        .file("main.cl", BUILD_ID_SRC)
        .output()
        .assert_ok();

    let meta_path = first.tmpdir.join(".cranelisp-cache").join("main.meta.json");
    let original_text = fs::read_to_string(&meta_path).expect("read main.meta.json");
    let original_build_id =
        extract_build_id(&original_text).expect("first compile wrote build_id");

    // Patch meta.build_id to a synthetic stale value.
    let patched_text = set_build_id(&original_text, "0.0.0+stale-synthetic");
    assert_eq!(
        extract_build_id(&patched_text).as_deref(),
        Some("0.0.0+stale-synthetic"),
        "patch must land before second compile"
    );
    fs::write(&meta_path, &patched_text).expect("write patched meta");

    // Second compile in the same TempDir — cache must miss and re-emit.
    let second = first
        .run_again()
        .run("main.cl")
        .output()
        .assert_ok();

    let after_path = second.tmpdir.join(".cranelisp-cache").join("main.meta.json");
    let after_text = fs::read_to_string(&after_path).expect("read meta after rebuild");
    let rewritten_build_id =
        extract_build_id(&after_text).expect("rebuild must restore build_id");
    // Negative: the stale sentinel MUST NOT survive — its survival would
    // mean the cache honoured the patched meta (i.e. invalidation didn't fire).
    assert_ne!(
        rewritten_build_id, "0.0.0+stale-synthetic",
        "stale build_id survived — cache did not invalidate on build_id mismatch"
    );
    assert_eq!(
        rewritten_build_id, original_build_id,
        "rebuild must stamp the current build_id (same as first compile)"
    );
}

// spec: design/backend/module-caching.md §6 — pre-Sprint-60 `.meta.json`
//   shape (no `build_id` field at all) MUST be treated as stale. Simulated
//   by removing the field from a freshly-written meta.
//
// REGRESSION-GUARD: Sprint 60 Workstream C — schema-evolution e2e wrapper
//   around unit `missing_build_id_field_routes_cache_stale`.
//
// (carry: legacy/sprint60_cache_build_marker.rs::cache_meta_without_build_id_field_triggers_recompile)
#[test]
fn cache_meta_without_build_id_field_triggers_recompile() {
    let first = Cranelisp::new()
        .run("main.cl")
        .file("main.cl", BUILD_ID_SRC)
        .output()
        .assert_ok();

    let meta_path = first.tmpdir.join(".cranelisp-cache").join("main.meta.json");
    let original_text = fs::read_to_string(&meta_path).expect("read main.meta.json");
    let original_build_id =
        extract_build_id(&original_text).expect("first compile wrote build_id");

    // Strip the build_id field entirely — pre-Sprint-60 cache shape.
    let patched_text = remove_build_id(&original_text);
    fs::write(&meta_path, &patched_text).expect("write patched meta");
    let verify = fs::read_to_string(&meta_path).expect("re-read patched meta");
    assert!(
        extract_build_id(&verify).is_none(),
        "patched meta must have no build_id field; got:\n{verify}"
    );

    // Second compile — cache must miss and rebuild.
    let second = first
        .run_again()
        .run("main.cl")
        .output()
        .assert_ok();

    let after_path = second.tmpdir.join(".cranelisp-cache").join("main.meta.json");
    let after_text = fs::read_to_string(&after_path).expect("read meta after rebuild");
    let restored = extract_build_id(&after_text).expect("rebuild must restore build_id");
    assert_eq!(
        restored, original_build_id,
        "rebuild must stamp the current build_id on pre-Sprint-60-shape caches"
    );
}
