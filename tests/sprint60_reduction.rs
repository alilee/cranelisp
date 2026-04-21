//! Sprint 60 reduction tests — cache-reuse crashes, reduced from the
//! A-cluster findings documented in
//! `design/backend/defects-456-reduction.md §"Sprint 60 A.2/A.3b audit findings"`
//! and `design/backend/jit-object-convergence.md §1.1 convergence invariant`.
//!
//! Sprint 59's A.3b audit noted (but did NOT commit) that cache-reuse crashes
//! deterministically on a simple `(make-grid)` program — distinct from the
//! intermittent fresh-cache SIGTRAP that dominated Wave 1/Wave 2's focus.
//! This file commits that repro plus a chain of reductions proving the
//! crash has NOTHING to do with heap, RC, ADT, or tail recursion — the
//! minimal crashing shape is 5 LOC spanning a cross-module wrapper that
//! calls a same-module helper returning an `Int` literal.
//!
//! All reductions are subprocess tests driving `--run`. Each test:
//!   1. Writes grid.cl + program.cl into a fresh tempdir.
//!   2. Runs `cranelisp --run program.cl` once — this fresh-cache run
//!      MUST succeed (populates `<tempdir>/.cranelisp-cache`).
//!   3. Runs `--run program.cl` a SECOND time in the same tempdir — cache-hit.
//!   4. Asserts the second run did NOT signal-crash.
//!
//! Exit codes observed for the failing reductions:
//!   - 0   = clean exit (test PASSES).
//!   - 139 = SIGSEGV (test FAILS; this is the reduced defect).
//!   - 133 = SIGTRAP (test FAILS).
//!   - None = killed by signal (test FAILS).
//!
//! The minimal crashing source is ~5 LOC of Cranelisp. Every reduction
//! below is a deterministic (3/3 or 10/10) crash in isolation.

use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn binary_path() -> PathBuf {
    project_root().join("target").join("debug").join("cranelisp")
}

fn stdlib_dir() -> PathBuf {
    project_root().join("stdlib")
}

fn platform_dir() -> PathBuf {
    project_root().join("target").join("debug")
}

fn run_once(cwd: &std::path::Path) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} -- run `cargo build` first"
    );
    Command::new(&binary)
        .current_dir(cwd)
        .args(["--run", "program.cl"])
        .env("CRANELISP_LIB", stdlib_dir())
        .env("CRANELISP_PLATFORM_PATH", platform_dir())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to invoke binary")
}

fn stdout_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}
fn stderr_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

/// Write two files into a fresh tempdir, run `--run program.cl` once to
/// populate the cache, then run again and return the SECOND invocation's
/// output. The tempdir handle is kept alive so that both invocations see
/// the same `.cranelisp-cache`.
struct CacheReuse {
    _td: tempfile::TempDir,
    first: Output,
    second: Output,
}

fn two_file_cache_reuse(grid_body: &str, program_body: &str) -> CacheReuse {
    let td = tempfile::tempdir().unwrap();
    std::fs::write(td.path().join("grid.cl"), grid_body).unwrap();
    std::fs::write(td.path().join("program.cl"), program_body).unwrap();

    let first = run_once(td.path());
    let second = run_once(td.path());

    CacheReuse { _td: td, first, second }
}

fn single_file_cache_reuse(program_body: &str) -> CacheReuse {
    let td = tempfile::tempdir().unwrap();
    std::fs::write(td.path().join("program.cl"), program_body).unwrap();

    let first = run_once(td.path());
    let second = run_once(td.path());

    CacheReuse { _td: td, first, second }
}

fn assert_no_signal_crash(label: &str, o: &Output) {
    let exit = o.status.code();
    let signal_crash = matches!(exit, Some(139) | Some(133)) || exit.is_none();
    if signal_crash {
        panic!(
            "{label}: child process crashed with exit={exit:?} \
             (139=SIGSEGV, 133=SIGTRAP, None=killed by signal). \
             This is the reduced reproduction of the underlying defect.\n\
             --- stdout ---\n{}\n--- stderr ---\n{}",
            stdout_str(o),
            stderr_str(o),
        );
    }
}

/// The first (fresh-cache) run must NOT signal-crash — we require the cache
/// to be populated. It need not exit 0: `main` may return a non-zero Int
/// value which becomes the exit code. A *signal* crash on the first run
/// means the test is measuring the wrong thing (a fresh-build crash, not
/// a cache-reuse crash) and must be declared explicitly.
fn assert_first_not_signal_crashed(label: &str, o: &Output) {
    let exit = o.status.code();
    let signal_crash = matches!(exit, Some(139) | Some(133)) || exit.is_none();
    if signal_crash {
        panic!(
            "{label}: first (fresh-cache) run signal-crashed (exit={exit:?}). \
             The test cannot measure cache-reuse behaviour if the fresh-build path \
             itself crashes. If this is the intended observation, use a \
             fresh-build test instead.\n--- stdout ---\n{}\n--- stderr ---\n{}",
            stdout_str(o),
            stderr_str(o),
        );
    }
}

// =============================================================================
// Step 1 — commit A.3b's uncommitted finding: cache-reuse + `(make-grid)`.
// =============================================================================
//
// The exemplar-shaped reduction: a Cell ADT, a Grid wrapper, a recursive
// build-helper. This is where /backend's A.3b audit observed the crash.

const GRID_EXEMPLAR_SHAPED: &str = r#"(import [primitives [*]])

(deftype Cell
  (Given [:Int value])
  (Solved [:Int value])
  (Candidates [:Int bitmask]))

(deftype Grid [cells])

(defn build-helper [v i]
  (if (eq-i64 i 9) v
    (build-helper (vec-push v (Given 1)) (add-i64 i 1))))

(defn make-grid [] (Grid (build-helper [] 0)))
"#;

const PROGRAM_CALLS_MAKE_GRID: &str = r#"(import [grid [make-grid]])
(defn main [] (let [g (make-grid)] 0))
"#;

// FIXME(/backend) — S60 Step 1: commits A.3b's uncommitted finding. First
// run compiles + caches. Second run crashes on cache-hit load with SIGSEGV.
// The exemplar-shaped baseline before reduction.
//
// When FIXED: restores the JIT/object convergence invariant
// (design/backend/jit-object-convergence.md §1.1) for the path that
// populates `ModuleEntry::Def.code` on cache-hit.
#[test]
fn s60_cache_reuse_exemplar_shaped_no_crash() {
    let r = two_file_cache_reuse(GRID_EXEMPLAR_SHAPED, PROGRAM_CALLS_MAKE_GRID);
    assert_first_not_signal_crashed("s60_cache_reuse_exemplar_shaped", &r.first);
    assert_no_signal_crash("s60_cache_reuse_exemplar_shaped", &r.second);
}

// =============================================================================
// Step 2 — aggressive reductions. Each test removes one feature from the
// baseline above. Failing tests are still-crashing reductions (committed
// regression guards). The PASSING controls after them pin features whose
// ABSENCE makes the crash disappear.
//
// Reduction chain: Cell ADT → Grid wrapper → heap/Vec → recursion →
// cross-module wrapper → helper-with-args.
// =============================================================================

// Step 2.1 — remove the Cell ADT. Push raw Ints into the Vec.
// Load-bearing finding: Cell multi-variant ADT not required. Crashes same.
const GRID_NO_CELL_ADT: &str = r#"(import [primitives [*]])

(deftype Grid [cells])

(defn build-helper [v i]
  (if (eq-i64 i 9) v
    (build-helper (vec-push v i) (add-i64 i 1))))

(defn make-grid [] (Grid (build-helper [] 0)))
"#;

// FIXME(/backend) — S60 reduction 2.1. Cell ADT not load-bearing.
#[test]
fn s60_cache_reuse_no_cell_adt_no_crash() {
    let r = two_file_cache_reuse(GRID_NO_CELL_ADT, PROGRAM_CALLS_MAKE_GRID);
    assert_first_not_signal_crashed("s60_cache_reuse_no_cell_adt", &r.first);
    assert_no_signal_crash("s60_cache_reuse_no_cell_adt", &r.second);
}

// Step 2.2 — remove the Grid wrapper ADT. `make-grid` returns a Vec directly.
// Load-bearing finding: Grid wrapper not required.
const GRID_NO_WRAPPER_ADT: &str = r#"(import [primitives [*]])

(defn build-helper [v i]
  (if (eq-i64 i 9) v
    (build-helper (vec-push v i) (add-i64 i 1))))

(defn make-grid [] (build-helper [] 0))
"#;

// FIXME(/backend) — S60 reduction 2.2. Grid wrapper ADT not load-bearing.
#[test]
fn s60_cache_reuse_no_wrapper_adt_no_crash() {
    let r = two_file_cache_reuse(GRID_NO_WRAPPER_ADT, PROGRAM_CALLS_MAKE_GRID);
    assert_first_not_signal_crashed("s60_cache_reuse_no_wrapper_adt", &r.first);
    assert_no_signal_crash("s60_cache_reuse_no_wrapper_adt", &r.second);
}

// Step 2.3 — helper is NOT tail-recursive. Just a one-shot vec-push.
// Load-bearing finding: tail recursion not required. Crashes same.
const GRID_NON_RECURSIVE: &str = r#"(import [primitives [*]])

(defn build-helper [v i] (vec-push v i))

(defn make-grid [] (build-helper [] 0))
"#;

// FIXME(/backend) — S60 reduction 2.3. Self-recursion not load-bearing.
#[test]
fn s60_cache_reuse_non_recursive_helper_no_crash() {
    let r = two_file_cache_reuse(GRID_NON_RECURSIVE, PROGRAM_CALLS_MAKE_GRID);
    assert_first_not_signal_crashed("s60_cache_reuse_non_recursive_helper", &r.first);
    assert_no_signal_crash("s60_cache_reuse_non_recursive_helper", &r.second);
}

// Step 2.4 — helper takes NO args and is NOT recursive. Pushes a literal.
// Load-bearing finding: helper arity/args not required.
const GRID_NULLARY_VEC_HELPER: &str = r#"(import [primitives [*]])

(defn build-helper [] (vec-push [] 0))

(defn make-grid [] (build-helper))
"#;

// FIXME(/backend) — S60 reduction 2.4. Helper arity not load-bearing.
#[test]
fn s60_cache_reuse_nullary_helper_no_crash() {
    let r = two_file_cache_reuse(GRID_NULLARY_VEC_HELPER, PROGRAM_CALLS_MAKE_GRID);
    assert_first_not_signal_crashed("s60_cache_reuse_nullary_helper", &r.first);
    assert_no_signal_crash("s60_cache_reuse_nullary_helper", &r.second);
}

// Step 2.5 — helper returns an empty Vec `[]` (no `vec-push` at all).
// Load-bearing finding: `vec-push` not required; any heap value suffices.
const GRID_EMPTY_VEC_HELPER: &str = r#"(import [primitives [*]])

(defn build-helper [] [])

(defn make-grid [] (build-helper))
"#;

// FIXME(/backend) — S60 reduction 2.5. `vec-push` not load-bearing.
#[test]
fn s60_cache_reuse_empty_vec_helper_no_crash() {
    let r = two_file_cache_reuse(GRID_EMPTY_VEC_HELPER, PROGRAM_CALLS_MAKE_GRID);
    assert_first_not_signal_crashed("s60_cache_reuse_empty_vec_helper", &r.first);
    assert_no_signal_crash("s60_cache_reuse_empty_vec_helper", &r.second);
}

// Step 2.6 — helper returns an Int literal. No heap involved at all.
// Load-bearing finding: heap allocation NOT required. The crash is not RC.
const GRID_INT_HELPER: &str = r#"(import [primitives [*]])

(defn build-helper [] 42)

(defn make-grid [] (build-helper))
"#;

// FIXME(/backend) — S60 reduction 2.6. NO HEAP. This rules out RC/drop-glue
// entirely. The crash is purely about cache-hit handling of an imported
// wrapper that calls a same-module helper, regardless of value type.
#[test]
fn s60_cache_reuse_int_helper_no_heap_no_crash() {
    let r = two_file_cache_reuse(GRID_INT_HELPER, PROGRAM_CALLS_MAKE_GRID);
    assert_first_not_signal_crashed("s60_cache_reuse_int_helper_no_heap", &r.first);
    assert_no_signal_crash("s60_cache_reuse_int_helper_no_heap", &r.second);
}

// Step 2.7 — MINIMAL SHAPE.
// Drop the `let` binding. Main body is just `(make-grid)` — the return
// value becomes main's return.
// Load-bearing finding: `let` binding not required.
//
// Total source: 5 LOC across two files.
//   grid.cl:
//     (import [primitives [*]])
//     (defn build-helper [] 42)
//     (defn make-grid [] (build-helper))
//   program.cl:
//     (import [grid [make-grid]])
//     (defn main [] (make-grid))
//
// First run compiles both modules, caches grid.cl + program.cl, and runs.
// Second run cache-loads both modules. Crash: SIGSEGV deterministically.
const PROGRAM_NO_LET: &str = r#"(import [grid [make-grid]])
(defn main [] (make-grid))
"#;

// FIXME(/backend) — S60 MINIMAL — cache-hit path segfaults on a two-file,
// no-heap, no-recursion, no-`let` program. The SOLE load-bearing shape:
//   1. Module `grid` defines `build-helper` (no args, returns literal).
//   2. Module `grid` defines `make-grid` that calls `build-helper`.
//   3. Module `program` imports `make-grid` and calls it from `main`.
//   4. Cache-hit second run (first run populated `.cranelisp-cache`).
//
// This is an invariant-layer bug: the JIT/object convergence invariant
// states that fresh-build and cache-hit paths must produce semantically
// identical code (design/backend/jit-object-convergence.md §1.1). They
// manifestly do not — fresh-build runs cleanly; cache-hit segfaults.
//
// Hypothesis (pending CLIF inspection): on cache-hit, `make-grid`'s call
// to `build-helper` is dispatched through a GOT slot for `grid.build-helper`
// that is NULL or stale. Reading a NULL function pointer and jumping to
// it produces a raw SIGSEGV with no stderr output — consistent with the
// observed signature. The `inline_jit_codegen_for_names` fresh-build path
// populates the slot before `Code::Jit` is visible; the
// `load_cached_module_via_linker` cache-hit path may have an ordering gap
// between slot store and caller visibility — or may write the slot with
// the linker-loaded pointer for cross-module imports but miss intra-module
// call targets that the fresh-build path dispatched through call_indirect
// via the same GOT slot.
//
// (Alternative hypothesis: cache-hit fails to register `grid.build-helper`
// as a JIT symbol at all because `load_cached_module_via_linker` iterates
// `cached.symbol_table().all_symbols()` but cross-module GOT population
// only looks at the IMPORTED subset — intra-module calls within `grid`
// land on an unpopulated slot.)
//
// Root cause is in `src/worker.rs::load_cached_module_via_linker` vicinity,
// intersecting with the convergence invariant breach at §4.3 of the design
// doc (`restore_cached_module`'s wholesale-swap of `symbol_tables[M].got`).
#[test]
fn s60_cache_reuse_minimal_5_loc_no_crash() {
    let r = two_file_cache_reuse(GRID_INT_HELPER, PROGRAM_NO_LET);
    assert_first_not_signal_crashed("s60_cache_reuse_minimal_5_loc", &r.first);
    assert_no_signal_crash("s60_cache_reuse_minimal_5_loc", &r.second);
}

// =============================================================================
// Step 3 — negative controls. These PASS on cache-hit. Each pins one
// feature whose absence removes the crash.
// =============================================================================

// Control A — no cross-module; single-file program. Same shape otherwise.
// Proves: cross-module import is load-bearing.
const SINGLE_FILE_WITH_HELPER: &str = r#"(import [primitives [*]])
(defn build-helper [] 42)
(defn make-grid [] (build-helper))
(defn main [] (make-grid))
"#;

#[test]
fn s60_control_single_file_no_crash() {
    let r = single_file_cache_reuse(SINGLE_FILE_WITH_HELPER);
    assert_first_not_signal_crashed("s60_control_single_file", &r.first);
    assert_no_signal_crash("s60_control_single_file", &r.second);
}

// Control B — no intra-module call in grid. `make-grid` returns a literal
// directly (no helper). Program imports and calls it.
// Proves: the INTRA-MODULE call (`make-grid` calls `build-helper` in same
// module) is what the cache-hit path mishandles, not cross-module dispatch
// generally.
const GRID_TRIVIAL_WRAPPER: &str = r#"(import [primitives [*]])
(defn make-grid [] 42)
"#;

#[test]
fn s60_control_no_intra_module_call_no_crash() {
    let r = two_file_cache_reuse(GRID_TRIVIAL_WRAPPER, PROGRAM_NO_LET);
    assert_first_not_signal_crashed("s60_control_no_intra_module_call", &r.first);
    assert_no_signal_crash("s60_control_no_intra_module_call", &r.second);
}

// Control C — direct call to the helper; no wrapper layer in grid. Program
// imports `build-helper` directly.
// Proves: the IMPORTED wrapper that calls a same-module helper is the
// load-bearing shape, not same-module calls in any imported module.
const GRID_HELPER_ONLY: &str = r#"(import [primitives [*]])
(defn build-helper [] 42)
"#;

const PROGRAM_CALLS_HELPER_DIRECTLY: &str = r#"(import [grid [build-helper]])
(defn main [] (build-helper))
"#;

#[test]
fn s60_control_direct_helper_call_no_crash() {
    let r = two_file_cache_reuse(GRID_HELPER_ONLY, PROGRAM_CALLS_HELPER_DIRECTLY);
    assert_first_not_signal_crashed("s60_control_direct_helper_call", &r.first);
    assert_no_signal_crash("s60_control_direct_helper_call", &r.second);
}
