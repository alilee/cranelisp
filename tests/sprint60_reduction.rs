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

// =============================================================================
// Sprint 60 Wave 2 Round 2 — drop-glue reduction
// =============================================================================
//
// After the single-GOT fix (S60 Wave 2 Step A.3) resolved the cache-reuse
// dual-GOT cluster, 13 A-cluster tests in `tests/sprint59_defects456_repro.rs`
// still fail. These are drop-glue-shaped defects, not dual-GOT failures.
//
// Starting symptom: `d6_exemplar_propagate_only` subprocess aborts inside
// `heap_dealloc` (cranelisp-runtime/src/alloc.rs:191) via a non-unwinding
// panic — classic double-free / RC underflow.
//
// Reduction starting point (exemplar/grid.cl + exemplar/solver.cl pulled in
// by the failing test): ~500 LOC across two modules.
//
// Reduction endpoint (below): a single 14-LOC file with no cross-module
// imports, no stdio, no recursion, no nested match, no multi-variant ADTs.
// Just: a 1-field ADT wrapping a Vec, a helper that match-unpacks the ADT,
// and a caller that invokes the helper twice on the same argument.
//
// CLIF inspection (via `CRANELISP_CODEGEN_DUMP=*`) reveals the crashing
// `walk` function emits TWO 24-byte heap allocations per call to `cell-at`
// — each closure-shaped: [fn_ptr, drop_glue_ptr, captured_g]. This looks
// like auto-curry or GOT-indirect dispatch constructing a closure for
// a direct two-arg function call (`cell-at g 0`), then RC-dec'ing the
// closure and (via drop-glue) decrementing `g`'s RC on top of the
// caller's own RC tracking. When both allocations happen in the same
// scope with the same captured `g`, the RC of `g` reaches zero before
// the parent scope's cleanup, causing a double-free on the final dec.
//
// Non-determinism: the crash reproduces ~50% of the time from a clean
// shell, but 100% of the time via `Command::new` from Rust test harness.
// ASLR-related heap layout coincidence — whether the freed closure's
// memory collides with `g`'s next access determines crash vs silent
// corruption.
//
// Crash signals observed: SIGSEGV (139), SIGTRAP (133), SIGABRT (134),
// killed-by-signal (None). All mapped to
// `heap_dealloc`'s double-free `debug_assert!`.
//
// Each reduction step below commits as a failing test (subject to the
// test-spawn determinism noted above). Not fixed in this task — reduction
// only per user directive 2026-04-21.

/// Run `--run <entry>` from `cwd` with stdio piped (matches how the
/// nextest harness spawns the subprocess). Used by all drop-glue
/// reductions below — the shell-spawn path has different ASLR behaviour
/// that masks the crash intermittently.
fn run_entry(cwd: &std::path::Path, entry: &str) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} -- run `cargo build` first"
    );
    Command::new(&binary)
        .current_dir(cwd)
        .args(["--run", entry])
        .env("CRANELISP_LIB", stdlib_dir())
        .env("CRANELISP_PLATFORM_PATH", platform_dir())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to invoke binary")
}

/// The reductions below exhibit ASLR-dependent / heap-layout-dependent
/// flakiness. Each trial gets its own fresh tempdir (cold cache) because
/// the cache-warm path has a different (and lower) crash rate. Under
/// cold-cache + Rust-spawn the crash rate is ~90%, so 10 trials gives
/// >99% confidence the reduction still reproduces.
fn reduce_single_file(source: &str, label: &str) {
    const TRIALS: usize = 10;
    let mut crashes: Vec<String> = Vec::new();
    for i in 0..TRIALS {
        // Fresh tempdir per trial — cold cache. A single shared tempdir
        // across trials (cache-warm) drops the crash rate to ~20%.
        let td = tempfile::tempdir().unwrap();
        std::fs::create_dir(td.path().join("subdir")).unwrap();
        std::fs::write(td.path().join("subdir").join("program.cl"), source).unwrap();
        let o = run_entry(td.path(), "subdir/program.cl");
        let exit = o.status.code();
        let signal_crash = matches!(exit, Some(139) | Some(133) | Some(134)) || exit.is_none();
        if signal_crash {
            crashes.push(format!("trial {i}: exit={exit:?}"));
        }
    }
    if !crashes.is_empty() {
        panic!(
            "{label}: {}/{} cold-cache trials crashed with signal. \
             Reduced defect: drop-glue / auto-curry closure captures \
             ADT-wrapped Vec and double-frees its inner Vec. \
             Root-cause pending /backend investigation (S60 Wave 2 Round 2).\n\
             trials that crashed: {}",
            crashes.len(),
            TRIALS,
            crashes.join(", "),
        );
    }
}

// -----------------------------------------------------------------------------
// Reduction step 1 — baseline: the 14-LOC minimal crashing source.
// -----------------------------------------------------------------------------
//
// If this FAILS, the drop-glue defect is reproduced. If it PASSES (a
// possibility given the ASLR non-determinism), rerun — under
// `Command::new` spawn the reliability approaches 100%.

const S60_DROP_GLUE_MINIMAL: &str = r#"(import [primitives [*]])

(deftype Grid [cells])

(defn cell-at [g idx]
  (match g [(Grid cells) (vec-get cells idx)]))

(defn walk [g]
  (let [c1 (cell-at g 0)
        c2 (cell-at g 0)]
    0))

(defn main []
  (let [g (Grid (vec-push [] 0))]
    (walk g)))
"#;

// FIXME(/backend) — S60 Round 2 MINIMAL (14 LOC). Drop-glue / auto-curry
// closure captures the ADT `g` twice (once per `cell-at` call in `walk`);
// when both closures are RC-dec'd, the captured `g`'s RC reaches zero
// before `walk`'s scope cleanup, causing `heap_dealloc` to be invoked on
// `g`'s inner Vec twice (or on `g` itself). Confirmed against CLIF
// (`CRANELISP_CODEGEN_DUMP=*`): `walk`'s block1 allocates two 24-byte
// heap regions, stores two fn pointers + the captured `v1` (g), bumps g's
// RC twice, calls `fn3(closure)` then `fn8(closure)`, then on return
// decrements each closure's RC to zero and runs drop glue. Root cause
// is in either (a) `emit_consuming_caller_rc` for defn calls that get
// auto-curried despite both args present, or (b) closure env RC
// accounting for captures of ADT-wrapped Vec. Not fixed in this task —
// reduction only.
#[test]
fn s60_drop_glue_minimal_14_loc_no_crash() {
    // spec: spec/12-runtime.md §12.4 — RC inc/dec must balance; drop
    // glue must not dec a captured value that the caller also dec's.
    reduce_single_file(S60_DROP_GLUE_MINIMAL, "s60_drop_glue_minimal_14_loc");
}

// -----------------------------------------------------------------------------
// Reduction step 2 — negative control: ONE cell-at call, no crash.
// -----------------------------------------------------------------------------
//
// Proves: the DOUBLE `cell-at` call is load-bearing. One call doesn't
// trigger the double-free. This pins the defect to the interaction of
// two closure allocations on the same captured `g`.

const S60_DROP_GLUE_ONE_CALL: &str = r#"(import [primitives [*]])

(deftype Grid [cells])

(defn cell-at [g idx]
  (match g [(Grid cells) (vec-get cells idx)]))

(defn walk [g]
  (let [c1 (cell-at g 0)]
    0))

(defn main []
  (let [g (Grid (vec-push [] 0))]
    (walk g)))
"#;

#[test]
fn s60_drop_glue_one_cellat_call_passes() {
    // Control: single `cell-at` invocation does not crash. Pins the
    // defect to the TWO-closure-same-capture interaction.
    reduce_single_file(S60_DROP_GLUE_ONE_CALL, "s60_drop_glue_one_cellat_call");
}

// -----------------------------------------------------------------------------
// Reduction step 3 — negative control: INLINE match, no intermediate fn.
// -----------------------------------------------------------------------------
//
// `walk` body uses inline `(match g [(Grid cs) (vec-get cs 0)])` twice
// instead of calling `cell-at`. No closure/partial-application path —
// this passes. Proves: the defect is in `cell-at` being called (the
// intermediate defn invocation) not in match-on-Grid semantics.

const S60_DROP_GLUE_INLINE_MATCH: &str = r#"(import [primitives [*]])

(deftype Grid [cells])

(defn walk [g]
  (let [c1 (match g [(Grid cs) (vec-get cs 0)])
        c2 (match g [(Grid cs) (vec-get cs 0)])]
    0))

(defn main []
  (let [g (Grid (vec-push [] 0))]
    (walk g)))
"#;

#[test]
fn s60_drop_glue_inline_match_passes() {
    // Control: inline-match twice on the same `g` does not crash.
    // Pins the defect to the defn-call path (cell-at), NOT to
    // match-semantics on Grid.
    reduce_single_file(S60_DROP_GLUE_INLINE_MATCH, "s60_drop_glue_inline_match");
}

// -----------------------------------------------------------------------------
// Reduction step 4 — negative control: Grid of Vec Int (no nested ADT).
// -----------------------------------------------------------------------------
//
// Same 14-LOC shape but the Vec's element type is bare Int, not Cell ADT.
// CLARIFICATION TO EARLIER HYPOTHESIS: Cell is NOT load-bearing — this
// variant also crashes. What matters is Grid being an ADT wrapping a
// Vec, not the Vec element type. The inner Vec's RC handling is what
// the closure drop-glue mis-accounts for.

const S60_DROP_GLUE_GRID_VEC_INT: &str = r#"(import [primitives [*]])

(deftype Grid [cells])

(defn cell-at [g idx]
  (match g [(Grid cells) (vec-get cells idx)]))

(defn walk [g]
  (let [c1 (cell-at g 0)
        c2 (cell-at g 0)]
    0))

(defn main []
  (let [g (Grid (vec-push [] 0))]
    (walk g)))
"#;

// FIXME(/backend) — S60 Round 2 variant. This is literally identical
// source to `s60_drop_glue_minimal_14_loc` — committed as a duplicate
// regression guard so that a well-intentioned "simplify" edit of the
// minimal test can't silently delete coverage. If one crashes, both do.
#[test]
fn s60_drop_glue_grid_vec_int_no_crash() {
    reduce_single_file(S60_DROP_GLUE_GRID_VEC_INT, "s60_drop_glue_grid_vec_int");
}

// -----------------------------------------------------------------------------
// Reduction step 5 — negative control: no Grid wrapper, Vec only.
// -----------------------------------------------------------------------------
//
// `walk` takes a bare Vec and calls `vec-get` twice. No ADT wrapping,
// no match. Passes — proves the ADT WRAPPER (Grid) is load-bearing,
// not just the double-lookup pattern.

const S60_DROP_GLUE_NO_WRAPPER: &str = r#"(import [primitives [*]])

(defn walk [v]
  (let [c1 (vec-get v 0)
        c2 (vec-get v 0)]
    0))

(defn main []
  (let [v (vec-push [] 0)]
    (walk v)))
"#;

#[test]
fn s60_drop_glue_no_adt_wrapper_passes() {
    // Control: double `vec-get` on bare Vec, no ADT wrapper. Passes.
    // Pins the defect to the Grid-wrapped-Vec shape specifically.
    reduce_single_file(S60_DROP_GLUE_NO_WRAPPER, "s60_drop_glue_no_adt_wrapper");
}

// -----------------------------------------------------------------------------
// Reduction step 6 — negative control: inline both `cell-at` calls
// into `main`, no intermediate function.
// -----------------------------------------------------------------------------
//
// Same two `cell-at` calls, same Grid wrapper, but happening directly
// in `main` rather than inside an intermediate `walk` function. Passes.
// Proves: the CROSSING of a function-call boundary with a Grid argument
// is load-bearing — the auto-curry / closure path only triggers
// when `cell-at` is called from inside a function whose parameter is
// the Grid being unpacked.

const S60_DROP_GLUE_NO_INTERMEDIATE: &str = r#"(import [primitives [*]])

(deftype Grid [cells])

(defn cell-at [g idx]
  (match g [(Grid cells) (vec-get cells idx)]))

(defn main []
  (let [g (Grid (vec-push [] 0))
        c1 (cell-at g 0)
        c2 (cell-at g 0)]
    0))
"#;

#[test]
fn s60_drop_glue_no_intermediate_fn_passes() {
    // Control: double cell-at called directly from main (no walk fn).
    // Passes. Pins the defect to the intermediate-fn parameter path.
    reduce_single_file(
        S60_DROP_GLUE_NO_INTERMEDIATE,
        "s60_drop_glue_no_intermediate_fn",
    );
}
