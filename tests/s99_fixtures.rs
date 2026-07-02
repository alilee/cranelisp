//! Sprint 99 Wave 0.3 — parallel-contention measurement fixtures (F1–F4).
//!
//! These are the committed, free-standing (zero-stdlib) regression guards for
//! the measurement ladder in `tests/fixtures/s99/`. The *timing* numbers are
//! produced out-of-band by `tests/perf/s99_measure.py` (not part of this
//! canonical suite — scheduling-dependent, flaky as hard asserts). What IS a
//! durable correctness guard, and lives here, is the **parallel ≡ serial**
//! invariant on the reshaped nested-ADT workloads: because the code is pure,
//! the speculative-parallel default and the genuinely-serial
//! `CRANELISP_NO_LENIENT=1` run MUST produce byte-identical results (here, the
//! process exit code = the fixture's checksum). A divergence is a real defect
//! (a lost-update / RC / codegen bug in the spark path). Per arch R5, these
//! land regardless of the mechanism-wave funding decision.
//!
//! spec: design/backend/lenient-eval.md §2.1 — the sparkability algorithm
//! (`find_sparkable_bindings`) produces the speculative-parallel path whose
//! result, because the code is pure, MUST equal the serial result.

#[path = "helpers/e2e.rs"]
mod e2e;

use e2e::{Cranelisp, PreludeVariant};

/// Run a fixture under the given lenient mode; return (exit_code, stderr).
fn run_mode(name: &str, src: &str, serial: bool) -> (i32, String) {
    let mut c = Cranelisp::new().with_prelude(PreludeVariant::None).file(name, src);
    if serial {
        c = c.env("CRANELISP_NO_LENIENT", "1");
    }
    let out = c.run(name).output();
    let code = out
        .status
        .code()
        .unwrap_or_else(|| panic!("{name} terminated by signal; stderr:\n{}", out.stderr));
    (code, out.stderr)
}

/// Assert the fixture compiles+runs cleanly and that the speculative-parallel
/// default and the serial (`CRANELISP_NO_LENIENT=1`) run agree.
fn assert_parallel_equals_serial(name: &str, src: &str) {
    let (par_code, par_err) = run_mode(name, src, false);
    let (ser_code, _ser_err) = run_mode(name, src, true);
    assert!(
        !par_err.contains("error"),
        "{name} produced a compile/runtime error:\n{par_err}"
    );
    assert_eq!(
        par_code, ser_code,
        "{name}: parallel exit {par_code} != serial exit {ser_code} (lost-update / RC / codegen defect in the spark path)"
    );
}

/// Run a fixture with an arbitrary env set; return (exit_code, stderr). Panics
/// (fails the test) if the child is terminated by a SIGNAL — a SIGABRT/SIGSEGV
/// from a double-free / use-after-free has no exit code, so this doubles as the
/// heap-corruption guard for the capture-borrow path.
fn run_with_env(name: &str, src: &str, envs: &[(&str, &str)]) -> (i32, String) {
    let mut c = Cranelisp::new().with_prelude(PreludeVariant::None).file(name, src);
    for (k, v) in envs {
        c = c.env(k, v);
    }
    let out = c.run(name).output();
    let code = out.status.code().unwrap_or_else(|| {
        panic!("{name} terminated by SIGNAL (heap corruption / crash) — env {envs:?}; stderr:\n{}", out.stderr)
    });
    (code, out.stderr)
}

/// Parse `rc_inc` from a `[RC_STATS] rc_inc=N rc_dec=N allocs=N deallocs=N` line.
fn rc_inc_of(stderr: &str) -> u64 {
    stderr
        .lines()
        .find_map(|l| l.split("rc_inc=").nth(1))
        .and_then(|rest| rest.split_whitespace().next())
        .and_then(|n| n.parse().ok())
        .unwrap_or_else(|| panic!("no [RC_STATS] rc_inc= line in stderr:\n{stderr}"))
}

/// Assert the fixture runs clean under the **capture-borrow toggle**
/// (`CRANELISP_CAPTURE_BORROW=1`, Sprint 99 Wave 1b, FIXME 0461) and that the
/// borrow-elided parallel run agrees with the genuinely-serial run. Because the
/// code is pure, borrowing a structurally-joined spark's captures MUST NOT
/// change the result — a divergence (or a signal) is a borrow-elision UAF /
/// lost-update defect (the S98 bug-#2 class).
fn assert_borrow_parallel_equals_serial(name: &str, src: &str) {
    let (borrow_code, borrow_err) =
        run_with_env(name, src, &[("CRANELISP_CAPTURE_BORROW", "1")]);
    let (serial_code, _) = run_with_env(name, src, &[("CRANELISP_NO_LENIENT", "1")]);
    assert!(
        !borrow_err.contains("error"),
        "{name} capture-borrow run produced a compile/runtime error:\n{borrow_err}"
    );
    assert_eq!(
        borrow_code, serial_code,
        "{name}: capture-borrow parallel exit {borrow_code} != serial exit \
         {serial_code} — a borrow/retain misclassification (UAF / lost update) in \
         the structurally-joined spark path (ring2-rc.md §5.5.2)"
    );
}

// spec: design/backend/ring2-rc.md §5.5.2.6 — the parallel≡serial correctness +
//       no-corruption guard for capture-by-borrow, with the toggle ON, on the
//       F1–F4 shared-grid copy-per-guess fixtures (captured `Grid`).
#[test]
fn s99_f1_capture_borrow_parallel_equals_serial() {
    assert_borrow_parallel_equals_serial("f1.cl", include_str!("fixtures/s99/f1_machinery.cl"));
}

// spec: design/backend/ring2-rc.md §5.5.2.6
#[test]
fn s99_f2_capture_borrow_parallel_equals_serial() {
    assert_borrow_parallel_equals_serial("f2.cl", include_str!("fixtures/s99/f2_contention.cl"));
}

// spec: design/backend/ring2-rc.md §5.5.2.6
#[test]
fn s99_f3_capture_borrow_parallel_equals_serial() {
    assert_borrow_parallel_equals_serial(
        "f3.cl",
        include_str!("fixtures/s99/f3_inverted_search.cl"),
    );
}

// spec: design/backend/ring2-rc.md §5.5.2.6
#[test]
fn s99_f4_capture_borrow_parallel_equals_serial() {
    assert_borrow_parallel_equals_serial("f4.cl", include_str!("fixtures/s99/f4_sudoku.cl"));
}

// spec: design/backend/ring2-rc.md §5.5.2.6 — the inc-count-drop WITNESS. With
//       the toggle ON, the per-copy shared-grid captures of F2's structurally-
//       joined apply-arg sparks become borrows, so `CRANELISP_RC_STATS`' `rc_inc`
//       drops materially vs the toggle OFF. Asserts a scheduling-independent
//       strict drop (not an exact number): borrow only ever *removes* capture
//       incs, and F2's D&C reduce reliably sparks its top-level apply-arg halves,
//       so no-borrow > borrow with a stable margin (observed ≥59 across runs;
//       the borrow count is deterministic == the serial count).
#[test]
fn s99_f2_capture_borrow_drops_rc_inc() {
    let src = include_str!("fixtures/s99/f2_contention.cl");
    let (nb_code, nb_err) = run_with_env("f2.cl", src, &[("CRANELISP_RC_STATS", "1")]);
    let (bo_code, bo_err) = run_with_env(
        "f2.cl",
        src,
        &[("CRANELISP_RC_STATS", "1"), ("CRANELISP_CAPTURE_BORROW", "1")],
    );
    assert_eq!(
        nb_code, bo_code,
        "capture-borrow changed F2's result ({nb_code} != {bo_code}) — a correctness defect"
    );
    let no_borrow = rc_inc_of(&nb_err);
    let borrow = rc_inc_of(&bo_err);
    assert!(
        borrow < no_borrow,
        "capture-borrow must DROP rc_inc on F2 (the shared-grid spark captures \
         become borrows): no_borrow={no_borrow} borrow={borrow} (drop={})",
        no_borrow as i64 - borrow as i64
    );
}

#[test]
fn s99_f1_machinery_parallel_equals_serial() {
    assert_parallel_equals_serial("f1.cl", include_str!("fixtures/s99/f1_machinery.cl"));
}

#[test]
fn s99_f2_contention_parallel_equals_serial() {
    assert_parallel_equals_serial("f2.cl", include_str!("fixtures/s99/f2_contention.cl"));
}

#[test]
fn s99_f3_inverted_search_parallel_equals_serial() {
    assert_parallel_equals_serial("f3.cl", include_str!("fixtures/s99/f3_inverted_search.cl"));
}

#[test]
fn s99_f4_sudoku_parallel_equals_serial() {
    assert_parallel_equals_serial("f4.cl", include_str!("fixtures/s99/f4_sudoku.cl"));
}
