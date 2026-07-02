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
