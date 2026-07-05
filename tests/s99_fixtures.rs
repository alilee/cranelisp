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

/// Assert the fixture runs clean under the **saturation-gate toggle**
/// (`CRANELISP_SATURATION_GATE=1`, Sprint 99 Wave 1c, FIXME 0459) and that the
/// gated parallel run agrees with the genuinely-serial run. The gate is a pure
/// scheduling choice (spark iff spare worker capacity; else inline the branch via
/// the create-gate's already-correct direct arm), so it MUST NOT change the
/// result — a divergence (or a SIGNAL, caught by `run_with_env`) would be a
/// codegen/scheduling defect, not a scheduling no-op.
fn assert_saturation_gate_parallel_equals_serial(name: &str, src: &str) {
    let (gate_code, gate_err) =
        run_with_env(name, src, &[("CRANELISP_SATURATION_GATE", "1")]);
    let (serial_code, _) = run_with_env(name, src, &[("CRANELISP_NO_LENIENT", "1")]);
    assert!(
        !gate_err.contains("error"),
        "{name} saturation-gate run produced a compile/runtime error:\n{gate_err}"
    );
    assert_eq!(
        gate_code, serial_code,
        "{name}: saturation-gate parallel exit {gate_code} != serial exit \
         {serial_code} — inlining a saturated branch must be result-equivalent to \
         sparking it (scheduling-only; both arms produce identical values)"
    );
}

// spec: design/backend/lenient-eval.md §3.6 — the parallel≡serial + no-corruption
//       guard for the saturation-shaped spark gate, toggle ON, on F1–F4. Inlining
//       the overflow branch (direct arm) must be byte-identical to sparking it.
#[test]
fn s99_f1_saturation_gate_parallel_equals_serial() {
    assert_saturation_gate_parallel_equals_serial(
        "f1.cl",
        include_str!("fixtures/s99/f1_machinery.cl"),
    );
}

// spec: design/backend/lenient-eval.md §3.6
#[test]
fn s99_f2_saturation_gate_parallel_equals_serial() {
    assert_saturation_gate_parallel_equals_serial(
        "f2.cl",
        include_str!("fixtures/s99/f2_contention.cl"),
    );
}

// spec: design/backend/lenient-eval.md §3.6
#[test]
fn s99_f3_saturation_gate_parallel_equals_serial() {
    assert_saturation_gate_parallel_equals_serial(
        "f3.cl",
        include_str!("fixtures/s99/f3_inverted_search.cl"),
    );
}

// spec: design/backend/lenient-eval.md §3.6
#[test]
fn s99_f4_saturation_gate_parallel_equals_serial() {
    assert_saturation_gate_parallel_equals_serial(
        "f4.cl",
        include_str!("fixtures/s99/f4_sudoku.cl"),
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

// =============================================================================
// S103 increment-II — the F2v single-ctor witness fixture (qa plan
// `tests/plan/s103-test-plan.md` §1.1, gate II-G1). F2v is the honest R5
// witness: one-word single-constructor `(Cell [:Int value])`, the shape R5's
// first landing (backend §7.1/§7.2) genuinely flattens. The *timing*/rc_inc
// gate itself is a perf lane (`ig_gates.py`, §2); the durable in-suite
// correctness guard is the same parallel≡serial invariant the F1–F4 rows carry
// — GREEN at draft (holds off-mechanism, because the code is pure) and
// LOAD-BEARING through R5: a flattening that corrupts the by-value copy path
// diverges the parallel and serial checksums here.
// =============================================================================

// spec: design/backend/lenient-eval.md §2.1 — the sparkability algorithm's
// speculative-parallel result MUST equal the serial result on the F2v
// single-ctor reshaped workload (parallel ≡ serial). GREEN at draft.
#[test]
fn s99_f2v_single_ctor_parallel_equals_serial() {
    assert_parallel_equals_serial(
        "f2v.cl",
        include_str!("fixtures/s99/f2v_single_ctor.cl"),
    );
}

// spec: design/backend/ring2-rc.md §5.5.2.6 — the capture-borrow parallel≡serial
// + no-corruption guard on F2v (the R5-witness shape). GREEN at draft;
// load-bearing when the borrow-elision + R5 flattening seams both run.
#[test]
fn s99_f2v_single_ctor_capture_borrow_parallel_equals_serial() {
    assert_borrow_parallel_equals_serial(
        "f2v.cl",
        include_str!("fixtures/s99/f2v_single_ctor.cl"),
    );
}

// =============================================================================
// S103 increment-II — L-B2(ii) byte-differential on the write-path fixtures
// (qa plan §1.2 / §4). `CRANELISP_NO_OWNERSHIP=1` is the permanent correctness
// oracle: R5 flattening is representation-internal + toggle-gated (toggle-off
// forces all-heap, byte-identical to pre-R5), so the OBSERVABLE output of F2v
// must be byte-identical with the toggle ON vs OFF regardless of which
// mechanism has landed. GREEN at draft (nothing flattens yet) and LOAD-BEARING
// when R5 lands — a flattening that changes an observable value fails here.
// Each session pins its polarity EXPLICITLY (env_remove for OFF) so the legs
// hold under the ambient-polarity L-B2(i) suite run.
// =============================================================================

/// Run a fixture under an explicit ownership-toggle polarity; return
/// (exit_code, stdout). Panics (fails) on a SIGNAL — a toggle-induced heap
/// corruption has no exit code.
fn run_ownership_polarity(name: &str, src: &str, no_ownership: bool) -> (i32, String) {
    let mut c = Cranelisp::new().with_prelude(PreludeVariant::None).file(name, src);
    c = if no_ownership {
        c.env("CRANELISP_NO_OWNERSHIP", "1")
    } else {
        c.env_remove("CRANELISP_NO_OWNERSHIP")
    };
    let out = c.run(name).output();
    let code = out.status.code().unwrap_or_else(|| {
        panic!("{name} terminated by SIGNAL under ownership polarity no_ownership={no_ownership}; stderr:\n{}", out.stderr)
    });
    (code, out.stdout)
}

/// Assert a fixture's observable output (exit code + stdout) is byte-identical
/// under both ownership-toggle polarities — the L-B2(ii) differential oracle.
fn assert_ownership_toggle_byte_identical(name: &str, src: &str) {
    let (off_code, off_out) = run_ownership_polarity(name, src, false);
    let (on_code, on_out) = run_ownership_polarity(name, src, true);
    assert_eq!(
        off_code, on_code,
        "{name}: ownership-toggle changed the exit value (off {off_code} != on {on_code}) — \
         the CRANELISP_NO_OWNERSHIP oracle demands byte-identical observable output \
         (qa plan §4; s100-ownership-verification.md §0.1)"
    );
    assert_eq!(
        off_out, on_out,
        "{name}: ownership-toggle changed stdout — off:\n{off_out}\non:\n{on_out}"
    );
}

// spec: tests/plan/s100-ownership-verification.md §3.1 — L-B2(ii) byte-
// differential on F2v: toggle-on ≡ toggle-off observable output for the R5
// witness. GREEN at draft; discriminating once R5 lands.
#[test]
fn s99_f2v_output_byte_identical_under_ownership_toggle() {
    assert_ownership_toggle_byte_identical(
        "f2v.cl",
        include_str!("fixtures/s99/f2v_single_ctor.cl"),
    );
}

// spec: tests/plan/s100-ownership-verification.md §3.1 — L-B2(ii) byte-
// differential on F2 (the two-ctor nested-ADT witness) as the reuse-token
// oracle: reuse tokens are off-ABI/function-local, so toggle-off forces the
// conservative dealloc+alloc path — byte-identical to pre-reuse codegen.
// GREEN at draft; load-bearing when reuse tokens land.
#[test]
fn s99_f2_output_byte_identical_under_ownership_toggle() {
    assert_ownership_toggle_byte_identical(
        "f2.cl",
        include_str!("fixtures/s99/f2_contention.cl"),
    );
}
