//! Sprint 61 Slice 2 — exemplar solver correctness (branch (b) handoff).
//!
//! Two committed-FAILING tests authored per
//! `memory/feedback_failing_not_ignored.md` +
//! `memory/feedback_repros_join_suite.md` +
//! `memory/feedback_cross_skill_minimal_repro.md`.
//!
//! These tests were authored during Sprint 61 Wave 2 after /port exited
//! Slice 2 via branch (b) with a three-layer finding (see
//! `exemplar/solver.cl:370+` FIXME block for the full narrative):
//!
//!   - Layer 1 (algorithmic): `eliminate` returns `(Some g)` on a cell that
//!     is already `(Given v)` or `(Solved v)` with the same value as the
//!     digit being eliminated. Should be `None` — a contradiction.
//!   - Layer 2 (compiler): applying the Layer 1 fix alone regresses valid
//!     puzzles via the backtracking path (`try-digits` + recursive `solve`).
//!     /port source-reduction hit the 2-day cap.
//!   - Layer 3 (compiler, isolated): `exemplar/repro-slice2.cl` — inline
//!     ADT constructor wrapping a `Vec` passed as a function argument
//!     corrupts the inner Vec's length (reads as 0 instead of 1).
//!
//! Both tests flip green when the underlying fix lands. T-S2-1 flips when
//! /port applies the Layer 1 one-line fix in `exemplar/solver.cl` — but
//! that cannot happen cleanly until /backend resolves Layer 2 because
//! applying Layer 1 without the Layer 2 fix regresses valid puzzles.
//! T-S2-2 flips when /backend fixes the inline-ADT-arg-wrapping-Vec
//! codegen defect.
//!
//! Baseline ledger entries: `tests/plan/baseline.md §"Sprint 61 Slice 2"`.

use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

// ---------------------------------------------------------------------------
// Subprocess harness — both tests drive `./cranelisp --run <exemplar.cl>`.
// ---------------------------------------------------------------------------

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

fn exemplar_dir() -> PathBuf {
    project_root().join("exemplar")
}

/// Run an exemplar `.cl` file via `cranelisp --run`. Working directory is
/// `exemplar/` so relative imports (grid, solver, etc.) resolve.
fn run_exemplar_file(relative_cl: &str) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );
    Command::new(&binary)
        .args(["--run", relative_cl])
        .current_dir(exemplar_dir())
        .env("CRANELISP_LIB", stdlib_dir())
        .env("CRANELISP_PLATFORM_PATH", platform_dir())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to invoke cranelisp")
}

fn stdout_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn stderr_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

// ===========================================================================
// T-S2-1 — Layer 1 contract: `eliminate` on a same-value Given/Solved cell
// MUST return None (a contradiction), not (Some g).
//
// The test fixture `exemplar/test-eliminate-contract.cl` builds a minimal
// grid with `(Given 5)` at cell 0 and calls `(eliminate g 0 5)`. Its `main`
// returns:
//   0 — pass (eliminate returned None, per the Layer 1 contract)
//   1 — fail (eliminate returned (Some _); current buggy behaviour)
//   2 — setup failure (unexpected)
//
// This cargo-level assertion asserts exit == 0. Current behaviour: exit == 1.
//
// Flips green when /port applies the Layer 1 fix in
// `exemplar/solver.cl::eliminate` (gated on /backend resolving Layer 2 first
// so the fix doesn't regress valid puzzles).
// ===========================================================================

// spec: exemplar/solver.cl:370+ FIXME block — Layer 1 eliminate contract;
//       memory/feedback_cross_skill_minimal_repro.md — minimal repro
// FIXME(/port): apply the one-line Layer 1 fix in exemplar/solver.cl once
//       /backend has resolved Layer 2 (inline-ADT-arg-wrapping-Vec, see T-S2-2).
#[test]
fn eliminate_on_same_value_given_returns_none() {
    let o = run_exemplar_file("test-eliminate-contract.cl");
    let exit = o.status.code();

    assert_eq!(
        exit, Some(0),
        "`eliminate` on `(Given 5)` at cell 0 with digit 5 MUST return \
         None (contradiction — eliminating the cell's own fixed value). \
         exemplar/solver.cl:370+ FIXME block Layer 1 contract. \
         Exit 0 = pass, 1 = eliminate returned (Some _) [current buggy \
         state], 2 = setup failure. \
         Got exit={exit:?}\nstdout: {}\nstderr: {}",
        stdout_str(&o),
        stderr_str(&o),
    );
}

// ===========================================================================
// T-S2-2 — Layer 3 compiler bug: inline ADT constructor wrapping Vec,
// passed as a function argument, corrupts the inner Vec's length.
//
// The repro file `exemplar/repro-slice2.cl` prints three lines:
//   direct-let: len=1   ; baseline — let-binding alone produces len=1
//   inline-arg: len=1   ; bug trigger — (consume (Box [0])) — SHOULD be len=1
//   let-arg:    len=1   ; workaround — (let [b (Box [0])] (consume b)) — len=1
//
// Current state (HEAD a9028c0, per /port readout 2026-04-22):
//   direct-let: len=1
//   inline-arg: len=0   ; BUG: Vec length reads as 0
//   let-arg:    len=1
//
// This test asserts the expected (post-fix) shape: all three `len=1`.
// Currently `inline-arg: len=0` so the test FAILS.
//
// Flips green when /backend fixes the consuming-arg RC / match-unwrap
// codegen defect for inline ADT constructors wrapping a Vec.
// ===========================================================================

// spec: exemplar/repro-slice2.cl (Layer 3 compiler-bug repro per /port
//       Slice 2 branch (b) readout 2026-04-22);
//       memory/feedback_repros_join_suite.md — committed failing
// FIXME(/backend): resolve inline-ADT-arg-wrapping-Vec corruption.
//       Hypothesis per exemplar/repro-slice2.cl: consuming-arg RC emission
//       for in-expression ADT constructors — constructor's allocation is
//       dec'd before the callee's match-unwrap can take ownership of the
//       inner Vec.
#[test]
fn inline_adt_arg_wrapping_vec_preserves_len() {
    let o = run_exemplar_file("repro-slice2.cl");

    assert!(
        o.status.success(),
        "exemplar/repro-slice2.cl MUST exit cleanly (exit 0); \
         non-zero exit indicates a runtime failure separate from the \
         length-corruption bug. \
         Got exit={:?}\nstdout: {}\nstderr: {}",
        o.status.code(),
        stdout_str(&o),
        stderr_str(&o),
    );

    let out = stdout_str(&o);

    // The direct-let and let-arg baselines must remain len=1 — if these
    // ever regress, the ledger entry's signature has shifted and the
    // harness itself needs re-verification before the Layer 3 assertion.
    assert!(
        out.contains("direct-let: len=1"),
        "exemplar/repro-slice2.cl baseline (direct-let) MUST print \
         `direct-let: len=1`; regression would invalidate the repro's \
         framing. Got stdout:\n{out}"
    );
    assert!(
        out.contains("let-arg:    len=1"),
        "exemplar/repro-slice2.cl workaround (let-arg) MUST print \
         `let-arg:    len=1`. Got stdout:\n{out}"
    );

    // The Layer 3 contract: inline-arg MUST also print `len=1`. Currently
    // prints `len=0` under the bug.
    assert!(
        out.contains("inline-arg: len=1"),
        "exemplar/repro-slice2.cl Layer 3 contract VIOLATED — \
         `(consume (Box [0]))` reads the inner Vec's length as 0 instead \
         of 1. Expected `inline-arg: len=1`; got stdout:\n{out}\n\
         This is the inline-ADT-arg-wrapping-Vec compiler bug per \
         exemplar/repro-slice2.cl. /backend owns the fix; hypothesis \
         space in the repro file header."
    );
}
