//! Sprint 96 — effect-concurrency Chunk A: stdio v7 adoption — the QA-first
//! (Phase-5 Wave-A1) e2e rows.
//!
//! Plan: `tests/plan/sprint-96.md` §3B / §3C (stdio half). Scope source:
//! `sprints/SPRINT.md` S96 item 1 ("`print` stays blocking; `read_line` the poll
//! candidate — the 'simple platform ports cleanly' ergonomics check").
//!
//! ## The unit-vs-e2e / RED honesty note (Wave A1 finding)
//!
//! The stdio `read_line` correctness round-trip is **observationally equivalent**
//! to the v6 path through the subprocess harness: with stdin piped + closed
//! up-front, a poll-shape `read_line` finds its data already ready and returns
//! without ever suspending, so it is byte-identical to the v6 blocking read. The
//! subprocess harness has no controllable mid-run stdin timing, so there is no
//! observable poll-vs-block distinction on instant I/O. Therefore these rows are
//! authored as **honest verify / stays-green pins**, NOT RED-first: they pin the
//! "simple platform ports cleanly" correctness invariant (the rewrite must not
//! regress the round-trip) and become regression guards once A4 lands. The
//! genuine RED-first acceptance for the poll carrier lives in
//! `concurrency_poll_capacity.rs` (the §1 capacity rows, which require the
//! acquire-around-poll machinery and are RED against the absent `poll-pool`
//! leaf). See the Wave-A1 ledger note in `tests/plan/sprint-96.md`.
//!
//! ## Lanes
//!
//! - §3B / §3B-neg are gated `#[cfg(feature = "concurrency-runtime")]` — they
//!   exercise the stdio leaves with the reactor ON (`nt-reactor-e2e`), the lane
//!   where the poll candidate matters.
//! - §3C-stdio is UNGATED — the byte-identical-off floor runs in the default
//!   `nt` lane (the production default, `concurrency-runtime` OFF).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

/// A read-line→echo program: read one line from stdin, print it back. Returns
/// `IO Int` (the `print` effect's `IO Int`).
fn read_echo_prog() -> &'static str {
    "(platform stdio)\n\
     (import [platform.stdio [print read-line]])\n\
     (import [primitives [bind]])\n\
     (defn main [] (bind (read-line) (fn [line] (print line))))\n"
}

// =============================================================================
// §3B — stdio `read_line` poll candidate round-trips (reactor ON).
// =============================================================================

// spec: spec/10-io.md §10.12.4.1 — a `--run` program built `concurrency-runtime`
// ON that `read_line`s from piped stdin (the poll candidate — suspends on stdin
// readiness, resumes) and echoes via `print` (which stays blocking): the line
// round-trips correctly. The "simple platform ports cleanly" ergonomics check.
// Posture: verify / stays-green (see the module RED-honesty note) — flips to a
// regression guard once the A4 stdio rewrite makes `read_line` poll-shape.
#[test]
fn stdio_read_line_poll_candidate_round_trips() {
    let probe = "hello-roundtrip-A1";
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .use_workspace_platforms()
        .run("user.cl")
        .user(read_echo_prog())
        .stdin(&format!("{probe}\n"))
        .output();
    out.assert_stdout_contains(probe);
}

// =============================================================================
// §3B-neg — `print` stays blocking (NOT converted to a poll leaf).
// =============================================================================

// spec: spec/10-io.md §10.12.4.1 — `print` is NOT converted to a poll leaf; it
// lowers to the blocking carrier. The negative face: the rewrite did NOT
// over-convert blocking effects to poll-shape. Observable proxy: sequential
// `print`s land in SOURCE ORDER (a synchronous/blocking effect is not reordered
// by the reactor). Posture: stays-green (the rewrite touches only `read_line`).
#[test]
fn stdio_print_stays_blocking_neg() {
    let prog = "(platform stdio)\n\
                (import [platform.stdio [print]])\n\
                (import [primitives [bind]])\n\
                (defn main []\n\
                  (bind (print \"first\\n\") (fn [_]\n\
                    (bind (print \"second\\n\") (fn [_]\n\
                      (print \"third\\n\"))))))\n";
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .use_workspace_platforms()
        .run("user.cl")
        .user(prog)
        .output();
    let stdout = out.stdout.clone();
    let i1 = stdout.find("first");
    let i2 = stdout.find("second");
    let i3 = stdout.find("third");
    assert!(
        matches!((i1, i2, i3), (Some(a), Some(b), Some(c)) if a < b && b < c),
        "`print` must stay blocking (sequential, source-ordered) — not reordered \
         as a poll leaf; got stdout={stdout:?}",
    );
}

// =============================================================================
// §3C-stdio — byte-identical when the feature is OFF (the default-lane floor).
// =============================================================================

// spec: spec/10-io.md §10.12.4.1 — a stdio `read_line`/`print` program is
// byte-identical through the default (feature-off) binary — the poll-candidate
// rewrite is invisible feature-off. Posture: stays-green (regression-replay over
// the standing `spec_platforms` stdio coverage). UNGATED — runs in `nt`.
#[test]
fn stdio_default_build_output_byte_identical_off() {
    let probe = "stdio-byte-identical-off-A1";
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .use_workspace_platforms()
        .run("user.cl")
        .user(read_echo_prog())
        .stdin(&format!("{probe}\n"))
        .output();
    out.assert_stdout_contains(probe);
}
