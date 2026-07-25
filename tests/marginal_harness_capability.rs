//! Capability fence for `tests/helpers/marginal.rs` — the marginal-balance
//! harness (S118 Branch-F closure; `sprints/SPRINT.md` §Notes 2026-07-26).
//!
//! METHOD §2.2: **an instrument is unverified until it is proven to detect.**
//! The marginal harness now carries four baseline cells whose GREEN is the
//! sprint's evidence that `conj`, the int-accumulator control, and the M3 clean
//! child leak nothing. That evidence is only worth what this file proves:
//!
//!  1. a leak of ONE block on the subject side shows up as a marginal residual
//!     of exactly one — the harness cannot subtract a real defect away;
//!  2. two identical children read exactly zero — the harness does not
//!     manufacture a marginal out of run-to-run noise;
//!  3. the ambient FIXME-0889 term that the retrofitted cells subtract is
//!     **deterministic run-to-run**, so it cancels exactly rather than
//!     approximately. This is the load-bearing precondition of the whole
//!     approach: a wandering ambient term would turn every marginal cell into
//!     noise with a plausible-looking number attached.
//!
//! The injected leak in (1) is the closed M3 detection-proof plant
//! (`CRANELISP_TEST_FAULTS=s116-detection-proof-v1`, `CRANELISP_TEST_FAULT=M3Leak`
//! — `design/intrinsics/diagnostic-modes.md` §7.2/§7.3), armed on the SUBJECT
//! child only. It suppresses exactly one production dealloc discharge, which is
//! the smallest leak the allocator can express — so this fence pins the
//! harness's resolution at one block, not at "some visible amount".
//!
//! No live compiler behaviour is asserted here, so this file cannot expire when
//! someone else's change lands: (1) is a plant, (2) is a tautology the harness
//! must honour, and (3) is stated as equality between two runs rather than
//! against any particular ambient number.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::marginal::{Child, MarginalPair};

/// Trivial program; the mini-prelude children below compile in milliseconds.
const TRIVIAL: &str = "(import [primitives [Pure]])\n\
     (defn main [] (Pure 0))\n";

/// A one-module library tree with nothing in it but an empty prelude — the
/// cheapest possible child that still exercises the full `--run` path.
fn mini_child() -> Child {
    Child::new(TRIVIAL).lib_file("prelude.cl", "")
}

// The harness must surface a ONE-BLOCK leak on the subject side. Control and
// subject are byte-identical children; the subject additionally arms the M3
// plant, which suppresses exactly one dealloc discharge. A harness that
// normalised, rounded, or otherwise absorbed the difference would read 0 here
// and every marginal cell in the suite would be worthless.
// spec: (harness capability fence — no single spec §) — the normative statements
//       are `sprints/METHOD.md` §2.2 (an instrument is unverified until proven to
//       detect) and `design/intrinsics/diagnostic-modes.md` §7.2 (the closed
//       plant protocol).
#[test]
fn marginal_harness_detects_a_single_injected_leak_in_the_subject() {
    let m = MarginalPair::new(
        "one suppressed dealloc discharge, injected by the M3 plant",
        mini_child(),
        mini_child()
            .env("CRANELISP_TEST_FAULTS", "s116-detection-proof-v1")
            .env("CRANELISP_TEST_FAULT", "M3Leak"),
    )
    .measure();

    assert_eq!(
        m.residual(),
        1,
        "the marginal harness MUST surface a one-block leak on the subject side. \
         The M3 plant suppresses exactly one dealloc, so the marginal residual is \
         exactly 1; a 0 here means the harness cannot see a real leak and every \
         cell built on it is a false green.\n{}",
        m.report()
    );
    assert_eq!(
        m.allocs(),
        0,
        "the plant suppresses a DEALLOC, so the marginal must be visible on the \
         dealloc side alone — a marginal alloc here means the plant changed what \
         the child does, not just what it frees.\n{}",
        m.report()
    );
}

// The other polarity: identical children must read exactly zero. A harness that
// drifted — leaking harness-side state between the two spawns, reusing a cache,
// inheriting ambient environment differently on the two sides — would show a
// spurious non-zero marginal and turn every retrofitted cell RED for a reason
// that has nothing to do with the compiler.
// spec: (harness capability fence — no single spec §) — `sprints/METHOD.md` §2.2.
#[test]
fn marginal_harness_reads_zero_for_identical_children() {
    let m = MarginalPair::new("nothing at all", mini_child(), mini_child()).measure();
    assert_eq!(
        m.residual(),
        0,
        "identical children MUST produce a zero marginal.\n{}",
        m.report()
    );
    assert_eq!(
        (m.allocs(), m.deallocs()),
        (0, 0),
        "identical children MUST agree on both counters, not merely on their \
         difference — a compensating pair of drifts is still drift.\n{}",
        m.report()
    );
}

// The precondition the four retrofitted baseline cells rest on: the ambient
// stdlib-prelude residual (FIXME 0889 — 1143 allocations at S118 HEAD) is the
// SAME number in two independent children, so subtracting it is exact rather
// than approximate. Stated as equality between the two runs, not against 1143,
// so it survives the 0889 fix unchanged (both sides simply become balanced).
//
// This is the one cell here that pays for two full stdlib children; it is worth
// it, because if this equality ever fails then `ms_p8_conj_leak` and
// `intrinsics_m3_detection_s116` are measuring noise and their greens mean
// nothing.
// spec: (harness capability fence — no single spec §) — `sprints/METHOD.md` §2.2;
//       the ambient term is `tests/plan/s118-test-plan.md` §2.5 / FIXME 0889.
#[test]
fn marginal_harness_cancels_the_ambient_prelude_residual_deterministically() {
    let stdlib_child = || Child::new(TRIVIAL).use_workspace_stdlib_for_stdlib_conformance_only();
    let m = MarginalPair::new(
        "two identical full-stdlib children",
        stdlib_child(),
        stdlib_child(),
    )
    .measure();

    assert_eq!(
        m.control().residual(),
        m.subject().residual(),
        "the ambient prelude-load residual MUST be identical in two independent \
         children, or it cannot be cancelled by subtraction and every marginal \
         cell over a stdlib child is measuring noise.\n{}",
        m.report()
    );
    assert_eq!(
        m.residual(),
        0,
        "identical stdlib children MUST produce a zero marginal.\n{}",
        m.report()
    );
}
