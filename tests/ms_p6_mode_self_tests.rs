// ms_p6_mode_self_tests.rs — MS-P6 diagnostic-mode capability fences (S113 W5).
//
// The tier-5 memory-safety diagnostic modes (`crates/cranelisp-intrinsics/src/
// diagnostics.rs`, `design/intrinsics/diagnostic-modes.md`) are env-gated allocator
// behaviour. Each mode gets a self-test proving it CATCHES a planted fault (and
// does NOT false-fire on a clean program) — the MS-P6 discipline: a diagnostic mode
// that cannot demonstrate it sees a planted fault is unverified.
//
//   M3 (counters/parity, `CRANELISP_ALLOC_PARITY`) — atexit hard-check
//       ALLOC==DEALLOC; dump + abort on imbalance.
//   M1 (quarantine, `CRANELISP_QUARANTINE_FREED`) — withhold freed blocks so a
//       freed address is never re-handed; a stale/second free is deterministically
//       detected instead of corrupting a reused block (see the 0638 M1 self-test in
//       macro_expansion_interior_alias_double_free.rs).
//   M2 (scrub, `CRANELISP_SCRUB_FREED`) — poison freed memory.
//
// These are GREEN capability fences. Free-standing (no stdlib).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// TOMBSTONE (S115 W3c, FIXME 0746) — `m3_parity_catches_planted_leak` is RETIRED,
// per the `tests/plan/memory-safety-coverage.md` §4.1 prong-2 lifecycle ruling and
// /qa's disposition at `tests/plan/s115-test-plan.md` §8.2.
//
// It was an e2e capability fence whose planted fault was a LIVE compiler defect, so
// it expired every time that defect was fixed — twice:
//
//   1. Original plant, the entry-`main` teardown shape
//      `(defn main [] (let [s "hi"] (Pure 9)))` — DRAINED by the S114 W4 F-R1 fix
//      (`rc_emission.rs::protect_return_value`); re-planted per FIXME 0690.
//   2. Re-plant, the non-`main` sibling `(defn g [] (let [s "hi"] (Pure 9)))
//      (defn main [] (g))` — DRAINED by the S115 W3 item-26 generalisation (no
//      protective inc for a fresh-construction return in ANY function), which
//      superseded the `main`-keyed F-R1 special case. The test's own FLIP-HAZARD
//      note predicted this verbatim.
//
// Both faces of the planted class are gone; the compiler moved in the correct
// direction each time and the fence's stimulus evaporated. A third plant drawn from
// a live defect would expire the same way, and /qa REJECTED the available candidate
// (the entry-`main` heap-payload leak, FIXME 0745) on exactly that ground — it now
// has an owner and a fix path, and a capability fence must not be collateral of
// someone else's fix.
//
// Why no synthetic e2e re-plant here: the compliant durable shape is a test-only
// injected imbalance at the intrinsics allocator/diagnostics seam behind an
// inert-unless-set env gate (the S114 MS-P6 precedent,
// `safety_lane_detects_falsified_clean_expectation_capability_green`, `7c2d5168`).
// That hook is `/dev`(intrinsics) source — outside `/testing`'s boundary — and did
// not land in this wave, so the §4.1 fallback applies. When the hook is authored,
// the fence returns here as `m3_parity_catches_injected_imbalance` and the hook
// joins `diagnostics/tests.rs::all_gates_default_off` in the same change-set.
//
// Coverage after retirement (§4.1's three prongs, all satisfied — NOT a regression):
//   - prong 1 (durable capability record): the four M3 parity self-tests at the
//     intrinsics allocator seam — `crates/cranelisp-intrinsics/src/diagnostics/
//     tests.rs::{parity_report_flags_leak, parity_report_flags_double_free,
//     parity_report_flags_nonempty_live_set, parity_report_none_when_balanced}`
//     (`:100/:108/:116/:124`) — prove the detection logic fires on a synthetic
//     leak, a synthetic double-free, and a non-empty live set, and stays silent
//     when balanced. These never depend on a live compiler defect.
//   - prong 3 (per-MODE env wiring, e2e): `m3_parity_no_false_abort_on_clean`
//     below keeps `CRANELISP_ALLOC_PARITY` exercised end-to-end through the
//     subprocess env plumbing that unit tests are structurally blind to.
//
// A memory-clean program — a vec build + indexed read, balanced. → 20.
const CLEAN_PROG: &str = "(defn main [] (Pure (vec-get [10 20 30] 1)))\n";

fn run_with(prog: &str, envs: &[(&str, &str)]) -> helpers::e2e::CrOutput {
    let mut b = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(prog);
    for (k, v) in envs {
        b = b.env(k, v);
    }
    b.output()
}

// M3 (parity) — the planted-imbalance fence `m3_parity_catches_planted_leak` was
// RETIRED here in S115 W3c; see the tombstone at the head of this file for the
// drained fault set, the unit-tier successor, and the surviving wiring face.

// M3 (parity) — does NOT false-fire on a clean program (byte-identical-off for a
// balanced program): CLEAN + parity exits with the correct value 20.
// spec: design/intrinsics/diagnostic-modes.md §3 M3 — no abort when balanced.
#[test]
fn m3_parity_no_false_abort_on_clean() {
    run_with(CLEAN_PROG, &[("CRANELISP_ALLOC_PARITY", "1")]).assert_exit(20);
}

// M1 (quarantine) — preserves a clean program (the mode is byte-identical-off for
// correct code; it only changes the fate of freed blocks).
// spec: design/intrinsics/diagnostic-modes.md §3 M1 — clean programs unaffected.
#[test]
fn m1_quarantine_preserves_clean_program() {
    run_with(CLEAN_PROG, &[("CRANELISP_QUARANTINE_FREED", "1")]).assert_exit(20);
}

// M2 (scrub) — preserves a clean program (scrub only poisons freed memory; a
// correct program never reads freed memory, so it is unaffected).
// spec: design/intrinsics/diagnostic-modes.md §3 M2 — clean programs unaffected.
#[test]
fn m2_scrub_preserves_clean_program() {
    run_with(CLEAN_PROG, &[("CRANELISP_SCRUB_FREED", "1")]).assert_exit(20);
}
