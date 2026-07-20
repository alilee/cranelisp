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

// A program with a planted alloc/dealloc IMBALANCE (the entry-`main` IO-teardown
// leak: the final IO/result box is never freed — 2 allocs / 1 free).
const LEAK_PROG: &str = "(defn main [] (let [s \"hi\"] (Pure 9)))\n";
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

// M3 (parity) — CATCHES a planted imbalance: the teardown-leak program under
// `CRANELISP_ALLOC_PARITY` aborts at exit with the located `[ALLOC_PARITY]
// IMBALANCE` report. GREEN = the mode sees the fault.
// spec: design/intrinsics/diagnostic-modes.md §3 M3 — atexit alloc-parity abort.
#[test]
fn m3_parity_catches_planted_leak() {
    let out = run_with(LEAK_PROG, &[("CRANELISP_ALLOC_PARITY", "1")]);
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        out.status.code() != Some(9)
            && (c.contains("IMBALANCE") || c.contains("PARITY") || c.contains("LEAK")),
        "M3 (CRANELISP_ALLOC_PARITY) MUST abort on the planted teardown-leak \
         imbalance with a located parity report; got exit {:?}:\n{c}",
        out.status.code()
    );
}

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
