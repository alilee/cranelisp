// Sprint 116 M3 production compiler-child wiring. The private plant protocol is
// closed and exact; tests never call allocator internals or counter setters.
//
// ===========================================================================
// S118 W1 BASELINE RECONCILIATION (`/testing`, 2026-07-25, HEAD `e15ff20f`;
// `tests/plan/s118-test-plan.md` §2.2 obligation 2 — "is the clean control's RED
// 0848-only (flips at W2) or leak-coupled (flips only after W4)?").
// MEASUREMENT ONLY; the attribution is `/qa`'s.
//
// ANSWER: NEITHER, and specifically NOT 0848-only. `m3_parity_clean_child_exits_
// normally_control` failed because the child ABORTS on a genuine exit imbalance —
// the detector is present and WORKING, and prints:
//
//   [ALLOC_PARITY] IMBALANCE — LEAK (allocs > deallocs — blocks never freed)
//   [ALLOC_PARITY]   ALLOC_COUNT=1199 DEALLOC_COUNT=56 delta=1143
//
// So no amount of 0848 detection-proof work at W2 can flip this cell: the plant
// is absent and the report is already correct. The imbalance is the coupling.
//
// WHAT THE 1143 IS. Direct subprocess probes at this HEAD isolate it as
// PROGRAM-INDEPENDENT prelude-load residue, not this child's result value:
//
//   child program                                CRANELISP_LIB   delta
//   (Pure (sub-i64 (str-len s) 11))  [this file] stdlib/         1143
//   (Pure (sub-i64 3 3))             [trivial]   stdlib/         1143
//   (Pure (sub-i64 3 3))             [trivial]   empty prelude      0  exit 0
//   ms_p8_conj_leak's INT_LOOP / CONJ_LOOP       stdlib/         1143
//
// The identical 1143 for a trivial `Int`-returning program and for an empty
// prelude's 0 says the residue is what compiling `stdlib/prelude.cl` and its
// module closure allocates and never releases. That is NOT 0745's mechanism —
// 0745 owns the program RESULT VALUE's single reference (this child's result is
// an `Int`, and the plan's own §2.2 note anticipated "compiler-side allocation
// only") — so a W4 result-owner fix is not established to flip this cell either.
// Recorded for `/qa`: this control's flip needs the ambient prelude-load residue
// owned, and that owner is not named by 0848, 0745 or Track-B backend glue.
//
// S118 BRANCH-F RESOLUTION (`/testing`, 2026-07-26; user decision
// `sprints/SPRINT.md` §Notes 2026-07-26; plan §2.5 Branch F; FIXME 0889). The
// residue's owner is now named: the int-side macro-turn marshal boundary
// (`src/marshal.rs` marshalled argument trees never RC-decremented +
// `src/expander.rs::invoke_clause` expansion-result trees never consumed) — a
// documented by-design compile-time leak, closed form `|marshalled arg cells +
// args spine| + |non-aliased result cells|` per expansion, exactly 1143 for the
// full stdlib prelude. It is ACCEPTED for now and recovered in a future sprint;
// its magnitude is fenced by `tests/macro_turn_marshal_leak_0889.rs`.
//
// The clean control below is therefore retrofitted onto MARGINAL accounting
// (`helpers::marginal`): it now measures this child against a same-prelude,
// same-env, no-workload child and asserts the DIFFERENCE. That is what the
// detection proof actually needs from a clean control — "with no plant, nothing
// is attributed to this child" — and it is a statement about the M3 wiring
// rather than about the ambient prelude. Measured at this HEAD:
//
//   control  (Pure 0)                    ALLOC_COUNT=1198 DEALLOC_COUNT=55  residual 1143
//   subject  (Pure (sub-i64 (str-len s) 11))
//                                        ALLOC_COUNT=1199 DEALLOC_COUNT=56  residual 1143
//   MARGINAL                             allocs +1  deallocs +1  residual 0
//
// The child's own `String` local allocates once and frees once. The cell flips
// GREEN on that measurement. The plant cell above is UNCHANGED — it is the
// 0848 detection proof and stays RED until the plant lands.
// ===========================================================================

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::marginal::{Child, Instrument, MarginalPair};
use std::process::{Command, Output};

/// The production compiler child both faces of the proof use. Single-sourced so
/// the plant cell and the clean control can never drift apart.
const M3_CHILD_PROGRAM: &str = "(import [primitives [Pure str-len sub-i64]])\n\
     (defn main [] (let [s \"owned-local\"] (Pure (sub-i64 (str-len s) 11))))\n";

/// The no-workload control for the marginal clean-control cell: same prelude,
/// same env, a program that computes nothing.
const M3_AMBIENT_ONLY: &str = "(import [primitives [Pure]])\n\
     (defn main [] (Pure 0))\n";

fn child(fault: Option<&str>) -> Output {
    let td = tempfile::tempdir().expect("tempdir");
    let source = td.path().join("user.cl");
    std::fs::write(&source, M3_CHILD_PROGRAM).expect("write source");
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let binary = root.join("target/debug/cranelisp");
    let mut cmd = Command::new(binary);
    cmd.env_clear()
        .current_dir(td.path())
        .args(["--run", "user.cl", "--no-cache"])
        .env("CRANELISP_LIB", root.join("stdlib"))
        .env("CRANELISP_PLATFORM_PATH", root.join("target/debug"))
        .env("CRANELISP_ALLOC_PARITY", "1");
    if let Some(plant) = fault {
        cmd.env("CRANELISP_TEST_FAULTS", "s116-detection-proof-v1")
            .env("CRANELISP_TEST_FAULT", plant);
    }
    cmd.output().expect("run compiler child")
}

// RED — one suppressed production discharge reaches the real always-on
// counters, atexit report, then abnormal termination. Removing M3 must make this
// assertion fail rather than false-green.
// spec: design/intrinsics/diagnostic-modes.md §7.3 — M3 compiler-child
// counter→atexit→report→abort proof using the exact closed plant protocol.
// defect: class=detection-gap locus=cranelisp-intrinsics diagnostics production wiring — M3Leak plant/e2e atexit proof absent (0848 R-1) found=S115 owner=/dev
#[test]
fn m3_parity_catches_injected_imbalance() {
    let out = child(Some("M3Leak"));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !out.status.success(),
        "M3 leak child MUST abort non-zero; stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("M3Leak")
            && stderr.contains("alloc")
            && stderr.contains("dealloc")
            && (stderr.contains("parity") || stderr.contains("imbalance")),
        "atexit report MUST name plant and alloc/dealloc imbalance; stderr:\n{stderr}"
    );
}

// GREEN control — parity enabled WITHOUT a plant attributes nothing to this
// child. That is the discrimination the proof above needs: the plant cell shows
// the detector fires on an injected imbalance, and this cell shows it does not
// otherwise fire on anything this child does.
//
// Stated MARGINALLY (see the header): the clean child's alloc-parity ledger is
// compared to a same-prelude, same-env child with no workload, and the
// difference must be exactly zero — nothing this child allocates survives it,
// and it over-frees nothing either. The ambient FIXME-0889 macro-turn residual
// is present in both ledgers and cancels; it is not this child's, not 0848's,
// and not 0745's. The two `is_some()` legs preserve the original "exits
// normally" contract in the only form that is checkable while 0889 stands, and
// they tighten back to it automatically once 0889 lands (both children then exit
// 0 and the second leg asserts it).
// spec: design/intrinsics/diagnostic-modes.md §7.3 — clean M3 child control.
#[test]
fn m3_parity_clean_child_exits_normally_control() {
    let m = MarginalPair::new(
        "the clean M3 child's own allocation over a no-workload child",
        Child::new(M3_AMBIENT_ONLY).use_workspace_stdlib_for_stdlib_conformance_only(),
        Child::new(M3_CHILD_PROGRAM).use_workspace_stdlib_for_stdlib_conformance_only(),
    )
    .instrument(Instrument::AllocParity)
    .measure();

    m.assert_balanced(
        "the clean M3 child MUST contribute nothing to the armed detector's ledger — \
         with no plant, the detector must attribute no imbalance to this child.",
    );
    assert!(
        !m.subject().stderr.contains("M3Leak") && !m.control().stderr.contains("M3Leak"),
        "no plant was armed, so no report may name one.\n{}\n--- subject stderr ---\n{}",
        m.report(),
        m.subject().stderr
    );
    assert_eq!(
        m.subject().exit_code().is_some(),
        m.control().exit_code().is_some(),
        "the clean M3 child MUST NOT change WHETHER the armed detector aborts \
         relative to a child that does no work at all.\n{}",
        m.report()
    );
    if m.control().exit_code().is_some() {
        // The ambient imbalance is gone (0889 fixed) — the original contract.
        assert_eq!(
            m.subject().exit_code(),
            Some(0),
            "with the ambient imbalance gone, the clean M3 child must exit normally.\n{}",
            m.report()
        );
    }
}
