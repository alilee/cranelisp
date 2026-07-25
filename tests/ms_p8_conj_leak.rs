// ms_p8_conj_leak.rs — MS-P8 (S113, /port ALLOC_PARITY finding).
//
// The tier-5 diagnostic modes (W5a) DETECTED a real latent leak in the exemplar on
// first contact: 1 Vec leaked per `conj`/`assoc` iteration (25,461 surviving in the
// solver). The superseded/temporary Vec on the persistent-op RC path is never dec'd
// to zero — a LEAK (bounded, non-corrupting: QUARANTINE+SCRUB clean ⇒ no UAF).
//
// SEAM (FIXME 0688, /qa 2026-07-20 — RC_TRACE-discriminated; s114-test-plan §2.1):
// verdict (a) BACKEND — the missing release is at the TCO tail-jump slot
// overwrite. `main::go`'s recur arm incs the old `v` (arg-pass), calls `conj`,
// then `jump block1(...)` overwriting the param slot with the fresh box and
// NEVER dec'ing the superseded value's slot reference — the PARAM sibling of the
// §13.3 B3.1a let-scope dead-block leak (`flush_let_scopes_before_tail_jump`
// covers `let` bindings only). conj's copy arm DOES emit its source release
// (atomic_rmw sub + drop-glue), so the copy-branch-polarity and
// intrinsics-non-accounting hypotheses are REFUTED — the conj copy path is the
// exposure, not the seam. Owner /dev(backend) — NO intrinsics deployment.
// `class=rc-miscount` (leak polarity).
//
// The leak is specific to the stdlib persistent collection verbs (`conj`/`count` —
// the COW/persistent path), NOT the primitive `vec-push` (which reuses in-place), so
// this pin uses the ONE sanctioned stdlib touchpoint. BOTH-POLARITY fence (the
// S110-8/S111-2 inversion lesson): the fix must make allocs==deallocs EXACTLY —
// it must not over-correct into an under-count.
//
// ===========================================================================
// S118 BRANCH-F RETROFIT — MARGINAL ACCOUNTING (`/testing`, 2026-07-26;
// user decision `sprints/SPRINT.md` §Notes 2026-07-26; `tests/plan/s118-test-plan.md`
// §2.5 Branch F; FIXME 0889).
//
// WHY THESE CELLS CHANGED SHAPE. Until this change-set all three asserted
// ABSOLUTE balance (`allocs == deallocs`) on a stdlib-prelude `--run` child. The
// S118 W1 baseline measurement and the Branch-F probe showed that assertion was
// not measuring any of these cells' named contracts:
//
//   conj loop  (CONJ_LOOP, RC_STATS)   allocs=1219 deallocs=76  residual=1143
//   int  loop  (INT_LOOP,  RC_STATS)   allocs=1198 deallocs=55  residual=1143
//   trivial `(defn main [] (Pure 0))`  allocs=1198 deallocs=55  residual=1143
//
// The residual is byte-identical across a persistent-collection workload, an
// int-accumulator workload, and NO workload at all: it is a program-independent
// compile-time leak at the int-side macro-turn marshal boundary (marshalled
// argument trees never RC-decremented; expansion-result trees never consumed —
// FIXME 0889, closed form `|marshalled arg cells + args spine| + |non-aliased
// result cells|` per expansion, 1143 for the full stdlib prelude). The three
// cells were reading that number and nothing else.
//
// The cells now assert their named contract on the MARGINAL residual
// (subject − control) via `helpers::marginal`. Every term common to both
// children — prelude load, macro expansion, the 0889 residual — cancels, and
// what survives is exactly the workload's own accounting. This is instrument
// truthfulness, not a threshold: the marginal has no slack to absorb a new leak,
// and it stays valid unchanged after 0889 is fixed (the common term simply goes
// to zero).
//
// MEASURED AT THIS HEAD (2026-07-26, `c8cee45e` + this change-set):
//
//   cell                         control                subject      marginal
//   int_loop_control_balances…   trivial `(Pure 0)`     INT_LOOP     allocs +0  deallocs +0  residual 0
//   conj_loop_does_not_leak      INT_LOOP               CONJ_LOOP    allocs +21 deallocs +21 residual 0
//   conj_loop_parity_no_abort    INT_LOOP               CONJ_LOOP    allocs +21 deallocs +21 residual 0
//
// All three flip GREEN, and they flip on a real measurement: the conj workload
// allocates 21 blocks over 20 iterations and frees all 21.
//
// WHAT THIS DOES **NOT** SETTLE (plan §2.1 / §2.2.1 — the question stays open).
// The 0688 signature these cells were enumerated under (allocs=22 / deallocs=2
// — one Vec leaked per iteration) is ABSENT at this HEAD, and the marginal now
// proves that absence rather than merely failing to see it under a 1143-wide
// ambient term. But absence is not closure: whether 0688 was cured by an
// S116/S117 change-set or whether this cell shape stopped reaching the TCO
// tail-jump seam is UNRESOLVED, and it is the same S98 suspicious-green kind as
// plan §2.6. The `// defect:` lines below therefore stand as written — a GREEN
// marginal here does NOT retire 0688's attribution, and `/qa` owns tracing it to
// a mechanism before the family is called closed.
//
// The 0889 leak itself is NOT closed by this change-set either. It is accepted
// for now by user decision and recovered in a future sprint; its magnitude is
// fenced by the exact-value pins in `tests/macro_turn_marshal_leak_0889.rs`.
// ===========================================================================

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::marginal::{Child, Instrument, MarginalPair};
use std::time::Duration;

/// The no-workload control: same prelude, same env, a program that computes
/// nothing. Its residual IS the ambient 0889 term and nothing else.
const AMBIENT_ONLY: &str = "(import [primitives [Pure]])\n\
     (defn main [] (Pure 0))\n";

const CONJ_LOOP: &str = "(import [collections.vec [conj count]])\n\
     (import [primitives [add-i64 eq-i64 Pure]])\n\
     (defn go [n v] (if (eq-i64 n 0) v (go (add-i64 n -1) (conj v n))))\n\
     (defn main [] (Pure (count (go 20 [0]))))\n";

const INT_LOOP: &str = "(import [primitives [add-i64 eq-i64 Pure]])\n\
     (defn go [n acc] (if (eq-i64 n 0) acc (go (add-i64 n -1) (add-i64 acc 1))))\n\
     (defn main [] (Pure (go 20 0)))\n";

/// Every child here compiles against the workspace `stdlib/` — the persistent
/// collection verbs are the subject and they live nowhere else (the ONE
/// sanctioned stdlib touchpoint, root `CLAUDE.md` §"Stdlib separation").
fn stdlib_child(src: &str) -> Child {
    Child::new(src).use_workspace_stdlib_for_stdlib_conformance_only()
}

fn pair(label: &str, control: &str, subject: &str) -> MarginalPair {
    MarginalPair::new(label, stdlib_child(control), stdlib_child(subject))
        .timeout(Duration::from_secs(120))
}

// MS-P8 pin — the conj loop MUST NOT leak. Stated marginally against the SAME
// loop shape threading an `Int` accumulator, so the subtraction charges this
// cell with exactly the persistent-collection workload: the `collections.vec`
// import, the `[0]` literal, and 20 `conj` iterations. A returning 0688 (one Vec
// leaked per iteration) shows up here as a marginal residual of ~20; the 0889
// ambient term cannot show up here at all.
// spec: spec/12-runtime.md §12.3.1 — a superseded persistent-collection value is
// freed when no longer reachable.
// defect: class=rc-miscount locus=crates/cranelisp-backend TCO tail-jump loop-param slot overwrite — superseded heap param never released (0688 verdict a; conj copy path is the exposure, not the seam) found=S113 owner=/dev
#[test]
fn conj_loop_does_not_leak() {
    let m = pair(
        "conj workload over the int-accumulator twin",
        INT_LOOP,
        CONJ_LOOP,
    )
    .measure();
    m.assert_balanced(
        "the conj loop MUST balance allocs/deallocs (no leak, no under-count — both \
         polarities). Measured marginally against the int-accumulator twin, so the \
         quantity asserted is what the persistent-op path itself allocated and \
         failed to free.",
    );
    assert_eq!(
        m.subject().exit_code(),
        Some(21),
        "the conj program's own value must still be produced — `(count (go 20 [0]))` = 21.\n{}",
        m.report()
    );
}

// MS-P8 parity face — the SAME marginal read through the M3 detector's atexit
// path (`CRANELISP_ALLOC_PARITY`) rather than the `[RC_STATS]` report, because a
// detector can disagree with a counter report and the cell is named after the
// detector. Under FIXME 0889 both children abort on the ambient imbalance, so
// "no abort" is stated as what it actually means here: the conj workload does
// not change the armed detector's verdict, and contributes zero to the
// imbalance it reports. When 0889 lands, both children reach normal exit and the
// second assertion below tightens back to the original `exit 21` contract with
// no edit.
// spec: spec/12-runtime.md §12.3.1 — a balanced program passes the alloc-parity check.
// defect: class=rc-miscount locus=crates/cranelisp-backend TCO tail-jump loop-param slot overwrite — superseded heap param never released (0688 verdict a; conj copy path is the exposure, not the seam) found=S113 owner=/dev
#[test]
fn conj_loop_parity_no_abort() {
    let m = pair(
        "conj workload under the armed M3 detector",
        INT_LOOP,
        CONJ_LOOP,
    )
    .instrument(Instrument::AllocParity)
    .measure();
    m.assert_balanced(
        "the conj loop MUST contribute nothing to the armed alloc-parity detector's \
         imbalance — the workload neither leaks into nor over-frees out of the \
         detector's ledger.",
    );
    assert_eq!(
        m.subject().exit_code().is_some(),
        m.control().exit_code().is_some(),
        "the conj workload MUST NOT change WHETHER the armed detector aborts: the \
         control and subject children must reach the same kind of exit.\n{}",
        m.report()
    );
    if m.control().exit_code().is_some() {
        // The ambient imbalance is gone (0889 fixed) — both children exit
        // normally and the program's value is observable under arming again.
        assert_eq!(
            m.subject().exit_code(),
            Some(21),
            "with the ambient imbalance gone, the armed conj child must exit with the \
             program's value 21.\n{}",
            m.report()
        );
    }
}

// MS-P8 CONTROL TWIN — the SAME loop shape threading an INT accumulator (no
// persistent-collection op). It is the standalone twin isolating the conj/assoc
// RC path as the leak's locus, and it is also the CONTROL side of both cells
// above, so its own contract has to hold independently: an int-accumulator loop
// allocates nothing to leak.
//
// Measured against the no-workload child it is marginally EXACT — `allocs +0
// deallocs +0` over 20 iterations, i.e. the int loop touches the heap zero
// times. The assertion stays on the residual (the named contract is balance, not
// zero-allocation), and `allocs` is reported in the failure message so a future
// drift into heap traffic is visible the moment the residual moves.
//
// The armed-detector face for this loop is covered as the CONTROL side of
// `conj_loop_parity_no_abort` — not duplicated here.
// spec: spec/12-runtime.md §12.3.1 — an int-accumulator loop allocates nothing to leak.
#[test]
fn int_loop_control_balances_green() {
    let m = pair(
        "int-accumulator loop over the no-workload child",
        AMBIENT_ONLY,
        INT_LOOP,
    )
    .measure();
    m.assert_balanced(
        "the int-loop control MUST balance (no persistent-collection op to leak), \
         measured against a same-prelude child with no workload at all.",
    );
    assert_eq!(
        m.subject().exit_code(),
        Some(20),
        "the int-loop program's own value must still be produced — `(go 20 0)` = 20.\n{}",
        m.report()
    );
}
