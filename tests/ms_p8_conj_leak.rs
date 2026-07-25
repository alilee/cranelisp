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
// this pin uses the ONE sanctioned stdlib touchpoint. The int-loop control balances.
// BOTH-POLARITY fence (the S110-8/S111-2 inversion lesson): the fix must make
// allocs==deallocs EXACTLY — it must not over-correct into an under-count.
//
// ===========================================================================
// S118 W1 BASELINE RECONCILIATION (`/testing`, 2026-07-25, HEAD `e15ff20f`;
// `tests/plan/s118-test-plan.md` §2.2 obligation 1). MEASUREMENT ONLY —
// attribution is `/qa`'s and no `// defect:` line below is changed here.
//
// ALL THREE cells in this file are RED, including the control twin
// `int_loop_control_balances_green`. So the §2.1 enumeration's `conj` family is
// THREE names, not two, and its arithmetic trades against
// `match_owned_temporary_scrutinee_0810::var_pattern_arm_consuming_owned_temporary_releases_it_once_linked`
// (enumerated cell #10, defect 0782), which is GREEN at this HEAD — NOT against
// the M3 clean control #23, which is also RED (see
// `intrinsics_m3_detection_s116.rs`). 28 lands exactly.
//
// WHAT THE THREE REDS ACTUALLY MEASURE. Focused per-binary runs at this HEAD:
//
//   conj loop  (CONJ_LOOP, RC_STATS)   allocs=1219 deallocs=76  residual=1143
//   int  loop  (INT_LOOP,  RC_STATS)   allocs=1198 deallocs=55  residual=1143
//
// The residuals are IDENTICAL. Direct subprocess probes isolate the 1143: it is
// program-independent and appears for ANY `--run` program whenever
// `CRANELISP_LIB` points at the real `stdlib/` (its `prelude.cl` and the module
// closure that prelude pulls in); with an EMPTY prelude directory the same child
// balances exactly and exits 0. Consequences for the flip accounting:
//
//   (a) the int-loop control is RED on that ambient prelude-load residue alone —
//       it has no persistent-collection op to leak, and it never did;
//   (b) the conj loop's MARGINAL residue over the control is ZERO (1219-1198=21
//       allocs against 76-55=21 deallocs). The 1-Vec-per-iteration signature the
//       header documents (allocs=22 / deallocs=2) is NOT what these cells read
//       today; whether the 0688 TCO-supersede leak was cured by S116/S117 or is
//       merely masked by the ambient term is an attribution question for `/qa`
//       (plan §4.4: `conj` cells are VERIFIED consequents, and a residual RED
//       after W3 is a NEW attribution, never a re-threshold);
//   (c) none of the three can flip on a Track-B backend change alone — the
//       ambient prelude-load term has to go first, and it is larger than, and
//       independent of, 0745's program-RESULT value.
// ===========================================================================

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;
use std::time::Duration;

// Parse `allocs=N` / `deallocs=N` from the `[RC_STATS]` line.
fn rc_alloc_dealloc(stderr: &str) -> (i64, i64) {
    let line = stderr
        .lines()
        .find(|l| l.contains("[RC_STATS]"))
        .unwrap_or_else(|| panic!("no [RC_STATS] line:\n{stderr}"));
    let field = |k: &str| -> i64 {
        line.split_whitespace()
            .find_map(|t| t.strip_prefix(k).and_then(|v| v.parse().ok()))
            .unwrap_or_else(|| panic!("no {k} in: {line}"))
    };
    (field("allocs="), field("deallocs="))
}

const CONJ_LOOP: &str = "(import [collections.vec [conj count]])\n\
     (import [primitives [add-i64 eq-i64 Pure]])\n\
     (defn go [n v] (if (eq-i64 n 0) v (go (add-i64 n -1) (conj v n))))\n\
     (defn main [] (Pure (count (go 20 [0]))))\n";

const INT_LOOP: &str = "(import [primitives [add-i64 eq-i64 Pure]])\n\
     (defn go [n acc] (if (eq-i64 n 0) acc (go (add-i64 n -1) (add-i64 acc 1))))\n\
     (defn main [] (Pure (go 20 0)))\n";

fn run_stdlib(src: &str, env: &[(&str, &str)]) -> helpers::e2e::CrOutput {
    let mut b = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .file("main.cl", src)
        .run("main.cl")
        .timeout(Duration::from_secs(90));
    for (k, v) in env {
        b = b.env(k, v);
    }
    b.output()
}

// MS-P8 pin — the conj loop MUST NOT leak: allocs == deallocs (BOTH-polarity fence).
// Today the persistent-op path leaks 1 Vec per iteration (allocs=22 / deallocs=2).
// spec: spec/12-runtime.md §12.3.1 — a superseded persistent-collection value is
// freed when no longer reachable.
// defect: class=rc-miscount locus=crates/cranelisp-backend TCO tail-jump loop-param slot overwrite — superseded heap param never released (0688 verdict a; conj copy path is the exposure, not the seam) found=S113 owner=/dev
#[test]
fn conj_loop_does_not_leak() {
    let out = run_stdlib(CONJ_LOOP, &[("CRANELISP_RC_STATS", "1")]);
    let (allocs, deallocs) = rc_alloc_dealloc(&out.stderr);
    assert_eq!(
        allocs, deallocs,
        "the conj loop MUST balance allocs/deallocs (no leak, no under-count — both \
         polarities); the persistent-op path leaks the superseded Vec each \
         iteration: allocs={allocs} deallocs={deallocs}.\nstderr:\n{}",
        out.stderr
    );
}

// MS-P8 parity face — the conj loop under ALLOC_PARITY must NOT abort (a balanced
// program passes the atexit parity check). `(count (go 20 [0]))` = 21.
// spec: spec/12-runtime.md §12.3.1 — a balanced program passes the alloc-parity check.
// defect: class=rc-miscount locus=crates/cranelisp-backend TCO tail-jump loop-param slot overwrite — superseded heap param never released (0688 verdict a; conj copy path is the exposure, not the seam) found=S113 owner=/dev
#[test]
fn conj_loop_parity_no_abort() {
    run_stdlib(CONJ_LOOP, &[("CRANELISP_ALLOC_PARITY", "1")]).assert_exit(21);
}

// MS-P8 CONTROL TWIN — the SAME loop shape threading an INT accumulator (no
// persistent-collection op). It was authored GREEN as the standalone twin
// isolating the conj/assoc RC path as the leak's locus.
//
// S118 W1: this cell is RED and is the third `conj`-family member of the 28-name
// baseline (header §"S118 W1 BASELINE RECONCILIATION"). It reads residual=1143
// — byte-for-byte the same ambient prelude-load residue the `conj` cell reads —
// so as of this HEAD it is NOT a control for the persistent-op path: it is a
// second reading of the ambient term. It stays un-`#[ignore]`d and asserts the
// same unconditional contract; its assertion is spec-correct and the residue it
// reports is a real leak. `/qa` owns the attribution and the flip wave; no
// `// defect:` line is asserted here because naming class/locus/owner for the
// ambient term is that attribution, not this measurement.
// spec: spec/12-runtime.md §12.3.1 — an int-accumulator loop allocates nothing to leak.
#[test]
fn int_loop_control_balances_green() {
    let out = run_stdlib(INT_LOOP, &[("CRANELISP_RC_STATS", "1")]);
    let (allocs, deallocs) = rc_alloc_dealloc(&out.stderr);
    assert_eq!(
        allocs, deallocs,
        "the int-loop control MUST balance (no persistent-collection op to leak): \
         allocs={allocs} deallocs={deallocs}.\nstderr:\n{}",
        out.stderr
    );
    run_stdlib(INT_LOOP, &[("CRANELISP_ALLOC_PARITY", "1")]).assert_exit(20);
}
