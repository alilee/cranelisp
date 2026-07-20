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

// MS-P8 CONTROL TWIN (GREEN) — the SAME loop shape threading an INT accumulator
// (no persistent-collection op) balances under RC_STATS and passes parity. The
// standalone twin isolating the conj/assoc RC path as the leak's locus.
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
