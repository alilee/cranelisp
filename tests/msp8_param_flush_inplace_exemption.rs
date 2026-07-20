// msp8_param_flush_inplace_exemption.rs — the two W4 (f9435b37) landed regressions
// in the MS-P8 param flush's in-place-COW exemption
// (`crates/cranelisp-backend/src/compiler/fn_compiler.rs::flush_superseded_heap_params_before_tail_jump`).
//
// The exemption skips the tail-jump dec of a superseded heap loop-param when an
// in-place `vec-set`/`vec-push` on that param may forward the param's OWN box.
// The W4 landing scoped it two ways wrong:
//
//  - FIXME 0691 (BLOCKER, UAF): the exemption was POSITIONAL-only — it checked
//    only the arg at the param's OWN slot. An in-place COW on `v` feeding a
//    DIFFERENT slot while `v`'s slot takes a fresh value classified `v`
//    superseded and dec'd it, freeing the box the mutate branch forwarded
//    (use-after-free, analysis-ON only). Fix: scan ALL args.
//  - FIXME 0695 (leak): under `CRANELISP_NO_OWNERSHIP` the COW always copies
//    (rc≥2 force-count) so nothing is carried forward in place — yet the
//    exemption still skipped the dec (1 leak/iter). Fix: the exemption does not
//    apply toggle-off.
//
// Both are BOTH-POLARITY fenced: the fix must not over-correct into an
// under-count (the S110-8/S111-2 inversion lesson). Free-standing (PrimitivesOnly,
// no stdlib).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn run_prims(src: &str, env: &[(&str, &str)]) -> helpers::e2e::CrOutput {
    let mut b = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(src);
    for (k, v) in env {
        b = b.env(k, v);
    }
    b.output()
}

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

// ── FIXME 0691 — cross-position in-place COW (UAF) ──────────────────────────
//
// `(vec-set v 0 n)` forwards `v`'s box into slot 0 (param `a`) while `v`'s OWN
// slot (position 1) takes a FRESH value `[1 2 3]`. The positional-only exemption
// missed the COW (it sat at position 0, not `v`'s position 1), dec'd `v`, and
// freed the carried box. The base case returns `(vec-get a 0)` = 1.
const CROSS_POSITION_UAF: &str = "(defn go [a v n]\n\
     (if (eq-i64 n 0)\n\
         (Pure (vec-get a 0))\n\
         (go (vec-set v 0 n) [1 2 3] (add-i64 n -1))))\n\
     (defn main [] (go [9 9] [5 5] 3))\n";

// 0691 pin — analysis-ON MUST return the correct value 1, deterministically.
// Before f9435b37's regression fix this returned nondeterministic garbage
// (exit 171/170/152/18…) — the forwarded box freed at the tail jump and its
// address immediately re-allocated (a UAF).
// spec: spec/12-runtime.md §12.3.1 — a heap value still reachable (carried
// forward into another slot) MUST NOT be freed.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::flush_superseded_heap_params_before_tail_jump (positional-only in-place-COW exemption freed a box a DIFFERENT slot forwarded) found=S114 owner=/dev
#[test]
fn cross_position_inplace_cow_no_uaf_analysis_on() {
    run_prims(CROSS_POSITION_UAF, &[]).assert_exit(1);
}

// 0691 BOTH-POLARITY oracle (born-GREEN) — the toggle-off path always COPIES
// (never forwards in place), so it computed the correct value 1 all along. The
// analysis-ON face above must converge on this oracle.
// spec: spec/12-runtime.md §12.3.1 — the conservative all-Owned lowering is the
// differential oracle for the value.
#[test]
fn cross_position_inplace_cow_oracle_toggle_off_green() {
    run_prims(CROSS_POSITION_UAF, &[("CRANELISP_NO_OWNERSHIP", "1")]).assert_exit(1);
}

// ── FIXME 0695 — in-place COW × toggle-off (leak) ───────────────────────────
//
// `(vec-set v 0 n)` on param `v` in its OWN position. Under toggle-off the COW
// always copies, so each iteration's old `v` is superseded by a fresh box and
// its slot reference is owed a dec — which the exemption wrongly skipped. `go`
// returns the Int and `main` wraps `Pure`, isolating the persistent-op RC path
// from the entry-return teardown (the same shape the balanced conj loop uses).
const INPLACE_COW_LOOP: &str = "(defn go [v n]\n\
     (if (eq-i64 n 0)\n\
         (vec-get v 0)\n\
         (go (vec-set v 0 n) (add-i64 n -1))))\n\
     (defn main [] (Pure (go [5 5] 3)))\n";

// 0695 pin — under `CRANELISP_NO_OWNERSHIP` the loop MUST balance exactly. Before
// the fix the exemption skipped the superseded-param dec on the copy path: 1 leak
// per iteration (allocs=5 deallocs=2 at 3 iterations). BOTH-polarity fence.
// spec: spec/12-runtime.md §12.3.1 — a superseded persistent-collection value is
// freed when no longer reachable.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::flush_superseded_heap_params_before_tail_jump (in-place-COW exemption applied toggle-off where the copy path always supersedes the param) found=S114 owner=/dev
#[test]
fn inplace_cow_loop_no_leak_toggle_off() {
    let out = run_prims(
        INPLACE_COW_LOOP,
        &[("CRANELISP_NO_OWNERSHIP", "1"), ("CRANELISP_RC_STATS", "1")],
    );
    let (allocs, deallocs) = rc_alloc_dealloc(&out.stderr);
    assert_eq!(
        allocs, deallocs,
        "toggle-off in-place-COW loop MUST balance (no leak, no under-count): \
         allocs={allocs} deallocs={deallocs}.\nstderr:\n{}",
        out.stderr
    );
}

// 0695 BOTH-POLARITY control (GREEN) — analysis-ON the same loop reuses the box
// in place (`reuse_hit=3`), so the exemption is doing its correct analysis-ON job
// and the loop balances. The exemption must be preserved for this polarity.
// spec: spec/12-runtime.md §12.3.3 — Vec copy-on-write reuses a uniquely-owned
// backing in place.
#[test]
fn inplace_cow_loop_reuse_preserved_analysis_on_green() {
    let out = run_prims(INPLACE_COW_LOOP, &[("CRANELISP_RC_STATS", "1")]);
    let (allocs, deallocs) = rc_alloc_dealloc(&out.stderr);
    assert_eq!(
        allocs, deallocs,
        "analysis-ON in-place-COW loop MUST balance (in-place reuse): \
         allocs={allocs} deallocs={deallocs}.\nstderr:\n{}",
        out.stderr
    );
    assert!(
        out.stderr.contains("reuse_hit=3"),
        "analysis-ON MUST preserve in-place reuse (reuse_hit=3):\n{}",
        out.stderr
    );
}
