// adt_wrapped_supersede_leak_0720.rs — S114 Phase-6b, FIXME 0720 pin batch.
//
// The exemplar's full solve leaks ~11.8k objects/solve (allocs≠deallocs). /qa's
// RC_TRACE per-pointer reconciliation (43,683 events): 11,772 of the 11,823 leaked
// are allocated then NEVER inc'd, dec'd, or freed (born rc=1, dropped) — a genuine
// never-freed face, NOT an accounting artifact.
//
// The W4 MS-P8 fix released the BARE heap loop-param at the TCO tail-jump; it does
// NOT cover the ADT-WRAPPED loop-param — the exemplar's `set-cell` shape
// (match-extract → COW vec-set → re-wrap in the ADT → supersede). The minimal
// scaling repro below (an ADT `Gr` wrapping a `cells` vec, superseded in a tail
// loop) leaks BOTH the superseded `Gr` box AND its `cells` vec every iteration:
// N=200 → allocs=403 deallocs=2 (residue 401); N=400 → allocs=803 deallocs=2
// (residue 801) — 2 leaked objects/iteration, scaling with N (~5.9k supersedes × 2
// ≈ 11.8k/solve, serial ≡ parallel; no concurrency). The BARE-vec twin of the same
// loop balances exactly (the GREEN control). Fix = S115 backend (MS-P8 sibling —
// the tail-jump superseded-param release keyed on "heap loop-param", not the vec
// shape), folded with §11-item-4's entry-return leak into ONE RC-release sweep.
//
// Serial (CRANELISP_NO_LENIENT=1 — the loop has no sparks; belt-and-suspenders for
// the RC-test-runs-serially convention). PrimitivesOnly, no stdlib.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// The ADT-WRAPPED COW supersede tail loop, parameterised on N. `go` threads a `Gr`,
// each iteration COW-sets `cells[0]` then re-wraps in a fresh `Gr` (superseding the
// old one), and the base reads `cells[0]` (forcing the chain observable).
fn adt_wrapped_loop(n: usize) -> String {
    format!(
        "(deftype G2 (Gr [cells]))\n\
         (defn set0 [g m] (match g [(Gr cells) (Gr (vec-set cells 0 m))]))\n\
         (defn go [g m] (if (eq-i64 m 0) (match g [(Gr cells) (vec-get cells 0)]) (go (set0 g m) (add-i64 m -1))))\n\
         (defn main [] (Pure (go (Gr [5 5]) {n})))\n"
    )
}

fn rc_alloc_dealloc(src: &str) -> (i64, i64) {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(src)
        .env("CRANELISP_RC_STATS", "1")
        .env("CRANELISP_NO_LENIENT", "1")
        .output();
    let line = out
        .stderr
        .lines()
        .find(|l| l.contains("[RC_STATS]"))
        .unwrap_or_else(|| panic!("no [RC_STATS] line:\n{}", out.stderr));
    let field = |k: &str| -> i64 {
        line.split_whitespace()
            .find_map(|t| t.strip_prefix(k).and_then(|v| v.parse().ok()))
            .unwrap_or_else(|| panic!("no {k} in: {line}"))
    };
    (field("allocs="), field("deallocs="))
}

// Small allowance for the O(1) live-at-exit residue (the returned scalar's box
// chain) — the leak we pin scales with N and dwarfs this.
const SMALL_CONST: i64 = 8;

// 0720 pin 1 (RED) — the ADT-wrapped supersede loop MUST NOT leak: the at-exit
// residue (allocs − deallocs) must be a small O(1) constant, NOT ~2·N. Today at
// N=200 the residue is 401 (allocs=403 deallocs=2) — every superseded `Gr` box AND
// its cells vec leaks. Flips with the S115 backend ADT-wrapped-param release.
// spec: spec/12-runtime.md §12.3.1 — a superseded heap value (the old `Gr` box and
// its cells vec) is freed when no longer reachable.
// defect: class=rc-miscount locus=crates/cranelisp-backend TCO tail-jump superseded-param release — ADT-wrapped loop param never released (MS-P8 sibling; bare-vec face fixed W4) found=S114 owner=/dev
#[test]
fn adt_wrapped_supersede_loop_does_not_leak() {
    let (allocs, deallocs) = rc_alloc_dealloc(&adt_wrapped_loop(200));
    let residue = allocs - deallocs;
    assert!(
        residue <= SMALL_CONST,
        "ADT-wrapped supersede loop (N=200) MUST NOT leak: residue = allocs − \
         deallocs = {allocs} − {deallocs} = {residue}, expected ≤ {SMALL_CONST}. \
         The superseded `Gr` box and its cells vec leak every iteration."
    );
}

// 0720 pin 2 (RED) — the residue MUST NOT SCALE with N: the never-freed face is a
// per-iteration leak, so residue(N=400) − residue(N=200) is ~2·200 today (801 −
// 401 = 400). A correct release makes the residue N-independent (both ~O(1)).
// spec: spec/12-runtime.md §12.3.1 — per-iteration superseded values are freed, so
// at-exit residue is O(1) in the iteration count.
// defect: class=rc-miscount locus=crates/cranelisp-backend TCO tail-jump superseded-param release — ADT-wrapped loop param never released (residue scales 2/iteration) found=S114 owner=/dev
#[test]
fn adt_wrapped_supersede_residue_does_not_scale_with_n() {
    let (a200, d200) = rc_alloc_dealloc(&adt_wrapped_loop(200));
    let (a400, d400) = rc_alloc_dealloc(&adt_wrapped_loop(400));
    let growth = (a400 - d400) - (a200 - d200);
    assert!(
        growth <= SMALL_CONST,
        "ADT-wrapped supersede residue MUST NOT scale with N: residue(400) − \
         residue(200) = {} − {} = {growth}, expected ≤ {SMALL_CONST}. Today it \
         grows ~2 objects/iteration (the superseded `Gr` + cells vec).",
        a400 - d400,
        a200 - d200
    );
}

// 0720 CONTROL (GREEN) — the BARE-vec twin of the SAME supersede loop (no ADT wrap)
// balances exactly (allocs == deallocs). Proves the leak is specific to the
// ADT-wrapped loop-param, not the supersede loop shape — the W4 MS-P8 fix covers
// this bare face. Must stay green; guards the fix from over-correcting into an
// under-count on the bare path.
// spec: spec/12-runtime.md §12.3.1 — a bare superseded heap loop-param is freed at
// the tail jump (the W4 MS-P8 fix).
#[test]
fn bare_vec_supersede_loop_balances_green() {
    let bare = "(defn set0 [cells m] (vec-set cells 0 m))\n\
         (defn go [cells m] (if (eq-i64 m 0) (vec-get cells 0) (go (set0 cells m) (add-i64 m -1))))\n\
         (defn main [] (Pure (go [5 5] 200)))\n";
    let (allocs, deallocs) = rc_alloc_dealloc(bare);
    assert_eq!(
        allocs, deallocs,
        "the bare-vec supersede twin MUST balance (the W4 MS-P8 bare-face fix): \
         allocs={allocs} deallocs={deallocs}."
    );
}
