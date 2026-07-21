// adt_wrapped_supersede_leak_0720.rs — S114 Phase-6b, FIXME 0720 pin batch.
// UPGRADED S115 W3c (FIXME 0763): the pins now assert EXACT balance in BOTH
// ownership-toggle states; the defect is FIXED.
//
// History. The exemplar's full solve leaked ~11.8k objects/solve (allocs≠deallocs).
// /qa's RC_TRACE per-pointer reconciliation (43,683 events) showed 11,772 of the
// 11,823 leaked were allocated then NEVER inc'd, dec'd, or freed (born rc=1,
// dropped) — a genuine never-freed face, NOT an accounting artifact.
//
// The S114 W4 MS-P8 fix released the BARE heap loop-param at the TCO tail-jump; it
// did NOT cover the ADT-WRAPPED loop-param — the exemplar's `set-cell` shape
// (match-extract → COW vec-set → re-wrap in the ADT → supersede). The minimal
// scaling repro below (an ADT `Gr` wrapping a `cells` vec, superseded in a tail
// loop) leaked BOTH the superseded `Gr` box AND its `cells` vec every iteration:
// N=200 → allocs=403 deallocs=2 (residue 401); N=400 → allocs=803 deallocs=2
// (residue 801) — 2 leaked objects/iteration, scaling with N.
//
// FIXED in the S115 W3/W3b backend RC-release sweep (ONE type-directed
// `emit_typed_rc_dec`). The face is now EXACT at every N in both toggles —
// N=1 5/5, N=2 7/7, N=200 403/403, N=400 803/803 — so these pins assert exact
// equality rather than the weaker "residue does not scale" property that was all
// the leaking tree could support. Exactness is what spec §12.3.1 actually
// requires, and it is the only assertion that also catches the opposite-polarity
// regression (an over-correction into a premature free / under-count).
//
// Sibling batch: `tests/rc_escape_release_0763.rs` (the escaping-fresh-value
// faces of the same sweep).
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

fn rc_alloc_dealloc(src: &str, ownership_off: bool) -> (i64, i64) {
    let mut b = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(src)
        .env("CRANELISP_RC_STATS", "1")
        .env("CRANELISP_NO_LENIENT", "1");
    if ownership_off {
        b = b.env("CRANELISP_NO_OWNERSHIP", "1");
    }
    let out = b.output();
    let line = out
        .stderr
        .lines()
        .rev()
        .find(|l| l.contains("[RC_STATS]"))
        .unwrap_or_else(|| panic!("no [RC_STATS] line:\n{}", out.stderr))
        .to_string();
    let field = |k: &str| -> i64 {
        line.split_whitespace()
            .find_map(|t| t.strip_prefix(k).and_then(|v| v.parse().ok()))
            .unwrap_or_else(|| panic!("no {k} in: {line}"))
    };
    (field("allocs="), field("deallocs="))
}

fn assert_exact(n: usize, ownership_off: bool) {
    let (allocs, deallocs) = rc_alloc_dealloc(&adt_wrapped_loop(n), ownership_off);
    let toggle = if ownership_off {
        "CRANELISP_NO_OWNERSHIP=1"
    } else {
        "ownership analysis ON"
    };
    assert_eq!(
        allocs, deallocs,
        "ADT-wrapped supersede loop (N={n}, {toggle}) MUST balance exactly: \
         allocs={allocs} deallocs={deallocs} (residue {}). Each superseded `Gr` \
         box and its cells vec is freed at the tail jump.",
        allocs - deallocs
    );
}

// 0720 pin 1 — the ADT-wrapped supersede loop balances EXACTLY at N=200 in both
// toggle states. Before the S115 W3 sweep: allocs=403 deallocs=2 (residue 401) —
// every superseded `Gr` box AND its cells vec leaked.
// spec: spec/12-runtime.md §12.3.1 — a superseded heap value (the old `Gr` box and
// its cells vec) is freed when no longer reachable.
// defect: class=rc-miscount locus=crates/cranelisp-backend TCO tail-jump superseded-param release — ADT-wrapped loop param never released (MS-P8 sibling; bare-vec face fixed W4) found=S114 owner=/dev
#[test]
fn adt_wrapped_supersede_loop_does_not_leak() {
    assert_exact(200, false);
    assert_exact(200, true);
}

// 0720 pin 2 — exactness holds at EVERY N, in both toggles: N=1, N=2, N=400. The
// former assertion was the weaker "residue(400) − residue(200) does not grow";
// exactness at each N subsumes it and additionally catches an under-count.
// spec: spec/12-runtime.md §12.3.1 — per-iteration superseded values are freed, so
// the at-exit residue is zero at every iteration count.
// defect: class=rc-miscount locus=crates/cranelisp-backend TCO tail-jump superseded-param release — ADT-wrapped loop param never released (residue scaled 2/iteration) found=S114 owner=/dev
#[test]
fn adt_wrapped_supersede_residue_does_not_scale_with_n() {
    for n in [1usize, 2, 400] {
        assert_exact(n, false);
        assert_exact(n, true);
    }
}

// 0720 CONTROL — the BARE-vec twin of the SAME supersede loop (no ADT wrap)
// balances exactly in both toggles. Proves the leak was specific to the
// ADT-wrapped loop-param, not the supersede loop shape — the S114 W4 MS-P8 fix
// covers this bare face. Guards the ADT-side fix from over-correcting into an
// under-count on the bare path.
// spec: spec/12-runtime.md §12.3.1 — a bare superseded heap loop-param is freed at
// the tail jump (the W4 MS-P8 fix).
#[test]
fn bare_vec_supersede_loop_balances_green() {
    let bare = "(defn set0 [cells m] (vec-set cells 0 m))\n\
         (defn go [cells m] (if (eq-i64 m 0) (vec-get cells 0) (go (set0 cells m) (add-i64 m -1))))\n\
         (defn main [] (Pure (go [5 5] 200)))\n";
    for ownership_off in [false, true] {
        let (allocs, deallocs) = rc_alloc_dealloc(bare, ownership_off);
        assert_eq!(
            allocs, deallocs,
            "the bare-vec supersede twin MUST balance (the W4 MS-P8 bare-face fix): \
             allocs={allocs} deallocs={deallocs} (ownership_off={ownership_off})."
        );
    }
}
