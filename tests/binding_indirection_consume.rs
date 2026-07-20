// binding_indirection_consume.rs — 0669/0668 binding-indirection consume family
// (S113 W5b/6b). Ownership accounting at consume/cleanup sites is decided by LOCAL
// SYNTAX (is this node a `Var`? a "temp"?) instead of the value-flow question "does
// this consume position receive an independently-owned count?". A heap value
// passing THROUGH a `let` binding or a match var-pattern into another consumer
// falls in the gap (FIXME 0668).
//
// The W5b sub-fix (vec-lit element store consuming discrimination, `compile_vec_lit`)
// flipped cells A/E — pinned here as born-green fences. The residual family faces
// (G let-bind alias, F/B nested-match forward, C-off B-2 toggle-off) stay RED,
// attributed to the 0668 consume seam (S114 /design(backend) consume-position ×
// operand-provenance contract). Free-standing (no stdlib).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn run_prims(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(src)
        .output()
}

fn run_prims_off(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(src)
        .env("CRANELISP_NO_OWNERSHIP", "1")
        .output()
}

// ---- Cells A/E — BORN-GREEN (the W5b vec-lit element-store sub-fix) --------------

// Cell A — `(let [q (vec-set v 1 99)] [q])` projects a COW result held through a
// `let` binding into a fresh container. The vec-lit element store now routes the
// heap `Var` element `q` through the consuming inc (analysis-independent). → 99.
// spec: spec/12-runtime.md §12.1 — a COW value bound by a `let` and stored into a
// container stays live for the container's reader.
#[test]
fn let_bound_cow_projected_into_container_green() {
    run_prims(
        "(defn f [v] (let [q (vec-set v 1 99)] [q]))\n\
         (defn main [] (Pure (vec-get (vec-get (f [1 2 3]) 0) 1)))\n",
    )
    .assert_exit(99);
}

// Cell A — toggle-off twin (the sub-fix is analysis-independent by construction).
// spec: spec/12-runtime.md §12.1 — same, conservative all-Owned lowering.
#[test]
fn let_bound_cow_projected_into_container_toggle_off_green() {
    run_prims_off(
        "(defn f [v] (let [q (vec-set v 1 99)] [q]))\n\
         (defn main [] (Pure (vec-get (vec-get (f [1 2 3]) 0) 1)))\n",
    )
    .assert_exit(99);
}

// Cell E — `(let [q [7 8 9]] [q])` — NO COW, no param: a fresh vec bound by `let`
// and stored into a container. → 7. Proves the family is pre-COW.
// spec: spec/12-runtime.md §12.1 — a let-bound fresh vec stored into a container.
#[test]
fn let_bound_fresh_vec_into_container_green() {
    run_prims(
        "(defn f [] (let [q [7 8 9]] [q]))\n\
         (defn main [] (Pure (vec-get (vec-get (f) 0) 0)))\n",
    )
    .assert_exit(7);
}

// Cell E — toggle-off twin.
// spec: spec/12-runtime.md §12.1 — same, conservative lowering.
#[test]
fn let_bound_fresh_vec_into_container_toggle_off_green() {
    run_prims_off(
        "(defn f [] (let [q [7 8 9]] [q]))\n\
         (defn main [] (Pure (vec-get (vec-get (f) 0) 0)))\n",
    )
    .assert_exit(7);
}

// ---- Residual family faces — RED (0668 consume seam, S114 contract) --------------

// Cell G — the LET-BIND ALIAS residual (`q = v` binds a `Var` to a `Var` without
// counting, so `q` and `v` BOTH scope-dec ⇒ the vec-lit inc pairs only one ⇒ the
// inner vec is freed under the container). `(vec-get (vec-get (f [7 8 9]) 0) 0)`
// MUST be 7; today a garbage word (RC_STATS: allocs=2 deallocs=1). Explicitly OUT
// of the vec-lit sub-fix scope (0668's "flips A/E/G" over-counted G).
// spec: spec/12-runtime.md §12.1 — a value aliased by a `let` and stored into a
// container stays live for the container's reader.
// defect: class=rc-miscount locus=crates/cranelisp-backend let-bind alias consume seam (q=v binds Var-to-Var uncounted; both scope-dec; FIXME 0668 direction) found=S113 owner=/dev
#[test]
fn let_bind_alias_into_container_neg() {
    run_prims(
        "(defn f [v] (let [q v] [q]))\n\
         (defn main [] (Pure (vec-get (vec-get (f [7 8 9]) 0) 0)))\n",
    )
    .assert_exit(7);
}

// Cell F — NESTED-MATCH forward, NO COW: `(match (match v [r r]) [q q])` forwards
// `v` through two var-pattern matches. Each match classifies its scrutinee "temp"
// syntactically and decs after the arm, but the result merely forwards a binding's
// value (an alias carrying no count). `(vec-get (f [7 8 9]) 0)` MUST be 7; today
// garbage. Ownership-independent (pre-COW).
// spec: spec/12-runtime.md §12.1 — a value forwarded through nested var-pattern
// matches stays live for the caller.
// defect: class=rc-miscount locus=crates/cranelisp-backend match scrutinee/arm forward consume seam (spurious temp-dec of a forwarded alias; FIXME 0668 direction 2) found=S113 owner=/dev
#[test]
fn nested_match_forward_alias_neg() {
    run_prims(
        "(defn f [v] (match (match v [r r]) [q q]))\n\
         (defn main [] (Pure (vec-get (f [7 8 9]) 0)))\n",
    )
    .assert_exit(7);
}

// Cell C (B-2) — the TOGGLE-OFF face that lost its pin (FIXME 0669): the B-2 shape
// `(match (vec-set v 1 99) [r r])` is correct with analysis ON (W5b escape-recording
// fix) but under `CRANELISP_NO_OWNERSHIP=1` the COPY branch mints a temp scrutinee,
// the match decs it after the arm, and the var-pattern arm forwards the alias
// (protect-inc comes AFTER the dec; rc hits 0 first). `(vec-get (h [1 2 3]) 1)`
// MUST be 99; toggle-off returns per-run-varying garbage. Restores the differential-
// oracle acceptance (analysis-on == analysis-off == correct).
// spec: spec/12-runtime.md §12.1 — a COW match result is memory-safe under the
// conservative all-Owned lowering too.
// defect: class=rc-miscount locus=crates/cranelisp-backend match consume seam, toggle-off COPY branch (temp scrutinee dec before var-arm protect-inc; FIXME 0669) found=S113 owner=/dev
#[test]
fn b2_match_cow_var_pattern_toggle_off_neg() {
    run_prims_off(
        "(defn h [v] (match (vec-set v 1 99) [r r]))\n\
         (defn main [] (Pure (vec-get (h [1 2 3]) 1)))\n",
    )
    .assert_exit(99);
}
