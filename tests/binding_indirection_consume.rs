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

// `--link` then run the produced binary — the divergence-bearing mode (per
// MS-P7's lesson `--run` + `--link` is the pair that exposes mode-specific
// consume-seam bugs; the widest codegen batch is the ObjectModule build).
fn link_prims(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user(src)
        .output()
}

fn link_prims_off(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
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

// ---- Cell H — BORN-GREEN twin for the match rows (BI-T pairing) -----------------

// Cell H — bare var-pattern match forwarding a SCALAR: `(match 7 [r r])` binds `r`
// to the scrutinee and returns it. This proves the match MACHINERY — var-pattern
// binding + arm forward — is correct; there is no heap RC to mis-account, so it
// stays GREEN. The GREEN twin the nested-match RED rows (F, B-cow) name: their bug
// is specifically the SPURIOUS temp-dec of a forwarded HEAP alias (H differs only
// in that its forwarded value is a non-heap Int), isolating the consume seam as
// the RC-accounting site, not the match logic. → 7.
//
// NOTE (/testing finding, verified 2026-07-20; s114-test-plan §2 BI-T): a bare
// match forwarding a HEAP value — `(match [7 8 9] [r r])` — is itself RED today
// (returns garbage, both inline AND across a fn return): the whole heap-forward-
// through-match family is broken, so no heap bare-match green twin exists. The
// scalar match is the correct isolating control. Reported to /qa.
// spec: spec/12-runtime.md §12.1 — a bare var-pattern match forwards its bound
// value to the caller.
#[test]
fn bare_match_forward_scalar_green() {
    run_prims(
        "(defn f [] (match 7 [r r]))\n\
         (defn main [] (Pure (f)))\n",
    )
    .assert_exit(7);
}

// ---- BI-B-cow — NESTED-MATCH forward WITH COW (0668 cell B verbatim), RED ×2 -----

// Cell B-cow — `(match (match (vec-set v 0 5) [r r]) [q q])`: a COW `vec-set`
// forwarded through TWO nested var-pattern matches. The inner match's scrutinee is
// the COW result; each match syntactically classifies its scrutinee "temp" and
// decs after the arm, but each arm merely forwards a binding's value (an alias
// carrying no independent count) — so the COW box is freed under the caller.
// `(vec-set [1 2 3] 0 5)` = `[5 2 3]`; `(vec-get (f [1 2 3]) 0)` MUST be 5. This is
// the 0669-named probe cell (cell F one axis over: COW scrutinee instead of a bare
// param), pinning that the forwarding-suppression rule (R3) fixes the COW nest too.
// GREEN twin: `bare_match_forward_fresh_vec_green` (H) — a single correct forward.
// Flips with the 0668 consume-contract /dev change-set (Track B).
// spec: spec/12-runtime.md §12.1 — a COW value forwarded through nested var-pattern
// matches stays live for the caller.
// defect: class=rc-miscount locus=crates/cranelisp-backend match scrutinee/arm forward consume seam (spurious temp-dec of a forwarded COW alias; FIXME 0668 direction 2 / R3 forwarding-suppression) found=S114 owner=/dev
#[test]
fn nested_match_forward_cow_alias_neg() {
    run_prims(
        "(defn f [v] (match (match (vec-set v 0 5) [r r]) [q q]))\n\
         (defn main [] (Pure (vec-get (f [1 2 3]) 0)))\n",
    )
    .assert_exit(5);
}

// Cell B-cow, toggle-off twin — the same nested-match-COW forward under
// `CRANELISP_NO_OWNERSHIP=1` (the conservative all-Owned lowering). The contract is
// structural (provenance traced to a live-binding root), so it must be correct in
// BOTH toggle states by construction. RED today; flips with the same change-set.
// spec: spec/12-runtime.md §12.1 — same, under the conservative all-Owned lowering.
// defect: class=rc-miscount locus=crates/cranelisp-backend match scrutinee/arm forward consume seam, toggle-off (spurious temp-dec of a forwarded COW alias; FIXME 0668 R3) found=S114 owner=/dev
#[test]
fn nested_match_forward_cow_alias_toggle_off_neg() {
    run_prims_off(
        "(defn f [v] (match (match (vec-set v 0 5) [r r]) [q q]))\n\
         (defn main [] (Pure (vec-get (f [1 2 3]) 0)))\n",
    )
    .assert_exit(5);
}

// ---- BI-M — mode-axis completion (the `--link` twins, MS-P7's divergence pair) ---

// The family file ran `--run` only (plan §0.5 mode-axis debt). The divergence-
// bearing pair is `--run` + `--link` (the ObjectModule build is the widest codegen
// batch and the mode where consume-seam mis-accounting corrupts the heap
// deterministically). Cell G and cell C-off each gain a `--link` twin; born-green
// cell A gains a `--link` fence proving the sub-fix holds under `--link` too.

// BI-M — cell A `--link` fence (BORN-GREEN). The vec-lit element-store sub-fix
// (W5b) holds under `--link`: `(let [q (vec-set v 1 99)] [q])` linked → exit 99.
// The must-hold fence that a Track-B consume-contract change must not break under
// the widest codegen batch.
// spec: spec/12-runtime.md §12.1 — a let-bound COW value stored into a container
// stays live for the container's reader (`--link`).
#[test]
fn let_bound_cow_projected_into_container_link_green() {
    link_prims(
        "(defn f [v] (let [q (vec-set v 1 99)] [q]))\n\
         (defn main [] (Pure (vec-get (vec-get (f [1 2 3]) 0) 1)))\n",
    )
    .assert_exit(99);
}

// BI-M — cell G `--link` twin (RED). The let-bind alias `(let [q v] [q])` under
// `--link`: the doubled scope-dec frees the inner vec under the container and the
// linked binary reads freed heap (deterministic corruption / wrong word). MUST be
// 7. GREEN twin: cell E (`let_bound_fresh_vec_into_container_green`, a fresh vec
// with no alias) is the alias-row green control; the `--run` sibling is
// `let_bind_alias_into_container_neg`. Flips with the contract.
// spec: spec/12-runtime.md §12.1 — a let-aliased value stored into a container
// stays live for the container's reader (`--link`).
// defect: class=rc-miscount locus=crates/cranelisp-backend let-bind alias consume seam (q=v binds Var-to-Var uncounted; both scope-dec; FIXME 0668), --link mode face found=S114 owner=/dev
#[test]
fn let_bind_alias_into_container_link_neg() {
    link_prims(
        "(defn f [v] (let [q v] [q]))\n\
         (defn main [] (Pure (vec-get (vec-get (f [7 8 9]) 0) 0)))\n",
    )
    .assert_exit(7);
}

// BI-M — cell C-off `--link` twin (RED). The B-2 shape under `CRANELISP_NO_OWNERSHIP=1`
// via `--link`: the toggle-off COPY branch mints a temp scrutinee dec'd before the
// var-arm protect-inc, so the linked binary reads freed heap. `(vec-get (h [1 2 3])
// 1)` MUST be 99. GREEN twin: the analysis-ON `--run` face stays correct (cell A
// class). Flips with the contract.
// spec: spec/12-runtime.md §12.1 — a COW match result is memory-safe under the
// conservative all-Owned lowering (`--link`).
// defect: class=rc-miscount locus=crates/cranelisp-backend match consume seam, toggle-off COPY branch (temp scrutinee dec before var-arm protect-inc; FIXME 0669), --link mode face found=S114 owner=/dev
#[test]
fn b2_match_cow_var_pattern_toggle_off_link_neg() {
    link_prims_off(
        "(defn h [v] (match (vec-set v 1 99) [r r]))\n\
         (defn main [] (Pure (vec-get (h [1 2 3]) 1)))\n",
    )
    .assert_exit(99);
}
