// mc_x4_consume_at_distance_0719.rs — S114 Phase-6b, FIXME 0719 (MC-X4 family
// consume-at-distance variant rows + the §5.1.2 EQUIVALENCE-TWIN bar upgrade).
//
// RULING (/qa, spec-settled by §5.1.2, no user question): a multi-sig defn
// "type-checks identically to the same logic written as two separate
// mutually-recursive functions", ambiguous "only when the equivalent standalone
// function would also fail to infer it … never merely because it belongs to a
// multi-signature form." The exemplar's `peers`/`make-grid` two-function forms ship
// green; the collapse of the SAME logic fails — the spec's own acid test ⇒
// `wrong-reject` (carrier-loss family, the MC-X4/P26-temporal root).
//
// BAR UPGRADE (this file): the MC-X4 family bar is raised from X4b's
// "monomorphise OR reject cleanly" (which lets a §5.1.2 wrong-reject read as green)
// to the §5.1.2 EQUIVALENCE-TWIN assertion — the multi-sig form and its
// two-function twin must BOTH compile AND agree on output.
//
// REDUCTION (COMPLETE — /testing, from the deterministic scratch-collapse):
// the discriminating axis is NOT the seed (`[0]` ≡ `[]`), the stdlib poly verbs,
// or an ADT wrapper — every single/double-axis synthetic is GREEN (the born-green
// controls below). It is the INDIRECTION: the multi-sig call made inside a WRAPPER
// function (`run-elim`), its bare-`(Vec Int)` result flowing through that wrapper's
// monomorphisation into a separately-monomorphised poly consumer (`vec-len`),
// rather than at a top-level concrete site. Called directly in `main`, the same
// multi-sig `peers` is GREEN — the wrapper is the sole load-bearing axis, and it
// is exactly the exemplar's shape (`peers` consumed inside `eliminate-from-peers`,
// never at a concrete site). Free-standing, PrimitivesOnly (no stdlib, no fixture
// copy) — a full reduction, no partial-reduction FIXME owed.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn assert_run_and_link(user: &str, code: i32) {
    for link in [false, true] {
        let b = Cranelisp::new().with_prelude(PreludeVariant::PrimitivesOnly);
        let b = if link {
            b.link_then_run("user.cl")
        } else {
            b.run("user.cl")
        };
        let o = b.user(user).output();
        assert_eq!(
            o.status.code(),
            Some(code),
            "[{}] expected exit {code}; got {:?}:\n{}{}",
            if link { "--link" } else { "--run" },
            o.status.code(),
            o.stdout,
            o.stderr
        );
    }
}

// A multi-sig `peers`: 1-arg entry seeds the acc, 2-arg sibling pushes. Returns a
// bare `(Vec Int)`. `(peers 3)` → `[3 2 1]` (seed `[]`) or `[0 3 2 1]` (seed `[0]`).
const PEERS_SEED_EMPTY: &str = "(defn peers\n\
     \x20 ([idx]     (peers idx []))\n\
     \x20 ([idx acc] (if (eq-i64 idx 0) acc (peers (add-i64 idx -1) (vec-push acc idx)))))\n";
const PEERS_SEED_ZERO: &str = "(defn peers\n\
     \x20 ([idx]     (peers idx [0]))\n\
     \x20 ([idx acc] (if (eq-i64 idx 0) acc (peers (add-i64 idx -1) (vec-push acc idx)))))\n";

// ── Born-green controls: the fixed variants (the S113 pins reach these) ──────

// CONTROL 1 (GREEN) — parameter-distance through a RECURSIVE consumer, bare
// `(Vec Int)`, seed `[0]`. The multi-sig return is passed as an ARG to `consume`
// (concrete site in `main`), then threaded through the recursive `sum-from`.
// `(peers 3)` = [0 3 2 1], sum = 6.
// spec: spec/05-definitions.md §5.1.2 — a multi-sig bare-Vec return consumed at
// parameter distance through a recursive consumer, concrete producer site.
#[test]
fn param_distance_recursive_consumer_seed_zero_green() {
    assert_run_and_link(
        &format!(
            "{PEERS_SEED_ZERO}\
             (defn sum-from [v i acc] (if (eq-i64 i (vec-len v)) acc (sum-from v (add-i64 i 1) (add-i64 acc (vec-get v i)))))\n\
             (defn consume [v] (sum-from v 0 0))\n\
             (defn main [] (Pure (consume (peers 3))))\n"
        ),
        6,
    );
}

// CONTROL 1b (GREEN) — the same, seed `[]` (element type genuinely free until the
// first push). `(peers 3)` = [3 2 1], sum = 6. The seed axis is NOT load-bearing.
// spec: spec/05-definitions.md §5.1.2 — an empty-seeded multi-sig Vec return
// consumed at parameter distance.
#[test]
fn param_distance_recursive_consumer_seed_empty_green() {
    assert_run_and_link(
        &format!(
            "{PEERS_SEED_EMPTY}\
             (defn sum-from [v i acc] (if (eq-i64 i (vec-len v)) acc (sum-from v (add-i64 i 1) (add-i64 acc (vec-get v i)))))\n\
             (defn consume [v] (sum-from v 0 0))\n\
             (defn main [] (Pure (consume (peers 3))))\n"
        ),
        6,
    );
}

// CONTROL 2 (GREEN) — untyped-ADT-field × distance: the multi-sig return is wrapped
// in an ADT with an UNTYPED field (`Bx [contents]`), pattern-matched out, then
// consumed at parameter distance. `(peers 3)` (seed [0]) = [0 3 2 1], sum = 6.
// spec: spec/05-definitions.md §5.1.2 — a multi-sig Vec return carried through an
// untyped ADT field and consumed at distance.
#[test]
fn untyped_adt_field_distance_green() {
    assert_run_and_link(
        &format!(
            "(deftype Box (Bx [contents]))\n\
             (defn peers\n\
             \x20 ([idx]     (peers idx [0]))\n\
             \x20 ([idx acc] (if (eq-i64 idx 0) (Bx acc) (peers (add-i64 idx -1) (vec-push acc idx)))))\n\
             (defn sum-from [v i acc] (if (eq-i64 i (vec-len v)) acc (sum-from v (add-i64 i 1) (add-i64 acc (vec-get v i)))))\n\
             (defn consume [b] (match b [(Bx v) (sum-from v 0 0)]))\n\
             (defn main [] (Pure (consume (peers 3))))\n"
        ),
        6,
    );
}

// CONTROL 3 (GREEN) — cross-module × untyped-field × distance: the ADT + multi-sig
// producer live in module `bld`, imported and consumed at parameter distance in
// `user`. sum = 6.
// spec: spec/05-definitions.md §5.1.2 — a cross-module multi-sig Vec-in-ADT return
// consumed at parameter distance.
#[test]
fn cross_module_untyped_field_distance_green() {
    let bld = "(deftype Box (Bx [contents]))\n\
         (defn peers\n\
         \x20 ([idx]     (peers idx [0]))\n\
         \x20 ([idx acc] (if (eq-i64 idx 0) (Bx acc) (peers (add-i64 idx -1) (vec-push acc idx)))))\n";
    let user = "(import [bld [Box Bx peers]])\n\
         (defn sum-from [v i acc] (if (eq-i64 i (vec-len v)) acc (sum-from v (add-i64 i 1) (add-i64 acc (vec-get v i)))))\n\
         (defn consume [b] (match b [(Bx v) (sum-from v 0 0)]))\n\
         (defn main [] (Pure (consume (peers 3))))\n";
    for link in [false, true] {
        let b = Cranelisp::new()
            .with_prelude(PreludeVariant::PrimitivesOnly)
            .file("bld.cl", bld);
        let b = if link {
            b.link_then_run("user.cl")
        } else {
            b.run("user.cl")
        };
        let o = b.user(user).output();
        assert_eq!(
            o.status.code(),
            Some(6),
            "[{}] cross-module distance control expected exit 6; got {:?}:\n{}{}",
            if link { "--link" } else { "--run" },
            o.status.code(),
            o.stdout,
            o.stderr
        );
    }
}

// ── The RED combination cell + its §5.1.2 EQUIVALENCE-TWIN ───────────────────

// RED — the multi-sig `peers` (seed []) called inside a WRAPPER `run-elim` whose
// result feeds the poly consumer `vec-len`. The element var never settles: today
// `type error … ambiguous type … monomorphised in \`user/peers$Var$Int\` (a
// residual unbound type variable reached a codegen position)`. The correct output
// is exit 3 (= `(vec-len [3 2 1])`), matching the two-function twin below. Flips
// with the S115 typecheck consume-at-distance carrier fix.
// spec: spec/05-definitions.md §5.1.2 — a multi-sig defn type-checks identically to
// the equivalent two-function form; the wrapper-indirected consume must infer.
// defect: class=carrier-loss locus=crates/cranelisp-typecheck consumer mono harvest — multi-sig bare-Vec return consumed through a wrapper-function indirection (a separately-monomorphised consumer context; the exemplar peers/eliminate-from-peers axis) found=S114 owner=/dev
#[test]
fn multi_sig_return_through_wrapper_indirection_infers() {
    assert_run_and_link(
        &format!(
            "{PEERS_SEED_EMPTY}\
             (defn run-elim [idx] (vec-len (peers idx)))\n\
             (defn main [] (Pure (run-elim 3)))\n"
        ),
        3,
    );
}

// EQUIVALENCE-TWIN (GREEN) — the SAME logic written as two mutually-recursive
// functions (`peers` delegating to `peers-helper`), SAME wrapper `run-elim`, SAME
// consumer. Compiles and returns 3. The §5.1.2 acid test: the two forms differ
// ONLY on the multi-sig axis, so the RED above is a `wrong-reject`, not a genuine
// ambiguity. Must stay green.
// spec: spec/05-definitions.md §5.1.2 — the two-function equivalent of the multi-sig
// form infers and runs.
#[test]
fn two_function_equivalent_through_wrapper_indirection_green() {
    assert_run_and_link(
        "(defn peers-helper [idx acc] (if (eq-i64 idx 0) acc (peers-helper (add-i64 idx -1) (vec-push acc idx))))\n\
         (defn peers [idx] (peers-helper idx []))\n\
         (defn run-elim [idx] (vec-len (peers idx)))\n\
         (defn main [] (Pure (run-elim 3)))\n",
        3,
    );
}
