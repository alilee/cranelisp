// w2a_review_fences.rs — MC-G1 (S113 W2a-close): the four review/fix-cycle repros
// become PERMANENT e2e cells. Each caught a real hole once during the W2a carrier
// fix cycle, so each guards a revert (GREEN fences post-fix — they MUST pass now).
//
//   (a) template-select inside a mono body                          — §5.1.2
//   (b) D3-harvested orphan-pendings (poly callee via multi-sig clause) — §5.1.2
//   (c) method-only-import wrapper hop through verify_constraints    — §7.11.2
//   (d) foreign-sig-type `(sh 5)` with no `Int` in the caller's scope — §7.11.2
//
// Free-standing (no stdlib).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn repl_prims(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(lines)
        .output()
}

// MC-G1(a) — template-select inside a MONO body: `ga` is monomorphised at `:a` =
// Int by `(ga 5)`, and inside its body the multi-sig `(h 1 2)` selects the arity-2
// template clause `([a b] a)` → 1; `(add-i64 1 0)` = 1. The W2a mono harvest must
// cover multi-sig dispatch reached from inside a minted mono body.
// spec: spec/05-definitions.md §5.1.2 — multi-sig dispatch inside a monomorphised body.
#[test]
fn template_select_inside_mono_body_green() {
    repl_prims(
        "(defn h ([x] (add-i64 x 1)) ([a b] a))\n\
         (defn ga [:a x] (add-i64 (h 1 2) 0))\n\
         (ga 5)\n",
    )
    .assert_stdout_contains(":primitives/Int 1");
}

// MC-G1(b) — D3-harvested orphan-pendings: the poly callee `h2` is reached ONLY
// through `poly2`, itself reached from a multi-sig clause body (`ms`'s arity-1
// clause). `(ms 7)` → `(poly2 7)` → `(let [q (h2 1)] 7)` = 7. The cross-arity-
// reached poly callee must be enqueued/instantiated (the D3 producer fix).
// spec: spec/05-definitions.md §5.1.2 — a poly callee reached via a multi-sig
// clause body is monomorphised.
#[test]
fn d3_harvested_orphan_pending_poly_callee_green() {
    repl_prims(
        "(defn h2 ([x] (add-i64 x 1)) ([a b] a))\n\
         (defn poly2 [p] (let [q (h2 1)] p))\n\
         (defn ms ([x] (poly2 x)) ([a b] a))\n\
         (ms 7)\n",
    )
    .assert_stdout_contains(":primitives/Int 7");
}

// MC-G1(c) — method-only-import WRAPPER HOP: the trait method `bump` is imported
// WITHOUT its trait `Bump`, then dispatched INDIRECTLY through a user wrapper
// `(defn wrap [x] (bump x))`. `(wrap 1)` → `(bump 1)` → 2. The wrapper hop passes
// through `verify_constraints` — the seam the review found un-covered.
// spec: spec/07-traits.md §7.11.2 — method-only import dispatches through a wrapper.
#[test]
fn method_only_import_wrapper_hop_green() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .file(
            "blib.cl",
            "(import [primitives [Int add-i64]])\n\
             (deftrait Bump (bump [self] Int))\n\
             (impl Bump Int (defn bump [x] (add-i64 x 1)))\n",
        )
        .user(
            "(import [primitives [Pure]])\n\
             (import [blib [bump]])\n\
             (defn wrap [x] (bump x))\n\
             (defn main [] (Pure (wrap 1)))\n",
        )
        .output();
    out.assert_exit(2);
}

// MC-G1(d) — FOREIGN-SIG type: `Show`'s method `sh` returns `Int`, but the caller
// imports ONLY `sh` — NOT `Int`, NOT the trait `Show`. `(sh 5)` still dispatches to
// `Show Int` → 99. Dispatch/constraint-checking must reach the sig's types via the
// method's home even when they are not in the caller's scope.
// spec: spec/07-traits.md §7.11.2 — dispatch reaches foreign sig types via the method home.
#[test]
fn foreign_sig_type_method_only_import_green() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .run("user.cl")
        .file(
            "zlib.cl",
            "(import [primitives [Int]])\n\
             (deftrait Show (sh [self] Int))\n\
             (impl Show Int (defn sh [x] 99))\n",
        )
        .user(
            "(import [primitives [Pure]])\n\
             (import [zlib [sh]])\n\
             (defn get-s [] (sh 5))\n\
             (defn main [] (Pure (get-s)))\n",
        )
        .output();
    out.assert_exit(99);
}
