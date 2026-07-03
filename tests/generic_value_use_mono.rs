//! FIXME 0488 (S101 Phase 6a, /stdlib + 6b addendum) — a generic (polymorphic)
//! function referenced any way other than a *bare call* typechecks but fails at
//! codegen: its monomorphised instance never reaches the consuming turn's
//! codegen batch. Three signatures, one suspected class (resolver: the
//! /backend//typecheck consuming-turn codegen-batch derivation seam — the
//! "resolves in typecheck, body never reaches the codegen batch" family):
//!
//!   (a) FQ call position on a generic → `undefined function: <fq>`
//!       (concrete FQ calls work — control below);
//!   (b) imported generic in value position → `undefined variable: <name>`
//!       (same-module generic as value works; imported CONCRETE as value
//!       works; builtin as value works since the S101 fix — controls below);
//!   (c) composition over a fold-bodied generic — an imported generic applied
//!       over the result of another imported generic whose body passes a
//!       builtin as a value to a same-module generic fold fails at the
//!       consuming turn with the error attributed to the OUTER fn
//!       (`undefined function: <outer>`), while the SAME fns called bare in
//!       the same session work.
//!
//! All three reproduce stdlib-free (probed 2026-07-03, this /qa batch —
//! the FIXME's stdlib shapes reduced to local fixture modules; the stdlib
//! collateral `collections.vec/vec-flatten` is the same class).
//!
//! Partial-reduction note for the resolver, signature (c): the trigger is
//! micro-shape-sensitive. The failing module below (ge-i64 early-exit branch
//! order, stdlib `vec-reduce`-mirroring helper) reproduces deterministically
//! in cwd AND lib-dir module placement, public AND private helper, with and
//! without `:Int` annotations, with and without a prior successful bare call
//! of the fold-bodied fn in the same session. A sibling shape with reversed
//! `if` branch polarity (`lt-i64` recurse-first) and different helper
//! naming/arg-order PASSED at probe time — which micro-detail flips it is
//! UNKNOWN (FIXME 0488 residue; do not "simplify" the fixture without
//! re-verifying it still fails).
//!
//! Failing-not-ignored per `memory/feedback_failing_not_ignored.md`; ledger:
//! `tests/plan/ledger.md` §"Sprint 101 Phase 6a/6b defect set".

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

// A local generic + a local concrete fn, imported by the value-position tests.
const GEN_MODULE: &str = "(import [primitives [*]])\n\
                          (defn iden2 [x] x)\n\
                          (defn incr2 [:Int x] (add-i64 x 1))\n";

// The signature-(c) fixture: a same-module generic fold (mirroring stdlib
// vec-reduce's loop-helper shape), a fold-bodied generic passing the builtin
// vec-push as a VALUE, and a trivial imported-generic composer.
const FOLD_MODULE: &str = "(import [primitives [*]])\n\
                           (defn vreduce [f init v]\n\
                           \x20 (vreduce-loop f init v (vec-len v) 0))\n\
                           (defn- vreduce-loop [f acc v :Int len :Int i]\n\
                           \x20 (if (ge-i64 i len) acc\n\
                           \x20   (vreduce-loop f (f acc (vec-get v i)) v len (add-i64 i 1))))\n\
                           (defn vconcat [va vb] (vreduce vec-push va vb))\n\
                           (defn vcount [v] :Int (vec-len v))\n";

// =============================================================================
// Signature (a) — FQ call position
// =============================================================================

// spec: spec/04-expressions.md §4.2.2 — a qualified reference to a function
// resolves through the module system identically to the bare name; calling a
// generic fn by its FQ name MUST monomorphise and run like the bare call.
// RED on HEAD (FIXME 0488 sig a): `undefined function: user/iden` at codegen
// after a clean typecheck. The bare call in the same session is the in-test
// green control.
#[test]
fn generic_fn_fq_call_monomorphises_like_bare_call() {
    repl_prims(
        "(defn iden [x] x)\n\
         (iden 7)\n\
         (user/iden 5)\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 7") // bare-call control
    .assert_stdout_contains(":primitives/Int 5") // FQ call — the defect
    .assert_stdout_does_not_contain("undefined function");
}

// spec: spec/04-expressions.md §4.2.2 — CONTROL (GREEN on HEAD): the FQ call
// on a CONCRETE (annotated) fn works, pinning the 0488 boundary to generics.
#[test]
fn concrete_fn_fq_call_control() {
    repl_prims(
        "(defn incr [:Int x] (add-i64 x 1))\n\
         (user/incr 5)\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 6");
}

// =============================================================================
// Signature (b) — imported generic in value position
// =============================================================================

// spec: spec/04-expressions.md §4.6.2 — indirect calls: an imported generic
// fn passed as an argument is callable through the parameter, exactly like a
// same-module one. RED on HEAD (FIXME 0488 sig b): `undefined variable:
// iden2` at codegen after a clean typecheck.
#[test]
fn imported_generic_in_value_position_monomorphises() {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("gen.cl", GEN_MODULE)
        .stdin(
            "(import [gen [iden2]])\n\
             (defn call1 [f x] (f x))\n\
             (call1 iden2 5)\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 5")
        .assert_stdout_does_not_contain("undefined variable");
}

// spec: spec/04-expressions.md §4.6.2 — CONTROL (GREEN on HEAD): the
// same-module generic as a value works; the 0488 boundary is the import edge.
#[test]
fn same_module_generic_in_value_position_control() {
    repl_prims(
        "(defn iden [x] x)\n\
         (defn call1 [f x] (f x))\n\
         (call1 iden 5)\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 5");
}

// spec: spec/04-expressions.md §4.6.2 — CONTROL (GREEN on HEAD): an imported
// CONCRETE fn as a value works; generics are the broken cell (0488 matrix).
#[test]
fn imported_concrete_in_value_position_control() {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("gen.cl", GEN_MODULE)
        .stdin(
            "(import [gen [incr2]])\n\
             (defn call1 [f x] (f x))\n\
             (call1 incr2 5)\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 6");
}

// =============================================================================
// Signature (c) — composition over a fold-bodied generic
// =============================================================================

// spec: spec/04-expressions.md §4.6.2 — a generic whose body passes a builtin
// as a value to a same-module generic fold MUST stay composable: applying
// another imported generic over its result is an ordinary nested call. RED on
// HEAD (FIXME 0488 sig c / 6b addendum): the composed turn fails codegen with
// the error attributed to the OUTER fn — `undefined function: vcount` — while
// the bare calls of BOTH fns in the same session succeed (in-test controls).
#[test]
fn composition_over_fold_bodied_imported_generic_monomorphises() {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("gen3.cl", FOLD_MODULE)
        .stdin(
            "(import [gen3 [vconcat vcount]])\n\
             (vconcat [1 2] [30 40 50])\n\
             (vcount [7 8 9])\n\
             (vcount (vconcat [1 2] [3 4 5]))\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_contains("[1 2 30 40 50]") // bare fold-bodied call: control
        .assert_stdout_contains(":primitives/Int 3") // bare outer call: control
        .assert_stdout_contains(":primitives/Int 5") // the composed turn — the defect
        .assert_stdout_does_not_contain("undefined function");
}
