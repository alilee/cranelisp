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
//!
//! SEAM ATTRIBUTION (S102 Wave 2, /qa isolation — full notes + call-chain
//! evidence in `tests/plan/0488-isolation.md`): all THREE signatures attribute
//! to `/dev(typecheck)` — the mono instance is NEVER MINTED (category (i):
//! "never requested"), verified by fresh-dir `/sig` probes showing no mangled
//! entry under any name after the failing turn, plus REPL ≡ `--run` parity on
//! all three. None attributes to the backend `fn_as_value.rs` seam (the
//! backend's "undefined function/variable" is the correct last-resort
//! fallthrough for a slot-less `Polymorphic` template reference).
//!   (a) pass-4 collection misses FQ-qualified callee heads: same-module FQ
//!       fails both collector gates (`resolve_terminal_entry_and_home` probes
//!       the table with the raw qualified key; the imported-collector's
//!       `home != current_module` gate excludes it); cross-module FQ is
//!       collected but `get_constrained_fn`'s home-probe re-uses the raw
//!       qualified string as a key in the home module's table → no mint.
//!   (b) `collect_parametric_fn_value_args`'s `home == current_module` gate
//!       (program.rs:3629) excludes imported generics in value position; the
//!       mint call (program.rs:3415) also hard-codes `home: None`.
//!   (c) DISTINCT mechanism: the fold-bodied template's DEFINING-module
//!       generalization publishes an over-general scheme — `vconcat` renders
//!       `(Fn [a (Vec b)] c)` (result UNTIED, first param degraded) where the
//!       loop-bodied control renders `(Fn [(Vec a) (Vec a)] (Vec a))`. At the
//!       composed turn the inner call's result type is then a free var, the
//!       OUTER site fails pass-4's all-args-concrete guard, no SigDispatch
//!       rewrite → codegen `undefined function: <outer>`. Pinning the free var
//!       (`(vcount :(Vec Int) (vconcat …))`) cures the whole composition —
//!       the annotation-cure control below pins that causal chain.
//!       Residue: WHERE gen3's own check loses the va/result↔vreduce
//!       unifications (0344 over-unification-guard interplay suspected) is
//!       for /dev(typecheck)'s isolating unit test. The minted
//!       `vconcat$Vec+Vec` entry also carries a residual-var scheme
//!       (`(Fn [(Vec Int) (Vec Int)] t16)`) — `register_mono_entry` captures
//!       `concrete_ret_ty` before the body re-check pins it (secondary find).

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

// =============================================================================
// S102 Wave-2 isolation reductions (`tests/plan/0488-isolation.md`)
// =============================================================================

// spec: spec/04-expressions.md §4.2.2 — a qualified reference resolves through
// the module system identically to the bare name, cross-module included. RED
// on HEAD (FIXME 0488 sig a, CROSS-module sub-cause): `undefined function:
// gen/iden2`. Distinct sub-cause from the same-module guard above — the
// isolation found the cross-module FQ site IS collected by pass-4
// (`collect_imported_constrained_calls` resolves qualified heads) but the
// mint dies in `get_constrained_fn`, whose home-probe re-uses the raw
// qualified string as a symbol-table key in the home module. A fix that only
// cures the same-module collector gates leaves this shape RED.
#[test]
fn generic_fn_cross_module_fq_call_monomorphises() {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("gen.cl", GEN_MODULE)
        .stdin(
            "(import [gen [iden2]])\n\
             (gen/iden2 5)\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 5")
        .assert_stdout_does_not_contain("undefined function");
}

// spec: spec/04-expressions.md §4.2.2 — CONTROL (GREEN on HEAD): the
// cross-module FQ call on a CONCRETE (annotated) fn works; a concrete fn
// needs no mono mint, pinning the 0488 boundary to generics on the
// cross-module axis too.
#[test]
fn concrete_fn_cross_module_fq_call_control() {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("gen.cl", GEN_MODULE)
        .stdin(
            "(import [gen [incr2]])\n\
             (gen/incr2 5)\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 6");
}

// spec: spec/03-types.md §3.4 — after generalization a defn's scheme
// quantifies the type variables of its inferred type; the fold body
// `(vreduce vec-push va vb)` unifies va, vb, and the result with vreduce's
// accumulator (`vreduce : (Fn [(Fn [a b] a) a (Vec b)] a)`, which HEAD
// publishes correctly), so `vconcat` MUST generalize to
// `(Fn [(Vec a) (Vec a)] (Vec a))` — exactly what the loop-bodied sibling
// publishes. RED on HEAD (FIXME 0488 sig c ROOT CAUSE, isolated S102 W2):
// HEAD publishes `(Fn [a (Vec b)] c)` — result untied, first param degraded —
// which is what makes every composed consumer turn fail pass-4's
// all-args-concrete guard and die at codegen attributed to the OUTER fn.
// This is the tightest (c) reduction: the defect is observable at the
// DEFINING module's check, one bare lookup, no composition needed.
#[test]
fn fold_bodied_generic_template_scheme_ties_params_and_result() {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("gen3.cl", FOLD_MODULE)
        .stdin(
            "(import [gen3 [vconcat]])\n\
             vconcat\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_contains(
            ":(Fn [(primitives/Vec a) (primitives/Vec a)] (primitives/Vec a)) gen3/vconcat",
        );
}

// spec: spec/04-expressions.md §4.6.2 — CONTROL (GREEN on HEAD), the sig-(c)
// annotation cure: pinning the inner call's result type with a `:Type`
// annotation makes the SAME composed turn that the RED guard above pins
// compile and run. Green today because the annotation substitutes for the
// scheme linkage the fold-bodied template lost — pinning the causal chain
// (free inner-result var → outer site skipped by the all-args-concrete
// guard). MUST stay green after the (c) fix (the annotation becomes
// redundant, never harmful).
#[test]
fn fold_bodied_composition_with_pinning_annotation_control() {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("gen3.cl", FOLD_MODULE)
        .stdin(
            "(import [gen3 [vconcat vcount]])\n\
             (vcount :(Vec Int) (vconcat [1 2] [3 4 5]))\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 5");
}

// =============================================================================
// G6 — prelude ≡ explicit import: a PRELUDE-DEFINED polymorphic fn (PLAN §III G6)
//
// Verified against the coverage above (2026-07-12): this file pins generics
// imported from LOCAL fixture modules through the 0488 mono-collection
// chokepoints, but NOT a polymorphic fn provided by the implicit prelude. A
// prelude-provided generic called at a concrete type MUST monomorphise through
// the same fallback-aware chokepoint as an explicitly-imported one. Twin over
// the generic's provenance.
// =============================================================================

// spec: spec/08-modules.md §8.8.1 + design/typecheck/monomorphisation.md — a
//   POLYMORPHIC prelude-provided fn called at a concrete type from user code
//   monomorphises and runs identically whether it is explicitly imported (leg A)
//   or reached via the implicit prelude glob (leg B).
//
// CLASSIFICATION: GREEN twin pin (G6). Both legs return 42 ((iden 42)).
#[test]
fn prelude_provided_polymorphic_fn_monomorphises_twin() {
    const PRELUDE_POLY: &str = "\
(export [primitives [*]])
(defn iden [x] x)
";
    // Leg A — the prelude generic `iden` explicitly imported (primitives imported
    // directly so `Pure` stays in scope after the prelude glob is suppressed).
    let leg_a = Cranelisp::new()
        .prelude(PRELUDE_POLY)
        .file(
            "user.cl",
            "(import [primitives [Pure]])\n\
             (import [prelude [iden]])\n\
             (defn main [] (Pure (iden 42)))",
        )
        .run("user.cl")
        .output();
    // Leg B — same program, `iden` reached via the implicit prelude.
    let leg_b = Cranelisp::new()
        .prelude(PRELUDE_POLY)
        .file("user.cl", "(defn main [] (Pure (iden 42)))")
        .run("user.cl")
        .output();
    leg_a.assert_exit(42);
    leg_b.assert_exit(42);
}
