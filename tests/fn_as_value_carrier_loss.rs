// fn_as_value_carrier_loss.rs — S114 W7 PIN-NOW (s114-test-plan §11 item 5).
//
// The fn-as-value GOT-slot carrier-loss defect: partially applying a trait operator
// whose impl IS present mints a fn-as-value wrapper for the operator, and the seam
// that mints the wrapper body derives NO GOT-slot carrier for the wrapped callee —
// so the loud keyed-consumer miss (`backend-keyed-consumer.md` §1.2/§10) fires on a
// SPEC-VALID program at codegen:
//
//   codegen error: fn-as-value wrapper for '=' reached codegen with no GOT-slot
//   carrier (S110 W2 keyed read; backend-keyed-consumer.md §1.2/§10)
//
// `class=carrier-loss` (S112 vocabulary): a keyed producer→consumer carrier is never
// written for a reaching consumer site, so a spec-valid program surfaces a
// backend/codegen error — NOT a `check-gate-leak` (nothing should be rejected) and
// NOT the forbidden soft-fallback (the loud keyed-consumer miss is working as
// designed; the PRODUCER is the owner). Attribution per §11 item 5: `cranelisp-
// typecheck`, the mono_collect fn-value rewrite seam — provisional. Fix = S115
// typecheck scope input (NOT a W7 rider — distinct seam from MS-P7/trait-shadow/
// F-D2-11; W7 typecheck is at capacity).
//
// FAMILY CROSS-REF: `shadowing_scope_lookup.rs::
// let_shadowed_trait_operator_auto_curry_resolves_to_local` surfaces the IDENTICAL
// error string ("fn-as-value wrapper for ... reached codegen with no GOT-slot
// carrier") for the auto-curry-over-a-LOCAL-closure face (FIXME 0705). That face is
// re-attributed to the BACKEND (a local closure has no GOT slot) and is PLAUSIBLY the
// SAME backend seam family as this cell (both are a fn-as-value wrapper minted with no
// GOT-slot carrier). The two attributions differ (this cell provisionally typecheck-
// producer per §11 item 5; 0705's face backend); whether they collapse to ONE seam is
// the open question the S115 fix resolves. See the reciprocal note on the 0705 cell.
//
// Mask note (§11 item 5, binding on F-D2-12's "P2 conformant" verdict): F-D2-12's
// auto-curry-no-impl probe reads "P2 conformant" only up to THIS mask — when this
// carrier-loss pin flips, /qa re-probes the true late-pinning shape.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// The generic-partial late-pinning shape (§11 item 5): `(defn g [x] (= x))` returns a
// PARTIAL application of the Eq operator `=` (a fn-as-value wrapper awaiting the second
// arg); instantiating `g` at Int (`(g 3)`) mints the wrapper at Eq[Int]. The Eq impl
// for Int IS present (TestStandard prelude), so this is impl-present carrier-loss, not
// a missing-impl reject. `((g 3) 3)` compares 3 == 3 → true → 5 → exit 5 when fixed.
// RED at HEAD: codegen fails minting the `=` wrapper with no GOT-slot carrier → exit 1.
// spec: spec/04-expressions.md §4.6.3 — a partial application of a trait operator with
// its impl present MUST compile and evaluate.
// defect: class=carrier-loss locus=crates/cranelisp-typecheck mono_collect fn-value rewrite seam — fn-as-value wrapper minted with no GOT-slot carrier (impl-present trait operator; §11 item 5; seam provisional, plausibly the shadowing_scope_lookup 0705 backend seam family) found=S114 owner=/dev
#[test]
fn trait_operator_partial_app_impl_present_has_got_carrier() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::TestStandard)
        .run("user.cl")
        .user(
            "(defn g [x] (= x))\n\
             (defn main [] (Pure (if ((g 3) 3) 5 0)))\n",
        )
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert_eq!(
        out.status.code(),
        Some(5),
        "partially applying the Eq operator `=` (impl present) — `(defn g [x] (= x))` \
         instantiated at Int — MUST compile and evaluate (`((g 3) 3)` → 3 == 3 → true \
         → 5), NOT fail codegen with `fn-as-value wrapper for '=' reached codegen with \
         no GOT-slot carrier`; got exit {:?}:\n{c}",
        out.status.code()
    );
}
