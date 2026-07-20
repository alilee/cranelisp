// ps_d1_impl_confirmation_home.rs — PS-D1 (S113, FIXME 0671).
//
// The REPL's `impl Trait for Type` confirmation line qualifies BOTH the trait and
// the target type with the ASKING module (`user` for a REPL impl), regardless of
// where the trait/type actually live — it does not chain-follow either name to its
// canonical home. `(impl Foo Int …)` renders `impl user/Foo for user/Int` when the
// type's home is `primitives`.
//
// Owner /dev(src), `class=display-envelope-mirror` — the P24 resolve-home class's
// display face (the eval.rs `impl_echo_type_name` precedent repeated): the
// confirmation COMPOSES FQ names from the asking context instead of reading the
// RESOLVED identities the registry already carries. Fix reads recorded resolved
// state (P26), never a display-side re-derivation. Display-only (dispatch +
// persistence unaffected). Uses the ONE sanctioned stdlib touchpoint (the demo runs
// under the full prelude).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;
use std::time::Duration;

// spec: repl/spec.md §1.3 — value/expression feedback uses fully-qualified names at
// each name's CANONICAL home (a wrong FQ name violates the self-documenting-REPL
// principle).
// defect: class=display-envelope-mirror locus=src/repl/format.rs (TraitImpl arms compose FQ from the asking `module` instead of each name's resolved home) found=S113 owner=/dev
#[test]
fn impl_confirmation_stamps_canonical_home_not_asking_module() {
    let out = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .repl()
        .stdin("(deftrait Foo (bar [a] Int))\n(impl Foo Int (defn bar [x] (* x 2)))\n")
        .timeout(Duration::from_secs(90))
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    // The impl-confirmation line must qualify the target type at its CANONICAL home
    // (`primitives/Int`), NOT the asking module (`user/Int`).
    assert!(
        c.contains("impl user/Foo for primitives/Int"),
        "the impl-confirmation line MUST qualify `Int` at its canonical home \
         `primitives/Int` (§1.3 FQ-correct), not the asking module `user/Int`; \
         got:\n{c}"
    );
    assert!(
        !c.contains("for user/Int"),
        "the impl-confirmation line MUST NOT stamp the asking module `user` on the \
         type `Int` (its home is `primitives`); got:\n{c}"
    );
}
