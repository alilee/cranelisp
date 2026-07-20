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

// PS-D1 twin (s114-test-plan §4.1) — the asking-module ≠ canonical-home composition
// on the OTHER axis: the committed pin above covers TYPE-home ≠ asking (`Foo`=user,
// `Int`=primitives). This twin covers TRAIT-home ≠ asking: a trait `Show` imported
// from a FOREIGN module `tlib`, impl'd for a USER-local type `Widget`. The
// confirmation MUST qualify the trait at its canonical home `tlib/Show` (NOT the
// asking module `user/Show`) AND the type at its home `user/Widget` (correct). RED
// today: the confirmation stamps `impl user/Show for user/Widget` — the trait is
// mis-qualified to the asking module. Flips with the same /dev(src) fix (read the
// RESOLVED homes, never a display-side re-derivation — P24/P26). Verified RED
// in-file at authoring per 0671's brief.
// spec: repl/spec.md §1.3 — value/expression feedback uses fully-qualified names at
// each name's CANONICAL home (both the trait and the target type).
// defect: class=display-envelope-mirror locus=src/repl/format.rs (TraitImpl arms compose the trait FQ from the asking `module` instead of its resolved home) found=S113 owner=/dev
#[test]
fn impl_confirmation_stamps_canonical_home_for_foreign_trait() {
    let out = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .repl()
        .file("tlib.cl", "(deftrait Show (sh [self] Int))\n")
        .stdin(
            "(import [tlib [Show]])\n\
             (deftype Widget (MkW [:Int n]))\n\
             (impl Show Widget (defn sh [x] 5))\n",
        )
        .timeout(Duration::from_secs(90))
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("impl tlib/Show for user/Widget"),
        "the impl-confirmation line MUST qualify the trait `Show` at its canonical \
         home `tlib/Show` (§1.3 FQ-correct), not the asking module `user/Show`; \
         got:\n{c}"
    );
    assert!(
        !c.contains("user/Show"),
        "the impl-confirmation line MUST NOT stamp the asking module `user` on the \
         foreign trait `Show` (its home is `tlib`); got:\n{c}"
    );
}
