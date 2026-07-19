// multi_sig_variant_display_constraint_drop.rs — D1 repro (S112 Phase 6b).
//
// A multi-signature `defn` variant that INFERS a trait bound drops that bound
// from its display. Under the standard prelude:
//
//   (defn h ([x] x) ([a b] (+ a b)))
//   /sig h
//     :(Fn [a] a) user/h ; defn        <- 1-arg identity clause (correctly unconstrained)
//     :(Fn [a a] a) user/h             <- 2-arg clause: `(+ a b)` MUST show `:Num`
//
// The 2-arg clause uses `+` (a `Num` method), so its inferred scheme is
// `(Fn [:Num a :Num a] a)` — exactly what a single-signature `(defn add2 [a b]
// (+ a b))` renders. The multi-sig variant renderer STRIPS the constraint,
// showing `(Fn [a a] a)`. repl/spec.md §4.1.1 is explicit: "a clause such as
// `([a b] (+ a b))` displays `:(Fn [:Num a :Num a] a)`, never the
// constraint-stripped `:(Fn [a a] a)` … Dropping the constraint from a variant's
// display is a §1.4 non-conformance even when the bound is still enforced."
//
// This is DISPLAY-ONLY: the bound is enforced (see the negative fence — `(h "a"
// "b")` is rejected `no impl of trait … Num for … String`). The GREEN fence in
// the main test — the single-signature `add2` DOES carry `:Num` — proves the
// renderer is capable; the multi-sig variant path drops it on the way out.
//
// ATTRIBUTION: /qa attributes precisely at S113 Phase 1. The `// defect:` line
// records the batch's provisional read: the OverloadVariant scheme→display path
// (typecheck-or-int) — a display-envelope where the per-variant render diverges
// from the single-signature render for the same inferred scheme.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// TestStandard provides `Num` (+, -, *, /) so a clause using `+` infers the
// `Num` bound. In this prelude the trait renders short as `:Num`.
fn repl_std(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin(lines)
        .output()
}

// D1 — the multi-signature variant that infers `Num` MUST display the bound
// inline, exactly as the single-signature `add2` does. The load-bearing RED: the
// 2-arg clause of `h` renders `(Fn [:Num a :Num a] a) user/h`, not the
// constraint-stripped `(Fn [a a] a) user/h`. The GREEN fence (`add2` carries
// `:Num`) proves the renderer is capable — so a missing constraint on `h`'s
// variant is a variant-path drop, not a whole-renderer gap.
// spec: repl/spec.md §4.1.1 — a multi-signature variant that infers a trait
// bound MUST display it inline (never the constraint-stripped `(Fn [a a] a)`).
// spec: repl/spec.md §1.4 — inline trait-constraint display format.
// defect: class=display-envelope-mirror locus=OverloadVariant scheme→display path (typecheck-or-int; single-sig vs multi-sig variant render diverge for the same inferred scheme) found=S112 owner=/dev
#[test]
fn multi_sig_variant_display_carries_inferred_num_constraint() {
    let out = repl_std(
        "(defn add2 [a b] (+ a b))\n\
         (defn h ([x] x) ([a b] (+ a b)))\n\
         /sig h\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);

    // GREEN fence: the single-signature `add2` — same inferred scheme as h's
    // 2-arg clause — DOES carry `:Num`. This proves the renderer can emit the
    // constraint; if this ever goes RED the whole constraint-display path broke,
    // not just the multi-sig variant path.
    assert!(
        c.contains("(Fn [:Num a :Num a] a) user/add2"),
        "GREEN fence: single-signature `add2` MUST render `(Fn [:Num a :Num a] \
         a) user/add2` — the renderer is capable of emitting the `:Num` \
         constraint; got:\n{c}"
    );

    // Load-bearing RED: h's 2-arg clause `([a b] (+ a b))` infers the SAME `Num`
    // scheme, so it MUST render `(Fn [:Num a :Num a] a) user/h` — exactly as
    // `add2` does (§4.1.1). At HEAD it renders the constraint-stripped
    // `(Fn [a a] a) user/h` — the D1 defect.
    assert!(
        c.contains("(Fn [:Num a :Num a] a) user/h"),
        "the 2-arg variant of `h` infers `Num` (it uses `+`) and MUST display it \
         inline as `(Fn [:Num a :Num a] a) user/h` — exactly as single-signature \
         `add2` does (§4.1.1); it MUST NOT drop the constraint to `(Fn [a a] a) \
         user/h`; got:\n{c}"
    );
}

// D1 negative fence — the bound is ENFORCED; the defect is display-only. Even
// though the 2-arg variant DISPLAYS unconstrained at HEAD, calling it at a type
// with no `Num` impl (`(h "a" "b")`) is still a clean type error — the constraint
// exists in the judgment, it is only lost on the render surface. If this ever
// goes GREEN (the String call accepted) the defect has widened from display-only
// into a soundness hole.
// spec: repl/spec.md §4.1.1 — the inferred bound is enforced even while the
// variant display drops it ("even when the bound is still enforced").
#[test]
fn multi_sig_variant_bound_still_enforced_neg() {
    let out = repl_std(
        "(defn h ([x] x) ([a b] (+ a b)))\n\
         (h \"a\" \"b\")\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("type")
            && c.contains("Num")
            && (c.contains("String") || c.contains("string")),
        "`(h \"a\" \"b\")` MUST be a clean `no impl of trait … Num for … String` \
         type error — the `Num` bound is enforced even though the variant display \
         drops it (display-only defect); got:\n{c}"
    );
    // Must not silently produce a value: the bound is real.
    assert!(
        !c.contains(":primitives/String \"ab\"") && !c.contains(":primitives/Int"),
        "the wrong-type `(h \"a\" \"b\")` MUST NOT succeed to a value — the \
         display-drop must not mask the enforced bound; got:\n{c}"
    );
}
