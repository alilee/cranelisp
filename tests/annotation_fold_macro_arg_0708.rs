// annotation_fold_macro_arg_0708.rs — S115 W1 (post-ruling), FIXME 0708.
//
// USER RULING (2026-07-21, Reading A-structural): a `:Type <form>` annotation folds
// to ONE structural annotated node at READ time, in ALL positions INCLUDING
// macro-argument position. Consequence: an annotated argument passed to a macro is
// a SINGLE argument (the annotated form), not two positional arguments (`:Type` and
// the form). The stdlib `(def x :primitives/Int 5)` MUST succeed (the `def` macro
// receives TWO arguments — `x` and the annotated `5`); the free-standing,
// stdlib-free equivalent below is an inline two-clause macro receiving an annotated
// argument.
//
// TODAY (HEAD, pre-implementation): `:primitives/Int` is delivered to the macro as
// a SEPARATE positional argument, so `(pick 1 :primitives/Int 5)` arrives as THREE
// arguments and dies with `no matching clause … with 3 argument(s); clauses accept
// 1 or 2` — the annotation did NOT fold in macro-argument position. FAILING-NOT-
// IGNORED; the flip trigger is the S116 IMPLEMENTATION wave (this S115 wave scribes
// the ruling + lands the behaviour pin only; no S115 fix wave carries it).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn repl_prims(lines: &str) -> String {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(lines)
        .output();
    format!("{}{}", out.stdout, out.stderr)
}

// RED — the annotation folds in MACRO-ARGUMENT position. `(pick 1 :primitives/Int 5)`
// MUST see TWO arguments (`1` and the annotated `5`), dispatch to the `[x y] y`
// clause, and evaluate the annotated `5` → `:primitives/Int 5`. Today the annotation
// does NOT fold: the macro sees THREE arguments and the `3 argument(s)` arity
// artifact surfaces. This cell asserts that artifact ABSENT (and the fold succeeds).
// Flips with the S116 implementation wave.
// spec: spec/01-lexical.md §1.4.5 — Colon-Prefixed Symbols [S115 ruling — Reading
// A-structural; :Type folds the following form in ALL positions incl. macro-arg;
// implementation carries to S116]
// defect: class=wrong-reject locus=frontend/int annotation-fold seam — `:Type` not folded in macro-argument position (0708) found=S115 owner=/dev
#[test]
fn annotation_folds_in_macro_argument_position() {
    let c = repl_prims("(defmacro pick ([x] x) ([x y] y))\n(pick 1 :primitives/Int 5)\n");
    assert!(
        !c.contains("3 argument(s)"),
        "the annotation `:primitives/Int` MUST fold into the following form `5` in \
         macro-argument position (Reading A-structural), so `pick` receives TWO \
         arguments — NOT three. Today the `3 argument(s)` arity artifact surfaces \
         (the annotation was passed as a separate positional argument). got:\n{c}"
    );
    assert!(
        c.contains(":primitives/Int 5"),
        "the folded annotated argument MUST dispatch to the `[x y] y` clause and \
         evaluate to `:primitives/Int 5`; got:\n{c}"
    );
}

// GREEN control TWIN — the SAME macro call WITHOUT the annotation already works
// today (`pick` receives two plain arguments `1` and `5`, returns `5`). Fences the
// boundary: the RED above is specifically about the ANNOTATION folding, not about
// the two-argument macro-call shape itself.
// spec: spec/02-grammar.md §2.3.8 — Type Annotation [S115 ruling — Reading
// A-structural; the un-annotated two-argument macro call is the boundary control]
#[test]
fn macro_two_arg_call_without_annotation_control_green() {
    let c = repl_prims("(defmacro pick ([x] x) ([x y] y))\n(pick 1 5)\n");
    assert!(
        c.contains(":primitives/Int 5"),
        "the un-annotated two-argument macro call `(pick 1 5)` MUST dispatch to the \
         `[x y] y` clause and evaluate to `:primitives/Int 5`; got:\n{c}"
    );
    assert!(
        !c.contains("3 argument(s)"),
        "the un-annotated control MUST NOT show an arity artifact; got:\n{c}"
    );
}
