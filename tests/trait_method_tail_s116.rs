// Sprint 116 §7.1 one-tail acceptance matrix. These cells intentionally pin
// the settled syntax before its frontend/typecheck implementation.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn repl(src: &str) -> String {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(src)
        .output();
    format!("{}{}", out.stdout, out.stderr)
}

// RED — a non-type trailing expression is the default body; there is no return
// type slot before it. Omission from the impl must dispatch to the inferred body.
// spec: spec/07-traits.md §7.1 and §7.1.5 — one trailing element; expression
// tail classifies as an inferred default method.
// defect: class=wrong-reject locus=frontend/typecheck trait method-tail classification — parser requires legacy return-type-plus-body spelling found=S115 owner=/dev
#[test]
fn inferred_default_body_is_the_single_tail_and_dispatches() {
    let c = repl(
        "(deftrait Sized (size [x] Int) (bump [x] (add-i64 (size x) 1)))\n\
         (impl Sized Int (defn size [x] x))\n\
         (bump 6)\n",
    );
    assert!(
        c.contains(":primitives/Int 7"),
        "single-tail inferred default MUST dispatch; got:\n{c}"
    );
}

// RED — ordinary value annotation folds with its subject into one structural
// tail; it constrains the inferred result without reviving the deleted slot.
// spec: spec/07-traits.md §7.1 — an annotated default body is one trailing
// element and its annotation is an optional result constraint.
// defect: class=wrong-reject locus=reader annotation fold + trait tail classifier — annotated body is read as two legacy trailing forms found=S115 owner=/dev
#[test]
fn annotated_default_body_is_one_structural_tail() {
    let c = repl(
        "(deftrait Sized (size [x] Int) (bump [x] :Int (add-i64 (size x) 1)))\n\
         (impl Sized Int (defn size [x] x))\n\
         (bump 8)\n",
    );
    assert!(
        c.contains(":primitives/Int 9"),
        "annotated default MUST dispatch; got:\n{c}"
    );
}

// RED — the old three-element spelling is no longer compatibility syntax. The
// diagnostic must reject the second trailing form at declaration time.
// spec: spec/07-traits.md §7.1 — `[params] return-type body` is deleted.
// defect: class=silent-accept locus=frontend trait method parser — legacy three-element spelling remains accepted found=S115 owner=/dev
#[test]
fn deleted_return_type_plus_body_spelling_rejected_neg() {
    let c = repl("(deftrait Sized (size [x] Int 7))\n");
    assert!(
        c.to_lowercase().contains("error") && !c.contains("; deftrait"),
        "deleted `[params] return-type body` spelling MUST reject; got:\n{c}"
    );
}

// RED — occurrence is not a nullary-only rule: every annotated parameter is a
// concrete non-self type and the concrete result mentions self nowhere.
// spec: spec/07-traits.md §7.1.1 — no implementing-type occurrence rejects at
// any arity with the occurrence reason.
// defect: class=silent-accept locus=typecheck trait occurrence validation — non-nullary all-concrete signature bypasses occurrence check (FIXME 0805) found=S115 owner=/dev
#[test]
fn nonnullary_no_self_occurrence_rejected_at_declaration_neg() {
    let c = repl("(deftrait Convertible (convert [:String s] Int))\n");
    assert!(
        c.contains("no occurrence of the implementing type"),
        "got:\n{c}"
    );
}

// GREEN — bare `x` is an implementing-type occurrence and a required bare type
// tail remains the required-method spelling.
// spec: spec/07-traits.md §7.1 and §7.1.1.
#[test]
fn required_method_bare_type_tail_control_green() {
    let c = repl(
        "(deftrait Sized (size [x] Int))\n\
         (impl Sized Int (defn size [x] x))\n\
         (size 4)\n",
    );
    assert!(c.contains(":primitives/Int 4"), "got:\n{c}");
}

// RED — replacing an impl must re-stage an omitted default body and resolve its
// sibling call against the replacement, not a stale or missing definition.
// spec: spec/07-traits.md §7.1.5 and spec/05-definitions.md §5.4.5 — defaults
// survive impl replacement and dispatch through the replacement's siblings.
// defect: class=check-gate-leak locus=typecheck/backend re-impl default synthesis — default sibling reference becomes undefined after replacement (FIXME 0832) found=S115 owner=/dev
#[test]
fn reimpl_default_body_calls_replaced_sibling() {
    let c = repl(
        "(deftrait Sized (size [x] Int) (tag [x] (add-i64 (size x) 1000)))\n\
         (deftype Box [:Int n])\n\
         (impl Sized Box (defn size [b] (match b [(Box v) v])))\n\
         (impl Sized Box (defn size [b] (match b [(Box v) (mul-i64 v 10)])))\n\
         (tag (Box 5))\n",
    );
    assert!(
        c.contains(":primitives/Int 1050"),
        "replacement sibling must feed the default body; got:\n{c}"
    );
    assert!(
        !c.contains("undefined function"),
        "default sibling reference leaked to codegen; got:\n{c}"
    );
}

// RED — conformance checks parameter count before accepting a first impl.
// spec: spec/05-definitions.md §5.4.5 — impl parameter count must equal the
// trait method signature.
// defect: class=silent-accept locus=typecheck impl conformance — extra unused binder is discarded and dispatch succeeds (FIXME 0833) found=S115 owner=/dev
#[test]
fn first_impl_extra_parameter_rejected_neg() {
    let c = repl(
        "(deftype Box [:Int n])\n\
         (deftrait Sized (size [x] Int))\n\
         (impl Sized Box (defn size [b junk] 3))\n",
    );
    assert!(
        c.to_lowercase().contains("error") && c.to_lowercase().contains("param"),
        "got:\n{c}"
    );
}

// RED — the identical arity error on a replacement is rejected atomically;
// the prior conforming implementation remains dispatchable.
// spec: spec/05-definitions.md §5.4.5 — re-impl uses the same conformance gate
// and a rejected replacement does not partially enroll.
// defect: class=silent-accept locus=typecheck impl conformance/re-impl transaction — extra unused binder accepted on replacement found=S115 owner=/dev
#[test]
fn reimpl_extra_parameter_rejected_and_prior_impl_survives_neg() {
    let c = repl(
        "(deftype Box [:Int n])\n\
         (deftrait Sized (size [x] Int))\n\
         (impl Sized Box (defn size [b] 7))\n\
         (impl Sized Box (defn size [b junk] 3))\n\
         (size (Box 0))\n",
    );
    assert!(
        c.to_lowercase().contains("error") && c.contains(":primitives/Int 7"),
        "got:\n{c}"
    );
}
