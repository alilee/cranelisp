// Sprint 116 structural annotation folding beyond the baseline macro-argument
// pin: recursive positions, malformed subjects, and cache persistence.

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

// RED — folding recurses inside application operands and nested expression
// subjects; each annotation and subject form one node before AST construction.
// spec: spec/01-lexical.md §1.4.5 — annotation folding is recursive in every
// expression position.
// defect: class=wrong-reject locus=frontend reader annotation fold — nested/application positions retain positional annotation tokens found=S116 owner=/dev
#[test]
fn nested_and_application_annotations_fold_recursively() {
    let c = repl("(add-i64 :Int (add-i64 :Int 1 :Int 2) :Int 3)\n");
    assert!(
        c.contains(":primitives/Int 6") && !c.to_lowercase().contains("error"),
        "got:\n{c}"
    );
}

// RED — a qualified compound type is the annotation half and the following Vec
// literal is its one structural subject, including through a macro boundary.
// spec: spec/01-lexical.md §1.4.5 and spec/09-macros.md §9.2.
// defect: class=wrong-reject locus=frontend reader/macro annotation carrier — qualified compound annotation is split from subject found=S116 owner=/dev
#[test]
fn qualified_compound_annotation_round_trips_through_macro() {
    let c = repl(
        "(defmacro pass ([x] x))\n\
         (vec-len (pass :(Vec primitives/Int) [1 2 3]))\n",
    );
    assert!(
        c.contains(":primitives/Int 3") && !c.contains("2 argument(s)"),
        "got:\n{c}"
    );
}

// RED — the structural carrier survives cold serialization and warm restore;
// stale positional pairing must not reappear from cache.
// spec: spec/01-lexical.md §1.4.5 and design/backend/module-caching.md §14 —
// structural annotations retain equivalent meaning after cache round-trip.
// defect: class=carrier-loss locus=frontend/int cache annotation carrier — folded annotation shape not persisted/restored structurally found=S116 owner=/dev
#[test]
fn structural_annotation_cold_warm_cache_round_trip() {
    let cold = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .user(
            "(defmacro pass ([x] x))\n\
             (defn main [] (Pure (pass :Int (add-i64 20 22))))\n",
        )
        .run("user.cl")
        .output();
    assert_eq!(
        cold.status.code(),
        Some(42),
        "cold:\n{}{}",
        cold.stdout,
        cold.stderr
    );
    let warm = cold.run_again().run("user.cl").output();
    assert_eq!(
        warm.status.code(),
        Some(42),
        "warm:\n{}{}",
        warm.stdout,
        warm.stderr
    );
}

// RED — an annotation introducer at EOF has no subject and is rejected at the
// introducer rather than surviving as a value token.
// spec: spec/01-lexical.md §1.4.5 — every annotation requires a following subject.
// defect: class=silent-accept locus=frontend reader annotation fold — dangling EOF annotation lacks located missing-subject rejection found=S116 owner=/dev
#[test]
fn dangling_annotation_at_eof_rejected_neg() {
    let c = repl(":Int\n");
    assert!(
        c.to_lowercase().contains("error") && (c.contains("subject") || c.contains("annotation")),
        "got:\n{c}"
    );
}

// RED — a delimiter cannot serve as an annotation subject; the diagnostic is
// attached to the dangling annotation inside the list.
// spec: spec/01-lexical.md §1.4.5 — malformed/delimiter-ended annotation rejects.
// defect: class=wrong-reject locus=frontend reader annotation fold — closing delimiter leaves annotation unpaired or mislocated found=S116 owner=/dev
#[test]
fn annotation_before_closing_delimiter_rejected_neg() {
    let c = repl("(add-i64 1 :Int)\n");
    assert!(
        c.to_lowercase().contains("error") && (c.contains("subject") || c.contains("annotation")),
        "got:\n{c}"
    );
}
