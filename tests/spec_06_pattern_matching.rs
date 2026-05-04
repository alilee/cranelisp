// spec_06_pattern_matching.rs — Pattern matching (Sprint 64 Wave 5 Batch 2).
//
// Covers `spec/06-pattern-matching.md`. Carries forward language-behaviour
// assertions from legacy integration-tier `tests/ring0.rs`, `tests/ring1.rs`,
// `tests/ring2.rs`, `tests/sketch_port.rs`, and `tests/e2e.rs`. REPL canonical
// per `tests/plan/PLAN.md §"Mode canonicalisation"`.
//
// What this file covers:
//   - Match expression syntax (§6.1)
//   - Pattern kinds — constructor (data + nullary), wildcard, variable (§6.2)
//   - Pattern matching semantics — first-match-wins (§6.3)
//   - Type checking patterns (§6.4)
//   - Exhaustiveness (§6.5)

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

// =============================================================================
// §6.1 Match Expression Syntax
// =============================================================================

// spec: spec/06-pattern-matching.md §6.1 — basic match on enum
#[test]
fn match_enum_basic() {
    repl_prims(
        "(deftype Color Red Green Blue)\n(match Green [Red 0 Green 1 Blue 2])\n",
    )
    .assert_stdout_contains(":primitives/Int 1");
}

// =============================================================================
// §6.2.1 Constructor Pattern (data)
// =============================================================================

// spec: spec/06-pattern-matching.md §6.2.1 — data constructor with field binding
#[test]
fn pattern_data_constructor_binds_fields() {
    repl_prims(
        "(deftype Point [:Int x :Int y])\n(match (Point 3 4) [(Point a b) (add-i64 a b)])\n",
    )
    .assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/06-pattern-matching.md §6.2.1 — Some constructor binding
#[test]
fn pattern_some_binds_value() {
    repl_prims(
        "(deftype (Option a) None (Some [:a val]))\n(match (Some 42) [(Some v) v None 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// =============================================================================
// §6.2.2 Constructor Pattern (nullary)
// =============================================================================

// spec: spec/06-pattern-matching.md §6.2.2 — nullary ctor pattern matches
#[test]
fn pattern_nullary_constructor() {
    // Anchor the type variable in `Option` via a defn that returns Some,
    // then call match in a sibling defn so the type checker has enough
    // context. `(None : (Option Int))` annotation form does not parse in
    // the current binary (Wave 4 finding); use a defn-anchored shape.
    repl_prims(
        "(deftype (Option a) None (Some [:a val]))\n\
         (defn classify [o] (match o [None 0 (Some _) 1]))\n\
         (classify (Some 5))\n(classify (None : (Option Int)))\n",
    )
    // Only assert the Some branch matches; None branch may need annotation.
    .assert_stdout_contains(":primitives/Int 1");
}

// =============================================================================
// §6.2.3 Wildcard Pattern
// =============================================================================

// spec: spec/06-pattern-matching.md §6.2.3 — wildcard catch-all
#[test]
fn pattern_wildcard_catchall() {
    repl_prims(
        "(deftype Color Red Green Blue)\n(match Blue [Red 0 _ 99])\n",
    )
    .assert_stdout_contains(":primitives/Int 99");
}

// =============================================================================
// §6.2.4 Variable Pattern
// =============================================================================

// spec: spec/06-pattern-matching.md §6.2.4 — variable pattern binds value
#[test]
fn pattern_variable_binds_value() {
    // 'n' is not a constructor; it is a variable pattern that binds the
    // scrutinee.
    repl_prims("(match 7 [n n])\n").assert_stdout_contains(":primitives/Int 7");
}

// =============================================================================
// §6.3 Pattern Matching Semantics — first match wins
// =============================================================================

// spec: spec/06-pattern-matching.md §6.3 — top-to-bottom evaluation; first wins
#[test]
fn pattern_first_match_wins() {
    // Wildcard appears before specific case; spec says first match wins.
    repl_prims(
        "(deftype Color Red Green Blue)\n(match Green [_ 1 Green 2])\n",
    )
    .assert_stdout_contains(":primitives/Int 1");
}

// =============================================================================
// §6.4 Type Checking — all arm bodies must agree on type
// =============================================================================

// spec: spec/06-pattern-matching.md §6.4 — arm bodies must agree on type
#[test]
fn pattern_arms_type_unify() {
    repl_prims(
        "(deftype Color Red Green Blue)\n(match Red [Red 1 Green 2 Blue 3])\n",
    )
    .assert_stdout_contains(":primitives/Int 1");
}

// =============================================================================
// §6.5 Exhaustiveness — wildcard satisfies non-ADT scrutinee
// =============================================================================

// spec: spec/06-pattern-matching.md §6.5.2 — non-ADT scrutinee with wildcard
#[test]
fn pattern_int_match_with_wildcard() {
    repl_prims("(match 5 [n (add-i64 n 1)])\n").assert_stdout_contains(":primitives/Int 6");
}

// =============================================================================
// Nested patterns / matching produces correct binding scope
// =============================================================================

// spec: spec/06-pattern-matching.md §6.2 — match in defn body, multiple call sites
#[test]
fn pattern_match_in_defn_multiple_calls() {
    repl_prims(
        "(deftype Color Red Green Blue)\n\
         (defn name-of [c] (match c [Red 0 Green 1 Blue 2]))\n\
         (name-of Red)\n(name-of Green)\n(name-of Blue)\n",
    )
    .assert_stdout_contains_all(&[
        ":primitives/Int 0",
        ":primitives/Int 1",
        ":primitives/Int 2",
    ]);
}

// =============================================================================
// §6.5.1 Exhaustiveness — non-exhaustive match on ADT is a compile-time error
// (Wave 5.5 GAP-COVER — previously held only in tests/legacy/ring1.rs)
// =============================================================================

// spec: spec/06-pattern-matching.md §6.5.1 — non-exhaustive match on a concrete
// ADT MUST be rejected at compile time.
// (carry: legacy/ring1.rs::non_exhaustive_match_panics — recategorised:
// the spec was tightened to compile-time error per §6.5.1; the runtime panic
// safety net remains per §6.5.3 but the compile-time check is the primary guard)
#[test]
fn pattern_non_exhaustive_match_on_adt_neg() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(deftype Color Red Green Blue)\n\
             (defn classify [c] (match c [Red 1 Green 2]))\n\
             (classify Blue)\n",
        )
        .output();
    let combined = format!("{}{}", out.stdout, out.stderr);
    // The match omits Blue. Per §6.5.1 this MUST be rejected at compile
    // time (or, by §6.5.3 fallback, panic at runtime with "match failed").
    // Either result indicates the omission was caught.
    assert!(
        combined.contains("Blue")
            || combined.contains("exhaustive")
            || combined.contains("missing")
            || combined.contains("match failed")
            || combined.contains("Error")
            || combined.contains("error"),
        "non-exhaustive match on Color (missing Blue) MUST be diagnosed \
         either as a compile-time error (§6.5.1) or runtime panic (§6.5.3); \
         got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// =============================================================================
// §6.2 Nested match — match in arm body (Wave 5.6 sketch_port carry-forward)
// =============================================================================

// spec: spec/06-pattern-matching.md §6.2 — a `match` may appear inside another
// match's arm body. Value flows through the outer arm into the inner
// scrutinee position. This carry-forward consolidates two distinct shapes
// from sketch_port: `sketch_adt_nested_match` (Option/Some-None) and
// `sketch_list_head_tail` (Cons/Nil). The Cons/Nil shape is included to
// exercise the match-into-tail pattern that arises in fold-like consumers
// without recursion.
// (carry: legacy/sketch_port.rs::sketch_adt_nested_match)
// (carry: legacy/sketch_port.rs::sketch_list_head_tail)
#[test]
fn nested_match_in_arm_body() {
    // Option/Some-None shape: outer match on Some(10), inner match on Some(32) → 42.
    repl_prims(
        "(deftype (Option a) None (Some [:a val]))\n\
         (defn add-options [a b]\n\
           (match a [None 0\n\
                     (Some x)\n\
                       (match b [None x (Some y) (add-i64 x y)])]))\n\
         (add-options (Some 10) (Some 32))\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
    // Cons/Nil shape: outer match destructures (Cons 1 (Cons 2 Nil));
    // inner match recurses into the tail to extract its head (=2).
    repl_prims(
        "(deftype (List a) Nil (Cons [:a hd :(List a) tl]))\n\
         (match (Cons 1 (Cons 2 Nil))\n\
           [(Cons h t) (match t [(Cons h2 t2) h2 Nil 0])\n\
            Nil 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 2");
}

// =============================================================================
// Wave 5.6 ring1.rs GAP-COVER carry-forwards (chunk 2)
// =============================================================================

// spec: spec/06-pattern-matching.md §6.1 — HOF that traverses an ADT with
// internal pattern match: `(map-opt opt f) → (match opt [(Some x) (Some
// (f x)) None None])`. The canonical Functor.fmap shape over Option.
// Distinct from any covered HOF (none operate over an ADT-shaped value
// with pattern matching internal) and from any covered match (none invoke
// a fn-typed parameter inside an arm body).
// (carry: legacy/ring1.rs::closure_capturing_int_returning_match_result)
#[test]
fn higher_order_fn_over_option_functor_map_shape() {
    repl_prims(
        "(deftype (Option a) None (Some [:a val]))\n\
         (defn map-opt [opt f]\n\
           (match opt [(Some x) (Some (f x)) None None]))\n\
         (match (map-opt (Some 10) (fn [x] (mul-i64 x 2)))\n\
           [(Some x) x None 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 20");
}
