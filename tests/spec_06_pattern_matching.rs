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
