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

use helpers::e2e::{Cranelisp, PreludeVariant, run_through_all_modes};

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
    repl_prims("(deftype Color Red Green Blue)\n(match Green [Red 0 Green 1 Blue 2])\n")
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
    // Reuse the prelude-seeded `primitives/Option` (§8.6.4: a local Option
    // deftype under the Option-providing prelude is a define-over-prelude
    // collision). Some-binding behaviour is unchanged.
    repl_prims("(match (Some 42) [(Some v) v None 0])\n")
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
    // Reuse the prelude-seeded `primitives/Option` (see §8.6.4 note above).
    repl_prims(
        "(defn classify [o] (match o [None 0 (Some _) 1]))\n\
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
    repl_prims("(deftype Color Red Green Blue)\n(match Blue [Red 0 _ 99])\n")
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
    repl_prims("(deftype Color Red Green Blue)\n(match Green [_ 1 Green 2])\n")
        .assert_stdout_contains(":primitives/Int 1");
}

// =============================================================================
// §6.4 Type Checking — all arm bodies must agree on type
// =============================================================================

// spec: spec/06-pattern-matching.md §6.4 — arm bodies must agree on type
#[test]
fn pattern_arms_type_unify() {
    repl_prims("(deftype Color Red Green Blue)\n(match Red [Red 1 Green 2 Blue 3])\n")
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
    // Reuse the prelude-seeded `primitives/Option` (§8.6.4: a local Option
    // deftype under the Option-providing prelude is a define-over-prelude
    // collision). The (List a) shape below is a non-seeded name — legal.
    repl_prims(
        "(defn add-options [a b]\n\
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
    // Reuse the prelude-seeded `primitives/Option` (see §8.6.4 note above).
    repl_prims(
        "(defn map-opt [opt f]\n\
           (match opt [(Some x) (Some (f x)) None None]))\n\
         (match (map-opt (Some 10) (fn [x] (mul-i64 x 2)))\n\
           [(Some x) x None 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 20");
}

// =============================================================================
// Wave 5.6 ring1.rs GAP-COVER carry-forwards (chunk 4)
// =============================================================================

// spec: spec/06-pattern-matching.md §6.5.2 — non-ADT scrutinee + wildcard
// pattern: `(match b [_ (if b 1 0)])` where `b : Bool`. Distinct from
// `pattern_int_match_with_wildcard` (Int + variable) and from
// `pattern_wildcard_catchall` (ADT + wildcard). The Bool+wildcard
// shape exercises the §6.5.2 "wildcard or variable required for
// non-ADT scrutinee" rule against the Bool primitive.
// (carry: legacy/ring1.rs::match_non_adt_bool_wildcard)
#[test]
fn pattern_bool_match_with_wildcard() {
    repl_prims(
        "(defn bool-to-int [b] (match b [_ (if b 1 0)]))\n\
         (bool-to-int true)\n",
    )
    .assert_stdout_contains(":primitives/Int 1");
}

// spec: spec/06-pattern-matching.md §6.5.1 — non-exhaustive ADT match
// MUST be a compile-time error naming the type AND the missing
// constructor. This is the strict-naming variant: the diagnostic for
// a Color match missing `Blue` MUST contain BOTH "Color" AND "Blue".
// `pattern_non_exhaustive_match_on_adt_neg` is the loose-or form.
// (carry: legacy/ring1.rs::neg_exhaustive_match_missing_constructor_compile_error)
#[test]
fn pattern_exhaustive_error_names_type_and_missing_ctor_strict_neg() {
    let out = repl_prims(
        "(deftype Color Red Green Blue)\n\
         (defn pick [c] (match c [Red 1 Green 2]))\n\
         (pick Blue)\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("Color"),
        "exhaustiveness diagnostic MUST name the ADT type 'Color', got: {combined}"
    );
    assert!(
        combined.contains("Blue"),
        "exhaustiveness diagnostic MUST name the missing ctor 'Blue', got: {combined}"
    );
}

// spec: spec/06-pattern-matching.md §6.5.1 — non-exhaustive ADT match
// MUST list ALL missing constructors. With a single-Red arm on Color,
// the diagnostic MUST contain BOTH "Green" AND "Blue". Distinct from
// the prior single-missing-ctor test (which omits one); this asserts
// the lists-all-missing angle (omitting two).
// (carry: legacy/ring1.rs::neg_exhaustive_match_single_arm_lists_all_missing)
#[test]
fn pattern_exhaustive_error_lists_all_missing_ctors_neg() {
    let out = repl_prims(
        "(deftype Color Red Green Blue)\n\
         (defn pick [c] (match c [Red 1]))\n\
         (pick Green)\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("Green") && combined.contains("Blue"),
        "exhaustiveness diagnostic MUST list ALL missing ctors (Green AND Blue), got: {combined}"
    );
}

// spec: spec/06-pattern-matching.md §6.5.2 — match with empty arms
// MUST be a compile-time error. A match cannot be exhaustive on
// `Int`/`Bool`/`String`/etc. without a wildcard or variable pattern;
// `(match b [])` has neither and MUST be rejected.
// (carry: legacy/ring1.rs::neg_match_empty_arms_rejected)
#[test]
fn pattern_match_empty_arms_rejected_neg() {
    let out = repl_prims(
        "(defn pick [b] (match b []))\n\
         (pick true)\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.to_lowercase().contains("error")
            || combined.to_lowercase().contains("exhaustive")
            || combined.to_lowercase().contains("arm"),
        "match with empty arms MUST be rejected per §6.5.2, got: {combined}"
    );
}

// spec: spec/06-pattern-matching.md §6.5.2 — non-ADT scrutinee with
// constructor patterns from a different ADT MUST be rejected. The
// type-mismatch enforces the "wildcard or variable required" rule
// indirectly: only those patterns type-check against `Int`/`Bool`/
// `String`/etc. Using `None`/`(Some _)` ctor patterns on an `Int`
// scrutinee MUST fail.
// (carry: legacy/ring1.rs::neg_match_non_adt_scrut_with_adt_constructor_rejected)
#[test]
fn pattern_non_adt_scrut_rejects_adt_ctor_pattern_neg() {
    // Reuse the prelude-seeded `primitives/Option` for `None`/`(Some _)` — a
    // local Option deftype under the Option-providing prelude would inject a
    // §8.6.4 define-over-prelude error that MASKS this negative's real intent
    // (the earlier `contains("error")` was satisfied by that collision, not by
    // the pattern rejection under test). With the collision gone, the ONLY
    // error is the genuine §6.5.2 rejection: `None`/`(Some _)` patterns force
    // the scrutinee to `(Option _)`, so calling `(pick 5)` with an `Int` is a
    // type mismatch. Assert on that specific mismatch, not a bare "error".
    let out = repl_prims(
        "(defn pick [n] (match n [None 1 (Some _) 2]))\n\
         (pick 5)\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    let lc = combined.to_lowercase();
    assert!(
        lc.contains("type mismatch")
            && lc.contains("option")
            && combined.contains("primitives/Int"),
        "constructor patterns on a non-ADT (Int) scrutinee MUST be rejected \
         per §6.5.2 with an Option-expected/Int-got type mismatch, got: {combined}"
    );
}

// spec: spec/06-pattern-matching.md §6.6.1 — nested constructor
// patterns are NOT supported and MUST be rejected. `(Some (Point x y))`
// nests a Point ctor pattern inside a Some ctor pattern. Per §6.6.1
// pattern matching is one level deep only. Consolidates the legacy
// duplicate pair `error_nested_pattern` + `neg_nested_pattern_rejected`
// (both same source, same assertion — Sprint 16 added the second
// without consolidating).
// (carry: legacy/ring1.rs::error_nested_pattern,
//  consolidates legacy/ring1.rs::neg_nested_pattern_rejected)
#[test]
fn pattern_nested_constructor_rejected_neg() {
    // Reuse the prelude-seeded `primitives/Option` for `Some`/`None` — a local
    // Option deftype under the Option-providing prelude would inject a §8.6.4
    // define-over-prelude error that MASKS this negative's real intent (the
    // earlier `contains("error")` was satisfied by that collision). `Point` is
    // a non-seeded name, so its deftype stays. With the Option collision gone,
    // the ONLY rejection is the genuine §6.6.1 one: the nested constructor
    // pattern `(Some (Point x y))` does not parse (one level deep only) — the
    // parser expects a symbol binder after `Some`, not a nested ctor form.
    let out = repl_prims(
        "(deftype Point [:Int x :Int y])\n\
         (defn bad [opt] (match opt [(Some (Point x y)) (add-i64 x y) None 0]))\n\
         (bad None)\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    let lc = combined.to_lowercase();
    assert!(
        lc.contains("parse error") && lc.contains("expected symbol"),
        "nested constructor pattern `(Some (Point x y))` MUST be rejected per \
         §6.6.1 (patterns are one level deep) — the parser rejects the nested \
         ctor form with `expected symbol`, got: {combined}"
    );
}

// spec: spec/06-pattern-matching.md §6.3.3 — match arm bodies MUST
// type-agree. The diagnostic MUST name BOTH conflicting types ("Int"
// AND "String") in the strict variant. `error_match_arm_type_mismatch`
// uses any-of-types form; this asserts both names per the U1.7 Wave
// 3 error-quality contract. Subsumes the Wave-0 #9
// `error_match_arm_type_disagreement`.
// (carry: legacy/ring1.rs::error_quality_match_arm_type_mismatch,
//  subsumes legacy/ring1.rs::error_match_arm_type_disagreement)
#[test]
fn pattern_match_arm_body_type_mismatch_names_both_types_strict_neg() {
    let out = repl_prims(
        "(deftype Color Red Green Blue)\n\
         (match Red [Red 1 Green \"two\" Blue 3])\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("Int"),
        "diagnostic MUST name 'Int', got: {combined}"
    );
    assert!(
        combined.contains("String"),
        "diagnostic MUST name 'String', got: {combined}"
    );
}

// spec: spec/06-pattern-matching.md §6.2.1 — constructor pattern with
// wrong arity MUST be rejected. Consolidates the legacy
// `neg_pattern_wrong_binding_count` (too few — `(Point x)` for
// `Point[:Int x :Int y]`) and `neg_pattern_too_many_bindings` (too
// many — `(Point a b c)`) into one carry per audit #25.
// (carry: legacy/ring1.rs::neg_pattern_wrong_binding_count,
//  consolidates legacy/ring1.rs::neg_pattern_too_many_bindings)
#[test]
fn pattern_constructor_arity_mismatch_neg() {
    let out_few = repl_prims(
        "(deftype Point [:Int x :Int y])\n\
         (match (Point 3 4) [(Point x) x])\n",
    );
    let combined_few = format!("{}{}", out_few.stdout, out_few.stderr);
    assert!(
        combined_few.to_lowercase().contains("error")
            || combined_few.to_lowercase().contains("arity")
            || combined_few.to_lowercase().contains("field"),
        "Point ctor pattern with too few bindings MUST be rejected per §6.2.1, got: {combined_few}"
    );

    let out_many = repl_prims(
        "(deftype Point [:Int x :Int y])\n\
         (match (Point 3 4) [(Point a b c) a])\n",
    );
    let combined_many = format!("{}{}", out_many.stdout, out_many.stderr);
    assert!(
        combined_many.to_lowercase().contains("error")
            || combined_many.to_lowercase().contains("arity")
            || combined_many.to_lowercase().contains("field"),
        "Point ctor pattern with too many bindings MUST be rejected per §6.2.1, got: {combined_many}"
    );
}

// =============================================================================
// §6.6.2 No Literal Patterns — rejection coverage (S93, FIXME 0433 owed Neg)
//
// §6.6.2: "Integer, float, string, and boolean literals MUST NOT appear as
// patterns. A literal in pattern position is rejected at compile time (the
// implementation reports `invalid pattern`)." The existing coverage was the
// positive workaround only; these are the owed `_neg` rejection guards that
// upgrade §6.6.2 toward [Tested+Neg]. COVERAGE posture: HEAD already rejects, so
// these pass on HEAD — that is the correct outcome (the spec MUST is honoured).
// =============================================================================

// spec: spec/06-pattern-matching.md §6.6.2 — an INTEGER literal in pattern
// position MUST be rejected at compile time with `invalid pattern`.
#[test]
fn match_literal_pattern_int_rejected_neg() {
    let out = repl_prims("(match 0 [0 \"zero\" _ \"other\"])\n");
    let combined = format!("{}{}", out.stdout, out.stderr).to_lowercase();
    assert!(
        combined.contains("invalid pattern"),
        "an integer literal pattern MUST be rejected with `invalid pattern` per \
         §6.6.2, got: {combined}"
    );
}

// spec: spec/06-pattern-matching.md §6.6.2 — a STRING literal in pattern
// position MUST be rejected at compile time with `invalid pattern`.
#[test]
fn match_literal_pattern_string_rejected_neg() {
    let out = repl_prims("(match \"x\" [\"x\" 1 _ 0])\n");
    let combined = format!("{}{}", out.stdout, out.stderr).to_lowercase();
    assert!(
        combined.contains("invalid pattern"),
        "a string literal pattern MUST be rejected with `invalid pattern` per \
         §6.6.2, got: {combined}"
    );
}

// spec: spec/06-pattern-matching.md §6.6.2 — a BOOLEAN literal in pattern
// position MUST be rejected at compile time with `invalid pattern`. (§6.5.2
// cross-ref: a Bool scrutinee MUST use a wildcard/variable pattern.)
#[test]
fn match_literal_pattern_bool_rejected_neg() {
    let out = repl_prims("(match true [true 1 _ 0])\n");
    let combined = format!("{}{}", out.stdout, out.stderr).to_lowercase();
    assert!(
        combined.contains("invalid pattern"),
        "a boolean literal pattern MUST be rejected with `invalid pattern` per \
         §6.6.2, got: {combined}"
    );
}

// =============================================================================
// FIXME 0434 sweep (this sprint) — qualified-AND-bare name positions the REPL
// displays qualified. Constructor-pattern position. verify-on-HEAD: a row that
// passes is a standing [Tested+Neg] guard against re-rooting regression of the
// qualified path; a row that FAILS is a newly-surfaced sibling defect → handed
// to /frontend (the D-qual-impl-target resolver) with this minimal repro.
// =============================================================================

// spec: spec/06-pattern-matching.md §6.2 + spec/08-modules.md §8.5 — a
// MODULE-QUALIFIED constructor pattern (`user/Green`) in `match` MUST resolve
// identically to the bare constructor pattern (`Green`); the qualified form MUST
// NOT be re-rooted (to a phantom `user/user/Green`). Both forms select the same
// arm and yield the same value.
#[test]
fn match_qualified_constructor_pattern_resolves() {
    // Bare control: `Green` selects arm → 1.
    repl_prims(
        "(deftype Color Red Green Blue)\n\
         (match Green [Red 0 Green 1 Blue 2])\n",
    )
    .assert_stdout_contains(":primitives/Int 1");

    // Qualified: `user/Green` MUST resolve to the same canonical ctor and select
    // the same arm → 1. The phantom double-root MUST NOT appear.
    repl_prims(
        "(deftype Color Red Green Blue)\n\
         (match Green [Red 0 user/Green 1 Blue 2])\n",
    )
    .assert_stdout_contains(":primitives/Int 1")
    .assert_stdout_does_not_contain("user/user/");
}

// =============================================================================
// Sprint 109 — dotted-`Type.Ctor` pattern position (DC-4/DC-5) + the
// exhaustiveness `.`-strip blast-radius guard (BR-1, arch-pre-flagged) +
// qualified-ctor pattern auto-load (M2-P). Plan: tests/plan/PLAN.md §S109 §D/§H.
// Fixtures are stdlib-free (own modules; --run mode for module resolution).
// =============================================================================

fn combined(out: &helpers::e2e::CrOutput) -> String {
    format!("{}\n{}", out.stdout, out.stderr)
}

// spec: spec/06-pattern-matching.md §6.2.1/§6.2.2 — the DOTTED constructor
// pattern always resolves REGARDLESS of scrutinee type: `(Maybe.Some x)` binds
// positionally and the dotted nullary `Maybe.Nil` arm matches; field-binding
// arity and exhaustiveness are computed against the type the dotted ctor names.
// Never scrutinee-contingent (contrast DC-11/DC-5). Fixture uses concrete
// construction only — no free-type-var param annotation (W1 fixture constraint).
// Mode-relevant DC twin: run through REPL/--run/--link.
// defect: class=enumeration-miss locus=crates/cranelisp-typecheck/src/checker.rs::resolve_dotted_field_accessor found=S108 owner=/dev
#[test]
fn same_named_ctors_dotted_pattern_position_disambiguates() {
    run_through_all_modes(
        "(import [primitives [Pure add-i64]])\n\
         (deftype (Maybe a) Nil (Some [:a v]))\n\
         (deftype (Option a) Nil (Some [:a v]))\n\
         (defn main [] (Pure\n\
           (add-i64 (match (Maybe.Some 7) [(Maybe.Some x) x Maybe.Nil 0])\n\
                    (match Maybe.Nil [(Maybe.Some x) x Maybe.Nil 3]))))\n",
        PreludeVariant::None,
    )
    .assert_all_equal(10);
}

// spec: spec/06-pattern-matching.md §6.2.1/§6.2.2 — scrutinee-directed (W1
// re-ruling, landed): a contested BARE constructor pattern RESOLVES against a
// DETERMINED scrutinee type. Here the scrutinee is determined via a unique ctor
// `(MOnly 7)` (concrete construction — no free-type-var annotation); the bare
// `(Some x)` arm resolves to `Maybe.Some` and the bare `None` arm to `Maybe.None`
// (data + nullary legs). REPLACES the pre-re-ruling "requires dotted" expectation.
// RED today: the bare contested pattern is not scrutinee-directed — it picks the
// wrong type, producing `type mismatch: Maybe vs Option`.
// defect: class=silent-accept locus=crates/cranelisp-typecheck (contested bare ctor pattern not resolved against the determined scrutinee type) found=S109 owner=/dev
#[test]
fn contested_bare_pattern_resolves_against_determined_scrutinee() {
    run_through_all_modes(
        "(import [primitives [Pure]])\n\
         (deftype (Maybe a) None (Some [:a v]) (MOnly [:a w]))\n\
         (deftype (Option a) None (Some [:a v]))\n\
         (defn main [] (Pure\n\
           (match (MOnly 7) [(Some x) x None 0 (MOnly w) w])))\n",
        PreludeVariant::None,
    )
    .assert_all_equal(7);
}

// spec: spec/06-pattern-matching.md §6.2.1 + §8.6.5 (NEG) — a contested bare
// constructor pattern is poisoned ONLY when the scrutinee type cannot
// disambiguate it. Here the scrutinee is an unannotated defn parameter with no
// other constraint (the §6.2.1 "indeterminate scrutinee" case): bare `(Some x)`
// MUST be a compile error listing the canonical alternatives. In-test control:
// the SAME match written dotted compiles. The negative targets the indeterminate
// case ONLY — a determined-scrutinee bare pattern is DC-11's positive.
// RED today: the indeterminate bare pattern silently compiles (poison absent).
// defect: class=silent-accept locus=crates/cranelisp-typecheck (indeterminate-scrutinee contested bare pattern silently resolves instead of poisoning) found=S109 owner=/dev
#[test]
fn contested_bare_pattern_indeterminate_scrutinee_poisoned_neg() {
    // Neg: indeterminate scrutinee (unannotated param) ⇒ poison.
    let neg = Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure Int]])\n\
             (deftype (Maybe a) None (Some [:a v]))\n\
             (deftype (Option a) None (Some [:a v]))\n\
             (defn f [m] (match m [(Some x) x None 0]))\n\
             (defn main [] (Pure 0))\n",
        )
        .run("main.cl")
        .output();
    let text = combined(&neg);
    assert!(
        !neg.status.success(),
        "an INDETERMINATE-scrutinee contested bare pattern MUST poison (§6.2.1), \
         not silently resolve; {text}"
    );
    assert!(
        text.contains("Maybe.Some") && text.contains("Option.Some"),
        "the poison error MUST list the canonical alternatives; {text}"
    );
    assert!(
        !text.contains("__expr"),
        "the diagnostic MUST NOT leak the internal `__expr` binder (0568); {text}"
    );
    // Control: the SAME match written dotted disambiguates and compiles.
    Cranelisp::new()
        .file(
            "ctrl.cl",
            "(import [primitives [Pure Int]])\n\
             (deftype (Maybe a) None (Some [:a v]))\n\
             (deftype (Option a) None (Some [:a v]))\n\
             (defn f [m] (match m [(Maybe.Some x) x Maybe.None 0]))\n\
             (defn main [] (Pure 0))\n",
        )
        .run("ctrl.cl")
        .output()
        .assert_ok();
}

// spec: spec/06-pattern-matching.md §6.5 exhaustiveness × the `.`-strip (design
// §4.1 — ARCH-PRE-FLAGGED blast radius). A TOTAL match written with dotted arms
// compiles with NO "non-exhaustive" diagnostic — the covered-set normalizer must
// `.`-strip dotted arms to recognise them as covering the type's constructors.
// Fixture uses concrete construction only — no free-type-var param annotation
// (W1 fixture constraint). RED until dotted patterns resolve; permanent
// fail-on-revert guard after.
#[test]
fn match_over_dotted_covered_ctor_not_false_nonexhaustive_neg() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure Int]])\n\
             (deftype (Maybe a) Nil (Some [:a v]))\n\
             (defn main [] (Pure\n\
               (match (Maybe.Some 5) [(Maybe.Some x) x Maybe.Nil 0])))\n",
        )
        .run("main.cl")
        .output();
    let text = combined(&out);
    assert!(
        !text.contains("non-exhaustive") && !text.contains("not exhaustive"),
        "a TOTAL match with dotted arms MUST NOT be flagged non-exhaustive \
         (BR-1 `.`-strip); {text}"
    );
    out.assert_exit(5);
}

// spec: spec/08-modules.md §8.5.4 edge 1 (pattern position, M2-P) — a qualified
// constructor pattern `(shapes/Circle r)` auto-loads its defining module and
// resolves in pattern position, matching value-position auto-load.
#[test]
fn fq_ctor_pattern_position_autoloads() {
    let aux = "(import [primitives [Int]])\n(deftype Circle [:Int r])\n";
    let entry = "(import [primitives [Pure Int]])\n\
                 (defn area [:shapes/Circle c] :Int (match c [(shapes/Circle r) r]))\n\
                 (defn main [] (Pure (area (shapes/Circle 8))))\n";
    Cranelisp::new()
        .file("shapes.cl", aux)
        .file("main.cl", entry)
        .run("main.cl")
        .output()
        .assert_exit(8);
    Cranelisp::new()
        .file("shapes.cl", aux)
        .file("main.cl", entry)
        .link_then_run("main.cl")
        .output()
        .assert_exit(8);
}

// =============================================================================
// Sprint 109 W1.2 — DC-11-Blocker: the tag-order class (arch §10.9). The
// committed DC-11/DC-6 greens are tag-layout coincidences; these differing-
// layout twins expose the silent wrong-ctor soundness Blocker (typecheck records
// the scrutinee-directed resolution in `pattern_ctors`, but the backend
// re-resolves the bare name context-free via a DashMap in arbitrary order → wrong
// module's same-named ctor, wrong tag/arity, runtime `match failed`, run-to-run
// nondeterminism). Plan: tests/plan/PLAN.md §S109 §D.3.
// =============================================================================

// spec: spec/06-pattern-matching.md §6.2.1 scrutinee-directed + arch §10.9 —
// DC-12 (the decisive rows): two in-scope types share a ctor name with DIFFERENT
// tags AND arities — `(Maybe a) None (Some [:a v])` (Some = tag 1, arity 1) vs
// `Opt2 (Some [:Int a :Int b]) None2` (Some = tag 0, arity 2). Scrutinee-directed
// bare `(Some …)` matched over BOTH types in ONE program, both directions. The
// two `deftype`s are authored in BOTH source orders (two legs, identical
// assertions) — the DashMap-arbitrary-iteration failure mode means both orders
// MUST give the correct, identical result (order-invariance IS the negative).
// Concrete `:Int` fields only (clear of the W6 poly-annotation defect). REPL +
// --run + --link parity. RED today: the backend picks the wrong same-named ctor,
// producing an arity mismatch ("constructor 'Some' has 1 fields but pattern has 2
// bindings") / wrong value instead of 35.
// defect: class=resolver-mirror locus=cranelisp-backend/src/compiler/match_codegen.rs::compile_constructor_pattern (context-free re-resolution ignores typecheck's pattern_ctors — differing tag/arity twin resolves to the wrong candidate) found=S109 owner=/dev
#[test]
fn contested_bare_pattern_differing_layout_twins_both_orders() {
    let body = "(defn main [] (Pure\n\
                  (add-i64 (match (Maybe.Some 5) [(Some x) x None 0])\n\
                           (match (Opt2.Some 10 20) [(Some x y) (add-i64 x y) None2 0]))))\n";
    // Leg 1 — source order: Maybe then Opt2.
    run_through_all_modes(
        &format!(
            "(import [primitives [Pure add-i64 Int]])\n\
             (deftype (Maybe a) None (Some [:a v]))\n\
             (deftype Opt2 (Some [:Int a :Int b]) None2)\n\
             {body}"
        ),
        PreludeVariant::None,
    )
    .assert_all_equal(35);
    // Leg 2 — source order swapped: Opt2 then Maybe. Order-invariance: identical.
    run_through_all_modes(
        &format!(
            "(import [primitives [Pure add-i64 Int]])\n\
             (deftype Opt2 (Some [:Int a :Int b]) None2)\n\
             (deftype (Maybe a) None (Some [:a v]))\n\
             {body}"
        ),
        PreludeVariant::None,
    )
    .assert_all_equal(35);
}

// spec: spec/06-pattern-matching.md §6.3 + arch §10.9 — DC-13 cross-module
// nondeterminism regression guard. The `/review` `xmod.cl` repro: the same ctor
// name `Some` across TWO imported modules with differing tag orders
// (`maybemod`: Some = tag 0; `optmod`: Some = tag 1). A scrutinee-directed bare
// `(Some x)` on a `Maybe.Some` scrutinee MUST resolve to `maybemod`'s Some.
// THREE consecutive `--run` invocations MUST give the SAME correct value 7.
// RED today: nondeterministic (observed exit 1/7/7) — the backend re-resolves the
// bare name context-free, sometimes picking `optmod`'s `Some` (wrong tag) →
// `runtime panic: match failed`. Per the forbidden-disposition rule, 1-in-3 wrong
// is a real bug, never "flaky".
// defect: class=resolver-mirror locus=cranelisp-backend/src/compiler/match_codegen.rs::compile_constructor_pattern (context-free re-resolution; the pattern_ctors sidecar never consumed — typecheck and backend disagree, one seam up from AN-2) found=S109 owner=/dev
#[test]
fn xmod_same_named_ctor_pattern_deterministic_across_runs() {
    // Each iteration is an independent fresh `--run` process (fresh tmpdir +
    // fresh cache) so the DashMap-order nondeterminism is maximally exposed.
    fn run_once() -> (Option<i32>, String) {
        let out = Cranelisp::new()
            .file(
                "maybemod.cl",
                "(import [primitives [Int]])\n(deftype (Maybe a) (Some [:a v]) MNone)\n",
            )
            .file(
                "optmod.cl",
                "(import [primitives [Int]])\n(deftype (Option a) ONone (Some [:a v]))\n",
            )
            .file(
                "xmod.cl",
                "(import [primitives [Pure]])\n\
                 (import [maybemod [Maybe]])\n\
                 (import [optmod [Option]])\n\
                 (defn main [] (Pure (match (Maybe.Some 7) [(Some x) x MNone 0])))\n",
            )
            .run("xmod.cl")
            .output();
        (out.status.code(), format!("{}\n{}", out.stdout, out.stderr))
    }
    let mut codes = Vec::new();
    for i in 0..3 {
        let (code, text) = run_once();
        assert!(
            !text.contains("match failed"),
            "run {i}: cross-module same-named ctor resolved to the WRONG candidate \
             (runtime `match failed`) — the resolver-mirror Blocker; {text}"
        );
        assert_eq!(
            code,
            Some(7),
            "run {i}: MUST deterministically return 7 (scrutinee-directed \
             `Maybe.Some`); a differing value is the nondeterministic wrong-ctor \
             bug (never flaky); {text}"
        );
        codes.push(code);
    }
    assert!(
        codes.iter().all(|c| *c == Some(7)),
        "three consecutive --run invocations MUST agree on 7; got {codes:?}"
    );
}
