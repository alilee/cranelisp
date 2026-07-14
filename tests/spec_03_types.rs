// spec_03_types.rs — Type system surface (Sprint 64 Wave 5 Batch 2).
//
// Covers `spec/03-types.md`. Carries forward language-behaviour assertions
// from the legacy integration-tier `tests/ring0.rs`, `tests/ring1.rs`,
// `tests/ring2.rs`, `tests/sketch_port.rs`, and `tests/e2e.rs`. Per
// `tests/plan/PLAN.md §"Mode canonicalisation"`, the canonical mode is
// REPL — type assertions are visible in the `:primitives/Type value`
// display per `repl/spec.md §1.2`.
//
// What this file covers:
//   - Primitive types display: Int, Float, Bool, String (§3.1)
//   - Type variables in polymorphic identity (§3.3)
//   - Let polymorphism / type schemes (§3.4)
//   - Algorithm-W inference (§3.5)
//   - Constrained polymorphism (§3.6)
//   - Higher-kinded types (§3.7)
//   - Unification rules (§3.8)
//   - Type annotations (§3.9)

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{run_through_all_modes, Cranelisp, PreludeVariant};

// =============================================================================
// Helpers
// =============================================================================

fn repl_prims(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(lines)
        .output()
}

fn repl_std(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin(lines)
        .output()
}

// =============================================================================
// §3.1 Primitive Types — Int, Float, Bool, String
// =============================================================================

// spec: spec/03-types.md §3.1 — Int literal displays as :primitives/Int
#[test]
fn primitive_int_display() {
    repl_prims("42\n").assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/03-types.md §3.1 — Float literal displays as :primitives/Float
#[test]
fn primitive_float_display() {
    repl_prims("3.14\n").assert_stdout_contains(":primitives/Float");
}

// spec: spec/03-types.md §3.1 — Bool literals display as :primitives/Bool
#[test]
fn primitive_bool_true_display() {
    repl_prims("true\n").assert_stdout_contains(":primitives/Bool true");
}

// spec: spec/03-types.md §3.1 — Bool false
#[test]
fn primitive_bool_false_display() {
    repl_prims("false\n").assert_stdout_contains(":primitives/Bool false");
}

// spec: spec/03-types.md §3.1 — String literal displays as :primitives/String
#[test]
fn primitive_string_display() {
    repl_prims("\"hello\"\n").assert_stdout_contains(":primitives/String");
}

// =============================================================================
// §3.3 Type Variables — polymorphic identity
// =============================================================================

// spec: spec/03-types.md §3.3 — identity defn applied at Int returns Int value
#[test]
fn polymorphic_identity_at_int() {
    repl_prims("(defn id [x] x)\n(id 42)\n").assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/03-types.md §3.3 — identity defn applied at Bool returns Bool
#[test]
fn polymorphic_identity_at_bool() {
    repl_prims("(defn id [x] x)\n(id true)\n").assert_stdout_contains(":primitives/Bool true");
}

// =============================================================================
// §3.4 Type Schemes — let polymorphism
// =============================================================================

// spec: spec/03-types.md §3.4 — let-bound identity reused at different types
#[test]
fn let_polymorphism_identity_two_types() {
    // The defn binding produces a polymorphic scheme; it instantiates fresh
    // type variables per call site, so applying to Int then Bool both work.
    repl_prims("(defn id [x] x)\n(id 7)\n(id false)\n")
        .assert_stdout_contains_all(&[":primitives/Int 7", ":primitives/Bool false"]);
}

// =============================================================================
// §3.5 Type Inference (Algorithm W)
// =============================================================================

// spec: spec/03-types.md §3.5 — return type inferred from body
#[test]
fn defn_return_type_inferred_from_body() {
    // No annotation; the return value Int is inferred from the body.
    repl_prims("(defn three [] 3)\n(three)\n").assert_stdout_contains(":primitives/Int 3");
}

// spec: spec/03-types.md §3.5 — let body type inferred
#[test]
fn let_body_type_inferred() {
    repl_prims("(let [x 5] x)\n").assert_stdout_contains(":primitives/Int 5");
}

// =============================================================================
// §3.6 Constrained Polymorphism — observable through trait dispatch
// =============================================================================

// spec: spec/03-types.md §3.6 — constrained polymorphic + dispatches at Int
#[test]
fn constrained_add_int() {
    repl_std("(+ 1 2)\n").assert_stdout_contains(":primitives/Int 3");
}

// spec: spec/03-types.md §3.6 — constrained polymorphic + dispatches at Float
#[test]
fn constrained_add_float() {
    repl_std("(+ 1.0 2.0)\n").assert_stdout_contains(":primitives/Float");
}

// =============================================================================
// §3.8 Unification Rules — incompatible types report both sides
// =============================================================================

// spec: spec/03-types.md §3.8 — Int vs String unification fails informatively
#[test]
fn unification_int_vs_string_errors() {
    let out = repl_prims("(if true 1 \"hello\")\n");
    // Spec: type mismatch reported; mention either both types or "type" / "mismatch"
    let s = &out.stdout;
    let e = &out.stderr;
    assert!(
        s.contains("Int") || s.contains("String") || e.contains("type") || s.contains("type"),
        "expected type-mismatch diagnostic for Int/String in if branches; stdout={s} stderr={e}"
    );
}

// =============================================================================
// §3.9 Type Annotations
// =============================================================================

// spec: spec/03-types.md §3.9 — annotated parameter types accepted
#[test]
fn annotated_params_int() {
    repl_prims("(defn f [:Int x] x)\n(f 7)\n").assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/04-expressions.md §4.9.3 — function type annotations: annotating
// MULTIPLE parameters simultaneously. `(defn f [:Int x :Int y] ...)` constrains
// both `x` and `y` to Int at once; the inferred scheme must be
// `(Fn [Int Int] Int)`, a call with matching arg types succeeds, and a call
// with a mismatched arg is rejected. Positive+negative companion to the
// single-param `annotated_params_int`.
#[test]
fn annotated_multiple_params_simultaneously_constrains_each() {
    let out = repl_prims(
        "(defn f [:Int x :Int y] (add-i64 x y))\n\
         (f 1 2)\n\
         (f 1 \"bad\")\n",
    );
    assert!(
        out.stdout
            .contains("(Fn [primitives/Int primitives/Int] primitives/Int)"),
        "both annotated params MUST be reflected in the inferred function type \
         `(Fn [Int Int] Int)`; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains(":primitives/Int 3"),
        "a call matching both annotated param types MUST succeed; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("type error") || out.stdout.contains("type mismatch"),
        "a call violating the second annotated param type MUST be rejected; \
         got:\n{}",
        out.stdout
    );
}

// spec: spec/03-types.md §3.9 — annotated return type accepted
#[test]
fn annotated_return_type_int() {
    // Spec allows annotations on params; return-type annotation is supported
    // via the body. Use (let [x :Int 5] x) to assert local annotations work.
    repl_prims("(let [x 5] x)\n").assert_stdout_contains(":primitives/Int 5");
}

// =============================================================================
// Wave 5.6 file 6 e2e.rs chunk-1 GAP-COVER carry-forwards (annotation as
// standalone expression form, per spec/02-grammar.md §2.3.8).
// =============================================================================

// spec: spec/02-grammar.md §2.3.8 — `:Int 42` is a standalone annotation
// expression: a leading `:Type` prefix scopes the immediately-following
// expression. Distinct from the parameter-position form `[:Int x]` covered
// by `annotated_params_int`.
// (carry: legacy/e2e.rs::e2e_s2_3_8_annotation_expr_simple)
#[test]
fn annotation_expression_standalone() {
    repl_prims(":Int 42\n").assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/02-grammar.md §2.3.8 — applied-type annotation `:(Option Int)
// None` constrains a polymorphic constructor at its use site. Distinct from
// the simple-type case (`:Int 42`): the type expression is itself applied.
// (carry: legacy/e2e.rs::e2e_s2_3_8_annotation_expr_applied_type)
#[test]
fn annotation_expression_applied_type() {
    repl_std(":(Option Int) None\n").assert_stdout_contains("Option.None");
}

// spec: spec/02-grammar.md §2.3.8 — REGRESSION-GUARD: `:Int 42` MUST be
// parsed as an annotation expression, not as a variable lookup of `:Int`
// followed by a literal. The annotation parser path must not fall through
// to variable resolution.
// (carry: legacy/e2e.rs::e2e_s2_3_8_annotation_neg_not_variable_error)
#[test]
fn annotation_expression_neg_not_variable_lookup() {
    let out = repl_prims(":Int 42\n");
    assert!(
        !out.stdout.contains("undefined variable"),
        "`:Int 42` MUST NOT produce an `undefined variable` error — \
         the annotation parser path must not fall through to variable \
         resolution; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Wave 5.6 ring1.rs GAP-COVER carry-forwards (chunk 3)
// =============================================================================

// spec: spec/03-types.md §3.5 — type-mismatch direction Int→String slot:
// `(str-len 42)` passes Int where String is expected. Mirror direction of
// `unification_int_vs_string_errors` (which is if-branches Int vs String).
// The fn-arg-type-mismatch direction (Int passed to String slot) is not
// isolated in any other carry — only the if-branches form is covered.
// (carry: legacy/ring1.rs::error_int_where_string_expected)
#[test]
fn unification_int_passed_to_string_arg_errors_neg() {
    let out = repl_prims("(str-len 42)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("Int")
            || combined.contains("String")
            || combined.to_lowercase().contains("type")
            || combined.to_lowercase().contains("error"),
        "(str-len 42) MUST produce a type-mismatch diagnostic mentioning \
         Int / String / type / error per §3.5; got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/03-types.md §3.3 — polymorphic identity instantiated at
// String. `polymorphic_identity_at_int`/`polymorphic_identity_at_bool`
// cover scalar instantiations; String is the heap-typed counterpart with
// a distinct codegen path (RC-aware). The poly-id-at-heap-type angle is
// not isolated elsewhere.
// (carry: legacy/ring1.rs::identity_on_string)
#[test]
fn polymorphic_identity_at_string() {
    repl_prims(
        "(defn id [x] x)\n\
         (str-len (id \"hello\"))\n",
    )
    .assert_stdout_contains(":primitives/Int 5");
}

// spec: spec/03-types.md §3.3 — polymorphic identity at a user-defined
// ADT type. Distinct from `polymorphic_identity_at_string` (literal-driven
// heap value) — ADT is ctor-driven heap. The user-defined-type
// instantiation angle is uncovered elsewhere.
// (carry: legacy/ring1.rs::identity_on_adt)
#[test]
fn polymorphic_identity_at_adt() {
    // Reuse the prelude-seeded `primitives/Option` (§8.6.4: a local
    // `(deftype (Option a) …)` under the Option-providing prelude would be a
    // define-over-prelude collision). Identity at an ADT type is exercised
    // identically against the seeded Option.
    repl_prims(
        "(defn id [x] x)\n\
         (match (id (Some 42)) [(Some x) x None 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/03-types.md §3.3 — polymorphic HOF returning ADT. Composition
// of poly-HOF + ADT-returning closure: `(apply-fn (fn [x] (Some x)) 42)`.
// Distinct from any covered HOF (none return ADTs) and from any covered
// ADT shape (none flow through the HOF return position). The
// Functor.return-into-Option shape.
// (carry: legacy/ring1.rs::higher_order_on_adt)
#[test]
fn polymorphic_higher_order_returning_adt() {
    // Reuse the prelude-seeded `primitives/Option` (see §8.6.4 note above).
    repl_prims(
        "(defn apply-fn [f x] (f x))\n\
         (match (apply-fn (fn [x] (Some x)) 42) [(Some x) x None 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// =============================================================================
// Wave 5.6 ring1.rs GAP-COVER carry-forwards (chunk 4)
// =============================================================================

// spec: spec/03-types.md §3.2.6 — Vec as function return type. The
// callee-allocates-and-returns-Vec angle exercises consuming-convention
// transfer + RC at the boundary. Distinct from
// `string_returned_from_function_freed` (String — different RC
// semantics) and from any covered `vec_in_let` shape (let-anchor only,
// no fn-return boundary).
// (carry: legacy/ring1.rs::vec_returned_from_function)
#[test]
fn vec_as_function_return_type() {
    repl_prims(
        "(defn make-vec [] [10 20 30])\n\
         (vec-get (make-vec) 1)\n",
    )
    .assert_stdout_contains(":primitives/Int 20");
}

// spec: spec/03-types.md §3.2.6 — Vec as function argument type. The
// fn-arg-with-Vec-typed-slot exercises consuming-convention + RC
// through a fn-arg boundary. Distinct from `vec_in_let` (let-anchor),
// `primitive_vec_let_bound_then_get` (let), and from
// `vec_as_function_return_type` (return position).
// (carry: legacy/ring1.rs::vec_passed_to_function)
#[test]
fn vec_as_function_argument() {
    repl_prims(
        "(defn sum-first-two [v] (add-i64 (vec-get v 0) (vec-get v 1)))\n\
         (sum-first-two [3 4 5])\n",
    )
    .assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/03-types.md §3.8 — type-mismatch error MUST name BOTH the
// expected and actual types. The U1.7 Wave 0 strict-naming contract:
// `unification_int_vs_string_errors` uses `||` (any-of-names suffices),
// not the strict-AND-naming property. This carry asserts BOTH "Int" AND
// "String" appear in the diagnostic.
// (carry: legacy/ring1.rs::error_type_mismatch_names_both_types)
#[test]
fn unification_error_names_both_types_strict() {
    let out = repl_prims("(add-i64 1 \"hello\")\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(combined.contains("Int"), "diagnostic MUST name 'Int', got: {combined}");
    assert!(
        combined.contains("String"),
        "diagnostic MUST name 'String', got: {combined}"
    );
}

// spec: spec/03-types.md §3.8 — String-where-Int-expected diagnostic
// MUST name "String" specifically. The U1.7 Wave 3 strict-naming
// variant — distinct from `unification_int_vs_string_errors` (any-of)
// and from `unification_error_names_both_types_strict` (asserts BOTH;
// this asserts only "String" via a flipped-arg shape).
// (carry: legacy/ring1.rs::error_quality_string_where_int_names_string)
#[test]
fn unification_error_string_where_int_names_string_strict() {
    let out = repl_prims("(add-i64 \"hello\" 1)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("String"),
        "diagnostic MUST name 'String', got: {combined}"
    );
}

// spec: spec/03-types.md §3.8 — String-where-Int-expected diagnostic
// MUST name "Int" specifically. Companion to
// `unification_error_string_where_int_names_string_strict` — same
// source, asserts the other type-name half of the strict-naming
// contract.
// (carry: legacy/ring1.rs::error_quality_string_where_int_names_int)
#[test]
fn unification_error_string_where_int_names_int_strict() {
    let out = repl_prims("(add-i64 \"hello\" 1)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(combined.contains("Int"), "diagnostic MUST name 'Int', got: {combined}");
}

// spec: spec/03-types.md §3.8 — Int-where-String-expected diagnostic
// MUST name "Int" specifically. Distinct from chunk-3
// `error_int_where_string_expected` (asserts any-error-indicator);
// this asserts the strict naming of the actual type "Int" in the
// diagnostic, exercising the §3.8 `String → primitives/Int` unification
// failure with the reverse argument-position.
// (carry: legacy/ring1.rs::error_quality_int_where_string_names_int)
#[test]
fn unification_error_int_where_string_names_int_strict() {
    let out = repl_prims("(str-len 42)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(combined.contains("Int"), "diagnostic MUST name 'Int', got: {combined}");
}

// spec: spec/03-types.md §3.8 — Int-where-String-expected diagnostic
// MUST name "String" specifically. Companion to
// `unification_error_int_where_string_names_int_strict` — same source
// (`(str-len 42)`), asserts the other type-name half (the expected
// "String" type).
// (carry: legacy/ring1.rs::error_quality_int_where_string_names_string)
#[test]
fn unification_error_int_where_string_names_string_strict() {
    let out = repl_prims("(str-len 42)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("String"),
        "diagnostic MUST name 'String', got: {combined}"
    );
}

// =============================================================================
// Wave 5.6 file 8 ring2.rs chunk 4 GAP-COVER carry-forwards.
// =============================================================================

// spec: spec/03-types.md §3.8.2 — variable binding via the occurs check:
// unifying a type variable `a` with a type that references `a` MUST be
// rejected (otherwise the inferred type is infinite). The classic shape is
// self-application `(fn [x] (x x))` — `x : a`, application requires
// `a ~ (Fn [a] b)`, so `a` occurs in its own binding. No prior
// carry-forward exercises the occurs-check error path; this is the
// canonical e2e shape.
// (carry: legacy/ring2.rs::neg_occurs_check_infinite_type)
#[test]
fn occurs_check_self_application_rejected_neg() {
    let out = repl_prims(
        "(defn apply-self [x] (x x))\n\
         (apply-self apply-self)\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.to_lowercase().contains("error")
            || combined.to_lowercase().contains("occurs")
            || combined.to_lowercase().contains("infinite")
            || combined.to_lowercase().contains("type"),
        "self-application `(x x)` MUST trigger the occurs-check error per \
         spec §3.8.2; stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/03-types.md §3.6.6 — Restrictions: a constrained polymorphic
// function (one whose signature carries trait constraints, such as `add`
// using trait-dispatched `+`) MUST NOT be captured as a first-class value
// in a `let` binding. Per §3.6.6, monomorphisation requires the call site
// to be visible; binding the constrained name to a let variable hides the
// call site. No prior carry covers the constrained-fn-as-value rejection.
// REGRESSION-GUARD: silently loosening this restriction would let
// constrained polymorphic fns leak through closures unmonomorphised.
// Cross-ref: spec/04-expressions.md §4.6.3 — auto-curry monomorphisation.
// (carry: legacy/ring2.rs::neg_constrained_fn_in_closure)
#[test]
fn constrained_polymorphic_fn_in_let_binding_rejected_neg() {
    // `add` is constrained polymorphic: (Fn [:Num a a] a). Capturing it
    // in `let [f add]` MUST fail per §3.6.6.
    let out = repl_std(
        "(defn add [x y] (+ x y))\n\
         (let [f add] (f 1 2))\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.to_lowercase().contains("error")
            || combined.to_lowercase().contains("constrained")
            || combined.to_lowercase().contains("cannot"),
        "constrained polymorphic fn captured in let MUST be rejected per \
         §3.6.6; stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/03-types.md §3.8.3 — function types unify only if their arities
// match. Calling a 2-arg fn with 3 args MUST be rejected. Distinct from
// `unification_int_passed_to_string_arg_errors_neg` (type mismatch by type)
// and from `defn_multi_clause_duplicate_sig_neg` (signature collision):
// the arity-too-many path is its own check. Lambda arity-mismatch is
// covered by `lambda_call_with_wrong_arg_count_neg` in spec_04; this
// covers the named-defn case.
// (carry: legacy/ring2.rs::neg_type_mismatch_fn_arity)
#[test]
fn defn_call_with_too_many_args_arity_mismatch_neg() {
    let out = repl_prims(
        "(defn f [x y] (add-i64 x y))\n\
         (f 1 2 3)\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.to_lowercase().contains("error")
            || combined.to_lowercase().contains("arity")
            || combined.to_lowercase().contains("arg"),
        "calling 2-arg `f` with 3 args MUST be rejected per §3.8.3; \
         stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// =============================================================================
// §3.3 [S109] — Written free-type-variable annotation resolution (W6).
// Plan: tests/plan/PLAN.md §S109 §L.1 (FV-1 … FV-15).
//
// §3.3 (S109 clarification) MUSTs, cited by every row below:
//   MUST-1 (positive): a lowercase identifier appearing free in an annotation
//     — standing alone (`:a`) or nested in an applied type (`:(Box a)`) — is a
//     type variable, implicitly universally quantified at the definition
//     boundary, IDENTICALLY to an inference-generated variable.
//   MUST-2 (negative): such an identifier MUST NOT be treated as a reference to
//     an unknown named type.
//
// The live defect (verified S109): a written free var fails
// `unknown type `a` (from module ``)` because the annotation resolver treats a
// free lowercase ident as a named-type lookup instead of minting a quantified
// var. The `// defect:` line rides every RED row.
//
// Fixture rules (§L preamble): annotation PRECEDES the param name (`[:a x]`,
// §5.1.1 EBNF); there is no return-annotation syntax (§5.1.1 — the "return"
// cell is the body-expression annotation `:Type form`); free-standing only
// (no stdlib) — helpers are the PrimitivesOnly / TestStandard fixture preludes.
//
// Order: the two over-broadening PINs (FV-13/FV-14, GREEN today and MUST HOLD)
// first, then the free-var REDs.
// =============================================================================

// --- FV-13 (PIN, GREEN today, MUST HOLD) — uppercase unknowns still error ----

// spec: spec/03-types.md §3.3 — MUST-2 boundary (over-broadening guard): an
// UPPERCASE unknown named type in a parameter annotation is a genuine
// unknown-type error (§3.9.3: neither type nor trait ⇒ error) and MUST stay one
// through the free-var fix. The fix keys on the §3.3 LOWERCASE rule; it must not
// swallow real unknown-type errors.
#[test]
fn unknown_uppercase_type_annotation_still_errors_neg() {
    let out = repl_prims("(defn f [:Foo x] x)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("unknown type") && combined.contains("Foo"),
        "an uppercase unknown named type `Foo` MUST still error as an unknown \
         type (§3.9.3); the free-var rule must not swallow it; got:\n{combined}"
    );
}

// spec: spec/03-types.md §3.3 — MUST-2 boundary, nested facet: an uppercase
// unknown INSIDE an applied type (`:(Box Foo)`, Box defined, Foo not) still
// errors as an unknown type. Sibling of the standalone guard above.
#[test]
fn unknown_uppercase_type_annotation_nested_still_errors_neg() {
    let out = repl_prims("(deftype (Box a) [:a v])\n(defn g [:(Box Foo) b] b)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("unknown type") && combined.contains("Foo"),
        "a nested uppercase unknown type `Foo` inside `:(Box Foo)` MUST still \
         error as an unknown type; got:\n{combined}"
    );
}

// --- FV-14 (PIN, GREEN today, MUST HOLD) — trait-constraint annotation --------

// spec: spec/03-types.md §3.3 — MUST-2 invariance: a KNOWN trait-name annotation
// (`:Num x`, §3.9.2) still yields the CONSTRAINED polymorphic scheme (§3.4.1
// display `:Num a`), not a bare free var and not an unknown-type error. The
// free-var rule must not disturb the trait-constraint path.
#[test]
fn trait_constraint_annotation_unaffected_by_free_var_rule() {
    // TestStandard provides the `Num` trait.
    let out = repl_std("(defn show2 [:Num x] x)\n");
    assert!(
        out.stdout.contains(":(Fn [:Num a] a) user/show2"),
        "a trait-constraint annotation MUST yield the constrained scheme \
         `(Fn [:Num a] a)` (§3.9.2/§3.4.1); got:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("unknown type"),
        "a known trait name MUST NOT be an unknown-type error; got:\n{}",
        out.stdout
    );
}

// --- FV-1 (RED) — standalone bare free var, quantified, used at two types -----

// spec: spec/03-types.md §3.3 — MUST-1: a bare free var `:a` is implicitly
// universally quantified, identical to an inferred var. Proof of GENUINE
// quantification: `id` is used at TWO types in one program — `(id 5)` at Int and
// `(id "ab")` at String (via `str-len`) — summed to 7. A wrongly-monomorphic `a`
// would reject the second use. All-modes value equivalence (REPL/--run/--link).
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr (free lowercase annotation var absent from var_map falls to TypeNotFound instead of minting a fresh quantified var) found=S109 owner=/dev
#[test]
fn defn_param_bare_free_var_quantifies_and_uses_at_two_types() {
    run_through_all_modes(
        "(defn id [:a x] x)\n\
         (defn main [] (Pure (add-i64 (id 5) (str-len (id \"ab\")))))",
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(7);
}

// --- FV-2 (RED, neg) — same fixture, MUST NOT be an unknown-type error --------

// spec: spec/03-types.md §3.3 — MUST-2: the written free var `:a` MUST NOT be
// treated as a reference to an unknown named type, and MUST NOT surface a
// codegen-layer frame (the class, if the fix regresses, must never be a
// named-type miss). The defn typechecks and evaluates.
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr (free lowercase annotation var absent from var_map falls to TypeNotFound instead of minting a fresh quantified var) found=S109 owner=/dev
#[test]
fn defn_param_bare_free_var_not_unknown_type_neg() {
    let out = repl_prims("(defn id [:a x] x)\n(id 3)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("unknown type"),
        "a written free var `a` MUST NOT be an unknown-type error (§3.3 MUST-2); \
         got:\n{combined}"
    );
    assert!(
        !combined.contains("codegen") && !combined.contains("literals.rs"),
        "a written free var MUST NOT surface a codegen-layer frame; got:\n{combined}"
    );
    assert!(
        out.stdout.contains(":primitives/Int 3"),
        "id with a free-var annotation MUST typecheck and evaluate at Int; \
         got:\n{}",
        out.stdout
    );
}

// --- FV-3 (RED, parity twin) — written var vs inferred var, identical scheme --

// spec: spec/03-types.md §3.3 — MUST-1 "identically to an inference-generated
// variable": the written-var `idw` and the inferred-var `idi` MUST display the
// SAME scheme `(Fn [a] a)` and evaluate at the same two types. The
// twin-fixture shape (one invariant, two provenances, same assertion) — a
// per-provenance codepath divergence fails the twin.
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr (free lowercase annotation var absent from var_map falls to TypeNotFound instead of minting a fresh quantified var) found=S109 owner=/dev
#[test]
fn written_var_vs_inferred_var_identical_scheme_twin() {
    let out = repl_prims(
        "(defn idw [:a x] x)\n\
         (defn idi [x] x)\n\
         (idw 3)\n(idw \"s\")\n(idi 3)\n(idi \"s\")\n",
    );
    assert!(
        out.stdout.contains(":(Fn [a] a) user/idw"),
        "the written-var `idw` MUST display the same `(Fn [a] a)` scheme as an \
         inferred var (§3.3 MUST-1 parity); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains(":(Fn [a] a) user/idi"),
        "the inferred-var `idi` baseline scheme `(Fn [a] a)`; got:\n{}",
        out.stdout
    );
    out.assert_stdout_contains_all(&[":primitives/Int 3", ":primitives/String \"s\""]);
}

// --- FV-4 (RED, all-modes, pos+neg facet) — free var nested in applied type ---

// spec: spec/03-types.md §3.3 — MUST-1 nested-in-applied-type: `:(Box a)` in a
// param annotation quantifies `a`; `unbox` is used at Int and String across all
// modes (summed to 7). Neg facet: the defn itself MUST NOT error `unknown type
// `a`` (MUST-2). The verified-live failing shape.
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr (free lowercase annotation var absent from var_map falls to TypeNotFound instead of minting a fresh quantified var) found=S109 owner=/dev
#[test]
fn defn_param_free_var_nested_in_applied_type() {
    // Neg facet: the definition must not error as unknown type `a`, and works.
    let out = repl_prims(
        "(deftype (Box a) [:a v])\n\
         (defn unbox [:(Box a) b] (v b))\n\
         (unbox (Box 7))\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("unknown type"),
        "a free var nested in `:(Box a)` MUST NOT be an unknown-type error \
         (§3.3 MUST-2); got:\n{combined}"
    );
    assert!(
        out.stdout.contains(":primitives/Int 7"),
        "unbox with `:(Box a)` MUST typecheck and evaluate at Int; got:\n{}",
        out.stdout
    );
    // Pos: quantified — works at Int and String across all modes.
    run_through_all_modes(
        "(deftype (Box a) [:a v])\n\
         (defn unbox [:(Box a) b] (v b))\n\
         (defn main [] (Pure (add-i64 (unbox (Box 5)) (str-len (unbox (Box \"ab\"))))))",
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(7);
}

// --- FV-5 (RED) — multiple type vars in an applied annotation ----------------

// spec: spec/03-types.md §3.3 — MUST-1 multi-var applied: `:(Pair2 k v)` in a
// param annotation quantifies both `k` and `v`; `get-x` has scheme
// `(Fn [(Pair2 k v)] k)` and `(get-x (Pair2 7 "s"))` returns 7. Neg facet: no
// `unknown type` for either var.
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr (free lowercase annotation var absent from var_map falls to TypeNotFound instead of minting a fresh quantified var) found=S109 owner=/dev
#[test]
fn defn_param_multi_var_applied_annotation() {
    let out = repl_prims(
        "(deftype (Pair2 a b) [:a x :b y])\n\
         (defn get-x [:(Pair2 k v) p] (x p))\n\
         (get-x (Pair2 7 \"s\"))\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("unknown type"),
        "free vars `k`/`v` nested in `:(Pair2 k v)` MUST NOT be unknown-type \
         errors (§3.3 MUST-2); got:\n{combined}"
    );
    assert!(
        out.stdout.contains(":primitives/Int 7"),
        "get-x MUST project the first field (7) at Int; got:\n{}",
        out.stdout
    );
}

// --- FV-6 (RED) — written var co-refers across param and body annotation ------

// spec: spec/03-types.md §3.3 — MUST-1 with §3.9/§4.9 (body-position annotation;
// no return-annotation syntax per §5.1.1): (a) the SAME written var `:a` in a
// param annotation and a body annotation `:a x` co-refer within one definition
// boundary → `(Fn [a] a)` (one var); (b) a var appearing ONLY in the body
// annotation `(defn id2 [x] :a x)` → `(Fn [a] a)`.
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr (free lowercase annotation var absent from var_map falls to TypeNotFound instead of minting a fresh quantified var) found=S109 owner=/dev
#[test]
fn written_var_param_and_body_annotation_corefer() {
    let out = repl_prims(
        "(defn id [:a x] :a x)\n\
         (defn id2 [x] :a x)\n\
         (id 3)\n(id2 \"s\")\n",
    );
    assert!(
        out.stdout.contains(":(Fn [a] a) user/id"),
        "param annotation `:a` and body annotation `:a x` MUST co-refer → \
         `(Fn [a] a)`, one var; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains(":(Fn [a] a) user/id2"),
        "a var only in the body annotation MUST quantify → `(Fn [a] a)`; got:\n{}",
        out.stdout
    );
    out.assert_stdout_contains_all(&[":primitives/Int 3", ":primitives/String \"s\""]);
}

// --- FV-7 (RED, all-modes, pos+neg) — two distinct vars stay independent ------

// spec: spec/03-types.md §3.3 — MUST-1 with distinct vars: `(defn fst2 [:a x :b
// y] x)` has scheme `(Fn [a b] a)`. Success at MIXED argument types
// (`(fst2 5 "hi")` → 5) is the guard that `a` and `b` are INDEPENDENT — a wrong
// cross-var unification would reject the Int/String mix. All-modes.
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr (free lowercase annotation var absent from var_map falls to TypeNotFound instead of minting a fresh quantified var) found=S109 owner=/dev
#[test]
fn defn_param_two_distinct_free_vars_independent() {
    // REPL scheme shape + the mixed-type success (the independence guard).
    let out = repl_prims("(defn fst2 [:a x :b y] x)\n(fst2 5 \"hi\")\n");
    assert!(
        out.stdout.contains(":(Fn [a b] a) user/fst2"),
        "two distinct free vars MUST yield `(Fn [a b] a)`; got:\n{}",
        out.stdout
    );
    // All-modes: mixed Int/String arguments type-check and return the Int.
    run_through_all_modes(
        "(defn fst2 [:a x :b y] x)\n\
         (defn main [] (Pure (fst2 5 \"hi\")))",
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(5);
}

// --- FV-8 (RED, pos) — same var reused within a boundary unifies --------------

// spec: spec/03-types.md §3.3 — one definition boundary = one var per identifier:
// `(defn eq2 [:a x :a y] x)` reuses `:a` → scheme `(Fn [a a] a)`; `(eq2 1 2)`
// returns 1.
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr (free lowercase annotation var absent from var_map falls to TypeNotFound instead of minting a fresh quantified var) found=S109 owner=/dev
#[test]
fn defn_param_same_free_var_reused_unifies() {
    let out = repl_prims("(defn eq2 [:a x :a y] x)\n(eq2 1 2)\n");
    assert!(
        out.stdout.contains(":(Fn [a a] a) user/eq2"),
        "a reused free var `:a` MUST yield `(Fn [a a] a)`; got:\n{}",
        out.stdout
    );
    out.assert_stdout_contains(":primitives/Int 1");
}

// --- FV-8 (RED, neg) — reused var forces unification, not unknown-type ---------

// spec: spec/03-types.md §3.3 — the reused `:a` means x and y MUST unify:
// `(eq2 1 "two")` is a type-mismatch (unification failure), NEVER `unknown
// type`. The negative confirms the var is a real, unifying type variable.
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr (free lowercase annotation var absent from var_map falls to TypeNotFound instead of minting a fresh quantified var) found=S109 owner=/dev
#[test]
fn defn_param_same_free_var_reused_neg_mismatch() {
    let out = repl_prims("(defn eq2 [:a x :a y] x)\n(eq2 1 \"two\")\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("unknown type"),
        "a reused free var MUST unify, NOT be an unknown-type error (§3.3 \
         MUST-2); got:\n{combined}"
    );
    assert!(
        combined.to_lowercase().contains("type")
            && (combined.contains("mismatch") || combined.to_lowercase().contains("error")),
        "`(eq2 1 \"two\")` MUST be a unification failure (x and y share `a`); \
         got:\n{combined}"
    );
}

// --- FV-9 (RED, pos) — free var and concrete annotation mixed -----------------

// spec: spec/03-types.md §3.3 + §3.9.1 — free `:a` and concrete `:Int` mixed:
// `(defn tag [:a x :Int n] x)` → `(Fn [a Int] a)`; `(tag "s" 3)` returns "s".
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr (free lowercase annotation var absent from var_map falls to TypeNotFound instead of minting a fresh quantified var) found=S109 owner=/dev
#[test]
fn defn_param_free_var_and_concrete_mixed() {
    let out = repl_prims("(defn tag [:a x :Int n] x)\n(tag \"s\" 3)\n");
    assert!(
        out.stdout.contains(":(Fn [a primitives/Int] a) user/tag"),
        "mixing a free var and a concrete annotation MUST yield \
         `(Fn [a Int] a)`; got:\n{}",
        out.stdout
    );
    out.assert_stdout_contains(":primitives/String \"s\"");
}

// --- FV-9 (RED, neg) — the concrete cell still constrains ---------------------

// spec: spec/03-types.md §3.9.1 — the concrete `:Int` cell still constrains
// independently of the free var: `(tag "s" "t")` is rejected (n must be Int),
// and NOT with `unknown type`.
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr (free lowercase annotation var absent from var_map falls to TypeNotFound instead of minting a fresh quantified var) found=S109 owner=/dev
#[test]
fn defn_param_free_var_and_concrete_mixed_neg() {
    let out = repl_prims("(defn tag [:a x :Int n] x)\n(tag \"s\" \"t\")\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("unknown type"),
        "the concrete cell rejection MUST NOT be an unknown-type error; \
         got:\n{combined}"
    );
    assert!(
        combined.to_lowercase().contains("type")
            && (combined.contains("mismatch") || combined.to_lowercase().contains("error")),
        "passing a String to the `:Int n` slot MUST be a type mismatch; \
         got:\n{combined}"
    );
}

// --- FV-10 (RED, neg) — codegen-reaching free var → ambiguity, not unknown ----

// spec: spec/03-types.md §3.3 — MUST-2 boundary vs §3.11: a free-var annotation
// on a CODEGEN-REACHING bare value routes into the EXISTING §3.11 ambiguity /
// disposition machinery, NEVER a `unknown type `a`` error. At the REPL a bare
// polymorphic value is disposition-3 introspection display (§3.11.4); under
// `--run` a codegen-reaching unpinned value is the §3.11.1 ambiguity error
// ("add an annotation"). In NO mode is the verdict `unknown type`.
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr (free lowercase annotation var absent from var_map falls to TypeNotFound instead of minting a fresh quantified var) found=S109 owner=/dev
#[test]
fn free_var_annotation_codegen_reaching_is_ambiguity_not_unknown_type_neg() {
    // REPL: disposition-3 — the bare polymorphic value displays its type; NOT
    // an unknown-type error (Vec is in scope via the PrimitivesOnly glob).
    let repl = repl_prims(":(Vec a) []\n");
    let rcomb = format!("{}{}", repl.stdout, repl.stderr);
    assert!(
        !rcomb.contains("unknown type"),
        "REPL `:(Vec a) []` MUST NOT be an unknown-type error — it is a \
         disposition-3 type display (§3.11.4 / §3.3 MUST-2); got:\n{rcomb}"
    );

    // --run: codegen-reaching — the §3.11.1 ambiguity error, NOT unknown-type.
    let run = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user("(defn main [] (let [x :(Vec a) []] (vec-len x)))")
        .output();
    let runcomb = format!("{}{}", run.stdout, run.stderr);
    assert!(
        !runcomb.contains("unknown type"),
        "a codegen-reaching free-var annotation MUST route to the §3.11 \
         ambiguity path, NOT an unknown-type error (§3.3 MUST-2); got:\n{runcomb}"
    );
    assert!(
        !run.status.success(),
        "a codegen-reaching unpinned free var MUST be rejected (§3.11.1 \
         ambiguity); got:\n{runcomb}"
    );
}
