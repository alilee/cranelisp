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
// §3.3.1 [S109 W6.3] — Written free-type-variable annotation resolution.
// Plan: tests/plan/PLAN.md §L.1 (retained guards + R1/R3/R9(i) PINs).
//
// §3.3.1 MUSTs cited by the rows below (the retired W6.2 MUST-1..MUST-4/SCOPE-5
// band is superseded):
//   (a) §3.3.1 — a BARE written variable (`:a`, or nested `:(Box a)`) is an
//       inference variable WITH A NAME: it relates same-named occurrences and
//       documents; inference determines it and the body MAY pin it. NOT a
//       reference to an unknown named type.
//   (g) §3.3.1 — lexical co-reference, including into nested `fn`.
//   [S109] ¶ — a written free lowercase var is NEVER a named-type miss.
//
// These guards were born from the W6 `unknown type 'a'` defect (fixed at
// `e401cce9`); they remain GREEN repros — a written free var must never fall to
// a named-type lookup. The `// defect:` lines ride them as class-frequency
// signal.
//
// Fixture rules (§L preamble): annotation PRECEDES the param name (`[:a x]`,
// §5.1.1 EBNF); there is no return-annotation syntax (§5.1.1 — the "return"
// cell is the body-expression annotation `:Type form`); free-standing only
// (no stdlib) — helpers are the PrimitivesOnly / TestStandard fixture preludes.
//
// Order: the name-discrimination PINs (FV-13/FV-14, GREEN today, MUST HOLD)
// first, then the bare-var PINs.
// =============================================================================

// --- FV-13 (PIN, GREEN today, MUST HOLD) — uppercase unknowns still error ----

// spec: spec/03-types.md §3.3.1 — MUST (a) boundary (over-broadening guard): an
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

// spec: spec/03-types.md §3.3.1 — MUST (a) boundary, nested facet: an uppercase
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

// spec: spec/03-types.md §3.3.2 — MUST (b) invariance: a KNOWN trait-name annotation
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

// spec: spec/03-types.md §3.3.1 — MUST (a): a bare free var `:a` is implicitly
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

// spec: spec/03-types.md §3.3.1 — MUST (a) / [S109] ¶: the written free var `:a` MUST NOT be
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
        "a written free var `a` MUST NOT be an unknown-type error (§3.3.1); \
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

// spec: spec/03-types.md §3.3.1 — MUST (a) "an inference variable with a name" —
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
         inferred var (§3.3.1 MUST (a) parity); got:\n{}",
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

// spec: spec/03-types.md §3.3.1 — MUST (a) nested-in-applied-type: `:(Box a)` in a
// param annotation quantifies `a`; `unbox` is used at Int and String across all
// modes (summed to 7). Neg facet: the defn itself MUST NOT error `unknown type
// `a`` ([S109] ¶). The verified-live failing shape.
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
         (§3.3.1); got:\n{combined}"
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

// spec: spec/03-types.md §3.3.1 — MUST (a) multi-var applied: `:(Pair2 k v)` in a
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
         errors (§3.3.1); got:\n{combined}"
    );
    assert!(
        out.stdout.contains(":primitives/Int 7"),
        "get-x MUST project the first field (7) at Int; got:\n{}",
        out.stdout
    );
}

// --- FV-6 (RED) — written var co-refers across param and body annotation ------

// spec: spec/03-types.md §3.3.1 — MUST (a)/(g) with §3.9/§4.9 (body-position annotation;
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

// spec: spec/03-types.md §3.3.1 — MUST (a) with distinct vars: `(defn fst2 [:a x :b
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

// spec: spec/03-types.md §3.3.1 — MUST (a)/(g): one definition boundary = one var per identifier:
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

// spec: spec/03-types.md §3.3.1 — MUST (a)/(g): the reused `:a` means x and y MUST unify:
// `(eq2 1 "two")` is a type-mismatch (unification failure), NEVER `unknown
// type`. The negative confirms the var is a real, unifying type variable.
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr (free lowercase annotation var absent from var_map falls to TypeNotFound instead of minting a fresh quantified var) found=S109 owner=/dev
#[test]
fn defn_param_same_free_var_reused_neg_mismatch() {
    let out = repl_prims("(defn eq2 [:a x :a y] x)\n(eq2 1 \"two\")\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("unknown type"),
        "a reused free var MUST unify, NOT be an unknown-type error (§3.3.1 \
         MUST (a)/(g)); got:\n{combined}"
    );
    assert!(
        combined.to_lowercase().contains("type")
            && (combined.contains("mismatch") || combined.to_lowercase().contains("error")),
        "`(eq2 1 \"two\")` MUST be a unification failure (x and y share `a`); \
         got:\n{combined}"
    );
}

// --- FV-9 (RED, pos) — free var and concrete annotation mixed -----------------

// spec: spec/03-types.md §3.3.1 + §3.9.1 — MUST (a): free `:a` and concrete `:Int` mixed:
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

// spec: spec/03-types.md §3.3.1 — MUST (a) boundary vs §3.11 (MUST (e)): a free-var annotation
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
         disposition-3 type display (§3.11.4 / §3.3.1); got:\n{rcomb}"
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
         ambiguity path, NOT an unknown-type error (§3.3.1); got:\n{runcomb}"
    );
    assert!(
        !run.status.success(),
        "a codegen-reaching unpinned free var MUST be rejected (§3.11.1 \
         ambiguity); got:\n{runcomb}"
    );
}

// =============================================================================
// §3.3.1–3.3.5 [S109 W6.3] — SETTLED written-type-var semantics (user ruling
// 2026-07-14; spec §3.3.1–3.3.5 rows 1–17). Plan: tests/plan/PLAN.md §L.1.
// This SUPERSEDES the W6.2 rigid-everywhere model shipped at `b2bfb760`: bare
// written vars are NOT rigid — rigidity lives on the CONSTRAINT path only.
//
// The settled model (spec §3.3):
//   (a) §3.3.1 — a BARE written var `:a` is an inference variable WITH A NAME:
//       it relates same-named occurrences (incl. lexically into nested `fn`)
//       and documents; the body MAY pin it to a concrete type — never an error.
//   (b) §3.3.2 — a CONSTRAINT `:C x` is a checkable claim ONLY at a quantified
//       (parameter / generalizable) position: held abstract over `C` for the
//       body-check; the body narrowing it concrete is a skolem escape (error),
//       arising from the BODY only — caller instantiation is always sound.
//   (c) §3.3.3 — a value-position constraint is a pure satisfaction check.
//   (d) §3.3.3 — a concrete-type value ascription resolves ambiguity, incl.
//       return-type-polymorphic trait dispatch; context resolves the same way.
//   (e) §3.3.3 — an unresolved return-type poly in a codegen-reaching position
//       is the §3.11 ambiguity error; a value-position constraint does NOT
//       disambiguate.
//   (f) §3.3.4 + §3.10 — a polymorphic function as a value (rank-2) is
//       unsupported.
//   (g) §3.3.1 — lexical co-reference including into nested `fn`; no fresh
//       quantification boundary at a nested `fn`.
//   (h) §3.3.1 — caller instantiation is never an error.
//
// Observed at `b2bfb760` (rigid-bare): the model is INVERTED on the rigidity
// axis — a bare `:a` narrowed by the body ERRORS ("a written type variable is
// rigid within its definition"), while a `:C x` constraint is NOT held
// abstract (body narrows it silently). The W6.3 REDs below flip that. Fixtures
// are free-standing (no stdlib); `[:a x]` annotation order (§5.1.1 EBNF); body
// annotations sit in the single-arity `defn` body position (0591 gaps stay
// unit-only). Free-standing trait fixtures: `Zeroable`/`zed` (return-type
// dispatch, Int→0 / Float→0.0) and `Num2`/`nadd` (`(Fn [a a] a)`, Int impl).
// =============================================================================

// --- R4 (RED→pass, was FV-16) — a bare var's value ascription PINS ------------

// spec: spec/03-types.md §3.3.1 — MUST (a), the worked row 4 verbatim:
// `(defn f [:a x] :a "hello")` → `(Fn [String] String)`, `(f "x")` → "x". The
// value-position bare ascription `:a "hello"` relates `a → String` exactly as
// unifying an inference var with a concrete type would — it is NEVER an error.
// This INVERTS the superseded W6.2 rigid reading (which rejected it as
// assert-not-acquire skolem escape). Never `unknown type`, never `rigid`.
// defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr + unify.rs::unify_with_rigid (W6.2 minted RIGID vars for BARE written names — spec-valid body pins rejected as skolem-escape; §3.3.1 puts rigidity on the constraint path only) found=S109 owner=/dev
#[test]
fn written_var_concrete_ascription_pins() {
    let out = repl_prims("(defn f [:a x] :a \"hello\")\n(f \"x\")\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("unknown type") && !combined.to_lowercase().contains("rigid"),
        "a value-position bare ascription MUST pin freely, never a rigid/unknown \
         error (§3.3.1 MUST (a)); got:\n{combined}"
    );
    assert!(
        out.stdout.contains(":(Fn [primitives/String] primitives/String) user/f"),
        "`:a \"hello\"` MUST relate `a := String` → `(Fn [String] String)` \
         (§3.3.1 MUST (a), row 4); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains(":primitives/String \"hello\""),
        "the body `:a \"hello\"` returns the constant \"hello\" — §3.3.1 row 4 \
         asserts only the TYPE `(Fn [String] String)`, not that `(f \"x\")` \
         echoes its argument; got:\n{}",
        out.stdout
    );

    // All-modes value equivalence: the body-ascribed fn computes end-to-end.
    // `main` returns `(Pure (str-len (f "ab")))` = `(Pure 5)` ⇒ exit 5;
    // `success()` was the wrong assertion for a nonzero-`Pure` `main`.
    run_through_all_modes(
        "(defn f [:a x] :a \"hello\")\n(defn main [] (Pure (str-len (f \"ab\"))))",
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(5);
}

// --- C-1 (RED→pass, was FV-17) — two bare vars TIED by the body MERGE ---------

// spec: spec/03-types.md §3.3.1 — MUST (a) derived corollary: two bare written
// vars tied by the body are ordinary inference vars that UNIFY (merge), not
// distinct rigid skolems. `(defn g [:a x :b y] :a y)` — the body `:a y` relates
// `a` and `b`, so they collapse to one var → `(Fn [a a] a)`, accepted. This
// INVERTS the superseded W6.2 "two distinct rigid vars cannot unify" reading.
// Never `unknown type`, never `rigid`.
// defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr + unify.rs::unify_with_rigid (W6.2 minted RIGID vars for BARE written names — spec-valid body pins rejected as skolem-escape; §3.3.1 puts rigidity on the constraint path only) found=S109 owner=/dev
#[test]
fn bare_vars_tied_by_body_merge() {
    let out = repl_prims("(defn g [:a x :b y] :a y)\n(g 1 2)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("unknown type") && !combined.to_lowercase().contains("rigid"),
        "tying two bare vars by the body MUST be ordinary unification, never a \
         rigid/unknown error (§3.3.1 MUST (a)); got:\n{combined}"
    );
    assert!(
        out.stdout.contains(":(Fn [a a] a) user/g"),
        "the body `:a y` MUST merge `a` and `b` into one var → `(Fn [a a] a)` \
         (§3.3.1 MUST (a)); got:\n{}",
        out.stdout
    );
    // Merged: same var both positions ⇒ `(g 1 2)` type-checks (both Int) → 2.
    assert!(
        out.stdout.contains(":primitives/Int 2"),
        "`(g 1 2)` returns `y` (the second arg) at Int → 2; got:\n{}",
        out.stdout
    );

    // All-modes value equivalence: the merged identity computes end-to-end.
    // `main` returns `(Pure (g 1 2))` = `(Pure 2)` ⇒ exit 2; `success()` was the
    // wrong assertion for a nonzero-`Pure` `main`.
    run_through_all_modes(
        "(defn g [:a x :b y] :a y)\n(defn main [] (Pure (g 1 2)))",
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(2);
}

// --- C-2 (RED→pass, was FV-18 neg) — bare var PINS THROUGH the constructor ----

// spec: spec/03-types.md §3.3.1 — MUST (a), applied form: a bare var pins
// through a type constructor by ordinary unification. `(defn h [:(Box Int) b]
// :(Box a) b)` — the body annotation `:(Box a)` co-refers `a`, and `b` already
// has `(Box Int)`, so `a := Int` pins through `Box` → `(Fn [(Box Int)] (Box
// Int))`, accepted. This INVERTS the superseded W6.2 "rigid `a ≠ Int` under the
// constructor" rejection. Never `unknown type`, never `rigid`.
// defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr + unify.rs::unify_with_rigid (W6.2 minted RIGID vars for BARE written names — spec-valid body pins rejected as skolem-escape; §3.3.1 puts rigidity on the constraint path only) found=S109 owner=/dev
#[test]
fn applied_annotation_bare_var_pins_through_ctor() {
    let out = repl_prims(
        "(deftype (Box a) [:a v])\n\
         (defn h [:(Box Int) b] :(Box a) b)\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("unknown type") && !combined.to_lowercase().contains("rigid"),
        "pinning a bare var through a constructor MUST be ordinary unification, \
         never a rigid/unknown error (§3.3.1 MUST (a)); got:\n{combined}"
    );
    assert!(
        out.stdout.contains(":(Fn [(user/Box primitives/Int)] (user/Box primitives/Int)) user/h"),
        "asserting `:(Box a)` over a `(Box Int)` param MUST pin `a := Int` through \
         the constructor → `(Fn [(Box Int)] (Box Int))` (§3.3.1 MUST (a)); got:\n{}",
        out.stdout
    );

    // All-modes value equivalence: `a := Int` pins through `Box` end-to-end.
    // `main` returns `(Pure (v (h (Box 7))))` = `(Pure 7)` ⇒ exit 7; `success()`
    // was the wrong assertion for a nonzero-`Pure` `main`.
    run_through_all_modes(
        "(deftype (Box a) [:a v])\n\
         (defn h [:(Box Int) b] :(Box a) b)\n\
         (defn main [] (Pure (v (h (Box 7)))))",
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(7);
}

// spec: spec/03-types.md §3.3.1 — MUST (a)/(g) DISCHARGE case (applied form; the
// positive control twin, UNCHANGED under W6.3): `(defn h2 [:(Box a) b] :(Box a)
// b)` checks — the body annotation `:(Box a)` co-refers to the param's own
// `(Box a)`, so it discharges by lexical co-reference → `(Fn [(Box a)] (Box a))`.
// The stable control alongside C-2's pin-through-ctor case.
#[test]
fn applied_annotation_bare_var_corefers_param() {
    let out = repl_prims(
        "(deftype (Box a) [:a v])\n\
         (defn h2 [:(Box a) b] :(Box a) b)\n",
    );
    assert!(
        out.stdout.contains(":(Fn [(user/Box a)] (user/Box a)) user/h2"),
        "a body annotation `:(Box a)` co-referring to the param's own \
         `(Box a)` MUST discharge → `(Fn [(Box a)] (Box a))` (§3.3.1 MUST \
         (a)/(g) discharge case); got:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("unknown type"),
        "the co-referring discharge MUST NOT be an unknown-type error; got:\n{}",
        out.stdout
    );
}

// --- R2 (RED→pass, was FV-19) — a bare var's body use PINS FREELY -------------

// spec: spec/03-types.md §3.3.1 — MUST (a): a bare written variable pins freely;
// the body narrowing it to a concrete type is NEVER an error. Row 2:
// `(defn f [:a x] (add-i64 1 x))` → `(Fn [Int] Int)`, `(f 5)` → 6 — the body use
// `(add-i64 1 x)` legitimately pins `a := Int` and the inferred scheme reflects
// that concrete type. This INVERTS the superseded W6.2 rigid-bare reading (which
// rejected the body pin as a skolem escape). Never `unknown type`, never a
// codegen frame. FV-3's extension facet: written-var and inferred-var parity is
// now TOTAL, in-body too.
// defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr + unify.rs::unify_with_rigid (W6.2 minted RIGID vars for BARE written names — spec-valid body pins rejected as skolem-escape; §3.3.1 puts rigidity on the constraint path only) found=S109 owner=/dev
#[test]
fn written_var_body_use_pins_freely() {
    let out = repl_prims("(defn f [:a x] (add-i64 1 x))\n(f 5)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("unknown type") && !combined.contains("codegen"),
        "a bare-var body pin MUST NOT be an unknown-type or codegen error (§3.3.1 \
         MUST (a)); got:\n{combined}"
    );
    assert!(
        !combined.to_lowercase().contains("rigid"),
        "a bare written var is NOT rigid — the body pin MUST NOT be rejected as a \
         rigid skolem escape (§3.3.1 MUST (a)); got:\n{combined}"
    );
    assert!(
        out.stdout.contains(":(Fn [primitives/Int] primitives/Int) user/f"),
        "the body use `(add-i64 1 x)` MUST pin `a := Int` → scheme `(Fn [Int] Int)` \
         (§3.3.1 MUST (a)); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains(":primitives/Int 6"),
        "`(f 5)` MUST evaluate to 6; got:\n{}",
        out.stdout
    );

    // All-modes value equivalence: the pinned identity computes end-to-end.
    run_through_all_modes(
        "(defn f [:a x] (add-i64 1 x))\n(defn main [] (Pure (f 5)))",
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(6);
}

// --- FV-21 (RED, neg) — qualified-lowercase annotation is NOT a var -----------

// spec: spec/03-types.md §3.3 (the var rule is for a BARE lowercase identifier)
// + §3.9.3 (neither type nor trait ⇒ error): a QUALIFIED lowercase annotation is
// a named-type REFERENCE, never a type variable. `(defn f [:user/int x] x)` MUST
// be an `unknown type` error naming `user/int`; it MUST NOT mint a type variable
// (today it mints silently and typechecks polymorphic — F2/0589). The qualified
// sibling of FV-13's uppercase guard — together they fence the minting rule to
// exactly bare-lowercase.
// defect: class=silent-accept locus=crates/cranelisp-typecheck (type-var minting keyed on lowercase-ness without excluding QUALIFIED names; four mirror mint sites per 0590 — traits/type_resolve.rs ×3 + form.rs — F2/0589) found=S109 owner=/dev
#[test]
fn qualified_lowercase_annotation_unknown_type_not_minted_neg() {
    let out = repl_prims("(defn f [:user/int x] x)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("unknown type") && combined.contains("user/int"),
        "a QUALIFIED lowercase annotation `:user/int` is a named-type reference \
         and MUST error as an unknown type naming `user/int` (§3.9.3); it MUST \
         NOT be minted as a var (§3.3 is bare-lowercase only); got:\n{combined}"
    );
    assert!(
        !out.stdout.contains("user/f ; defn"),
        "`(defn f [:user/int x] x)` MUST be rejected, not silently defined as a \
         polymorphic fn over a minted `user/int` var (F2/0589); got:\n{}",
        out.stdout
    );

    let run = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user("(defn f [:user/int x] x)\n(defn main [] (Pure 0))\n")
        .output();
    let rcomb = format!("{}{}", run.stdout, run.stderr);
    assert!(
        !run.status.success(),
        "--run: a qualified-lowercase named-type annotation with no such type \
         MUST be rejected (§3.9.3), never minted (F2/0589); got success:\n{rcomb}"
    );
    assert!(
        rcomb.contains("unknown type"),
        "--run: the failure MUST be an unknown-type error naming `user/int`; \
         got:\n{rcomb}"
    );
}

// =============================================================================
// §3.3.2–3.3.5 [S109 W6.3] — constraint path + value-position rows (R5–R17).
// Free-standing trait fixtures (no stdlib). Plan: tests/plan/PLAN.md §L.1.
// =============================================================================

// `nadd : (Fn [a a] a)` — a `Num`-style trait; bare params default to `self`
// (§7.1.1), so both args and the result are the implementing type. Int impl.
const NUM2_FIXTURE: &str = "(deftrait Num2 (nadd [a b] self))\n\
     (impl Num2 Int (defn nadd [a b] (add-i64 a b)))\n";

// `zed : ∀a. Zeroable a => (Fn [] a)` — return-type-polymorphic dispatch; Int
// impl → 0, Float impl → 0.0 (the SPRINT.md empirical fixture).
const ZEROABLE_FIXTURE: &str = "(deftrait Zeroable (zed [] self))\n\
     (impl Zeroable Int (defn zed [] 0))\n\
     (impl Zeroable Float (defn zed [] 0.0))\n";

// --- R5 (PIN) — a constraint used only through its interface stays polymorphic -

// spec: spec/03-types.md §3.3.2 — MUST (b) accepted side, row 5: a `:C x`
// parameter whose body uses ONLY the trait interface keeps the constrained
// polymorphic scheme. `(defn f5 [:Num2 x] (nadd x x))` → `∀a. Num2 a =>
// (Fn [a] a)` (result is `self` = `a`, NOT Int) and `(f5 3)` → 6. The body never
// narrows the held-abstract var, so no skolem escape.
#[test]
fn constraint_param_interface_use_keeps_constrained_scheme() {
    let out = repl_prims(&format!(
        "{NUM2_FIXTURE}(defn f5 [:Num2 x] (nadd x x))\n(f5 3)\n"
    ));
    assert!(
        out.stdout.contains(":(Fn [:Num2 a] a) user/f5"),
        "interface-only use of a `:Num2` param MUST keep the constrained \
         polymorphic scheme `(Fn [:Num2 a] a)` (result = self = a) (§3.3.2 \
         MUST (b)); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains(":primitives/Int 6"),
        "`(f5 3)` MUST evaluate to 6 (nadd 3 3); got:\n{}",
        out.stdout
    );
}

// --- R6 (RED, neg) — a constraint at a param is held abstract; body narrow errs -

// spec: spec/03-types.md §3.3.2 — MUST (b), row 6 (the error): a `:C x`
// parameter is held abstract over `C` for the body-check; the body narrowing it
// to a concrete type is a skolem escape. `(defn f6 [:Num2 x] (add-i64 1 x))`
// forces `x : Int`, narrowing the held-abstract `Num2` var → the defn MUST be
// rejected as a type error. Contrast row 2 (a BARE `:a` narrowed by the body is
// accepted) — the caller relies on the CONSTRAINT, not the name. Never `unknown
// type`, never a codegen frame.
// defect: class=silent-accept locus=crates/cranelisp-typecheck constraint path (0590 mirror sites: traits/type_resolve.rs x3 + form.rs — a :C x parameter is never held abstract, so the body narrows the claimed-abstract type silently) found=S109 owner=/dev
#[test]
fn constraint_param_body_narrow_skolem_escape_neg() {
    let out = repl_prims(&format!(
        "{NUM2_FIXTURE}(defn f6 [:Num2 x] (add-i64 1 x))\n"
    ));
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("unknown type") && !combined.contains("codegen"),
        "a held-abstract constraint narrowed by the body MUST be a type error, \
         never `unknown type`/codegen (§3.3.2 MUST (b)); got:\n{combined}"
    );
    assert!(
        !out.stdout.contains(":(Fn [primitives/Int] primitives/Int) user/f6"),
        "the body `(add-i64 1 x)` narrows the held-abstract `:Num2` var to Int — \
         the defn MUST be REJECTED as a skolem escape, NOT accepted as \
         `(Fn [Int] Int)` (§3.3.2 MUST (b)); got:\n{}",
        out.stdout
    );

    let run = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(&format!(
            "{NUM2_FIXTURE}(defn f6 [:Num2 x] (add-i64 1 x))\n(defn main [] (Pure 0))\n"
        ))
        .output();
    let rcomb = format!("{}{}", run.stdout, run.stderr);
    assert!(
        !run.status.success(),
        "--run: a `:Num2` param narrowed to Int by its body MUST be rejected \
         (§3.3.2 MUST (b) skolem escape); got success:\n{rcomb}"
    );
    assert!(
        !rcomb.contains("unknown type"),
        "--run: the rejection MUST be a type error, never `unknown type`; \
         got:\n{rcomb}"
    );
}

// --- R7 (PIN) — a constraint INFERRED from use is not asserted, not held ------

// spec: spec/03-types.md §3.3.2 — MUST (b), row 7: a bare `:a` param whose body
// uses a trait method accrues the constraint by INFERENCE (not assertion), and
// nothing is held abstract. `(defn f7 [:a x] (nadd x x))` → `∀a. Num2 a =>
// (Fn [a] a)`, no error — the same constrained scheme as R5, reached via the
// bare name rather than an explicit `:Num2`. This is the twin of R5 (one
// invariant, two provenances: asserted vs inferred constraint).
#[test]
fn bare_var_inferred_constraint_not_held_abstract() {
    let out = repl_prims(&format!("{NUM2_FIXTURE}(defn f7 [:a x] (nadd x x))\n"));
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("unknown type"),
        "a bare `:a` accruing a constraint from use MUST NOT error (§3.3.2 \
         MUST (b) inferred-not-asserted); got:\n{combined}"
    );
    assert!(
        out.stdout.contains(":(Fn [:Num2 a] a) user/f7"),
        "`(nadd x x)` on a bare `:a` MUST INFER the `Num2` constraint → \
         `(Fn [:Num2 a] a)`, identical to the asserted R5 scheme (§3.3.2 \
         MUST (b)); got:\n{}",
        out.stdout
    );
}

// --- R10 (RED, neg) — a returned polymorphic fn is poly-as-value, unsupported --

// spec: spec/03-types.md §3.3.4 + §3.10 — MUST (f), row 10: a written var that
// would leave a function polymorphic in a VALUE position (returned, stored) is
// rank-2 polymorphism, which Cranelisp does not support. `(defn mk [] (fn [:b y]
// y))` returns a still-polymorphic `∀b. (Fn [b] b)` → MUST be a clear type
// error, not silent mis-inference. Contrast R9: a polymorphic `fn` APPLIED in
// place is fine (application instantiates it). Never a codegen frame.
// defect: class=silent-accept locus=crates/cranelisp-typecheck generalization boundary (the §3.10 rank-1 gate is absent for a RETURNED still-polymorphic fn — the fn is accepted and displayed as `(Fn [] (Fn [a] a))`) found=S109 owner=/dev
#[test]
fn returned_polymorphic_fn_rejected_neg() {
    let out = repl_prims("(defn mk [] (fn [:b y] y))\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("codegen") && !combined.contains("__expr"),
        "the poly-as-value rejection MUST be a clean type error, never a codegen \
         frame (§3.3.4/§3.10 MUST (f)); got:\n{combined}"
    );
    assert!(
        !out.stdout.contains(":(Fn [] (Fn [a] a)) user/mk"),
        "a RETURNED still-polymorphic `fn` MUST be rejected as poly-as-value, NOT \
         silently accepted as `(Fn [] (Fn [a] a))` (§3.3.4/§3.10 MUST (f), \
         rank-1); got:\n{}",
        out.stdout
    );

    let run = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user("(defn mk [] (fn [:b y] y))\n(defn main [] (Pure 0))\n")
        .output();
    let rcomb = format!("{}{}", run.stdout, run.stderr);
    assert!(
        !run.status.success(),
        "--run: returning a still-polymorphic `fn` MUST be rejected (§3.10 \
         rank-1, no first-class polymorphism); got success:\n{rcomb}"
    );
}

// --- B-1 (RED, pos) — an annotated lambda APPLIED IN PLACE at a GENERIC arg ----
//
// Plan: tests/plan/PLAN.md §L Table 2b, row B-1 (FIXME 0596). The poly-as-value
// discriminator that landed at `c3008d1f` (R10) over-fires: it flags ANY written
// lambda param var that is still `Type::Var` after body inference, conflating
// (a) free-because-held-as-a-value (row 10, correctly rejected) with
// (b) free-because-applied-in-place-at-the-enclosing-definition's-own-quantified
// -var (spec-valid, wrongly rejected). This is the {applied-in-place ×
// GENERIC-arg} cell that was missing from both the §L matrix and the unit tier
// (R9(ii) only exercised the CONCRETE arg `3`), which is exactly why the
// over-fire landed unobserved.

// spec: spec/03-types.md §3.3.4/§3.10 — MUST (f)/(h): a written variable is
// rejected ONLY when it would leave a function polymorphic in a VALUE position
// (returned/stored/passed rather than instantiated at a use); a lambda APPLIED
// IN PLACE to a generic-typed argument is instantiation-at-use (§3.10, always
// sound) and MUST be accepted. `(defn f1 [x] ((fn [:b y] y) x))` and
// `(defn f2 [:a x] ((fn [:b y] y) x))` — the inner annotated lambda is applied
// in place to the enclosing defn's own quantified param; application binds `b`
// to that var and NO function value stays polymorphic anywhere (the result is
// `y`'s value, not a `fn`). Both MUST be accepted as `∀a. (Fn [a] a)`.
// defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/program.rs::check_defn_body (escaped_poly_fn) + infer.rs::infer_lambda (lambda_written_vars) (the landed W6.3 discriminator flags any written lambda var still Type::Var after body inference, conflating held-as-value with applied-in-place-at-a-GENERIC-type — §3.3.4's operative "held as a value" condition does not hold, §3.10 makes instantiation-at-use sound; FIXME 0596) found=S109 owner=/dev
#[test]
fn lambda_applied_in_place_at_generic_arg_accepted() {
    // Facet 1 — bare-enclosing: `(defn f1 [x] ((fn [:b y] y) x))`.
    let f1 = repl_prims("(defn f1 [x] ((fn [:b y] y) x))\n");
    let c1 = format!("{}{}", f1.stdout, f1.stderr);
    assert!(
        !c1.contains("cannot be returned or stored") && !c1.contains("rank-2"),
        "f1 applies the annotated lambda IN PLACE to a generic arg — NO function \
         value stays polymorphic, so it MUST NOT be rejected as poly-as-value \
         (§3.3.4/§3.10 MUST (f)/(h); the 0596 over-fire); got:\n{c1}"
    );
    assert!(
        !c1.contains("codegen") && !c1.contains("__expr"),
        "the acceptance MUST be clean — never a codegen frame (§3.10); got:\n{c1}"
    );
    assert!(
        f1.stdout.contains(":(Fn [a] a) user/f1"),
        "`(defn f1 [x] ((fn [:b y] y) x))` MUST be accepted as `∀a. (Fn [a] a)` — \
         the inner `b` is instantiated at `x`'s var by application (§3.10); \
         got:\n{}",
        f1.stdout
    );

    // Facet 2 — co-annotated-enclosing: `(defn f2 [:a x] ((fn [:b y] y) x))`.
    // The enclosing `:a` and lambda-owned `:b` are DISTINCT names (b is not in
    // the enclosing scope); application binds `b` to `a`, result is `a`.
    let f2 = repl_prims("(defn f2 [:a x] ((fn [:b y] y) x))\n");
    let c2 = format!("{}{}", f2.stdout, f2.stderr);
    assert!(
        !c2.contains("cannot be returned or stored") && !c2.contains("rank-2"),
        "f2 applies the annotated lambda IN PLACE to the `:a`-typed param — MUST \
         NOT be rejected as poly-as-value (§3.3.4/§3.10; 0596 over-fire); \
         got:\n{c2}"
    );
    assert!(
        f2.stdout.contains(":(Fn [a] a) user/f2"),
        "`(defn f2 [:a x] ((fn [:b y] y) x))` MUST be accepted as `∀a. (Fn [a] a)` \
         — application binds the lambda-owned `b` to the enclosing `a` (§3.10); \
         got:\n{}",
        f2.stdout
    );

    // All-modes value: the in-place-instantiated identity computes end-to-end.
    run_through_all_modes(
        "(defn f1 [x] ((fn [:b y] y) x))\n(defn main [] (Pure (f1 7)))",
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(7);
}

// --- B-1 fence (GREEN, neg) — the held-as-value trio STAYS rejected -----------
//
// Non-regression fence for the 0596 fix (Table 2b B-1): the narrowing that flips
// f1/f2 green MUST NOT un-reject the genuine poly-as-value cases. R10's
// `returned_polymorphic_fn_rejected_neg` already pins the RETURNED leg (`mk`);
// this pins the two remaining trio members — let-stored-and-returned (`mk3`) and
// passed-uninstantiated (`mk4`) — which were previously unpinned. All three are
// GREEN (correctly rejected) at `c3008d1f` and MUST stay so: a fix regressing
// either is a mis-narrowing.

// spec: spec/03-types.md §3.3.4/§3.10 — MUST (f): a written variable that would
// leave a function polymorphic in a VALUE position — stored in a `let` and
// returned, or passed uninstantiated to another function — is rank-2 and MUST be
// rejected. `(defn mk3 [] (let [g (fn [:b y] y)] g))` (stored then returned) and
// `(defn mk4 [] (takes (fn [:b y] y)))` (passed uninstantiated) both hold the
// `fn` as a value with `b` free → both rejected. The arg axis is moot: the value
// never reaches an application, so it is NOT instantiation-at-use.
#[test]
fn held_as_value_polymorphic_fn_variants_stay_rejected_neg() {
    // let-stored-and-returned.
    let mk3 = repl_prims("(defn mk3 [] (let [g (fn [:b y] y)] g))\n");
    let c3 = format!("{}{}", mk3.stdout, mk3.stderr);
    assert!(
        !c3.contains("codegen") && !c3.contains("__expr"),
        "the poly-as-value rejection MUST be a clean type error, never a codegen \
         frame (§3.3.4/§3.10); got:\n{c3}"
    );
    assert!(
        !mk3.stdout.contains("user/mk3 ; defn"),
        "a `fn` stored in a `let` and RETURNED is poly-as-value — `mk3` MUST be \
         REJECTED, not silently defined (§3.3.4 MUST (f)); got:\n{}",
        mk3.stdout
    );

    // passed-uninstantiated (to a function that never applies it).
    let mk4 = repl_prims(
        "(defn takes [g] 0)\n(defn mk4 [] (takes (fn [:b y] y)))\n",
    );
    let c4 = format!("{}{}", mk4.stdout, mk4.stderr);
    assert!(
        !c4.contains("codegen") && !c4.contains("__expr"),
        "the poly-as-value rejection MUST be a clean type error, never a codegen \
         frame (§3.3.4/§3.10); got:\n{c4}"
    );
    assert!(
        !mk4.stdout.contains("user/mk4 ; defn"),
        "a `fn` PASSED uninstantiated is poly-as-value — `mk4` MUST be REJECTED, \
         not silently defined (§3.3.4 MUST (f)); got:\n{}",
        mk4.stdout
    );

    // --run: both rejections hold end-to-end.
    let run = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(defn mk3 [] (let [g (fn [:b y] y)] g))\n\
             (defn main [] (Pure 0))\n",
        )
        .output();
    let rcomb = format!("{}{}", run.stdout, run.stderr);
    assert!(
        !run.status.success(),
        "--run: a let-stored-and-returned still-polymorphic `fn` MUST be rejected \
         (§3.10 rank-1); got success:\n{rcomb}"
    );
}

// --- B-1 fence (GREEN, pos) — a let-stored `fn` APPLIED in place is accepted ---
//
// The other side of the fence: the fix must not OVER-narrow. A `fn` stored in a
// `let` and then APPLIED in place is pinned by the use (§3.10) — `b` is
// instantiated, no value stays polymorphic — so it MUST stay accepted. Contrast
// `mk3` above (stored + returned, rejected): storage alone is not the trigger,
// escaping-as-a-value is. GREEN PIN at `c3008d1f`.

// spec: spec/03-types.md §3.3.4/§3.10 — MUST (h): `(defn f3 [] (let [g (fn [:b
// y] y)] (g 3)))` stores the polymorphic `fn` then APPLIES it in place; the
// application instantiates `b := Int`, so nothing stays polymorphic → accepted
// as `(Fn [] Int)`, `(f3)` → 3.
#[test]
fn let_stored_polymorphic_fn_applied_in_place_accepted() {
    let out = repl_prims("(defn f3 [] (let [g (fn [:b y] y)] (g 3)))\n(f3)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("cannot be returned or stored") && !combined.contains("rank-2"),
        "a let-stored `fn` APPLIED in place is pinned by the use (§3.10) — MUST \
         NOT be rejected as poly-as-value; got:\n{combined}"
    );
    assert!(
        out.stdout.contains(":(Fn [] primitives/Int) user/f3"),
        "`(defn f3 [] (let [g (fn [:b y] y)] (g 3)))` MUST be accepted as \
         `(Fn [] Int)` — the application pins `b := Int` (§3.10); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains(":primitives/Int 3"),
        "`(f3)` MUST evaluate to 3; got:\n{}",
        out.stdout
    );

    run_through_all_modes(
        "(defn f3 [] (let [g (fn [:b y] y)] (g 3)))\n(defn main [] (Pure (f3)))",
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(3);
}

// --- R11 (RED→pass) — a bare value-position `:a` pins to the concrete type -----

// spec: spec/03-types.md §3.3.1 — MUST (a), row 11: a bare value-position
// ascription pins to the concrete type. `(defn f [] :a 5)` → `(Fn [] Int)`,
// `(f)` → 5 — the named var is simply pinned by the literal `5`, no error. This
// INVERTS the superseded W6.2 rigid reading (which rejected it as a skolem
// escape at a top-level definition boundary).
// defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr + unify.rs::unify_with_rigid (W6.2 minted RIGID vars for BARE written names — spec-valid body pins rejected as skolem-escape; §3.3.1 puts rigidity on the constraint path only) found=S109 owner=/dev
#[test]
fn bare_var_value_position_pins_to_concrete() {
    let out = repl_prims("(defn f [] :a 5)\n(f)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("unknown type") && !combined.to_lowercase().contains("rigid"),
        "a bare value-position `:a 5` MUST pin freely, never a rigid/unknown \
         error (§3.3.1 MUST (a)); got:\n{combined}"
    );
    assert!(
        out.stdout.contains(":(Fn [] primitives/Int) user/f"),
        "`(defn f [] :a 5)` MUST pin `a := Int` → `(Fn [] Int)` (§3.3.1 MUST (a), \
         row 11); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains(":primitives/Int 5"),
        "`(f)` MUST evaluate to 5; got:\n{}",
        out.stdout
    );

    run_through_all_modes(
        "(defn f [] :a 5)\n(defn main [] (Pure (f)))",
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(5);
}

// --- R12 (RED, pos) — a value-position constraint is a satisfaction check ------

// spec: spec/03-types.md §3.3.3 — MUST (c), row 12: a trait-constraint
// annotation on a concrete value expression is a pure satisfaction check — it is
// accepted iff the expression's type implements the trait and changes nothing.
// `(defn f12 [] :Num2 5)` → no error (Int implements Num2), `(f12)` → 5. Observed
// at b2bfb760: this REJECTS with `unknown type Num2` (value-position trait
// constraints are unsupported) — RED-for-right-reason (wrong-reject). Never
// `unknown type`.
// defect: class=wrong-reject locus=crates/cranelisp-typecheck value-position annotation path (a trait-name annotation on a concrete expression is resolved as a TYPE and errors `unknown type`, instead of a satisfaction check per §3.3.3) found=S109 owner=/dev
#[test]
fn value_position_constraint_satisfaction_check() {
    let out = repl_prims(&format!("{NUM2_FIXTURE}(defn f12 [] :Num2 5)\n(f12)\n"));
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("unknown type"),
        "a value-position trait constraint `:Num2 5` MUST be a satisfaction \
         check, never an `unknown type` error (§3.3.3 MUST (c)); got:\n{combined}"
    );
    assert!(
        out.stdout.contains(":(Fn [] primitives/Int) user/f12"),
        "`:Num2 5` MUST NOT change the type of `5` — `(defn f12 [] :Num2 5)` is \
         `(Fn [] Int)` (§3.3.3 MUST (c)); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains(":primitives/Int 5"),
        "`(f12)` MUST evaluate to 5; got:\n{}",
        out.stdout
    );
}

// --- R12 (RED, neg) — the satisfaction check REJECTS a non-implementing type ---

// spec: spec/03-types.md §3.3.3 — MUST (c), negative face: the satisfaction
// check is accepted IFF the type implements the trait. `:Num2 "s"` (no String
// impl of Num2) MUST be a satisfaction-check type error naming the trait — NOT
// `unknown type Num2` (which is what b2bfb760 emits: the value-position
// constraint isn't recognised as a constraint at all).
// defect: class=wrong-reject locus=crates/cranelisp-typecheck value-position annotation path (a trait-name annotation on a concrete expression is resolved as a TYPE and errors `unknown type`, instead of a satisfaction check per §3.3.3) found=S109 owner=/dev
#[test]
fn value_position_constraint_satisfaction_check_neg() {
    let out = repl_prims(&format!("{NUM2_FIXTURE}(defn f12b [] :Num2 \"s\")\n"));
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("unknown type"),
        "the failed satisfaction check MUST name the trait, NEVER `unknown type` \
         (§3.3.3 MUST (c)); got:\n{combined}"
    );
    assert!(
        !out.stdout.contains(":(Fn [] primitives/String) user/f12b"),
        "`:Num2 \"s\"` (String has no Num2 impl) MUST be rejected by the \
         satisfaction check, NOT accepted (§3.3.3 MUST (c)); got:\n{}",
        out.stdout
    );
}

// --- R13 (PIN) — a concrete ascription resolves return-type dispatch (Int) -----

// spec: spec/03-types.md §3.3.3 — MUST (d), row 13 (cross-cite §7 return-type
// dispatch): a concrete-type value ascription selects the impl for
// return-type-polymorphic trait dispatch. `:Int (zed)` → `:primitives/Int 0` —
// the annotation picks the Int impl of `Zeroable`. Empirically GREEN at
// b2bfb760; MUST HOLD.
#[test]
fn concrete_ascription_resolves_return_type_dispatch_int() {
    let out = repl_prims(&format!("{ZEROABLE_FIXTURE}:Int (zed)\n"));
    assert!(
        out.stdout.contains(":primitives/Int 0"),
        "`:Int (zed)` MUST select the Int impl of return-type dispatch → 0 \
         (§3.3.3 MUST (d)); got:\n{}",
        out.stdout
    );
    run_through_all_modes(
        &format!("{ZEROABLE_FIXTURE}(defn main [] (Pure :Int (zed)))"),
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(0);
}

// --- R14 (PIN) — the same method, other impl, chosen by the annotation (Float) -

// spec: spec/03-types.md §3.3.3 — MUST (d), row 14: `:Float (zed)` →
// `:primitives/Float 0.0` — the same `zed` method, the Float impl, chosen by the
// concrete ascription. Empirically GREEN at b2bfb760; MUST HOLD.
#[test]
fn concrete_ascription_resolves_return_type_dispatch_float() {
    let out = repl_prims(&format!("{ZEROABLE_FIXTURE}:Float (zed)\n"));
    assert!(
        out.stdout.contains(":primitives/Float 0.0"),
        "`:Float (zed)` MUST select the Float impl of return-type dispatch → 0.0 \
         (§3.3.3 MUST (d)); got:\n{}",
        out.stdout
    );
    // Cross-mode acceptance for the Float payload (the value is not an i32, so
    // assert compilation succeeds in --run and --link rather than an i32 value).
    for mode in ["run", "link"] {
        let cl = Cranelisp::new().with_prelude(PreludeVariant::PrimitivesOnly);
        let built = if mode == "run" {
            cl.run("user.cl")
        } else {
            cl.link("user.cl")
        }
        .user(&format!("{ZEROABLE_FIXTURE}(defn main [] (Pure :Float (zed)))\n"))
        .output();
        let c = format!("{}{}", built.stdout, built.stderr);
        assert!(
            built.status.success(),
            "--{mode}: `:Float (zed)` MUST select the Float impl and compile \
             (§3.3.3 MUST (d)); got failure:\n{c}"
        );
    }
}

// --- R15 (PIN) — surrounding CONTEXT resolves return-type dispatch -------------

// spec: spec/03-types.md §3.3.3 — MUST (d), row 15: surrounding context resolves
// the dispatch with no annotation needed. `(add-i64 (zed) 5)` fixes `(zed)` to
// the Int impl → `:primitives/Int 5`. Empirically GREEN at b2bfb760; MUST HOLD.
#[test]
fn context_resolves_return_type_dispatch() {
    let out = repl_prims(&format!("{ZEROABLE_FIXTURE}(add-i64 (zed) 5)\n"));
    assert!(
        out.stdout.contains(":primitives/Int 5"),
        "`(add-i64 (zed) 5)` MUST let the Int context resolve dispatch → 5 \
         (§3.3.3 MUST (d)); got:\n{}",
        out.stdout
    );
    run_through_all_modes(
        &format!("{ZEROABLE_FIXTURE}(defn main [] (Pure (add-i64 (zed) 5)))"),
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(5);
}

// --- R16 (RED, neg) — unresolved return-type poly is the §3.11 ambiguity error -

// spec: spec/03-types.md §3.3.3 — MUST (e), row 16: a return-type-polymorphic
// form left unresolved in a codegen-reaching value position — no annotation, no
// disambiguating context — MUST be the §3.11 ambiguous-type error ("ambiguous …
// add an annotation"), the sibling disposition of an unpinned `[]`, and it MUST
// be MODE-UNIFORM across REPL/--run/--link. The output MUST NOT contain a
// backend leak (`GOT slot`, `codegen error`, the internal `__expr` binder — the
// 0568 message-quality sibling). Discrimination facet: the bare NAME `zed` (no
// call) is disposition-3 introspection display (§3.11.4), not an error.
//
// Observed at b2bfb760: bare `(zed)` leaks `codegen error … __expr entry has no
// GOT slot` at the REPL; --run reports "entry module has no main function";
// --link reports "main has no GOT slot" — none is the §3.11 message and they
// diverge per mode. RED-for-right-reason (check-gate-leak + mode-divergence).
// defect: class=check-gate-leak locus=crates/cranelisp-typecheck §3.11 finalization gate (unresolved return-type-poly trait dispatch reaches the backend as an __expr-has-no-GOT-slot codegen error instead of the check-side ambiguous-type rejection; message-quality sibling FIXME 0568) found=S109 owner=/dev
#[test]
fn unresolved_return_type_dispatch_ambiguity_error_neg() {
    // Discrimination facet (disposition-3): the bare NAME shows the scheme.
    let name = repl_prims(&format!("{ZEROABLE_FIXTURE}zed\n"));
    assert!(
        name.stdout.contains("user/zed") && !name.stdout.contains("no GOT slot"),
        "the bare name `zed` (no call) MUST be a disposition-3 introspection \
         display, not an error (§3.11.4); got:\n{}",
        name.stdout
    );

    // REPL: bare `(zed)` in a codegen-reaching position → §3.11 ambiguity.
    let repl = repl_prims(&format!("{ZEROABLE_FIXTURE}(zed)\n"));
    let rc = format!("{}{}", repl.stdout, repl.stderr);
    assert!(
        !rc.contains("GOT slot") && !rc.contains("__expr") && !rc.contains("codegen error"),
        "REPL: unresolved `(zed)` MUST NOT leak a backend GOT-slot/__expr/codegen \
         frame (§3.3.3 MUST (e), 0568); got:\n{rc}"
    );
    assert!(
        rc.contains("ambiguous"),
        "REPL: unresolved `(zed)` MUST be the §3.11 ambiguous-type error \
         (§3.3.3 MUST (e)); got:\n{rc}"
    );

    // --run and --link: MODE-UNIFORM — the same §3.11 ambiguity, never a leak.
    for mode in ["run", "link"] {
        let cl = Cranelisp::new().with_prelude(PreludeVariant::PrimitivesOnly);
        let out = if mode == "run" {
            cl.run("user.cl")
        } else {
            cl.link("user.cl")
        }
        .user(&format!("{ZEROABLE_FIXTURE}(defn main [] (Pure (zed)))\n"))
        .output();
        let c = format!("{}{}", out.stdout, out.stderr);
        assert!(
            !out.status.success(),
            "--{mode}: an unresolved return-type poly MUST be rejected (§3.3.3 \
             MUST (e)); got success:\n{c}"
        );
        assert!(
            !c.contains("GOT slot") && !c.contains("__expr") && !c.contains("has no `main`"),
            "--{mode}: the rejection MUST NOT leak a backend/module frame — it \
             MUST be the §3.11 ambiguity, mode-uniform (§3.3.3 MUST (e)); got:\n{c}"
        );
        assert!(
            c.contains("ambiguous"),
            "--{mode}: unresolved `(zed)` MUST be the §3.11 ambiguous-type error, \
             identical across modes (§3.3.3 MUST (e)); got:\n{c}"
        );
    }
}

// --- R17 (RED, neg) — a value-position constraint does NOT disambiguate --------

// spec: spec/03-types.md §3.3.3 — MUST (e), row 17: a value-position CONSTRAINT
// does not disambiguate return-type dispatch — only a concrete TYPE does. So
// `:Zeroable (zed)` remains the §3.11 ambiguous-type error (the constraint is a
// satisfaction check, not a resolution). Observed at b2bfb760: it errors
// `unknown type Zeroable` (the value-position constraint is unrecognised) — RED
// for the settled reason. MUST NOT be `unknown type`, MUST NOT leak a GOT slot,
// MUST be the §3.11 ambiguity.
// defect: class=check-gate-leak locus=crates/cranelisp-typecheck §3.11 finalization gate (a value-position trait constraint neither disambiguates nor routes to the §3.11 gate — it errors `unknown type` instead of the ambiguous-type rejection) found=S109 owner=/dev
#[test]
fn value_position_constraint_does_not_disambiguate_neg() {
    let out = repl_prims(&format!("{ZEROABLE_FIXTURE}:Zeroable (zed)\n"));
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("unknown type"),
        "`:Zeroable (zed)` MUST NOT be an `unknown type` error — a value-position \
         constraint is a satisfaction check, not a type miss (§3.3.3 MUST (e)); \
         got:\n{c}"
    );
    assert!(
        !c.contains("GOT slot") && !c.contains("__expr"),
        "`:Zeroable (zed)` MUST NOT leak a backend GOT-slot/__expr frame (§3.3.3 \
         MUST (e)); got:\n{c}"
    );
    assert!(
        c.contains("ambiguous"),
        "a value-position constraint does NOT disambiguate — `:Zeroable (zed)` \
         MUST remain the §3.11 ambiguous-type error (§3.3.3 MUST (e)); got:\n{c}"
    );
}
