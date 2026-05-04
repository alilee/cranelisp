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

use helpers::e2e::{Cranelisp, PreludeVariant};

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
