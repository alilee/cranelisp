// REPL experience tests for Ring 0.
//
// These tests validate the REPL from the user's perspective, as specified in
// repl/spec.md. They focus on display formats, session state management, and
// error recovery — the contract between the REPL and the user.
//
// Ring 0 uses monomorphic named primitives per spec/appendix-a-builtins.md:
//   add-i64, sub-i64, mul-i64, div-i64, eq-i64, lt-i64, gt-i64, le-i64, ge-i64
//   add-f64, sub-f64, mul-f64, div-f64, eq-f64, lt-f64, gt-f64, le-f64, ge-f64
//   not
// Polymorphic operator syntax (+, <, etc.) arrives in Ring 2 via trait dispatch.
//
// Many basic REPL behaviors (eval int, define and call, etc.) are already
// tested in ring0.rs. This file tests the REPL *experience* aspects:
// display format, type reporting, definition metadata, error recovery with
// state preservation, and realistic multi-step sessions.

#[path = "helpers/mod.rs"]
mod helpers;

use cranelisp::repl::format_result;
use cranelisp_types::{CranelispError, Span, Type, TypeName};
use helpers::*;

// =============================================================================
// Display Format (spec: §1.2 Expression Results)
// =============================================================================

#[test]
fn display_int_result() {
    // Spec §1.2: `:primitives/Int 3`
    // Current format_result uses short names (:Int 3). This test documents
    // the current behavior. When qualified names are implemented, update.
    let s = format_result(3, &Type::Int);
    assert_eq!(s, ":Int 3");
}

#[test]
fn display_bool_true() {
    // Spec §1.2: `:primitives/Bool true`
    let s = format_result(1, &Type::Bool);
    assert_eq!(s, ":Bool true");
}

#[test]
fn display_bool_false() {
    let s = format_result(0, &Type::Bool);
    assert_eq!(s, ":Bool false");
}

#[test]
fn display_float_result() {
    // Spec §1.2: `:primitives/Float 3.14`
    let bits = 3.14_f64.to_bits() as i64;
    let s = format_result(bits, &Type::Float);
    assert!(s.starts_with(":Float 3.14"), "got: {s}");
}

#[test]
fn display_negative_int() {
    let s = format_result(-7, &Type::Int);
    assert_eq!(s, ":Int -7");
}

#[test]
fn display_zero() {
    let s = format_result(0, &Type::Int);
    assert_eq!(s, ":Int 0");
}

#[test]
fn display_large_int() {
    let s = format_result(1_000_000_000, &Type::Int);
    assert_eq!(s, ":Int 1000000000");
}

#[test]
fn display_adt_enum_type() {
    // Spec §1.2: nullary constructor tag displayed as value.
    // Spec §1.5: `Color.Red` notation (Ring 0: enum display is the tag integer).
    // The ADT type should be displayed in the output.
    let adt = Type::ADT(TypeName::from("Color"), vec![]);
    let s = format_result(0, &adt);
    assert_eq!(s, ":Color 0");
}

#[test]
fn display_float_negative() {
    let bits = (-2.5_f64).to_bits() as i64;
    let s = format_result(bits, &Type::Float);
    assert!(s.starts_with(":Float -2.5"), "got: {s}");
}

#[test]
fn display_float_zero() {
    let bits = 0.0_f64.to_bits() as i64;
    let s = format_result(bits, &Type::Float);
    assert_eq!(s, ":Float 0");
}

// =============================================================================
// Expression Results — Type Reporting (spec: §1.2)
// =============================================================================

#[test]
fn eval_reports_int_type() {
    let mut session = repl_session();
    let result = session.eval("42").unwrap();
    assert_eq!(result.ty, Type::Int);
    assert!(!result.is_definition);
}

#[test]
fn eval_reports_bool_type() {
    let mut session = repl_session();
    let result = session.eval("true").unwrap();
    assert_eq!(result.ty, Type::Bool);
    assert!(!result.is_definition);
}

#[test]
fn eval_reports_float_type() {
    let mut session = repl_session();
    let result = session.eval("3.14").unwrap();
    assert_eq!(result.ty, Type::Float);
    assert!(!result.is_definition);
}

#[test]
fn eval_arithmetic_reports_int_type() {
    let mut session = repl_session();
    let result = session.eval("(add-i64 10 20)").unwrap();
    assert_eq!(result.ty, Type::Int);
    assert_eq!(result.value, 30);
    assert!(!result.is_definition);
}

#[test]
fn eval_comparison_reports_bool_type() {
    let mut session = repl_session();
    let result = session.eval("(lt-i64 3 5)").unwrap();
    assert_eq!(result.ty, Type::Bool);
    assert_eq!(result.value, 1); // true
    assert!(!result.is_definition);
}

#[test]
fn eval_if_inherits_branch_type() {
    let mut session = repl_session();
    let result = session.eval("(if true 42 0)").unwrap();
    assert_eq!(result.ty, Type::Int);
    assert!(!result.is_definition);
}

#[test]
fn eval_let_reports_body_type() {
    let mut session = repl_session();
    let result = session.eval("(let [x 10] (lt-i64 x 20))").unwrap();
    assert_eq!(result.ty, Type::Bool);
    assert!(!result.is_definition);
}

// =============================================================================
// Definition Results — Type Reporting (spec: §1.3)
// =============================================================================

#[test]
fn defn_reports_function_type() {
    // Spec §1.3: defn displays its inferred type scheme and qualified name.
    // At the API level, ReplResult.ty should be a Fn type and is_definition=true.
    let mut session = repl_session();
    let result = session.eval("(defn double [x] (mul-i64 x 2))").unwrap();
    assert!(result.is_definition);
    // Type should be (Fn [Int] Int)
    assert_eq!(
        result.ty,
        Type::Fn(vec![Type::Int], Box::new(Type::Int))
    );
}

#[test]
fn defn_polymorphic_reports_var_type() {
    // (defn id [x] x) should be polymorphic: (Fn [a] a)
    let mut session = repl_session();
    let result = session.eval("(defn id [x] x)").unwrap();
    assert!(result.is_definition);
    // The type should be (Fn [Var(n)] Var(n)) for some n — a polymorphic function.
    match &result.ty {
        Type::Fn(params, ret) => {
            assert_eq!(params.len(), 1);
            match (&params[0], ret.as_ref()) {
                (Type::Var(a), Type::Var(b)) => {
                    assert_eq!(a, b, "param and return type vars should match");
                }
                _ => panic!(
                    "expected polymorphic (Fn [Var] Var), got: (Fn [{:?}] {:?})",
                    params[0], ret
                ),
            }
        }
        other => panic!("expected Fn type for defn, got: {other:?}"),
    }
}

#[test]
fn defn_multi_param_reports_full_signature() {
    let mut session = repl_session();
    let result = session
        .eval("(defn add3 [a b c] (add-i64 a (add-i64 b c)))")
        .unwrap();
    assert!(result.is_definition);
    assert_eq!(
        result.ty,
        Type::Fn(vec![Type::Int, Type::Int, Type::Int], Box::new(Type::Int))
    );
}

#[test]
fn defn_zero_param_reports_thunk_type() {
    let mut session = repl_session();
    let result = session.eval("(defn always-42 [] 42)").unwrap();
    assert!(result.is_definition);
    assert_eq!(
        result.ty,
        Type::Fn(vec![], Box::new(Type::Int))
    );
}

#[test]
fn deftype_reports_adt_type() {
    // Spec §1.3: type definition displays the qualified type name.
    let mut session = repl_session();
    let result = session.eval("(deftype Color Red Green Blue)").unwrap();
    assert!(result.is_definition);
    assert_eq!(
        result.ty,
        Type::ADT(TypeName::from("Color"), vec![])
    );
}

#[test]
fn deftype_two_constructors() {
    let mut session = repl_session();
    let result = session.eval("(deftype Answer Yes No)").unwrap();
    assert!(result.is_definition);
    assert_eq!(
        result.ty,
        Type::ADT(TypeName::from("Answer"), vec![])
    );
}

// =============================================================================
// Constructor Evaluation (spec: §1.5 — nullary constructors)
// =============================================================================

#[test]
fn constructor_reports_adt_type() {
    // Entering a constructor name evaluates to its ADT type.
    let mut session = repl_session();
    session.eval("(deftype Color Red Green Blue)").unwrap();
    let result = session.eval("Red").unwrap();
    assert_eq!(
        result.ty,
        Type::ADT(TypeName::from("Color"), vec![])
    );
    assert!(!result.is_definition);
    assert_eq!(result.value, 0); // tag 0
}

#[test]
fn constructor_tags_are_sequential() {
    let mut session = repl_session();
    session.eval("(deftype Light Off Dim Bright)").unwrap();

    let r0 = session.eval("Off").unwrap();
    assert_eq!(r0.value, 0);
    assert_eq!(r0.ty, Type::ADT(TypeName::from("Light"), vec![]));

    let r1 = session.eval("Dim").unwrap();
    assert_eq!(r1.value, 1);

    let r2 = session.eval("Bright").unwrap();
    assert_eq!(r2.value, 2);
}

// =============================================================================
// Error Recovery (spec: §5.2)
// =============================================================================

#[test]
fn type_error_does_not_corrupt_definitions() {
    // Spec §5.2: session state MUST NOT be corrupted by an error.
    let mut session = repl_session();
    session.eval("(defn inc [x] (add-i64 x 1))").unwrap();
    assert_eq!(repl_eval(&mut session, "(inc 5)"), 6);

    // Trigger a type error.
    let err = session.eval("(inc true)");
    assert!(err.is_err());

    // Previous definition still works.
    assert_eq!(repl_eval(&mut session, "(inc 10)"), 11);
}

#[test]
fn parse_error_does_not_corrupt_definitions() {
    let mut session = repl_session();
    session.eval("(defn double [x] (mul-i64 x 2))").unwrap();

    // Parse error (unbalanced parens).
    let err = session.eval("(double 5");
    assert!(err.is_err());

    // Previous definition still works.
    assert_eq!(repl_eval(&mut session, "(double 5)"), 10);
}

#[test]
fn error_after_typedef_preserves_type() {
    let mut session = repl_session();
    session.eval("(deftype Dir North South)").unwrap();

    // Error.
    let err = session.eval("(add-i64 true 1)");
    assert!(err.is_err());

    // Type still usable.
    let result = session.eval("North").unwrap();
    assert_eq!(result.ty, Type::ADT(TypeName::from("Dir"), vec![]));
}

#[test]
fn multiple_errors_then_success() {
    // Spec §5.2: repeated errors should not accumulate damage.
    let mut session = repl_session();

    let err1 = session.eval("(add-i64 true 1)");
    assert!(err1.is_err());

    let err2 = session.eval("(unknown-fn 1 2)");
    assert!(err2.is_err());

    let err3 = session.eval("(if 1 2 3)"); // condition not bool
    assert!(err3.is_err());

    // Session still works.
    assert_eq!(repl_eval(&mut session, "(add-i64 1 2)"), 3);
}

#[test]
fn error_preserves_multiple_definitions() {
    // Define several things, error, verify all survive.
    let mut session = repl_session();
    session.eval("(defn a [] 1)").unwrap();
    session.eval("(defn b [] 2)").unwrap();
    session.eval("(deftype Flag On Off)").unwrap();
    session.eval("(defn c [x] (add-i64 x 10))").unwrap();

    // Error.
    let err = session.eval("(add-i64 true false)");
    assert!(err.is_err());

    // All definitions survive.
    assert_eq!(repl_eval(&mut session, "(a)"), 1);
    assert_eq!(repl_eval(&mut session, "(b)"), 2);
    assert_eq!(repl_eval(&mut session, "(c 5)"), 15);
    let flag = session.eval("On").unwrap();
    assert_eq!(flag.ty, Type::ADT(TypeName::from("Flag"), vec![]));
}

// =============================================================================
// Error Categories (spec: §5.1)
// =============================================================================

#[test]
fn error_category_parse() {
    let mut session = repl_session();
    match session.eval("(add-i64 1") {
        Err(CranelispError::ParseError { .. }) => {} // expected
        Err(other) => panic!("expected ParseError, got: {other}"),
        Ok(_) => panic!("expected ParseError, got Ok"),
    }
}

#[test]
fn error_category_type() {
    let mut session = repl_session();
    match session.eval("(add-i64 true 1)") {
        Err(CranelispError::TypeError { .. }) => {} // expected
        Err(other) => panic!("expected TypeError, got: {other}"),
        Ok(_) => panic!("expected TypeError, got Ok"),
    }
}

#[test]
fn error_has_message() {
    // Spec §5.1: errors MUST include a human-readable message.
    let mut session = repl_session();
    match session.eval("(add-i64 true 1)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(!msg.is_empty(), "error message should not be empty");
        }
        Ok(_) => panic!("expected error, got Ok"),
    }
}

// =============================================================================
// Function Redefinition (GOT update)
// =============================================================================

#[test]
fn redefinition_changes_return_value() {
    let mut session = repl_session();
    session.eval("(defn val [] 1)").unwrap();
    assert_eq!(repl_eval(&mut session, "(val)"), 1);

    session.eval("(defn val [] 2)").unwrap();
    assert_eq!(repl_eval(&mut session, "(val)"), 2);
}

#[test]
fn redefinition_propagates_through_callers() {
    // Spec: redefined function is picked up by existing callers via GOT.
    let mut session = repl_session();
    session.eval("(defn base [x] (mul-i64 x 2))").unwrap();
    session.eval("(defn caller [x] (base x))").unwrap();
    assert_eq!(repl_eval(&mut session, "(caller 5)"), 10);

    // Redefine base to multiply by 3.
    session.eval("(defn base [x] (mul-i64 x 3))").unwrap();
    assert_eq!(repl_eval(&mut session, "(caller 5)"), 15);
}

#[test]
fn redefinition_with_different_body_logic() {
    let mut session = repl_session();
    session.eval("(defn compute [n] (add-i64 n 10))").unwrap();
    assert_eq!(repl_eval(&mut session, "(compute 5)"), 15);

    // Change from addition to subtraction.
    session.eval("(defn compute [n] (sub-i64 n 10))").unwrap();
    assert_eq!(repl_eval(&mut session, "(compute 5)"), -5);
}

// =============================================================================
// Recursive Functions in REPL
// =============================================================================

#[test]
fn recursive_factorial_in_repl() {
    let mut session = repl_session();
    session
        .eval("(defn fact [n] (if (eq-i64 n 0) 1 (mul-i64 n (fact (sub-i64 n 1)))))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(fact 0)"), 1);
    assert_eq!(repl_eval(&mut session, "(fact 1)"), 1);
    assert_eq!(repl_eval(&mut session, "(fact 5)"), 120);
    assert_eq!(repl_eval(&mut session, "(fact 10)"), 3628800);
}

#[test]
fn recursive_fibonacci_in_repl() {
    let mut session = repl_session();
    session
        .eval("(defn fib [n] (if (eq-i64 n 0) 0 (if (eq-i64 n 1) 1 (add-i64 (fib (sub-i64 n 1)) (fib (sub-i64 n 2))))))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(fib 0)"), 0);
    assert_eq!(repl_eval(&mut session, "(fib 1)"), 1);
    assert_eq!(repl_eval(&mut session, "(fib 10)"), 55);
}

#[test]
fn recursive_with_accumulator_in_repl() {
    let mut session = repl_session();
    session
        .eval("(defn sum-to [n acc] (if (eq-i64 n 0) acc (sum-to (sub-i64 n 1) (add-i64 acc n))))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(sum-to 100 0)"), 5050);
}

// =============================================================================
// Enum Types and Pattern Matching in REPL
// =============================================================================

#[test]
fn enum_define_then_match() {
    let mut session = repl_session();
    session.eval("(deftype Coin Heads Tails)").unwrap();
    session
        .eval("(defn flip-val [c] (match c [Heads 100 Tails 0]))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(flip-val Heads)"), 100);
    assert_eq!(repl_eval(&mut session, "(flip-val Tails)"), 0);
}

#[test]
fn enum_wildcard_pattern_in_repl() {
    let mut session = repl_session();
    session.eval("(deftype Priority Low Medium High)").unwrap();
    session
        .eval("(defn is-high [p] (match p [High 1 _ 0]))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(is-high High)"), 1);
    assert_eq!(repl_eval(&mut session, "(is-high Low)"), 0);
    assert_eq!(repl_eval(&mut session, "(is-high Medium)"), 0);
}

#[test]
fn enum_used_in_function_chain() {
    let mut session = repl_session();
    session.eval("(deftype Bit Zero One)").unwrap();
    session
        .eval("(defn bit-val [b] (match b [Zero 0 One 1]))")
        .unwrap();
    session
        .eval("(defn double-bit [b] (mul-i64 (bit-val b) 2))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(double-bit One)"), 2);
    assert_eq!(repl_eval(&mut session, "(double-bit Zero)"), 0);
}

#[test]
fn multiple_enum_types_in_session() {
    let mut session = repl_session();
    session.eval("(deftype Color Red Green Blue)").unwrap();
    session.eval("(deftype Size Small Large)").unwrap();

    let color = session.eval("Red").unwrap();
    assert_eq!(color.ty, Type::ADT(TypeName::from("Color"), vec![]));

    let size = session.eval("Small").unwrap();
    assert_eq!(size.ty, Type::ADT(TypeName::from("Size"), vec![]));
}

// =============================================================================
// Realistic Multi-Step Sessions
// =============================================================================

#[test]
fn session_build_up_program_incrementally() {
    // Simulates a user building a small program at the REPL step by step.
    let mut session = repl_session();

    // Step 1: explore literals.
    let r = session.eval("42").unwrap();
    assert_eq!(r.value, 42);
    assert_eq!(r.ty, Type::Int);

    // Step 2: try arithmetic.
    let r = session.eval("(add-i64 10 20)").unwrap();
    assert_eq!(r.value, 30);

    // Step 3: define a helper.
    let r = session.eval("(defn square [x] (mul-i64 x x))").unwrap();
    assert!(r.is_definition);

    // Step 4: use the helper.
    assert_eq!(repl_eval(&mut session, "(square 7)"), 49);

    // Step 5: define another that uses the first.
    session
        .eval("(defn sum-of-squares [a b] (add-i64 (square a) (square b)))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(sum-of-squares 3 4)"), 25);

    // Step 6: make a mistake, recover.
    let err = session.eval("(square true)");
    assert!(err.is_err());

    // Step 7: continue working.
    assert_eq!(repl_eval(&mut session, "(sum-of-squares 5 12)"), 169);
}

#[test]
fn session_define_type_then_functions_over_it() {
    let mut session = repl_session();

    // Define a type.
    let r = session.eval("(deftype TrafficLight Red Yellow Green)").unwrap();
    assert!(r.is_definition);

    // Define a function that uses the type.
    session
        .eval("(defn can-go [light] (match light [Green 1 _ 0]))")
        .unwrap();

    // Define another.
    session
        .eval("(defn next-light [light] (match light [Red 1 Yellow 2 Green 0]))")
        .unwrap();

    // Use them.
    assert_eq!(repl_eval(&mut session, "(can-go Green)"), 1);
    assert_eq!(repl_eval(&mut session, "(can-go Red)"), 0);
    assert_eq!(repl_eval(&mut session, "(next-light Red)"), 1);
}

#[test]
fn session_interleave_definitions_and_expressions() {
    let mut session = repl_session();

    // Define, evaluate, define, evaluate pattern.
    session.eval("(defn inc [x] (add-i64 x 1))").unwrap();
    assert_eq!(repl_eval(&mut session, "(inc 0)"), 1);

    session.eval("(defn dec [x] (sub-i64 x 1))").unwrap();
    assert_eq!(repl_eval(&mut session, "(dec 10)"), 9);

    // Use both together.
    assert_eq!(repl_eval(&mut session, "(inc (dec 5))"), 5);

    // Define something that uses both.
    session
        .eval("(defn same [x] (inc (dec x)))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(same 42)"), 42);
}

// =============================================================================
// Float Arithmetic in REPL (spec: §1.2 Float display)
// =============================================================================

#[test]
fn float_display_format_in_session() {
    let mut session = repl_session();
    let result = session.eval("(add-f64 1.5 2.5)").unwrap();
    assert_eq!(result.ty, Type::Float);
    let display = format_result(result.value, &result.ty);
    assert!(display.starts_with(":Float 4"), "got: {display}");
}

#[test]
fn float_and_int_are_distinct_types() {
    let mut session = repl_session();
    let int_result = session.eval("42").unwrap();
    let float_result = session.eval("42.0").unwrap();
    assert_eq!(int_result.ty, Type::Int);
    assert_eq!(float_result.ty, Type::Float);
    // They should not be equal types.
    assert_ne!(int_result.ty, float_result.ty);
}

// =============================================================================
// Boolean Logic
// =============================================================================

#[test]
fn not_returns_bool_type() {
    let mut session = repl_session();
    let result = session.eval("(not true)").unwrap();
    assert_eq!(result.ty, Type::Bool);
    assert_eq!(result.value, 0); // false
}

// =============================================================================
// Warnings (spec: §5.1)
// =============================================================================

#[test]
fn successful_eval_has_empty_warnings() {
    let mut session = repl_session();
    let result = session.eval("42").unwrap();
    assert!(
        result.warnings.is_empty(),
        "simple expression should produce no warnings"
    );
}

// =============================================================================
// Edge Cases
// =============================================================================

#[test]
fn empty_input_is_error() {
    let mut session = repl_session();
    let err = session.eval("");
    assert!(err.is_err());
    // Session still works after empty input.
    assert_eq!(repl_eval(&mut session, "1"), 1);
}

#[test]
fn whitespace_only_is_error() {
    let mut session = repl_session();
    let err = session.eval("   ");
    assert!(err.is_err());
    assert_eq!(repl_eval(&mut session, "1"), 1);
}

#[test]
fn deeply_nested_expression() {
    let mut session = repl_session();
    // (add-i64 (add-i64 (add-i64 (add-i64 1 2) 3) 4) 5)
    assert_eq!(
        repl_eval(
            &mut session,
            "(add-i64 (add-i64 (add-i64 (add-i64 1 2) 3) 4) 5)"
        ),
        15
    );
}

#[test]
fn let_binding_shadowing() {
    let mut session = repl_session();
    let result = session
        .eval("(let [x 1] (let [x 2] x))")
        .unwrap();
    assert_eq!(result.value, 2);
    assert_eq!(result.ty, Type::Int);
}

#[test]
fn many_sequential_evals() {
    // Stress test: many sequential evaluations don't degrade the session.
    let mut session = repl_session();
    for i in 0..50 {
        let result = session.eval(&format!("{i}")).unwrap();
        assert_eq!(result.value, i);
    }
}

#[test]
fn redefine_function_many_times() {
    // Each redefinition should work and not leak.
    let mut session = repl_session();
    for i in 0..20 {
        session
            .eval(&format!("(defn f [] {i})"))
            .unwrap();
        assert_eq!(repl_eval(&mut session, "(f)"), i);
    }
}

// =============================================================================
// Error Source Location (spec: §5.1 — errors MUST include source location)
// =============================================================================

#[test]
fn error_has_source_span() {
    // Spec §5.1: All errors MUST display the source location.
    // At the API level, CranelispError carries a Span with byte offsets.
    let mut session = repl_session();
    match session.eval("(add-i64 true 1)") {
        Err(e) => {
            let span = e.span();
            // Span should not be synthetic (0..0) — it should point at real source.
            assert!(
                span != Span::SYNTHETIC,
                "error span should not be synthetic: {span:?}"
            );
        }
        Ok(_) => panic!("expected error"),
    }
}

#[test]
fn parse_error_has_source_span() {
    let mut session = repl_session();
    match session.eval("(add-i64 1") {
        Err(e) => {
            let span = e.span();
            assert!(
                span != Span::SYNTHETIC,
                "parse error span should not be synthetic: {span:?}"
            );
        }
        Ok(_) => panic!("expected error"),
    }
}

// =============================================================================
// Type Error Quality (spec: §5.3)
// =============================================================================

#[test]
fn type_error_mentions_expected_and_actual() {
    // Spec §5.3: Type errors MUST include expected and actual types.
    let mut session = repl_session();
    match session.eval("(add-i64 true 1)") {
        Err(ref e) => {
            let msg = e.message();
            // The error should mention the conflicting types.
            assert!(
                msg.contains("Int") || msg.contains("Bool"),
                "type error should mention the types involved, got: {msg}"
            );
        }
        Ok(_) => panic!("expected type error"),
    }
}

#[test]
fn if_condition_type_error_is_clear() {
    // Spec §5.3: if condition must be Bool.
    let mut session = repl_session();
    match session.eval("(if 42 1 2)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                msg.contains("Bool") || msg.contains("Int"),
                "if-condition type error should mention Bool or Int, got: {msg}"
            );
        }
        Ok(_) => panic!("expected type error for non-Bool if condition"),
    }
    // Session still works after the error.
    assert_eq!(repl_eval(&mut session, "(if true 1 2)"), 1);
}

#[test]
fn if_branch_type_mismatch_is_clear() {
    // Spec §5.3: if branches must have same type.
    let mut session = repl_session();
    match session.eval("(if true 42 true)") {
        Err(ref e) => {
            let msg = e.message();
            // Error should mention the type mismatch.
            assert!(
                !msg.is_empty(),
                "branch type mismatch error should have a message"
            );
        }
        Ok(_) => panic!("expected type error for mismatched if branches"),
    }
    assert_eq!(repl_eval(&mut session, "1"), 1);
}

// =============================================================================
// Unbound Symbol (spec: §4.1 — clear error for unbound names)
// =============================================================================

#[test]
fn unbound_symbol_produces_clear_error() {
    // Spec §4.1: If a name is unbound, the error MUST say so clearly.
    let mut session = repl_session();
    match session.eval("undefined-name") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                msg.contains("unbound") || msg.contains("undefined") || msg.contains("not found")
                    || msg.contains("unknown"),
                "unbound symbol error should mention the symbol is not defined, got: {msg}"
            );
        }
        Ok(_) => panic!("expected error for unbound symbol"),
    }
    // Session still works.
    assert_eq!(repl_eval(&mut session, "42"), 42);
}

#[test]
fn unbound_function_produces_clear_error() {
    // Calling a function that doesn't exist.
    let mut session = repl_session();
    match session.eval("(nonexistent-fn 1 2)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                !msg.is_empty(),
                "error for undefined function should have a message"
            );
        }
        Ok(_) => panic!("expected error for undefined function"),
    }
    assert_eq!(repl_eval(&mut session, "1"), 1);
}

// =============================================================================
// Wrong Arity (spec: §5.1)
// =============================================================================

#[test]
fn wrong_arity_too_many_args() {
    let mut session = repl_session();
    session.eval("(defn one-arg [x] x)").unwrap();
    match session.eval("(one-arg 1 2 3)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                !msg.is_empty(),
                "arity error should have a message"
            );
        }
        Ok(_) => panic!("expected arity error"),
    }
    // Session still works.
    assert_eq!(repl_eval(&mut session, "(one-arg 42)"), 42);
}

#[test]
fn wrong_arity_too_few_args() {
    let mut session = repl_session();
    session
        .eval("(defn two-args [x y] (add-i64 x y))")
        .unwrap();
    match session.eval("(two-args 1)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                !msg.is_empty(),
                "arity error should have a message"
            );
        }
        Ok(_) => panic!("expected arity error"),
    }
    assert_eq!(repl_eval(&mut session, "(two-args 1 2)"), 3);
}

// =============================================================================
// Format Result — Additional Types (spec: §1.2)
// =============================================================================

#[test]
fn display_function_type() {
    // Spec §1.2: function values should display type scheme.
    // For Ring 0, non-capturing function values are displayed.
    let fn_type = Type::Fn(vec![Type::Int], Box::new(Type::Int));
    let s = format_result(0, &fn_type);
    // format_result falls through to "{type} {value}" for Fn types.
    assert!(
        s.contains("Fn"),
        "function type display should contain 'Fn', got: {s}"
    );
}

#[test]
fn display_max_int() {
    let s = format_result(i64::MAX, &Type::Int);
    assert_eq!(s, format!(":Int {}", i64::MAX));
}

#[test]
fn display_min_int() {
    let s = format_result(i64::MIN, &Type::Int);
    assert_eq!(s, format!(":Int {}", i64::MIN));
}

#[test]
fn display_float_infinity() {
    let bits = f64::INFINITY.to_bits() as i64;
    let s = format_result(bits, &Type::Float);
    assert!(
        s.contains("inf"),
        "infinity should display as inf, got: {s}"
    );
}

#[test]
fn display_float_nan() {
    let bits = f64::NAN.to_bits() as i64;
    let s = format_result(bits, &Type::Float);
    assert!(
        s.contains("NaN"),
        "NaN should display as NaN, got: {s}"
    );
}

// =============================================================================
// Type Inference Accuracy (spec: §1.3 — function definitions show correct type)
// =============================================================================

#[test]
fn defn_with_let_infers_return_type() {
    let mut session = repl_session();
    let result = session
        .eval("(defn inner [x] (let [y (add-i64 x 1)] y))")
        .unwrap();
    assert!(result.is_definition);
    assert_eq!(
        result.ty,
        Type::Fn(vec![Type::Int], Box::new(Type::Int))
    );
}

#[test]
fn defn_with_if_infers_return_type() {
    let mut session = repl_session();
    let result = session
        .eval("(defn abs [x] (if (lt-i64 x 0) (sub-i64 0 x) x))")
        .unwrap();
    assert!(result.is_definition);
    assert_eq!(
        result.ty,
        Type::Fn(vec![Type::Int], Box::new(Type::Int))
    );
}

#[test]
fn defn_bool_return_type() {
    let mut session = repl_session();
    let result = session
        .eval("(defn is-zero [n] (eq-i64 n 0))")
        .unwrap();
    assert!(result.is_definition);
    assert_eq!(
        result.ty,
        Type::Fn(vec![Type::Int], Box::new(Type::Bool))
    );
}

#[test]
fn defn_float_params_and_return() {
    let mut session = repl_session();
    let result = session
        .eval("(defn avg [a b] (div-f64 (add-f64 a b) 2.0))")
        .unwrap();
    assert!(result.is_definition);
    assert_eq!(
        result.ty,
        Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float))
    );
}

// =============================================================================
// Error Recovery — Advanced Scenarios (spec: §5.2)
// =============================================================================

#[test]
fn error_between_dependent_definitions() {
    // Define A, error, define B that uses A — B should still work.
    let mut session = repl_session();
    session.eval("(defn helper [x] (add-i64 x 10))").unwrap();

    // Error.
    let err = session.eval("(add-i64 true false)");
    assert!(err.is_err());

    // Define something that depends on the pre-error definition.
    session
        .eval("(defn uses-helper [x] (helper (helper x)))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(uses-helper 5)"), 25);
}

#[test]
fn failed_defn_does_not_pollute_namespace() {
    // A defn with a type error should not leave a partial definition visible.
    let mut session = repl_session();

    // Try to define a function with a type error in its body.
    let err = session.eval("(defn bad [x] (add-i64 x true))");
    assert!(err.is_err());

    // The failed definition should not be callable.
    let err2 = session.eval("(bad 1)");
    assert!(err2.is_err());

    // Session still works for valid expressions.
    assert_eq!(repl_eval(&mut session, "42"), 42);
}

#[test]
fn error_after_redefinition_preserves_latest() {
    // Redefine a function, then error — the latest good definition persists.
    let mut session = repl_session();
    session.eval("(defn f [] 1)").unwrap();
    session.eval("(defn f [] 2)").unwrap();
    assert_eq!(repl_eval(&mut session, "(f)"), 2);

    // Error.
    let err = session.eval("(add-i64 true 1)");
    assert!(err.is_err());

    // Latest definition (returning 2) should still be active.
    assert_eq!(repl_eval(&mut session, "(f)"), 2);
}

// =============================================================================
// Enum ADT — Advanced Patterns (spec: §1.5, §6)
// =============================================================================

#[test]
fn enum_with_many_constructors() {
    let mut session = repl_session();
    session
        .eval("(deftype Weekday Mon Tue Wed Thu Fri Sat Sun)")
        .unwrap();

    let r = session.eval("Mon").unwrap();
    assert_eq!(r.value, 0);
    assert_eq!(r.ty, Type::ADT(TypeName::from("Weekday"), vec![]));

    let r = session.eval("Sun").unwrap();
    assert_eq!(r.value, 6);
    assert_eq!(r.ty, Type::ADT(TypeName::from("Weekday"), vec![]));
}

#[test]
fn match_all_constructors() {
    let mut session = repl_session();
    session.eval("(deftype RGB Red Green Blue)").unwrap();
    session
        .eval("(defn rgb-val [c] (match c [Red 1 Green 2 Blue 3]))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(rgb-val Red)"), 1);
    assert_eq!(repl_eval(&mut session, "(rgb-val Green)"), 2);
    assert_eq!(repl_eval(&mut session, "(rgb-val Blue)"), 3);
}

#[test]
fn enum_type_persists_across_many_evals() {
    // Type defined early in session is available many evals later.
    let mut session = repl_session();
    session.eval("(deftype Sign Pos Neg Zero)").unwrap();

    // Many intervening evaluations.
    for i in 0..10 {
        assert_eq!(repl_eval(&mut session, &format!("{i}")), i);
    }

    // The type is still available.
    let r = session.eval("Pos").unwrap();
    assert_eq!(r.ty, Type::ADT(TypeName::from("Sign"), vec![]));
}

// =============================================================================
// Primitive Coverage (spec: appendix-a-builtins — all 19 Ring 0 primitives)
// =============================================================================

#[test]
fn all_int_arithmetic_primitives_work_in_repl() {
    let mut session = repl_session();
    assert_eq!(repl_eval(&mut session, "(add-i64 3 4)"), 7);
    assert_eq!(repl_eval(&mut session, "(sub-i64 10 3)"), 7);
    assert_eq!(repl_eval(&mut session, "(mul-i64 3 4)"), 12);
    assert_eq!(repl_eval(&mut session, "(div-i64 10 3)"), 3);
}

#[test]
fn all_int_comparison_primitives_work_in_repl() {
    let mut session = repl_session();
    assert_eq!(repl_eval(&mut session, "(eq-i64 3 3)"), 1);
    assert_eq!(repl_eval(&mut session, "(eq-i64 3 4)"), 0);
    assert_eq!(repl_eval(&mut session, "(lt-i64 3 4)"), 1);
    assert_eq!(repl_eval(&mut session, "(lt-i64 4 3)"), 0);
    assert_eq!(repl_eval(&mut session, "(gt-i64 4 3)"), 1);
    assert_eq!(repl_eval(&mut session, "(gt-i64 3 4)"), 0);
    assert_eq!(repl_eval(&mut session, "(le-i64 3 3)"), 1);
    assert_eq!(repl_eval(&mut session, "(le-i64 3 4)"), 1);
    assert_eq!(repl_eval(&mut session, "(le-i64 4 3)"), 0);
    assert_eq!(repl_eval(&mut session, "(ge-i64 3 3)"), 1);
    assert_eq!(repl_eval(&mut session, "(ge-i64 4 3)"), 1);
    assert_eq!(repl_eval(&mut session, "(ge-i64 3 4)"), 0);
}

#[test]
fn all_float_arithmetic_primitives_work_in_repl() {
    let mut session = repl_session();
    let r = session.eval("(add-f64 1.5 2.5)").unwrap();
    assert_eq!(r.ty, Type::Float);
    assert_eq!(f64::from_bits(r.value as u64), 4.0);

    let r = session.eval("(sub-f64 5.0 2.0)").unwrap();
    assert_eq!(f64::from_bits(r.value as u64), 3.0);

    let r = session.eval("(mul-f64 3.0 4.0)").unwrap();
    assert_eq!(f64::from_bits(r.value as u64), 12.0);

    let r = session.eval("(div-f64 10.0 4.0)").unwrap();
    assert_eq!(f64::from_bits(r.value as u64), 2.5);
}

#[test]
fn all_float_comparison_primitives_work_in_repl() {
    let mut session = repl_session();
    assert_eq!(repl_eval(&mut session, "(eq-f64 3.0 3.0)"), 1);
    assert_eq!(repl_eval(&mut session, "(eq-f64 3.0 4.0)"), 0);
    assert_eq!(repl_eval(&mut session, "(lt-f64 3.0 4.0)"), 1);
    assert_eq!(repl_eval(&mut session, "(gt-f64 4.0 3.0)"), 1);
    assert_eq!(repl_eval(&mut session, "(le-f64 3.0 3.0)"), 1);
    assert_eq!(repl_eval(&mut session, "(ge-f64 3.0 3.0)"), 1);
}

#[test]
fn not_primitive_works_in_repl() {
    let mut session = repl_session();
    let r = session.eval("(not true)").unwrap();
    assert_eq!(r.ty, Type::Bool);
    assert_eq!(r.value, 0); // false

    let r = session.eval("(not false)").unwrap();
    assert_eq!(r.ty, Type::Bool);
    assert_eq!(r.value, 1); // true
}

// =============================================================================
// Let Binding Patterns (spec: §4 expressions)
// =============================================================================

#[test]
fn let_multiple_bindings() {
    let mut session = repl_session();
    let result = session
        .eval("(let [x 10 y 20] (add-i64 x y))")
        .unwrap();
    assert_eq!(result.value, 30);
    assert_eq!(result.ty, Type::Int);
}

#[test]
fn let_binding_depends_on_previous() {
    let mut session = repl_session();
    let result = session
        .eval("(let [x 10 y (add-i64 x 5)] y)")
        .unwrap();
    assert_eq!(result.value, 15);
    assert_eq!(result.ty, Type::Int);
}

#[test]
fn nested_let_with_different_types() {
    let mut session = repl_session();
    let result = session
        .eval("(let [x 42] (let [b (eq-i64 x 42)] (if b 1 0)))")
        .unwrap();
    assert_eq!(result.value, 1);
    assert_eq!(result.ty, Type::Int);
}

// =============================================================================
// Performance (spec: §7.2 — simple eval < 50ms)
// =============================================================================

#[test]
fn simple_eval_is_fast() {
    // Spec §7.2: Simple expressions MUST evaluate within 50ms.
    let mut session = repl_session();
    let start = std::time::Instant::now();
    let _ = session.eval("(add-i64 1 2)").unwrap();
    let elapsed = start.elapsed();
    assert!(
        elapsed.as_millis() < 50,
        "simple eval took {}ms, spec requires < 50ms",
        elapsed.as_millis()
    );
}

#[test]
fn defn_eval_is_fast() {
    // Spec §7.2: defining a simple function should also be fast.
    let mut session = repl_session();
    let start = std::time::Instant::now();
    let _ = session.eval("(defn f [x] (add-i64 x 1))").unwrap();
    let elapsed = start.elapsed();
    assert!(
        elapsed.as_millis() < 50,
        "defn took {}ms, spec requires < 50ms",
        elapsed.as_millis()
    );
}

// =============================================================================
// Display Format — Consistency (spec: §1)
// =============================================================================

#[test]
fn display_format_colon_prefix() {
    // Spec §1.2: format is `:Type value` — starts with colon.
    let s = format_result(42, &Type::Int);
    assert!(s.starts_with(':'), "display format must start with ':', got: {s}");
}

#[test]
fn display_format_type_value_separated_by_space() {
    // Spec §1.2: format is `:Type value` — type and value separated by space.
    let s = format_result(42, &Type::Int);
    let parts: Vec<&str> = s.splitn(2, ' ').collect();
    assert_eq!(parts.len(), 2, "display should be ':Type value', got: {s}");
    assert_eq!(parts[0], ":Int");
    assert_eq!(parts[1], "42");
}

#[test]
fn display_bool_value_is_word_not_number() {
    // Spec §1.5: Bool displays as `true` or `false`, not 0/1.
    let s_true = format_result(1, &Type::Bool);
    assert!(
        s_true.contains("true") && !s_true.contains('1'),
        "Bool true should display as word 'true', got: {s_true}"
    );
    let s_false = format_result(0, &Type::Bool);
    assert!(
        s_false.contains("false") && !s_false.contains('0'),
        "Bool false should display as word 'false', got: {s_false}"
    );
}

// =============================================================================
// Deftype + Constructor in Expressions (spec: §1.3, §1.5)
// =============================================================================

#[test]
fn constructor_in_if_expression() {
    let mut session = repl_session();
    session.eval("(deftype AB A B)").unwrap();
    session
        .eval("(defn pick [cond] (if cond A B))")
        .unwrap();
    let r = session.eval("(pick true)").unwrap();
    assert_eq!(r.ty, Type::ADT(TypeName::from("AB"), vec![]));
    assert_eq!(r.value, 0); // A is tag 0

    let r = session.eval("(pick false)").unwrap();
    assert_eq!(r.value, 1); // B is tag 1
}

#[test]
fn constructor_in_let() {
    let mut session = repl_session();
    session.eval("(deftype YN Yes No)").unwrap();
    let result = session.eval("(let [x Yes] x)").unwrap();
    assert_eq!(result.ty, Type::ADT(TypeName::from("YN"), vec![]));
    assert_eq!(result.value, 0);
}

// =============================================================================
// Session Startup (spec: §6, §7.1)
// =============================================================================

#[test]
fn session_creation_is_fast() {
    // Spec §7.1: REPL MUST start within 500ms (Ring 0 has no prelude to load).
    let start = std::time::Instant::now();
    let _session = repl_session();
    let elapsed = start.elapsed();
    assert!(
        elapsed.as_millis() < 500,
        "session creation took {}ms, spec requires < 500ms",
        elapsed.as_millis()
    );
}

#[test]
fn fresh_session_can_evaluate_immediately() {
    // Spec §6.1: A new user can evaluate a simple expression immediately.
    let mut session = repl_session();
    let result = session.eval("42").unwrap();
    assert_eq!(result.value, 42);
    assert_eq!(result.ty, Type::Int);
}

// =============================================================================
// Realistic Session: First Five Minutes (spec: §6.1)
// =============================================================================

#[test]
fn first_five_minutes_workflow() {
    // Spec §6.1: A new user can:
    // 1. Evaluate a simple expression
    // 2. See typed result
    // 3. Define a function and see its type
    // 4. Use the function
    let mut session = repl_session();

    // 1-2. Evaluate and see typed result.
    let r = session.eval("(add-i64 1 2)").unwrap();
    assert_eq!(r.value, 3);
    assert_eq!(r.ty, Type::Int);
    assert!(!r.is_definition);

    // 3. Define a function and see its type.
    let r = session.eval("(defn double [x] (mul-i64 x 2))").unwrap();
    assert!(r.is_definition);
    assert_eq!(
        r.ty,
        Type::Fn(vec![Type::Int], Box::new(Type::Int))
    );

    // 4. Use the function.
    assert_eq!(repl_eval(&mut session, "(double 21)"), 42);
}

// =============================================================================
// Mixed Types in Session (spec: §1.2)
// =============================================================================

#[test]
fn session_with_all_three_primitive_types() {
    // A session using Int, Bool, and Float — all Ring 0 primitive types.
    let mut session = repl_session();

    let r_int = session.eval("42").unwrap();
    assert_eq!(r_int.ty, Type::Int);

    let r_bool = session.eval("true").unwrap();
    assert_eq!(r_bool.ty, Type::Bool);

    let r_float = session.eval("3.14").unwrap();
    assert_eq!(r_float.ty, Type::Float);

    // Mix them in expressions.
    session
        .eval("(defn classify [n] (if (lt-i64 n 0) false true))")
        .unwrap();
    let r = session.eval("(classify 5)").unwrap();
    assert_eq!(r.ty, Type::Bool);
    assert_eq!(r.value, 1);

    let r = session.eval("(classify (sub-i64 0 1))").unwrap();
    assert_eq!(r.ty, Type::Bool);
    assert_eq!(r.value, 0);
}

// =============================================================================
// =============================================================================
//
// Ring 1 REPL Experience Tests
//
// These tests validate the REPL user experience for Ring 1 features: strings,
// ADTs with fields, and closures. Focus is on display format, type reporting,
// error quality, and session continuity — not on correctness (that's /qa's job
// in ring1.rs and rc.rs).
//
// Ring 1 spec references:
//   repl/spec.md §1.2 — expression result display
//   repl/spec.md §1.5 — value display (String, data ADT, closure)
//   repl/spec.md §5.3 — type error quality
//
// =============================================================================
// =============================================================================

// =============================================================================
// String Display (repl/spec.md §1.5: String → "contents" with escapes)
// =============================================================================

#[test]
fn ring1_string_literal_display_format() {
    // Spec §1.5: String values display as `"contents"`.
    // Full result format: `:String "contents"`.
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "\"hello\"");
    assert_eq!(display, ":String \"hello\"");
}

#[test]
fn ring1_string_empty_display() {
    // Empty string should display as `:String ""`.
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "\"\"");
    assert_eq!(display, ":String \"\"");
}

#[test]
fn ring1_string_concat_result_display() {
    // Result of str-concat should display the concatenated string.
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "(str-concat \"hello\" \" world\")");
    assert_eq!(display, ":String \"hello world\"");
}

#[test]
fn ring1_string_literal_reports_string_type() {
    // Spec §1.2: string expression should report Type::String.
    let mut session = repl_session();
    let result = session.eval("\"hello\"").unwrap();
    assert_eq!(result.ty, Type::String);
    assert!(!result.is_definition);
}

#[test]
fn ring1_string_primitive_reports_correct_types() {
    // String primitives should report appropriate return types.
    let mut session = repl_session();

    // str-len returns Int.
    let r = session.eval("(str-len \"hello\")").unwrap();
    assert_eq!(r.ty, Type::Int);
    assert_eq!(r.value, 5);

    // str-eq returns Bool.
    let r = session.eval("(str-eq \"a\" \"a\")").unwrap();
    assert_eq!(r.ty, Type::Bool);
    assert_eq!(r.value, 1);

    // int-to-string returns String.
    let r = session.eval("(int-to-string 42)").unwrap();
    assert_eq!(r.ty, Type::String);
}

#[test]
fn ring1_int_to_string_display() {
    // Converting an integer to string and displaying the result.
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "(int-to-string 42)");
    assert_eq!(display, ":String \"42\"");
}

#[test]
fn ring1_string_with_spaces_display() {
    // Strings containing spaces display correctly with surrounding quotes.
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "\"hello world\"");
    assert_eq!(display, ":String \"hello world\"");
}

// =============================================================================
// ADT Display (repl/spec.md §1.5: data constructors, product types, polymorphic)
// =============================================================================

#[test]
fn ring1_adt_product_display() {
    // Spec §1.5: Data constructor display: `(Type.Ctor field1 field2 ...)`.
    // Product type with Int fields.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype Point [:Int x :Int y])");
    let display = repl_eval_display(&mut session, "(Point 3 4)");
    assert_eq!(display, ":Point (Point 3 4)");
}

#[test]
fn ring1_adt_sum_some_display() {
    // Spec §1.5: `:(Option Int) (Some 42)` for data constructor.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype (Option a) None (Some [:a val]))");
    let display = repl_eval_display(&mut session, "(Some 42)");
    assert_eq!(display, ":(Option Int) (Some 42)");
}

#[test]
fn ring1_adt_sum_none_display() {
    // Nullary constructor of polymorphic type displays correctly.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype (Option a) None (Some [:a val]))");
    let display = repl_eval_display(&mut session, "None");
    // None is nullary — type var may be unresolved. Display should show
    // the Option type and the constructor name.
    assert!(
        display.contains("Option") && display.ends_with("None"),
        "expected Option ... None display, got: {display}"
    );
}

#[test]
fn ring1_adt_polymorphic_type_display() {
    // Parameterized types show their type args: `:(Option Int)`.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype (Option a) None (Some [:a val]))");
    let result = session.eval("(Some 42)").unwrap();
    // Type should be ADT("Option", [Int]).
    assert_eq!(
        result.ty,
        Type::ADT(TypeName::from("Option"), vec![Type::Int])
    );
}

#[test]
fn ring1_adt_product_type_reports_adt_type() {
    // Constructing a product type should report the ADT type.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype Point [:Int x :Int y])");
    let result = session.eval("(Point 3 4)").unwrap();
    assert_eq!(
        result.ty,
        Type::ADT(TypeName::from("Point"), vec![])
    );
    assert!(!result.is_definition);
}

#[test]
fn ring1_adt_nested_string_field_display() {
    // ADT containing a String field should recursively display the string.
    // Spec §1.5: "ADT fields MUST be recursively formatted."
    //
    // USABILITY FINDING U1.1: Polymorphic ADT field display does not substitute
    // type variables with concrete type args. `(Some "hello")` shows the raw
    // pointer value instead of `"hello"` because the field type is stored as
    // `Type::Var(a)` in TypeDefInfo, not `Type::String`. The type portion
    // `:(Option String)` is correct, but the value display is not.
    // Filed to tests/plan/usability.md.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype (Option a) None (Some [:a val]))");
    let display = repl_eval_display(&mut session, "(Some \"hello\")");
    // Current behavior: field rendered as raw i64 (the pointer) due to Var type.
    // When U1.1 is fixed, this should become:
    //   assert_eq!(display, ":(Option String) (Some \"hello\")");
    assert!(
        display.starts_with(":(Option String) (Some "),
        "should show type as (Option String), got: {display}"
    );
}

#[test]
fn ring1_adt_monomorphic_string_field_display() {
    // Monomorphic ADT with concrete String field type (no type variable issue).
    // Spec §1.5: fields must be recursively formatted.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype Named [:String name])");
    let display = repl_eval_display(&mut session, "(Named \"alice\")");
    assert_eq!(display, ":Named (Named \"alice\")");
}

#[test]
fn ring1_adt_enum_display_with_type_defs() {
    // Nullary constructors should show constructor names, not bare tags.
    // This uses a REPL session where type_defs are accumulated.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype Color Red Green Blue)");
    let display = repl_eval_display(&mut session, "Red");
    assert_eq!(display, ":Color Red");
    let display = repl_eval_display(&mut session, "Blue");
    assert_eq!(display, ":Color Blue");
}

#[test]
fn ring1_deftype_with_fields_reports_type() {
    // Spec §1.3: type definition displays the type name.
    let mut session = repl_session();
    let result = session
        .eval("(deftype Point [:Int x :Int y])")
        .unwrap();
    assert!(result.is_definition);
    assert_eq!(
        result.ty,
        Type::ADT(TypeName::from("Point"), vec![])
    );
}

// =============================================================================
// Closure Display (repl/spec.md §1.5: Closure → `<closure>`)
// =============================================================================

#[test]
fn ring1_closure_display_format() {
    // Spec §1.5: Closure values display as `<closure>`.
    let mut session = repl_session();
    repl_eval(&mut session, "(defn make-adder [n] (fn [x] (add-i64 n x)))");
    let display = repl_eval_display(&mut session, "(make-adder 5)");
    assert!(
        display.contains("<closure>"),
        "closure display should contain '<closure>', got: {display}"
    );
}

#[test]
fn ring1_closure_display_includes_fn_type() {
    // Closure display format: `:(Fn [params] return) <closure>`.
    let mut session = repl_session();
    repl_eval(&mut session, "(defn make-adder [n] (fn [x] (add-i64 n x)))");
    let display = repl_eval_display(&mut session, "(make-adder 5)");
    assert!(
        display.starts_with(":(Fn "),
        "closure display should start with ':(Fn ', got: {display}"
    );
    assert!(
        display.ends_with("<closure>"),
        "closure display should end with '<closure>', got: {display}"
    );
}

#[test]
fn ring1_closure_result_type_is_fn() {
    // The type of a closure value should be Type::Fn.
    let mut session = repl_session();
    repl_eval(&mut session, "(defn make-adder [n] (fn [x] (add-i64 n x)))");
    let result = session.eval("(make-adder 5)").unwrap();
    match &result.ty {
        Type::Fn(params, _ret) => {
            assert_eq!(params.len(), 1, "make-adder should return a 1-param closure");
        }
        other => panic!("expected Fn type for closure, got: {other:?}"),
    }
}

#[test]
fn ring1_defn_returning_closure_type() {
    // Defining a function that returns a closure should report the higher-order type.
    let mut session = repl_session();
    let result = session
        .eval("(defn make-adder [n] (fn [x] (add-i64 n x)))")
        .unwrap();
    assert!(result.is_definition);
    // Should be (Fn [Int] (Fn [Int] Int)).
    match &result.ty {
        Type::Fn(params, ret) => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0], Type::Int);
            match ret.as_ref() {
                Type::Fn(inner_params, inner_ret) => {
                    assert_eq!(inner_params.len(), 1);
                    assert_eq!(inner_params[0], Type::Int);
                    assert_eq!(inner_ret.as_ref(), &Type::Int);
                }
                other => panic!("expected inner Fn type, got: {other:?}"),
            }
        }
        other => panic!("expected Fn type for make-adder, got: {other:?}"),
    }
}

#[test]
fn ring1_lambda_immediate_display_not_closure() {
    // Immediately-applied lambda should show the result, not <closure>.
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "((fn [x] (add-i64 x 1)) 5)");
    assert_eq!(display, ":Int 6");
}

// =============================================================================
// Error Quality for Ring 1 Types (repl/spec.md §5.3)
// =============================================================================

#[test]
fn ring1_error_string_where_int_expected() {
    // Passing a String where Int is expected should produce a clear type error.
    let mut session = repl_session();
    match session.eval("(add-i64 \"hello\" 1)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                msg.contains("Int") || msg.contains("String"),
                "type error should mention the types involved, got: {msg}"
            );
        }
        Ok(_) => panic!("expected type error for String where Int expected"),
    }
    // Session recovery.
    assert_eq!(repl_eval(&mut session, "(add-i64 1 2)"), 3);
}

#[test]
fn ring1_error_int_where_string_expected() {
    // Passing an Int where String is expected.
    let mut session = repl_session();
    match session.eval("(str-len 42)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                msg.contains("Int") || msg.contains("String"),
                "type error should mention types, got: {msg}"
            );
        }
        Ok(_) => panic!("expected type error for Int where String expected"),
    }
    // Session continues.
    assert_eq!(repl_eval(&mut session, "(str-len \"hi\")"), 2);
}

#[test]
fn ring1_error_if_branch_string_int_mismatch() {
    // If branches with String and Int should produce a clear type error.
    let mut session = repl_session();
    match session.eval("(if true \"hello\" 42)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                !msg.is_empty(),
                "branch type mismatch error should have a message"
            );
        }
        Ok(_) => panic!("expected type error for mismatched if branches (String vs Int)"),
    }
    assert_eq!(repl_eval(&mut session, "1"), 1);
}

#[test]
fn ring1_error_constructor_wrong_arg_count() {
    // Constructing an ADT with wrong number of arguments should error clearly.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype Point [:Int x :Int y])");
    match session.eval("(Point 1)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                !msg.is_empty(),
                "constructor arity error should have a message"
            );
        }
        Ok(_) => panic!("expected error for wrong constructor argument count"),
    }
    // Session recovery: correct usage still works.
    let display = repl_eval_display(&mut session, "(Point 1 2)");
    assert_eq!(display, ":Point (Point 1 2)");
}

#[test]
fn ring1_error_constructor_wrong_type() {
    // Constructing an ADT with wrong field type should produce a type error.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype Point [:Int x :Int y])");
    match session.eval("(Point true 2)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                msg.contains("Int") || msg.contains("Bool"),
                "constructor type error should mention the types, got: {msg}"
            );
        }
        Ok(_) => panic!("expected type error for wrong constructor field type"),
    }
}

#[test]
fn ring1_error_undefined_constructor() {
    // Using an undefined constructor should produce a clear error.
    let mut session = repl_session();
    match session.eval("(Foo 1 2)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                msg.contains("Foo") || msg.contains("unbound") || msg.contains("undefined")
                    || msg.contains("unknown") || msg.contains("not found"),
                "undefined constructor error should mention the name, got: {msg}"
            );
        }
        Ok(_) => panic!("expected error for undefined constructor"),
    }
    assert_eq!(repl_eval(&mut session, "42"), 42);
}

#[test]
fn ring1_error_closure_arity_mismatch() {
    // Calling a closure with wrong number of arguments should error clearly.
    let mut session = repl_session();
    match session.eval("(let [f (fn [x] x)] (f 1 2))") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                !msg.is_empty(),
                "closure arity error should have a message"
            );
        }
        Ok(_) => panic!("expected error for closure arity mismatch"),
    }
    assert_eq!(repl_eval(&mut session, "(let [f (fn [x] x)] (f 42))"), 42);
}

#[test]
fn ring1_error_has_span_for_heap_type_mismatch() {
    // Spec §5.1: errors MUST include source location.
    // Type errors involving heap types should have non-synthetic spans.
    let mut session = repl_session();
    match session.eval("(str-len 42)") {
        Err(ref e) => {
            let span = e.span();
            assert!(
                span != Span::SYNTHETIC,
                "heap type error span should not be synthetic: {span:?}"
            );
        }
        Ok(_) => panic!("expected type error"),
    }
}

// =============================================================================
// Type Display for Ring 1 (repl/spec.md §1.4)
// =============================================================================

#[test]
fn ring1_defn_with_string_param_type() {
    // Defining a function with String parameter should report String in the type.
    let mut session = repl_session();
    let result = session
        .eval("(defn greet-len [s] (str-len s))")
        .unwrap();
    assert!(result.is_definition);
    assert_eq!(
        result.ty,
        Type::Fn(vec![Type::String], Box::new(Type::Int))
    );
}

#[test]
fn ring1_defn_returning_string_type() {
    // Defining a function returning String should report String in return type.
    let mut session = repl_session();
    let result = session
        .eval("(defn greeting [] \"hello\")")
        .unwrap();
    assert!(result.is_definition);
    assert_eq!(
        result.ty,
        Type::Fn(vec![], Box::new(Type::String))
    );
}

#[test]
fn ring1_defn_with_adt_param_type() {
    // A function taking an ADT parameter shows the ADT type.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype Point [:Int x :Int y])");
    let result = session
        .eval("(defn get-x [p] (match p [(Point x y) x]))")
        .unwrap();
    assert!(result.is_definition);
    assert_eq!(
        result.ty,
        Type::Fn(
            vec![Type::ADT(TypeName::from("Point"), vec![])],
            Box::new(Type::Int)
        )
    );
}

#[test]
fn ring1_defn_polymorphic_adt_return_type() {
    // A function returning a polymorphic ADT shows the instantiated type.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype (Option a) None (Some [:a val]))");
    let result = session
        .eval("(defn wrap [x] (Some x))")
        .unwrap();
    assert!(result.is_definition);
    // wrap should be polymorphic: (Fn [a] (Option a))
    match &result.ty {
        Type::Fn(params, ret) => {
            assert_eq!(params.len(), 1);
            match ret.as_ref() {
                Type::ADT(name, args) => {
                    assert_eq!(name, &TypeName::from("Option"));
                    assert_eq!(args.len(), 1, "Option should have 1 type arg");
                }
                other => panic!("expected ADT return type, got: {other:?}"),
            }
        }
        other => panic!("expected Fn type for wrap, got: {other:?}"),
    }
}

// =============================================================================
// Session Continuity — Ring 1 (repl/spec.md §5.2)
// =============================================================================

#[test]
fn ring1_error_between_adt_and_closure_definitions() {
    // Define an ADT, trigger an error, then define a closure over the ADT.
    // All definitions should survive.
    let mut session = repl_session();

    // Step 1: define an ADT.
    repl_eval(&mut session, "(deftype (Option a) None (Some [:a val]))");

    // Step 2: define a function using it.
    repl_eval(
        &mut session,
        "(defn unwrap [opt] (match opt [(Some x) x None 0]))",
    );

    // Step 3: trigger an error.
    let err = session.eval("(add-i64 \"hello\" 1)");
    assert!(err.is_err());

    // Step 4: the ADT and function still work.
    assert_eq!(repl_eval(&mut session, "(unwrap (Some 99))"), 99);

    // Step 5: define a closure that uses the ADT.
    repl_eval(&mut session, "(defn make-wrapper [n] (fn [] (Some n)))");
    let display = repl_eval_display(&mut session, "((make-wrapper 42))");
    assert_eq!(display, ":(Option Int) (Some 42)");
}

#[test]
fn ring1_error_preserves_string_definitions() {
    // Define functions using strings, error, verify they survive.
    let mut session = repl_session();

    repl_eval(&mut session, "(defn greet [] \"hello\")");

    // Error.
    let err = session.eval("(add-i64 true 1)");
    assert!(err.is_err());

    // String function still works.
    let display = repl_eval_display(&mut session, "(greet)");
    assert_eq!(display, ":String \"hello\"");
}

#[test]
fn ring1_session_incremental_with_heap_types() {
    // Simulates a user building up definitions with strings, ADTs, and closures.
    let mut session = repl_session();

    // Step 1: explore strings.
    let display = repl_eval_display(&mut session, "\"hello\"");
    assert_eq!(display, ":String \"hello\"");

    // Step 2: define an ADT.
    repl_eval(&mut session, "(deftype (Option a) None (Some [:a val]))");

    // Step 3: wrap a string in an ADT.
    let display = repl_eval_display(&mut session, "(Some \"world\")");
    // Note: field display for polymorphic ADTs shows raw value due to U1.1
    // (type variable not substituted with concrete type). Type portion is correct.
    assert!(
        display.starts_with(":(Option String) (Some "),
        "should show type as (Option String), got: {display}"
    );

    // Step 4: define a closure.
    repl_eval(&mut session, "(defn make-adder [n] (fn [x] (add-i64 n x)))");
    let display = repl_eval_display(&mut session, "(make-adder 10)");
    assert!(display.contains("<closure>"), "got: {display}");

    // Step 5: use the closure.
    assert_eq!(repl_eval(&mut session, "((make-adder 10) 32)"), 42);

    // Step 6: make a mistake.
    let err = session.eval("(str-len 42)");
    assert!(err.is_err());

    // Step 7: everything still works.
    assert_eq!(repl_eval(&mut session, "((make-adder 5) 5)"), 10);
    let display = repl_eval_display(&mut session, "(Some 99)");
    assert_eq!(display, ":(Option Int) (Some 99)");
}
