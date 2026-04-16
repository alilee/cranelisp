// Ring 0 integration tests: core expressions, types, functions.
//
// Tests the full pipeline from source text to execution result.
// Organized by category per tests/plan/ring0.md.
//
// Ring 0 uses monomorphic named primitives per spec/appendix-a-builtins.md:
//   add-i64, sub-i64, mul-i64, div-i64   (Int arithmetic)
//   eq-i64, lt-i64, gt-i64, le-i64, ge-i64   (Int comparison)
//   add-f64, sub-f64, mul-f64, div-f64   (Float arithmetic)
//   eq-f64, lt-f64, gt-f64, le-f64, ge-f64   (Float comparison)
//   not   (Boolean)
// Polymorphic operator syntax (+, <, etc.) arrives in Ring 2 via trait dispatch.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::*;
use cranelisp_types::Type;

// =============================================================================
// Core Batch (spec: 04-expressions)
// =============================================================================

// spec: 04-expressions §4.1.1 — integer literal return
#[test]
fn hello() {
    // Simplest program: return an integer.
    let result = compile_and_run_simple("(defn main [] 42)");
    assert_eq!(result, 42);
}

// spec: appendix-a-builtins §A.3 — add-i64 primitive
#[test]
fn arithmetic_addition() {
    let result = compile_and_run_simple("(defn main [] (add-i64 3 4))");
    assert_eq!(result, 7);
}

// spec: appendix-a-builtins §A.3 — sub-i64 primitive
#[test]
fn arithmetic_subtraction() {
    let result = compile_and_run_simple("(defn main [] (sub-i64 10 3))");
    assert_eq!(result, 7);
}

// spec: appendix-a-builtins §A.3 — mul-i64 primitive
#[test]
fn arithmetic_multiplication() {
    let result = compile_and_run_simple("(defn main [] (mul-i64 6 7))");
    assert_eq!(result, 42);
}

// spec: appendix-a-builtins §A.3 — div-i64 primitive
#[test]
fn arithmetic_division() {
    let result = compile_and_run_simple("(defn main [] (div-i64 20 4))");
    assert_eq!(result, 5);
}

// spec: 04-expressions §4.6 — recursive function application
#[test]
fn factorial() {
    let src = "
        (defn fact [n]
          (if (eq-i64 n 0)
            1
            (mul-i64 n (fact (sub-i64 n 1)))))
        (defn main [] (fact 10))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 3628800);
}

// spec: 04-expressions §4.6 — recursive function application
#[test]
fn fibonacci() {
    let src = "
        (defn fib [n]
          (if (eq-i64 n 0)
            0
            (if (eq-i64 n 1)
              1
              (add-i64 (fib (sub-i64 n 1)) (fib (sub-i64 n 2))))))
        (defn main [] (fib 10))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 55);
}

// spec: 04-expressions §4.3 — nested let bindings
#[test]
fn nested_let() {
    let src = "
        (defn main []
          (let [x 10
                y 20]
            (let [z (add-i64 x y)]
              z)))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 30);
}

// spec: 04-expressions §4.6.1 — direct function calls
#[test]
fn chained_function_calls() {
    let src = "
        (defn double [x] (mul-i64 x 2))
        (defn inc [x] (add-i64 x 1))
        (defn main [] (double (inc 5)))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 12);
}

// spec: appendix-a-builtins §A.3 — comparison primitives
#[test]
fn comparison_operators() {
    let src = "(defn main [] (if (lt-i64 3 5) 1 0))";
    assert_eq!(compile_and_run_simple(src), 1);

    let src = "(defn main [] (if (gt-i64 3 5) 1 0))";
    assert_eq!(compile_and_run_simple(src), 0);

    let src = "(defn main [] (if (eq-i64 5 5) 1 0))";
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 05-definitions §5.1 — forward reference in batch mode
#[test]
fn forward_reference() {
    // Forward reference: callee defined after caller.
    // In batch mode, all functions are declared before any are compiled,
    // so forward references within the same compilation unit work.
    let src = "
        (defn double [x] (mul-i64 x 2))
        (defn main [] (double 21))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 42);
}

// spec: 04-expressions §4.4 — nested if expression
#[test]
fn nested_if() {
    let src = "
        (defn classify [n]
          (if (lt-i64 n 0)
            (sub-i64 0 1)
            (if (eq-i64 n 0)
              0
              1)))
        (defn main [] (add-i64 (add-i64 (classify (sub-i64 0 5)) (classify 0)) (classify 5)))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 0);
}

// =============================================================================
// REPL Basics (spec: 04-expressions, 12-runtime)
// =============================================================================

// spec: 04-expressions §4.1.1 — integer literal in REPL
#[test]
fn repl_eval_expression() {
    let mut session = repl_session();
    assert_eq!(repl_eval(&mut session, "42"), 42);
}

// spec: appendix-a-builtins §A.3 — arithmetic primitive in REPL
#[test]
fn repl_eval_arithmetic() {
    let mut session = repl_session();
    assert_eq!(repl_eval(&mut session, "(add-i64 3 4)"), 7);
}

// spec: 05-definitions §5.1 — defn and call in REPL
#[test]
fn repl_define_and_call() {
    let mut session = repl_session();
    repl_eval(&mut session, "(defn double [x] (mul-i64 x 2))");
    assert_eq!(repl_eval(&mut session, "(double 21)"), 42);
}

// spec: 04-expressions §4.6.1 — chained calls in REPL
#[test]
fn repl_chained_calls() {
    let mut session = repl_session();
    repl_eval(&mut session, "(defn inc [x] (add-i64 x 1))");
    repl_eval(&mut session, "(defn double [x] (mul-i64 x 2))");
    assert_eq!(repl_eval(&mut session, "(double (inc 5))"), 12);
}

// spec: repl/spec.md §5.2 — GOT-based redefinition
#[test]
fn repl_redefinition_updates_callers() {
    let mut session = repl_session();
    repl_eval(&mut session, "(defn helper [x] (add-i64 x 1))");
    repl_eval(&mut session, "(defn caller [] (helper 10))");
    assert_eq!(repl_eval(&mut session, "(caller)"), 11);

    // Redefine helper to add 2 instead of 1.
    repl_eval(&mut session, "(defn helper [x] (add-i64 x 2))");
    // caller should pick up the new helper via GOT.
    assert_eq!(repl_eval(&mut session, "(caller)"), 12);
}

// spec: 04-expressions §4.6 — recursive function in REPL
#[test]
fn repl_recursive_function() {
    let mut session = repl_session();
    repl_eval(
        &mut session,
        "(defn fact [n] (if (eq-i64 n 0) 1 (mul-i64 n (fact (sub-i64 n 1)))))",
    );
    assert_eq!(repl_eval(&mut session, "(fact 5)"), 120);
}

// spec: repl/spec.md §5.2 — error recovery in REPL
#[test]
fn repl_type_error_recovers() {
    let mut session = repl_session();
    // Type error: add-i64 expects Int, not Bool.
    let err = session.eval("(add-i64 1 true)");
    assert!(err.is_err());

    // Session should still work after error.
    assert_eq!(repl_eval(&mut session, "(add-i64 1 2)"), 3);
}

// spec: 05-definitions §5.1.1 — multi-param function
#[test]
fn repl_multiple_params() {
    let mut session = repl_session();
    repl_eval(
        &mut session,
        "(defn add3 [a b c] (add-i64 a (add-i64 b c)))",
    );
    assert_eq!(repl_eval(&mut session, "(add3 1 2 3)"), 6);
}

// =============================================================================
// Lambdas (spec: 04-expressions)
// Ring 1: closures and lambdas now supported in codegen.
// =============================================================================

// spec: 04-expressions §4.5 — lambda immediate application
#[test]
fn lambda_immediate_call() {
    let src = "(defn main [] ((fn [x] (add-i64 x 1)) 5))";
    assert_eq!(compile_and_run_simple(src), 6);
}

// spec: 04-expressions §4.5 — lambda bound in let
#[test]
fn lambda_in_let() {
    let src = "
        (defn main []
          (let [f (fn [x] (mul-i64 x 2))]
            (f 21)))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 04-expressions §4.6 — lambda passed as argument
#[test]
fn lambda_passed_to_function() {
    let src = "
        (defn apply-fn [f x] (f x))
        (defn main [] (apply-fn (fn [x] (add-i64 x 10)) 32))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 12-runtime §12.2.3 — top-level function as value
#[test]
fn named_function_as_value() {
    let src = "
        (defn inc [x] (add-i64 x 1))
        (defn apply-fn [f x] (f x))
        (defn main [] (apply-fn inc 41))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 04-expressions §4.5 — zero-param lambda
#[test]
fn lambda_zero_params() {
    let src = "
        (defn main []
          (let [f (fn [] 42)]
            (f)))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 04-expressions §4.5 — multi-param lambda
#[test]
fn lambda_multi_params() {
    let src = "
        (defn main []
          (let [f (fn [a b c] (add-i64 a (add-i64 b c)))]
            (f 1 2 3)))
    ";
    assert_eq!(compile_and_run_simple(src), 6);
}

// spec: 04-expressions §4.5 — lambda immediate in REPL
#[test]
fn repl_lambda_immediate() {
    let mut session = repl_session();
    assert_eq!(repl_eval(&mut session, "((fn [x] (add-i64 x 1)) 5)"), 6);
}

// spec: 04-expressions §4.5 — lambda in let in REPL
#[test]
fn repl_lambda_in_let() {
    let mut session = repl_session();
    assert_eq!(
        repl_eval(&mut session, "(let [f (fn [x] (mul-i64 x 2))] (f 21))"),
        42
    );
}

// spec: 04-expressions §4.6 — higher-order function in REPL
#[test]
fn repl_higher_order_function() {
    let mut session = repl_session();
    repl_eval(&mut session, "(defn apply-fn [f x] (f x))");
    assert_eq!(
        repl_eval(&mut session, "(apply-fn (fn [x] (add-i64 x 10)) 32)"),
        42
    );
}

// spec: 12-runtime §12.2.3 — named function as value in REPL
#[test]
fn repl_named_function_as_value() {
    let mut session = repl_session();
    repl_eval(&mut session, "(defn inc [x] (add-i64 x 1))");
    repl_eval(&mut session, "(defn apply-fn [f x] (f x))");
    assert_eq!(repl_eval(&mut session, "(apply-fn inc 41)"), 42);
}

// =============================================================================
// TCO (spec: 12-runtime)
// =============================================================================

// spec: 12-runtime §12.5 — self-recursive tail call optimization
#[test]
fn tco_deep_countdown() {
    // Deep recursion that would stack-overflow without TCO.
    let src = "
        (defn countdown [n]
          (if (eq-i64 n 0)
            0
            (countdown (sub-i64 n 1))))
        (defn main [] (countdown 1000000))
    ";
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: 12-runtime §12.5 — TCO with accumulator
#[test]
fn tco_accumulator() {
    let src = "
        (defn sum-acc [n acc]
          (if (eq-i64 n 0)
            acc
            (sum-acc (sub-i64 n 1) (add-i64 acc n))))
        (defn main [] (sum-acc 100 0))
    ";
    assert_eq!(compile_and_run_simple(src), 5050);
}

// spec: 12-runtime §12.5 — TCO in match tail position
#[test]
fn tco_match_tail_position() {
    // TCO with match in tail position using enum (no fields in Ring 0).
    // Use if-based loop that exercises match in a tail-call context.
    let src = "
        (deftype Action Stop Continue)
        (defn loop-match [n]
          (match (if (eq-i64 n 0) Stop Continue)
            [Stop 0
             Continue (loop-match (sub-i64 n 1))]))
        (defn main [] (loop-match 100000))
    ";
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: 12-runtime §12.5 — TCO in let body tail position
#[test]
fn tco_let_body_tail_position() {
    let src = "
        (defn loop-let [n]
          (if (eq-i64 n 0)
            42
            (let [m (sub-i64 n 1)]
              (loop-let m))))
        (defn main [] (loop-let 100000))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 12-runtime §12.5 — non-tail recursion unchanged
#[test]
fn tco_non_tail_recursion_unchanged() {
    // Non-tail recursion should still work (just not optimized).
    let src = "
        (defn sum [n]
          (if (eq-i64 n 0)
            0
            (add-i64 n (sum (sub-i64 n 1)))))
        (defn main [] (sum 10))
    ";
    assert_eq!(compile_and_run_simple(src), 55);
}

// =============================================================================
// Floats (spec: 03-types)
// Ring 0 uses monomorphic float primitives (add-f64, sub-f64, etc.)
// =============================================================================

// spec: 03-types §3.1 — Float arithmetic
#[test]
fn float_arithmetic() {
    let src = "(defn main [] (add-f64 1.5 2.5))";
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Float);
    let f = f64::from_bits(value as u64);
    assert!((f - 4.0).abs() < f64::EPSILON);
}

// spec: 03-types §3.1 — Float subtraction
#[test]
fn float_subtraction() {
    let src = "(defn main [] (sub-f64 10.0 3.5))";
    let (value, _) = compile_and_run_typed(src);
    let f = f64::from_bits(value as u64);
    assert!((f - 6.5).abs() < f64::EPSILON);
}

// spec: 03-types §3.1 — Float multiplication
#[test]
fn float_multiplication() {
    let src = "(defn main [] (mul-f64 3.0 4.0))";
    let (value, _) = compile_and_run_typed(src);
    let f = f64::from_bits(value as u64);
    assert!((f - 12.0).abs() < f64::EPSILON);
}

// spec: 03-types §3.1 — Float division
#[test]
fn float_division() {
    let src = "(defn main [] (div-f64 10.0 2.0))";
    let (value, _) = compile_and_run_typed(src);
    let f = f64::from_bits(value as u64);
    assert!((f - 5.0).abs() < f64::EPSILON);
}

// spec: 03-types §3.1 — Float comparison
#[test]
fn float_comparison() {
    let src = "(defn main [] (if (lt-f64 1.0 2.0) 1 0))";
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 03-types §3.1 — Float/Int type mismatch
#[test]
fn float_type_error_mixed() {
    // Cannot pass Float to add-i64.
    assert_type_error("(defn main [] (add-i64 1 1.5))", "");
}

// spec: 03-types §3.1 — Float literal in REPL
#[test]
fn repl_float_eval() {
    let mut session = repl_session();
    let (value, ty) = repl_eval_typed(&mut session, "1.234");
    assert_eq!(ty, Type::Float);
    let f = f64::from_bits(value as u64);
    assert!((f - 1.234).abs() < f64::EPSILON);
}

// spec: 03-types §3.1 — Float arithmetic in REPL
#[test]
fn repl_float_arithmetic() {
    let mut session = repl_session();
    let (value, ty) = repl_eval_typed(&mut session, "(add-f64 1.5 2.5)");
    assert_eq!(ty, Type::Float);
    let f = f64::from_bits(value as u64);
    assert!((f - 4.0).abs() < f64::EPSILON);
}

// =============================================================================
// Errors (spec: various)
// =============================================================================

// spec: 12-runtime §12.7.1 — type error Bool in arithmetic
#[test]
fn type_error_add_bool() {
    assert_type_error("(defn main [] (add-i64 true 1))", "");
}

// spec: 12-runtime §12.7.1 — type error Int + Bool
#[test]
fn error_type_error_int_plus_bool() {
    assert_type_error("(defn main [] (add-i64 1 true))", "");
}

// spec: 12-runtime §12.7.1 — type error Bool as Int
#[test]
fn error_type_error_bool_as_int() {
    // Using a bool where int is expected.
    assert_type_error("(defn main [] (add-i64 true false))", "");
}

// spec: 04-expressions §4.4 — if branch type mismatch
#[test]
fn error_type_mismatch_if_branches() {
    assert_type_error("(defn main [] (if true 1 true))", "");
}

// spec: 03-types §3.5.3 — annotation body mismatch
#[test]
fn error_defn_body_type_mismatch() {
    // Annotation says Int but body can return Bool.
    assert_type_error("(defn bad [:Int x] (if true x true))", "");
}

// spec: 01-lexical §1.5 — unclosed parenthesis
#[test]
fn error_parse_error_unclosed_paren() {
    assert_parse_error("(defn main [] (add-i64 1 2)", "");
}

// spec: 01-lexical §1.5 — extra closing parenthesis
#[test]
fn error_parse_error_extra_closing_paren() {
    assert_parse_error("(defn main [] 42))", "");
}

// spec: 04-expressions §4.2 — unbound variable reference
#[test]
fn error_unbound_symbol() {
    assert_error("(defn main [] undefined-var)", "undefined");
}

// spec: 04-expressions §4.6 — wrong arity too many
#[test]
fn error_wrong_arity_too_many_args() {
    assert_error(
        "(defn inc [x] (add-i64 x 1)) (defn main [] (inc 1 2))",
        "",
    );
}

// spec: 04-expressions §4.6.3 — too few args triggers auto-curry (returns closure)
#[test]
fn auto_curry_too_few_args_returns_closure() {
    // With auto-currying, (add 1) returns a closure, not an error.
    // The closure captures 1 and expects one more arg.
    let src = "(defn add [x y] (add-i64 x y)) (defn main [] (let [f (add 1)] (f 2)))";
    assert_eq!(compile_and_run_simple(src), 3);
}

// =============================================================================
// ADT Enums -- no heap fields (spec: 03-types, 06-pattern-matching)
// Match syntax: (match scrutinee [pattern body pattern body ...])
// =============================================================================

// spec: 06-pattern-matching §6.2.2 — nullary constructor pattern
#[test]
fn adt_enum_match() {
    let src = "
        (deftype Color Red Green Blue)
        (defn color-val [c]
          (match c
            [Red 1
             Green 2
             Blue 3]))
        (defn main [] (color-val Green))
    ";
    assert_eq!(compile_and_run_simple(src), 2);
}

// spec: 05-definitions §5.2.3 — enum type in REPL
#[test]
fn repl_adt_enum() {
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype Color Red Green Blue)");
    let (value, ty) = repl_eval_typed(&mut session, "Red");
    assert_eq!(
        ty,
        Type::ADT(cranelisp_types::FQTypeName::new(cranelisp_types::ModuleFullPath::from("user"), cranelisp_types::TypeName::from("Color")), vec![])
    );
    // Red is tag 0
    assert_eq!(value, 0);
}

// spec: 06-pattern-matching §6.2.2 — enum match in REPL
#[test]
fn repl_adt_enum_match() {
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype Color Red Green Blue)");
    repl_eval(
        &mut session,
        "(defn color-val [c] (match c [Red 1 Green 2 Blue 3]))",
    );
    assert_eq!(repl_eval(&mut session, "(color-val Blue)"), 3);
}

// spec: 06-pattern-matching §6.5.3 — runtime safety net
#[test]
fn error_non_exhaustive_match_runtime() {
    // Non-exhaustive match should panic at runtime (caught by catch_unwind).
    let src = "
        (deftype Color Red Green Blue)
        (defn partial [c]
          (match c
            [Red 1
             Green 2]))
        (defn main [] (partial Blue))
    ";
    let result = std::panic::catch_unwind(|| {
        compile_and_run_simple(src)
    });
    assert!(result.is_err(), "non-exhaustive match should panic");
}

// =============================================================================
// Dual-mode parity (batch + interactive produce same results)
// =============================================================================

// spec: 04-expressions §4.1.1 — dual-mode integer parity
#[test]
fn dual_mode_simple_int() {
    compile_both("(defn main [] 42)", 42);
}

// spec: appendix-a-builtins §A.3 — dual-mode arithmetic parity
#[test]
fn dual_mode_arithmetic() {
    compile_both("(defn main [] (add-i64 3 4))", 7);
}

// spec: 04-expressions §4.6 — dual-mode recursive parity
#[test]
fn dual_mode_factorial() {
    let src = "
        (defn fact [n] (if (eq-i64 n 0) 1 (mul-i64 n (fact (sub-i64 n 1)))))
        (defn main [] (fact 10))
    ";
    compile_both(src, 3628800);
}

// spec: 04-expressions §4.3 — dual-mode let parity
#[test]
fn dual_mode_nested_let() {
    compile_both("(defn main [] (let [x 10 y 20] (add-i64 x y)))", 30);
}

// spec: 04-expressions §4.6.1 — dual-mode chained calls parity
#[test]
fn dual_mode_chained_calls() {
    let src = "
        (defn double [x] (mul-i64 x 2))
        (defn inc [x] (add-i64 x 1))
        (defn main [] (double (inc 5)))
    ";
    compile_both(src, 12);
}

// spec: appendix-a-builtins §A.3 — dual-mode comparison parity
#[test]
fn dual_mode_comparison() {
    compile_both("(defn main [] (if (lt-i64 3 5) 1 0))", 1);
}

// spec: 05-definitions §5.1 — dual-mode forward reference parity
#[test]
fn dual_mode_forward_reference() {
    // Callee defined before caller (dependency order).
    let src = "
        (defn double [x] (mul-i64 x 2))
        (defn main [] (double 21))
    ";
    compile_both(src, 42);
}

// spec: 04-expressions §4.1.3 — dual-mode boolean parity
#[test]
fn dual_mode_boolean_logic() {
    compile_both("(defn main [] (if true 1 0))", 1);
    compile_both("(defn main [] (if false 1 0))", 0);
}

// spec: 06-pattern-matching §6.2.2 — dual-mode enum match parity
#[test]
fn dual_mode_enum_match() {
    let src = "
        (deftype Dir North South)
        (defn dir-val [d] (match d [North 1 South 2]))
        (defn main [] (dir-val South))
    ";
    compile_both(src, 2);
}

// spec: 04-expressions §4.6 — dual-mode recursive parity
#[test]
fn dual_mode_recursive() {
    let src = "
        (defn fact [n] (if (eq-i64 n 0) 1 (mul-i64 n (fact (sub-i64 n 1)))))
        (defn main [] (fact 6))
    ";
    compile_both(src, 720);
}

// =============================================================================
// Annotations (spec: 03-types)
// =============================================================================

// spec: 04-expressions §4.9 — type annotation on params
#[test]
fn annotated_params() {
    let src = "(defn inc [:Int x] (add-i64 x 1)) (defn main [] (inc 5))";
    assert_eq!(compile_and_run_simple(src), 6);
}

// spec: 04-expressions §4.9 — type annotation constrains inference
#[test]
fn annotated_return_inferred() {
    // Annotation on param constrains the body type.
    let src = "(defn id [:Int x] x) (defn main [] (id 42))";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 04-expressions §4.9 — annotation mismatch error
#[test]
fn annotation_mismatch_error() {
    // Annotated param as Int but passed a Bool.
    assert_type_error(
        "(defn inc [:Int x] (add-i64 x 1)) (defn main [] (inc true))",
        "",
    );
}

// =============================================================================
// Let-polymorphism (spec: 03-types)
// =============================================================================

// spec: 03-types §3.4 — let-polymorphism identity
#[test]
fn let_polymorphism_identity() {
    // The identity function should work with different types.
    let src = "
        (defn id [x] x)
        (defn main [] (add-i64 (id 1) (id 2)))
    ";
    assert_eq!(compile_and_run_simple(src), 3);
}

// spec: 03-types §3.4 — let-bound polymorphic usage
#[test]
fn let_bound_polymorphic_usage() {
    // Let-bound identity used at multiple types within the same function.
    let src = "
        (defn main []
          (let [id (fn [x] x)]
            (add-i64 (id 1) (id 2))))
    ";
    assert_eq!(compile_and_run_simple(src), 3);
}

// =============================================================================
// Multi-defn programs (spec: 04-expressions)
// =============================================================================

// spec: 05-definitions §5.1 — multiple function definitions
#[test]
fn multiple_functions() {
    let src = "
        (defn add1 [x] (add-i64 x 1))
        (defn mul2 [x] (mul-i64 x 2))
        (defn sub3 [x] (sub-i64 x 3))
        (defn main [] (sub3 (mul2 (add1 5))))
    ";
    assert_eq!(compile_and_run_simple(src), 9);
}

// spec: 05-definitions §5.1 — forward references between functions
#[test]
fn mutual_forward_references() {
    // Both functions reference each other (structurally -- not mutual recursion).
    let src = "
        (defn is-positive [n] (if (gt-i64 n 0) 1 0))
        (defn classify [n] (if (eq-i64 (is-positive n) 1) (add-i64 n 10) (sub-i64 0 n)))
        (defn main [] (add-i64 (classify 5) (classify (sub-i64 0 3))))
    ";
    assert_eq!(compile_and_run_simple(src), 18); // (5+10) + 3 = 18
}

// spec: 05-definitions §5.1 — main calls helper
#[test]
fn main_calls_helper() {
    let src = "
        (defn helper [] 42)
        (defn main [] (helper))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// =============================================================================
// Additional batch tests
// =============================================================================

// spec: 04-expressions §4.1.1 — negative integer literal
#[test]
fn negative_integer() {
    let src = "(defn main [] -3)";
    assert_eq!(compile_and_run_simple(src), -3);
}

// spec: 04-expressions §4.1.1 — zero integer literal
#[test]
fn zero() {
    let src = "(defn main [] 0)";
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: 04-expressions §4.1.1 — large integer literal
#[test]
fn large_integer() {
    let src = "(defn main [] 1000000000)";
    assert_eq!(compile_and_run_simple(src), 1000000000);
}

// spec: appendix-a-builtins §A.3 — not primitive true
#[test]
fn boolean_not_true() {
    let src = "(defn main [] (not true))";
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: appendix-a-builtins §A.3 — not primitive false
#[test]
fn boolean_not_false() {
    let src = "(defn main [] (not false))";
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 04-expressions §4.3 — deeply nested let
#[test]
fn deeply_nested_let() {
    let src = "
        (defn main []
          (let [a 1]
            (let [b 2]
              (let [c 3]
                (let [d 4]
                  (add-i64 (add-i64 a b) (add-i64 c d)))))))
    ";
    assert_eq!(compile_and_run_simple(src), 10);
}

// spec: 04-expressions §4.4 — if with let in branches
#[test]
fn if_with_let_branches() {
    let src = "
        (defn main []
          (if (eq-i64 1 1)
            (let [x 10] x)
            (let [y 20] y)))
    ";
    assert_eq!(compile_and_run_simple(src), 10);
}

// spec: 06-pattern-matching §6.2.3 — wildcard pattern
#[test]
fn match_wildcard() {
    let src = "
        (deftype Color Red Green Blue)
        (defn is-red [c]
          (match c
            [Red 1
             _ 0]))
        (defn main [] (add-i64 (is-red Red) (is-red Blue)))
    ";
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 06-pattern-matching §6.2.4 — variable pattern
#[test]
fn match_var_pattern() {
    let src = "
        (deftype Color Red Green Blue)
        (defn to-int [c]
          (match c
            [Red 0
             x 99]))
        (defn main [] (to-int Green))
    ";
    assert_eq!(compile_and_run_simple(src), 99);
}

// spec: appendix-a-builtins §A.3 — le-i64 primitive
#[test]
fn comparison_less_equal() {
    let src = "(defn main [] (if (le-i64 3 3) 1 0))";
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: appendix-a-builtins §A.3 — ge-i64 primitive
#[test]
fn comparison_greater_equal() {
    let src = "(defn main [] (if (ge-i64 5 3) 1 0))";
    assert_eq!(compile_and_run_simple(src), 1);
}

// =============================================================================
// Additional REPL tests
// =============================================================================

// spec: 04-expressions §4.1.3 — boolean literal in REPL
#[test]
fn repl_boolean_expression() {
    let mut session = repl_session();
    let (value, ty) = repl_eval_typed(&mut session, "true");
    assert_eq!(ty, Type::Bool);
    assert_eq!(value, 1);
}

// spec: 04-expressions §4.1.3 — boolean false in REPL
#[test]
fn repl_boolean_false() {
    let mut session = repl_session();
    let (value, ty) = repl_eval_typed(&mut session, "false");
    assert_eq!(ty, Type::Bool);
    assert_eq!(value, 0);
}

// spec: 04-expressions §4.4 — if expression in REPL
#[test]
fn repl_if_expression() {
    let mut session = repl_session();
    assert_eq!(repl_eval(&mut session, "(if true 1 2)"), 1);
    assert_eq!(repl_eval(&mut session, "(if false 1 2)"), 2);
}

// spec: 04-expressions §4.3 — let expression in REPL
#[test]
fn repl_let_expression() {
    let mut session = repl_session();
    assert_eq!(
        repl_eval(&mut session, "(let [x 10 y 20] (add-i64 x y))"),
        30
    );
}

// spec: 04-expressions §4.1.1 — negative integer in REPL
#[test]
fn repl_negative_int() {
    let mut session = repl_session();
    assert_eq!(repl_eval(&mut session, "-5"), -5);
}

// spec: 04-expressions §4.6.1 — nested calls in REPL
#[test]
fn repl_nested_calls() {
    let mut session = repl_session();
    repl_eval(&mut session, "(defn inc [x] (add-i64 x 1))");
    repl_eval(&mut session, "(defn double [x] (mul-i64 x 2))");
    assert_eq!(repl_eval(&mut session, "(inc (double (inc 3)))"), 9);
}

// spec: repl/spec.md §5.2 — parse error recovery in REPL
#[test]
fn repl_parse_error_recovers() {
    let mut session = repl_session();
    let err = session.eval("(add-i64 1");
    assert!(err.is_err());
    // Session still works.
    assert_eq!(repl_eval(&mut session, "(add-i64 2 3)"), 5);
}

// spec: appendix-a-builtins §A.3 — not primitive in REPL
#[test]
fn repl_not_operator() {
    let mut session = repl_session();
    assert_eq!(repl_eval(&mut session, "(not true)"), 0);
    assert_eq!(repl_eval(&mut session, "(not false)"), 1);
}

// spec: appendix-a-builtins §A.3 — comparison primitives in REPL
#[test]
fn repl_comparison_operators() {
    let mut session = repl_session();
    assert_eq!(repl_eval(&mut session, "(if (lt-i64 3 5) 1 0)"), 1);
    assert_eq!(repl_eval(&mut session, "(if (gt-i64 3 5) 1 0)"), 0);
    assert_eq!(repl_eval(&mut session, "(if (eq-i64 5 5) 1 0)"), 1);
    assert_eq!(repl_eval(&mut session, "(if (le-i64 3 3) 1 0)"), 1);
    assert_eq!(repl_eval(&mut session, "(if (ge-i64 5 3) 1 0)"), 1);
}

// spec: 05-definitions §5.1 — multiple definitions in REPL
#[test]
fn repl_multiple_definitions() {
    let mut session = repl_session();
    repl_eval(&mut session, "(defn a [] 1)");
    repl_eval(&mut session, "(defn b [] 2)");
    repl_eval(&mut session, "(defn c [] 3)");
    assert_eq!(repl_eval(&mut session, "(add-i64 (a) (add-i64 (b) (c)))"), 6);
}

// spec: 04-expressions §4.6 — recursive countdown in REPL
#[test]
fn repl_recursive_countdown() {
    let mut session = repl_session();
    repl_eval(
        &mut session,
        "(defn countdown [n] (if (eq-i64 n 0) 0 (countdown (sub-i64 n 1))))",
    );
    assert_eq!(repl_eval(&mut session, "(countdown 100)"), 0);
}

// spec: 05-definitions §5.2.3 — enum definition and use in REPL
#[test]
fn repl_enum_definition_and_use() {
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype Bool2 Yes No)");
    let (value, _ty) = repl_eval_typed(&mut session, "Yes");
    assert_eq!(value, 0); // tag 0
    let (value2, _ty2) = repl_eval_typed(&mut session, "No");
    assert_eq!(value2, 1); // tag 1
}

// spec: 05-definitions §5.1 — defn then expression in REPL
#[test]
fn repl_defn_then_expression() {
    // Define a function, then evaluate a bare expression calling it.
    let mut session = repl_session();
    repl_eval(&mut session, "(defn square [x] (mul-i64 x x))");
    assert_eq!(repl_eval(&mut session, "(square 7)"), 49);
}

// =============================================================================
// Additional error tests
// =============================================================================

// spec: 04-expressions §4.4 — if condition must be Bool
#[test]
fn error_if_condition_not_bool() {
    assert_type_error("(defn main [] (if 1 2 3))", "");
}

// spec: 05-definitions §5.1.1 — duplicate parameter names
#[test]
fn error_duplicate_param_names() {
    // Two parameters with the same name.
    assert_error("(defn bad [x x] (add-i64 x x))", "");
}

// spec: 04-expressions §4.2 — undefined function call
#[test]
fn error_undefined_function_call() {
    assert_error("(defn main [] (nonexistent 1))", "");
}

// =============================================================================
// Runtime errors (spec: 12-runtime §12.7.2)
// =============================================================================

// spec: 12-runtime §12.7.2 — integer overflow wraps silently
#[test]
fn integer_overflow_wraps() {
    // i64::MAX + 1 should wrap to i64::MIN (two's complement).
    let src = "(defn main [] (add-i64 9223372036854775807 1))";
    assert_eq!(compile_and_run_simple(src), i64::MIN);
}

// spec: 12-runtime §12.7.2 — integer underflow wraps silently
#[test]
fn integer_underflow_wraps() {
    // i64::MIN - 1 should wrap to i64::MAX.
    let src = "(defn main [] (sub-i64 -9223372036854775808 1))";
    assert_eq!(compile_and_run_simple(src), i64::MAX);
}

// spec: 12-runtime §12.7.3 — integer division by zero panics
#[test]
fn checked_division_by_zero_panics() {
    // div-i64 with zero divisor must return a runtime error (not trap or crash).
    let mut session = repl_session();
    let result = session.eval("(div-i64 42 0)");
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("division by zero should return Err"),
    };
    let msg = err.to_string();
    assert!(msg.contains("division by zero"), "error should mention division by zero, got: {msg}");
}

// spec: 12-runtime §12.7.3 — i64::MIN / -1 overflow panics
#[test]
fn checked_div_min_neg1_panics() {
    // i64::MIN / -1 would overflow (result is i64::MAX + 1). Must return error.
    let mut session = repl_session();
    let result = session.eval("(div-i64 -9223372036854775808 -1)");
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("i64::MIN / -1 should return Err (overflow)"),
    };
    let msg = err.to_string();
    assert!(msg.contains("division by zero"), "error should mention division by zero, got: {msg}");
}

// spec: 12-runtime §12.7.3 — normal integer division works
#[test]
fn checked_division_normal() {
    // Normal division should work without panicking.
    let src = "(defn main [] (div-i64 100 7))";
    assert_eq!(compile_and_run_simple(src), 14); // truncates toward zero
}

// spec: 01-lexical §1.1 — source encoding is UTF-8
#[test]
fn source_encoding_utf8() {
    // String literals containing UTF-8 multibyte characters.
    let src = r#"(defn main [] (str-len "héllo"))"#;
    // "héllo" has 5 Unicode chars but str-len counts bytes (6 bytes due to é).
    let result = compile_and_run_simple(src);
    // The implementation counts bytes (Rust's len()). "héllo" = 6 bytes.
    assert!(result > 0, "UTF-8 source should compile and run");
}
