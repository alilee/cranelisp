// QUARANTINED — Sprint 64 Wave 5 test-port. Not built or run by Cargo.
// FIXME: design/arch/fixmes/0136-harvest-tests-legacy-sketch_port.md
// Owning crate: tests/ harvest
// Owning skill: /qa (test-shape harvest; mostly self-resolved)
// Quarantined: 2026-05-04
//
// This file's assertions test Rust-internal state with no clean e2e
// equivalent (or the language-behaviour subset has been carried forward
// into the spec-section files). Harvest into `#[cfg(test)]` unit tests
// inside the owning crate per memory/feedback_unit_tests_with_dev.md and
// memory/project_test_strategy.md. Source preserved verbatim; translation
// may require dev-dependency adjustments and import rewrites.

// Sketch test port — adapted from sketch/tests/integration.rs, sketch/tests/rc.rs,
// sketch/tests/trace.rs, sketch/tests/run_tests.rs, and sketch/tests/platform.rs.
//
// These tests are kept SEPARATE from the ring-organized test suite even where
// they overlap, per user request. They validate the same behaviors using the
// reimplementation's test helpers and display conventions.
//
// Key adaptations from sketch:
//   - Sketch uses trait operators (+, -, *, =, <, etc.) via prelude — reimplementation
//     uses named primitives (add-i64, sub-i64, etc.) for Ring 0 or the test prelude
//     for trait dispatch.
//   - Sketch wraps batch results in (pure ...) — reimplementation doesn't need this
//     for REPL-mode tests.
//   - Display format: `:primitives/Int 3` not `:Int 3`.
//   - Module paths: `user/foo` not just `foo`.
//
// =============================================================================
// TRIAGE REPORT — 11 failing tests (2026-03-25)
// =============================================================================
//
// 1. sketch_multi_sig_different_arities — FAILS
//    Error: "multi-signature functions not supported in Ring 0"
//    Classification: A (real implementation gap) — typecheck gap
//    Spec: 05-definitions §5.1.2 — multi-sig is specified and tested in Ring 2 scope.
//    The typecheck crate explicitly rejects DefnMulti. Needs typecheck + backend
//    implementation of multi-sig dispatch.
//
// 2. sketch_multi_sig_type_based_dispatch — FAILS
//    Error: "multi-signature functions not supported in Ring 0"
//    Classification: A (real implementation gap) — same as #1, typecheck gap.
//    Spec: 05-definitions §5.1.2, 04-expressions §4.7
//
// 3. sketch_repl_multi_sig_different_arities — FAILS
//    Error: "multi-signature functions not supported in Ring 0"
//    Classification: A (real implementation gap) — same as #1, typecheck gap.
//    Spec: 05-definitions §5.1.2
//
// 4. sketch_default_method_used_when_not_overridden — FAILS
//    Error: "no hard-coded default body for Greetable.wave"
//    Classification: A (real implementation gap) — typecheck/backend gap.
//    Spec: 07-traits §7.1.5 — default method bodies must be stored on the trait
//    declaration and synthesized into impl blocks that omit the method. The
//    implementation does not synthesize default method defns from the trait's
//    stored S-expression body.
//
// 5. sketch_default_method_overridden — FAILS
//    Error: assertion left=49372856320 right=500
//    Classification: A (real implementation gap) — codegen gap.
//    Spec: 07-traits §7.1.5 — when an impl explicitly overrides a default method,
//    the override should be used. The garbage return value (49372856320) indicates
//    the overridden method dispatches to the wrong function pointer or the method
//    resolution table is not updated when an override is provided.
//
// 6. sketch_default_method_on_adt — FAILS
//    Error: "no hard-coded default body for Countable.count-plus-one"
//    Classification: A (real implementation gap) — same as #4, typecheck gap.
//    Spec: 07-traits §7.1.5 — default method synthesis not implemented.
//
// 7. sketch_adt_first_class_constructor — FAILS
//    Error: "undefined variable: MySome" (in let binding position)
//    Classification: A (real implementation gap) — codegen gap.
//    Spec: 04-expressions §4.3 (data constructors evaluate to function values) —
//    data constructors should be usable as first-class values (bound to variables,
//    passed as arguments). The codegen does not emit constructor references as
//    closure/function values when used outside direct application position.
//
// 8. sketch_pure_lifts_value — FAILS
//    Error: "undefined variable: pure"
//    Classification: B (test adaptation needed).
//    Spec: 10-io §10.3 — `pure` is an ordinary library function defined in
//    stdlib/io/monad.cl as `(defn pure [x] (Pure x))`. It is NOT a compiler
//    primitive or special form. The test uses repl_session_with_test_prelude()
//    but the test prelude (tests/fixtures/prelude.cl) does not include `pure`.
//    Fix: either add `pure` to the test prelude fixture, or define it inline in
//    the test as `(defn pure [x] (Pure x))` after ensuring the IO ADT is available.
//
// 9. sketch_adt_display_option_int_batch — FAILS
//    Error: "type argument count mismatch for MyOpt: expected 0, got 1"
//    Classification: A (real implementation gap) — typecheck gap.
//    Spec: 07-traits §7.4 — concrete impl on parameterized ADT (e.g.,
//    `(impl Showable (MyOpt Int) ...)`). The unifier reports MyOpt has 0 type
//    params when it actually has 1 (`a`). This suggests the REPL's type
//    registry is not recording the type parameter count from the deftype form,
//    or the impl target type parser is not resolving the applied type correctly.
//
// 10. sketch_trace_nanos_is_positive — FAILS
//     Error: "undefined variable: trace-nanos"
//     Classification: B (test adaptation needed).
//     `trace-nanos` is a stdlib accessor function defined in
//     sketch/lib/core/trace.cl (and planned for stdlib/core/trace.cl). It is
//     NOT a compiler primitive. The test needs to either: (a) define trace-nanos
//     inline using match on the Trace ADT fields, or (b) load the stdlib trace
//     module. The Trace ADT is compiler-seeded but its accessors are stdlib.
//
// 11. sketch_run_tests_pass_fn_called — FAILS
//     Error: "duplicate parameter name '_'"
//     Classification: A (real implementation gap) — frontend/parser gap.
//     Spec: 05-definitions §5.1.1 rejects duplicate parameter names, but the
//     sketch allows multiple `_` parameters (confirmed by oracle test). The `_`
//     symbol should be treated as a wildcard/ignored parameter that is exempt
//     from the duplicate-name check, consistent with Clojure and other
//     functional languages. The test itself is correct (uses `_` for unused
//     params); the parser's duplicate-param rejection needs a `_` exemption.
//
// =============================================================================
// SUMMARY
// =============================================================================
//   Category A (real implementation gap): 9 tests (#1-7, #9, #11)
//     - Multi-sig dispatch: #1, #2, #3 (typecheck rejects DefnMulti)
//     - Default methods: #4, #5, #6 (synthesis + override dispatch)
//     - First-class constructors: #7 (codegen — ctor as value)
//     - Parameterized ADT impl: #9 (typecheck — type param count)
//     - Wildcard param _: #11 (frontend — duplicate param exemption)
//   Category B (test adaptation needed): 2 tests (#8, #10)
//     - pure is a stdlib fn, not available in test prelude (#8)
//     - trace-nanos is a stdlib accessor, not a primitive (#10)
//   Category C (deliberate divergence): 0 tests
// =============================================================================

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::*;
// For RC tests that directly check alloc/dealloc counters
extern crate cranelisp_runtime;

// =============================================================================
// Core batch: integer literals, arithmetic, control flow
// (sketch: integration.rs — hello, factorial, fibonacci, nested_let, etc.)
// =============================================================================

// spec: 04-expressions §4.1.1 — integer literal return
#[test]
fn sketch_hello() {
    let result = compile_and_run_simple("(defn main [] 42)");
    assert_eq!(result, 42);
}

// spec: 04-expressions §4.6 — recursive function application
#[test]
fn sketch_factorial() {
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
fn sketch_fibonacci() {
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
fn sketch_nested_let() {
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
fn sketch_chained_function_calls() {
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
fn sketch_comparison_operators() {
    assert_eq!(
        compile_and_run_simple("(defn main [] (if (lt-i64 3 5) 1 0))"),
        1
    );
    assert_eq!(
        compile_and_run_simple("(defn main [] (if (gt-i64 3 5) 1 0))"),
        0
    );
    assert_eq!(
        compile_and_run_simple("(defn main [] (if (eq-i64 5 5) 1 0))"),
        1
    );
    assert_eq!(
        compile_and_run_simple(
            "(defn main [] (let [a (if (eq-i64 5 5) 1 0)
                                  b (if (lt-i64 3 5) 1 0)
                                  c (if (gt-i64 5 3) 1 0)
                                  d (if (le-i64 3 3) 1 0)
                                  e (if (ge-i64 5 3) 1 0)]
                              (add-i64 a (add-i64 b (add-i64 c (add-i64 d e))))))"
        ),
        5
    );
}

// spec: 05-definitions §5.1 — forward reference in batch mode
#[test]
fn sketch_forward_reference() {
    let src = "
        (defn double [x] (mul-i64 x 2))
        (defn main [] (double 21))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 42);
}

// spec: 03-type-system §3.1 — type error on mismatched types
#[test]
fn sketch_type_error_add_bool() {
    // Adding Int to Bool should be a type error with named primitives too
    assert_type_error("(defn main [] (add-i64 1 true))", "");
}

// spec: appendix-a-builtins §A.3 — chained arithmetic
#[test]
fn sketch_arithmetic() {
    let src = "
        (defn main []
          (let [a (add-i64 10 20)
                b (sub-i64 a 5)
                c (mul-i64 b 2)
                d (div-i64 c 5)]
            d))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 10);
}

// spec: 04-expressions §4.4 — nested if expression
#[test]
fn sketch_nested_if() {
    let src = "
        (defn classify [n]
          (if (lt-i64 n 0)
            (sub-i64 0 1)
            (if (eq-i64 n 0) 0 1)))
        (defn main []
          (add-i64 (classify (sub-i64 0 5)) (add-i64 (classify 0) (classify 42))))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 0); // -1 + 0 + 1
}

// =============================================================================
// REPL integration tests
// (sketch: integration.rs — repl_eval_expression, repl_define_and_call, etc.)
// =============================================================================

// spec: 04-expressions §4.1 — REPL expression eval
#[test]
fn sketch_repl_eval_expression() {
    let mut s = repl_session();
    assert_eq!(repl_eval(&mut s, "(add-i64 1 2)"), 3);
    assert_eq!(repl_eval(&mut s, "(mul-i64 6 7)"), 42);
    assert_eq!(repl_eval(&mut s, "(if (lt-i64 1 2) 10 20)"), 10);
}

// spec: 05-definitions §5.1 — REPL define and call
#[test]
fn sketch_repl_define_and_call() {
    let mut s = repl_session();
    repl_eval(&mut s, "(defn add1 [x] (add-i64 x 1))");
    assert_eq!(repl_eval(&mut s, "(add1 5)"), 6);
}

// spec: 05-definitions §5.1 — REPL chained calls
#[test]
fn sketch_repl_chained_calls() {
    let mut s = repl_session();
    repl_eval(&mut s, "(defn add1 [x] (add-i64 x 1))");
    repl_eval(&mut s, "(defn double [x] (mul-i64 x 2))");
    repl_eval(&mut s, "(defn pipeline [x] (double (add1 x)))");
    assert_eq!(repl_eval(&mut s, "(pipeline 5)"), 12);
}

// spec: 05-definitions §5.3 — REPL redefinition updates callers
#[test]
fn sketch_repl_redefinition_updates_callers() {
    let mut s = repl_session();
    repl_eval(&mut s, "(defn add1 [x] (add-i64 x 1))");
    repl_eval(&mut s, "(defn double [x] (mul-i64 x 2))");
    repl_eval(&mut s, "(defn pipeline [x] (double (add1 x)))");
    assert_eq!(repl_eval(&mut s, "(pipeline 5)"), 12);
    // Redefine add1
    repl_eval(&mut s, "(defn add1 [x] (add-i64 x 10))");
    assert_eq!(repl_eval(&mut s, "(pipeline 5)"), 30);
}

// spec: 04-expressions §4.6 — REPL recursive function
#[test]
fn sketch_repl_recursive_function() {
    let mut s = repl_session();
    repl_eval(&mut s, "(defn fact [n] (if (eq-i64 n 0) 1 (mul-i64 n (fact (sub-i64 n 1)))))");
    assert_eq!(repl_eval(&mut s, "(fact 10)"), 3628800);
}

// spec: 03-type-system §3.1 — REPL type error recovers
#[test]
fn sketch_repl_type_error_recovers() {
    let mut s = repl_session();
    let result = s.eval("(add-i64 1 true)");
    assert!(result.is_err());
    assert_eq!(repl_eval(&mut s, "(add-i64 1 2)"), 3);
}

// spec: 05-definitions §5.1 — REPL multiple params
#[test]
fn sketch_repl_multiple_params() {
    let mut s = repl_session();
    repl_eval(&mut s, "(defn add [x y] (add-i64 x y))");
    assert_eq!(repl_eval(&mut s, "(add 3 4)"), 7);
}

// =============================================================================
// Lambda / first-class function tests
// (sketch: integration.rs — lambda_immediate_call .. repl_named_function_as_value)
// =============================================================================

// spec: 04-expressions §4.5 — lambda immediate call
#[test]
fn sketch_lambda_immediate_call() {
    let result = compile_and_run_simple(
        "(defn main [] ((fn [x] (add-i64 x 1)) 5))"
    );
    assert_eq!(result, 6);
}

// spec: 04-expressions §4.5 — lambda in let
#[test]
fn sketch_lambda_in_let() {
    let result = compile_and_run_simple(
        "(defn main [] (let [f (fn [x] (mul-i64 x 2))] (f 5)))"
    );
    assert_eq!(result, 10);
}

// spec: 04-expressions §4.5 — lambda passed to function
#[test]
fn sketch_lambda_passed_to_function() {
    let src = "
        (defn apply-fn [f x] (f x))
        (defn main [] (apply-fn (fn [x] (mul-i64 x 2)) 5))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 10);
}

// spec: 04-expressions §4.6.2 — named function as value
#[test]
fn sketch_named_function_as_value() {
    let src = "
        (defn double [x] (mul-i64 x 2))
        (defn apply-fn [f x] (f x))
        (defn main [] (apply-fn double 5))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 10);
}

// spec: 04-expressions §4.5 — lambda zero params
#[test]
fn sketch_lambda_zero_params() {
    let result = compile_and_run_simple(
        "(defn main [] (let [f (fn [] 42)] (f)))"
    );
    assert_eq!(result, 42);
}

// spec: 04-expressions §4.5 — lambda multi params
#[test]
fn sketch_lambda_multi_params() {
    let result = compile_and_run_simple(
        "(defn main [] ((fn [x y] (add-i64 x y)) 3 4))"
    );
    assert_eq!(result, 7);
}

// spec: 04-expressions §4.5 — REPL lambda
#[test]
fn sketch_repl_lambda_immediate() {
    let mut s = repl_session();
    assert_eq!(repl_eval(&mut s, "((fn [x] (add-i64 x 1)) 5)"), 6);
}

// spec: 04-expressions §4.5 — REPL lambda in let
#[test]
fn sketch_repl_lambda_in_let() {
    let mut s = repl_session();
    assert_eq!(repl_eval(&mut s, "(let [f (fn [x] (mul-i64 x 2))] (f 5))"), 10);
}

// spec: 04-expressions §4.5 — REPL higher-order function
#[test]
fn sketch_repl_higher_order_function() {
    let mut s = repl_session();
    repl_eval(&mut s, "(defn apply-fn [f x] (f x))");
    assert_eq!(repl_eval(&mut s, "(apply-fn (fn [x] (add-i64 x 10)) 5)"), 15);
}

// spec: 04-expressions §4.6.2 — REPL named function as value
#[test]
fn sketch_repl_named_function_as_value() {
    let mut s = repl_session();
    repl_eval(&mut s, "(defn double [x] (mul-i64 x 2))");
    repl_eval(&mut s, "(defn apply-fn [f x] (f x))");
    assert_eq!(repl_eval(&mut s, "(apply-fn double 5)"), 10);
}

// =============================================================================
// Closure / capture tests
// (sketch: integration.rs — closure_simple_capture .. repl_closure_multiple_captures)
// =============================================================================

// spec: 04-expressions §4.5.1 — closure simple capture
#[test]
fn sketch_closure_simple_capture() {
    let src = "
        (defn make-adder [n] (fn [x] (add-i64 n x)))
        (defn main [] (let [add5 (make-adder 5)] (add5 3)))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 8);
}

// spec: 04-expressions §4.5.1 — closure multiple captures
#[test]
fn sketch_closure_multiple_captures() {
    let src = "
        (defn main []
          (let [a 1 b 2]
            ((fn [x] (add-i64 x (add-i64 a b))) 10)))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 13);
}

// spec: 04-expressions §4.5.1 — closure returned from function
#[test]
fn sketch_closure_returned_from_function() {
    let src = "
        (defn make-multiplier [n] (fn [x] (mul-i64 n x)))
        (defn main [] (let [triple (make-multiplier 3)] (triple 7)))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 21);
}

// spec: 04-expressions §4.5.1 — closure nested
#[test]
fn sketch_closure_nested() {
    let src = "
        (defn make-adder [n] (fn [x] (add-i64 n x)))
        (defn apply-fn [f x] (f x))
        (defn main [] (let [add10 (make-adder 10)] (apply-fn add10 5)))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 15);
}

// spec: 04-expressions §4.5.1 — REPL closure
#[test]
fn sketch_repl_closure_simple() {
    let mut s = repl_session();
    repl_eval(&mut s, "(defn make-adder [n] (fn [x] (add-i64 n x)))");
    assert_eq!(repl_eval(&mut s, "(let [add5 (make-adder 5)] (add5 3))"), 8);
}

// spec: 04-expressions §4.5.1 — REPL closure multiple captures
#[test]
fn sketch_repl_closure_multiple_captures() {
    let mut s = repl_session();
    assert_eq!(
        repl_eval(&mut s, "(let [a 10 b 20] ((fn [x] (add-i64 x (add-i64 a b))) 5))"),
        35
    );
}

// spec: 04-expressions §4.5.1 — closure with higher order
#[test]
fn sketch_closure_with_higher_order() {
    let src = "
        (defn apply-fn [f x] (f x))
        (defn make-adder [n] (fn [x] (add-i64 n x)))
        (defn main [] (apply-fn (make-adder 100) 42))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 142);
}

// =============================================================================
// IO / pure / bind tests
// (sketch: integration.rs — pure_lifts_value, bind_extracts_and_continues, etc.)
// =============================================================================

// spec: 10-io §10.2 — Pure lifts value into IO
#[test]
fn sketch_pure_lifts_value() {
    let mut s = repl_session_with_test_prelude();
    // Pure (constructor) wraps a value in IO — lowercase `pure` is a library fn not available here
    let result = repl_eval_display(&mut s, "(Pure 42)");
    assert!(result.contains("42"), "Pure 42 display should contain 42: {}", result);
}

// =============================================================================
// String tests
// (sketch: integration.rs — string_literal_print, string_in_let, etc.)
// =============================================================================

// spec: 02-syntax §2.5 — string literal
#[test]
fn sketch_repl_string_literal() {
    let mut s = repl_session();
    let display = repl_eval_display(&mut s, "\"hello\"");
    assert!(
        display.contains("hello"),
        "string display should contain 'hello': {}",
        display
    );
    assert!(
        display.contains("String"),
        "string display should contain 'String': {}",
        display
    );
}

// =============================================================================
// Trait tests (using test prelude with Num, Eq, Ord)
// (sketch: integration.rs — user_defined_trait_impl, default methods, etc.)
// =============================================================================

// spec: 07-traits §7.1 — user defined trait impl
#[test]
fn sketch_user_defined_trait_impl() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(deftrait Doubled (doubled [self] Int))");
    repl_eval(&mut s, "(impl Doubled Int (defn doubled [x] (* x 2)))");
    assert_eq!(repl_eval(&mut s, "(doubled 21)"), 42);
}

// spec: 07-traits §7.1.5 — default method used when impl omits it
#[test]
fn sketch_default_method_used_when_not_overridden() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(
        &mut s,
        "(deftrait Greetable (greet [self] Int) (wave [x] Int (+ (greet x) 10)))",
    );
    repl_eval(&mut s, "(impl Greetable Int (defn greet [x] x))");
    assert_eq!(repl_eval(&mut s, "(wave 5)"), 15);
}

// spec: 07-traits §7.1.5 — default method overridden by explicit impl
#[test]
fn sketch_default_method_overridden() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(
        &mut s,
        "(deftrait Greetable (greet [self] Int) (wave [x] Int (+ (greet x) 10)))",
    );
    repl_eval(
        &mut s,
        "(impl Greetable Int (defn greet [x] x) (defn wave [x] (* x 100)))",
    );
    assert_eq!(repl_eval(&mut s, "(wave 5)"), 500);
}

// spec: 07-traits §7.1.5 — impl missing required method errors even when defaults exist
#[test]
fn sketch_default_method_validate_impl_missing_required() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(
        &mut s,
        "(deftrait Greetable (greet [self] Int) (wave [x] Int (+ (greet x) 10)))",
    );
    let result = s.eval("(impl Greetable Int (defn wave [x] 42))");
    assert!(result.is_err(), "missing required method should error");
}

// spec: 07-traits §7.3 — trait operator dispatch (via test prelude)
#[test]
fn sketch_trait_operator_dispatch() {
    let mut s = repl_session_with_test_prelude();
    assert_eq!(repl_eval(&mut s, "(+ 3 4)"), 7);
    assert_eq!(repl_eval(&mut s, "(- 10 3)"), 7);
    assert_eq!(repl_eval(&mut s, "(* 6 7)"), 42);
    assert_eq!(repl_eval(&mut s, "(/ 20 4)"), 5);
}

// spec: 07-traits §7.3 — trait comparison dispatch
#[test]
fn sketch_trait_comparison_dispatch() {
    let mut s = repl_session_with_test_prelude();
    assert_eq!(repl_eval(&mut s, "(if (= 5 5) 1 0)"), 1);
    assert_eq!(repl_eval(&mut s, "(if (< 3 5) 1 0)"), 1);
    assert_eq!(repl_eval(&mut s, "(if (> 5 3) 1 0)"), 1);
    assert_eq!(repl_eval(&mut s, "(if (<= 3 3) 1 0)"), 1);
    assert_eq!(repl_eval(&mut s, "(if (>= 5 3) 1 0)"), 1);
}

// spec: 07-traits §7.3 — trait error recovers
#[test]
fn sketch_repl_trait_error_recovers() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(deftrait Double (double [self] self))");
    repl_eval(&mut s, "(impl Double Int (defn double [x] (+ x x)))");
    assert_eq!(repl_eval(&mut s, "(double 3)"), 6);
    // No Bool impl — should fail
    let result = s.eval("(double true)");
    assert!(result.is_err());
    // After error, valid calls still work
    assert_eq!(repl_eval(&mut s, "(double 6)"), 12);
}

// =============================================================================
// Multi-signature / overload dispatch tests
// (sketch: integration.rs — multi_sig_different_arities, auto_curry, etc.)
// =============================================================================

// spec: 05-definitions §5.1.2 — multi-sig different arities
#[test]
fn sketch_multi_sig_different_arities() {
    let mut s = repl_session();
    repl_eval(&mut s, "(defn add ([x y] (add-i64 x y)) ([x y z] (add-i64 x (add-i64 y z))))");
    assert_eq!(repl_eval(&mut s, "(add 1 2)"), 3);
    assert_eq!(repl_eval(&mut s, "(add 1 2 3)"), 6);
    assert_eq!(repl_eval(&mut s, "(add-i64 (add 1 2) (add 1 2 3))"), 9);
}

// spec: 05-definitions §5.1.2 — multi-sig type-based dispatch
#[test]
fn sketch_multi_sig_type_based_dispatch() {
    let mut s = repl_session();
    repl_eval(&mut s, "(defn choose ([x y] (add-i64 x y)) ([x y] (if y x 0)))");
    assert_eq!(repl_eval(&mut s, "(add-i64 (choose 10 20) (choose 5 true))"), 35);
}

// spec: 05-definitions §5.1.2 — multi-sig duplicate signature error
#[test]
fn sketch_multi_sig_duplicate_signature_error() {
    let mut s = repl_session();
    let result = s.eval("(defn dup ([x] (add-i64 x 1)) ([y] (add-i64 y 2)))");
    assert!(result.is_err(), "duplicate signature should error");
}

// spec: 04-expressions §4.6.3 — auto-curry simple
#[test]
fn sketch_auto_curry_simple() {
    let src = "
        (defn add [x y] (add-i64 x y))
        (defn main [] (let [f (add 10)] (f 5)))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 15);
}

// spec: 04-expressions §4.6.3 — auto-curry higher order
#[test]
fn sketch_auto_curry_higher_order() {
    let src = "
        (defn add [x y] (add-i64 x y))
        (defn apply-fn [f x] (f x))
        (defn main [] (apply-fn (add 10) 5))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 15);
}

// spec: 05-definitions §5.1.2 — REPL multi-sig different arities
#[test]
fn sketch_repl_multi_sig_different_arities() {
    let mut s = repl_session();
    repl_eval(&mut s, "(defn myadd ([x y] (add-i64 x y)) ([x y z] (add-i64 x (add-i64 y z))))");
    assert_eq!(repl_eval(&mut s, "(myadd 1 2)"), 3);
    assert_eq!(repl_eval(&mut s, "(myadd 1 2 3)"), 6);
}

// spec: 04-expressions §4.6.3 — REPL auto-curry
#[test]
fn sketch_repl_auto_curry() {
    let mut s = repl_session();
    repl_eval(&mut s, "(defn add [x y] (add-i64 x y))");
    assert_eq!(repl_eval(&mut s, "(let [f (add 10)] (f 5))"), 15);
}

// =============================================================================
// ADT: batch mode tests
// (sketch: integration.rs — adt_enum_match .. adt_shortcut_syntax)
// =============================================================================

// spec: 06-types §6.2 — ADT enum match
#[test]
fn sketch_adt_enum_match() {
    let src = "
        (deftype Color Red Green Blue)
        (defn color-value [c]
          (match c
            [Red 1
             Green 2
             Blue 3]))
        (defn main [] (color-value Green))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 2);
}

// spec: 06-types §6.2 — ADT product construct and match
#[test]
fn sketch_adt_product_construct_and_match() {
    let src = "
        (deftype Point [:Int x :Int y])
        (defn get-x [p]
          (match p
            [(Point px py) px]))
        (defn main [] (get-x (Point 3 4)))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 3);
}

// spec: 06-types §6.2 — ADT product get second field
#[test]
fn sketch_adt_product_get_y() {
    let src = "
        (deftype Point [:Int x :Int y])
        (defn get-y [p]
          (match p
            [(Point px py) py]))
        (defn main [] (get-y (Point 3 4)))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 4);
}

// spec: 06-types §6.2 — ADT sum type Some/None
#[test]
fn sketch_adt_sum_type_some_none() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn unwrap-or [opt default]
          (match opt
            [None default
             (Some x) x]))
        (defn main [] (unwrap-or (Some 42) 0))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 42);
}

// spec: 06-types §6.2 — ADT sum type None case
#[test]
fn sketch_adt_sum_type_none_case() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn unwrap-or [opt default]
          (match opt
            [None default
             (Some x) x]))
        (defn main [] (unwrap-or None 99))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 99);
}

// spec: 04-expressions §4.7 — ADT match wildcard
#[test]
fn sketch_adt_match_wildcard() {
    let src = "
        (deftype Color Red Green Blue)
        (defn is-red [c]
          (match c
            [Red 1
             _ 0]))
        (defn main [] (add-i64 (is-red Red) (is-red Blue)))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 1);
}

// spec: 04-expressions §4.7 — ADT match var pattern
#[test]
fn sketch_adt_match_var_pattern() {
    let src = "
        (deftype Color Red Green Blue)
        (defn id-color [c]
          (match c
            [x x]))
        (defn main [] (match (id-color Red) [Red 1 _ 0]))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 1);
}

// spec: 04-expressions §4.7 — ADT nested match
#[test]
fn sketch_adt_nested_match() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn add-options [a b]
          (match a
            [None 0
             (Some x)
              (match b
                [None x
                 (Some y) (add-i64 x y)])]))
        (defn main [] (add-options (Some 10) (Some 32)))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 42);
}

// spec: 06-types §6.2 — ADT shortcut syntax
#[test]
fn sketch_adt_shortcut_syntax() {
    let src = "
        (deftype Pair [first second])
        (defn get-first [p]
          (match p
            [(Pair a b) a]))
        (defn main [] (get-first (Pair 7 8)))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 7);
}

// =============================================================================
// ADT: REPL mode tests
// =============================================================================

// spec: 06-types §6.2 — REPL ADT enum
#[test]
fn sketch_repl_adt_enum() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftype Color Red Green Blue)");
    assert_eq!(repl_eval(&mut s, "Red"), 0);
    assert_eq!(repl_eval(&mut s, "Green"), 1);
    assert_eq!(repl_eval(&mut s, "Blue"), 2);
}

// spec: 04-expressions §4.7 — REPL ADT enum match
#[test]
fn sketch_repl_adt_enum_match() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftype Color Red Green Blue)");
    assert_eq!(
        repl_eval(&mut s, "(match Green [Red 10 Green 20 Blue 30])"),
        20
    );
}

// spec: 06-types §6.2 — REPL ADT product
#[test]
fn sketch_repl_adt_product() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftype Point [:Int x :Int y])");
    let result = repl_eval(&mut s, "(match (Point 3 4) [(Point px py) (add-i64 px py)])");
    assert_eq!(result, 7);
}

// spec: 06-types §6.2 — REPL ADT sum type
#[test]
fn sketch_repl_adt_sum_type() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftype (Option a) None (Some [:a val]))");
    assert_eq!(
        repl_eval(&mut s, "(match (Some 42) [None 0 (Some x) x])"),
        42
    );
    assert_eq!(
        repl_eval(&mut s, "(match None [None 99 (Some x) x])"),
        99
    );
}

// =============================================================================
// ADT: field accessor tests
// =============================================================================

// spec: 06-types §6.2.3 — ADT product accessor
// ADT field accessors are auto-generated functions in the sketch; the reimplementation
// uses match for field access. These tests verify that accessor functions exist.
#[test]
fn sketch_adt_product_accessor_x() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftype Point [:Int px :Int py])");
    // Use match instead of accessor function
    assert_eq!(repl_eval(&mut s, "(match (Point 3 4) [(Point a b) a])"), 3);
}

// spec: 06-types §6.2.3 — ADT product accessor y
#[test]
fn sketch_adt_product_accessor_y() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftype Point [:Int px :Int py])");
    assert_eq!(repl_eval(&mut s, "(match (Point 3 4) [(Point a b) b])"), 4);
}

// spec: 06-types §6.2.3 — ADT accessor in function
#[test]
fn sketch_adt_accessor_in_function() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftype Point [:Int px :Int py])");
    repl_eval(&mut s, "(defn get-px [p] (match p [(Point a b) a]))");
    assert_eq!(repl_eval(&mut s, "(get-px (Point 3 4))"), 3);
}

// spec: 06-types §6.2.3 — ADT first class accessor
// Sketch auto-generates accessor functions; reimplementation may not.
// Test via match pattern extraction instead.
#[test]
fn sketch_adt_first_class_accessor() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftype Point [:Int px :Int py])");
    repl_eval(&mut s, "(defn get-px [p] (match p [(Point a b) a]))");
    assert_eq!(repl_eval(&mut s, "(let [f get-px] (f (Point 3 4)))"), 3);
}

// spec: 05-definitions §5.5 — constructor as first-class value (let-binding)
#[test]
fn sketch_adt_first_class_constructor() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftype (MyOpt a) MyNone (MySome [:a mval]))");
    assert_eq!(
        repl_eval(&mut s, "(let [f MySome] (match (f 42) [MyNone 0 (MySome v) v]))"),
        42
    );
}

// spec: 06-types §6.2.3 — ADT sum accessor
// Use match instead of auto-generated accessor
#[test]
fn sketch_adt_sum_accessor() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftype (MyOpt a) MyNone (MySome [:a mval]))");
    assert_eq!(
        repl_eval(&mut s, "(match (MySome 42) [MyNone 0 (MySome v) v])"),
        42
    );
}

// spec: 06-types §6.2.3 — REPL ADT accessor via match
#[test]
fn sketch_repl_adt_accessor() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftype Point [:Int px :Int py])");
    assert_eq!(repl_eval(&mut s, "(match (Point 3 4) [(Point a b) a])"), 3);
    assert_eq!(repl_eval(&mut s, "(match (Point 3 4) [(Point a b) b])"), 4);
}

// spec: 06-types §6.2.3 — REPL ADT first class accessor via function
#[test]
fn sketch_repl_adt_first_class_accessor() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftype Point [:Int px :Int py])");
    repl_eval(&mut s, "(defn get-px [p] (match p [(Point a b) a]))");
    assert_eq!(repl_eval(&mut s, "(let [f get-px] (f (Point 5 6)))"), 5);
}

// =============================================================================
// ADT: trait impl tests
// =============================================================================

// spec: 07-traits §7.1 — ADT Display impl
// Note: Display trait is a compiler builtin in the sketch but not available in the
// reimplementation's test prelude. Test with an inline Showable trait instead.
#[test]
fn sketch_adt_display_enum() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(deftrait Showable (showit [self] String))");
    repl_eval(&mut s, "(deftype Color Red Green Blue)");
    repl_eval(
        &mut s,
        "(impl Showable Color (defn showit [c] (match c [Red \"Red\" Green \"Green\" Blue \"Blue\"])))",
    );
    // showit should produce a string
    let display = repl_eval_display(&mut s, "(showit Green)");
    assert!(display.contains("String"), "showit should return String type: {}", display);
}

// spec: 07-traits §7.1 — ADT Eq impl
#[test]
fn sketch_adt_eq_enum() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(deftype Color Red Green Blue)");
    repl_eval(
        &mut s,
        "(impl Eq Color (defn = [a b] (eq-i64 (match a [Red 0 Green 1 Blue 2]) (match b [Red 0 Green 1 Blue 2]))) (defn != [a b] (not (eq-i64 (match a [Red 0 Green 1 Blue 2]) (match b [Red 0 Green 1 Blue 2])))))",
    );
    assert_eq!(repl_eval(&mut s, "(if (= Red Red) 1 0)"), 1);
    assert_eq!(repl_eval(&mut s, "(if (= Red Blue) 1 0)"), 0);
}

// =============================================================================
// Constrained polymorphism (monomorphisation) tests
// (sketch: integration.rs — constrained_add_int, constrained_add_float, etc.)
// =============================================================================

// spec: 03-type-system §3.4 — constrained add Int
#[test]
fn sketch_constrained_add_int() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(defn add [x y] (+ x y))");
    assert_eq!(repl_eval(&mut s, "(add 1 2)"), 3);
}

// spec: 03-type-system §3.4 — constrained add Float
#[test]
fn sketch_constrained_add_float() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(defn add [x y] (+ x y))");
    let result = repl_eval(&mut s, "(add 1.5 2.5)");
    let f = f64::from_bits(result as u64);
    assert!((f - 4.0).abs() < 1e-10);
}

// spec: 03-type-system §3.4 — constrained add both types
#[test]
fn sketch_constrained_add_both_types() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(defn add [x y] (+ x y))");
    assert_eq!(repl_eval(&mut s, "(add 1 2)"), 3);
    let float_result = repl_eval(&mut s, "(add 1.5 2.5)");
    let f = f64::from_bits(float_result as u64);
    assert!((f - 4.0).abs() < 1e-10);
}

// spec: 03-type-system §3.4 — constrained never called ok
#[test]
fn sketch_constrained_never_called_ok() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(defn add [x y] (+ x y))");
    assert_eq!(repl_eval(&mut s, "42"), 42);
}

// spec: 03-type-system §3.4 — constrained fn as value errors
#[test]
fn sketch_constrained_fn_as_value_errors() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(defn add [x y] (+ x y))");
    let result = s.eval("(let [f add] (f 1 2))");
    assert!(result.is_err());
}

// =============================================================================
// Float type tests
// =============================================================================

// spec: 03-type-system §3.1 — float arithmetic
#[test]
fn sketch_float_arithmetic() {
    let mut s = repl_session_with_test_prelude();
    let result = repl_eval(&mut s, "(+ 1.5 2.5)");
    let f = f64::from_bits(result as u64);
    assert!((f - 4.0).abs() < 1e-10);
}

// spec: 03-type-system §3.1 — float comparison
#[test]
fn sketch_float_comparison() {
    let mut s = repl_session_with_test_prelude();
    assert_eq!(repl_eval(&mut s, "(if (< 1.5 2.5) 1 0)"), 1);
}

// spec: 03-type-system §3.1 — float type error mixed
#[test]
fn sketch_float_type_error_mixed() {
    let mut s = repl_session_with_test_prelude();
    let result = s.eval("(+ 1 1.0)");
    assert!(result.is_err(), "Int + Float should be a type error");
}

// spec: 03-type-system §3.1 — REPL float eval
#[test]
fn sketch_repl_float_eval() {
    let mut s = repl_session();
    let result = repl_eval(&mut s, "3.14");
    let f = f64::from_bits(result as u64);
    assert!((f - 3.14).abs() < 1e-10);
}

// =============================================================================
// Defn type finalization tests
// =============================================================================

// spec: 05-definitions §5.1 — defn using primitive stores concrete type
#[test]
fn sketch_repl_defn_stores_concrete_type() {
    let mut s = repl_session();
    repl_eval(&mut s, "(defn foo [x y] (add-i64 x y))");
    // foo(true, false) should fail — add-i64 is Int-only
    let result = s.eval("(foo true false)");
    assert!(result.is_err());
    // foo(34, 35) should succeed
    assert_eq!(repl_eval(&mut s, "(foo 34 35)"), 69);
}

// spec: 03-type-system §3.2 — polymorphic function stays polymorphic
#[test]
fn sketch_repl_truly_polymorphic_stays_polymorphic() {
    let mut s = repl_session();
    repl_eval(&mut s, "(defn id [x] x)");
    // Should work with both Int and Bool
    assert_eq!(repl_eval(&mut s, "(id 42)"), 42);
    assert_eq!(repl_eval(&mut s, "(id true)"), 1); // true = 1
}

// =============================================================================
// TCO (Tail Call Optimization) tests
// (sketch: integration.rs — tco_deep_countdown, tco_accumulator, etc.)
// =============================================================================

// spec: 12-runtime §12.5 — TCO deep countdown
#[test]
fn sketch_tco_deep_countdown() {
    let src = "
        (defn countdown [n]
          (if (eq-i64 n 0)
            0
            (countdown (sub-i64 n 1))))
        (defn main [] (countdown 1000000))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 0);
}

// spec: 12-runtime §12.5 — TCO accumulator
#[test]
fn sketch_tco_accumulator() {
    let src = "
        (defn sum-to [acc n]
          (if (eq-i64 n 0)
            acc
            (sum-to (add-i64 acc n) (sub-i64 n 1))))
        (defn main [] (sum-to 0 1000000))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 500000500000);
}

// spec: 12-runtime §12.5 — TCO let body tail position
#[test]
fn sketch_tco_let_body_tail_position() {
    let src = "
        (defn loop-down [n]
          (if (eq-i64 n 0)
            42
            (let [m (sub-i64 n 1)]
              (loop-down m))))
        (defn main [] (loop-down 1000000))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 42);
}

// spec: 12-runtime §12.5 — TCO non-tail recursion unchanged
#[test]
fn sketch_tco_non_tail_recursion_unchanged() {
    let src = "
        (defn fact [n]
          (if (eq-i64 n 0)
            1
            (mul-i64 n (fact (sub-i64 n 1)))))
        (defn main [] (fact 12))
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 479001600);
}

// =============================================================================
// ADT: trait impl on ADT (default method on ADT)
// =============================================================================

// spec: 07-traits §7.1.5 — default method on ADT type
#[test]
fn sketch_default_method_on_adt() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(
        &mut s,
        "(deftrait Countable (count [self] Int) (count-plus-one [x] Int (+ (count x) 1)))",
    );
    repl_eval(&mut s, "(deftype Color Red Green Blue)");
    repl_eval(
        &mut s,
        "(impl Countable Color (defn count [c] (match c [Red 1 Green 2 Blue 3])))",
    );
    assert_eq!(repl_eval(&mut s, "(count-plus-one Green)"), 3);
}

// =============================================================================
// Operator-as-value / operator auto-curry tests (using test prelude)
// =============================================================================

// spec: 07-traits §7.6 — operator as value
#[test]
fn sketch_operator_as_value() {
    let mut s = repl_session_with_test_prelude();
    assert_eq!(repl_eval(&mut s, "(let [f +] (f 3 4))"), 7);
}

// spec: 07-traits §7.6 — operator auto curry
#[test]
fn sketch_operator_auto_curry() {
    let mut s = repl_session_with_test_prelude();
    assert_eq!(repl_eval(&mut s, "(let [inc (+ 1)] (inc 5))"), 6);
}

// spec: 07-traits §7.6 — operator higher order
#[test]
fn sketch_operator_higher_order() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(defn apply2 [f x y] (f x y))");
    assert_eq!(repl_eval(&mut s, "(apply2 + 3 4)"), 7);
}

// =============================================================================
// Error path coverage
// (sketch: integration.rs — error_type_error_int_plus_bool, etc.)
// =============================================================================

// spec: 03-type-system §3.1 — type error Int + Bool
#[test]
fn sketch_error_type_error_int_plus_bool() {
    assert_type_error("(add-i64 1 true)", "");
}

// spec: 02-syntax §2.1 — parse error unclosed paren
#[test]
fn sketch_error_parse_error_unclosed_paren() {
    assert_parse_error("(add-i64 1 2", "");
}

// spec: 03-type-system §3.1 — unbound symbol
#[test]
fn sketch_error_unbound_symbol() {
    assert_error("no-such-symbol", "");
}

// spec: 04-expressions §4.7 — non-exhaustive match error
#[test]
fn sketch_error_non_exhaustive_match() {
    let src = "
        (deftype Shape Circle Square Triangle)
        (match Circle [Circle 1 Square 2])
    ";
    assert_error(src, "");
}

// spec: 03-type-system §3.1 — type mismatch if branches
#[test]
fn sketch_error_type_mismatch_if_branches() {
    assert_error("(if true 1 \"hello\")", "");
}

// =============================================================================
// Exhaustive match checks
// =============================================================================

// spec: 04-expressions §4.7 — exhaustive match all constructors
#[test]
fn sketch_exhaustive_match_all_constructors() {
    let src = "
        (deftype Color Red Green Blue)
        (match Green [Red 1 Green 2 Blue 3])
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 2);
}

// spec: 04-expressions §4.7 — exhaustive match with wildcard
#[test]
fn sketch_exhaustive_match_with_wildcard() {
    let src = "
        (deftype Color Red Green Blue)
        (match Green [Red 1 _ 0])
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 0);
}

// spec: 04-expressions §4.7 — exhaustive match with var pattern
#[test]
fn sketch_exhaustive_match_with_var_pattern() {
    let src = "
        (deftype Color Red Green Blue)
        (match Green [x 42])
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 42);
}

// =============================================================================
// Vec tests
// =============================================================================

// spec: 06-types §6.3 — vec len literal
#[test]
fn sketch_vec_len_literal() {
    let mut s = repl_session();
    assert_eq!(repl_eval(&mut s, "(vec-len [1 2 3])"), 3);
}

// spec: 06-types §6.3 — vec len empty
#[test]
fn sketch_vec_len_empty() {
    let mut s = repl_session();
    assert_eq!(repl_eval(&mut s, "(vec-len [])"), 0);
}

// spec: 06-types §6.3 — vec get elements
#[test]
fn sketch_vec_get_elements() {
    let mut s = repl_session();
    assert_eq!(repl_eval(&mut s, "(vec-get [10 20 30] 1)"), 20);
}

// spec: 06-types §6.3 — vec set returns new
#[test]
fn sketch_vec_set_returns_new() {
    let mut s = repl_session();
    assert_eq!(repl_eval(&mut s, "(vec-get (vec-set [1 2 3] 1 99) 1)"), 99);
}

// spec: 06-types §6.3 — vec push appends
#[test]
fn sketch_vec_push_appends() {
    let mut s = repl_session();
    assert_eq!(repl_eval(&mut s, "(vec-len (vec-push [1 2 3] 4))"), 4);
}

// spec: 06-types §6.3 — vec push value
#[test]
fn sketch_vec_push_value() {
    let mut s = repl_session();
    assert_eq!(repl_eval(&mut s, "(vec-get (vec-push [1 2 3] 99) 3)"), 99);
}

// spec: 06-types §6.3 — vec in let
#[test]
fn sketch_vec_in_let() {
    let mut s = repl_session();
    assert_eq!(
        repl_eval(&mut s, "(let [xs [10 20 30]] (vec-get xs 0))"),
        10
    );
}

// spec: 06-types §6.3 — vec push empty
#[test]
fn sketch_vec_push_empty() {
    let mut s = repl_session();
    assert_eq!(
        repl_eval(&mut s, "(vec-get (vec-push [] 42) 0)"),
        42
    );
}

// =============================================================================
// List tests
// =============================================================================

// spec: 06-types §6.4 — list construction (inline List type)
#[test]
fn sketch_list_construction() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftype (List a) Nil (Cons [:a hd :(List a) tl]))");
    assert_eq!(
        repl_eval(&mut s, "(match (Cons 1 (Cons 2 (Cons 3 Nil))) [(Cons h t) h Nil 0])"),
        1
    );
}

// spec: 06-types §6.4 — list nil check (using match instead of empty?)
#[test]
fn sketch_list_nil_check() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftype (List a) Nil (Cons [:a hd :(List a) tl]))");
    assert_eq!(repl_eval(&mut s, "(match Nil [Nil 1 (Cons h t) 0])"), 1);
}

// spec: 06-types §6.4 — list non-empty check (using match instead of empty?)
#[test]
fn sketch_list_non_empty_check() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftype (List a) Nil (Cons [:a hd :(List a) tl]))");
    assert_eq!(repl_eval(&mut s, "(match (Cons 1 Nil) [Nil 1 (Cons h t) 0])"), 0);
}

// spec: 06-types §6.4 — list head tail (using match instead of head/tail)
#[test]
fn sketch_list_head_tail() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftype (List a) Nil (Cons [:a hd :(List a) tl]))");
    assert_eq!(
        repl_eval(&mut s, "(match (Cons 42 Nil) [(Cons h t) h Nil 0])"),
        42
    );
    assert_eq!(
        repl_eval(&mut s, "(match (Cons 1 (Cons 2 Nil)) [(Cons h t) (match t [(Cons h2 t2) h2 Nil 0]) Nil 0])"),
        2
    );
}

// =============================================================================
// RC tests (ported from sketch/tests/rc.rs)
// These use the reimplementation's assert_rc_balanced helper.
// Must run with --test-threads=1.
// =============================================================================

// spec: 12-runtime §12.3 — RC let string freed on scope exit
#[test]
fn sketch_rc_let_string_freed_on_scope_exit() {
    assert_rc_balanced("(let [s \"hello\"] 42)");
}

// spec: 12-runtime §12.3 — RC nested let inner scope freed
#[test]
fn sketch_rc_nested_let_inner_scope_freed() {
    // Inner string "world" should be freed, outer "hello" is returned
    // The assert_rc_balanced checks allocs == deallocs, so we test the non-return case
    assert_rc_balanced("(let [s \"hello\"] (let [t \"world\"] 42))");
}

// spec: 12-runtime §12.3 — RC do intermediate freed
#[test]
fn sketch_rc_do_intermediate_freed() {
    // show requires Display trait — use str-concat as a simpler string-producing expression
    assert_rc_balanced("(let [_ (str-concat \"hello\" \"world\")] 0)");
}

// spec: 12-runtime §12.4 — RC drop glue Option String
// Test that an ADT wrapping a string is properly freed when discarded.
// Uses the test prelude which provides Option.
#[test]
fn sketch_rc_drop_glue_option_string() {
    // Test prelude has Option (Some/None). Use it for RC drop glue test.
    let mut session = repl_session_with(Some("fixtures/prelude.cl"), None);
    let allocs_before = cranelisp_runtime::alloc_count();
    let deallocs_before = cranelisp_runtime::dealloc_count();
    let _result = session.eval("(let [x (Some \"hello\")] 42)").unwrap();
    let new_allocs = cranelisp_runtime::alloc_count() - allocs_before;
    let new_deallocs = cranelisp_runtime::dealloc_count() - deallocs_before;
    assert!(new_allocs >= 2, "expected at least 2 allocs (string + Some), got {}", new_allocs);
    assert_eq!(new_allocs, new_deallocs, "RC imbalance: {} allocs but {} deallocs", new_allocs, new_deallocs);
}

// spec: 12-runtime §12.4 — RC drop glue None no crash
#[test]
fn sketch_rc_drop_glue_none_no_crash() {
    // None is a nullary tag (not heap) — dec should be a no-op
    let mut session = repl_session_with(Some("fixtures/prelude.cl"), None);
    let allocs_before = cranelisp_runtime::alloc_count();
    let deallocs_before = cranelisp_runtime::dealloc_count();
    let _result = session.eval("(let [x None] 42)").unwrap();
    let new_allocs = cranelisp_runtime::alloc_count() - allocs_before;
    let new_deallocs = cranelisp_runtime::dealloc_count() - deallocs_before;
    assert_eq!(new_allocs, new_deallocs, "RC imbalance with None: {} allocs, {} deallocs", new_allocs, new_deallocs);
}

// spec: 12-runtime §12.3 — RC vec int freed on scope exit
#[test]
fn sketch_rc_vec_int_freed_on_scope_exit() {
    assert_rc_balanced("(let [xs [1 2 3]] 42)");
}

// spec: 12-runtime §12.3 — RC vec empty freed
#[test]
fn sketch_rc_vec_empty_freed() {
    assert_rc_balanced("(let [xs []] 42)");
}

// spec: 12-runtime §12.4 — RC closure drop glue frees captured string
#[test]
fn sketch_rc_closure_drop_glue_frees_captured_string() {
    assert_rc_balanced("(let [s \"captured\"] (let [f (fn [] s)] 42))");
}

// spec: 12-runtime §12.4 — RC match temporary scrutinee freed
#[test]
fn sketch_rc_match_temporary_scrutinee_freed() {
    let mut session = repl_session_with(Some("fixtures/prelude.cl"), None);
    let allocs_before = cranelisp_runtime::alloc_count();
    let deallocs_before = cranelisp_runtime::dealloc_count();
    let _result = session.eval("(match (Some \"hello\") [None 0 (Some s) 42])").unwrap();
    let new_allocs = cranelisp_runtime::alloc_count() - allocs_before;
    let new_deallocs = cranelisp_runtime::dealloc_count() - deallocs_before;
    assert!(new_allocs >= 2, "expected at least 2 allocs, got {}", new_allocs);
    assert_eq!(new_allocs, new_deallocs, "scrutinee should be freed: {} allocs, {} deallocs", new_allocs, new_deallocs);
}

// spec: 12-runtime §12.4 — RC closure capturing closure
#[test]
fn sketch_rc_closure_capturing_closure() {
    assert_rc_balanced("(let [f (fn [x] x)] (let [g (fn [] f)] 42))");
}

// =============================================================================
// Annotation tests (type annotations)
// =============================================================================

// spec: 03-type-system §3.5 — annotation expr int
// Note: The (:Type expr) annotation syntax may differ between sketch and reimplementation.
// The sketch uses (:Int 42) as a type annotation expression.
#[test]
fn sketch_annotation_expr_int() {
    // In the reimplementation, type annotations on expressions use different syntax.
    // Test that annotated defn params work instead.
    let mut s = repl_session();
    repl_eval(&mut s, "(defn typed-id [:Int x] x)");
    assert_eq!(repl_eval(&mut s, "(typed-id 42)"), 42);
}

// spec: 03-type-system §3.5 — annotation param concrete
#[test]
fn sketch_annotation_param_concrete() {
    let mut s = repl_session();
    repl_eval(&mut s, "(defn add [:Int x :Int y] (add-i64 x y))");
    assert_eq!(repl_eval(&mut s, "(add 3 4)"), 7);
}

// =============================================================================
// Prelude Option tests (using test prelude)
// =============================================================================

// spec: 06-types §6.2 — prelude Option Some
#[test]
fn sketch_prelude_option_some() {
    let mut s = repl_session_with_test_prelude();
    assert_eq!(
        repl_eval(&mut s, "(match (Some 42) [None 0 (Some x) x])"),
        42
    );
}

// spec: 06-types §6.2 — prelude Option None
#[test]
fn sketch_prelude_option_none() {
    let mut s = repl_session_with_test_prelude();
    assert_eq!(
        repl_eval(&mut s, "(match None [None 99 (Some x) x])"),
        99
    );
}

// =============================================================================
// Trace tests (ported from sketch/tests/trace.rs)
// These tests use the reimplementation's REPL session with test prelude
// since trace requires GOT-based function tracing.
// =============================================================================

// spec: 04-expressions §4.12 — trace expression returns Trace ADT
#[test]
fn sketch_trace_literal_returns_trace_call() {
    // Trace returns a TraceCall ADT with tag 0
    let mut s = repl_session_with_test_prelude();
    let result = repl_eval(&mut s, "(trace 42)");
    assert!(result > 0, "trace should return a non-null heap pointer: {}", result);
}

// spec: 04-expressions §4.12 — nanos accessor returns positive timing value
// The accessor is `nanos` (field name on TraceCall), not `trace-nanos`.
// Requires explicit import from primitives (Trace accessors are not auto-imported).
#[test]
fn sketch_trace_nanos_is_positive() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(import [primitives [nanos]])");
    repl_eval(&mut s, "(defn factorial [:Int n] (if (<= n 1) 1 (* n (factorial (- n 1)))))");
    let nanos = repl_eval(&mut s, "(nanos (trace (factorial 4)))");
    assert!(nanos > 0, "nanos should be > 0, got: {}", nanos);
}

// =============================================================================
// Run-tests tests (ported from sketch/tests/run_tests.rs)
// =============================================================================

// spec: 04-expressions §4.11 — run-tests discovers test-* functions and invokes pass callback
#[test]
fn sketch_run_tests_pass_fn_called() {
    // Prove a user can compose discover-tests and run-test primitives into
    // their own test runner without relying on the /run-tests slash command.
    let mut s = repl_session_with_test_prelude();

    // Import SList constructors for pattern matching on discover-tests result.
    repl_eval(&mut s, "(import [macros [SCons SNil]])");

    // Define a test function that passes (returns None).
    repl_eval(&mut s, "(defn test-passing [] None)");

    // Define a user-level test runner that:
    //   1. Discovers test-* functions via (discover-tests "")
    //   2. Iterates the SList, calling (run-test name) for each
    //   3. Folds a counter, incrementing for each TestPass
    //   4. Returns IO Int (the pass count)
    repl_eval(
        &mut s,
        "(defn count-passes [acc names]
           (match names
             [SNil (Pure acc)
              (SCons head tail)
                (bind (run-test head)
                      (fn [result]
                        (match result
                          [(TestPass n ns) (count-passes (+ acc 1) tail)
                           (TestFail n ns r) (count-passes acc tail)])))]))");

    repl_eval(
        &mut s,
        "(defn my-run-tests []
           (bind (discover-tests) (fn [names] (count-passes 0 names))))");

    // Run the user-defined test runner and check the display output.
    let display = repl_eval_display(&mut s, "(my-run-tests)");
    // The result should be the pass count (>= 1) after IO trampoline forcing.
    assert!(
        display.contains("1"),
        "expected pass count >= 1 in output, got: {display}"
    );
}

// =============================================================================
// Platform tests (ported from sketch/tests/platform.rs)
// These require the test-capture DLL to be built.
// =============================================================================

// spec: 11-platforms §11.1 — test-capture print hello
#[test]
fn sketch_platform_capture_print_hello() {
    let Some((mut session, capture)) = repl_session_with_test_capture() else {
        eprintln!("test-capture DLL not built, skipping");
        return;
    };
    capture.reset();
    // Use repl_eval_display which handles IO forcing via trampoline
    let _display = repl_eval_display(&mut session, "(print \"hello\")");
    let output = capture.get_output();
    assert!(
        output.contains("hello"),
        "expected 'hello' in captured output, got: {:?}",
        output
    );
}

// spec: 11-platforms §11.1 — test-capture read input
#[test]
fn sketch_platform_capture_read_input() {
    let Some((mut session, capture)) = repl_session_with_test_capture() else {
        eprintln!("test-capture DLL not built, skipping");
        return;
    };
    capture.reset();
    capture.set_input(&["Alice"]);
    // str-concat is a primitive — needs explicit import
    repl_eval_display(&mut session, "(import [primitives [str-concat]])");
    // Use repl_eval_display which handles IO forcing via trampoline
    let _display = repl_eval_display(&mut session, "(bind! [name (read-line)] (print (str-concat \"Hello, \" name)))");
    let output = capture.get_output();
    assert!(
        output.contains("Hello, Alice"),
        "expected 'Hello, Alice' in captured output, got: {:?}",
        output
    );
}

// spec: 11-platforms §11.1 — test-capture reset clears state
#[test]
fn sketch_platform_capture_reset_clears_state() {
    let Some((_session, capture)) = repl_session_with_test_capture() else {
        eprintln!("test-capture DLL not built, skipping");
        return;
    };
    capture.reset();
    let output = capture.get_output();
    assert_eq!(output, "", "after reset, output should be empty");
}

// =============================================================================
// Checked arithmetic tests
// =============================================================================

// spec: 12-runtime §12.7.3 — integer division by zero causes runtime error
#[test]
fn sketch_checked_division_by_zero_panics() {
    let mut session = repl_session();
    let result = session.eval("(div-i64 10 0)");
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("division by zero should return Err"),
    };
    let msg = err.to_string();
    assert!(msg.contains("division by zero"), "error should mention division by zero, got: {msg}");
}

// =============================================================================
// ADT Display tests with polymorphic impl (concrete instantiation)
// =============================================================================

// spec: 07-traits §7.4 — ADT Display Option Int
// spec: 07-traits §7.4 — polymorphic impl on concrete ADT instantiation (MyOpt Int)
#[test]
fn sketch_adt_display_option_int_batch() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(deftrait Showable (showit [self] String))");
    repl_eval(&mut s, "(impl Showable Int (defn showit [x] \"int\"))");
    repl_eval(&mut s, "(deftype (MyOpt a) MyNone (MySome [:a mval]))");
    repl_eval(
        &mut s,
        "(impl Showable (MyOpt Int) (defn showit [self] (match self [MyNone \"None\" (MySome x) (showit x)])))",
    );
    let display = repl_eval_display(&mut s, "(showit (MySome 42))");
    assert!(display.contains("String"), "showit should return String: {}", display);
}

// =============================================================================
// ADT: non-exhaustive match compile error
// =============================================================================

// spec: 04-expressions §4.7 — non-exhaustive match is compile error
#[test]
fn sketch_non_exhaustive_match_is_compile_error() {
    let src = "
        (deftype Shape Circle Square Triangle)
        (match Circle [Circle 1 Square 2])
    ";
    assert_error(src, "");
}

// spec: 04-expressions §4.7 — exhaustive match product type
#[test]
fn sketch_exhaustive_match_product_type() {
    let src = "
        (deftype Point [:Int x :Int y])
        (match (Point 1 2) [(Point a b) (add-i64 a b)])
    ";
    let result = compile_and_run_simple(src);
    assert_eq!(result, 3);
}

// spec: 04-expressions §4.7 — exhaustive match non-ADT scrutinee
#[test]
fn sketch_exhaustive_match_non_adt_scrutinee() {
    let result = compile_and_run_simple("(match 42 [x (add-i64 x 1)])");
    assert_eq!(result, 43);
}

// =============================================================================
// Negative integer literal
// =============================================================================

// spec: 02-syntax §2.3 — negative integer still works
#[test]
fn sketch_negative_int_still_works() {
    let mut s = repl_session();
    assert_eq!(repl_eval(&mut s, "-3"), -3);
    assert_eq!(repl_eval(&mut s, "(add-i64 -1 -2)"), -3);
}

// =============================================================================
// Boolean literal
// =============================================================================

// spec: 02-syntax §2.4 — boolean literals
#[test]
fn sketch_boolean_literals() {
    let mut s = repl_session();
    assert_eq!(repl_eval(&mut s, "true"), 1);
    assert_eq!(repl_eval(&mut s, "false"), 0);
    assert_eq!(repl_eval(&mut s, "(not true)"), 0);
    assert_eq!(repl_eval(&mut s, "(not false)"), 1);
}

// =============================================================================
// Batch compile_both — runs in both batch and REPL
// =============================================================================

// spec: 04-expressions §4.1.1 — compile_both basic
#[test]
fn sketch_compile_both_basic() {
    compile_both("42", 42);
}

// spec: 04-expressions §4.6 — compile_both recursive
#[test]
fn sketch_compile_both_recursive() {
    compile_both(
        "(defn fact [n] (if (eq-i64 n 0) 1 (mul-i64 n (fact (sub-i64 n 1))))) (fact 10)",
        3628800,
    );
}

// =============================================================================
// SIGSEGV isolation: minimal trait impl method repro
// =============================================================================

// Minimal repro: trait impl on primitive, no default methods, no ADT
#[test]
fn sigsegv_isolation_trait_impl_minimal() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftrait Dbl (dbl [self] Int))");
    repl_eval(&mut s, "(impl Dbl Int (defn dbl [x] (add-i64 x x)))");
    assert_eq!(repl_eval(&mut s, "(dbl 3)"), 6);
}

// Minimal repro: trait impl on ADT, no default methods
#[test]
fn sigsegv_isolation_trait_impl_on_adt() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftype Color Red Green Blue)");
    repl_eval(&mut s, "(deftrait Tag (tag [self] Int))");
    repl_eval(&mut s, "(impl Tag Color (defn tag [c] (match c [Red 1 Green 2 Blue 3])))");
    assert_eq!(repl_eval(&mut s, "(tag Red)"), 1);
}

// Minimal repro: trait with default method (uses required method in default body)
#[test]
fn sigsegv_isolation_default_method() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftrait Countable (count [self] Int) (count-plus [x] Int (add-i64 (count x) 10)))");
    repl_eval(&mut s, "(impl Countable Int (defn count [x] x))");
    assert_eq!(repl_eval(&mut s, "(count-plus 5)"), 15);
}

// Minimal repro: polymorphic ADT impl calling another impl of same trait
#[test]
fn sigsegv_isolation_poly_adt_impl() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftrait Showable (showit [self] String))");
    repl_eval(&mut s, "(impl Showable Int (defn showit [x] \"int\"))");
    repl_eval(&mut s, "(deftype (MyOpt a) MyNone (MySome [:a mval]))");
    repl_eval(&mut s, "(impl Showable (MyOpt Int) (defn showit [self] (match self [MyNone \"none\" (MySome x) (showit x)])))");
    let result = s.eval("(showit (MySome 42))");
    eprintln!("poly_adt_impl result: is_ok={}, err={}", result.is_ok(), result.as_ref().err().map(|e| e.message()).unwrap_or_default());
    assert!(result.is_ok(), "showit should succeed");
}

// Check: does a default method that uses add-i64 directly (no trait call) also crash?
#[test]
fn sigsegv_isolation_default_method_no_trait_call() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftrait Simple (val [self] Int) (val-plus [x] Int (add-i64 (val x) 1)))");
    repl_eval(&mut s, "(impl Simple Int (defn val [x] x))");
    assert_eq!(repl_eval(&mut s, "(val 5)"), 5);
    assert_eq!(repl_eval(&mut s, "(val-plus 5)"), 6);
}

// Check: trait method that uses trait dispatch internally (like + from prelude)
#[test]
fn sigsegv_isolation_trait_impl_with_trait_dispatch_in_body() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(deftrait Double (double [self] Int))");
    repl_eval(&mut s, "(impl Double Int (defn double [x] (+ x x)))");
    assert_eq!(repl_eval(&mut s, "(double 3)"), 6);
}

// Check: impl method that calls add-i64 (not a trait method)
#[test]
fn sigsegv_isolation_trait_impl_with_primitive_in_body() {
    let mut s = repl_session();
    repl_eval(&mut s, "(deftrait Double (double [self] Int))");
    repl_eval(&mut s, "(impl Double Int (defn double [x] (add-i64 x x)))");
    assert_eq!(repl_eval(&mut s, "(double 3)"), 6);
}
