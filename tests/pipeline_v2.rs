// Pipeline v2 comparison tests: run programs through both v1 and v2 pipelines
// and assert identical results. Validates pipeline convergence before switchover.
//
// v1 = compile_and_run_simple (REPL-based, via helpers)
// v2 = compile_unit (unified pipeline entry point)
//
// Both pipelines need primitives imported as bare names. v1 gets this from
// the PREAMBLE_PRIMITIVES fixture. v2 gets it from a manual register_imports
// call on the CompilationSession's TypeChecker.
//
// **Structural difference**: v1 (compile_and_run_simple) evaluates each
// top-level form sequentially through the REPL, so forward references across
// forms are not supported. v2 (compile_unit) processes all forms together
// in a single pass, supporting forward references. Tests must use programs
// that work in both models: definitions before uses, no forward references.
//
// Any difference in results between v1 and v2 is a regression finding.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::*;
use cranelisp::pipeline::CompilationSession;
use cranelisp::pipeline_v2::compile_unit;
use cranelisp_types::{
    CompileContext, CompileMode, ImportNames, ImportSpec, ModuleFullPath,
    ModuleStrategy, Span,
};

// =============================================================================
// v2 helpers
// =============================================================================

/// Create a CompilationSession with primitives imported as bare names,
/// matching the v1 PREAMBLE_PRIMITIVES setup.
fn v2_session_with_primitives() -> CompilationSession {
    let mut session = CompilationSession::new();
    let import_spec = ImportSpec {
        module_path: ModuleFullPath::from("primitives"),
        alias: None,
        names: ImportNames::Glob,
        span: Span::SYNTHETIC,
    };
    session
        .tc
        .register_imports(&[import_spec])
        .expect("failed to import primitives for v2 session");
    session
}

/// Run source through v2 batch pipeline, return the i64 result.
fn compile_v2_batch(src: &str) -> i64 {
    let mut session = v2_session_with_primitives();
    let ctx = CompileContext {
        module: ModuleFullPath::from("user"),
        strategy: ModuleStrategy::Additive,
        compile_mode: CompileMode::Batch,
        codegen_target: cranelisp_types::CodegenTarget::JitAndCache,
    };
    let result = compile_unit(&mut session, src, &ctx)
        .expect("v2 compile_unit failed");
    result.value.expect("v2 produced no value")
}

/// Run source through v2 interactive pipeline, return the i64 result.
fn compile_v2_interactive(src: &str) -> i64 {
    let mut session = v2_session_with_primitives();
    let ctx = CompileContext {
        module: ModuleFullPath::from("user"),
        strategy: ModuleStrategy::Additive,
        compile_mode: CompileMode::Interactive,
        codegen_target: cranelisp_types::CodegenTarget::JitAndCache,
    };
    let result = compile_unit(&mut session, src, &ctx)
        .expect("v2 compile_unit failed");
    result.value.expect("v2 produced no value")
}

/// Run a program through both v1 and v2 and assert identical i64 results.
///
/// v1 uses compile_and_run_simple (REPL-based pipeline with primitives preamble).
/// v2 uses compile_unit in Batch mode with primitives imported.
fn compare_pipelines(src: &str, expected: i64) {
    let v1_result = compile_and_run_simple(src);
    let v2_result = compile_v2_batch(src);
    assert_eq!(
        v1_result, expected,
        "v1 returned {v1_result}, expected {expected}"
    );
    assert_eq!(
        v2_result, expected,
        "v2 returned {v2_result}, expected {expected}"
    );
    assert_eq!(
        v1_result, v2_result,
        "PIPELINE DIVERGENCE: v1={v1_result}, v2={v2_result}"
    );
}

// =============================================================================
// 1. Core: integer arithmetic (spec: appendix-a-builtins §A.3)
// =============================================================================

// spec: 04-expressions §4.1.1 — integer literal return
#[test]
fn v2_compare_integer_literal() {
    compare_pipelines("(defn main [] 42)", 42);
}

// spec: appendix-a-builtins §A.3 — add-i64 primitive
#[test]
fn v2_compare_add_i64() {
    compare_pipelines("(defn main [] (add-i64 1 2))", 3);
}

// spec: appendix-a-builtins §A.3 — sub-i64 primitive
#[test]
fn v2_compare_sub_i64() {
    compare_pipelines("(defn main [] (sub-i64 10 3))", 7);
}

// spec: appendix-a-builtins §A.3 — mul-i64 primitive
#[test]
fn v2_compare_mul_i64() {
    compare_pipelines("(defn main [] (mul-i64 6 7))", 42);
}

// spec: appendix-a-builtins §A.3 — div-i64 primitive
#[test]
fn v2_compare_div_i64() {
    compare_pipelines("(defn main [] (div-i64 20 4))", 5);
}

// spec: 04-expressions §4.1.1 — negative integer literal
#[test]
fn v2_compare_negative_integer() {
    compare_pipelines("(defn main [] -7)", -7);
}

// spec: 04-expressions §4.1.1 — zero
#[test]
fn v2_compare_zero() {
    compare_pipelines("(defn main [] 0)", 0);
}

// =============================================================================
// 2. Core: let binding (spec: 04-expressions §4.3)
// =============================================================================

// spec: 04-expressions §4.3 — let binding with simple value
#[test]
fn v2_compare_let_binding() {
    compare_pipelines("(defn main [] (let [x 5] (add-i64 x 1)))", 6);
}

// spec: 04-expressions §4.3 — nested let bindings
#[test]
fn v2_compare_nested_let() {
    compare_pipelines(
        "(defn main [] (let [x 3] (let [y 4] (add-i64 x y))))",
        7,
    );
}

// spec: 04-expressions §4.3 — let with multiple bindings
#[test]
fn v2_compare_let_multiple_bindings() {
    compare_pipelines(
        "(defn main [] (let [a 10 b 20] (add-i64 a b)))",
        30,
    );
}

// spec: 04-expressions §4.3 — shadowing in let
#[test]
fn v2_compare_let_shadowing() {
    compare_pipelines(
        "(defn main [] (let [x 1] (let [x 2] x)))",
        2,
    );
}

// =============================================================================
// 3. Core: if expression (spec: 04-expressions §4.4)
// =============================================================================

// spec: 04-expressions §4.4 — if true branch
#[test]
fn v2_compare_if_true() {
    compare_pipelines("(defn main [] (if true 1 2))", 1);
}

// spec: 04-expressions §4.4 — if false branch
#[test]
fn v2_compare_if_false() {
    compare_pipelines("(defn main [] (if false 1 2))", 2);
}

// spec: 04-expressions §4.4 — if with comparison
#[test]
fn v2_compare_if_with_comparison() {
    compare_pipelines("(defn main [] (if (eq-i64 3 3) 100 200))", 100);
}

// spec: 04-expressions §4.4 — nested if
#[test]
fn v2_compare_nested_if() {
    compare_pipelines(
        "(defn main [] (if true (if false 1 2) 3))",
        2,
    );
}

// =============================================================================
// 4. Core: function calls (spec: 04-expressions §4.6)
// =============================================================================

// spec: 04-expressions §4.6 — function application (callee before caller)
#[test]
fn v2_compare_function_call() {
    compare_pipelines(
        "(defn double [x] (add-i64 x x)) (defn main [] (double 21))",
        42,
    );
}

// spec: 04-expressions §4.6 — multi-argument function
#[test]
fn v2_compare_multi_arg_function() {
    compare_pipelines(
        "(defn add3 [a b c] (add-i64 a (add-i64 b c))) (defn main [] (add3 1 2 3))",
        6,
    );
}

// spec: 04-expressions §4.6 — recursive function (factorial)
#[test]
fn v2_compare_factorial() {
    let src = "
        (defn fact [n]
          (if (eq-i64 n 0)
            1
            (mul-i64 n (fact (sub-i64 n 1)))))
        (defn main [] (fact 10))
    ";
    compare_pipelines(src, 3628800);
}

// spec: 04-expressions §4.6 — fibonacci (double recursion)
#[test]
fn v2_compare_fibonacci() {
    let src = "
        (defn fib [n]
          (if (eq-i64 n 0) 0
            (if (eq-i64 n 1) 1
              (add-i64 (fib (sub-i64 n 1)) (fib (sub-i64 n 2))))))
        (defn main [] (fib 10))
    ";
    compare_pipelines(src, 55);
}

// spec: 04-expressions §4.6 — deeply nested function calls
#[test]
fn v2_compare_deeply_nested_calls() {
    compare_pipelines(
        "(defn f [x] (add-i64 x 1)) (defn main [] (f (f (f (f 0)))))",
        4,
    );
}

// =============================================================================
// 5. Core: boolean primitives (spec: appendix-a-builtins §A.3)
// =============================================================================

// spec: 04-expressions §4.1.2 — boolean true
#[test]
fn v2_compare_bool_true() {
    compare_pipelines("(defn main [] (if true 1 0))", 1);
}

// spec: appendix-a-builtins §A.3 — not primitive
#[test]
fn v2_compare_not() {
    compare_pipelines("(defn main [] (if (not false) 1 0))", 1);
}

// spec: appendix-a-builtins §A.3 — lt-i64 comparison
#[test]
fn v2_compare_lt_i64() {
    compare_pipelines("(defn main [] (if (lt-i64 3 5) 1 0))", 1);
}

// spec: appendix-a-builtins §A.3 — gt-i64 comparison
#[test]
fn v2_compare_gt_i64() {
    compare_pipelines("(defn main [] (if (gt-i64 5 3) 1 0))", 1);
}

// spec: appendix-a-builtins §A.3 — le-i64 comparison
#[test]
fn v2_compare_le_i64() {
    compare_pipelines("(defn main [] (if (le-i64 3 3) 1 0))", 1);
}

// spec: appendix-a-builtins §A.3 — ge-i64 comparison
#[test]
fn v2_compare_ge_i64() {
    compare_pipelines("(defn main [] (if (ge-i64 5 5) 1 0))", 1);
}

// =============================================================================
// 6. Core: float arithmetic (spec: appendix-a-builtins §A.3)
// =============================================================================

// spec: appendix-a-builtins §A.3 — Float arithmetic returns correct bit pattern
#[test]
fn v2_compare_float_add() {
    // Float results are stored as i64 bit patterns, so we compare the raw values.
    let src = "(defn main [] (add-f64 1.5 2.5))";
    let v1 = compile_and_run_simple(src);
    let v2 = compile_v2_batch(src);
    assert_eq!(v1, v2, "PIPELINE DIVERGENCE for float add: v1={v1}, v2={v2}");
    let f = f64::from_bits(v2 as u64);
    assert!((f - 4.0).abs() < f64::EPSILON, "expected 4.0, got {f}");
}

// spec: appendix-a-builtins §A.3 — Float subtraction
#[test]
fn v2_compare_float_sub() {
    let src = "(defn main [] (sub-f64 10.0 3.5))";
    let v1 = compile_and_run_simple(src);
    let v2 = compile_v2_batch(src);
    assert_eq!(v1, v2, "PIPELINE DIVERGENCE for float sub: v1={v1}, v2={v2}");
}

// =============================================================================
// 7. Types: closures (spec: 04-expressions §4.7)
// =============================================================================

// spec: 04-expressions §4.7 — lambda expression
#[test]
fn v2_compare_closure_basic() {
    compare_pipelines(
        "(defn main [] (let [f (fn [x] (add-i64 x 1))] (f 5)))",
        6,
    );
}

// spec: 04-expressions §4.7 — closure captures variable
#[test]
fn v2_compare_closure_capture() {
    compare_pipelines(
        "(defn main [] (let [y 10] (let [f (fn [x] (add-i64 x y))] (f 5))))",
        15,
    );
}

// spec: 04-expressions §4.7 — higher-order function
#[test]
fn v2_compare_higher_order() {
    compare_pipelines(
        "(defn apply-fn [f x] (f x)) (defn main [] (apply-fn (fn [x] (mul-i64 x 2)) 21))",
        42,
    );
}

// spec: 04-expressions §4.7 — closure returns closure
#[test]
fn v2_compare_closure_returning_closure() {
    let src = "
        (defn make-adder [n] (fn [x] (add-i64 x n)))
        (defn main [] ((make-adder 10) 32))
    ";
    compare_pipelines(src, 42);
}

// =============================================================================
// 8. Types: ADTs (spec: 06-types §6.3)
// =============================================================================

// spec: 06-types §6.3 — enum ADT (nullary constructors)
#[test]
fn v2_compare_adt_enum() {
    let src = "
        (deftype Color Red Green Blue)
        (defn color-code [c]
          (match c [Red 1 Green 2 Blue 3]))
        (defn main [] (color-code Green))
    ";
    compare_pipelines(src, 2);
}

// spec: 06-types §6.3 — product ADT (data constructor)
#[test]
fn v2_compare_adt_product() {
    let src = "
        (deftype Point [:Int x :Int y])
        (defn get-x [p] (match p [(Point x y) x]))
        (defn main [] (get-x (Point 42 99)))
    ";
    compare_pipelines(src, 42);
}

// spec: 06-types §6.3 — sum ADT (Option-like)
#[test]
fn v2_compare_adt_sum() {
    let src = "
        (deftype (Maybe a) Nothing (Just [:a val]))
        (defn unwrap-or [m default]
          (match m
            [(Just v) v
             Nothing default]))
        (defn main [] (unwrap-or (Just 42) 0))
    ";
    compare_pipelines(src, 42);
}

// spec: 06-types §6.3 — match with wildcard
#[test]
fn v2_compare_match_wildcard() {
    let src = "
        (deftype Color Red Green Blue)
        (defn is-red [c]
          (match c [Red 1 _ 0]))
        (defn main [] (add-i64 (is-red Red) (is-red Blue)))
    ";
    compare_pipelines(src, 1);
}

// =============================================================================
// 9. Types: string operations (spec: appendix-a-builtins §A.3)
// =============================================================================

// spec: appendix-a-builtins §A.3 — str-len primitive
#[test]
fn v2_compare_str_len() {
    let src = r#"(defn main [] (str-len "hello"))"#;
    compare_pipelines(src, 5);
}

// spec: appendix-a-builtins §A.3 — str-concat + str-len
#[test]
fn v2_compare_str_concat_len() {
    let src = r#"(defn main [] (str-len (str-concat "hello" " world")))"#;
    compare_pipelines(src, 11);
}

// =============================================================================
// 10. Core: tail call optimization (spec: 12-runtime §12.3)
// =============================================================================

// spec: 12-runtime §12.3 — self-recursive tail call does not overflow
#[test]
fn v2_compare_tco_sum() {
    let src = "
        (defn sum-to [n acc]
          (if (eq-i64 n 0)
            acc
            (sum-to (sub-i64 n 1) (add-i64 acc n))))
        (defn main [] (sum-to 10000 0))
    ";
    compare_pipelines(src, 50005000);
}

// =============================================================================
// 11. Core: polymorphic functions (spec: 05-type-inference §5.3)
// =============================================================================

// spec: 05-type-inference §5.3 — polymorphic identity function
#[test]
fn v2_compare_polymorphic_identity() {
    compare_pipelines(
        "(defn id [x] x) (defn main [] (id 42))",
        42,
    );
}

// spec: 05-type-inference §5.3 — polymorphic const function
#[test]
fn v2_compare_polymorphic_const() {
    compare_pipelines(
        "(defn const-fn [x y] x) (defn main [] (const-fn 42 99))",
        42,
    );
}

// =============================================================================
// 12. Bare expressions: interactive mode (spec: design/arch/pipeline-v2.md §5.5)
//
// These test v2 interactive mode only (v1 comparison not applicable since
// compile_and_run_simple always uses defn main).
// =============================================================================

// spec: design/arch/pipeline-v2.md §5.5 — bare arithmetic expression
#[test]
fn v2_interactive_bare_arithmetic() {
    let result = compile_v2_interactive("(add-i64 1 2)");
    assert_eq!(result, 3);
}

// spec: design/arch/pipeline-v2.md §5.5 — bare if expression
#[test]
fn v2_interactive_bare_if() {
    let result = compile_v2_interactive("(if true 42 0)");
    assert_eq!(result, 42);
}

// spec: design/arch/pipeline-v2.md §5.5 — bare let expression
#[test]
fn v2_interactive_bare_let() {
    let result = compile_v2_interactive("(let [x 10] (add-i64 x 5))");
    assert_eq!(result, 15);
}

// spec: design/arch/pipeline-v2.md §5.5 — bare integer literal
#[test]
fn v2_interactive_bare_literal() {
    let result = compile_v2_interactive("42");
    assert_eq!(result, 42);
}

// =============================================================================
// 13. v2-only: forward references (v2 supports, v1 does not)
//
// These tests verify v2 capabilities that go beyond v1. They do not compare
// pipelines since v1 cannot handle these programs.
// =============================================================================

// spec: 04-expressions §4.6 — forward reference (v2 only, v1 evals per-form)
#[test]
fn v2_forward_reference() {
    let src = "(defn a [x] (b x)) (defn b [x] (add-i64 x 1)) (defn main [] (a 5))";
    let result = compile_v2_batch(src);
    assert_eq!(result, 6);
}

// spec: 04-expressions §4.6 — mutual recursion (v2 only, v1 evals per-form)
#[test]
fn v2_mutual_recursion() {
    let src = "
        (defn is-even [n]
          (if (eq-i64 n 0)
            true
            (is-odd (sub-i64 n 1))))
        (defn is-odd [n]
          (if (eq-i64 n 0)
            false
            (is-even (sub-i64 n 1))))
        (defn main [] (if (is-even 10) 1 0))
    ";
    let result = compile_v2_batch(src);
    assert_eq!(result, 1);
}
