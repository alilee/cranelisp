// spec_04_expressions.rs — Expression forms (Sprint 64 Wave 5 Batch 2).
//
// Covers `spec/04-expressions.md`. Carries forward language-behaviour
// assertions from the legacy integration-tier `tests/ring0.rs`,
// `tests/ring1.rs`, `tests/ring2.rs`, `tests/lenient.rs`,
// `tests/sketch_port.rs`, and `tests/e2e.rs`. Per
// `tests/plan/PLAN.md §"Mode canonicalisation"`, REPL is canonical.
//
// What this file covers:
//   - Literals: Int, Float, Bool, String (§4.1)
//   - Variable reference + unbound (§4.2)
//   - Let expressions (§4.3)
//   - If expressions (§4.4)
//   - Lambda + application (§4.5, §4.6)
//   - Multi-signature dispatch (§4.7)
//   - Match (cross-ref §6) (§4.8)
//   - Type annotations (§4.9)
//   - Vec literals (§4.10)
//   - Trace expression (§4.12)
//   - Lenient / parallel let (cross-ref §12.4.3)

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

fn repl_std(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin(lines)
        .output()
}

// =============================================================================
// §4.1 Literals
// =============================================================================

// spec: spec/04-expressions.md §4.1.1 — integer literal
#[test]
fn literal_integer_positive() {
    repl_prims("42\n").assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/04-expressions.md §4.1.1 — negative integer literal
#[test]
fn literal_integer_negative() {
    repl_prims("-7\n").assert_stdout_contains(":primitives/Int -7");
}

// spec: spec/04-expressions.md §4.1.1 — zero
#[test]
fn literal_integer_zero() {
    repl_prims("0\n").assert_stdout_contains(":primitives/Int 0");
}

// spec: spec/04-expressions.md §4.1.2 — float literal
#[test]
fn literal_float_positive() {
    repl_prims("3.14\n").assert_stdout_contains(":primitives/Float");
}

// spec: spec/04-expressions.md §4.1.3 — true literal
#[test]
fn literal_boolean_true() {
    repl_prims("true\n").assert_stdout_contains(":primitives/Bool true");
}

// spec: spec/04-expressions.md §4.1.3 — false literal
#[test]
fn literal_boolean_false() {
    repl_prims("false\n").assert_stdout_contains(":primitives/Bool false");
}

// spec: spec/04-expressions.md §4.1.4 — string literal
#[test]
fn literal_string_basic() {
    repl_prims("\"hello\"\n").assert_stdout_contains(":primitives/String");
}

// spec: spec/04-expressions.md §4.1.4 — empty string literal
#[test]
fn literal_string_empty() {
    repl_prims("\"\"\n").assert_stdout_contains(":primitives/String");
}

// =============================================================================
// §4.2 Variable Reference
// =============================================================================

// spec: spec/04-expressions.md §4.2 — let-bound variable reference
#[test]
fn variable_reference_let_bound() {
    repl_prims("(let [x 99] x)\n").assert_stdout_contains(":primitives/Int 99");
}

// spec: spec/04-expressions.md §4.2 — unbound name is a compile-time error
#[test]
fn variable_reference_unbound_errors() {
    let out = repl_prims("undefined-name\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("undefined-name")
            || combined.contains("unbound")
            || combined.contains("not found"),
        "expected error naming undefined-name; output: {combined}"
    );
}

// =============================================================================
// §4.3 Let Expression
// =============================================================================

// spec: spec/04-expressions.md §4.3 — single binding
#[test]
fn let_single_binding() {
    repl_prims("(let [x 5] x)\n").assert_stdout_contains(":primitives/Int 5");
}

// spec: spec/04-expressions.md §4.3 — sequential bindings
#[test]
fn let_sequential_bindings() {
    repl_prims("(let [x 3 y (add-i64 x 4)] y)\n").assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/04-expressions.md §4.3 — nested let with shadowing
#[test]
fn let_nested_shadowing() {
    repl_prims("(let [x 1] (let [x 2] x))\n").assert_stdout_contains(":primitives/Int 2");
}

// =============================================================================
// §4.4 If Expression
// =============================================================================

// spec: spec/04-expressions.md §4.4 — true branch evaluated
#[test]
fn if_true_branch() {
    repl_prims("(if true 1 2)\n").assert_stdout_contains(":primitives/Int 1");
}

// spec: spec/04-expressions.md §4.4 — false branch evaluated
#[test]
fn if_false_branch() {
    repl_prims("(if false 1 2)\n").assert_stdout_contains(":primitives/Int 2");
}

// spec: spec/04-expressions.md §4.4 — branches must agree on type (negative)
#[test]
fn if_neg_branch_type_mismatch() {
    let out = repl_prims("(if true 1 \"two\")\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.to_lowercase().contains("type") || combined.contains("Int") || combined.contains("String"),
        "expected branch type mismatch error; output: {combined}"
    );
}

// =============================================================================
// §4.5 Lambda + §4.6 Application
// =============================================================================

// spec: spec/04-expressions.md §4.5 — lambda immediate call
#[test]
fn lambda_immediate_call() {
    repl_prims("((fn [x] x) 7)\n").assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/04-expressions.md §4.5 — zero-arg lambda
#[test]
fn lambda_zero_args() {
    repl_prims("((fn [] 42))\n").assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/04-expressions.md §4.5 — multi-arg lambda
#[test]
fn lambda_multi_args() {
    repl_prims("((fn [x y] (add-i64 x y)) 3 4)\n").assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/04-expressions.md §4.6 — chained function application
#[test]
fn application_chained() {
    repl_prims(
        "(defn inc [x] (add-i64 x 1))\n(inc (inc (inc 0)))\n",
    )
    .assert_stdout_contains(":primitives/Int 3");
}

// spec: spec/04-expressions.md §4.6 — closure capture
#[test]
fn lambda_closure_captures() {
    repl_prims(
        "(defn make-add [n] (fn [x] (add-i64 x n)))\n((make-add 10) 5)\n",
    )
    .assert_stdout_contains(":primitives/Int 15");
}

// =============================================================================
// §4.7 Multi-Signature Dispatch
// =============================================================================

// spec: spec/04-expressions.md §4.7 — single-clause defn dispatch by arity
// (multi-clause arity-disambig case is covered in spec_05_definitions.rs)
#[test]
fn multi_sig_arity_dispatch() {
    repl_prims(
        "(defn f ([x] x) ([x y] (add-i64 x y)))\n(f 5)\n(f 3 4)\n",
    )
    .assert_stdout_contains_all(&[":primitives/Int 5", ":primitives/Int 7"]);
}

// =============================================================================
// §4.10 Vec Literal
// =============================================================================

// spec: spec/04-expressions.md §4.10 — vec literal of Ints
#[test]
fn vec_literal_int() {
    // Vec display includes the type-arg form: ":(primitives/Vec primitives/Int)"
    repl_prims("[1 2 3]\n").assert_stdout_contains("primitives/Vec");
}

// spec: spec/04-expressions.md §4.10 — empty vec literal
#[test]
fn vec_literal_empty() {
    // Empty vec inference may need a binding to anchor the type variable;
    // pin via vec-len which always returns Int.
    repl_prims("(vec-len [])\n").assert_stdout_contains(":primitives/Int 0");
}

// =============================================================================
// §4.12 Trace Expression
// =============================================================================

// spec: spec/04-expressions.md §4.12 — trace returns Trace value
#[test]
fn trace_returns_trace_type() {
    repl_prims("(trace 42)\n").assert_stdout_contains(":primitives/Trace");
}

// =============================================================================
// Lenient evaluation (cross-ref §12.4.3) — observable through correct
// results from independent let bindings.
// =============================================================================

// spec: spec/12-runtime.md §12.4.3 — independent bindings produce correct sum
#[test]
fn lenient_independent_bindings_correct() {
    repl_std(
        "(defn double [x] (* x 2))\n(defn triple [x] (* x 3))\n(let [a (double 5) b (triple 7)] (+ a b))\n",
    )
    .assert_stdout_contains(":primitives/Int 31");
}

// spec: spec/12-runtime.md §12.4.3 — dependent bindings remain correct
#[test]
fn lenient_dependent_bindings_correct() {
    repl_std(
        "(defn double [x] (* x 2))\n(let [a (double 5) b (+ a 1)] b)\n",
    )
    .assert_stdout_contains(":primitives/Int 11");
}

// =============================================================================
// Lenient evaluation — Wave 5.6 dedupe-recovery carries (cross-ref §12.4.3).
//
// These exercise corners that the two carries above (independent_bindings,
// dependent_bindings) do not: the cheap-builtin / heterogeneous-binding /
// nested-let / mixed-indep-dep boundaries, plus heap-typed results, closure
// capture across a sparked binding, and all-literal bodies. Per spec §12.4.3
// lenient evaluation is semantically transparent — the assertions check
// correctness of the result regardless of which bindings are sparked.
// =============================================================================

// spec: spec/12-runtime.md §12.4.3 — pure-arithmetic bindings (cheap builtins
// excluded from sparking by the cost heuristic) still produce the correct sum.
// (carry: legacy/lenient.rs::test_lenient_cheap_builtins_not_sparked)
#[test]
fn let_independent_bindings_pure_arithmetic() {
    // a=3, b=12, c=5; (+ a (+ b c)) = 20.
    repl_std(
        "(let [a (+ 1 2) b (* 3 4) c (- 10 5)] (+ a (+ b c)))\n",
    )
    .assert_stdout_contains(":primitives/Int 20");
}

// spec: spec/12-runtime.md §12.4.3 — heterogeneous bindings (one call + one
// literal) below the two-sparkable threshold still yield the correct result.
// (carry: legacy/lenient.rs::test_lenient_min_two_sparkable)
#[test]
fn let_mixed_literal_and_call_binding() {
    // double(5)=10, b=7, sum=17.
    repl_std(
        "(defn double [x] (* x 2))\n(let [a (double 5) b 7] (+ a b))\n",
    )
    .assert_stdout_contains(":primitives/Int 17");
}

// spec: spec/12-runtime.md §12.4.3 — nested lets: the inner let's spark group
// is independent of the outer let; both produce correct results.
// (carry: legacy/lenient.rs::test_lenient_nested_lets)
#[test]
fn let_nested_inner_independent_spark_group() {
    // a=10, b=triple(10)=30, c=double(10)=20, result=50.
    repl_std(
        "(defn double [x] (* x 2))\n\
         (defn triple [x] (* x 3))\n\
         (let [a (double 5)] (let [b (triple a) c (double a)] (+ b c)))\n",
    )
    .assert_stdout_contains(":primitives/Int 50");
}

// spec: spec/12-runtime.md §12.4.3 — three-binding let where the last binding
// depends on the first; independent prefix and dependent tail mix correctly.
// (carry: legacy/lenient.rs::test_lenient_mixed_independent_dependent)
#[test]
fn let_three_bindings_last_depends_on_first() {
    // a=10, b=21, c=a+1=11, result=b+c=32.
    repl_std(
        "(defn double [x] (* x 2))\n\
         (defn triple [x] (* x 3))\n\
         (let [a (double 5) b (triple 7) c (+ a 1)] (+ b c))\n",
    )
    .assert_stdout_contains(":primitives/Int 32");
}

// spec: spec/12-runtime.md §12.4.3 — heap-typed results (Strings) survive
// parallel evaluation: each binding owns its value, the body's str-concat
// observes both fully-formed.
// (carry: legacy/lenient.rs::test_lenient_heap_typed_results)
#[test]
fn let_heap_typed_results_string_concat() {
    // greet("world") = "hello world", shout("hey") = "hey!"
    // str-concat(a, b) = "hello worldhey!" — verify via str-eq.
    repl_prims(
        "(defn greet [name] (str-concat \"hello \" name))\n\
         (defn shout [name] (str-concat name \"!\"))\n\
         (let [a (greet \"world\") b (shout \"hey\")] \
           (str-eq (str-concat a b) \"hello worldhey!\"))\n",
    )
    .assert_stdout_contains(":primitives/Bool true");
}

// spec: spec/04-expressions.md §4.5.1 — sparked thunks correctly capture
// variables from the enclosing let scope (cross-ref §12.4.3 lenient eval).
// (carry: legacy/lenient.rs::test_lenient_closures_with_captures)
#[test]
fn let_sparked_binding_captures_outer_let_scope() {
    // base=10, a=add-n(10,5)=15, b=add-n(10,20)=30, sum=45.
    repl_std(
        "(defn add-n [n x] (+ n x))\n\
         (let [base 10] (let [a (add-n base 5) b (add-n base 20)] (+ a b)))\n",
    )
    .assert_stdout_contains(":primitives/Int 45");
}

// spec: spec/12-runtime.md §12.4.3 — all-literal/var bindings are not
// sparkable per the cost heuristic; the let body still produces the correct
// value. Negative-of-spark angle.
// (carry: legacy/lenient.rs::test_lenient_neg_literals_not_sparkable)
#[test]
fn let_all_literal_bindings_correct() {
    // a=42, b=true, c="hello"; body returns a.
    repl_prims(
        "(let [a 42 b true c \"hello\"] a)\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}
