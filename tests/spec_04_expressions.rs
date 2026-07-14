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

use helpers::e2e::{run_through_all_modes, Cranelisp, PreludeVariant};

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

// spec: spec/04-expressions.md §4.3 — depth-3+ let nesting; outer
// bindings remain visible through the body of every inner let.
// (carry: legacy/ring0.rs::let_deeply_nested_3_or_more)
#[test]
fn let_deeply_nested_3_or_more() {
    // Four nested lets; each binding is referenced from the innermost
    // body. Result: 1 + 2 + 4 + 8 = 15. This exercises the depth axis
    // that the existing single/sequential/shadowing carries do not.
    repl_prims(
        "(let [a 1]\n\
           (let [b 2]\n\
             (let [c 4]\n\
               (let [d 8]\n\
                 (add-i64 a (add-i64 b (add-i64 c d)))))))\n",
    )
    .assert_stdout_contains(":primitives/Int 15");
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

// spec: spec/04-expressions.md §4.4 — nested if as a 3-way classification
// ladder. An inner `if` in the false branch of an outer `if` exercises
// both tail-position (the inner if as the body of the outer's else) and
// non-tail composition (multiple ladder calls combined under arithmetic).
// The single-arm `if_true_branch`/`if_false_branch` carries don't cover
// the nested ladder shape that the legacy test asserts.
// (carry: legacy/ring0.rs::nested_if)
#[test]
fn if_nested_three_way_ladder() {
    // classify(n) = -1 if n<0, 0 if n=0, 1 if n>0.
    // Sum classify(-5) + classify(0) + classify(5) = -1 + 0 + 1 = 0.
    repl_prims(
        "(defn classify [n] (if (lt-i64 n 0) (sub-i64 0 1) (if (eq-i64 n 0) 0 1)))
(add-i64 (add-i64 (classify (sub-i64 0 5)) (classify 0)) (classify 5))
",
    )
    .assert_stdout_contains(":primitives/Int 0");
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

// spec: spec/04-expressions.md §4.5.1 — closure capturing two outer let
// bindings. Distinct from `lambda_closure_captures` (single capture from a
// fn-param). Multi-capture exercises the closure environment layout for
// `>=2` captured values.
// (carry: legacy/sketch_port.rs::sketch_closure_multiple_captures)
#[test]
fn lambda_closure_multi_captures() {
    repl_prims(
        "(let [a 1 b 2] ((fn [x] (add-i64 x (add-i64 a b))) 10))\n",
    )
    .assert_stdout_contains(":primitives/Int 13");
}

// spec: spec/04-expressions.md §4.5 — a lambda value bound in `let` and
// invoked via the let-bound name. The first-class-value property of
// lambdas (§4.5: "result is a first-class value that can be ... bound
// with `let`") is exercised end-to-end: the lambda is created, stored in
// a binding, and called via that binding rather than directly.
// (carry: legacy/ring0.rs::lambda_in_let)
#[test]
fn lambda_bound_in_let_and_called() {
    repl_prims("(let [f (fn [x] (mul-i64 x 2))] (f 21))\n")
        .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/04-expressions.md §4.6 — a lambda passed as an argument and
// invoked inside the callee. The §4.5 first-class-value property
// ("can be ... passed as an argument") combined with the §4.6.2 indirect
// call convention. Distinct from `lambda_closure_captures` (which
// returns a closure) and from `multi_sig_arity_dispatch`.
// (carry: legacy/ring0.rs::lambda_passed_to_function)
#[test]
fn lambda_passed_as_argument_invoked_inside_callee() {
    repl_prims(
        "(defn apply-fn [f x] (f x))
(apply-fn (fn [x] (add-i64 x 10)) 32)
",
    )
    .assert_stdout_contains(":primitives/Int 42");
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

// spec: spec/04-expressions.md §4.6.3 — auto-curried partial application
// passed as an argument to a higher-order function. Distinct from
// `defn_auto_curry_call_with_fewer_args` (curry-then-direct-call): here the
// curried result flows through `apply-fn` invocation.
// (carry: legacy/sketch_port.rs::sketch_auto_curry_higher_order)
#[test]
fn auto_curry_passed_to_higher_order_fn() {
    repl_prims(
        "(defn add [x y] (add-i64 x y))\n\
         (defn apply-fn [f x] (f x))\n\
         (apply-fn (add 10) 5)\n",
    )
    .assert_stdout_contains(":primitives/Int 15");
}

// spec: spec/04-expressions.md §4.6.3 — auto-currying: calling a two-param fn
// with fewer args returns a closure; applying the closure completes the call.
// (carry: legacy/io.rs::auto_curry_two_param_partial_apply)
#[test]
fn auto_curry_two_param_partial_apply() {
    repl_prims(
        "(defn add [x y] (add-i64 x y))\n\
         (let [f (add 1)] (f 2))\n",
    )
    .assert_stdout_contains(":primitives/Int 3");
}

// spec: spec/04-expressions.md §4.6.3 — auto-currying: a three-param fn applied
// to two args returns a one-arg closure.
// (carry: legacy/io.rs::auto_curry_three_param_partial_apply)
#[test]
fn auto_curry_three_param_partial_apply() {
    repl_prims(
        "(defn add3 [x y z] (add-i64 (add-i64 x y) z))\n\
         (let [f (add3 10 20)] (f 30))\n",
    )
    .assert_stdout_contains(":primitives/Int 60");
}

// spec: spec/04-expressions.md §4.6 — supplying MORE args than a fn's arity is
// still an error (auto-curry only handles fewer args).
// (carry: legacy/io.rs::auto_curry_too_many_args_error)
#[test]
fn auto_curry_too_many_args_error_neg() {
    let out = repl_prims(
        "(defn add [x y] (add-i64 x y))\n\
         (add 1 2 3)\n",
    );
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "too many args MUST be an error per §4.6; got:\n{}",
        out.stdout
    );
}

// spec: spec/04-expressions.md §4.6.3 — auto-curry checks argument types: a
// wrong-typed argument is rejected even at partial application.
// (carry: legacy/io.rs::auto_curry_wrong_type_error)
#[test]
fn auto_curry_wrong_type_error_neg() {
    let out = repl_prims(
        "(defn add [x y] (add-i64 x y))\n\
         (add true)\n",
    );
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "wrong-typed arg MUST be an error per §4.6.3; got:\n{}",
        out.stdout
    );
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
// spec: spec/03-types.md §3.11.1 — `[]` is `(Vec a)`; under the tightened
// full-concreteness verdict the unpinned element type at a codegen-reaching
// position is a type error. The source MUST pin it with the directed remedy
// `:(Vec Int) []` (the worked example of §3.11.1, "Fix by annotating the
// literal concrete"). With the annotation the program type-checks and runs.
#[test]
fn vec_literal_empty() {
    repl_prims("(vec-len :(Vec Int) [])\n").assert_stdout_contains(":primitives/Int 0");
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

// =============================================================================
// Wave 5.6 ring1.rs GAP-COVER carry-forwards (chunks 1-3)
// =============================================================================

// spec: spec/04-expressions.md §4.4 — `if` returning a heap-typed (String)
// result. Both branches return String constants; `str-len` consumes the
// unified result. Distinct from the int-branch `if_*_branch` carries (Int
// result), `if_neg_branch_type_mismatch` (negative — Int vs String), and
// from `string_concat_chained` (which exercises chained str-concat without
// `if`). The heap-typed positive-result if-unification shape is unique.
// (carry: legacy/ring1.rs::string_in_if_branches)
#[test]
fn if_branches_heap_typed_string_result() {
    repl_prims("(str-len (if true \"hello\" \"hi\"))\n")
        .assert_stdout_contains(":primitives/Int 5");
}

// spec: spec/04-expressions.md §4.6 — HOF that invokes its fn-typed
// parameter twice: `(apply-twice f x) → (f (f x))`. Distinct from
// `lambda_passed_as_argument_invoked_inside_callee` (single application).
// The double-call shape exercises closure-as-value invariance under
// repeat invocation — no per-call cleanup in the HOF body must drop or
// shadow the captured value.
// (carry: legacy/ring1.rs::closure_apply_twice)
#[test]
fn lambda_passed_as_argument_invoked_twice_inside_callee() {
    repl_prims(
        "(defn apply-twice [f x] (f (f x)))\n\
         (apply-twice (fn [x] (add-i64 x 1)) 0)\n",
    )
    .assert_stdout_contains(":primitives/Int 2");
}

// spec: spec/04-expressions.md §4.5.1 — function composition
// `(compose f g) → (fn [x] (f (g x)))` returns a closure that captures
// **two fn-typed values**. Distinct from `lambda_closure_captures` (Int
// capture) and the single-fn HOF tests; the multi-fn-typed-capture
// angle is uncovered elsewhere.
// (carry: legacy/ring1.rs::closure_compose)
#[test]
fn closure_composition_returns_capturing_two_fn_args() {
    repl_prims(
        "(defn compose [f g] (fn [x] (f (g x))))\n\
         (defn inc [x] (add-i64 x 1))\n\
         (defn double [x] (mul-i64 x 2))\n\
         ((compose inc double) 5)\n",
    )
    .assert_stdout_contains(":primitives/Int 11");
}

// spec: spec/04-expressions.md §4.5 — a named `defn` (not a lambda)
// passed as a fn-typed value to a HOF. The codegen path for
// defn-as-value may differ from lambda-as-value (direct code-pointer
// vs closure trampoline), exercising a distinct reification path.
// Distinct from `lambda_passed_as_argument_invoked_inside_callee`
// (lambda-as-value).
// (carry: legacy/ring1.rs::named_function_as_value_apply)
#[test]
fn named_defn_passed_as_value_to_higher_order_fn() {
    repl_prims(
        "(defn inc [x] (add-i64 x 1))\n\
         (defn apply-fn [f x] (f x))\n\
         (apply-fn inc 41)\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/04-expressions.md §4.4 — `if` returning a closure value.
// Both branches return closures of the same fn type. Heap-typed-if-result
// for **closure** type — distinct from `if_branches_heap_typed_string_result`
// (String result) and from `if_*_branch` (Int result). Closure-result
// branches exercise closure-pointer unification at the if-result.
// (carry: legacy/ring1.rs::closure_in_if_branch)
#[test]
fn if_branches_heap_typed_closure_result() {
    repl_prims(
        "(let [pick true]\n\
           (let [f (if pick (fn [x] (add-i64 x 1)) (fn [x] (sub-i64 x 1)))]\n\
             (f 10)))\n",
    )
    .assert_stdout_contains(":primitives/Int 11");
}

// spec: spec/04-expressions.md §4.5 — closure-application arity rejection:
// calling a one-arg closure with two arguments. Distinct from
// `defn_multi_clause_arity` (defn arity, positive — dispatches between
// clauses). The "calling closure with too many args" rejection path is
// not isolated.
// (carry: legacy/ring1.rs::error_closure_arity_mismatch)
#[test]
fn lambda_call_with_wrong_arg_count_neg() {
    let out = repl_prims("(let [f (fn [x] x)] (f 1 2))\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.to_lowercase().contains("error")
            || combined.to_lowercase().contains("arity")
            || combined.to_lowercase().contains("arg"),
        "((fn [x] x) 1 2) MUST produce an arity-mismatch diagnostic per \
         §4.5; got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/04-expressions.md §4.5.1 — let-bound capturing closure
// invoked twice with **independent args** (f(1) and f(2), not f(f(x))).
// Distinct from `lambda_passed_as_argument_invoked_twice_inside_callee`
// (f(f(x)) shape) and from `lambda_closure_captures` (single call). The
// capture-invariance-under-independent-calls angle exercises that the
// captured value is not consumed/dropped after the first call.
// (carry: legacy/ring1.rs::let_bound_lambda_with_capture)
#[test]
fn let_bound_capturing_lambda_invoked_with_independent_args() {
    repl_prims(
        "(let [base 100 f (fn [x] (add-i64 base x))]\n\
           (add-i64 (f 1) (f 2)))\n",
    )
    .assert_stdout_contains(":primitives/Int 203");
}

// =============================================================================
// Wave 5.6 ring1.rs GAP-COVER carry-forwards (chunk 4)
// =============================================================================

// spec: spec/04-expressions.md §4.4 — `if` returning a Vec value with
// **different-length** branches (`[1 2 3]` vs `[4 5]`). Distinct from
// `if_branches_heap_typed_string_result` (String result) and from
// `if_branches_heap_typed_closure_result` (closure result). The
// Vec-result-with-different-lengths angle exercises if-branch
// unification of a heap-typed compound where branch instances
// genuinely differ in shape (allocation size, length).
// (carry: legacy/ring1.rs::vec_in_if_branch)
#[test]
fn if_branches_heap_typed_vec_result_different_lengths() {
    repl_prims("(vec-len (if true [1 2 3] [4 5]))\n")
        .assert_stdout_contains(":primitives/Int 3");
}

// spec: spec/04-expressions.md §4.4 — if-branch type-mismatch
// diagnostic MUST name BOTH branch types ("Int" AND "String"). The
// U1.7 Wave 3 strict-naming variant — chunk-4 #22 per the audit, which
// subsumes the Wave-0 #8 (any-of-types form). `if_neg_branch_type_mismatch`
// exists but does not enforce strict naming of both type names.
// (carry: legacy/ring1.rs::error_quality_if_branch_mismatch_names_types,
//  subsumes legacy/ring1.rs::error_if_branch_type_mismatch)
#[test]
fn if_branch_mismatch_names_both_types_strict() {
    let out = repl_prims("(if true \"hello\" 42)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(combined.contains("Int"), "diagnostic MUST name 'Int', got: {combined}");
    assert!(
        combined.contains("String"),
        "diagnostic MUST name 'String', got: {combined}"
    );
}

// spec: spec/04-expressions.md §4.2.1 — undefined-constructor
// diagnostic MUST name the constructor literal "Foo". Distinct from
// chunk-3 `error_undefined_constructor` which asserts any-of-error
// indicators; this is the strict-Foo-naming variant per the U1.7
// Wave 3 error-quality contract.
// (carry: legacy/ring1.rs::error_quality_undefined_constructor_names_it)
#[test]
fn data_constructor_undefined_error_names_constructor_strict() {
    let out = repl_prims("(Foo 1 2)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(combined.contains("Foo"), "diagnostic MUST name 'Foo', got: {combined}");
}

// =============================================================================
// Wave 5.6 file 8 ring2.rs chunk 4 GAP-COVER carry-forwards.
// =============================================================================

// spec: spec/04-expressions.md §4.6.3 — Restriction: a multi-signature
// function name MUST NOT be used as a bare value (without arguments). The
// reference is ambiguous because the compiler cannot determine which
// variant is intended. The `defn_multi_clause_arity` test (existing)
// covers the positive multi-sig dispatch path; this is the negative
// companion that asserts the bare-value rejection. Cross-ref: spec/04
// §4.7 (Multi-Signature Dispatch); spec/05 §5.1.2.
// (carry: legacy/ring2.rs::neg_multi_sig_bare_value_errors)
#[test]
fn multi_sig_fn_used_as_bare_value_rejected_neg() {
    let out = repl_prims(
        "(defn choose ([:Int x] x) ([:Int x :Int y] (add-i64 x y)))\n\
         (let [f choose] (f 1))\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.to_lowercase().contains("error")
            || combined.to_lowercase().contains("ambiguous")
            || combined.to_lowercase().contains("multi"),
        "multi-sig fn used as bare value MUST be rejected per §4.6.3 \
         restriction + §4.7; stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/04-expressions.md §4.6.3 — constrained polymorphic make-adder
// monomorphises for Int at the call site. `(defn make-adder [n] (+ n))`
// uses trait-dispatched `+` auto-curried in its body; calling
// `(make-adder 10)` resolves with `n : Int`, monomorphises, and returns
// a `(Fn [Int] Int)` closure. Distinct from existing
// `auto_curry_passed_to_higher_order_fn` (named-prim path,
// `add-i64`-anchored): this tests the trait-dispatched-operator +
// constrained-polymorphism + auto-curry composition unique to §4.6.3.
// Paired with `make_adder_constrained_auto_curry_monomorphises_for_float`
// to prove monomorphisation at the curry boundary works for both Int
// and Float instantiations.
// Cross-ref: spec/03-types.md §3.6 — constrained polymorphism;
// spec/07-traits.md §7.5.
// (carry: legacy/ring2.rs::constrained_auto_curry_make_adder_int)
#[test]
fn make_adder_constrained_auto_curry_monomorphises_for_int() {
    repl_std(
        "(defn make-adder [n] (+ n))\n\
         ((make-adder 10) 32)\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/04-expressions.md §4.6.3 — constrained polymorphic make-adder
// monomorphises for Float at the call site. Sister of
// `make_adder_constrained_auto_curry_monomorphises_for_int`: together
// they prove per-call-site monomorphisation works at the auto-curry
// boundary for both Int and Float type instantiations of the same
// constrained polymorphic source.
// Cross-ref: spec/03-types.md §3.6.4 — name mangling per concrete type.
// (carry: legacy/ring2.rs::constrained_auto_curry_make_adder_float)
#[test]
fn make_adder_constrained_auto_curry_monomorphises_for_float() {
    repl_std(
        "(defn make-adder [n] (+ n))\n\
         ((make-adder 1.5) 2.5)\n",
    )
    .assert_stdout_contains(":primitives/Float");
}

// spec: spec/04-expressions.md §4.6.3 — auto-currying applies only when
// the callee is a variable reference. Anonymous lambda expressions like
// `((fn [x y] ...) 1)` MUST NOT auto-curry; they MUST be bound to a
// variable first. Asserts the explicit "auto-curry requires a named
// function" error message text — REGRESSION-GUARD because the message
// text is normative diagnostic content (a fix that drops the message
// or replaces it with a vague "type error" would silently regress
// the user-facing error quality).
// (carry: legacy/ring2.rs::auto_curry_lambda_partial_apply)
#[test]
fn auto_curry_on_anonymous_lambda_partial_apply_rejected_neg() {
    let out = repl_prims("((fn [x y] (add-i64 x y)) 1)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.to_lowercase().contains("error"),
        "auto-curry on anonymous lambda MUST produce an error per §4.6.3; \
         stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
    assert!(
        combined.contains("auto-curry requires a named function")
            || combined.to_lowercase().contains("named")
            || combined.to_lowercase().contains("lambda"),
        "diagnostic MUST mention the auto-curry / named-function \
         requirement per §4.6.3 (target text: \"auto-curry requires a \
         named function\"); got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// =============================================================================
// §3.4 Type Schemes — polymorphic-accumulator recursive fold (FIXME 0344)
//
// FAILING-NOT-IGNORED repro (S81 close), free-standing (no stdlib — defines
// its own fold inline per root CLAUDE.md §"Stdlib separation"). A Clojure-style
// `reduce` over a Vec threads a polymorphic accumulator (type `b`) that is
// DISTINCT from the element type (`a`, via `vec-get`). The correct scheme is
// `(Fn [(Fn [b a] b) b (Vec a)] b)`. Inference over-unifies: when a SIBLING
// definition in the same module uses `reduce` at an accumulator type of
// `(Vec a)` (here `(reduce vec-push [] vv)`), `reduce`'s scheme collapses so
// the accumulator becomes `(Vec a)` everywhere — instead of instantiating a
// fresh copy of `reduce`'s generalized scheme at that use site. A later call
// with a NON-`(Vec a)` accumulator then fails:
//   `(reduce add-i64 0 [1 2 3])` → `type mismatch: expected (Vec t…), got Int`.
//
// This is the inlined shape of `stdlib/collections/vec.cl::vec-reduce` (whose
// sibling `vec-flatten` uses `(vec-reduce vec-concat [] vv)`), reduced to the
// minimal trigger: caller + recursive helper + ONE Vec-accumulator sibling use.
//
// Owning skill: /typecheck (over-unification of the accumulator type variable
// in the recursive-helper inference path; the sibling use must instantiate a
// fresh copy of the generalized scheme, not monomorphise it). A tighter UNIT
// repro in cranelisp-typecheck will follow separately from /dev; this is the
// e2e cross-skill record. Flips green when the accumulator var generalizes.
// =============================================================================

// spec: spec/03-types.md §3.4 — a polymorphic accumulator threaded through a
//   recursive fold helper MUST generalize so a sibling Vec-accumulator use
//   does not collapse the scheme; `(reduce add-i64 0 [1 2 3])` MUST infer and
//   return 6. FIXME(/typecheck 0344).
#[test]
fn polymorphic_accumulator_fold_does_not_over_unify() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .file(
            "user.cl",
            "(import [primitives \
                [add-i64 ge-i64 vec-len vec-get vec-push Pure]])\n\
             (defn reduce [f init v] (reduce-loop f init v (vec-len v) 0))\n\
             (defn reduce-loop \
                [f acc v :primitives/Int len :primitives/Int i]\n  \
               (if (ge-i64 i len) acc \
                 (reduce-loop f (f acc (vec-get v i)) v len (add-i64 i 1))))\n\
             ;; sibling use with a (Vec a) accumulator — this is what collapses\n\
             ;; `reduce`'s scheme today.\n\
             (defn collect [vv] (reduce vec-push [] vv))\n\
             (defn main [] (Pure (reduce add-i64 0 [1 2 3])))",
        )
        .run("user.cl")
        .output()
        // CORRECT: `reduce` is polymorphic in its accumulator; the Int-accumulator
        // call sums to 6. Today this FAILS with
        // `type mismatch: expected (primitives/Vec t…), got Int`.
        .assert_exit(6);
}

// =============================================================================
// FIXME 0434 sweep (this sprint) — type-annotation name-position, qualified vs
// bare. verify-on-HEAD: a passing row is a standing [Tested+Neg] guard on the
// qualified type-annotation path; a failing row is a surfaced sibling defect
// handed to /frontend with this minimal repro.
// =============================================================================

// spec: spec/04-expressions.md §4.9 + spec/08-modules.md §8.5 — a type
// annotation written with a QUALIFIED type name (`:primitives/Int`) MUST infer
// the SAME canonical type as the bare form (`:Int`); the qualified form MUST NOT
// be re-rooted (to a phantom `user/primitives/Int`). Both display identically.
#[test]
fn type_annotation_qualified_and_bare_resolve_identically() {
    // Bare control: `:Int 42` annotates the literal as Int → `:primitives/Int 42`.
    repl_prims(":Int 42\n").assert_stdout_contains(":primitives/Int 42");

    // Qualified: `:primitives/Int 42` MUST resolve to the same canonical Int and
    // display identically — NOT re-rooted to `user/primitives/Int`.
    repl_prims(":primitives/Int 42\n")
        .assert_stdout_contains(":primitives/Int 42")
        .assert_stdout_does_not_contain("user/primitives/Int");
}

// =============================================================================
// Sprint 109 — SS-1: §4.5 `fn` is single-arity; the parenthesised multi-arity
// clause form is a compile-time (parse) error. Plan: tests/plan/PLAN.md §S109 §I.
// =============================================================================

// spec: spec/04-expressions.md §4.5 — `(fn ([x] x) ([x y] x))` (the parenthesised
// multi-arity clause form, `defn`-only) is a compile-time PARSE error, in REPL
// and `--run` alike. The rejection already fires; the ERROR-QUALITY facet is the
// RED — the diagnostic MUST name `fn` as single-arity and point the user at
// `defn` (the 0575 `/dev` diagnostic tail), not a generic "expected bracket".
// defect: class=silent-accept locus=crates/cranelisp-frontend (fn multi-arity rejected with a generic parse error, not a single-arity/defn-pointing diagnostic) found=S108 owner=/dev
#[test]
fn fn_multi_arity_clause_form_parse_error_neg() {
    // REPL leg.
    let out = repl_prims("(fn ([x] x) ([x y] x))\n");
    let text = format!("{}\n{}", out.stdout, out.stderr);
    assert!(
        text.contains("error"),
        "the multi-arity `fn` form MUST be rejected; {text}"
    );
    assert!(
        text.contains("single-arity")
            || text.contains("single arity")
            || text.contains("defn"),
        "the error MUST name `fn` as single-arity and point at `defn` (0575); {text}"
    );
    // --run leg — the same rejection, uniform across modes.
    let run = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user("(import [primitives [Pure]])\n(def bad (fn ([x] x) ([x y] x)))\n(defn main [] (Pure 0))\n")
        .output();
    assert!(
        !run.status.success(),
        "the multi-arity `fn` form MUST be rejected under --run too; {}\n{}",
        run.stdout, run.stderr
    );
}

// =============================================================================
// §4.5 [S109] — Written free-type-variable annotation in `fn` param position.
// Plan: tests/plan/PLAN.md §S109 §L.1 (FV-15).
//
// §3.3 (S109) MUST-1: a lowercase identifier appearing free in an annotation is
// implicitly universally quantified, IDENTICALLY to an inference-generated
// variable. Here in `fn` (lambda) param position (§4.5) — the same annotation
// shape as a `defn` param, and it MUST behave identically (per-position
// divergence would be the codepath-duplication smell). MUST-2: never
// `unknown type`.
// =============================================================================

// spec: spec/03-types.md §3.3 — MUST-1 in `fn` param position (§4.5): a bare
// free var `:a` on a lambda parameter quantifies; `((fn [:a x] x) 3)` → 3.
// All-modes value equivalence. The written var is a fresh var — the annotation
// adds NO new generalization boundary (parity with the unannotated
// `let_polymorphism_identity_two_types` twin). Nested facet `:(Box a)` too.
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr (free lowercase annotation var absent from var_map falls to TypeNotFound instead of minting a fresh quantified var) found=S109 owner=/dev
#[test]
fn fn_lambda_param_free_var_annotation() {
    // Neg facet: the lambda with `:a` param must not error `unknown type`.
    let out = repl_prims("((fn [:a x] x) 3)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("unknown type"),
        "a free var `:a` on a `fn` param MUST NOT be an unknown-type error \
         (§3.3 MUST-2, §4.5); got:\n{combined}"
    );
    assert!(
        out.stdout.contains(":primitives/Int 3"),
        "`((fn [:a x] x) 3)` MUST evaluate to 3; got:\n{}",
        out.stdout
    );

    // Nested facet: `:(Box a)` on a lambda param.
    let nested = repl_prims(
        "(deftype (Box a) [:a v])\n\
         ((fn [:(Box a) b] (v b)) (Box 7))\n",
    );
    let ncomb = format!("{}{}", nested.stdout, nested.stderr);
    assert!(
        !ncomb.contains("unknown type"),
        "a free var nested in `:(Box a)` on a `fn` param MUST NOT be an \
         unknown-type error; got:\n{ncomb}"
    );

    // Pos: all-modes value equivalence for the lambda-annotated identity.
    run_through_all_modes(
        "(defn main [] (Pure ((fn [:a x] x) 3)))",
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(3);
}
