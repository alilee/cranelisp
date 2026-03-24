// Lenient evaluation & auto IO scheduling tests (Sprint 25, Wave 2).
//
// Lenient evaluation: automatic parallelization of independent let bindings.
// Auto IO scheduling: automatic parallelization of commutative bind! effects.
//
// Tests validate spec requirements from:
//   - spec/12-runtime.md §12.4.3 (lenient evaluation)
//   - spec/10-io.md §10.12 (automatic IO scheduling)
//
// Tests MUST NOT depend on stdlib. Uses compiler primitives and test prelude.
//
// Implementation landed in Sprint 25 Wave 2: IVar intrinsics, sparkability
// analysis, lenient eval codegen, Par node emission, bind-chain analysis.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::*;

// =============================================================================
// Lenient Evaluation — Correctness (spec: 12-runtime §12.4.3)
//
// Independent let bindings produce correct results whether parallelized or not.
// =============================================================================

// spec: spec/12-runtime.md §12.4.3 — independent let bindings produce same result
#[test]
fn test_lenient_independent_bindings_same_result() {
    // Two independent function calls in a let block.
    // Result must be correct regardless of evaluation order.
    let mut session = repl_session_with_test_prelude();
    repl_eval(&mut session, "(defn double [x] (* x 2))");
    repl_eval(&mut session, "(defn triple [x] (* x 3))");
    let result = repl_eval(
        &mut session,
        "(let [a (double 5) b (triple 7)] (+ a b))",
    );
    // double(5) = 10, triple(7) = 21, sum = 31
    assert_eq!(result, 31);
}

// spec: spec/12-runtime.md §12.4.3 — dependent bindings are NOT sparked
#[test]
fn test_lenient_dependent_bindings_sequential() {
    // Binding `b` references binding `a`, so they MUST be sequential.
    // This tests that dependent bindings still produce correct results.
    let mut session = repl_session_with_test_prelude();
    repl_eval(&mut session, "(defn double [x] (* x 2))");
    let result = repl_eval(
        &mut session,
        "(let [a (double 5) b (+ a 1)] b)",
    );
    // double(5) = 10, a + 1 = 11
    assert_eq!(result, 11);
}

// spec: spec/12-runtime.md §12.4.3 — cheap builtins excluded from sparking
#[test]
fn test_lenient_cheap_builtins_not_sparked() {
    // All bindings are cheap arithmetic — no sparking should occur.
    // Verify correct result (no crash, no overhead).
    let mut session = repl_session_with_test_prelude();
    let result = repl_eval(
        &mut session,
        "(let [a (+ 1 2) b (* 3 4) c (- 10 5)] (+ a (+ b c)))",
    );
    // a=3, b=12, c=5, result=20
    assert_eq!(result, 20);
}

// spec: spec/12-runtime.md §12.4.3 — at least 2 sparkable bindings required
#[test]
fn test_lenient_min_two_sparkable() {
    // Only one function call binding plus one literal — no sparking.
    // Verify correct result.
    let mut session = repl_session_with_test_prelude();
    repl_eval(&mut session, "(defn double [x] (* x 2))");
    let result = repl_eval(
        &mut session,
        "(let [a (double 5) b 7] (+ a b))",
    );
    // double(5)=10, b=7, result=17
    assert_eq!(result, 17);
}

// spec: spec/12-runtime.md §12.4.3 — CRANELISP_NO_LENIENT=1 disables sparking
#[test]
fn test_lenient_no_lenient_env_var() {
    // With CRANELISP_NO_LENIENT=1 set, independent bindings should still
    // produce the correct result (just sequentially).
    // Note: We cannot easily set env vars for the JIT compiler within the
    // test process, so this test verifies the result is correct and relies
    // on the opt-out mechanism being tested via E2E or timing tests.
    let mut session = repl_session_with_test_prelude();
    repl_eval(&mut session, "(defn double [x] (* x 2))");
    repl_eval(&mut session, "(defn triple [x] (* x 3))");
    let result = repl_eval(
        &mut session,
        "(let [a (double 5) b (triple 7)] (+ a b))",
    );
    assert_eq!(result, 31);
}

// spec: spec/12-runtime.md §12.4.3 — nested lets have independent sparkability
#[test]
fn test_lenient_nested_lets() {
    // Inner let block has its own spark group, independent of outer let.
    let mut session = repl_session_with_test_prelude();
    repl_eval(&mut session, "(defn double [x] (* x 2))");
    repl_eval(&mut session, "(defn triple [x] (* x 3))");
    let result = repl_eval(
        &mut session,
        "(let [a (double 5)]
           (let [b (triple a) c (double a)]
             (+ b c)))",
    );
    // a=10, b=triple(10)=30, c=double(10)=20, result=50
    assert_eq!(result, 50);
}

// spec: spec/12-runtime.md §12.4.3 — mixed independent/dependent bindings
#[test]
fn test_lenient_mixed_independent_dependent() {
    // a and b are independent (sparkable), c depends on a (sequential).
    let mut session = repl_session_with_test_prelude();
    repl_eval(&mut session, "(defn double [x] (* x 2))");
    repl_eval(&mut session, "(defn triple [x] (* x 3))");
    let result = repl_eval(
        &mut session,
        "(let [a (double 5) b (triple 7) c (+ a 1)] (+ b c))",
    );
    // a=10, b=21, c=a+1=11, result=b+c=32
    assert_eq!(result, 32);
}

// spec: spec/12-runtime.md §12.4.3 — three independent sparkable bindings
#[test]
fn test_lenient_three_independent_calls() {
    let mut session = repl_session_with_test_prelude();
    repl_eval(&mut session, "(defn double [x] (* x 2))");
    repl_eval(&mut session, "(defn triple [x] (* x 3))");
    repl_eval(&mut session, "(defn square [x] (* x x))");
    let result = repl_eval(
        &mut session,
        "(let [a (double 3) b (triple 4) c (square 5)] (+ a (+ b c)))",
    );
    // a=6, b=12, c=25, result=43
    assert_eq!(result, 43);
}

// spec: spec/12-runtime.md §12.4.3 — heap-typed results survive parallel eval
#[test]
fn test_lenient_heap_typed_results() {
    // String values (heap-typed) must be correct after lenient evaluation.
    let mut session = repl_session_with_test_prelude();
    repl_eval(&mut session, r#"(defn greet [name] (str-concat "hello " name))"#);
    repl_eval(&mut session, r#"(defn shout [name] (str-concat name "!"))"#);
    let result = repl_eval(
        &mut session,
        r#"(let [a (greet "world") b (shout "hey")] (str-concat a b))"#,
    );
    // greet("world") = "hello world", shout("hey") = "hey!"
    // str-concat("hello world", "hey!") = "hello worldhey!"
    let s = unsafe { cranelisp_runtime::read_string_as_str(result) };
    assert_eq!(s, "hello worldhey!");
}

// spec: spec/12-runtime.md §12.4.3 — thunks capture enclosing scope
#[test]
fn test_lenient_closures_with_captures() {
    // Sparked thunks must correctly capture variables from enclosing scope.
    let mut session = repl_session_with_test_prelude();
    repl_eval(&mut session, "(defn add-n [n x] (+ n x))");
    let result = repl_eval(
        &mut session,
        "(let [base 10]
           (let [a (add-n base 5) b (add-n base 20)] (+ a b)))",
    );
    // a = 10+5 = 15, b = 10+20 = 30, result = 45
    assert_eq!(result, 45);
}

// spec: spec/12-runtime.md §12.4.3 — literals not sparkable
#[test]
fn test_lenient_neg_literals_not_sparkable() {
    // Bindings whose expressions are literals or variable references
    // are not sparkable. Verify correct result (no crash).
    let mut session = repl_session_with_test_prelude();
    let result = repl_eval(
        &mut session,
        r#"(let [a 42 b true c "hello"] a)"#,
    );
    assert_eq!(result, 42);
}

// =============================================================================
// Auto IO Scheduling (spec: 10-io §10.12)
//
// Automatic parallelization of commutative, data-independent IO effects.
// These tests require the test-capture platform with commutative functions
// (being added by /platform in Sprint 25 Wave 2).
// =============================================================================

// spec: spec/10-io.md §10.12.1 — commutative + data-independent => Par node
#[test]
fn test_io_schedule_commutative_pair_par() {
    // Two data-independent calls to a Commutative platform function should
    // produce a Par node and run concurrently.
    // Requires: test-capture platform with a Commutative function (e.g., test-sleep-ms).
    let Some((mut session, _capture)) = repl_session_with_test_capture() else {
        eprintln!("test-capture DLL not available, skipping");
        return;
    };
    // TODO: When commutative test functions are available, replace with actual calls.
    // For now, verify the basic bind! chain still works sequentially.
    let result = session.eval(
        r#"(defn main [] (bind! [a (print "one") b (print "two")] (pure 0)))"#,
    );
    assert!(result.is_ok(), "bind! chain should compile: {:?}", result.err());
}

// spec: spec/10-io.md §10.12.2 — Sequential scheduling class preserves order
#[test]
fn test_io_schedule_sequential_no_par() {
    // Two calls to a Sequential platform function (print) remain sequential.
    let Some((mut session, capture)) = repl_session_with_test_capture() else {
        eprintln!("test-capture DLL not available, skipping");
        return;
    };
    capture.reset();
    let result = session.eval(
        r#"(defn main [] (bind! [a (print "first") b (print "second")] (pure 0)))"#,
    );
    assert!(result.is_ok(), "sequential bind! should compile: {:?}", result.err());
    // If we called main and forced IO, output order should be preserved.
    // Full verification requires IO forcing + output capture.
}

// spec: spec/10-io.md §10.12.1 — data-dependent pair: no Par node
#[test]
fn test_io_schedule_data_dependent_no_par() {
    // Two Commutative calls where the second uses the first's binding name.
    // No Par node emitted — data dependency prevents parallelization.
    let Some((mut session, _capture)) = repl_session_with_test_capture() else {
        eprintln!("test-capture DLL not available, skipping");
        return;
    };
    // `b` depends on `a` — must be sequential even if both call the same function.
    // `a` binds the result of print (IO Int), `b` references `a` in its expression.
    let result = session.eval(
        r#"(defn main [] (bind! [a (print "one") b (print (int-to-string a))] (pure 0)))"#,
    );
    // This should compile (sequential execution) without error.
    assert!(result.is_ok(), "data-dependent bind! should compile: {:?}", result.err());
}

// spec: spec/10-io.md §10.12.4 — same resource token serializes
#[test]
fn test_io_schedule_resource_serial_same_token_sequential() {
    // Two ResourceSerial calls with the same non-zero resource token.
    // They are serialized even though they are data-independent.
    // Requires: test-capture platform with ResourceSerial functions.
    //
    // When implemented, verify via timing: two 50ms calls should take ~100ms.
    let Some((_session, _capture)) = repl_session_with_test_capture() else {
        eprintln!("test-capture DLL not available, skipping");
        return;
    };
    // TODO: ResourceSerial test functions not yet available in test-capture platform.
    // When available, write two ResourceSerial calls with matching token and
    // verify sequential timing.
}

// spec: spec/10-io.md §10.12.4 — different resource tokens run concurrently
#[test]
fn test_io_schedule_resource_serial_diff_token_parallel() {
    // Two ResourceSerial calls with different resource tokens.
    // They run concurrently because tokens don't conflict.
    // Requires: test-capture platform with ResourceSerial functions.
    //
    // When implemented, verify via timing: two 50ms calls with different
    // tokens should complete in ~50ms (parallel), not ~100ms.
    let Some((_session, _capture)) = repl_session_with_test_capture() else {
        eprintln!("test-capture DLL not available, skipping");
        return;
    };
    // TODO: ResourceSerial test functions not yet available in test-capture platform.
}
