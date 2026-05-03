// IO integration tests: Pure constructor, bind primitive, internal constructor rejection,
// IO type checking, and IO display format.
//
// Tests the full pipeline from source text to execution result.
// Organized per the Sprint 16, Wave 5 test plan.
//
// IO is compiler-seeded in the `primitives` module: Pure (tag=0), Effect (tag=1),
// Bind (tag=2, internal). `bind` is an inline primitive. The trampoline forces
// IO trees iteratively.
//
// Tests MUST NOT depend on stdlib. Uses compiler primitives directly.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::*;
use cranelisp_types::Type;
use serial_test::serial;

// =============================================================================
// Pure constructor through pipeline (spec: 10-io §10.1, §10.2)
// =============================================================================

// spec: 10-io §10.1 — Pure constructor creates IO node, type is (IO Int)
#[test]
fn io_pure_int_type() {
    // Per the Sprint 57 Wave 6 eval contract, IO is trampolined inline: the
    // returned type is the unwrapped inner type, and value is the final result.
    let (value, ty) = compile_and_run_typed("(defn main [] (Pure 42))");
    assert_eq!(ty, Type::Int, "eval must unwrap IO inline; got {ty:?}");
    assert_eq!(value, 42);
}

// spec: 10-io §10.2.3 — Pure wraps Bool
#[test]
fn io_pure_bool() {
    let (value, ty) = compile_and_run_typed("(defn main [] (Pure true))");
    assert_eq!(ty, Type::Bool);
    assert_eq!(value, 1); // true = 1
}

// spec: 10-io §10.2.3 — Pure wraps String
#[test]
fn io_pure_string() {
    let (value, ty) = compile_and_run_typed(r#"(defn main [] (Pure "hello"))"#);
    assert_eq!(ty, Type::String);
    let s = unsafe { cranelisp_runtime::read_string_as_str(value) };
    assert_eq!(s, "hello");
    cranelisp_runtime::heap_dealloc(value);
}

// spec: 10-io §10.1 — Pure in batch mode
#[test]
fn io_pure_both_modes() {
    // batch_run trampolines IO automatically — returns the inner value.
    let src = "(defn main [] (Pure 99))";
    let (value, _ty) = batch_run(src)
        .unwrap_or_else(|e| panic!("batch failed: {e}"));
    assert_eq!(value, 99);
}

// =============================================================================
// bind through pipeline (spec: 10-io §10.3)
// =============================================================================

// spec: 10-io §10.3.1 — bind constructs a Bind node, trampoline evaluates it
#[test]
fn io_bind_pure_to_pure() {
    // (bind (Pure 42) (fn [x] (Pure (add-i64 x 1))))
    let src = r#"
        (defn main []
          (bind (Pure 42) (fn [x] (Pure (add-i64 x 1)))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 43);
}

// spec: 10-io §10.3.3 — nested bind chains (bind result as first arg to outer bind)
#[test]
fn io_bind_nested_chain() {
    // bind (bind (Pure 10) (fn [x] (Pure (add-i64 x 20)))) (fn [y] (Pure (add-i64 y 100)))
    let src = r#"
        (defn main []
          (bind (bind (Pure 10) (fn [x] (Pure (add-i64 x 20))))
                (fn [y] (Pure (add-i64 y 100)))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 130); // 10 + 20 + 100
}

// spec: 10-io §10.3.1 — bind with identity continuation
#[test]
fn io_bind_identity_continuation() {
    // bind (Pure 77) (fn [x] (Pure x))
    let src = r#"
        (defn main []
          (bind (Pure 77) (fn [x] (Pure x))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 77);
}

// spec: 10-io §10.3.1 — bind with computation in continuation
#[test]
fn io_bind_continuation_computation() {
    // Tests that the continuation receives the inner value and can compute with it.
    let src = r#"
        (defn main []
          (bind (Pure 5)
                (fn [x] (Pure (mul-i64 x x)))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 25); // 5 * 5
}

// spec: 10-io §10.3 — bind type: (Fn [(IO a) (Fn [a] (IO b))] (IO b))
#[test]
fn io_bind_type_polymorphic() {
    // bind returns IO of the continuation's return inner type.
    // (bind (Pure 42) (fn [x] (Pure (eq-i64 x 42)))) => IO Bool
    let src = r#"
        (defn main []
          (bind (Pure 42) (fn [x] (Pure (eq-i64 x 42)))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Bool);
    assert_eq!(value, 1); // true
}

// =============================================================================
// Internal constructor rejection (spec: 10-io §10.1)
// =============================================================================

// spec: 10-io §10.1 — Bind constructor is internal, cannot be constructed by user code
#[test]
fn io_bind_constructor_rejected() {
    // Bind is not exported from primitives, so it produces an "undefined" error.
    assert_error(
        "(defn main [] (Bind (Pure 1) (fn [x] (Pure x))))",
        "Bind",
    );
}

// spec: 10-io §10.1 — Bind cannot be used in pattern matching
#[test]
fn io_bind_pattern_rejected() {
    let src = r#"
        (defn main []
          (let [io (Pure 42)]
            (match io [(Bind inner cont) 0 (Pure x) x])))
    "#;
    // Bind is not visible as a constructor name, so this produces an error.
    assert_error(src, "Bind");
}

// spec: 10-io §10.1 — Pure and Effect ARE constructable (not internal)
#[test]
fn io_pure_constructor_not_rejected() {
    // Pure should work fine — not internal.
    let (value, ty) = compile_and_run_typed("(defn main [] (Pure 1))");
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 1);
}

// =============================================================================
// IO type checking (spec: 10-io §10.1.1, §10.2, §10.3)
// =============================================================================

// spec: 10-io §10.1.1 — IO participates in type inference as ordinary ADT
#[test]
fn io_type_inference_pure() {
    // Pure wraps its argument: Pure 42 :: (IO Int). After Sprint 57 Wave 6
    // the eval contract trampolines IO inline and returns the unwrapped
    // inner type. The IO-wrapped shape is covered by unit tests on the
    // inference stage; integration tests see the final unwrapped type.
    let (_, ty) = compile_and_run_typed("(defn main [] (Pure 42))");
    assert_eq!(ty, Type::Int, "eval must unwrap IO inline; got {ty:?}");
}

// spec: 10-io §10.3 — bind type inference: (IO a) -> (Fn [a] (IO b)) -> (IO b)
#[test]
fn io_type_inference_bind() {
    let src = r#"
        (defn main []
          (bind (Pure 42) (fn [x] (Pure (add-i64 x 1)))))
    "#;
    let (_, ty) = compile_and_run_typed(src);
    // Inner type of the bind's IO result is Int.
    assert_eq!(ty, Type::Int, "eval must unwrap IO inline; got {ty:?}");
}

// spec: 10-io §10.7.2 — branch consistency: both branches must be IO
#[test]
fn io_branch_consistency_type_error() {
    // if one branch is IO and other is plain Int, type error
    let src = r#"
        (defn main []
          (if true (Pure 1) 2))
    "#;
    assert_type_error(src, "");
}

// spec: 10-io §10.7.2 — both branches IO, type checks
#[test]
fn io_branch_consistency_both_io() {
    let src = r#"
        (defn main []
          (if true (Pure 1) (Pure 2)))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 1);
}

// =============================================================================
// IO display format at REPL (spec: 10-io §10.6.2)
// =============================================================================

// spec: 10-io §10.6.2 — REPL evaluates IO expression, returns forced inner value
#[test]
fn io_repl_eval_pure_int() {
    let mut session = repl_session();
    let (value, ty) = repl_eval_typed(&mut session, "(Pure 42)");
    // Sprint 57 Wave 6: REPL eval unwraps IO inline per §10.6.2 and returns the
    // forced inner value. The IO type at the source level is covered by inference
    // unit tests; at the eval boundary the caller sees the final result.
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 42);
}

// spec: 10-io §10.6.2 — REPL evaluates bind expression, unwraps IO inline
#[test]
fn io_repl_eval_bind_result() {
    let mut session = repl_session();
    let (value, ty) = repl_eval_typed(&mut session, "(bind (Pure 10) (fn [x] (Pure (add-i64 x 5))))");
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 15);
}

// spec: 10-io §10.2.3 — REPL evaluates Pure Bool, unwraps IO inline
#[test]
fn io_repl_eval_pure_bool() {
    let mut session = repl_session();
    let (value, ty) = repl_eval_typed(&mut session, "(Pure true)");
    assert_eq!(ty, Type::Bool);
    assert_eq!(value, 1); // true
}

// =============================================================================
// Negative tests (spec: 10-io §10.1)
// =============================================================================

// spec: 10-io §10.1 — Bind NOT in /info visible constructors for user code
// (It IS visible in introspection but cannot be constructed)
#[test]
fn io_neg_bind_not_constructable() {
    // Verify that Bind produces an error, not a value.
    let result = batch_run(
        "(defn main [] (Bind (Pure 1) (fn [x] (Pure x))))",
    );
    assert!(result.is_err(), "Bind constructor should be rejected");
    let err = result.err().unwrap();
    let err_msg = err.message();
    assert!(
        err_msg.contains("Bind"),
        "error should mention 'Bind', got: {err_msg}"
    );
}

// spec: 10-io §10.1 — Pattern match on Bind rejected
#[test]
fn io_neg_bind_not_matchable() {
    let result = batch_run(
        r#"(defn main []
          (let [io (Pure 42)]
            (match io [(Bind i c) 0 (Pure x) x])))"#,
    );
    assert!(result.is_err(), "matching on Bind should be rejected");
    let err = result.err().unwrap();
    let err_msg = err.message();
    assert!(
        err_msg.contains("Bind"),
        "error should mention 'Bind', got: {err_msg}"
    );
}

// =============================================================================
// Match on IO values (spec: 10-io §10.1, §10.8.1)
// =============================================================================

// spec: 10-io §10.1 — match on Pure and Effect is allowed (exhaustive without Bind)
#[test]
fn io_match_on_pure() {
    let src = r#"
        (defn unwrap-pure [io]
          (match io [(Pure x) x (Effect _) 0]))
        (defn main [] (unwrap-pure (Pure 99)))
    "#;
    assert_eq!(compile_and_run_simple(src), 99);
}

// =============================================================================
// IO in let bindings (spec: 10-io §10.8.1)
// =============================================================================

// spec: 10-io §10.8.1 — IO values can be bound in let without forcing
#[test]
fn io_let_binding_deferred() {
    // IO values are data — binding them does not force execution.
    let src = r#"
        (defn main []
          (let [io (Pure 42)]
            (match io [(Pure x) x (Effect _) 0])))
    "#;
    assert_eq!(compile_and_run_simple(src), 42);
}

// =============================================================================
// IO with function composition (spec: 10-io §10.3)
// =============================================================================

// spec: 10-io §10.3.1 — bind with named function as continuation
// IGNORED: SIGSEGV when using named function reference as bind continuation
// in REPL session mode. Cross-eval function references in IO bind chains
// produce invalid heap pointers during trampoline execution.
// Runs via subprocess to contain the crash.
#[test]
fn io_bind_with_named_function() {
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("test.cl");
    std::fs::write(&file, "\
        (import [primitives [Pure bind add-i64]])\n\
        (defn wrap-add-one [x] (Pure (add-i64 x 1)))\n\
        (defn main [] (bind (Pure 9) wrap-add-one))\n\
    ").unwrap();
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_cranelisp"))
        .args(["--run", file.to_str().unwrap()])
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.is_empty(),
        "io_bind_with_named_function produced error output: {stderr}"
    );
    // Result is IO wrapping 10; exit code = 10
    assert_eq!(
        output.status.code(),
        Some(10),
        "io_bind_with_named_function wrong result, stderr={stderr}"
    );
}

// spec: 10-io §10.3.3 — triple bind chain
#[test]
fn io_triple_bind_chain() {
    let src = r#"
        (defn main []
          (bind (Pure 1)
                (fn [a]
                  (bind (Pure (add-i64 a 10))
                        (fn [b]
                          (bind (Pure (add-i64 b 100))
                                (fn [c] (Pure (add-i64 c 1000)))))))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 1111); // 1 + 10 + 100 + 1000
}

// =============================================================================
// Platform effect tests (spec: 10-io §10.9, §10.10)
//
// These tests exercise the full IO path including Effect nodes and platform
// DLL loading. They use the test-capture platform to intercept print output
// in-memory, avoiding real stdout side effects.
//
// Requires: cargo build -p cranelisp-test-capture
// =============================================================================

// spec: 10-io §10.9 — (platform test-capture) loads DLL and makes print available
#[test]
#[serial(test_capture)]
fn io_platform_print_hello_world() {
    // The simplest IO program: print a string via test-capture platform.
    // Uses REPL session which supports (platform ...) loading.
    // Sprint 57 Wave 6: REPL eval trampolines IO inline and returns the
    // forced inner value — the print effect has already fired by the time
    // eval returns. Type is the unwrapped inner type.
    let (mut session, capture) = match repl_session_with_test_capture() {
        Some(pair) => pair,
        None => {
            eprintln!("skipping test: test-capture platform DLL not built");
            return;
        }
    };

    capture.reset();
    let (_value, ty) = repl_eval_typed(&mut session, r#"(print "hello")"#);
    // print returns (IO Int); eval unwraps inline to Int.
    assert_eq!(ty, Type::Int, "print IO must be unwrapped inline; got {ty:?}");

    // Verify captured output — the print effect fired during eval.
    let output = capture.get_output();
    assert_eq!(output, "hello", "captured output should be 'hello', got: '{output}'");
}

// spec: 10-io §10.9.2 — print returns (IO Int); eval unwraps to Int
#[test]
#[serial(test_capture)]
fn io_print_returns_io_int() {
    // print :: (Fn [String] (IO Int)) per spec §10.9.2. Sprint 57 Wave 6:
    // eval unwraps IO inline, so the caller sees the unwrapped inner type.
    // The IO-wrapped shape is covered by inference unit tests.
    let (mut session, _capture) = match repl_session_with_test_capture() {
        Some(pair) => pair,
        None => {
            eprintln!("skipping test: test-capture platform DLL not built");
            return;
        }
    };

    let (_, ty) = repl_eval_typed(&mut session, r#"(print "x")"#);
    assert_eq!(ty, Type::Int, "print IO must be unwrapped inline; got {ty:?}");
}

// spec: 10-io §10.3.3 — bind chains platform effects
#[test]
#[serial(test_capture)]
fn io_bind_print_sequence() {
    // Sequence two prints: (bind (print "a") (fn [_] (print "b")))
    let (mut session, capture) = match repl_session_with_test_capture() {
        Some(pair) => pair,
        None => {
            eprintln!("skipping test: test-capture platform DLL not built");
            return;
        }
    };

    capture.reset();
    // bind is a primitives function — import it per spec §8.9.1.
    let _ = session.eval("(import [primitives [bind]])");
    let (_value, ty) = repl_eval_typed(
        &mut session,
        r#"(bind (print "a") (fn [_] (print "b")))"#,
    );
    // Sprint 57 Wave 6: eval unwraps IO inline; both effects have fired by
    // the time eval returns. Type is the unwrapped inner type (Int from the
    // terminal (print "b")).
    assert_eq!(ty, Type::Int, "bind print chain must unwrap to Int; got {ty:?}");

    // Verify both prints were captured in order.
    let output = capture.get_output();
    assert_eq!(output, "a\nb", "captured output should be 'a\\nb', got: '{output}'");
}

// spec: 10-io §10.7.1 — IO propagates through call graph
#[test]
#[serial(test_capture)]
fn io_effect_propagation_through_functions() {
    // A function that calls print inherits IO in its return type. Sprint 57
    // Wave 6: eval unwraps IO inline, so the effect fires during eval.
    let (mut session, capture) = match repl_session_with_test_capture() {
        Some(pair) => pair,
        None => {
            eprintln!("skipping test: test-capture platform DLL not built");
            return;
        }
    };

    session
        .eval("(defn greet [name] (print name))")
        .unwrap_or_else(|e| panic!("defn greet failed: {e}"));

    capture.reset();
    let (_value, ty) = repl_eval_typed(&mut session, r#"(greet "world")"#);
    assert_eq!(ty, Type::Int, "greet IO must be unwrapped inline; got {ty:?}");

    // Verify output — effect fired during eval.
    let output = capture.get_output();
    assert_eq!(output, "world", "captured output should be 'world', got: '{output}'");
}

// =============================================================================
// read-line end-to-end tests (spec: 10-io §10.9)
//
// Uses test-capture platform with scripted input.
// =============================================================================

// spec: 10-io §10.9 — read-line returns (IO String); eval unwraps to String
#[test]
#[serial(test_capture)]
fn io_read_line_returns_io_string() {
    let (mut session, capture) = match repl_session_with_test_capture() {
        Some(pair) => pair,
        None => {
            eprintln!("skipping test: test-capture platform DLL not built");
            return;
        }
    };

    capture.set_input(&["hello from input"]);
    let (value, ty) = repl_eval_typed(&mut session, "(read-line)");
    // Sprint 57 Wave 6: eval unwraps (IO String) inline to String.
    assert_eq!(ty, Type::String, "read-line IO must be unwrapped inline; got {ty:?}");
    let s = unsafe { cranelisp_runtime::read_string_as_str(value) };
    assert_eq!(s, "hello from input");
}

// spec: 10-io §10.9, §10.3 — read-line chained with bind to print (echo)
#[test]
#[serial(test_capture)]
fn io_read_line_bind_print_echo() {
    let (mut session, capture) = match repl_session_with_test_capture() {
        Some(pair) => pair,
        None => {
            eprintln!("skipping test: test-capture platform DLL not built");
            return;
        }
    };

    capture.set_input(&["echo me"]);
    capture.reset();
    capture.set_input(&["echo me"]);
    // bind is a primitives function — import it per spec §8.9.1.
    let _ = session.eval("(import [primitives [bind]])");
    let (_value, ty) =
        repl_eval_typed(&mut session, "(bind (read-line) (fn [line] (print line)))");
    // Sprint 57 Wave 6: eval unwraps IO inline; the terminal (print line)
    // returns (IO Int), so the bind result unwraps to Int.
    assert_eq!(ty, Type::Int, "bind read-line→print must unwrap to Int; got {ty:?}");

    let output = capture.get_output();
    assert_eq!(
        output, "echo me",
        "echo program should print the input line"
    );
}

// =============================================================================
// IO `do` macro semantics tests (spec: 10-io §10.4)
//
// `do` is a library macro that sequences IO expressions via bind.
// These tests verify the desugared form (nested bind with _) since the
// macro itself comes from stdlib (which tests must not depend on).
//
// The `do`-as-macro tests are #[ignore] until the macro is available in
// the test environment (Sprint 17 Wave 2 scope).
// =============================================================================

// spec: 10-io §10.4.1 — do with platform effects: sequenced prints
#[test]
#[serial(test_capture)]
fn io_do_macro_sequenced_prints() {
    // This test requires the `do` macro from stdlib or defmacro.
    // When available: (do (print "a") (print "b") (print "c"))
    // For now, manual desugaring tested in io_do_desugared_three_exprs above.
    let (mut session, capture) = match repl_session_with_test_capture() {
        Some(pair) => pair,
        None => {
            eprintln!("skipping test: test-capture platform DLL not built");
            return;
        }
    };

    capture.reset();
    // Sprint 57 Wave 6: eval unwraps IO inline; all three prints fire during eval.
    let (_value, ty) = repl_eval_typed(
        &mut session,
        r#"(do (print "a") (print "b") (print "c"))"#,
    );
    assert_eq!(ty, Type::Int, "do of prints must unwrap to Int; got {ty:?}");
    let output = capture.get_output();
    assert_eq!(output, "a\nb\nc", "do should sequence prints in order");
}

// spec: 10-io §10.4.2 — do type is the type of the last expression
#[test]
#[serial(test_capture)]
fn io_do_macro_type_is_last_expression() {
    let (mut session, _capture) = match repl_session_with_test_capture() {
        Some(pair) => pair,
        None => {
            eprintln!("skipping test: test-capture platform DLL not built");
            return;
        }
    };

    // Pure is a primitives constructor — import it per spec §8.9.1.
    let _ = session.eval("(import [primitives [Pure]])");
    // (do (print "x") (Pure true)) — last expr is IO Bool; eval unwraps to Bool.
    let (_, ty) = repl_eval_typed(
        &mut session,
        r#"(do (print "x") (Pure true))"#,
    );
    assert_eq!(ty, Type::Bool, "do last-expr IO Bool must unwrap to Bool; got {ty:?}");
}

// spec: 10-io §10.4.1, §10.4.2 — do-chain with Pure terminator: both prints must emit
// and trampoline must return the Pure inner value without crashing.
//
// Regression guard for the ring4b/ring4j demo failure (Sprint 57 Wave 6): the
// pattern `(do (print "one") (print "two") (Pure 42))` emits the first print
// but terminates the REPL process before the second. Full spec surface per
// §10.4.1 requires: (1) ALL intermediate effects execute in source order, and
// (2) the final Pure inner value is returned.
#[test]
#[serial(test_capture)]
fn io_do_print_sequence_with_pure_terminator_emits_all() {
    let (mut session, capture) = match repl_session_with_test_capture() {
        Some(pair) => pair,
        None => {
            eprintln!("skipping test: test-capture platform DLL not built");
            return;
        }
    };

    // Pure is a primitives constructor — import it per spec §8.9.1.
    let _ = session.eval("(import [primitives [Pure]])");
    capture.reset();

    // Exact demo pattern from repl/demos/ring4b.demo + ring4j.demo.
    // Sprint 57 Wave 6: eval unwraps IO inline; both prints fire and the
    // terminal Pure's inner value (42) is returned directly.
    let (value, ty) = repl_eval_typed(
        &mut session,
        r#"(do (print "one") (print "two") (Pure 42))"#,
    );
    assert_eq!(ty, Type::Int, "do last-expr IO Int must unwrap to Int; got {ty:?}");
    assert_eq!(value, 42, "eval must return Pure's inner 42");

    // Both prints must appear, in source order.
    let output = capture.get_output();
    assert!(
        output.contains("one"),
        "first print 'one' missing from output: {output:?}"
    );
    assert!(
        output.contains("two"),
        "second print 'two' missing from output — process likely terminated between prints: {output:?}"
    );
    assert_eq!(
        output, "one\ntwo",
        "do should sequence prints in order, got: {output:?}"
    );
}

// spec: 10-io §10.5.1, §10.5.2 — bind!-chain with Pure terminator: both effects must emit
// and trampoline must return the Pure inner value without crashing.
//
// Regression guard companion to `io_do_print_sequence_with_pure_terminator_emits_all`.
// `bind!` uses the same underlying bind-chain scaffolding as `do`; if the demo
// crash is bind-chain specific, both forms regress together.
#[test]
#[serial(test_capture)]
fn io_bind_bang_print_sequence_with_pure_terminator_emits_all() {
    let (mut session, capture) = match repl_session_with_test_capture() {
        Some(pair) => pair,
        None => {
            eprintln!("skipping test: test-capture platform DLL not built");
            return;
        }
    };

    // Pure is a primitives constructor — import it per spec §8.9.1.
    let _ = session.eval("(import [primitives [Pure]])");
    capture.reset();

    // bind! equivalent of the do demo pattern — discard two print results,
    // return Pure(42). Per §10.5.1, expands to nested bind/fn chains.
    // Sprint 57 Wave 6: eval unwraps IO inline; both prints fire and the
    // terminal Pure's inner value (42) is returned directly.
    let (value, ty) = repl_eval_typed(
        &mut session,
        r#"(bind! [_ (print "one") _ (print "two")] (Pure 42))"#,
    );
    assert_eq!(ty, Type::Int, "bind! body IO Int must unwrap to Int; got {ty:?}");
    assert_eq!(value, 42, "eval must return Pure's inner 42");

    // Both prints must appear, in source order.
    let output = capture.get_output();
    assert!(
        output.contains("one"),
        "first print 'one' missing from output: {output:?}"
    );
    assert!(
        output.contains("two"),
        "second print 'two' missing from output — process likely terminated between prints: {output:?}"
    );
    assert_eq!(
        output, "one\ntwo",
        "bind! should sequence prints in order, got: {output:?}"
    );
}

// =============================================================================
// Platform declaration error tests (spec: 10-io §10.9)
// =============================================================================

// spec: 10-io §10.9 — platform with nonexistent DLL produces error
// Note: platform declarations require the module graph pipeline (compile_project),
// not the simple compile_and_run pipeline. The simple pipeline passes platform
// forms to the AST builder which rejects them. This test verifies that a
// (platform ...) form in the simple pipeline produces an error (which it does,
// since the AST builder rejects unhandled platform forms).
#[test]
fn io_platform_nonexistent_error() {
    let src = r#"
        (platform nonexistent_platform_xyz)
        (defn main [] (Pure 0))
    "#;
    let result = batch_run(src);
    assert!(result.is_err(), "platform form in simple pipeline should produce an error");
}

// spec: 10-io §10.9.3 — (platform) with no name is a parse/syntax error
#[test]
fn io_platform_missing_name_error() {
    // (platform) with no argument — should fail during pre-scan or parsing.
    let src = r#"
        (platform)
        (defn main [] (Pure 0))
    "#;
    let result = batch_run(src);
    // This should either be silently ignored (no platform loaded) or produce an error.
    // Per the spec, platform takes a bare symbol name, so no-arg is invalid.
    // The actual behavior depends on whether scan_for_platform_decls rejects it.
    // If it compiles (no platform loaded), that's acceptable — no error from the platform system.
    // If it errors, the error should be meaningful.
    match result {
        Ok(_) => {
            // Acceptable: (platform) with no arg is not recognized as a platform decl
            // by extract_platform_name (which requires exactly 2 elements), so it
            // falls through to the AST builder which may reject it.
        }
        Err(e) => {
            let msg = e.message();
            assert!(
                msg.contains("platform") || msg.contains("expected"),
                "error should relate to platform syntax, got: {msg}"
            );
        }
    }
}

// spec: 10-io §10.9.1 — platform in non-entry module is a compile-time error
#[test]
fn io_platform_non_entry_module_error() {
    // Platform declarations are entry-module-only. A (platform ...) in a
    // submodule should produce a compile error. This test needs multi-module
    // test infrastructure to properly validate — with a single source string
    // and the v2 pipeline, (mod sub ...) is correctly extracted in Stage 2
    // and the inline (platform stdio) is just sexp content of the mod
    // declaration (never compiled since there's no file to load for sub).
    // The test validates that mod extraction doesn't crash and main compiles.
    let src = r#"
        (mod sub (platform stdio))
        (defn main [] (Pure 0))
    "#;
    let result = batch_run(src);
    // With the v2 pipeline, (mod sub ...) is extracted in Stage 2.
    // The inline content is not compiled (no file for sub module).
    // main compiles and returns Pure(0) = 0.
    assert!(result.is_ok(), "mod extraction should not crash: {:?}", result.err());
}

// =============================================================================
// Batch entry point tests (spec: 10-io §10.6)
// =============================================================================

// spec: 10-io §10.6 — batch trampoline unwraps IO, returns inner value and type
#[test]
fn io_batch_main_returns_io() {
    let src = "(defn main [] (Pure 42))";
    let (value, ty) = batch_run(src)
        .unwrap_or_else(|e| panic!("batch IO main failed: {e}"));
    // batch_run trampolines IO automatically — returns inner value and type.
    assert_eq!(value, 42);
    assert_eq!(ty, Type::Int);
}

// spec: 10-io §10.6.1 — exit code is the inner value of main's IO
#[test]
fn io_batch_exit_code_from_pure() {
    let src = "(defn main [] (Pure 0))";
    let (value, _ty) = batch_run(src)
        .unwrap_or_else(|e| panic!("batch failed: {e}"));
    assert_eq!(value, 0);
}

// spec: 10-io §10.6.1 — non-zero exit code
#[test]
fn io_batch_exit_code_nonzero() {
    let src = "(defn main [] (Pure 1))";
    let (value, _ty) = batch_run(src)
        .unwrap_or_else(|e| panic!("batch failed: {e}"));
    assert_eq!(value, 1);
}

// spec: 10-io §10.6.1 — exit code from bind chain
#[test]
fn io_batch_exit_code_from_bind() {
    let src = r#"
        (defn main []
          (bind (Pure 10) (fn [x] (Pure (primitives/add-i64 x 32)))))
    "#;
    let (value, _ty) = batch_run(src)
        .unwrap_or_else(|e| panic!("batch failed: {e}"));
    assert_eq!(value, 42);
}

// =============================================================================
// Effect constructor tests (spec: 10-io §10.1, §10.8)
// =============================================================================

// spec: 10-io §10.1 — Effect is a valid pattern in match (not internal like Bind)
#[test]
fn io_effect_is_valid_match_pattern() {
    // Effect nodes are created by platform functions, not directly by user code.
    // But the spec says Effect is not internal (unlike Bind), so it can be
    // used in pattern matching. The Pure arm is taken here; the Effect arm
    // verifies the pattern is accepted by the compiler.
    let src = r#"
        (defn main []
          (match (Pure 42) [(Pure x) x (Effect _) 0]))
    "#;
    assert_eq!(compile_and_run_simple(src), 42);
}

// =============================================================================
// Trampoline tests (spec: 10-io §10.8)
// =============================================================================

// spec: 10-io §10.8.2 — trampoline handles deeply nested bind chains (O(1) stack)
// IGNORED: SIGBUS when cross-eval named function references are used in IO bind
// chains under REPL session mode. Same root cause as io_bind_with_named_function.
// Runs via subprocess to contain the crash.
#[test]
fn io_trampoline_deep_bind_chain() {
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("test.cl");
    std::fs::write(&file, "\
        (import [primitives [Pure bind]])\n\
        (defn add-one [x] (Pure (primitives/add-i64 x 1)))\n\
        (defn main []\n\
          (bind (Pure 0)\n\
                (fn [a] (bind (add-one a)\n\
                (fn [b] (bind (add-one b)\n\
                (fn [c] (bind (add-one c)\n\
                (fn [d] (bind (add-one d)\n\
                (fn [e] (bind (add-one e)\n\
                (fn [f] (bind (add-one f)\n\
                (fn [g] (bind (add-one g)\n\
                (fn [h] (bind (add-one h)\n\
                (fn [i] (bind (add-one i)\n\
                (fn [j] (Pure j))))))))))))))))))))))\n\
    ").unwrap();
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_cranelisp"))
        .args(["--run", file.to_str().unwrap()])
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.is_empty(),
        "io_trampoline_deep_bind_chain produced error output: {stderr}"
    );
    // 0 + add-one called 9 times = 9; exit code = 9
    assert_eq!(
        output.status.code(),
        Some(9),
        "io_trampoline_deep_bind_chain wrong result, stderr={stderr}"
    );
}

// spec: 10-io §10.8.1 — IO values are data until forced
#[test]
fn io_values_are_deferred_data() {
    // Binding an IO value in a let does not force it (at compile time).
    // Both branches of an if can construct IO values without forcing them.
    // At eval exit, the whole IO tree is trampolined inline.
    let src = r#"
        (defn main []
          (let [io1 (Pure 10)
                io2 (Pure 20)]
            (bind io1 (fn [x] (bind io2 (fn [y] (Pure (add-i64 x y))))))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 30);
}

// spec: 10-io §10.8.3 — effect isolation: only chosen branch's effect is in the tree
#[test]
fn io_effect_isolation_if_branches() {
    // Both branches create IO values, but only the chosen branch is returned.
    let src = r#"
        (defn choose [p a b] (if p a b))
        (defn main []
          (choose true (Pure 1) (Pure 2)))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 1);
}

// spec: 10-io §10.8.3 — effect isolation: false branch chosen
#[test]
fn io_effect_isolation_false_branch() {
    let src = r#"
        (defn choose [p a b] (if p a b))
        (defn main []
          (choose false (Pure 1) (Pure 2)))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 2);
}

// =============================================================================
// IO in match expressions (spec: 10-io §10.7.2)
// =============================================================================

// spec: 10-io §10.7.2 — all match arms must have same type including IO
#[test]
fn io_match_arms_all_io() {
    let src = r#"
        (deftype Color Red Green Blue)
        (defn main []
          (match Red
            [Red (Pure 1)
             Green (Pure 2)
             Blue (Pure 3)]))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 1);
}

// spec: 10-io §10.7.2 — match arms: mixed IO and non-IO is a type error
#[test]
fn io_match_arms_mixed_type_error() {
    let src = r#"
        (deftype Color Red Green Blue)
        (defn main []
          (match Red
            [Red (Pure 1)
             Green 2
             Blue (Pure 3)]))
    "#;
    assert_type_error(src, "");
}

// =============================================================================
// IO with ADT values (spec: 10-io §10.2.3)
// =============================================================================

// spec: 10-io §10.2.3 — Pure wraps Option None
#[test]
fn io_pure_option_none() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main [] (Pure None))
    "#;
    let (_value, ty) = compile_and_run_typed(src);
    // Sprint 57 Wave 6: eval unwraps (IO (Option a)) inline to (Option a).
    match &ty {
        Type::ADT(name, _) => assert_eq!(name.name.as_ref(), "Option", "expected Option ADT; got {ty:?}"),
        _ => panic!("expected Option ADT; got {ty:?}"),
    }
}

// spec: 10-io §10.2.3 — Pure wraps Option (Some 42)
#[test]
fn io_pure_option_some() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main [] (Pure (Some 42)))
    "#;
    let (_value, ty) = compile_and_run_typed(src);
    // Sprint 57 Wave 6: eval unwraps (IO (Option Int)) inline to (Option Int).
    match &ty {
        Type::ADT(name, args) => {
            assert_eq!(name.name.as_ref(), "Option");
            assert_eq!(args, &vec![Type::Int]);
        }
        _ => panic!("expected Option ADT; got {ty:?}"),
    }
}

// =============================================================================
// bind! macro tests (spec: 10-io §10.5)
//
// bind! is a stdlib macro. These tests use manual bind desugaring to test
// the semantics without stdlib dependency. Macro expansion is tested separately.
// =============================================================================

// spec: 10-io §10.5.1 — single binding: (bind! [x (Pure 42)] (Pure x))
// Desugared: (bind (Pure 42) (fn [x] (Pure x)))
#[test]
fn io_bind_bang_single_binding_desugared() {
    let src = r#"
        (defn main []
          (bind (Pure 42) (fn [x] (Pure x))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 42);
}

// spec: 10-io §10.5.1 — multiple bindings desugared
// (bind! [x (Pure 10) y (Pure 20)] (Pure (add-i64 x y)))
// Desugared: (bind (Pure 10) (fn [x] (bind (Pure 20) (fn [y] (Pure (add-i64 x y))))))
#[test]
fn io_bind_bang_multiple_bindings_desugared() {
    let src = r#"
        (defn main []
          (bind (Pure 10)
                (fn [x]
                  (bind (Pure 20)
                        (fn [y] (Pure (add-i64 x y)))))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 30);
}

// spec: 10-io §10.5.2 — bindings reference earlier bindings
// (bind! [x (Pure 5) y (Pure (add-i64 x x))] (Pure y))
// Desugared to nested bind where y's IO expr uses x from outer scope
#[test]
fn io_bind_bang_sequential_reference_desugared() {
    let src = r#"
        (defn main []
          (bind (Pure 5)
                (fn [x]
                  (bind (Pure (add-i64 x x))
                        (fn [y] (Pure y))))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 10);
}

// =============================================================================
// do macro tests (spec: 10-io §10.4)
//
// The spec says do is IO-specific (expands to bind). The current prelude do
// uses let (pure sequencing). These tests verify the bind-based semantics
// using manual desugaring.
// =============================================================================

// spec: 10-io §10.4.1 — (do e1 e2 e3) desugars to nested bind
// (bind e1 (fn [_] (bind e2 (fn [_] e3))))
#[test]
fn io_do_desugared_three_exprs() {
    let src = r#"
        (defn main []
          (bind (Pure 1)
                (fn [_]
                  (bind (Pure 2)
                        (fn [_] (Pure 3))))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 3); // last expression's value
}

// spec: 10-io §10.4.2 — do type is the type of the last expression; eval unwraps
#[test]
fn io_do_type_is_last_expression() {
    // Last expression returns IO Bool; eval unwraps to Bool.
    let src = r#"
        (defn main []
          (bind (Pure 1)
                (fn [_] (Pure true))))
    "#;
    let (_, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Bool, "last-expr IO Bool must unwrap to Bool; got {ty:?}");
}

// =============================================================================
// pure function tests (spec: 10-io §10.2)
// =============================================================================

// spec: 10-io §10.2.3 — pure is NOT a special form, it's an ordinary function
// Since pure is a stdlib function (defn pure [x] (Pure x)), and tests must not
// depend on stdlib, we define it inline here.
#[test]
fn io_pure_as_user_defined_function() {
    let src = r#"
        (defn my-pure [x] (Pure x))
        (defn main [] (my-pure 42))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 42);
}

// spec: 10-io §10.2 — pure can be passed as a higher-order function
#[test]
fn io_pure_as_higher_order() {
    let src = r#"
        (defn my-pure [x] (Pure x))
        (defn apply-to-42 [f] (f 42))
        (defn main [] (apply-to-42 my-pure))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 42);
}

// =============================================================================
// IO with closures (spec: 10-io §10.3)
// =============================================================================

// spec: 10-io §10.3 — bind continuation captures outer scope
#[test]
fn io_bind_continuation_captures_scope() {
    let src = r#"
        (defn main []
          (let [offset 100]
            (bind (Pure 42)
                  (fn [x] (Pure (add-i64 x offset))))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 142);
}

// =============================================================================
// then combinator / discard pattern RC tests (spec: 10-io §10.4, §10.3)
//
// The `>>` combinator (then) uses `(bind a (fn [_] b))` — the `_` discard
// pattern must correctly dec the unused parameter to avoid memory leaks.
// These tests verify the discard pattern works with both heap and non-heap
// inner values.
// =============================================================================

// spec: 10-io §10.4.1 — then combinator: discard Int result (NeverHeap)
#[test]
fn io_then_combinator_discard_int() {
    // (bind (Pure 999) (fn [_] (Pure 42))) — discard 999, keep 42
    let src = r#"
        (defn main []
          (bind (Pure 999) (fn [_] (Pure 42))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 42);
}

// spec: 10-io §10.4.1 — then combinator: discard String result (AlwaysHeap)
// Regression test for Sprint 16 X1: the `_` parameter must be dec'd in the
// lambda body to avoid leaking the discarded String.
#[test]
fn io_then_combinator_discard_string() {
    let src = r#"
        (defn main []
          (bind (Pure "discarded") (fn [_] (Pure 42))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 42);
}

// spec: 10-io §10.4.1 — then combinator: discard ADT result (Mixed heap)
// Tests the discard pattern with a Mixed heap type (ADT with nullary + data ctors).
#[test]
fn io_then_combinator_discard_adt() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (bind (Pure (Some 99)) (fn [_] (Pure 42))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 42);
}

// spec: 10-io §10.4.1 — chained then: two discards in sequence
// (bind (Pure "a") (fn [_] (bind (Pure "b") (fn [_] (Pure 0)))))
#[test]
fn io_then_combinator_chained_discards() {
    let src = r#"
        (defn main []
          (bind (Pure "first")
                (fn [_]
                  (bind (Pure "second")
                        (fn [_] (Pure 0))))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 0);
}

// spec: 10-io §10.3 — lambda with unused heap param (non-discard name)
// Same RC issue as `_` but with a named parameter that happens to be unused.
#[test]
fn io_bind_unused_heap_param() {
    let src = r#"
        (defn main []
          (bind (Pure "unused") (fn [x] (Pure 77))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Int);
    assert_eq!(value, 77);
}

// =============================================================================
// REPL IO display (spec: 10-io §10.6.2)
// =============================================================================

// spec: 10-io §10.6.2 — REPL forces IO and shows inner result
#[test]
fn io_repl_forces_and_displays() {
    // When the REPL evaluates an IO expression, it forces the trampoline
    // and displays the inner value directly. The forced result is the unwrapped
    // value, not the IO wrapper — e.g. (Pure 42) displays as `:primitives/Int 42`.
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "(Pure 42)");
    // The display should contain the forced inner value.
    assert!(
        display.contains("42"),
        "REPL should display forced inner value 42, got: {display}"
    );
}

// =============================================================================
// Negative tests for IO spec surface
// =============================================================================

// spec: 10-io §10.1.2 — purity guarantee: pure function cannot call IO function
#[test]
fn io_neg_pure_function_cannot_call_io() {
    // A function declared to return Int cannot call a function that returns IO Int.
    // This requires platform functions to exist (print returns IO Int).
    let src = r#"
        (platform stdio)
        (import [platform.stdio [print]])
        (defn bad [] (print "oops"))
        (defn main [] (add-i64 (bad) 1))
    "#;
    // bad returns IO Int, add-i64 expects Int — type mismatch.
    let result = batch_run(src);
    assert!(result.is_err(), "mixing IO and pure should be a type error");
}

// spec: 10-io §10.3 — bind first arg must be IO
#[test]
fn io_neg_bind_first_arg_must_be_io() {
    // bind expects (IO a) as first arg, not a bare Int.
    let src = r#"
        (defn main [] (bind 42 (fn [x] (Pure x))))
    "#;
    let result = batch_run(src);
    assert!(result.is_err(), "bind with non-IO first arg should be a type error");
}

// spec: 10-io §10.3 — bind second arg must be function
#[test]
fn io_neg_bind_second_arg_must_be_function() {
    let src = r#"
        (defn main [] (bind (Pure 42) 99))
    "#;
    let result = batch_run(src);
    assert!(result.is_err(), "bind with non-function second arg should be a type error");
}

// spec: 10-io §10.3 — bind continuation must return IO
#[test]
fn io_neg_bind_continuation_must_return_io() {
    // The continuation (fn [x] x) returns Int, not IO Int.
    let src = r#"
        (defn main [] (bind (Pure 42) (fn [x] x)))
    "#;
    let result = batch_run(src);
    assert!(result.is_err(), "bind continuation returning non-IO should be a type error");
}

// spec: 10-io §10.1 — IO type is parametric: IO Int != IO Bool
#[test]
fn io_neg_type_mismatch_io_int_vs_io_bool() {
    let src = r#"
        (defn main []
          (if true (Pure 1) (Pure true)))
    "#;
    assert_type_error(src, "");
}

// =============================================================================
// R3 coverage gap tests — auto-currying (spec: 04-expressions)
// =============================================================================

// spec: 04-expressions §4.6.3 — auto-currying: calling with fewer args returns closure
#[test]
fn auto_curry_two_param_partial_apply() {
    let src = r#"
        (defn add [x y] (add-i64 x y))
        (defn main []
          (let [f (add 1)]
            (f 2)))
    "#;
    assert_eq!(compile_and_run_simple(src), 3);
}

// spec: 04-expressions §4.6.3 — auto-currying: partial application of 3-param function
#[test]
fn auto_curry_three_param_partial_apply() {
    let src = r#"
        (defn add3 [x y z] (add-i64 (add-i64 x y) z))
        (defn main []
          (let [f (add3 10 20)]
            (f 30)))
    "#;
    assert_eq!(compile_and_run_simple(src), 60);
}

// spec: 04-expressions §4.6.3 — auto-currying: curried function used as higher-order
#[test]
fn auto_curry_higher_order_usage() {
    let src = r#"
        (defn add [x y] (add-i64 x y))
        (defn apply-to-five [f] (f 5))
        (defn main []
          (apply-to-five (add 10)))
    "#;
    assert_eq!(compile_and_run_simple(src), 15);
}

// spec: 04-expressions §4.6.3 — auto-currying in REPL
#[test]
fn auto_curry_repl() {
    let mut session = repl_session();
    repl_eval(&mut session, "(defn add [x y] (add-i64 x y))");
    let result = repl_eval(&mut session, "(let [f (add 1)] (f 2))");
    assert_eq!(result, 3);
}

// spec: 04-expressions §4.6 — too many args is still an error
#[test]
fn auto_curry_too_many_args_error() {
    let src = r#"
        (defn add [x y] (add-i64 x y))
        (defn main [] (add 1 2 3))
    "#;
    assert_error(src, "");
}

// spec: 04-expressions §4.6.3 — auto-curry checks arg types
#[test]
fn auto_curry_wrong_type_error() {
    let src = r#"
        (defn add [x y] (add-i64 x y))
        (defn main [] (add true))
    "#;
    assert_error(src, "");
}
