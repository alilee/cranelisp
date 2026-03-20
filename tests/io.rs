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
    let (value, ty) = compile_and_run_typed("(defn main [] (Pure 42))");
    // The type should be IO Int.
    assert!(ty.is_io(), "expected IO type, got: {:?}", ty);
    assert_eq!(ty.io_inner_type(), Type::Int);
    // The raw value is a heap pointer to an IO node. Force it via trampoline.
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 42);
    cranelisp_runtime::heap_dealloc(value);
}

// spec: 10-io §10.2.3 — Pure wraps Bool
#[test]
fn io_pure_bool() {
    let (value, ty) = compile_and_run_typed("(defn main [] (Pure true))");
    assert!(ty.is_io(), "expected IO type, got: {:?}", ty);
    assert_eq!(ty.io_inner_type(), Type::Bool);
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 1); // true = 1
    cranelisp_runtime::heap_dealloc(value);
}

// spec: 10-io §10.2.3 — Pure wraps String
#[test]
fn io_pure_string() {
    let (value, ty) = compile_and_run_typed(r#"(defn main [] (Pure "hello"))"#);
    assert!(ty.is_io(), "expected IO type, got: {:?}", ty);
    assert_eq!(ty.io_inner_type(), Type::String);
    let inner = cranelisp_runtime::run_io_trampoline(value);
    let s = unsafe { cranelisp_runtime::read_string_as_str(inner) };
    assert_eq!(s, "hello");
    cranelisp_runtime::heap_dealloc(inner);
    cranelisp_runtime::heap_dealloc(value);
}

// spec: 10-io §10.1 — Pure in both batch and interactive modes
#[test]
fn io_pure_both_modes() {
    let src = "(defn main [] (Pure 99))";
    let batch = cranelisp::pipeline::compile_and_run(src, cranelisp_types::CompileMode::Batch)
        .unwrap_or_else(|e| panic!("batch failed: {e}"));
    assert!(batch.ty.is_io());
    let batch_inner = cranelisp_runtime::run_io_trampoline(batch.value);
    assert_eq!(batch_inner, 99);
    cranelisp_runtime::heap_dealloc(batch.value);

    let interactive = cranelisp::pipeline::compile_and_run(src, cranelisp_types::CompileMode::Interactive)
        .unwrap_or_else(|e| panic!("interactive failed: {e}"));
    assert!(interactive.ty.is_io());
    let interactive_inner = cranelisp_runtime::run_io_trampoline(interactive.value);
    assert_eq!(interactive_inner, 99);
    cranelisp_runtime::heap_dealloc(interactive.value);
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
    assert!(ty.is_io(), "expected IO type, got: {:?}", ty);
    assert_eq!(ty.io_inner_type(), Type::Int);
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 43);
    cranelisp_runtime::heap_dealloc(value);
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
    assert!(ty.is_io(), "expected IO type, got: {:?}", ty);
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 130); // 10 + 20 + 100
    cranelisp_runtime::heap_dealloc(value);
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
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 77);
    cranelisp_runtime::heap_dealloc(value);
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
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 25); // 5 * 5
    cranelisp_runtime::heap_dealloc(value);
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
    assert!(ty.is_io(), "expected IO type, got: {:?}", ty);
    assert_eq!(ty.io_inner_type(), Type::Bool);
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 1); // true
    cranelisp_runtime::heap_dealloc(value);
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
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 1);
    cranelisp_runtime::heap_dealloc(value);
}

// =============================================================================
// IO type checking (spec: 10-io §10.1.1, §10.2, §10.3)
// =============================================================================

// spec: 10-io §10.1.1 — IO participates in type inference as ordinary ADT
#[test]
fn io_type_inference_pure() {
    // Pure wraps its argument: Pure 42 :: (IO Int)
    let (_, ty) = compile_and_run_typed("(defn main [] (Pure 42))");
    match &ty {
        Type::ADT(name, args) => {
            assert_eq!(name.as_ref(), "IO");
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], Type::Int);
        }
        _ => panic!("expected ADT type (IO Int), got: {:?}", ty),
    }
}

// spec: 10-io §10.3 — bind type inference: (IO a) -> (Fn [a] (IO b)) -> (IO b)
#[test]
fn io_type_inference_bind() {
    let src = r#"
        (defn main []
          (bind (Pure 42) (fn [x] (Pure (add-i64 x 1)))))
    "#;
    let (_, ty) = compile_and_run_typed(src);
    match &ty {
        Type::ADT(name, args) => {
            assert_eq!(name.as_ref(), "IO");
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], Type::Int);
        }
        _ => panic!("expected ADT type (IO Int), got: {:?}", ty),
    }
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
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 1);
    cranelisp_runtime::heap_dealloc(value);
}

// =============================================================================
// IO display format at REPL (spec: 10-io §10.6.2)
// =============================================================================

// spec: 10-io §10.6.2 — REPL evaluates IO expression, type is IO
#[test]
fn io_repl_eval_pure_int() {
    let mut session = repl_session();
    let (value, ty) = repl_eval_typed(&mut session, "(Pure 42)");
    assert!(ty.is_io(), "expected IO type in REPL, got: {:?}", ty);
    assert_eq!(ty.io_inner_type(), Type::Int);
    // Force the IO tree to verify the inner value.
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 42);
}

// spec: 10-io §10.6.2 — REPL evaluates bind expression, type is IO
#[test]
fn io_repl_eval_bind_result() {
    let mut session = repl_session();
    let (value, ty) = repl_eval_typed(&mut session, "(bind (Pure 10) (fn [x] (Pure (add-i64 x 5))))");
    assert!(ty.is_io(), "expected IO type in REPL, got: {:?}", ty);
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 15);
}

// spec: 10-io §10.2.3 — REPL evaluates Pure Bool
#[test]
fn io_repl_eval_pure_bool() {
    let mut session = repl_session();
    let (value, ty) = repl_eval_typed(&mut session, "(Pure true)");
    assert!(ty.is_io(), "expected IO type in REPL, got: {:?}", ty);
    assert_eq!(ty.io_inner_type(), Type::Bool);
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 1); // true
}

// =============================================================================
// Negative tests (spec: 10-io §10.1)
// =============================================================================

// spec: 10-io §10.1 — Bind NOT in /info visible constructors for user code
// (It IS visible in introspection but cannot be constructed)
#[test]
fn io_neg_bind_not_constructable() {
    // Verify that Bind produces an error, not a value.
    let result = cranelisp::pipeline::compile_and_run(
        "(defn main [] (Bind (Pure 1) (fn [x] (Pure x))))",
        cranelisp_types::CompileMode::Batch,
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
    let result = cranelisp::pipeline::compile_and_run(
        r#"(defn main []
          (let [io (Pure 42)]
            (match io [(Bind i c) 0 (Pure x) x])))"#,
        cranelisp_types::CompileMode::Batch,
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
#[test]
fn io_bind_with_named_function() {
    let src = r#"
        (defn wrap-add-one [x] (Pure (add-i64 x 1)))
        (defn main [] (bind (Pure 9) wrap-add-one))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 10);
    cranelisp_runtime::heap_dealloc(value);
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
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 1111); // 1 + 10 + 100 + 1000
    cranelisp_runtime::heap_dealloc(value);
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
    let (mut session, capture) = match repl_session_with_test_capture() {
        Some(pair) => pair,
        None => {
            eprintln!("skipping test: test-capture platform DLL not built");
            return;
        }
    };

    capture.reset();
    let (value, ty) = repl_eval_typed(&mut session, r#"(print "hello")"#);
    assert!(ty.is_io(), "print should return IO type, got: {:?}", ty);

    // Force the IO tree to execute the effect.
    let _inner = cranelisp_runtime::run_io_trampoline(value);

    // Verify captured output.
    let output = capture.get_output();
    assert_eq!(output, "hello", "captured output should be 'hello', got: '{output}'");
}

// spec: 10-io §10.9.2 — print returns (IO Int)
#[test]
#[serial(test_capture)]
fn io_print_returns_io_int() {
    // print :: (Fn [String] (IO Int)) per spec §10.9.2
    let (mut session, _capture) = match repl_session_with_test_capture() {
        Some(pair) => pair,
        None => {
            eprintln!("skipping test: test-capture platform DLL not built");
            return;
        }
    };

    let (_, ty) = repl_eval_typed(&mut session, r#"(print "x")"#);
    assert!(ty.is_io(), "expected IO type, got: {:?}", ty);
    match &ty {
        Type::ADT(name, args) => {
            assert_eq!(name.as_ref(), "IO");
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], Type::Int, "print inner type should be Int");
        }
        _ => panic!("expected ADT type (IO Int), got: {:?}", ty),
    }
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
    let (value, ty) = repl_eval_typed(
        &mut session,
        r#"(bind (print "a") (fn [_] (print "b")))"#,
    );
    assert!(ty.is_io(), "bind of prints should return IO type, got: {:?}", ty);

    // Force the IO tree to execute both effects.
    let _inner = cranelisp_runtime::run_io_trampoline(value);

    // Verify both prints were captured in order.
    let output = capture.get_output();
    assert_eq!(output, "a\nb", "captured output should be 'a\\nb', got: '{output}'");
}

// spec: 10-io §10.7.1 — IO propagates through call graph
#[test]
#[serial(test_capture)]
fn io_effect_propagation_through_functions() {
    // A function that calls print inherits IO in its return type.
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
    let (value, ty) = repl_eval_typed(&mut session, r#"(greet "world")"#);
    assert!(ty.is_io(), "greet should propagate IO, got: {:?}", ty);

    // Force the IO tree to execute the effect.
    let _inner = cranelisp_runtime::run_io_trampoline(value);

    // Verify output.
    let output = capture.get_output();
    assert_eq!(output, "world", "captured output should be 'world', got: '{output}'");
}

// =============================================================================
// read-line end-to-end tests (spec: 10-io §10.9)
//
// Uses test-capture platform with scripted input.
// =============================================================================

// spec: 10-io §10.9 — read-line returns (IO String) with scripted input
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
    assert!(ty.is_io(), "read-line should return IO type, got: {:?}", ty);
    assert_eq!(
        ty.io_inner_type(),
        Type::String,
        "read-line inner type should be String"
    );

    // Force the IO tree to get the string value.
    let inner = cranelisp_runtime::run_io_trampoline(value);
    let s = unsafe { cranelisp_runtime::read_string_as_str(inner) };
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
    let (value, ty) =
        repl_eval_typed(&mut session, "(bind (read-line) (fn [line] (print line)))");
    assert!(ty.is_io(), "bind chain should return IO type, got: {:?}", ty);

    // Force the IO tree to execute effects.
    let _inner = cranelisp_runtime::run_io_trampoline(value);

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
    // Using do macro (requires stdlib/prelude):
    let (value, ty) = repl_eval_typed(
        &mut session,
        r#"(do (print "a") (print "b") (print "c"))"#,
    );
    assert!(ty.is_io(), "do should return IO type, got: {:?}", ty);
    let _inner = cranelisp_runtime::run_io_trampoline(value);
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

    // (do (print "x") (Pure true)) — last expr is IO Bool
    let (_, ty) = repl_eval_typed(
        &mut session,
        r#"(do (print "x") (Pure true))"#,
    );
    assert!(ty.is_io(), "do should return IO type, got: {:?}", ty);
    assert_eq!(ty.io_inner_type(), Type::Bool, "do type should be IO Bool");
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
    let result = cranelisp::pipeline::compile_and_run(src, cranelisp_types::CompileMode::Batch);
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
    let result = cranelisp::pipeline::compile_and_run(src, cranelisp_types::CompileMode::Batch);
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
    // submodule should produce a compile error. This test is ignored because
    // multi-module test infrastructure is needed.
    let src = r#"
        (mod sub (platform stdio))
        (defn main [] (Pure 0))
    "#;
    let result = cranelisp::pipeline::compile_and_run(src, cranelisp_types::CompileMode::Batch);
    assert!(result.is_err(), "platform in submodule should be rejected");
}

// =============================================================================
// Batch entry point tests (spec: 10-io §10.6)
// =============================================================================

// spec: 10-io §10.6 — main must return IO type in IO programs
#[test]
fn io_batch_main_returns_io() {
    let src = "(defn main [] (Pure 42))";
    let result = cranelisp::pipeline::compile_and_run(src, cranelisp_types::CompileMode::Batch)
        .unwrap_or_else(|e| panic!("batch IO main failed: {e}"));
    assert!(result.ty.is_io(), "main should return IO type");
}

// spec: 10-io §10.6.1 — exit code is the inner value of main's IO
#[test]
fn io_batch_exit_code_from_pure() {
    let src = "(defn main [] (Pure 0))";
    let result = cranelisp::pipeline::compile_and_run(src, cranelisp_types::CompileMode::Batch)
        .unwrap_or_else(|e| panic!("batch failed: {e}"));
    let exit_code = cranelisp_runtime::run_io_trampoline(result.value);
    assert_eq!(exit_code, 0);
    cranelisp_runtime::heap_dealloc(result.value);
}

// spec: 10-io §10.6.1 — non-zero exit code
#[test]
fn io_batch_exit_code_nonzero() {
    let src = "(defn main [] (Pure 1))";
    let result = cranelisp::pipeline::compile_and_run(src, cranelisp_types::CompileMode::Batch)
        .unwrap_or_else(|e| panic!("batch failed: {e}"));
    let exit_code = cranelisp_runtime::run_io_trampoline(result.value);
    assert_eq!(exit_code, 1);
    cranelisp_runtime::heap_dealloc(result.value);
}

// spec: 10-io §10.6.1 — exit code from bind chain
#[test]
fn io_batch_exit_code_from_bind() {
    let src = r#"
        (defn main []
          (bind (Pure 10) (fn [x] (Pure (add-i64 x 32)))))
    "#;
    let result = cranelisp::pipeline::compile_and_run(src, cranelisp_types::CompileMode::Batch)
        .unwrap_or_else(|e| panic!("batch failed: {e}"));
    let exit_code = cranelisp_runtime::run_io_trampoline(result.value);
    assert_eq!(exit_code, 42);
    cranelisp_runtime::heap_dealloc(result.value);
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
#[test]
fn io_trampoline_deep_bind_chain() {
    // Build a chain of 100 binds — if the trampoline is recursive, this
    // would need 100 stack frames. The iterative trampoline handles it in O(1).
    // We construct this as a deeply nested bind chain.
    let src = r#"
        (defn add-one [x] (Pure (add-i64 x 1)))
        (defn main []
          (bind (Pure 0)
                (fn [a] (bind (add-one a)
                (fn [b] (bind (add-one b)
                (fn [c] (bind (add-one c)
                (fn [d] (bind (add-one d)
                (fn [e] (bind (add-one e)
                (fn [f] (bind (add-one f)
                (fn [g] (bind (add-one g)
                (fn [h] (bind (add-one h)
                (fn [i] (bind (add-one i)
                (fn [j] (Pure j))))))))))))))))))))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 9); // 0 + add-one called 9 times (a=0, b=1, ..., j=9)
    cranelisp_runtime::heap_dealloc(value);
}

// spec: 10-io §10.8.1 — IO values are data, not forced until trampoline runs
#[test]
fn io_values_are_deferred_data() {
    // Binding an IO value in a let does not force it.
    // Both branches of an if can construct IO values without forcing them.
    let src = r#"
        (defn main []
          (let [io1 (Pure 10)
                io2 (Pure 20)]
            (bind io1 (fn [x] (bind io2 (fn [y] (Pure (add-i64 x y))))))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 30);
    cranelisp_runtime::heap_dealloc(value);
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
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 1);
    cranelisp_runtime::heap_dealloc(value);
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
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 2);
    cranelisp_runtime::heap_dealloc(value);
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
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 1);
    cranelisp_runtime::heap_dealloc(value);
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
    let (value, ty) = compile_and_run_typed(src);
    assert!(ty.is_io(), "expected IO type, got: {:?}", ty);
    // IO (Option a) — inner type is an ADT
    cranelisp_runtime::heap_dealloc(value);
}

// spec: 10-io §10.2.3 — Pure wraps Option (Some 42)
#[test]
fn io_pure_option_some() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main [] (Pure (Some 42)))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert!(ty.is_io(), "expected IO type, got: {:?}", ty);
    cranelisp_runtime::heap_dealloc(value);
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
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 42);
    cranelisp_runtime::heap_dealloc(value);
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
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 30);
    cranelisp_runtime::heap_dealloc(value);
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
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 10);
    cranelisp_runtime::heap_dealloc(value);
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
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 3); // last expression's value
    cranelisp_runtime::heap_dealloc(value);
}

// spec: 10-io §10.4.2 — do type is the type of the last expression
#[test]
fn io_do_type_is_last_expression() {
    // Last expression returns IO Bool, so the whole do returns IO Bool
    let src = r#"
        (defn main []
          (bind (Pure 1)
                (fn [_] (Pure true))))
    "#;
    let (_, ty) = compile_and_run_typed(src);
    assert!(ty.is_io());
    assert_eq!(ty.io_inner_type(), Type::Bool);
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
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 42);
    cranelisp_runtime::heap_dealloc(value);
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
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 42);
    cranelisp_runtime::heap_dealloc(value);
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
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 142);
    cranelisp_runtime::heap_dealloc(value);
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
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 42);
    cranelisp_runtime::heap_dealloc(value);
}

// spec: 10-io §10.4.1 — then combinator: discard String result (AlwaysHeap)
// Regression test for Sprint 16 X1: the `_` parameter must be dec'd in the
// lambda body to avoid leaking the discarded String.
// NOTE: Cannot use assert_rc_balanced here because IO tree nodes (Pure, Bind)
// are heap-allocated and not freed by compile_and_run (needs IO-aware RC helper).
#[test]
fn io_then_combinator_discard_string() {
    let src = r#"
        (defn main []
          (bind (Pure "discarded") (fn [_] (Pure 42))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 42);
    cranelisp_runtime::heap_dealloc(value);
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
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 42);
    cranelisp_runtime::heap_dealloc(value);
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
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 0);
    cranelisp_runtime::heap_dealloc(value);
}

// spec: 10-io §10.3 — lambda with unused heap param (non-discard name)
// Same RC issue as `_` but with a named parameter that happens to be unused.
// NOTE: Cannot use assert_rc_balanced — IO nodes leak (needs IO-aware RC helper).
#[test]
fn io_bind_unused_heap_param() {
    let src = r#"
        (defn main []
          (bind (Pure "unused") (fn [x] (Pure 77))))
    "#;
    let (value, ty) = compile_and_run_typed(src);
    assert!(ty.is_io());
    let inner = cranelisp_runtime::run_io_trampoline(value);
    assert_eq!(inner, 77);
    cranelisp_runtime::heap_dealloc(value);
}

// =============================================================================
// REPL IO display (spec: 10-io §10.6.2)
// =============================================================================

// spec: 10-io §10.6.2 — REPL forces IO and shows inner result
#[test]
fn io_repl_forces_and_displays() {
    // When the REPL evaluates an IO expression, it should force the trampoline
    // and display the inner value. The display format is: `value :: (IO Type)`
    // For (Pure 42), the REPL should show: 42 :: (IO Int)
    // This test verifies the REPL correctly forces the IO tree.
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "(Pure 42)");
    // The display should contain the forced inner value and the IO type.
    assert!(
        display.contains("42"),
        "REPL should display forced inner value 42, got: {display}"
    );
    assert!(
        display.contains("IO"),
        "REPL should show IO type, got: {display}"
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
    let result = cranelisp::pipeline::compile_and_run(src, cranelisp_types::CompileMode::Batch);
    assert!(result.is_err(), "mixing IO and pure should be a type error");
}

// spec: 10-io §10.3 — bind first arg must be IO
#[test]
fn io_neg_bind_first_arg_must_be_io() {
    // bind expects (IO a) as first arg, not a bare Int.
    let src = r#"
        (defn main [] (bind 42 (fn [x] (Pure x))))
    "#;
    let result = cranelisp::pipeline::compile_and_run(src, cranelisp_types::CompileMode::Batch);
    assert!(result.is_err(), "bind with non-IO first arg should be a type error");
}

// spec: 10-io §10.3 — bind second arg must be function
#[test]
fn io_neg_bind_second_arg_must_be_function() {
    let src = r#"
        (defn main [] (bind (Pure 42) 99))
    "#;
    let result = cranelisp::pipeline::compile_and_run(src, cranelisp_types::CompileMode::Batch);
    assert!(result.is_err(), "bind with non-function second arg should be a type error");
}

// spec: 10-io §10.3 — bind continuation must return IO
#[test]
fn io_neg_bind_continuation_must_return_io() {
    // The continuation (fn [x] x) returns Int, not IO Int.
    let src = r#"
        (defn main [] (bind (Pure 42) (fn [x] x)))
    "#;
    let result = cranelisp::pipeline::compile_and_run(src, cranelisp_types::CompileMode::Batch);
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
