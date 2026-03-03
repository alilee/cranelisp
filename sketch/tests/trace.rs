//! Integration tests for the `(trace ...)` special form.
//!
//! These tests require the full REPL module system (GOT-based function tracing).
//! A shared session loads the prelude (including `lib/core/trace.cl`) once and
//! then defines test helper functions (`factorial`, `fib`) used across all tests.
//!
//! ADT heap layout (from `alloc_adt`):
//!   `ptr[0]` = tag, `ptr[1]` = field0, `ptr[2]` = field1, `ptr[3]` = field2, ...
//!
//! `TraceCall(name, params, result, children, nanos)` — Phase 2 layout:
//!   `ptr[0]` = 0 (TAG_TRACE_CALL)
//!   `ptr[1]` = tname (String heap ptr)
//!   `ptr[2]` = tparams (SList<String> heap ptr)
//!   `ptr[3]` = tresult (String heap ptr)
//!   `ptr[4]` = tchildren (SList<Trace> heap ptr)
//!   `ptr[5]` = tnanos (i64 nanoseconds)

use cranelisp::ast::ReplInput;
use cranelisp::ast_builder::parse_repl_input;
use cranelisp::sexp::parse_sexps;

// ── Shared session ────────────────────────────────────────────────────────────

struct SendableSession(std::sync::Mutex<cranelisp::repl::ReplSession>);
// SAFETY: ReplSession's raw pointers are JIT code/GOT addresses valid for program lifetime.
// Mutex ensures exclusive access.
unsafe impl Send for SendableSession {}
unsafe impl Sync for SendableSession {}

static TRACE_SESSION: std::sync::LazyLock<SendableSession> =
    std::sync::LazyLock::new(|| {
        let mut session = cranelisp::repl::ReplSession::new().unwrap();
        session.load_prelude();
        // Make SList constructors available as bare names for test expressions.
        session.tc.install_imported_names(&[
            ("SCons".to_string(), "macros".to_string()),
            ("SNil".to_string(), "macros".to_string()),
        ]);
        // Define test helper functions used across trace tests.
        feed_defn(
            &mut session,
            "(defn factorial [:Int n] (if (<= n 1) 1 (* n (factorial (- n 1)))))",
        );
        feed_defn(
            &mut session,
            "(defn fib [:Int n] (if (<= n 1) n (+ (fib (- n 1)) (fib (- n 2)))))",
        );
        SendableSession(std::sync::Mutex::new(session))
    });

fn with_trace_session<F, R>(f: F) -> R
where
    F: FnOnce(&mut cranelisp::repl::ReplSession) -> R,
{
    let mut session = TRACE_SESSION.0.lock().unwrap();
    // Set TC ptr for cranelisp_trace_format (format_result_value backend).
    // The session.tc address is stable inside the Mutex<ReplSession>.
    cranelisp::jit::set_trace_tc(&session.tc as *const _);
    f(&mut session)
}

// ── Helpers ───────────────────────────────────────────────────────────────────

/// Feed a `defn` into the session (side-effects only, no return value needed).
fn feed_defn(session: &mut cranelisp::repl::ReplSession, src: &str) {
    let sexps = parse_sexps(src).unwrap();
    let sexp = sexps.into_iter().next().unwrap();
    let input = parse_repl_input(src).unwrap();
    session.handle_input(input, src, &sexp);
}

/// Evaluate a bare expression in the session and return the raw `i64` result.
/// Handles IO wrapping transparently.
fn eval_raw(session: &mut cranelisp::repl::ReplSession, src: &str) -> i64 {
    let input = parse_repl_input(src).unwrap();
    let expr = match input {
        ReplInput::Expr(e) => e,
        _ => panic!("eval_raw: expected expression, got defn for: {}", src),
    };

    let ty = session.tc.check_expr(&expr).unwrap();
    let mut mr = session.tc.resolve_methods().unwrap();
    session.tc.resolve_overloads(&mut mr).unwrap();
    let et = session.tc.resolve_expr_types();
    let (mono_defns, mono_dispatches) = session.tc.monomorphise_all().unwrap();
    mr.extend(mono_dispatches);
    session
        .compile_mono_specializations(&mono_defns, &mr, &et)
        .unwrap();

    let fn_slots = session.jit.build_fn_slots_from_modules(&session.tc.modules);
    let eval_fn = session
        .jit
        .compile_expr(&expr, &mr, &et, &fn_slots, &session.tc.modules)
        .unwrap();
    let result = eval_fn();

    let resolved = session.tc.resolve(&ty);
    if matches!(&resolved, cranelisp::types::Type::ADT(name, _) if name == "IO") {
        unsafe { cranelisp::intrinsics::IoTask::from_raw(result) }.run()
    } else {
        result
    }
}

/// Read field at `index` from an ADT heap pointer.
/// Layout: `ptr[0]` = tag, `ptr[1]` = field0, `ptr[2]` = field1, ...
unsafe fn adt_field(ptr: i64, index: usize) -> i64 {
    unsafe { *((ptr as *const i64).add(index)) }
}

/// Read a Rust `String` from a Cranelisp string heap pointer.
/// String layout: `[i64 len][bytes...]`
unsafe fn read_cl_string(ptr: i64) -> String {
    unsafe {
        let len = *(ptr as *const i64) as usize;
        let bytes = std::slice::from_raw_parts((ptr as *const i64).add(1) as *const u8, len);
        String::from_utf8_lossy(bytes).into_owned()
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────────

/// `(trace 42)` returns a non-null heap pointer with TraceCall tag = 0.
#[test]
fn trace_literal_returns_trace_call() {
    with_trace_session(|s| {
        let ptr = eval_raw(s, "(trace 42)");
        assert!(ptr > 0, "trace should return a non-null heap pointer: {}", ptr);
        let tag = unsafe { adt_field(ptr, 0) };
        assert_eq!(tag, 0, "TraceCall tag should be 0 (TAG_TRACE_CALL)");
    });
}

/// The root frame name is always `"::trace::"` (synthetic GOT-swap root).
#[test]
fn trace_root_name_is_trace_sentinel() {
    with_trace_session(|s| {
        let name_ptr = eval_raw(s, "(trace-name (trace 42))");
        let name = unsafe { read_cl_string(name_ptr) };
        assert_eq!(name, "::trace::", "root TraceCall name should be '::trace::'");
    });
}

/// `(trace 42)` — literal body, no function calls — root has no children (SNil = 0).
/// children is now at field index 4 (was 2 in Phase 1).
#[test]
fn trace_literal_has_no_children() {
    with_trace_session(|s| {
        let ptr = eval_raw(s, "(trace 42)");
        // tchildren is field 4 (tag=0, tname=1, tparams=2, tresult=3, tchildren=4, tnanos=5)
        let children = unsafe { adt_field(ptr, 4) };
        // SNil is the bare integer 0
        assert_eq!(children, 0, "trace of literal should have SNil children");
    });
}

/// `(trace (factorial 4))` has non-empty children (factorial was called).
#[test]
fn trace_factorial_has_children() {
    with_trace_session(|s| {
        let ptr = eval_raw(s, "(trace (factorial 4))");
        let children = unsafe { adt_field(ptr, 4) };
        // SCons = heap ptr (> 0); SNil = bare 0
        assert!(
            children > 0,
            "trace(factorial 4) root should have children (SCons != 0)"
        );
    });
}

/// The first child of `(trace (factorial 4))` has name `"factorial"`.
#[test]
fn trace_factorial_first_child_name() {
    with_trace_session(|s| {
        // trace-children returns the children SList; match to get the head
        let name_ptr = eval_raw(
            s,
            r#"(match (trace-children (trace (factorial 4)))
                 [(SCons h _) (trace-name h)])"#,
        );
        let name = unsafe { read_cl_string(name_ptr) };
        assert_eq!(name, "factorial");
    });
}

/// `trace-nanos` returns a positive integer (actual wall-clock time).
/// tnanos is now at field index 5 (was 3 in Phase 1).
#[test]
fn trace_nanos_is_positive() {
    with_trace_session(|s| {
        let nanos = eval_raw(s, "(trace-nanos (trace (factorial 4)))");
        assert!(nanos > 0, "trace-nanos should be > 0, got: {}", nanos);
    });
}

/// `trace-depth` of `(trace (factorial 4))` is at least 5.
///
/// Root "::trace::" → factorial(4) → factorial(3) → factorial(2) → factorial(1)
/// depth = 1 (root) + 4 (recursive calls) = 5.
#[test]
fn trace_depth_factorial_4() {
    with_trace_session(|s| {
        let depth = eval_raw(s, "(trace-depth (trace (factorial 4)))");
        assert!(
            depth >= 5,
            "trace-depth(factorial 4) should be >= 5, got: {}",
            depth
        );
    });
}

/// `trace-flatten` of `(trace (factorial 4))` is a non-empty SList.
#[test]
fn trace_flatten_nonempty() {
    with_trace_session(|s| {
        // Pattern-match: SCons → 1, _ (SNil or other) → 0
        let result = eval_raw(
            s,
            "(match (trace-flatten (trace (factorial 4))) [(SCons _ _) 1 _ 0])",
        );
        assert_eq!(result, 1, "trace-flatten should return a non-empty SList");
    });
}

/// Nested body: `(trace (fib 5))` — multiple calls, tree has at least 5 nodes.
#[test]
fn trace_fib_has_subtree() {
    with_trace_session(|s| {
        let depth = eval_raw(s, "(trace-depth (trace (fib 5)))");
        // fib is binary-recursive; depth >= 4 (fib 5 → fib 4 → fib 3 → fib 2 → fib 1)
        // Plus the root "::trace::" frame → depth >= 5
        assert!(depth >= 5, "trace-depth(fib 5) should be >= 5, got: {}", depth);
    });
}

// ── Phase 2: Params and result capture ───────────────────────────────────────

/// The first child of `(trace (factorial 4))` should have a non-empty params SList.
#[test]
fn trace_factorial_first_child_has_params() {
    with_trace_session(|s| {
        // trace-params returns the params SList; check it's non-empty (SCons)
        let result = eval_raw(
            s,
            r#"(match (trace-params (match (trace-children (trace (factorial 4)))
                                      [(SCons h _) h]))
                 [(SCons _ _) 1 _ 0])"#,
        );
        assert_eq!(result, 1, "first child of trace(factorial 4) should have params");
    });
}

/// The parameter of `(factorial 4)` formats as `"4"`.
#[test]
fn trace_factorial_first_child_param_value() {
    with_trace_session(|s| {
        // Get the first param string of the first child (factorial 4 call)
        let param_ptr = eval_raw(
            s,
            r#"(match (trace-params (match (trace-children (trace (factorial 4)))
                                      [(SCons h _) h]))
                 [(SCons p _) p])"#,
        );
        let param = unsafe { read_cl_string(param_ptr) };
        assert_eq!(param, "4", "param of (factorial 4) should format as \"4\"");
    });
}

/// The result of `(factorial 4)` formats as `"24"`.
#[test]
fn trace_factorial_first_child_result_value() {
    with_trace_session(|s| {
        let result_ptr = eval_raw(
            s,
            r#"(trace-result (match (trace-children (trace (factorial 4)))
                               [(SCons h _) h]))"#,
        );
        let result = unsafe { read_cl_string(result_ptr) };
        assert_eq!(result, "24", "result of (factorial 4) should format as \"24\"");
    });
}

/// `trace-call-string` produces the syntactically correct call form.
#[test]
fn trace_call_string_correct_form() {
    with_trace_session(|s| {
        let ptr = eval_raw(
            s,
            r#"(trace-call-string (match (trace-children (trace (factorial 4)))
                                    [(SCons h _) h]))"#,
        );
        let s_val = unsafe { read_cl_string(ptr) };
        assert!(
            s_val.starts_with("(factorial"),
            "trace-call-string should start with \"(factorial\", got: {:?}",
            s_val
        );
        assert!(
            s_val.contains('4'),
            "trace-call-string should contain the argument \"4\", got: {:?}",
            s_val
        );
    });
}

/// `trace-show-tree` returns a non-empty string for a trace with children.
#[test]
fn trace_show_tree_nonempty() {
    with_trace_session(|s| {
        let ptr = eval_raw(s, "(trace-show-tree (trace (factorial 3)))");
        let tree = unsafe { read_cl_string(ptr) };
        assert!(!tree.is_empty(), "trace-show-tree should return a non-empty string");
        assert!(
            tree.contains("(factorial"),
            "trace-show-tree should contain \"(factorial\", got: {:?}",
            tree
        );
    });
}
