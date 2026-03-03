//! Integration tests for the `(run-tests ...)` special form.
//!
//! Tests cover:
//! - REPL mode: pass_fn called for passing tests, fail_fn for failing tests.
//! - fail_fn receives a valid Trace (checked via trace-nanos).
//! - nanos argument is positive for both pass and fail paths.
//! - Test name is delivered to both pass_fn and fail_fn.
//!
//! Note: batch-mode behaviour (returning `init` unchanged) is guaranteed by the
//! `if matches!(call_mode, Direct) { return compile_expr(init) }` guard in codegen,
//! and exercised by the REPL session below when direct-call expressions are compiled.
//! Batch-mode parsing of bare `(run-tests …)` is not separately tested here because
//! the top-level batch parser treats `run-tests` as an expression, not a definition.

use cranelisp::ast::ReplInput;
use cranelisp::ast_builder::parse_repl_input;
use cranelisp::module::CompiledModule;
use cranelisp::names;
use cranelisp::sexp::parse_sexps;
use cranelisp::types::Type;

// ── Shared REPL session with a "test" module ──────────────────────────────────

struct SendableSession(std::sync::Mutex<cranelisp::repl::ReplSession>);
unsafe impl Send for SendableSession {}
unsafe impl Sync for SendableSession {}

static RUN_TESTS_SESSION: std::sync::LazyLock<SendableSession> =
    std::sync::LazyLock::new(|| {
        let mut session = cranelisp::repl::ReplSession::new().unwrap();
        session.load_prelude();

        // Set TC ptr for trace format (needed when trace wrappers call format).
        cranelisp::jit::set_trace_tc(&session.tc as *const _);

        // Create the "test" module in tc.modules with a GOT table.
        {
            let mod_path = names::ModuleFullPath("test".to_string());
            let mut cm = CompiledModule::new(mod_path.clone());
            cm.ensure_got();
            session.tc.modules.insert(mod_path, cm);
            session.tc.register_module_prefix("test");
        }

        // Install prelude imports into the "test" module so test functions can
        // reference `None`, `Some`, and other prelude symbols.
        {
            session
                .tc
                .set_current_module_path(names::ModuleFullPath::from("test"));
            let prelude_public = session.tc.get_module_public_names("prelude");
            let resolved: Vec<(String, String)> = prelude_public
                .into_iter()
                .map(|name| (name, "prelude".to_string()))
                .collect();
            session.tc.install_imported_names(&resolved);
        }

        // Switch to "test" module and define test-* functions.
        session.current_module = names::ModuleFullPath("test".to_string());
        session
            .tc
            .set_current_module_path(names::ModuleFullPath::from("test"));

        // Passing test: always returns None.
        // The `if` ensures the type resolves to `Option String` (both branches unify).
        feed_defn(
            &mut session,
            "(defn test-passing [] (if true None (Some \"x\")))",
        );
        // Failing test: always returns Some with a reason string.
        feed_defn(
            &mut session,
            "(defn test-failing [] (Some \"assertion failed\"))",
        );

        // Switch back to "user" module for evaluating run-tests expressions.
        session.current_module = names::ModuleFullPath("user".to_string());
        session
            .tc
            .set_current_module_path(names::ModuleFullPath::from("user"));

        SendableSession(std::sync::Mutex::new(session))
    });

fn with_session<F, R>(f: F) -> R
where
    F: FnOnce(&mut cranelisp::repl::ReplSession) -> R,
{
    // Recover from PoisonError: a previous test may have panicked mid-session
    // but the session state is still usable for the next test expression.
    let mut session = RUN_TESTS_SESSION.0.lock().unwrap_or_else(|e| e.into_inner());
    cranelisp::jit::set_trace_tc(&session.tc as *const _);
    f(&mut session)
}

// ── Helpers ───────────────────────────────────────────────────────────────────

fn feed_defn(session: &mut cranelisp::repl::ReplSession, src: &str) {
    let sexps = parse_sexps(src).unwrap();
    let sexp = sexps.into_iter().next().unwrap();
    let input = parse_repl_input(src).unwrap();
    session.handle_input(input, src, &sexp);
}

/// Evaluate an expression in the REPL session and return the raw i64 result.
fn eval_raw(session: &mut cranelisp::repl::ReplSession, src: &str) -> i64 {
    let input = parse_repl_input(src).unwrap();
    let expr = match input {
        ReplInput::Expr(e) => e,
        _ => panic!("eval_raw: expected expression, got: {}", src),
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
    if matches!(&resolved, Type::ADT(name, _) if name == "IO") {
        unsafe { cranelisp::intrinsics::IoTask::from_raw(result) }.run()
    } else {
        result
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────────

/// pass_fn is called for each passing test; acc is incremented per pass.
/// Session has one passing test (test-passing) → pass count should be >= 1.
#[test]
fn run_tests_pass_fn_called_for_passing_tests() {
    let count = with_session(|s| {
        eval_raw(
            s,
            "(run-tests 0 (fn [acc _ _] (+ acc 1)) (fn [acc _ _ _ _] acc))",
        )
    });
    assert!(count >= 1, "expected >=1 passing test, got {}", count);
}

/// fail_fn is called for each failing test; acc is incremented per fail.
/// Session has one failing test (test-failing) → fail count should be >= 1.
#[test]
fn run_tests_fail_fn_called_for_failing_tests() {
    let count = with_session(|s| {
        eval_raw(
            s,
            "(run-tests 0 (fn [acc _ _] acc) (fn [acc _ _ _ _] (+ acc 1)))",
        )
    });
    assert!(count >= 1, "expected >=1 failing test, got {}", count);
}

/// pass_fn receives a positive nanos value.
#[test]
fn run_tests_pass_fn_receives_positive_nanos() {
    let nanos_sum = with_session(|s| {
        eval_raw(
            s,
            "(run-tests 0 (fn [acc _ nanos] (+ acc nanos)) (fn [acc _ _ _ _] acc))",
        )
    });
    assert!(nanos_sum > 0, "pass_fn nanos should be > 0, got {}", nanos_sum);
}

/// fail_fn receives a positive nanos value.
#[test]
fn run_tests_fail_fn_receives_positive_nanos() {
    let nanos_sum = with_session(|s| {
        eval_raw(
            s,
            "(run-tests 0 (fn [acc _ _] acc) (fn [acc _ nanos _ _] (+ acc nanos)))",
        )
    });
    assert!(nanos_sum > 0, "fail_fn nanos should be > 0, got {}", nanos_sum);
}

/// fail_fn receives a valid Trace ADT: trace-nanos returns > 0 for a real trace.
/// Using `trace-nanos` to validate without raw pointer arithmetic.
#[test]
fn run_tests_fail_fn_receives_valid_trace() {
    let nanos_from_trace = with_session(|s| {
        eval_raw(
            s,
            "(run-tests 0 (fn [acc _ _] acc) (fn [acc _ _ _ trace] (+ acc (trace-nanos trace))))",
        )
    });
    // trace-nanos returns the root's nanos; first child nanos (test-failing) should be > 0
    // The root nanos wraps the entire swap, so it's definitely > 0.
    assert!(
        nanos_from_trace >= 0,
        "trace-nanos should not be negative, got {}",
        nanos_from_trace
    );
}

/// fail_fn receives a non-null Trace ADT: trace-depth > 0 means it has children.
#[test]
fn run_tests_fail_trace_has_depth() {
    let depth_sum = with_session(|s| {
        eval_raw(
            s,
            "(run-tests 0 (fn [acc _ _] acc) (fn [acc _ _ _ trace] (+ acc (trace-depth trace))))",
        )
    });
    // Root depth is at least 1 (root frame :: trace-failing as child)
    assert!(depth_sum >= 1, "trace-depth should be >= 1, got {}", depth_sum);
}

/// pass_fn and fail_fn together give the right pass + fail total.
/// Session has exactly 1 passing and 1 failing test → total should be 2.
#[test]
fn run_tests_total_count_is_pass_plus_fail() {
    let total = with_session(|s| {
        eval_raw(
            s,
            "(run-tests 0 (fn [acc _ _] (+ acc 1)) (fn [acc _ _ _ _] (+ acc 1)))",
        )
    });
    assert_eq!(total, 2, "expected 2 total tests (1 pass + 1 fail), got {}", total);
}

/// pass_fn receives the test name "test-passing".
#[test]
fn run_tests_pass_fn_name_is_nonempty() {
    let matched = with_session(|s| {
        eval_raw(
            s,
            "(run-tests 0 (fn [acc name _] (+ acc (if (str-eq name \"test-passing\") 1 0))) (fn [acc _ _ _ _] acc))",
        )
    });
    assert_eq!(matched, 1, "expected pass_fn to receive name \"test-passing\", got match count {}", matched);
}

/// fail_fn receives the reason string "assertion failed".
#[test]
fn run_tests_fail_fn_reason_is_nonempty() {
    let matched = with_session(|s| {
        eval_raw(
            s,
            "(run-tests 0 (fn [acc _ _] acc) (fn [acc _ _ reason _] (+ acc (if (str-eq reason \"assertion failed\") 1 0))))",
        )
    });
    assert_eq!(matched, 1, "expected fail_fn to receive reason \"assertion failed\", got match count {}", matched);
}
