// /run-tests slash command: discover and execute test-* functions.

use std::io::Write;
use std::time::Instant;

use cranelisp_types::NULLARY_TAG_THRESHOLD;

use super::ReplSession;

/// Handle `/run-tests [prefix]` -- discover and run test-* functions.
///
/// Discovers zero-arg functions whose names start with "test-" in the GOT
/// state, calls them directly, and interprets the `(Option String)` result:
/// - None (value 0) = pass
/// - Some(reason) (heap pointer) = fail with reason string
pub(crate) fn handle_run_tests(session: &mut ReplSession, prefix: &str, stdout: &mut impl Write) {
    let tests = discover_test_functions(session, prefix);
    if tests.is_empty() {
        if prefix.is_empty() {
            let _ = writeln!(stdout, "No test-* functions found.");
        } else {
            let _ = writeln!(stdout, "No test-* functions found matching '{prefix}'.");
        }
        return;
    }

    let start = Instant::now();
    let (passed, failed) = run_discovered_tests(&tests, stdout);
    let elapsed = start.elapsed();

    let _ = writeln!(stdout);
    if failed == 0 {
        let _ = writeln!(
            stdout,
            "{passed} passed in {:.2}ms",
            elapsed.as_secs_f64() * 1000.0,
        );
    } else {
        let _ = writeln!(
            stdout,
            "{passed} passed, {failed} failed in {:.2}ms",
            elapsed.as_secs_f64() * 1000.0,
        );
    }
}

/// Discover test-* zero-arg functions with code pointers in the GOT state.
///
/// Returns a sorted list of (name, code_ptr) pairs. If `prefix` is non-empty,
/// only functions whose names start with `"test-{prefix}"` are included.
fn discover_test_functions(
    session: &ReplSession,
    prefix: &str,
) -> Vec<(String, *const u8)> {
    let mut tests = Vec::new();

    for (name, dc) in &session.core.got_state.def_codegen {
        let name_str = name.as_ref();
        // Must be a test-* function.
        if !name_str.starts_with("test-") {
            continue;
        }
        // Apply prefix filter if given.
        if !prefix.is_empty() && !name_str.starts_with(&format!("test-{prefix}")) {
            continue;
        }
        // Must be a zero-arg function with a valid code pointer.
        let (code_ptr, arity) = match (dc.code_ptr, dc.param_count) {
            (Some(ptr), Some(a)) if !ptr.is_null() => (ptr, a),
            _ => continue,
        };
        if arity != 0 {
            continue;
        }
        tests.push((name_str.to_string(), code_ptr));
    }

    tests.sort_by(|a, b| a.0.cmp(&b.0));
    tests
}

/// Execute discovered test functions and print per-test results.
///
/// Each test function is `extern "C" fn() -> i64` returning `(Option String)`:
/// - 0 = None = pass
/// - heap pointer = Some(reason_string) = fail
///
/// Returns (passed_count, failed_count).
fn run_discovered_tests(
    tests: &[(String, *const u8)],
    stdout: &mut impl Write,
) -> (usize, usize) {
    let mut passed = 0usize;
    let mut failed = 0usize;

    for (name, code_ptr) in tests {
        // SAFETY: code_ptr points to JIT-compiled code with the extern "C" fn() -> i64
        // calling convention. It was produced by the backend for a zero-arg function.
        let result = invoke_test_fn(*code_ptr);
        let dots = ".".repeat(40_usize.saturating_sub(name.len()));

        match result {
            TestResult::Pass => {
                let _ = writeln!(stdout, "  {name} {dots} ok");
                passed += 1;
            }
            TestResult::Fail(reason) => {
                let _ = writeln!(stdout, "  {name} {dots} FAILED: {reason}");
                failed += 1;
            }
            TestResult::Panic(msg) => {
                let _ = writeln!(stdout, "  {name} {dots} PANIC: {msg}");
                failed += 1;
            }
        }
    }

    (passed, failed)
}

/// Result of running a single test function.
enum TestResult {
    Pass,
    Fail(String),
    Panic(String),
}

/// Invoke a test function and interpret its `(Option String)` result.
///
/// Uses the runtime panic boundary to catch panics from match exhaustiveness
/// failures or other runtime errors.
fn invoke_test_fn(code_ptr: *const u8) -> TestResult {
    // Clear stale errors and call with panic boundary.
    let _ = cranelisp_runtime::panic::take_runtime_error();

    // SAFETY: code_ptr is a valid JIT function pointer for a zero-arg function.
    let value = unsafe {
        let func: extern "C" fn() -> i64 = std::mem::transmute(code_ptr);
        func()
    };

    // Check for runtime panic (e.g., match exhaustiveness failure).
    if let Some(msg) = cranelisp_runtime::panic::take_runtime_error() {
        return TestResult::Panic(msg);
    }

    interpret_option_string_result(value)
}

/// Interpret an `(Option String)` value: 0 = None (pass), heap ptr = Some (fail).
fn interpret_option_string_result(value: i64) -> TestResult {
    if (value as usize) < NULLARY_TAG_THRESHOLD {
        // Nullary constructor (None = tag 0) -- test passed.
        TestResult::Pass
    } else {
        // Data constructor (Some = heap pointer) -- extract reason string.
        // Layout: [header(16) | tag(8) | string_ptr(8)]
        // string_ptr is at base + 24 (HeapAdt::field_offset(0)).
        let string_ptr = unsafe {
            let base = value as *const u8;
            *(base.add(cranelisp_backend::heap::HeapAdt::field_offset(0) as usize) as *const i64)
        };
        // SAFETY: string_ptr points to a valid heap-allocated String.
        let reason = unsafe { cranelisp_runtime::read_string_as_str(string_ptr) };
        TestResult::Fail(reason.to_string())
    }
}
