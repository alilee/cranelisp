// Shared test helpers for integration tests.
//
// These helpers wire the full pipeline (parse -> build -> typecheck -> codegen -> execute)
// so integration tests only need to provide source text.

use cranelisp::pipeline;
use cranelisp::repl::ReplSession;
use cranelisp_types::{CompileMode, CranelispError, Type};

/// Full pipeline: compile source text and return the i64 result.
///
/// Uses Batch mode with no macros.
pub fn compile_and_run_simple(src: &str) -> i64 {
    let result = pipeline::compile_and_run(src, CompileMode::Batch)
        .unwrap_or_else(|e| panic!("compile_and_run failed: {e}"));
    result.value
}

/// Full pipeline: compile source text and return (result, inferred type).
pub fn compile_and_run_typed(src: &str) -> (i64, Type) {
    let result = pipeline::compile_and_run(src, CompileMode::Batch)
        .unwrap_or_else(|e| panic!("compile_and_run_typed failed: {e}"));
    (result.value, result.ty)
}

/// Run in both Batch and Interactive modes and assert the same i64 result.
pub fn compile_both(src: &str, expected: i64) {
    let batch = pipeline::compile_and_run(src, CompileMode::Batch)
        .unwrap_or_else(|e| panic!("batch compile_and_run failed: {e}"));
    assert_eq!(
        batch.value, expected,
        "Batch mode: expected {expected}, got {}",
        batch.value
    );

    let interactive = pipeline::compile_and_run(src, CompileMode::Interactive)
        .unwrap_or_else(|e| panic!("interactive compile_and_run failed: {e}"));
    assert_eq!(
        interactive.value, expected,
        "Interactive mode: expected {expected}, got {}",
        interactive.value
    );
}

/// Assert that compiling the source produces a TypeError containing the substring.
pub fn assert_type_error(src: &str, expected_substring: &str) {
    let result = pipeline::compile_and_run(src, CompileMode::Batch);
    match result {
        Err(CranelispError::TypeError { message, .. }) => {
            assert!(
                message.contains(expected_substring),
                "expected type error containing '{expected_substring}', got: {message}"
            );
        }
        Err(other) => {
            panic!("expected TypeError, got: {other}");
        }
        Ok(_) => {
            panic!("expected TypeError, but compilation succeeded");
        }
    }
}

/// Assert that compiling the source produces a ParseError containing the substring.
pub fn assert_parse_error(src: &str, expected_substring: &str) {
    let result = pipeline::compile_and_run(src, CompileMode::Batch);
    match result {
        Err(CranelispError::ParseError { message, .. }) => {
            assert!(
                message.contains(expected_substring),
                "expected parse error containing '{expected_substring}', got: {message}"
            );
        }
        Err(other) => {
            panic!("expected ParseError, got: {other}");
        }
        Ok(_) => {
            panic!("expected ParseError, but compilation succeeded");
        }
    }
}

/// Assert that compiling produces any error (type, parse, codegen, or module) containing the substring.
pub fn assert_error(src: &str, expected_substring: &str) {
    let result = pipeline::compile_and_run(src, CompileMode::Batch);
    match result {
        Err(e) => {
            let msg = e.message();
            assert!(
                msg.contains(expected_substring),
                "expected error containing '{expected_substring}', got: {msg}"
            );
        }
        Ok(_) => {
            panic!("expected error containing '{expected_substring}', but compilation succeeded");
        }
    }
}

/// Create a new REPL session for multi-input testing.
pub fn repl_session() -> ReplSession {
    ReplSession::new()
}

/// Evaluate one input in a REPL session, returning the i64 result.
pub fn repl_eval(session: &mut ReplSession, src: &str) -> i64 {
    let result = session
        .eval(src)
        .unwrap_or_else(|e| panic!("repl_eval failed on '{src}': {e}"));
    result.value
}

/// Evaluate one input in a REPL session, returning (value, type).
pub fn repl_eval_typed(session: &mut ReplSession, src: &str) -> (i64, Type) {
    let result = session
        .eval(src)
        .unwrap_or_else(|e| panic!("repl_eval_typed failed on '{src}': {e}"));
    (result.value, result.ty)
}
