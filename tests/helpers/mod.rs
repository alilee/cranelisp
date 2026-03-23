// Shared test helpers for integration tests.
//
// These helpers wire the full pipeline (parse -> build -> typecheck -> codegen -> execute)
// so integration tests only need to provide source text.

#![allow(dead_code)]

use cranelisp::repl::{format_result_value, ReplSession};
use cranelisp_types::{CranelispError, Type};

use cranelisp::repl::ReplResult;

// =============================================================================
// Multi-form eval helper
// =============================================================================

/// Parse source text into individual top-level forms and eval each one in the session.
///
/// REPL `eval()` only processes one sexp per call. This helper parses the source
/// to find form boundaries (via spans), then evals each form's source substring
/// in order, returning the result of the last form.
fn eval_all_forms(session: &mut ReplSession, src: &str, label: &str) -> ReplResult {
    let sexps = cranelisp_frontend::parse(src)
        .unwrap_or_else(|e| panic!("{label} parse failed: {e}"));
    assert!(!sexps.is_empty(), "{label}: no forms in source");
    let mut last_result = None;
    for sexp in &sexps {
        let span = sexp.span();
        let form_src = &src[span.start as usize..span.end as usize];
        let result = session
            .eval(form_src)
            .unwrap_or_else(|e| panic!("{label} failed on '{form_src}': {e}"));
        last_result = Some(result);
    }
    last_result.unwrap()
}

/// Like `eval_all_forms` but returns Err if any form produces an error.
fn try_eval_all_forms(session: &mut ReplSession, src: &str) -> Result<ReplResult, CranelispError> {
    let sexps = cranelisp_frontend::parse(src)?;
    if sexps.is_empty() {
        return Err(CranelispError::ParseError {
            message: "empty input".into(),
            span: cranelisp_types::Span::SYNTHETIC,
        });
    }
    let mut last_result = None;
    for sexp in &sexps {
        let span = sexp.span();
        let form_src = &src[span.start as usize..span.end as usize];
        let result = session.eval(form_src)?;
        last_result = Some(result);
    }
    Ok(last_result.unwrap())
}

// =============================================================================
// Fixtures directory and preamble paths
// =============================================================================

/// Path to the test fixtures directory (tests/fixtures/).
pub fn test_fixtures_dir() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
}

/// Standard preamble: import all primitives as bare names.
/// Most tests need this.
pub const PREAMBLE_PRIMITIVES: &str = "fixtures/preamble_primitives.cl";

// =============================================================================
// REPL session helpers
// =============================================================================

/// Create a REPL session with optional prelude and preamble.
///
/// - `prelude`: path relative to `tests/` for a prelude `.cl` file loaded via
///   the prelude mechanism (e.g., `"fixtures/prelude.cl"`). Pass `None` for no prelude.
/// - `preamble`: path relative to `tests/` for a preamble `.cl` file whose
///   contents are eval'd into the session before returning (e.g.,
///   `"fixtures/preamble_primitives.cl"`). Pass `None` for no preamble.
///
/// Examples:
/// ```ignore
/// let s = repl_session(None, None);                                    // bare
/// let s = repl_session(None, Some(PREAMBLE_PRIMITIVES));               // primitives only
/// let s = repl_session(Some("fixtures/prelude.cl"), None);             // prelude only
/// let s = repl_session(Some("fixtures/prelude.cl"), Some("fixtures/preamble_macros.cl")); // both
/// ```
pub fn repl_session_with(prelude: Option<&str>, preamble: Option<&str>) -> ReplSession {
    let project_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));

    let mut session = if let Some(prelude_path) = prelude {
        let prelude_dir = project_root.join("tests").join(prelude_path);
        let lib_dir = prelude_dir.parent().unwrap().to_path_buf();
        ReplSession::new_with_prelude(project_root, &[lib_dir])
            .unwrap_or_else(|e| panic!("failed to load prelude '{prelude_path}': {e}"))
    } else {
        ReplSession::new()
    };

    if let Some(preamble_path) = preamble {
        let full_path = project_root.join("tests").join(preamble_path);
        let preamble_src = std::fs::read_to_string(&full_path)
            .unwrap_or_else(|e| panic!("failed to read preamble '{preamble_path}': {e}"));
        for line in preamble_src.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with(";;") {
                continue;
            }
            session
                .eval(trimmed)
                .unwrap_or_else(|e| panic!("preamble '{preamble_path}' failed on '{trimmed}': {e}"));
        }
    }

    session
}

// =============================================================================
// Batch pipeline helpers
// =============================================================================

/// Full pipeline: compile source text and return the i64 result.
///
/// Uses a REPL session with the given preamble, then evals each top-level form.
/// Pass `Some(PREAMBLE_PRIMITIVES)` for tests that use bare primitive names.
/// Pass `None` for tests that need a bare environment.
pub fn compile_and_run_simple_with(preamble: Option<&str>, src: &str) -> i64 {
    let mut session = repl_session_with(None, preamble);
    // Eval each top-level form separately (REPL eval only processes one form at a time).
    let result = eval_all_forms(&mut session, src, "compile_and_run_simple");
    // If source defines a main function, call it to get the result (batch-mode compat).
    if src.contains("defn main") {
        let main_result = session
            .eval("(main)")
            .unwrap_or_else(|e| panic!("compile_and_run_simple: calling (main) failed: {e}"));
        main_result.value
    } else {
        result.value
    }
}

/// Full pipeline: compile source text and return (result, inferred type).
pub fn compile_and_run_typed_with(preamble: Option<&str>, src: &str) -> (i64, Type) {
    let mut session = repl_session_with(None, preamble);
    let result = eval_all_forms(&mut session, src, "compile_and_run_typed");
    // If source defines a main function, call it to get the result (batch-mode compat).
    if src.contains("defn main") {
        let main_result = session
            .eval("(main)")
            .unwrap_or_else(|e| panic!("compile_and_run_typed: calling (main) failed: {e}"));
        (main_result.value, main_result.ty)
    } else {
        (result.value, result.ty)
    }
}

/// Run in both Batch and Interactive modes and assert the same i64 result.
pub fn compile_both(src: &str, expected: i64) {
    // Use REPL with primitives preamble for both modes.
    let mut session = repl_session_with(None, Some(PREAMBLE_PRIMITIVES));
    let result = eval_all_forms(&mut session, src, "compile_both");
    // If source defines a main function, call it to get the result (batch-mode compat).
    let final_value = if src.contains("defn main") {
        let main_result = session
            .eval("(main)")
            .unwrap_or_else(|e| panic!("compile_both: calling (main) failed: {e}"));
        main_result.value
    } else {
        result.value
    };
    assert_eq!(
        final_value, expected,
        "expected {expected}, got {}",
        final_value
    );
}

/// Assert that compiling the source produces a TypeError containing the substring.
pub fn assert_type_error_with(preamble: Option<&str>, src: &str, expected_substring: &str) {
    let mut session = repl_session_with(None, preamble);
    let result = try_eval_all_forms(&mut session, src);
    // If eval succeeded and source defines main, try calling it to trigger the error.
    let result = if result.is_ok() && src.contains("defn main") {
        session.eval("(main)")
    } else {
        result
    };
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
    let mut session = repl_session_with(None, Some(PREAMBLE_PRIMITIVES));
    let result = session.eval(src);
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

/// Assert that compiling produces any error containing the substring.
pub fn assert_error_with(preamble: Option<&str>, src: &str, expected_substring: &str) {
    let mut session = repl_session_with(None, preamble);
    let result = try_eval_all_forms(&mut session, src);
    // If eval succeeded and source defines main, try calling it to trigger the error.
    let result = if result.is_ok() && src.contains("defn main") {
        session.eval("(main)")
    } else {
        result
    };
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

// =============================================================================
// Backward-compatible convenience wrappers
//
// These preserve the old signatures so 650+ existing call sites don't need
// updating. They default to PREAMBLE_PRIMITIVES. New tests should use the
// parameterized versions above for clarity.
// =============================================================================

/// REPL session with primitives imported. This is the most common setup —
/// 348 existing call sites use `repl_session()`.
pub fn repl_session() -> ReplSession {
    repl_session_with(None, Some(PREAMBLE_PRIMITIVES))
}

/// REPL session with test prelude (Option, Num, Eq, Ord).
pub fn repl_session_with_test_prelude() -> ReplSession {
    repl_session_with(Some("fixtures/prelude.cl"), None)
}

/// Compile with primitives preamble. 309 existing call sites use this.
pub fn compile_and_run_simple(src: &str) -> i64 {
    compile_and_run_simple_with(Some(PREAMBLE_PRIMITIVES), src)
}

/// Compile and return typed result with primitives preamble.
pub fn compile_and_run_typed(src: &str) -> (i64, Type) {
    compile_and_run_typed_with(Some(PREAMBLE_PRIMITIVES), src)
}

/// Compile and return heap display with primitives preamble.
pub fn compile_and_run_heap(src: &str) -> (i64, Type, String) {
    compile_and_run_heap_with(Some(PREAMBLE_PRIMITIVES), src)
}

/// Assert type error with primitives preamble.
pub fn assert_type_error(src: &str, expected_substring: &str) {
    assert_type_error_with(Some(PREAMBLE_PRIMITIVES), src, expected_substring)
}

/// Assert any error with primitives preamble.
pub fn assert_error(src: &str, expected_substring: &str) {
    assert_error_with(Some(PREAMBLE_PRIMITIVES), src, expected_substring)
}

/// Assert RC balanced with primitives preamble.
pub fn assert_rc_balanced(src: &str) {
    assert_rc_balanced_with(Some(PREAMBLE_PRIMITIVES), src)
}

// =============================================================================
// REPL eval helpers (session already created)
// =============================================================================

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

/// Compile source text and return (value, type, display_string).
///
/// The display string is formatted with full type definition context for
/// heap types (String, ADT, Fn).
pub fn compile_and_run_heap_with(preamble: Option<&str>, src: &str) -> (i64, Type, String) {
    let mut session = repl_session_with(None, preamble);
    let last_result = eval_all_forms(&mut session, src, "compile_and_run_heap");
    // If source defines a main function, call it to get the result (batch-mode compat).
    let result = if src.contains("defn main") {
        session.eval("(main)")
            .unwrap_or_else(|e| panic!("compile_and_run_heap: calling (main) failed: {e}"))
    } else {
        last_result
    };
    let display = format_result_value(
        result.value,
        &result.ty,
        session.type_defs(),
        session.type_modules(),
    );
    (result.value, result.ty, display)
}

/// Assert that all RC allocations are balanced (allocs == deallocs) after
/// running the given source text.
///
/// Uses delta-based assertions: snapshots counters before and after execution,
/// then asserts that alloc_count and dealloc_count incremented by the same amount
/// and that bytes_current returned to its prior level.
///
/// Must be run serially (`--test-threads=1`) since global counters are shared.
pub fn assert_rc_balanced_with(preamble: Option<&str>, src: &str) {
    let mut session = repl_session_with(None, preamble);
    let allocs_before = cranelisp_runtime::alloc_count();
    let deallocs_before = cranelisp_runtime::dealloc_count();
    let bytes_before = cranelisp_runtime::bytes_current();

    let _result = eval_all_forms(&mut session, src, "assert_rc_balanced");

    // If source defines a main function, call it (batch-mode compat).
    if src.contains("defn main") {
        let _main_result = session.eval("(main)")
            .unwrap_or_else(|e| panic!("assert_rc_balanced: calling (main) failed: {e}"));
    }

    let allocs_after = cranelisp_runtime::alloc_count();
    let deallocs_after = cranelisp_runtime::dealloc_count();
    let bytes_after = cranelisp_runtime::bytes_current();

    let new_allocs = allocs_after - allocs_before;
    let new_deallocs = deallocs_after - deallocs_before;

    assert_eq!(
        new_allocs, new_deallocs,
        "RC imbalance: {new_allocs} allocs but {new_deallocs} deallocs for: {src}"
    );
    assert_eq!(
        bytes_after, bytes_before,
        "Leaked {} bytes for: {src}",
        bytes_after - bytes_before
    );
}

// =============================================================================
// Platform-aware test helpers (test-capture DLL)
// =============================================================================

/// Wrapper for the test-capture platform DLL's utility functions.
///
/// Provides access to `test_capture_reset`, `test_capture_get_output`, and
/// `test_capture_free_output` via `libloading`. The test-capture platform
/// captures print output in-memory and provides scripted read-line input,
/// enabling IO integration tests without real stdout/stdin.
///
/// The test-capture DLL must be built before running these tests:
///   cargo build -p cranelisp-test-capture
pub struct TestCapture {
    _lib: libloading::Library,
    reset_fn: unsafe extern "C" fn(),
    get_output_fn: unsafe extern "C" fn(*mut *const u8, *mut usize),
    free_output_fn: unsafe extern "C" fn(*mut u8, usize),
    set_input_fn: unsafe extern "C" fn(*const *const u8, *const usize, usize),
}

impl TestCapture {
    /// Load the test-capture DLL from the project's Cargo build output.
    ///
    /// Returns None if the DLL is not built.
    pub fn load() -> Option<Self> {
        let project_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        let dll_path = cranelisp::platform::resolve_platform_path("test-capture", project_root)?;

        let lib = unsafe { libloading::Library::new(&dll_path).ok()? };

        let reset_fn: libloading::Symbol<unsafe extern "C" fn()> =
            unsafe { lib.get(b"test_capture_reset").ok()? };
        let get_output_fn: libloading::Symbol<unsafe extern "C" fn(*mut *const u8, *mut usize)> =
            unsafe { lib.get(b"test_capture_get_output").ok()? };
        let free_output_fn: libloading::Symbol<unsafe extern "C" fn(*mut u8, usize)> =
            unsafe { lib.get(b"test_capture_free_output").ok()? };
        let set_input_fn: libloading::Symbol<
            unsafe extern "C" fn(*const *const u8, *const usize, usize),
        > = unsafe { lib.get(b"test_capture_set_input").ok()? };

        Some(TestCapture {
            reset_fn: *reset_fn,
            get_output_fn: *get_output_fn,
            free_output_fn: *free_output_fn,
            set_input_fn: *set_input_fn,
            _lib: lib,
        })
    }

    /// Reset captured output and input queue.
    pub fn reset(&self) {
        unsafe { (self.reset_fn)() }
    }

    /// Get all captured print output as a string.
    pub fn get_output(&self) -> String {
        let mut ptr: *const u8 = std::ptr::null();
        let mut len: usize = 0;
        unsafe {
            (self.get_output_fn)(&mut ptr, &mut len);
            if ptr.is_null() || len == 0 {
                return String::new();
            }
            let bytes = std::slice::from_raw_parts(ptr, len);
            let result = String::from_utf8_lossy(bytes).into_owned();
            (self.free_output_fn)(ptr as *mut u8, len);
            result
        }
    }

    /// Set scripted input lines for read-line.
    pub fn set_input(&self, lines: &[&str]) {
        let ptrs: Vec<*const u8> = lines.iter().map(|s| s.as_ptr()).collect();
        let lens: Vec<usize> = lines.iter().map(|s| s.len()).collect();
        unsafe {
            (self.set_input_fn)(ptrs.as_ptr(), lens.as_ptr(), lines.len());
        }
    }
}

/// Create a REPL session with the test-capture platform loaded and imported.
///
/// Returns (session, test_capture) or None if the DLL is not built.
pub fn repl_session_with_test_capture() -> Option<(ReplSession, TestCapture)> {
    let capture = TestCapture::load()?;
    capture.reset();

    let project_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let stdlib_dir = project_root.join("stdlib");
    let mut session = ReplSession::new_with_prelude(project_root, &[stdlib_dir])
        .unwrap_or_else(|e| panic!("failed to load prelude: {e}"));
    // Load the test-capture platform.
    session
        .eval("(platform test-capture)")
        .unwrap_or_else(|e| panic!("failed to load test-capture platform: {e}"));
    // Import all platform functions (print, read-line).
    session
        .eval("(import [platform.test-capture [print read-line]])")
        .unwrap_or_else(|e| panic!("failed to import test-capture functions: {e}"));

    Some((session, capture))
}

/// Evaluate in REPL and return the formatted display string with ADT context.
///
/// Uses `definition_display` when available (for deftrait, impl, constrained fn).
/// For IO types, forces the IO tree via trampoline (executing side effects) and
/// formats the inner result value, mirroring what the REPL does in its eval loop.
/// Otherwise falls back to `format_result_value`.
pub fn repl_eval_display(session: &mut ReplSession, src: &str) -> String {
    let result = session
        .eval(src)
        .unwrap_or_else(|e| panic!("repl_eval_display failed on '{src}': {e}"));
    if let Some(display) = result.definition_display {
        display
    } else if result.ty.is_io() {
        // IO expression: force the IO tree via trampoline, then format the inner
        // value wrapped in (IO.Pure ...). This mirrors the REPL's force_io_and_format behavior.
        let inner_val = cranelisp_runtime::run_io_trampoline(result.value);
        let inner_ty = result.ty.io_inner_type();
        let inner_display = format_result_value(
            inner_val,
            &inner_ty,
            session.type_defs(),
            session.type_modules(),
        );
        let value_part = extract_value_from_display(&inner_display);
        let inner_type_str = extract_type_from_display(&inner_display);
        format!(":(IO {inner_type_str}) (IO.Pure {value_part})")
    } else {
        format_result_value(result.value, &result.ty, session.type_defs(), session.type_modules())
    }
}

/// Extract the type string from a `:Type value` display string.
///
/// Handles both simple types (`:primitives/Int`) and parenthesized types
/// (`:(Fn [a] a)`, `:(Option primitives/Int)`).
fn extract_type_from_display(display: &str) -> &str {
    if !display.starts_with(':') {
        return display;
    }
    if display.starts_with(":(") {
        // Parenthesized type: find the matching ')' by counting parens.
        let mut depth = 0;
        for (i, ch) in display[1..].char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        // Type is display[1..1+i+1], i.e. the parenthesized expression.
                        return &display[1..i + 2];
                    }
                }
                _ => {}
            }
        }
        // Malformed: return everything after ':'
        &display[1..]
    } else {
        // Simple type: everything from ':' to first space.
        match display[1..].find(' ') {
            Some(pos) => &display[1..pos + 1],
            None => &display[1..],
        }
    }
}

/// Extract the value string from a `:Type value` display string.
///
/// Handles both simple types and parenthesized types.
fn extract_value_from_display(display: &str) -> &str {
    if !display.starts_with(':') {
        return display;
    }
    if display.starts_with(":(") {
        // Parenthesized type: find the matching ')' by counting parens in display[1..],
        // then the value follows after ') '.
        let mut depth = 0;
        for (i, ch) in display[1..].char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        // ')' is at display[1 + i]. Value starts after ') '.
                        let close_paren_pos = 1 + i; // position in display
                        let value_start = close_paren_pos + 2; // skip ') '
                        if value_start <= display.len() {
                            return &display[value_start..];
                        }
                        return "";
                    }
                }
                _ => {}
            }
        }
        display
    } else {
        // Simple type: value is everything after first space.
        match display.find(' ') {
            Some(pos) => &display[pos + 1..],
            None => display,
        }
    }
}
