//! Panic handler for JIT-compiled code.
//!
//! Because Cranelift JIT frames lack registered unwind tables, Rust's
//! `catch_unwind` cannot unwind through them. Instead of calling `panic!()`,
//! `runtime_panic` stores the error message in a thread-local and returns
//! a sentinel value (0). The host checks `take_runtime_error()` after every
//! JIT call to detect and report errors.

use std::cell::RefCell;

thread_local! {
    static RUNTIME_ERROR: RefCell<Option<String>> = const { RefCell::new(None) };
}

/// Set a runtime error from JIT-compiled code.
///
/// Stores the error message in a thread-local and returns. The JIT function
/// will return 0 (the sentinel) and the host MUST call `take_runtime_error()`
/// to check for errors after every JIT invocation.
///
/// # Safety
///
/// `msg_ptr` must point to a valid UTF-8 byte sequence of length `msg_len`,
/// or be null (in which case a default message is used).
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)] // Called from JIT code; cannot be marked unsafe
pub extern "C" fn runtime_panic(msg_ptr: *const u8, msg_len: usize) {
    let msg = if msg_ptr.is_null() || msg_len == 0 {
        "match exhaustiveness failure"
    } else {
        // SAFETY: caller guarantees msg_ptr points to valid UTF-8 of length msg_len
        unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(msg_ptr, msg_len)) }
    };
    RUNTIME_ERROR.with(|cell| {
        *cell.borrow_mut() = Some(format!("runtime panic: {msg}"));
    });
}

/// Check and take the last runtime error, if any.
///
/// Returns `Some(message)` if `runtime_panic` was called during the last JIT
/// invocation, clearing the error. Returns `None` if no error occurred.
pub fn take_runtime_error() -> Option<String> {
    RUNTIME_ERROR.with(|cell| cell.borrow_mut().take())
}

#[cfg(test)]
mod tests {
    use super::*;

    // spec: 12-runtime §12.7.2 — runtime panic with custom message
    #[test]
    fn test_panic_with_message() {
        let msg = "test panic message";
        runtime_panic(msg.as_ptr(), msg.len());
        let err = take_runtime_error();
        assert!(err.is_some());
        assert!(err.unwrap().contains("test panic message"));
    }

    // spec: 12-runtime §12.7.2 — null pointer panic defaults to "match exhaustiveness failure"
    #[test]
    fn test_panic_with_null_ptr() {
        runtime_panic(std::ptr::null(), 0);
        let err = take_runtime_error();
        assert!(err.is_some());
        assert!(err.unwrap().contains("match exhaustiveness failure"));
    }

    // spec: 12-runtime §12.7.2 — zero-length message panic
    #[test]
    fn test_panic_with_empty_len() {
        let msg = "ignored";
        runtime_panic(msg.as_ptr(), 0);
        let err = take_runtime_error();
        assert!(err.is_some());
    }

    // spec: 12-runtime §12.7.2 — take clears the error
    #[test]
    fn test_take_clears_error() {
        let msg = "clear test";
        runtime_panic(msg.as_ptr(), msg.len());
        assert!(take_runtime_error().is_some());
        assert!(take_runtime_error().is_none());
    }

    // spec: 12-runtime §12.7.2 — no error when no panic
    #[test]
    fn test_no_error_by_default() {
        // Clear any prior state
        let _ = take_runtime_error();
        assert!(take_runtime_error().is_none());
    }
}
