//! Panic handler for JIT-compiled code.
//!
//! Called when a match expression hits a non-exhaustive case at runtime.
//! Uses `extern "C-unwind"` so the host can catch this via `std::panic::catch_unwind`.

/// Panic with a message from JIT-compiled code.
///
/// # Safety
///
/// `msg_ptr` must point to a valid UTF-8 byte sequence of length `msg_len`,
/// or be null (in which case a default message is used).
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)] // Called from JIT code; cannot be marked unsafe
pub extern "C-unwind" fn runtime_panic(msg_ptr: *const u8, msg_len: usize) {
    let msg = if msg_ptr.is_null() || msg_len == 0 {
        "match exhaustiveness failure"
    } else {
        // SAFETY: caller guarantees msg_ptr points to valid UTF-8 of length msg_len
        unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(msg_ptr, msg_len)) }
    };
    panic!("cranelisp runtime: {msg}");
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::panic;

    // spec: 12-runtime §12.7.2 — runtime panic with custom message
    #[test]
    fn test_panic_with_message() {
        let result = panic::catch_unwind(|| {
            let msg = "test panic message";
            runtime_panic(msg.as_ptr(), msg.len());
        });
        assert!(result.is_err());
        let err = result.unwrap_err();
        let msg = err.downcast_ref::<String>().unwrap();
        assert!(msg.contains("test panic message"));
    }

    // spec: 12-runtime §12.7.2 — null pointer panic defaults to "match exhaustiveness failure"
    #[test]
    fn test_panic_with_null_ptr() {
        let result = panic::catch_unwind(|| {
            runtime_panic(std::ptr::null(), 0);
        });
        assert!(result.is_err());
        let err = result.unwrap_err();
        let msg = err.downcast_ref::<String>().unwrap();
        assert!(msg.contains("match exhaustiveness failure"));
    }

    // spec: 12-runtime §12.7.2 — zero-length message panic
    #[test]
    fn test_panic_with_empty_len() {
        let result = panic::catch_unwind(|| {
            let msg = "ignored";
            runtime_panic(msg.as_ptr(), 0);
        });
        assert!(result.is_err());
    }

    // spec: 12-runtime §12.7.2 — runtime panic is catchable via catch_unwind
    #[test]
    fn test_panic_is_catchable() {
        let result = panic::catch_unwind(|| {
            let msg = "catchable";
            runtime_panic(msg.as_ptr(), msg.len());
        });
        assert!(result.is_err(), "panic should be catchable via catch_unwind");
    }
}
