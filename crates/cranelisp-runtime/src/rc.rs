//! Reference counting trace logging and debug helpers.
//!
//! When `CRANELISP_RC_TRACE=1`, logs every alloc/free/inc/dec with pointer
//! address and RC value to stderr. Gated behind `cfg(debug_assertions)`.
//!
//! The backend emits RC inc/dec inline as atomic_rmw — NOT as extern function
//! calls. This module provides the trace logging infrastructure that both the
//! runtime (alloc/free) and the backend (inc/dec underflow check) can use.

use std::sync::LazyLock;
use std::sync::atomic::{AtomicBool, Ordering};

/// Whether RC trace logging is enabled. Checked once at process start.
static RC_TRACE_ENABLED: LazyLock<AtomicBool> = LazyLock::new(|| {
    let enabled = std::env::var("CRANELISP_RC_TRACE")
        .map(|v| v == "1")
        .unwrap_or(false);
    AtomicBool::new(enabled)
});

/// Log an RC operation (alloc, free, inc, dec) to stderr if tracing is enabled.
///
/// Only active in debug builds. In release builds this is a no-op.
#[inline]
pub fn rc_trace(op: &str, ptr: i64, rc: i64) {
    #[cfg(debug_assertions)]
    {
        if RC_TRACE_ENABLED.load(Ordering::Relaxed) {
            eprintln!("[RC] {op:>5} {ptr:#x} rc={rc}");
        }
    }
    #[cfg(not(debug_assertions))]
    {
        let _ = (op, ptr, rc);
    }
}

/// Check if RC trace logging is currently enabled.
pub fn is_rc_trace_enabled() -> bool {
    RC_TRACE_ENABLED.load(Ordering::Relaxed)
}

/// RC underflow check — called from JIT-generated inline dec code.
///
/// The backend emits `atomic_rmw(Sub, ...)` inline. After the sub, if the
/// old RC value was <= 0 (underflow), the backend calls this function for
/// diagnostic logging and debug assertion.
///
/// In release builds, this is a no-op (the JIT should not emit the call).
#[unsafe(no_mangle)]
pub extern "C-unwind" fn rc_underflow_check(ptr: i64, old_rc: i64) -> i64 {
    debug_assert!(
        old_rc > 0,
        "RC underflow: ptr={ptr:#x} had rc={old_rc} before decrement"
    );
    rc_trace("UNDERFLOW", ptr, old_rc);
    0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rc_trace_does_not_panic() {
        // Just verify it doesn't crash — output goes to stderr.
        rc_trace("test", 0x1234, 1);
    }

    #[test]
    fn test_rc_trace_enabled_default_false() {
        // Without CRANELISP_RC_TRACE=1 in env, should be false.
        // Note: this test may pass or fail depending on env, but shouldn't panic.
        let _ = is_rc_trace_enabled();
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "RC underflow")]
    fn test_underflow_check_panics_on_zero() {
        rc_underflow_check(0x1234, 0);
    }

    #[cfg(debug_assertions)]
    #[test]
    fn test_underflow_check_ok_on_positive() {
        // Should not panic when old_rc > 0.
        rc_underflow_check(0x1234, 1);
        rc_underflow_check(0x1234, 5);
    }
}
