//! Panic handler for JIT-compiled code.
//!
//! Because Cranelift JIT frames lack registered unwind tables, Rust's
//! `catch_unwind` cannot unwind through them. Instead of calling `panic!()`,
//! `runtime_panic` stores the error message in a thread-local and returns
//! a sentinel value (0). The host checks `take_runtime_error()` after every
//! JIT call to detect and report errors.
//!
//! ## Two-layer naming (`design/arch/test-discovery.md` §6)
//!
//! - [`take_runtime_error`] / [`set_runtime_error`] are the **internal Rust
//!   mechanism** — plain take-and-clear / set-if-empty over the thread-local
//!   error slot. They are NOT C-ABI exports and NOT language names. The
//!   combinator and the fork-join error-slot ferry (`ivar.rs`, `io.rs`) call
//!   them.
//! - [`catch_runtime_error`] (export name `catch-runtime-error`) is the
//!   **language-level** protected-call combinator. It invokes a thunk closure,
//!   reads-and-clears the slot, and marshals `(Ok result)` / `(Err message)`
//!   as a heap `Result` ADT. One body serves every `a` (uniform i64 ABI).

use std::cell::RefCell;

/// Offset of `code_ptr` within a closure (Decision 11).
/// Closure layout: `[header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]`
const CLOSURE_CODE_PTR_OFFSET: isize = 16;

/// Heap-ADT tag offset (after the 16-byte alloc header).
const ADT_TAG_OFFSET: isize = 16;
/// Heap-ADT first-field offset.
const ADT_FIELD_0_OFFSET: isize = 24;

/// `Result` constructor tags — declaration order `(Ok …) (Err …)` (matches the
/// `primitives` bootstrap seeding, modelled on `Option`'s `None`/`Some`).
const RESULT_TAG_OK: i64 = 0;
const RESULT_TAG_ERR: i64 = 1;

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
#[unsafe(export_name = "runtime/panic")]
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

/// Set a runtime error into the calling thread's slot, **first-error-wins**.
///
/// The companion to [`take_runtime_error`]. The fork-join error-slot ferry
/// (`ivar.rs`, `io.rs`) uses this to re-raise a worker thread's panic into the
/// joining thread's slot. If the slot is already occupied, the existing message
/// is kept (the first error aborts the whole expression — sequential semantics,
/// `design/arch/test-discovery.md` §"the fork-join error-slot ferry obligation").
/// It is internal Rust, not a C-ABI export and not a language name.
pub fn set_runtime_error(msg: String) {
    RUNTIME_ERROR.with(|cell| {
        let mut slot = cell.borrow_mut();
        if slot.is_none() {
            *slot = Some(msg);
        }
    });
}

/// `catch-runtime-error` — the language-level protected-call combinator
/// (`design/arch/test-discovery.md` §5/§6).
///
/// Signature `forall a. (Fn [(Fn [] a)] (Result a String))`. One Rust body
/// serves every `a` because every Cranelisp value is a uniform `i64` at the ABI.
///
/// Body:
/// 1. clear any stale error (`take_runtime_error()` discard);
/// 2. load `code_ptr` from the thunk closure (offset `CLOSURE_CODE_PTR_OFFSET`)
///    and call `extern "C" fn(env_ptr) -> i64` with the closure pointer as
///    `env_ptr` (the `io::call_continuation` / `ivar::ivar_force` precedent —
///    every `(fn [] …)` thunk is a closure, even with zero captures);
/// 3. read the slot via `take_runtime_error()`;
/// 4. `Some(msg)` → heap `(Err message)`; `None` → heap `(Ok result)`. Both
///    `Result` variants carry data, so both are heap ADTs `[header | tag | field]`.
///
/// Under live lenient/Par evaluation the bracket stays a plain own-thread
/// slot-reader: the fork-join error-slot ferry (`ivar.rs`/`io.rs`) re-raises any
/// worker error into this thread's slot before control returns to the
/// combinator's synchronous frame (structured fork-join — every spark joins
/// inside the bracket's dynamic extent).
///
/// # Safety
///
/// `thunk_closure` must be a valid base pointer to a zero-arg HeapClosure whose
/// `code_ptr` has signature `extern "C" fn(env_ptr: i64) -> i64`.
#[unsafe(export_name = "catch-runtime-error")]
#[allow(clippy::not_unsafe_ptr_arg_deref)] // Called from JIT code; cannot be marked unsafe.
pub extern "C" fn catch_runtime_error(thunk_closure: i64) -> i64 {
    // 1. Clear any stale error so we observe only this thunk's panic.
    let _ = take_runtime_error();

    // 2. Load code_ptr from the thunk closure and call it with the closure
    //    pointer itself as env_ptr.
    // SAFETY: caller guarantees `thunk_closure` is a valid zero-arg closure
    // base pointer; the code_ptr lives at CLOSURE_CODE_PTR_OFFSET.
    let code_ptr =
        unsafe { *((thunk_closure as isize + CLOSURE_CODE_PTR_OFFSET) as *const i64) };
    let call: extern "C" fn(i64) -> i64 =
        unsafe { std::mem::transmute(code_ptr as *const ()) };
    let result = call(thunk_closure);

    // 3. Read-and-clear the slot (covers both this thread's panic and any
    //    worker error ferried into it by the join paths).
    // 4. Marshal the Result ADT.
    match take_runtime_error() {
        Some(msg) => {
            // A panic crossed the bracket. If it crossed an actively-tracing
            // `(trace …)` body, the trace guard would otherwise stay stuck and
            // the next same-thread trace would spuriously raise "nested trace"
            // (test-discovery.md §5 scope item 5 / 0258 NOTE-2). Both are
            // intrinsics-owned thread-locals, so the cleanup is in-crate.
            crate::trace::clear_trace_guard_on_panic();
            let msg_ptr = crate::heap_string::alloc_string(msg.as_bytes()) as i64;
            alloc_result(RESULT_TAG_ERR, msg_ptr)
        }
        None => alloc_result(RESULT_TAG_OK, result),
    }
}

/// Allocate a single-field heap `Result` ADT `[header | tag | field0]`.
fn alloc_result(tag: i64, field0: i64) -> i64 {
    // 16 bytes payload: tag(8) + field0(8); allocator prepends the 16-byte header.
    let base = crate::alloc::alloc_with_rc(16) as isize;
    // SAFETY: `base` is a valid allocation of header + 16 payload bytes; tag at
    // offset 16 and field0 at offset 24 are within bounds and 8-byte aligned.
    unsafe {
        *((base + ADT_TAG_OFFSET) as *mut i64) = tag;
        *((base + ADT_FIELD_0_OFFSET) as *mut i64) = field0;
    }
    base as i64
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

    // spec: 12-runtime §12.4.3 — set_runtime_error stores into an empty slot
    #[test]
    fn test_set_runtime_error_empty_slot() {
        let _ = take_runtime_error(); // clear
        set_runtime_error("ferried error".to_string());
        let err = take_runtime_error();
        assert_eq!(err.as_deref(), Some("ferried error"));
    }

    // spec: 12-runtime §12.4.3 — set_runtime_error is first-error-wins
    #[test]
    fn test_set_runtime_error_first_error_wins() {
        let _ = take_runtime_error(); // clear
        set_runtime_error("first".to_string());
        set_runtime_error("second".to_string());
        // The first error is kept; the second is dropped.
        assert_eq!(take_runtime_error().as_deref(), Some("first"));
    }

    /// Build a zero-arg closure whose body returns a captured constant.
    /// Layout: `[header(16) | code_ptr(8) | drop_glue_ptr(8) | capture(8)]`.
    fn make_const_thunk(value: i64) -> i64 {
        extern "C" fn const_fn(env_ptr: i64) -> i64 {
            unsafe { *((env_ptr as isize + 32) as *const i64) }
        }
        let base = crate::alloc::alloc_with_rc(24);
        unsafe {
            *((base as isize + 16) as *mut i64) = const_fn as *const () as i64;
            *((base as isize + 24) as *mut i64) = 0; // drop glue
            *((base as isize + 32) as *mut i64) = value;
        }
        base as i64
    }

    /// Build a zero-arg closure whose body raises a runtime panic and returns 0.
    fn make_panicking_thunk() -> i64 {
        extern "C" fn boom_fn(_env_ptr: i64) -> i64 {
            let msg = "boom";
            runtime_panic(msg.as_ptr(), msg.len());
            0
        }
        let base = crate::alloc::alloc_with_rc(16);
        unsafe {
            *((base as isize + 16) as *mut i64) = boom_fn as *const () as i64;
            *((base as isize + 24) as *mut i64) = 0; // drop glue
        }
        base as i64
    }

    // spec: 12-runtime §12.7.2 — a passing thunk yields (Ok result)
    #[test]
    fn test_catch_runtime_error_ok() {
        let _ = take_runtime_error();
        let thunk = make_const_thunk(99);
        let res = catch_runtime_error(thunk);
        unsafe {
            let tag = *((res as isize + ADT_TAG_OFFSET) as *const i64);
            let field0 = *((res as isize + ADT_FIELD_0_OFFSET) as *const i64);
            assert_eq!(tag, RESULT_TAG_OK, "passing thunk must yield Ok");
            assert_eq!(field0, 99, "Ok payload must be the thunk result");
        }
        // Slot left clean after the call.
        assert!(take_runtime_error().is_none(), "slot must be clean after Ok");
        unsafe { crate::alloc::dealloc(res as *mut u8) };
        unsafe { crate::alloc::dealloc(thunk as *mut u8) };
    }

    // spec: 12-runtime §12.7.2 — a panicking thunk yields (Err message)
    #[test]
    fn test_catch_runtime_error_err() {
        let _ = take_runtime_error();
        let thunk = make_panicking_thunk();
        let res = catch_runtime_error(thunk);
        unsafe {
            let tag = *((res as isize + ADT_TAG_OFFSET) as *const i64);
            assert_eq!(tag, RESULT_TAG_ERR, "panicking thunk must yield Err");
            // field0 is a heap String ptr; non-null and above the nullary threshold.
            let field0 = *((res as isize + ADT_FIELD_0_OFFSET) as *const i64);
            assert!(field0 != 0, "Err payload must be a heap String ptr");
        }
        // Slot left clean — the combinator consumed the error.
        assert!(
            take_runtime_error().is_none(),
            "slot must be clean after the combinator consumes the panic"
        );
        // Free the Err string then the Result, then the thunk.
        unsafe {
            let field0 = *((res as isize + ADT_FIELD_0_OFFSET) as *const i64);
            crate::alloc::dealloc(field0 as *mut u8);
            crate::alloc::dealloc(res as *mut u8);
            crate::alloc::dealloc(thunk as *mut u8);
        }
    }

    // spec: 12-runtime §12.7.2 — the combinator clears a stale error before
    // running the thunk, so a prior thread error does not leak into the result.
    #[test]
    fn test_catch_runtime_error_clears_stale() {
        let _ = take_runtime_error();
        // Pollute the slot before the call.
        set_runtime_error("stale".to_string());
        let thunk = make_const_thunk(7);
        let res = catch_runtime_error(thunk);
        unsafe {
            let tag = *((res as isize + ADT_TAG_OFFSET) as *const i64);
            assert_eq!(tag, RESULT_TAG_OK, "stale error must not produce Err");
        }
        unsafe { crate::alloc::dealloc(res as *mut u8) };
        unsafe { crate::alloc::dealloc(thunk as *mut u8) };
    }
}
