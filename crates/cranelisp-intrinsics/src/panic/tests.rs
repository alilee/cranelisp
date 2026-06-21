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

// spec: design/arch/bounded-contexts.md §4b invariant 14 — the dispatch
// fault slot round-trips a captured fault for int to compose.
#[test]
fn test_dispatch_fault_set_take_roundtrip() {
    let _ = take_dispatch_fault(); // clear
    set_dispatch_fault(DispatchFault {
        fn_name: "stdio/read-line".to_string(),
        cause: "device unavailable".to_string(),
    });
    let fault = take_dispatch_fault().expect("fault present");
    assert_eq!(fault.fn_name, "stdio/read-line");
    assert_eq!(fault.cause, "device unavailable");
    // take clears the slot.
    assert!(take_dispatch_fault().is_none());
}

// spec: design/arch/bounded-contexts.md §4b invariant 14 — the dispatch
// fault slot is first-fault-wins (sequential abort semantics).
#[test]
fn test_dispatch_fault_first_fault_wins() {
    let _ = take_dispatch_fault();
    set_dispatch_fault(DispatchFault {
        fn_name: "a".to_string(),
        cause: "first".to_string(),
    });
    set_dispatch_fault(DispatchFault {
        fn_name: "b".to_string(),
        cause: "second".to_string(),
    });
    let fault = take_dispatch_fault().expect("fault present");
    assert_eq!(fault.fn_name, "a", "first fault is kept");
    assert_eq!(fault.cause, "first");
}

// spec: spec/12-runtime.md §12.7.4.2 — the `--link` runtime-error gate
// (FIXME 0399) drains the slot message the startup stub prints. The thin
// export wraps this with an `exit(1)`; the helper is the testable half.
#[test]
fn test_drain_runtime_error_message_surfaces_and_clears() {
    let _ = take_runtime_error(); // clear
    let msg = "division by zero";
    runtime_panic(msg.as_ptr(), msg.len());
    let drained = drain_runtime_error_message();
    assert!(
        drained.as_deref().is_some_and(|m| m.contains("division by zero")),
        "the --link gate must surface the panic message (got {drained:?})"
    );
    // Draining clears the slot — the stub exits, but a clean re-read is None.
    assert!(
        drain_runtime_error_message().is_none(),
        "the gate must clear the slot after surfacing the message"
    );
}

// spec: spec/12-runtime.md §12.7.4.2 — a clean run leaves nothing to drain,
// so the `--link` gate returns and `main`'s result proceeds (no spurious
// exit). The negative half of the FIXME 0399 gate.
#[test]
fn test_drain_runtime_error_message_none_on_clean_run() {
    let _ = take_runtime_error(); // clear
    assert!(
        drain_runtime_error_message().is_none(),
        "no runtime error => the gate must not surface anything"
    );
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

// ---------------------------------------------------------------------
// FIXME 0366 — the unified program driver `cranelisp_run_program`. The
// driver owns the clear→call→pre-IO-peek→trampoline→post-IO-peek sequence
// and returns a `ProgramOutcome` WITHOUT exiting and WITHOUT clearing the
// slots. These tests assert the four outcome cases + the "slot left SET, no
// exit" contract the callers depend on.
// ---------------------------------------------------------------------

/// A clean non-IO `main` returning a constant. `extern "C" fn() -> i64`.
extern "C" fn main_returns_7() -> i64 {
    7
}

/// A non-IO `main` that raises a runtime panic and returns the panic-path
/// sentinel `0` (the `emit_panic_return` shape — set slot, return 0).
extern "C" fn main_panics() -> i64 {
    let msg = "boom in main";
    runtime_panic(msg.as_ptr(), msg.len());
    0
}

/// A non-IO `main` that captures a platform-dispatch fault (modelling a
/// fault captured during `main` evaluation) and returns the sentinel `0`.
extern "C" fn main_dispatch_faults() -> i64 {
    set_dispatch_fault(DispatchFault {
        fn_name: "stdio/read-line".to_string(),
        cause: "device unavailable".to_string(),
    });
    0
}

/// A `main` returning an IO `Pure(42)` node base pointer. Layout
/// `[header(16) | tag=PURE(8) | value(8)]`; the driver forces it via the IO
/// trampoline and reduces to the inner value.
extern "C" fn main_returns_io_pure() -> i64 {
    let base = crate::alloc::alloc_with_rc(16);
    unsafe {
        // tag at offset 16 = IO_TAG_PURE (0); value at offset 24.
        *((base as isize + 16) as *mut i64) = cranelisp_platform::IO_TAG_PURE;
        *((base as isize + 24) as *mut i64) = 42;
    }
    base as i64
}

/// A `main` returning an IO `bind (Pure 1) (fn [_] <panic; sentinel 0>)`
/// tree — the panic fires INSIDE the trampoline (during-IO case, FIXME 0401).
extern "C" fn main_returns_io_bind_panic() -> i64 {
    // Inner Pure(1).
    let inner = {
        let b = crate::alloc::alloc_with_rc(16);
        unsafe {
            *((b as isize + 16) as *mut i64) = cranelisp_platform::IO_TAG_PURE;
            *((b as isize + 24) as *mut i64) = 1;
        }
        b as i64
    };
    // Panicking continuation closure.
    extern "C" fn panic_cont(_env: i64, _val: i64) -> i64 {
        let msg = "division by zero";
        runtime_panic(msg.as_ptr(), msg.len());
        0 // panic-path sentinel — NOT a valid IO node
    }
    let cont = {
        let b = crate::alloc::alloc_with_rc(16);
        unsafe {
            *((b as isize + 16) as *mut i64) = panic_cont as *const () as i64;
            *((b as isize + 24) as *mut i64) = 0; // drop glue
        }
        b as i64
    };
    // Bind node [header | tag=BIND | inner | cont].
    let bind = crate::alloc::alloc_with_rc(24);
    unsafe {
        *((bind as isize + 16) as *mut i64) = cranelisp_platform::IO_TAG_BIND;
        *((bind as isize + 24) as *mut i64) = inner;
        *((bind as isize + 32) as *mut i64) = cont;
    }
    bind as i64
}

// spec: spec/12-runtime.md §12.7.4.2 — a clean non-IO main yields a clean
// outcome carrying main's result; no slot is touched.
#[test]
fn run_program_clean_non_io() {
    let _ = take_runtime_error();
    let _ = take_dispatch_fault();
    let outcome = cranelisp_run_program(main_returns_7 as *const u8, false);
    assert_eq!(outcome.error_kind, OUTCOME_CLEAN, "clean run");
    assert_eq!(outcome.exit_code, 7, "exit_code is main's result");
    assert!(take_runtime_error().is_none(), "no runtime error slot set");
    assert!(take_dispatch_fault().is_none(), "no dispatch fault slot set");
}

// spec: spec/12-runtime.md §12.7.4.2 — a clean IO main is forced through the
// trampoline and the outcome carries the inner IO value.
#[test]
fn run_program_clean_io_reduces_to_inner_value() {
    let _ = take_runtime_error();
    let _ = take_dispatch_fault();
    let outcome = cranelisp_run_program(main_returns_io_pure as *const u8, true);
    assert_eq!(outcome.error_kind, OUTCOME_CLEAN, "clean IO run");
    assert_eq!(outcome.exit_code, 42, "exit_code is the inner Pure value");
    assert!(take_runtime_error().is_none());
    assert!(take_dispatch_fault().is_none());
}

// spec: spec/12-runtime.md §12.7.4.2 — a panic during `main` evaluation
// (pre-IO, FIXME 0399) yields error_kind=1 and LEAVES the runtime-error slot
// SET (the driver peeks, never takes; the caller drains). The driver does NOT
// exit and does NOT reach the trampoline.
#[test]
fn run_program_pre_io_panic_leaves_slot_set() {
    let _ = take_runtime_error();
    let _ = take_dispatch_fault();
    // main_returns_io=true so we also prove the pre-IO peek stops BEFORE the
    // trampoline (forcing sentinel 0 would null-deref).
    let outcome = cranelisp_run_program(main_panics as *const u8, true);
    assert_eq!(outcome.error_kind, OUTCOME_RUNTIME_ERROR, "pre-IO runtime error");
    // The slot is left SET — the caller is the surfacing point.
    let drained = take_runtime_error();
    assert!(
        drained.as_deref().is_some_and(|m| m.contains("boom in main")),
        "runtime-error slot left SET with the panic message (got {drained:?})"
    );
    assert!(take_dispatch_fault().is_none());
}

// spec: spec/12-runtime.md §12.7.4.2 — a panic raised DURING the IO
// trampoline (inside a `bind` continuation, FIXME 0401) yields error_kind=1
// and LEAVES the runtime-error slot SET. The driver must NOT SIGSEGV.
#[test]
fn run_program_during_io_panic_leaves_slot_set() {
    let _ = take_runtime_error();
    let _ = take_dispatch_fault();
    let outcome = cranelisp_run_program(main_returns_io_bind_panic as *const u8, true);
    assert_eq!(outcome.error_kind, OUTCOME_RUNTIME_ERROR, "during-IO runtime error");
    let drained = take_runtime_error();
    assert!(
        drained.as_deref().is_some_and(|m| m.contains("division by zero")),
        "runtime-error slot left SET with the continuation panic (got {drained:?})"
    );
    assert!(take_dispatch_fault().is_none());
}

// spec: design/arch/bounded-contexts.md §4b invariant 14 — a platform
// dispatch fault captured during `main` yields error_kind=2 and LEAVES the
// dispatch-fault slot SET for the caller to compose into
// `PlatformError::DispatchError`. No exit; the runtime-error slot is clean.
#[test]
fn run_program_dispatch_fault_leaves_slot_set() {
    let _ = take_runtime_error();
    let _ = take_dispatch_fault();
    let outcome = cranelisp_run_program(main_dispatch_faults as *const u8, false);
    assert_eq!(outcome.error_kind, OUTCOME_DISPATCH_FAULT, "dispatch fault");
    // The dispatch-fault slot is left SET; the runtime-error slot is empty.
    assert!(take_runtime_error().is_none(), "no runtime-error slot set");
    let fault = take_dispatch_fault().expect("dispatch-fault slot left SET");
    assert_eq!(fault.fn_name, "stdio/read-line");
    assert_eq!(fault.cause, "device unavailable");
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
