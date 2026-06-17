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
    static DISPATCH_FAULT: RefCell<Option<DispatchFault>> = const { RefCell::new(None) };
}

/// A platform-dispatch fault captured by the IO trampoline's fault guard
/// (`crate::io`, FIXME 0327 — the dispatch funnel, step 3).
///
/// This is the **intrinsics-internal fault outcome** the guard produces when a
/// platform Effect thunk faults (Rust panic OR SIGFPE/SIGILL/SIGBUS/SIGSEGV).
/// Intrinsics is diagnostics-free by charter (BC §4b) — it does NOT construct a
/// `PlatformError`. Instead the guard sets this carrier on a thread-local slot
/// via [`set_dispatch_fault`] and int reads it via [`take_dispatch_fault`] and
/// composes `PlatformError::DispatchError { fn_name, cause, location }` at its
/// runtime-error surface (the two-layer split that [`catch_runtime_error`] and
/// `invoke_jit_protected` already use: intrinsics sets the slot, int reads +
/// composes).
///
/// The `fn_name` is read from the faulting Effect node's fourth field (the
/// backend-baked NUL-terminated C-string, ABI v4); a node the backend did not
/// stamp carries `"<unknown>"`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DispatchFault {
    /// The cranelisp-level platform fn name, read from the Effect node's baked
    /// field-3 handle (or `"<unknown>"` when the handle is null).
    pub fn_name: String,
    /// The fault cause message (the panic payload, signal description, or the
    /// `runtime_panic` slot message captured during the thunk force).
    pub cause: String,
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

/// Set a captured platform-dispatch fault into the calling thread's slot,
/// **first-fault-wins**.
///
/// The IO trampoline's fault guard (`crate::io`) calls this when a platform
/// Effect thunk faults. The companion to [`take_dispatch_fault`]. If the slot
/// is already occupied (an earlier fault on this thread), the existing fault is
/// kept — the first fault aborts the expression (sequential semantics, matching
/// [`set_runtime_error`]). It is internal Rust → int signalling, not a C-ABI
/// export and not a language name.
pub fn set_dispatch_fault(fault: DispatchFault) {
    DISPATCH_FAULT.with(|cell| {
        let mut slot = cell.borrow_mut();
        if slot.is_none() {
            *slot = Some(fault);
        }
    });
}

/// Check and take the last platform-dispatch fault, if any.
///
/// int calls this at its runtime-error surface (after forcing an IO tree) to
/// detect a fault the trampoline's guard captured, then composes
/// `PlatformError::DispatchError` from the carried `fn_name` + `cause`. Returns
/// `Some(fault)` and clears the slot, or `None` if no dispatch fault occurred.
pub fn take_dispatch_fault() -> Option<DispatchFault> {
    DISPATCH_FAULT.with(|cell| cell.borrow_mut().take())
}

/// Non-clearing PEEK of the runtime-error slot (FIXME 0401).
///
/// Returns `true` when [`runtime_panic`] (or the fork-join ferry via
/// [`set_runtime_error`]) populated the slot, WITHOUT taking it. The IO
/// trampoline (`crate::io`) calls this after running a continuation's user code:
/// when a runtime error is pending it stops the walk and returns the sentinel,
/// leaving the slot SET so the **host** (`--run`'s `session_v4::trampoline` /
/// `--link`'s `cranelisp_check_runtime_error`) is the single surfacing point.
/// If the trampoline took the slot here it would trade the SIGSEGV for a silent
/// swallow (clean exit, no message) — the peek is non-clearing by design.
pub(crate) fn has_runtime_error() -> bool {
    RUNTIME_ERROR.with(|cell| cell.borrow().is_some())
}

/// Non-clearing PEEK of the dispatch-fault slot (FIXME 0401).
///
/// The companion to [`has_runtime_error`] for the platform-dispatch-fault slot.
/// The trampoline stops the walk on a pending fault, leaving it SET for the host
/// to compose into `PlatformError::DispatchError`. Non-clearing for the same
/// reason: the host is the surfacing point, not the trampoline.
pub(crate) fn has_dispatch_fault() -> bool {
    DISPATCH_FAULT.with(|cell| cell.borrow().is_some())
}

/// Drain the runtime-error slot and format the message the `--link` startup
/// stub prints, if any (the testable half of [`cranelisp_check_runtime_error`]).
///
/// Returns `Some(message)` when [`runtime_panic`] (or the fork-join ferry via
/// [`set_runtime_error`]) populated the slot during `main`, clearing it; `None`
/// when no runtime error occurred. The slot already carries the `"runtime
/// panic: …"` prefix (set by [`runtime_panic`]), so the returned string matches
/// the `--run` host's slot read (`src/pipeline.rs` / `src/session_v4.rs`) —
/// keeping the two run modes' surfaced text identical.
///
/// Factored out of the export so it is unit-testable without the
/// `std::process::exit` in the thin wrapper. `pub(crate)` — the testable seam
/// of the startup gate, not a cross-crate surface item (the export is the only
/// public surface; int/backend reach it by `Linkage::Import` symbol name).
pub(crate) fn drain_runtime_error_message() -> Option<String> {
    take_runtime_error()
}

/// The terminal outcome of running a program's `main` (+ optional IO
/// trampoline) — the single C-ABI carrier both run modes read (FIXME 0366).
///
/// `cranelisp_run_program` returns this; it does NOT `exit` and does NOT clear
/// the error slots. Callers drain the slots themselves (the `--link` stub via
/// [`cranelisp_check_runtime_error`], the `--run` host via [`take_runtime_error`]
/// / [`take_dispatch_fault`]) and decide how to surface the error and what exit
/// code to use. This keeps the host REPL-safe (no `process::exit` inside the
/// driver) and keeps the error TEXT in the thread-local slots (no string
/// marshalling across the C-ABI).
///
/// `#[repr(C)]` carrier (Principle 14 — FFI layout discipline): an
/// intrinsics-local boundary type, named only by the `--link` startup stub
/// (`src/exe.rs`) and the `--run` host (`src/session_v4.rs`). NOT a
/// `cranelisp-types` boundary type.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProgramOutcome {
    /// The reduced terminal result — the inner IO value when `main` returns IO,
    /// or `main`'s own result otherwise. The `--link` stub `exit()`s with the
    /// `i32`-truncation of this; the `--run` host reads it as the inner value
    /// and applies its own type-driven exit-code reduction.
    pub exit_code: i64,
    /// `0` = clean run (no error; slots empty).
    /// `1` = runtime error (the runtime-error slot is SET — drain it for text).
    /// `2` = platform-dispatch fault (the dispatch-fault slot is SET — drain it
    /// for the `(fn_name, cause)` the host composes into
    /// `PlatformError::DispatchError`).
    ///
    /// On a non-zero kind the relevant slot is left SET (the driver peeks, never
    /// takes) so the caller is the single surfacing point.
    pub error_kind: i32,
}

/// `error_kind` values for [`ProgramOutcome`].
const OUTCOME_CLEAN: i32 = 0;
const OUTCOME_RUNTIME_ERROR: i32 = 1;
const OUTCOME_DISPATCH_FAULT: i32 = 2;

/// The single program driver both run modes call (FIXME 0366).
///
/// Owns the whole shareable core — *everything between "main is callable" and
/// "the program's terminal result is known"*:
///
/// 1. clear any stale runtime error (`take_runtime_error()` discard);
/// 2. transmute `main_ptr` to `extern "C" fn() -> i64` and call it;
/// 3. **pre-IO** slot peek: if `main` raised a runtime error or dispatch fault,
///    stop here and return the outcome with the slot left SET (forcing the
///    panic-path sentinel `0` through the IO trampoline would null-deref —
///    FIXME 0399);
/// 4. if `main_returns_io`, force the IO task tree via the shared
///    [`crate::io::run_io_trampoline`] and release the caller's tree via
///    [`crate::drop::consume_io_tree`] (Decision 24 — the trampoline is
///    non-consuming of its input);
/// 5. **post-IO** slot peek: a runtime error or dispatch fault raised *during*
///    the trampoline (inside a `bind` continuation, or a faulting platform
///    Effect) leaves its slot SET and the trampoline returns the sentinel `0` —
///    return the outcome with the slot still SET (FIXME 0401).
///
/// Returns [`ProgramOutcome`] WITHOUT exiting and WITHOUT clearing the slots —
/// the caller drains and surfaces. This collapses the three former lockstep
/// slot-check points (pre-IO runtime-error, post-IO runtime-error, post-IO
/// dispatch-fault) — which were transcribed independently into the `--run` host
/// and the `--link` stub — into THIS one site (FIXME 0366).
///
/// # Safety
///
/// `main_ptr` must be a valid non-null pointer to a finalized zero-arg
/// `extern "C" fn() -> i64` (the compiled entry `main`). When `main_returns_io`
/// is true, `main`'s returned `i64` must be a valid IO-tree base pointer (rc > 0)
/// — or the panic-path sentinel `0`, which is caught by the pre-IO peek before
/// the trampoline dereferences it.
#[unsafe(export_name = "cranelisp_run_program")]
#[allow(clippy::not_unsafe_ptr_arg_deref)] // Called from the JIT host / link stub.
pub extern "C" fn cranelisp_run_program(
    main_ptr: *const u8,
    main_returns_io: bool,
) -> ProgramOutcome {
    // 1. Clear any stale runtime error so we observe only this run's panic.
    let _ = take_runtime_error();

    // 2. Call main.
    // SAFETY: caller guarantees `main_ptr` is a valid finalized zero-arg
    // `extern "C" fn() -> i64` (the contract of this fn's `# Safety`).
    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(main_ptr) };
    let main_result = func();

    // 3. Pre-IO peek: a panic during `main` evaluation leaves the slot SET and
    //    makes `main` return the panic-path sentinel `0`. Stop BEFORE the IO
    //    trampoline (forcing `0` through it would null-deref — FIXME 0399).
    if let Some(kind) = peek_error_kind() {
        return ProgramOutcome { exit_code: main_result, error_kind: kind };
    }

    // 4. IO trampoline (if main returns IO).
    let exit_code = if main_returns_io {
        let inner = crate::io::run_io_trampoline(main_result);
        // Decision 24: release the caller's tree (non-consuming trampoline).
        crate::drop::consume_io_tree(main_result);
        inner
    } else {
        main_result
    };

    // 5. Post-IO peek: a panic or dispatch fault raised DURING the trampoline
    //    (a `bind` continuation, or a faulting platform Effect) leaves its slot
    //    SET and the trampoline returns the sentinel `0` (FIXME 0401).
    if let Some(kind) = peek_error_kind() {
        return ProgramOutcome { exit_code, error_kind: kind };
    }

    ProgramOutcome { exit_code, error_kind: OUTCOME_CLEAN }
}

/// Non-clearing classification of the error slots for [`cranelisp_run_program`].
///
/// Returns the [`ProgramOutcome::error_kind`] discriminant for whichever slot is
/// SET (runtime-error wins over dispatch-fault, matching the host's former
/// check order), leaving the slot SET for the caller to drain; `None` when both
/// slots are empty (clean).
fn peek_error_kind() -> Option<i32> {
    if has_runtime_error() {
        Some(OUTCOME_RUNTIME_ERROR)
    } else if has_dispatch_fault() {
        Some(OUTCOME_DISPATCH_FAULT)
    } else {
        None
    }
}

/// `--link` startup-stub error-surfacing gate (FIXME 0399 / 0401 / 0366).
///
/// Since the FIXME 0366 program-driver unification, the linked startup stub
/// (`src/exe.rs::generate_startup_object`) calls this export at exactly ONE site
/// — immediately after the single `cranelisp_run_program` call, on a non-zero
/// `ProgramOutcome::error_kind`. `cranelisp_run_program` owns the whole
/// clear→call→drain-peek→trampoline→drain-peek sequence and leaves the SET slot
/// for this drain; this export is the stub's slot-printer + `exit(1)`.
///
/// On a runtime error this prints the slot message to stderr and `exit(1)`s — a
/// clean batch-mode exit matching `--run` (spec §12.7.4.2). It also drains the
/// platform-dispatch-fault slot ([`take_dispatch_fault`]): the linked binary has
/// no int runtime to compose a structured `PlatformError::DispatchError`, so it
/// surfaces the carried `(fn_name, cause)` directly. Because it drains BOTH slots
/// it surfaces the pre-IO case (panic during `main` evaluation, FIXME 0399) and
/// the during-IO case (panic/fault inside the trampoline, FIXME 0401) with the
/// same body — the driver already classified which slot is SET.
///
/// On a clean outcome the stub does NOT call this (it `exit()`s with the
/// `ProgramOutcome::exit_code` directly), so a clean run never reaches the drain.
///
/// It is force-linked into the produced binary via `cranelisp-exe-bundle`'s
/// `pub use cranelisp_intrinsics::panic` re-export, exactly like
/// `cranelisp_check_layout_hash`; backend/int declare it `Linkage::Import` and
/// never reference the Rust symbol directly. It is NOT in `intrinsics_table()`
/// (that catalog publishes user-code dispatch targets, not startup-stub calls).
#[unsafe(export_name = "cranelisp_check_runtime_error")]
pub extern "C" fn cranelisp_check_runtime_error() {
    if let Some(msg) = drain_runtime_error_message() {
        eprintln!("{msg}");
        std::process::exit(1);
    }
    // Adjacent twin: a platform-dispatch fault left SET by `cranelisp_run_program`
    // (the driver classified `error_kind == 2`) surfaces here rather than
    // null-deref through the trampoline.
    if let Some(fault) = take_dispatch_fault() {
        // The dispatch-fault TEXT format lives in TWO inherently-distinct
        // printers because intrinsics is diagnostics-free by charter (BC §4b)
        // and must not depend on `cranelisp-types`:
        //   - the `--run`/REPL host composes `PlatformError::DispatchError` and
        //     surfaces it through that enum's `Display` (`cranelisp-types`, the
        //     authoritative structured-error source);
        //   - this `--link` slot-printer, the ONLY copy of the format string in
        //     intrinsics, surfaces the carried `(fn_name, cause)` directly (the
        //     linked binary has no int runtime to inflate the structured error).
        // The FIXME 0366 unification removed every OTHER duplicate of the
        // surfacing SEQUENCE (the three lockstep slot-check points now live once
        // in `cranelisp_run_program`); this single format-string copy is the
        // irreducible residue of the diagnostics-free charter — it is kept here,
        // documented as the sole intrinsics-side copy, deliberately matching
        // `PlatformError::DispatchError`'s `Display` template so both run modes
        // surface identical text. A single source would require an
        // intrinsics→types dependency the charter forbids.
        eprintln!(
            "platform fn `{}` dispatch failed: {}",
            fault.fn_name, fault.cause
        );
        std::process::exit(1);
    }
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
}
