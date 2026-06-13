//! Fault guard for forcing platform Effect thunks (FIXME 0327 — the
//! fault-guarded FFI-dispatch funnel, step 3/4).
//!
//! The IO trampoline (`crate::io`) forces platform Effect thunks via
//! `cranelisp_platform::call_effect_thunk`. A fault in foreign platform code —
//! a Rust panic OR a hardware trap (SIGFPE/SIGILL/SIGBUS/SIGSEGV) — must NOT
//! crash the host; it must surface as a structured `PlatformError::DispatchError`.
//! This module provides the single guard primitive
//! [`force_effect_thunk_protected`] that wraps the force with the SAME machinery
//! int uses for protected JIT calls (`src/expander.rs::invoke_jit_protected`):
//! `std::panic::catch_unwind` for Rust panics + `sigsetjmp`/signal handlers for
//! hardware traps + the `crate::panic::take_runtime_error()` slot check.
//!
//! ## Why the machinery lives here
//!
//! BC §4b invariant 14 + §5 invariant 9 place the guard at the **single force
//! site** for every platform Effect in every mode (Principle 7 + Principle 6 —
//! one guard, not per-DLL). The force site is intrinsics-owned (the trampoline,
//! `crate::io`). The `invoke_jit_protected` precedent lived only in int; this is
//! the intrinsics-side re-host of the same pattern (the guard infra is not
//! shared between crates — int retains its own copy for the macro-expansion JIT
//! call; this one guards the platform-Effect force). The machinery is
//! `pub(crate)` — it is not a public-surface item.
//!
//! ## Two-layer construction (BC §4b invariant 14)
//!
//! On a fault the guard captures `(cause, fn_name)` — the fn-name read from the
//! Effect node's backend-baked fourth field — into a
//! [`crate::panic::DispatchFault`] carrier and signals int via the
//! thread-local slot ([`crate::panic::set_dispatch_fault`]). It does NOT
//! construct a `PlatformError` (intrinsics is diagnostics-free by charter).
//! int reads the slot and composes `PlatformError::DispatchError`.
//!
//! ## Fork-join slot safety (BC §4b invariant 13)
//!
//! Platform Effects force on the trampoline's OWN joining thread (the
//! trampoline walks the IO tree sequentially; Par branch dispatch joins before
//! the trampoline steps past a Par node), so the own-thread-slot-reader property
//! the error-slot ferry relies on holds — the dispatch-fault slot is set and
//! read on the same thread that runs the trampoline, introducing no new race
//! vs. the existing `take_runtime_error()` slot usage.

use crate::panic::{set_dispatch_fault, take_runtime_error, DispatchFault};

/// Outcome of forcing a platform Effect thunk under the fault guard.
pub(crate) enum ForceOutcome {
    /// The thunk forced cleanly; carries its result value.
    Value(i64),
    /// The thunk faulted (panic or hardware trap). The fault has already been
    /// captured into the thread-local dispatch-fault slot
    /// ([`crate::panic::set_dispatch_fault`]) for int to compose.
    Faulted,
}

/// Force a platform Effect thunk under fault protection (FIXME 0327 step 3).
///
/// Happy path is a strict no-op relative to an unguarded
/// `cranelisp_platform::call_effect_thunk(thunk_ptr)`: it forces the thunk and
/// returns [`ForceOutcome::Value`]. The guard only changes behaviour on the
/// faulting path: a Rust panic, a hardware trap (SIGFPE/SIGILL/SIGBUS/SIGSEGV),
/// or a `runtime_panic` slot message during the force is captured into the
/// dispatch-fault slot (paired with `fn_name`) and returns
/// [`ForceOutcome::Faulted`].
///
/// `fn_name` is the cranelisp-level platform fn name (read by the caller from
/// the Effect node's baked field-3, or `"<unknown>"` when the handle is null).
///
/// # Safety
/// `thunk_ptr` must be a valid double-boxed thunk pointer as produced by
/// `CLIO::effect*` — the contract `cranelisp_platform::call_effect_thunk`
/// requires (forced at most once).
pub(crate) unsafe fn force_effect_thunk_protected(thunk_ptr: i64, fn_name: &str) -> ForceOutcome {
    use std::panic::{catch_unwind, AssertUnwindSafe};

    // Clear any stale runtime error so we observe only this thunk's fault.
    let _ = take_runtime_error();

    // catch_unwind handles Rust panics from the platform thunk / runtime_panic.
    let result = catch_unwind(AssertUnwindSafe(|| {
        // SAFETY: sigsetjmp/siglongjmp recover from hardware traps without
        // unwinding through the platform `extern "C"` frames (which would be
        // UB). sigsetjmp saves the execution context; a signal handler that
        // calls siglongjmp returns control here with a non-zero value (the
        // signal number).
        unsafe {
            let sig = sigsetjmp(JMP_BUF.with(|buf| buf.get()), 1);
            if sig != 0 {
                // Reached here via siglongjmp from a signal handler.
                return Err(sig);
            }

            // Install trap handlers that siglongjmp back on fault.
            let old_handlers = install_signal_handlers();

            // SAFETY: caller guarantees `thunk_ptr` is a valid, not-yet-forced
            // double-boxed Effect thunk.
            let value = cranelisp_platform::call_effect_thunk(thunk_ptr);

            restore_signal_handlers(old_handlers);
            Ok(value)
        }
    }));

    // A `runtime_panic` during the force sets the slot but returns the sentinel
    // (the JIT-panic convention) — check it first, as it carries the most
    // specific message.
    if let Some(msg) = take_runtime_error() {
        set_dispatch_fault(DispatchFault {
            fn_name: fn_name.to_string(),
            cause: msg,
        });
        return ForceOutcome::Faulted;
    }

    match result {
        Ok(Ok(value)) => ForceOutcome::Value(value),
        Ok(Err(sig)) => {
            let cause = match sig {
                libc::SIGFPE => "arithmetic exception (division by zero)".to_string(),
                libc::SIGILL => "illegal instruction".to_string(),
                libc::SIGBUS => "bus error".to_string(),
                libc::SIGSEGV => "segmentation fault".to_string(),
                _ => format!("signal {sig}"),
            };
            set_dispatch_fault(DispatchFault {
                fn_name: fn_name.to_string(),
                cause,
            });
            ForceOutcome::Faulted
        }
        Err(panic_payload) => {
            let cause = if let Some(s) = panic_payload.downcast_ref::<String>() {
                s.clone()
            } else if let Some(s) = panic_payload.downcast_ref::<&str>() {
                (*s).to_string()
            } else {
                "unknown panic in platform effect".to_string()
            };
            set_dispatch_fault(DispatchFault {
                fn_name: fn_name.to_string(),
                cause,
            });
            ForceOutcome::Faulted
        }
    }
}

// ---------------------------------------------------------------------------
// sigsetjmp/siglongjmp FFI + signal-handler infra
//
// Mirrors `src/expander.rs::invoke_jit_protected` (the int-side protected JIT
// call). The guard infra is not shared across crates — int keeps its own copy
// for the macro-expansion JIT call; this copy guards the platform-Effect force
// at the intrinsics force site (BC §4b invariant 14).
// ---------------------------------------------------------------------------

// On macOS/aarch64, sigjmp_buf is 196 bytes (jmp_buf + signal mask). We use a
// conservatively sized array; the exact layout is opaque.
#[cfg(target_os = "macos")]
type SigJmpBuf = [u8; 196];

#[cfg(not(target_os = "macos"))]
type SigJmpBuf = [u8; 256]; // Conservative fallback for other platforms.

unsafe extern "C" {
    /// POSIX sigsetjmp: save execution context and optionally signal mask.
    /// Returns 0 on direct call, a non-zero value (from siglongjmp) on return.
    ///
    /// On glibc/musl `sigsetjmp` is a header macro, not a linkable symbol — the
    /// real function is `__sigsetjmp(env, savemask)` (same signature). macOS
    /// exports a real `sigsetjmp`, so the redirect is Linux-only.
    #[cfg_attr(target_os = "linux", link_name = "__sigsetjmp")]
    fn sigsetjmp(env: *mut SigJmpBuf, savesigs: libc::c_int) -> libc::c_int;

    /// POSIX siglongjmp: restore execution context saved by sigsetjmp.
    fn siglongjmp(env: *mut SigJmpBuf, val: libc::c_int) -> !;
}

// Thread-local jump buffer for signal recovery during the Effect-thunk force.
// Only accessed by the signal handler and `force_effect_thunk_protected` on the
// same thread. Signal delivery for SIGFPE/SIGILL/SIGBUS/SIGSEGV is synchronous
// (delivered to the thread that caused the trap).
std::thread_local! {
    static JMP_BUF: std::cell::UnsafeCell<SigJmpBuf> =
        const { std::cell::UnsafeCell::new([0u8; std::mem::size_of::<SigJmpBuf>()]) };
}

/// Signal handler for SIGFPE/SIGILL/SIGBUS/SIGSEGV during the Effect-thunk force.
///
/// Uses siglongjmp to jump back to the sigsetjmp point, bypassing the platform
/// `extern "C"` code frames entirely (unwinding through them would be UB).
extern "C" fn signal_handler_longjmp(sig: libc::c_int) {
    unsafe {
        // Reset to the default handler to prevent infinite signal loops.
        libc::signal(sig, libc::SIG_DFL);
        siglongjmp(JMP_BUF.with(|buf| buf.get() as *mut SigJmpBuf), sig);
    }
}

/// Saved signal-handler state for restoration after the force.
struct SavedSignalHandlers {
    fpe: libc::sighandler_t,
    ill: libc::sighandler_t,
    bus: libc::sighandler_t,
    segv: libc::sighandler_t,
}

/// Install trap handlers that siglongjmp on SIGFPE/SIGILL/SIGBUS/SIGSEGV.
/// Returns the previously installed handlers for later restoration.
fn install_signal_handlers() -> SavedSignalHandlers {
    unsafe {
        let handler = signal_handler_longjmp as *const () as libc::sighandler_t;
        let fpe = libc::signal(libc::SIGFPE, handler);
        let ill = libc::signal(libc::SIGILL, handler);
        let bus = libc::signal(libc::SIGBUS, handler);
        let segv = libc::signal(libc::SIGSEGV, handler);
        SavedSignalHandlers { fpe, ill, bus, segv }
    }
}

/// Restore previously saved signal handlers.
fn restore_signal_handlers(saved: SavedSignalHandlers) {
    unsafe {
        libc::signal(libc::SIGFPE, saved.fpe);
        libc::signal(libc::SIGILL, saved.ill);
        libc::signal(libc::SIGBUS, saved.bus);
        libc::signal(libc::SIGSEGV, saved.segv);
    }
}
