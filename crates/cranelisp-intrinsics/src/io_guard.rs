//! Fault guard for forcing platform Effect thunks (FIXME 0327 — the
//! fault-guarded FFI-dispatch funnel; Option A, S81 — fault-catch is DLL-local).
//!
//! The IO trampoline (`crate::io`) forces platform Effect thunks via
//! `cranelisp_platform::call_effect_thunk`. A fault in foreign platform code —
//! a Rust panic OR a hardware trap (SIGFPE/SIGILL/SIGBUS/SIGSEGV) — must NOT
//! crash the host; it must surface as a structured `PlatformError::DispatchError`.
//! This module provides the single guard primitive
//! [`force_effect_thunk_protected`].
//!
//! ## Two faults, two catch sites (FIXME 0327 Option A)
//!
//! **Rust panics are caught DLL-side, NOT here.** A platform `cdylib` statically
//! links its own panic runtime; a `panic!` inside the DLL unwinds with the DLL's
//! runtime and CANNOT be caught by a host `catch_unwind` (a foreign unwind
//! reaching the host aborts). So the panic catch lives in the DLL-monomorphised
//! `CLIO::effect*` thunk wrapper (`cranelisp-platform`), which converts a caught
//! panic into an `EffectOutcome` value (`fault_cause` non-null) carried back
//! across the C-ABI. This guard simply **reads** that signal: a non-null
//! `fault_cause` ⇒ compose a `DispatchFault`. The host-side panic `catch_unwind`
//! that step-3 used is GONE — there is nothing host-side to catch.
//!
//! **Hardware traps are still caught here.** A genuine SIGSEGV/FPE/ILL/BUS from
//! foreign C code is process-global (delivered to the faulting thread regardless
//! of which cdylib raised it), so the host `sigsetjmp`/signal-handler half still
//! recovers it across the DLL boundary. That half is RETAINED unchanged. (A Rust
//! null-deref now lands as a non-unwinding panic caught DLL-side, not a SIGSEGV.)
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

use crate::panic::{DispatchFault, set_dispatch_fault, take_runtime_error};

/// Outcome of forcing a platform Effect thunk under the fault guard.
pub(crate) enum ForceOutcome {
    /// The thunk forced cleanly; carries its result value.
    Value(i64),
    /// The thunk faulted (panic or hardware trap). The fault has already been
    /// captured into the thread-local dispatch-fault slot
    /// ([`crate::panic::set_dispatch_fault`]) for int to compose.
    Faulted,
}

/// Force a platform Effect thunk under fault protection (FIXME 0327 Option A).
///
/// Happy path forces the thunk via `cranelisp_platform::call_effect_thunk` and
/// returns [`ForceOutcome::Value`] from the resulting [`EffectOutcome`]'s value.
/// Two fault paths converge on [`ForceOutcome::Faulted`] + the dispatch-fault
/// slot (paired with `fn_name`):
/// - a **Rust panic** in the platform fn, caught DLL-side and signalled by a
///   non-null `EffectOutcome::fault_cause` (this guard reads the cause string);
/// - a **hardware trap** (SIGFPE/SIGILL/SIGBUS/SIGSEGV) from foreign C code,
///   recovered by the retained `sigsetjmp`/signal-handler half.
///
/// [`EffectOutcome`]: cranelisp_platform::EffectOutcome
///
/// `fn_name` is the cranelisp-level platform fn name (read by the caller from
/// the Effect node's baked field-3, or `"<unknown>"` when the handle is null).
///
/// # Safety
/// `thunk_ptr` must be a valid double-boxed thunk pointer as produced by
/// `CLIO::effect*` — the contract `cranelisp_platform::call_effect_thunk`
/// requires (forced at most once).
pub(crate) unsafe fn force_effect_thunk_protected(thunk_ptr: i64, fn_name: &str) -> ForceOutcome {
    // Clear any stale runtime error so a leftover slot value cannot be
    // misattributed to this thunk (defensive — DLL-origin panics no longer set
    // the host slot; they are caught DLL-side and travel back in EffectOutcome).
    let _ = take_runtime_error();

    // The host-side panic `catch_unwind` is GONE (FIXME 0327 Option A). A panic
    // raised inside a platform DLL is caught by the DLL's OWN runtime in the
    // `CLIO::effect*` thunk wrapper and returned across the C-ABI as an
    // `EffectOutcome` — a foreign unwind never reaches here (it would abort).
    // We keep ONLY the sigsetjmp/signal half: genuine hardware traps from
    // foreign C code (SIGSEGV/FPE/ILL/BUS) are process-global, delivered to the
    // faulting thread regardless of which cdylib raised them, so the host
    // handler still catches them across the DLL boundary.
    //
    // SAFETY: sigsetjmp/siglongjmp recover from hardware traps without unwinding
    // through the platform `extern "C"` frames (which would be UB). sigsetjmp
    // saves the execution context; a signal handler that calls siglongjmp
    // returns control here with a non-zero value (the signal number).
    let outcome: Result<cranelisp_platform::EffectOutcome, libc::c_int> = unsafe {
        let sig = sigsetjmp(JMP_BUF.with(|buf| buf.get()), 1);
        if sig != 0 {
            // Reached here via siglongjmp from a signal handler.
            Err(sig)
        } else {
            // Install trap handlers that siglongjmp back on fault.
            let old_handlers = install_signal_handlers();
            // SAFETY: caller guarantees `thunk_ptr` is a valid, not-yet-forced
            // double-boxed Effect thunk; it returns an EffectOutcome (ABI v5).
            let eo = cranelisp_platform::call_effect_thunk(thunk_ptr);
            restore_signal_handlers(old_handlers);
            Ok(eo)
        }
    };

    match outcome {
        // Clean force OR DLL-caught panic — distinguished by fault_cause.
        Ok(eo) => {
            if eo.fault_cause.is_null() {
                ForceOutcome::Value(eo.value)
            } else {
                // Faulted DLL-side: read the DLL-owned (session-leaked) UTF-8
                // panic-cause bytes from the EffectOutcome C-string.
                // SAFETY: a non-null fault_cause points at `fault_len` valid
                // UTF-8 bytes owned by the DLL for the session (§5 invariant 6).
                let cause = unsafe {
                    let bytes = std::slice::from_raw_parts(eo.fault_cause, eo.fault_len);
                    String::from_utf8_lossy(bytes).into_owned()
                };
                set_dispatch_fault(DispatchFault {
                    fn_name: fn_name.to_string(),
                    cause,
                });
                ForceOutcome::Faulted
            }
        }
        // Hardware trap recovered via the signal/sigsetjmp half.
        Err(sig) => {
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
        SavedSignalHandlers {
            fpe,
            ill,
            bus,
            segv,
        }
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

// ---------------------------------------------------------------------------
// Fault-guard strategy tier (FIXME 0501)
//
// io_guard had ZERO unit coverage. The core `force_effect_thunk_protected`
// needs a live platform Effect thunk (a DLL fixture), but the RETAINED
// hardware-trap recovery half — the `sigsetjmp`/signal-handler/`siglongjmp`
// mechanism (§io_guard "Hardware traps are still caught here") — IS unit-
// testable in isolation. These tests exercise the strategy scenarios per
// METHOD §2.2: the trap-recovery happy path, the four-signal install matrix,
// and the install/restore round-trip negative (handlers must NOT be left
// dangling). Each `#[test]` is its own nextest process, so mutating
// process-global signal dispositions is isolated. Windows in which the real
// trap handler is installed contain only straight-line, non-faulting reads.
// spec: BC §4b invariant 14 — the single platform-Effect force-site guard.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;

    fn longjmp_handler_ptr() -> libc::sighandler_t {
        signal_handler_longjmp as *const () as libc::sighandler_t
    }

    // complexity / positive: a SIGSEGV is recovered end-to-end through sigsetjmp
    // + the installed handler + siglongjmp — the retained half the guard's Err
    // arm relies on. The signal is delivered via `libc::raise` (synchronous, to
    // this thread): it drives the identical handler -> siglongjmp path a genuine
    // foreign-code hardware trap takes, without invoking memory UB (a real null
    // deref is intercepted by Rust's own debug null-check + abort, and integer
    // div-by-zero does not trap on aarch64 — neither reaches this handler).
    #[test]
    fn hardware_trap_recovers_via_sigsetjmp_handler() {
        // SAFETY: mirrors `force_effect_thunk_protected`'s sigsetjmp dance; the
        // handler resets the signal to SIG_DFL before siglongjmp, so no loop.
        let recovered: libc::c_int = JMP_BUF.with(|buf| unsafe {
            let sig = sigsetjmp(buf.get(), 1);
            if sig != 0 {
                // Reached via siglongjmp from the trap handler.
                return sig;
            }
            let _old = install_signal_handlers();
            // Deliver SIGSEGV to this thread; the installed handler siglongjmps back.
            libc::raise(libc::SIGSEGV);
            0 // unreachable — the handler jumps out.
        });

        // Tidy up: the trap path jumped out before restoring, and the handler
        // reset SIGSEGV to SIG_DFL. Return every trap signal to the default so no
        // stale-frame longjmp handler survives this test frame.
        unsafe {
            libc::signal(libc::SIGSEGV, libc::SIG_DFL);
            libc::signal(libc::SIGFPE, libc::SIG_DFL);
            libc::signal(libc::SIGILL, libc::SIG_DFL);
            libc::signal(libc::SIGBUS, libc::SIG_DFL);
        }

        assert_eq!(
            recovered,
            libc::SIGSEGV,
            "sigsetjmp + trap handler must recover the SIGSEGV and report the signal number",
        );
    }

    // matrix / edge: install routes ALL FOUR trap signals (FPE/ILL/BUS/SEGV) to
    // the guard's longjmp handler.
    #[test]
    fn install_covers_all_four_trap_signals() {
        unsafe {
            let o_fpe = libc::signal(libc::SIGFPE, libc::SIG_DFL);
            let o_ill = libc::signal(libc::SIGILL, libc::SIG_DFL);
            let o_bus = libc::signal(libc::SIGBUS, libc::SIG_DFL);
            let o_segv = libc::signal(libc::SIGSEGV, libc::SIG_DFL);

            // `_saved` (the prior dispositions install captured, all DFL here) is
            // not needed — we restore the true originals directly below.
            let _saved = install_signal_handlers();
            // Read back each installed handler (swap DFL in, capture old). This
            // window is straight-line with no faulting op.
            let i_fpe = libc::signal(libc::SIGFPE, libc::SIG_DFL);
            let i_ill = libc::signal(libc::SIGILL, libc::SIG_DFL);
            let i_bus = libc::signal(libc::SIGBUS, libc::SIG_DFL);
            let i_segv = libc::signal(libc::SIGSEGV, libc::SIG_DFL);

            // Restore true originals.
            libc::signal(libc::SIGFPE, o_fpe);
            libc::signal(libc::SIGILL, o_ill);
            libc::signal(libc::SIGBUS, o_bus);
            libc::signal(libc::SIGSEGV, o_segv);

            let expected = longjmp_handler_ptr();
            for (name, got) in [
                ("SIGFPE", i_fpe),
                ("SIGILL", i_ill),
                ("SIGBUS", i_bus),
                ("SIGSEGV", i_segv),
            ] {
                assert_eq!(
                    got, expected,
                    "install must route {name} to the sigsetjmp trap handler"
                );
            }
        }
    }

    // negative: install returns the PRIOR disposition and restore reverts it —
    // the guard must NOT leave the trap handler dangling after the force. Proven
    // on SIGFPE (never fires in straight-line code).
    #[test]
    fn install_returns_prior_and_restore_reverts() {
        unsafe {
            // Establish a known, non-default baseline for SIGFPE.
            let true_orig = libc::signal(libc::SIGFPE, libc::SIG_IGN);

            let saved = install_signal_handlers();
            // Capture the installed handler, resetting FPE to the IGN baseline.
            let installed = libc::signal(libc::SIGFPE, libc::SIG_IGN);
            restore_signal_handlers(saved);
            // Capture the post-restore handler, putting the true original back.
            let restored = libc::signal(libc::SIGFPE, true_orig);

            assert_eq!(
                installed,
                longjmp_handler_ptr(),
                "install must set the sigsetjmp trap handler for SIGFPE (not the IGN baseline)",
            );
            assert_ne!(installed, libc::SIG_IGN);
            assert_eq!(
                restored,
                libc::SIG_IGN,
                "restore must revert SIGFPE to its saved (IGN) disposition, not leave the trap handler",
            );
        }
    }
}
