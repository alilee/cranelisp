//! Fault guard for forcing platform Effect thunks (FIXME 0327 — the
//! fault-guarded FFI-dispatch funnel; Option A, S81 — fault-catch is DLL-local).
//!
//! The IO trampoline (`crate::io`) forces platform Effect thunks via
//! `cranelisp_platform::call_effect_thunk`. A fault in foreign platform code —
//! a Rust panic OR a hardware trap (SIGFPE/SIGILL/SIGBUS/SIGSEGV) — must NOT
//! die by a raw signal; it must end the process with a dispatch-fault report.
//! This module provides the force-site guard [`force_effect_thunk_protected`]
//! and the trap guard [`run_trap_guarded`] it runs the platform call under.
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
//! `fault_cause` ⇒ a dispatch fault; there is nothing host-side to catch.
//!
//! **Hardware traps are still caught here.** A genuine SIGSEGV/FPE/ILL/BUS from
//! foreign C code is process-global (delivered to the faulting thread regardless
//! of which cdylib raised it), so the host `sigsetjmp`/signal-handler half still
//! recovers it across the DLL boundary. The handler is installed once per
//! process and never restored; only the calling thread's armed jump context
//! changes per call (`design/intrinsics/process-lifecycle.md` §1.8). (A Rust
//! null-deref lands as a non-unwinding panic caught DLL-side, not a SIGSEGV.)
//!
//! ## Why the machinery lives here
//!
//! BC §4b invariant 14 + §5 invariant 9 place the guard at the **single force
//! site** for every platform Effect in every mode (Principle 7 + Principle 6 —
//! one guard, not per-DLL). The force site is intrinsics-owned (the trampoline,
//! `crate::io`). It is the process's only writer of the trap dispositions: the
//! binary writes none (`src/expander/trap_dispositions_tests.rs`). The
//! machinery is `pub(crate)` — it is not a public-surface item.
//!
//! ## Outcome
//!
//! A fault ends the process through the terminator with the platform fn name
//! (read from the Effect node's backend-baked fourth field) and the cause
//! (`design/intrinsics/process-lifecycle.md` §1.1). Nothing is returned to a
//! host.

use crate::panic::{Fault, terminate};

/// Force a platform Effect thunk under fault protection (FIXME 0327 Option A).
///
/// Forces the thunk via `cranelisp_platform::call_effect_thunk` and returns the
/// resulting [`EffectOutcome`]'s value. Two fault paths end the process as a
/// dispatch fault naming `fn_name`:
/// - a **Rust panic** in the platform fn, caught DLL-side and signalled by a
///   non-null `EffectOutcome::fault_cause` (this guard reads the cause string);
/// - a **hardware trap** (SIGFPE/SIGILL/SIGBUS/SIGSEGV) from foreign C code,
///   recovered by [`run_trap_guarded`].
///
/// [`EffectOutcome`]: cranelisp_platform::EffectOutcome
///
/// `fn_name` is the cranelisp-level platform fn name (read by the caller from
/// the Effect node's baked field-3, or `"<unknown>"` when the handle is null).
///
/// # Safety
/// `thunk_ptr` must be the live thunk word of an `Effect` node built by
/// `CLIO::effect*`, borrowed for this call while the caller holds a counted
/// reference to that node — the contract `cranelisp_platform::call_effect_thunk`
/// requires. The thunk is intact after the call, whatever its outcome.
pub(crate) unsafe fn force_effect_thunk_protected(thunk_ptr: i64, fn_name: &str) -> i64 {
    // A panic raised inside a platform DLL is caught by the DLL's own runtime
    // and returned as an `EffectOutcome`; a foreign unwind never reaches here.
    //
    // SAFETY: the caller guarantees a live, borrowed thunk whose node it
    // holds; the call returns an EffectOutcome.
    let outcome = run_trap_guarded(|| unsafe { cranelisp_platform::call_effect_thunk(thunk_ptr) });
    match outcome {
        // Clean force OR DLL-caught panic — distinguished by fault_cause.
        Ok(eo) => {
            if eo.fault_cause.is_null() {
                eo.value
            } else {
                // Faulted DLL-side: read the DLL-owned (session-leaked) UTF-8
                // panic-cause bytes from the EffectOutcome C-string.
                // SAFETY: a non-null fault_cause points at `fault_len` valid
                // UTF-8 bytes owned by the DLL for the session (§5 invariant 6).
                let cause = unsafe {
                    let bytes = std::slice::from_raw_parts(eo.fault_cause, eo.fault_len);
                    String::from_utf8_lossy(bytes).into_owned()
                };
                terminate(Fault::Dispatch {
                    fn_name,
                    cause: &cause,
                })
            }
        }
        // Hardware trap recovered via the signal/sigsetjmp half.
        Err(trap) => terminate(Fault::Dispatch {
            fn_name,
            cause: &trap.cause(),
        }),
    }
}

/// The trap signal that ended a [`run_trap_guarded`] extent.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct TrapSignal(libc::c_int);

impl TrapSignal {
    /// The dispatch-fault cause text for this signal.
    fn cause(self) -> String {
        match self.0 {
            libc::SIGFPE => "arithmetic exception (division by zero)".to_string(),
            libc::SIGILL => "illegal instruction".to_string(),
            libc::SIGBUS => "bus error".to_string(),
            libc::SIGSEGV => "segmentation fault".to_string(),
            sig => format!("signal {sig}"),
        }
    }
}

/// Run `f` under the trap guard: return its value, or the trap signal that
/// interrupted it (`design/intrinsics/process-lifecycle.md` §1.8).
///
/// The first call in the process installs the guard's handler for the four trap
/// signals; no later call writes a disposition. Each call arms only the calling
/// thread, for the extent of `f`, by publishing a jump context held in its own
/// frame, and restores the thread's previous context on return, so a nested
/// call leaves its caller armed. A trap on a thread with no armed context is
/// forwarded to the action the install found.
///
/// `f` must not unwind: a panic leaves through this frame with the context
/// restored, but `f`'s frames are not a supported jump target.
#[inline(never)]
pub(crate) fn run_trap_guarded<T>(f: impl FnOnce() -> T) -> Result<T, TrapSignal> {
    INSTALL.call_once(install_trap_handlers);
    let mut context: SigJmpBuf = [0; std::mem::size_of::<SigJmpBuf>()];
    let context: *mut SigJmpBuf = &mut context;
    let _extent = ArmedExtent {
        previous: ARMED_CONTEXT.get(),
    };
    // SAFETY: sigsetjmp/siglongjmp recover from hardware traps without unwinding
    // through the platform `extern "C"` frames (which would be UB). sigsetjmp
    // saves the execution context in this frame; the handler's siglongjmp
    // returns here with the signal number. Nothing read after the jump is
    // written between the two returns.
    let sig = unsafe { sigsetjmp(context, 1) };
    if sig != 0 {
        return Err(TrapSignal(sig));
    }
    ARMED_CONTEXT.set(context);
    Ok(f())
}

// ---------------------------------------------------------------------------
// sigsetjmp/siglongjmp FFI and the process-wide trap handler.
//
// The disposition is process state, installed once; the jump context is thread
// state, armed per call (`process-lifecycle.md` §1.8).
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

/// The signals the guard recovers.
const TRAP_SIGNALS: [libc::c_int; 4] = [libc::SIGFPE, libc::SIGILL, libc::SIGBUS, libc::SIGSEGV];

static INSTALL: std::sync::Once = std::sync::Once::new();

/// The action each of [`TRAP_SIGNALS`] had before the install, in that order.
/// It is recorded before any handler is installed, so the handler always finds
/// it. A process writer that changes an action between the record and the
/// install is not seen; nothing in this crate does.
static PREVIOUS_ACTIONS: std::sync::OnceLock<[libc::sigaction; 4]> = std::sync::OnceLock::new();

std::thread_local! {
    /// The calling thread's armed jump context, or null. Const-initialized with
    /// no destructor, so the handler's read is a plain thread-local load.
    static ARMED_CONTEXT: std::cell::Cell<*mut SigJmpBuf> =
        const { std::cell::Cell::new(std::ptr::null_mut()) };
}

/// One call's armed extent: restores the thread's previous context on exit.
struct ArmedExtent {
    previous: *mut SigJmpBuf,
}

impl Drop for ArmedExtent {
    fn drop(&mut self) {
        ARMED_CONTEXT.set(self.previous);
    }
}

/// Record every signal's current action, then install the handler for each, so
/// the handler finds the action it replaced from the moment it is installed.
fn install_trap_handlers() {
    let _ = PREVIOUS_ACTIONS.set(TRAP_SIGNALS.map(current_action));
    TRAP_SIGNALS.into_iter().for_each(install_trap_handler);
}

/// The action installed for `sig`, read without changing it.
fn current_action(sig: libc::c_int) -> libc::sigaction {
    // SAFETY: a null new action makes `sigaction` a pure query into `action`.
    unsafe {
        let mut action: libc::sigaction = std::mem::zeroed();
        libc::sigaction(sig, std::ptr::null(), &mut action);
        action
    }
}

/// Install the guard's handler for `sig`.
fn install_trap_handler(sig: libc::c_int) {
    // SAFETY: a zeroed `sigaction` with an empty mask, a valid `SA_SIGINFO`
    // handler and valid flags is a well-formed argument.
    unsafe {
        let mut action: libc::sigaction = std::mem::zeroed();
        action.sa_sigaction = trap_handler as *const () as libc::sighandler_t;
        action.sa_flags = libc::SA_SIGINFO | libc::SA_ONSTACK;
        libc::sigemptyset(&mut action.sa_mask);
        libc::sigaction(sig, &action, std::ptr::null_mut());
        #[cfg(test)]
        if let Some(hook) = AFTER_HANDLER_INSTALL.get() {
            hook(sig);
        }
    }
}

/// A test hook run on the installing thread just after the handler for each
/// signal is installed, to deliver a signal inside the install.
#[cfg(test)]
static AFTER_HANDLER_INSTALL: std::sync::OnceLock<fn(libc::c_int)> = std::sync::OnceLock::new();

/// The process-wide handler for [`TRAP_SIGNALS`]. A trap on a thread with an
/// armed context disarms it and jumps there; any other trap is not the guard's
/// and is forwarded.
extern "C" fn trap_handler(
    sig: libc::c_int,
    info: *mut libc::siginfo_t,
    context: *mut libc::c_void,
) {
    let armed = ARMED_CONTEXT.replace(std::ptr::null_mut());
    if !armed.is_null() {
        // SAFETY: `armed` is the context of a `run_trap_guarded` frame still on
        // this thread's stack; its extent ends only after clearing the slot.
        unsafe { siglongjmp(armed, sig) };
    }
    forward_unarmed_trap(sig, info, context);
}

/// Deliver an unarmed trap as the action the install replaced would have: call
/// a previous handler with the arguments it expects, ignore it if it was
/// ignored, and otherwise restore the default action and re-raise, so the
/// process dies on the signal.
fn forward_unarmed_trap(sig: libc::c_int, info: *mut libc::siginfo_t, context: *mut libc::c_void) {
    let previous = PREVIOUS_ACTIONS.get().and_then(|actions| {
        TRAP_SIGNALS
            .iter()
            .position(|trap| *trap == sig)
            .map(|index| actions[index])
    });
    match previous {
        Some(action) if action.sa_sigaction == libc::SIG_IGN => {}
        Some(action) if action.sa_sigaction != libc::SIG_DFL => {
            if action.sa_flags & libc::SA_SIGINFO != 0 {
                // SAFETY: an `SA_SIGINFO` action's handler has this signature.
                let handler: extern "C" fn(libc::c_int, *mut libc::siginfo_t, *mut libc::c_void) =
                    unsafe { std::mem::transmute(action.sa_sigaction) };
                handler(sig, info, context);
            } else {
                // SAFETY: a plain action's handler takes only the signal.
                let handler: extern "C" fn(libc::c_int) =
                    unsafe { std::mem::transmute(action.sa_sigaction) };
                handler(sig);
            }
        }
        _ => {
            // SAFETY: installing `SIG_DFL` is valid; the re-raised signal is
            // blocked until this handler returns, then takes the default action.
            unsafe {
                let mut action: libc::sigaction = std::mem::zeroed();
                action.sa_sigaction = libc::SIG_DFL;
                libc::sigemptyset(&mut action.sa_mask);
                libc::sigaction(sig, &action, std::ptr::null_mut());
                libc::raise(sig);
            }
        }
    }
}

/// The address of the guard's trap handler, as `sigaction` reports it.
#[cfg(test)]
fn trap_handler_address() -> libc::sighandler_t {
    trap_handler as *const () as libc::sighandler_t
}

#[cfg(test)]
mod tests;
