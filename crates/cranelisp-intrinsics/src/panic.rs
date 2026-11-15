//! Process-ending faults: the language panic entry, the one terminator, and the
//! program driver.
//!
//! A runtime panic is raised inside JIT frames that have no unwind tables, so
//! control cannot return to a host without resuming user code on a fabricated
//! value. The runtime therefore ends the process at the raise
//! (`design/intrinsics/process-lifecycle.md` §1). Every fault kind enters one
//! crate-private terminator, which claims termination once per process, flushes buffered
//! standard output, writes one report to stderr and exits.

use std::io::Write;
use std::sync::atomic::{AtomicBool, Ordering};

/// The first characters of every language-panic report (`spec/12-runtime.md`
/// §12.7.5).
///
/// Every language-panic report is exactly one stderr line that begins with this
/// prefix, after which the process exits with [`PANIC_EXIT_STATUS`]. A raiser
/// that knows a source location leads its message with `<file>:<line>: `.
pub const PANIC_REPORT_PREFIX: &str = "error: runtime panic: ";

/// The exit status of a process ended by a language panic.
///
/// The status is shared with other process-ending failures, including platform
/// dispatch faults, whose reports do not carry [`PANIC_REPORT_PREFIX`]. A
/// consumer must not classify an ending as a panic by status alone.
pub const PANIC_EXIT_STATUS: i32 = 1;

/// The exit status of the `OneShot` backstop (`reactor.md` §8.2), distinct so a
/// hung batch program is distinguishable from a program error at the shell.
const BACKSTOP_EXIT_STATUS: i32 = 70;

/// The message of an emitted panic site that passes no text.
const DEFAULT_PANIC_MESSAGE: &str = "match exhaustiveness failure";

/// Why the process is ending. Each kind fixes its report and exit status.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Fault<'a> {
    /// A language panic (`runtime/panic`, or a runtime-raised one such as an
    /// empty `select`).
    Panic(&'a str),
    /// A platform `Effect` thunk faulted: a panic in the platform DLL, or a
    /// hardware trap. Not a language panic, so its report has no panic prefix.
    Dispatch { fn_name: &'a str, cause: &'a str },
    /// A Rust panic inside runtime code, caught at the supervised-strand
    /// boundary. Carries the panic payload.
    RuntimeDefect(&'a str),
    /// The `OneShot` backstop expired; carries the backstop diagnostic.
    BackstopExpired(&'a str),
}

impl Fault<'_> {
    /// The complete report, including its line terminator.
    pub(crate) fn report(&self) -> String {
        match self {
            Fault::Panic(msg) => format!("{PANIC_REPORT_PREFIX}{msg}\n"),
            Fault::Dispatch { fn_name, cause } => {
                format!("platform fn `{fn_name}` dispatch failed: {cause}\n")
            }
            Fault::RuntimeDefect(payload) => format!("error: runtime defect: {payload}\n"),
            Fault::BackstopExpired(diagnostic) => format!("{diagnostic}\n"),
        }
    }

    pub(crate) fn exit_status(&self) -> i32 {
        match self {
            Fault::Panic(_) | Fault::Dispatch { .. } | Fault::RuntimeDefect(_) => PANIC_EXIT_STATUS,
            Fault::BackstopExpired(_) => BACKSTOP_EXIT_STATUS,
        }
    }
}

static TERMINATION_CLAIMED: AtomicBool = AtomicBool::new(false);

/// The outcome of one attempt to claim termination.
#[derive(Debug, PartialEq, Eq)]
enum Claim {
    /// This caller reports and exits.
    Won,
    /// Another caller already ended the process; this one must never return.
    Lost,
}

fn claim(flag: &AtomicBool) -> Claim {
    if flag.swap(true, Ordering::AcqRel) {
        Claim::Lost
    } else {
        Claim::Won
    }
}

/// Whether some thread has begun ending the process because of a fault. The
/// exit-time parity check reads it to stand down (`diagnostic-modes.md` §3).
pub(crate) fn termination_claimed() -> bool {
    TERMINATION_CLAIMED.load(Ordering::Acquire)
}

/// End the process because of `fault`. Never returns.
///
/// Only the first caller in the process reports and exits. Every later caller,
/// on any thread, parks until the exit reclaims it: returning would resume user
/// code, and concurrent `exit` calls are unsound.
pub(crate) fn terminate(fault: Fault<'_>) -> ! {
    if claim(&TERMINATION_CLAIMED) == Claim::Lost {
        loop {
            std::thread::park();
        }
    }
    let _ = std::io::stdout().flush();
    // One buffer, one write, so another thread's stderr output cannot split it.
    let _ = std::io::stderr()
        .lock()
        .write_all(fault.report().as_bytes());
    std::process::exit(fault.exit_status())
}

/// `runtime/panic`: raise a language panic. Never returns.
///
/// Reports `msg` with [`PANIC_REPORT_PREFIX`] and ends the process with
/// [`PANIC_EXIT_STATUS`]. A null pointer or zero length reports the default
/// match-exhaustiveness message.
///
/// # Safety
///
/// `msg_ptr` must point to `msg_len` valid UTF-8 bytes, or be null.
#[unsafe(export_name = "runtime/panic")]
#[allow(clippy::not_unsafe_ptr_arg_deref)] // Called from JIT code; cannot be marked unsafe
pub extern "C" fn runtime_panic(msg_ptr: *const u8, msg_len: usize) -> ! {
    let msg = if msg_ptr.is_null() || msg_len == 0 {
        DEFAULT_PANIC_MESSAGE
    } else {
        // SAFETY: caller guarantees msg_ptr points to valid UTF-8 of length msg_len
        unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(msg_ptr, msg_len)) }
    };
    terminate(Fault::Panic(msg))
}

/// Run a program's `main` and, when it returns IO, force its task tree. Returns
/// the program's reduced result word: the inner IO value, or `main`'s own
/// result.
///
/// Both run modes call this one driver: the `--run` host and the `--link`
/// startup stub. A fault during the run ends the process, so a return is always
/// a completed run.
///
/// # Safety
///
/// `main_ptr` must be a valid non-null pointer to a finalized zero-arg
/// `extern "C" fn() -> i64` (the compiled entry `main`). When `main_returns_io`
/// is true, `main`'s returned `i64` must be a valid IO-tree base pointer
/// (rc > 0), whose ownership transfers to this driver.
#[unsafe(export_name = "cranelisp_run_program")]
#[allow(clippy::not_unsafe_ptr_arg_deref)] // Called from the JIT host / link stub.
pub extern "C" fn cranelisp_run_program(main_ptr: *const u8, main_returns_io: bool) -> i64 {
    // SAFETY: caller guarantees `main_ptr` is a valid finalized zero-arg
    // `extern "C" fn() -> i64` (the contract of this fn's `# Safety`).
    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(main_ptr) };
    let main_result = func();
    if !main_returns_io {
        return main_result;
    }
    let inner = crate::io::drive_io(main_result);
    // Decision 24: the trampoline does not consume its input; release it here.
    // SAFETY: an IO-valued main result transfers its tree owner to this driver.
    crate::drop::consume_io_tree(unsafe { crate::handle::Owned::from_abi(main_result) });
    inner
}

#[cfg(test)]
mod tests;
