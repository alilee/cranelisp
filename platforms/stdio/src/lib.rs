//! Stdio platform for cranelisp -- standalone cdylib.
//!
//! Implements the "stdio" platform as a dynamically-loaded library. Under the
//! single-ABI cutover (`design/arch/platform-interface.md` §6.8.0) a single
//! manifest freely **mixes** a blocking effect and a poll-shape leaf:
//!
//! - `print`: `String -> IO Int` -- print a string followed by a newline. Stays
//!   a **blocking** `SchedulingClass::Sequential` effect: output must appear in
//!   program order, and it never blocks long enough for the poll model to buy it
//!   anything (`poll-support.md §3.1`). It is the byte-identical-off witness — the
//!   v6-shape effect coexisting with a poll leaf in ONE manifest.
//! - `read-line`: `() -> IO String` -- read a line from stdin. The **poll-shape**
//!   candidate (`design/platform/poll-support.md §3.1`): it blocks on stdin
//!   readiness, the textbook poll leaf. Rewritten as a [`PollFn`]: the first poll
//!   does a non-blocking read of stdin (fd 0); if data is available it returns the
//!   line `Ready`, otherwise it registers fd-readiness with the host reactor and
//!   parks, resuming when stdin becomes readable. It is `Commutative` (tokenless),
//!   so the backend injects the `(0, 1)` leading pair — no token/capacity args.
//!
//! This is the "simple platform ports cleanly" ergonomics check
//! (`poll-support.md §3.1`): the poll leaf is written against the extracted
//! `poll_support` suite — [`PollEnv`] for the env, [`Reactor`] for fd-readiness,
//! [`PollState`] for the first-poll/re-poll phase — so the only hand-written part
//! is the syscall + the line-buffering + the `CLString` result construction.
//!
//! Uses the `cranelisp-platform` shared crate for ABI types, wrapper types
//! (`CLString`, `CLInt`, `CLIO`), the `poll_support` suite, and the
//! `declare_platform!` macro.

use core::ffi::c_void;
use std::sync::Mutex;

use cranelisp_platform::poll_support::{PollEnv, PollState, PollStep, Reactor};
use cranelisp_platform::*;

static HOST: HostContext = HostContext::new();

/// Print a string followed by a newline. Returns a deferred IO Effect.
///
/// BLOCKING (`SchedulingClass::Sequential`) — unchanged from v6. Uses the
/// consuming capture-RC protocol (Decision 24): `into_owned_consuming` takes
/// ownership of the caller's transferred reference and releases it on drop when
/// the Effect thunk runs. See `design/backend/ring2-rc.md` §10.4.
pub extern "C" fn print_string(s: CLString) -> CLIO<CLInt> {
    let owned = s.into_owned_consuming();
    CLIO::effect(move || {
        println!("{}", owned.as_str());
        CLInt::from(0i64)
    })
}

// ---------------------------------------------------------------------
// read-line -- the poll-shape leaf
// ---------------------------------------------------------------------

/// Line-accumulation buffer for the serial stdin resource.
///
/// `read-line` reads stdin (fd 0) non-blocking, one chunk per poll, accumulating
/// here until a newline (or EOF) delimits a line. stdin is a process-singleton
/// serial resource, so a single process-global buffer is the right cardinality:
/// a line straddling several poll wakeups accumulates across them, and bytes
/// past the first newline stay buffered for the *next* `read-line` call (ordinary
/// line buffering). The `Mutex` is for interior mutability of the `static`, not
/// contention — stdin is read by at most one in-flight `read-line` at a time.
static STDIN_BUF: Mutex<Vec<u8>> = Mutex::new(Vec::new());

/// A non-zero phase marker stashed in the env result slot while parked
/// ([`PollState::drive`]) — must never collide with the `0` unstarted sentinel
/// nor with a real `CLString` base pointer once `Ready` overwrites it.
const READ_LINE_ARMED: i64 = -1;

/// Set stdin (fd 0) to `O_NONBLOCK` (idempotent). The poll-fn must never block
/// inside the syscall — on no-data it returns `EWOULDBLOCK` and we park.
fn set_stdin_nonblocking() {
    // SAFETY: `fcntl`/`F_GETFL`/`F_SETFL` on fd 0 are sound; idempotent re-set.
    unsafe {
        let flags = libc::fcntl(0, libc::F_GETFL);
        if flags >= 0 && (flags & libc::O_NONBLOCK) == 0 {
            libc::fcntl(0, libc::F_SETFL, flags | libc::O_NONBLOCK);
        }
    }
}

/// If `STDIN_BUF` contains a full line (a `\n`), remove and return it (trailing
/// `\n`/`\r` trimmed, matching the v6 blocking `read_line`). `None` if no
/// complete line is buffered yet.
fn take_buffered_line() -> Option<String> {
    let mut buf = STDIN_BUF.lock().expect("stdio STDIN_BUF mutex poisoned");
    let nl = buf.iter().position(|&b| b == b'\n')?;
    // Drain through the newline; the line is the bytes before it.
    let rest = buf.split_off(nl + 1);
    let mut line = std::mem::replace(&mut *buf, rest);
    line.truncate(nl); // drop the '\n'
    if line.last() == Some(&b'\r') {
        line.pop();
    }
    Some(String::from_utf8_lossy(&line).into_owned())
}

/// Drain whatever remains in `STDIN_BUF` as the final (unterminated) line at EOF
/// (trailing `\r` trimmed). Mirrors v6 `read_line` returning the last partial
/// line on a newline-less EOF.
fn drain_buffered_all() -> String {
    let mut buf = STDIN_BUF.lock().expect("stdio STDIN_BUF mutex poisoned");
    let mut line = std::mem::take(&mut *buf);
    if line.last() == Some(&b'\r') {
        line.pop();
    }
    String::from_utf8_lossy(&line).into_owned()
}

/// Attempt to complete one `read-line`: drain buffered bytes / non-blocking-read
/// more, returning `Ready(cls)` when a line is delimited (or at EOF) and `Park`
/// (after registering stdin readiness) when the read would block.
///
/// The `i64` result of `Ready` is a freshly-allocated `CLString` base pointer at
/// RC=1 (allocated via the host allocator installed at manifest `init`, exactly
/// as the v6 blocking `read_line` did) — the consuming continuation, compiled
/// from the `(IO String)` signature, adopts that reference (carrier-agnostic:
/// the result is threaded identically to the blocking carrier).
fn poll_read_line(reactor: &Reactor) -> PollStep {
    set_stdin_nonblocking();
    loop {
        if let Some(line) = take_buffered_line() {
            let cls: CLString = line.into();
            return PollStep::Ready(cls.to_raw());
        }
        let mut chunk = [0u8; 1024];
        // SAFETY: fd 0 is valid; `chunk` is a valid mutable out-buffer.
        let n = unsafe { libc::read(0, chunk.as_mut_ptr() as *mut c_void, chunk.len()) };
        if n > 0 {
            STDIN_BUF
                .lock()
                .expect("stdio STDIN_BUF mutex poisoned")
                .extend_from_slice(&chunk[..n as usize]);
            continue; // re-check for a complete line, then read again if needed.
        } else if n == 0 {
            // EOF: return whatever remains as the last line (possibly empty).
            let cls: CLString = drain_buffered_all().into();
            return PollStep::Ready(cls.to_raw());
        } else {
            // SAFETY: read errno location after a failed `read`.
            let err = unsafe { *libc::__errno_location() };
            if err == libc::EWOULDBLOCK || err == libc::EAGAIN {
                reactor.wake_on_readable(0);
                return PollStep::Park;
            }
            // Hard error: surface an empty line rather than wedge the strand.
            let cls: CLString = String::new().into();
            return PollStep::Ready(cls.to_raw());
        }
    }
}

/// `read-line` -- the poll-shape leaf (`() -> IO String`).
///
/// The host re-invokes this `PollFn` after each readiness wake; [`PollState`]
/// distinguishes the first poll (arm: set non-blocking, first read attempt) from
/// the resume (re-read after a wake) over the env result slot reused as the
/// `0`-initialised phase sentinel. The whole syscall body is the same closure for
/// both phases (the read attempt is idempotent), so the only phase-specific work
/// the scaffold encodes is the marker bookkeeping.
///
/// # Safety
/// C-ABI poll-fn ([`PollFn`]): `state` is the host-built state-closure env base
/// (`result_slot` at `+0`; `read-line` declares no leaf args); `host` / `waker`
/// are live for the call.
pub unsafe extern "C" fn read_line_pollfn(
    state: *mut c_void,
    host: *const HostCtx,
    waker: *const Waker,
) -> Poll {
    // SAFETY: `state` is the host-built env base; `host`/`waker` are live.
    let env = unsafe { PollEnv::new(state) };
    let reactor = unsafe { Reactor::new(host, waker) };
    let phase = PollState::new(&env);
    phase.drive(
        READ_LINE_ARMED,
        || poll_read_line(&reactor),
        || poll_read_line(&reactor),
    )
}

/// The `Commutative` (tokenless) descriptor `read-line` carries: `token 0`
/// (no admission token — stdin's serial discipline is a host concern, not a
/// pooled resource), `cardinality 0`, `blocking 0` (poll-shape ⇒ the reactor
/// carrier). `nearest_scheduling_class` maps `token 0, cardinality 0` ⇒
/// `Commutative`, so the backend INJECTS the `(0, 1)` leading pair (no
/// token/capacity cranelisp args — `poll-support.md §3.4.2`).
const COMMUTATIVE: ConcurrencyDescriptor = ConcurrencyDescriptor {
    token: 0,
    cardinality: 0,
    global_budget: 0,
    blocking: 0,
    _reserved: [0; 3],
};

declare_platform! {
    name: "stdio",
    version: "0.1.0",
    host: HOST,
    functions: [
        print_string {
            cl_name: "print",
            sig: "(Fn [primitives/String] (primitives/IO primitives/Int))",
            doc: "Print a string followed by a newline",
            params: [s],
            scheduling: SchedulingClass::Sequential,
        },
        read_line_pollfn {
            cl_name: "read-line",
            sig: "(Fn [] (primitives/IO primitives/String))",
            doc: "Read a line from stdin (poll-shape: suspends on stdin readiness)",
            params: [],
            descriptor: COMMUTATIVE,
        },
    ]
}
