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

/// The original fd-0 status flags captured the first time `read-line` sets
/// `O_NONBLOCK` in a session, so the poll leaf can restore fd 0 **as found** on
/// its terminal (`Ready`/EOF) — FIXME 0551 (A). fd 0 is a process-global shared
/// resource borrowed for the poll read; a poll leaf that mutates it and never
/// restores leaves the host's blocking stdin reader (the REPL loop) reading a
/// non-blocking fd, whose empty read returns `EWOULDBLOCK` and used to be
/// misread as EOF → the REPL exited. Restoring the flags returns the fd unchanged.
static ORIG_STDIN_FLAGS: Mutex<Option<i32>> = Mutex::new(None);

/// Set `fd` to `O_NONBLOCK` (idempotent). The poll-fn must never block inside the
/// syscall — on no-data it returns `EWOULDBLOCK` and we park.
fn set_fd_nonblocking(fd: i32) {
    // SAFETY: `fcntl`/`F_GETFL`/`F_SETFL` on a valid fd are sound; idempotent re-set.
    unsafe {
        let flags = libc::fcntl(fd, libc::F_GETFL);
        if flags >= 0 && (flags & libc::O_NONBLOCK) == 0 {
            libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK);
        }
    }
}

/// Restore `fd`'s status flags to `orig` (FIXME 0551 (A) — return a borrowed
/// shared fd as found).
fn restore_fd_flags(fd: i32, orig: i32) {
    // SAFETY: `F_SETFL` restoring previously-read flags on a valid fd is sound.
    unsafe {
        libc::fcntl(fd, libc::F_SETFL, orig);
    }
}

/// Set stdin (fd 0) to `O_NONBLOCK`, recording its original flags once so the
/// terminal `Ready`/EOF path can restore them ([`restore_stdin_flags`]).
fn set_stdin_nonblocking() {
    // Capture the original flags exactly once per not-yet-restored cycle.
    // SAFETY: `F_GETFL` on fd 0 is sound.
    let flags = unsafe { libc::fcntl(0, libc::F_GETFL) };
    if flags >= 0 {
        let mut orig = ORIG_STDIN_FLAGS
            .lock()
            .expect("stdio ORIG_STDIN_FLAGS mutex poisoned");
        if orig.is_none() {
            *orig = Some(flags);
        }
    }
    set_fd_nonblocking(0);
}

/// Restore fd 0's original flags captured by [`set_stdin_nonblocking`] (FIXME
/// 0551 (A)). Called on the poll terminal (`Ready`/EOF), never on `Park` — while
/// parked the fd must stay non-blocking for the re-poll.
fn restore_stdin_flags() {
    let mut orig = ORIG_STDIN_FLAGS
        .lock()
        .expect("stdio ORIG_STDIN_FLAGS mutex poisoned");
    if let Some(flags) = orig.take() {
        restore_fd_flags(0, flags);
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

/// The progress of one non-blocking read attempt against a line-delimited fd.
#[derive(Debug, PartialEq, Eq)]
enum ReadProgress {
    /// `buf` now ends with a `\n` — a complete line is delimited.
    LineReady,
    /// The fd reached EOF (writer closed, all bytes consumed).
    Eof,
    /// The read would block — park and re-poll on readiness.
    WouldBlock,
}

/// Read from `fd` one byte at a time, appending into `buf`, until a `\n` delimits
/// a line ([`ReadProgress::LineReady`]), EOF, or the read would block.
///
/// Byte-at-a-time (not a 1024-byte chunk) so the leaf **never consumes past the
/// line delimiter** — fd 0 is shared with the REPL host's own line reader, and a
/// chunk read would steal the host's next line into [`STDIN_BUF`] (the FIXME 0551
/// (C) split-brain). Reading exactly up to `\n` leaves the remainder in the fd for
/// the next consumer, so neither side over-reads the other. `EINTR` retries;
/// `EWOULDBLOCK`/`EAGAIN` parks; a hard error is treated as terminal (EOF-shaped).
fn read_line_bytes(fd: i32, buf: &mut Vec<u8>) -> ReadProgress {
    loop {
        let mut b = [0u8; 1];
        // SAFETY: `fd` is valid; `b` is a valid 1-byte out-buffer.
        let n = unsafe { libc::read(fd, b.as_mut_ptr() as *mut c_void, 1) };
        if n > 0 {
            buf.push(b[0]);
            if b[0] == b'\n' {
                return ReadProgress::LineReady;
            }
        } else if n == 0 {
            return ReadProgress::Eof;
        } else {
            // SAFETY: read errno location after a failed `read`.
            let err = unsafe { *libc::__errno_location() };
            if err == libc::EWOULDBLOCK || err == libc::EAGAIN {
                return ReadProgress::WouldBlock;
            }
            if err == libc::EINTR {
                continue;
            }
            // Hard error: treat as a terminal so the strand does not wedge.
            return ReadProgress::Eof;
        }
    }
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
///
/// FIXME 0551 (A): fd 0's original flags are restored on every terminal
/// (`Ready`/EOF), never on `Park`.
fn poll_read_line(reactor: &Reactor) -> PollStep {
    set_stdin_nonblocking();
    // A complete line may already be buffered from a prior park.
    if let Some(line) = take_buffered_line() {
        restore_stdin_flags();
        let cls: CLString = line.into();
        return PollStep::Ready(cls.to_raw());
    }
    let progress = {
        let mut buf = STDIN_BUF.lock().expect("stdio STDIN_BUF mutex poisoned");
        read_line_bytes(0, &mut buf)
    };
    match progress {
        ReadProgress::LineReady => {
            // take_buffered_line removes exactly through the `\n`; the byte-wise
            // read stopped there, so nothing is left behind for the next reader.
            let line = take_buffered_line().unwrap_or_default();
            restore_stdin_flags();
            let cls: CLString = line.into();
            PollStep::Ready(cls.to_raw())
        }
        ReadProgress::Eof => {
            // EOF: return whatever remains as the last line (possibly empty).
            restore_stdin_flags();
            let cls: CLString = drain_buffered_all().into();
            PollStep::Ready(cls.to_raw())
        }
        ReadProgress::WouldBlock => {
            // Keep fd 0 non-blocking (flags NOT restored) for the re-poll; any
            // partial line stays buffered in STDIN_BUF across the park.
            reactor.wake_on_readable(0);
            PollStep::Park
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
    // v9 ctx-vtable (`poll-support.md §3.1`, resolves FIXME 0471 STRUCTURALLY):
    // stdin is a process SINGLETON with no handle to project a token from, so it
    // declares a MANIFEST-STATIC serial token. The poll-fn acquires that CONSTANT
    // (capacity 1) — admission then permits at most ONE in-flight `read-line` by
    // construction. `Parked` (a second concurrent `read-line`) ⇒ Pending before the
    // read; the host releases the STDIN permit on Ready/cancel.
    if matches!(reactor.acquire(STDIN_TOKEN, 1), Acquire::Parked) {
        return Poll::Pending;
    }
    let phase = PollState::new(&env);
    phase.drive(
        READ_LINE_ARMED,
        || poll_read_line(&reactor),
        || poll_read_line(&reactor),
    )
}

/// v9: the manifest-static SINGLETON serial token for stdin (`poll-support.md §3.1`).
/// A fixed non-zero token; the `read-line` poll-fn acquires it at capacity 1, so
/// admission enforces single-in-flight stdin by construction (resolves FIXME 0471).
const STDIN_TOKEN: u64 = 0x5354_4449_4E5F_544B; // "STDIN_TK" — any fixed non-zero value

/// The v9 SINGLETON-`Consume` descriptor `read-line` carries: role `Consume`,
/// a manifest-static serial `token` ([`STDIN_TOKEN`]) at `cardinality 1`, `blocking 0`
/// (poll-shape ⇒ the reactor carrier). The poll-fn acquires [`STDIN_TOKEN`] itself
/// via the `ctx` vtable — single-in-flight by construction, not a host special case.
const READ_LINE_DESC: ConcurrencyDescriptor = ConcurrencyDescriptor {
    token: STDIN_TOKEN,
    cardinality: 1,
    global_budget: 0,
    blocking: 0,
    role: ResourceRole::Consume,
    _reserved: [0; 2],
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
            descriptor: READ_LINE_DESC,
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A pipe pair as a stand-in for a borrowed shared fd. Returns (read, write).
    fn pipe() -> (i32, i32) {
        let mut fds = [0i32; 2];
        assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0, "pipe() failed");
        (fds[0], fds[1])
    }

    fn is_nonblocking(fd: i32) -> bool {
        let f = unsafe { libc::fcntl(fd, libc::F_GETFL) };
        f >= 0 && (f & libc::O_NONBLOCK) != 0
    }

    // FIXME 0551 (A): the poll leaf must return a borrowed shared fd AS FOUND —
    // set O_NONBLOCK for the non-blocking read, restore the captured original on
    // the terminal. This round-trips the (A) mechanism on a pipe fd (fd 0 is the
    // test runner's own stdin, unsafe to mutate in a parallel harness).
    #[test]
    fn fd_flags_capture_and_restore_round_trips() {
        let (r, w) = pipe();
        let orig = unsafe { libc::fcntl(r, libc::F_GETFL) };
        assert_eq!(orig & libc::O_NONBLOCK, 0, "pipe read end starts blocking");
        set_fd_nonblocking(r);
        assert!(is_nonblocking(r), "set_fd_nonblocking sets O_NONBLOCK");
        restore_fd_flags(r, orig);
        assert!(
            !is_nonblocking(r),
            "restore_fd_flags returns the fd as found (O_NONBLOCK cleared)"
        );
        unsafe {
            libc::close(r);
            libc::close(w);
        }
    }

    // FIXME 0551 (C-proximate): the read leaf must not consume past the line
    // delimiter — it reads exactly one line and leaves the remainder in the fd for
    // the next reader (the REPL host), so it never steals the host's next line.
    #[test]
    fn read_line_bytes_reads_exactly_one_line_no_overread() {
        let (r, w) = pipe();
        let data = b"hello\nworld\n";
        assert_eq!(
            unsafe { libc::write(w, data.as_ptr() as *const c_void, data.len()) },
            data.len() as isize
        );
        let mut buf = Vec::new();
        assert_eq!(read_line_bytes(r, &mut buf), ReadProgress::LineReady);
        assert_eq!(buf, b"hello\n", "read exactly the first line, no over-read");
        // The second line is still on the fd — NOT stolen into a private buffer.
        let mut buf2 = Vec::new();
        assert_eq!(read_line_bytes(r, &mut buf2), ReadProgress::LineReady);
        assert_eq!(buf2, b"world\n");
        unsafe {
            libc::close(r);
            libc::close(w);
        }
    }

    // FIXME 0551 (B, platform half): a would-block read is distinct from EOF —
    // the leaf parks on WouldBlock and only reports Eof when the writer closes.
    #[test]
    fn read_line_bytes_distinguishes_would_block_from_eof() {
        let (r, w) = pipe();
        set_fd_nonblocking(r);
        let mut buf = Vec::new();
        // No data yet, non-blocking → WouldBlock (NOT Eof).
        assert_eq!(read_line_bytes(r, &mut buf), ReadProgress::WouldBlock);
        assert!(buf.is_empty());
        // Writer closes → genuine EOF.
        unsafe { libc::close(w) };
        assert_eq!(read_line_bytes(r, &mut buf), ReadProgress::Eof);
        unsafe { libc::close(r) };
    }
}
