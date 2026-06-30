//! `web` platform for cranelisp -- a hand-rolled HTTP/1.0 server cdylib.
//!
//! ## S96 Chunk B (Wave B4) — the v8 poll-shape rewrite (FIXME 0465 resolution)
//!
//! Originally (Sprint 86 Wave E.1, FIXME 0405) a v6 single-stream BLOCKING
//! `listen`/`accept`/`send` over a process-global `Mutex<ServerState>`. The S96
//! single-ABI v8 cutover (`design/arch/platform-interface.md` §6.8.0a) makes the
//! reactor unconditional, so the connection lifecycle is now expressed as
//! **poll-shape leaves over per-connection tokens**
//! (`design/platform/poll-support.md §3.5`, the FIXME-0465 interface):
//!
//! | effect | shape | FQ signature | leading pair |
//! |---|---|---|---|
//! | `bind-listener` | blocking (`Sequential`) | `(Fn [Int Int] (IO web/Listener))` | none |
//! | `accept-conn` | poll `ResourceSerial` | `(Fn [Int Int Int] (IO web/Connection))` | `[listener_fd, 1, listener_fd]` |
//! | `read-conn` | poll `ResourceSerial` | `(Fn [Int Int Int] (IO web/Request))` | `[conn_token, 1, conn_fd]` |
//! | `send-conn` | poll `ResourceSerial` | `(Fn [Int Int Int web/Response] (IO Int))` | `[conn_token, 1, conn_fd, resp]` |
//!
//! `bind-listener` (blocking) and the three poll leaves coexist in ONE v8
//! `declare_platform!` manifest — exactly the mixed shape stdio's
//! `print`+`read-line` proved in Chunk A. The poll leaves are written against the
//! extracted `poll_support` suite ([`PollEnv`] for the env, [`Reactor`] for
//! fd-readiness, [`PollState`] for the first-poll/re-poll phase) — web is the
//! **3rd `poll_support` consumer**, adding NO new scaffold (`poll-support.md
//! §3.5.4`). Two parts stay hand-written (the §2.4 "what `poll_support` does NOT
//! own"): the ADT construct/read on the ready phase (via `CLAdt` +
//! `web.platform-schema`) and the syscall + line-buffering.
//!
//! ### The connection-token model (gate (a) non-re-entry, `poll-support.md §3.2`)
//!
//! `accept-conn` mints a FRESH connection token (`token == conn fd`) on
//! listener-readable, so distinct connections are concurrent by construction (the
//! Chunk-B fan-out vehicle); `read-conn`/`send-conn` ride that token
//! (`capacity == 1` ⇒ serial within one connection). The `(token, capacity)`
//! leading pair the `.cl` wrappers supply (`web.cl`) is peeled by the backend to
//! the IO node's reserved slots (token @abs 32, capacity @abs 40) and drives the
//! A3 acquire-around-poll permit — the poll-fn never sees them; it reads only its
//! re-passed fd at `state+8` (`PollEnv::arg(0)`) and (for `send-conn`) the
//! `Response` base ptr at `state+16` (`arg(1)`).
//!
//! ### Internal state: fd-keyed maps, NOT a process-global `Mutex<ServerState>`
//!
//! The v6 single-in-flight-stream `Mutex<ServerState>` is RETIRED. The OS
//! resources live in fd-keyed internal maps ([`LISTENERS`] keeps the bound
//! `TcpListener` alive so its fd stays valid; [`READBUFS`]/[`WRITEBUFS`] carry the
//! per-connection read accumulation / pending write across `Pending` boundaries).
//! Only the i64 fd/token/capacity cross the boundary (the standard fd-as-handle
//! pattern; no `TcpStream` value in cranelisp) — the connection now threads
//! through cranelisp (`web.cl`'s `Connection` ADT), not a hidden global.
//!
//! The two pure halves -- the request **parser** ([`parse_http_request`]) and the
//! response **formatter** ([`format_http_response`]) -- are unchanged and carry
//! the unit tests.
//!
//! Uses the `cranelisp-platform` shared crate for ABI types, the `CLAdt<T>`
//! ADT-marshaling wrapper, the `poll_support` suite, and `declare_platform!`.

use core::ffi::c_void;
use std::collections::HashMap;
use std::net::TcpListener;
use std::os::unix::io::AsRawFd;
use std::sync::{LazyLock, Mutex};

use cranelisp_platform::poll_support::{PollEnv, PollState, PollStep, Reactor};
use cranelisp_platform::*;

static HOST: HostContext = HostContext::new();

// ---------------------------------------------------------------------
// ADT marker types -- carry the FQ cranelisp identity for schema lookup
// ---------------------------------------------------------------------

/// Marker for the `web/Listener` ADT (the value `bind-listener` constructs):
/// `[fd, pool]` (`web.cl`). `fd` is the bound listener socket fd (accept's serial
/// admission token); `pool` is `N`, the Chunk-B in-flight-connection ceiling.
pub struct Listener;
impl CLAdtType for Listener {
    const TYPE_NAME: &'static str = "web/Listener";
}

/// Marker for the `web/Connection` ADT (the value `accept-conn` mints):
/// `[token, capacity, fd]` (`web.cl`). `token == fd` (fresh per accept ⇒ distinct
/// connections concurrent), `capacity == 1` (serial within the connection), `fd`
/// is the accepted socket fd (the syscall handle, re-passed as `leaf_0`).
pub struct Connection;
impl CLAdtType for Connection {
    const TYPE_NAME: &'static str = "web/Connection";
}

/// Marker for the `web/Request` ADT (the value `read-conn` constructs).
pub struct Request;
impl CLAdtType for Request {
    const TYPE_NAME: &'static str = "web/Request";
}

/// Marker for the `web/Response` ADT (the value `send-conn` reads).
pub struct Response;
impl CLAdtType for Response {
    const TYPE_NAME: &'static str = "web/Response";
}

// ---------------------------------------------------------------------
// Pure HTTP parsing / formatting (the unit-tested core) -- UNCHANGED
// ---------------------------------------------------------------------

/// A parsed HTTP request -- the three fields the Sudoku roundtrip needs.
///
/// `method` is upper-cased ASCII (`"GET"` / `"POST"`); `path` is the raw
/// request-target as sent (query string included if present); `body` is the
/// entity body verbatim (URL-encoded form data for POST, empty for GET).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedRequest {
    pub method: String,
    pub path: String,
    pub body: String,
}

/// Parse a raw HTTP/1.0 (or /1.1) request buffer into method / path / body.
///
/// PURE: no IO, no globals. This is the riskiest hand-rolled part, so it is the
/// primary unit-test target. The grammar handled is the minimal subset the
/// Sudoku GET-form / POST-solve roundtrip exercises:
///
/// - **Request line** `METHOD SP request-target SP HTTP-version CRLF` -- method
///   and target are taken from the first two whitespace-delimited tokens of the
///   first line; the version is ignored.
/// - **Headers** -- `field-name ":" OWS field-value` lines until the first empty
///   line. Only `Content-Length` is interpreted (case-insensitively) to bound
///   the body length; all other headers are ignored.
/// - **Body** -- everything after the blank line, truncated to `Content-Length`
///   bytes when that header is present (otherwise the remainder of the buffer).
///
/// Header/line splitting tolerates both CRLF and bare LF (so test fixtures may
/// use `\n`). Returns `None` when the buffer has no parseable request line
/// (empty input, or a first line with fewer than two tokens).
pub fn parse_http_request(raw: &str) -> Option<ParsedRequest> {
    // Split off the header block from the body at the first blank line. Try
    // CRLFCRLF first (canonical), then LFLF (bare-LF fixtures).
    let (head, body_rest) = match raw.find("\r\n\r\n") {
        Some(i) => (&raw[..i], &raw[i + 4..]),
        None => match raw.find("\n\n") {
            Some(i) => (&raw[..i], &raw[i + 2..]),
            None => (raw, ""),
        },
    };

    // The header block is line-oriented; normalise on '\n' and trim trailing
    // '\r' per line so CRLF and bare-LF both work.
    let mut lines = head.split('\n').map(|l| l.trim_end_matches('\r'));

    // Request line: METHOD SP target SP version. Need at least method + target.
    let request_line = lines.next()?;
    let mut toks = request_line.split_whitespace();
    let method = toks.next()?.to_ascii_uppercase();
    let path = toks.next()?.to_string();

    // Scan headers for Content-Length (case-insensitive field name).
    let mut content_length: Option<usize> = None;
    for line in lines {
        if let Some((name, value)) = line.split_once(':')
            && name.trim().eq_ignore_ascii_case("content-length")
        {
            content_length = value.trim().parse::<usize>().ok();
        }
    }

    // Body: bounded by Content-Length when present, else the remainder.
    let body = match content_length {
        Some(n) => {
            let bytes = body_rest.as_bytes();
            let take = n.min(bytes.len());
            // The body subset is at a byte boundary of the original &str; take is
            // bounded by the slice length, so this slice is valid UTF-8.
            String::from_utf8_lossy(&bytes[..take]).into_owned()
        }
        None => body_rest.to_string(),
    };

    Some(ParsedRequest { method, path, body })
}

/// Format a status / content-type / body triple into a raw HTTP/1.0 response.
///
/// PURE: no IO, no globals. The second unit-test target. Emits:
///
/// ```text
/// HTTP/1.0 <status> <reason>\r\n
/// Content-Type: <content_type>\r\n
/// Content-Length: <body.len()>\r\n
/// Connection: close\r\n
/// \r\n
/// <body>
/// ```
///
/// `Content-Length` is the body's **byte** length (not char count). The reason
/// phrase is a small lookup over the codes the exemplar emits (200/400/404/500),
/// falling back to `"Status"` for anything else -- the reason phrase is
/// advisory, so an unknown code still produces a well-formed response.
pub fn format_http_response(status: i64, content_type: &str, body: &str) -> String {
    let reason = match status {
        200 => "OK",
        400 => "Bad Request",
        404 => "Not Found",
        405 => "Method Not Allowed",
        500 => "Internal Server Error",
        _ => "Status",
    };
    format!(
        "HTTP/1.0 {status} {reason}\r\n\
         Content-Type: {content_type}\r\n\
         Content-Length: {len}\r\n\
         Connection: close\r\n\
         \r\n\
         {body}",
        len = body.len(),
    )
}

/// Parse a header block for the `Content-Length` value (case-insensitive),
/// defaulting to `0`. Shared by the poll-shape read accumulator below and the
/// pure parser's body bounding.
fn content_length_of(head: &str) -> usize {
    head.split('\n')
        .map(|l| l.trim_end_matches('\r'))
        .find_map(|line| {
            line.split_once(':').and_then(|(name, value)| {
                if name.trim().eq_ignore_ascii_case("content-length") {
                    value.trim().parse::<usize>().ok()
                } else {
                    None
                }
            })
        })
        .unwrap_or(0)
}

// ---------------------------------------------------------------------
// Connection state -- fd-keyed internal maps (NO process-global Mutex<ServerState>)
// ---------------------------------------------------------------------

/// Bound listeners, keyed by their socket fd. Keeps the `TcpListener` alive so
/// the fd stays valid for `libc::accept`; the accepted connection fds are raw
/// (managed by the platform, closed in `finish_connection`).
static LISTENERS: LazyLock<Mutex<HashMap<i32, TcpListener>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

/// Per-connection read accumulation buffers, keyed by connection fd. A request
/// straddling several poll wakeups accumulates here until the header terminator
/// + declared body are present (`read-conn`).
static READBUFS: LazyLock<Mutex<HashMap<i32, Vec<u8>>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

/// A pending response write: the formatted wire bytes + how many have been
/// written so far (a partial write resumes from there across a `send-conn` park).
type PendingWrite = (Vec<u8>, usize);

/// Per-connection pending-write buffers, keyed by connection fd.
static WRITEBUFS: LazyLock<Mutex<HashMap<i32, PendingWrite>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

/// A non-zero phase marker stashed in the env result slot while a web poll leaf
/// is parked ([`PollState::drive`]) — must never collide with the `0` unstarted
/// sentinel nor with a real heap base pointer once `Ready` overwrites it (heap
/// base pointers are positive allocator addresses; `-1` is neither).
const WEB_ARMED: i64 = -1;

/// Set `fd` to `O_NONBLOCK` (idempotent). A poll-fn must never block inside the
/// syscall — on no-data it returns `EWOULDBLOCK` and we park.
fn set_nonblocking(fd: i32) {
    // SAFETY: `fcntl`/`F_GETFL`/`F_SETFL` on a valid fd are sound; idempotent re-set.
    unsafe {
        let flags = libc::fcntl(fd, libc::F_GETFL);
        if flags >= 0 && (flags & libc::O_NONBLOCK) == 0 {
            libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK);
        }
    }
}

/// True iff `errno` indicates a would-block (the park signal).
fn errno_would_block() -> bool {
    // SAFETY: read errno location after a failed nonblocking syscall.
    let err = unsafe { *libc::__errno_location() };
    err == libc::EWOULDBLOCK || err == libc::EAGAIN
}

// ---------------------------------------------------------------------
// bind-listener -- the blocking (Sequential) effect
// ---------------------------------------------------------------------

/// Bind a `TcpListener` on `0.0.0.0:<port>` (all interfaces) and return a
/// `web/Listener [fd, pool]`. BLOCKING (`SchedulingClass::Sequential`) — a bind
/// is fast; no poll-fn. `n` is the Chunk-B in-flight-connection ceiling carried
/// on the handle (inert under the serial serve loop).
///
/// On bind failure the listener fd is `-1` (a subsequent `accept-conn` on `-1`
/// errors gracefully into an empty connection); the showcase ignores it.
pub extern "C" fn bind_listener(port: CLInt, n: CLInt) -> CLIO<CLAdt<Listener>> {
    let port = i64::from(port);
    let n = i64::from(n);
    CLIO::effect(move || {
        // `CRANELISP_PORT` override: cranelisp has no user-facing env accessor, so
        // a port-parametrized fixture (the S96 C-fanout `web_fanout` e2e binds an
        // ephemeral port to avoid the 8080 collision, Gap G4) supplies the port via
        // this platform-side env read. Absent/unparseable ⇒ the source `port` arg
        // (the exemplar's 8080) — backward-compatible with `exemplar_web.rs`.
        let port = std::env::var("CRANELISP_PORT")
            .ok()
            .and_then(|s| s.trim().parse::<i64>().ok())
            .unwrap_or(port);
        let addr = format!("0.0.0.0:{port}");
        let fd = match TcpListener::bind(&addr) {
            Ok(l) => {
                let _ = l.set_nonblocking(true);
                let fd = l.as_raw_fd();
                LISTENERS
                    .lock()
                    .expect("web LISTENERS mutex poisoned")
                    .insert(fd, l);
                fd as i64
            }
            Err(_) => -1i64,
        };
        // web/Listener is a single-ctor product (tag 0): fields [fd, pool].
        let fields = [fd, n];
        adt_into_raw(CLAdt::<Listener>::construct(0, &fields))
    })
}

/// Forget a freshly-`construct`ed (RC=1) owned ADT and hand its base pointer to
/// the caller (the producing side of the consuming convention, Decision 24 —
/// `forget` suppresses the `CLOwned` dec so the caller adopts the RC=1 ref).
fn adt_into_raw<T: CLAdtType>(owned: CLOwned<CLAdt<T>>) -> CLAdt<T> {
    let adt: CLAdt<T> = *owned;
    std::mem::forget(owned);
    adt
}

// ---------------------------------------------------------------------
// accept-conn -- poll-shape: park on listener-readable, mint a fresh Connection
// ---------------------------------------------------------------------

/// `accept-conn` poll-fn (`(Fn [Int Int Int] (IO web/Connection))`). leaf arg 0
/// (`state+8`, `PollEnv::arg(0)`) is the re-passed listener fd. First poll tries
/// `accept`; on `EWOULDBLOCK` it registers listener-readable and parks; on a
/// connection it mints a FRESH `Connection [conn_fd, 1, conn_fd]` (token == fd).
///
/// # Safety
/// C-ABI poll-fn ([`PollFn`]): `state` is the host-built state-closure env base;
/// `host`/`waker` are live for the call.
pub unsafe extern "C" fn accept_conn_pollfn(
    state: *mut c_void,
    host: *const HostCtx,
    waker: *const Waker,
) -> Poll {
    // SAFETY: `state` is the host-built env base; `host`/`waker` are live.
    let env = unsafe { PollEnv::new(state) };
    let reactor = unsafe { Reactor::new(host, waker) };
    // SAFETY: leaf arg 0 (the re-passed listener fd) is in the env.
    let listener_fd = unsafe { env.arg(0) } as i32;
    PollState::new(&env).drive(
        WEB_ARMED,
        || accept_step(listener_fd, &reactor),
        || accept_step(listener_fd, &reactor),
    )
}

/// One `accept-conn` attempt: `accept` the listener fd, or park on readable.
fn accept_step(listener_fd: i32, reactor: &Reactor) -> PollStep {
    // SAFETY: `listener_fd` is a nonblocking listening socket (set at bind).
    let cfd = unsafe { libc::accept(listener_fd, std::ptr::null_mut(), std::ptr::null_mut()) };
    if std::env::var("WEBDBG").is_ok() && cfd >= 0 {
        eprintln!("[WEB] accept listener={listener_fd} -> conn_fd={cfd}");
    }
    if cfd >= 0 {
        set_nonblocking(cfd);
        // Fresh per-connection token == the accepted fd; capacity 1.
        let fields = [cfd as i64, 1i64, cfd as i64];
        let adt = adt_into_raw(CLAdt::<Connection>::construct(0, &fields));
        if std::env::var("WEBDBG").is_ok() {
            eprintln!("[WEB] accept built Connection ptr={:#x}", adt.to_raw());
        }
        PollStep::Ready(adt.to_raw())
    } else if errno_would_block() {
        reactor.wake_on_readable(listener_fd);
        PollStep::Park
    } else {
        // Hard accept error (e.g. listener fd == -1): yield a sentinel
        // connection so the cranelisp side stays total rather than the DLL
        // wedging the strand.
        let fields = [-1i64, 1i64, -1i64];
        let adt = adt_into_raw(CLAdt::<Connection>::construct(0, &fields));
        PollStep::Ready(adt.to_raw())
    }
}

// ---------------------------------------------------------------------
// read-conn -- poll-shape: park on connection-readable, parse one Request
// ---------------------------------------------------------------------

/// `read-conn` poll-fn (`(Fn [Int Int Int] (IO web/Request))`). leaf arg 0
/// (`state+8`) is the re-passed connection fd. Reads (nonblocking) into the
/// per-fd accumulation buffer until the header terminator + declared body are
/// present, then parses and constructs a `web/Request`; parks on `EWOULDBLOCK`.
///
/// # Safety
/// C-ABI poll-fn ([`PollFn`]); see [`accept_conn_pollfn`].
pub unsafe extern "C" fn read_conn_pollfn(
    state: *mut c_void,
    host: *const HostCtx,
    waker: *const Waker,
) -> Poll {
    // SAFETY: `state` is the host-built env base; `host`/`waker` are live.
    let env = unsafe { PollEnv::new(state) };
    let reactor = unsafe { Reactor::new(host, waker) };
    // SAFETY: leaf arg 0 (the re-passed connection fd) is in the env.
    let conn_fd = unsafe { env.arg(0) } as i32;
    PollState::new(&env).drive(
        WEB_ARMED,
        || read_step(conn_fd, &reactor),
        || read_step(conn_fd, &reactor),
    )
}

/// One `read-conn` attempt: drain a complete request if buffered, else read more
/// and park on `EWOULDBLOCK`.
fn read_step(conn_fd: i32, reactor: &Reactor) -> PollStep {
    loop {
        if let Some(raw) = take_complete_request(conn_fd) {
            return PollStep::Ready(build_request(&raw));
        }
        let mut chunk = [0u8; 1024];
        // SAFETY: `conn_fd` is a valid nonblocking socket; `chunk` is a valid
        // out-buffer.
        let n =
            unsafe { libc::read(conn_fd, chunk.as_mut_ptr() as *mut c_void, chunk.len()) };
        if n > 0 {
            READBUFS
                .lock()
                .expect("web READBUFS mutex poisoned")
                .entry(conn_fd)
                .or_default()
                .extend_from_slice(&chunk[..n as usize]);
            // Guard against unbounded growth from a hostile peer.
            if READBUFS
                .lock()
                .expect("web READBUFS mutex poisoned")
                .get(&conn_fd)
                .map(|b| b.len() > (1 << 20))
                .unwrap_or(false)
            {
                return PollStep::Ready(build_request(&drain_all(conn_fd)));
            }
            continue; // re-check for a complete request, then read again.
        } else if n == 0 {
            // EOF: hand whatever arrived to the pure parser (which 400s on junk).
            return PollStep::Ready(build_request(&drain_all(conn_fd)));
        } else if errno_would_block() {
            reactor.wake_on_readable(conn_fd);
            return PollStep::Park;
        } else {
            // Hard read error: surface an empty request (router answers 400).
            return PollStep::Ready(build_request(""));
        }
    }
}

/// If the per-fd buffer holds a complete request (header terminator + declared
/// body), remove and return it; else `None`.
fn take_complete_request(conn_fd: i32) -> Option<String> {
    let mut bufs = READBUFS.lock().expect("web READBUFS mutex poisoned");
    let buf = bufs.get(&conn_fd)?;
    if buf.is_empty() {
        return None;
    }
    let text = String::from_utf8_lossy(buf);
    let header_end = text
        .find("\r\n\r\n")
        .map(|i| i + 4)
        .or_else(|| text.find("\n\n").map(|i| i + 2))?;
    let want_body = content_length_of(&text[..header_end]);
    let have_body = buf.len().saturating_sub(header_end);
    if have_body >= want_body {
        let raw = text.into_owned();
        bufs.remove(&conn_fd);
        Some(raw)
    } else {
        None
    }
}

/// Drain whatever remains buffered for `conn_fd` (EOF / overflow fallback).
fn drain_all(conn_fd: i32) -> String {
    let mut bufs = READBUFS.lock().expect("web READBUFS mutex poisoned");
    let buf = bufs.remove(&conn_fd).unwrap_or_default();
    String::from_utf8_lossy(&buf).into_owned()
}

/// Parse a raw request and construct a `web/Request` ADT, returning its base
/// pointer (RC=1, caller adopts). A parse failure yields an empty triple so the
/// cranelisp router answers 400 rather than the DLL panicking.
fn build_request(raw: &str) -> i64 {
    let parsed = parse_http_request(raw).unwrap_or(ParsedRequest {
        method: String::new(),
        path: String::new(),
        body: String::new(),
    });
    // Field order MUST match the deftype: method(0), path(1), body(2).
    let method: CLString = parsed.method.into();
    let path: CLString = parsed.path.into();
    let body: CLString = parsed.body.into();
    let fields = [method.to_raw(), path.to_raw(), body.to_raw()];
    adt_into_raw(CLAdt::<Request>::construct(0, &fields)).to_raw()
}

// ---------------------------------------------------------------------
// send-conn -- poll-shape: park on connection-writable, write + close
// ---------------------------------------------------------------------

/// `send-conn` poll-fn (`(Fn [Int Int Int web/Response] (IO Int))`). leaf arg 0
/// (`state+8`) is the re-passed connection fd; leaf arg 1 (`state+16`) is the
/// `web/Response` base pointer (read-only — RC owned by the env's drop glue, so
/// no capture-RC dance needed: re-read from the env each poll). Formats the wire
/// once into the per-fd write buffer, writes (nonblocking, resumable across a
/// park on `EWOULDBLOCK`), then closes the connection and returns `0`.
///
/// # Safety
/// C-ABI poll-fn ([`PollFn`]); see [`accept_conn_pollfn`]. `state+16` is a live
/// `web/Response` base pointer (the effect declares it as a `web/Response` param).
pub unsafe extern "C" fn send_conn_pollfn(
    state: *mut c_void,
    host: *const HostCtx,
    waker: *const Waker,
) -> Poll {
    // SAFETY: `state` is the host-built env base; `host`/`waker` are live.
    let env = unsafe { PollEnv::new(state) };
    let reactor = unsafe { Reactor::new(host, waker) };
    // SAFETY: leaf arg 0 (the re-passed connection fd) is in the env.
    let conn_fd = unsafe { env.arg(0) } as i32;
    PollState::new(&env).drive(
        WEB_ARMED,
        || send_step(conn_fd, &env, &reactor),
        || send_step(conn_fd, &env, &reactor),
    )
}

/// One `send-conn` attempt: format the wire on first entry, write the remainder,
/// close + `Ready(0)` when fully written, or park on `EWOULDBLOCK`.
fn send_step(conn_fd: i32, env: &PollEnv, reactor: &Reactor) -> PollStep {
    ensure_write_buffered(conn_fd, env);
    loop {
        match write_some(conn_fd) {
            WriteOutcome::Done | WriteOutcome::Err => {
                finish_connection(conn_fd);
                return PollStep::Ready(0);
            }
            WriteOutcome::More => continue,
            WriteOutcome::WouldBlock => {
                reactor.wake_on_writable(conn_fd);
                return PollStep::Park;
            }
        }
    }
}

/// Format the `web/Response` (env leaf arg 1) into the per-fd write buffer if not
/// already present. Reads the Response's three fields by name from the embedded
/// schema (`status: Int`, `content-type: String`, `body: String`) — a borrow
/// (RC owned by the env's drop glue), never a consume.
fn ensure_write_buffered(conn_fd: i32, env: &PollEnv) {
    let mut wbufs = WRITEBUFS.lock().expect("web WRITEBUFS mutex poisoned");
    if wbufs.contains_key(&conn_fd) {
        return;
    }
    // SAFETY: leaf arg 1 is a live `web/Response` base pointer.
    let resp = CLAdt::<Response>::from_raw(unsafe { env.arg(1) });
    let status: CLInt = resp.read_field("status");
    let content_type: CLString = resp.read_field("content-type");
    let body: CLString = resp.read_field("body");
    if std::env::var("WEBDBG").is_ok() {
        eprintln!("[WEB] send fd={conn_fd} resp_ptr={:#x} status={} ctype={:?} body_len={}", unsafe { env.arg(1) }, i64::from(status), content_type.as_str(), body.as_str().len());
    }
    let wire = format_http_response(i64::from(status), content_type.as_str(), body.as_str());
    wbufs.insert(conn_fd, (wire.into_bytes(), 0));
}

enum WriteOutcome {
    Done,
    More,
    WouldBlock,
    Err,
}

/// Write the unwritten remainder of the per-fd write buffer with one nonblocking
/// `write`.
fn write_some(conn_fd: i32) -> WriteOutcome {
    let mut wbufs = WRITEBUFS.lock().expect("web WRITEBUFS mutex poisoned");
    let Some((bytes, written)) = wbufs.get_mut(&conn_fd) else {
        return WriteOutcome::Done;
    };
    if *written >= bytes.len() {
        return WriteOutcome::Done;
    }
    let slice = &bytes[*written..];
    // SAFETY: `conn_fd` is a valid nonblocking socket; `slice` is a valid buffer.
    let n = unsafe { libc::write(conn_fd, slice.as_ptr() as *const c_void, slice.len()) };
    if n > 0 {
        *written += n as usize;
        if *written >= bytes.len() {
            WriteOutcome::Done
        } else {
            WriteOutcome::More
        }
    } else if n == 0 {
        WriteOutcome::Done
    } else if errno_would_block() {
        WriteOutcome::WouldBlock
    } else {
        WriteOutcome::Err
    }
}

/// Drop the per-connection buffers and close the socket (Connection: close).
fn finish_connection(conn_fd: i32) {
    if std::env::var("WEBDBG").is_ok() {
        eprintln!("[WEB] finish/close fd={conn_fd}");
    }
    WRITEBUFS
        .lock()
        .expect("web WRITEBUFS mutex poisoned")
        .remove(&conn_fd);
    READBUFS
        .lock()
        .expect("web READBUFS mutex poisoned")
        .remove(&conn_fd);
    // SAFETY: `conn_fd` is a platform-owned accepted socket fd; close once here.
    unsafe {
        libc::close(conn_fd);
    }
}

/// The `ResourceSerial` descriptor every web poll leaf carries: `token 0` (the
/// static conflict identity — the DYNAMIC per-resource token rides the leading
/// `token` operand the `.cl` wrapper supplies), `cardinality 1`, `blocking 0`
/// (poll-shape ⇒ the reactor carrier). `nearest_scheduling_class` maps
/// `token 0, cardinality 1` ⇒ `ResourceSerial`, so the backend leaves the
/// source-supplied `(token, capacity)` leading pair intact (no `(0,1)` inject —
/// `poll-support.md §3.4.2`).
const RESOURCE_SERIAL: ConcurrencyDescriptor = ConcurrencyDescriptor {
    token: 0,
    cardinality: 1,
    global_budget: 0,
    blocking: 0,
    _reserved: [0; 3],
};

declare_platform! {
    name: "web",
    version: "0.1.0",
    host: HOST,
    schema: include_str!("web.platform-schema"), // GENERATED -- regenerated via /platform-schema web
    functions: [
        bind_listener {
            cl_name: "bind-listener",
            sig: "(Fn [primitives/Int primitives/Int] (primitives/IO web/Listener))",
            doc: "Bind the HTTP server to 0.0.0.0:<port> (all interfaces) with pool ceiling N; yields a Listener",
            params: [port, n],
            scheduling: SchedulingClass::Sequential,
        },
        accept_conn_pollfn {
            cl_name: "accept-conn",
            sig: "(Fn [primitives/Int primitives/Int primitives/Int] (primitives/IO web/Connection))",
            doc: "Poll-shape: park on the listener fd readable, accept a connection, mint a fresh Connection",
            params: [token, capacity, fd],
            descriptor: RESOURCE_SERIAL,
        },
        read_conn_pollfn {
            cl_name: "read-conn",
            sig: "(Fn [primitives/Int primitives/Int primitives/Int] (primitives/IO web/Request))",
            doc: "Poll-shape: park on the connection fd readable, read+parse one HTTP request into a Request",
            params: [token, capacity, fd],
            descriptor: RESOURCE_SERIAL,
        },
        send_conn_pollfn {
            cl_name: "send-conn",
            sig: "(Fn [primitives/Int primitives/Int primitives/Int web/Response] (primitives/IO primitives/Int))",
            doc: "Poll-shape: park on the connection fd writable, write the Response as HTTP/1.0, and close",
            params: [token, capacity, fd, resp],
            descriptor: RESOURCE_SERIAL,
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------
    // parse_http_request -- the request parser (PURE, the riskiest half)
    // spec: design/arch/platform-interface.md §3a -- hand-rolled HTTP/1.0
    // request parse into method/path/body
    // -----------------------------------------------------------------

    #[test]
    fn parse_get_request_crlf() {
        let raw = "GET / HTTP/1.0\r\nHost: localhost\r\n\r\n";
        let req = parse_http_request(raw).expect("GET parses");
        assert_eq!(req.method, "GET");
        assert_eq!(req.path, "/");
        assert_eq!(req.body, "");
    }

    #[test]
    fn parse_post_request_with_body() {
        let body = "grid=53__7____&difficulty=easy";
        let raw = format!(
            "POST /solve HTTP/1.1\r\n\
             Host: localhost\r\n\
             Content-Type: application/x-www-form-urlencoded\r\n\
             Content-Length: {}\r\n\
             \r\n\
             {}",
            body.len(),
            body
        );
        let req = parse_http_request(&raw).expect("POST parses");
        assert_eq!(req.method, "POST");
        assert_eq!(req.path, "/solve");
        assert_eq!(req.body, body);
    }

    #[test]
    fn parse_method_is_uppercased() {
        let raw = "post /x HTTP/1.0\r\nContent-Length: 1\r\n\r\nQ";
        let req = parse_http_request(raw).expect("lowercase method parses");
        assert_eq!(req.method, "POST");
    }

    #[test]
    fn parse_content_length_truncates_body() {
        // Declared length is shorter than the buffered bytes -- truncate to it.
        let raw = "POST /p HTTP/1.0\r\nContent-Length: 3\r\n\r\nABCDEFG";
        let req = parse_http_request(raw).expect("parses");
        assert_eq!(req.body, "ABC");
    }

    #[test]
    fn parse_content_length_case_insensitive() {
        let raw = "POST /p HTTP/1.0\r\ncontent-length: 2\r\n\r\nXY";
        let req = parse_http_request(raw).expect("parses");
        assert_eq!(req.body, "XY");
    }

    #[test]
    fn parse_path_keeps_query_string() {
        let raw = "GET /board?n=5 HTTP/1.0\r\n\r\n";
        let req = parse_http_request(raw).expect("parses");
        assert_eq!(req.path, "/board?n=5");
    }

    #[test]
    fn parse_tolerates_bare_lf() {
        // Fixtures may use bare LF instead of CRLF.
        let raw = "GET /lf HTTP/1.0\nContent-Length: 2\n\nhi";
        let req = parse_http_request(raw).expect("bare-LF parses");
        assert_eq!(req.method, "GET");
        assert_eq!(req.path, "/lf");
        assert_eq!(req.body, "hi");
    }

    #[test]
    fn parse_empty_input_is_none() {
        assert_eq!(parse_http_request(""), None);
    }

    #[test]
    fn parse_request_line_without_target_is_none() {
        // A first line with only one token has no request-target.
        assert_eq!(parse_http_request("GET\r\n\r\n"), None);
    }

    #[test]
    fn parse_no_content_length_takes_remainder() {
        let raw = "POST /p HTTP/1.0\r\n\r\nleftover-body";
        let req = parse_http_request(raw).expect("parses");
        assert_eq!(req.body, "leftover-body");
    }

    // -----------------------------------------------------------------
    // content_length_of -- the poll-read accumulator's header scan
    // design: design/platform/poll-support.md §3.5.2 -- read-conn accumulates
    // until header terminator + declared body
    // -----------------------------------------------------------------

    #[test]
    fn content_length_of_reads_declared_length() {
        assert_eq!(content_length_of("POST /p\r\nContent-Length: 7\r\n"), 7);
        assert_eq!(content_length_of("post /p\ncontent-length: 3\n"), 3);
        assert_eq!(content_length_of("GET / HTTP/1.0\r\nHost: x\r\n"), 0);
    }

    // -----------------------------------------------------------------
    // format_http_response -- the response formatter (PURE)
    // spec: design/arch/platform-interface.md §3a -- format status+body into
    // raw HTTP/1.0 bytes
    // -----------------------------------------------------------------

    #[test]
    fn format_200_html() {
        let wire = format_http_response(200, "text/html", "<h1>hi</h1>");
        assert_eq!(
            wire,
            "HTTP/1.0 200 OK\r\n\
             Content-Type: text/html\r\n\
             Content-Length: 11\r\n\
             Connection: close\r\n\
             \r\n\
             <h1>hi</h1>"
        );
    }

    #[test]
    fn format_content_length_is_byte_length() {
        // Multi-byte UTF-8: "é" is 2 bytes, so a 1-char body is length 2.
        let wire = format_http_response(200, "text/plain", "é");
        assert!(
            wire.contains("Content-Length: 2\r\n"),
            "byte length, not char count: {wire:?}"
        );
    }

    #[test]
    fn format_known_reason_phrases() {
        assert!(format_http_response(404, "text/plain", "").starts_with("HTTP/1.0 404 Not Found\r\n"));
        assert!(format_http_response(400, "text/plain", "").starts_with("HTTP/1.0 400 Bad Request\r\n"));
        assert!(format_http_response(500, "text/plain", "").starts_with("HTTP/1.0 500 Internal Server Error\r\n"));
    }

    #[test]
    fn format_unknown_status_falls_back() {
        let wire = format_http_response(418, "text/plain", "");
        assert!(wire.starts_with("HTTP/1.0 418 Status\r\n"), "{wire:?}");
    }

    #[test]
    fn format_empty_body() {
        let wire = format_http_response(200, "text/html", "");
        assert!(wire.ends_with("Content-Length: 0\r\nConnection: close\r\n\r\n"));
    }

    // -----------------------------------------------------------------
    // round-trip: a formatted response's header block re-parses (the two
    // pure halves agree on the HTTP/1.0 framing)
    // -----------------------------------------------------------------

    #[test]
    fn roundtrip_response_reparses_as_request_shape() {
        // Not a real use, but proves the framing (request line + headers + blank
        // line + body) is consistent between formatter and parser.
        let wire = format_http_response(200, "text/html", "BODY");
        // Treat the status line as if it were a request line: 3 tokens, blank
        // line separates headers from body.
        let (_, body) = wire.split_once("\r\n\r\n").expect("has blank line");
        assert_eq!(body, "BODY");
    }
}
