//! `web` platform for cranelisp -- a hand-rolled HTTP/1.0 server cdylib.
//!
//! Sprint 86 Wave E.1 (FIXME 0405). The Sudoku exemplar's browser front-end:
//! the first **effectful** application platform that marshals application-defined
//! ADTs (`web/Request`, `web/Response`) across the FFI boundary in production
//! (the `shapes` DLL was the test fixture that proved the path).
//!
//! ## Serve model: Model A only (platform-interface.md §3a)
//!
//! Three `SchedulingClass::Sequential` effect functions, all returning `IO _`:
//!
//! - `listen :: (Fn [Int] (IO Int))` -- bind a `TcpListener` on the given port.
//! - `accept :: (Fn [] (IO Request))` -- block until the next request arrives,
//!   read + parse one HTTP/1.0 request, and return it as a `web/Request` ADT.
//!   The accepted `TcpStream` is held until the matching `send`.
//! - `send :: (Fn [Response] (IO Int))` -- serialize a `web/Response` ADT to
//!   HTTP/1.0 and write it to the held connection, then close it.
//!
//! The cranelisp side drives a tail-recursive `serve-loop`
//! (`(accept) -> handle -> (send …) -> recur`). A blocking `accept()` inside a
//! `Sequential` effect thunk is legal -- the scheduling class is a compile-time
//! parallel-scheduling hint, not a runtime latency contract; the thunk is forced
//! synchronously on the calling thread (platform-interface.md §3a). Model B
//! (`serve` + closure callback) is a deferred platform-model gap (FIXME 0407).
//!
//! ## Request/Response are ordinary `.cl` ADTs, not opaque handles
//!
//! Per the third convergence, platforms do not declare ADTs. `Request` /
//! `Response` are ordinary `.cl` types (see `web.cl`), referenced FQ in the
//! sigs (`web/Request`, `web/Response`). The DLL **reads** request fields by
//! name via `CLAdt::read_field` (resolved against the embedded
//! `web.platform-schema`) and **constructs** a `Request` (and reads a
//! `Response`) via `CLAdt::construct` -> `HostCallbacks::alloc_with_tag`. Field
//! access on the cranelisp side is ordinary `match` / accessors -- there are no
//! `request-method` / `request-path` platform accessor functions.
//!
//! ## No external HTTP dependency
//!
//! The HTTP/1.0 roundtrip is hand-rolled over `std::net::TcpListener` -- a
//! single-threaded read-request / parse / write-response loop, no `tiny_http`
//! (or any) dependency. The two pure halves -- the request **parser**
//! ([`parse_http_request`]) and the response **formatter**
//! ([`format_http_response`]) -- are the riskiest part and carry unit tests.
//!
//! Uses the `cranelisp-platform` shared crate for ABI types, the `CLAdt<T>`
//! ADT-marshaling wrapper, and the `declare_platform!` macro.

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::Mutex;

use cranelisp_platform::*;

static HOST: HostContext = HostContext::new();

// ---------------------------------------------------------------------
// ADT marker types -- carry the FQ cranelisp identity for schema lookup
// ---------------------------------------------------------------------

/// Marker for the `web/Request` ADT (the value `accept` constructs).
pub struct Request;
impl CLAdtType for Request {
    const TYPE_NAME: &'static str = "web/Request";
}

/// Marker for the `web/Response` ADT (the value `send` reads).
pub struct Response;
impl CLAdtType for Response {
    const TYPE_NAME: &'static str = "web/Response";
}

// ---------------------------------------------------------------------
// Pure HTTP parsing / formatting (the unit-tested core)
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

/// Read a single HTTP request off a stream into a `String` buffer.
///
/// Reads in chunks until the header terminator (`\r\n\r\n` / `\n\n`) is seen,
/// then -- if a `Content-Length` is present and the body is short -- keeps
/// reading until the declared body length is available (or the peer closes).
/// Best-effort: a malformed/short request still hands whatever arrived to the
/// pure parser, which returns `None` and lets the caller respond with a 400.
fn read_request(stream: &mut TcpStream) -> std::io::Result<String> {
    let mut buf: Vec<u8> = Vec::with_capacity(1024);
    let mut chunk = [0u8; 1024];
    loop {
        let n = stream.read(&mut chunk)?;
        if n == 0 {
            break; // peer closed
        }
        buf.extend_from_slice(&chunk[..n]);

        // Have we seen the end of headers yet?
        let text = String::from_utf8_lossy(&buf);
        let header_end = text
            .find("\r\n\r\n")
            .map(|i| i + 4)
            .or_else(|| text.find("\n\n").map(|i| i + 2));
        if let Some(he) = header_end {
            // Determine the expected body length from Content-Length, if any.
            let head = &text[..he];
            let want_body = head
                .split('\n')
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
                .unwrap_or(0);
            let have_body = buf.len().saturating_sub(he);
            if have_body >= want_body {
                break;
            }
        }
        // Guard against unbounded growth from a hostile peer.
        if buf.len() > 1 << 20 {
            break;
        }
    }
    Ok(String::from_utf8_lossy(&buf).into_owned())
}

// ---------------------------------------------------------------------
// Connection state -- the listener + the in-flight accepted stream
// ---------------------------------------------------------------------

/// Per-DLL server state: the bound listener and the connection accepted by the
/// most recent `accept`, held until the matching `send` writes the response.
///
/// One DLL = one compilation unit, and Model A is single-threaded (one
/// accept -> handle -> send cycle at a time per `serve-loop` iteration), so a
/// single process-global behind a `Mutex` is the right cardinality. The `Mutex`
/// is for soundness (interior mutability of a `static`), not contention.
struct ServerState {
    listener: Option<TcpListener>,
    current: Option<TcpStream>,
}

static SERVER: Mutex<ServerState> = Mutex::new(ServerState {
    listener: None,
    current: None,
});

// ---------------------------------------------------------------------
// Effect functions (Model A) -- all SchedulingClass::Sequential, IO-returning
// ---------------------------------------------------------------------

/// Bind a `TcpListener` on `0.0.0.0:<port>` (all interfaces). Returns a deferred IO Effect
/// yielding `0` on success (or a negative code if the bind fails -- the cranelisp
/// caller can branch on it; the showcase ignores it).
///
/// No heap parameters, so no capture-RC; the `CLInt` port is a value type.
pub extern "C" fn listen(port: CLInt) -> CLIO<CLInt> {
    let port = i64::from(port);
    CLIO::effect(move || {
        let addr = format!("0.0.0.0:{port}");
        match TcpListener::bind(&addr) {
            Ok(l) => {
                let mut state = SERVER.lock().expect("web platform SERVER mutex poisoned");
                state.listener = Some(l);
                CLInt::from(0i64)
            }
            Err(_) => CLInt::from(-1i64),
        }
    })
}

/// Block until the next request arrives, read + parse it, and return a
/// `web/Request` ADT. The accepted `TcpStream` is stored for the matching
/// `send`. Returns a deferred IO Effect (the blocking accept runs when the
/// thunk is forced -- legal for a `Sequential` effect, §3a).
///
/// A request that fails to parse still yields a `Request` -- an empty
/// method/path/body triple -- so the cranelisp router can answer with a 400
/// rather than the DLL panicking.
///
/// ## ADT construction (mirrors the `shapes` precedent, inverted)
///
/// `Request` is a single-ctor product (tag 0) with three String fields in
/// declaration order `method`/`path`/`body`. We build three fresh `CLString`s
/// (RC=1 from the host allocator) and pass their base pointers to
/// `CLAdt::construct`, which routes through `HostCallbacks::alloc_with_tag`; the
/// field RCs transfer into the ADT. `construct` returns a `CLOwned` (RC=1); we
/// hand the value back across the boundary, so `into_raw` releases the owned
/// handle WITHOUT a dec -- the caller adopts the reference (the producing side
/// of the consuming convention, Decision 24, symmetric with `shapes`' consuming
/// read side).
pub extern "C" fn accept() -> CLIO<CLAdt<Request>> {
    CLIO::effect(move || {
        // Take the accepted stream (blocking) and read one request.
        let parsed = {
            let mut state = SERVER.lock().expect("web platform SERVER mutex poisoned");
            match state.listener.as_ref() {
                Some(listener) => match listener.accept() {
                    Ok((mut stream, _peer)) => {
                        let raw = read_request(&mut stream).unwrap_or_default();
                        // Hold the stream for the matching `send`.
                        state.current = Some(stream);
                        parse_http_request(&raw).unwrap_or(ParsedRequest {
                            method: String::new(),
                            path: String::new(),
                            body: String::new(),
                        })
                    }
                    Err(_) => ParsedRequest {
                        method: String::new(),
                        path: String::new(),
                        body: String::new(),
                    },
                },
                // `accept` before `listen` -- yield an empty request rather than
                // panic; the router answers 400/500.
                None => ParsedRequest {
                    method: String::new(),
                    path: String::new(),
                    body: String::new(),
                },
            }
        };

        // Build the three String fields, then the Request ADT. Field order MUST
        // match the deftype: method(0), path(1), body(2).
        let method: CLString = parsed.method.into();
        let path: CLString = parsed.path.into();
        let body: CLString = parsed.body.into();
        let fields = [method.to_raw(), path.to_raw(), body.to_raw()];
        let owned = CLAdt::<Request>::construct(0, &fields);
        // `construct` returns a CLOwned at RC=1. Hand that single reference to
        // the caller (producing side of the consuming convention, Decision 24):
        // copy out the transparent `CLAdt` value, then `mem::forget` the
        // CLOwned so its Drop does NOT dec -- the caller adopts the RC=1 ref.
        // (`CLOwned` exposes no `into_inner`; `forget` is the sanctioned way to
        // suppress the dec when transferring ownership outward. Net RC: alloc +1
        // -> forget (no dec) = caller holds 1.)
        let adt: CLAdt<Request> = *owned;
        std::mem::forget(owned);
        adt
    })
}

/// Serialize a `web/Response` ADT to HTTP/1.0 and write it to the held
/// connection, then drop the stream (Connection: close). Returns a deferred IO
/// Effect yielding `0`.
///
/// Reads the Response's three fields by name from the embedded schema:
/// `status: Int`, `content-type: String`, `body: String`.
pub extern "C" fn send(resp: CLAdt<Response>) -> CLIO<CLInt> {
    let owned = <CLAdt<Response> as CLHeap>::into_owned_consuming(resp);
    CLIO::effect(move || {
        let status: CLInt = owned.read_field("status");
        let content_type: CLString = owned.read_field("content-type");
        let body: CLString = owned.read_field("body");
        let wire = format_http_response(
            i64::from(status),
            content_type.as_str(),
            body.as_str(),
        );

        let mut state = SERVER.lock().expect("web platform SERVER mutex poisoned");
        if let Some(mut stream) = state.current.take() {
            let _ = stream.write_all(wire.as_bytes());
            let _ = stream.flush();
            // stream drops here -> connection closes.
        }
        CLInt::from(0i64)
    })
}

declare_platform! {
    name: "web",
    version: "0.1.0",
    host: HOST,
    schema: include_str!("web.platform-schema"), // GENERATED -- regenerated via /platform-schema web
    functions: [
        listen {
            cl_name: "listen",
            sig: "(Fn [primitives/Int] (primitives/IO primitives/Int))",
            doc: "Bind the HTTP server to 0.0.0.0:<port> (all interfaces); yields 0 on success",
            params: [port],
            scheduling: SchedulingClass::Sequential,
        },
        accept {
            cl_name: "accept",
            sig: "(Fn [] (primitives/IO web/Request))",
            doc: "Block until the next HTTP request arrives; return it as a Request",
            params: [],
            scheduling: SchedulingClass::Sequential,
        },
        send {
            cl_name: "send",
            sig: "(Fn [web/Response] (primitives/IO primitives/Int))",
            doc: "Write a Response as HTTP/1.0 to the current connection and close it",
            params: [resp],
            scheduling: SchedulingClass::Sequential,
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
