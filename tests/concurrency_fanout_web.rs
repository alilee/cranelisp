//! Sprint 96 — effect-concurrency C-fanout wave: the marquee "server with no
//! `spawn`" headline e2e (concurrent per-connection fan-out) + the web 500-mapping
//! + the now-un-deferred cancel-on-disconnect / graceful-shutdown web rows, PLUS
//! the launch-eligibility negative matrix (E1/E2/E3) observable face.
//!
//! Plan: `tests/plan/sprint-96.md` (CHUNK C) §C5b/§C5c + the C-fanout rows from
//! `design/arch/fixmes/0470-design-user-fn-launch-eligibility-server-fanout.md`
//! (/arch lighter-path ruling: option-2 inline-handler + local discarded-disjoint
//! sub-tree launch; eligibility predicate E1/E2/E3 at `effect-concurrency.md`
//! §4.1). Spec of record:
//!   - `spec/10-io.md` §10.12.7  (Launch-and-Continue — the fan-out, E1/E2/E3)
//!   - `spec/10-io.md` §10.12.10 (Reference Control Patterns — cancel-on-disconnect,
//!                                graceful shutdown)
//!   - `spec/12-runtime.md` §12.7.9 (Supervised Detached Strands — 500/log/drop)
//!
//! ## Posture (Wave-C1 = QA-first, RED-first / co-landing)
//!
//! **The web rows depend on the C-fanout /int + /port wave** (0470): /int extends
//! `bind_chain_analysis` to launch a discarded, locally-token-disjoint bind
//! SUB-TREE (E1/E2/E3); /port inlines the connection handler into the serve loop
//! down to platform leaves so the launch fires. Until then the serve loop runs
//! SERIALLY (`handle-conn` is a user fn `classify_expr` treats as `Sequential`).
//!
//! The rows are authored RED-first against a **port-parametrized poll-shape fan-out
//! web fixture** (the Gap-G4 fixture, co-landing with the /port C-fanout rewrite —
//! a port-configurable `main.cl` reading `CRANELISP_PORT`). On HEAD the fixture is
//! ABSENT, so the server child fails to start ⇒ the readiness probe surfaces the
//! early exit as a fast, loud RED (NOT a 20 s hang). The fixture is referenced by
//! path; an absent fixture is a clean runtime-RED, NOT a workspace-build break
//! (these tests shell out to the binary), per the Chunk-A/B deferred-web precedent.
//!
//! Each web row's dependency is marked:
//!   - **C-fanout** — needs only the /int sub-tree launch + /port inline fixture.
//!   - **C3 + C-fanout** — ALSO needs Chunk-C cancellation (cancel-on-disconnect /
//!     graceful shutdown cancel outstanding detached handler strands).
//!
//! ## Port isolation
//!
//! Every row binds an EPHEMERAL free port (bind `127.0.0.1:0`, read it back, pass
//! it to the fixture via `CRANELISP_PORT`) — so these rows never collide with
//! `tests/exemplar_web.rs` (fixed 8080) NOR with each other under parallel nextest.
//! This is the Gap-G4 resolution: a port-parametrized fixture + harness retires the
//! 8080 collision that deferred the Chunk-A/B web rows.

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, CrOutput};

// =============================================================================
// Raw-process port-parametrized web harness (the Gap-G4 deliverable, /qa-owned).
// Mirrors `tests/exemplar_web.rs`'s spawn_server / ServerGuard / http_request, but
// parametrized on (fixture-path, ephemeral-port) instead of the fixed exemplar +
// 8080. The `Cranelisp` builder runs the child to completion; an infinite web
// server is exactly the case it does not model, so we manage a raw `Child`.
// =============================================================================

/// The co-landing port-parametrized poll-shape fan-out web fixture (Gap G4).
/// Authored WITH the /port C-fanout serve-loop rewrite (inline handler → platform
/// leaves, port read from `CRANELISP_PORT`). Absent on HEAD ⇒ the spawn fails fast.
const FANOUT_FIXTURE: &str = "tests/fixtures/web_fanout/main.cl";

/// A deliberately-slow handler route in the fixture (≈ this many ms per request) —
/// the fan-out overlap witness. Co-landed in the fixture by /port.
const SLOW_ROUTE: &str = "/slow";
/// A fault-injecting route — the handler deliberately faults ⇒ the supervisor maps
/// it to a 500 for that request (§12.7.9). Co-landed in the fixture.
const FAULT_ROUTE: &str = "/fault";
/// A normal fast route (the form page / health check) — proves the server lives.
const OK_ROUTE: &str = "/";

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Reserve an ephemeral free TCP port (bind :0, read it, drop the listener). Small
/// TOCTOU window before the server re-binds it; acceptable for a per-test port.
fn free_port() -> u16 {
    let l = TcpListener::bind("127.0.0.1:0").expect("bind ephemeral port");
    l.local_addr().expect("local_addr").port()
}

/// RAII guard that kills + reaps the server child on drop, so a panicking assertion
/// never leaks the process (which would hold the port).
struct ServerGuard {
    child: Child,
}

impl ServerGuard {
    /// Send SIGTERM (graceful-shutdown signal) to the child; return whether it was
    /// delivered. Used by the graceful-shutdown row.
    fn signal_term(&self) -> bool {
        // Best-effort: `kill -TERM <pid>` (portable enough for the Linux CI lane).
        Command::new("kill")
            .arg("-TERM")
            .arg(self.child.id().to_string())
            .status()
            .map(|s| s.success())
            .unwrap_or(false)
    }
}

impl Drop for ServerGuard {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// Spawn `--run <fixture>` with the port + platform + stdlib env, then poll the
/// port until it accepts a connection. Surfaces an early child exit (e.g. the
/// fixture is ABSENT on HEAD ⇒ file-not-found ⇒ fast exit) as a loud panic rather
/// than spinning to the readiness deadline.
fn spawn_server(fixture_rel: &str, port: u16) -> ServerGuard {
    let root = workspace_root();
    let binary = root.join("target").join("debug").join("cranelisp");
    assert!(
        binary.exists(),
        "cranelisp binary not found at {} — run `cargo build` first",
        binary.display()
    );

    let child = Command::new(&binary)
        .current_dir(&root)
        .arg("--run")
        .arg(fixture_rel)
        .env("CRANELISP_PORT", port.to_string())
        .env("CRANELISP_PLATFORM_PATH", root.join("target").join("debug"))
        .env("CRANELISP_LIB", root.join("stdlib"))
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn fan-out web server");

    let mut guard = ServerGuard { child };

    let deadline = Instant::now() + Duration::from_secs(20);
    loop {
        if let Ok(Some(status)) = guard.child.try_wait() {
            panic!(
                "fan-out web server exited before listening (status {status:?}). \
                 The port-parametrized poll-shape fan-out fixture `{fixture_rel}` is \
                 a co-landing C-fanout deliverable (/port + /int 0470); it is absent \
                 on HEAD ⇒ this row is RED-first until that wave lands."
            );
        }
        if TcpStream::connect_timeout(
            &format!("127.0.0.1:{port}").parse().unwrap(),
            Duration::from_millis(200),
        )
        .is_ok()
        {
            break;
        }
        assert!(
            Instant::now() < deadline,
            "fan-out web server did not start listening on 127.0.0.1:{port} within 20s"
        );
        std::thread::sleep(Duration::from_millis(100));
    }
    guard
}

/// One HTTP/1.0 request on a fresh connection; return the full response.
fn http_request(port: u16, method: &str, path: &str) -> String {
    let mut stream =
        TcpStream::connect(format!("127.0.0.1:{port}")).expect("connect to fan-out server");
    stream.set_read_timeout(Some(Duration::from_secs(20))).unwrap();
    let request = format!("{method} {path} HTTP/1.0\r\n\r\n");
    stream.write_all(request.as_bytes()).expect("write request");
    stream.flush().ok();
    let mut response = String::new();
    stream.read_to_string(&mut response).expect("read response");
    response
}

// =============================================================================
// §C-fanout 1 — the marquee: concurrent per-connection fan-out (no `spawn`).
// =============================================================================

// spec: spec/10-io.md §10.12.7 — the reshaped fan-out serve loop (poll
// `accept`/`read`/`send` + launch-and-continue, NO `spawn`) serves K concurrent
// SLOW requests with wall-clock ≈ max NOT sum — the per-connection handlers OVERLAP
// (the accept loop did not serialise behind each handler; item 1 + item 4). The
// load-bearing assertion is the launch-and-continue fan-out (E1/E2/E3 over the
// inlined handler sub-tree). Dependency: C-fanout (/int sub-tree launch + /port
// inline fixture).
//
// S96 C4 + 0470 fix: the witness is DETERMINISTIC and GREEN — the web server
// GENUINELY FANS OUT. The fixture's /slow handler parks a real `(sleep 100)` (the C4
// timer leaf), so K=4 concurrent requests measure ≈1·D ≈ 110ms when OVERLAPPING vs
// ≈4·D ≈ 440ms when serial — a robustly discriminating ratio (the assertion below is
// `elapsed < one*K - one/2` = 3.5·one for K=4; overlap ≈1·one passes with wide
// margin). FIXME 0470 is RESOLVED: the cause was NOT an interprocedural wall — C4's
// `slow-delay` (a user fn returning IO) had been placed in an EFFECT POSITION,
// suppressing an inference that already fired for the pre-C4 handler. The fix admits
// the resource-free `sleep` timer as a launchable sub-tree effect MEMBER
// (`src/bind_chain_analysis.rs`, §4.1) and reshapes the fixture so every handler
// effect position is a direct leaf (`read-conn`/`send-conn` poll + `sleep` timer), so
// the whole `read→sleep→send` handler launches as one supervised strand and K
// connections overlap. The mechanism is independently proven by
// `tests/concurrency_fanout.rs::launch_and_continue_runs_concurrently_launcher_does_not_await`.
#[test]
fn web_server_fans_out_concurrent_requests_overlap() {
    let port = free_port();
    let _server = spawn_server(FANOUT_FIXTURE, port);

    // Fire K concurrent slow requests and measure the wall-clock of the slowest.
    const K: usize = 4;
    let start = Instant::now();
    let handles: Vec<_> = (0..K)
        .map(|_| std::thread::spawn(move || http_request(port, "GET", SLOW_ROUTE)))
        .collect();
    let mut bodies = Vec::new();
    for h in handles {
        bodies.push(h.join().expect("client thread"));
    }
    let elapsed = start.elapsed();

    // All K requests got a response.
    for (i, b) in bodies.iter().enumerate() {
        assert!(
            b.contains("200") || b.to_lowercase().contains("ok") || !b.is_empty(),
            "concurrent request {i} got no response body:\n{b}"
        );
    }

    // The fixture defines `SLOW_ROUTE` as a ≈D-ms handler. With the fan-out, K
    // concurrent slow requests OVERLAP ⇒ wall-clock ≈ 1·D, NOT serial ≈ K·D. We do
    // not know D exactly (fixture-defined), so the discriminating assertion is the
    // RATIO: K overlapping requests must take far less than K times one request.
    let one = {
        let s = Instant::now();
        let _ = http_request(port, "GET", SLOW_ROUTE);
        s.elapsed()
    };
    assert!(
        elapsed < one * (K as u32) - one / 2,
        "K={K} concurrent slow requests must OVERLAP (≈1·D, wall-clock {elapsed:?}) \
         not serialise (≈K·D ≈ {:?}); the serve loop did not fan out (launch-and-\
         continue not firing — 0470 / E1-E3 sub-tree launch)",
        one * (K as u32),
    );
}

// =============================================================================
// §C-fanout 2 — the web 500-mapping: a faulting handler → 500 for that request,
// the server keeps serving (the supervisor turns the panic into a response).
// =============================================================================

// spec: spec/12-runtime.md §12.7.9 — a request to a fault-injecting route gets a
// 500 / error response for THAT request (the supervisor maps the detached handler
// strand's `StrandFailed` to a 500, §10/§11), and a subsequent normal GET on a
// fresh connection STILL succeeds — the accept loop + supervising context outlived
// the fault. The load-bearing negative half: the fault did NOT kill the server.
// Dependency: C-fanout (a detached supervised handler strand to fault — only exists
// under the fan-out; with a serial loop there are no per-connection strands to map).
#[test]
fn web_handler_fault_yields_500_for_that_request_server_lives() {
    let port = free_port();
    let _server = spawn_server(FANOUT_FIXTURE, port);

    // The fault route → 500 for that request.
    let fault_resp = http_request(port, "GET", FAULT_ROUTE);
    assert!(
        fault_resp.contains("500"),
        "a faulting handler must yield a 500 for THAT request (the supervisor maps \
         the strand fault to a 500, §12.7.9); got:\n{fault_resp}"
    );

    // The server keeps serving: a subsequent normal GET still succeeds.
    let ok_resp = http_request(port, "GET", OK_ROUTE);
    assert!(
        !ok_resp.contains("500") && !ok_resp.is_empty(),
        "the server must KEEP SERVING after a handler fault (the fault must not kill \
         the accept loop / crash the process, §12.7.9); subsequent GET got:\n{ok_resp}"
    );
}

// =============================================================================
// §C5b — cancel-on-disconnect (a §10.12.10 reference pattern).
// =============================================================================

// spec: spec/10-io.md §10.12.10 — a client that disconnects mid-request has its
// per-connection handler CANCELLED (`race handler (await-disconnect conn)`): the
// in-flight handler poll is dropped, its resources released (§10.12.9), and the
// server keeps serving subsequent requests. Dependency: C3 + C-fanout (needs the
// concurrent per-connection fan-out — a detached handler strand to cancel — AND
// Chunk-C cancellation). RED-first: the fixture is absent on HEAD.
#[test]
fn web_handler_cancelled_on_client_disconnect() {
    let port = free_port();
    let server = spawn_server(FANOUT_FIXTURE, port);

    // Open a slow request and ABANDON it mid-flight (drop the connection without
    // reading the response) — the client disconnect should cancel the handler.
    {
        let mut s = TcpStream::connect(format!("127.0.0.1:{port}")).expect("connect");
        let req = format!("GET {SLOW_ROUTE} HTTP/1.0\r\n\r\n");
        s.write_all(req.as_bytes()).expect("write slow request");
        s.flush().ok();
        // Drop `s` here without reading the response — simulate a disconnect.
    }
    // Give the server a moment to observe the disconnect + cancel the handler.
    std::thread::sleep(Duration::from_millis(200));

    // The server must keep serving (the cancelled handler freed its resources; the
    // disconnect did not wedge the accept loop).
    let ok_resp = http_request(port, "GET", OK_ROUTE);
    assert!(
        !ok_resp.is_empty(),
        "after a client disconnect mid-request the server must keep serving (the \
         handler is cancelled, its permit + reactor interest released, §10.12.10); \
         subsequent GET got an empty response"
    );
    drop(server);
}

// =============================================================================
// §C5c — graceful shutdown (a §10.12.10 reference pattern).
// =============================================================================

// spec: spec/10-io.md §10.12.10 — on a shutdown signal (SIGTERM) the server cancels
// its outstanding detached handler strands (their in-flight polls dropped, resources
// released, §10.12.9), drains, and EXITS CLEANLY (no hang, no leaked strand) within
// a bounded time. Dependency: C3 + C-fanout (needs >= 1 outstanding CONCURRENT
// handler strand to cancel — only exists under the fan-out — AND Chunk-C
// cancellation). RED-first: the fixture is absent on HEAD.
#[test]
fn web_server_graceful_shutdown_cancels_outstanding_handler_strands() {
    let port = free_port();
    let mut server = spawn_server(FANOUT_FIXTURE, port);

    // Start a slow request so there is an outstanding handler strand in flight, then
    // signal graceful shutdown.
    let slow = std::thread::spawn(move || {
        let mut s = TcpStream::connect(format!("127.0.0.1:{port}")).ok()?;
        s.set_read_timeout(Some(Duration::from_secs(5))).ok();
        let _ = s.write_all(format!("GET {SLOW_ROUTE} HTTP/1.0\r\n\r\n").as_bytes());
        let mut buf = String::new();
        let _ = s.read_to_string(&mut buf);
        Some(buf)
    });
    std::thread::sleep(Duration::from_millis(100));
    assert!(
        server.signal_term(),
        "could not deliver SIGTERM to the server child (graceful-shutdown probe)"
    );

    // The server must exit cleanly within a bound (cancelling outstanding strands,
    // not hanging on them).
    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        match server.child.try_wait() {
            Ok(Some(_status)) => break, // exited
            Ok(None) => {
                assert!(
                    Instant::now() < deadline,
                    "graceful shutdown must CANCEL outstanding handler strands and \
                     EXIT cleanly within 10s (§10.12.10); the server is still running \
                     — looks like it hung on an outstanding strand (no cancellation)"
                );
                std::thread::sleep(Duration::from_millis(100));
            }
            Err(e) => panic!("try_wait failed: {e}"),
        }
    }
    let _ = slow.join();
}

// =============================================================================
// Launch-eligibility negative matrix (E1/E2/E3) — the observable e2e face.
//
// /arch's 0470 ruling (`effect-concurrency.md` §4.1): a discarded, locally-token-
// disjoint bind sub-tree is launch-eligible IFF (E1) result-discarded, (E2)
// value-locality (every effect acts on a value bound WITHIN the sub-tree; shares no
// free var with the continuation), and (E3) it touches NO `Commutative` (token-0)
// nor `Sequential` (token-1) shared-singleton effect — those are REFUSED (the
// provenance argument cannot prove them disjoint; detaching them REORDERS same-token
// effects, §8.2). MOST of the matrix is /int UNIT rows (co-landing with the C-fanout
// /dev wave — they assert the analysis class on hand-built bind chains); the ONE
// black-box-observable negative is **E3 token-0 ordering preserved**: a token-0
// sub-tree must NOT be launched, so same-token-0 effects stay SOURCE-ORDERED.
// =============================================================================

// spec: spec/10-io.md §10.12.7 — E3 (token-0 refusal): a chain of discarded
// (E1-eligible) `poll-log` steps on the SHARED token 0 (`Commutative` / shared
// stdout) must NOT be launched — token-0 is a shared singleton E2's provenance
// argument cannot prove disjoint, and detaching it would REORDER the same-token
// effects (§8.2). So the tags stay in SOURCE ORDER (a<b<c). Posture: verify /
// stays-green — on HEAD the serve loop is serial (0470 wall) so the order holds
// trivially; once C-fanout lands, this guards that the E3 token-0 REFUSAL keeps the
// order (it must NOT become reorderable). Failing-not-ignored-faithful (the B1c
// precedent): a genuinely-passing pin, NOT `#[ignore]`'d.
#[test]
fn e3_token0_discarded_subtree_not_launched_stays_source_ordered() {
    // Three discarded `poll-log` steps on token 0 (E1: results unused ⇒
    // launch-shaped; E3: token 0 ⇒ MUST be REFUSED ⇒ stays serial + ordered).
    let prog = "(platform poll-pool)\n\
         (import [platform.poll-pool [poll-log]])\n\
         (import [primitives [bind Pure]])\n\
         (defn main []\n\
           (bind (poll-log 0 1 30 \"a\") (fn [_]\n\
             (bind (poll-log 0 1 30 \"b\") (fn [_]\n\
               (bind (poll-log 0 1 30 \"c\") (fn [_]\n\
                 (Pure 0))))))))\n";
    let out: CrOutput = Cranelisp::new()
        .use_workspace_platforms()
        .run("user.cl")
        .user(prog)
        .output();
    let stdout = out.stdout.clone();
    out.assert_exit(0);
    let (ia, ib, ic) = (stdout.find('a'), stdout.find('b'), stdout.find('c'));
    assert!(
        matches!((ia, ib, ic), (Some(a), Some(b), Some(c)) if a < b && b < c),
        "a token-0 (Commutative / shared-stdout) discarded sub-tree must NOT be \
         launched — same-token-0 effects stay SOURCE-ORDERED (a<b<c, E3 refusal, \
         spec/10-io.md §10.12.7 / effect-concurrency.md §4.1); got stdout={stdout:?}",
    );
}
