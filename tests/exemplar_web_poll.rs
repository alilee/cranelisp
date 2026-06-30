//! Sprint 96 — effect-concurrency Chunk B (Wave B4): the §3A web single-serial-
//! roundtrip e2e against the v8 POLL-shape web platform (FIXME 0465 / Gap G4).
//!
//! Plan: `tests/plan/sprint-96.md` §3A (`web_poll_accept_read_serves_one_roundtrip_serial`,
//! DEFERRED → A4 co-landing). Contract of record:
//! `design/platform/poll-support.md §3.5` (the web connection-handle interface —
//! bind-listener blocking + accept-conn/read-conn/send-conn poll leaves over
//! per-connection tokens) / §3.5.5 (the SERIAL serve loop, the Chunk-A baseline).
//! Spec of record: `spec/10-io.md` §10.12.4.1 (the poll carrier is mechanism-
//! neutral to the spec) — the observable here is the serve roundtrip, not the
//! capacity pool (that is `concurrency_poll_capacity.rs`).
//!
//! ## Why a port-parametrized fixture (Gap G4)
//!
//! The Sudoku exemplar (`exemplar/main.cl`, exercised by `tests/exemplar_web.rs`)
//! hard-codes `(defn port [] 8080)`. A new web-server test on 8080 would collide
//! with `exemplar_web.rs` in the shared default lane (`cargo nextest run` runs the
//! whole suite). So this row uses a MINIMAL free-standing poll-shape fixture
//! (`tests/fixtures/web_poll/`: the ADTs-only `web.cl` + the `serve.cl` wrappers +
//! a fixed-response `main.cl`) copied into a per-test tmpdir with the
//! `(defn port [] …)` line rewritten to a PROBED FREE PORT — so the row never
//! collides, in any lane.
//!
//! ## Raw-process pattern (mirrors `exemplar_web.rs`)
//!
//! The web server is an infinite loop, so the `Cranelisp` builder (which runs the
//! child to completion) cannot drive it. This test manages a raw
//! `std::process::Child` directly: copy fixture → rewrite port → spawn → poll
//! until listening → one HTTP roundtrip → kill via an RAII `ServerGuard`.

use std::fs;
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Probe a free TCP port by binding `127.0.0.1:0`, reading the assigned port, and
/// dropping the listener. A small TOCTOU window remains (the port could be taken
/// before the server binds), but it is far better than a fixed port colliding
/// with `exemplar_web.rs`'s 8080 in the shared lane.
fn free_port() -> u16 {
    let l = TcpListener::bind("127.0.0.1:0").expect("bind ephemeral port");
    l.local_addr().expect("local addr").port()
}

/// RAII guard that kills + reaps the server child on drop (a panicking assertion
/// must not leak the process holding the port).
struct ServerGuard {
    child: Child,
    port: u16,
    // Keep the tmpdir alive for the server's lifetime (the .cl files live in it).
    _tmp: tempfile::TempDir,
}

impl Drop for ServerGuard {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// Copy the `web_poll` fixture into a fresh tmpdir, rewrite its `(defn port [] …)`
/// to a probed free port, spawn `--run main.cl`, and poll until it is listening.
fn spawn_poll_web_server() -> ServerGuard {
    let root = workspace_root();
    let binary = root.join("target").join("debug").join("cranelisp");
    assert!(
        binary.exists(),
        "cranelisp binary not found at {} — run `cargo build` first",
        binary.display()
    );
    let fixture = root.join("tests").join("fixtures").join("web_poll");

    let tmp = tempfile::tempdir().expect("tempdir");
    // Copy the three fixture files (ADTs `web.cl`, wrappers `serve.cl`, entry
    // `main.cl`) into the per-test project root.
    for name in ["web.cl", "serve.cl", "main.cl"] {
        let src = fixture.join(name);
        let dst = tmp.path().join(name);
        fs::copy(&src, &dst)
            .unwrap_or_else(|e| panic!("copy {} -> {}: {e}", src.display(), dst.display()));
    }

    // Rewrite the port to a probed free port (Gap G4 — no 8080 collision).
    let port = free_port();
    let main_path = tmp.path().join("main.cl");
    let main_src = fs::read_to_string(&main_path).expect("read fixture main.cl");
    let rewritten = main_src.replace("(defn port [] 18080)", &format!("(defn port [] {port})"));
    assert_ne!(
        rewritten, main_src,
        "fixture main.cl must contain the `(defn port [] 18080)` line to rewrite"
    );
    fs::write(&main_path, rewritten).expect("write rewritten main.cl");

    let child = Command::new(&binary)
        .current_dir(tmp.path())
        .arg("--run")
        .arg("main.cl")
        .env("CRANELISP_PLATFORM_PATH", root.join("target").join("debug"))
        // The fixture is free-standing (no stdlib / no prelude); `web` + `serve`
        // resolve from the tmpdir project root.
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn poll web server");

    let mut guard = ServerGuard { child, port, _tmp: tmp };

    let deadline = Instant::now() + Duration::from_secs(20);
    loop {
        if let Ok(Some(status)) = guard.child.try_wait() {
            panic!(
                "poll web server exited before listening (status {status:?}). \
                 Is CRANELISP_PLATFORM_PATH right / the cranelisp-web DLL built?"
            );
        }
        if TcpStream::connect_timeout(
            &format!("127.0.0.1:{}", guard.port).parse().unwrap(),
            Duration::from_millis(200),
        )
        .is_ok()
        {
            break;
        }
        assert!(
            Instant::now() < deadline,
            "poll web server did not start listening on 127.0.0.1:{} within 20s",
            guard.port
        );
        std::thread::sleep(Duration::from_millis(100));
    }

    guard
}

/// One HTTP/1.0 GET on a fresh connection; returns the full response.
fn http_get(port: u16, path: &str) -> String {
    let mut stream =
        TcpStream::connect(format!("127.0.0.1:{port}")).expect("connect to poll web server");
    stream.set_read_timeout(Some(Duration::from_secs(20))).unwrap();
    let request = format!("GET {path} HTTP/1.0\r\n\r\n");
    stream.write_all(request.as_bytes()).expect("write request");
    stream.flush().ok();
    let mut response = String::new();
    stream.read_to_string(&mut response).expect("read response");
    response
}

// =============================================================================
// §3A — the v8 poll-shape web platform serves ONE serial roundtrip.
// =============================================================================

// spec: spec/10-io.md §10.12.4.1 — the poll carrier serves a request; the serial
// serve loop (accept -> read -> handle -> send -> recur) drives the poll
// accept-conn / read-conn / send-conn leaves end-to-end.
// design: design/platform/poll-support.md §3.5 — the web connection-handle
// interface (bind-listener blocking + the three poll leaves over per-connection
// tokens) + §3.5.5 (the SERIAL baseline serve loop). The accept-conn parks on
// listener-readable + mints a fresh Connection; read-conn parks on conn-readable
// + parses the request; send-conn writes the response + closes. A GET round-trips
// to the fixed marker body — proof the poll arc drove the request under the
// serial loop (no fan-out; that is Chunk B).
#[test]
fn web_poll_accept_read_serves_one_roundtrip_serial() {
    let server = spawn_poll_web_server();

    let resp = http_get(server.port, "/");
    assert!(
        resp.starts_with("HTTP/1.0 200 OK\r\n"),
        "poll web server must answer 200 OK; got:\n{resp}"
    );
    assert!(
        resp.contains("hello-from-poll-web"),
        "poll web server must serve the fixed marker body (proving accept-conn -> \
         read-conn -> send-conn drove the roundtrip); got:\n{resp}"
    );
    // server's Drop kills + reaps the child here.
}
