//! Sprint 97 Wave-3 — the DETERMINISTIC repro of exemplar-web bug #2:
//! launched-strand heap corruption on the user-fn `get`/`assoc` grid path.
//!
//! ## What this is
//!
//! `tests/exemplar_web.rs::exemplar_web_server_serves_form_solution_and_not_found_over_http`
//! is the ~1/6-flaky over-HTTP WITNESS of a heap corruption that is DISTINCT
//! from the now-fixed single-threaded inline-temporary `emit_vec_drop_if_temporary`
//! defect (`regression.rs::nested_adt_wrapping_vec_looped_double_use_corrupts_heap_neg`).
//! This file is its DETERMINISTIC counterpart: a minimal free-standing "server
//! with no `spawn`" (`tests/fixtures/web_grid_corrupt/`) whose per-connection
//! handler is LAUNCHED (inferred launch-and-continue) and, inside that launched
//! strand, builds an ADT-wrapping-`(Vec Cell)` grid `g`, churns a second grid `s`
//! (both live), and renders BOTH via the thin USER-FN wrappers `get`/`assoc`
//! (`vec-get`/`vec-set` on a Var PARAMETER — the `ring2-rc.md §5.5` borrowed-Var
//! RC path), then `send-conn`s the rendered page. A single read-to-EOF request
//! triggers a `free(): chunks in smallbin corrupted` abort.
//!
//! ## Sampling (2026-07-01, /qa, binary target/debug/cranelisp @ 01:52)
//!
//!   - default (lenient):        8/8  SIGABRT (status -6)
//!   - `CRANELISP_NO_LENIENT=1`:  3/3  SIGABRT   ⇒ the reactor/launch-and-continue
//!                                     path, NOT rayon-spark (spark is disabled
//!                                     under NO_LENIENT yet the corruption persists).
//!   - `CRANELISP_RC_TRACE=1`:    4/4  SIGABRT (stderr→file). The RC trace shows a
//!                                     DOUBLE-FREE: 2082 alloc / 1478 free with 205
//!                                     distinct pointers freed 2+ times (grid Vec
//!                                     pointers) — an RC undercount → free-while-
//!                                     reachable → second free.
//!   - `Stdio::null` (this test): 8/8  SIGABRT.
//!
//! The ONLY non-crash observed was `subprocess.PIPE` + `RC_TRACE=1` together: the
//! massive RC-trace volume fills the stderr pipe and blocks the child mid-run
//! (an I/O deadlock, not a real "clean" outcome). This test pipes nothing
//! (`Stdio::null`) and RC_TRACE is off, so it is deterministic.
//!
//! ## What the bare-launch strip revealed (negative result — the reduction floor)
//!
//! Stripping the WEB layer entirely — replacing `accept`/`read-conn`/`send-conn`
//! with `poll-pool` timer leaves (`poll-read`/`poll-log`) while doing the IDENTICAL
//! grid build/churn/render inside the launched strand — does NOT corrupt: 8/8 clean
//! (and timing confirmed the launch DID fire — 8 strands × 60 ms → 314 ms, timers
//! overlap). So a generic launched strand over the borrowed-Var vec RC path is NOT
//! sufficient; the web-reactor terminal (`send-conn` — a Consume poll leaf that
//! ALSO marshals a `Response` ADT to the platform DLL, over a per-`accept` fresh
//! opaque `Connection` handle) is load-bearing for the manifestation. The reduction
//! therefore floors at the `web` fixture; the bare-launch strip is kept only as a
//! diagnostic note (it is a passing negative, not a guard, so it is not committed
//! as a test).
//!
//! ## Ownership (tentative — cross-skill, LAYERED)
//!
//! Lean `/backend` RC codegen of the borrowed-Var `vec-get`/`vec-set` path
//! (`ring2-rc.md §5.5` `borrowed_vars` / `emit_capture_return_inc`) — the same
//! residual the S97 Wave-3 /backend note names, and the double-free is on grid Vec
//! pointers. BUT the bare-launch clean result shows the miscount is only EXPOSED
//! when the launched strand terminates through a DLL-ADT-marshaling Consume leaf
//! (`send-conn`), so `/int` trampoline launch-capture / Consume-release lifecycle
//! cannot be excluded — this is a cross-skill handoff and the fixing skill should
//! confirm with a crate-level unit repro before patching. Regression class:
//! LATENT, cutover-surfaced — the borrowed-Var undercount pre-existed; the S97 v9
//! serve-loop reshape is what actually LAUNCHES the handler (previously serial),
//! exposing it.
//!
//! ## Why a raw `std::process::Child` (not the `Cranelisp` builder)
//!
//! Same reason as `tests/exemplar_web.rs`: the fixture is an INFINITE server; the
//! builder runs a child to completion. This test spawns → polls-until-listening →
//! one read-to-EOF request → inspects exit → kills. Every wait is bounded so the
//! test can NEVER stall the suite: readiness deadline 10s (+ early-exit detect),
//! read timeout 3s, post-request settle 0.5s, then the RAII guard kills the child.
//!
//! spec: spec/10-io.md §10.12.7 — Launch-and-Continue (Detached Effects). A
//! launched per-connection handler MUST NOT corrupt the heap (RC soundness:
//! `design/backend/ring2-rc.md §5.5`). RED on HEAD (the launched-strand grid Vec
//! double-free aborts the server); flips GREEN when the borrowed-Var RC miscount
//! on the launched path is fixed. Failing-not-ignored per
//! `memory/feedback_failing_not_ignored.md`.

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::os::unix::process::ExitStatusExt;
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Reserve an ephemeral free TCP port (bind :0, read it, drop the listener).
fn free_port() -> u16 {
    let l = TcpListener::bind("127.0.0.1:0").expect("bind ephemeral port");
    l.local_addr().expect("local_addr").port()
}

/// RAII guard: kill + reap the server child on drop so a panicking assertion
/// (or the normal end of test) never leaks the process nor holds the port.
struct ServerGuard {
    child: Child,
}

impl Drop for ServerGuard {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// Spawn `--run tests/fixtures/web_grid_corrupt/main.cl` on `port` with the
/// workspace platform DLL + stdlib on the env, stdio nulled. Polls until the
/// server is listening (bounded), or panics loudly if it exits early / never
/// binds. `CRANELISP_PORT` overrides the fixture's hard-coded `(listen 8080 …)`
/// (honoured platform-side in `bind-listener`).
fn spawn_server(port: u16) -> ServerGuard {
    let root = workspace_root();
    let binary = root.join("target").join("debug").join("cranelisp");
    assert!(
        binary.exists(),
        "cranelisp binary not found at {} — run `cargo build` first",
        binary.display()
    );
    let fixture = root.join("tests").join("fixtures").join("web_grid_corrupt");
    let main_cl = fixture.join("main.cl");
    assert!(
        main_cl.exists(),
        "web_grid_corrupt fixture not found at {}",
        main_cl.display()
    );

    let child = Command::new(&binary)
        .current_dir(&fixture)
        .arg("--run")
        .arg("main.cl")
        .env("CRANELISP_PORT", port.to_string())
        .env("CRANELISP_PLATFORM_PATH", root.join("target").join("debug"))
        .env("CRANELISP_LIB", root.join("stdlib"))
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn web_grid_corrupt server");

    let mut guard = ServerGuard { child };

    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        if let Ok(Some(status)) = guard.child.try_wait() {
            panic!(
                "web_grid_corrupt server exited before listening (status {:?}). \
                 Is port {port} already in use? Check CRANELISP_PLATFORM_PATH/CRANELISP_LIB.",
                status
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
            "web_grid_corrupt server did not start listening on 127.0.0.1:{port} within 10s"
        );
        std::thread::sleep(Duration::from_millis(100));
    }

    guard
}

/// Send one HTTP/1.0 GET on a fresh connection and read the response to EOF
/// (bounded). The launched per-connection handler runs during this exchange; on
/// HEAD it aborts the server mid-handle (heap corruption), so the read may return
/// a partial body or a reset — both are fine, we only care about the child's exit.
fn drive_one_request(port: u16) {
    if let Ok(mut stream) = TcpStream::connect(format!("127.0.0.1:{port}")) {
        stream.set_read_timeout(Some(Duration::from_secs(3))).ok();
        let _ = stream.write_all(b"GET / HTTP/1.0\r\n\r\n");
        stream.flush().ok();
        let mut sink = String::new();
        // Ignore the result: a corruption-abort mid-response surfaces as an early
        // EOF / reset, which is not itself the assertion — the child exit is.
        let _ = stream.read_to_string(&mut sink);
    }
}

// spec: spec/10-io.md §10.12.7 — Launch-and-Continue (Detached Effects).
//
// The inferred launch of the per-connection handler MUST NOT corrupt the heap.
// The fixture's handler builds an ADT-wrapping-`(Vec Cell)` grid, derives a
// second grid via `assoc` (`vec-set` on a Var param), and renders BOTH via `get`
// (`vec-get` on a Var param) — the borrowed-Var RC path (`ring2-rc.md §5.5`).
// On HEAD a single request aborts the server with SIGABRT (`free(): chunks in
// smallbin corrupted`) — deterministic 8/8 under `Stdio::null`. The correct
// behaviour is that the server survives the request (still serving, or a clean
// coded exit); this guard is RED until the launched-path RC miscount is fixed.
#[test]
fn launched_strand_grid_get_assoc_does_not_corrupt_heap_neg() {
    let port = free_port();
    let mut server = spawn_server(port);

    drive_one_request(port);

    // Give the launched handler a bounded moment to finish (and to abort if it is
    // going to) before we inspect the child's disposition.
    std::thread::sleep(Duration::from_millis(500));

    match server.child.try_wait() {
        Ok(Some(status)) => {
            // The server terminated on its own after one request. If it was killed
            // by a SIGNAL (SIGABRT from the glibc heap-corruption abort), that IS
            // the bug. A clean coded exit would be acceptable (the fixture is an
            // infinite server, so it should not exit at all — but a coded exit is
            // still not heap corruption).
            let sig = status.signal();
            assert!(
                sig.is_none(),
                "launched per-connection handler corrupted the heap: the server was \
                 killed by signal {:?} (SIGABRT=6 ⇒ `free(): chunks in smallbin \
                 corrupted`) after ONE request. This is exemplar-web bug #2 — the \
                 borrowed-Var `get`/`assoc` grid Vec double-free on the launched \
                 strand (ring2-rc.md §5.5). Full status: {:?}",
                sig,
                status
            );
        }
        Ok(None) => {
            // Still alive after handling the request — the healthy outcome (the
            // infinite serve loop is ready for the next connection). PASS.
            // The ServerGuard Drop kills + reaps it.
        }
        Err(e) => panic!("failed to poll web_grid_corrupt server status: {e}"),
    }

    // Explicit: keep the guard alive to the end so Drop performs the kill/reap.
    drop(server);
}
