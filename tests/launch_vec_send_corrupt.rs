//! Sprint 98 Stage-1 (QA-first) — the SMALLER deterministic repro of exemplar-web
//! bug #2 (FIXME 0486). Sibling of `tests/launch_grid_corrupt.rs`; same failure
//! (a launched per-connection handler whose terminal `send-conn` is reactor-polled
//! AFTER the launched frame is torn down → heap-metadata overrun → SIGABRT), one
//! reduction step SMALLER: it drops the `Cell` / `Grid` ADT wrappers and renders
//! two live `(Vec Int)`s directly through the borrowed-Var `get`/`assoc` wrappers.
//!
//! ## Why a second, smaller guard (CLAUDE.md §Testing — "small repros aid the fix")
//!
//! FIXME 0486 asked whether a still-smaller `redA` shape — "launch + send-conn +
//! churned STRING body, no grids/vec" — reproduces (the pure `Response.body` heap
//! String being the freed-early buffer). The S98 Stage-1 /qa reduction MEASURED that
//! it does NOT (0/8 SIGABRT across two String-only variants), while a two-live-`(Vec
//! Int)` render through the borrowed-Var wrappers reproduces DETERMINISTICALLY (8/8),
//! and a SINGLE live vec does not (0/8). So the load-bearing floor is:
//!   (1) a `(Vec …)` reached through the borrowed-Var-param wrappers (`ring2-rc.md
//!       §5.5`), AND (2) TWO vecs BOTH live simultaneously — NOT the ADT wrapper, and
//!   NOT the pure String body. See the fixture header
//!   `tests/fixtures/web_launch_vec_send_corrupt/main.cl` for the full reduction table.
//! This refines FIXME 0486's fix target (the pure-String UAF hypothesis is refuted;
//! the borrowed-Var vec RC path on the launched strand is load-bearing) and is fed
//! back to /arch + /backend. Both this guard and its grid sibling flip GREEN when
//! /backend lands the keep-alive fix (BC §4b invariant 15).
//!
//! ## Determinism (2026-07-01, /qa, binary target/debug/cranelisp)
//!
//!   - ISOLATION, one small (81) request: 8/8 SIGABRT (status -6, `Stdio::null`).
//!   - The smaller shape churns LESS per request than the grid sibling, so a SINGLE
//!     81-size request's deferred-send window can CLOSE under full-suite parallel
//!     contention (1795-way) — measured false-GREEN. Two independent robustness
//!     widenings restore determinism under the canonical `cargo nextest run`:
//!       (a) heavy per-request churn — two live `(Vec Int)` of size 400 + a 400-wide
//!           interleaved string render (fixture `make-resp`), and
//!       (b) a bounded BURST of up to 8 sequential requests + a 3s poll-for-abort
//!           window (launched strands can be scheduled late under load).
//!     Result: RED across consecutive FULL-suite runs (6/6 total failures stable) —
//!     NOT a timing-sensitive guard (ledger discipline forbids "flaky").
//! Same infinite-server / raw-`Child` harness rationale as `launch_grid_corrupt.rs`:
//! spawn → poll-until-listening (bounded 10s) → bounded burst of read-to-EOF requests
//! → poll-for-abort (bounded 3s) → inspect the child exit → RAII-guard kill/reap.
//! Every wait is bounded so the suite can never stall.
//!
//! spec: spec/10-io.md §10.12.7 — Launch-and-Continue (Detached Effects). A launched
//! per-connection handler MUST NOT corrupt the heap (RC soundness: `ring2-rc.md §5.5`;
//! arg-lifetime-across-suspension: `bounded-contexts.md §4b` invariant 15). RED on HEAD
//! (the launched-strand two-live-vec render double-free aborts the server); flips GREEN
//! when the launched-path keep-alive / borrowed-Var RC miscount is fixed. Failing-not-
//! ignored per `memory/feedback_failing_not_ignored.md`.

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

/// Spawn `--run tests/fixtures/web_launch_vec_send_corrupt/main.cl` on `port` with
/// the workspace platform DLL + stdlib on the env, stdio nulled. Polls until the
/// server is listening (bounded), or panics loudly if it exits early / never binds.
fn spawn_server(port: u16) -> ServerGuard {
    let root = workspace_root();
    let binary = root.join("target").join("debug").join("cranelisp");
    assert!(
        binary.exists(),
        "cranelisp binary not found at {} — run `cargo build` first",
        binary.display()
    );
    let fixture = root
        .join("tests")
        .join("fixtures")
        .join("web_launch_vec_send_corrupt");
    let main_cl = fixture.join("main.cl");
    assert!(
        main_cl.exists(),
        "web_launch_vec_send_corrupt fixture not found at {}",
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
        .expect("spawn web_launch_vec_send_corrupt server");

    let mut guard = ServerGuard { child };

    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        if let Ok(Some(status)) = guard.child.try_wait() {
            panic!(
                "web_launch_vec_send_corrupt server exited before listening (status {:?}). \
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
            "web_launch_vec_send_corrupt server did not start listening on 127.0.0.1:{port} within 10s"
        );
        std::thread::sleep(Duration::from_millis(100));
    }

    guard
}

/// Send one HTTP/1.0 GET on a fresh connection and read the response to EOF
/// (bounded). The launched per-connection handler runs during this exchange; on
/// HEAD it aborts the server mid-handle (heap corruption).
fn drive_one_request(port: u16) {
    if let Ok(mut stream) = TcpStream::connect(format!("127.0.0.1:{port}")) {
        stream.set_read_timeout(Some(Duration::from_secs(3))).ok();
        let _ = stream.write_all(b"GET / HTTP/1.0\r\n\r\n");
        stream.flush().ok();
        let mut sink = String::new();
        let _ = stream.read_to_string(&mut sink);
    }
}

// spec: spec/10-io.md §10.12.7 — Launch-and-Continue (Detached Effects).
//
// The inferred launch of the per-connection handler MUST NOT corrupt the heap. The
// fixture's handler builds a `(Vec Int)` `g`, derives a second `s` via `assoc`
// (`vec-set` on a Var param), and renders BOTH via `get` (`vec-get` on a Var param)
// — the borrowed-Var RC path (`ring2-rc.md §5.5`), NO ADT wrapper. On HEAD a single
// request aborts the server with SIGABRT — deterministic 8/8 under `Stdio::null`.
// The correct behaviour is that the server survives the request (still serving, or a
// clean coded exit); this guard is RED until the launched-path keep-alive / RC
// miscount is fixed (FIXME 0486; BC §4b invariant 15).
#[test]
fn launched_strand_two_live_vecs_send_does_not_corrupt_heap_neg() {
    let port = free_port();
    let mut server = spawn_server(port);

    // Drive several sequential requests: each launched handler churns two live vecs
    // and defers a `send-conn`, so N requests = N overlapping corruption windows. A
    // single request reproduces 8/8 in isolation but the window can close under heavy
    // parallel suite load (measured); several requests widen it so the guard fires
    // deterministically under the canonical parallel `cargo nextest run` too — NOT a
    // timing-sensitive guard (ledger discipline forbids "flaky").
    for _ in 0..8 {
        if server.child.try_wait().ok().flatten().is_some() {
            break; // already aborted — no point sending more.
        }
        drive_one_request(port);
    }

    // Poll for the abort over a bounded window (not a single fixed sleep): under
    // heavy parallel suite load the launched strand may be scheduled late, so the
    // heap-corruption abort can arrive some hundreds of ms after the request. Poll up
    // to 3s for a signal-exit; break early the instant the child dies. Bounded, so the
    // suite can never stall.
    let abort_deadline = Instant::now() + Duration::from_secs(3);
    loop {
        if server.child.try_wait().ok().flatten().is_some() {
            break;
        }
        if Instant::now() >= abort_deadline {
            break;
        }
        std::thread::sleep(Duration::from_millis(100));
    }

    match server.child.try_wait() {
        Ok(Some(status)) => {
            let sig = status.signal();
            assert!(
                sig.is_none(),
                "launched per-connection handler corrupted the heap: the server was \
                 killed by signal {:?} (SIGABRT=6 ⇒ `free(): chunks in smallbin \
                 corrupted`) after ONE request. This is the SMALLER reduction of \
                 exemplar-web bug #2 — the borrowed-Var two-live-vec render on the \
                 launched strand (ring2-rc.md §5.5; FIXME 0486). Full status: {:?}",
                sig,
                status
            );
        }
        Ok(None) => {
            // Still alive after handling the request — the healthy outcome. PASS.
        }
        Err(e) => panic!("failed to poll web_launch_vec_send_corrupt server status: {e}"),
    }

    // Explicit: keep the guard alive to the end so Drop performs the kill/reap.
    drop(server);
}
