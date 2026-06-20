//! Sprint 86 Wave E — durable web-serve e2e for the exemplar HTTP front-end.
//!
//! Proves the `web` platform front-end ACTUALLY SERVES over HTTP: a real
//! `--run exemplar/main.cl` server process is spawned, an HTTP client connects
//! to its listening port, and the GET-form / POST-solve / 404 round-trips are
//! asserted against the rendered HTML. `/arch §3a` specified a
//! "one-request-then-exit" guard; until that lands, this test drives the
//! infinite serve loop (Model A) directly and KILLS the process when done.
//!
//! Why NOT the `Cranelisp` builder (`tests/helpers/e2e.rs`): that harness runs
//! the child to completion (it polls `try_wait` and kills only on a 30s
//! TIMEOUT, then captures the full output). `exemplar/main.cl` is an INFINITE
//! server — it never exits on its own — so the builder would always hit the
//! timeout and never let the test talk to the live socket mid-run. A
//! long-running, talk-to-it-while-alive server is exactly the case the builder
//! does not model, so this single server test manages a raw `std::process::Child`
//! directly (spawn → poll-until-listening → HTTP round-trips → kill). This is
//! the documented exception for the persistent-server shape.
//!
//! Exemplar dependency: this test references `exemplar/main.cl` and the
//! workspace `stdlib/` + `target/debug/` (the `web` platform DLL). Per
//! `tests/CLAUDE.md §"Repros live in tests/"`, exemplar-driven tests MAY depend
//! on `exemplar/` (cf. `tests/exemplar.rs`); the exemplar is one of the two
//! trees permitted to use stdlib (root CLAUDE.md §Stdlib separation).
//!
//! Port: `exemplar/main.cl` hard-codes `(defn port [] 8080)`, so this test
//! binds the fixed port 8080. If another process holds 8080 the spawn will fail
//! to bind and the readiness poll times out (the test fails loudly rather than
//! hanging). This is the documented limitation until the exemplar takes an
//! ephemeral/env-configured port.
//!
//! FIXME(/qa — DEF-4): once DEF-4 (`tests/link.rs::
//! link_multi_module_platform_emits_single_layout_hash_gate_symbol`) lands,
//! extend this guard with a `--link`-then-run variant — the standalone linked
//! server should serve identically. `--run` is the only viable server entry
//! today because `--link` of the multi-module `(platform web)` program fails
//! with the duplicate per-platform hash symbol.
//!
//! spec: design/arch/platform-interface.md §3a — Model A (Cranelisp-owned serve
//! loop; one accept→handle→send→recur cycle per request, synchronous platform
//! effects).

use std::io::{Read, Write};
use std::net::TcpStream;
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

/// The fixed port `exemplar/main.cl` listens on (`(defn port [] 8080)`).
const PORT: u16 = 8080;

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// RAII guard that kills + reaps the server child on drop, so a panicking
/// assertion never leaks the process (which would hold the port for the next
/// run). Holds a captured-stderr handle for diagnostics.
struct ServerGuard {
    child: Child,
}

impl Drop for ServerGuard {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// Spawn `--run exemplar/main.cl` with the workspace platform + stdlib env, then
/// poll the listening port until it accepts a connection (server is ready).
fn spawn_server() -> ServerGuard {
    let root = workspace_root();
    let binary = root.join("target").join("debug").join("cranelisp");
    assert!(
        binary.exists(),
        "cranelisp binary not found at {} — run `cargo build` first",
        binary.display()
    );
    let main_cl = root.join("exemplar").join("main.cl");
    assert!(
        main_cl.exists(),
        "exemplar/main.cl not found at {}",
        main_cl.display()
    );

    let child = Command::new(&binary)
        .current_dir(&root)
        .arg("--run")
        .arg("exemplar/main.cl")
        .env("CRANELISP_PLATFORM_PATH", root.join("target").join("debug"))
        .env("CRANELISP_LIB", root.join("stdlib"))
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn exemplar web server");

    let mut guard = ServerGuard { child };

    // Poll the port until the server is listening (or the child died, or we
    // exceed the readiness deadline).
    let deadline = Instant::now() + Duration::from_secs(20);
    loop {
        // If the child exited early, the server never came up — surface its
        // output rather than spin to the deadline.
        if let Ok(Some(status)) = guard.child.try_wait() {
            panic!(
                "exemplar web server exited before listening (status {:?}). \
                 Is port {PORT} already in use? Check CRANELISP_PLATFORM_PATH/CRANELISP_LIB.",
                status
            );
        }
        if TcpStream::connect_timeout(
            &format!("127.0.0.1:{PORT}").parse().unwrap(),
            Duration::from_millis(200),
        )
        .is_ok()
        {
            break;
        }
        assert!(
            Instant::now() < deadline,
            "exemplar web server did not start listening on 127.0.0.1:{PORT} within 20s"
        );
        std::thread::sleep(Duration::from_millis(100));
    }

    guard
}

/// Send one HTTP/1.0 request on a fresh connection and return the full response
/// (status line + headers + body). The exemplar `web` DLL is a single-threaded
/// accept loop that reads one request per connection and honours Content-Length
/// for POST bodies (exemplar/platforms/web/src/lib.rs).
fn http_request(method: &str, path: &str, body: Option<&str>) -> String {
    let mut stream = TcpStream::connect(format!("127.0.0.1:{PORT}"))
        .expect("connect to exemplar web server");
    stream
        .set_read_timeout(Some(Duration::from_secs(20)))
        .unwrap();

    let request = match body {
        Some(b) => format!(
            "{method} {path} HTTP/1.0\r\n\
             Content-Type: application/x-www-form-urlencoded\r\n\
             Content-Length: {}\r\n\r\n{b}",
            b.len()
        ),
        None => format!("{method} {path} HTTP/1.0\r\n\r\n"),
    };
    stream.write_all(request.as_bytes()).expect("write request");
    stream.flush().ok();

    let mut response = String::new();
    stream.read_to_string(&mut response).expect("read response");
    response
}

/// Build the URL-encoded form body for a 9x9 puzzle string (81 chars; '.' or
/// '0' for empty). The HTML form names fields `cRC` (row, col) — empty cells
/// send an empty value. Matches `exemplar/form.cl::parse-form-body`.
fn encode_puzzle_form(puzzle: &str) -> String {
    assert_eq!(puzzle.len(), 81, "puzzle must be 81 chars");
    let chars: Vec<char> = puzzle.chars().collect();
    let mut pairs = Vec::with_capacity(81);
    for r in 0..9 {
        for c in 0..9 {
            let ch = chars[r * 9 + c];
            let v = if ch.is_ascii_digit() && ch != '0' {
                ch.to_string()
            } else {
                String::new()
            };
            pairs.push(format!("c{r}{c}={v}"));
        }
    }
    pairs.join("&")
}

// =============================================================================
// The web-serve e2e — proves the front-end actually serves over HTTP.
// =============================================================================

// spec: design/arch/platform-interface.md §3a — Model A serve loop.
//   The `web` exemplar front-end, run via `--run exemplar/main.cl`, serves a
//   real HTTP server. This guard spawns it, polls until listening, exercises
//   all three routes over live TCP connections, asserts the rendered HTML, and
//   kills the process. It proves the platform DLL crosses Request/Response ADTs
//   across the host<->DLL boundary AND the pure Cranelisp router produces the
//   correct pages end-to-end.
//
//   GET  /        -> form page    (<form ... action="/solve">, <title>Sudoku Solver</title>)
//   POST /solve   -> solution page (<title>Solution</title>, an 81-cell solved grid:
//                                   30 given + 51 solved <td> cells, a valid sudoku)
//   GET  /missing -> 404 page     (<title>Not Found</title>)
#[test]
fn exemplar_web_server_serves_form_solution_and_not_found_over_http() {
    let _server = spawn_server();

    // --- GET / -> the puzzle-entry form page ---
    let form_resp = http_request("GET", "/", None);
    assert!(
        form_resp.contains("<form") && form_resp.contains("action=\"/solve\""),
        "GET / must serve the puzzle-entry form (a <form action=\"/solve\">); got:\n{}",
        truncate(&form_resp, 600)
    );
    assert!(
        form_resp.contains("<title>Sudoku Solver</title>"),
        "GET / must serve the Sudoku Solver form page title; got:\n{}",
        truncate(&form_resp, 600)
    );

    // --- POST /solve -> the solved-grid solution page ---
    // A known-solvable classic puzzle (the canonical "easy" board). Encode it
    // as the HTML form body and POST it; the server parses -> solves -> renders.
    let puzzle =
        "53..7....6..195....98....6.8...6...34..8.3..17...2...6.6....28....419..5....8..79";
    let body = encode_puzzle_form(puzzle);
    let solve_resp = http_request("POST", "/solve", Some(&body));

    assert!(
        solve_resp.contains("<title>Solution</title>"),
        "POST /solve must serve the Solution page (the puzzle is solvable); got:\n{}",
        truncate(&solve_resp, 800)
    );
    // The solution page renders all 81 cells as <td class="given">d</td> /
    // <td class="solved">d</td>. Extract them in row-major order and verify the
    // grid is a COMPLETE, VALID sudoku solution — the strongest proof the full
    // parse->solve->render pipeline ran across the HTTP boundary.
    let grid = extract_solution_grid(&solve_resp);
    assert_eq!(
        grid.len(),
        81,
        "solution page must render all 81 cells; got {}\nresp:\n{}",
        grid.len(),
        truncate(&solve_resp, 800)
    );
    assert!(
        is_valid_sudoku_solution(&grid),
        "POST /solve must return a VALID completed sudoku grid; got rows:\n{:?}",
        grid.chunks(9).collect::<Vec<_>>()
    );
    // The 30 givens from the input puzzle keep the `given` style; the remaining
    // 51 are `solved`. (Negative-ish guard: a degenerate all-`given` or
    // all-`solved` page would mean the original/solved distinction collapsed.)
    let given = solve_resp.matches("class=\"given\"").count();
    let solved = solve_resp.matches("class=\"solved\"").count();
    assert_eq!(
        given, 30,
        "solution page must mark the 30 input givens; got {given} given / {solved} solved"
    );
    assert_eq!(
        solved, 51,
        "solution page must mark the 51 solved cells; got {given} given / {solved} solved"
    );

    // --- GET /missing -> the 404 not-found page ---
    let nf_resp = http_request("GET", "/no-such-path", None);
    assert!(
        nf_resp.contains("<title>Not Found</title>"),
        "GET on an unknown path must serve the Not Found page; got:\n{}",
        truncate(&nf_resp, 600)
    );

    // _server's Drop kills + reaps the child here.
}

// =============================================================================
// Helpers — solution-grid extraction + sudoku validation.
// =============================================================================

/// Extract the 81 solution digits (row-major) from the rendered solution page.
fn extract_solution_grid(html: &str) -> Vec<u8> {
    let mut grid = Vec::with_capacity(81);
    // Cells look like `<td class="given">5</td>` or `<td class="solved">4</td>`.
    // Walk the string and pull the digit after each cell-class marker.
    let mut rest = html;
    while let Some(pos) = rest.find("<td class=\"") {
        rest = &rest[pos..];
        // Find the closing `>` of the opening tag, then the next char is the digit.
        if let Some(gt) = rest.find('>') {
            let after = &rest[gt + 1..];
            if let Some(ch) = after.chars().next() {
                if ch.is_ascii_digit() {
                    grid.push(ch as u8 - b'0');
                }
            }
            rest = after;
        } else {
            break;
        }
    }
    grid
}

/// True iff `grid` (81 cells, row-major) is a complete valid sudoku solution:
/// every row, column, and 3x3 box is a permutation of 1..=9.
fn is_valid_sudoku_solution(grid: &[u8]) -> bool {
    if grid.len() != 81 {
        return false;
    }
    let is_perm = |cells: &[u8]| {
        let mut seen = [false; 10];
        for &v in cells {
            if v < 1 || v > 9 || seen[v as usize] {
                return false;
            }
            seen[v as usize] = true;
        }
        true
    };
    // Rows.
    for r in 0..9 {
        if !is_perm(&grid[r * 9..r * 9 + 9]) {
            return false;
        }
    }
    // Columns.
    for c in 0..9 {
        let col: Vec<u8> = (0..9).map(|r| grid[r * 9 + c]).collect();
        if !is_perm(&col) {
            return false;
        }
    }
    // 3x3 boxes.
    for br in 0..3 {
        for bc in 0..3 {
            let mut bx = Vec::with_capacity(9);
            for dr in 0..3 {
                for dc in 0..3 {
                    bx.push(grid[(br * 3 + dr) * 9 + (bc * 3 + dc)]);
                }
            }
            if !is_perm(&bx) {
                return false;
            }
        }
    }
    true
}

fn truncate(s: &str, max: usize) -> String {
    if s.len() <= max {
        s.to_string()
    } else {
        format!("{}...<{} bytes truncated>", &s[..max], s.len() - max)
    }
}
