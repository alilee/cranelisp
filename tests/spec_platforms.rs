// spec_platforms.rs — Platform DLL integration (Sprint 64 Wave 5.6 sketch_port carry-forward).
//
// Verifies that any platform DLL can integrate with a Cranelisp program via the
// `(platform <name>)` declaration form (spec/02-grammar.md §2.2.9). The tests
// invoke a test platform (`test-capture`) and compare its observable behaviour
// against the standard `stdio` platform. The differential observation is the
// integration witness: `print` via `stdio` writes to stdout; `print` via
// `test-capture` redirects into an in-memory buffer and writes nothing to stdout.
//
// What this file covers:
//   - §2.2.9 — `(platform <name>)` declaration loads the named DLL and
//     registers its exported functions under `platform.<name>/...`.
//   - §11.1 — platform `print` and `read-line` integrate via the same
//     entry-module declaration; behaviour is platform-specific.
//
// Mode: `--run` only. The platform declaration is processed during the module
// loading phase (per §2.2.9) and is "only valid in the entry module". A REPL
// session does not have a declared platform until `(platform ...)` is
// evaluated; the file mode (`--run main.cl`) is the canonical surface.
//
// Helper: `Cranelisp::use_workspace_platforms()` sets `CRANELISP_PLATFORM_PATH`
// to `target/debug/` so the child process can `dlopen` the workspace DLLs.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;

// =============================================================================
// §2.2.9 / §11.1 — `print` integrates via the declared platform DLL
// =============================================================================

// spec: spec/02-grammar.md §2.2.9 — `(platform test-capture)` declaration loads
// the test-capture DLL; the `print` function from that platform redirects
// stdout-bound output into an in-memory capture buffer rather than writing to
// stdout. The integration is observable via differential stdout: nothing from
// the captured `print` reaches stdout, while the program completes cleanly
// and exits with the value-returning `Pure`.
// (carry: legacy/sketch_port.rs::sketch_platform_capture_print_hello)
#[test]
fn platform_print_via_test_capture() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(platform test-capture)\n\
             (import [platform.test-capture [*]])\n\
             (import [primitives [bind Pure]])\n\
             (defn main [] (bind (print \"hello\") (fn [_] (Pure 42))))\n",
        )
        .use_workspace_platforms()
        .run("main.cl")
        .output()
        // Integration witness: program ran via the test-capture platform and
        // completed; the printed string did not reach stdout (it was captured).
        .assert_exit(42)
        .assert_stdout_does_not_contain("hello");
}

// spec: spec/02-grammar.md §2.2.9 — `read-line` from the test-capture
// platform returns empty from an empty scripted input queue. Differential
// observation against stdio (which would block on stdin): test-capture
// returns immediately with an empty string, so `(str-len (read-line))` = 0
// and the program exits with 0 without consuming stdin.
// (carry: legacy/sketch_port.rs::sketch_platform_capture_read_input)
#[test]
fn platform_read_line_via_test_capture() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(platform test-capture)\n\
             (import [platform.test-capture [*]])\n\
             (import [primitives [bind Pure str-len]])\n\
             (defn main [] (bind (read-line) (fn [s] (Pure (str-len s)))))\n",
        )
        .use_workspace_platforms()
        .run("main.cl")
        .output()
        // Empty input queue + read-line via test-capture → empty string → str-len 0.
        .assert_exit(0);
}
