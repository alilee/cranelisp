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

// =============================================================================
// Wave 5.6 file 6 e2e.rs chunk-3 GAP-COVER carry-forwards (REGRESSION-GUARD).
// Sprint 58 Wave 5 — Cranelisp.toml E2E coverage (per
// tests/plan/wave-5.6-e2e-reaudit.md chunk 3 cluster MM).
//
// `/int` Wave 4 landed Step 5d (iii) — `Cranelisp.toml` project config
// lookup in `src/session.rs::load_project_config_lib_dirs` +
// `assemble_lib_dirs`. Unit tests in `src/session.rs` cover the helper
// directly; these E2E tests exercise the full binary path (config
// discovered + applied to module resolution) per spec/08 §8.11.4 item 2.
//
// All four tests use `--run main` (Run mode) rather than REPL because
// Run mode is the simpler fully-working integration path for module
// imports from lib_dirs. (REPL mode has a separate, pre-existing issue
// with relative `lib-dirs` paths.)
// =============================================================================

// spec: spec/08-modules.md §8.11.4 — `Cranelisp.toml.lib-dirs` is consulted
// to resolve module imports. Positive end-to-end: a relative lib-dirs
// entry resolves a sibling-directory module, exit code carries the
// returned Int via main.
// (carry: legacy/e2e.rs::e2e_cranelisp_toml_lib_dirs_resolves_modules)
#[test]
fn cranelisp_toml_lib_dirs_resolves_module() {
    Cranelisp::new()
        .file("Cranelisp.toml", r#"lib-dirs = ["./mylib"]"#)
        .file(
            "main.cl",
            "(import [foo [forty-two]])\n(defn main [] (forty-two))\n",
        )
        .file("mylib/foo.cl", "(defn forty-two [] 42)\n")
        .run("main")
        .output()
        .assert_exit(42);
}

// spec: spec/08-modules.md §8.11.4 — project-config tier (item 2) takes
// precedence over CRANELISP_LIB env-var tier (item 3). When both point
// at modules of the same name, the config wins.
//
// REGRESSION-GUARD: explicit `assert_ne!(exit, 13)` (env-var path
// shadow). Preserves the load-bearing precedence-regression check from
// the legacy test's negative companion.
// (carry: legacy/e2e.rs::e2e_cranelisp_toml_overrides_cranelisp_lib_env)
#[test]
fn cranelisp_toml_takes_precedence_over_cranelisp_lib_env() {
    // Build the env-tier lib in a sibling tempdir (separate from the
    // project root). `lose-lib` defines `(pick) -> 13`; the project-tier
    // `conflict-lib` defines `(pick) -> 99`. Config tier MUST win.
    let env_lib_td = tempfile::tempdir().expect("env_lib TempDir");
    std::fs::write(env_lib_td.path().join("foo.cl"), "(defn pick [] 13)\n")
        .expect("write env_lib/foo.cl");

    let out = Cranelisp::new()
        .file("Cranelisp.toml", r#"lib-dirs = ["./conflict-lib"]"#)
        .file(
            "main.cl",
            "(import [foo [pick]])\n(defn main [] (pick))\n",
        )
        .file("conflict-lib/foo.cl", "(defn pick [] 99)\n")
        .env(
            "CRANELISP_LIB",
            env_lib_td.path().to_str().expect("env_lib path utf8"),
        )
        .run("main")
        .output();

    let exit = out.status.code();
    assert_eq!(
        exit,
        Some(99),
        "Cranelisp.toml MUST take precedence over CRANELISP_LIB; expected exit 99 (config), got {exit:?}\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    // Negative companion: env-var module value (13) MUST NOT win.
    assert_ne!(
        exit,
        Some(13),
        "env-var module MUST NOT shadow project-config module"
    );
}

// spec: spec/08-modules.md §8.11.4 — when no Cranelisp.toml is present,
// the CRANELISP_LIB env var is consulted (tier 3). Absent-config
// fall-through to env tier.
// (carry: legacy/e2e.rs::e2e_cranelisp_toml_missing_falls_through_to_env)
#[test]
fn cranelisp_toml_missing_falls_through_to_env_var() {
    // Env-tier lib in a sibling tempdir; no Cranelisp.toml in project root.
    let env_lib_td = tempfile::tempdir().expect("env_lib TempDir");
    std::fs::write(env_lib_td.path().join("foo.cl"), "(defn val [] 77)\n")
        .expect("write env_lib/foo.cl");

    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(import [foo [val]])\n(defn main [] (val))\n",
        )
        .env(
            "CRANELISP_LIB",
            env_lib_td.path().to_str().expect("env_lib path utf8"),
        )
        .run("main")
        .output();

    assert_eq!(
        out.status.code(),
        Some(77),
        "absent Cranelisp.toml MUST fall through to CRANELISP_LIB; expected 77\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
}

// spec: spec/08-modules.md §8.11.4 — malformed Cranelisp.toml MUST NOT
// crash the binary. Per the implementation's documented behaviour
// (`assemble_lib_dirs` swallows parse errors and falls through to env/
// default tiers), a malformed config silently falls through. Verify
// no panic / no signal-style termination occurs and the binary exits
// cleanly when the program is independent of lib_dirs.
//
// REGRESSION-GUARD: defensive ("does not crash") rather than diagnostic
// ("errors helpfully"). If a future spec revision elevates this behaviour
// to a surfaced diagnostic, this test's assertion flips — file
// FIXME(/int) at that time.
// (carry: legacy/e2e.rs::e2e_cranelisp_toml_malformed_errors_helpfully)
#[test]
fn cranelisp_toml_malformed_does_not_crash() {
    let out = Cranelisp::new()
        // Unclosed string literal — TOML parser MUST reject as malformed.
        .file("Cranelisp.toml", "lib-dirs = [\"oops\n")
        // Self-contained main: no imports needed (independent of lib_dirs).
        .file("main.cl", "(defn main [] 0)\n")
        .run("main")
        .output();

    let code = out.status.code();
    assert!(
        code.is_some(),
        "binary MUST exit cleanly (not killed by signal); status: {:?}\nstderr: {}",
        out.status, out.stderr
    );
    let code = code.unwrap();
    assert!(
        (0..=125).contains(&code),
        "malformed Cranelisp.toml MUST NOT cause abnormal termination; exit code {code}\nstderr: {}",
        out.stderr
    );
}
