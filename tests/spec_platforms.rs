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
use std::path::PathBuf;

/// The platform DLL file extension for the host OS (mirrors
/// `src/platform.rs::PLATFORM_EXT`). The platform-dir resolver
/// (`resolve_platform_path`) looks for `libcranelisp_{name}.{ext}` using this
/// extension, so the union fixtures below copy the workspace `stdio` DLL under
/// the same host-correct name.
#[cfg(target_os = "linux")]
const PLATFORM_EXT: &str = "so";
#[cfg(target_os = "macos")]
const PLATFORM_EXT: &str = "dylib";
#[cfg(target_os = "windows")]
const PLATFORM_EXT: &str = "dll";

/// Cargo's artifact file name for the workspace `stdio` platform cdylib, e.g.
/// `libcranelisp_stdio.so`. This is exactly the name `resolve_platform_path`'s
/// `check_dir` matches (`libcranelisp_{name}.{ext}`), so a directory containing
/// a copy of this file resolves `(platform stdio)`.
fn stdio_dll_filename() -> String {
    format!("libcranelisp_stdio.{PLATFORM_EXT}")
}

/// Absolute path to the workspace `stdio` platform cdylib in `target/debug/`.
/// The nextest setup-script (`tests/scripts/build-link-prereqs.sh`, wired in
/// `.config/nextest.toml`) builds `cranelisp-stdio` into `target/debug` before
/// any test runs, so this artifact is present without the test shelling out to
/// `cargo build` (forbidden per `tests/CLAUDE.md`).
fn workspace_stdio_dll() -> PathBuf {
    // read-only on project_root: locating the prebuilt workspace cdylib.
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("debug")
        .join(stdio_dll_filename())
}

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
            "(import [primitives [Pure]])\n(import [foo [forty-two]])\n(defn main [] (Pure (forty-two)))\n",
        )
        .file("mylib/foo.cl", "(defn forty-two [] 42)\n")
        .run("main")
        .output()
        .assert_exit(42);
}

// spec: spec/08-modules.md §8.11.4 — the lib-dir model is an additive UNION and
// the search order places `CRANELISP_LIB` (env, source 2) BEFORE the
// `Cranelisp.toml lib-dirs` config tier (source 3). When BOTH provide a module of
// the same name, the env path is searched first and WINS (env > config — the S91
// settled additive model, REVERSING the old config > env precedence). BOTH tiers
// also contribute to the resolved set: a module present ONLY in the config tier
// still resolves (proving the union is additive, not env-replaces-config).
//
// SUPERSEDED-FLOOR RE-ALIGN (S91, Wave-6): this test formerly asserted the old
// config > env precedence (`cranelisp_toml_takes_precedence_over_cranelisp_lib_env`);
// it correctly went RED when `/dev`'s additive `assemble_lib_dirs` landed. This is
// the spec ruling superseding an existing floor, NOT a regression. Renamed to fit.
// (carry: legacy/e2e.rs::e2e_cranelisp_toml_overrides_cranelisp_lib_env, re-aligned)
#[test]
fn cranelisp_lib_env_searched_before_toml_lib_dirs() {
    // Env-tier lib in a sibling tempdir, with TWO modules:
    //   `foo.cl` (pick -> 13)  — SHADOWS the same-named config-tier module
    //   (no `bar` here)         — so `bar` can only come from the config tier
    let env_lib_td = tempfile::tempdir().expect("env_lib TempDir");
    std::fs::write(env_lib_td.path().join("foo.cl"), "(defn pick [] 13)\n")
        .expect("write env_lib/foo.cl");

    // (1) Same-module shadow: env tier wins (env > config under the S91 order).
    let shadow = Cranelisp::new()
        .file("Cranelisp.toml", r#"lib-dirs = ["./conflict-lib"]"#)
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(import [foo [pick]])\n(defn main [] (Pure (pick)))\n",
        )
        .file("conflict-lib/foo.cl", "(defn pick [] 99)\n")
        .env(
            "CRANELISP_LIB",
            env_lib_td.path().to_str().expect("env_lib path utf8"),
        )
        .run("main")
        .output();
    let exit = shadow.status.code();
    assert_eq!(
        exit,
        Some(13),
        "on a same-module shadow, CRANELISP_LIB (env) MUST be searched before the \
         Cranelisp.toml config tier and WIN (env > config, S91 §8.11.4); expected \
         exit 13 (env), got {exit:?}\nstdout: {}\nstderr: {}",
        shadow.stdout, shadow.stderr
    );
    // Negative companion: the config-tier module value (99) MUST NOT win the shadow.
    assert_ne!(
        exit,
        Some(99),
        "config-tier module MUST NOT shadow the env-tier module (the S91 order \
         reverses the old config > env precedence)"
    );

    // (2) Additive union: a module present ONLY in the config tier still resolves
    // (the env tier does not REPLACE the config tier — both contribute). `bar`
    // lives only under `conflict-lib` (config tier); it must resolve to 42.
    let additive = Cranelisp::new()
        .file("Cranelisp.toml", r#"lib-dirs = ["./conflict-lib"]"#)
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(import [bar [val]])\n(defn main [] (Pure (val)))\n",
        )
        .file("conflict-lib/bar.cl", "(defn val [] 42)\n")
        .env(
            "CRANELISP_LIB",
            env_lib_td.path().to_str().expect("env_lib path utf8"),
        )
        .run("main")
        .output();
    assert_eq!(
        additive.status.code(),
        Some(42),
        "a config-tier-only module MUST still resolve under the additive union — \
         the env tier does not suppress the config tier (S91 §8.11.4); expected \
         exit 42\nstdout: {}\nstderr: {}",
        additive.stdout, additive.stderr
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
            "(import [primitives [Pure]])\n(import [foo [val]])\n(defn main [] (Pure (val)))\n",
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

// =============================================================================
// §8.11.5 — Platform Directory Configuration: additive UNION of
// `CRANELISP_PLATFORM_PATH` (env, tier 3 ②) and `Cranelisp.toml` `platform-dirs`
// (tier 3 ③). Mirrors the §8.11.4 lib-dir union test
// (`cranelisp_lib_env_searched_before_toml_lib_dirs` +
// `lib_dir_union_neg_empty_toml_does_not_suppress`) for the platform tier.
//
// The §8.11.5 union semantics, mirroring §8.11.4:
//   - BOTH sources contribute; neither replaces nor suppresses the other.
//   - Search order on a same-name shadow is env (`CRANELISP_PLATFORM_PATH`)
//     BEFORE config (`Cranelisp.toml` `platform-dirs`).
//   - An absent `platform-dirs` key, `platform-dirs = []`, and an absent
//     `Cranelisp.toml` are equivalent: each contributes nothing and removes
//     nothing — the env tier is NOT suppressed.
//
// Witness: the workspace `stdio` cdylib is copied into per-test tier dirs; a
// `(platform stdio)` program that resolves the DLL prints via stdio (observable
// on stdout) and exits 0. A non-resolving / mis-resolving config tier is shown
// by a garbage same-name file that loads only if it is searched first.
//
// E2E SHADOW LIMIT: a true "env value WINS the shadow with DIFFERENT behaviour"
// witness (the lib-dir test's `pick -> 13 vs 99`) is NOT expressible at the e2e
// tier for platforms. A platform DLL's manifest export is namespaced by name
// (`cranelisp_platform_manifest_<name>`, src/platform.rs §5.5.5), so two
// physically-distinct DLLs cannot both answer to the SAME platform name without
// recompilation — there is no pair of differing-behaviour `stdio` DLLs to copy.
// The shadow is instead proven by ORDER OF SELECTION: a valid env-tier DLL beats
// a garbage config-tier file of the same resolvable name (env searched first =>
// loads cleanly; control with only the garbage config file => load fails),
// which is the §8.11.5 first-match-env-before-config guarantee.
// =============================================================================

// spec: spec/08-modules.md §8.11.5 — `CRANELISP_PLATFORM_PATH` (env) and
// `Cranelisp.toml` `platform-dirs` (config) form an additive UNION; the env tier
// is searched FIRST on a same-name shadow; an empty/absent `platform-dirs` key
// does not suppress the env tier.
#[test]
fn platform_path_env_searched_before_toml_platform_dirs() {
    let stdio_src = workspace_stdio_dll();
    assert!(
        stdio_src.is_file(),
        "workspace stdio cdylib not found at {stdio_src:?} — the nextest \
         setup-script (build-link-prereqs.sh) should have built it"
    );
    let dll_name = stdio_dll_filename();

    // The program prints via stdio (observable on stdout) and returns Pure 0.
    let prog = "(platform stdio)\n\
                (import [platform.stdio [print]])\n\
                (import [primitives [bind Pure]])\n\
                (defn main [] (bind (print \"plat-union\") (fn [_] (Pure 0))))\n";

    // (1) Config tier alone resolves — `platform-dirs` CONTRIBUTES to the union
    //     even with NO `CRANELISP_PLATFORM_PATH` set. (Proves the union is not
    //     env-only.)
    let cfg_only = Cranelisp::new()
        .file("Cranelisp.toml", r#"platform-dirs = ["./platdir"]"#)
        .file("main.cl", prog);
    let cfg_dir = cfg_only.tmpdir_path().join("platdir");
    std::fs::create_dir_all(&cfg_dir).expect("mkdir platdir");
    std::fs::copy(&stdio_src, cfg_dir.join(&dll_name)).expect("copy stdio -> platdir");
    cfg_only
        .run("main.cl")
        .output()
        .assert_exit(0)
        .assert_stdout_contains("plat-union");

    // (2) Env tier alone resolves with an ABSENT `platform-dirs` key — the env
    //     tier is NOT suppressed by a config file that omits `platform-dirs`.
    //     (Negative companion: absent key contributes nothing AND removes
    //     nothing.)
    let env_only = Cranelisp::new()
        .file("Cranelisp.toml", "# no platform-dirs key\n")
        .file("main.cl", prog);
    let env_dir = env_only.tmpdir_path().join("envdir");
    std::fs::create_dir_all(&env_dir).expect("mkdir envdir");
    std::fs::copy(&stdio_src, env_dir.join(&dll_name)).expect("copy stdio -> envdir");
    env_only
        .env("CRANELISP_PLATFORM_PATH", env_dir.to_str().expect("envdir utf8"))
        .run("main.cl")
        .output()
        .assert_exit(0)
        .assert_stdout_contains("plat-union");

    // (2b) Same, but with an EXPLICITLY EMPTY `platform-dirs = []` — equivalent
    //      to absent: the env tier still resolves.
    let env_empty = Cranelisp::new()
        .file("Cranelisp.toml", "platform-dirs = []\n")
        .file("main.cl", prog);
    let env_empty_dir = env_empty.tmpdir_path().join("envdir");
    std::fs::create_dir_all(&env_empty_dir).expect("mkdir envdir");
    std::fs::copy(&stdio_src, env_empty_dir.join(&dll_name)).expect("copy stdio -> envdir");
    env_empty
        .env(
            "CRANELISP_PLATFORM_PATH",
            env_empty_dir.to_str().expect("envdir utf8"),
        )
        .run("main.cl")
        .output()
        .assert_exit(0)
        .assert_stdout_contains("plat-union");

    // (3) Shadow: env tier is searched BEFORE config. A VALID env-tier DLL beats
    //     a GARBAGE config-tier file of the same resolvable name. Because env is
    //     searched first, the valid DLL is selected and the program runs cleanly.
    let shadow = Cranelisp::new()
        .file("Cranelisp.toml", r#"platform-dirs = ["./cfgdir"]"#)
        .file("main.cl", prog);
    let shadow_env = shadow.tmpdir_path().join("envdir");
    let shadow_cfg = shadow.tmpdir_path().join("cfgdir");
    std::fs::create_dir_all(&shadow_env).expect("mkdir envdir");
    std::fs::create_dir_all(&shadow_cfg).expect("mkdir cfgdir");
    std::fs::copy(&stdio_src, shadow_env.join(&dll_name)).expect("copy stdio -> envdir");
    // Garbage same-name file in the config tier: it IS a file (so it would be
    // selected if config were searched first) but is NOT a loadable DLL.
    std::fs::write(shadow_cfg.join(&dll_name), b"not a real dll\n").expect("write garbage cfg dll");
    shadow
        .env(
            "CRANELISP_PLATFORM_PATH",
            shadow_env.to_str().expect("envdir utf8"),
        )
        .run("main.cl")
        .output()
        .assert_exit(0)
        .assert_stdout_contains("plat-union");
}

// spec: spec/08-modules.md §8.11.5 — negative control proving the shadow above
// is genuinely env-FIRST and not merely "the valid DLL wins regardless of tier":
// with ONLY the garbage config-tier file on the search path (no
// `CRANELISP_PLATFORM_PATH`), the config-tier file IS selected (it is the only
// candidate) and the load FAILS — the binary surfaces a platform-load error and
// does not exit 0. If the resolver searched env-before-config but the shadow
// test passed only because some OTHER valid `stdio` was found, this control
// would still pass spuriously; it fails precisely because the config tier is
// reached and yields the garbage file.
#[test]
fn platform_dirs_neg_config_only_garbage_fails_to_load() {
    let dll_name = stdio_dll_filename();

    let proj = Cranelisp::new()
        .file("Cranelisp.toml", r#"platform-dirs = ["./cfgdir"]"#)
        .file(
            "main.cl",
            "(platform stdio)\n\
             (import [platform.stdio [print]])\n\
             (defn main [] (print \"unreached\"))\n",
        );
    let cfg_dir = proj.tmpdir_path().join("cfgdir");
    std::fs::create_dir_all(&cfg_dir).expect("mkdir cfgdir");
    std::fs::write(cfg_dir.join(&dll_name), b"not a real dll\n").expect("write garbage cfg dll");

    let out = proj.run("main.cl").output();
    // The garbage config-tier file is selected (config tier IS reached and
    // contributes) and the DLL load fails. Must NOT exit 0, and must NOT have
    // printed the program's output.
    assert_ne!(
        out.status.code(),
        Some(0),
        "a garbage config-tier platform DLL MUST fail to load, not exit 0; \
         stdout: {}\nstderr: {}",
        out.stdout,
        out.stderr
    );
    out.assert_stdout_does_not_contain("unreached");
}

// =============================================================================
// §8.9 + design/int/step8-platform-registry.md — stdio platform integration
// (carry-forward: legacy/v4_pipeline.rs §F — Wave 6 batch 6)
//
// Distinct from the test-capture mock above: these exercise the real
// `stdio` DLL through PlatformRegistry. The IO-trampoline path is
// observable as `print "..."` writing the text to STDOUT.
// =============================================================================

// spec: spec/08-modules.md §8.9 — `(platform stdio)` form loads the stdio
// platform DLL through PlatformRegistry; program compiles cleanly.
// (carry: legacy/v4_pipeline.rs::v4_platform_form,
//         legacy/v4_pipeline.rs::v4_platform_stdio_print collapsed)
// REGRESSION-GUARD: Sprint 56 baseline failure cluster — flipped green
// per `tests/plan/legacy/ring4.md` line 712 acceptance criteria.
#[test]
fn platform_form_with_stdio_compiles_in_run_mode() {
    let out = Cranelisp::new()
        .use_workspace_platforms()
        .user(
            "(platform stdio)\n\
             (import [platform.stdio [print]])\n\
             (defn main [] (print \"hello platform registry\"))",
        )
        .run("user.cl")
        .output();
    let err: String = out
        .stderr
        .lines()
        .filter(|line| !line.starts_with("nice-worker:"))
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        err.is_empty(),
        "platform_form: expected clean compilation but got stderr: {}",
        err
    );
}

// spec: repl/spec.md §0.2 + design/int/step8-platform-registry.md — main
// returns IO Action; the trampoline executes the effect, producing the
// printed text on STDOUT.
// (carry: legacy/v4_pipeline.rs::v4_platform_io_trampoline)
// REGRESSION-GUARD: IO trampoline runtime path.
#[test]
fn io_trampoline_executes_print_to_stdout() {
    Cranelisp::new()
        .use_workspace_platforms()
        .user(
            "(platform stdio)\n\
             (import [platform.stdio [print]])\n\
             (defn main [] (print \"trampoline works\"))",
        )
        .run("user.cl")
        .output()
        .assert_stdout_contains("trampoline works");
}

// spec: design/int/step8-platform-registry.md — programs WITHOUT
// `(platform ...)` MUST continue to compile and run after the
// PlatformRegistry refactor. Negative complement of the platform-form
// tests above.
// (carry: legacy/v4_pipeline.rs::v4_platform_empty_registry)
// REGRESSION-GUARD: empty-registry codegen invariant.
#[test]
fn no_platform_form_program_runs_with_empty_registry() {
    Cranelisp::new()
        .user("(defn main [] (primitives/Pure (primitives/add-i64 100 200)))")
        .run("user.cl")
        .output()
        // 300 mod 256 = 44 on Unix (exit codes are bytes).
        .assert_exit(300 % 256);
}

// =============================================================================
// IO effect sequencing over the stdio platform — spec/10-io.md §10.3 / §10.4
// (harvest: legacy/io.rs::io_bind_print_sequence / io_do_macro_sequenced_prints
//  / io_effect_propagation_through_functions / io_read_line_bind_print_echo
//  / io_do_print_sequence_with_pure_terminator_emits_all
//  / io_bind_bang_print_sequence_with_pure_terminator_emits_all)
//
// The legacy file used the in-memory test-capture platform to assert effect
// ORDER. The e2e equivalent uses the `stdio` platform under `--run`: each
// `print` emits to real stdout (one line each), so source-order sequencing is
// directly observable as ordered stdout. The exit code carries the final
// `(Pure N)` inner value, proving the trampoline returns after all effects.
// =============================================================================

// spec: spec/10-io.md §10.3 — `(bind (print a) (fn [_] (print b)))` sequences
// two effects in source order.
#[test]
fn bind_print_sequence_in_order() {
    Cranelisp::new()
        .use_workspace_platforms()
        .file(
            "main.cl",
            "(platform stdio)\n\
             (import [platform.stdio [print]])\n\
             (import [primitives [bind]])\n\
             (defn main [] (bind (print \"a\") (fn [_] (print \"b\"))))\n",
        )
        .run("main.cl")
        .output()
        .assert_stdout_eq("a\nb\n");
}

// spec: spec/10-io.md §10.7.1 — IO propagates through the call graph: a function
// that calls `print` inherits IO in its return type, and the effect fires when
// the resulting action is run.
#[test]
fn effect_propagates_through_function() {
    Cranelisp::new()
        .use_workspace_platforms()
        .file(
            "main.cl",
            "(platform stdio)\n\
             (import [platform.stdio [print]])\n\
             (defn greet [name] (print name))\n\
             (defn main [] (greet \"world\"))\n",
        )
        .run("main.cl")
        .output()
        .assert_stdout_contains("world");
}

// spec: spec/10-io.md §10.3 — read-line chained with bind to print (echo):
// the input line is read and printed back. test-capture supplies a scripted
// input line; the echoed line appears in the capture's flushed output.
#[test]
fn read_line_bind_print_echo() {
    Cranelisp::new()
        .use_workspace_platforms()
        .file(
            "main.cl",
            "(platform stdio)\n\
             (import [platform.stdio [print read-line]])\n\
             (import [primitives [bind]])\n\
             (defn main [] (bind (read-line) (fn [line] (print line))))\n",
        )
        .stdin("echo me\n")
        .run("main.cl")
        .output()
        .assert_stdout_contains("echo me");
}

// spec: spec/10-io.md §10.4.1 — a `do`/`bind!`-shaped print-sequence with a
// `(Pure N)` terminator, expressed via the primitive `bind` it desugars to
// (tests MUST NOT depend on stdlib — root CLAUDE.md "Design Principles"). The
// stdlib `do`/`bind!` macro desugaring is covered separately in
// `tests/spec_11_stdlib.rs`; here the bind-chain trampoline path is the target.
//
// REGRESSION-GUARD: the Sprint 57 Wave 6 ring4b/ring4j demo crash emitted the
// first print but terminated the process before the second. The full
// `print … print … Pure` chain here re-pins that all intermediate effects fire
// before the terminal value returns and the process exits cleanly with it.
#[test]
fn bind_chain_print_sequence_with_pure_terminator_emits_all() {
    Cranelisp::new()
        .use_workspace_platforms()
        .file(
            "main.cl",
            "(platform stdio)\n\
             (import [platform.stdio [print]])\n\
             (import [primitives [bind Pure]])\n\
             (defn main []\n\
               (bind (print \"one\") (fn [_]\n\
                 (bind (print \"two\") (fn [_] (Pure 42))))))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(42)
        .assert_stdout_eq("one\ntwo\n");
}
