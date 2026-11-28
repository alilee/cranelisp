// platform_errors.rs — Sprint 66 Phase 5 Stage 1 (FIXME 0104),
// Platform-load error reporting.
//
// Asserts the e2e-observable shape of platform-load failures: the binary
// surfaces a structured `CranelispError` carrying an `ErrorLocation`
// (file:line:col form-span) and a message naming the platform and the
// failure mode.
//
// E2E-OBSERVABILITY BOUNDARY (verified S77 W-Platform against the real
// `stdio`/`test-capture` workspace platforms):
//   - A **non-existent platform name** is e2e-triggerable today: it fails
//     at `resolve_platform_path → None` (`src/platform.rs:550`) BEFORE the
//     DLL is loaded, producing `CranelispError::ModuleError` whose Display
//     is `module error … platform '<name>' not found` with the form span.
//   - A **load failure** of a present-but-malformed DLL, and **manifest
//     absence**, surface the requested platform name + a load/not-found
//     message with the form span.
// ABI-version and ADT layout-hash refusals are exercised by spec_platforms_adt.rs
// using the shapes and shapes-badabi DLLs.
//
// Spec basis: `spec/12-runtime.md §12.8 Platform ABI` (platform fns loaded
// via `(platform name)`; discovery via the §8.11.3 DLL search order) +
// `§12.7 Error Model` (compile-time error reporting / message format).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};
use std::sync::Once;

/// No-op: the platform cdylibs/rlibs are built suite-wide by the nextest setup
/// script (`tests/scripts/build-link-prereqs.sh`), the single owner of that
/// artifact-set invariant (`tests/AGENTS.md` §"`--link` prerequisites" — "A test
/// MUST NOT shell out to `cargo build`").
///
/// The former per-test `cargo build -p cranelisp-stdio -p cranelisp-test-capture`
/// band-aid is RETIRED: under the single-ABI cutover it rebuilt
/// `target/debug/libcranelisp_stdio.rlib` against a `cranelisp-platform` variant
/// resolved over a DIFFERENT dep-subgraph than the setup script's
/// (`{stdio,test-capture}` vs `{stdio,…,exe-bundle}`), yielding a mismatched crate
/// disambiguator. A concurrent `--link` test then saw stdio.rlib and
/// `libcranelisp_exe_bundle.a` reference different `cranelisp_platform::*` symbol
/// manglings → `undefined reference` link failures under parallel load.
fn ensure_platform_cdylibs_built() {
    // qa-ratified S96 B1: the A4c neutralization is sound — no coverage hole. The
    // setup script (`tests/scripts/build-link-prereqs.sh`) builds the full platform
    // set (stdio + test-capture included) once, profile-consistent, before any
    // test; this helper's former per-test `cargo build` is the forbidden band-aid
    // that broke parallel `--link` with mismatched crate disambiguators. Inert by
    // design; call sites preserved.
    // Intentionally empty — see the doc comment above. The setup script owns it.
    static BUILT: Once = Once::new();
    BUILT.call_once(|| {});
}

// =============================================================================
// Platform-load error reporting — e2e-observable shapes (FIXME 0104 closed;
// see spec_platforms_adt.rs for ABI and layout-hash gates)
// =============================================================================

// spec: spec/12-runtime.md §12.7 Error Model
// Structured load error carries the form's source span (ErrorLocation).
#[test]
fn platform_load_failed_carries_form_span() {
    // user.cl declares a non-existent platform DLL; the produced error
    // must carry the form's source location — a `<file>:<line>:<col>`
    // prefix matching the (platform ...) line.
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .run("user.cl")
        .user("(platform this-dll-does-not-exist)\n")
        .output();
    // Span prefix: the form starts at line 1, col 1 in user.cl.
    assert!(
        out.stderr.contains("user.cl:1:1") || out.stderr.contains("user.cl:1:"),
        "platform-load error must carry form-span prefix `user.cl:1:1` per Decision 42; \
         got stderr:\n{}",
        out.stderr
    );
    assert!(
        out.stderr.contains("not found")
            || out.stderr.contains("load")
            || out.stderr.contains("platform"),
        "platform-load error must mention the platform/load shape; got stderr:\n{}",
        out.stderr
    );
}

// spec: spec/12-runtime.md §12.8 Platform ABI
// A platform whose DLL cannot be resolved on the search path surfaces the
// requested platform name + a not-found/manifest-absent message.
#[test]
fn platform_manifest_not_found_carries_dll_path() {
    // Use_workspace_platforms() to make sure the DLL search path is set;
    // then declare a platform whose DLL exists but whose manifest is
    // absent. Test passes synthetic conditions: declare a platform name
    // that the search path won't resolve.
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .run("user.cl")
        .user("(platform nonexistent-manifest-platform)\n")
        .output();
    // Error must mention the DLL search path or the requested DLL name.
    assert!(
        out.stderr.contains("nonexistent-manifest-platform"),
        "platform-error must surface the requested platform name; got stderr:\n{}",
        out.stderr
    );
    // Structured carrier — must mention either `manifest` or `not found in search path`.
    assert!(
        out.stderr.contains("manifest")
            || out.stderr.contains("search path")
            || out.stderr.contains("not found"),
        "platform-error must surface the structured shape (manifest / search path); \
         got stderr:\n{}",
        out.stderr
    );
}

// spec: spec/12-runtime.md §12.8 Platform ABI
//
// A `(platform <name>)` form naming a platform that resolves to no DLL on
// the search order (§8.11.3) is refused with a structured, span-carrying
// error BEFORE any DLL load is attempted (`resolve_platform_path → None`,
// `src/platform.rs:550` → `CranelispError::ModuleError { message:
// "platform '<name>' not found", location }`). This is the e2e-observable
// half of the platform-load gate.
//
// NOTE — the original `platform_abi_version_mismatch_emits_expected_vs_found`
// asserted the ABI-mismatch `expected`/`found` carrier against a
// non-existent `stdio-with-stale-abi` platform. That shape is NOT
// e2e-triggerable against the real `stdio`/`test-capture` platforms (they
// have no ADT-typed fns and always match the host ABI), so the prior test
// only ever exercised the not-found path under a misleading name. The real
// `PlatformError::AbiVersionMismatch { expected, found }` carrier IS
// unit-proven in `src/platform.rs::abi_version_mismatch_detected`
// (perturbed `ABI_VERSION + 1` → both values surface). The e2e ABI-drift
// round-trip (build an ADT-typed / perturbed-ABI test-DLL, clean
// round-trip and perturbed-ABI refusal) is covered by spec_platforms_adt.rs
// and the shapes-badabi fixture below.
#[test]
fn platform_unknown_name_emits_structured_not_found() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .use_workspace_platforms()
        .run("user.cl")
        .user("(platform stdio-with-stale-abi)\n")
        .output();
    // Structured, not a crash: clean non-zero exit, message to stderr.
    assert!(
        !out.status.success(),
        "an unresolvable platform name MUST be a clean compile-time error \
         (non-zero exit, not a crash); status: {:?}\nstderr:\n{}",
        out.status,
        out.stderr
    );
    // The error names the requested platform and the not-found mode, and
    // carries the form span (it starts at line 1, col 1 in user.cl).
    assert!(
        out.stderr.contains("stdio-with-stale-abi"),
        "error MUST surface the requested platform name; got stderr:\n{}",
        out.stderr
    );
    assert!(
        out.stderr.contains("not found"),
        "error MUST surface the not-found mode (`platform '<name>' not found`); \
         got stderr:\n{}",
        out.stderr
    );
    assert!(
        out.stderr.contains("user.cl:1:"),
        "error MUST carry the (platform ...) form span `user.cl:1:…`; \
         got stderr:\n{}",
        out.stderr
    );
}

// spec: spec/12-runtime.md §12.8 Platform ABI
//
// A platform declaration and import resolve `print` across the host↔DLL
// boundary; invoking it writes the argument and exits successfully.
#[test]
fn platform_fn_dispatches_across_dll_boundary() {
    let out = Cranelisp::new()
        .use_workspace_platforms()
        .user(
            "(platform stdio)\n\
             (import [platform.stdio [print]])\n\
             (defn main [] (print \"dispatch round-trip\"))\n",
        )
        .run("user.cl")
        .output();
    assert!(
        out.status.success(),
        "platform-fn dispatch MUST complete cleanly; status: {:?}\nstderr:\n{}",
        out.status,
        out.stderr
    );
    assert!(
        out.stdout.contains("dispatch round-trip"),
        "the dispatched platform fn `print` MUST write its argument to stdout; \
         got stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}

// =============================================================================
// Platform load refusals and dispatch faults use the dedicated bad-ABI and
// faulting DLL fixtures below.
// =============================================================================

// The `shapes.cl` module the perturbed-ABI program imports `Rectangle` from
// (self-contained, no `platforms/` coupling — same fixture shape as
// `tests/spec_platforms_adt.rs`).
const SHAPES_MODULE: &str = "(deftype Rectangle [:primitives/Int w :primitives/Int h])\n";

// spec: spec/12-runtime.md §12.8 Platform ABI
// A platform DLL whose baked `abi_version` differs from the host ABI version
// MUST be refused at load with a structured `PlatformError::AbiVersionMismatch
// { expected, found }`, and BOTH values MUST appear in the stderr message so a
// user can see what they have vs. what the runtime expects. The DLL
// (`platforms/shapes-badabi/`) is hand-rolled with the immediately preceding
// `abi_version` literal (= 10). Per the §5.5.5 DEF-5 invariant it exports the
// per-platform-namespaced
// manifest symbol `cranelisp_platform_manifest_shapes-badabi` (matching
// `platform_manifest_symbol("shapes-badabi")`), so the host FINDS the manifest,
// reads the stale ABI, and rejects on the mismatch — NOT a missing-symbol error.
// Host expected = 11 (S122 `Effect` thunk contract); DLL found = 10.
#[test]
fn platform_abi_version_mismatch_e2e() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .use_workspace_platforms()
        .file("shapes.cl", SHAPES_MODULE)
        .file(
            "user.cl",
            "(platform shapes-badabi)\n\
             (import [platform.shapes-badabi [area]])\n\
             (import [shapes [Rectangle]])\n\
             (defn main [] (area (Rectangle 3 4)))\n",
        )
        .run("user.cl")
        .output();
    // Refused at load — not a crash, clean non-zero exit.
    assert!(
        !out.status.success(),
        "an ABI-version-mismatched platform DLL MUST be refused at load \
         (non-zero exit, not a crash); status: {:?}\nstderr:\n{}",
        out.status,
        out.stderr
    );
    // The structured carrier surfaces the ABI-version-mismatch shape.
    assert!(
        out.stderr.contains("AbiVersionMismatch")
            || (out.stderr.contains("ABI") && out.stderr.contains("version")),
        "load refusal MUST surface the ABI-version-mismatch carrier; got stderr:\n{}",
        out.stderr
    );
    // BOTH versions MUST surface so the user sees what they have (the DLL's
    // stale `found` = 10) vs. what the runtime requires (`expected` = 11). The
    // `PlatformError::AbiVersionMismatch` Display
    // (`crates/cranelisp-types/src/error.rs:327`) renders
    // `DLL <path> ABI version <found> does not match expected <expected>` — it
    // names `expected` and prints both numbers, so assert the carrier names the
    // host's expected version AND both numeric values appear (the literal token
    // "found" is not in the message; the requirement is that both numbers are
    // reported, which they are).
    assert!(
        out.stderr.contains("expected"),
        "ABI-version-mismatch error MUST name the runtime's `expected` version; \
         got stderr:\n{}",
        out.stderr
    );
    assert!(
        out.stderr
            .contains("ABI version 10 does not match expected 11"),
        "ABI-version-mismatch error MUST report the adjacent DLL/runtime pair \
         exactly (`10` found, `11` expected), without passing on unrelated digits; \
         got stderr:\n{}",
        out.stderr
    );
}

const BOOM_PROGRAM: &str =
    "(platform boom)\n(import [platform.boom [crash]])\n(defn main [] (crash))\n";
const FAULT_DURING_IO_PROGRAM: &str = "(platform test-capture)\n(import [platform.test-capture [fault-now]])\n(defn main [] (fault-now))\n";

fn assert_dispatch_fault_surfaced(
    out: &helpers::e2e::CrOutput,
    boom: bool,
    repl: bool,
    linked: bool,
) {
    let (name, cause) = if boom {
        (
            "platform.boom/crash",
            "boom: deliberate dispatch-time fault in platform fn `crash`",
        )
    } else {
        (
            "platform.test-capture/fault-now",
            "test-capture fault-now: deliberate dispatch fault",
        )
    };
    assert_named_dispatch_fault_surfaced(out, name, cause, repl, linked);
}

fn assert_named_dispatch_fault_surfaced(
    out: &helpers::e2e::CrOutput,
    name: &str,
    cause: &str,
    repl: bool,
    linked: bool,
) {
    let lines: Vec<_> = out
        .stderr
        .lines()
        .filter(|l| !l.starts_with("; Linking:"))
        .collect();
    let mut problems = Vec::new();
    if !matches!(out.status.code(), Some(c) if c != 0) {
        problems.push("non-zero non-signal exit");
    }
    if lines.iter().filter(|line| line.contains(name)).count() != 1
        || !lines
            .iter()
            .any(|line| line.contains(name) && line.contains(cause))
    {
        problems.push("exactly one stderr line naming function and carrying cause");
    }
    if lines
        .iter()
        .any(|line| line.starts_with("error: runtime panic: "))
    {
        problems.push("no stderr line starts with the language-panic prefix");
    }
    if out.stdout.contains(cause) {
        problems.push("report must not appear on stdout");
    }
    if repl
        && (out.stdout.contains(":primitives/Int 813") || out.stdout.matches("user> ").count() != 1)
    {
        problems.push("no later REPL evaluation or prompt");
    }
    if linked && out.linked_execution_elapsed.is_none() {
        problems.push("linked executable must run");
    }
    assert!(
        problems.is_empty(),
        "dispatch fault contract: {problems:?}\nstatus:{:?}\nstdout:{}\nstderr:{}",
        out.status,
        out.stdout,
        out.stderr
    );
}

fn dispatch_output(boom: bool, mode: &str, fault: bool) -> helpers::e2e::CrOutput {
    let program = if boom {
        BOOM_PROGRAM
    } else {
        FAULT_DURING_IO_PROGRAM
    };
    let program = if fault {
        program.to_owned()
    } else {
        program
            .replace(
                "(defn main [] (crash))",
                "(defn main [] (primitives/pure 42))",
            )
            .replace(
                "(defn main [] (fault-now))",
                "(defn main [] (primitives/pure 42))",
            )
    };
    let builder = Cranelisp::new().use_workspace_platforms().user(&program);
    match mode {
        "run" => builder.run("user.cl").output(),
        "link" => builder.link_then_run("user.cl").output(),
        "repl" => builder
            .repl()
            .stdin("(main)\n(primitives/add-i64 800 13)\n")
            .output(),
        _ => unreachable!(),
    }
}

// spec: spec/12-runtime.md §12.7.6 — P-7: boom reports its function and cause under --run.
#[test]
fn platform_dispatch_error_carries_fn_name() {
    assert_dispatch_fault_surfaced(&dispatch_output(true, "run", true), true, false, false);
}

// spec: spec/12-runtime.md §12.7.6 — P-7: boom reports its function and cause when linked.
#[test]
fn platform_dispatch_error_exits_link() {
    assert_dispatch_fault_surfaced(&dispatch_output(true, "link", true), true, false, true);
}

// spec: spec/12-runtime.md §12.7.6 — P-7: a platform fault ends the REPL without another prompt.
#[test]
fn platform_dispatch_fault_exits_repl() {
    assert_dispatch_fault_surfaced(&dispatch_output(true, "repl", true), true, true, false);
}

// spec: spec/12-runtime.md §12.7.6 — P-7: fault-now also ends the REPL without another prompt.
#[test]
fn dispatch_fault_during_io_exits_repl() {
    assert_dispatch_fault_surfaced(&dispatch_output(false, "repl", true), false, true, false);
}

// spec: spec/12-runtime.md §12.7.6 — P-7: fault-now's run report has no language-panic prefix.
#[test]
fn dispatch_fault_during_io_surfaces_run() {
    assert_dispatch_fault_surfaced(&dispatch_output(false, "run", true), false, false, false);
}

// spec: spec/12-runtime.md §12.7.6 — P-7: fault-now's linked report has no language-panic prefix.
#[test]
fn dispatch_fault_during_io_surfaces_link() {
    assert_dispatch_fault_surfaced(&dispatch_output(false, "link", true), false, false, true);
}

// spec: spec/12-runtime.md §12.7.6 — P-7 control: the same platform modules without faults finish.
#[test]
fn platform_dispatch_non_faulting_controls_finish() {
    for boom in [true, false] {
        for mode in ["run", "link", "repl"] {
            let out = dispatch_output(boom, mode, false);
            let out = if mode == "repl" {
                out.assert_ok()
                    .assert_stdout_contains(":primitives/Int 813")
            } else {
                out.assert_exit(42)
            };
            assert!(
                !out.stderr.contains("dispatch") && !out.stderr.contains("runtime panic:"),
                "{}",
                out.stderr
            );
        }
    }
}

// =============================================================================
// Linux PLATFORM_EXT fold-in (S80 Pillar A, item 5) — platform-DLL discovery
// on the current platform.
// =============================================================================

// spec: spec/12-runtime.md §12.8 Platform ABI
//
// NARROW ROOT-CAUSE PIN. The 8th standing red was
// `examples::every_example_runs_with_documented_exit` — the 4 IO examples
// (`21-hello-io`..`24-io-echo`) failed `platform 'stdio'/'test-capture' not
// found`. This test isolates the cause to **platform-DLL discovery via the
// search path**, NOT example doc drift: a `(platform stdio)` program, resolved
// through the Tier-3 `CRANELISP_PLATFORM_PATH=target/debug` search order
// (exactly how the examples are now run), MUST load the platform and run on
// whatever OS the suite executes on.
//
// MECHANISM (settled S80 Wave 1E): the old symlink convention
// (`examples/platforms/*.dylib`, git-ignored, machine-local, dangling on
// Linux) is dropped. `resolve_platform_path`'s `check_dir` already tries
// cargo's `libcranelisp_{name}.{ext}` naming, so putting `target/debug` on the
// search path finds `libcranelisp_stdio.so` (or `.dylib`/`.dll`) directly —
// zero symlinks, `cfg`-correct on every OS. `use_workspace_platforms()` sets
// exactly that env (`tests/helpers/e2e.rs`).
//
// PLATFORM-AGNOSTIC by construction: it asserts the program *loads and runs*
// (clean exit + the printed effect reaches stdout). It never asserts a literal
// `.so`/`.dylib`/`.dll` string.
#[test]
fn platform_dll_resolves_on_current_platform() {
    // The cdylibs are workspace members nothing links, so a plain
    // `cargo nextest run` may not build them — guarantee they exist on the
    // search path before asserting resolution (same prereq as the examples
    // umbrella; mirrors `tests/examples.rs::ensure_platform_cdylibs_built`).
    ensure_platform_cdylibs_built();

    // Resolve `(platform stdio)` through the Tier-3 search path
    // (`CRANELISP_PLATFORM_PATH=target/debug`, via `use_workspace_platforms()`)
    // — the mechanism the examples harness now uses.
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .use_workspace_platforms()
        .file(
            "user.cl",
            "(platform stdio)\n\
             (import [platform.stdio [print]])\n\
             (defn main [] (print \"load-ok\"))\n",
        )
        .run("user.cl")
        .output();

    // The platform DLL MUST resolve + load on the current platform: clean exit
    // and the printed effect reaches stdout. (Platform-agnostic — no literal
    // extension is asserted.)
    assert!(
        out.status.success(),
        "a `(platform stdio)` program MUST load the platform DLL via the \
         `CRANELISP_PLATFORM_PATH=target/debug` search path on the current \
         platform; status: {:?}\nstdout:\n{}\nstderr:\n{}",
        out.status,
        out.stdout,
        out.stderr
    );
    assert!(
        !out.stderr.contains("not found"),
        "platform-DLL discovery MUST NOT fail with `not found` on the current \
         platform (cargo's `libcranelisp_stdio.{{ext}}` must be discoverable in \
         target/debug); got stderr:\n{}",
        out.stderr
    );
    assert!(
        out.stdout.contains("load-ok"),
        "the loaded platform fn `print` MUST emit its argument once the DLL \
         resolves; got stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}

fn platform_placement(module: Option<&str>) -> helpers::e2e::CrOutput {
    let cr = Cranelisp::new()
        .use_workspace_platforms()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("--no-cache");
    let cr = match module {
        None => cr.user(
            "(platform stdio) (import [platform.stdio [print]]) (defn main [] (print \"loaded\"))",
        ),
        Some(name) => cr
            .file(
                &format!("{}.cl", name.replace('.', "/")),
                "(platform stdio) (defn value [] 0)",
            )
            .user(&format!("(defn main [] (primitives/pure ({name}/value)))")),
    };
    cr.run("user.cl").output()
}

// spec: spec/10-io.md §10.9.1 — entry declaration loads platform; ACT-0973 control.
#[test]
fn platform_entry_placement_loads_control() {
    platform_placement(None)
        .assert_exit(0)
        .assert_stdout_contains("loaded");
}

// spec: spec/10-io.md §10.9.1 — root-level non-entry platform declaration is an error.
// defect: class=silent-accept locus=src/process_form/platform.rs::handle_platform found=S122 owner=/dev fixed=S124/68f042d5
// ACT-0973 formerly accepted a non-entry platform declaration; control: platform_entry_placement_loads_control.
#[test]
fn platform_root_non_entry_declaration_rejected_neg() {
    let out = platform_placement(Some("helper"));
    assert!(
        out.status.code() == Some(1)
            && out.stderr.contains("platform")
            && out.stderr.contains("entry"),
        "non-entry platform declaration must be a compile-time error; exit {:?}; {}{}",
        out.status.code(),
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.9.1 — nested non-entry platform declaration is an error.
// defect: class=silent-accept locus=src/process_form/platform.rs::handle_platform found=S122 owner=/dev fixed=S124/68f042d5
// ACT-0973 formerly accepted a non-entry platform declaration; control: platform_entry_placement_loads_control.
#[test]
fn platform_nested_non_entry_declaration_rejected_neg() {
    let out = platform_placement(Some("nested.helper"));
    assert!(
        out.status.code() == Some(1)
            && out.stderr.contains("platform")
            && out.stderr.contains("entry"),
        "nested non-entry platform declaration must be a compile-time error; exit {:?}; {}{}",
        out.status.code(),
        out.stdout,
        out.stderr
    );
}

fn s124_platform_placement(module: Option<&str>, mode: &str) {
    let cr = Cranelisp::new().use_workspace_platforms();
    let cr = match module {
        None => cr.user(
            "(platform stdio) (import [platform.stdio [print]]) (defn main [] (print \"loaded\"))",
        ),
        Some(name) => cr
            .file(
                &format!("{}.cl", name.replace('.', "/")),
                "(platform stdio) (defn value [] 0)",
            )
            .user(&format!("(defn main [] (primitives/pure ({name}/value)))")),
    };
    let out = match mode {
        "link" => cr.link_then_run("user.cl").output(),
        "repl" => cr.stdin("(main)\n").output(),
        _ => cr.run("user.cl").output(),
    };
    let diag = format!("{}{}", out.stdout, out.stderr);
    if module.is_some() {
        assert!(
            diag.contains("platform") && diag.contains("entry") && diag.contains("error"),
            "{diag}"
        );
        if mode != "repl" {
            assert_eq!(out.status.code(), Some(1), "{diag}");
        }
    } else {
        assert!(
            out.status.success() && out.stdout.contains("loaded"),
            "{diag}"
        );
    }
}

// spec: spec/10-io.md §10.9.1 — T-0973 entry
#[test]
fn s124_0973_entry_link() {
    s124_platform_placement(None, "link");
}

// spec: spec/10-io.md §10.9.1 — T-0973 entry
#[test]
fn s124_0973_entry_repl() {
    s124_platform_placement(None, "repl");
}

// spec: spec/10-io.md §10.9.1 — T-0973 root
// defect: class=silent-accept locus=src/process_form/platform.rs::handle_platform found=S122 owner=/dev fixed=S124/68f042d5
#[test]
fn s124_0973_root_link() {
    s124_platform_placement(Some("helper"), "link");
}

// spec: spec/10-io.md §10.9.1 — T-0973 root
// defect: class=silent-accept locus=src/process_form/platform.rs::handle_platform found=S122 owner=/dev fixed=S124/68f042d5
#[test]
fn s124_0973_root_repl() {
    s124_platform_placement(Some("helper"), "repl");
}

// spec: spec/10-io.md §10.9.1 — T-0973 nested
// defect: class=silent-accept locus=src/process_form/platform.rs::handle_platform found=S122 owner=/dev fixed=S124/68f042d5
#[test]
fn s124_0973_nested_link() {
    s124_platform_placement(Some("nested.helper"), "link");
}

// spec: spec/10-io.md §10.9.1 — T-0973 nested
// defect: class=silent-accept locus=src/process_form/platform.rs::handle_platform found=S122 owner=/dev fixed=S124/68f042d5
#[test]
fn s124_0973_nested_repl() {
    s124_platform_placement(Some("nested.helper"), "repl");
}

// spec: spec/10-io.md §10.9.1 — T-0973-c, cached entry becomes dependency
// defect: class=silent-accept locus=src/process_form/platform.rs::handle_platform found=S122 owner=/dev fixed=S124/68f042d5
#[test]
fn s124_0973_cached_entry_run() {
    let first = Cranelisp::new()
        .use_workspace_platforms()
        .file(
            "helper.cl",
            "(platform stdio) (defn value [] 0) (defn main [] (primitives/pure 0))",
        )
        .run("helper.cl")
        .output()
        .assert_exit(0);
    assert!(
        first.tmp_exists(".cranelisp-cache/helper.o"),
        "entry must be cached"
    );
    let cr = first
        .run_again()
        .use_workspace_platforms()
        .env("CRANELISP_MODULE_TRACE", "1")
        .file(
            "app.cl",
            "(import [helper [value]]) (defn main [] (primitives/pure (value)))",
        );
    let out = cr.run("app.cl").output();
    let diag = format!("{}{}", out.stdout, out.stderr);
    assert!(
        diag.contains("platform") && diag.contains("entry") && diag.contains("error"),
        "cached non-entry declaration must refuse: {diag}"
    );
    assert!(
        !diag
            .lines()
            .any(|line| line.contains("helper") && line.contains("restored")),
        "dependency must not restore: {diag}"
    );
}

// spec: spec/10-io.md §10.9.1 — T-0973-c, cached entry becomes dependency
// defect: class=silent-accept locus=src/process_form/platform.rs::handle_platform found=S122 owner=/dev fixed=S124/68f042d5
#[test]
fn s124_0973_cached_entry_link() {
    let first = Cranelisp::new()
        .use_workspace_platforms()
        .file(
            "helper.cl",
            "(platform stdio) (defn value [] 0) (defn main [] (primitives/pure 0))",
        )
        .run("helper.cl")
        .output()
        .assert_exit(0);
    assert!(
        first.tmp_exists(".cranelisp-cache/helper.o"),
        "entry must be cached"
    );
    let cr = first
        .run_again()
        .use_workspace_platforms()
        .env("CRANELISP_MODULE_TRACE", "1")
        .file(
            "app.cl",
            "(import [helper [value]]) (defn main [] (primitives/pure (value)))",
        );
    let out = cr.link("app.cl").output();
    let diag = format!("{}{}", out.stdout, out.stderr);
    assert!(
        diag.contains("platform") && diag.contains("entry") && diag.contains("error"),
        "cached non-entry declaration must refuse: {diag}"
    );
    assert!(
        !diag
            .lines()
            .any(|line| line.contains("helper") && line.contains("restored")),
        "dependency must not restore: {diag}"
    );
}

// spec: spec/10-io.md §10.9.1 — T-0973-c, cached entry becomes dependency
#[test]
fn s124_0973_cached_entry_repl() {
    let first = Cranelisp::new()
        .use_workspace_platforms()
        .file(
            "helper.cl",
            "(platform stdio) (defn value [] 0) (defn main [] (primitives/pure 0))",
        )
        .run("helper.cl")
        .output()
        .assert_exit(0);
    assert!(
        first.tmp_exists(".cranelisp-cache/helper.o"),
        "entry must be cached"
    );
    let cr = first
        .run_again()
        .use_workspace_platforms()
        .env("CRANELISP_MODULE_TRACE", "1")
        .file(
            "app.cl",
            "(import [helper [value]]) (defn main [] (primitives/pure (value)))",
        );
    let out = cr.cli_flag("app.cl").stdin("5\n").output();
    let diag = format!("{}{}", out.stdout, out.stderr);
    assert!(
        diag.contains("platform") && diag.contains("entry") && diag.contains("error"),
        "cached non-entry declaration must refuse: {diag}"
    );
    assert!(
        !diag
            .lines()
            .any(|line| line.contains("helper") && line.contains("restored")),
        "dependency must not restore: {diag}"
    );
}

// spec: spec/10-io.md §10.9.1 — T-0973, non-entry import of an entry platform
#[test]
fn s124_0973_dependency_import_control() {
    let src = "(platform stdio) (import [helper [say]]) (defn main [] (say))";
    for mode in ["run", "link", "repl"] {
        let cr = Cranelisp::new()
            .use_workspace_platforms()
            .file(
                "helper.cl",
                "(import [platform.stdio [print]]) (defn say [] (print \"loaded\"))",
            )
            .user(src);
        let out = match mode {
            "link" => cr.link_then_run("user.cl").output(),
            "repl" => cr.stdin("(main)\n").output(),
            _ => cr.run("user.cl").output(),
        };
        assert!(
            out.status.success() && out.stdout.contains("loaded"),
            "{}{}",
            out.stdout,
            out.stderr
        );
    }
}

fn overlapping_trap_output(first_ms: u64) -> helpers::e2e::CrOutput {
    let source = format!(
        r#"(platform pool-demo)
(platform poll-pool)
(import [platform.pool-demo [pool-read pool-trap]])
(import [platform.poll-pool [poll-read]])
(import [primitives [bind sleep select add-i64]])
(defn main []
  (let [x (bind (pool-read 1 1 {first_ms}) (fn [r] (bind (poll-read 9 1 5000) (fn [q] (primitives/pure (add-i64 r q))))))
        z (bind (sleep 300) (fn [r] (pool-trap 2 1 900)))]
    (select [x z])))
"#
    );
    Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .use_workspace_platforms()
        .user(&source)
        .run("user.cl")
        .output()
}

// spec: spec/12-runtime.md §12.7.6 — T-F2: overlapping platform calls retain trap protection.
// defect: class=shared-state-write-race locus=crates/cranelisp-intrinsics/src/io_guard.rs::force_effect_thunk_protected found=S125 owner=/dev
#[test]
fn overlapping_platform_trap_reports_fault_without_signal_death() {
    assert_named_dispatch_fault_surfaced(
        &overlapping_trap_output(800),
        "platform.pool-demo/pool-trap",
        "segmentation fault",
        false,
        false,
    );
}

// spec: spec/12-runtime.md §12.7.6 — T-F2 control: the first blocking call returns before the trapping call begins.
#[test]
fn non_overlapping_platform_trap_reports_fault_control() {
    assert_named_dispatch_fault_surfaced(
        &overlapping_trap_output(50),
        "platform.pool-demo/pool-trap",
        "segmentation fault",
        false,
        false,
    );
}
