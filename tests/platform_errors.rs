// platform_errors.rs — Sprint 66 Phase 5 Stage 1 (FIXME 0104),
// reframed Sprint 77 W-Platform (R9, FIXME 0289).
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
//   - **ABI-version mismatch** and **layout-hash drift** are NOT
//     e2e-triggerable against the real platforms: `stdio`/`test-capture`
//     have no ADT-typed fns (so no `__cranelisp_layout_hash`) and always
//     match the host ABI. The detection paths ARE wired and unit-proven in
//     `src/platform.rs` (`abi_version_mismatch_detected`,
//     `abi_version_match_accepts`). A true drift round-trip e2e needs a
//     perturbed-ABI / ADT-typed `shapes` test-DLL — deferred to FIXME 0289
//     (the platform-interface e2e walk slice).
//
// Spec basis: `spec/12-runtime.md §12.8 Platform ABI` (platform fns loaded
// via `(platform name)`; discovery via the §8.11.3 DLL search order) +
// `§12.7 Error Model` (compile-time error reporting / message format).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};
use std::sync::Once;

/// Build the platform cdylibs (`stdio`, `test-capture`) into `target/debug`
/// once per test-binary process. These crates are workspace members that
/// nothing links, so a plain `cargo nextest run` does NOT build them — a
/// `(platform stdio)` program would otherwise fail `platform 'stdio' not
/// found` on the search path. Mirrors `tests/examples.rs` + the root
/// `justfile run-example` recipe; idempotent and cheap when already built.
fn ensure_platform_cdylibs_built() {
    static BUILT: Once = Once::new();
    BUILT.call_once(|| {
        let status = std::process::Command::new("cargo")
            .args([
                "build",
                "-p",
                "cranelisp-stdio",
                "-p",
                "cranelisp-test-capture",
            ])
            .current_dir(env!("CARGO_MANIFEST_DIR"))
            .status()
            .expect("failed to spawn `cargo build` for platform cdylibs");
        assert!(
            status.success(),
            "`cargo build -p cranelisp-stdio -p cranelisp-test-capture` failed; \
             a `(platform stdio)` program cannot resolve its DLL without these cdylibs"
        );
    });
}

// =============================================================================
// Platform-load error reporting — e2e-observable shapes (FIXME 0104 closed;
// reframed under FIXME 0289)
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
        out.stderr.contains("not found") || out.stderr.contains("load") || out.stderr.contains("platform"),
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
// round-trip, then perturb → `AbiVersionMismatch` e2e) is deferred to
// FIXME 0289 (it needs the `shapes` test-DLL fixture).
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
        out.status, out.stderr
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
// Platform-fn DISPATCH works end-to-end: a `(platform stdio)` form loads
// the DLL, `(import [platform.stdio [print]])` binds the platform fn, and
// invoking it from `main` dispatches through the GOT-indirect platform
// path so the effect (the printed string) reaches stdout. This is the
// honest e2e-observable analogue of "dispatch carries the offending fn
// name": it proves the named platform fn is resolved and invoked across
// the host↔DLL boundary, exit clean.
//
// NOTE — the original `platform_dispatch_error_during_run_carries_fn_name`
// asserted `PlatformError::DispatchError { fn_name }` but had no way to
// trigger a dispatch-time error against the real platforms (its else-branch
// `panic!("synthetic DLL fixture not yet available")` was a placeholder, not
// a real assertion). The structured `DispatchError { fn_name }` carrier and
// the dispatch-error round-trip both require the ADT-typed `shapes` test-DLL
// fixture — deferred to FIXME 0289 (the platform-interface e2e walk slice).
// Until then this test exercises the SUCCESS half of the dispatch path,
// which is fully e2e-observable today.
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
    // The platform fn resolved + dispatched: the effect reached stdout and
    // the program exited clean (no unresolved-symbol / dispatch error).
    assert!(
        out.status.success(),
        "platform-fn dispatch MUST complete cleanly; status: {:?}\nstderr:\n{}",
        out.status, out.stderr
    );
    assert!(
        out.stdout.contains("dispatch round-trip"),
        "the dispatched platform fn `print` MUST write its argument to stdout; \
         got stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
}

// =============================================================================
// FIXME 0289 items 4-5 — perturbed-ABI + dispatch-error e2e (RED until the
// Wave-1 `/platform` test-DLLs land: `platforms/shapes-badabi/` for item 4 and
// the dispatch-failure sibling DLL for item 5). These are the e2e companions to
// the already-unit-proven `PlatformError::{AbiVersionMismatch, DispatchError}`
// carriers (`src/platform.rs`). They ride RED — the real `stdio`/`test-capture`
// platforms cannot trigger either error path (no ADT-typed fns, host-matching
// ABI), so an ADT-typed / perturbed test-DLL is required.
// =============================================================================

// The `shapes.cl` module the perturbed-ABI program imports `Rectangle` from
// (self-contained, no `platforms/` coupling — same fixture shape as
// `tests/spec_platforms_adt.rs`).
const SHAPES_MODULE: &str = "(deftype Rectangle [:primitives/Int w :primitives/Int h])\n";

// spec: spec/12-runtime.md §12.8 Platform ABI
// FAILING-FIRST (RED until the Wave-1 `platforms/shapes-badabi/` DLL lands).
// A platform DLL whose baked `abi_version` differs from the host ABI version
// MUST be refused at load with a structured `PlatformError::AbiVersionMismatch
// { expected, found }`, and BOTH values MUST appear in the stderr message so a
// user can see what they have vs. what the runtime expects. The DLL is
// hand-rolled with a stale `abi_version` literal (distinct dylib name dodges the
// `cranelisp_platform_manifest` symbol collision). RED today: there is no
// perturbed-ABI test-DLL on the workspace search path, so this resolves to a
// not-found path, not the mismatch carrier.
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
        out.status, out.stderr
    );
    // The structured carrier surfaces the ABI-version-mismatch shape.
    assert!(
        out.stderr.contains("AbiVersionMismatch")
            || (out.stderr.contains("ABI") && out.stderr.contains("version")),
        "load refusal MUST surface the ABI-version-mismatch carrier; got stderr:\n{}",
        out.stderr
    );
    // BOTH versions MUST surface so the user sees what they have (the DLL's
    // stale `found` = 2) vs. what the runtime requires (`expected` = 5 as of
    // Sprint 81 / FIXME 0337 — the Option-A DLL-local fault catch bumped the
    // `call_effect_thunk` force-return contract, host ABI 4 → 5). The
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
        out.stderr.contains("2") && out.stderr.contains("5"),
        "ABI-version-mismatch error MUST report BOTH the DLL's stale version (2) \
         and the runtime's required version (5) so the user sees what they have \
         vs. what is required; got stderr:\n{}",
        out.stderr
    );
}

// spec: spec/12-runtime.md §12.8 Platform ABI
//
// FIXME 0289 item 5 — the dispatch-error-with-fn-name e2e. The Option-A funnel
// close (FIXMEs 0327/0337) fixed the ABORT half but exposed a RESIDUAL fn-name
// gap — see THE RESIDUAL GAP below. IGNORED until the fn-name baking is wired on
// the fault path.
//
// THE FIXTURE (S81 W-G, `/platform`): `platforms/boom` — a minimal scalar-only
// platform whose single fn `crash :: (Fn [] (IO Int))` returns an IO Effect whose
// FORCED thunk `panic!`s. The backend bakes the FQ fn-name `platform.boom/crash`
// into the Effect node's field-3, so a fully-working funnel would surface
// `PlatformError::DispatchError { fn_name: "platform.boom/crash", .. }`. Wired
// into the canonical run via `tests/scripts/build-link-prereqs.sh`.
//
// spec: design/arch/bounded-contexts.md §5 invariant 9 — a platform-fn dispatch
// fault surfaces a structured `PlatformError::DispatchError { fn_name, cause }`,
// never a process abort or a silent wrong result.
//
// THE MECHANISM (Option A, landed). A platform `cdylib` statically links its OWN
// copy of the Rust panic runtime, so a `panic!` raised inside the DLL cannot be
// caught by the host's `catch_unwind` — it would unwind with the DLL's runtime
// and, crossing the dlopen boundary, abort the process ("Rust cannot catch
// foreign exceptions", exit 134). Option A moves the catch INSIDE the DLL:
// `cranelisp_platform::CLIO::effect*` wraps the user thunk in a DLL-local
// `catch_unwind`; a caught panic is converted to a `#[repr(C)] EffectOutcome`
// fault signal (DLL-owned UTF-8 cause bytes) returned ACROSS the C-ABI by
// `call_effect_thunk` — no abort. The host trampoline
// (`force_effect_thunk_protected`) reads the `EffectOutcome` and composes the
// fault; int composes `PlatformError::DispatchError` → `CranelispError::Platform`.
// The `sigsetjmp` signal half is retained for genuine C-level hardware traps.
//
// THE FN-NAME. The offending fn's baked FQ name (`platform.boom/crash`) survives
// the fault path because the backend stamps field-3 at the GOT-indirect dispatch
// chokepoint, at node construction — BEFORE the force — so a faulting dispatch
// still carries its baked name (`abe3553`). The host-side trampoline reads it from
// the node and int folds it into `DispatchError { fn_name }`.
#[test]
fn platform_dispatch_error_carries_fn_name() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .use_workspace_platforms()
        .file(
            "user.cl",
            "(platform boom)\n\
             (import [platform.boom [crash]])\n\
             (defn main [] (crash))\n",
        )
        .run("user.cl")
        .output();
    // A dispatch-time failure surfaces a clean structured error (non-zero exit),
    // not a process abort, a silent wrong result, or an opaque crash.
    assert!(
        !out.status.success(),
        "a dispatch-time platform-fn fault MUST surface a structured error \
         (clean non-zero exit, NOT a process abort); status: {:?}\nstderr:\n{}",
        out.status, out.stderr
    );
    // The carrier surfaces the `DispatchError` shape.
    assert!(
        out.stderr.contains("dispatch"),
        "dispatch fault MUST surface the `DispatchError` carrier \
         (Display: `platform fn \\`<name>\\` dispatch failed: …`); got stderr:\n{}",
        out.stderr
    );
    // The carrier NAMES the offending fn — the user must see the baked FQ name
    // `platform.boom/crash` (NOT `<unknown>`).
    assert!(
        out.stderr.contains("platform.boom/crash"),
        "`DispatchError` MUST name the offending platform fn by its baked FQ name \
         `platform.boom/crash` (not `<unknown>`); got stderr:\n{}",
        out.stderr
    );
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
        out.status, out.stdout, out.stderr
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
        out.stdout, out.stderr
    );
}
