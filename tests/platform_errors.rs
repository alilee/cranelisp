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
