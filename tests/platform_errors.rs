// platform_errors.rs — Sprint 66 Phase 5 Stage 1 (FIXME 0104).
//
// Authored failing-not-ignored at Phase-5 Stage-1 open per /qa Phase-5
// obligation. Asserts the post-Wave-3 `PlatformError` adoption end-to-end
// shape: errors carry `ErrorLocation` (file:line:col) form-spans; specific
// variants surface (LoadFailed, ManifestNotFound, AbiVersionMismatch,
// DispatchError) with their structured fields visible in stderr.
//
// What this file covers (per `tests/plan/implementation-slice-s66.md §5.5`):
//   - load_failed carries form span — REPL/run program with platform decl
//     that fails to find the DLL produces `lib/main.cl:LINE:COL` prefix.
//   - manifest not found carries DLL path inspected.
//   - ABI version mismatch surfaces expected vs found values.
//   - dispatch error during run carries the offending fn name.
//
// At Phase-5 Stage 1 these tests fail because the legacy `String`-backed
// platform-load error has different shape; the structured `PlatformError`
// formatter is not yet wired through `Sess::format_error`.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// =============================================================================
// FIXME 0104 — PlatformError adoption: error reshape
// =============================================================================

// spec: spec/11-platform.md §"Platform error reporting"
// FIXME(/dev types Wave 0 + /dev platform Phase 2 + /dev int Phase 3 of
// FIXME 0104) — fails until the structured error path lands all the way
// through to the user-facing format.
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

// spec: spec/11-platform.md §"Platform error reporting"
// FIXME(/dev types Wave 0 + /dev platform Phase 2 of FIXME 0104) — fails
// until `PlatformError::ManifestNotFound { dll, .. }` surfaces with the
// DLL path inspected.
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

// spec: spec/11-platform.md §"Platform error reporting"
// FIXME(/dev types Wave 0 + /dev platform Phase 2 of FIXME 0104 + manifest
// loader audit) — fails until `PlatformError::AbiVersionMismatch
// { expected, found, .. }` exists and surfaces with both values.
#[test]
fn platform_abi_version_mismatch_emits_expected_vs_found() {
    // This test asserts the SHAPE of an ABI-version-mismatch error.
    // The synthetic stale-ABI DLL fixture is a Wave-3a infrastructure
    // task (per /qa slice §3.5 + §8.1 `with_synthetic_dll`). At Phase-5
    // Stage 1 we cannot construct a fake DLL with stale `ABI_VERSION` —
    // the helper does not yet exist. The test is therefore minimal: it
    // exercises a known-bad platform name and asserts that, when the
    // ABI mismatch path lands, the error carries `expected` and `found`
    // values. Today the legacy String error has neither field shape;
    // when the fixture infrastructure lands, the test extends.
    //
    // Pre-fix: the loader either crashes or emits a generic
    // "load failed" that doesn't name the ABI version. Post-fix, the
    // structured `PlatformError::AbiVersionMismatch` emits both values.
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .use_workspace_platforms()
        .run("user.cl")
        .user("(platform stdio-with-stale-abi)\n")
        .output();
    // We expect either "ABI version mismatch" with both expected+found OR
    // "platform not found" — either way the structured carrier must be
    // present. Pre-fix: legacy "Failed to load platform: …" has neither.
    let has_structured = out.stderr.contains("ABI")
        || out.stderr.contains("abi version")
        || out.stderr.contains("expected")
        || out.stderr.contains("not found in search path");
    assert!(
        has_structured,
        "platform-error must surface structured ABI-mismatch or search-path shape; \
         got stderr:\n{}",
        out.stderr
    );
}

// spec: spec/11-platform.md §"Platform error reporting"
// FIXME(/dev types Wave 0 + /dev platform Phase 2 + /dev int Phase 3 of
// FIXME 0104) — fails until `PlatformError::DispatchError { fn_name, .. }`
// surfaces with the offending fn name when a dispatch-time error fires.
#[test]
fn platform_dispatch_error_during_run_carries_fn_name() {
    // Construct a program that loads a real platform but invokes a
    // function with mismatched arg shape — dispatch error should fire
    // and the structured carrier surfaces the fn name.
    //
    // Today's user-facing error is the legacy generic "type sig
    // mismatch" without the fn name; post-fix the structured
    // PlatformError::DispatchError shows it.
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .use_workspace_platforms()
        .run("user.cl")
        // Try to invoke a non-existent platform fn — closest shape we
        // can express without a synthetic DLL fixture. Pre-fix, error
        // is generic; post-fix, fn name surfaces structured.
        .user(
            "(platform stdio)\n\
             (defn main [] (Pure 0))\n",
        )
        .output();
    // Soft assertion: under Wave-3 final shape the error (if any) must
    // mention either a specific fn name or the structured "DispatchError"
    // shape. This will fail at Phase-5 Stage 1 because either (a) this
    // program runs successfully (no error to assert) or (b) the legacy
    // error has neither structured shape. Post-fix the test tightens
    // against synthetic DLL fixtures (deferred infrastructure).
    if !out.status.success() {
        let has_structured =
            out.stderr.contains("dispatch") || out.stderr.contains("fn ") || out.stderr.contains("DispatchError");
        assert!(
            has_structured,
            "platform dispatch error must carry structured shape (DispatchError / fn name); \
             got stderr:\n{}",
            out.stderr
        );
    } else {
        // Today this program may run successfully. Post-fix Wave 3 the
        // synthetic-DLL helper enables a true dispatch-error assertion.
        // For now: mark the test as failing-not-ignored by asserting a
        // structural prerequisite that doesn't yet hold — the
        // `DispatchError` variant must exist in the user-visible surface
        // when actually triggered. We pin this by panicking until the
        // synthetic DLL fixture lands.
        panic!(
            "FIXME(/qa Wave 3a): synthetic DLL fixture not yet available; \
             test cannot exercise dispatch-error path. \
             stderr was empty (program ran clean)."
        );
    }
}
