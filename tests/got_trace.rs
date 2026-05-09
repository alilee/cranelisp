// got_trace.rs — Sprint 66 Phase 5 Stage 1 (FIXME 0099).
//
// Authored failing-not-ignored at Phase-5 Stage-1 open per /qa Phase-5
// obligation (METHOD §2.2). New e2e file mirroring the existing
// `CRANELISP_IO_TRACE`-shape coverage. Asserts the GotObserver extension
// point (backend Phase 1) + int-side ring buffer + flush guard (Phase 2)
// produce stderr trace events when `CRANELISP_GOT_TRACE=1`.
//
// What this file covers (per `tests/plan/implementation-slice-s66.md §5.2`):
//   - JitWrite events fire when symbols are JIT'd.
//   - LinkerWrite events fire when cached objects are loaded.
//   - Redefinition events fire when a REPL redefines a name.
//   - Negative: zero overhead when env var unset (no observer registered;
//     no got-trace stderr lines).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// =============================================================================
// FIXME 0099 — GotObserver: JitWrite event
// =============================================================================

// spec: spec/12-runtime.md §"Diagnostic logging" (CRANELISP_GOT_TRACE
// reservation, parallel to CRANELISP_IO_TRACE).
// FIXME(/dev backend FIXME 0099 Phase 1 + /dev int FIXME 0099 Phase 2) —
// fails until backend authors GotObserver trait + int wires the ring
// buffer + flush guard + register call.
#[test]
fn got_trace_emits_jit_write_event() {
    // A simple `--run` program — produces at least one JitWrite event
    // for `main` (and the prelude defns). Asserts presence of the
    // `JitWrite` event tag in stderr.
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user("(defn main [] (Pure 0))\n")
        .env("CRANELISP_GOT_TRACE", "1")
        .output();
    out.assert_stderr_contains("JitWrite");
}

// spec: spec/12-runtime.md §"Diagnostic logging"
// FIXME(/dev backend FIXME 0099 Phase 1 + /dev int FIXME 0099 Phase 2) —
// fails identically until the observer extension point exists.
#[test]
fn got_trace_emits_linker_write_event_on_cache_hit() {
    // First run populates cache; second run (same TempDir via run_again)
    // exercises the cache-hit path — observer fires LinkerWrite events
    // when cached objects are loaded into GOT slots.
    let warm = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user("(defn main [] (Pure 0))\n")
        .output();
    let out = warm
        .run_again()
        .with_prelude_no_overwrite(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .env("CRANELISP_GOT_TRACE", "1")
        .output();
    out.assert_stderr_contains("LinkerWrite");
}

// spec: spec/12-runtime.md §"Diagnostic logging"
// FIXME(/dev backend FIXME 0099 Phase 1 + /dev int FIXME 0099 Phase 2) —
// fails until the observer surfaces redefinition events.
#[test]
fn got_trace_emits_redefinition_event_on_repl_redefn() {
    // REPL defines `foo` then redefines `foo` — the GOT slot rewrite
    // surfaces as a `Redefinition` event in stderr.
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .env("CRANELISP_GOT_TRACE", "1")
        .stdin(
            "(defn foo [] 1)\n\
             (defn foo [] 2)\n\
             (foo)\n",
        )
        .output();
    out.assert_stderr_contains("Redefinition");
}

// spec: spec/12-runtime.md §"Diagnostic logging" — zero-overhead claim
// (negative test).
// FIXME(/dev backend FIXME 0099 Phase 1) — fails until the observer
// extension point exists; this test asserts ABSENCE of trace lines when
// the env var is unset, validating the relaxed-load null check zero-cost
// path.
#[test]
fn got_trace_off_path_zero_overhead_neg() {
    // Run the same program WITHOUT the env var — no got-trace lines
    // should appear in stderr.
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user("(defn main [] (Pure 0))\n")
        .output();
    let stderr = &out.stderr;
    assert!(
        !stderr.contains("JitWrite") && !stderr.contains("LinkerWrite") && !stderr.contains("Redefinition"),
        "no GOT trace events should fire when CRANELISP_GOT_TRACE is unset (zero-overhead claim); \
         got stderr:\n{}",
        stderr
    );
}
