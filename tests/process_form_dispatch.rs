// process_form_dispatch.rs — Sprint 66 Phase 5 Stage 1 (FIXME 0098).
//
// Authored failing-not-ignored at Phase-5 Stage-1 open per /qa Phase-5
// obligation (METHOD §2.2). These three tests gate the **critical-path
// triad** identified by /arch Phase-2 recommendation #1: the `process_form`
// shape-pivot must land as a single same-wave sub-batch (frontend row 7 +
// typecheck row 1 + int row 3) — if any one slips, the other two cannot
// validate end-to-end.
//
// What this file covers (per `tests/plan/implementation-slice-s66.md §5.1`):
//   - REPL `(import [m])` immediately followed by `(macro-from-m ...)` —
//     the typed `ExpansionError::Gap(ResolutionGap::MacroInMem(fq))` retry
//     completes in a single REPL eval. Today the orchestrator's retry
//     dispatch is ad-hoc string parsing on stringly-typed errors.
//   - Forward-reference within REPL transcript (`(defn f [] (g 1))` then
//     `(defn g [x] x)`) — the typed
//     `CheckError::Gap(ResolutionGap::SymbolTypechecked(fq))` path completes.
//   - Negative: when `wait_for_typecheck_symbol` returns a *function* (not
//     a macro), the orchestrator must NOT speculatively JIT it. Verified
//     via `CRANELISP_GOT_TRACE=1` showing no `JitWrite` event from the
//     speculative path.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// =============================================================================
// FIXME 0098 — process_form gap-orchestration retry loop, typed errors
// =============================================================================

// spec: spec/08-modules.md §"REPL form sequencing"
// FIXME(/dev frontend Phase 2 + /dev int Phase 4 of FIXME 0098) — fails
// until `expand` migrates to `cranelisp-frontend` and emits typed
// `ExpansionError::Gap(ResolutionGap::MacroInMem(fq))` AND `process_form`
// pattern-matches on the typed contract.
#[test]
fn process_form_dispatch_macro_after_import_succeeds_in_one_eval() {
    // Two-module setup: helper module exports a macro; user imports it
    // and immediately uses it. Pre-fix, the orchestrator's stringly-typed
    // retry path may double-evaluate or fail to discover the macro on
    // the first eval; post-fix the typed Gap returns from frontend's
    // expand and the retry completes inside the same REPL eval.
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::None)
        .file(
            "helper.cl",
            "(mod helper)\n\
             (export [my-double])\n\
             (defmacro my-double [x] `(add-i64 ~x ~x))\n",
        )
        .stdin(
            "(import [primitives [*]])\n\
             (import [helper [my-double]])\n\
             (my-double 21)\n",
        )
        .output();
    // Expectation: 21 + 21 = 42 surfaces in stdout; no error reported.
    out.assert_stderr_empty()
        .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/08-modules.md §"REPL form sequencing"
// FIXME(/dev typecheck Phase 3 + /dev int Phase 4 of FIXME 0098) — fails
// until `check_form` shape-pivots to `Result<CheckResult, CheckError>` and
// emits `CheckError::Gap(ResolutionGap::SymbolTypechecked(fq))` on
// forward-reference, which int's process_form orchestrator retries after
// `wait_for_typecheck_symbol`.
#[test]
fn process_form_dispatch_typecheck_gap_completes_in_one_eval() {
    // Forward reference pattern: f references g before g is defined.
    // Today this either rejects or relies on a multi-pass; post-fix the
    // typed Gap completes the retry inside the orchestrator. The asserted
    // outcome is that BOTH defns end up in the user module, observable
    // via `/list`.
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(defn f [] (g 1))\n\
             (defn g [x] x)\n\
             (f)\n\
             /list\n",
        )
        .output();
    // Both defns must be present; (f) must evaluate to 1.
    out.assert_stdout_contains(":primitives/Int 1")
        .assert_stdout_contains_all(&["f", "g"]);
}

// spec: spec/12-runtime.md §"Diagnostic logging" (CRANELISP_GOT_TRACE
// reservation) + facade-level invariant per
// `tests/plan/implementation-slice-s66.md §5.1`.
// FIXME(/dev int Phase 4 of FIXME 0098 + /dev backend Phase 1 of FIXME 0099)
// — fails until backend's `register_got_observer` exists AND int's
// orchestrator dispatches macro vs. fn after wait_for_typecheck_symbol
// without speculatively JIT'ing functions.
#[test]
fn process_form_dispatch_function_gap_does_not_speculatively_jit() {
    // Define a function (g) AFTER referencing it; the typecheck-gap retry
    // path resolves to a *function* (not a macro). The orchestrator must
    // NOT speculatively JIT g — JIT must wait for an actual call.
    // Observability: with CRANELISP_GOT_TRACE=1, no `JitWrite` event for
    // `g` should fire from the orchestrator's speculative path.
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .env("CRANELISP_GOT_TRACE", "1")
        .stdin(
            "(defn f [] (g 1))\n\
             (defn g [x] x)\n",
        )
        .output();
    // Negative assertion: no `JitWrite` for `g` should appear in the
    // got-trace stderr after typecheck-gap retry, only after actual call.
    // This is a structural assertion; the trace itself must exist (else
    // it cannot prove zero speculative writes).
    assert!(
        out.stderr.contains("got_trace") || out.stderr.contains("JitWrite") || out.stderr.contains("LinkerWrite") || out.stderr.contains("[GOT"),
        "expected CRANELISP_GOT_TRACE=1 to produce got_trace stderr lines (per FIXME 0099); \
         got stderr:\n{}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("JitWrite g") && !out.stderr.contains("JitWrite user/g"),
        "orchestrator MUST NOT speculatively JIT a typecheck-gap-resolved function; \
         got stderr:\n{}",
        out.stderr
    );
}
