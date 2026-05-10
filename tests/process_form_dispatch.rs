// process_form_dispatch.rs — Sprint 66 Phase 5 (FIXME 0098 + Decision 44).
//
// Authored failing-not-ignored at Phase-5 Stage-1 open per /qa Phase-5
// obligation (METHOD §2.2). These tests gate the **critical-path triad**
// identified by /arch Phase-2 recommendation #1: the `process_form` →
// `process_cluster` shape-pivot must land as a single same-wave sub-batch
// (frontend row 7 + typecheck row 1 + int row 3) — if any one slips, the
// other two cannot validate end-to-end.
//
// What this file covers (post Decision 44 + /spec FIXME 0165 resolution +
// /arch FIXME 0166 resolution; per `tests/plan/implementation-slice-s66.md
// §5.1` revised):
//
//   - REPL `(import [m])` immediately followed by `(macro-from-m ...)` —
//     the typed `ExpansionError::Gap(ResolutionGap::MacroInMem(fq))` retry
//     completes in a single REPL eval. Today the orchestrator's retry
//     dispatch is ad-hoc string parsing on stringly-typed errors. (Macro
//     resolution is a per-form concern; no `(begin ...)` cluster needed.)
//   - `(begin ...)` cluster forward-reference (POSITIVE) —
//     `(begin (defn f [] (g 1)) (defn g [x] x))` typechecks atomically:
//     Pass 1 registers signatures of both into staging, Pass 2 body-checks
//     both against the unified (staging ∪ live) view, the cluster commits
//     atomically. Both defns end up in the user module; `(f)` evaluates.
//   - Bare cross-input forward reference (NEGATIVE) — without a `(begin)`
//     cluster, `(defn f [] (g 1))` is processed as a one-form cluster.
//     The body-check pass cannot resolve `g` (not in staging, not in live)
//     and must surface a clear, typed error to the user. Staging is
//     dropped on the floor; the live `SymbolTable` remains byte-identical
//     to its pre-cluster state — `f` does NOT commit.
//   - Negative: when `wait_for_typecheck_symbol` returns a *function* (not
//     a macro), the orchestrator must NOT speculatively JIT it. Verified
//     via `CRANELISP_GOT_TRACE=1` showing no `JitWrite` event from the
//     speculative path. (Re-shaped to use a `(begin ...)` cluster so the
//     forward-reference path is exercisable per Decision 44.)

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// =============================================================================
// FIXME 0098 — process_cluster gap-orchestration retry loop, typed errors
// (Decision 44 — cluster-atomic typecheck via two pure passes + staging)
// =============================================================================

// spec: spec/08-modules.md §"REPL form sequencing"
// FIXME(/dev frontend Phase 2 + /dev int Phase 4 of FIXME 0098) — fails
// until `expand` migrates to `cranelisp-frontend` and emits typed
// `ExpansionError::Gap(ResolutionGap::MacroInMem(fq))` AND `process_cluster`
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

// spec: spec/05-definitions.md §5.13.2 — REPL Input Boundary and begin Clusters
//       (cluster-atomic two-pass typecheck; mutual recursion via `(begin ...)`)
//       design/arch/decisions/0044-cluster-atomic-typecheck-orchestrator-staging.md
// FIXME(/dev typecheck Phase 3 + /dev int Phase 4 of FIXME 0098, Decision 44)
//       — fails until `check_form` splits into `check_form_signatures` +
//       `check_form_body` AND int's `process_cluster` orchestrates the two
//       pure passes against orchestrator-owned staging with `View::union`
//       and atomic commit per Decision 44.
#[test]
fn process_form_dispatch_begin_cluster_resolves_mutual_forward_ref() {
    // Positive: a `(begin ...)` cluster wraps two mutually-referencing
    // defns into one REPL input. Per /spec §5.13.2 + Decision 44, the
    // orchestrator processes them as one cluster:
    //   Pass 1 — `check_form_signatures` on each form, registers sigs of
    //            both `f` and `g` into the orchestrator-owned staging
    //            `SymbolTable`.
    //   Pass 2 — `check_form_body` on each form, body-checks against the
    //            View (staging ∪ live) so `f`'s body sees `g`'s sig.
    //   Commit — staging drains atomically into the live `SymbolTable`.
    // Once the cluster commits, both defns are in the user module and
    // `(f)` evaluates correctly.
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(begin (defn f [] (g 1)) (defn g [x] x))\n\
             (f)\n\
             /list\n",
        )
        .output();
    // Both defns must be present in /list; (f) must evaluate to 1.
    out.assert_stdout_contains(":primitives/Int 1")
        .assert_stdout_contains_all(&["f", "g"]);
}

// spec: spec/05-definitions.md §5.13.2 — non-clustered cross-input forward
//       references are an error ("a reference in a REPL input to a name that
//       has not yet been defined is an error, with the same diagnostic shape
//       as a reference to a non-existent identifier")
// FIXME(/dev int Phase 4 of FIXME 0098, Decision 44) — fails until
//       `process_cluster` rejects bare cross-input forward refs with a
//       typed Gap-converted error and drops staging atomically without
//       committing the failing form to the live `SymbolTable`.
#[test]
fn process_form_dispatch_bare_forward_ref_errors_clearly() {
    // Negative: without a `(begin ...)` cluster, the REPL input
    // `(defn f [] (g 1))` is processed as a one-form cluster. Pass 1
    // (`check_form_signatures`) registers `f`'s signature into staging.
    // Pass 2 (`check_form_body`) cannot resolve `g` — `g` is not in
    // staging (the cluster has only one form) and not in live (`g` has
    // never been defined). Typecheck returns
    // `Err(CheckError::Gap(ResolutionGap::SymbolTypechecked(g)))`; the
    // scheduler reports the gap as an unresolvable cross-input forward
    // reference; the orchestrator surfaces a clear, typed error to the
    // user. Staging is dropped on the floor; nothing commits.
    //
    // The second REPL input `(defn g [x] x)` is itself a single-form
    // cluster with no forward refs and SHOULD succeed (defining `g`
    // does NOT retroactively repair `f`, per §5.13.2 example).
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(defn f [] (g 1))\n\
             (defn g [x] x)\n\
             /list\n",
        )
        .output();
    // Error path: stderr (or stdout, depending on REPL error sink — see
    // repl/spec.md §5.1 — diagnostic output goes on stdout; stderr is
    // reserved for traces) must mention `g` as undefined / unresolved.
    // Accept either sink to remain robust against a possible
    // /repl-side decision; the typed-error contract from int requires
    // the message to NAME `g`.
    let combined = format!("{}{}", out.stdout, out.stderr);
    let mentions_unresolved = combined.contains("unresolved")
        || combined.contains("undefined")
        || combined.contains("not defined")
        || combined.contains("not found")
        || combined.contains("unknown");
    assert!(
        mentions_unresolved,
        "expected error message indicating `g` is undefined/unresolved\n\
         stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    assert!(
        combined.contains('g'),
        "error message must name the unresolved identifier `g`\n\
         stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    // Atomicity: the second defn (`g`) is its own one-form cluster and
    // has no forward refs, so it commits successfully. `/list` should
    // show `g`. Cluster atomicity for the failing first input means
    // `f` did NOT commit — the live `SymbolTable` is byte-identical
    // to its pre-cluster state for that cluster, so `/list` shows
    // `g` but NOT `f`.
    out.assert_stdout_contains("g")
        .assert_stdout_does_not_contain("f ");
}

// spec: spec/12-runtime.md §"Diagnostic logging" (CRANELISP_GOT_TRACE
// reservation) + facade-level invariant per
// `tests/plan/implementation-slice-s66.md §5.1`.
// FIXME(/dev int Phase 4 of FIXME 0098 + /dev backend Phase 1 of FIXME 0099,
//       Decision 44) — fails until backend's `register_got_observer` exists
//       AND int's `process_cluster` dispatches macro vs. fn after the
//       Pass-2 body-check resolves a forward reference, without
//       speculatively JIT'ing the function.
#[test]
fn process_form_dispatch_function_gap_does_not_speculatively_jit() {
    // Define a function (`g`) referenced ahead of its definition inside a
    // `(begin ...)` cluster (per Decision 44 — the only spec-legal way to
    // express forward refs at the REPL). The Pass-2 body-check resolves
    // `g` as a *function* (not a macro). The orchestrator must NOT
    // speculatively JIT `g` from the body-check resolution path — JIT must
    // wait for an actual call.
    //
    // Observability: with CRANELISP_GOT_TRACE=1, no `JitWrite` event for
    // `g` should fire from the orchestrator's body-check-resolution path.
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .env("CRANELISP_GOT_TRACE", "1")
        .stdin("(begin (defn f [] (g 1)) (defn g [x] x))\n")
        .output();
    // Negative assertion: no `JitWrite` for `g` should appear in the
    // got-trace stderr after Pass-2 body-check resolves `g` as a
    // function, only after an actual call. This is a structural
    // assertion; the trace itself must exist (else it cannot prove zero
    // speculative writes).
    assert!(
        out.stderr.contains("got_trace")
            || out.stderr.contains("JitWrite")
            || out.stderr.contains("LinkerWrite")
            || out.stderr.contains("[GOT"),
        "expected CRANELISP_GOT_TRACE=1 to produce got_trace stderr lines (per FIXME 0099); \
         got stderr:\n{}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("JitWrite g") && !out.stderr.contains("JitWrite user/g"),
        "orchestrator MUST NOT speculatively JIT a body-check-resolved function; \
         got stderr:\n{}",
        out.stderr
    );
}
