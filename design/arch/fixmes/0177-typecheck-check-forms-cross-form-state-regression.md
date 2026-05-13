---
number: 0177
target: /typecheck
filed_by: /dev (int)
filed_at: 2026-05-13
sprint_filed: 66
refers_to: crates/cranelisp-typecheck/src/form.rs, crates/cranelisp-typecheck/src/program.rs, design/arch/decisions/0044-cluster-atomic-typecheck-orchestrator-staging.md
status: open
---

# `check_forms` regresses cross-form state for constrained polymorphism and macro-clause compilation

## Issue

The Wave 3a-β collapse of the typecheck public surface from the legacy
multi-call shape (`check_form(Register)` + `check_form(CheckBody)` +
`finalize_check_result` + a publicly-threaded `ModuleCheckAccumulator`) onto
the single `check_forms(parsed, &mut ctx, symbol_tables)` call (Decision 44's
2026-05-13 third amendment) regresses ~60 tests in the workspace e2e suite
relative to the pre-Wave-3a baseline.

Pre-S66 failure count: ~33.
Post-int-migration failure count: 93.

Regression clusters:

1. **Constrained polymorphism across separate REPL inputs**.
   Minimal repro at the REPL:
   ```
   (defn id [x] x)        ; first input — registers `id` as
                          ; constrained polymorphic
   (id 7)                 ; second input — wraps as __expr defn,
                          ; check_forms runs over [__expr]
   ```
   The second `check_forms` call reaches `pass4_monomorphise`, attempts
   to monomorphise `(id 7)` to `id$Int`, and stack-overflows on the main
   thread. The pre-S66 path threaded `defn_type_vars` and the
   monomorphisation working set across `check_form` calls via the
   publicly-shared `ModuleCheckAccumulator`; the new single-call shape
   rebuilds that state per call, but the constrained-fn it's monomorphising
   lives in **live** (registered by an earlier `check_forms` call), and the
   monomorphisation re-entry interacts pathologically.

2. **Multi-clause macro compilation through `compile_macro_clause_inline`**.
   Pre-S66, macro-clause defns were appended to the same `ModuleCheckAccumulator`
   as the surrounding module; `finalize_check_result`'s post-passes saw both
   together. The new shape runs `check_forms` per clause with a fresh local
   accumulator, which loses cross-clause + cross-module context. Tests in
   `spec_09_macros` and `spec_11_stdlib` regress here.

## Proposed resolution

Two candidate directions for `/typecheck` to evaluate:

A. **Carry `check_forms`-internal working state across calls inside a
   cluster**. Either: (a) make `check_forms` accept an externally-provided
   `&mut CheckState` (or equivalent persistent state) so consecutive REPL
   inputs in the same module can share `defn_type_vars` / generalisation
   state; or (b) make the per-call state rehydrate fully from the live
   `SymbolTable` on entry — read back already-checked entries' constraints
   etc. into the local accumulator before Pass 4 runs.

B. **Distinguish "register-only" (Pass 1) from "check-body" (Pass 2) at the
   facade** again, but in a way that doesn't expose `ModuleCheckAccumulator`.
   The orchestrator (int) drives Pass 1 across all forms first, then Pass 2,
   threading internal state through an opaque cluster handle (e.g.,
   `ClusterState` lives on `ClusterContext`). This preserves the
   `state-threading hole closure by construction` intent of Decision 44's
   third amendment while restoring cross-form-state preservation.

The choice is `/typecheck`'s — both are facade-compatible with `int`'s
single `process_cluster` entry.

## Operational implication / Context

Wave 3a-β cluster-atomic acceptance landed:

- `process_form_dispatch_begin_cluster_resolves_mutual_forward_ref`: PASS
- `process_form_dispatch_bare_forward_ref_errors_clearly`: PASS (pre-existing)
- `process_form_dispatch_macro_after_import_succeeds_in_one_eval`: FAIL
  (interacts with regression cluster 2 above; also depends on FIXME 0175
  for the deferred macro-invocation path on the frontend side)
- `process_form_dispatch_function_gap_does_not_speculatively_jit`: FAIL
  (depends on FIXME 0099 for backend `register_got_observer`)

The 60-test regression should clear once `/typecheck` resolves the cross-form
state preservation. The int-side scaffold (`worker::check_program_compat`,
`worker::build_program_compat`, the `process_module_forms` flow that calls
`check_forms` once per cluster) is correct against the facade; the bug is
in how `check_forms` handles the per-call state lifecycle when constrained
polymorphism / cross-clause macros span the boundary.

Carries forward into post-Sprint-66 follow-up.
