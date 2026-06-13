---
number: 0117
target: /qa
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/legacy/wave2_g6.rs
status: open
---

> **S81 W-C (backend-half resolved → RE-TARGET /qa for file deletion):** Both
> halves of the harvest are now landed. The backend-internal assertion — the
> finalized native-code pointer written into the entry's GOT slot after
> `compile_to_module` (the backend-observable half of the legacy
> `g6_code_on_entry_after_compile` `code.is_some()` check) — is covered by the
> existing backend unit test
> `crates/cranelisp-backend/src/lib.rs::tests::sprint56_compile_to_module_direct_call_writes_got_and_artifacts`
> (asserts `!guard.got.load_slot(slot).is_null()` for a
> `Def { ast: Some(_), got_slot: Some(_) }`), plus `capture_clif_gates_clif_ir_text`.
> The remaining legacy assertions are NOT backend-crate-internal and have no
> portable unit home:
> - `g6_clif_introspection_reads_from_symbol_table` /
>   `g6_source_introspection_reads_from_symbol_table` — read `SharedState.introspection`
>   via `ReplSession`; introspection is REPL-only (D1b) + 0109-blocked.
> - `g6_codegen_product_regression_guard` / `g6_check_result_slim_shape` —
>   filesystem/type-level grep guards over `src/` and `cranelisp-types`; not
>   backend-internal (the slim-shape guard is the tc-half's
>   `check_result_slim_shape`, landed W-A).
> - `g6_cross_module_call_via_symbol_table` / `g6_repl_expr_uses_compile_to_module_path` /
>   `g6_multi_sig_*` — drive the int worker/session (`batch_run_file`, `repl_eval`,
>   `__expr` registration) end-to-end; their language-observable behaviour is
>   carried e2e in the active `tests/` suite, not backend-internal.
>
> **Disposition: RE-TARGET → /qa.** No remaining backend-internal assertion to
> port. The owed work is purely the legacy-file deletion (`/qa`'s prerogative)
> plus removing its row from `tests/legacy/README.md`.

# Harvest tests/legacy/wave2_g6.rs into cranelisp-typecheck (and -backend) unit tests

## Issue

The Sprint 64 test-port quarantined this file because its assertions
test Rust-internal state with no e2e equivalent: Layer-3 integration
observations of `Code { ptr }` writes onto `ModuleEntry::Def` via the
`CodeFinalizer` trait (Sprint 57 Wave 2 / G6) — exercised through
`ReplSession` / `CompilerSession` Rust API. Per the two-tier strategy
(`memory/project_test_strategy.md`), these belong as
`#[cfg(test)]` unit tests inside the owning crates.

Primary owner: `/typecheck` (the `ModuleEntry::Def` shape and
SymbolTable contract). Secondary participant: `/backend` (the
`CodeFinalizer` write path). The 9 tests should split between the
two crates by which layer the assertion observes.

## Proposed resolution

- Read each of the 9 tests in `tests/legacy/wave2_g6.rs`.
- Translate the SymbolTable / ModuleEntry shape assertions into
  `#[cfg(test)]` modules inside `crates/cranelisp-typecheck/src/`.
- Translate the `CodeFinalizer` write-path assertions into
  `#[cfg(test)]` modules inside `crates/cranelisp-backend/src/`.
- Use cranelisp-frontend's `parse` + `build_program` for AST input
  per `tests/CLAUDE.md §"Isolating Cross-Crate Failures"` — do NOT
  hand-construct AST.
- When complete, delete `tests/legacy/wave2_g6.rs` and remove its
  row from `tests/legacy/README.md`. Git history preserves provenance.

## Operational implication / Context

This harvest is a coverage-preservation commitment from S64. Until
it lands, the assertions are inert (the file is not compiled). The
FIXME blocks no other work — but the longer it sits, the further
the internal surface drifts from the quarantined shape and the more
rewrite the harvest requires.
