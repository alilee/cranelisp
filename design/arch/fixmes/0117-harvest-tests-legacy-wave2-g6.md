---
number: 0117
target: /typecheck
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/legacy/wave2_g6.rs
status: open
---

> **S81 W-A (tc-half harvested):** The typecheck-relevant assertions are
> harvested into `crates/cranelisp-typecheck/src/program/tests.rs`:
> - `def_entry_carries_annotated_ast_after_check` — the Phase-1
>   `ModuleEntry::Def.ast = Some(_)` annotation write (the typecheck half of
>   the legacy `g6_code_on_entry_after_compile`).
> - `check_result_slim_shape` — the `CheckResult { warnings, display }`
>   structural guard (legacy `g6_check_result_slim_shape`).
>
> **Backend-half pending W-C:** the `Code { ptr }` write onto
> `ModuleEntry::Def.code` via the `CodeFinalizer` trait (the `code.is_some()`
> half of `g6_code_on_entry_after_compile`), the `/clif`/`/source`
> introspection read-path guards (`g6_clif_introspection_reads_from_symbol_table`,
> `g6_source_introspection_reads_from_symbol_table`), the `CodegenProduct`
> deletion guard (`g6_codegen_product_regression_guard`), the cross-module
> symbol-table call resolution (`g6_cross_module_call_via_symbol_table`), the
> `__expr`-via-compile_to_module path (`g6_repl_expr_uses_compile_to_module_path`),
> and the multi-sig JIT dispatch regression guards
> (`g6_multi_sig_*`) — all observe backend / int wiring and are harvested in the
> W-C backend sweep. `tests/legacy/wave2_g6.rs` is RETAINED until the
> backend-half lands. FIXME left OPEN.

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
