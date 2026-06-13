---
number: 0118
target: /qa
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/legacy/wave3_g8.rs
status: open
---

> **S81 W-C (backend sweep — RE-TARGET /qa for file deletion):** Reviewed all 9
> tests for backend-crate-internal assertions portable to a `#[cfg(test)]` home
> in `cranelisp-backend`. None qualify:
> - `g8_platform_fn_ptr_on_entry_after_form_handled`, `g8_kept_dlls_retains_handles`,
>   `g8_cross_module_platform_fn_resolution` — observe `SharedState.{symbol_tables,
>   kept_dlls}` + `ModuleEntry::Def.platform_fn_ptr` AFTER the int session handles
>   a `(platform ...)` form. The write site is the int load path, not backend
>   codegen; needs `ReplSession`/`SharedState` (0109-adjacent, not backend-internal).
> - `g8_scheduling_class_read_via_symbol_table` — calls
>   `cranelisp::bind_chain_analysis::scheduling_of`, which lives in the **int crate**
>   (`src/bind_chain_analysis.rs`), NOT `cranelisp-backend`. Not portable to a
>   backend unit test under the narrow-deployment rule.
> - `g8_platform_effect_variant_carries_scheduling_class`,
>   `g8_scheduling_class_moved_to_types_regression_guard` — pure
>   `cranelisp-types` enum-variant destructure / dependency-direction guards; the
>   `PrimitiveKind::PlatformEffect { scheduling_class }` shape is a types-crate
>   contract, owned by `/arch` via `cranelisp-types`, not backend.
> - `g8_platform_registry_regression_guard` — filesystem grep over `src/`
>   (int crate), not backend.
> - `g8_io_trampoline_rc_balanced`, `g8_rc_balance_bind_chain` — RC balance via
>   `cranelisp_runtime::{alloc,dealloc}_count` driven through `session.eval`;
>   runtime-atomics (post-D43 → cranelisp-intrinsics) + int session, not backend.
>
> **Disposition: RE-TARGET → /qa.** No backend-crate-internal assertion to port.
> The owed work is the legacy-file deletion + `tests/legacy/README.md` row removal.

# Harvest tests/legacy/wave3_g8.rs into cranelisp-backend unit tests

## Issue

The Sprint 64 test-port quarantined this file because its assertions
test Rust-internal state with no e2e equivalent: Layer-3 integration
observations of platform-registry removal (Sprint 57 Wave 3 / G8) —
`platform_fn_ptr` and `scheduling_class` directly on
`ModuleEntry::Def`, exercised through `ReplSession` / `CompilerSession`
Rust API. Per the two-tier strategy
(`memory/project_test_strategy.md`), these belong as
`#[cfg(test)]` unit tests inside the owning crate.

## Proposed resolution

- Read each of the 9 tests in `tests/legacy/wave3_g8.rs`.
- Translate into `#[cfg(test)]` modules inside
  `crates/cranelisp-backend/src/` adjacent to the platform-fn-pointer
  write path.
- Use cranelisp-frontend's `parse` + `build_program` for AST input
  per `tests/CLAUDE.md §"Isolating Cross-Crate Failures"` — do NOT
  hand-construct AST.
- When complete, delete `tests/legacy/wave3_g8.rs` and remove its
  row from `tests/legacy/README.md`. Git history preserves provenance.

## Operational implication / Context

This harvest is a coverage-preservation commitment from S64. Until
it lands, the assertions are inert (the file is not compiled). The
FIXME blocks no other work — but the longer it sits, the further
the internal surface drifts from the quarantined shape and the more
rewrite the harvest requires.
