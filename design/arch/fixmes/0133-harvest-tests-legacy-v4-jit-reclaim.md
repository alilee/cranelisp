---
number: 0133
target: /backend
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
refers_to: tests/legacy/v4_jit_reclaim.rs
status: open
---

> **S81 W-C — backend `Jit::drop` half harvested; intrinsics/0109 remainder
> pending. FIXME stays OPEN.** The backend-side contract — Decision 31 reclaim:
> `Jit::drop` calls `unsafe free_memory()` exactly once, observable via the
> `jit_free_memory_call_count()` counter, and the `Code::Jit`/`Code::Linker`
> `Arc` lifecycle (Scenario 2 per-redefinition reclaim primitive) — is already
> covered backend-internal by existing `#[cfg(test)]` tests:
> - `crates/cranelisp-backend/src/jit.rs::tests::{drop_runs_without_panic,
>   drop_invokes_free_memory, compile_call_drop_roundtrip}` — `Jit::drop` fires
>   the reclaim path; counter increments by exactly 1 (legacy
>   `decision31_scenario2_per_redefinition_jit_pages_reclaimed` /
>   `..._repeated_redefinition_no_unbounded_growth` backend assertion).
> - `crates/cranelisp-backend/src/code.rs::tests::{code_enum_jit_variant_carries_arc_jit,
>   code_enum_linker_variant_constructible}` — the `Arc<Jit>` / `Arc<Linker>`
>   strong-count semantics: clone bumps, drop decrements, last-drop fires
>   `Jit::drop`/`free_memory` (legacy `decision31_code_linker_session_scope_only`
>   = the portable `Code::Linker` Arc-lifecycle test).
>
> **Remainder (NOT W-C, stays OPEN):**
> - The `cranelisp_runtime::{bytes_current, alloc_count, dealloc_count}` atomics
>   half (legacy `decision31_scenario1_*` per-eval reclaim + the `MemSnapshot`
>   byte-delta assertions) moved to **cranelisp-intrinsics** post-D43 — not
>   backend; belongs in an intrinsics `#[cfg(test)]` harvest.
> - The `ReplSession::symbol_tables()` reach-through to `ModuleEntry::Def.code`
>   shape (legacy tests 3 + 6 read `Code::Jit`/`Code::Linker` off a live session)
>   is **0109-blocked** — needs the int session, not portable to backend.
>
> No new backend code this wave (backend half pre-existed). Re-evaluate the
> intrinsics + 0109 remainder when the int/intrinsics harvest wave runs.

# Harvest tests/legacy/v4_jit_reclaim.rs into cranelisp-backend + cranelisp-runtime unit tests

## Issue

The Sprint 64 test-port quarantined `tests/legacy/v4_jit_reclaim.rs` (700
LOC, 6 tests). The file validates Decision 31 Scenarios 1 & 2 — per-eval
and per-redefinition JIT page reclaim — by asserting on:

- `cranelisp_runtime::bytes_current() / alloc_count() / dealloc_count()`
  process-global atomics. The same data the `/mem` slash command reports.
- `cranelisp_backend::jit::jit_free_memory_call_count()` — fires in
  `Jit::drop`.
- `ReplSession::symbol_tables()` → `ModuleEntry::Def.code` shape
  (`Code::Jit` / `Code::Linker`) inspection via internal API reach-through.

The user-visible reclaim contract IS observable through `/mem` (per
`repl/spec.md §3.7` — "live: <bytes> bytes (<live-allocs> allocations)"),
but the precision required by these tests (byte-level deltas across
redefinition cycles, with `REPL_EVAL_OVERHEAD_BOUND` thresholds) is
finer than `/mem` text output supports.

## Proposed resolution

Split by where the contract lives:

- **`cranelisp-backend` `#[cfg(test)]`** — Decision 31 Scenario 2 (per-
  redefinition reclaim) is a backend-side contract: the `Arc<Jit>` on
  `ModuleEntry::Def.code` drops to zero refcount when the def is
  redefined, triggering `Jit::drop` which calls `unsafe free_memory()`
  via the `jit_free_memory_call_count` counter. Translate the redefinition
  + counter-delta tests into unit tests adjacent to `Jit::drop` in
  cranelisp-backend. Use `cranelisp_frontend::parse` + `build_program` +
  `compile_to_module` per-symbol (Decision 41) to drive the codegen
  directly.

- **`cranelisp-runtime` `#[cfg(test)]`** — the `bytes_current` /
  `alloc_count` / `dealloc_count` atomic primitives are runtime-side.
  Their unit-level invariants (counters move monotonically; deltas
  match alloc/free pairs) belong in cranelisp-runtime. The integration
  property "JIT reclaim returns bytes_current to baseline" is the
  backend-side test above; the runtime-side tests are simpler atomicity
  / monotonicity assertions.

- **`/mem`-based smoke (e2e)** — a single `/mem`-output e2e test
  asserting "live bytes do not monotonically increase across N
  redefinitions" would be useful as a release-gate companion. Add it
  to `tests/spec_12_runtime.rs` at harvest time if the `/mem` output
  format is stable enough by then. Until then the e2e suite covers
  reclaim implicitly: long-running examples / exemplar would surface
  unbounded growth as a memory-pressure failure.

Note on test infrastructure: per Decision 41 (amending Decisions 31
and 35), the `Code` enum moves from `src/` (`cranelisp::code::Code`) to
`cranelisp-backend` in S65+. The harvest must update the `use` paths
accordingly.

## Operational implication / Context

This harvest is a coverage-preservation commitment from S64. Until it
lands, the file is inert. The user-visible reclaim contract is preserved
implicitly by the e2e test suite (no test exhibits unbounded memory
growth under repeated redefinition); the precise byte-level assertion
moves to crate-internal unit tests where it belongs.

The 6 tests:

- `decision_31_scenario_1_per_eval_reclaim_repl` — per-eval JIT pages
  reclaimed.
- `decision_31_scenario_2_per_redefinition_reclaim_repl` — per-redefn
  reclaimed.
- `code_linker_session_scope_retention` — `Code::Linker` participates in
  same Arc reclaim.
- (3 supporting tests for snapshot helpers / counter shapes.)

When complete, delete `tests/legacy/v4_jit_reclaim.rs` and remove its
row from `tests/legacy/README.md`. Git history preserves provenance.
