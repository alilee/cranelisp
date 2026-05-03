---
number: 0133
target: /backend
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
refers_to: tests/legacy/v4_jit_reclaim.rs
status: open
---

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
