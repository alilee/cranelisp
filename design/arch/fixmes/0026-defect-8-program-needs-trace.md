---
number: 0026
target: /int
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_neg.rs:232, design/backend/defect-8-repro-notes.md
status: open
migrated_from_inline: true
---

# 0026 — Widen `program_needs_trace` alongside `program_uses_test_forms`

## Issue

Sprint 59 Workstream B Defect 8 — widen `program_needs_trace` alongside `program_uses_test_forms` in the single commit that resolves Defect 8. Repro notes at `design/backend/defect-8-repro-notes.md`.

Expected behaviour before the fix: `tests/sprint59_neg.rs::defn_body_with_trace_triggers_extern_registration_neg` fails with a Cranelift JIT panic "can't resolve symbol trace" (or similar) at `finalize_definitions`, matching the Defect 8 failure signature transposed to `trace`.

## Source location

`tests/sprint59_neg.rs:232` (FIXME above `defn_body_with_trace_triggers_extern_registration_neg`).

## Context

`program_needs_trace` and `program_uses_test_forms` are predicates in `/int`'s session orchestration that decide whether to register the corresponding extern. The defect: a `defn` body that uses `trace` does not trigger registration, leading to JIT-finalize failure.

## Proposed resolution

`/int` widens `program_needs_trace` to scan `defn` bodies (mirroring whatever `program_uses_test_forms` does for the test forms). Land in a single commit per Defect 8 repro notes.
