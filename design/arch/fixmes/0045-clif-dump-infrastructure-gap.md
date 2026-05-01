---
number: 0045
target: /backend
filed_by: /backend
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/backend/defects-456-reduction.md:155
status: open
migrated_from_inline: true
---

# 0045 — CLIF dump infrastructure gap (`CRANELISP_CODEGEN_TRACE`)

## Issue

`CRANELISP_CODEGEN_TRACE=1` is documented in `tests/CLAUDE.md §"Diagnostic Logging"` as dumping "CLIF IR before/after optimization", but is currently wired only for error paths in `src/worker.rs` and `src/session_v4.rs`, not for normal codegen paths. Sprint 59 Wave 1 defect hunting was forced to use `CRANELISP_RC_TRACE=1` as a proxy because `CODEGEN_TRACE` doesn't dump IR.

The missing infrastructure: add CLIF emission hooks to the per-defn codegen path in `cranelisp-backend` gated on the env var, so small-repro debugging can read compiled IR by eye (per the discipline in root `CLAUDE.md §"Usability Findings and Defects"` paragraph "Keep reductions as small as possible — small tests aid debugging").

## Source location

`design/backend/defects-456-reduction.md:155` (HTML-comment FIXME at the top of §Phase 2).

## Context

The Sprint 60+ defect-hunting work is bottlenecked on the lack of CLIF inspection. The `S60` finding (`CRANELISP_CODEGEN_DUMP=*` precedent) is the partial answer; this FIXME asks for the full env-var hookup matching the documented `CRANELISP_CODEGEN_TRACE` shape.

## Proposed resolution

`/backend` adds CLIF emission hooks to the per-defn codegen path gated on `CRANELISP_CODEGEN_TRACE`. Document the env var alongside the others in `tests/CLAUDE.md §"Diagnostic Logging"`.
