---
number: 0113
target: /spec
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: spec/03-types.md, spec/05-definitions.md, spec/08-modules.md (and ~50 occurrences across spec/*.md), CLAUDE.md (root, Annotation Convention)
status: open
---

# Retire `R{N}` ring annotations from spec headings

## Issue

User decision (Sprint 64): "All the functionality envisaged by rings has been delivered. We are now testing new features in maintenance/extension mode. Rings are a planning legacy and distraction."

The ring axis is retired from the project's scheduling and traceability vocabulary. Sprint is now the only scheduling axis.

`spec/*.md` files carry ~50 ring annotations in headings of the form `## 8.13 REPL Integration [R4 S10]`, `### 3.2.3 IO Type [R4 S10]`, etc. These should be removed (or the `[R4]` portion stripped, leaving the sprint reference if still meaningful).

Sample occurrences (`grep -rn "\[R[0-9]" spec/` finds them):
- `spec/08-modules.md:415` — `#### Explicit Imports Shadow the Implicit Prelude [R4 S20]`
- `spec/08-modules.md:544` — `[R4 S52]` inline
- `spec/08-modules.md:555` — `### 8.9.3 Platform Modules [R4 S10]`
- `spec/08-modules.md:684` — `## 8.13 REPL Integration [R4 S10]`
- `spec/08-modules.md:726` — `## 8.15 Complete Example [R4 S10]`
- `spec/05-definitions.md:42` — `[R4 S52]` inline
- `spec/05-definitions.md:494` — `## 5.10 Platform Declaration [R4 S10]`
- `spec/03-types.md:20` — `## 3.2 Compound Types [R4 S10]`
- `spec/03-types.md:57` — `### 3.2.3 IO Type [R4 S10]`
- `spec/03-types.md:94` — `### 3.2.5 TestResult Type [R4]`

(Full list discoverable with `grep -rn '\[R[0-9]' spec/`.)

## Proposed resolution

`/spec` decides between:

(a) **Strip `R{N}` portion only**: change `[R4 S10]` → `[S10]`. Preserves the sprint-scheduling annotation.

(b) **Strip the entire bracket**: change `## 5.10 Platform Declaration [R4 S10]` → `## 5.10 Platform Declaration`. The sprint annotation is no longer meaningful for already-delivered functionality.

(c) **Replace with delivery sprint**: change `[R4 S10]` → `[Delivered S10]` or similar. Records the historical fact rather than a forward-looking schedule.

`/qa`'s soft preference: option (b). Most of these annotations refer to features long-delivered; the sprint number was a forecast made in the ring-planning era and is no longer load-bearing. Headings should describe the spec, not historical scheduling artefacts.

If preserving the historical record is important, option (c) is acceptable but adds noise.

## Operational implication / Context

Once `/spec` lands the change, the related root `CLAUDE.md` annotation-convention table update (FIXME 0114) will refer only to `[Tested ...]`/`[S{M}]`/`[S{M} — IGNORED]` — no `[R{N}...]` form. Test plan documents (`tests/plan/PLAN.md`, `tests/CLAUDE.md`) and the `/qa` skill def already updated this sprint.

This is mechanical text-replacement work. ~50 occurrences across ~10 spec files. Single-pass `sed` or grep-then-edit.
