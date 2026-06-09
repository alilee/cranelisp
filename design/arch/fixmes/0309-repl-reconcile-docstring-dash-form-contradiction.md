---
number: 0309
target: /repl
filed_by: /sprint
filed_at: 2026-06-10
sprint_filed: 77
refers_to: repl/spec.md §1.1 (line 165 dash form vs line 167 separate-field), §4.1.7 (lines 758/761/764), spec/appendix-a-builtins.md §A.5
status: open
---

# Reconcile repl/spec.md docstring-suffix contradiction to the dash form

## Issue

`repl/spec.md` is internally inconsistent on the introspection docstring suffix:
- §1.1 line 165: dash form `; {classification} - {docstring}` (matches the
  authoritative spec/appendix-a-builtins.md §A.5).
- §1.1 line 167 + §4.1.7 examples (lines 758/761/764): separate-field form
  `; primitive ; Add`.

S77 W-Repl implemented + tested the dash form (agrees with §A.5 and §1.1 line
165). The §A.5 spec side is already correct; only repl/spec.md's line 167 +
§4.1.7 examples are stale. Surfaced by the W-Repl `/review` gate (Important).

## Proposed resolution

`/repl` reconciles repl/spec.md line 167 + the §4.1.7 examples (758/761/764) to
the dash form `; classification - docstring` to match §1.1 line 165 + spec §A.5.
Doc-only; no code or spec/ change needed.

## Operational implication / Context

Doc consistency; non-blocking. repl/spec.md is /repl-owned.
