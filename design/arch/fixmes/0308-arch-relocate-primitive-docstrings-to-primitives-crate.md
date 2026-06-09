---
number: 0308
target: /arch
filed_by: /sprint
filed_at: 2026-06-10
sprint_filed: 77
refers_to: src/builtin_docs.rs (parallel docstring table), crates/cranelisp-primitives (PrimitiveDef carries docstring: None), spec/appendix-a-builtins.md §A.3/§A.5
status: open
---

# Relocate primitive Description text into cranelisp-primitives (retire src/builtin_docs.rs)

## Issue

S77 W-Repl (FIXME 0301) added `src/builtin_docs.rs` — a hand-maintained table
of primitive docstrings sourced from spec Appendix A.3 — because
`cranelisp-primitives` registers primitive `Def`s with `docstring: None`. The
REPL display + `/doc` read from this table. It is a pragmatic, correctly-bounded
home for now, but it DUPLICATES the §A.3 Description column with nothing
structurally coupling the two (Principle 7 tension): a new/renamed primitive in
§A.3 silently shows bare `; primitive` until the table is hand-updated.

Surfaced by the W-Repl `/review` gate (Important; non-blocking — the fix shipped).

## Proposed resolution

Evaluate carrying the §A.5 Description text on `cranelisp-primitives::PrimitiveDef`
(the canonical home) so int reads it through the existing `docstring` field,
retiring the parallel `src/builtin_docs.rs` table. Cross-crate (primitives shape
+ int consumer) → /arch-owned; cascade baseline/facade as needed.

## Operational implication / Context

Stage 2 quality item. No behavioural bug today (the table is complete for the
current primitive set + rustdoc-documented maintenance rule); this defends
against §A.3↔table drift.
