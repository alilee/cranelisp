---
number: 0196
target: /design (int)
filed_by: /dev (int)
filed_at: 2026-05-16
sprint_filed: 67
refers_to: design/arch/facades/int.md §"Introspection records" line 388
status: open
---

# `SymbolInfo.category` inline comment lists only 5 variants vs enum's 7

## Issue

`facades/int.md:388` documents `pub category: SymbolCategory` with the inline
comment `// Module | Macro | Trait | Type | Fn` — only 5 variants. The
actual enum declaration two lines below (line 394) lists 7:
`{ Module, Macro, Trait, Type, Fn, SpecialForm, Constructor }`.

Post-Sprint 67 Wave 4 Cluster C2, the int implementation matches the
7-variant enum exactly (`src/session_v4.rs:586-595`). The L388 comment is
the only drift.

## Proposed resolution

Update line 388's inline comment to either:

- `// Module | Macro | Trait | Type | Fn | SpecialForm | Constructor` (full
  list), or
- `// see enum below` (delegating to the type-side enumeration).

The first is more searchable; the second avoids comment-vs-source drift on
future variant additions.

## Operational implication / Context

Cosmetic only — the binding shape and source impl already match. No
behaviour or contract impact. Lands on /design (int)'s next facade-text
sweep.
