---
number: 0048
target: /arch
filed_by: /int
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/int/session-persistence.md:383, design/arch/interfaces.md, design/typecheck/traitimpl-symbol-table.md
status: open
migrated_from_inline: true
---

# 0048 — Add `ModuleEntry::TraitImpl` variant to `interfaces.md`

## Issue

Update `design/arch/interfaces.md` to add the `TraitImpl` variant on `ModuleEntry` (with `sexp: Option<Sexp>` field) per the `traitimpl-symbol-table.md` design.

## Source location

`design/int/session-persistence.md:383` (item 3 of §"Pending boundary changes").

## Context

Session persistence requires `ModuleEntry::TraitImpl` entries to round-trip through `serde`. The variant is specified in `traitimpl-symbol-table.md` but not yet reflected in the boundary contract `interfaces.md`.

## Proposed resolution

`/arch` updates `design/arch/interfaces.md` to include the `TraitImpl` variant with the documented field shape. Coordinate with `/typecheck` on the `sexp` field's serialisation discipline.
