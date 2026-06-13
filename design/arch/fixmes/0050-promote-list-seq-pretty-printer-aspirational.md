---
number: 0050
target: /int
filed_by: /repl
filed_at: 2026-05-01
sprint_filed: 64
refers_to: repl/spec.md:319
status: deferred
deferred_at: 2026-06-13
deferred_reason: blocked on display-protocol design (does not yet exist); revisit in the Ring-4 polish sprint that builds the type-directed pretty-printer
target_sprint: TBD
migrated_from_inline: true
---

# 0050 — Promote List/Seq aspirational pretty-printer forms to MUST when protocol exists

## Issue

When the type-directed pretty-printer or display-protocol mechanism is designed (likely in a Ring 4 polish sprint), revisit `repl/spec.md §1.5` and promote the aspirational forms (`(list elem1 elem2 ...)` and `(seq elem1 elem2 ... +more)`) to MUST. Owning skill: `/int` (REPL display layer); coordinate with `/arch` on the protocol design and `/stdlib` on opt-in for List/Seq.

## Source location

`repl/spec.md:319` (HTML-comment FIXME below the §1.5 aspirational paragraph).

## Context

Currently the REPL renders `List` and `Seq` (stdlib types) through the generic ADT recursive formatter. A future revision may introduce a type-directed pretty-printer recognising these types and rendering them in their natural surface form. Until that protocol exists, the generic ADT form is normative.

## Proposed resolution

`/int` (with `/arch` and `/stdlib`) designs the display protocol; once the protocol lands, promote the aspirational forms to MUST in `repl/spec.md §1.5` and remove the FIXME.
