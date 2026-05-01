---
number: 0034
target: /int
filed_by: /typecheck
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/typecheck/ast-annotation.md:1270
status: open
migrated_from_inline: true
---

# 0034 — Does the implicit prelude injection appear in `imports`?

## Issue

Open question for `/int` writer: does the implicit prelude injection appear in `SymbolTable.imports`? Two principled answers — (a) yes, with a synthetic `Span` distinguishing it (preserves "imports is the source of every Import entry's reason"); (b) no, the prelude is special-cased and its `ModuleEntry::Import` chains lack a corresponding `ImportSpec` (matches today's behaviour). `/typecheck` does not pre-empt the choice; the resolver's diagnostic quality drives it.

## Source location

`design/typecheck/ast-annotation.md:1270` (item 4 in §11.3 invariants).

## Context

Coherence between the structural `imports: Vec<ImportSpec>` and per-symbol `ModuleEntry::Import { source: FQSymbol }` is one-way: every `ImportSpec` produces `ModuleEntry::Import` entries (or a "name not exported" diagnostic), but the reverse is not required. The implicit prelude injection is the open case.

## Proposed resolution

`/int` decides between (a) synthetic-Span injection or (b) special-cased absence; documents the decision in `crates/cranelisp-types/src/module.rs` doc comments and updates the design doc's open question to a resolved bullet.
