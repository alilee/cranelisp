---
number: 0033
target: /typecheck
filed_by: /review
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/typecheck/ast-annotation.md:475, crates/cranelisp-types/src/check.rs:43-50, design/review/sprint57-wave2-review.md I-1
status: open
migrated_from_inline: true
---

# 0033 — `MonoDefn.resolutions` and `MonoDefn.expr_types` are redundant after Phase-1 AST annotation

## Issue

Sprint 57 Wave 2 review I-1: `MonoDefn.resolutions` and `MonoDefn.expr_types` at `crates/cranelisp-types/src/check.rs:43-50` are Span-keyed side maps retained inside typecheck after the Phase-1 AST-annotation migration. No cross-crate consumer reads them post-Wave-2. The `Defn` inside `MonoDefn` is already annotated by `monomorphise_call` in `traits.rs`, so the side maps are redundant — `annotate_defn_from_maps` could read annotations off AST nodes directly. Either drop the fields (making `MonoDefn` a newtype wrapping `Defn`) or document the retention rationale and schedule elimination.

## Source location

`design/typecheck/ast-annotation.md:475` (HTML-comment FIXME). Field definitions in `crates/cranelisp-types/src/check.rs:43-50`. Origin: `design/review/sprint57-wave2-review.md` I-1.

## Context

Section 5 of `ast-annotation.md` covers default-method-defn body checking. The FIXME flags that the Phase-1 AST-annotation migration left `MonoDefn`'s side maps as redundant carry-overs.

## Proposed resolution

`/typecheck` either drops `resolutions` + `expr_types` from `MonoDefn` (making it a `Defn` newtype) or records the retention rationale + schedules elimination in a future sprint.
