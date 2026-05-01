---
number: 0053
target: /arch
filed_by: /review
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/review/ring0-report.md:86 (M-2), crates/cranelisp-types/src/check.rs:60-64, design/arch/interfaces.md:500-513
status: open
migrated_from_inline: true
---

# 0053 — `CheckResult` has two extra fields beyond `interfaces.md` specification

## Issue

The implementation adds `type_defs: HashMap<TypeName, TypeDefInfo>` and `constructor_to_type: HashMap<Symbol, TypeName>` to `CheckResult`. These are needed by the backend for match codegen against ADTs and are correctly used. However, they are not documented in the design book.

Either update `design/arch/interfaces.md` to include these fields, or evaluate and explicitly approve the addition.

## Source location

`design/review/ring0-report.md:86` (Ring 0 M-2 finding).

## Context

Ring 0 review finding M-2. Owner per checklist 7b: `/arch` (interface change requires `/arch` review).

## Proposed resolution

`/arch` updates `design/arch/interfaces.md` (or its successor reference, post-S63 reorganisation) to document the two `CheckResult` fields with rationale (backend ADT codegen need).
