---
number: 0015
target: /int
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint23.rs:343, design/backend/executable-generation.md §3
status: open
migrated_from_inline: true
---

# 0015 — `--link` fails to resolve `___cranelisp_got_helper`

## Issue

Sprint 58 Wave 2c — `--link` fails because the linker cannot resolve `___cranelisp_got_helper` (the helper module's per-module GOT base symbol is not exported in the helper.o emitted by the cache writer). The `tests/cache.rs` migration to the new API (Decision 33+34) does not affect this — the defect is in `/int`'s `--link` flow / cross-module GOT export in the cache-write `.o` emission path. See `design/backend/executable-generation.md §3`.

## Source location

`tests/sprint23.rs:343` (FIXME at `link_multi_module_project`).

## Context

The test exercises a project with an entry module that imports another module and calls `--link` to produce a standalone executable. The cache-write `.o` emission for the helper module fails to export the per-module GOT base symbol that the linker needs to resolve cross-module references.

## Proposed resolution

`/int` audits the cache `.o` writer (per `design/backend/executable-generation.md §3`) and ensures the per-module `__cranelisp_got_{M}` symbol is declared with `Linkage::Export` in helper modules' `.o` output, mirroring the entry module's GOT declaration.
