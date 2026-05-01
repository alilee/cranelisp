---
number: 0016
target: /int
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint23.rs:1304, design/int/session-persistence.md, repl/spec.md §15.2
status: open
migrated_from_inline: true
---

# 0016 — Persisted import not restored on second REPL session

## Issue

Sprint 58 Wave 2c — second REPL session does not see the persisted import (the helper module is not loaded on session 2 startup even though `user.cl` was regenerated with the import statement). The `tests/cache.rs` migration to the new API (Decision 33+34) does not affect this — the defect is in `/int`'s session restart / persisted-`user.cl` reload flow.

## Source location

`tests/sprint23.rs:1304` (FIXME at `persist_import_survives_restart`).

## Context

User imports a module, quits, restarts; the imported symbol is not visible in session 2. `user.cl` regeneration writes the import statement, but reload on startup does not effect the import. Same family of defect as the dual-path persistence collapse class (see also FIXME 0017 / `design/int/dual-path-persistence-collapse.md`).

## Proposed resolution

`/int` reviews session restart in `src/session_v4.rs` against `repl/spec.md §15.2` and ensures the regenerated `user.cl` is replayed (or its import effects re-applied) at session 2 startup.
