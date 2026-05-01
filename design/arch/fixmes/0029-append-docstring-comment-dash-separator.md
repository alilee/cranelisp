---
number: 0029
target: /int
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/wave6_demo_repros.rs:279, src/session_v4.rs::append_docstring_comment, repl/spec.md §1.1
status: open
migrated_from_inline: true
---

# 0029 — Fix `append_docstring_comment` to use ` - ` separator (REPL §1.1)

## Issue

Fix `src/session_v4.rs::append_docstring_comment` format string to use ` - ` instead of ` ; ` between classification and docstring. Spec anchor: `repl/spec.md §1.1` — REPL output format is `:Type {value|name} ; {classification} - {docstring}` and mandates a DASH separator between classification and docstring (e.g. `; defn - Pick first arg`, not `; defn ; Pick first arg`).

## Source location

`tests/wave6_demo_repros.rs:279` (FIXME above the regression repro).

## Context

Sprint 58 Wave 6 `/repl` demo surfaced this as Defect 3. The displayed REPL format used a second semicolon where the spec mandates a dash. Fix lands in the format string.

## Proposed resolution

`/int` edits the format string. Test must pass post-fix.
