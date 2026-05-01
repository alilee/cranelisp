---
number: 0046
target: /int
filed_by: /backend
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/backend/defects-456-reduction.md:1122, src/session_v4.rs::regenerate_backing_file, design/int/dual-path-persistence-collapse.md
status: open
migrated_from_inline: true
---

# 0046 — `session_v4::regenerate_backing_file` REPL-eval entry-module update site

## Issue

`session_v4::regenerate_backing_file` or the enclosing REPL-eval path is the right site for the Sprint 60 Wave 2 Round 3 `/run-tests` batched defect (FIXME 0020). This belongs to `/int` (session and REPL orchestration), not `/backend` (codegen). The dual-path-persistence collapse doc (`design/int/dual-path-persistence-collapse.md`) already names this class of bug; this is a residual site the Sprint 59 collapse did not cover.

Surprise: the 10 html tests actually pass; the earlier framing as "/run-tests html crashes with SIGSEGV" (Defect 4) was based on stale evidence. The ongoing failure is the REPL-time entry-module update case.

## Source location

`design/backend/defects-456-reduction.md:1122` (FIXME inside §Owning skill).

## Context

Section §Owning skill of `defects-456-reduction.md` documents the routing call. This FIXME pins `/int` as the resolver and names `regenerate_backing_file` as the most likely fix site.

## Proposed resolution

`/int` audits `regenerate_backing_file` against the REPL-time entry-module update path and lands the residual fix. Closes FIXME 0020.
