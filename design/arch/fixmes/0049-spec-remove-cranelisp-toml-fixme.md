---
number: 0049
target: /spec
filed_by: /int
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/int/cranelisp-toml.md:222, spec/08-modules.md §8.11.4
status: open
migrated_from_inline: true
---

# 0049 — Remove `FIXME(/int)` at `spec/08-modules.md §8.11.4` and update annotation

## Issue

Per `design/int/cranelisp-toml.md §10 Next Skills`: `/spec` should remove the `FIXME(/int)` at `spec/08-modules.md §8.11.4` and update the annotation to drop "NOT YET IMPLEMENTED". The `Cranelisp.toml` lib_dirs feature has shipped (Sprint 58 Step 5d (iii)).

## Source location

`design/int/cranelisp-toml.md:222` (item in §10 Next Skills).

## Context

`design/int/cranelisp-toml.md §1` (intro paragraph) closes the inline FIXME(/int) at `spec/08-modules.md:639,648`. The spec annotation update is the remaining `/spec` work to reflect that the project-config file feature has landed.

## Proposed resolution

`/spec` edits `spec/08-modules.md §8.11.4` to drop the inline FIXME(/int) and the "NOT YET IMPLEMENTED" annotation; replaces with a `[Tested ...]` annotation citing the relevant integration tests.
