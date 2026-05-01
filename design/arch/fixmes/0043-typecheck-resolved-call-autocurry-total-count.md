---
number: 0043
target: /typecheck
filed_by: /backend
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/backend/auto-curry-and-run-tests.md:112
status: open
migrated_from_inline: true
---

# 0043 — `ResolvedCall::AutoCurry` is missing `total_count`

## Issue

The reimplementation's `ResolvedCall::AutoCurry` currently has `target_name: Symbol` and `applied_count: usize` but is missing `total_count`. The sketch has `total_count`. The typechecker must provide this. The total arity can alternatively be looked up via `ctx.func_arities[&target_name]` at codegen time, which avoids changing the type.

## Source location

`design/backend/auto-curry-and-run-tests.md:112` (FIXME inside §4 ResolvedCall shape).

## Context

Auto-curry codegen needs the total arity to know how many remaining args the wrapper closure expects. `applied_count` alone is insufficient. Two routes: extend the type (add `total_count`) or look up via `ctx.func_arities` at codegen time.

## Proposed resolution

`/typecheck` either adds `total_count` to `ResolvedCall::AutoCurry` (and threads it through the resolution) or confirms that codegen-time lookup via `ctx.func_arities` is sufficient. Coordinate with `/backend` on the chosen shape.
