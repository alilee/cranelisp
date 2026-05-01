---
number: 0057
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint60_reduction.rs:223
status: open
migrated_from_inline: true
split_from_cluster: 0022
---

# 0057 — S60 reduction 2.2: Grid wrapper ADT not load-bearing

## Issue

S60 reduction 2.2. Grid wrapper ADT not load-bearing.

## Test name

`s60_cache_reuse_no_wrapper_adt_no_crash`

## Test purpose

Step 2.2 — remove the Grid wrapper ADT; `make-grid` returns a Vec directly. Establishes that the Grid wrapper is not required for the cache-hit crash.

## Source location

`tests/sprint60_reduction.rs:223`

## Cluster context

This entry was split from cluster 0022 (S60 Round 1 cache-hit / JIT-object convergence reduction series). Sibling entries: 0055–0056, 0058–0062.

## Proposed resolution

`/backend` (with `/int` collaboration on `restore_cached_module`) audits the cache-hit code-population path against the minimal repro. See `/arch`'s Phase 3a answer in `design/backend/jit-object-convergence.md §4.3` for the recommended fix shape.
