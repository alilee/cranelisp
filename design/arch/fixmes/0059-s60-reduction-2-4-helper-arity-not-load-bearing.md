---
number: 0059
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint60_reduction.rs:257
status: open
migrated_from_inline: true
split_from_cluster: 0022
---

# 0059 — S60 reduction 2.4: helper arity not load-bearing

## Issue

S60 reduction 2.4. Helper arity not load-bearing.

## Test name

`s60_cache_reuse_nullary_helper_no_crash`

## Test purpose

Step 2.4 — helper takes NO args and is NOT recursive; pushes a literal. Establishes that helper arity / args are not required for the cache-hit crash.

## Source location

`tests/sprint60_reduction.rs:257`

## Cluster context

This entry was split from cluster 0022 (S60 Round 1 cache-hit / JIT-object convergence reduction series). Sibling entries: 0055–0058, 0060–0062.

## Proposed resolution

`/backend` (with `/int` collaboration on `restore_cached_module`) audits the cache-hit code-population path against the minimal repro. See `/arch`'s Phase 3a answer in `design/backend/jit-object-convergence.md §4.3` for the recommended fix shape.
