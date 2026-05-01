---
number: 0056
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint60_reduction.rs:204
status: open
migrated_from_inline: true
split_from_cluster: 0022
---

# 0056 — S60 reduction 2.1: Cell ADT not load-bearing

## Issue

S60 reduction 2.1. Cell ADT not load-bearing.

## Test name

`s60_cache_reuse_no_cell_adt_no_crash`

## Test purpose

Step 2.1 — remove the Cell ADT and push raw Ints into the Vec. Establishes that the multi-variant Cell ADT is not required for the cache-hit crash; the same shape still segfaults without it.

## Source location

`tests/sprint60_reduction.rs:204`

## Cluster context

This entry was split from cluster 0022 (S60 Round 1 cache-hit / JIT-object convergence reduction series). Sibling entries: 0055, 0057–0062.

## Proposed resolution

`/backend` (with `/int` collaboration on `restore_cached_module`) audits the cache-hit code-population path against the minimal repro. See `/arch`'s Phase 3a answer in `design/backend/jit-object-convergence.md §4.3` for the recommended fix shape.
