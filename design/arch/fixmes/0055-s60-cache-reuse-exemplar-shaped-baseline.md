---
number: 0055
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint60_reduction.rs:167
status: open
migrated_from_inline: true
split_from_cluster: 0022
---

# 0055 — S60 Step 1 cache-reuse exemplar-shaped baseline

## Issue

S60 Step 1: commits A.3b's uncommitted finding. First run compiles + caches. Second run crashes on cache-hit load with SIGSEGV. The exemplar-shaped baseline before reduction.

When FIXED: restores the JIT/object convergence invariant (design/backend/jit-object-convergence.md §1.1) for the path that populates `ModuleEntry::Def.code` on cache-hit.

## Test name

`s60_cache_reuse_exemplar_shaped_no_crash`

## Test purpose

Two-file cache reuse over a Grid/Cell exemplar-shaped module pair: first run populates `.cranelisp-cache`; second run cache-loads both modules and is expected not to crash.

## Source location

`tests/sprint60_reduction.rs:167`

## Cluster context

This entry was split from cluster 0022 (S60 Round 1 cache-hit / JIT-object convergence reduction series). Sibling entries: 0056–0062.

## Proposed resolution

`/backend` (with `/int` collaboration on `restore_cached_module`) audits the cache-hit code-population path against the minimal repro. See `/arch`'s Phase 3a answer in `design/backend/jit-object-convergence.md §4.3` for the recommended fix shape.
