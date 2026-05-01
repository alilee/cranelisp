---
number: 0062
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint60_reduction.rs:321
status: open
migrated_from_inline: true
split_from_cluster: 0022
---

# 0062 — S60 MINIMAL cache-hit segv on two-file no-heap program

## Issue

S60 MINIMAL — cache-hit path segfaults on a two-file, no-heap, no-recursion, no-`let` program. The SOLE load-bearing shape:

  1. Module `grid` defines `build-helper` (no args, returns literal).
  2. Module `grid` defines `make-grid` that calls `build-helper`.
  3. Module `program` imports `make-grid` and calls it from `main`.
  4. Cache-hit second run (first run populated `.cranelisp-cache`).

This is an invariant-layer bug: the JIT/object convergence invariant states that fresh-build and cache-hit paths must produce semantically identical code (design/backend/jit-object-convergence.md §1.1). They manifestly do not — fresh-build runs cleanly; cache-hit segfaults.

Hypothesis (pending CLIF inspection): on cache-hit, `make-grid`'s call to `build-helper` is dispatched through a GOT slot for `grid.build-helper` that is NULL or stale. Reading a NULL function pointer and jumping to it produces a raw SIGSEGV with no stderr output — consistent with the observed signature. The `inline_jit_codegen_for_names` fresh-build path populates the slot before `Code::Jit` is visible; the `load_cached_module_via_linker` cache-hit path may have an ordering gap between slot store and caller visibility — or may write the slot with the linker-loaded pointer for cross-module imports but miss intra-module call targets that the fresh-build path dispatched through call_indirect via the same GOT slot.

(Alternative hypothesis: cache-hit fails to register `grid.build-helper` as a JIT symbol at all because `load_cached_module_via_linker` iterates `cached.symbol_table().all_symbols()` but cross-module GOT population only looks at the IMPORTED subset — intra-module calls within `grid` land on an unpopulated slot.)

Root cause is in `src/worker.rs::load_cached_module_via_linker` vicinity, intersecting with the convergence invariant breach at §4.3 of the design doc (`restore_cached_module`'s wholesale-swap of `symbol_tables[M].got`).

## Test name

`s60_cache_reuse_minimal_5_loc_no_crash`

## Test purpose

Step 2.7 — MINIMAL SHAPE. Drop the `let` binding; main body is just `(make-grid)`. 5 LOC across two files. First run compiles and caches both modules; second run cache-loads both modules and is expected not to SIGSEGV.

## Source location

`tests/sprint60_reduction.rs:321`

## Cluster context

This entry was split from cluster 0022 (S60 Round 1 cache-hit / JIT-object convergence reduction series). Sibling entries: 0055–0061. This is the minimal shape.

## Proposed resolution

`/backend` (with `/int` collaboration on `restore_cached_module`) audits the cache-hit code-population path against the minimal repro. See `/arch`'s Phase 3a answer in `design/backend/jit-object-convergence.md §4.3` for the recommended fix shape.
