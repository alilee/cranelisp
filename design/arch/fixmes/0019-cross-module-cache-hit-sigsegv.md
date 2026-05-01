---
number: 0019
target: /int
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/cache.rs:1307, tests/v4_pipeline.rs:587
status: open
migrated_from_inline: true
---

# 0019 — Cross-module cache-hit second-build SIGSEGV cluster

## Issue

The second-build cache-hit path for cross-module projects SIGSEGVs in the JIT (Sprint 58 Wave 2c diagnostic). After the Wave 2c migration of `tests/cache.rs` to the `cache::write_meta` / `cache::load_meta` API (Decision 33+34), the following cluster still fails:

- `tests/cache.rs::cache_multi_module_hit_cross_module_call` (SIGSEGV)
- `tests/cache.rs::cache_multi_module_multiple_imports` (SIGSEGV)
- `tests/v4_pipeline.rs::v4_cache_hit_dependency` — second `--run` invocation produces a different exit code (`None` vs `Some(77)`)

Same root cause family in `/int`'s cache-hit re-derive flow.

## Source location

`tests/cache.rs:1307` (FIXME at the multi-module cache-hit cluster) and `tests/v4_pipeline.rs:587` (FIXME at `v4_cache_hit_dependency`).

## Context

These tests exercise the full cache-hit path with cross-module function calls. The first build succeeds; the second build (cache-hit) crashes during JIT setup. Hypothesis aligns with the `__cranelisp_got_M` / cache-restore symbol-table-merge concerns documented in `design/backend/jit-object-convergence.md §4.3` (see `/arch` answer at lines 551–553 of that doc).

## Proposed resolution

`/int` audits `try_cache_hit_load` in `src/worker.rs` and the `restore_cached_module` path; merge slot layout into the preserved `Arc<GotTable>` rather than swapping the Arc, or propagate the preserved Arc onto the newly-installed SymbolTable per `/arch`'s Phase 3a answer.
