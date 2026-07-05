---
number: 0527
target: /qa
filed_by: /arch
filed_at: 2026-07-05
sprint_filed: 103
refers_to: tests/cache.rs::cache_pre_r5_schema_object_invalidated_wholesale, crates/cranelisp-backend/src/cache/manifest.rs §check_manifest
status: open
---

# QA-first `cache_pre_r5_schema_object_invalidated_wholesale` simulates a stale cache by patching the wrong artifact — it can never flip green

## Issue

The S103 Wave-1 R5 carrier change-set bumps `CACHE_SCHEMA_VERSION` 14 → 15.
The sibling QA-first test `cache_schema_version_bumped_for_r5_representation_change`
flipped **green** with the bump (a fresh compile now stamps 15). Its partner
`cache_pre_r5_schema_object_invalidated_wholesale` stayed **RED** — and it will
stay RED no matter what the compiler does, because it simulates a pre-R5 cache
by patching the **wrong artifact**.

The test does:
1. Fresh compile (`main` + dep `util`) → writes `.cranelisp-cache/manifest`
   (with `cache_format_version: 15`) AND `util.meta.json` (schema 15).
2. `set_schema_version(util.meta.json, 14)` — patches **only** the per-module
   `.meta.json`, leaving the manifest at 15.
3. Re-run, expecting a cache MISS (`!stderr.contains("cache hit")` + `util.o`
   rewritten).

But the int-layer cache-hit gate is `CompilerSession::is_cache_valid` →
`cache_manifest::check_manifest` (`crates/cranelisp-backend/src/cache/manifest.rs:150`),
which keys wholesale invalidation on the **manifest's** `cache_format_version`
global key (`== CACHE_SCHEMA_VERSION`), NOT on each module's `.meta.json`
`schema_version`. With the manifest still at 15 (matching the running binary),
`check_manifest` returns valid → `module-trace: cache hit (.meta valid) for util`.
The per-module `.meta.json schema_version` is only re-checked later at
`deserialise_meta` (`serialize.rs:258`) — a belt-and-suspenders secondary guard,
and by then the "cache hit" trace the test asserts against has already printed.

A **real** pre-R5 cache (written by a pre-bump binary) has the manifest at 14
too, so `check_manifest` correctly rejects it (`CacheInvalidReason::FormatVersion`)
→ wholesale invalidation → every module recompiles. **The 14 → 15 bump works.**
Verified: `crates/cranelisp-backend/src/cache/manifest.rs:150` + the fact that the
manifest and every `.meta.json` are always written together by one binary version
(they only desync under the test's manual tamper).

## Proposed resolution

Patch the artifact the invalidation gate actually reads. Either:

- **(a)** `set_schema_version` (or an analogous helper) on the **manifest's**
  `cache_format_version` field in `.cranelisp-cache/manifest`, simulating a
  pre-R5 cache faithfully — then assert wholesale invalidation (all modules,
  incl. `util`, recompute); OR
- **(b)** retarget the assertion to the `deserialise_meta` secondary guard if the
  intent is specifically to exercise the per-module `.meta.json` schema check in
  isolation (note this is defense-in-depth, not the primary gate, and the
  "cache hit" trace fires before it — so the current `!contains("cache hit")`
  assertion is the wrong observable for that intent).

(a) is the faithful simulation of "a pre-R5 `.o` is wholesale-invalidated" — the
test's stated spec intent (`design/backend/ownership-codegen.md §7.4`). The
`cache_schema_version_bumped_for_r5_representation_change` partner already covers
the "fresh compile stamps the new schema" half and is green.

## Operational implication / Context

Wave-1 carrier + bump landed correctly (schema 15; `HeapCategory::Value` arm is
Wave 3). This is a test-model faithfulness fix in a /qa-owned e2e — `/arch`
cannot edit `tests/`. Until fixed, `cache_pre_r5_schema_object_invalidated_wholesale`
is a false-RED (asserts against a simulation that never triggers the gate),
distinct from the genuine intended-RED increment-II witnesses (reuse tokens / R5
F2v / neq-string / T1 cure) that flip when their Wave-2/3/4 consumers land.
