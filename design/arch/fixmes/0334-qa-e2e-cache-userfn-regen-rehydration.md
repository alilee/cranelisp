---
number: 0334
target: /qa
filed_by: /dev int (S81 W-E)
filed_at: 2026-06-13
sprint_filed: 81
refers_to: src/save.rs::rehydrate_userfn_introspection_from_source, src/session_v4.rs::regenerate_backing_file, tests/cache.rs, tests/repl_persist.rs
status: open
---

# e2e: cache-restored UserFn survives REPL-edit `.cl` regeneration (FIXME 0220 fix)

## Issue

FIXME 0220 (resolved this wave by /dev int) closed the gap where a
cache-restored regular `UserFn` with no REPL `Introspection` record was
**silently dropped** from the regenerated backing `.cl` when the user edited
a different symbol in the same module at the REPL. The fix is a lazy
re-read + re-parse of the backing `.cl` in `src/save.rs`
(`rehydrate_userfn_introspection_from_source`), driven from
`session_v4::regenerate_backing_file`.

The fix landed with a **unit test** at the exact seam
(`src/save.rs::tests::rehydrate_recovers_cache_loaded_userfn_dropped_from_regen`).
That pins the rehydration logic, but the bug is also observable **end-to-end**
across the `--run`/cache-hit → REPL-edit → `.cl`-regen boundary, which a unit
test cannot exercise.

## Proposed minimal repro (e2e — /qa to author in tests/, which is /qa-owned)

1. Project with a module defining two functions, e.g. `(defn keep [] 1)` and
   `(defn other [] 2)` in `user.cl` (plus a `main`).
2. First run/REPL session compiles + populates the on-disk cache.
3. A second REPL session loads the module **from cache** (so `keep`/`other`
   have NO introspection record).
4. At the REPL, define a NEW function or redefine one symbol (triggering
   `regenerate_backing_file`).
5. Assert the regenerated `user.cl` STILL contains `(defn keep ...)` and
   `(defn other ...)` — the cache-loaded UserFns must not be dropped.

Without the 0220 fix, step 5 fails (the cache-loaded UserFns vanish from the
regenerated file, breaking a subsequent restart that references them).

`tests/repl_persist.rs` (session persistence across REPL restarts) and
`tests/cache.rs` (cache integration) are the natural homes.

## Context

Unit coverage is in place (mandatory-per-fix discipline satisfied). This FIXME
is the e2e complement — it crosses cache-hit + REPL-edit + file-regen modes,
which is exactly the seam the unit test cannot reach.
