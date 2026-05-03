---
number: 0120
target: /backend
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/legacy/cache.rs
status: open
---

# Harvest tests/legacy/cache.rs into cranelisp-backend unit tests

## Issue

The Sprint 64 test-port quarantined this file because the bulk of its
assertions test Rust-internal state of `cranelisp_backend::cache::*`
with no e2e equivalent. Specifically:

- 28 tests directly construct `CacheManifest`, `SymbolTable`,
  `ObjectCompileInput`, `CacheWritePacket`, and `IntrinsicTable`,
  exercise their methods (`upsert_module`, `check_manifest`,
  `hash_source`, `process_cache_packet`, `read_manifest`,
  `write_manifest`), and inspect internal fields (manifest
  `compiler_mtime`, `cache_format_version`, `target_triple`,
  `cranelift_version`).
- Several pipeline tests use `cache::load_meta` to inspect the
  on-disk `SymbolTable` (e.g., `cache_load_symbol_table_equivalence`,
  the two `cache_round_trip_observable_equivalence` tests) — the
  runtime-value parity portion of those tests carried forward as
  e2e; the structural-SymbolTable-shape parity stayed.
- `cache_schema_version_mismatch_e2e_falls_through` calls
  `cache::serialize::serialise_meta` to tamper with `schema_version`,
  then asserts `CacheStale::SchemaMismatch` on `cache::load_meta`. The
  same code path is reachable e2e (build, tamper the JSON file,
  rebuild, observe stale-cache fall-through) but the variant-typing
  assertion is internal.

These belong as `#[cfg(test)]` unit tests inside `cranelisp-backend`
adjacent to the cache code under test (per
`memory/project_test_strategy.md` two-tier strategy and
`memory/feedback_unit_tests_with_dev.md`).

The pipeline-shape tests that were e2e-observable
(`cache_single_file_sanity`, `cache_multi_module_*`,
`cache_pipeline_*`, `cache_prelude_*`, `cache_repl_restart_cache_hit`,
`cache_repl_incremental_monomorphisation`,
`cache_quick_build_*`, `cache_invalidation_on_dep_change_e2e`)
carried forward to the new `tests/cache.rs` using `Cranelisp::new()` +
`out.tmp_exists()` + `out.run_again()`.

## Proposed resolution

- Read each test in `tests/legacy/cache.rs`.
- For pure-internal tests (manifest field manipulation, hash equality,
  symbol-table construction): translate into `#[cfg(test)]` modules
  inside `crates/cranelisp-backend/src/cache/` adjacent to the code
  under test. The existing test structure (sections marked by `///
  spec:` comments naming `design/backend/module-caching.md` sections)
  maps directly to per-section unit modules.
- For the `cache_load_symbol_table_equivalence` and
  `cache_round_trip_*_observable_equivalence` structural-parity bits:
  translate into unit tests that use `cranelisp-frontend::parse` +
  `build_program` to drive a real compile through the backend's cache
  write path, then call `cache::load_meta` directly to inspect the
  shape (this part is the unit-tier equivalent of what was done with
  `cached_def_summary` against a real subprocess cache directory).
- When complete, delete `tests/legacy/cache.rs` and remove its row
  from `tests/legacy/README.md`. Git history preserves provenance.

## Operational implication / Context

This harvest is a coverage-preservation commitment from S64. Until it
lands, the assertions are inert (the file is not compiled by Cargo).
The FIXME blocks no other work — but the longer it sits, the further
the post-FIXME-0109 internal surface drifts from the quarantined shape
and the more rewrite the harvest requires.

The runtime-value parity for cache-hit/cache-miss behaviour is fully
covered by the new `tests/cache.rs` e2e suite, so this is genuinely a
preservation-of-detail FIXME, not a coverage gap to be plugged
urgently.
