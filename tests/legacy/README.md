# tests/legacy/ — Quarantine archive (HARVEST COMPLETE)

Source archive of test files moved out of the e2e tier during the
Sprint 64 test-port. Not built by Cargo (nested directory under
`tests/` is not auto-discovered).

> **HARVEST COMPLETE (S82, 2026-06-14).** All 20 quarantined files have
> been harvested into the owning crate's `#[cfg(test)]` unit tests (or
> active e2e tests) and DELETED, and all 12 harvest FIXMEs are closed.
> The quarantine table below is now empty. Git history preserves the
> provenance of every deleted file and its carry-forward record.
>
> The final file harvested was `sprint23.rs` (FIXME 0144): its one
> remaining GAP — `watch_unchanged_modules_keep_cache`, the §14.7 watch
> invariant that an unchanged module keeps its cached `.o` — was ported
> as a backend cache-manifest unit test
> (`crates/cranelisp-backend/src/cache/manifest.rs::
> check_manifest_changed_module_misses_unchanged_sibling_hits`), pinning
> the manifest-level property the watcher relies on.

| File | LOC | Tests | Owning skill | FIXME | Residue (what is NOT yet covered) |
|---|---:|---:|---|---|---|
| _(empty — all harvested)_ | | | | | |

## Discipline (historical)

- Files here were NOT modified after quarantine. They were read-only
  archive until each FIXME was actioned and the file deleted.
- Each FIXME was filed against the owning crate's `/dev` skill with
  a `harvest:` prefix in the title.
- When a file was fully harvested it was deleted (not blanked) and
  its row removed from this README. Git history preserves provenance.
