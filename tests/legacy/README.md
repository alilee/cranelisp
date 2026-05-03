# tests/legacy/ — Quarantine archive

Source archive of test files moved out of the e2e tier during the
Sprint 64 test-port. Not built by Cargo (nested directory under
`tests/` is not auto-discovered). Each file is awaiting harvest
into the owning crate's `#[cfg(test)]` unit tests.

| File | LOC | Tests | Owning skill | FIXME | Quarantined |
|---|---:|---:|---|---|---|
| `cache.rs` | 2073 | 55 | /backend | 0120 | 2026-05-03 |
| `scheduler.rs` | 571 | 18 | /int | 0116 | 2026-05-03 |
| `wave2_g6.rs` | 370 | 9 | /typecheck | 0117 | 2026-05-03 |
| `wave3_g8.rs` | 557 | 9 | /backend | 0118 | 2026-05-03 |
| `wave4_g9.rs` | 534 | 4 | /int | 0119 | 2026-05-03 |

## Discipline

- Files here are NOT modified after quarantine. They are read-only
  archive until the FIXME is actioned and the file is deleted.
- Each FIXME is filed against the owning crate's `/dev` skill with
  a `harvest:` prefix in the title (e.g.,
  "harvest: tests/legacy/scheduler.rs into src/ (scheduler) unit tests").
- When a file is fully harvested, it is deleted (not blanked) and
  its row removed from this README. Git history preserves
  provenance.
