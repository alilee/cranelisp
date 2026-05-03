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
| `repl_experience.rs` | 3120 | 190 | /int (with /typecheck, /backend) | 0124 | 2026-05-03 |
| `repl_negative_old.rs` | 917 | 31 | /int (with /typecheck) | 0124 | 2026-05-03 |
| `ring3_repl.rs` | 825 | 50 | /int (with /typecheck) | 0125 | 2026-05-03 |
| `v4_repl_eval.rs` | 567 | 14 | /int (optional — carry-forward complete) | 0126 | 2026-05-03 |
| `io.rs` | 1360 | 76 | /int (with /typecheck, /backend, /runtime) | 0127 | 2026-05-03 |
| `io_minimal.rs` | 120 | 5 | /int (Sprint 57 W6 reductions; with /backend) | 0127 | 2026-05-03 |
| `sprint61_io_closure_regression.rs` | 215 | 2 | /backend (capture-return-inc; optional) | 0127 | 2026-05-03 |
| `observability_io.rs` | 446 | 7 | /runtime (io_trace internals) | 0128 | 2026-05-03 |

## Discipline

- Files here are NOT modified after quarantine. They are read-only
  archive until the FIXME is actioned and the file is deleted.
- Each FIXME is filed against the owning crate's `/dev` skill with
  a `harvest:` prefix in the title (e.g.,
  "harvest: tests/legacy/scheduler.rs into src/ (scheduler) unit tests").
- When a file is fully harvested, it is deleted (not blanked) and
  its row removed from this README. Git history preserves
  provenance.
