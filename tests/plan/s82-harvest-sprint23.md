# S82 harvest disposition — tests/legacy/sprint23.rs

- **File:** `tests/legacy/sprint23.rs`
- **LOC:** 2759
- **Tests:** 61 `#[test]` fns
- **Owning crate:** `src/`
- **FIXME:** 0144
- **Prior audit:** none

## Disposition

Sprint 23 delivered `--link` executable generation, `/sh` shell escape,
file-watching, session persistence, cache integration, batch-mode, and
the H5/Heisenbug race gates. 57 of 61 are COVERED by the active suite
(`tests/link.rs`, `tests/repl_shell.rs`, `tests/repl_watch.rs`,
`tests/repl_persist.rs`, `tests/cache.rs`, `tests/repl_persist_race.rs`)
— mostly verbatim carry-forwards (renamed). The file's own header lists
the carry-forward map, which the audit verified.

| Feature | Tests | COVERED | GAP |
|---|---:|---:|---:|
| `--link` executable | 11 | 11 (`tests/link.rs`) | 0 |
| `/sh` shell escape | 11 | 11 (`tests/repl_shell.rs`) | 0 |
| file watching | 13 | 12 (`tests/repl_watch.rs`) | 1 |
| session persistence | 15 | 15 (`tests/repl_persist.rs`) | 0 |
| cache integration | 5 | 5 (`tests/cache.rs` + `repl_persist.rs`) | 0 |
| batch mode (`--run`) | 3 | 0 | 3 |
| H5 / Heisenbug gates | 3 | 3 (`tests/repl_persist_race.rs`) | 0 |

**GAP (4):**
- `watch_unchanged_modules_keep_cache` — cache-manifest API direct test (hash_source / check_manifest / write_manifest); → `tests/cache.rs` (or backend cache unit). repl/spec.md §14.7.
- `batch_main_missing_produces_error`, `batch_main_int_exit_code`, `batch_main_nonzero_exit_code` — `--run` main-validation/exit-code (implicit in `--link` tests but no dedicated `--run` e2e) → `tests/build_confidence.rs`. repl/spec.md §0.2.

REGRESSION-GUARD among COVERED (3, already active): `heisenbug_race_reduced_concurrent_import_pairs`, `h5_gate_typechecking_user_fires_only_on_repl_thread`, `h5_normal_completion_does_not_starve_repl_eval_thread` (all in `tests/repl_persist_race.rs`).

## Summary

**61 tests: 57 covered / 4 gap / 0 obsolete**

REGRESSION-GUARD among GAP: 0 (3 reg-guards are in the COVERED set).

## Exit checklist
- [x] (a) dispositioned; [ ] (b) GAP harvested (Wave 2); [ ] (c) deleted; [ ] (d) README row; [ ] (e) FIXME 0144 closed
