---
number: 0144
target: /int
filed_by: /qa
filed_at: 2026-05-05
sprint_filed: 64
refers_to: tests/legacy/sprint23.rs, tests/link.rs, tests/repl_shell.rs, tests/cache.rs, tests/repl_watch.rs, tests/repl_persist.rs, tests/repl_persist_race.rs, tests/build_confidence.rs
status: open
---

# Harvest tests/legacy/sprint23.rs into /int unit tests + review inline FIXMEs

## Issue

Sprint 64 Wave 6 batch 2 quarantined `tests/sprint23.rs` (61 tests, 2,744 LOC, Sprint 23 work-product covering `--link` + `/sh` + file watching + REPL cache + session persistence + heisenbug). Six new e2e files preserve the load-bearing coverage:

- `tests/link.rs` — Executable Generation cluster (Part A, commit `3b10234`)
- `tests/repl_shell.rs` — `/sh` cluster (Part A)
- `tests/cache.rs` (extended) — `/reset` + cache integration (Part A)
- `tests/repl_watch.rs` — file watching cluster (Part B)
- `tests/repl_persist.rs` — session persistence cluster, including 8 named-defect REGRESSION-GUARDs (Part B)
- `tests/repl_persist_race.rs` — heisenbug + H5 gate cluster, calibration constants preserved (Part B)
- `tests/build_confidence.rs` (extended) — `batch_main_nonzero_exit_code` (#57) (Part B)

Total carry-forward: 58 tests across 7 files (25 Part A + 33 Part B).

The legacy file retains finer-grained Rust-API tests worth preserving as `/int` `#[cfg(test)]` unit tests — notably `watch_unchanged_modules_keep_cache` (mtime test that the e2e tier cannot directly observe).

## Inline FIXMEs preserved in legacy/sprint23.rs

The legacy file preserves 4 inline `FIXME(/int)` markers from prior sprints. Verify each during harvest:

- **Line 343** — Sprint 58 Wave 2c `--link` linker error. **Likely stale**: `tests/link.rs::link_multi_module_project_with_cross_module_call_exits_with_main_value` (Part A) PASSES on current binary, suggesting the underlying defect resolved. Confirm during harvest; delete inline marker if resolved.
- **Line 1304** — Sprint 58 Wave 2c second REPL session not seeing prior persistence state. Verify against `tests/repl_persist.rs` carry-forwards; if the e2e test for "second session loads prior defns" passes, the inline marker is stale.
- **Line 2119** — Sprint 59 Workstream A dual-path persistence collapse. Verify against `tests/repl_persist.rs` carry-forwards.
- **Line 2194** — Sprint 61 Wave 3 step 3e scheduler/worker race fix. The heisenbug carry-forwards in `tests/repl_persist_race.rs` (calibration THREADS=6, ITERS=2, TRIALS=10) all PASS on current binary, suggesting the H5 race fix held.

Each surviving inline FIXME (post-harvest review) should migrate to its own numbered `design/arch/fixmes/NNNN-*.md` per Sprint 63 M7 protocol. If all four prove stale, delete the legacy file outright when harvest completes.

## Proposed resolution

`/int` reviews the quarantined file:

1. For each `#[test]` in `tests/legacy/sprint23.rs`, verify it is e2e-equivalent to a carry-forward (most are). For Rust-API-only tests (e.g., `watch_unchanged_modules_keep_cache`), translate into `#[cfg(test)]` modules inside `src/session_v4.rs`, `src/watch.rs`, or whichever `src/` module owns the surface.
2. For each inline FIXME (lines 343, 1304, 2119, 2194), verify against the corresponding e2e carry-forward. If the e2e test passes, the FIXME is stale — delete from the legacy file. If the FIXME survives review, migrate to its own numbered FIXME file.
3. When all surface is harvested or proven stale, delete `tests/legacy/sprint23.rs`. Git history preserves provenance.

## Operational implication / Context

The largest single quarantine in Wave 5.6/Wave 6 by carry-forward count (58 tests across 7 files). Sprint 23 was a feature-introduction sprint (`--link`, `/sh`, file watching, persistence, REPL cache); none of the surfaces had pre-existing carry-forward in the new e2e suite — hence the 97% GAP-COVER rate the audit identified.

The Part A + Part B authoring exercised every carry-forward against the current binary and all 58 pass green, validating that the implementation behaviours Sprint 23 introduced have held through Sprints 24-64 without regression. Useful signal for `/int`'s future roadmap.
