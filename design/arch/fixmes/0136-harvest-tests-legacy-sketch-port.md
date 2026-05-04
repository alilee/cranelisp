---
number: 0136
target: /qa
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
refers_to: tests/legacy/sketch_port.rs
status: open
---

# Harvest tests/legacy/sketch_port.rs into per-crate unit tests + delete

## Issue

The Sprint 64 Wave 5 test-port quarantined `tests/legacy/sketch_port.rs`
(1886 LOC, 296 tests). The file is the original sketch-prototype test
port — adapted from `sketch/tests/integration.rs`, `sketch/tests/rc.rs`,
`sketch/tests/trace.rs`, `sketch/tests/run_tests.rs`, `sketch/tests/platform.rs`.

The language-conformance subset has been carried forward as REPL-canonical
e2e tests across the 8 spec-section files (`spec_03_*` through
`spec_appendix_a_builtins.rs`). Many sketch_port tests duplicate
ring0/ring1/ring2/e2e coverage that itself was carried forward — the
spec-anchored re-authoring naturally deduplicates.

The legacy file also carries 11 known pre-existing failures in the
sketch-port cluster (referenced as "11 sketch_port" in
`memory/CLAUDE.md`'s old pre-existing-failure count). Those are
captured by the Wave 1 ledger note and the legacy file's
`unwrap_or_else(|e| panic!(...))` shape.

## Proposed resolution

This is a **`/qa`-internal** harvest commitment — most of the sketch-port
content is already covered by:

1. **e2e spec-section files** (Wave 5 — language conformance).
2. **`tests/spec_10_io.rs`** (Wave 3 — IO surface).
3. **`tests/spec_12_runtime.rs`** (Wave 4 — RC + trace + run-tests).

The remaining work is:

- **Audit** `tests/legacy/sketch_port.rs` to identify any spec-anchored
  assertion not yet covered by the carry-forward (likely few — the new
  suite's spec-anchoring is broader than the source-file shape).
- **Distribute** any uncovered assertions into the appropriate
  spec-section file(s) as additional tests.
- **Delete** `tests/legacy/sketch_port.rs` once verified empty of
  spec-relevant uncovered assertions.

If Rust-API observations remain (sketch_port often uses
`compile_and_run_simple()` to assert specific i64 values), file
sub-FIXMEs against `/typecheck`, `/backend`, or `/int` per the assertion
shape — but defer aggressively, since the sketch-port content is
historically the noisiest source of duplicate coverage.

## Operational implication / Context

The 11 pre-existing failures in `sketch_port.rs` remained because the
file's testing approach (assert specific monomorphisation outputs)
exercised compiler corner cases that haven't been fixed. Those defects
are still real; harvesting into the owning crate's unit suite is the
right path so they remain visible during refactor work in S65+.

When complete (or when verified that all spec-anchored coverage is in
the carry-forward set), delete `tests/legacy/sketch_port.rs` and remove
its row from `tests/legacy/README.md`.
