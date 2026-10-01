---
id: ACT-1032
title: Make every e2e test that runs a checked-in program write its module cache into a fresh directory, never into the source tree
status: deferred
priority: advisory
from: qa
to: test
sprint: 122
filed_at: 2026-09-30
refers_to:
  - tests/CLAUDE.md §Fresh temp directory per test
  - tests/concurrency_fanout_web.rs
  - tests/launch_vec_send_corrupt.rs
  - tests/launch_grid_corrupt.rs
  - tests/plan/s122-evidence-delta.md
---

## Request

Remove every write the suite makes under a checked-in path. `tests/CLAUDE.md`
§Fresh temp directory per test forbids it. The writes observed are git-ignored
`.cranelisp-cache/` directories.

## Observation

Verified on 2026-09-30 at `88bbbd12`. The
[clean-cache intake](../../tests/plan/s122-evidence-delta.md#act-1021-amendment--final-intake-2026-09-30)
and the [K4 record](../../tests/plan/s122-evidence-delta.md#final-test-visit-k4--record-and-phase-5-adequacy-2026-09-30)
hold the earlier evidence.

- **Identified writers.** None of the three passes `--no-cache`.
  - `concurrency_fanout_web.rs` sets its working directory to the repository
    root and runs `tests/fixtures/web_fanout/main.cl`.
  - `launch_vec_send_corrupt.rs` runs in
    `tests/fixtures/web_launch_vec_send_corrupt/`.
  - `launch_grid_corrupt.rs` runs in `tests/fixtures/web_grid_corrupt/`.
- **Unidentified writers.** Caches under `examples/` (including
  `16-modules/` and `37-method-import/`) and `exemplar/`.
  - Their timestamps match the checkpoint suite's run at 20:54, as do the
    three fixture caches.
  - Test files that set a working directory and name those trees are
    candidates only, not attributed: `examples.rs`, `exemplar_*.rs` and
    `regression.rs`.
  - A repository-root `.cranelisp-cache/` dated 2026-09-24 has no identified
    writer.
- **Risk.** An in-place run can restore objects compiled by an earlier
  binary. Its result can then describe that binary rather than the source
  under test. `fixture_tree` also copies such a cache into the tests that use
  it. Armed cells, the golden lanes and fresh-tempdir cells are clean by
  construction; K4 relied on purging the caches first.
- **Class.** A maintenance check, not a compiler defect. It blocks no compiler
  acceptance.

## Disposition

Carried to S123 (user, 2026-09-30), approved with the Phase-5 checkpoint
([checkpoint carries](../../tests/plan/s122-evidence-delta.md#phase-5-checkpoint-carries-approved-2026-09-30)).
First deferral.

## Completion evidence

- Each writer is identified. Each then either runs from a fresh per-test
  directory, for example through `fixture_tree`, or passes `--no-cache` where
  the cache is not under test.
- Starting from a tree with the ignored caches purged, one full run leaves no
  `.cranelisp-cache/` under `tests/fixtures/`, `examples/`, `exemplar/` or
  the repository root. Record the listing before and after that run. The
  caches the checkpoint run wrote at 20:54 already show that such a listing
  detects the writes.
- No permanent detector is allocated. Moving each writer to a fresh
  directory removes the fault structurally.
