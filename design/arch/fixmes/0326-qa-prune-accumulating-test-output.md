---
number: 0326
target: /qa
filed_by: /sprint
filed_at: 2026-06-13
sprint_filed: 81
refers_to: tests/helpers/e2e.rs, tests/plan/e2e-architecture.md, .config/nextest.toml, tests/scripts/build-link-prereqs.sh
status: open
---

# Test runs continually accumulate output that is never pruned

## Issue (user-directed, 2026-06-13)

Repeated test runs continually accumulate artifacts on disk that are never
pruned. The e2e suite spins up per-test temp directories, compiles modules,
writes `.o`/cache/metadata files, builds platform cdylibs, and produces
standalone `--link` executables — and across many runs this output piles up
rather than being cleaned. The accumulation is unbounded: nothing in the
harness or the run lifecycle reclaims it, so a developer's working tree (and
any CI cache) grows without limit run-over-run.

This is a hygiene defect, not a correctness one — but it works against the
"clean & green" standard: stale accumulated artifacts are exactly the kind of
inconsistent-build hazard that produced S80's two `--link` misdiagnoses
(artifact ABSENCE vs presence skewing results), and a tree that grows every
run masks reproducibility problems.

## Proposed resolution

`/qa` (owner of the e2e harness + `tests/plan/`) decides and implements the
pruning discipline. Candidate mechanisms:

- **Per-test cleanup** — ensure every test's temp dir / cache dir is reclaimed
  on completion (RAII guard / `TempDir` drop), including on the failure path.
  Audit the harness for tests that opt out of cleanup to inspect artifacts.
- **Run-scoped reclamation** — a pre/post step (nextest setup/teardown, or a
  justfile recipe) that prunes a known scratch root before/after the suite,
  alongside the existing `build-link-prereqs.sh` setup script.
- **Bounded scratch root** — confine all test output under one well-known
  directory (e.g. `target/test-scratch/`) so it is trivially `clean`-able and
  `.gitignore`d, rather than scattered tmpdirs that escape cleanup.

Identify WHERE the accumulation lands (tmpdir leakage, a persistent cache dir,
`target/debug` cdylib/exe bloat, etc.), then pick the smallest mechanism that
keeps the tree flat run-over-run. Document the chosen discipline in
`tests/plan/e2e-architecture.md` (the coverage/infra contract).

## Operational implication / Context

NOT blocking — the suite is green; this is accumulating cruft, not a failure.
Filed during S81 ("clean & green" consolidation) Phase-1 scoping per the
user's directive that test output "needs to be continually pruned." Candidate
S81 work if it fits the consolidation theme; otherwise carry forward. No test
is red on it.
