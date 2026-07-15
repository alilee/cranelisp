---
number: 0605
target: /testing
filed_by: /qa
filed_at: 2026-07-15
sprint_filed: 109
scheduled: S110
refers_to: the CI gate gap that let the 0604 defect ship invisibly — stdlib
  self-tests are not in `cargo nextest`; nothing in the suite imports the
  stdlib module surface, so a compiler regression that breaks stdlib
  compilation/importability has zero signal (27 num.bits self-tests failing,
  no RED). Gate design in tests/plan/s109-attribution-index-feed-race.md §6.
status: open
---

# Stdlib-compile smoke gate: a stdlib-breaking compiler regression must not ship invisibly

## The gap

`tests/` is deliberately stdlib-free (root `CLAUDE.md` §Design Principles,
Stdlib separation — correct, keep it), and the only sanctioned stdlib
touchpoints (`use_workspace_stdlib_for_stdlib_conformance_only()`, in
`repl_persist.rs` + `regression.rs`) import a handful of modules, not the
surface. Result: the S109 index-feed race made `num.bits` unimportable and
blocked all 27 of its self-tests with **zero CI signal**. The separation
principle needs its paired conformance gate on the stdlib side — that is
exactly what the named exception exists for.

## What to build (tier 1, the S110 must-have)

**Stdlib-compile smoke gate**: an e2e test (family) behind
`use_workspace_stdlib_for_stdlib_conformance_only()` that `--run`s a program
importing **every top-level stdlib module**, asserting clean compile + exit 0.

- **Enumerate `stdlib/` at test time** (skip `prelude.cl` and `.test`
  submodules), don't hand-list — new stdlib modules must join the gate
  automatically; a hand-list rots into the same blindness.
- One test per module (nextest process isolation localizes the failing
  module) or one enumerating test with a per-module failure report — 
  `/testing`'s call; the requirement is that the failing MODULE is named.
- Known scope limit, accepted: single-shot, so it reliably catches the
  DETERMINISTIC face of "stdlib unimportable" regressions; the 0604 RACE
  itself is guarded by the ≥25-iteration sweep that lands with the 0604 fix
  (owner `/dev`, see 0604 §Acceptance). This gate's job is the CLASS.

## Follow-on (tier 2, size separately — `/stdlib` + `/testing`)

Stdlib **self-test execution** gate: drive the stdlib's own test runner
(`discover-tests` over the `.test` submodules) as a suite-level job so the
27-self-test class fails loudly. Couples to test-runner maturity; not the
S110 blocker.

## Related infra (not this FIXME's scope, same wave candidate)

`agent_flag_errors_on_non_agent_build` build-interleave race (SPRINT.md
§Findings — nextest setup-script ordering / separate profile fix candidate).
Separate root from 0604; convenient to land in the same `/testing` infra wave.
