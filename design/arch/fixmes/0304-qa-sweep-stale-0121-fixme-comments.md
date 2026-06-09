---
number: 0304
target: /qa
filed_by: /sprint
filed_at: 2026-06-09
sprint_filed: 77
refers_to: tests/cache.rs (~240-252), tests/spec_08_modules.rs (~9 inline FIXME(/int) comments)
status: open
---

# Sweep stale `FIXME(0121)` / "do not fix in-sprint" comments now that 0121 is resolved

## Issue

Sprint 77 W-Module resolved FIXME 0121 (`--run`/cache `(mod …)` discovery) and
its 11 e2e tests now pass. The test files still carry stale tracking comments:
- `tests/cache.rs:240-252` — "Filed as `design/arch/fixmes/0121-…` … do not fix
  in-sprint".
- `tests/spec_08_modules.rs` — ~9 `// FIXME(/int): same --run-mode defect as
  FIXME 0121` comments on tests that now pass.

These are misleading (the defect is fixed) and are `/qa`-owned test-file edits,
out of scope for the W-Module `/dev` (int) change-set.

## Proposed resolution

`/qa` sweeps the stale `FIXME(0121)` / "do not fix in-sprint" comments from
`tests/cache.rs` and `tests/spec_08_modules.rs`, leaving the tests as plain
passing regression guards (keep the `// spec:` annotations).

## Operational implication / Context

Cosmetic test-hygiene; surfaced by the W-Module `/review` gate (Suggestion).
Non-blocking. Can fold into any `/qa` ledger pass this sprint.
