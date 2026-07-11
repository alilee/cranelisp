# Failure Ledger — RETIRED (S108)

This ledger is **retired as of Sprint 108** (M1, user-approved). It had grown
into ~4400 lines of append-only per-sprint RED narrative, mostly describing
tests long since GREEN. Both of its functions moved onto the permanent test
corpus:

- **Regression triage** (expected-RED vs new breakage): the inline
  defect-comment / open-FIXME convention — root `CLAUDE.md` §Testing. Every
  intentional RED traces to an open defect naming its owner; a RED that does
  not so trace is a genuine regression.
- **Frequency / locus / recurrence analysis**: the `// defect:` notation on
  repro tests — `tests/CLAUDE.md` §"Defect-repro notation" (controlled
  `class=` vocabulary owned by `/qa`). Works over GREEN repros too.
- The anti-pattern discipline (no "flaky" / "timing-sensitive" / "documented
  race" / "pre-existing") migrated to `tests/CLAUDE.md` §"Failing-test
  discipline".

Full history: `git log -p -- tests/plan/ledger.md` (last full revision:
`git show a25ce2c8:tests/plan/ledger.md`).
