---
number: 0274
target: /repl
filed_by: /spec
filed_at: 2026-06-06
sprint_filed: 76
refers_to: repl/spec.md §16 (test discovery and execution), design/arch/test-discovery.md (SETTLED, fourth convergence), spec/appendix-a-builtins.md §A.3, spec/03-types.md §3.2.5–§3.2.6
status: open
---

# Align repl/spec.md §16 to the settled test-discovery design

## Issue

The settled test-discovery design (`design/arch/test-discovery.md`, user 2026-06-06)
changes the test surface repl/spec.md §16 describes. The /spec cascade landed in
spec/ (S76); §16 is /repl-owned and needs the matching alignment.

## Proposed resolution

- §16 narrative moves to the **pairs-and-combinator** shape: `discover-tests`
  returns `(Vec (Pair String (Fn [] (Option String))))` name+callable pairs; the
  in-language runner folds three-way over `catch-runtime-error`'s
  `(Result (Option String) String)` — panic / pass / assertion-fail.
- Record the **freshness** property: wrappers are late-bound GOT-slot callables;
  re-calling `discover-tests` re-scans live state. The macro-runner approach is
  retired (composability disproof — see the design doc's superseded appendix).
- Record `--link` interim behavior: `discover-tests` is REPL/`--run` only
  (unresolved symbol at link, no friendly rejection); `catch-runtime-error`
  works in all modes.
- Retire any §16 reference to `TestResult`/`TestPass`/`TestFail` and `run-test`;
  results are `(Option String)` (None=pass, Some reason=fail); the FQ name lives
  in the Pair; timing via `trace`'s nanos.
- Keep the `#16-test-discovery-and-execution` heading anchor stable — new spec/
  cross-links reference it.
- `/run-tests` slash command: decide its presentation (sugar over the in-language
  runner) with /int + /stdlib (FIXME 0273 carries the stdlib runner, S77).

## Operational implication / Context

Doc-only alignment; no implementation dependency (can land any time, naturally
with the S77 implementation FIXMEs 0269–0273).
