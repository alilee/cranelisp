---
id: ACT-0986
title: Resolve the remaining test-discovery contract discrepancies
status: open
priority: required
from: arch
to: qa
sprint: 122
filed_at: 2026-09-22
refers_to:
  - repl/spec/16-test-discovery.md
  - spec/appendix-a-builtins.md
  - design/arch/test-discovery.md
  - design/int/test-runner.md
  - src/session_v4/test_runner.rs
  - crates/cranelisp-frontend/src/ast_builder/tests.rs
---

## S122 disposition (user-approved 2026-09-30)

Under the [approved S122 disposition](../../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30):

- **Item 1 is carried to S123 (K9, C6).** First deferral. The requirement stands; the user may instead narrow it through `spec`.
- **Item 2 is S122 work (K3).** `spec` makes the §16.5 example runnable, and frontend `dev` corrects the `test_discover_tests_no_arg_builds_as_apply` citation.

## Request

Two discrepancies remain open. Both fall outside the compiler-owned runner.

1. **In-language discovery does not warn.**
   - REPL §16.1 and the Appendix A `discover-tests` row require a mistyped
     `test-` function to be excluded and warned at discovery time.
   - `discover_eligible_tests` in `src/session_v4/test_runner.rs` discards the
     shared scan's warnings. The runner design's
     [residual leads](../../design/int/test-runner.md#12-residual-leads) and
     `design/arch/test-discovery.md` record the same thing: the extern runs
     inside compiled code and has no warning channel.
   - A REPL `(discover-tests [])` over a mistyped test therefore excludes it
     silently.
   - Resolve by one of these, not both:
     - a user ruling, through `spec`, that confines the warning to the
       compiler runner, or that accepts the residual; or
     - a failing `test` reproduction, then an `arch`/`design` warning channel
       for extern calls.
2. **§16.5 and one frontend test attribution.**
   - The REPL §16.5 programmatic-use example does not follow settled syntax:
     - each `match` arm is in its own vector, where spec §4.8 requires one
       flat `[pattern body …]` vector;
     - it uses nested constructor patterns such as `(Ok (Some why))`, which
       spec §6.6.1 rejects;
     - it uses `map`, `filter`, `str-concat` and `contains?` without importing
       them.
   - Assess a runnable form against settled syntax and route the prose to
     `spec`. Keep this separate from discovery behaviour.
   - `crates/cranelisp-frontend/src/ast_builder/tests.rs::test_discover_tests_no_arg_builds_as_apply`
     cites Appendix A for a parse-only property. The requirement it observes is
     REPL §16's "parse as plain applications". Arity rejection is evidenced
     separately by
     `tests/spec_12_runtime.rs::discover_tests_neg_no_argument_and_string_forms_are_type_errors`.
     The citation belongs to frontend `dev`.

## Resolved on 2026-09-28 (QA)

I opened the source and evidence for each item below.

- **Slash command versus extern eligibility.** Both use one predicate,
  `discovery::classify_test_definition`. `/run-tests` and `--test` read it
  through the shared runner, and `discover-tests` through the same scan.
  Evidence: `tests/test_runner.rs::test_mode_runs_every_test_reports_fq_lines_and_matches_run_tests`
  and `tests/spec_12_runtime.rs::discover_tests_excludes_mistyped_test_neg`.
- **The runner's warning.** `--test` writes the warning to stderr, and
  `/run-tests` shows it. The same TR-1 cell evidences both.
- **The direct-vector result and scope.** Evidenced as recorded on the
  Appendix A row.
- **Mode availability, including `--link`.** Appendix A now defers to REPL
  §16.6. Evidence: `tests/test_runner.rs` TR-5 and TR-5c.
- **The DT-1 carry.** Superseded by TR-5, which passes.

## Completion evidence

- For item 1: a recorded user disposition, or a failing un-ignored spec-traced
  reproduction plus its correction.
- For item 2: a runnable §16.5 form accepted by `spec`, and the frontend
  citation corrected.

This filing authorizes no assertion or runtime change by itself.
