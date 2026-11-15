# Appendix D: Open Requirement Questions

Owner: `spec`. The user decides open normative questions; proposals are
non-normative.

No open requirement questions remain from S123-Q1–Q11. The user rulings of
2026-11-15 are recorded in their normative homes: runtime §12.4.3 and §12.7,
IO §10.10.1, modules §8.9.3, and REPL §0.5.6, §0.8, §14.9 and §16.
The decision source is [Sprint 123, Phase 3 user rulings](../sprints/SPRINT.md#user-rulings-on-the-phase-3-decisions-2026-11-15).

### S123-Q12: Deleted-file recreation question

**Open, 2026-11-15; user decision required through `sprint`.** What exact sentence should precede the `[y/N]` prompt when the REPL asks to recreate a deleted backing file (§14.9)?

The [Phase 3 → 4 ruling](../sprints/SPRINT.md#user-rulings-at-the-phase-3--4-checkpoint-2026-11-15) accepts the design's deletion-notice wording. [REPL lifecycle design](../design/int/repl-lifecycle.md) specifies the `[y/N]` prompt and proposes `[deleted: <file>]` in §1.4, now recorded in [REPL §14.9](../repl/spec/14-file-watching.md#149-backing-file-appearance-and-deletion-s123), but its deletion rule leaves the question wording to `spec` without supplying a sentence. There is no exact question text to transcribe from the approved reading.

### S123-Q13: Test child ending without a result

**Open, 2026-11-15; user decision required through `sprint`.** For a test whose child ends without a result and is not classified as a panic, should [REPL §16.2](../repl/spec/16-test-discovery.md#162-running-tests-s123) require a `FAILED: <reason>` result line with these exact reasons?

- Signal termination: `test process was killed by signal N`.
- Exit status: `test process exited with status N without a result`.

Here `N` is the signal number or exit status. **Recommendation:** adopt these two report forms. They distinguish signal termination from an exit without a returned result and retain the usual fully qualified test name in the result line. The alternative is to require that distinction and the number while leaving the sentence diagnostic rather than fixing its wording.

[Test-runner design §6.5](../design/int/test-runner.md#65-the-test-child) assigns an open test a failure for such an ending and restarts after it, but explicitly leaves wording to `spec`. The built messages are in `open_test_outcome` in [the child supervisor](../src/session_v4/test_runner/child.rs). They are recorded here as an unapproved proposal, not as normative behavior inferred from implementation. For a dispatch fault, the built result reason names only the exit status; the platform function and fault text appear in the relayed stderr report. The coordinator must reconcile that placement with the [checkpoint ruling](../sprints/SPRINT.md#user-rulings-at-the-phase-3--4-checkpoint-2026-11-15) that a test child shows a dispatch fault as a failed test naming the cause before adoption.
