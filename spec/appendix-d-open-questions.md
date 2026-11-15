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
