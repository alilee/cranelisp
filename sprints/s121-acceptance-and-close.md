# Sprint 121 — acceptance and close

**Status:** CLOSED — 2026-09-09, with accepted residuals. The user explicitly
approved closure, commit and push. Publication is limited to the delivered
sprint and its reviewed shared-package contribution; upstream package adoption
waits until the next sprint's opening.

## Delivered outcome

The compiler wave decisions and their individual API/spec approvals are
recorded in [the sprint archive](archive/sprint-121.md). All five Phase-6b user-facing streams are
delivered: documentation, learning examples, stdlib helpers, REPL records/demos,
and exemplar records plus linked HTTP verification. The timeout rejection is
fixed with permanent regression evidence; helper item 0780 is closed.

Fresh default-suite run `3d3fde5b-001f-4179-a076-2e1502fa6a96` finished in
131.473s: 5,905 run, 5,901 passed, four failed, one skipped. Besides the accepted
sequence-IO failure, it found a draft archive-path citation error and two
`spec_11_stdlib` failure-path tests. The citation wording is repaired and its
ratchet passes. QA classified the diagnostic trigger as stale/unarmed; the
subsequent explicit-status isolation established three permanent REDs and one
GREEN control: generic scalar replacement returns the prior body result,
the vector sibling signals 11, and monomorphic replacement succeeds. Runs
`970011df-7f8e-4734-989e-02776f415023` and
`a0a0d4fb-2034-408a-8243-c03c5111cc51` record those incremental results.
The user accepted these residuals for top priority next sprint; no aggregate
final-suite rerun or all-green claim is made. Original full-suite evidence:
`/tmp/cranelisp-s121-phase6b-acceptance-iFoDVf/nextest.log`.
Earlier focused evidence is not promoted to a current whole-suite pass.

## Accepted residuals and limits

- **Top priority next sprint:** investigate and fix the public generic
  redefinition stale-body/SIGSEGV family from its enabled REDs in
  `tests/spec_11_stdlib.rs`, with internal attribution and a seam-level RED
  before implementation. Coordinate the distinct failed-turn coverage repair
  in [ACT-0958](actions/ACT-0958-rearm-failed-turn-recovery-coverage.md).
  The user directed this carry while wrapping Sprint 121; no investigation
  remains active. No requirement is weakened and no test is ignored.
- The public sequence-IO runtime defect remains an enabled failing test; its
  explicit-bind control remains enabled. The user deferred investigation/fix.
- Audit residuals are approved next-sprint work in
  [ACT-0957](actions/ACT-0957-shared-role-audit-residuals.md). This is not a claim
  that every audit recommendation is implemented.
- Existing `/learn`, semantic `/search`, network-lesson, `def` application,
  exemplar performance/adoption and other individually recorded carries retain
  their approved scope. No carry expands or narrows the platform interface.
- Acceptance is not an all-green or fresh-clone-verified release claim.
  Commit and push authority is the user's separate, explicit close approval.

## Phase 7 — approved close operations

The user approved:

1. Record the accepted outcome, exact evidence, residuals and next-sprint
   handoffs in the sprint outcome.
2. Update the Sprint 121 outcome and next-sprint handoff in `sprints/ROADMAP.md`.
3. Archive the completed live plan under the standard Sprint 121 archive name, retaining
   this proposal and the linked decision/evidence records. The live
   `sprints/SPRINT.md` is removed only as that recoverable archival move.
4. Run reference/structure checks affected by these record changes and report
   completion with the known runtime defect still explicit.

5. Commit and push the delivered Cranelisp changes and the reviewed five-file
   shared-package contribution. Preserve the sprint-tested package revision
   `1172631` in Cranelisp; reconcile the contribution with upstream in an
   isolated checkout, without adopting other projects' changes in this sprint.

Sprint coordinates these operations. The package contribution adds cohesive
stream guidance and the explicitly authorized per-run model override, with
documentation and tests. Its local dispatcher and statistics checks pass
23/23 and 10/10 respectively. Package integration is separately verified before
publication. No compiler fix, spec/API change, baseline regeneration, upstream
package adoption, deployment or full-suite rerun belongs to this close.

## Closure evidence

The shared contribution is published on `se-agentic/main` at `98436c9`, a
normal fast-forward merge retaining both upstream history and Cranelisp's
sprint-tested `1172631` commit as an ancestor. Remote readback matches. The
isolated merge changes only the five contribution files relative to upstream;
Claude dispatcher tests pass 33/33, Codex dispatcher tests 66/66, and statistics
tests 10/10. Cranelisp's `.agents` checkout and gitlink remain at `1172631`.

The live plan is archived at `sprints/archive/sprint-121.md`; ROADMAP records
the next-sprint priority and accepted carries. The post-archive live citation
ratchet passes: 486 documents, 8,458 citations, zero findings. Staging exposed
extra EOF blank lines in new documents; those were removed without prose or
requirement changes. No permanent RED was disabled or removed.

Commit scope was checked against the seven compiler streams, five user-facing
streams, their evidence and standing records, starting from Sprint 120's close
commit `18bca20d`. The untraced `Cargo.toml` development-debug setting is
preserved locally but excluded from publication. The reported executing
evidence used the existing worktree configuration; no fresh-clone test claim
is made for the published commit.
