---
number: 0431
target: /qa
filed_by: /dev
filed_at: 2026-06-22
sprint_filed: 89
refers_to: tests/agent.rs::agent_build_cap_exhausted_give_up_stays_wire_valid
status: open
---

# E2E give-up assertion updated for corrected Phase-6 turn-end semantics

## Issue

The S89 Phase-6 fix (commit `fix(s89): … give-up line only at true turn-end …`)
corrected a live-confirmed defect: the user-facing
"I couldn't produce a definition that compiles cleanly here, so I did not submit
anything." line was printed per-failed-`submit` MID-turn, even when the turn
CONTINUED and ultimately produced a successful submit or a Done answer (live
trace: `fib` was defined after the first submit's repair cap exhausted). The line
was FALSE by end-of-turn.

The fix decouples the two feedbacks:
- **Model-facing** abort (`submit aborted: could not produce compiling code`) —
  KEPT, fed as the submit tool_result so the model can adapt and retry.
- **User-facing** give-up line — moved to TRUE turn-end (`agent_turn`), emitted
  at most once and ONLY when the turn produced no committed write AND no Done
  answer.

The e2e `agent_build_cap_exhausted_give_up_stays_wire_valid`
(`tests/agent.rs`, /qa-owned) drives the `CAP_EXHAUSTED_GIVE_UP` fixture, which
ends with `done: I tried but could not` — i.e. the turn ENDS ON A DONE ANSWER.
Under the corrected semantics the give-up line must NOT appear (the turn produced
an answer). The test's assertion (ii) previously asserted the line DID render —
that assertion was encoding the buggy behaviour.

## Proposed resolution

`/dev` made the minimal in-place correction to keep `--test agent` green (the
task's release gate): assertion (ii) now asserts the give-up line is ABSENT and
the model's answer (`I tried but could not`) renders instead. The PRIMARY
wire-validity guard (i), the silent-discard guard (iii), and the commit-nothing
guard (iv) are unchanged.

`/qa` should review the corrected assertion and, if a dedicated e2e for the
"turn produces NOTHING → give-up line shown exactly once" path is wanted, author
a fixture whose script ends WITHOUT a terminal `done:` (so the turn exhausts the
iteration budget with no answer) and assert the give-up line renders exactly
once. The unit-tier coverage for both arms already lands with the fix:
`src/agent/mod.rs::give_up_line_not_shown_when_turn_ultimately_submits` and
`::give_up_line_shown_once_when_turn_produces_nothing`.

## Operational implication / Context

`/dev` editing a `tests/`-owned file is outside the normal boundary; it was done
only to keep the release gate green in the same change-set as the behaviour fix
(no "test owed" follow-up). This FIXME records the edit for /qa's review and
ownership.
