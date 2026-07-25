---
number: 0885
target: /dev
filed_by: /review
filed_at: 2026-07-26
sprint_filed: 118
refers_to: crates/cranelisp-primitives/src/marshal/tests.rs::re1_embed_takes_exactly_one_reference_whatever_the_tail_size
status: open
---

# RE-1 inc-count fence proves net-zero, not "exactly one inc"

## Severity
Important

## Issue

`re1_embed_takes_exactly_one_reference_whatever_the_tail_size` (commit
`959833ea`) snapshots the RC words of every `ys` node/element before and
after the complete `sconcat` call and asserts the summed delta is 0.
Because the embed inc and the unconditional `consume_slist(ys)` epilogue
cancel *inside* the call, a summed delta of 0 proves interior holders were
untouched — the RE-1 core — but does NOT prove exactly one inc occurred.

Verified by walking the arithmetic: the mechanism the design explicitly
rejected (`design/runtime/s118-structural-embedding-ownership.md` §3,
"move instead of inc-then-consume" — delete the inc AND the
`consume_slist(ys)`) produces identical deltas and passes this row, every
balance row, and `re1_shared_tail_survives_the_results_release`. So the §3
ruling that the inc/consume pair stays unconditional and explicit
(Principle 18 — enforce invariants structurally) has no structural pin, and
the fence is weaker than the §5 claim and the commit message state ("the
embed performs exactly one inc for any |ys|, asserted against the RC
counters"). It does still catch deep-inc regressions (sum = n+h−1 > 0),
which is its primary purpose.

Delegated-review origin: Codex finding (Principle 5 cited), verified by the
adjudicator against the test body and the move-variant arithmetic.

## Proposed resolution

Add an observation that distinguishes one-inc-plus-one-consume from
zero-plus-zero. The cheapest in-process signal is the intrinsics RC tally
(`cranelisp_intrinsics::diagnostics` `tally_rc_inc`/`RC_INC_COUNT` twins,
already always-on counters): assert the rc_inc tally rises by exactly
|xs items| + 1 (copies + the single embed inc) across one `sconcat` call at
each |ys|. Alternatively pin the epilogue textually alongside the existing
grep-zero fence. `/dev`'s pick; test-only change.

## Context

Not a defect in the shipped fix — the fix itself is correct against RE-1
and the move-variant is arithmetically sound today; the gap is that the
fence advertised as pinning the *mechanism* pins only the *arithmetic*, so
a future "simplification" to the rejected move would land green.
