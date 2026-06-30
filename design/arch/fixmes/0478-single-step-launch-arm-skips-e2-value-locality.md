---
number: 0478
target: /int
filed_by: /sprint
filed_at: 2026-06-29
sprint_filed: 96
refers_to: src/bind_chain_analysis.rs (launch_eligible single-step arm), design/arch/effect-concurrency.md §4.1 (E2 value-locality, §B4 accept-loop rationale)
status: open
---

# Title — the single-step launch arm admits a discarded ResourceSerial step without an E2 value-locality check

## Issue

Surfaced during the S96 0470 marquee fix. `launch_eligible`'s **single-step**
arm accepts a discarded `ResourceSerial` effect step relying on the per-call
dynamic token (per §4.1 §B4's accept-loop rationale), and does **not** run the
E2 value-locality check that the sub-tree arm runs. This is a latent
permissiveness: a **discarded ResourceSerial middle step whose continuation
performs a same-token effect** could be detached single-step, reordering two
same-token effects across the detach boundary.

It is **not triggered** by the marquee web fixture — the timer (`sleep`) added
to the launchable set is token-free and is explicitly EXCLUDED from the
single-step arm (`test_no_single_step_launch_for_lone_sleep_step` pins this),
and the web handler launches as a whole sub-tree (where E2 *is* checked), not
single-step. So the marquee fan-out is sound.

## Proposed resolution

A §4.1 hardening pass: either (a) extend the single-step arm to run the same
E2 value-locality check as the sub-tree arm (refuse a discarded ResourceSerial
single step whose continuation shares its token), or (b) confirm via §B4 that
the accept-loop dynamic-token guarantee makes the single-step case sound in all
shapes and document why no E2 check is needed there. Whichever: add a unit in
`src/bind_chain_analysis/tests.rs` for the `discarded same-token middle step +
same-token continuation` shape so the chosen behaviour is pinned. Do NOT weaken
the existing §B4 single-step launch the synthetic `concurrency_fanout` test
guards.

## Operational implication / Context

Low severity, latent, no current trigger. Filed as the forward hardening note
the 0470 fix author flagged, so it is not lost. Not a blocker for S96.
