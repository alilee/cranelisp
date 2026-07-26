---
number: 0872
target: /arch
filed_by: /sprint
filed_at: 2026-07-25
sprint_filed: 118
refers_to: audits/cranelisp-platform-s117.md §R3;
  design/arch/bounded-contexts.md §5
status: open
---

# Reconcile bounded-contexts §5 from migration diary to current invariants (audit R3)

User-accepted S117 platform-audit recommendation R3 (2026-07-25, S118 Phase 1).
Quoting the assessment:

> BC §5 states the current generated-schema/layout-hash mechanism, core v9
> poll ABI, shared two-field callback builder relationship, and
> poll-in/wake-out boundary once. Superseded S71/S76/v7 mechanisms are reduced
> to short historical pointers. Every "pending/as-built" label agrees with
> source. This is a documentation convergence only; it does not reopen settled
> platform architecture.

Evidence: `bounded-contexts.md:515-575` simultaneously says target, as-built,
implementation pending, dormant feature, future wiring, and current v9
cutover; the durable current invariants begin only at `:591`.

Cost: medium. Scheduling: `/arch` may fold this into any S118 pass over
`bounded-contexts.md` (Phase 2/7 windows) or defer to S119 with rationale;
documentation convergence only.

> **Status confirmation (`/arch`, 2026-07-26, option-paper dispatch):** the
> Phase-2 ruling-4 scheduling STANDS — this is executed in the S118 `/arch`
> Phase-7 close window (it gates nothing), deferring to S119 only if close is
> compressed. The S118 descope (2026-07-26) does not change this: Phase 7
> still runs, and the option-paper dispatch was scoped to the paper + 0883,
> not to a BC §5 rewrite.
