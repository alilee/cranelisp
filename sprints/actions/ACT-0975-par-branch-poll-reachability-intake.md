---
id: ACT-0975
title: Investigate poll and combinator nodes reached inside synchronous Par branches
status: resolved
priority: normal
from: design
to: qa
sprint: 122
filed_at: 2026-09-21
refers_to:
  - spec/10-io.md
  - crates/cranelisp-intrinsics/src/io.rs
  - src/bind_chain_analysis.rs
  - design/intrinsics/reactor.md
---

## Resolution (qa, 2026-11-16, S124 Phase 3, at `4b58ab93`)

- **Not a defect: the shape is excluded.** `src/bind_chain_analysis.rs::classify_expr`
  classes every bind step that is not a direct call to a platform effect as
  `Sequential`, so only a platform-effect leaf becomes a `Par` branch. A
  branch that continues through a `Bind` to a poll, launch or select node is
  never built.
- **Observed.** Nine independent-pair programs whose steps are a user
  function, an inline `bind`, a `race`, a `select` or a launching loop each
  returned the right value and ran serially; the direct-leaf control
  overlapped. Record: [S124 evidence delta](../../tests/plan/s124-evidence-delta.md#41-act-0975--excluded).
- **Refuted if** the scheduling pass admits a non-leaf step into a `Par`
  group. Fence F-0975 of that delta fails then.
- Delete this action once F-0975 is committed and
  `tests/plan/s122-evidence-delta.md` no longer links it.

## S122 disposition (user-approved 2026-09-30)

Under the [approved S122 disposition](../../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30):

- **Carried to S123 (K7, R4).** First deferral.

## Observation and limit

The runtime documentation pass found that the synchronous trampoline used on
Rayon workers rejects EffectPoll, Launch and Select node tags. A Par branch
whose root is not a poll node can route to that synchronous path. It is not
established whether language lowering can produce such a branch whose later
Bind step reaches one of those nodes. This is a source-read reachability
question, not a reproduced defect or attributed failure.

## Required disposition

Read current lowering and dispatch first. Allocate the smallest language-level
case and discriminating control needed to establish whether such a branch is
reachable. If a permitted program fails, retain a permanent failing, unignored
spec-traced reproduction before attributing and routing a correction. If the
shape is excluded, record the actual exclusion mechanism and close this intake.

Provenance: design (intrinsics) session
`6cc56e2b-7704-4032-85cc-5cb819c732d1`, S122 documentation consolidation.
