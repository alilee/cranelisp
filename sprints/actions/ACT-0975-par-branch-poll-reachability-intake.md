---
id: ACT-0975
title: Investigate poll and combinator nodes reached inside synchronous Par branches
status: open
priority: normal
from: design
to: qa
sprint: 122
filed_at: 2026-09-21
refers_to:
  - spec/10-io.md
  - crates/cranelisp-intrinsics/src/io.rs
  - design/intrinsics/reactor.md
---

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
