---
id: ACT-0977
title: Establish evidence and realize cancellation ownership for launched work
status: open
priority: normal
from: sprint
to: qa
sprint: 122
filed_at: 2026-09-21
refers_to:
  - spec/10-io.md
  - spec/12-runtime.md
  - design/arch/effect-concurrency.md
  - design/intrinsics/reactor.md
---

## Approved requirement and current limit

The user approved launched work inheriting the cancellation context of enclosing
race/select/timeout effects, independent of scheduling and ordinary function
lifetime. Normal completion continues draining. The current runtime places
launched strands under one supervisor per drive; it does not connect their
cancellation to the launching branch. The coherence pass records the requirement
and implementation limit, without adding runtime capability.

## Next disposition

QA first establishes a minimal reproduction on existing synthetic platform
leaves: a losing or timed-out branch launches work whose remaining effects must
stop and resources release. Pair it with a winning-branch control, and preserve
nested propagation and scheduling-independent ownership in the evidence design.
A separate observable completion witness must discriminate normal draining from
skipped launched work; process startup/compilation timing alone is insufficient.
Existing direct-race cancellation tests do not cover these launched-work cases.

Route a confirmed failing, unignored spec-traced reproduction through arch and
intrinsics design before implementation. Do not add task handles, task-group
syntax, global cancellation or a drain-deadline policy as an incidental fix.
Any public API/schema proposal follows its existing approval rules.

Shutdown-signal and disconnect-watch platform effects remain separate missing
capabilities. The user asked for coherent contracts before adding capability;
this action preserves the outstanding work and does not approve those additions
or claim the new ownership semantics are implemented.

Provenance: spec `731347f0-c576-419d-98b5-234c5dd595a5` and QA
`434e5dcb-8036-42e8-bcbb-ebc7e1049752`, S122.
