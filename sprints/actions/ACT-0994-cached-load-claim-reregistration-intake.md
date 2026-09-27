---
id: ACT-0994
title: Assess cached-load completion across module re-registration
status: open
priority: advisory
from: sprint
to: qa
sprint: 122
filed_at: 2026-09-27
refers_to:
  - src/scheduler.rs
  - src/worker.rs
  - design/int/int.md
  - tests/plan/s122-evidence-delta.md
---

## Request

Retain S122 review FA-1 as QA intake. It is an unobserved, pre-existing lead,
not a demonstrated recurrence of the repaired REPL cache-restore race and not
an accepted residual. The mechanism and falsifier are in
[the cache-load design](../../design/int/int.md#71-cache-hit-flow-inside-register_module),
under *Claim and re-registration*.

Source verified on 2026-09-27: `src/scheduler.rs` permits re-registration of
a typecheck-ready module while its cached load is claimed. Re-registration
replaces its scheduler state; `CachedLoadClaim::complete_loaded` then marks
the current module state in memory without checking which registration
received the claim. The cached loader publishes into the live table in
`src/worker.rs`. No harmful watcher interleaving has been reproduced.

When scheduled, coordinate with design(int) on whether load completion must
be bound to its registration. Allocate the smallest discriminating evidence;
do not infer a runtime failure from the scheduler transition alone.

## Completion evidence

Record a supported or refuted mechanism and its disposition. If a defect is
reproduced, retain an unignored regression test and route the repair to
`dev`(src). A useful runtime discriminator is an edit to a restored module
while its cached load is outstanding, followed by a call that observes the
pre-edit body or a signal. Keep this intake separate from RR-1's completed
2000-session acceptance evidence.
