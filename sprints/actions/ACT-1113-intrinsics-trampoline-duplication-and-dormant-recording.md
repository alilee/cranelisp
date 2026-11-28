---
id: ACT-1113
title: Single-source the IO trampoline transitions and remove test-only strand recording cost from production
status: open
priority: advisory
from: sprint
to: design
sprint: 125
filed_at: 2026-11-27
refers_to:
  - audits/cranelisp-intrinsics-s125.md
  - crates/cranelisp-intrinsics/src/io.rs
  - crates/cranelisp-intrinsics/src/strand.rs
---

## Request

Audit finding F4 (`audits/cranelisp-intrinsics-s125.md` §4), carried by the
user at the S125 Phase 6a checkpoint (2026-11-27, "otherwise agreed").
`design` on intrinsics decides the shape when intrinsics is the focus module.

Verified 2026-11-27 against the audit's citations:
`io.rs::run_io_trampoline_inner_async` and `run_io_trampoline_inner` each keep
frame initialization, edge-disposer selection, tag dispatch, the `Bind`
event/push sequence and step advancement. `strand.rs::sink::emit_strand_event`
takes a global mutex on every event, and only tests read what it records. No
latency or contention cost has been measured.

Keep the worker/reactor execution boundary and the existing discriminating
evidence. Route any interface change through `arch`.

## Completion evidence

One owner for each common transition, ordinary execution without the
recording lock, and the existing trampoline and strand tests green.
