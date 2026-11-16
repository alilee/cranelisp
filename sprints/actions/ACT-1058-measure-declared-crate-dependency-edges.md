---
id: ACT-1058
title: Measure the declared crate dependency edges with an executing check
status: deferred
priority: advisory
from: sprint
to: arch
sprint: 124
filed_at: 2026-11-16
refers_to:
  - sprints/s124-rust-context-standard-evaluation.md
  - design/arch/bounded-contexts.md
  - .agents/tools/check_rust_contexts.py
---

## Request

The bounded-context dependency table is asserted, not measured: Cargo rejects
only cycles, and one absence (backend does not depend on primitives) has a
test. The reverse edge, primitives to backend, has no guard.

The user ruled on 2026-11-16 that the Rust context standard stays unadopted
and that the edge check is taken, scheduled after S124. `arch` selects the
mechanism. The [evaluation](../s124-rust-context-standard-evaluation.md)
records two candidates and their costs: the package checker with the contexts
declared as supporting crates (needs a recorded exception in root guidance),
or an in-repository check over `cargo metadata`.

## Completion evidence

- An executing check fails when a crate gains an edge the declaration lacks,
  shown by a planted edge, and stays silent on the tree as committed.
- `design/arch/bounded-contexts.md` states the graph's grade as measured and
  names the check.
