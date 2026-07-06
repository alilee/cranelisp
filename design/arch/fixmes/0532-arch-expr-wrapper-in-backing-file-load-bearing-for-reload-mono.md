---
number: 0532
target: /arch
filed_by: /sprint
filed_at: 2026-07-06
sprint_filed: 103
refers_to: src/save.rs::generate_fns_and_macros, src/redefine.rs (T1 reload path), design/int/session-transaction.md
status: open
---

# Regen leaks the synthetic `__expr` wrapper into backing `.cl` files — and the reload path depends on it

## Issue
Discovered during S103 Wave 4 (T1 full cure). `src/save.rs::generate_fns_and_macros`
writes the synthetic `__expr` wrapper into the persisted backing `.cl` file: a normal
`expr`-then-`defn` session persists the stray top-level expression. This reads as a regen
fidelity leak (an internal artifact in a user-facing backing file).

The Wave-4 /dev attempted a filter to suppress it and found the leak is **load-bearing**:
the T1 reload path RELIES on that persisted expression to force mono-instantiation of the
reloaded module. Removing it regressed the polymorphic reload. The filter was reverted.

So this is not a simple cosmetic leak — it is a latent architectural coupling: regen writes
`__expr` wrappers, and the reload mono-instantiation path silently depends on their presence.
Two concerns that should not be entangled (persistence fidelity vs. mono-instantiation
triggering) are coupled through a synthetic artifact in a user-visible file.

## Proposed resolution
`/arch` (cross-boundary: persistence in src/ + mono-instantiation triggering) to decide the
right seam:
- Should mono-instantiation on reload be triggered explicitly (a reload-path instantiation
  request) rather than implicitly via a persisted `__expr`?
- Should the backing-file writer omit `__expr` wrappers (persistence fidelity) once the
  reload path no longer depends on them?
Sequence the decoupling so persistence fidelity and reload correctness are both satisfied
without the shared artifact.

## Operational implication / Context
Not a correctness bug today (the coupling works). It is a maintainability/soundness smell —
a future change to either regen or the reload path can silently break the other. Flagged
note-only by the Wave-4 /dev (the filter was reverted, so no code change shipped). Relates to
[[0530]] (regen sections 5–7 not source-first) — both are regen-fidelity gaps under the T1
reload path.
