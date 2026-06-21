---
number: 0425
target: /arch
filed_by: /arch
filed_at: 2026-06-21
sprint_filed: 87
refers_to: design/int/concurrency-architecture.md §3 (inventory) + §6 (recommendations), design/arch/sequences/concurrency-dependency-service.mmd, design/arch/bounded-contexts.md §6, src/scheduler.rs, src/worker.rs, src/process_form.rs, src/session_v4.rs
status: open
---

# Compiler-internal concurrency debt — promote the dependency-service extraction (+ SharedState ownership cleanup) to actionable arch work

## Issue

Re-surveying the compiler-internal concurrency model during the S87 `/arch`
concurrency discussion confirmed the standing structural debt already inventoried
in `design/int/concurrency-architecture.md`. It has an analysis but no actionable
arch tracking item, so it risks being perpetually "documented but never scheduled."

The highest-leverage item: the **dependency publication / readiness protocol**
(register dep → publish parsed sexps → block → resume) is *one logical protocol
smeared across four files* — `src/scheduler.rs`, `src/worker.rs`,
`src/process_form.rs`, `src/session_v4.rs` — with **no single owning subsystem**.
The `concurrency-dependency-service` sequence diagram asserts a clean invariant —
"the dependency service is the sole writer of dependency state; workers do not poll
or read shared state" — but the as-built **achieves that invariant by convention
spread over four files, not by a structural boundary**. That is:

- a **Principle 18 gap** — the invariant is enforced by discipline (every site
  remembers to route through the right call), not by construction; and
- a **Principle 13 gap** — the diagram claims a structure (a single "dependency
  service" actor) that the code does not embody as a unit.

Adjacent debt the same audit records:

- **`SharedState` field-ownership opacity** — REPL-only state is mixed into the
  shared data plane; broad direct field access weakens local reasoning about who
  may mutate what when.
- **`cached_modules` dual-store smell** — the set appears in both `SharedState`
  and `SchedulerState`; the audit cannot tell from the code whether this is two
  physical stores of one logical set (a Principle 7 violation) or two legitimate
  stores. Classified `invariant-unclear`.
- **Priority/nice worker subsystem split** — priority-worker logic in
  `worker.rs`, nice-worker logic in `session_v4.rs`, with mirrored code paths.

None of this changes language behaviour; it is pure internal structure.

## Proposed resolution

1. **Extract one explicit dependency-service subsystem** that owns
   publish/readiness/block/resume as a unit, so the "sole writer" invariant is
   *structural* (a type/module other code cannot bypass) rather than convention.
   This is the audit's "highest-leverage architecture change."
2. Sweep `SharedState` for **per-field ownership**; move REPL-only state out of the
   shared plane where possible; narrow direct mutation to owned accessors.
3. Resolve the `cached_modules` dual-store — collapse to a single home or justify
   the two as a documented exception (Principle 7).
4. Unify the priority/nice worker subsystem; collapse mirrored paths.

Manifestation sites when actioned: **BC §6 (int)** for the subsystem boundary;
`design/int/` for the interior; the `concurrency-dependency-service` diagram
reconciles to the as-built once the subsystem exists as a unit.

**Phase-H scope decision needed.** Because this is structure-only (no language-
behaviour change), it can land independent of H feature work — but H is the
efficiency tier and a clean coordination boundary is the right substrate for any
scheduling tuning. Decide explicitly: H-prep, or carried debt with a later
dedicated arc.

## Operational implication / Context

- **No defect, no failing test** — structural debt, not a spec violation or crash.
  Per `memory/feedback_no_fixme_with_failing_test.md`, a design FIXME (not a test)
  is the correct record for structural debt / a capability gap.
- The analysis already exists (`concurrency-architecture.md` §3 inventory + §6
  recommendations). This FIXME promotes the recommendation to an actionable arch
  item with a scope decision attached.
- **Cross-ref [0426]** — a dependency-service / scheduler restructure is the
  natural place to also reconsider the Decision 0030 mutual-import deadlock
  (separating signature resolution from body checking is the candidate fix for
  both). Do not redesign the coordination layer for one without evaluating the
  other in the same design.
