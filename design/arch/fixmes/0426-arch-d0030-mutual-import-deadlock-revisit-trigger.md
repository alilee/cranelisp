---
number: 0426
target: /arch
filed_by: /arch
filed_at: 2026-06-21
sprint_filed: 87
refers_to: design/arch/decisions/0030-form-by-form-scheduler-mutual-imports.md, src/scheduler.rs, src/worker.rs, design/arch/bounded-contexts.md §6
status: open
---

# Decision 0030 mutual-import deadlock — standing accepted-unfixed constraint; record the revisit-trigger

## Issue

Re-surfaced during the S87 `/arch` concurrency discussion. **Decision 0030**
records that the form-by-form scheduler **deadlocks when two modules import from
each other**: when A's Pass-0 hits `(import [B [*]])` it blocks waiting on B's
signatures, while B's Pass-0 hits `(import [A [*]])` and blocks waiting on A's —
neither makes progress, because signatures are registered incrementally
form-by-form rather than in a separate pre-pass.

It is **accepted-unfixed by design**, per:
- **Principle 6** (complexity budget) — a real fix requires a major scheduler
  redesign; the workaround (one-directional imports; the `discover-tests` /
  `run-test` test-scaffolding pattern) is clear, cheap, and ergonomic; and
- **Principle 8** (no interim implementation) — we do not half-fix with a
  timeout-based deadlock detector or a speculative one-shot retry.

The constraint is correctly documented as a Decision, but it has **no actionable
tracking item carrying a revisit-trigger** — so it is at risk of being
rediscovered from scratch rather than revisited deliberately. This FIXME supplies
the trigger.

## Proposed resolution

**Keep the constraint as-is (no roadmap work)** until one of:

- **(a)** a user-facing program legitimately needs mutually-importing modules and
  the documented workaround is inadequate; or
- **(b)** a scheduler / dependency-resolution restructure happens for other
  reasons — in particular the **dependency-service extraction ([0425])** — at
  which point the candidate fix (a **pre-pass that registers all module
  signatures before any body typechecks**, separating signature resolution from
  body checking) MUST be evaluated in the same design, not bolted on later.

Record the chosen trigger here when actioned. Manifestation when fixed: the
scheduler design (BC §6 + `design/int/` + `src/scheduler.rs`); Decision 0030
updates or retracts at that point.

A standalone fix for this constraint alone is **not** justified (Principle 6) —
its resolution rides on a coordination-layer redesign undertaken for broader
reasons.

## Operational implication / Context

- **No defect, no failing test** — an accepted architectural constraint, not a
  bug. Decision 0030 is the canonical statement; this FIXME is the actionable
  revisit-tracker that the Decision cannot be (a Decision states "what is," a
  FIXME tracks "what to reconsider and when").
- **Strongly coupled to [0425].** The signature/body pre-pass that would lift
  this constraint is exactly the kind of change a dependency-service extraction
  invites. Decide the two together or not at all.
