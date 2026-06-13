---
number: 0325
target: /backend
filed_by: /sprint
filed_at: 2026-06-13
sprint_filed: 80
refers_to: design/arch/d1-introspection-repl-only.md §B4/§B6, design/arch/bounded-contexts.md §6
status: open
---

# Skip CLIF-IR text generation in batch when introspection is off

## Issue
S80's D1b made `SharedState.introspection` REPL-only (`Option<DashMap>`, `None`
outside REPL), so in `--run`/`--link` no `Introspection` record is allocated and
the int-side codegen-product sinks pass `None` — the gate is closed. **But the
CLIF-IR text itself is still GENERATED unconditionally below the int boundary**:
`cranelisp-backend::compile_one_function` runs `format!("{}", func.display())`
(the CLIF rendering) on every compile regardless of mode, and the int layer then
drops it unread in batch. The user's introspection-REPL-only ruling (data
generated ONLY for introspection must not be generated in batch) is satisfied at
the "no record retained" floor, but not at the "no wasted generation" level —
the CLIF/disasm string formatting is wasted work + allocation in batch.

This was the explicit Class-2 residual of the D1b ruling
(`d1-introspection-repl-only.md §B4/§B6`): it was scoped OUT of D1b because the
generation site is in `cranelisp-backend` (a baseline-regen-carrying change),
and `bounded-contexts.md §6` references this as a "backend follow-up." The
follow-up was not filed at the time; `/sprint` files it now (S80 close-prep,
flagged by the consolidated `/review`).

## Proposed resolution
Thread an explicit "capture CLIF" intent into backend codegen so the
`func.display()` formatting (and any disasm string work done only for
introspection) is skipped when introspection is off:
- A `capture_clif: bool` on a `CompileOptions`/codegen-input struct, set true
  only when the int layer's `RunMode` populates introspection (REPL).
- `compile_one_function` skips the CLIF/disasm string rendering when false.
- Genuine byproducts the codegen knows anyway (e.g. `code_size`) keep flowing
  back to the worker for the existing retain-in-REPL / drop-in-batch path.
- Carries a `cranelisp-backend` public-api baseline regen if the signature of a
  pub fn changes — note in the change.

## Operational implication / Context
- **Not a correctness defect** — batch output is identical; this is wasted
  generation, not a behavioural bug. No test rides red on it.
- The "floor" (introspection store absent in batch, no record retained) already
  landed in S80 D1b. This FIXME is the data-flow completion of the user's
  introspection-REPL-only principle (`memory/introspection-repl-only-principle.md`).
- Schedule alongside other `/backend` codegen-input work; low urgency.
