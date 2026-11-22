---
id: ACT-1109
title: "Function values and nested IO values do not display as `#closure` and `#io`"
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-22
refers_to:
  - spec/12-runtime.md §12.9.1
  - repl/spec/01-display-format.md §1.5
  - spec/01-lexical.md §1.6
  - src/display.rs
---

## Authority

The user ruled the `#io` and `#closure` display markers on 2026-11-22
(`sprints/SPRINT.md`, Notes; `spec` at `2fe6d28f`), and decided the marker
migration is not S124 scope.

## Observation

`qa`, 2026-11-22, the debug binary built from `11ea995e`, no prelude, at the
REPL.

| Turn | Observed | Required |
|---|---|---|
| `(let [f (fn [:primitives/Int x] x)] f)` | `:(Fn [primitives/Int] primitives/Int) <closure>` | `#closure` |
| `(primitives/Some (fn [:primitives/Int x] x))` | `(Option.Some <closure>)` | `(Option.Some #closure)` |
| `[(primitives/sleep 0)]` | `[<unknown-tag:4>]` | `[#io]` |
| `(primitives/Some (primitives/sleep 0))` | `(Option.Some <unknown-tag:4>)` | `(Option.Some #io)` |
| A box holding `(primitives/Pure 1)` | `(Box.Mk (IO.Pure 1))` | `(Box.Mk #io)` |
| `#io`, and `#closure`, as input | A parse error each; the session continues | Rejected, which this is |

## Classification

- **A nonconformance against a requirement ruled on 2026-11-22;** wrong
  display, no memory hazard.
- **One row is older than the ruling:** a nested `sleep` value prints
  `<unknown-tag:4>`, an internal fallback, under the earlier text too.
- **Committed cells assert the retired token,** for example
  `repl_introspection::closure_value_display_shows_closure_token`. They are
  migrated with the correction.

## Attribution

The binary's value display (`src/display.rs`, `src/styled.rs`). `spec`'s
report names the `<closure>` comments there; `qa` did not read the
rendering code.

## Routing

- **`qa` holds this action.** Carried to the next sprint by the user's
  decision.
- **`test`:** T-MARKERS, in the
  [S124 evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).
- **`design`(int), then `dev`(`src/`):** the migration.

## Completion evidence

T-MARKERS is committed, observed RED on its two display clauses, and passes
on the corrected build with the reader clause unchanged.
