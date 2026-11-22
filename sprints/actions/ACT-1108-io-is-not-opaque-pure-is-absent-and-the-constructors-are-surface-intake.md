---
id: ACT-1108
title: "`IO` is not opaque: `primitives/pure` does not exist and the `Pure` constructor constructs and matches"
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-22
refers_to:
  - spec/10-io.md §10.1
  - spec/10-io.md §10.2
  - spec/03-types.md §3.2.3
  - src/bootstrap.rs
---

## Authority

The user ruled on 2026-11-22 that `IO` is an opaque type with `pure` as its
interface (`sprints/SPRINT.md`, Notes; `spec` at `2fe6d28f`).
[Spec §10.1](../../spec/10-io.md): the language has `(IO a)` and no
constructors for it, and user code MUST NOT construct an IO value through a
constructor or pattern-match on one. §10.2: `primitives/pure` is a public
built-in function. **The user also decided the compiler work is not S124
scope.** This filing is the record of the gap and carries its cell.

## Observation

`qa`, 2026-11-22, the debug binary built from `11ea995e` (no compiler source
has changed since), no prelude, REPL with `--no-color --no-agent`.

| Turn | Observed | Required |
|---|---|---|
| `(primitives/pure 42)` | `module 'primitives' has no member 'pure'`, then two more lines for the one refusal, one of them an internal value (`SymbolTypechecked(FQSymbol { … })`) | 42 |
| `(primitives/Pure 42)` | 42 | Refused |
| A match arm `(primitives/Pure x)` on an IO value | Accepted | Refused |
| `Effect` and `Bind` | [ACT-1106](ACT-1106-effect-constructors-field-is-typed-as-the-io-value-and-holds-a-thunk-intake.md), [ACT-1107](ACT-1107-match-on-io-with-pure-and-effect-arms-is-accepted-and-fails-on-a-bind-node-intake.md), [ACT-1105](ACT-1105-qualified-primitives-bind-constructs-a-node-shorter-than-the-runtime-reads-intake.md) | Refused |

## Classification

- **A nonconformance against a requirement ruled on 2026-11-22.** Before it
  the specification listed the constructors. No wrong value follows from
  `Pure` itself.
- **Reach.** The suite's own fixtures, the examples and the guides build IO
  values with `Pure`. The correction is a migration of all of them.
- **The three memory-unsafe filings are faces of the same surface** and are
  closed by the same correction. They stay open on their own cells.

## Attribution

`src/bootstrap.rs` seeds `IO` with three constructors, two of them public,
and seeds no `pure`. Read in source; `spec`'s report names the same lines.

## Routing

- **`qa` holds this action.** Carried to the next sprint by the user's
  decision.
- **`test`:** T-IO-OPAQUE, in the
  [S124 evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).
- **`arch`, then `design` and `dev`:** the opaque type and the migration.
- **Lead for `dev`(`src/`):** the three-line refusal of an absent member.

## Completion evidence

T-IO-OPAQUE is committed, observed RED, and passes on the corrected build.
