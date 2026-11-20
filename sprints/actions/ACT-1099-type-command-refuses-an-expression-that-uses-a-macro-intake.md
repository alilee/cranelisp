---
id: ACT-1099
title: "`/type` refuses an expression that uses a macro, as an undefined variable"
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-20
refers_to:
  - repl/spec/03-slash-commands.md §3.1
  - src/repl/commands.rs::typecheck_only
  - sprints/actions/ACT-1089-type-command-given-a-definition-commits-it-without-code-intake.md
---

## Observation

`qa`, 2026-11-20, the debug binary built from `3c5e41ca`, no prelude, a
scratch directory since removed, found while re-reading ACT-1089.

```clojure
(import [primitives [Int add-i64]])
(defmacro twice [x] `(add-i64 ~x ~x))
(twice 2)          ; :primitives/Int 4
/type (twice 2)    ; Error: type error at 1..6: undefined variable: twice
```

Control: `/type (add-i64 2 2)` prints `:primitives/Int`.

## Classification: a defect against REPL §3.1

- §3.1: `/type <form>` shows an expression's type without evaluating it.
  `(twice 2)` is an expression the session evaluates, and its type is
  `Int`.
- Expanding a macro is not evaluating the expression: the same expansion
  happens when any expression is typechecked.
- **Severity: a legal query refused,** with a diagnostic that names a defined
  macro as undefined. No session effect and no memory hazard.
- **Not established:** its age. `qa` ran no earlier tree.

## Attribution: the binary, provisional

The control differs from the subject only by the macro call, so `/type`'s
path does not expand macros. `qa` did not read where
`src/repl/commands.rs::typecheck_only` departs from the evaluation path.
**Refuted if** `/type` of a macro call succeeds in some session shape.

## Routing

- **`qa` holds this action.**
- **`test`:** T-TYPE-MACRO, in the
  [S124 evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).
- **`design`(int), then `dev`(`src/`):** the correction, carried on
  T-TYPE-MACRO unless the user schedules it. It shares `typecheck_only` with
  ACT-1089.

## Completion evidence

T-TYPE-MACRO is committed, observed RED on its type clause, and passes on
the corrected build with its control unchanged.
