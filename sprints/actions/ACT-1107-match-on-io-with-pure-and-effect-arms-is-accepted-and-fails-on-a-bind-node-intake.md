---
id: ACT-1107
title: A match on `IO` with `Pure` and `Effect` arms is accepted as exhaustive and fails at run time on a bind node
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-22
refers_to:
  - spec/06-pattern-matching.md §6.5
  - spec/10-io.md §10.1
  - crates/cranelisp-typecheck/src/adt.rs
---

## Origin

`sprint`, by hand while answering a user question. `qa` took it in on
2026-11-22. What `IO` should be as a language type is open with the user;
this filing does not settle it.

## Observation

`qa`, 2026-11-22, the debug binary built from `11ea995e`, no prelude,
scratch directories since removed.

| Program | Observed |
|---|---|
| `(defn peek [io] (match io [(primitives/Pure x) x (primitives/Effect t) t]))` | Accepted: `(Fn [(primitives/IO a)] a)` |
| `(peek (primitives/bind (primitives/Pure 1) (fn [x] (primitives/Pure x))))` at the REPL | **`error: runtime panic: match failed`; the process exits 1** |
| The same as `main`'s value under `--run`, and linked | **The same panic; exit 1** |
| Control: the match with only the `Pure` arm | Refused: `non-exhaustive match on IO: missing constructor(s) Effect` |
| Control: `Pure` and a wildcard arm, on the bind node | 0 |

## Classification: a defect against spec §6.5

- [§6.5](../../spec/06-pattern-matching.md): every `match` "MUST be
  statically guaranteed to handle all possible values of the scrutinee
  type", and "well-typed programs do not encounter runtime match failure".
- `IO` has three constructors (§10.1). `Bind` cannot be matched by user
  code, so no set of constructor arms covers `IO`; only a wildcard does.
  The check accepts `Pure` and `Effect` as covering it.
- **It holds under either answer to the open question.** If `IO`'s
  constructors are not surface, the match is refused. If they are, the
  uncoverable constructor requires a wildcard. Acceptance followed by a
  run-time failure is neither.
- **Severity: an accepted program ends on a panic.** No memory hazard from
  this face; binding `Effect`'s field is ACT-1106's.
- **Age: not established.**

## Attribution: typecheck

- **In source.** The exhaustiveness check in
  `crates/cranelisp-typecheck/src/adt.rs` builds the set of constructors to
  cover from those not marked internal, so `Bind` is never required.
- **Control.** Omitting the `Effect` arm is refused and names `Effect`
  alone.
- **Refuted if** a type with no internal constructor shows the same
  acceptance.

## Routing

- **`qa` holds this action.**
- **`test`:** T-IO-MATCH, in the
  [S124 evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).
- **`design`(typecheck), then `dev`(typecheck):** the correction, after the
  user's answer on `IO`.

## Completion evidence

T-IO-MATCH is committed and observed RED on its no-panic clause, and passes
on the corrected build with its wildcard control unchanged.

## Narrowed after the ruling on `IO` (qa, 2026-11-22)

The user ruled `IO` opaque: no match on an IO value is accepted, with or
without a wildcard. T-IO-MATCH is accepted as committed (`e9a60317`): its
subject ends on `match failed`. Its clause is narrowed to refusal at compile
time in T-IO-OPAQUE, and its wildcard control becomes a subject (evidence
delta §14.3). Carried to the next sprint by the user's decision.
