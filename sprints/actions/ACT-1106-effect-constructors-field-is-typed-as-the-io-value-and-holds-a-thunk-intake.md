---
id: ACT-1106
title: The `Effect` constructor's field is typed as the IO's value and treated by the runtime as a thunk, so constructing or matching it ends the process on a signal
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-22
refers_to:
  - spec/10-io.md §10.1
  - spec/10-io.md §10.1.3
  - spec/03-types.md §3.2.3
  - src/bootstrap.rs
  - crates/cranelisp-intrinsics/src/io.rs
---

## Origin

`sprint`, by hand while answering a user question. `qa` took it in on
2026-11-22.

**What `IO` should be as a language type, and whether its constructors are
surface at all, is open with the user. This filing does not settle it.**

## Observation

`qa`, 2026-11-22, the debug binary built from `11ea995e` (no compiler source
has changed since), no prelude, scratch directories since removed. REPL
rows use `--no-color --no-agent`.

**Constructing.**

| Program | Observed |
|---|---|
| `(primitives/Effect 5)` at the REPL | `Executing IO…`, then **signal 11** |
| The same after `(import [primitives [Effect]])`, bare | **Signal 11** |
| `(primitives/Effect "abc")` at the REPL | **Signal 11** |
| `(let [e (primitives/Effect 5)] 7)` at the REPL | **Signal 11,** with no output: the node is never forced |
| `(defn main [] (primitives/Effect 5))` under `--run`, and linked | **Signal 11** in both |
| `(defn main [] (let [e (primitives/Effect 5)] (primitives/Pure 7)))` under `--run` | **Signal 11** |
| `/type (primitives/Effect 5)` | `:(primitives/IO primitives/Int)`; the session continues |
| `(defn mk [] (primitives/Effect 5))`, not called | Accepted; the session continues |
| Control: `(primitives/Pure 5)` at the REPL | `:primitives/Int 5` |

**Matching.** With
`(defn peek [io] (match io [(primitives/Pure x) x (primitives/Effect t) t]))`,
accepted at `(Fn [(primitives/IO a)] a)`, and the `test-capture` platform:

| Turn | Observed |
|---|---|
| `(peek (primitives/Pure 7))` | 7 |
| `(peek (print "MARK"))` | **`:primitives/Int 187651193746496`:** the thunk's address, as an `Int`. The effect is not performed |
| `(primitives/str-len (peek (read-line)))` | **Signal 7** (bus error): the thunk's address read as a `String` |
| `(peek (pure-int))`, a platform result that is a `Pure` node | 121 |

## Classification: a defect, memory-unsafe

- **Against the specification as written.** [§10.1](../../spec/10-io.md)
  declares `(Effect [:a thunk])` among `IO`'s constructors and marks only
  `Bind` internal; §3.2.3 and §10.1.1 call `IO` an ordinary ADT. So
  `(primitives/Effect 5)` and the `peek` function are well-typed programs.
  A well-typed program ends on a signal, or yields an address as an `Int`.
- **The declaration contradicts itself.** The same line types the field as
  `a` and describes it as an opaque thunk pointer; §10.1.3 gives it a boxed
  closure. A field cannot be both the IO's value and a closure.
- **Severity: memory-unsafe.** A wild pointer is called or freed on
  construction, and a closure's address is read at another type on a
  match. Deterministic, in every mode.
- **What the right outcome is depends on the open question:** refuse the
  constructor to user code, give its field an opaque type, or remove the
  constructors from the surface. Under each, what happens today is wrong.
- **Age: not established.** `qa` ran no earlier tree.

## Attribution: the requirement, as realised in `src/bootstrap.rs`

- **In source.** The bootstrap registers `Effect` as a public constructor
  whose one field has the type parameter's type, as §10.1 writes it. The
  runtime forces and releases that field as a closure
  (`crates/cranelisp-intrinsics/src/io.rs`).
- **Control.** `Pure`, registered beside it with the same field type, holds
  a value of that type, and both rows with `Pure` behave.
- **Where it entered: the specification's declaration.** The realisation
  follows it. The correction is a requirement change first.
- **Refuted if** a constructed `Effect` whose field is a real thunk of the
  right type also ends on a signal; `qa` knows no way to write one.

## Routing

- **`qa` holds this action.**
- **`spec`, with the user's answer:** what `Effect` is to user code.
- **`test`:** T-EFFECT-FIELD, in the
  [S124 evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).
- **`arch`, then `design` and `dev`:** the correction, after the answer.

## Completion evidence

T-EFFECT-FIELD is committed and observed RED on its no-signal clauses.
`qa` narrows the cell to the recorded answer, and it passes on the
corrected build with its `Pure` controls unchanged.

## Narrowed after the ruling on `IO` (qa, 2026-11-22)

The user ruled `IO` opaque: `Effect` is neither constructible nor matchable.
T-EFFECT-FIELD is accepted as committed (`e9a60317`): five subjects end on a
signal and four controls pass. Its clause is narrowed from "no signal" to
"refused with a diagnostic" in T-IO-OPAQUE (evidence delta §14.3). Carried
to the next sprint by the user's decision.
