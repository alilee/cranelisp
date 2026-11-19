---
id: ACT-1089
title: "`/type` given a definition commits it to the live session without code; the next call ends the process on a signal"
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-20
refers_to:
  - repl/spec/03-slash-commands.md
  - repl/spec/14-file-watching.md §14.5
  - repl/spec/18-redefinition.md §18
  - design/int/result-owner.md §4.3
  - src/repl/commands.rs::typecheck_only
---

## Observation

`qa`, 2026-11-20, `target/debug/cranelisp` built from `4cef5784`, each
session in its own scratch directory, input piped. `dev`(`src/`) reported
the first two rows with `793af750`.

| Session | Observed |
|---|---|
| `"abc"`, then `/type (defn q [:Int n] n)` | `:primitives/String`, the previous expression's type |
| `/type (defn q [:Int n] n)` with no earlier expression | `` `/type` found no `__expr` to read a type from ``; `/list` then shows `q` and `/sig q` its signature |
| The same, then `(q 3)` | **The process ends on signal 11** (exit 139) |
| `(defn q [:Int n] n)`, `(q 3)` gives 3, `/type (defn q [:Int n] (add-i64 n 100))`, `(q 3)` | **Signal 11** |
| `(defn q [:Int n] n)`, `/type (defn q [:Int n :Int m] (add-i64 n m))`, `/sig q`, `(q 3)` | `/sig` shows two parameters; `(q 3)` prints a closure |
| `/type (deftype T A B)`, `/list`, `A` | `T`, `T.A` and `T.B` are listed and `A` resolves to the constructor |
| `/type (defmacro mm [x] x)`, `/list` | The error of row 2; nothing is listed |
| `(defn q …)`, `/type (defn q … other body)`, `/quit`; a new session | `user.cl` holds the first `q`, and `(q 3)` gives 3 |

Control: `/type (add-i64 1 2)` prints `:primitives/Int` and leaves the
session as it was (`tests/repl_introspection.rs`).

## Classification: a defect, memory-unsafe

`/type` is specified as "show type without evaluating" (REPL §3) and as a
compile-only diagnostic that stays available in a locked session (REPL
§14.5). Whatever `/type` should print for a definition, three faces are
defects under any answer:

1. **Signal 11** on the next call of a name `/type` was given.
2. **A working definition is replaced** in the live session, with no
   definition confirmation and outside the commit gate of REPL §18. The
   backing file is not changed, so the session and its source disagree.
3. **A stale type**: the printed type belongs to an earlier input.

It predates S124. `typecheck_only` has committed its checked cluster to the
live table since at least S110 (`3944a4bc`, by blame); `793af750` changed only
the text of row 2.

## Attribution: the binary

`src/repl/commands.rs::typecheck_only` checks its input through the live
cluster context and reads `__expr` back from the live table.

- A definition is checked and committed like any cluster, so its entry and
  slot claim are live and no code is compiled for it. That is read from
  source; the empty slot is not observed at its seam.
- With no `__expr` in the input, the read returns the previous input's
  `__expr`, or nothing.
- **Control:** an expression argument differs only in being wrapped as
  `__expr`, and leaves every other entry alone.
- **Refuted if** the entry `/type` leaves holds compiled code.

[Result owner §4.3](../../design/int/result-owner.md) states that `__expr`
is absent after a clean check "only through an invariant violation" and that
"the only face is a wrong display". Both are false for a definition
argument. `design`(int) owns that text.

## Open requirement question, for the user through `spec`

REPL §3 gives `/type` an `<expr>` and does not say what a definition form is
to it. The question:

> When `/type` is given a definition form (`defn`, `deftype`, `deftrait`,
> `impl`, `defmacro`, `import` or `export`) and not an expression, does it
> (a) refuse the input with a located diagnostic saying `/type` takes an
> expression, or (b) report the type the definition would have if entered,
> for example the line its confirmation would print?

Both answers leave the session unchanged. If the user intends `/type` to
define what it is given, that is a third answer and REPRO-1089's clauses
change with it. `qa` does not choose.

Not probed: `/type` with a definition in a locked session, where REPL §14.5
admits `/type` and refuses every definition; `/type` with `deftrait`,
`impl`, `import` or `export`.

## Evidence allocation

**REPRO-1089**, allocated to `test` in the
[evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-returned-to-test).
Its clauses hold under answers (a) and (b) and pin no response text.

## Completion evidence

REPRO-1089's subjects fail as allocated, then pass with the control
unchanged. The user's answer is scribed in REPL §3, and `qa` allocates the
clause for the printed response.
