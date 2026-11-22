---
id: ACT-1089
title: "`/type` given a definition form commits it to the live session without code and reports no error; the next call ends the process on a signal"
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

## Ruled, 2026-11-20

The user ruled answer (b): `/type` given a definition form reports its type
and defines nothing in the session
([REPL §3.1](../../repl/spec/03-slash-commands.md#31-command-inventory),
`467e6a97`). The user also ruled that the defect is carried past S124 on its
reproductions (`sprints/SPRINT.md`, Notes).

The user ruled again on 2026-11-20: "type should not evaluate a non-pure
form" (REPL §3.1, `21101921`).

- **Open with the user as S124-Q10:** what `/type` reports for a form that
  has no value type, such as `deftype` and `defmacro`
  ([spec appendix D](../../spec/appendix-d-open-questions.md)). No allocated
  clause reads that report.
- **Not probed:** `/type` with a definition in a locked session, where REPL
  §14.5 admits `/type` and refuses every definition; `/type` with `export`.

## Forms other than `defn`

`qa`, 2026-11-20, the debug binary built from `39db1bb1` (source unchanged
to `21101921`), no prelude, each session in its own scratch directory.

| Given to `/type` | Then | Observed |
|---|---|---|
| `(impl Sz T (defn sz [self] 7))`, after `Sz` and `T` are defined | `(sz A)` | **The process ends on signal 11**, 4 of 4. Without the `/type` line the call is refused: `no impl of trait user/Sz for type user/T` |
| `(deftrait Sz (sz [self] Int))` | `/list` | `Sz` is listed |
| `(deftype T A B)` | `/list`, `A` | Row 6 above, re-read. A new session does not have `T`: nothing reached `user.cl` |
| `(defmacro mm [x] x)` | `(mm 3)` | Refused as undefined |
| `(import [primitives [add-i64]])` | `(add-i64 1 2)` | Refused as undefined: the import was read as an expression and not run |
| `(print "MARK")`, an `IO` expression | — | `:(primitives/IO primitives/Int)`; `MARK` is not printed. Entered without `/type`, it prints |

- **The `impl` row is a fourth memory-unsafe subject** of the same
  mechanism: an implementation committed with no code.
- **`deftype`, `deftrait` and `impl` are committed as `defn` is.** A
  correction that special-cases `defn` leaves those three rows failing.
- **An `IO` expression conforms.** The nonconformance against the new
  sentence is the committed forms.

## Evidence allocation

**REPRO-1089** is committed (`14341a53`): four subjects fail on their
assertions and the expression control passes, as read at `ee65d9aa`.
**T-TYPE-DEFN** is committed (`28176b57`), RED. **T-TYPE-PURE** covers the
rows above and is allocated to `test` in the
[evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).
**T-TYPE-NONVALUE**, the report for a non-value form, is held on S124-Q10.

## Completion evidence

REPRO-1089's subjects, T-TYPE-DEFN and T-TYPE-PURE pass with their controls
unchanged. `qa` restores the REPL §3.1 bands.

## Evidence state (qa, 2026-11-20, `b72742f7`)

T-TYPE-PURE is committed (`ea6778aa`, `c4282cb5`) and accepted: the `impl`
cell fails at signal 11, the `deftype` and `deftrait` cells on the `/list`
clause, and the three guards pass. Eight cells fail on this action.

## Ruled finally, 2026-11-20: a definition form is an error

The user closed S124-Q10: "I think it should error - \"definition form has no
type\"". [REPL §3.1](../../repl/spec/03-slash-commands.md#31-command-inventory)
(`39be7cfe`) now requires `/type` given a definition form to report an error,
evaluate nothing and define nothing. The definition forms are those of
[language §5.14](../../spec/05-definitions.md#514-summary-of-top-level-forms).
The message's wording is not prescribed. **The earlier ruling above, that
`/type` reports the definition's type, is withdrawn,** and with it the fifth
face ("the reported type is not the definition's").

`qa`, 2026-11-20, the debug binary built from `3c5e41ca`, no prelude:

| Given to `/type` | With no earlier expression | After the turn `"abc"` |
|---|---|---|
| `defn`, `defn-`, `deftype`, `deftrait`, `impl` | An error line (`found no __expr`); **the form is committed** | **`:primitives/String`, no error;** the form is committed |
| `defmacro` | An error line; nothing defined | not run |
| `import`, `export`, `mod`, `mod-`, `platform` | An error line (`undefined variable: import`, and so on); no effect | not run |
| `(const x 1)`, with `const` a session macro | An error line (`undefined variable: const`); nothing defined | the same |

- **Two faces against the final text.** The form is committed (the faces
  above), and after any expression the query reports that expression's type
  where an error is required.
- **The error printed with no earlier expression is an accident of the
  missing result,** so a cell that requires the error is discriminating only
  after an expression.
- **`const` and `def` are prelude macros** (§5.14). `/type` does not expand
  macros at all, which is a separate defect
  ([ACT-1099](ACT-1099-type-command-refuses-an-expression-that-uses-a-macro-intake.md)).
  No stdlib-free cell covers them as definition forms.

## Evidence allocation after the final ruling

- **REPRO-1089's four subjects stand.** They assert that nothing is defined
  and that no stale type is printed, which the final text keeps.
- **T-TYPE-DEFN is withdrawn.**
  `repl_introspection::s124_1089_definition_reports_its_function_type`
  asserts the withdrawn rule and would fail on a conforming build. T-TYPE-ERR
  replaces it.
- **T-TYPE-NONVALUE is released into T-TYPE-ERR:** the report for every
  definition form is an error.
- **T-TYPE-PURE stands unchanged.** No clause of it reads the report.
- T-TYPE-ERR is in the
  [evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).

## Completion evidence (replaces the two statements above)

REPRO-1089's four subjects, T-TYPE-PURE and T-TYPE-ERR pass with their
controls unchanged. `qa` restores the REPL §3.1 bands.

## `defmacro` joins the stale-answer face (qa, 2026-11-20, `121c5c9e`)

`qa` expected `/type (defmacro mm [x] x)` to report an error after an
expression and had not run it. It prints the earlier expression's type, as
the four defining forms do; the macro is still not defined. `test` found it
when the guard cell arrived RED. Twelve cells fail on this action: four of
REPRO-1089, three of T-TYPE-PURE, the four T-TYPE-ERR subjects and the
T-TYPE-ERR guard cell. `test` splits `defmacro` out of the guard cell
(evidence delta §14.3).

## A face on an ordinary expression (qa, 2026-11-22)

Found while probing `macros/sconcat`. The debug binary built from `11ea995e`,
at the REPL, no prelude unless stated:

| Session | Observed |
|---|---|
| `/type (primitives/Some 1)`, then `(primitives/Some 1)` | The type, then **signal 11** |
| `/type (primitives/Some 1)`, then `(primitives/Some 2)` | **Signal 11** |
| `/type (primitives/Some 1)`, `(primitives/add-i64 1 2)`, `(primitives/Some 1)` | The type, 3, then **signal 11** |
| `/type (primitives/Pair 1 2)`, then the same expression | **Signal 11** |
| `(deftype (Box a) (Mk [:a v]))`, `/type (Mk 1)`, `(Mk 1)` | **Signal 11** |
| `/type (macros/SCons (macros/SexpInt 1) macros/SNil)`, then the same | **Signal 11** |
| The first row with the standard-library prelude and bare `Some` | **Signal 11** |
| Control: `(primitives/Some 1)` first, then `/type` of it, then it again | The value, the type, the value |
| Control: `/type "abc"` then `"abc"`; `/type [1 2]` then `[1 2]`; `/type Red` then `Red` for a type with no parameter | Each prints its value |

- **`/type` given an expression is the documented use,** and REPL §3.1
  requires it to change nothing. Here it makes a later evaluation end the
  process.
- **The shape.** The expression applies a constructor of a parametric
  type at a concrete type that the session has not yet used. Evaluating
  first makes the later query harmless.
- **Mechanism, by control and consistent with this filing's attribution:**
  the query commits the constructor's instance to the live table with no
  code, and the next use calls it. `qa` did not observe the empty slot.
- **The committed expression control does not reach it:** it queries a
  call of a monomorphic function.
- **This widens what the user's carry decision covers.** The decision was
  taken on the definition-form faces.

T-TYPE-EXPR is allocated in the
[evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).
