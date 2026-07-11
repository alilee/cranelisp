# stdlib/BACKLOG.md — Standard Library Request Backlog

A groomed, prioritized inventory of "missing library function" requests surfaced as
the language is exercised through testing, examples, the exemplar, the REPL, and
docs. Every row is a **library function or namespace we wish existed**, modeled on
the Clojure standard library (root `CLAUDE.md` design principle: "Follow the Clojure
standard library for function naming and design as much as possible"). Owned and
groomed by `/stdlib`.

## What this file IS and is NOT

This is **one of four channels**. Route a finding to the right one:

| Kind of finding | Example | Goes to |
|---|---|---|
| **Defect** — wrong output, crash, spec violation, `--run`/`--link`/REPL divergence | `(map f v)` drops the last element | A committed **failing, un-ignored test** with a `// spec:` annotation — **NOT this file**. (See root `CLAUDE.md` §"Usability Findings and Defects".) |
| **Language usability finding** — inference friction, unhelpful error message, a missing **primitive** or **special form**, ergonomics | trait resolution surprise; a needed codegen intrinsic | A **FIXME** in `design/arch/fixmes/NNNN-*.md` targeting the owning skill. |
| **Stdlib request** — a **library function / namespace** written in Cranelisp that you wish were there | "I keep hand-rolling `group-by`" | **THIS file.** |
| Something already planned | a module in `plan-stdlib.md` not yet built | Not a backlog row — it lives in `plan-stdlib.md` build order. |

The dividing line for this file vs. a usability FIXME: **can it be written in
Cranelisp from existing primitives + special forms?** If yes, it is a stdlib request
(here). If it needs a new compiler primitive, special form, or a language change, it
is a usability finding (FIXME).

## Ownership and flow

- **`/stdlib` owns and grooms this file.** No other skill edits `stdlib/`.
- **Capture flow.** Requests are surfaced by user-proxy skills (`/testing`,
  `/examples`, `/port`, `/repl`, `/docs`) while exercising the language. `/sprint`
  **batches** the surfaced requests and dispatches `/stdlib` to append + groom them
  here. `/sprint` and other skills do **not** edit this file directly.
- **Grooming.** `/stdlib` sets the Clojure analog + signature (keeps naming
  disciplined and rows directly actionable), assigns priority, and dedupes.
- **Pull into scope.** When `/sprint` plans a stdlib increment, it pulls
  high-priority `requested` rows into scope; `/stdlib` flips them to
  `in-increment (S<NN>)`, then `landed (S<NN>)` once shipped with self-tests.
- **Landed rows are kept for provenance** — moved to the "Landed" section below with
  the implementing sprint recorded.

## Priority scheme

Three levels, by how often the gap is hit and how much friction it causes:

- **P1** — surfaced repeatedly, or blocks idiomatic expression of a common pattern;
  pull into the next stdlib increment.
- **P2** — genuinely useful, surfaced at least once; schedule when convenient.
- **P3** — nice-to-have / completeness; batch opportunistically.

## Status values

`requested` → `in-increment (S<NN>)` → `landed (S<NN>)`

## Requests

| Function | Clojure analog + signature | Use-case that surfaced it | Priority | Status |
|---|---|---|---|---|
| _`group-by` (EXAMPLE ROW — format demo, not a real request)_ | `(group-by f coll)` → map of `(f x)` → vector of matching `x` | _Illustrative only: bucketing test fixtures by a key while exercising collections._ | P2 | requested |

_No real requests have been surfaced yet. The row above demonstrates the format;
replace or append below it as `/sprint` routes batched requests here._

## Landed

_(none yet — landed rows move here with their implementing sprint for provenance.)_
