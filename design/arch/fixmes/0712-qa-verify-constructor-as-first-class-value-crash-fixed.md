---
number: 0712
target: /qa
filed_by: /docs
filed_at: 2026-07-20
sprint_filed: 114
refers_to: user/guide/concurrency.md §"Known rough edges" (bare-constructor-as-value crash) vs S114 fn-as-value carrier work + residual 0705
status: open
---

# Verify the "bare ADT constructor as a first-class value crashes" rough-edge is fixed, and land a regression test so /docs can retire the workaround

## Severity
Important (defect-shaped doc claim — a documented crash that no longer reproduces
in probing)

## Issue

`user/guide/concurrency.md` §"Known rough edges" (lines ~340-342) warns:

> **A bare ADT constructor used as a first-class function value crashes.** Wrap it
> in a lambda: write `(fn [x] (Some x))`, not a bare `Some`, when passing a
> constructor to a higher-order function. (This is why `timeout`'s definition
> wraps `Some`.)

This **contradicts** `user/guide/constructors.md` (line 28: "Like any function it
is first-class — you can pass it as an argument or bind it to a variable") and, at
HEAD (`3cdd285c`), contradicts observed behaviour. REPL probes (clean dir, lib
found) all succeed — no crash:

- `(let [f Bx] (f 5))` → `(Box.Bx 5)`
- `(map-list Bx (Cons 1 (Cons 2 Nil)))` → maps correctly
- `(map-list Some (Cons 1 (Cons 2 Nil)))` → `(List.Cons (Option.Some 1) …)` — the
  exact "bare constructor to a higher-order function" shape the hedge warns about
- a user-defined HOF taking a bare constructor and applying it → works

S114's fn-as-value carrier / GOT-slot work is the plausible fix. **But** S114 left
a residual `0705` (AutoCurry-over-local target reaches codegen with no GOT-slot
carrier — S115-attributed), so *some* fn-as-value shape still crashes. The
constructor-specific shape appears fixed; the boundary between "fixed" and "still
0705" needs pinning before /docs edits.

## What /docs needs (defect-handoff protocol)

Per root CLAUDE.md §"Usability Findings and Defects", a doc claim that contradicts
reality is not closed on prose alone. Before /docs removes or narrows the hedge:

1. **Confirm** the bare-constructor-as-first-class-value shape works end-to-end
   under `--run` and `--link` (not just REPL — REPL/--run divergence is the
   red-flag class). /docs probes were REPL-only (the `--run` probes hit the
   free-standing-examples / lib-path constraint, not a compiler result).
2. **Land a narrow regression test** proving the shape works (constructor passed
   to a HOF; constructor bound then applied), annotated `// spec:`/`// docs:`.
3. Return the **precise still-broken boundary** (if any) — e.g. "auto-curry of a
   *local fn value* still aborts (0705), but a *constructor* value does not" — so
   /docs can either delete the rough-edge outright or narrow it to the surviving
   shape and cross-link 0705.

## Priority
Medium. Blocks the concurrency.md rough-edge edit in Phase 6b; that edit carries to
whichever sprint the verification lands in if it slips past 6b. (The second
concurrency rough edge — `race` with an inline `bind`-lambda — is a separate
lenient/race concern, out of this FIXME's scope.)
