---
number: 0569
target: /dev
filed_by: /repl
filed_at: 2026-07-12
sprint_filed: 108
refers_to: `/search` result-row rendering (§17.19.2) — the `:Type` column for a
  MACRO entry; the macro symbol-table entry's type-sig field (a placeholder).
  Reproduced at S108 Inc3 6a assessment.
status: open
---

# `/search` shows a bogus `:primitives/Int` type annotation for macro rows

## Issue

Macros surfaced by `/search` render a meaningless `:primitives/Int` type column:

```
> /search when
:primitives/Int when
  in control   — already in scope — no import needed
> /search cond
:primitives/Int cond
> /search do
:primitives/Int do
```

Every macro (`when`, `cond`, `do`, …) shows `:primitives/Int` — a placeholder
type that is simply wrong for a macro. Contrast bare-symbol lookup, which is
correct:

```
> when
:control/when ; defmacro - Conditional with implicit None else branch
```

So the same entry renders correctly through the introspection path but leaks a
bogus scalar type through the `/search` row path.

## Assessment (severity: low / cosmetic — but a spec-conformance/display defect)

`:primitives/Int` for a macro violates the self-documenting-REPL contract: the
type column is supposed to help a user judge what a name is, and here it
actively misinforms (a macro is not an `Int`). Bare lookup already knows to show
`; defmacro` instead of a type, so the correct information is available at the
entry — the `/search` row renderer just isn't consulting the classification.

Pre-existing (the macro placeholder type predates the S108 Inc3 importable-set
work), surfaced by exercising the freshly-changed `/search` surface.

## Proposed resolution (for /dev + a spec touch by /repl)

Two coupled parts:

1. **/dev** — the `/search` row renderer should, for a macro entry, render the
   classification (`; defmacro`) in place of — or instead of a bogus — `:Type`
   column, mirroring what bare-symbol lookup / `/info` already do. Do not print
   `:primitives/Int` for an entry that carries no meaningful function type.
2. **/repl (repl/spec.md §17.19.2)** — the search-row spec does not currently
   pin what a MACRO row's `:Type` column shows. `/repl` will elaborate §17.19.2
   with the macro-row form once the intended shape is agreed (classification
   drawer vs omitted type). Filed here so the display fix and the spec pin land
   together.

## Notes

- Likely warrants a narrow `/testing` repro (a macro's `/search` row must not
  show a scalar type) since it is output that does not match the intended
  display — recommend `/qa` fold it into the S108 `/search` coverage.
- Colour-off byte output is the assertable seam (`:primitives/Int when` vs the
  fixed form).
