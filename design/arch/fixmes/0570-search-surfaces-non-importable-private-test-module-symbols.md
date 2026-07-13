---
number: 0570
target: /spec
filed_by: /repl
filed_at: 2026-07-12
sprint_filed: 108
refers_to: which module symbols are eligible to appear as importable `/search`
  rows (repl/spec.md §17.19.2) — specifically test/private modules such as
  `collections.vec.test`. Whether such modules are user-importable is a spec
  question. Reproduced post-S108 via `/search count`.
status: open
---

# `/search` surfaces symbols from private/test modules that are not importable

## Issue

`/search count` returns rows for symbols living in a `.test` module, each
advertising an `(import …)` hint:

```
> /search count
:(Fn [(primitives/Vec a)] primitives/Int) count
  in collections.vec   — (import [collections.vec [count]])
:(Fn [] (primitives/Option primitives/String)) test-count
  in collections.vec.test   — (import [collections.vec.test [test-count]])
:(Fn [] (primitives/Option primitives/String)) test-range-count
  in collections.vec.test   — (import [collections.vec.test [test-range-count]])
  …
```

`test-count` / `test-range-count` live in `collections.vec.test` — apparently a
test module — yet `/search` presents them as ordinary importable results with an
`(import [collections.vec.test [test-count]])` hint. If those modules are not
meant to be user-importable, `/search` is advertising an invalid import path.

## Assessment (severity: medium — search-contract correctness gated on a spec ambiguity)

The self-documenting REPL's `/search` should only offer importable symbols (or
mark non-importable ones as such). But the root question is **normative and
currently unpinned**: is `collections.vec.test` a private module? What makes a
module or symbol non-importable — a naming convention (`.test` suffix), an
explicit privacy marker, or nothing at all (everything importable)? The spec does
not currently define module visibility/privacy for the import + search surfaces.
This is a question for the **user to arbitrate** (recorded by `/spec`), not one
`/sprint` or `/dev` should settle by fiat — the display fix depends on the answer.

## Proposed resolution (spec first, then display)

Two coupled parts:

1. **/spec + user** — settle the visibility rule: what makes a module/symbol
   non-importable (convention like `.test`, an explicit marker, or nothing), and
   whether `/search` filters to importable symbols only. Pin it in the module /
   import spec.
2. **Once settled** — `/dev` filters the search index (or `/repl` marks
   non-importable rows), and `repl/spec.md §17.19.2` pins how `/search` treats
   non-importable symbols.

## Notes

- Related to **0571** (FQ-symbol reference resolution) — both touch module
  loading/visibility from the REPL.
- Warrants a narrow `/testing` repro once the rule is set: `/search` must not
  advertise an import path that then fails. Colour-off row bytes are the
  assertable seam.
