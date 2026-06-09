---
number: 0302
target: /int
filed_by: /qa
filed_at: 2026-06-09
sprint_filed: 77
refers_to: tests/repl_introspection.rs::data_constructor_product_no_dot_notation_display (FAILING), repl/spec.md §1.5 (line 309 — single-ctor product value display), tests/plan/ledger.md (RT1→layered)
status: open
---

# Single-constructor product value display drops the field values (`:user/Point Point` not `(Point 3 4)`)

## Issue

Discovered during S77 W-Fix RT1 triage. The test
`data_constructor_product_no_dot_notation_display` failed FIRST on RT1 (bare
`:Int` in the deftype fields — fixed by adding `(import [primitives [Int]])`).
With RT1 cleared the test STILL FAILS on a genuine value-DISPLAY defect:

A single-constructor product type whose constructor name matches the type name
MUST display its value as `(Point 3 4)` per repl/spec.md §1.5 (line 309:
"Data constructor (single-ctor, name matches type) → `(Ctor field1 field2 ...)`,
e.g. `(Point 3 4)`"). Observed (fresh tmpdir, current binary):

```
user> (deftype Point [:Int x :Int y])
user> (Point 3 4)
:user/Point Point
```

The value position shows only the constructor name `Point` — the field values
`3 4` are dropped, and there are no surrounding parens. Verified the formatter
CAN render fields: the sum-ctor path `(Some 42)` correctly displays
`(Option.Some 42)` (test `data_constructor_applied_dot_notation_display`
passes). The defect is specific to the single-ctor product (name==type) path
— it falls into a nullary-like rendering that omits the fields.

## Proposed resolution

In the REPL value formatter, the single-constructor product (ctor name == type
name) case must render `(Ctor field1 field2 ...)` with the field values
recursively formatted — the same field-walk the multi-ctor `(Type.Ctor ...)`
path uses, but WITHOUT the `Type.` dot prefix (per §1.5 line 309). Currently
this case appears to render only the constructor name.

## Operational implication / Context

S77 (RT1 layered — surfaced under W-Fix, resolution is a code fix, not a
fixture fix). Owner: /dev int (REPL value display formatting). The test
`data_constructor_product_no_dot_notation_display` is left FAILING-NOT-IGNORED
with the RT1 fixture part fixed; it now fails purely on this display defect and
is the durable record + regression guard.
