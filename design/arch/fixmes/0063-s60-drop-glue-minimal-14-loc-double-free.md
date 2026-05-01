---
number: 0063
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint60_reduction.rs:542
status: open
migrated_from_inline: true
split_from_cluster: 0023
---

# 0063 — S60 Round 2 MINIMAL (14 LOC) drop-glue / auto-curry double-free

## Issue

S60 Round 2 MINIMAL (14 LOC). Drop-glue / auto-curry closure captures the ADT `g` twice (once per `cell-at` call in `walk`); when both closures are RC-dec'd, the captured `g`'s RC reaches zero before `walk`'s scope cleanup, causing `heap_dealloc` to be invoked on `g`'s inner Vec twice (or on `g` itself). Confirmed against CLIF (`CRANELISP_CODEGEN_DUMP=*`): `walk`'s block1 allocates two 24-byte heap regions, stores two fn pointers + the captured `v1` (g), bumps g's RC twice, calls `fn3(closure)` then `fn8(closure)`, then on return decrements each closure's RC to zero and runs drop glue. Root cause is in either (a) `emit_consuming_caller_rc` for defn calls that get auto-curried despite both args present, or (b) closure env RC accounting for captures of ADT-wrapped Vec. Not fixed in this task — reduction only.

## Test name

`s60_drop_glue_minimal_14_loc_no_crash`

## Test purpose

spec: spec/12-runtime.md §12.4 — RC inc/dec must balance; drop glue must not dec a captured value that the caller also dec's. Reduces a 14-LOC single file containing a 1-field Grid ADT wrapping a Vec, a `cell-at` helper that match-unpacks the ADT, and a `walk` caller that invokes `cell-at` twice on the same argument.

## Source location

`tests/sprint60_reduction.rs:542`

## Cluster context

This entry was split from cluster 0023 (S60 Round 2 drop-glue / auto-curry minimal repro). Sibling entry: 0064 (committed duplicate regression guard with identical source).

## Proposed resolution

`/backend` audits `emit_consuming_caller_rc` and closure-env RC accounting for captures of ADT-wrapped Vec. Both reduction tests must pass without crashing after the fix.
