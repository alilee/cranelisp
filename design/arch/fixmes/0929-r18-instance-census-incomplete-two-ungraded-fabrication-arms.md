---
number: 0929
target: /arch
filed_by: /qa
filed_at: 2026-07-27
sprint_filed: 119
refers_to: design/arch/safety-invariants.md §4;
  design/arch/concrete-boundary-type.md §3.1.1;
  crates/cranelisp-types/src/mono_expr.rs;
  tests/scripts/concrete_boundary_check.py
status: open
---

# R18: the one remaining fabricated concrete default

## Current state (verified 2026-11-27)

- Safety-register row R18 (no fabricated concreteness) is graded
  asserted-with-a-named-falsifier. Its detector is the source census
  `tests/concrete_boundary_census.rs` (T-NC2), which passes with both
  detection legs and a stale-entry leg.
- One fabrication remains and is the census's single allow-list entry,
  citing this filing:
  `crates/cranelisp-types/src/mono_expr.rs::lenient_from_expr`,
  `unwrap_or(ConcreteType::Int)` (`pub(crate)`).
- Every other site this filing listed is absent from source or a refusal.

## Remaining obligation

`arch` (types), with `dev`(backend) as the consumer, deletes the
placeholder as ruled in
[concrete boundary type](../concrete-boundary-type.md) §3.1.1. The same
change-set removes the allow-list entry; the census's stale-entry leg
fails if it stays.

## Closure

`lenient_from_expr` fabricates no type, the allow-list is empty, and R18
no longer names an allowed site.
