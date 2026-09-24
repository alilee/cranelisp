---
number: 0903
target: /design (backend)
filed_by: /dev (backend)
filed_at: 2026-07-26
sprint_filed: 118
refers_to: design/backend/non-concrete-release-contract.md §2, §4, §7;
  crates/cranelisp-backend/src/compiler/fn_compiler.rs::emit_heap_binding_decs;
  crates/cranelisp-backend/src/compiler/rc_emission.rs::signature_heap_category;
  design/typecheck/non-concrete-producer-obligations.md;
  tests/fixtures/clif_baseline/MANIFEST.md
status: open
ruled_at: design/backend/non-concrete-release-contract.md (S119 Phase 3)
blocked_on: typecheck producer obligations for faces 2 and 3
---

# Retire the non-concrete release and retain arms for the whole measured class

## Current state (verified 2026-09-24)

- A frame-keyed narrowing of the release admission was implemented, measured
  (+16 corpus refusals, twice) and reverted. The measurement, the two
  escapee families and the ruling are canonical in
  [the non-concrete release contract](../../backend/non-concrete-release-contract.md)
  §2 and §4; its `/review` reject 4 forbids re-landing the frame key alone.
- Family 1 (synthetic accessors of a generic product) and family 2 (generic
  trait-method instances) are memory-unsafe, not merely leaky: an RC
  operation on a residual-`Var` word treats a scalar at or above
  `NULLARY_TAG_THRESHOLD` as a pointer. The family-2 runtime guard is the
  1023/1024 boundary pair in `tests/trait_scrutinee_scalar_payload_0916.rs`,
  which this filing now carries (FIXME 0916 retired into it).
- `emit_heap_binding_decs` still carries the type-keyed shallow-dec arm, and
  `signature_heap_category` still maps `Err` to `Mixed`.

## Remaining obligation

The contract's open backend work, in its order (§7.7):

1. the refusal frame (§7.2, shared with FIXME 0915);
2. the armed category census with both detection legs (§7.3);
3. the R-1 structural close (§7.4): constructor field types become an
   instantiation fact, `Err ⇒ Mixed` becomes a located error, and the
   `emit_heap_binding_decs` shallow-dec arm is deleted rather than re-keyed —
   census-gated on zero licences in the `Ctor`, `Accessor` and `TraitMethod`
   partitions.

Faces 2 and 3 additionally need typecheck's producer obligations
(monomorphised accessors and trait-method instances).

The structural close must carry a scoped, attributed re-baseline of the
`f4_sudoku` `user::Grid.cells` accessor frame as its static witness: the S118
golden blessed a shallower release there. That frame is uncalled in the
corpus and exemplar, so it is not a runtime witness.

## Closure

The shallow-dec arm and the `Err ⇒ Mixed` arm are gone, the census reads zero
in the three partitions, and the `Grid.cells` re-baseline is recorded.
