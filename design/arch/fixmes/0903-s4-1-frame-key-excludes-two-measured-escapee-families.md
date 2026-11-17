---
number: 0903
target: /design (backend)
filed_by: /dev (backend)
filed_at: 2026-07-26
sprint_filed: 118
refers_to: design/backend/non-concrete-release-contract.md §2, §4, §7;
  crates/cranelisp-backend/src/compiler/fn_compiler.rs::emit_release;
  crates/cranelisp-backend/src/compiler/fn_compiler.rs::emit_dup;
  crates/cranelisp-backend/src/compiler/rc_emission.rs::signature_heap_category;
  design/typecheck/non-concrete-producer-obligations.md;
  tests/fixtures/clif_baseline/MANIFEST.md
status: open
ruled_at: design/backend/non-concrete-release-contract.md (S119 Phase 3)
blocked_on: the census readings (S124), then the producer corrections they attribute — typecheck accessor monomorphisation and ACT-1034 — and ACT-1050's producer
---

# Retire the non-concrete release and retain arms for the whole measured class

## Current state (verified 2026-11-15, after the U′ cutover)

`arch` read the S123 W2 U′ cutover in the uncommitted working tree and the W2
evidence in `.local/s123-w2/`. **U′ did not resolve this filing**, and it was
not designed to. This is a category fault: an RC operation on a word that may
not be a reference at all. U′ changes counting only, and
[uniform counting](../../backend/uniform-counting.md) §2 lists "category before
operation" as unchanged. The S123 carry's expectation that option 2 resolves
the leaks does not apply here.

- The type-keyed shallow-dec arm still stands. It moved from the deleted
  `emit_heap_binding_decs` to `FnCompiler::emit_release` (`fn_compiler.rs`).
  A binding whose type fails `ConcreteType::from_type` takes a guarded shallow
  dec there.
- `signature_heap_category` still maps `Err` to `Mixed`, so
  `FnCompiler::emit_dup` emits a guarded increment on the same words.
- U′ widens the reach of both arms. Every binder drop at its death point and
  every duplicate now passes through these two functions, so a residual-typed
  binder in a family 1 or family 2 frame meets the arms at each such point. The
  pre-U′ seams were the scope-exit and tail flushes plus the consuming argument
  paths. Traffic has not been re-measured since S119.
- Families 1 (synthetic accessors of a generic product) and 2 (generic
  trait-method instances) are memory-unsafe, not merely leaky. An RC
  operation on a residual-`Var` word treats a scalar at or above
  `NULLARY_TAG_THRESHOLD` as a pointer
  ([release contract](../../backend/non-concrete-release-contract.md) §2.4,
  §4.3).
- The family 2 runtime guard is the 1023/1024 boundary pair in
  `tests/trait_scrutinee_scalar_payload_0916.rs`. It was not part of the W2
  cutover evidence (72 targeted cells), so its state on the U′ build is
  unmeasured.
- The frame-key narrowing remains forbidden: it was measured at +16 corpus
  refusals and reverted (contract §2.6 and §8).
- This filing subsumes FIXME 0891 (face 1, a constructor template's own
  residual parameter), deleted at S123 W2; Git history holds it. Verified
  2026-11-16: face 1 is structural. Codegen targets are `Life::Concrete` body
  arms (`crates/cranelisp-backend/src/lib.rs`, target collection), their
  parameter types come from the arm's scheme, and a `Concrete` arm requires a
  concrete scheme (`SlotMintError::NotConcrete` at minting,
  `CallableSlot::rebind` at reuse, `LifecycleError::NonConcreteSlot` in
  `SymbolTable::validate_lifecycle`, which the cache load runs). So no
  constructor frame reaches `emit_release` with a residual-typed parameter.
  The residual reaches 0903's families through the constructor declaration
  channel instead (contract §7.4). 0891's two tails are below: the arm deletion
  (item 5), and the `Ctor` census partition, whose zero reading reconciles with
  FIXME 0931's constructor witness.

## Remaining obligation

Scheduled in S124; designed in Phase 3 and not in source at `4b58ab93`. The
order is the contract's §7.7 and is not restated here;
the cross-surface rules it must respect are
[the S124 close](../concrete-boundary-type.md#312-the-s124-close--no-rc-operation-on-a-word-without-a-category).
What this filing still owes:

1. the armed category census over three arms (retain, release, absent type),
   with both detection legs for each (§7.3);
2. the constructor field channel (§7.4 step 1, S124 packet row D1): field
   types become an instantiation fact;
3. the producer corrections the census attributes
   ([the S124 close](../concrete-boundary-type.md#312-the-s124-close--no-rc-operation-on-a-word-without-a-category),
   attribution): typecheck designs ACT-1034 now and predicts no other traffic of
   its own, so the accessor correction and ACT-1050's producer are scoped from
   the readings and `qa`'s reductions;
4. the census reading zero in **every** partition and arm, `Plain` included;
5. the arm deletion (§7.4 step 2): binder types are concrete, and the retain,
   release and absent-type arms are deleted rather than re-keyed.

The refusal frame (§7.2, FIXME 0915) is no longer a precondition: it carries
past S124 by the user's ruling, and the close adds a refusal only where the
census measured zero traffic.

No `Grid.cells` re-baseline is owed. An accessor of a generic product is a
template, compiled only at the instantiations a program demands; `f4_sudoku`
never calls `cells`, and `tests/fixtures/clif_baseline/golden/f4_sudoku.clif`
carries no such frame (read 2026-11-18). The census read zero residual and
absent field reads, so the field-channel change-set (item 2) lands directly
after the census (contract §7.3, §7.4).

Register rows: [safety invariants](../safety-invariants.md) R15, R17 and R18.

## Closure

The shallow-dec arm, the `Err ⇒ Mixed` arm and the absent-type early returns
are gone, and the census reads zero in every partition and arm.
