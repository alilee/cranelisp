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
blocked_on: typecheck producer obligations for faces 2 and 3
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
- `test`'s U′ golden-CLIF re-capture (W2 C-6, C-7) changes every fixture. It
  does not supply the scoped `Grid.cells` re-baseline below, because the arm it
  would witness still stands.
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
  (item 3), and the `Ctor` census partition, whose zero reading reconciles with
  FIXME 0931's constructor witness.

## Remaining obligation

The contract's open backend work, in its order (§7.7):

1. the refusal frame (§7.2, shared with FIXME 0915);
2. the armed category census, with both detection legs (§7.3). It now
   instruments `emit_release` and `emit_dup`;
3. the R-1 structural close (§7.4). Constructor field types become an
   instantiation fact, `Err ⇒ Mixed` becomes a located error, and the
   shallow-dec arm in `emit_release` is deleted rather than re-keyed. The
   close is census-gated on zero licences in the `Ctor`, `Accessor` and
   `TraitMethod` partitions.

Faces 2 and 3 also need typecheck's producer obligations: monomorphised
accessors and trait-method instances.

The structural close must carry a scoped, attributed re-baseline of the
`f4_sudoku` `user::Grid.cells` accessor frame as its static witness. That frame
is uncalled in the corpus and the exemplar, so it is not a runtime witness.

Register rows: [safety invariants](../safety-invariants.md) R15, R17 and R18.

## Closure

The shallow-dec arm and the `Err ⇒ Mixed` arm are gone, the census reads zero
in the three partitions, and the `Grid.cells` re-baseline is recorded.
