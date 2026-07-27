---
number: 0931
target: /design
filed_by: /arch
filed_at: 2026-07-28
sprint_filed: 119
refers_to: design/arch/total-concreteness.md §3.1/§5.2;
  design/typecheck/non-concrete-producer-obligations.md §2 (P-1, P-2, A-MINT
  — the machinery this extends);
  design/backend/non-concrete-release-contract.md §2.5 (the template body is
  compiled-but-uncalled — the measured fact that makes this cheap), §4.1
  (I-CT'/face 1, which this subsumes once landed);
  crates/cranelisp-types/src/module.rs (DefKind::Constructor.got_slot rustdoc,
  re-ruled); crates/cranelisp-backend/src/compiler/control_flow/fn_as_value/
  (compile_data_constructor_as_value + compile_ctor_wrapper_body — the
  existing per-concrete wrapper this promotes);
  src/bootstrap.rs::register_synth_adt + :760-830 (the seeded generic ctors
  incl. Bind)
status: open
---

# S120: constructors join monomorphisation — the non-concrete ctor template slot retires

**Target: `/design`(typecheck), with backend adjacency for the wrapper
promotion. S120 scope — do NOT interleave with S119 Phase 5.**

> **AMENDED 2026-07-28.** The types-side representation is now PINNED by
> `design/arch/concreteness-types-first.md` §3: the slot retirement is
> `DefKind::Constructor { state: CtorState { Template | Concrete { got_slot:
> CallableSlot } }, .. }` with the ONE fallible witness mint
> (`SymbolTable::mint_callable_slot`) — design item 1 below builds against
> that vocabulary, not an `Option<usize>`. Item 4's schema window is
> confirmed (ONE bump, shared). The collection design additionally absorbs
> FIXME 0935 (carrier/storage-key identity — the register R-24 resolution)
> and A-MINT's pairing constraint recorded there.

Per the user-directed re-ruling (`design/arch/total-concreteness.md`), the
generic-ADT ctor's mandatory slot is the largest remaining exception to the
universal `slot ⇒ is_concrete()` invariant, held under a licence (I-CT'
representation-parametricity) that is a property of the uniform i64
representation and dies with it under `--release` layouts.

Design the S120 tranche:

1. **Template slot retirement.** A `DefKind::Constructor` whose scheme fails
   `is_concrete()` carries no slot and is excluded from `defined_symbols()`
   (joins `Polymorphic`/`Constrained`). Concrete-ADT ctors are byte-identical
   to today. The canonical `Type.Ctor` entry survives as the declaration-side
   template (scheme, tag, field_count, type_def facet, pattern/display
   identity) — resolution, `/list`, introspection, and the §8.6.5 contest read
   the entry, not its slot.
2. **Instance mint.** Value-position demand mints an instantiation-keyed
   concrete ctor instance under the ONE canonical mangler
   (`build_mangled_name`; P-2 applies — no second grammar), fed from the mono
   worklist, A-MINT-style (re-run the derivation at concrete args, never
   re-check a body). The existing ctor-as-value wrapper
   (`compile_ctor_wrapper_body`) is the promotion seed — measure whether it
   simply becomes the instance. Direct construction stays inline emission at
   concrete `MonoExpr::ConstrADT` sites (no entry, no slot).
3. **`Bind`.** Its slot retires with the class; internal, never legally a
   value; teardown is face 4 + FIXME 0934. Its existential scheme survives as
   a checking artefact.
4. **Schema window.** `Constructor.got_slot: usize` mandatory → state-carried
   is a serde shape change ⇒ ONE `CACHE_SCHEMA_VERSION` bump; this tranche
   forces the S120 window and the S120 witness-mint + R6 re-check ride the
   SAME window.
5. **Measures before binding** (the S119 discipline): MEASURE-C1
   wrapper/instance count across the corpus; MEASURE-C2 the `primitives`
   module's GOT high-water mark (cross-module mono homes instances there per
   FIXME 0355; 1024-slot slab).

Acceptance: NC-1's ctor population flips GREEN (FIXME 0930); backend's R17
census ctor partition reads zero; face 1's deletion site vanishes with the
template bodies (record the subsumption in the release contract's §4.1 in the
same window — file to `/design`(backend) or coordinate the edit).

Delete this file when the S120 design lands.
