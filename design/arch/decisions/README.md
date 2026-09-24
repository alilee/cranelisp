# Decision labels

Source comments, tests and design documents cite architecture rulings as
"Decision N" / "D00NN". This index resolves each label to the ruling's current
statement. The label is a name for the ruling; the linked home is the authority.

- No Decision files exist and none are authored. A new cross-context commitment
  is written into [bounded contexts](../bounded-contexts.md) or a focused
  contract; a label row is added only for a number source already cites.
- Every record was retired once its ruling was confirmed in the listed home.
  The original texts are Git history under `design/arch/decisions/` (the last
  four, 43, 44, 47 and 48, before the S122 Phase 5 checkpoint that removed
  them) and the retired legacy decision directory.
- A number absent from this table (7, 14, 15 and other gaps) was withdrawn
  before the register was split into files; Git history is its only record.

BC = [`bounded-contexts.md`](../bounded-contexts.md).

| Label | Ruling | Current home |
|---|---|---|
| 1 | The pipeline crates form an acyclic DAG over the shared types crate. | BC per-context dependency statements; [source conventions](../../../src/CLAUDE.md) §"Dependencies Between Crates"; Cargo enforces it |
| 2 | Types shared across contexts live in `cranelisp-types`; [Principle 15](../principles/15-facade-types-live-with-behavior.md) governs what belongs there. | [BC 7](../bounded-contexts.md#7-cross-crate-types-cratescranelisp-types); [types memory](../../../crates/cranelisp-types/CLAUDE.md) |
| 3, 4, 5, 6 | `Span` is a struct; `TypeId` is `u32`; no optional metadata bag on a definition entry; `Type::from_name`/`type_name` centralise primitive naming. | Types-crate rustdoc; [source conventions](../../../src/CLAUDE.md) |
| 8 | Withdrawn: the first `MacroExpander` trait. The current callback is a different contract. | [`interfaces.md`](../interfaces.md) §"Macro execution callback" |
| 9 | Withdrawn: per-product side stores. Compiled code, AST and callees live on the symbol-table entry. | [BC 7](../bounded-contexts.md#7-cross-crate-types-cratescranelisp-types) |
| 10 | Heap pointers address the allocation base; every field offset is positive. | [BC 4b](../bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics) in-scope heap memory model; [source conventions](../../../src/CLAUDE.md) §"Heap Access" |
| 11 | A closure embeds its drop-glue pointer beside its code pointer, so a closure released in another module needs no side table. | [BC 4b](../bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics) invariant 5 |
| 12 | String layout is opaque to backend; every string operation is an extern call. | [BC 4b](../bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics) invariant 4 |
| 13 | Reference-count operations are atomic from the first ring, with an acquire fence before drop glue reads fields. | [BC 4b](../bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics) invariant 3; `design/backend/ring2-rc.md` §2.1 |
| 16 | Trait-method and multi-signature symbol mangling. | [source conventions](../../../src/CLAUDE.md) §"JIT Symbol Names" |
| 17 | Withdrawn: compiler-seeded traits. No trait is registered at startup. | `crates/cranelisp-typecheck/src/builtins.rs` tests |
| 18 | Withdrawn with `ReplCheckResult`; typecheck has one entry and one result shape. | [BC 2](../bounded-contexts.md#2-typecheck-cratescranelisp-typecheck) |
| 19 | `generalize` collects trait constraints into `Scheme.constraints`. | [BC 2](../bounded-contexts.md#2-typecheck-cratescranelisp-typecheck) invariant 6 |
| 20 | Withdrawn: call-site borrow/consume split. Replaced by 24. | — |
| 21 | The call graph is produced by typecheck and stored as `callees` on the entry. | [BC 2](../bounded-contexts.md#2-typecheck-cratescranelisp-typecheck) invariant 4 |
| 22 | `SymbolTable::codegen_targets()` is the one codegen-compilable predicate. | [BC 2](../bounded-contexts.md#2-typecheck-cratescranelisp-typecheck) invariant 3, §3 invariant 4; rustdoc on the method |
| 23 | One CLIF for JIT and object modes; the mode is a property of the `Module` that resolves the per-module GOT symbol. | [BC 3](../bounded-contexts.md#3-backend-cratescranelisp-backend) invariants 1 and 6 |
| 24 | Uniform consuming calling convention; it is the conservative point that ownership inference narrows from. | [BC 3](../bounded-contexts.md#3-backend-cratescranelisp-backend) invariant 2, [BC 4a](../bounded-contexts.md#4a-primitives-cratescranelisp-primitives) invariant 8, [BC 4b](../bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics) invariant 6; [ownership inference](../ownership-inference.md) |
| 25 | Compiled code lives on the definition entry as runtime-only state; the cache stores metadata and object code, and a cache hit loads rather than recompiles. | [BC 3](../bounded-contexts.md#3-backend-cratescranelisp-backend), [BC 7](../bounded-contexts.md#7-cross-crate-types-cratescranelisp-types); `design/backend/module-caching.md` |
| 26 | Platform function addresses live in the owning module's GOT slot; the scheduling class is a field of the platform-effect kind. | [BC 5](../bounded-contexts.md#5-platform-cratescranelisp-platform) invariant 1 |
| 27 | Withdrawn: a Sprint 57 wave-ordering constraint, discharged when both waves landed. | — |
| 28 | Withdrawn: a persistent per-worker JIT. Replaced by 31. | `design/int/int.md` §5.3 |
| 29 | The IO trampoline releases only the IO nodes it owns, each through the single IO teardown tail under the disposition its transfer requires; no release is outer-allocation-only. | [BC 4b](../bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics) invariant 7; [ownership and disposal](../../intrinsics/ownership-and-disposal.md) §6–§7 |
| 30 | Withdrawn: mutual imports are diagnosed as a cycle instead of deadlocking the scheduler. | [BC 6](../bounded-contexts.md#6-binary-int-src-cratescranelisp-exe-bundle) "Known architectural constraints" |
| 31 | JIT pages are reclaimed only by dropping the owning `Jit`; every pointer published from it has a retention owner. | [BC 3](../bounded-contexts.md#3-backend-cratescranelisp-backend) invariant 5; [Principle 22](../principles/22-published-pointers-have-retention-owners.md); `crates/cranelisp-backend/src/jit.rs` rustdoc; `design/int/session-transaction.md` |
| 32 | `CodeStore` and `LinkerStore` are method-free marker bounds, so the types crate never names Cranelift. | [arch memory](../CLAUDE.md) §"Facade convention"; rustdoc in `crates/cranelisp-types/src/module.rs` |
| 33 | Import, export, platform and submodule declarations are fields of `SymbolTable`, preserving the source specification for regeneration. | Rustdoc on the `SymbolTable` fields in `crates/cranelisp-types/src/module.rs` |
| 34 | The cache carries an explicit schema version; a mismatch is a stale entry, never a deserialisation failure. | `crates/cranelisp-backend/src/cache/mod.rs` rustdoc; `design/backend/module-caching.md` |
| 35 | `Code` is the session's concrete code store and owns lifetime only; callable addresses live in the GOT. | [BC 7](../bounded-contexts.md#7-cross-crate-types-cratescranelisp-types) "Callability is structural"; `crates/cranelisp-backend/src/code.rs` rustdoc |
| 36 | Every compiled function is declared under its bare name with local linkage; cross-module reachability is the GOT. | [BC 3](../bounded-contexts.md#3-backend-cratescranelisp-backend) invariant 7 |
| 37 | A cache hit is a branch inside module registration, not a second orchestration path; code generation is order-independent because typecheck fixes slot layout. | `design/int/cache-hit-loading.md` |
| 38 | `SharedState` is the worker-shareable session subset; introspection is an optional store whose presence is the mode discriminator. | [BC 6](../bounded-contexts.md#6-binary-int-src-cratescranelisp-exe-bundle); [`d1-introspection-repl-only.md`](../d1-introspection-repl-only.md); `design/int/int.md` |
| 39 | Errors carry their location as data; per-definition source lives with introspection and drives source-first regeneration. | `crates/cranelisp-types/src/error.rs` rustdoc; `design/int/int.md` §8.3 |
| 40 | IO observation is a callback contract registered with intrinsics; the observer state belongs to the binary. The `(trace …)` half was withdrawn. | [BC 4b](../bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics) in-scope and [BC 6](../bounded-contexts.md#6-binary-int-src-cratescranelisp-exe-bundle) development tooling for the observer half, with `crates/cranelisp-intrinsics/src/io_observer.rs` rustdoc; [`tracing.md`](../tracing.md) for tracing |
| 41 | One JIT per compiled symbol; backend publishes the slot address and returns artifacts; disassembly is produced on demand. | [BC 3](../bounded-contexts.md#3-backend-cratescranelisp-backend) "What crosses the boundary" and invariant 5; backend crate rustdoc |
| 42 | Platform failures are a located `PlatformError` in the types crate, surfaced through `CranelispError::Platform`. | [BC 5](../bounded-contexts.md#5-platform-cratescranelisp-platform) invariant 9; rustdoc in `crates/cranelisp-types/src/error.rs` |
| 43 | The runtime is split into `cranelisp-primitives` and `cranelisp-intrinsics`; backend has no trait knowledge and its inline table is name-keyed only. Retracts 14 and reframes 15; the operator-table debt they created is recorded in [Principle 16](../principles/16-punctuation-symbols-are-not-special.md). | [BC 4a](../bounded-contexts.md#4a-primitives-cratescranelisp-primitives) invariants 4, 5 and 7; [BC 4b](../bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics) invariant 9; [BC 3](../bounded-contexts.md#3-backend-cratescranelisp-backend) invariant 10 |
| 44 | Typecheck is cluster-atomic over caller-owned staging, behind the single `check_forms` entry; a source-ordered `defmacro` is a checkpoint outside that rollback domain. | [BC 2](../bounded-contexts.md#2-typecheck-cratescranelisp-typecheck) cluster definition and invariants 2, 3a, 7, 10 and 11; [`check_forms` narrative](../interfaces.md#check_forms); [macro availability](../macro-availability-model.md) |
| 45 | A trait implementation's shell is stored in the trait's defining module; method bodies live with the writer. | [BC 7](../bounded-contexts.md#7-cross-crate-types-cratescranelisp-types) "TraitImpl storage"; [`backend-keyed-consumer.md`](../backend-keyed-consumer.md) §1.1.1; [`trait-impl-cache-carrier.md`](../trait-impl-cache-carrier.md) |
| 46 | Withdrawn: a Sprint 66 wave-ordering constraint, discharged when both waves landed. | [BC 2](../bounded-contexts.md#2-typecheck-cratescranelisp-typecheck) invariant 10 holds the surviving locality rule |
| 47 | Resolved-stage type identity is module-qualified (`FQTypeName`/`FQTraitName`), with two named exceptions. | [`interfaces.md`](../interfaces.md) §"Type System"; [BC 7](../bounded-contexts.md#7-cross-crate-types-cratescranelisp-types) "FQTypeName binding"; rustdoc in `crates/cranelisp-types/src/newtype.rs` |
| 48 | Primitives own a statically constructed symbol table and GOT and dispatch like any other module; backend and primitives do not depend on each other. | [BC 4a](../bounded-contexts.md#4a-primitives-cratescranelisp-primitives) boundary statement, invariants 2, 3, 5 and 6 and "Rejected shapes"; [BC 4b](../bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics) invariants 9 and 11; [Principle 18](../principles/18-enforce-invariants-structurally.md); crate-root rustdoc of `crates/cranelisp-primitives/src/lib.rs` and `crates/cranelisp-exe-bundle/src/lib.rs` |
