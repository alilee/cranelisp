# Total concreteness at the end of typecheck

**Owner:** `arch`. **Status:** current contract. The invariants in §2 are user-directed
(2026-07-28, clarified 2026-09-21; §0 quotes them) and ruled by `arch`, which authored the clause wording.
They are delivered except where a section names an open obligation. §3.4 is the
canonical IO-node ownership contract, including the 2026-09-21 reuse ruling. The S119 census,
the staged S120/S121 route, the superseded I-ABI clause and the forty-row requirements
cross-check are in Git history (the S119 types-first design commission was retired into this
document at S122).

Neighbouring contracts, not restated here:

- [Concrete codegen boundary](concrete-boundary-type.md) — `ConcreteType`, `MonoExpr`, the
  ambiguity verdict, and the signature-path residuals.
- [Symbol-table lifecycle](symbol-table-lifecycle.md) — the callable states and slot claims
  that represent §2.
- [Safety invariants](safety-invariants.md) — rows R11, R17–R20 grade what this document
  states.

Section numbers are stable because designs, source and tests cite them. Retired numbers
(§1, §4–§6) are not reused.

## 0. The ruling

> **User, 2026-07-28:** "we need concrete types at the end of typecheck. we need to
> eliminate edge cases that seem to need polymorphism. In the future when we have more
> sophisticated storage layouts, there will be no chances for generic functions."
>
> "typecheck must emit fully concrete-typed syntax tree including calls to primitives … I
> don't think we should tolerate any slotted-and-polymorphic."

> **User, 2026-09-21, on I-CONC's domain:** "I think it is stronger - only concrete
> signatures should have callable slots."
>
> "the retained prior isn't callable by any new callers though - it is retained to avoid
> stomping on existing callers, before we set up cascading recompiles."

- Every licence once granted to a non-concrete slot holder was a property of the uniform
  `i64` tag-or-pointer representation, not of the entry kind. Layout specialisation
  ([release-backend proposal](release-llvm-backend.md)) removes that uniformity, so a licence
  of that kind fails silently — a wrong shared body — exactly when layouts diverge.
- When sanctioned exceptions falsify an invariant's universal statement, eliminate the
  exceptions; do not partition the invariant. A kind-partitioned statement was tried at S119
  and replaced: its predecessor, stated universally with unstated exceptions, was asserted
  nowhere, and two unsanctioned mints hid behind it for thirty-five sprints.

## 2. The invariants

- **I-CONC (the table).** For every callable in every symbol table, only a concrete
  signature has a callable GOT slot. Universal and kind-free. The reverse direction is behavioural:
  a missed reachable instance is a missing-slot failure, never a fallback through a template.
- **I-FRAME (the codegen domain).** Every frame the backend compiles, and every call,
  construction or release site it emits, carries only concrete types. A non-concrete callable
  is a monomorphisation source and is never a codegen target.
- **I-EMIT (the emitted tree).** The tree typecheck emits references no polymorphic callable.
  Each call site's dispatch identity resolves to a slotted concrete entry, an inline lowering
  driven by the site's own concrete types, or a per-instantiation concrete instance of a
  hand-written runtime body. Polymorphism survives only below the tree, as a backend-interior
  realization choice (§3.3). I-EMIT replaced the earlier I-ABI roster licence on the user's
  direction quoted above.

How each is held (verified at source, 2026-09-21):

- I-CONC is represented by the lifecycle: `Life::Concrete` and `Life::Broken` carry the
  `CallableSlot` their arm is settled on; `Life::Template`, inline primitives and
  host-promised externs have none; `Life::Declared` may retain a displaced prior, which
  is not callable (next bullet) (`crates/cranelisp-types/src/lifecycle.rs`). The slot's field
  is private, and every settlement and install funnel converts the scheme through
  `ConcreteType::from_type` before it claims a slot, refusing with
  `SlotMintError::NotConcrete`.
- **Retained prior — `Life::Declared { prior }` conforms.** Physical retention of a slot
  index is not assignment of a callable slot to the provisional signature (§0, 2026-09-21).
  - Semantic ownership. The retained index stays the displaced concrete signature's slot. Its
    GOT cell keeps serving already-compiled callers under that signature's ABI; retention
    exists so a redefinition does not stomp on them. The provisional scheme has no callable
    slot: `Binding::callable_got_slot` and `is_callable_target` exclude `Declared`, so no new
    call site can target it, and publication refuses a `Declared` arm (pin:
    `crates/cranelisp-types/src/module/tests.rs::redeclaration_rebinds_the_same_slot`).
  - Exits. Concrete settlement reuses the index only through `CallableSlot::rebind`, which
    refuses a non-concrete scheme; template settlement and `retire_abi_changing` tombstone
    it. The index is never reissued (pin:
    `crates/cranelisp-types/src/module/tests.rs::concrete_to_template_conserves_and_never_reissues_prior_slot`).
    A tombstone is the same case: an index retained for existing callers, callable under no
    new signature.
  - Representation witness. `CallableSlot` is a bare index and the table holding the
    `Declared` arm does not record the displaced signature. That is an absent witness, not a
    non-conforming owner: I-CONC does not require it, and no reader needs it there. Every
    production staging table is seeded empty (`src/worker.rs`,
    `src/session_v4/index_worker.rs`), so the live table keeps the displaced arm intact until
    publication, where integration's `PreserveAbi`/`ChangeAbi` decision compares old and new.
  - Grade. Structural for every reader that uses the two accessors. Asserted, with a
    falsifier, for the rest: `prior` and `CallableSlot::index` are public, and the falsifier
    is a read of `prior` outside the types lifecycle funnels that reaches slot emission or a
    GOT load. QA's one-off static census (2026-09-21) found none.
- Clone and serde bypass the funnels. `SymbolTable::validate_lifecycle` re-checks every arm —
  `LifecycleError::NonConcreteSlot` for a slotted non-concrete scheme and `ConcreteTemplate`
  for the converse — and the cache loader calls it
  (`crates/cranelisp-backend/src/cache/serialize.rs`), so a stale or corrupt sidecar is a
  diagnosed recompile. Pin:
  `crates/cranelisp-types/src/module/tests.rs::load_validation_rejects_nonconcrete_and_out_of_range_claims`.
- I-FRAME's projection is `SymbolTable::codegen_targets()`; the body half is the
  [concrete codegen boundary](concrete-boundary-type.md).
- Rejected representations, retained because each is a plausible future shortcut: the slot
  inside the codegen view, a `symbol → slot` register beside the GOT, an entry-level split of
  the declaration union, and distinct index types for host and platform slots. The reasons
  live on `CallableSlot`'s rustdoc (`crates/cranelisp-types/src/module.rs`) and in
  [symbol-table lifecycle](symbol-table-lifecycle.md) §4.3 and §8.

### 2.1 Constructor field types at an instantiation

`cranelisp_types::ctor_field_types_at` is the only legal derivation of a constructor's field
types at a concrete instantiation for category and glue purposes.

- It substitutes the instantiation's arguments into the declared field types and converts
  each through `ConcreteType::from_type`. An already-concrete constructor projects unchanged
  and a nullary constructor has zero fields.
- One residual field refuses the whole constructor (`CtorFieldsAtError::NotConcrete`). It
  never fabricates: there is no default arm.
- A caller bug — a key that is not a constructor, a parameter-arity mismatch, an
  instantiation mismatch — is a typed error distinct from the refusal.
- Pins: `crates/cranelisp-types/src/heap/value_layout_tests.rs`. Source rustdoc owns the
  exact signature.
- Open: the backend's declaration-scheme walk in
  `crates/cranelisp-backend/src/compiler/context.rs` still fills a missing field type with
  `Type::Int`; safety-register rows R17 and R18 and FIXME 0929 own its retirement onto this
  projection.

## 3. Populations

### 3.1 Constructors

- A generic constructor's canonical entry is a declaration-side template: scheme, tag, field
  count, type facet, docstring and pattern/display identity, with no slot. A concrete-ADT
  constructor is slotted. Source ADTs split in `crates/cranelisp-typecheck/src/adt.rs` and
  bootstrap seeds in `src/bootstrap.rs::register_synth_adt`.
- Direct construction lowers inline at a concrete site. Value-position use and accessors are
  served by per-instantiation instances minted through the one canonical mangler.
- `IO.Bind` is a template. Its scheme is existential (`b` in
  `Bind { inner: IO b, cont: Fn [b] (IO a) }` is not recoverable from `IO a`), it is internal,
  and no concrete instance can be demanded as a value. Its teardown is §3.4.
- A constructor instance body owes zero RC operations: fields transfer into the box at
  concrete types as they did in the template.
- Open: FIXME 0931 holds one evidence tail — a current witness, or a recorded supersession,
  for the whole bootstrap constructor population and the R17 constructor partition.

### 3.2 The Vec family

- `vec-len`, `vec-get`, `vec-set` and `vec-push` are inline primitives
  (`crates/cranelisp-primitives/src/declarations.rs`): slot-less, with no shared compiled
  body. Each call site is emitted from its own concrete element type, so the family survives
  layout specialisation by construction.
- Value-position use rides the backend's span-keyed, unit-local `__wrap_{name}_…__` closure
  wrapper over the same inline lowering, with one `(name, arity)` arm per member. No
  per-signature `__inlwrap` family has ever existed in source; do not cite one.
- `vec-len` was the last slotted polymorphic primitive. It was ruled inline (2026-09-01)
  rather than a by-name extern because the closed primitive-declaration set is the crate's
  structural control, a by-name polymorphic extern is the one row shape that can present a
  bare variable to ABI-kind derivation, and the alternative grows the §3.3 roster.
- `pub mod cranelisp_primitives::vec` remains on the primitives baseline as an item-free
  module. No approval to remove it is in force:
  - `arch` ruled its deletion a contraction (2026-09-01) scoped to the `vec-len` de-slot
    change-set. That change-set landed without the deletion, so the ruling's condition has
    passed, and an `arch` ruling never satisfied the user gate.
  - Removal is an inter-crate public-API change under root `CLAUDE.md` §Inter-crate
    public-API user gate. Before implementation `arch` presents the exact delta: one baseline
    line (`pub mod cranelisp_primitives::vec`), no Rust importer, and the e2e guard
    `tests/facade_pif_rows.rs` that asserts the line's presence, which `test` revises in the
    same change-set. After implementation the generated `public-api.txt` diff returns to the
    user.
  - The contraction needs no shim or deprecation window.

### 3.3 The uniform-realization roster

- A hand-written runtime body is below the type system: typecheck cannot make it concrete. It
  is kept behind a uniform value ABI that it declares, or split per layout class when that ABI
  stops being uniform.
- The roster is the closed set of generic, slot-less, host-promised bodies:
  `primitives/bind`, `primitives/race`, `primitives/select` and
  `primitives/catch-runtime-error`. It is a backend-interior realization contract, not an
  exception to any typecheck invariant. A new or reclassified member fails the pin until it is
  declared with its representation dependencies (uniform value word; IO-node tag discipline;
  closure `DROP_GLUE_PTR`; `Result` Ok/Err tag order). Pin:
  `src/bootstrap.rs::bootstrap_generic_uniform_body_roster_is_closed`.
- `bind`, `race` and `select` have no body anywhere: the backend intercepts them by name and
  lowers IO-node construction inline at the concrete call site. `catch-runtime-error` has one
  C-ABI body in `cranelisp-intrinsics`.
- **Open — I-EMIT is not yet delivered for these four.** Each is still a polymorphic entry
  that the emitted tree references by name. The ratified dispositions are:
  - `bind`, `race`, `select` re-kind to the inline-primitive model. Precondition MEASURE-RK:
    a census of their value-position uses; any hit needs its wrapper-body arm before the
    re-kind, landed dormant as the `vec-len` arm was.
  - `catch-runtime-error` gains per-instantiation concrete instances named by the canonical
    mangler, each realised today as an alias onto the one body. The instance name is where
    the type closes; a layout change then alters realization per instance with no tree change.
  - No filing carries this work. `sprint` schedules it or records an owned deferral.
- The `TemplateBody::UniformRust` and `Realization::FacadeOf` carriers exist for that end
  state; their presence is not evidence of a production roster.

### 3.4 The IO existential (`Bind`): a representation question, and it dissolves

The existential is real — `b` in `Bind { inner: IO b, cont: Fn [b] (IO a) }` is
not recoverable from `IO a`, so monomorphising every caller still leaves a
runtime teardown walk unable to name a nested `Pure b` payload's type. The cure
is the architecture's standing pattern (closure `DROP_GLUE_PTR`, Decision 0011):
**local self-description, stamped at the concrete construction site.** Under
I-FRAME every site that constructs an IO node is concrete post-mono, so the
existential becomes a representation fact — no type-system residual and no
header type-word (R15 stands: one glue pointer on one runtime-owned node
family). The `Bind` *entry*'s existential scheme survives as a
checking/introspection artefact; compiled code and slots are where polymorphism
ends.

#### Layout and stamp (produce side) — delivered S121

- The glue word is a hidden second field on the **`Pure` node only**:
  `[header | tag@16 | payload@24 | payload_glue@32]`. Every other IO node keeps
  its layout: `Effect`'s thunk and `EffectPoll`'s state closure are
  Rust/closure-owned, `Bind`'s continuation carries its own `DROP_GLUE_PTR`, and
  `Par`/`Select`/`Launch` children are IO nodes walked recursively. Pattern
  matching binds field 0; IO mints no accessor for the hidden word.
- The word is a **witness, written once before publication**: `0` (`Scalar`) —
  the payload owes no discharge — or the canonical `drop<T>` address
  (`Owned(glue)`), the same glue every other release site calls (release-contract
  reject criterion 5). The type is known at the stamp site, which closes the
  wild-write-on-scalar class by construction. `1` is reserved and emitted by
  nothing; its decode and report are intrinsics interior
  ([ownership and disposal §6.1](../intrinsics/ownership-and-disposal.md#61-the-pure-payload-witness--retain-on-force)).
- Stamp authority is the backend's alone, over the closed set its design
  enumerates ([backend release contract](../backend/non-concrete-release-contract.md)); the runtime allocates no
  `Pure`. The platform writes only `0`, and the platform-return seam below
  replaces it.

#### Ownership on force — IO values are reusable (user ruling, 2026-09-21)

`spec/10-io.md` §10.8.1 owns the language statement. The representation rule:
**a force never moves a field out of a published node.** The node keeps every
reference it owns until `free_io_node` discharges it at count zero, after the
zero decrement and its Acquire fence; a force hands its consumer a *new*
reference or a borrow. Two owners of one obligation therefore have no
representation (Principle 20), and nothing arbitrates between force and
teardown. Deleting the former once-only claim without the retain would restore a
double discharge; choosing a move from the node's count or freshness is rejected
(intrinsics invariant 5).

| Node | Rule | Status (2026-09-21) |
|---|---|---|
| `Pure` | Force reads the witness; `Owned(glue)` ⇒ one `rc_inc` of the payload for the consumer. Teardown discharges `Owned(glue)` under both dispositions. Private to intrinsics: no layout, stamp, public-API or ABI effect | Implemented in the working tree; reviewed with no blocking finding; **not accepted**. Sequential reuse and heap balance pass (IOR-1/IOR-2); the reserved-word cells and their detection proof pass. QA accepted the correction evidence; integration remains pending |
| `Effect` | The node owns a repeatable, thread-safe thunk. Force borrows it; teardown destroys it once under both dispositions. Changes `cranelisp-platform`'s public API and ABI — approved delta below | Producer and consumer implemented and reviewed; generated baseline matches the approval; **user confirmed the generated diff on 2026-09-21**. Sequential reuse (IOR-4) and module lifetime tests pass. The corrected composed unforced-capture fence passes and is proven to detect omitted teardown |
| `Launch` | Force still moves the sub-tree out through a non-atomic `0` sentinel | **No correction is approved or scheduled.** A second force is unmeasured; a measured fault enters through `qa` |
| `EffectPoll` | Node untouched; one state closure is re-entered | Re-entry unmeasured; no change approved |
| `Bind`, `Par`, `Select` | No mutation on force | Inherit their leaves' behaviour |

Cost of the `Pure` rule is derived, not measured (intrinsics design §6.1): one
atomic increment per heap-payload force and one glue call at teardown, replacing
an atomic exchange per force. Trigger for measurement: a `Pure`-dense regression
attributable to this seam.

#### `Effect` public API — approved by the user, ABI 11

Producer `cranelisp-platform`, `impl<CL: CLType> CLIO<CL>` and crate root:

```text
- pub fn effect(f: impl FnOnce() -> CL + 'static) -> Self
+ pub fn effect(f: impl Fn() -> CL + Send + Sync + 'static) -> Self
- pub fn effect_on_resource(token: i64, f: impl FnOnce() -> CL + 'static) -> Self
+ pub fn effect_on_resource(token: i64, f: impl Fn() -> CL + Send + Sync + 'static) -> Self
- pub fn effect_on_resource_with_capacity(token: i64, capacity: i64, f: impl FnOnce() -> CL + 'static) -> Self
+ pub fn effect_on_resource_with_capacity(token: i64, capacity: i64, f: impl Fn() -> CL + Send + Sync + 'static) -> Self
  pub unsafe fn call_effect_thunk(thunk_ptr: i64) -> EffectOutcome      // signature unchanged
+ pub unsafe fn drop_effect_thunk(thunk_ptr: i64)
- pub const ABI_VERSION: u32 = 10;
+ pub const ABI_VERSION: u32 = 11;
```

- `call_effect_thunk` borrows: valid any number of times, from any thread,
  concurrently, until discharge. `drop_effect_thunk` is valid exactly once,
  with no force in progress or to follow. Both live in the platform crate so one
  crate owns the boxed type (Principle 7); source rustdoc carries the caller
  obligations.
- `Send + Sync` is required, not defensive: token-0 `Par` branches run on rayon
  workers and a token with capacity above one admits concurrent holders, so one
  aliased node is called through `&self` from two threads and destroyed wherever
  its count reaches zero. The bound makes an unsafe capture fail to compile in
  the author's crate (Principle 20); a per-node lock would serialize effects the
  platform declared concurrent.
- Unchanged: the `CL: CLType` bound, `EffectOutcome`, `CLIO`, the 40-byte
  `Effect` layout, every `IO_EFFECT_*` offset, re-exports, cache schema.
  `ABI_VERSION` 11 is mandatory: a v10 `FnOnce` box cannot be called by
  reference, and the load gate must refuse it before a force.
- Author semantics: a captured `CLOwned` lives until the node is freed, and each
  force runs the closure again. A closure that moves a capture into a consuming
  call must clone per call; `Rc`/`RefCell`/`Cell` captures move to
  `Arc`/`Mutex`/atomics.
- **Conformance.** Independent review found the implemented surface equal to
  this delta with no extra signature; the stored-thunk alias and the
  capture-drop holder are private. The generated
  `crates/cranelisp-platform/public-api.txt` diff is exactly the three
  constructor lines plus the added `drop_effect_thunk(i64)` line; the
  `ABI_VERSION` line carries no value and does not move. The user confirmed
  that exact generated diff on 2026-09-21.
- **Consumers.** `cranelisp-intrinsics`: the unchanged
  `io_guard::force_effect_thunk_protected` call, and the new teardown edge from
  the `Effect` row of `free_io_node_with_disposition` to `drop_effect_thunk`
  ([design §6.2](../intrinsics/ownership-and-disposal.md#62-the-effect-thunk--borrowed-on-force-discharged-at-teardown)).
  Its fixtures now build through `CLIO::effect*`. The workspace and in-tree
  DLL build succeeds with the approved bounds. The `ABI_VERSION` literal pins
  and adjacent-version rejection fixture follow ABI 11 and pass the final integrated run.

#### Lifetime edges and residuals

A lane forces only while it holds a counted reference, teardown runs behind the
zero decrement's fence, and a `Par` worker's reads are ordered before the root's
teardown by the join its result already rides. These residuals are separate, and
none is cured by the rules above:

- **Severed join** (pre-existing; `qa` intake). A cancelled `Select` loser with a
  rayon bridge in flight detaches its worker: the dropped `run_blocking_branch`
  future abandons the `oneshot`, `pending_bridges` has no drop guard, and
  `block_on_reactor` drains the supervisor but not bridges. The detached
  worker's walk — now including a borrowed thunk call — can race the root's
  `consume_io_tree`: a use-after-free window. Falsifier: a `select` whose losing
  branch holds an in-flight blocking `Par` bridge at cancellation. The cure
  restores the join; it must not add an ownership channel.
- **Capture-destructor trap** (new with node-owned thunks; consciously
  unprotected). Teardown runs outside the signal guard, so a hardware trap
  inside a capture destructor is not contained. Known captures are `i64`s and
  `CLOwned` host references. Trigger: a platform capture owning a foreign
  resource whose destructor can trap. A *panicking* capture destructor is
  contained DLL-side; that containment across a real cdylib boundary is
  asserted, and `design`(platform) and `qa` own its falsifier and
  classification.
- **Abort-path leak** (pre-existing; read at source, unmeasured; `qa` intake). A
  runtime error or dispatch fault returns without releasing the fresh current
  node and un-popped continuations. Retention changes only magnitude — a leaked
  forced node now leaks its payload or thunk with it. Direction: leak, never a
  second owner.

The separate backend scope-result retain defect (IOR-5) is corrected in the
working tree ([backend design §8](../backend/s122-closure.md)). The extra retain
was observed before the change; both IOR-5 controls and IOR-2 now balance.

#### Grades

| Property | Grade |
|---|---|
| `Pure` force retains; teardown discharges once | **Measured** at the module tier: the retain cells were observed failing on a force without the mint. The public heap-reuse balance observation also passes (IOR-2) |
| No store to a published `Pure` or `Effect` node | **Asserted, with a falsifier** — a source fact read once at review, not structural. Falsifier: any non-construction store to such a node's field in intrinsics. The one known post-publication writer is the `Launch` sentinel |
| Reuse-safe thunk across threads | **Structural**: the `Fn + Send + Sync` bound, pinned by the executing baseline guard |
| One thunk discharge; no force overlaps discharge | Discharge-once is **measured** by the red-first intrinsics lifetime cells, including the shared-reference negative leg. Non-overlap is **asserted**; falsifier: the severed join |
| One `rc_inc` is the exact inverse of one `drop<T>` for every stamped payload category | **Asserted, with a falsifier** (source analysis; module cells cover the shallow and bare-nullary shapes only): a category whose glue is not count-gated |

#### The platform-return seam — stamps are tag-licensed (R19)

`compile_direct_call` is the one platform-call chokepoint. Its post-call stamp
dispatches on the **returned node's tag**, never the call target's kind — a
kind-keyed unconditional store is out of bounds whenever a platform fn returns
`CLIO::pure`, which is published author surface:

```
node = <GOT-indirect platform call>            # non-poll; the poll arm returns earlier
tag  = load.i64 [node + 16]
tag == IO_TAG_EFFECT ⇒ store fn_name_ptr → [node + 40]
tag == IO_TAG_PURE   ⇒ store glue        → [node + 32]   # in-bounds at ABI ≥ 10 only
otherwise            ⇒ no write                          # degrades like a null fn-name
```

- The `Pure` arm is the **adoption stamp**: the DLL cannot name a glue address
  (`HostCallbacks` is permanently two fields) and writes `0`; the backend knows
  `T` from the entry's `(Fn […] (IO T))` scheme and overwrites it with the
  canonical `drop<T>` (`DropGlueRegistry::request_if_owning`; `iconst 0` when
  the request declines; a residual `T` is a located refusal — R18). The store
  lands before the node can be forced or transferred. `CLIO` does not implement
  `CLType`, so a nested DLL `Pure` is unconstructable through the facade.
- The crossing datum is absolute byte offset **32**, pinned independently at
  compile time in each owning crate: backend's
  `const _: () = assert!(PURE_GLUE_ABS_OFFSET == 32);` and platform's
  `const _: () = assert!(HEAP_HEADER_SIZE + IO_PURE_GLUE_OFFSET == 32);`. No
  joint or root assertion is added: it would duplicate a relationship already
  structural and give it a second owner.
- Evidence: backend CLIF rows pin the tag load, both stores, the no-write
  fall-through and that the stores are branch-dominated by the tag compare
  (`(IO String)` materialises the same `drop<String>` `FuncId` the release path
  names; `(IO Int)` stamps `0`); a non-platform callee emits no stamp block. The
  `Pure`-returning platform fixture pair observes adoption, discharge and the
  scalar path end-to-end with a no-double-discharge control.

**ABI.** The IO-node family is a layout contract governed by
`cranelisp_platform::ABI_VERSION` (Principle 14): 9→10 carried the `Pure`
widening, 10→11 the `Effect` thunk contract.


### 3.5 Platform effects

- A platform function is a C-ABI body, so a polymorphic platform signature is a declared
  contract nothing can check. The class is concrete by construction:
  `SymbolTable::install_platform` converts the manifest scheme before it claims the
  descriptor-order slot, and `src/platform.rs` reports a refusal as a module error naming the
  platform function. The error carries `Span::SYNTHETIC`, not a source location.
- Open: FIXME 0933 also asked for a parse-side refusal naming the offending lowercase leaf.
  The structural gate is delivered; the filing's disposition against source is
  `design`(int)'s.
