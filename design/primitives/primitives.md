# `cranelisp-primitives` — design

**Status.** Current interior design of the primitives surface. The
cross-surface contract is `design/arch/bounded-contexts.md` §4a. The Rust
surface is the crate-root and item rustdoc plus
`crates/cranelisp-primitives/public-api.txt`. The shared typed-handle contract
is `design/runtime/s119-typed-consume-funnel.md`; this document states how
primitives consumes it.

## 1. Purpose and boundaries

`cranelisp-primitives` owns spec-defined, user-callable operations mounted in
the synthetic `primitives` module. It builds a process-static
`SymbolTable<(), ()>` and its statically backed GOT. Session integration
concretises the table to the compiler's `Code` parameter without changing the
shared GOT.

The crate is the user-facing half of the runtime library:

- primitives owns language-level operation names, schemes, documentation,
  implementation bodies, generated extern wrappers and declared ownership
  facts;
- `cranelisp-intrinsics` owns allocation, heap representation, the typed handle
  vocabulary, RC/drop mechanics and backend-emitted runtime entry points;
- typecheck and the standard library own trait dispatch;
- backend owns lowering, including inline emission of slot-less operations and
  closure wrappers for primitives used as values;
- the Binary surface mounts the static table and orchestrates sessions.

The dependency direction is `cranelisp-primitives → {cranelisp-types,
cranelisp-intrinsics}`. Primitives and backend do not depend on one another.
No primitive knows about compiler sessions, `Code`, trait resolution or JIT
ownership. This applies Principles 1 (decoupling over convenience), 2 (narrow
interfaces), 3 (dependency flows toward stability) and 21 (actors and
functions before mechanism).

## 2. Actors and authoritative data

### 2.1 Declaration inventory

`crates/cranelisp-primitives/src/declarations.rs` is the sole primitive
declaration inventory. One private `primitive_declarations!` invocation
records each declaration as one of three closed variants:

- `UserExtern` — a user-callable table entry, a generated C-ABI wrapper, a
  populated GOT slot and a harvested shim;
- `UserInline` — a user-callable table entry with no slot, wrapper or shim;
- `HarvestExtern` — a generated, harvested wrapper with no user-callable table
  entry.

A row supplies the operation's canonical name, scheme, parameter names,
docstring, publication kind and, where user-callable, its finished
`ModeSummary`. Extern rows also carry their `shim:` clause (§2.4). The macro
generates every `#[unsafe(export_name = "...")]` wrapper from that row.
Category modules contain ordinary crate-private implementation functions; they
are not a second export inventory.

The closed variants make extern-without-shim, harvest-only-inline and
shim-without-slot states unrepresentable. Duplicate table or harvest names fail
during construction.

The inventory projects:

1. user-callable `ModuleEntry::Def` rows;
2. GOT allocation and pointer population for extern rows;
3. the linker/DCE shim harvest;
4. schemes, parameter names and docstrings;
5. declared ownership summaries;
6. the private ABI-kind data of extern rows (§2.4).

There is no parallel operator registry, handwritten shim map or
name-classifying ownership table (Principles 7, 18 and 20).

### 2.2 Primitive table and GOT

`PRIMITIVES_TABLE` is built once through `LazyLock`. Its entries have
`CallableOrigin::RustPrimitive` and no compiled-code owner; primitive identity
is read from the origin. `PRIMITIVES_GOT_SLAB` is the writable, process-static backing for
the table's GOT. The table and its inner `Arc<GotTable>` are shared, not
reconstructed per session.

An extern row installs as a concrete callable whose slot is populated with its
wrapper address. An inline row installs in the settled slot-less inline state;
it is a callable target for direct lowering but has no slot. The distinction
is the entry's lifecycle state (`design/arch/symbol-table-lifecycle.md` §4.2
and §4.6), never a null-pointer convention. Slot minting refuses a
non-concrete scheme, so a polymorphic extern row fails table construction.

The Vec query family — `vec-get`, `vec-set`, `vec-push` and `vec-len` — is
inline. Their value-position use is served below the table by the backend's
unit-local closure wrapper (`symbol-table-lifecycle.md` §5.5); it mints no
table entry. The item-free `pub mod cranelisp_primitives::vec` remains on the
public baseline; its removal is governed by `design/arch/total-concreteness.md`
§3.2.

Exported shim survival in linked binaries relies on the export-name linker
symbol, the declaration-derived address harvest and the executable bundle's
force of `PRIMITIVES_TABLE`. There is no `#[used]` function mechanism.

`public-api.txt` mechanically enumerates the Rust surface. Numeric counts of
primitives, exports, modules or baseline lines are not design authority; the
semantic inventory is governed by the language specification and conformance
tests.

### 2.3 Implementation bodies

Category modules own the behavior of scalar, conversion, String, marshalling
and Sexp operations. Extern wrappers follow the Decision-24 consuming
convention: every heap-typed argument that is not returned is discharged at the
wrapper boundary. Private bodies express that convention in their signatures
(§2.4); it does not vary per call site.

Backend inline substitution for an extern row is an optional optimisation that
must preserve the named operation's semantics; indirect calls stay valid
through the GOT. Inline rows have no extern fallback, and their slot-less state
makes that absence explicit.

### 2.4 Typed ABI boundary

Generated wrappers remain raw `extern "C" fn(i64, ...) -> i64`. Each converts
raw words to the private body's parameter types on entry and the body's result
back to a raw word on return. Typing changes no exported symbol, arity, word,
GOT slot or `ModeSummary`.

**Derivation.** For each parameter the kind is:

| Declared parameter | Kind |
|---|---|
| `Int`, `Bool` or `Float` | scalar `i64` |
| heap-carried, `ParamFlow::IntoResult` | `Borrowed<'_>` |
| heap-carried, any consuming flow | `Owned` |

- The axis is `ParamFlow`, never `Mode`. The only-read String rows keep
  `Mode::Borrowed` as the analysis fact while their ABI still consumes, so
  their bodies take `Owned` and discharge once.
- `string-identity` is the sole `IntoResult` row: its body borrows, mints one
  owner for the result and discharges nothing.
- The row's `shim:` clause writes each private parameter and result type once.
  The macro uses those tokens both for the entry/exit conversion and for the
  row's ABI-kind data. rustc ties the tokens to the body; a declaration unit
  ties them to the declared type and `ParamFlow`; a compile-fail case proves a
  contradictory token/body pair is rejected.
- `UserInline` rows carry no wrapper tokens. Scalar `HarvestExtern` rows derive
  scalar kinds. `sconcat` is the one named exemption, because Binary/int seeds
  its Cranelisp type; rustc still checks its tokens against its body. Adding a
  second exemption is a design decision, not a local edit.
- ABI-kind data stays private. It does not enter `SymbolTable`,
  `cranelisp-types`, the cache or typecheck.

**Body transfer.**

- String reads borrow and return slices tied to the borrow. A consuming body
  reads through its owner, constructs its result, then passes the owner once
  to the intrinsics consume funnel.
- `split` holds fresh children as owners. Exact raw capacity is reserved before
  any child is disarmed; the children then move into the intrinsics
  Vec-of-String constructor, whose unpublished-construction guard owns them
  from entry. No child is disarmed while an allocation can still unwind.
- Marshal constructors state which fields are ownership-bearing by type rather
  than by tag threshold. A node is allocated and tagged first; each owned field
  moves into raw storage inside its field write; the completed node is adopted
  once. SList reads return views tied to the root, and quoting never consumes
  its source views.
- Raw field accessors and pre-initialisation allocator outputs stay raw
  representation seams. Typing adds no general panic-cleanup regime.

**Trusted base.** Beyond the wrapper's entry conversion and ABI return, three
private operations touch raw handles, each at an exact approved site set:

- a produced-value adapter, whose precondition is a fully initialised fresh
  RC=1 value, a canonical produced nullary value, or `quote-sexp`'s existing
  raw-zero error sentinel after `runtime_panic` has recorded an unknown tag.
  The sentinel is carried and returned, never treated as a valid Sexp;
- a parent-lifetime child view over a live Sexp/SList node's heap payload,
  which is never an owner or a discharge right; and
- owner-to-raw storage exits into ADT fields and the reserved Vec capacity.

The site sets are enforced by
`crates/cranelisp-primitives/src/abi_facts/tests.rs::typed_consume_trusted_base_matches_exact_production_callers`,
and their counts are recorded in the [shared trusted base](../runtime/s119-typed-consume-funnel.md#3-the-trusted-base-counted). The guard
makes the assertions enumerable; it does not prove raw provenance. Adding an
operation or site changes the shared trusted base: route it to `arch` and the
user before implementation. The current base adds no public item, C ABI,
Cargo edge, cache schema, heap layout or language behavior.

## 3. Data flows

### 3.1 Declaration and dispatch

```text
one declaration row
  ├─→ generated extern wrapper (typed body) ─→ shim harvest
  └─→ ModuleEntry::Def
        ├─→ scheme / params / docstring / ModeSummary
        └─→ Extern: allocate + populate GOT slot
            Inline: no GOT slot

PRIMITIVES_TABLE
  → session concretisation preserving Arc<GotTable>
  → typecheck name/trait resolution
  → backend inline emission or GOT-indirect call
  → runtime implementation body
```

No downstream stage re-identifies a primitive from an independently
maintained list.

### 3.2 Ownership declarations

Every user-callable row carries a finished `ModeSummary`. Scalar parameters are
`Copy`; only-read heap parameters may be `Borrowed` even though the extern ABI
consumes them; transforming operations use owned/fresh results; identity uses
`AliasOf`; element reads use `ProjectionOf`; conditional copy-on-write Vec
operations use `MayAliasOf`. Absence is the conservative default only outside
the heap-parameter set; user-callable heap declarations must carry a summary.

A row whose emission borrows a parameter and may return it must declare
`MayAliasOf`, never `Fresh`: a false `Fresh` lets return-protect elision free a
value the caller still owns.

The production flow is:

```text
declaration ModeSummary
  → ModuleEntry
  → session primitive-table seed
  → typecheck ClusterEnv transfer and fixpoint
  → settled callable entry and MonoDefnVariant.codegen_view
  → backend FnCompiler
```

Statically resolved calls consume parameter modes through the ordinary moded
argument path. For a compiled producer, `return_is_fresh_by_summary` consumes
the result summary: `Fresh` permits the return-protect elision; non-`Fresh`
keeps the protect.

Inline Vec CLIF is body semantics, not a generic declaration-result consumer.
`vec-get` materialises an element according to layout and local consumer
facts; `vec-set` and `vec-push` implement their unique/shared COW branches;
`vec-len` reads the length word and releases the Vec it consumed. Changing
declaration metadata must not rewrite those mechanics.

The declarations are the authority for the wrapper adaptation used when a
primitive is a value. Backend owns that emission and must match declared
`ParamFlow`; that repair is open in the
[backend release contract](../backend/non-concrete-release-contract.md#76-decision-24-wrapper-discharge-follows-realization-open).

### 3.3 String/Vec representation boundary

String semantics remain in primitives; Vec layout and lifetime mechanics
remain in intrinsics. `split` creates owned HeapStrings and transfers them in
one call to the purpose-specific `vec_strings_from_owned`. Intrinsics
initialises element slots before publishing length and owns exact cleanup of
every transferred String, Vec header and data allocation if construction
unwinds.

`join` reads through `with_vec_strings(base, callback)`. Intrinsics validates
the Vec metadata before forming a callback-scoped immutable slice. The borrow
cannot escape in safe Rust and performs no RC action. `join` leaves the borrow
before allocating its result, then consumes the separator and input
Vec-of-Strings exactly once.

These two unsafe Rust-path functions are purpose-specific. They are absent
from the intrinsic catalog, carry no exported C symbol and do not create a
general erased-`i64` Vec API. Primitives performs no Vec header or data offset
arithmetic.

## 4. Invariants

1. Every user-callable primitive is represented by exactly one declaration
   row and one table entry.
2. Every primitive extern wrapper and harvested pointer is generated from its
   declaration row; only `HarvestExtern` rows are harvested without a table
   entry.
3. Extern rows have one populated GOT slot; inline rows have none. A null
   phantom slot is not a legal representation. No slotted entry carries a
   polymorphic scheme: slot minting refuses it at table construction.
4. Every user-callable heap-parameter primitive carries an explicit,
   declaration-local ownership summary.
5. `PRIMITIVES_TABLE` and its statically backed GOT have process lifetime and
   are shared through session concretisation.
6. Every primitive entry has `CallableOrigin::RustPrimitive` and no compiled-code owner;
   callable addresses live only in the GOT.
7. The extern language-call boundary consumes the heap arguments it does not
   return, by type: a consumed heap parameter reaches its body as `Owned`, a
   retained one as `Borrowed`. A missing discharge is a `#[must_use]` warning
   and a debug drop bomb; a second discharge does not compile.
   `string-identity` is the one retained parameter.
8. Backend substitution is optional and trait-ignorant; the named primitive
   remains the semantic authority.
9. Intrinsics is the sole Vec representation owner. Primitive String code uses
   only the purpose-specific construction and scoped-read boundary.
10. The Vec-of-String constructor publishes length last and cleans partial
    ownership exactly once; the read view validates metadata, cannot outlive
    its callback, and neither retains nor consumes elements.
11. Adding a primitive changes one declaration row plus its implementation and
    tests. Re-kinding an existing primitive also touches the typecheck fixture
    seed and the types crate's rustdoc, which are owned elsewhere.
12. No allocator/RC tracing, fault injection, detector mode or diagnostic hook
    is part of this design.
13. **Structural embedding takes exactly one reference.** A primitive that
    embeds an existing heap structure into a new one by pointer takes exactly
    one reference — on the node it stores. Interior nodes are owned by their
    parent and elements by the node that holds them; the embedding does not
    re-count them. The inc count for one embed is 1, independent of the
    embedded structure's size and depth. Copied content takes one reference
    per copied item. Every intrinsics `consume_*` is tree-ownership drop glue
    and cannot discharge a reference no owner holds. In types: the chain read
    returns borrowed elements, each copied item mints once and the embed mints
    once, so a surplus reference is a drop bomb at the frame that minted it.
    The [structural-embedding contract](../runtime/s118-structural-embedding-ownership.md#2-the-invariant-stated-declaratively)
    is the full statement; `crates/cranelisp-primitives/src/marshal.rs::sconcat`
    implements it.
14. Raw handles enter and leave typed code only at the wrapper boundary and the
    exact trusted-base sites of §2.4. `Owned` is never `Copy` or `Clone`;
    `Borrowed` has no discharge operation. Widening that set is an
    `arch`-visible [trusted-base change](../runtime/s119-typed-consume-funnel.md#3-the-trusted-base-counted).

## 5. Test strategy

Tests mirror the module composition (Principles 5 and 23):

- declaration tests cover every legal variant, compile-fail illegal macro
  shapes (including a token/body contradiction), duplicates, missing heap
  ownership, token-versus-declaration ABI kinds and exact inventory projection;
- a source-structure guard keeps primitive function exports inside the
  declaration macro, and the trusted-base guard pins each raw-handle site;
- table/GOT tests call through loaded slots and verify static backing,
  primitive origin, the absence of a compiled-code owner, the inline/no-slot Vec family, schemes, docs and
  declared summaries;
- category units cover operation behavior and extern-boundary RC balance,
  including exactly-once child transfer for `split`;
- marshal units assert the structural-embedding rule across sizes: one mint
  per embed, one per copied item;
- production CLIF witnesses cover `Borrowed` parameter polarity and the
  `Fresh`/non-`Fresh` producer-return boundary; Run, Link and REPL twins check
  the same value/lifetime behavior through the unified pipeline;
- typecheck transfer units pin the distinct meanings of `ProjectionOf`,
  `AliasOf`, `MayAliasOf` and `Fresh`;
- Vec-runtime units cover construction, cleanup, invalid metadata, callback
  unwinding and final release.

Mutation experiments are evidence records, not a product feature. They change
one declaration at a time, observe existing artifacts, and restore the
truthful declaration. They add no persistent override or observation seam.

### R-2 evidence boundary — accepted, with a revival trigger

The compiler exposes stable production differences for Borrowed→Owned and for
non-`Fresh`→`Fresh`, including MayAliasOf→Fresh. It exposes none for
`vec-get: ProjectionOf(0) → Fresh`: an escaping heap element is materialised as
an owned reference under either declaration. The declaration still reaches the
typecheck transfer and fixpoint, where Projection, Alias and Fresh remain
distinct.

The user accepted R-2 on 2026-09-01 on the existing evidence — the typecheck
transfer units, the direct inline-body guards and the nine production
witnesses. The declaration-sensitive witness obligation revives as a plan row
when projection provenance becomes emission-live; `tests/plan/PLAN.md` carries
the trigger. No source work remains in this crate.

This design does not claim production mutation sensitivity for every
ownership variant. A test-only override, cross-crate carrier or diagnostic hook
made only to turn a test red remains excluded.

## 6. Risks and controls

| Risk | Control |
|---|---|
| Declaration/export/harvest drift | one macro inventory generates every projection |
| Invalid body/publication combination | closed `PrimitiveDecl` variants |
| Null GOT target or slotted polymorphic row | extern allocation and population are one projection; inline has no slot; slot minting refuses non-concrete schemes |
| Missed or doubled heap discharge in a body | `Owned`/`Borrowed` signatures derived from `ParamFlow`; token/body compile-fail case |
| Raw-handle misuse | exact trusted-base site guard (§2.4) |
| False or missing heap ownership fact | summary required in each user row; transfer, CLIF and public-mode evidence |
| Primitive/backend coupling | dependency severance; communication through types and the mounted table |
| Vec layout drift in String code | purpose-specific intrinsics boundary; no primitive-side offsets |
| Partial Vec construction leak or double release | unpublished construction guard; capacity reserved before child transfer |
| Scoped Vec read escapes or races mutation | callback lifetime plus caller safety contract |

The surface holds no mutable shared runtime state: the declaration inventory is
immutable after construction, and Vec-of-String construction stays unpublished
until complete.

## 7. Rejected alternatives

- **Independent registries plus parity tests** — tests detect some drift but
  leave multiple production authorities.
- **A general declaration-generator framework** — complexity beyond the three
  legal states (Principle 6).
- **Allocated-but-null slots for inline primitives** — an impossible call target
  should be absent by representation.
- **A slot-less by-name extern `vec-len`** — needs a fourth declaration variant
  for one row, can present a bare type variable to ABI-kind derivation, and
  grows the backend uniform-realization roster.
- **A `Mode`-keyed ABI derivation** — would give the only-read String rows
  borrowed handles and silently delete their Decision-24 discharges.
- **Weakening a declaration to fit a backend wrapper** — the declaration is the
  authority; the emission must match it.
- **Declaration mutations that alter inline Vec bodies** — inline CLIF is body
  semantics, not the generic result-summary consumer.
- **Every ownership variant must emit different RC** — distinct analysis
  provenance can legitimately converge at the backend's `Fresh`/non-`Fresh`
  decision.
- **A generic owned-`i64` Vec builder** — partial cleanup cannot know the erased
  element drop operation without a general descriptor/callback API.
- **Public offsets with primitive-side Vec arithmetic** — shared constants do
  not centralise allocation, initialisation, publication, validation or
  cleanup.
- **New handle operations to make a primitives instrument compile** — a need
  for one is a gap in the shared contract, returned to its owner.
- **Persistent mutation overrides, tracing, fault injection or detector modes**
  — the diagnostic surface is intrinsics-owned (invariant 12).

## 8. References

- [Primitives](../arch/bounded-contexts.md#4a-primitives--cratescranelisp-primitives) and [intrinsics](../arch/bounded-contexts.md#4b-intrinsics--cratescranelisp-intrinsics) bounded contexts
- `design/arch/symbol-table-lifecycle.md` §4.2, §4.6 and §5.5
- `design/arch/total-concreteness.md` §3.2 — Vec family and public `vec` module
- `design/runtime/s118-structural-embedding-ownership.md` — invariant 13
- `design/runtime/s119-typed-consume-funnel.md` — handle vocabulary and trusted
  base (invariants 7 and 14)
- `design/backend/non-concrete-release-contract.md` §7.6 — value-position
  wrapper discharge
- `crates/cranelisp-primitives/src/lib.rs` crate and item rustdoc
- `crates/cranelisp-primitives/public-api.txt`
- `crates/cranelisp-primitives/CLAUDE.md`
