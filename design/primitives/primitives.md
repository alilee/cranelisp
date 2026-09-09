# `cranelisp-primitives` — master design

**Status.** ACTIVE — the maintained interior of the primitives surface. The
canonical cross-surface contract is `design/arch/bounded-contexts.md` §4a; the
as-designed Rust surface is the crate-root and per-item rustdoc plus
`crates/cranelisp-primitives/public-api.txt`. The completed S66 migration plan
remains historical in `design/primitives/implementation-slice-s66.md`.

**Sprint 121's design delta is `design/primitives/s121-c5-primitives-visit.md`**
— the `vec-len` de-slot, the typed consume funnel's primitives half, and the
per-filing dispositions. Where this master states a target that has not yet
landed, it names the bundle that lands it; a clause asserting landed state it
does not have is a defect in this document.

Sprint 117's option analysis and evidence live in
`design/runtime/s117-primitives-integrity.md`. This master records the settled
state rather than repeating the delivery log.

## 1. Purpose and boundaries

`cranelisp-primitives` owns spec-defined, user-callable operations mounted in
the synthetic `primitives` module. It builds a process-static
`SymbolTable<(), ()>` and its statically backed GOT. Session integration
concretises the table to the compiler's `Code` parameter without changing the
shared GOT.

The crate is the user-facing half of the runtime library:

- primitives owns language-level operation names, schemes, documentation,
  implementation bodies, exported fallback shims, and declared ownership
  facts;
- `cranelisp-intrinsics` owns allocation, heap representation, RC/drop
  mechanics, and backend-emitted runtime entry points;
- typecheck and the standard library own trait dispatch;
- backend owns lowering and may substitute known direct primitive calls with
  inline CLIF, but the named primitive remains the indirect-call fallback;
- the Binary surface mounts the static table and orchestrates sessions.

The dependency direction is deliberately
`cranelisp-primitives → {cranelisp-types, cranelisp-intrinsics}`.
Primitives and backend do not depend on one another. No primitive knows about
compiler sessions, `Code`, trait resolution, or JIT ownership.

This split applies Principles 1 (decoupling over convenience), 2 (narrow
interfaces), 3 (dependency flows toward stability), and 21 (actors and
functions before mechanism).

## 2. Actors and authoritative data

### 2.1 Declaration inventory

`src/declarations.rs` is the sole primitive declaration inventory. One private
`primitive_declarations!` invocation records each legal declaration as one of
three closed variants:

- `UserExtern` — a user-callable table entry plus generated C-ABI wrapper and
  harvested shim;
- `UserInline` — a user-callable table entry with no GOT slot;
- `HarvestExtern` — a generated and harvested shim with no user-callable
  table entry.

The row supplies the operation's canonical name, scheme, parameter names,
docstring, body/publication kind, and—where user-callable—its finished
`ModeSummary`. The macro generates every primitive-function
`#[unsafe(export_name = "...")]` wrapper from that same row. Category modules
contain ordinary crate-private Rust implementation functions; they are not a
second export inventory.

The closed variants make extern-without-shim and harvest-only-inline states
unrepresentable. Duplicate table or harvest names fail during construction.
An inline row receives no phantom GOT slot; an extern row's allocated slot is
populated from the shim carried by that row.

The inventory projects:

1. user-callable `ModuleEntry::Def` rows;
2. GOT allocation and pointer population for extern rows;
3. the linker/DCE shim harvest;
4. schemes, parameter names, and docstrings;
5. declared ownership summaries.

There is no parallel operator registry, handwritten shim map, or
name-classifying ownership table. This is the maintained application of
Principles 7 (single source of truth), 18 (enforce invariants structurally),
and 20 (model invariants by representation).

### 2.2 Primitive table and GOT

`PRIMITIVES_TABLE` is built once through `LazyLock`. Its entries use
`DefKind::Primitive` and carry `code: None`; primitive identity is never
inferred from `code`. `PRIMITIVES_GOT_SLAB` is the writable, process-static
backing for the table's GOT. The table and its inner `Arc<GotTable>` are
shared, not reconstructed per session.

Extern declarations get a callable slot populated with their wrapper
address. Inline declarations are callable targets for known direct lowering
but have no slot. The distinction is carried by the entry's own callable state,
never by a null pointer convention; the representation of that state is
`cranelisp-types`', and its target form is the unified lifecycle
(`design/arch/symbol-table-lifecycle.md` §4.2/§4.6), under which a concrete
extern is a slotted entry realized by its extern shim and an inline operation
is a settled slot-less state. **A polymorphic extern cannot hold a slot**: the
settlement funnel mints against the declared scheme, so the construction does
not compile. Primitives selects no second lifecycle vocabulary.

Exported shim survival in linked binaries relies on the export-name linker
symbol, the declaration-derived address harvest, and the executable bundle's
force of `PRIMITIVES_TABLE`. There is no `#[used]` function mechanism.

The committed `public-api.txt` mechanically enumerates the Rust surface.
Numeric counts of primitives, exports, modules, or baseline lines are not
design authority. The semantic primitive inventory and its signatures are
governed by the language specification and conformance tests.

### 2.3 Implementation bodies

Category modules own the behavior of scalar, conversion, String, marshalling,
and Vec operations. Extern wrappers follow the consuming convention: every
heap-typed argument that is not returned is decremented at the wrapper
boundary. Internal Rust helpers may use narrower local borrowing conventions,
but they do not change that uniform language-call ABI.

Backend inline substitutions are optional optimisations for rows that keep an
extern fallback. They must preserve the named operation's semantics, and
indirect calls must remain valid through the table/GOT fallback.

The **inline Vec operations are not that shape**: they intentionally have no
extern fallback at all, and their slot-less state makes the absence explicit
rather than representing it as a null slot. `vec-get`, `vec-set` and `vec-push`
are inline today; `vec-len` joins them in Sprint 121 C5 bundle P0, which retires
the last slotted polymorphic entry in the system. Its applied-call emission is
already the inline one and does not change; its value-position use moves from
the GOT fallback to the inline wrapper arm, which carries the release the extern
convention would otherwise owe.

## 3. Data flows

### 3.1 Declaration and dispatch

```text
one declaration row
  ├─→ generated extern wrapper ─→ shim harvest
  └─→ ModuleEntry::Def
        ├─→ scheme / params / docstring / ModeSummary
        └─→ Extern: allocate + populate GOT slot
            Inline: no GOT slot

PRIMITIVES_TABLE
  → session concretisation preserving Arc<GotTable>
  → typecheck name/trait resolution
  → backend direct inline substitution or ordinary GOT-indirect call
  → runtime implementation body
```

No downstream stage re-identifies a primitive from an independently
maintained list.

### 3.2 Ownership declarations

Every user-callable row carries a finished `ModeSummary`. Scalar parameters
are `Copy`; only-read heap parameters may be declared `Borrowed` even though
the extern ABI consumes them; transforming operations use the applicable
owned/fresh result; identity uses `AliasOf`; element reads use
`ProjectionOf`; conditional copy-on-write Vec operations use `MayAliasOf`.
Absence is the conservative default only outside the classified
heap-primitive set; user-callable heap declarations are required to carry a
summary.

**The declaration row is also the ABI ownership fact — ratified, landing in
Sprint 121 C5 bundle P2; no handle type exists in source yet.** The generated
extern shim wraps each parameter in a typed handle derived from the row's own
declared type and `ParamFlow` — one derivation, no second hand-written
assertion — and a unit row checks the derived kinds against the row's facts.
The derivation axis is **`ParamFlow`, never `Mode`**: the S102 CS-B split is
deliberate, so an only-read heap parameter stays `Mode::Borrowed` (the analysis
fact) while its ABI kind remains consuming. The full statement, the one named
exemption (`sconcat`, whose type is seeded outside the pair), and the counted
trusted base are in `design/runtime/s119-typed-consume-funnel.md` §4.

The production flow is:

```text
declaration ModeSummary
  → ModuleEntry
  → session primitive-table seed
  → typecheck ClusterEnv transfer and fixpoint
  → settled callable entry and MonoDefnVariant.codegen_view
  → backend FnCompiler
```

Downstream statically resolved calls consume parameter modes through the
ordinary moded argument path. For a compiled producer,
`return_is_fresh_by_summary` consumes the result summary: `Fresh` permits the
return-protect elision; non-`Fresh` retains the conservative protect.

Direct inline Vec CLIF is body semantics, not a generic declaration-result
consumer. `vec-get` materialises an element according to layout and local
consumer facts; `vec-set` and `vec-push` implement their unique/shared COW
branches; `vec-len` reads the length word and releases the Vec it consumed.
Changing declaration metadata must not rewrite those mechanics.

### 3.3 String/Vec representation boundary

String semantics remain in primitives, while Vec layout and lifetime
mechanics remain in intrinsics. `split` creates owned HeapStrings and
transfers them in one call to the purpose-specific
`vec_strings_from_owned(Vec<i64>)`. Intrinsics initialises element slots
before publishing length and owns exact cleanup of every transferred String,
Vec header, and data allocation if construction unwinds.

`join` reads through `with_vec_strings(base, callback)`. Intrinsics validates
the Vec metadata before forming a callback-scoped immutable slice. The borrow
cannot escape in safe Rust and performs no RC action. `join` leaves the borrow
before allocating its result, then consumes the separator and input
Vec-of-Strings exactly once.

These two unsafe Rust-path functions are purpose-specific. They are absent
from the intrinsic catalog, carry no exported C symbol, and do not create a
general erased-`i64` Vec API. Primitives performs no Vec header or data offset
arithmetic.

## 4. Invariants

1. Every user-callable primitive is represented by exactly one declaration
   row and one table entry.
2. Every primitive extern wrapper and harvested pointer is generated from its
   declaration row; only `HarvestExtern` rows are harvested without a table
   entry.
3. Extern rows have one populated GOT slot; inline rows have none. A null
   phantom slot is not a legal representation. **No slotted entry carries a
   polymorphic scheme** — `vec-len` was the one exception and its de-slot
   (Sprint 121 C5 bundle P0) is what discharges the clause, after which the
   whole-table property is asserted by a negative row rather than by the absence
   of a counterexample.
4. Every user-callable heap-parameter primitive carries an explicit,
   declaration-local ownership summary.
5. `PRIMITIVES_TABLE` and its statically backed GOT have process lifetime and
   are shared through session concretisation.
6. Every primitive entry has `kind: DefKind::Primitive` and `code: None`;
   callable addresses live only in the GOT.
7. The extern language-call boundary consumes heap arguments it does not
   return. `string-identity` is the one extern row whose parameter is retained
   (`ParamFlow::IntoResult`) rather than consumed. **Target, landing in Sprint
   121 C5 bundle P1/P2: this becomes a type rather than a convention** — the
   implementation function behind each shim takes an owned handle for a consumed
   heap parameter and a borrowed one for a retained parameter, so a missing dec
   is a `#[must_use]` warning plus a debug drop bomb and a double dec does not
   compile. Until then it is enforced by review and by the module balance rows,
   and `vec-len` is the one row whose body does not honour it
   (`s121-c5-primitives-visit.md` §2.2), which is among the reasons its de-slot
   is ordered first.
8. Backend substitution is optional and trait-ignorant; the named primitive
   remains the semantic authority.
9. Intrinsics is the sole Vec representation owner. Primitive String code
   uses only the purpose-specific construction and scoped-read boundary.
10. The Vec-of-String constructor publishes length last and cleans partial
    ownership exactly once; the read view validates metadata, cannot outlive
    its callback, and neither retains nor consumes elements.
11. Adding a primitive changes one declaration row plus its implementation
    and tests; it does not require another production registry. **Re-kinding an
    existing primitive is not that shape**: a row's kind is also mirrored in the
    typecheck fixture seed and in the types crate's rustdoc, both owned
    elsewhere, so a re-kind carries filings those owners resolve.
12. No allocator/RC tracing, fault injection, detector mode, or diagnostic
    hook is part of this design.
13. **Structural embedding takes exactly one reference.** A primitive that
    embeds an existing heap structure into a new one *by pointer* (structural
    sharing, not copying) takes exactly one `rc_inc` — on the node it stores.
    Interior nodes are owned by their parent; elements by the node that holds
    them; those owners are unchanged by the embedding and are not re-counted.
    The auditable corollary: the inc count for one embed is **1, independent
    of the size and depth of the embedded structure**. Copied content instead
    takes one inc per copied reference, and deep-copied content takes incs
    only on the leaves it re-uses. The dual — every `cranelisp-intrinsics`
    `consume_*` is tree-ownership drop glue and therefore cannot discharge a
    reference no owner holds — is why this is an invariant and not a
    preference. Ruled S118 W2b (FIXME 0835);
    `design/runtime/s118-structural-embedding-ownership.md` §2 is the full
    statement, and `marshal.rs::sconcat` implements it. **Target, landing with
    invariant 7: the contract becomes signatures** — the chain read returns
    borrowed elements (they are owned by the chain), copied items each take one
    mint, and the structural embed takes exactly one — so a walk minting
    references no owner holds produces one drop bomb per surplus reference at
    the frame that minted it.
14. **Target, landing with invariant 7 — not yet in source. The pair has
    exactly one raw entry and one raw exit for heap handles**: the shim's
    ownership assertion on the way in, and the ABI return on the way out, which
    is also the only `mem::forget` the pair's non-test code performs on a
    handle. The owned handle is never `Copy` or `Clone`; the borrowed handle has
    no discharge operation. Widening that set is an `arch`-visible change to the
    trusted base, guarded by a structural gate —
    `design/runtime/s119-typed-consume-funnel.md` §2.1 and §3.

## 5. Test strategy

Tests mirror the module composition (Principles 5 and 23):

- declaration tests cover all legal variants, compile-fail illegal macro
  shapes, duplicates, missing heap ownership, and exact inventory projection
  into table, GOT, harvest, metadata, and ownership. Each carries its negative
  direction as a whole-table property rather than a per-row spot check — no
  slotted polymorphic entry, no harvested inline row, no unsummarised heap
  parameter — so a new counterexample REDs instead of arriving unobserved;
- a source-structure guard keeps primitive function exports inside the
  declaration macro;
- table/GOT tests call through loaded slots and verify static backing,
  `DefKind`, `code: None`, inline/no-slot shape, schemes, docs, and declared
  summaries;
- category units cover operation behavior and extern-boundary RC balance;
- production CLIF witnesses cover Borrowed parameter polarity and the
  `Fresh`/non-`Fresh` producer-return boundary; Run, Link, and REPL twins
  check the same value/lifetime behavior through the unified pipeline;
- typecheck transfer units pin the distinct meanings of `ProjectionOf`,
  `AliasOf`, `MayAliasOf`, and `Fresh`;
- Vec-runtime units cover empty and populated construction, partial and full
  pre-publication cleanup, invalid metadata, normal and unwinding callbacks,
  and exact final release;
- primitive and public-path split/join cases cover empty inputs and reuse of
  caller-owned inputs, including result lifetime independence.

Mutation experiments are evidence records, not a product feature. They change
one declaration at a time, observe existing artifacts, and restore the
truthful declaration. They add no persistent override or observation seam.

### R-2 evidence boundary — accepted, with a revival trigger

The compiler exposes stable production differences for Borrowed→Owned and for
non-`Fresh`→`Fresh`, including MayAliasOf→Fresh. It exposes none for
`vec-get: ProjectionOf(0) → Fresh`: an escaping heap element is materialised as
an owned reference under either declaration, so no production artifact's emitted
ownership behavior changes. The declaration still demonstrably reaches the
typecheck transfer and fixpoint, where Projection, Alias and Fresh remain
distinct.

**The user accepted R-2 on the existing evidence on 2026-09-01** — the typecheck
transfer units distinguishing projection provenance, the direct inline-body
guards, and the nine committed production witnesses — **with a named revival
trigger**: the declaration-sensitive witness obligation revives automatically,
as a plan row of the sprint concerned, the moment projection provenance becomes
emission-live. No source work remains in this crate, and the trigger's record is
`qa`'s.

So this design does not claim complete production mutation sensitivity for every
ownership variant, and states the gap rather than borrowing the language of a
grade. Inventing a test-only override, a cross-crate carrier or a diagnostic
hook to make a test turn red remains excluded.

## 6. Risks and controls

| Risk | Structural control |
|---|---|
| Declaration/export/harvest drift | one macro inventory generates every projection |
| Invalid body/publication combination | closed `PrimitiveDecl` variants |
| Null GOT target | extern allocation and pointer population are one projection; inline has no slot |
| False or missing heap ownership fact | summary required in each user row; transfer, CLIF, public-mode, and mutation evidence |
| Primitive/backend coupling | dependency severance; communication through types and mounted table |
| Vec layout drift in String code | purpose-specific intrinsics boundary; no primitive-side offsets |
| Partial Vec construction leak or double release | unpublished construction guard; initialise before publish |
| Scoped Vec read escapes or races mutation | callback lifetime plus caller safety contract |
| Documentation becomes a numeric snapshot | rustdoc and `public-api.txt` are surface authority; no volatile counts here |

The surface holds no mutable shared runtime state: the declaration inventory is
immutable after construction, and Vec-of-String construction stays unpublished
until complete. The Vec-of-String boundary has linear construction and in-place
read costs and clones no element.

## 7. Rejected alternatives

- **Independent registries plus parity tests.** Rejected because tests can
  detect some drift but leave multiple production authorities.
- **A general declaration-generator framework.** Rejected as complexity
  beyond the three legal states currently required (Principle 6).
- **Allocated-but-null slots for inline primitives.** Rejected because an
  impossible call target should be absent by representation.
- **Make declaration mutations alter inline Vec bodies.** Rejected because
  inline CLIF implements body semantics and is not the generic result-summary
  consumer.
- **Claim every ownership ADT variant must emit different RC.** Rejected:
  distinct analysis provenance can legitimately converge at the current
  backend's `Fresh`/non-`Fresh` decision.
- **Generic owned-`i64` Vec builder.** Rejected because partial cleanup cannot
  know the erased element drop operation without widening into a general
  descriptor/callback API.
- **Public offsets with primitive-side Vec arithmetic.** Rejected because
  shared constants do not centralise allocation, initialisation, publication,
  validation, or cleanup.
- **Persistent mutation overrides, tracing, fault injection, or detector
  modes.** Rejected as unnecessary product surface: the diagnostic surface is
  intrinsics-owned (invariant 12), and a primitives-local observer would be a
  second one.
- **A slot-less by-name `vec-len`** (the alternative de-slot spelling).
  Rejected: it needs a fourth declaration variant for one row, keeps a type
  variable inside the ABI derivation's domain, and adds a member to the backend
  uniform-realization roster that the inline spelling avoids —
  `s121-c5-primitives-visit.md` §3.1.

## 8. Quality attributes

- **Simplicity:** one declaration inventory and two purpose-specific
  Vec-of-String operations; no parallel catalogue or general builder.
- **Maintainability:** primitive churn has one metadata site, and
  representation changes remain with intrinsics.
- **Observability:** existing CLIF and public execution modes provide the
  evidence; no runtime diagnostics were added.
- **Concurrency safety:** immutable process-static declarations; publication
  after Vec initialisation; immutable callback-scoped reads.
- **Performance:** table construction remains one-time; split uses bulk
  allocation/copy; join reads in place.
- **Testability:** projections and representation transitions have explicit
  module seams and negative cases.

## 9. References

- `design/arch/bounded-contexts.md` §4a and §4b invariant 17
- `crates/cranelisp-primitives/src/lib.rs` crate and item rustdoc
- `crates/cranelisp-primitives/public-api.txt`
- `crates/cranelisp-primitives/CLAUDE.md`
- `design/runtime/s117-primitives-integrity.md`
- `design/runtime/s118-structural-embedding-ownership.md` (invariant 13 — the
  FIXME-0835 consume-owner contract; `marshal.rs` producer seams S1–S4)
- `design/runtime/s119-typed-consume-funnel.md` (invariants 7 and 14 — the typed
  handle vocabulary, the shim-fact derivation, the drop-bomb detection proof,
  and the churn-safety classes). Held by the intrinsics pass while Sprint 121's
  C5 stream runs; this surface consumes it without editing it
- `design/primitives/s121-c5-primitives-visit.md` (the Sprint 121 design delta)
- `design/arch/symbol-table-lifecycle.md` §4.2/§4.6/§5.5 (the callable
  lifecycle this crate's rows are born settled into)
- `design/primitives/implementation-slice-s66.md` (historical)

## 10. Next roles

- `sprint` — the one open gate is the de-slot's backend arm
  (`s121-c5-primitives-visit.md` §3.8); the wave shape is its §6.
- `qa` — the value-position ownership finding at that visit's §2.3, for
  attribution with the falsifier it names; and the acceptance cells for the
  de-slot.
- `dev` — use this master and the S121 visit for primitive changes; do not
  reopen the retired registries or primitive-side Vec layout access.
- `review` — check the delivered change-sets against the visit's reject
  criteria and this master's invariants, and read the `public-api.txt` diff
  beside the source diff.
