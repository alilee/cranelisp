# `cranelisp-primitives` — master design

**Status.** ACTIVE — current target design, refreshed in Sprint 117 after the
primitive declaration, ownership-evidence, and Vec-of-String work. This
document describes the maintained interior of the primitives surface. The
canonical cross-surface contract is
`design/arch/bounded-contexts.md` §4a; the as-designed Rust surface is the
crate-root and per-item rustdoc plus
`crates/cranelisp-primitives/public-api.txt`. The completed S66 migration plan
remains historical in `design/primitives/implementation-slice-s66.md`.

Detailed Sprint 117 option analysis and evidence live in
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
but have no slot. The distinction is represented by `PrimitiveBody`, not by a
null pointer convention.

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

Backend inline substitutions are optional optimisations. They must preserve
the named operation's semantics, and indirect calls must remain valid through
the table/GOT fallback. The three inline Vec operations intentionally have no
extern fallback slot; their `PrimitiveBody::Inline` representation makes that
exception explicit.

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
branches. Changing declaration metadata must not rewrite those mechanics.

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
   phantom slot is not a legal representation.
4. Every user-callable heap-parameter primitive carries an explicit,
   declaration-local ownership summary.
5. `PRIMITIVES_TABLE` and its statically backed GOT have process lifetime and
   are shared through session concretisation.
6. Every primitive entry has `kind: DefKind::Primitive` and `code: None`;
   callable addresses live only in the GOT.
7. The extern language-call boundary consumes heap arguments it does not
   return.
8. Backend substitution is optional and trait-ignorant; the named primitive
   remains the semantic authority.
9. Intrinsics is the sole Vec representation owner. Primitive String code
   uses only the purpose-specific construction and scoped-read boundary.
10. The Vec-of-String constructor publishes length last and cleans partial
    ownership exactly once; the read view validates metadata, cannot outlive
    its callback, and neither retains nor consumes elements.
11. Adding a primitive changes one declaration row plus its implementation
    and tests; it does not require another production registry.
12. No allocator/RC tracing, fault injection, detector mode, or diagnostic
    hook is part of this design.

## 5. Test strategy

Tests mirror the module composition (Principles 5 and 23):

- declaration tests cover all legal variants, compile-fail illegal macro
  shapes, duplicates, missing heap ownership, and exact inventory projection
  into table, GOT, harvest, metadata, and ownership;
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

### R-2 evidence limitation

The current compiler exposes stable production differences for
Borrowed→Owned and for non-`Fresh`→`Fresh`, including
MayAliasOf→Fresh. Bounded Sprint 117 attempts did not find a production
artifact whose emitted ownership behavior changes for
`vec-get: ProjectionOf(0) → Fresh`; escaping heap elements are materialised as
owned values in the attempted shapes. The declaration still demonstrably
reaches the typecheck transfer/fixpoint, where Projection, Alias, and Fresh
remain distinct.

Therefore this master does not claim complete production mutation sensitivity
for every ownership variant. FIXME 0859 is deferred to Sprint 118 to either
find an existing stable production consumer or return the evidence-backed
materialisation boundary to the user for disposition. Inventing a test-only
override, cross-crate carrier, or diagnostic hook is not an acceptable way to
make the test turn red.

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

This sprint did not introduce shared runtime state. The declaration inventory
is immutable after `LazyLock` construction, and Vec construction remains
unpublished until complete. Runtime diagnostics are deliberately unchanged.
The selected boundary has linear construction and in-place read costs without
an additional element clone.

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
  modes.** Rejected as unnecessary product surface and outside the Sprint 117
  cyber boundary.
- **Fold intrinsics-internal raw-read cleanup into R-3.** Rejected as a scope
  expansion. FIXME 0850 remains open and untouched.

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
- `design/primitives/implementation-slice-s66.md` (historical)
- `design/arch/fixmes/0859-*.md` (deferred R-2 evidence boundary)
- `design/arch/fixmes/0850-*.md` (excluded intrinsics raw-read convergence)

## 10. Next skills

- `/review` — check the maintained master against the settled W4/W5
  implementation and current source rustdoc.
- `/qa` — carry FIXME 0859's bounded Projection evidence question into Sprint
  118 without introducing a product observation seam.
- `/dev` — use this master for future primitive changes; do not reopen the
  retired registries or primitive-side Vec layout access.
- `/sprint` — record FIXME 0861 resolved and continue Sprint 117 W6.
