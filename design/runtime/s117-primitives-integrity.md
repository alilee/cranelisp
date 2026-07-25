# Sprint 117 — primitive registration, ownership evidence, and Vec/String boundary

**Status:** Phase 3 design of record
**Scope:** Runtime surface (`cranelisp-primitives` with its
`cranelisp-intrinsics` Rust-path dependency)
**Authority:** elaborates `design/runtime/runtime.md`; public-surface changes
remain subject to `/arch`

## 1. Actors and functions

| Actor | Function | Contract |
|---|---|---|
| Primitive declaration | describes one user-callable operation | Supplies the symbol, scheme, parameter names, docstring, body kind, exported shim where one exists, and declared ownership fact as one row. |
| Primitive table builder | turns declarations into `ModuleEntry::Def` rows | Allocates a GOT slot only for an extern body, stores exactly that row's shim, and attaches exactly that row's ownership declaration. |
| Intrinsics Vec owner | allocates, initialises, publishes, reads, and destroys Vec storage | Owns all offset arithmetic and the two-allocation Vec invariant. |
| Primitive String implementation | supplies String semantics | Calls the Vec owner for `split` construction and `join` read access; it never reads or writes Vec fields. |
| Backend production lowering | consumes declared ownership facts | Produces ordinary CLIF whose retain/release shape is the evidence for those facts. |
| Public compiler modes | execute the lowered program | Run, Link, and REPL supply the value/lifetime twin of the CLIF evidence. |

This actor split applies Principle 21 (actors and functions before mechanism).
The design deliberately does not move String semantics into intrinsics:
intrinsics owns representation and lifetime mechanics; primitives owns the
user-callable operation.

## 2. R-1 — registration complete by construction

### 2.1 Selected shape

Replace the four independently name-keyed inventories with one crate-private
declaration inventory in a new `src/declarations.rs`. The inventory is emitted
by one crate-private `primitive_declarations!` invocation. Conceptually, each
row is:

```text
PrimitiveDecl {
  name,
  scheme,
  param_names,
  docstring,
  body: Inline | Extern { shim },
  ownership,
  publication: UserCallable | HarvestOnly,
}
```

The concrete representation is two closed enums, rather than independent
booleans:

```text
Publication {
  UserCallable { scheme, param_names, docstring, ownership },
  HarvestOnly,
}

Body {
  Inline,
  Extern { shim: *const u8 },
}
```

`PrimitiveDecl { name, publication, body }` is crate-private. The macro may
use typed function items while expanding and erase them to `*const u8` only in
the final row. The following states must be representable directly:

- `UserCallable + Inline`: a symbol-table entry with no GOT slot and no shim
  (`vec-get`, `vec-set`, `vec-push`);
- `UserCallable + Extern { shim }`: a symbol-table entry whose allocated GOT
  slot is populated from the shim carried by the same declaration;
- `HarvestOnly + Extern { shim }`: a linker/harvest symbol with no
  `PRIMITIVES_TABLE` entry.

`HarvestOnly + Inline` is not a legal state: `HarvestOnly` is constructed only
by the macro arm that also requires a shim function item. The four exceptional
harvest-only shims (`neq-i64`, `neq-f64`, `neq-bool`, and `sconcat`) are rows
using that arm; there is no string allow-list.

The macro is also the export declaration site for extern bodies. Each extern
row supplies the wrapper signature and implementation expression; expansion
emits both the `#[unsafe(export_name = "<name>")] extern "C"` wrapper and the
row carrying that same wrapper's function item. Existing exported bodies
become unexported implementation functions in their current category modules.
This is the part that closes the currently-unchecked body-to-harvest direction:
there is no independently authored `export_name` attribute for a primitive
shim. Review and a unit grep guard require that the only primitive-function
`export_name` attributes occur in the declaration macro (the GOT slab's
`__cranelisp_got_primitives` attribute is the named non-function exception).

The table builder and shim harvest are projections of the same inventory.
Ownership is a field of every `UserCallable` declaration, not a second
classifier keyed by `name`. Scalar rows carry their mechanically constructed
`Copy/Fresh` summary in that field; heap rows carry their audited summary.
There is no `declared_mode_summary(name, ty)` production classifier after the
migration.

All descriptor and projection machinery is `pub(crate)`. The existing
`PRIMITIVES_TABLE`, static GOT slab, exported symbol names, and module
visibility remain unchanged. Therefore R-1 has no Rust public-API or
cross-crate interface delta.

This is Principle 7 (single source of truth), Principle 18 (make omission
unrepresentable), and Principle 20 (model the legal body/publication pairings
as variants). It also obeys Principle 6: this is one inventory and two simple
projections, not a generator framework.

### 2.2 Completeness and failure behavior

Construction must hard-fail during `LazyLock` initialisation on duplicate
symbols, a user-callable heap-parameter row without an ownership declaration,
or a duplicate harvested name. An extern-without-shim and
harvest-only-inline row are unconstructable macro states. No row may silently
leave a null GOT slot: an `Extern` row allocates then immediately stores its
carried pointer; an `Inline` row allocates no slot.

The reverse-inventory unit check is mechanically derived from the declaration
inventory and the built table:

- every `UserCallable` declaration contributes exactly one table entry;
- every `Extern` declaration contributes exactly one harvested pointer;
- every table primitive and harvested primitive comes from one declaration;
- only `HarvestOnly` declarations are absent from the table.

It is a guard on the projection implementation, not a hand-written second
inventory.

### 2.3 Exact source seams and migration order

Implementation is one primitives-crate change, in this order:

1. Add `src/declarations.rs` with the private row types, the single macro
   invocation, and pure projections `build_table(decls)` and
   `harvest_shims(decls)`. Move the current four polymorphic Vec schemes into
   row constructors here; they cease to be a separate insertion path.
2. Convert exported bodies in `ring0.rs`, `int.rs`, `float.rs`, `bool.rs`,
   `marshal.rs`, `string.rs`, and `vec.rs` to ordinary crate-private
   implementations. Macro-generated wrappers preserve every existing exported
   symbol and C ABI. `lib.rs` re-exports no new Rust item.
3. Replace `operator.rs`'s `PrimitiveDef` and
   `ring{0,1,3}_primitives()` registries with the one inventory. Delete
   `insert_primitive_entry`, `insert_vec_query_entries`, and the handwritten
   `extern_shims()` map from `lib.rs`.
4. Delete the production name classifier in `ownership_facts.rs`; retain only
   small ownership-summary constructors if they keep declaration rows
   readable. The declaration row supplies the finished `ModeSummary`.
5. Build `PRIMITIVES_TABLE` by filtering `UserCallable`, and build the
   internal harvest by filtering `Extern`. The static GOT slab, table type,
   symbol names, schemes, parameter names, docstrings, and entry kinds remain
   byte-for-byte/compare-equal to the pre-migration projections.

The migration does not temporarily run old and new inventories together.
That would create a fifth synchronization surface and violate Principle 8
(no interim implementations).

### 2.4 Unit scenario space

Per Principle 23, the declaration module owns:

- compile-pass examples of all three legal body/publication variants;
- compile-fail macro cases for missing shim and harvest-only-inline;
- runtime-construction negatives for duplicate declaration/harvest name and
  missing heap ownership;
- GOT allocation/pointer population for extern rows and absence for inline
  rows;
- the complete production inventory projected both ways:
  `UserCallable declarations == table names` and
  `Extern declarations == harvested names`, with each table extern slot equal
  to its declaration pointer;
- a source-structure guard asserting that primitive function exports are
  emitted only by `primitive_declarations!`; the separately named static GOT
  slab is the sole allowed direct export attribute;
- a projection-equivalence test pinning every row's scheme, param names,
  docstring, body kind, and ownership summary during migration. This fixture is
  deleted only if its expected side is generated from the settled inventory;
  it must not survive as a second hand-maintained catalogue.

## 3. R-2 — declaration flow and bounded production evidence

R-2 changes no runtime interface. A primitive ownership declaration follows
this authoritative production path:

```text
declaration inventory
  → PrimitiveDecl projection into ModuleEntry::Def { mode_summary }
  → session primitive-table seed and per-session concretisation
  → typecheck ClusterEnv::summary_of
  → transfer / fixpoint / publish
  → MonoDefnVariant.codegen_view.mode_summary
  → FnCompiler
```

There is no parallel name classifier and no overwrite of the declared leaf
fact. `ClusterEnv::summary_of` reads the seeded `ModuleEntry`; transfer maps
the leaf result mode into origins, projection provenance, conditional COW
links, escape facts, and derived user-function summaries; the fixpoint
publishes the settled result both to the callable entry and its
`codegen_view`. Backend receives that published summary with the body.

The backend has two deliberately different consumption seams:

- Downstream statically resolved calls consume **parameter modes** through the
  ordinary moded argument-list path.
- For a compiled producer, `return_is_fresh_by_summary` is the sole backend
  consumer of the callable's **result summary**. `Fresh` elides the producer's
  return protect; every non-`Fresh` result keeps it.

Direct inline Vec lowering does not consult the declaration's result mode.
`compile_vec_get` materialises a heap element according to element layout and
its bounded consumer-site elision fact. `compile_vec_set`/`vec-push` implement
the operation's unique/shared COW branches from source liveness, escape, and
layout facts. Their direct CLIF is therefore a **body-semantic guard**, not a
declaration-mutation witness. Making false metadata rewrite those mechanics
would make the implementation less truthful, not make the declaration more
operational.

The committed public-path set contains **nine witnesses: five CLIF witnesses
and four Run/Link/REPL value/lifetime twins**. Together they show normal
production lowering and one-pipeline behavioral parity. The existing
`CRANELISP_NO_OWNERSHIP` switch remains only the conservative reference for
the Borrowed polarity; W4b adds no observation surface.

### 3.1 W4b mutation record and evidence boundary

The declaration projection unit tier proves a changed row reaches a changed
`ModuleEntry::mode_summary()`. Typecheck transfer units separately pin the
semantic distinctions among `ProjectionOf`, `AliasOf`, `MayAliasOf`, and
`Fresh`. Production mutation experiments then test only backend distinctions
that the current consumer model promises:

| Declaration-only mutation | Production result | Disposition |
|---|---|---|
| `str-len`: borrowed heap parameter → `Owned` | RED | Downstream static-call parameter-mode consumption is proven operational. |
| `string-identity`: `AliasOf(0)` → `Fresh` | RED | The derived producer becomes `Fresh`; `return_is_fresh_by_summary` removes its return protect. |
| `vec-set`: `MayAliasOf(0)` → `Fresh` | RED in the producer witness | The derived producer becomes `Fresh`; its return-protect emission changes through the sole result-summary consumer. The inline COW body itself remains unchanged, as required. |
| `vec-get`: `ProjectionOf(0)` → `Fresh` | emission-inert in the bounded attempted shapes | Direct inline materialisation is independent of the row. Attempted producer/downstream shapes did not yield a stable additional CLIF difference beyond the fixed materialisation/protect behavior. |
| `vec-get`: `ProjectionOf(0)` → `AliasOf(0)` | emission-inert by the current backend contract | Both are non-`Fresh`, so both keep the producer protect. Their distinct origin/provenance meanings remain pinned in typecheck transfer units. |
| `vec-set`: `MayAliasOf(0)` → `AliasOf(0)` | no separate stable production claim | Both are non-`Fresh` at the sole backend result consumer. Their conditional-versus-unconditional origin distinction remains pinned in typecheck transfer units. |

The `ProjectionOf → Fresh` investigation is deliberately recorded as
**partial evidence**, not proof that the declaration is operationally
irrelevant. The fact demonstrably reaches transfer/fixpoint and changes the
derived summary; the bounded source shapes attempted in W4b did not expose a
further stable production-emission distinction. Exhaustively proving that no
such source shape exists would require a wider ownership-consumer analysis
than this runtime wave authorises.

Accordingly, the accepted claim is bounded as follows:

1. The inventory is the sole leaf-fact authority and its facts reach the
   settled ownership analysis unchanged.
2. Direct inline Vec CLIF guards the primitive body's real lifetime mechanics.
3. Downstream static calls prove declaration parameter modes operational.
4. Producer return-protect emission proves the `Fresh` versus non-`Fresh`
   result boundary operational where a stable distinction exists.
5. Finer result variants whose current backend emission is identical are
   checked at typecheck's transfer seam; W4b does not invent a product hook or
   claim production sensitivity it did not observe.

This is the strongest evidence supported by the present consumer graph.
Principle 5 requires testing at the real seam; Principle 25 requires each
actual narrowing to remain checkable against its conservative fallback. It
does not require semantically different analysis variants to produce
different machine code when the only backend predicate is `Fresh` versus
non-`Fresh`.

### 3.2 W4 sequence and interface assessment

- **W4a — complete:** the private declaration inventory generates wrappers,
  table/GOT/harvest projections, metadata, and ownership summaries.
- **W4b — evidence reconciliation:** retain the five production CLIF guards
  and four public-mode twins; retain the successful Borrowed, Alias/Fresh, and
  MayAlias/Fresh mutation records; record the bounded emission-inert
  Projection attempts and the typecheck transfer coverage without overstating
  them as production REDs.

No persistent override, alternate table, allocator/RC/ownership tracing,
fault injection, detector mode, or diagnostic hook is introduced. W4b
changes no Rust public API, C ABI, intrinsic catalogue, symbol-table schema,
heap layout, cross-crate interface, or language specification. A future
requirement for backend-visible distinctions among every non-`Fresh` result
variant would be a new cross-crate consumer/carrier design requiring `/arch`
arbitration, not an in-scope primitives repair.

## 4. R-3 — runtime-owned `Vec String` boundary

### 4.1 Options considered

**A. Generic owned-`i64` builder/read view.** This appears reusable, but erases
the element drop operation at the failure boundary. A partially constructed
builder cannot release an owned element correctly from `i64` alone. Restoring
that knowledge needs a drop callback/type descriptor and becomes a general
mutable Vec API. Rejected.

**B. Public offsets plus primitive-side arithmetic.** This is the current
shape. It shares constants but not the allocate/initialise/publish protocol,
so `split` can publish `len` too early and `join` can read an invalid
`len/cap/data_ptr` combination. Rejected.

**C. Purpose-specific `Vec String` construction and scoped read access.**
Selected. Intrinsics already knows HeapString allocation and
`consume_vec_of_string`; it can therefore clean up partial initialisation
exactly. The surface is narrow enough that it does not become a general Vec
mutation API. Both operations are `unsafe`: `Vec<i64>` carries words, not
HeapString provenance, liveness, or reference ownership, so the Rust type
cannot make either boundary safe.

### 4.2 Proposed intrinsics surface

Exact conceptual entries (final Rust naming is `/arch`-approved):

```rust
pub unsafe fn vec_strings_from_owned(elements: Vec<i64>) -> i64;

pub unsafe fn with_vec_strings<R>(
    base: i64,
    read: impl FnOnce(&[i64]) -> R,
) -> R;
```

Required rustdoc:

- `vec_strings_from_owned` requires every input word to be the base pointer of
  one live HeapString allocation and to carry one owned reference that the
  caller transfers to the function. Duplicate words are valid only when the
  caller actually owns the corresponding number of references. From call
  entry the caller must neither consume nor separately release those
  transferred references, including if the function unwinds. On success the
  returned live Vec owns exactly those references. Before publication the
  implementation owns the input `Vec<i64>`, any allocated Vec object/data
  buffer, and the transferred HeapString references: it initialises element
  slots before writing `len`, writes `len` last, and an unwind guard
  shallow-consumes each transferred reference exactly once and frees each
  unpublished allocation exactly once. Only `0..len` is live.
- `with_vec_strings` requires `base` to be a non-null, correctly aligned base
  pointer to a live Vec whose live elements are HeapString base pointers, with
  an owning Vec reference kept alive and no concurrent mutation for the
  complete callback. Before forming a slice it checks `0 <= len <= cap`,
  checked `cap * size_of::<i64>()` representability, and that `data_ptr` is
  non-null and correctly aligned when `cap > 0`; the caller remains
  responsible for allocation provenance and liveness, which runtime field
  checks cannot establish. The slice borrow cannot escape the callback in
  safe Rust. The callback may copy an element word only as a non-owning
  observation; retaining or consuming an element requires an explicit RC
  operation outside this helper's contract. Normal return and unwind perform
  no increment, decrement, transfer, or consumption of the Vec or its
  elements.

The implementation remains in `vec_runtime`; its internal raw helpers and
offset constants stay the single layout authority. These functions are
Rust-path helpers only: they are absent from `intrinsics_table`, carry no
`export_name`, and are never backend-emitted-call targets.

`split` creates all HeapStrings, transfers the resulting owned handles in one
call to `vec_strings_from_owned`, then consumes its two String arguments.
`join` builds its host `String` inside `with_vec_strings`, exits the borrow,
allocates the result, then consumes the separator and the input through
`consume_vec_of_string`. No primitives source reads or writes a Vec offset.

This explicitly names allocation, initialisation, publication, borrow, and
release points (Principles 7, 18, and 22). It does not resolve or partially
resolve FIXME 0850: intrinsics-internal `drop.rs` raw-read convergence remains
excluded.

### 4.3 Scenario matrix

The `vec_runtime` unit tier covers:

- construction sizes `{zero, one, several}`;
- the private pre-publication cleanup guard directly, with unit-owned
  HeapStrings in `{none, partially initialised, fully initialised}` states;
  there is no allocation-failure plant, product hook, or fault-injection mode;
- invalid read states `{negative len, len > cap, null data with positive cap}`;
- read callback `{returns normally, panics}` with no consumption by the view;
- final drop proves every transferred HeapString and both Vec allocations are
  released exactly once through ordinary allocation counters.

The primitives unit/e2e tier keeps semantic `split`/`join` cases, including
empty separator/empty Vec and reuse of caller-owned inputs. No cyber-sensitive
instrumentation is required.

### 4.4 Public-interface assessment

R-3 adds two `pub` Rust-path functions to
`cranelisp_intrinsics::vec_runtime` and therefore changes
`crates/cranelisp-intrinsics/public-api.txt` and the crate-root consumed-surface
rustdoc. It does not alter the C ABI, heap layout, intrinsic catalog, language
specification, or `cranelisp-types`. FIXME 0860 carried this exact narrow
surface through architecture approval and implementation closure; the settled
cross-crate contract is `design/arch/bounded-contexts.md` §4b invariant 17.

## 5. R-4/R-5 master and rustdoc intent

The maintained runtime master should describe settled actors, invariants, data
flow, risks, tests, and rejected alternatives. Completed S73/S74 migration
instructions and retired-facade bookkeeping are historical, not target design.
This document supplies the settled R-1/R-2/R-3 content that the current master
must absorb; numeric primitive counts and baseline line counts are not
authority.

For R-5, crate-root primitives rustdoc should say only that the public Rust
surface comprises the process-static primitives table, its exported GOT slab,
and the public category modules. The committed `public-api.txt` is the
mechanical enumeration. Rustdoc must not embed counts of primitives, exported
functions, modules, or baseline lines. No semantic/public shape change is
authorised by that documentation repair.

## 6. Quality attributes and risks

- **Simplicity:** one private declaration inventory; two purpose-specific Vec
  functions; no general builder framework (Principle 6).
- **Maintainability:** adding a primitive edits one declaration; String
  primitives cannot drift from Vec layout/protocol (Principles 1 and 7).
- **Observability:** normal CLIF and public-mode behavior are the evidence;
  this sprint introduces no runtime diagnostics.
- **Concurrency:** no new shared state. Construction is unpublished until
  `len` is written last; scoped reads borrow immutable storage.
- **Performance:** one bulk allocation and one bulk copy for split, equivalent
  asymptotically to the current path. Join reads in place; it adds invariant
  checks but no element clone beyond its existing host-String construction.
- **Testability:** declaration projections and Vec transition points are named
  submodule seams with negative scenario matrices (Principles 5 and 23).

Primary risks are accidental widening into a general raw-`i64` Vec API,
publishing length before initialisation, double-consuming transferred String
handles, retaining a read slice, and mistaking R-3 for the excluded FIXME
0850. The selected types, scoped callback, rustdoc, and tests address these
directly.

## 7. Next skills

- `/arch` — maintain the approved two-function intrinsics surface and its
  public-api/rustdoc contract in `design/arch/bounded-contexts.md` §4b
  invariant 17 (FIXME 0860 resolved); arbitrate only if R-2 is required to
  distinguish `ProjectionOf` from `AliasOf` in interprocedural production RC.
- `/qa` — reconcile the R-2 plan with the verified consumer graph and the
  explicit partial-evidence boundary.
- `/testing` — retain the nine public-path witnesses with the direct inline Vec
  CLIF cases classified as body-semantic guards.
- `/dev` — narrow serial implementation: primitives R-1; intrinsics then
  primitives for R-3; finally R-4/R-5 doc/source reconciliation. No new R-2
  product seam is selected by this refinement.
- `/review` — verify each narrow implementation against this design.
