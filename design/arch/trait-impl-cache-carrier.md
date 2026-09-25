# Trait-impl cache carrier — the writer-side persisted record

**Status: current cross-crate contract, delivered.** A trait implementation
written in one module but discovered through the trait's home module survives
cache restoration because its writer persists a record from which restore
re-enrols the discovery shell. Types owns the record and its mint and enrolment
functions; typecheck produces the record; int restores it. Exact API promises
are the rustdoc on `WrittenTraitImpl` and the functions below
(`crates/cranelisp-types/src/module.rs`). The executing discriminator is
`tests/cache.rs::cache_restores_sibling_written_trait_impls_for_dispatch`.

## 1. Why the trait home cannot be the durable home

Decision 45 splits a trait implementation across two tables: the **discovery
shell** (`Decl::ImplShell`, keyed `impl$FQType$FQTrait`) lives in the **trait's
home module**; the mangled method entries and their GOT slots live in the
**writer's module**.

- Cache persistence snapshots per module. The trait home's snapshot can be
  written before a sibling's implementation mutates that live table, or the
  trait home can be a cache hit while the writer recompiles.
- No snapshot ordering makes the trait home's sidecar a reliable carrier of
  implementations other modules wrote into it, and coupling snapshot timing
  across modules would break module-granular caching
  ([module caching](../backend/module-caching.md) §1).

The durable home is therefore the **causal producer**, the writer module.
Restoration re-derives the shell from the writer's record — never by parsing
mangled names and never by scanning foreign tables; either would be a second
resolver ([Principle 24](principles/24-resolve-once.md)).

## 2. The carrier — `WrittenTraitImpl` on the writer's `SymbolTable`

- `WrittenTraitImpl { trait_name, impl_type, impl_module, methods, visibility }`
  records the canonical trait and type, the writer module, the local
  (unmangled) method names and the implementation's visibility.
- It is carried as `SymbolTable.written_trait_impls`, in registration order,
  which keeps sidecars reproducible.
- **The field has no `#[serde(default)]`.** A sidecar without it is a hard
  serde error, never a silently empty carrier; a default-empty read would
  reproduce the defect this carrier cures.
- **It lives in `cranelisp-types` because it rides the writer's
  `SymbolTable`**, and it is interpreted by typecheck (producer) and by the
  enrolment seam int calls; definition-seam operations over shared tables
  belong to the types crate. Backend persists it through the generic sidecar
  serialisation and takes no surface change.

## 3. Producer seam — recorded once, from settled state

Typecheck records the implementation at its successful `register_trait_impl`
seam, from the same resolved values that build the shell: one derivation, two
carriers ([Principle 26](principles/26-record-from-settled-state.md)).

- The record rides the shell's staging transaction. Fresh registration retains
  the writer's method entries and stages the candidate shell; the writer
  record is upserted only after every method has checked and settled, as the
  last fallible act before the method and shell tokens commit. On failure,
  methods and shell roll back and the prior writer record is untouched.
- **Invariant: record ⟺ shell.** At every commit boundary the writer's
  records and the shells its registration wrote are in bijection. A record
  without a committed shell, or a committed shell whose writer holds no
  record, is a defect.
- A same-type, same-trait re-implementation (`spec/05-definitions.md` §5.4.5
  hot reload) upserts under its `trait_impl_key`: at most one record per key
  per writer.

## 4. One mint, restore enrolment, and fresh staging

The key mint and shell representation are shared. Restore and fresh
registration have different conflict policy, because only fresh registration
provisionally exposes a same-key re-implementation.

1. **`trait_impl_key(&FQTypeName, &FQTraitName)`** is the one mint of the
   `impl$FQType$FQTrait` storage key, beside `member_key` in `resolve.rs`. It is
   injective over canonical inputs, which discharges the keyed-identity
   obligation for the `impl$` family (register R4 in
   [safety invariants](safety-invariants.md)). Do not hand-roll the format.
2. **`enrol_written_trait_impl(table, record)`** is the one idempotent
   restore enrolment over the trait home's table. Absent: insert the shell
   (`Enrolled`). Present and identical: no-op (`AlreadyEnrolled`), which
   carries idempotence when several dependency paths restore the writer.
   Present and divergent: a hard error naming both payloads — never a silent
   choice.
3. **Fresh registration** uses `stage_trait_impl_shell`, which returns an
   opaque `StagedImplShell` committed by `StagedImplShell::commit` or undone by
   `rollback_trait_impl_shell`, together with `upsert_written_trait_impl`. The
   token retains any prior same-key shell and verifies the staged candidate
   before restoring or removing it. Upsert validates writer ownership and a
   non-empty method list, then replaces in place or appends once per key.
   Method entries use the sibling `RetainedCallables` token, whose contract is
   its rustdoc.

## 5. Restore-time contract (int)

- Restoration extracts the writer's records before installing its table,
  rejects malformed provenance as a cache miss, restores each foreign trait
  home first, installs the writer, then enrols every record. Both the object
  and no-object registrations pass through the one cache-restore entry
  ([restoration parity](../int/int.md#75-restoration-parity)).
- A divergent live shell is a hard error, not an ordinary miss.
- **Trust boundary.** Each loaded record is validated before enrolment:
  canonical names are well formed, `impl_module` equals the owning sidecar's
  module and the method list is non-empty. A violation is a diagnosed
  `CacheStale` and a recompile (register R6 in
  [safety invariants](safety-invariants.md)).
- The restored state has one canonical discovery shell in the trait home,
  the writer's own methods and slots, and the same dispatch as a fresh run.
  Qualified and imported-bare implementation heads produce the same canonical
  record, so restore cannot distinguish them.

## 6. Schema window

The field is serde-mandatory: a sidecar predating it fails the
`CACHE_SCHEMA_VERSION` gate and recompiles wholesale, with no migration shim.
A change to the record's serde shape or meaning is an ordinary schema bump under
the [types cache contract](../../crates/cranelisp-types/CLAUDE.md#the-serde-shape-is-the-cache-contract).

## 7. Why a second home is justified (Principle 7)

The record duplicates the shell's fields. Authority is split by lifetime, with
one derivation and one reconciliation seam:

- in a live session the trait-home shell is the sole discovery authority, and
  dispatch never reads the record;
- across sessions the writer's record is the sole persistence authority for
  the implementations it wrote (§1);
- both are written from one derivation at one seam (§3), and restore
  enrolment's conflict rule (§4) makes a divergent pairing a hard error.

Rejected alternatives, each of which a reasonable contributor might propose:

- **Re-snapshot the trait home after sibling writes** — couples cache-write
  timing across modules and still loses on a trait-home hit with a fresh
  writer.
- **Parse mangled method names in the writer's table at restore** — a second
  resolver over a spelling (Principle 24).
- **Scan foreign tables for orphaned method families** — an ambient scan as an
  identity source, over restore-order-dependent tables.
- **An int-private sidecar beside `.meta.json`** — a second cache-metadata home
  and a second trust boundary.
- **A duplicate shell in the writer's own table** — pollutes the writer's
  resolution namespace and blurs the discovery/storage split.

## 8. Evidence

- **Measured end to end.**
  `tests/cache.rs::cache_restores_sibling_written_trait_impls_for_dispatch`
  observes warm dispatch through a sibling-written implementation, for both
  qualification variants.
- **Measured in types.** `crates/cranelisp-types/src/module/tests.rs` covers
  shell staging and rollback, refusal of intervening writes and a wrong trait
  home, and one upsert per key with writer checking.
- **Not directly unit-tested** (found 2026-09-25): restore enrolment's
  `AlreadyEnrolled` and divergent-conflict arms, malformed-record rejection at
  load, and typecheck's record ⟺ shell bijection. Only the end-to-end cell
  exercises them. `qa` owns whether that evidence is sufficient.
