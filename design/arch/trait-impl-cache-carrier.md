# Trait-impl cache carrier — the writer-side persisted record

**Status: RULING (S118 Phase 3, `/arch`, 2026-07-25) — pre-implementation.**
This is the binding cross-crate contract for FIXME 0869
(`design/arch/fixmes/0869-cache-restoration-loses-sibling-written-trait-impls.md`),
authored per the S118 Phase-2 ruling 1 (`sprints/SPRINT.md` §Architecture
review). Implementation is capacity-conditional Track D this sprint; if cut,
the ruling carries to S119 unchanged. The failing-not-ignored discriminator is
`tests/cache.rs::cache_restores_sibling_written_trait_impls_for_dispatch`.

**Archive trigger:** the implementation lands and the contract folds into
`crates/cranelisp-types/src/module.rs` rustdoc (the record + helper), 
`design/arch/interfaces.md` §(new "Written-impl cache carrier"), and
`bounded-contexts.md` §7 (types) + §6 (int restore seam); then this file moves
to `archive/`.

## 1. The defect, and why the trait-home snapshot cannot be the durable home

Decision 45 (amended S110 §1.1.1) splits a trait impl across two tables: the
**discovery shell** (`ModuleEntry::TraitImpl`, keyed `impl$FQType$FQTrait`)
lives in the **trait's home module**; the mangled method `Def`s + GOT slots
live in the **impl-writer's module**. Fresh compilation writes both. Cache
persistence, however, snapshots per module — and the trait home's snapshot may
be written *before* a sibling's impl later mutates that live table (the
observed loss), or the trait home may be a cache **hit** while the writer
recompiles fresh. There is no snapshot ordering that makes the trait-home
sidecar a reliable carrier of impls *other modules* wrote into it, and
coupling snapshot timing across modules would break per-module cache
independence (`design/backend/module-caching.md` — module-granular caching is
the design's first goal).

The durable home is therefore the **causal producer**: the writer module.
Restoration re-derives the shell from a writer-side record — never from
mangled-name parsing, never from a foreign-table scan (both banned by the
Phase-2 ruling; a mangled-spelling parse is a second resolver, Principle 24).

## 2. The carrier — `WrittenTraitImpl` on the writer's `SymbolTable`

**Record type** (`crates/cranelisp-types/src/module.rs`, beside
`ModuleEntry::TraitImpl`):

```rust
/// One trait impl this module WROTE (the persistence projection of the
/// `ModuleEntry::TraitImpl` discovery shell that fresh registration placed
/// in the trait's home table). Serde-visible on the module's `.meta.json`;
/// restoration re-enrols the shell from this record.
#[non_exhaustive]
pub struct WrittenTraitImpl {
    pub trait_name: FQTraitName,      // canonical, resolved (never re-derived)
    pub impl_type: FQTypeName,        // canonical, resolved
    pub impl_module: ModuleFullPath,  // == the owning table's module (validated at load)
    pub methods: Vec<Symbol>,         // local method names (not mangled)
    pub visibility: Visibility,       // Public per spec §5.11.1
}
```

**Carried as** `SymbolTable.written_trait_impls: Vec<WrittenTraitImpl>` — the
established per-module-metadata placement (the Decision-32/33 family:
structural decls as fields on `SymbolTable`). **No `#[serde(default)]`** — the
typed-resolution-carrier precedent (schema-22 window): post-bump, absence is a
hard serde error, not a silently-empty default. Vec order is registration
order (deterministic from source; keeps `.meta.json` byte-reproducible).

**Placement ruling — the record type lives in `cranelisp-types`. This is a
public delta on the types crate** (record type + the two functions of §4;
`public-api.txt` regenerated in the implementing change-set). Placement is
structurally forced, not preferential: the carrier rides the writer's
`SymbolTable`, which is types-defined and depends on nothing — a
typecheck-defined record cannot appear as its field. Principle 15 is also
satisfied on its own terms: the record's structure is interpreted by typecheck
(producer) and by the enrolment seam that int's restore path calls, and the
established home for definition-seam operations over symbol tables shared by
typecheck and int is the types crate (`reject_def_over_binding`,
`chain_follow_committed` precedents). **No other crate takes a public-surface
delta**: backend persists the field for free through the existing generic
`serialise_meta`/`deserialise_meta` (the `CACHE_SCHEMA_VERSION` value edit does
not change `public-api.txt` shape); int's restore call sites are binary-private.

## 3. Producer seam — recorded once, from settled state

The record is appended by **typecheck** at the `check_trait_impl` seam
(`crates/cranelisp-typecheck/src/traits/impl_check.rs`) — the same site that
constructs the shell — from the **same single-source values** the shell is
built from (`fq_trait_name`, `fq_impl_type`, `state.current_module`,
`method_names`): one derivation, two carriers (Principle 24; no re-resolution,
no spelling re-parse). Per Principle 26, the append happens at the **success
point of the impl's method-check transaction** (the shell is staged before
method checks and rolled back on failure; the record must never persist for a
failed or rolled-back impl — appending after the transaction settles is
simpler than staging + rollback of the record, and is the required shape). The
write targets the **writer's own table** through the orchestrator accessor
(Decision 44 — it commits with the writer's staging like the method `Def`s).

## 4. One mint, one enrolment helper — shared by fresh and restore

Two functions in `cranelisp-types`, both routed through by BOTH the fresh path
and the restore path (Principle 7; the "reusing fresh registration's checks"
constraint of the Phase-2 ruling):

1. **`pub fn trait_impl_key(&FQTypeName, &FQTraitName) -> Symbol`** — the ONE
   mint of the `impl$FQType$FQTrait` storage key, hoisted beside `member_key`
   (the established mint-point pattern, `resolve.rs`). Today the format string
   is hand-rolled at two typecheck sites (`impl_check.rs:421`,
   `dispatch.rs:143`) — the implementing change-set re-points both. This also
   discharges the safety-register R4 (keyed-identity injectivity) census
   obligation for the `impl$` family: one mint, injective by construction over
   canonical FQ inputs.

2. **`pub fn enrol_written_trait_impl(table: &mut SymbolTable<C, L>, record:
   &WrittenTraitImpl) -> Result<EnrolOutcome, CranelispError>`** — the ONE
   idempotent shell-enrolment primitive over the **trait home's** table.
   Semantics: mint the key via (1); probe; **absent** → insert the shell
   (`ModuleEntry::TraitImpl` with the record's five fields) → `Enrolled`;
   **present and payload-identical** → no-op → `AlreadyEnrolled` (idempotence
   under multi-path restore); **present and payload-divergent** → hard error
   naming both payloads (deterministic conflict handling — reject, never
   silently choose one row; the FIXME's requirement). Fresh registration's
   staged insert routes its key mint and its conflict discrimination through
   the same two functions (its retain-prior/rollback transaction wraps the
   call; the transaction mechanics stay typecheck-internal).

## 5. Restore-time contract (int)

- Enrolment runs during cache restoration **after the writer's table and its
  dependency closure are installed** (the FIXME's ordering), at a chokepoint
  covered by **both** restore entry points — `register_module_cached` AND
  `register_module_cached_no_object` (the S108 lesson: the no-object path
  bypasses publication hooks; a single-entry-point enrolment silently misses
  it).
- Idempotence when multiple dependency paths restore the writer is carried by
  the helper's `AlreadyEnrolled` arm, not by caller bookkeeping.
- **R6 trust boundary** (`design/arch/safety-invariants.md` §4): the record is
  a new persisted carrier, so its load-side validation lands **in the
  introducing change-set** (the register's maintenance rule): well-formed
  canonical FQ names, `impl_module` equal to the owning sidecar's module path,
  non-empty method list. A violation is a diagnosed `CacheStale` (recompile),
  never trusted into enrolment. The implementing change-set extends the R6
  census row accordingly.
- The restored state preserves: one canonical discovery shell in the trait
  home; writer-owned mangled methods + GOT slots (untouched by this mechanism
  — they already restore correctly); fresh/warm `Run` dispatch equivalence;
  qualified and imported-bare impl-head equivalence (both variants produce the
  same canonical record at the producer, so restore cannot distinguish them).

## 6. Schema window

`CACHE_SCHEMA_VERSION` 23→24 in the implementing change-set — **the sole S118
bump** (Phase-2 ruling 1; QA plan §1 blocks any other schema delta at close).
Old sidecars lacking the carrier are invalidated wholesale by the version
gate; no migration shim, no `#[serde(default)]` back-compat (Principle 8 — a
default-empty read of a pre-24 sidecar would silently reproduce the defect
this carrier cures).

## 7. Principle-7 second-home justification (required by the Phase-2 ruling)

The record duplicates the shell's five fields. The justification for the
second home: **authority is split by lifetime, with one derivation and one
reconciliation seam.** In a live session the trait-home shell is the sole
discovery authority (dispatch never reads the record). Across sessions the
writer's record is the sole persistence authority for impls the writer
produced (the trait-home sidecar cannot carry them reliably — §1). Both
carriers are written from ONE derivation at ONE seam (§3), and the enrolment
helper's conflict discrimination (§4) is the standing check that the two can
never silently diverge: a divergent shell/record pairing is a hard error at
restore, not a pick. This is the same shape as `got_slot`-in-GOT vs
`Def`-entry (one authority per question, cross-checked at the seam), not the
parallel-store defect P7 forbids.

**Rejected alternatives** (recorded per the facade-rationale convention):

- *Re-snapshot the trait home after sibling writes* — couples cache-write
  timing across modules and still loses on a trait-home cache hit + writer
  fresh recompile; breaks module-granular cache independence.
- *Reconstruct at restore by parsing mangled method `Def` spellings in the
  writer's table* — a second resolver over a spelling (P24's banned shape);
  explicitly excluded by the Phase-2 ruling and the FIXME.
- *Scan foreign tables at restore for orphaned method families* — an ambient
  scan as identity source (P24) over tables whose population is
  restore-order-dependent.
- *An int-private sidecar beside `.meta.json`* — a second cache-metadata home
  and a second trust boundary (P7 + R6); the module's cache metadata is the
  serialized `SymbolTable`, and the record belongs in it.
- *A duplicate `ModuleEntry::TraitImpl` in the writer's own table* — pollutes
  the writer's resolution namespace with a discovery-shaped entry, blurring
  the Decision-45 discovery/storage split ("one canonical discovery shell").

## 8. Acceptance

- The committed discriminator
  `tests/cache.rs::cache_restores_sibling_written_trait_impls_for_dispatch`
  flips green (both qualification variants).
- Owner unit tests per the FIXME: writer-side projection (record appears iff
  the impl transaction settles), restore-time enrolment, idempotent replay
  (`AlreadyEnrolled`), malformed-record rejection (`CacheStale`), divergent
  conflict rejection (hard error, no silent pick).
- QA's stale-cache-rejection cell (`tests/plan/s118-test-plan.md`, 0869
  conditional row) — a pre-24 sidecar is rejected by the version gate.
