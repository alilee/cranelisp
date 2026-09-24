# Trait-impl cache carrier — the writer-side persisted record

**Status: RULING AND LANDED (S121, 2026-09-05); carrier half LANDED
(S119); producer + restore halves LANDED S121 (`/arch`, 2026-09-01 — §9);
fresh-registration transaction facade AMENDED by the executing C3 falsifier
(S121, 2026-09-01 — §§3–4).**
This is the durable cross-crate contract for the resolved sibling written-trait-impl
cache-restoration defect (former FIXME 0869), authored per the S118 Phase-2
ruling 1. The satisfied filing is retired; the landed carrier, producer and
restore obligations remain here and in the owning source contracts. The types carrier
(`WrittenTraitImpl`, `SymbolTable.written_trait_impls`,
`enrol_written_trait_impl`, `trait_impl_key`) landed S119 with unit coverage;
At the S121 opening it had **zero producers and zero readers** — the exact
"landed with zero consumers" pattern root `CLAUDE.md` §Assurance names. §9
closes that: the producer is C3's, the restore enrolment C6's, both inside
S121. The failing-not-ignored discriminator is
`tests/cache.rs::cache_restores_sibling_written_trait_impls_for_dispatch`.

> **Seam-name correction (S121 Phase 3).** §3 as written cites a typecheck
> `check_trait_impl` success point. **No such symbol exists at HEAD.** The
> registration seam is `register_trait_impl`
> (`crates/cranelisp-typecheck/src/traits/impl_check.rs:94`, invoked from
> `crates/cranelisp-typecheck/src/program/register.rs:66`) — the site that
> constructs the Decision-45 shell. §3's temporal rule (P26) is unchanged;
> only the seam's name was a phantom. The same phantom appears at **four**
> sites in the landed carrier rustdoc (`crates/cranelisp-types/src/module.rs:240`,
> `:884`, `:1570`, `:1587` — count corrected 2026-09-01 against live source;
> the earlier three-site enumeration missed `:1587`) — that correction is
> source text and **rides C3's producer
> change-set** (`arch` owns the types crate's voice; the edit is approved
> here so the wave needs no round-trip).

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
S114 typed-carrier precedent (schema-22 window;
[backend keyed consumption §8](backend-keyed-consumer.md#8-the-landed-carrier-surface)): post-bump, absence is a
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

The record is upserted by **typecheck** at the successful
`register_trait_impl` seam
(`crates/cranelisp-typecheck/src/traits/impl_check.rs:94`, invoked from
`program/register.rs:66`) — the same site that constructs the shell — from the
**same single-source values** the shell is built from (`fq_trait_name`,
`fq_impl_type`, `state.current_module`, `method_names`): one derivation, two
carriers (Principle 24; no re-resolution, no spelling re-parse). Per
Principle 26, the record rides the **same staging transaction as the shell**.
Fresh registration first retains the writer's method entries and stages the
candidate shell in the trait home. The writer record is deliberately not
touched until every method has checked and settled;
`upsert_written_trait_impl` is the final fallible table act before the
method/shell tokens commit. On failure the methods and shell restore/remove
while the prior writer record was never changed. This ordering is how the two
carriers commit or roll back together without a speculative writer-record
append.
The checkable invariant is **record ⟺ shell** — at any commit boundary the
writer's `written_trait_impls` set and the shells its registration wrote are
in bijection; a record without a committed shell, or a committed shell whose
writer holds no record, is a defect. A same-`(type, trait)` re-impl
(spec §5.4.5 hot reload) **upserts** its record under the `trait_impl_key`
identity — at most one record per key per writer, never an appended
duplicate.

## 4. One mint, restore enrolment, and fresh staging

The key mint and shell representation are shared. Restore and fresh
registration deliberately have different conflict policy because only fresh
registration must provisionally expose a same-key re-impl:

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
   silently choose one row; the FIXME's requirement). This remains the restore
   path; fresh registration uses item 3.

3. **Fresh-registration transaction facade.** The types-owned public surface
   is `stage_trait_impl_shell(&mut self, &WrittenTraitImpl) ->
   Result<StagedImplShell<C>, CranelispError>`,
   `rollback_trait_impl_shell(&mut self, StagedImplShell<C>)`, and
   `StagedImplShell::commit(self)`, plus
   `upsert_written_trait_impl(&mut self, WrittenTraitImpl)`. The opaque token
   retains an absent/identical/divergent prior same-key shell, never exposes a
   binding, and rollback verifies the staged candidate before restoring or
   removing it. Upsert validates writer ownership and non-empty methods, then
   replaces in place or appends exactly once per `trait_impl_key`.

   Method entries use the sibling types-owned `RetainedCallables<C>` token
   (`retain_callables` / `rollback_callables` / `commit`) from
   `symbol-table-lifecycle.md` §4.4. C3 derives one record, retains methods,
   stages the shell, checks and settles all methods, upserts the writer record,
   then commits both tokens. Any earlier failure rolls methods back and then
   the shell; an upsert refusal is non-mutating and takes the same rollback.
   The temporary candidate-shell/prior-record pairing exists only in staging;
   the record ⇔ shell bijection is exact at every cluster commit boundary.

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

**As built (S121).** `try_cache_hit_load` extracts writer records before moving
the table, rejects malformed provenance as a cache miss before installation,
synchronously restores each foreign canonical trait home, installs the writer,
and calls `enrol_written_trait_impl` for every record. The cache probe is
`Result<bool, CranelispError>`: an ordinary/stale miss is `Ok(false)`, while a
divergent live shell is a hard error rather than a silently selected occupant.
Both object and no-object registrations pass through this single restore entry
point.

## 6. Schema window

**As landed:** the carrier's window was `CACHE_SCHEMA_VERSION` **23→24, taken
S119** with the field's introduction. Old sidecars lacking the carrier are
invalidated wholesale by the version gate; no migration shim, no
`#[serde(default)]` back-compat (Principle 8 — a default-empty read of a
pre-carrier sidecar would silently reproduce the defect this carrier cures).

**S121:** the producer and restore halves take **no schema increment** — the
field is already serde-mandatory at 24, and the S121 24→25 window belongs to
C1's lifecycle wash (the S121 lifecycle migration, retained in Git history), which this contract
reads and never bumps.

**Named residual (S121, honest grade: asserted-with-a-falsifier).** Inside the
S121 wash there is a window in which schema-25 sidecars can be written after
C1 lands and before C3's producer lands; such a sidecar carries a **valid but
empty** `written_trait_impls` and would restore impls-lost if trusted. The
exposure is developer-local caches inside the wash only — acceptance evidence
runs against post-C3 caches (the e2e discriminator builds its own cache in a
scratch dir), and any pre-C1 sidecar is wholesale-invalidated by the 24→25
gate. Falsifier: a parity failure reproduced from a sidecar whose write
predates the producer's landing; disposition is regenerate, never a shim.

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
- **Producer unit rows (C3, added S121):** record ⟺ shell bijection — the
  record appears iff the impl's registration commits (absent for a failed or
  rolled-back impl); a same-key re-impl upserts (one record, not two); the
  record's five fields equal the shell's construction values byte-for-byte;
  both hand-rolled `impl$` sites route through `trait_impl_key` (grep-zero
  `format!("impl$…")` outside the mint).

## 9. S121 allocation (the C6 H1 blocker, discharged 2026-09-01)

The S121 C6 int visit verified the carrier had **no producer and no scheduled
producer** — an enrolment loop over a
permanently empty vector cannot flip the discriminator. `arch` rules the
allocation rather than rejecting the feature (SPRINT's C3 scope row already
carried "populate the already-landed written-trait carrier"; the C3 design
visit closed without it — the omission is a scheduling gap, not a design
question):

- **C3 (typecheck) — the producer.** The §3 success-only upsert at
  `register_trait_impl`
  (`traits/impl_check.rs:94` / `program/register.rs:66`), the re-pointing of
  the two hand-rolled `impl$` format sites
  (`traits/impl_check.rs:421`, `traits/dispatch.rs:143` — verified live at
  HEAD) onto `trait_impl_key`, and the `module.rs:240`/`:884`/`:1570`/`:1587`
  rustdoc seam-name correction (four sites, verified 2026-09-01). **This
  contract's amended §§3–4 and `symbol-table-lifecycle.md` §§4.4/5.7 are the
  complete interior design**: retain methods, stage shell, check/settle,
  success-only writer upsert, then token commit. The executing falsifier
  required the C1 facade reopen; C3 consumes that repaired contract without
  inventing a local transaction vocabulary, alongside `bounded-contexts.md`
  §2's `instantiate_demands` contract.
  Zero typecheck public-API delta; zero schema delta (§6).
- **C6 (int, bundle N3) — the restore enrolment**, exactly as section 5 of this
  contract and [cache-hit loading](../int/cache-hit-loading.md) design it, at both cache
  entry points, after the writer's
  dependency closure installs. N3's entry gate "0869 producer placed" reads
  **"C3's producer landed"**.
- **Order:** C3 before C6's N3 — already the §9 stream order of
  `symbol-table-lifecycle.md`; no reordering needed.
