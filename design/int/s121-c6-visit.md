# The S121 C6 binary / exe-bundle visit — one interior change

**Status:** DESIGN — authored S121 Phase 3, `/design`(int: `src/` +
`crates/cranelisp-exe-bundle/`); reconciled 2026-09-01 to the two `arch`
rulings that discharged its blockers, and again the same day to allocate the
fifth annotated-sexp census row (`annotated-sexp-node.md` §7's 2026-09-01
current-state correction) into N5 as §7.3.1. Every claim below was verified
against live source in this window; where a filing's central claim is already
discharged, that is recorded as a disposition rather than re-designed (§11).
The 2026-09-03 root integration census then falsified the former zero-public-
delta entry condition twice: §14 records the implemented, baseline-confirmed
metadata mutation and the implemented, independently reviewed
compiled-publication transaction whose generated baseline the user confirmed
on 2026-09-03. Both went through their individual pre-implementation and
post-implementation user gates. The user then approved the source-ordered
macro checkpoint rule: a complete `defmacro` publishes immediately and is not
rolled back by a later form. This supersedes N5's former cluster-wide
`TurnCheckWorld`/`PreparedMacroTurn` design; §7 and §13.1 carry the replacement.
**Subordinate to:** `int.md`.

The two blockers C6 opened with remain discharged: the 0869 producer is C3's
(`trait-impl-cache-carrier.md` §9), and the 0798 scoped alias lookup is C1's
walk plus C3's one call-site flip (`module-alias-scoped-lookup.md`). The
all-features census found the metadata facade gap at the existing agent
Document-write seam, and the prepared-turn realization found that staged
publication needed owner attachment in the same one-module transaction.
Section 14 records both approved boundaries; neither may be worked around in
int. Cross-module and whole-source macro atomicity are not requirements.

**Consumes, does not decide:**

- `design/arch/symbol-table-lifecycle.md` §§4.1–4.4, 5.2 and 6 — the current
  one `Life`/`Realization` machine, `retired_slots`, `MonoDemand`/
  `InstanceLink` and load-boundary revalidation. The single
  `CACHE_SCHEMA_VERSION` 24→25 window and C6 stream allocation are S121
  migration provenance in [the lifecycle design at checkpoint
  `dc78ddbe`](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/symbol-table-lifecycle.md)
  §9, not current scheduling instructions.
- `design/arch/bounded-contexts.md` §2 — the approved `instantiate_demands`
  facade and its C3→C6 handoff clause.
- `design/arch/bounded-contexts.md` §6 — the macro-clause ABI ownership ruling
  (absorbed here at §7.1) and the `Introspection` narrowing.
- `design/arch/symbol-table-lifecycle.md` §4.4 and the
  `crates/cranelisp-types/src/module.rs::publish_compiled_staged` rustdoc — the
  current compiled-publication transaction, owner-conserving refusal and GOT
  rollback order used by N1.
- `design/arch/trait-impl-cache-carrier.md` — the `WrittenTraitImpl` carrier,
  its enrolment primitive, and §9's allocation of the producer to C3 and the
  restore enrolment to C6 N3, with §6's named intra-wash residual (a valid
  empty schema-25 sidecar between C1 and C3 regenerates; it is never shimmed).
- `design/arch/module-alias-scoped-lookup.md` — the scoped segment walk of
  keyed probes, its visibility rule, the one `module_alias_key` mint, and the
  C1 → C3 → C6 allocation. C6 owns the int writers and consumers only.
- `design/backend/s122-closure.md` §2 — the backend twin of the result-root
  rule; C4 removes it, C6 removes int's (the local result-root section below).
- `design/runtime/s119-typed-consume-funnel.md` §3 — the `Owned`/`Borrowed`
  vocabulary, `from_abi`/`into_raw`, `is_nullary_tag`, and the `pub`
  `consume_sexp`/`consume_slist` signatures C6 discharges through.
- [ownership/disposal 5](../intrinsics/ownership-and-disposal.md#5-the-sexp-family) — the `TAG_SEXP_ANNOTATED`
  arm of `consume_sexp` (C5 bundle I1), which is C6's Rule-4 precondition.
- C2's published quote classifier (`quote_head`/`QuoteHead` beside `Sexp`),
  consumed by the scope-aware quote shield.

**Re-rules within int:** `prelude-table-write-isolation.md` §2.1/§2.4 (census
closure); `impl-redefinition-hot-reload.md` §3/§5 (enrolment derivation);
`macro-turn-ownership.md` §3 Rule 0, §8, §12 (Rule-0 pin, discharged
dependencies); `session-transaction.md` §10 CS-1 (the reload driver);
`result-owner.md` §1.1.1/§4.2.1 (the strip-rule collapse, the `/mem` window).

**Carries:** FIXMEs 0050, 0052, 0604, 0694, 0708, 0740, 0745, 0793, 0795, 0798,
0800, 0818, 0863, 0868, 0869, 0889, 0898, 0914, 0921, 0927, 0933, plus the C6
half of 0553.

---

## 1. The one sentence

Int stops carrying four private copies of facts its neighbours now own — the
symbol lifecycle, the result-root rule, the RC primitive, the instantiation
trigger — and, in the same visit, makes the **cache-restored world equal the
freshly-built one** for every relationship a module can hold: its declared
children, the trait impls it wrote, its module aliases, and its monomorphic
instances.

Everything else in the visit falls out of those two: the census closes because
the lifecycle names its own writers; the macro turn balances because the
releaser lives in intrinsics; presentation becomes truthful because each macro
definition has a complete publication checkpoint.

## 2. What is genuinely new here, and what is consumption

Three of C6's six bundles are **consumption** of contracts settled upstream in
this sprint — they are large in site count and small in judgment. Naming that
split up front is what keeps the visit one visit:

| Bundle | Judgment C6 makes | Judgment C6 consumes |
|---|---|---|
| N1 lifecycle | where the freeze half lands; how a restore seam revalidates | the `Life` machine, `retired_slots`, schema 24→25 |
| N2 reload driver | the capture projection and its exact ordering | `instantiate_demands`' semantics (decline-as-warning, synthetic site, idempotence) |
| N3 restoration parity | the enrolment points and their idempotence obligations; which int writers and consumers carry the alias keying and the referring module | `enrol_written_trait_impl` (over C3's producer output), `drive_submodules`, the scoped alias walk + `module_alias_key` |
| N4 macro turn | nothing new — §7.1 absorbs an arch ruling | Rules 0–7, the typed handle pair, the tag-7 arm |
| N5 macro checkpoint + presentation | source continuation and one-module checkpoint integration | the user-approved checkpoint rule and `s117-conformance-recovery.md` §1.1.2/§2.1/§6 |
| N6 platform + result | the located refusal's frame; the third-encoding collapse | the manifest-order mint, `ConcreteType::result_root` |

## 3. Bundle N1 — consume the lifecycle

[The S121 lifecycle design at checkpoint
`dc78ddbe`](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/symbol-table-lifecycle.md)
§9 row 5 allocated C6's obligation in four clauses. Each was a relocation of
authority *out* of int, not a new int mechanism.

### 3.1 The commit gate keeps its policy, loses its bookkeeping

The redefinition commit gate stays the single live-slot policy authority
(§4.3's "forced by staging/commit concurrency"): it is int that knows a staged
table is a parallel world whose slots are re-pointed at commit. What moves is
the *record* of a de-claimed index. Today an `AbiChanging` redefinition freezes
the old slot by leaving it populated and retaining its `Code` in the int-side
retention pool, and nothing in the table says the index is spent. After the
wash the gate performs one additional act: the displaced index moves into the
table's `retired_slots` with `RetireReason::AbiChanging { symbol }`.

The two halves are deliberately not merged. `retired_slots` is the **index**
tombstone and lives table-side because the mint's allocation authority is
`claims ∪ tombstones` and that derivation must survive serialization. The
retention pool is the **pages** owner and stays int-side because `Code` does
not serialize. Both are the one Principle-22 owner, each at the layer that owns
its half; `session-transaction.md` §6 keeps the pool's contract unchanged.

The `Template` flip transition (`Declared` → `Template` with a `prior` slot)
also lands in `retired_slots`, with `RetireReason::TemplateFlip { symbol }`.
Int reaches it through the same gate: a redefinition from a concrete `defn` to
a polymorphic one is exactly the slot-less-displacement class the gate already
classifies (`session-transaction.md` §10 T1), and it is the class whose crash
edge FIXME 0479 closed by retaining `Code`. The tombstone makes the index half
as explicit as the pages half already is.

### 3.2 `Broken` moves into the table

`redefine.rs::mark_broken` today paints a symbol broken through int-side state
plus a trap stub, and the entry itself does not say it is broken
(`session-transaction.md` §5.1). `Life::Broken { slot, error }` makes that
state representable where every reader already looks. Int's obligations:

- `mark_broken` transitions the entry through the funnel rather than mutating
  around it; the slot is **retained**, which is what keeps the trap stub
  reachable and the index claimed for the §4.3 scan;
- `BrokenProvenance` carries the depth-1 provenance `session-transaction.md`
  §5.2 already specifies — no transitive breaking, no new provenance kind;
- `/info` / `/sig` broken status (§9.2) reads the state instead of the
  int-side side-table; the recovery paths of §5.3 become ordinary transitions
  back through `declare` → `settle_concrete`.

The int-side broken registry deletes. This is the same shape as §3.1: the
*policy* (what breaks, how deep, how it recovers) stays int's; the *record*
moves to the entry.

### 3.3 The platform cursor write deletes

`src/platform.rs:351` writes `table.next_got_slot = platform.descriptors.len()`
after wrapping the DLL slab. Under §4.3 the stored cursor field is gone and
allocation authority is re-derived from claims ∪ tombstones, so a manifest
claim is an ordinary claim and this write has nothing to do. It deletes; §10
covers the mint that replaces it.

### 3.4 Every restore seam revalidates at the load boundary

Serde bypasses every funnel (§4.4), so the load boundary is the tier-3 seam
check for the whole machine. Int owns two of the three entry points to it, and
they must not each grow a private check:

| Seam | Where | Obligation |
|---|---|---|
| cache-hit registration | `src/process_form/cache_restore.rs:331` (`register_cached_with_scheduler`) → `register_module_cached{,_no_object}` | one call into the types-owned load validation, before any entry is exposed; a failure is `CacheStale`, treated exactly as a stale sidecar |
| session persistence restore | `src/save.rs` regen path / degraded startup | same call, same failure class |

The validation itself — slot uniqueness, `slot ⇒ is_concrete()`, origin×state
legality, tombstone conservation — is C1's, published once. Int calls it and
maps its refusal onto the existing stale-cache route; int does **not** re-derive
any of its clauses. A private int-side check of a lifecycle invariant is a
`/review` reject (§16).

## 4. Bundle N2 — the 0553 reload driver

### 4.1 What is being replaced

At the S121 measurement point, the former `capture_instantiation_drivers`
helper in `src/redefine.rs` read the module's live `__expr`
`Introspection.sexp` and handed it to the then-current `extra_forms` parameter
of `reload_module` in `src/session_v4/lifecycle.rs`, which appended it to the
re-parsed program. `drive_t1_full_cure` sequenced the three operations.

The mechanism is correct for the reachable case and was accepted as such
(`session-transaction.md` §10 CS-1). It carries two structural limits the
filing names: only the **last** `__expr` survives to be replayed, and the
record is session-persistent, so a cure firing on an unrelated later turn can
re-inject a now-ill-typed form and degrade a clean cure to the CS-3
error-blocked floor. Both are properties of replaying a *form*.

### 4.2 The replacement — a demand-set projection

After the C1 wash, every monomorphic instance is an entry born
`Life::Concrete { minted_from: Some(InstanceLink { template, type_args }), .. }`.
The capture is therefore a **projection of the reloading module's own table**,
not session bookkeeping:

> For each entry in the target module whose `life` is `Concrete` with
> `minted_from = Some(link)`, emit
> `MonoDemand::from_type_args(link.template, link.type_args.clone(), Span::SYNTHETIC)`.

Three properties follow directly and are the reason this is the general cure:

1. **Every historical instantiation is covered**, not the last one. The table
   holds all live instances; `__expr` held one.
2. **No stale-form hazard exists.** A demand names a template and concrete
   arguments. There is no expression to re-typecheck, so nothing can have
   acquired ill-typedness since it was minted.
3. **No new session state.** The projection reads what the lifecycle already
   records for its own reasons; `Introspection` stops being an instantiation
   ledger (Principle 7 — the reason the `.cl` stopped being one at S106).

### 4.3 Exact ordering

The driver is end-of-turn sequenced, as CS-1 already requires. The demand set
must be read from the pre-reload world and applied to the post-reload one:

```
T1 downgrade survives the §9.1.1 F2 slot-refined trigger
  1. regenerate_backing_file(target.module)          — source is now current
  2. demands := project minted_from over target.module's LIVE table
  3. reload_module(target.module, path)              — from source; Replace commit
  4. wait for the reload's terminal signal
  5. instantiate_demands(demands, ctx, …)            — after the reload settles
  6. poll_and_reload dependent cascade               — unchanged
```

Step 2 is **before** step 3 and after step 1. Before step 3 because the Replace
commit is what displaces the old instances — reading after it yields an empty
projection. After step 1 because `regenerate_backing_file` must not observe a
half-built world; it does not touch instances, so the order between 1 and 2 is
free, and pinning it removes a question rather than answering one.

Step 5 is **after** the reload's terminal signal, not interleaved with it: the
demands are against the *new* templates, and a demand raised before the
template settles would take the `CheckError::Gap` arm and re-enter the
orchestrator loop for a module the eval thread is already driving. Waiting is
what the eval thread already does at this seam (`wait_inmem_complete_blocking`,
the S93 watcher ruling), so this adds no new blocking discipline.

### 4.4 Outcome handling

`instantiate_demands` returns an ordinary `CheckResult`. C6 maps it onto the
existing turn report and nothing else:

- `CheckResult.warnings` — the legitimately-declined demands (a reload that
  changed a symbol's arity orphans its old variants). These render through the
  existing `TransactionReport` warning channel. They are **not** a cure
  failure: declining below the driver-replay floor would be a regression, and
  declining *above* it is the point.
- `Err(CheckError::Gap)` — the ordinary load-and-retry the orchestrator already
  handles; it means a template's home module is absent, not that a demand was
  stale.
- Any other `Err` — the CS-3 error-blocked degrade, unchanged
  (`session-transaction.md` §10 CS-3, the 0489 prompt floor).

### 4.5 What retires in the same change-set

`capture_instantiation_drivers`, `reload_module`'s `extra_forms` parameter and
its `parsed.extend_from_slice` append, and the `SYNTHETIC_EXPR_WRAPPER`
introspection read that fed them. **No source-form replay fallback survives.**
A partial landing that keeps the replay path as a fallback is a `/review`
reject: two instantiation triggers for one obligation is the mirror class this
spine exists to remove, and the fallback's own stale-`__expr` wart is one of
the two defects being cured.

## 5. Bundle N3 — fresh, warm, reload and concurrent publication agree

This is the visit's largest behavioural bundle and the one the sprint's RED set
concentrates in. The organising claim is Principle 11: **a restored world is
not a second kind of world.** Every gap below is a step the fresh path performs
that the restore path silently omits, and every cure is the *same* call at the
equivalent lifecycle point — never a cache-specific parallel.

### 5.1 Declared children (0868)

Fresh: `process_form.rs:413-416` calls `dependency.rs:1090::drive_submodules`
after the parent's cluster reaches `ClusterOnce::Done`, which resolves each
`ModDecl` child relative to the declaring parent's real file and drives it.

Warm: `cache_restore.rs` recurses on `imports` + `reexport_deps` only
(`:86-90`); `register_cached_with_scheduler` (`:331`) performs no child
enrolment. The persisted table already carries the `submodules` declaration —
the structural state is restored, the *act* is not.

**As built.** Fresh `drive_submodule` and cache restore both call the same
`enrol_declared_submodule` registrar. It owns child path resolution, watcher
mapping, recursive cache restore and fresh scheduler registration. Only parent
orchestration differs: a fresh working parent blocks/retries on a newly
registered child; a cache-restored parent is already terminal. Parent metadata
is installed before either child path, so a child's `super` import sees the
settled parent. Existing children are idempotent no-ops, and `ModDecl`
visibility is untouched—private and public children take the identical path.

### 5.2 Written trait impls (0869)

The split storage model (`Decision-45` as amended) means the discovery shell
lives at the trait's home while the mangled methods live in the writer's table.
Restoring per-module snapshots reconstructs the methods and loses the shell.

The carrier is landed: `SymbolTable.written_trait_impls`
(`crates/cranelisp-types/src/module.rs:251`, serde-visible, no default),
`WrittenTraitImpl` (`:867`), `enrol_written_trait_impl` (`:929`) and
`trait_impl_key` (`crates/cranelisp-types/src/resolve.rs:1062`).

**C6's half** is restore-time enrolment at **both** cache entry points, after
the writer's dependency closure installs: for each record in the restored
table's `written_trait_impls`, call `enrol_written_trait_impl` against the
trait home's table. `Enrolled` and `AlreadyEnrolled` are both success (a writer
reached by two dependency paths must be idempotent); a divergence is a hard
error routed to the same `CacheStale` class as §3.4, never a silent pick.

**As built.** `try_cache_hit_load` returns `Result<bool, CranelispError>`:
ordinary or malformed-cache misses and conflicting live state are distinct. It
preloads each foreign canonical trait home, validates writer provenance, then
re-enrols every record with the types-owned strict helper after installing the
writer table.

**The producer is C3's, and it lands first.** The visit opened on a carrier
with zero producers and zero readers — the "landed with zero consumers"
pattern root `CLAUDE.md` §Assurance names — because an enrolment loop over a
permanently empty vector is a no-op that would pass review and could never flip
the discriminator. `arch` ruled the allocation rather than the feature
(`trait-impl-cache-carrier.md` §9): the §3 append at `register_trait_impl`
(`crates/cranelisp-typecheck/src/traits/impl_check.rs:94`, invoked from
`program/register.rs:66`), the two `impl$` mint re-points, and the phantom
`check_trait_impl` rustdoc correction all ride C3's wash change-set, and C3's
own design carries them as CS-6 (`design/typecheck/traits.md` §3.0.1). N3's entry
gate is therefore "C3's producer landed", an ordinary edge in the already-
ordered wash — nothing is owed to C6 and nothing is owed by it here.

**The intra-wash empty sidecar regenerates; C6 does not shim it.** Between C1's
schema-25 bump and C3's producer, a developer-local sidecar can be written that
is *valid* and carries an empty `written_trait_impls` — restoring impls-lost if
trusted. That exposure is `arch`'s named residual with its falsifier
(`trait-impl-cache-carrier.md` §6), and its disposition is to regenerate the
cache. C6 must not acquire a tolerance for it: no `#[serde(default)]`-shaped
read, no "empty ⇒ rescan the trait home" fallback, no restore-time
reconstruction from mangled method names. Each is a second derivation of the
shell and a `/review` reject (§16).

### 5.3 Module aliases (0798)

`(import [(main.util u) []])` then `(u/helper)` fails with
`module 'u' … not found`, and the alias-only form of §8.3.6 is therefore
entirely non-functional. The seam is located, and it is int's:

- `src/imports.rs:63-72` (`install_imports`) writes the alias under
  `alias_key(current_module, alias)` = `main.u` (`imports.rs:542`); the
  cache-restore mirror does the same (`imports.rs:505-511`);
- `cranelisp_types::resolve::substitute_module_alias`
  (`crates/cranelisp-types/src/resolve.rs:961-995`) matches an alias key only
  when it is a dot-segment prefix of the **queried** module part. For `u/helper`
  the queried part is `u`; the stored key is `main.u`; no match.
- The contrast that proves it is a keying inconsistency and not a missing
  feature: submodule aliases are keyed by the **bare short name**
  (`dependency.rs:921-932`), whose own rustdoc gives the reason — "so §8.6.6
  longest-prefix substitution matches the `module_part` of a bare qualified
  reference". The import-alias path contradicts its sibling's rationale.

**The cure is ruled, and it is not "key bare".** Bare keys are globally visible
in one `ModuleAliases` map, so two modules aliasing different targets to `u`
collide silently — the hazard the submodule path already carries.
`arch` ruled the scoped alternative (`module-alias-scoped-lookup.md`):
`substitute_module_alias` gains a `referring_module` and becomes the spec
§8.6.6 segment walk of **keyed** probes — leading segment against the referring
module's own aliases at any visibility, later segments `Public`-only, depth-
capped, no match leaving the path unchanged. One key shape `<owner>.<name>`,
one mint (`module_alias_key`), both alias kinds sharing the primitive. Bare
submodule keys retire with the wrong-accept they carry. `ModuleAliases` stays
unserialized session state, so there is no schema contact and no restore-format
question — only the same two writer families, re-keyed on both their fresh and
their restore legs.

**C6's exact share** (the walk, the visibility rule and the mint are C1's; the
`checker.rs:1476` call-site is C3's):

| Site | Kind | C6's act |
|---|---|---|
| `src/imports.rs:63-72`, `:505-511` | import-alias writers, fresh + restore | re-point onto `module_alias_key`; the key value is unchanged |
| `src/process_form/dependency.rs:921` (`register_submodule_alias`, invoked `:994`) and `src/imports.rs:514-522` | submodule-alias writers, fresh + restore | flip the bare short name to `module_alias_key(parent, short)`; the two rustdoc blocks stating the bare-key rationale are re-written with it |
| `src/imports.rs:542` (`alias_key`) | int-private mint | **deletes** — the one mint is types' |
| `src/repl/mod.rs:680` | consumer | pass the session's current module |
| `src/process_form/macro_resolution.rs:106` (FQ-autoload boundary) | consumer | pass the module whose form is being processed |

Two properties C6 must preserve as it lands them. **No transitional bare-key
fallback arm** — the interim between C1's walk and C6's writer flips lies
inside the wash, whose landing model is compilation-plus-tests enumeration
([S121 lifecycle design at checkpoint
`dc78ddbe`](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/symbol-table-lifecycle.md)
§9), and a fallback leg would preserve both wrong-accepts indefinitely
(Principle 8; §16 reject 13). **An undeclared alias stays a located "module not
found"** — the substitution that accepts any head
is the pre-existing §16 reject 5.

### 5.4 Monomorphic instances

Covered by N2 for the reload path. For the cache path no gap exists: instances
are ordinary `Concrete` entries in the demanding module's own table, restored
with it, and the `minted_from` link travels with them. §3.4's load validation
is what keeps a restored instance honest (its slot must still satisfy
`slot ⇒ is_concrete()`).

### 5.5 Concurrent publication, and the live 0694 facts

Two 0694 members are live conditions this sprint, and C6 owns the seam one of
them points at. Neither is C6's to *attribute* — that is `qa`'s under its
control discipline — but the design must say what the seam guarantees, because
that is what makes the discriminating observation possible.

**Class II — `nullary_return_dispatch_method_only_import_no_codegen_leak`.**
The captured in-suite failure is a compile-time diagnostic,
`undefined function: z`, from a subprocess that then exited cleanly: a symbol
was not there when the compiler looked. Its *accept-side* defect is C3's (the
D2 family, method-only-import dispatch). Its load-conditional face is a
publication-order signature at C6's seam. The invariant the visit must preserve
and state:

> A name is observable to a reader **only** through its module publication
> gate, and that gate publishes owners → entries → introspection after the
> complete publication unit has compiled. For an ordinary HM cluster that unit
> is the cluster; for a macro it is the parent plus every active clause. There
> is no interval in which an entry is readable and its GOT cell is unpopulated.

That preserves the S117 W3a ordinary-cluster contract, while N5 gives each
macro a smaller source-ordered checkpoint. Because the 0604 wave
landed `MODULE_TRACE` emission at `commit_staging_to_live`'s gate
(`src/worker.rs:798-805`), the discriminating observation — a trace showing an
eval read preceding publication — is now available under load. C6's obligation
is to keep that emission at the seam through the N1/N5 churn; the experiment is
`qa`'s (0694 D1/D2).

**Class I — the launched-grid corruption** (`tests/launch_grid_corrupt.rs`) is
an RC undercount on the borrowed-Var vec path, evidenced by an RC trace showing
205 pointers freed twice. It is a backend/runtime-pair fact C6 consumes as
context only: nothing in this visit changes emission or RC. It must not be
folded into any int bundle.

## 6. Bundle N4 — the macro turn balances

`macro-turn-ownership.md` §3 is the normative protocol and is unchanged by this
visit. What C6 records is that its two open dependencies have returned settled,
and its preconditions are now dated facts rather than assumptions.

### 6.1 Rule 0's enforcement, absorbed (0927)

`arch` ruled the boundary question at the S119 Phase-3 exit gate; the canonical
statement is `bounded-contexts.md` §6. Absorbed into `macro-turn-ownership.md`
§3 Rule 0 and §8 D4 by this visit:

- the declaration is **not** satisfied by construction — clause defns run the
  full `check_forms` path and the ownership fixpoint publishes summaries onto
  callable entries, so a fresh-result clause can legally classify
  `Mode::Borrowed` and backend elides its parameter release;
- the pin is int's, at the clause-preparation seam: after `check_forms` returns
  and before the clause entry is published for codegen, int **clears** the
  synthesized clause entry's mode summary. Summary-absent ⇒ all-Owned
  Decision-24 compilation, which is what `SexpListToSexpI64V1` declares.
  Widening toward Owned is always sound; the cost is a few redundant RC ops in
  clause bodies, compile-time only;
- it is structural under Principle 19 because int knows clause-ness by
  construction — it synthesized the defn. No name-prefix privileging enters
  typecheck or backend.

Verified not implemented at HEAD: the only non-test `mode_summary` mention in
`src/process_form/macro_clause.rs` is the `set_callable_slot` destructure at
`:455`, which explicitly preserves the summary while overwriting the slot.
Under the C1 wash the same act becomes a `Life::Concrete` field clear at the
settlement funnel; the seam does not move.

### 6.2 The three tranche-A requirements returned (0921)

C6 filed three requirements against the runtime pair's typed-handle
vocabulary. All three are met by `design/runtime/s119-typed-consume-funnel.md`
§3, and `macro-turn-ownership.md` §12's first bullet is discharged:

| Requirement | Answer |
|---|---|
| a blessed transfer across a non-`extern` host↔JIT boundary | `Owned::from_abi` (the one raw entry) / `Owned::into_raw` (the one raw exit, `#[must_use]`, the only handle-related `mem::forget`) |
| tolerance of bare nullary-tag words | `from_abi` is nullary-tag-safe; `is_nullary_tag` single-sources the `< NULLARY_TAG_THRESHOLD` predicate |
| `consume_sexp`/`consume_slist` reachable with typed signatures from a third crate | both stay `pub`; tranche A's signatures are what force the handle types public |

The separately-confirmed intrinsics gap in the same filing —
`consume_sexp` has no `TAG_SEXP_ANNOTATED` arm, so an annotated cell deallocs
its parent and leaks both halves — is C5 bundle I1. Re-verified at HEAD:
`crates/cranelisp-intrinsics/src/drop.rs:242-255` has two arms plus a scalar
catch-all, and `TAG_SEXP_ANNOTATED` is not even imported (`drop.rs:45`). This
is **D2's gate**, and it is now scheduled rather than speculative: C5 lands the
arm, C6 confirms it before Rule 4 binds. The fix is never a compensating walk
in `src/marshal.rs`.

### 6.3 What remains C6's, and its as-built preconditions

`macro-turn-ownership.md` §8's D0–D6 stand unchanged. Re-verified at HEAD so
the wave does not open on stale premises:

- `src/marshal.rs:5` still documents "RC is never decremented" as intent;
- `protect_marshalled_cell` (`marshal.rs:204`) has **four** call sites —
  `:220`, `:234`, `:251`, `:264` — not the three its own doc block (`:196-203`)
  enumerates. `alloc_sexp_pair` (`:225`) was added by the S116 annotated-node
  cascade and never joined the list. Rule 2 deletes the function and all four;
- `marshal::rc_inc` (`:316`) is a **non-atomic** `*rc_ptr += 1` on cells the
  JIT and its lenient-eval sparks touch atomically. Rule 5 deletes it; the
  typed mint replaces it. This is the citation
  `s119-typed-consume-funnel.md` asked int to re-verify — it holds;
- `src/expander.rs:512::invoke_clause` obtains the result word at `:537` and
  returns `marshal::runtime_to_sexp(result_i64)` at `:548` without consuming
  it. Grep confirms **zero** `consume_sexp` call sites in `src/` — Rule 4
  introduces the discipline there;
- `tests/macro_turn_marshal_leak_0889.rs` pins the residual at `+2` (`:139`)
  and `+1` (`:185`); both flip to `0` at D5.

## 7. Bundle N5 — source-ordered macro checkpoints and presentation

### 7.1 One complete macro, one immediate module transaction

The user-approved checkpoint replaces the former cluster-wide candidate world.
Int walks authored and expansion-produced forms in source order. At each
`defmacro` it prepares the parent plus all active clauses, checks every clause
and its already-available expansion-time closure, compiles the complete clause
batch, then publishes through `publish_compiled_staged`. Later forms may use
the now-live macro. Their failure does not roll it back. If any part of the
macro itself fails, none of its parent, clauses, owners or introspection
publishes.

Ordinary forms accumulate across macro checkpoints and still enter one HM
binding cluster. They are not published early and cannot act as same-module
expansion-time helpers. Dependency modules and required generated realizations
publish independently through their ordinary module work; a later target
failure does not undo them.

On a `ResolutionGap`, the scheduler work item retains only source work: the
already-expanded ordinary prefix, the unprocessed authored/emitted suffix and
entered-form provenance. It retries the macro when the gap occurred before its
checkpoint, or resumes after it when the checkpoint already succeeded. This
prevents an already-committed direct or generated macro from being interpreted
as an illegal duplicate, while a genuine second same-named occurrence in the
original cluster remains an error.

For Replace/reload, the continuation also records that generation setup has
already run. A gap retry must not clear the module again and erase a committed
macro checkpoint. A new watcher event or explicit reload is a new generation
against current live state. A successful macro replacement remains current if
a later ordinary form in that reload fails; the prior ordinary generation stays
live and the reload reports the error.

The §18 dependent-recompilation/reload cure starts after macro publication. It
is not a precondition of checkpoint success and may not retain a checked macro
as a candidate. A later cure refusal or block is reported under that
transaction's rules and does not restore the prior macro generation.

#### 7.1.1 Committed outcomes leave by a stack-owned receipt

Publication returns an int-private, non-`Clone`, `#[must_use]`
`PublicationReceipt { outcomes: Vec<RedefinitionOutcome> }`. It contains only
facts about commits that have already happened: no staging table, checked
state, generated program, owner, slot reservation, or resume position.
`ProcessedCluster` does not carry or copy these rows.

The private attempt entry has the shape
`ProcessAttempt<T> { terminal: Result<T, CranelispError>, publications:
PublicationReceipt }`. Its outer wrapper owns the receipt and passes a mutable
sink into the fallible processing core. Every successful ordinary or macro
publication appends its outcome before processing continues. Therefore `?`
may end the core after a later failure without discarding an earlier committed
checkpoint; the wrapper still returns the terminal result and move-only
receipt.

The route settles the receipt exactly once, before interpreting its terminal:

- eval applies `repl/spec.md` §18 on `Done`, before waiting on `Gap`, and before
  returning `Err`;
- dependent recheck owns one receipt across source retries and settles it
  before reporting either success or failure; and
- initial-load and watcher/reload pool work consumes or acknowledges the
  receipt synchronously on the worker stack on every `Done`, `Gap`, and `Err`.
  Pool work uses complete `Replace` generations: success already recompiles
  same-module callers and watcher/T1 orchestration owns dependent reload;
  failure uses the existing error block. No waiter needs individual outcome
  rows; and
- the retained `New`-only batch compatibility route proves its receipt empty
  and treats an effectful receipt as an internal contract failure.

A scheduler mailbox or any receipt field in `SharedState`, `ModuleState`, a
parking record, or a persisted continuation is explicitly rejected. It would
duplicate a settled fact and add reset/drain ordering without changing an
observable result. Retry retains only the source/emitted continuation and the
generation-started bit. Public `process_cluster` need not change: production
uses the crate-private attempt entry, while any retained compatibility wrapper
may discard only a receipt proven inert for its `New`-only route.

`TurnCheckWorld`, `TurnDelta`, `PreparedMacroTurn`, candidate invocation,
reserved unpublished slots and cross-module rollback delete. The ordinary
`PreparedCommit` shape is reused for the macro's one-module staging and exact
owner map. Result presentation is a separate eval-stack receipt: exact emitted
definition identities are retained in source order, macro rows become
displayable at their checkpoint, and ordinary rows wait for HM/codegen
publication. No binding is projected to the type of invoking it.

Before typecheck, int predeclares each exact synthesized clause key in the
private staging table as `Private` `CallableOrigin::MacroClause { group }` with
the canonical `(Fn [(macros/SList macros/Sexp)] macros/Sexp)` ABI. Typecheck
may preserve that origin only from the staging-local row; name spelling and a
live prior row confer no authority. After checking, int validates the complete
active clause set before codegen. Language-value candidate selection excludes
macro clauses, while internal codegen enumeration and the macro executor retain
access.

An `N`-clause parent replaced by an `M`-clause parent, for `M < N`, supplies
the exact old keys at indices `M..N` as absent-key `ChangeAbi` decisions in the
same prepared and final publication as the new parent and active clauses. The
keys are derived from the prior parent metadata, never from a symbol-prefix
scan, and each must resolve to a private `MacroClause` owned by that parent.
No ordinary callable is eligible for this removal path. The approved
absent-key semantic retires each selected binding, returns its displaced owner,
and leaves its prior GOT slot frozen behind an `AbiChanging` tombstone. Int
retains all returned owners before releasing the writer guard.

For the diagnostic sequence 3→1→3, the first replacement preserves active
index 0 and retires indices 1 and 2. The second preserves the current index 0
and allocates fresh slots for indices 1 and 2; it cannot reuse either retired
slot. Any plan or final-publication refusal leaves the old parent, clauses,
pointers, owners, candidates, tombstones and continuation unchanged. Cache
restore validates a bijection between parent metadata and active private
same-group `MacroClause` rows: missing, duplicate, surplus, wrong-group and old
`Plain` rows are stale and regenerate.

N5 consumes the separately approved absent-key behavior of the existing
`ChangeAbi` decision. It adds no further public Rust surface, cache schema,
platform or backend contract, and it does not alter `TraitImpl` registration,
publication, replacement, or restoration.

### 7.2 Replacement safety and N4 ordering

N4 reworks clause **invocation**; N5 reworks clause **preparation and
publication**. Rule 7 keeps marshal handles inside one invocation frame, so no
handle enters either prepared publication or retry continuation.

N4 lands first because both bundles edit `src/expander.rs`. N5 then changes the
macro reader to take one module read guard and snapshot parent metadata plus
the selected clause's origin, ABI, GOT pointer and cloned `Code` owner. The
guard is released before invocation. Replacement holds the matching module
write guard from before backend finalization can patch a reused canonical slot
through `publish_compiled_staged`. A reader therefore gets one complete old or
new generation, and its owner remains live for the call.

Each macro batch publishes its drop-glue `{artifact, owner}` rows as pairs
through the ordinary publication machinery. There is no absorbed second
writer and no cross-module owner carrier.

### 7.3 The annotation-mirror tail (0708)

The S116 read-time fold **landed**: `Sexp::Annotated`
(`crates/cranelisp-types/src/sexp.rs:23`) is constructed by the reader
(`crates/cranelisp-frontend/src/reader.rs:453`), `try_expand_sexp`
(`src/process_form/macro_resolution.rs:360-408`) no longer counts raw children,
and both frontend mirrors named for retirement are gone. 0708's central claim —
an annotation standing alone in macro-argument position — is discharged.

What survives is a **documentary and dead-code tail in `src/`**. `arch` corrected
`design/arch/annotated-sexp-node.md` §7 on 2026-09-01 against live source, and
its retirement list now names **four** live rows, not three. All four are C6's,
in bundle N5, and they take **three** dispositions rather than one:

| Site | State at HEAD | Disposition |
|---|---|---|
| `worker::leading_annotation_len` (`src/worker.rs:126`) | constant-`0` stub with a live caller at `src/process_form.rs:791` feeding dead `annotation_prefix` plumbing through `process_regular_form` (`:958`, `:992`); pinned by `src/worker/tests.rs:1513` | **delete outright** — stub, caller, `annotation_prefix` parameter and pin together, as one deletion |
| `save.rs` colon suppression (`src/save.rs:250` `is_bare_colon`, `:264-276`, `:279-330`) | live | **re-express structurally** — the renderer emits an `Sexp::Annotated` (the node is what it is rendering) |
| `expander::is_annotation_symbol` (`src/expander.rs:1098`) | live, called at `src/expander.rs:1220` and `src/process_form/macro_resolution.rs:696` | **re-express structurally** — the predicate becomes a match on the node |
| `pretty.rs` lexical annotation dispatch (`src/pretty.rs:583` `is_type_annotation_list`, `:590` `pp_type_annotation_list`, plus the two sibling `starts_with(':')` role tests at `:271` and `:369`) | live; its structural replacement is **already landed in the same file** | **delete** — §7.3.1 |

The two middle rows are **not** blind deletions: they are string-prefix
dispatches over rendered or re-read text, and each needs its replacement stated
before it goes. Both are structural re-expressions of a lexical test, which is
the point of the S116 flip; a deletion that leaves a lexical test behind under a
different name is a `/review` reject (§16 reject 9).

#### 7.3.1 The `pretty.rs` row — a deletion, because the replacement already runs

This row is classed apart from the two re-expression rows because its structural
replacement is not owed: it is in the same file and already executing. `pp`'s
`Sexp::Annotated` arm (`src/pretty.rs:334`) emits the annotation half as one
`Role::TypeAnnotation` span and recurses the subject at its own roles, and
`emit_source_spans`' arm (`:253`) does the same over the original bytes. That is
`repl/spec.md` §10.3 R4 as written — R4 covers the *annotation* (`:Type`,
`:(Fn […] …)`), and §10.4's worked line keeps the subject (`user/double`) in
R7/R15 outside the cyan span. The surviving helpers encode the **pre-fold**
shape, where annotation and subject were siblings and the printer had to
recognise the pair lexically; they wrap the whole list — subject included — in
one cyan span, or bold it entire in head position.

**The guard is unsatisfiable from the reader, and that is the deletion's ground
— structural, not an inspection.** `is_type_annotation_list` fires only on a
`Sexp::List` whose first child is a `Sexp::Symbol` whose *name* begins with `:`.
Since the fold no reader-produced symbol can: `is_symbol_start` admits only
`[A-Za-z_]` (`crates/cranelisp-frontend/src/reader.rs:249`), `:` is not an
operator char (`:257`), and the sole `:` dispatch (`:291`) is
`read_colon_prefix`, which strips the introducer and returns `Annotated`
(`:453`). The shape the helpers were written for — the sole-element
parenthesized annotation `(:Int 42)` (spec §2.3.8; live at
`tests/spec_08_modules.rs:1607` and `examples/29-annotations.cl:150`) — now
reads as a one-child list holding an `Annotated` and renders through the arm
above.

**What the deletion removes is therefore a wrong-accept, not dead weight.** One
producer can still mint a symbol whose spelling begins with a colon: a macro,
through `runtime_to_sexp`, out of an ordinary language string. Such a symbol is
**not** an annotation — annotation-ness moved into the tree at S116 — and
styling it cyan on its spelling is exactly what the node retires
(`annotated-sexp-node.md` §1: the invariant "never a standalone atom" becomes
structurally unrepresentable). The identical argument holds for the two sibling
role tests at `:271` and `:369`, which is why they go in the same deletion:
removing the list-head test while leaving the symbol-position test under another
name is §16 reject 9 by construction.

**Exact set, one change-set.** Delete `is_type_annotation_list` (`:583`) and
`pp_type_annotation_list` (`:590`), then `pp_type_multiline_unstyled` (`:611`)
and `flat_content_unstyled` (`:628`) — both sole-called from the deleted body —
together with the `pp_list` dispatch at `:384-385` and the `starts_with(':')`
arms of `pp_symbol` (`:369`) and `emit_source_spans`' `Symbol` arm (`:271`).
After it, `Symbol(":Int")` in list-head position renders R1 Head and elsewhere
R15 Plain, which is what an ordinary symbol whose spelling starts with a colon
is.
Nothing is added. `Role::TypeAnnotation`'s other producers (`src/display.rs`,
`src/repl/format.rs::push_type_annotation`) are untouched — they render resolved
types, not `Sexp`, and are outside this row.

**Evidence — module tier, in `src/pretty.rs`'s own `#[cfg(test)]` module.** The
seam is the printer submodule (METHOD §2.2) and all three rows are pure
transforms needing no session:

| Row | Shape | Polarity |
|---|---|---|
| the wrong-accept | a hand-built `Sexp::List([Symbol(":Int"), Int(42)])` — the macro-mintable shape no reader input produces — carries **no** `TypeAnnotation` span; its head takes the ordinary head/plain role | **RED at HEAD, GREEN after.** This is the arming proof: it fails today *because* the helper fires, and it is what separates the deletion from a no-op |
| colour-off identity | `pretty_print_str("(:Int 42)")` == `"(:Int 42)"` | green both sides — §10.3 requirement 2 |
| colour-on spans | `(:Int 42)` renders `(` Plain · `:Int` R4 · ` ` · `42` R2 · `)` Plain, and the verbatim leg (`style_source_verbatim`, `:186`) reproduces the input bytes with R4 over the annotation half only | green both sides — §10.3 requirement 3, §10.4 |

The existing row `type_annotation_symbol` (`src/pretty.rs:847`) must **not** be
counted as coverage here, and is replaced in the same change-set: `:Int` alone
is not a readable form (the reader raises `annotation missing expression`), so
the assertion is satisfied by `try_parse_and_format_doc`'s parse-failure
fallback and exercises no role assignment at all. `compound_type_annotation`
(`:921`) and `result_display_format` (`:927`) do parse, and stay as the
node-path guards.

**No e2e is warranted, and the assessment is recorded rather than skipped.** The
deletion is behaviour-preserving on every reader-reachable input, and the
observable surface — `/sexp` colour-off — is already pinned by
`tests/spec_08_modules.rs:1607` and the demo goldens. The colour-**on** fixture
for `(:Int 42)` is `qa`'s allocation (H3), not a new C6 obligation.

`annotated-sexp-node.md`'s retirement list is `arch`'s text and is now current
on the row *set*; what remains routed is that row 5's locus list names two of
the four live `src/pretty.rs` sites (§15 H5).

### 7.4 What 0800 gets, and what it does not

Faces 1 and 2 are resolved by correcting the premise. `def` emits two
definitions, so the definition result lists both `user/n-def ; defn` and
`user/n ; defmacro` in order. `/info n` and `/sig n` correctly describe the
macro binding; entering bare `n` is the separate invocation that produces an
`Int`. No name-shape test on `def`, `-def`, `*-def` or the stdlib module is
needed.

Face 3 (a `def`-bound function value cannot be applied) is **out of scope** and
stays out. It is a stdlib API decision retargeted to `/stdlib` by the S117 QA
disposition, and `s117-conformance-recovery.md` §6 records DF-3 as excluded.
C6 changes no macro arity, resolution or runtime invocation.

### 7.5 FIXME 0050 stays deferred, and is not coupled here

0050 promotes `repl/spec.md` §1.5's aspirational `List`/`Seq` surface forms to
MUST **when a display protocol exists**. The trigger is unmet: no type-directed
pretty-printer is implemented, and `design/arch/display-protocol.md` is a
pre-implementation design. The user re-affirmed the deferral 2026-09-01 with the
verified trigger and directed that it not be coupled to 0800/0863.

The two are genuinely separable: 0800/0863 is about reporting the complete set
of definitions produced by a turn, while 0050 is about **how a value renders**
through a type-directed protocol. Nothing in N5 makes 0050 cheaper, and
nothing in 0050 would fix a face of 0800. C6 introduces no render marker and
no §1.5 promotion.

### 7.6 FIXME 0052 — disposition only

`/learn` is outside Sprint 121 product and design scope. Verified: no normative
`/learn` behaviour remains in the live specification (`spec/` and `repl/spec.md`
carry the word only in ordinary prose). ACT-0951 carries the complete
user-ruled feature specification and gates any future architecture, C6 design,
QA plan or implementation.

C6 therefore touches **no** `/learn` product code and **no** `/learn`
documentation. The record here exists so that the next reader of this surface
finds the disposition beside the surface it would otherwise be designed into,
rather than only in a sprint archive.

## 8. Bundle N6a — the platform manifest

### 8.1 The mint replaces the cursor write

Under `symbol-table-lifecycle.md` §5.6 a platform effect is born
`Concrete { slot: manifest-order mint, realization: Dll }` with
`origin: PlatformEffect { scheduling_class, poll_shape }`. Descriptor *i*
claims index *i*. The DLL slab continues to wrap in place as the module's GOT
(`src/platform.rs:333-346`) — unchanged. The direct cursor write at
`src/platform.rs:351` deletes (§3.3), because manifest claims are ordinary
claims and the mint's authority is the claim scan.

"Slot *i* == descriptor *i*" becomes assertable as a mint-order invariant, and
the load-boundary uniqueness scan (§3.4) is where a violation surfaces.

### 8.2 The located refusal (0933)

Every shipped platform sig is concrete and `PlatformEffect` schemes are minted
with `type_vars: vec![]` (`src/platform.rs:378`). Nothing refuses a manifest sig
whose parsed type contains a residual variable, and the path is reachable, not
theoretical:

- `fqize_type_expr` (`src/platform.rs:474-506`) re-partitions only *slashed*
  leaves; `split_slashed_type_ref` (`:520-530`) returns `None` for a bare
  lowercase leaf, which therefore survives as `TypeExpr::TypeVar`;
- `check_type_expr` **mints a fresh `TypeId`** for an unknown bare lowercase
  leaf (`crates/cranelisp-typecheck/src/form.rs:444-455`) rather than erroring;
- the only post-check validation is `require_io_return` (`src/platform.rs:597`),
  which constrains the return head only — a `Type::Var` in a parameter, or
  inside `IO a`, passes;
- the hard-empty `type_vars` then leaves that variable unquantified in a slotted
  scheme.

**Where the refusal lives.** The *structural* refusal is C1's: the settlement
funnel checks `is_concrete()` and the mint cannot produce a witness for a
non-concrete scheme, so after the wash the smuggled entry stops being
constructible. That is the guarantee, and C6 must not duplicate it with a
second predicate.

**What C6 owns is the frame.** A funnel refusal at the DLL-load seam would
surface as an internal invariant error naming a scheme — useless to the person
who wrote the manifest. C6 converts it into a **located diagnosed load error**
at `parse_and_check_platform_type_sig`, naming the platform, the function, and
the offending leaf, and routed through the existing `PlatformError` channel so
it degrades the load exactly as an ABI or layout-hash refusal does. It is a
diagnosed error, never a panic. This is Principle 25's shape: the narrowing
(a platform sig is concrete) carries its check, and the check speaks in the
vocabulary of the boundary it guards.

Unit rows: a concrete sig mints unchanged; a bare-lowercase-leaf sig refuses
naming that leaf and its platform fn; the refusal is a diagnosed load error.

### 8.3 What stays C7's

The public platform facade, schema, `ABI_VERSION` 9→10 for the FIXME-0934 IO
node layout, marker binding and the shared-heap fixtures are C7's. C6 changes
no platform ABI and rebuilds no fixture. The one C6↔C7 contact is the mint
order invariant above, which C7 consumes.

## 9. Bundle N6b — one program result, one strip rule

### 9.1 The owner is settled; only its instrument is not

`result-owner.md` is RATIFIED as-built: `OwnedProgramResult`
(`src/result_owner.rs:134`) with observation, one consuming finalize
(`EvalResult::release_program_result`, `src/session_v4/types.rs:176-180`) and a
`Drop` backstop (`:294`); three resolution adapters
(`SessionGlueResolver`, `result_owner.rs:445` — `FreshJit` / `Cached` / a
no-code-owner refusal); linked startup through `StartupResultExit` (`:375`)
baked by `src/exe.rs`. Construction is at three seams and release at four call
sites, all verified live. FIXME 0745 is closed by that work; C6 rebuilds none
of it.

The one live obligation is **0914**: `/mem`'s delta window
(`src/repl/commands.rs:1141`) reads its closing counters at `:1152-1154` while
the owner is released by the `Drop` backstop at the end of the match arm
(`:1161-1165`), so every heap-valued expression reports a phantom leak.
`result-owner.md` §4.2.1 ruled shape (a): the command drives the release
through the same chokepoint, inside its own turn — render, release, *then*
close the window. That is not a second release site; it replaces a backstop
release that already happens, two statements later. `/time` is deliberately
unchanged. Unit tier extends the exactly-once rows at
`src/session_v4/types.rs:275`, `:298`, `:311`, `:339` rather than duplicating
them.

### 9.2 The strip rule — S121 measured three encodings, not two

This is the pre-migration S121 measurement. Both consumers now call the shared
helper; `result-owner.md` §4.3 and `s122-closure.md` §4 carry the current state.

0898 was filed against two literal encodings of the `IO a ⇒ a` result-root
rule. At the S121 measurement point, the types half had landed without either
consumer migrating, so there were **three**:

| Encoding | Site | Disposition |
|---|---|---|
| `ConcreteType::result_root()` | `crates/cranelisp-types/src/concrete.rs:131` | the ONE rule; **zero production call sites at the S121 measurement point** |
| backend's inline `result_roots` map | `crates/cranelisp-backend/src/lib.rs:672-684` | C4 bundle B6 deletes it |
| former private `strip_io_head` in `src/result_owner.rs` | sole caller was `release_key` | **C6 deletes it**, re-expressing over `result_root()` |

Semantics are byte-identical — exactly one hop on the `primitives/IO`
non-empty-args head. Any semantic change is out of scope. The filing deletes
when both consumers are collapsed, which was a two-stream act: C4's twin and
C6's twin both had to go, and neither alone discharged it.

This is worth naming as a pattern, not just a row: a shared helper published
without migrating its consumers **increases** the duplication it was meant to
remove. The falsifier is cheap and should be standing — a helper introduced to
collapse N encodings has a call-site count of at least N in the change-set that
introduces it, or the collapse has not happened.

## 10. The census closes (0740, 0793, 0604, 0818)

The lifecycle migration invalidates the old binding census: a terminal
`Binding` no longer carries the local aliases through which it is exposed, so
the binding-shaped `check_terminal_closure` is a hardcoded no-op. N-census
deletes that function, `write_is_closure_valid`, and every binding-loop call.
There is one truthful chokepoint, shaped as
`check_terminal_closure(destination, local_name, canonical_source, visibility,
span, D(M))`.

`install_imports`, `install_exports`, prepared publication, the retained legacy
staging-publication seam, and bootstrap route every `NameCandidate` exposure
through that gate before table or GOT mutation. Private and same-module
candidates pass; a public cross-module candidate passes only when its local name
belongs to `D(M)` or `D(M)` is unknown. Own definitions are exported by §8.4
and are not described as having passed a candidate gate.

Bootstrap's structural proof sweeps `all_name_candidates`, requires a
non-vacuous candidate count, and includes a public cross-module candidate
outside `D(M)` that must fail. This replaces the old empty-table/binding sweep
and retires its slot-before-gate residual rather than preserving a second
predicate. 0740 and 0793 retire only when the candidate census and bootstrap
proof are green.

0818 is **evidence, not an attribution**: the probe-contamination hypothesis for
0604's firing environments. It records a real and measured contamination
surface, is cheap to test and cheaper to falsify, and is `qa`'s to run. C6
neither implements nor forecloses it; the structural gate stands on its own
merits either way, which is exactly why the record must survive independently
of whether the hypothesis holds.

## 11. Per-FIXME disposition

Every row was verified against its `refers_to` source in this window.

| FIXME | Class | Verified state | Disposition |
|---|---|---|---|
| **0050** | producer/trigger-gated | no display protocol or type-directed pretty-printer exists; `display-protocol.md` is pre-implementation | **deferred, trigger recorded** (§7.5). Not coupled to 0800/0863 |
| **0052** | accepted residual | zero normative `/learn` text in `spec/` or `repl/spec.md` | **disposition-only** (§7.6). ACT-0951 carries the specification; no code, no docs |
| **0553** (C6 half) | live implementation | `capture_instantiation_drivers` (`redefine.rs:1264`) and `reload_module(extra_forms)` (`lifecycle.rs:1330`) both live; `instantiate_demands` absent workspace-wide | **N2** — capture/re-request, replay retired in the same change-set |
| **0604** | evidence-only | predicate, routing, trigger guard, twins all landed and green; only the census rows are owed | **retirement**, on §10's rows. No further `dev` or `qa` work owed |
| **0694** | current-state wash for C6 | Class-II member live and load-conditional; Class-I is backend/runtime | **consumed as fact** (§5.5). C6 preserves the publication invariant and the `MODULE_TRACE` seam; attribution stays `qa`'s |
| **0708** | evidence-only + documentary tail | read-time fold landed; frontend mirrors gone; **four** `src/` mirror rows survive — the `pretty.rs` lexical dispatch is the fifth census row `arch` added 2026-09-01 | **retirement of the claim; N5 retires the whole tail** (§7.3): one outright deletion, two structural re-expressions, one deletion-against-a-landed-replacement (§7.3.1) |
| **0740** | live implementation (design) | code half landed W6; §2.1/§2.4 rows never written | **N-census** (§10), with the two factual corrections |
| **0745** | current-state wash | `result-owner.md` ratified as-built; I0–I5 landed; four cells flipped | **retirement**. Its residual pointers (0898, the lenient-view row) have their own homes |
| **0793** | live implementation (design) | `PRIMITIVES_TABLE` mount at `lifecycle.rs:268-274` uncensused; bootstrap sweep uses an empty `primitives` table | **N-census** (§10), same edit as 0740 |
| **0795** | live implementation (design) | §3 still prescribes `for each method in impl_.methods`; the landed mechanism is a trait-wide prefix scan | **doc correction** (§13 row), with the general caution stated |
| **0798** | live implementation | alias written under `<owner>.<alias>` (`imports.rs:542`); `substitute_module_alias` matches the queried module part only | **N3** writer/consumer flips + `alias_key` deletion (§5.3), under the ruled scoped lookup; the walk and mint are C1's |
| **0800** | live implementation | singular result drops one of the two emitted definitions; face 3 retargeted to `/stdlib` | **N5** ordered definition batch (§7.4) |
| **0818** | evidence-only | contamination surface real and measured | **recorded** (§10). `qa`'s experiment; C6 neither implements nor forecloses |
| **0863** | live implementation | former cluster-wide candidate design is superseded; temporary carriers remain in source and definition results are singular | **N5** (§7.1): delete the temporary world, add immediate macro checkpoints and the eval-stack definition receipt, after N4 |
| **0868** | live implementation | `cache_restore.rs` recurses on imports/re-export deps only; fresh path calls `drive_submodules` at `process_form.rs:413-416` | **N3** (§5.1) |
| **0869** | live implementation | carrier landed in types with zero producer and zero consumer; the producer is now C3's CS-6 | **N3** restore half (§5.2), entered on C3's producer; no empty-vector shim |
| **0889** | live implementation | marshal header, four protect sites, non-atomic `rc_inc`, unconsumed result word all confirmed | **N4** (§6.3), gated on C5's tag-7 arm |
| **0898** | live implementation | **three** encodings, not two; `result_root()` has zero production callers | **N6b** int twin (§9.2); C4 removes the backend twin; the filing deletes when both go |
| **0914** | live implementation | window closes at `commands.rs:1152-1154`; release is the `Drop` backstop at `:1165` | **N6b** (§9.1), per the §4.2.1 ruling |
| **0921** | evidence-only | all three requirements answered by tranche A | **retirement** (§6.2). Its intrinsics finding is C5 bundle I1 |
| **0927** | live implementation (design) | pin not implemented; `macro_clause.rs:455` preserves the summary | **absorbed** into `macro-turn-ownership.md` §3/§8 (§6.1); the `dev` obligation is N4's |
| **0933** | live implementation | no residual-var refusal anywhere; `check_type_expr` mints a fresh id for a bare leaf | **N6a** (§8.2) — C6 owns the located frame, C1 owns the structural refusal |

## 12. Bundles, in order

Serial. Each is independently reviewable and leaves no partial path reachable.

| # | Bundle | Content | Gate to enter | Exit |
|---|---|---|---|---|
| **N1** | Lifecycle consumption | commit-gate freeze → `retired_slots`; `Broken` adoption; platform cursor delete; both restore seams call the load validation | C1 landed | `cargo check -p cranelisp` clean against the new machine; no int-side lifecycle predicate remains |
| **N-census** | Candidate-closure census | delete the no-op binding gate and `write_is_closure_valid`; route every candidate exposure through the one candidate-shaped gate; replace the bootstrap proof | — | candidate polarities and non-vacuous bootstrap sweep are green; 0604/0740/0793 retire |
| **N3** | Restoration parity | child enrolment (0868); written-impl enrolment (0869 restore half); alias writer/consumer flips + `alias_key` deletion (0798) | N1; **C3's `written_trait_impls` producer landed** (its CS-6, not the whole of C3); **C1's scoped alias walk + `module_alias_key` landed** | `cache.rs` discriminators flip; the alias matrix flips fresh **and** warm; no bare alias key and no int-side key construction remain |
| **N2** | Reload driver | `minted_from` projection, re-request, replay retirement | N1, C3's `instantiate_demands` | T1 full-cure guards hold; no `extra_forms` parameter survives |
| **N4** | Macro turn | Rules 0–7: the Rule-0 clear, single-owner marshalling, transfer, `consume_sexp` discharge, `rc_inc`/`protect_marshalled_cell` deletion | N1; **C5 tag-7 arm landed** (D2); D0 measured; D1 clear | both 0889 pins read `0`; the S118 instrument set is byte-identical across the churn |
| **N5** | Macro checkpoints + definition results | source-order continuation; stack-owned publication and definition receipts; one-module parent+clause prepared publication; exact `MacroClause` birth; exact absent-key `ChangeAbi` retirement of surplus same-parent clauses; one-guard reader; deletion of `TurnCheckWorld`/`TurnDelta`/`PreparedMacroTurn`; ordered `EvalResult::Definitions`; the 0708 `src/` tail | N4 (textual overlap in `expander.rs`); N6b | checkpoint/retry/redefinition matrix including receipt settlement on every `Done`/`Gap`/`Err`, 3→1→3 fresh-slot proof and cache parent↔active-clause bijection; complete ordered definition echo and macro introspection controls green; temporary machinery and receipt mailboxes absent |
| **N6a** | Platform | manifest-order mint consumption; the located residual-var refusal | N1 | 0933 unit rows; platform e2e lanes unchanged |
| **N6b** | Result | `/mem` window; `strip_io_head` deletion | C4's B6 for the twin | 0914's evidence run reports `deallocs +2 live +0` |

**Why this order.** N1 first because every other bundle re-arms the same match
sites and doing them twice is the cost the unified wash exists to avoid. N3
before N2 because the reload driver's projection reads the same `minted_from`
field the restore path must already be validating. N4 before N5 preserves the
invocation-frame boundary and resolves their textual overlap. N6b before N5
because N5 converges macro drop-glue publication onto the ordinary seam N6b
consumes.

**Rejected orderings.** N5 first is wrong: it changes the publication spine in
a world whose entries are about to be re-shaped by N1, guaranteeing a rebase of
the largest change.
Folding N-census into a later bundle is wrong: it is 0604's acceptance
instrument and three filings retire on it, so it should land at the first
opportunity rather than ride the sprint's riskiest wave.

## 13. Source and module-test reservations

Reserved to C6 for the sprint. No other stream may edit these paths; where a
path is shared, the row says who else holds a claim and when.

| Path | Bundles | Notes |
|---|---|---|
| `src/redefine.rs` | N1, N2 | `mark_broken` + the reload driver |
| `src/session_v4/lifecycle.rs` | N1, N2, N6a | `reload_module` signature; `PRIMITIVES_TABLE` mount; trampoline owner |
| `src/session_v4/types.rs` | N5, N6b | `EvalResult::Definitions` + eval-stack definition receipt; exactly-once rows extend |
| `src/session_v4/shared_state.rs`, `src/session_v4.rs` | N5 | source-continuation retry state only; no checked/compiled candidate world and no publication-receipt storage |
| `src/cluster.rs` | N5 | crate-private `PublicationReceipt`/`ProcessAttempt`; outer receipt-owning wrapper around the fallible core; `ProcessedCluster` carries no outcomes |
| `src/scheduler.rs`, `src/worker_pool.rs` | N5 | no receipt mailbox; pool routes acknowledge their move-only receipt synchronously on every terminal path |
| `src/process_form/cache_restore.rs` | N3 | child + written-impl enrolment; load validation |
| `src/process_form/macro_clause.rs` | N4, N5 | Rule-0 clear; one-module parent+clause preparation; delete the temporary world/delta/turn |
| `src/process_form/form_dispatch.rs` | N5 | build the owner-free macro staging product; no direct live registration |
| `src/process_form/macro_resolution.rs` | N3, N5 | FQ-autoload boundary passes the referring module (§5.3); outer `macro_id`; `is_annotation_symbol` caller (§7.3 tail) |
| `src/process_form/dependency.rs` | N3 | `register_submodule_alias` key flip and its two bare-key rustdoc blocks |
| `src/process_form.rs` (+ `src/process_form/tests.rs`) | N3, N5 | `drive_submodules` parity point; `annotation_prefix` deletion; the FQ-autoload boundary's test note |
| `src/worker.rs` (+ `src/worker/tests.rs`) | N1, N-census, N5 | commit gate; `leading_annotation_len` deletion; ordinary `PreparedCommit` reuse for macro publication |
| `src/imports.rs` (+ `src/imports/tests.rs`) | N-census, N3 | census-comment mirror; both alias writers re-keyed; `alias_key` deletes |
| `src/bootstrap.rs` | N1, N-census | build synthetic tables off-map through fallible lifecycle helpers; include `Bind` in the original IO roster; candidate-shaped bootstrap sweep |
| `src/platform.rs` (+ `src/platform/tests.rs`) | N1, N6a | cursor-write delete; mint consumption; the located refusal |
| `src/marshal.rs`, `src/expander.rs` | N4, N5 | Rules 1–5; Rule 4 discharge; `is_annotation_symbol` |
| `src/result_owner.rs` | N6b | `strip_io_head` deletion |
| `src/repl/commands.rs` | N6b, N5 | `/mem` window; `/info`/`/sig` projection accessor |
| `src/repl/mod.rs` | N3 | the alias consumer passes the session's current module |
| `src/repl/format.rs`, `src/repl/format_type.rs` | N5 | the one projection accessor; no second reader |
| `src/eval.rs` | N5, N2 | echo from carried subject; turn-report warnings |
| `src/save.rs` | N5 | colon-suppression → structural render (§7.3 tail) |
| `src/agent/harvest.rs` | N5 | all-features read projection; consume `Binding` facets and candidates, with docstring-grain selection kept int-private |
| `src/agent/pull.rs` | N1 | all-features Document write; blocked on §14's reviewed metadata-only funnel |
| `src/pretty.rs` (incl. its `#[cfg(test)]` module) | N5 | the lexical annotation dispatch deletes against the landed `Annotated` arms (§7.3.1); no other stream holds a claim this sprint |
| `crates/cranelisp-exe-bundle/` | — | **untouched**. Linked startup changes nothing this visit |

**Collisions, resolved.**

- `crates/cranelisp-backend/src/cache/mod.rs` — the `CACHE_SCHEMA_VERSION`
  value is **C1's for the whole sprint**. C6 reads it and never bumps it.
- `crates/cranelisp-types/` — the one S121 window is C1's, and every C6 need is
  inside it: `retired_slots`, `MonoDemand`, `enrol_written_trait_impl`,
  `result_root`, and — since the 2026-09-01 ruling — the re-signatured
  `substitute_module_alias` and the `module_alias_key` mint. C6 opens no
  second window and takes no line of that baseline.
- `src/bootstrap.rs` — C6 consumes C4's `Bind` ruling by including it in the
  original fallible IO roster; bootstrap construction and its candidate proof
  are one edit, not a later mutation of a settled type.
- `src/worker.rs` — N1 and N5 both restructure the commit gate. They are one
  bundle-ordered sequence in one stream, not two claims.

### 13.1 Root integration census and one-pass order (2026-09-03)

The post-C1 production failure count is 114 in the default root library, but
it is not 114 independent edits. The default and all-features checks identify
28 production paths, partitioned exactly once below. These are one int visit;
the family order is the implementation order, not permission to land eight
partial architectures.

| Order / family | Production paths | Owning invariant and exact approved consumption | Family exit evidence |
|---|---|---|---|
| 1. Prepared publication and redefinition | `src/worker.rs`; `src/process_form.rs`; `src/process_form/form_dispatch.rs`; `src/process_form/macro_clause.rs`; `src/cluster.rs`; `src/redefine.rs`; `src/session_v4/lifecycle.rs` | Use one owner-free current-module staging table, one `PreparedCommit` shape and one final live write guard per publication unit. The ordinary HM cluster stays one unit. Each direct or generated `defmacro` is a smaller source-ordered unit containing its parent and every active clause; publish it immediately after complete typecheck and codegen, then continue. Replace raw map drain, cursor snapshots/repointing and per-clause self-publication with complete `StagedPublicationDecision`s. For macro shrink, derive only exact surplus `M..N` keys from prior parent metadata, validate private same-parent `MacroClause` origin, omit them from staging, and carry their absent-key `ChangeAbi` decisions unchanged through isolated planning and final publication; never prefix-scan or retire an ordinary callable. Apply owner-free `publish_staged` only to the isolated prepared view before codegen; publish the original staging, decisions and exact `HashMap<Symbol, Code>` through `publish_compiled_staged`. Retain displaced owners—including retired surplus-clause owners—before writer-guard release. On refusal recover all owners, restore GOT cells while they remain live, and propagate an internal error without panic. Leave retired slots frozen and tombstoned; never clear or recycle them. A crate-private `ProcessAttempt` returns its terminal `Done`/`Gap`/`Err` together with one move-only receipt of every already-committed outcome; the calling route settles it once before handling that terminal. Delete `PreparedMacroTurn`, `TurnCheckWorld`, `TurnDelta`, candidate invocation and reserved-slot rollback. Retry carries only the uncommitted source/emitted continuation so a committed checkpoint is not replayed. Replace the int broken registry with `mark_broken`; retain its displaced owner and trap owner before patching the returned slot. While each file is open, convert its remaining reads through `all_symbols`/`public_symbols` and `Binding` facets. | Root library check advances past raw publication/cursor errors; ordinary-cluster failure remains atomic; macro-local failure publishes nothing; later failure retains a successful macro; each eval, dependent-recheck and pool route settles committed outcomes exactly once on `Done`, `Gap`, and `Err`; gap retry does not duplicate them; compiled-publication refusal restores touched GOT cells while returned owners remain live; successful multi-body publication exposes no ownerless body; exact shrink decisions cannot remove an ordinary callable; 3→1 tombstones two frozen slots and subsequent 1→3 mints two fresh slots; failed shrink is unchanged with no partial retirement; cache restore enforces parent↔active-clause bijection; broken state is read from `Life::Broken`; temporary macro-turn machinery and persistent receipt state are absent. `MODULE_TRACE` remains at each final module gate. |
| 2. Complete restored/indexed module product | `src/process_form/cache_restore.rs`; `src/session_v4/index_worker.rs` | A restored or indexed module is a complete private `SymbolTable`, not a reconstruction from selected public `ModuleEntry` rows. Validate restored tables at the load boundary; enumerate with `all_symbols`/`public_symbols`; merge the checked index staging through `publish_staged`; derive an int-private `ImportableRow` projection for `.meta` without rebuilding the table. Preserve candidates, type/trait/group facets, structural vectors, written impls, sequence and tombstones. | Fresh/warm/index parity covers bindings, candidates, macros, children and written impls; malformed lifecycle state is cache-stale, not exposed or panicked. |
| 3. Synthetic and platform births | `src/bootstrap.rs`; `src/platform.rs` | Build root, primitives, and macros tables off-map in bootstrap order. Every synthetic declaration uses its declared fallible funnel: `build_adt_entries` then `install_binding`/`install_template`/`install_concrete` and `expose_candidate`; special forms/types use `Decl` records plus `install_binding`; host promises use `install_host_promised`; platform descriptors use `install_platform` at manifest index. The IO `Bind` constructor is included in the original synthesized IO roster rather than mutating a settled type. Bootstrap helpers return `Result<_, LifecycleError>` and session construction maps that error once to located `CranelispError`; no caller allocates or advances a slot. | Bootstrap tables pass `validate_lifecycle`; injected invalid construction returns `Err` without panic; candidate sweep is non-vacuous and includes the forbidden public cross-module/outside-closure case; constructor/template classification and bare candidates are preserved; platform duplicate, range and non-concrete refusals are located errors and manifest slot *i* remains descriptor *i*. |
| 4. Resolution and semantic classification | `src/bind_chain_analysis.rs`; `src/expander.rs`; `src/process_form/macro_resolution.rs` | Imports are `NameCandidate`s, never entry-chain variants. Use `ResolutionScope`/`resolve_terminal_entry_and_home`; ambiguous candidates remain ambiguous. Macro recognition is `Decl::Group(GroupKind::Macro)`; bind scheduling is `CallableOrigin::PlatformEffect`; sleep is the uniquely resolved canonical Rust-primitive host promise. Pass the referring module to `substitute_module_alias`. | Alias-scope and ambiguity tests retain both polarities; macro-head resolution and bind/sleep classification have no name-only or chain-walk fallback. |
| 5. Runtime/codegen read projections | `src/pipeline.rs`; `src/eval.rs`; `src/exe.rs`; `src/session_v4/test_runner.rs` | Read callable scheme/origin/life rather than reconstructing old kinds. Executable bodies are exactly `Life::Concrete` + `Realization::Body`; constructors are `CallableOrigin::Ctor`; host promises and platform effects remain distinct origins/states. AST, compiled owner and GOT slot are read only from their legal lifecycle arms. | Default root library check is green for these paths; expression execution, entry-point validation and test eligibility retain their positive and negative cases without runtime shape checks. |
| 6. Persistence and presentation projections | `src/save.rs`; `src/display.rs`; `src/repl/mod.rs`; `src/repl/commands.rs`; `src/repl/format.rs`; `src/repl/format_type.rs`; `src/repl/search.rs` | One exhaustive int-private projection over `Binding`/`Decl`/`CallableOrigin`/`Life` supplies save, list, doc, signature, search and type display. Candidate resolution replaces `Import` walking; `GroupKind` distinguishes macro and overload; `TypeRecord`, `TraitRecord`, `SpecialFormRecord` and ctor `type_def_info` supply their facets. Preserve source/sequence and rendered bytes; use the unboxed return `Type` directly. | Save/restart and REPL golden/command tests retain bytes, ordering, classification and ambiguity diagnostics; a grep finds no old lifecycle vocabulary in production presentation code. |
| 7. Dead carrier removal | `src/cluster.rs`; `src/code.rs` | `PreparedCommit` is the sole pre-publication carrier. Delete `ProcessedCluster.entries`, `ProcessedCluster.redefinitions`, their plumbing, and the unused `SessionModuleEntry` alias; do not create a replacement lifecycle DTO. `PublicationReceipt` is only the post-publication effect receipt described in §7.1.1. | Root library check plus a production-use search shows no raw-entry publication, `ProcessedCluster` outcome storage, or persistent receipt state remains. |
| 8. Agent all-features surface | `src/agent/harvest.rs`; `src/agent/pull.rs` | Harvest consumes the same `Binding` presentation projection and selects docstring grain without mutating a clone. Pull's existing `set-doc` behavior must use §14's metadata-only table operation. No callable reconstruction or mutable getter is permitted. | `cargo check -p cranelisp --lib --all-features` and the agent harvest/set-doc tests are green after the public gate; default-only green is not this family's exit. |

Within the visit, implement families 1–3 before re-arming readers: they establish
the only publication and birth routes. Families 4–6 then convert consumers
against the settled representation, family 7 removes the now-unreferenced
scaffold, and family 8 closes the feature-gated surface after its user/API
gate. This order visits each path once and prevents presentation or fixtures
from inventing compatibility shims while the ownership spine is still moving.

Backend unit fixtures and root `#[cfg(test)]`/sibling fixture modules are not
part of this production pass. They form the already-planned subsequent fixture
migration; their stale constructors must not be used to widen the production
facade. The production exits above therefore precede, but do not replace, the
workspace all-targets fixture gate.

## 14. Public API, schema and ABI effects

| Surface | Effect |
|---|---|
| `cranelisp-types` `public-api.txt` | **Two individually approved and baseline-confirmed C6 additions.** (1) `set_plain_callable_docstring(&mut self, &Symbol, String) -> Result<(), LifecycleError>` is implemented and its generated baseline line was user-confirmed on 2026-09-03. It is the sole agent `set-doc` mutation; its current behavior is specified by `crates/cranelisp-types/src/module.rs::set_plain_callable_docstring` and `design/arch/symbol-table-lifecycle.md` §4.4. (2) The S121-approved signature was `publish_compiled_staged(&mut self, SymbolTable<C, ()>, &[StagedPublicationDecision], HashMap<Symbol, C>) -> Result<Vec<PublicationRecord<C>>, CompiledPublicationRejection<C>>`; that operation and the opaque `CompiledPublicationRejection<C>` with `reason` / owner-returning `into_parts` were implemented, independently reviewed and generated-baseline-confirmed on 2026-09-03. S122 subsequently changed only the owner-map key in this displayed signature to `CallableTarget`; the current transaction and overload-family contracts are `design/arch/symbol-table-lifecycle.md` §§4.4 and 5.3 plus the method's source rustdoc. The dated S121 approval record remains available at Git checkpoint `dc78ddbee3107043925505531798667dc61f7a03`. The full types suite was green at 262/262; QA's staging-tombstone and `Life::Declared` refusal controls proved owner return plus zero live mutation. The operation atomically binds the exact keyed owner set while publishing the staged cluster; `publish_staged` remains owner-free. No raw map access, callable reconstruction, sequential live owner attachment or owner-bearing staging is permitted. |
| `cranelisp-typecheck` `public-api.txt` | **none from C6.** `instantiate_demands`' one line is C3's |
| `cranelisp-backend`, `cranelisp-intrinsics`, `cranelisp-primitives`, `cranelisp-platform` baselines | **none from C6** |
| `CACHE_SCHEMA_VERSION` | **read-only.** 24→25 is C1's, once |
| `ABI_VERSION` | **read-only.** 9→10 is C7's, for the FIXME-0934 IO node |
| `cranelisp-exe-bundle` | none. A binary has no baseline; the exe-bundle stub is untouched |
| root `EvalResult` | user-approved `Definitions { symbols: Vec<FQSymbol>, warnings: Vec<Warning> }`; `ty()` returns `Option<&Type>` because a batch has no singular type. No inter-crate baseline, cache field or ABI effect |
| `CompilerSession::new` | **User-approved root public API correction (2026-09-04):** `pub fn CompilerSession::new(settings: SessionSettings, project_root: PathBuf, entry_module_name: &str) -> Result<CompilerSession, CranelispError>`. Bootstrap lifecycle failure is propagated through this constructor; `main` and callers use `?`/an explicit error path. This changes no inter-crate baseline, cache schema, platform contract, or ABI. |
| `repl/spec.md` | `qa`/`spec` own the traceability band; §3.7's recorded non-conformance is cleared by N6b's landing, not by this design |

All three public-surface stop rules fired and received their pre-implementation
user decisions, including the fallible root constructor on 2026-09-04.
The metadata method has also passed its generated-baseline confirmation. The
compiled-publication source, independent review, QA correction and baseline
generation are complete, and the user confirmed the exact generated delta on
2026-09-03. Int must not consume a different signature. The root must not
clone/rebuild a `Callable`, publish a live cluster before all of its owners, or
allow compiled owners into ordinary staging.

`ModuleAliases` is unserialized session state, so the alias change adds no
cache field and no restore-format question; the `imports`/`submodules` table
fields the map is rebuilt from are unchanged.

## 15. Handoffs

**Upstream, consumed (no action owed by C6):** C1's lifecycle machine, schema
window, scoped alias walk and `module_alias_key` mint; C2's quote classifier;
C3's `instantiate_demands`, its `written_trait_impls` producer and its one
alias call-site flip; C4's canonical glue and its removal of the 0898 backend
twin; C5's typed handle vocabulary and `TAG_SEXP_ANNOTATED` arm.

**Discharged, and now ordinary upstream consumption (2026-09-01):**

| # | Was | Ruled | What C6 waits on |
|---|---|---|---|
| H1 | the missing 0869 producer | `trait-impl-cache-carrier.md` §9 allocates it to C3, whose design carries it as CS-6; the `check_trait_impl` seam correction rides the same change-set | C3's CS-6 landed — an N3 entry gate, not a scheduling request |
| H2 | the unruled scoped alias lookup | `module-alias-scoped-lookup.md` rules the walk, the visibility split and the `module_alias_key` mint into C1's one types window, with C3 flipping its single call site | C1's walk and mint landed; typecheck's consumer needs no C6 coordination |

Neither leaves a residual owed to C6, and neither widens the stream: the two
rulings moved authority upstream and left C6 with writer, consumer and
evidence work it already reserved.

**Downstream, owed by C6:**

| # | To | What |
|---|---|---|
| H3 | `qa` | plan rows for: the fresh/warm parity matrix (children × public/private × second-dependency-path); the written-impl enrolment outcomes (Enrolled / AlreadyEnrolled / divergence-rejects); the alias evidence set of `module-alias-scoped-lookup.md` §7 — 0798's own matrix both polarities, **scoped isolation** (two modules aliasing `u` to different targets, each resolving its own and neither seeing the other's), the undeclared-alias negative twin, and submodule parity **fresh and warm** (the restore mirror is a distinct writer); the 0553 decline-as-warning leg; 0933's three unit rows; 0914's `deallocs +2 live +0` evidence run; the colour-**on** `/sexp` fixture for the sole-element parenthesized annotation `(:Int 42)` (§7.3.1 — the colour-off bytes are already pinned by `tests/spec_08_modules.rs:1607` and the demo goldens; the §10.3 R4 span boundary is not); and N5's direct/generated macro checkpoint matrix: clause failure publishes nothing, later failure retains success, gaps on both sides resume exactly, reload replacement persists, multi-clause parent/owners publish together, reader replacement is generation-consistent, `MacroClause` is inaccessible as a language value, exact 3→1 retirement cannot match a foreign/ordinary row, 3→1→3 uses fresh slots after tombstones, late refusal is unchanged, and cache restore proves the parent↔active-clause bijection in both directions. Also: the 0694 D1/D2 experiments are unblocked at the `MODULE_TRACE` seam N1/N5 preserve |
| H4 | C7 | the manifest-order mint invariant (slot *i* == descriptor *i*) and the located refusal's error class; C7 owns schema, `ABI_VERSION` and fixtures |
| H5 | `arch` | one stale-record correction, plus one locus refinement, in `arch`-owned text: 0898's "two encodings" framing, now three (§9.2); and `annotated-sexp-node.md` §7's row 5, whose locus list names `src/pretty.rs:583/:590` but not the two sibling `starts_with(':')` role tests at `:271` and `:369` that fall in the same deletion (§7.3.1) — the row's *disposition* is unaffected, so this is a citation refinement, not a re-routing. The retirement-list correction itself is **discharged** by the 2026-09-01 current-state box, as is the `check_trait_impl` citation |
| H6 | `dev`(int) | two source-text corrections `design` may not make. (a) The stale-citation sweep `result-owner.md` already names — `src/result_owner.rs::release_key` rustdoc and `src/CLAUDE.md` §"Program-result ownership" both cite the retired FIXME number 0892; the ruling is 0896. (b) Riding N3: `src/CLAUDE.md` §"`(mod X)` short-name alias" states that import-alias bare qualified refs "resolve only via `<owner>.alias/…`" and that submodule aliases are bare-keyed for longest-prefix matching — both become false at the flip, and the same rationale is spelled in `dependency.rs`'s two rustdoc blocks |
| H7 | `spec` / `qa` | `repl/spec.md` §3.7 records `/mem`'s exclusion as a known non-conformance and names the snapshot form as the truthful instrument. When N6b lands, that record and `repl/demos/memory-lifecycle.demo`'s closing note need re-reading. Not C6's text |
| H8 | `qa` | Correction boundary: direct and generated macro redefinitions followed by `Done`, `Gap→Done`, `Gap→dependency failure`, and later `Err`; one-shot settlement in eval and dependent-recheck success/failure; initial-load and watcher/reload worker acknowledgement on every terminal with no persistent receipt; the `New`-only batch compatibility route proves its receipt inert. Candidate-gate polarities cover public external outside-`D(M)` reject, inside-`D(M)` admit, private admit, same-module/self-alias admit, and unknown-`D(M)` admit; the bootstrap sweep is non-vacuous and includes the forbidden negative. Bootstrap failure injection reaches `CompilerSession::new` as `Err` without panic and successful seed validates. Structural fences find no bootstrap lifecycle `unwrap`/`expect`/`unreachable!`, no binding-shaped/no-op closure gate, no `ProcessedCluster` outcomes, and no scheduler/session receipt mailbox. |

## 16. `/review` reject criteria

Standing rejects for this surface, in addition to `result-owner.md` §Next
skills' list, which remains in force:

1. **A second lifecycle representation.** Any int-side predicate that re-derives
   `is_concrete()`, slot legality, origin×state legality or tombstone
   conservation. Int calls C1's validation; it does not re-state its clauses.
2. **A source-form replay fallback.** Any surviving path that re-injects an
   `__expr` (or any other form) to trigger instantiation after N2.
3. **A cache-specific parallel.** A child-enrolment, impl-enrolment or alias
   path that exists only on the restore branch. The cure is the same call at
   the equivalent point, or it is not the cure.
4. **A silent pick on divergence.** `enrol_written_trait_impl` returning
   `AlreadyEnrolled` is success; a divergence swallowed, retried, or resolved
   by preferring one row is a Blocker.
5. **A blanket accept-before-slash.** 0798's fix must keep an *undeclared*
   alias a located "module not found"; a substitution that accepts any head is
   a Blocker.
6. **A name-shape test in presentation.** Any branch on `def`, `-def`, a
   `*-def` suffix, `stdlib`, or a module identity (Principles 10 and 19).
7. **A projected macro presentation.** `presentation_scheme`, a parallel
   presentation store, post-publication table scan, reader-side inference, dry
   invocation typecheck, second source field, or cache field. Introspection
   describes the macro binding; it does not predict the type of invoking it.
8. **A compensating walk in `src/marshal.rs`.** The one releaser is
   `consume_sexp` and it lives in intrinsics; a private traversal in int is the
   mirror class the spine removes.
9. **A retained lexical annotation test.** Deleting `is_annotation_symbol`, the
   `save.rs` colon suppression or the `pretty.rs` dispatch and re-introducing an
   equivalent string-prefix test under another name — including any surviving
   `starts_with(':')` in `src/pretty.rs` after §7.3.1, and any re-introduced
   whole-list cyan span that swallows the annotated subject.
10. **A second GOT-cursor authority.** Re-introducing a direct cursor write in
    `platform.rs` or anywhere else.
11. **A panic at the platform load boundary.** 0933's refusal is a diagnosed,
    located load error.
12. **A macro-specific `fresh_jit_drop_glues` writer, or a non-pair row
    update.** Macro checkpoints use the ordinary publication seam.
13. **A second alias-key mint, or a bare-key survivor.** Any
    `module_aliases.insert` whose key is not `module_alias_key`'s output —
    including a hand-spelled `<owner>.<alias>` in a fixture — and any retained
    global longest-prefix leg as a fallback beside the scoped walk.
14. **A tolerance for the empty `written_trait_impls` vector.** A
    `#[serde(default)]`-shaped read, an "empty ⇒ rescan the trait home"
    fallback, or any restore-time reconstruction from mangled method names.
    The intra-wash sidecar regenerates (§5.2).
15. **A split compiled publication.** Publishing one module's staged delta before
    attaching every compiled owner, accepting owner-bearing ordinary staging,
    or retaining a per-symbol `publish_compiled_owner` loop for the prepared
    cluster. The approved operation is the one §14 transaction.
16. **Owner release before GOT rollback.** On compiled-publication refusal,
    dropping any returned owner before every touched GOT cell has been restored
    to its pre-codegen snapshot, or treating the refusal as unreachable.
17. **A retained temporary macro world.** Any `PreparedMacroTurn`,
    `TurnCheckWorld`, `TurnDelta`, candidate-clause invocation, reserved
    unpublished slot stack, or cross-module rollback transaction.
18. **A retry that replays a committed checkpoint.** Re-expanding an authored
    form to recreate its already-committed generated macro, or treating that
    checkpoint as permission to accept a genuine second same-name definition.
19. **Persistent publication receipts.** Any scheduler mailbox, `SharedState`
    or `ModuleState` field, parking record, cache field, or source-continuation
    payload containing committed outcomes. Receipts are move-only route values.
20. **A binding-shaped closure gate.** Retaining the hardcoded no-op,
    `write_is_closure_valid`, or any second predicate over `Binding` beside the
    candidate-shaped gate.
21. **A bootstrap lifecycle panic.** Any `unwrap`, `expect`, or
    `unwrap_or_else(unreachable!)` used to assert a fallible lifecycle
    transition during bootstrap or session initialization.

## 17. Falsifiers

Each of the visit's load-bearing claims, and what would refute it:

| Claim | Falsifier |
|---|---|
| The restored world equals the fresh one for children, impls, aliases and instances | any parity cell where fresh and warm disagree on a *relationship* (not a timing) after N3 |
| `minted_from` projection covers every historical instantiation | a T1 cure after which a previously-live mono variant is absent and no decline warning names it |
| Declining a stale demand is above the driver-replay floor | a reload where `instantiate_demands` declines a demand the single-`__expr` replay would have re-minted |
| The publication gate has no readable-but-unpopulated interval | a `MODULE_TRACE` under load showing an eval read preceding the staging→live commit for the read symbol |
| A macro checkpoint is independently complete | any clause, active owner or required expansion-time realization absent when its parent becomes visible |
| Later failure retains an earlier macro checkpoint | a later error restores the old macro, removes the new macro, or makes its active clause uncallable |
| Gap retry does not replay a checkpoint | duplicate-definition handling or a second macro codegen caused by retrying work after an already-committed checkpoint |
| Macro replacement is generation-consistent | a reader snapshots old parent metadata with a new clause pointer/owner, or the reverse |
| Macro shrink selects only owned surplus clauses | any prefix scan, any absent-key decision for an ordinary/foreign callable, or a selected key not derived from the prior parent's exact `M..N` indices |
| Retired macro-clause slots stay frozen | 3→1 clears or reuses either surplus slot, or the following 1→3 does not mint fresh slots for indices 1 and 2 |
| Macro cache parent and clauses are bijective | a cache with a missing, duplicate, surplus, wrong-group or `Plain` clause row restores instead of regenerating |
| Rule 0's clear is sufficient | a clause compiling with a `Borrowed` `(SList Sexp)` parameter after the clear — D4's standing fence |
| The 0638 trap is dissolved, not braved | any of the five `macro_expansion_interior_alias_double_free` pins red under plain **or** M1+M2-armed lanes after Rules 1–3 |
| The census is closed | a `/review` grep finding a public-insert seam with no recorded disposition |
| Candidate closure is checked before publication | any public cross-module candidate outside `D(M)` reaching the table or GOT; any binding-shaped predicate deciding exposure |
| Committed outcomes are settled exactly once | any successful checkpoint outcome lost on later `Gap`/`Err`, applied twice on retry, or retained in scheduler/session state |
| Bootstrap construction is diagnosed, not asserted | an invalid synthetic lifecycle transition panics or a constructor caller can observe a partially mounted seed world |
| An alias is found only from the module that declared it | a module resolving a bare qualified reference through another module's private alias or submodule short name, after N3 |
| The empty-vector window is a regenerate, not a defect class | a warm parity failure reproduced from a sidecar written **after** C3's producer landed |
| C6 needs no public surface beyond C1 | **Falsified twice 2026-09-03:** the all-features `set-doc` writer needs §14's metadata-only mutation funnel, and prepared publication needs the owner-conserving compiled-staging transaction. Both responses are individually approved public gates, not raw mutation, lifecycle reconstruction, owner-bearing staging or sequential live owner attachment. |
| The `pretty.rs` annotation dispatch is unreachable from the reader, so deleting it changes no reader-driven output | the wrong-accept row (§7.3.1) passing **before** the deletion — which would mean the helper never fired and the deletion is a no-op, not a cure — or any colour-off `/sexp` byte moving |

## 18. Quality attributes

- **Simplicity.** Net deletion across the visit: `strip_io_head`,
  `capture_instantiation_drivers`, `reload_module(extra_forms)`,
  `protect_marshalled_cell` and its four sites, `marshal::rc_inc`,
  `leading_annotation_len` and its plumbing, the platform cursor write, the
  int-side broken registry, the private `alias_key` mint, the no-op
  binding-shaped closure gate and `write_is_closure_valid`, three `RC == 2`
  marshal unit rows, and the `pretty.rs` lexical annotation dispatch — four
  functions plus three `starts_with(':')` arms, against a replacement already
  running in the same file. Additions are one projection, one enrolment loop, one
  child-enrolment call, one field clear, one crate-private `Introspection`
  field, and one located error — plus, at five alias sites, a call to a mint
  that already exists upstream.
- **Maintainability.** Every removed item was a private copy of a fact another
  crate owns. The visit's durable product is that int holds no second
  representation of the lifecycle, the result-root rule, RC, or the
  instantiation trigger. Post-publication outcomes have one move-only route
  owner and no mailbox lifecycle; candidate exposure has one truthful gate.
- **Observability.** No new trace sink or ring buffer. The `MODULE_TRACE`
  emission at the staging→live commit is preserved deliberately (§5.5) because
  it is the instrument 0694's D2 experiment needs. `/mem` becomes truthful,
  which restores an instrument the S118 work silently invalidated.
- **Concurrency-safety.** Rule 5 removes a non-atomic host RMW on cells the JIT
  and its lenient-eval sparks touch atomically. Macro readers snapshot one
  generation under the module guard, and `fresh_jit_drop_glues` keeps its
  pair-atomic replacement invariant through the ordinary publication seam.
  Retry stores source continuation only; publication receipts stay stack-local;
  marshal handles stay frame-local by Rule 7. Bootstrap tables are built
  off-map and mounted only after fallible lifecycle construction succeeds.
- **Performance.** One extra keyed read per cache-hit module (children,
  written impls), one bounded `consume_sexp` walk per macro expansion over trees
  small by construction, one demand projection per T1 cure. All compile-time;
  no runtime path changes.
- **Testability.** The reservations in §13 are submodule-grained, which is what
  makes the unit tier attributable per seam (METHOD §2.2). The three seams that
  need no session — the `minted_from` projection, the marshal single-owner
  invariant, and the alias writers' keying — are pure transforms and carry their
  own rows. The walk itself is unit-tested in `cranelisp-types` by C1, so int's
  rows discriminate what int decides: that each writer keys under its declaring
  module, and that each consumer passes the module doing the referring.
- **Untouched this visit.** int's compiler-internal concurrency architecture
  (`concurrency-architecture.md`), the scheduler and cadence model, the
  observability sinks, the `--link` driver and the exe-bundle stub.

## 19. Open, and owned elsewhere

- **0694's attribution** — `qa`'s, under the control discipline. C6 supplies the
  seam and the invariant; the experiments are D1/D2.
- **0818's hypothesis** — `qa`'s. Recorded, not implemented.
- **0800 face 3** — `/stdlib`'s API decision, then `/repl` presentation. Not
  reopened here.
- **0050** — trigger-gated on a display protocol that does not exist.
- **0052 / `/learn`** — ACT-0951's complete user-ruled specification gates any
  future work.
- **The lenient-view `ConcreteType::Int` placeholder** (`result-owner.md`
  §1.1.1's recorded limitation — why an unpinned `[]` or bare `None` result
  still leaks) is a typecheck row, not an int row.

## Next skills

- **`/sprint`** — C6 opens with no blocker owed to it. N3's two upstream gates
  are C3's CS-6 producer and C1's scoped alias walk, both inside the ordered
  wash; the gate to watch is that N3 does not open on C3's *start*. Note the
  §12 bundle order, which is not the FIXME-number order.
- **`/arch`** — H5's two remaining stale-record corrections.
- **`/qa`** — H3's plan rows, and the 0694 D1/D2 experiments the preserved
  `MODULE_TRACE` seam unblocks.
- **`/dev`(int)** — the §12 bundles in order, with §16's rejects and §17's
  falsifiers as the acceptance frame; H6's stale-citation sweep rides N6b.
- **`/design`(int)** — re-open only if an upstream facade moves. A later stream
  may not redesign a path this visit has released (SPRINT §No-refix rule 2).

## Cross-references

- `design/arch/symbol-table-lifecycle.md` §§4–6 — the current machine,
  publication funnels, declaration populations and enforcement. The S121
  handoff table is migration provenance in [the lifecycle design at checkpoint
  `dc78ddbe`](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/symbol-table-lifecycle.md)
  §9.
- `design/arch/bounded-contexts.md` §2 (the `instantiate_demands` contract),
  §6 (the macro-clause ABI ruling, the `Introspection` narrowing).
- `design/arch/trait-impl-cache-carrier.md` — the 0869 contract, §6's residual
  and §9's C3/C6 allocation.
- `design/arch/module-alias-scoped-lookup.md` — the 0798 contract: the scoped
  walk, the mint, and the C1/C3/C6 allocation.
- `design/int/result-owner.md` §1.1.1, §4.2.1, §11 — the release key, the
  `/mem` seam, the 0863 ordering.
- `design/int/macro-turn-ownership.md` §3, §8, §9, §12 — the protocol, the
  `dev` gates, the 0863 interaction.
- `design/int/s117-conformance-recovery.md` §1.1.2, §6, §6.5 — the prepared
  transaction and the presentation design.
- `design/int/prelude-table-write-isolation.md` §2.1, §2.4 — the census.
- `design/int/session-transaction.md` §5, §6, §7, §10 — Broken, the retention
  pool, the commit gate, the T1 cure.
- `design/int/impl-redefinition-hot-reload.md` §3, §5 — the enrolment
  derivation.
- `design/backend/s122-closure.md` §2 and `design/backend/non-concrete-release-contract.md` §5.6 — the backend twin, the `Bind`
  seed rider.
- `design/runtime/s119-typed-consume-funnel.md` §3 — the typed handle
  vocabulary.
- [ownership/disposal 5](../intrinsics/ownership-and-disposal.md#5-the-sexp-family) — the `TAG_SEXP_ANNOTATED`
  arm.
