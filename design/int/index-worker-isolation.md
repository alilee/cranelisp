# Index-feed isolation contract — the background stdlib indexer never shares a substrate with the foreground compile

Owner: `/design` (int). Subordinate to `int.md` (§ the compilation cadence) and to the
concurrency-isolation lineage `heisenbug-race-closure.md` (S61) →
`signature-body-prepass.md` (S93). Authored Sprint 110 Phase 3 to record the durable
cure for **FIXME 0604** (the index-feed phantom-prelude write-race). The attribution of
record is `tests/plan/s109-attribution-index-feed-race.md`.

> **This is a contract, not a root-cause claim.** The isolation *invariant* below is the
> design intent the S110 fix must satisfy. Which surviving write violates it is for
> `/dev` + `/testing` to LOCATE with the ≥25-iteration `CRANELISP_MODULE_TRACE=1` sweep
> BEFORE patching (per the memory lesson *verify-fix-not-symptom-absence* — a
> scheduling-perturbation fix that quiets the crash under one interleaving is a
> false-green). §4 names the prime suspect the sweep should confirm first; the contract
> holds regardless of which channel the sweep implicates.

> **SCOPE RULING (S110 Phase 5, FIXME 0626).** The **in-memory** half of this contract
> (§3.1/§3.2 — private discard substrate for symbol tables, aliases, prelude-fallback) is the
> **landed, adopted cure** and remains the live design intent. The **cache-channel severance
> (§3.3)** is ruled **WON'T-DO** (§25.5 kept) — the 0604 defect is proven foreground and does
> not flow through the index cache channel, and the cache-hit is a genuine optimization with no
> proven harm (full rationale in the §3.3 ruling box). Read §2's "no cache artifact" clause and
> §5's guard item 2 as **scoped to the parked cache-channel proposal, not enforced end-state**.

---

## 1. Actors and the function between them (Principle 21)

Two actors run concurrently over the one `Arc<SharedState>`:

- **The foreground compile** — the eval thread and the priority workers. Owns the
  authoritative `shared.symbol_tables`, `shared.module_aliases`, `shared.prelude_fallback`,
  and `shared.cache` (the source-hash manifest + on-disk `.meta`/`.o`). A user `(import
  [num.bits [bit-and]])` runs here.
- **The background index feed** — the nice workers, draining `IndexModule` tasks
  (`index_worker.rs::run_one_index_task` → `index_one_module`, the three branches). REPL-only
  (R17), best-effort (R18). Its *product* is the in-memory `/search` reachability index
  (`shared.importable_indices` rows).

The function between them is the one this contract governs: **"warm the `/search` index for
a not-yet-imported module."** The defect is that the background actor, to compute that
product, currently touches substrate the foreground actor later reads — so a background
warm-up can change the outcome of a foreground compile. That coupling, not any single
interleaving, is the bug (the S61→S93 lesson: a coupling closed by cleanup/undo re-opens
through the next window; a coupling closed by construction stays closed).

## 2. The invariant (the durable cure)

> **INDEX-ISOLATION.** No index-feed branch may write, or cause to be written, ANY
> substrate that a foreground compile reads. The index feed's only output is the in-memory
> `shared.importable_indices` rows. Every intermediate the index typecheck needs —
> symbol tables, module aliases, prelude-fallback bits, staging — is a **function-local
> discard substrate**, dropped before the task returns; and the index feed writes **no
> foreground-consumable cache artifact** (no `.meta`, no source-hash manifest entry, no
> `record_compiled`).

Under INDEX-ISOLATION the four R13 SharedState maps are byte-unchanged by the feed **by
construction, not by undo** — there is no residue to remove because there is no live write
to make. The "typecheck-into-live then remove the residue (R13)" model the FIXME quotes is
retired: R13 stops being an obligation the code must discharge and becomes a property of the
substrate's shape.

## 3. As-built vs. the contract — what already holds, what leaks

The S91 refactor (`9ba2ca91`, 2026-06-26) already moved the **in-memory** half onto a
discard substrate. The contract ratifies that half and closes the half it missed.

### 3.1 In-memory tables — ISOLATED (S91, ratified here)

`checked_typecheck_module` (`index_worker.rs:1053`) builds a function-local
`private_tables: DashMap<ModuleFullPath, SessionSymbolTable>` — a **deep** snapshot of live
(the `symbols` field is a plain `HashMap`, so `SymbolTable::clone` copies it; the shared
`Arc<GotTable>` carries no bindings) — plus a fresh `private_aliases`. The indexed module
starts empty in the snapshot (Replace semantics). `index_typecheck_into_private` runs
`install_imports` / `install_exports` / `register_macro_in_module` / `check_forms` against
those **private** maps only, wrapped in the CF.2 `catch_unwind`; the typed entries are read
back out of `private_tables[module]` and the whole snapshot is dropped at function return.
This half satisfies INDEX-ISOLATION for `symbol_tables` and `module_aliases` today.

**Doc-hygiene defect (own-file, `/dev`).** The docstrings at `index_branch_c` (`:928–937`)
and the top-of-file model note (`:13–21`, "typecheck once … against throwaway staging …
then REMOVE the live residue so the four SharedState maps stay byte-unchanged (R13)") still
describe the **retired** mutate-live-then-undo model and even name `cluster::process_cluster`
as the driver — which `checked_typecheck_module` no longer calls (it calls
`index_typecheck_into_private`). A stale "R13 by cleanup" docstring is precisely the framing
that invites a future edit to reintroduce a live write "and just undo it." These comments are
rewritten to the isolated model (private discard substrate; R13 by construction) in the same
change-set as the fix.

### 3.2 The prelude-fallback thread — read-only, but LIVE (tighten)

The one live SharedState handle still threaded into the "isolated" typecheck is
`&shared.prelude_fallback` (`:1097`). Audit of every index-path callee
(`install_imports`/`install_exports`/`register_macro_in_module`/`check_forms`) shows all
four **read** it (`.get`) and none **write** it — so it is not a write leak today. It is,
however, a live map read concurrently with foreground writes, and it is a live handle a
future edit to any of those callees could turn into a write without tripping the invariant's
greppable form. Contract: snapshot it into a function-local `private_prelude_fallback`
alongside `private_tables`, so the index typecheck reads a consistent, private fallback and
the invariant's grep (no `&shared.*` map into an install/typecheck/register call) is total.
This needs **no types-level primitive** — `PreludeFallback` is a `DashMap` alias cloned the
same way `private_tables` already is (see §6, the contingency check).

### 3.3 The cache artifact — the LEAK the in-memory isolation missed (the load-bearing gap)

The index feed does **not** stop at in-memory tables. On a clean branch-(c) check it writes
**foreground-consumable persistent state**:

- `write_index_meta` (`:995`) serialises a `.meta` for the module, explicitly "so a later
  real `/import` of this module is a **cache-hit** (§25.5)" (`:946–948`, `:990–994`);
- it records `shared.cache.record_source_hash(module, hash)` **and**
  `shared.cache.record_compiled(module, hash, {})` (`:1034–1037`), and `try_branch_b`
  likewise `record_source_hash`s (`:916`).

These are **live writes into `shared.cache`**, a substrate the **foreground import path
reads** (`is_cache_valid` → deserialise the index-written `.meta` → install its entries
without re-typechecking). So even with the in-memory tables perfectly isolated, the index
feed reaches the foreground compile through the cache: a background warm-up of module *M*
publishes a `.meta` + manifest entry that a subsequent real `(import M)` (or a transitive
import of *M*) installs verbatim. If the index typecheck's result differs in any entry from
what the real Phase-1 writer would have produced for that module — which the **0569 macro
carve-out already proves can happen** (`:950–969` suppresses the index `.meta` for
macro-carrying modules precisely because the index result is *incomplete* for a real import)
— the difference is laundered into the foreground world as a cache-hit. This is the
persistent-artifact analogue of the mutate-live-then-undo coupling, and it is the channel the
S91 in-memory isolation left open.

> **RULING — §3.3 severance is WON'T-DO; §25.5 is KEPT (S110 Phase 5, FIXME 0626, `/design`
> (int)).** The 0604 `/dev` deployment implemented then **reverted** the severance below; the
> ruling ratifies the revert. Two facts decide it:
>
> 1. **§3.3 does not fix 0604.** The 0604 deterministic recipe (`--run --no-cache`) drives the
>    index feed **0×** — `arm_importable_index()` is REPL-only (`main.rs:342`) and
>    `index_one_module` fires 39× under REPL but never under `--run` (instrumentation, FIXME
>    0626). The residual phantom writer re-scopes to the **foreground** concurrent-compile path
>    (carried to S111; re-attribution owed to `/qa`). Severing the cache channel therefore
>    cannot change the recipe's outcome — the entire raison d'être of this contract (a durable
>    cure for 0604) is refuted for the cache face.
> 2. **The dangerous coupling is already closed.** The S61→S93 lineage concern is a
>    *shared-mutable-state* race; that is the in-memory half (§3.1/§3.2), **landed**. The cache
>    channel is a *persistent-artifact read* — a materially safer shape, content-addressed by
>    source hash and gated by `is_cache_valid`. The one known divergence (an incomplete index
>    `.meta` for a macro-carrying module) is already carved out at `:950–969`.
>
> Against that: severing retires **§25.5, a genuine optimization** (warm-project startup stays
> mostly `.meta`-reads; a found-then-imported symbol skips a re-typecheck), reddens **three
> committed GREEN pins** in `tests/search.rs`
> (`search_branch_c_stale_meta_typechecks_writes_meta`,
> `search_burndown_arms_at_repl_startup_neg_not_on_first_search`,
> `search_index_to_import_is_meta_cache_hit`), and imposes a re-typecheck on every
> actually-imported module — real cost, **zero proven benefit** (per the evidence-gated-carry
> discipline: retire an optimization only with proof it is harmful; the 0604 proof is refuted).
> So **§25.5 stays live**; `agent.md §25` (which already describes §25.5 as the live cache-hit)
> is unchanged; this doc's INDEX-ISOLATION invariant (§2) scopes to the **in-memory** substrate
> as its landed end-state.
>
> **Parked as a movable boundary (revisit on evidence).** The cache-channel coupling the text
> below analyses is real *in principle* — the 0569 macro carve-out is a special-case, not a
> closed-by-construction property, and the S93 doctrine prefers the latter. It is parked, not
> dismissed: **if a trace sweep ever exhibits a non-macro module whose index-written branch-(c)
> `.meta` diverges from what the foreground Phase-1 writer would produce** (i.e. the carve-out
> proves insufficient), re-open this section and re-weigh the severance against that concrete
> evidence. Absent such an observation the optimization is carried. The original severance
> analysis is retained below for that future re-weighing.
>
> ---
>
> **(Superseded severance proposal — retained for the parked re-weighing above.)**
> Sever the
§25.5 index→import cache-hit. The index feed's product is the in-memory
`importable_indices` rows and nothing else: on branch (c) it records rows and writes **no**
`.meta`, **no** `record_source_hash`, **no** `record_compiled`; branch (b) may *read* a
foreground-written `.meta` (that is the foreground's own artifact, byte-authoritative) but
records no manifest side-effects of its own. A later real `/import` then re-typechecks
through the ordinary foreground path — the cost is one re-typecheck of a module the user
actually imports, paid once, against the removal of a whole class of "background produced an
artifact the foreground trusted." R13's persistent-artifact face would become true by
construction: **the foreground never consumes anything the background produced.** (The
narrow performance regression would be the acceptable-and-bounded side of the
no-shared-substrate trade — but per the ruling above it is NOT taken this sprint.)

## 4. Prime suspect for the trace-sweep (confirm before patching)

Given §3, the trace sweep should first test the hypothesis that the phantom terminal enters
the foreground compile through the **cache channel** (§3.3), not through a live table write —
consistent with every direct symbol-table write on the index path already landing in
`private_tables`. The `bit-and`-only fingerprint (never the identically-shaped
`bit-or`/`bit-xor` beside it) fits a **per-module artifact** race — one module's index
`.meta` / manifest entry published (or read back) at a scheduling-dependent instant — better
than a systematic resolver write. Concretely, watch under `CRANELISP_MODULE_TRACE=1`:
(a) whether the phantom `prelude` terminal appears only after an index `.meta`/manifest entry
for `num.bits`, `prelude`, or a `super`-parent is written; and (b) whether it survives once
the §3.3 severance is in place. If the phantom persists after §3.3 with all three private
snapshots (§3.1–3.2) in place, the residual writer is on the **foreground** import/prelude
path (`process_form/dependency.rs::inject_prelude_if_needed` / `register_dep` / `block_dep`
around `:1354–1425`) and the feed is only the timing perturbation — in which case attribution
moves off int-isolation and the FIXME re-scopes (flag to `/qa`/`/sprint`, do not force a
one-window patch onto the wrong actor).

## 5. Reviewer-greppable invariant (the structural guard, Principle 18)

A `/review` pass on `src/session_v4/index_worker.rs` confirms INDEX-ISOLATION by grepping
for the *absence* of foreground-substrate writes on every index branch:

1. **No live SharedState map into an install/typecheck/register call.** Every
   `install_imports` / `install_exports` / `register_macro_in_module` / `check_forms` /
   `SymbolTableAccess::cluster` call reached from an index branch takes the function-local
   `private_tables` / `private_aliases` / `private_prelude_fallback` / discard `staging` —
   never `shared.symbol_tables`, `shared.module_aliases`, or `shared.prelude_fallback`. The
   only permitted contact with a live map is the **read** that seeds the snapshot clone.
2. **(PARKED — not enforced; FIXME 0626 ruling.)** ~~No `shared.cache` write on any index
   branch.~~ This guard belonged to the §3.3 severance, ruled **WON'T-DO** — §25.5 is kept, so
   branch (b)/(c) `record_source_hash` / `record_compiled` / `write_index_meta` writes are the
   sanctioned as-built (the index→import cache-hit optimization). A `/review` pass must **not**
   flag these as a Blocker. Re-instate this guard only if the parked cache-channel coupling is
   ever re-opened on evidence (§3.3 ruling box).
3. **The feed's sole write target is `shared.importable_indices`** (`record_triples` /
   `record_entries` / `mark_skipped`) and the read-only `feed_loaded_module` projection of
   already-terminal live tables.

Any hit in **(1)** is a `/review` Blocker — a re-opened in-memory coupling, regardless of
whether a current interleaving exhibits the phantom. (Guard (2) is PARKED per the FIXME 0626
ruling — see above; index-branch `shared.cache` writes are sanctioned as-built.)

## 6. Contingency check (per Phase-2 Rev on 0604) — no `/arch` FIXME

The Phase-2 architecture review flagged: *if the indexer's staging/discard substrate needs a
types-level primitive beyond the existing staging-view vocabulary, file `target: /arch` — do
not hand-roll a second staging shape in int.* **Checked and it does not fire.** The complete
substrate is: the deep-cloned `DashMap<ModuleFullPath, SymbolTable>` snapshot (already
as-built), a fresh `ModuleAliases` (already as-built), a cloned `PreludeFallback` DashMap
(§3.2 — same clone shape), and the existing per-cluster `SymbolTableAccess::cluster(priv,
&mut staging, module)` view (already the S72 Decision-44 staging vocabulary, used here over
the private tables). Severing the cache channel (§3.3) is a *deletion* of writes, needing no
new type. No new `cranelisp-types` staging primitive is required; no `/arch` FIXME is filed.

## 7. Acceptance (mirrors FIXME 0604 §Acceptance)

1. INDEX-ISOLATION (in-memory scope) holds — the §5 grep item (1)/(3) is clean; §3.1
   docstrings rewritten to the isolated model; §3.2 fallback snapshot in place. (§3.3 cache
   channel severance is WON'T-DO per the FIXME 0626 ruling — not an acceptance item.)
2. **Fail-on-revert guard lands WITH the fix** (`/dev` + `/testing`): the ≥25-iteration sweep
   of the deterministic recipe against the full real stdlib, plus a unit test at the write
   seam per METHOD §2.2. Behavioural verification (not symptom-absence under a perturbing
   tool) per the memory lesson.
3. The twin guards in `tests/spec_08_prelude_outer_scope.rs` stay GREEN; the
   `concurrency_capacity` verify-after-fix step (0604 Family) is recorded.
4. `/testing` retro-tags the repro family `// defect:` (candidate class
   `shared-state-write-race`, `/qa` to confirm the vocabulary add).

## 8. R7 live-table insertion-seam asserts — the 0604 observability rider (S113 W4)

**Status: DESIGN (S113 Phase 3, `/design`(src/)).** The W4 rider for FIXME 0604
per `/arch` revision 7 (`safety-invariants.md` R7 / §6 task 4) + `/qa`'s
`s113-test-plan.md` PS-R7. The register row R7 is **`/arch`-owned**
(`safety-invariants.md`); this section designs only the **int-side mechanism** —
the live-table insertion-seam asserts — per the SPRINT Q1-revision-1 ownership
split. **Ungated by the W0 depth decision** (it is the user's "assertion density"
palette item, src/-surface and tiny). It is NOT a fix — the S110 `/dev`
disposition re-scoped the phantom writer to the FOREGROUND concurrent-compile path
(the index feed is provably inert under the `--run --no-cache` recipe); the ~320
cumulative no-fires say quiet-environment hunting is spent evidence. **The
deliverable is observability: the next firing anywhere NAMES its seam** instead of
needing another hunt.

### 8.1 The invariant asserted — prelude-export closure

`stdlib/prelude.cl` exports only its declared closure; no stdlib module
re-exports `bit-and`. The defect is a phantom **public** `bit-and →
primitives/bit-and` entry appearing in the live `prelude` module's table (§"The
defect", FIXME 0604). The invariant every live-table insertion must preserve:

> a **public** binding written into the `prelude` module's live table MUST trace
> to prelude's own declared exports / re-export edges — never a foreground
> compile's import-direction write mis-targeting `prelude`.

### 8.2 The mechanism — ONE shared assert at EVERY live-table insertion seam (Principle 7/18)

A single shared helper — not per-seam copies (the mirror the phantom hunt fought)
— called at every seam that writes a `ModuleEntry` into a live `shared.symbol_tables`
table:

```
fn assert_prelude_closure(module, name, entry, /* MODULE_TRACE sink */) {
    debug_assert!(
        module != PRELUDE || !entry.is_public()
            || prelude_export_closure_contains(name),
        "R7 prelude-export-closure breach: public `{name}` written into the \
         `prelude` live table but not in its export closure (source: {…})"
    );
    // Release: cheap MODULE_TRACE emit of (module, name, source, seam-id) on
    // the same predicate — the ghost becomes a named seam on the next firing.
}
```

`prelude_export_closure_contains` reads prelude's OWN declared exports/re-export
edges (the same closure the fallback bit consults), so it is authoritative and
does not itself scan foreground state.

### 8.3 The seams it is threaded through (the enumerated write set)

Every live-table insertion reachable from the foreground concurrent-compile path
(FIXME 0604 §"Why the recipe RE-SCOPES to the foreground" — eval thread +
priority/nice workers building `num.bits` + `num.bits.test` + `prelude` + its
re-exported domain modules concurrently):

1. `src/imports.rs::install_imports` / `install_exports` — the per-symbol
   `Import`/`Reexport` writers (the import-direction writes suspected of
   mis-targeting `prelude`).
2. `src/cluster.rs::insert_cluster` — drains `ProcessedCluster` bindings into the
   live tables.
3. `src/process_form/` + `src/worker.rs` register paths — foreground Def/decl
   commits.
4. `src/imports.rs::insert_detecting_ambiguity` (~L547-560) — the §8.6.5
   poison-consumer is **CORRECT (do not touch its logic)**; the assert is added
   BESIDE the insertion, not inside the poison decision, so it observes without
   perturbing the sanctioned ambiguity behaviour.

Because the assert is single-sourced, its call sites are the greppable structural
guard (§5-style): a live-table insertion WITHOUT the assert is a `/review` finding
(a seam that could write the phantom un-observed).

### 8.4 What this rider does and does NOT claim

- **Does:** convert any future firing into a **named seam** (which insertion, which
  `name → source`) — the observability deliverable; land a unit test at the assert
  seam (METHOD §2.2) pinning that a planted out-of-closure `prelude` public write
  trips the assert; keep the two GREEN twins (`tests/spec_08_prelude_outer_scope.rs`)
  + the IR-1 lane must-hold.
- **Does NOT:** locate or fix the write (no stable RED exists — that is the
  sanctioned no-stable-RED exception; FIXME 0604 stays open until a named-seam
  firing yields the fix + its fail-on-revert sweep). A bounded recipe re-sweep runs
  ONLY in an environment with prior fires — quiet-environment sweeps are spent.

/qa's PS-R7 consumes the named seam when it fires. This is the R7 "seam assert /
diagnosed-error-at-trust-boundary" tier of the `safety-invariants.md` §2 ladder,
applied to the int live-table trust boundary.

## Cross-references

- `tests/plan/s109-attribution-index-feed-race.md` — the attribution of record (mechanism,
  fingerprint, family verdict, the coverage gate 0605).
- `design/int/heisenbug-race-closure.md` (S61) → `signature-body-prepass.md` (S93) — the
  isolation-over-undo lineage this contract instantiates for the index feed.
- `design/int/agent.md §25` — the `/search` importable-index subsystem (R13–R18); §25.5 (the
  index→import cache-hit) is **KEPT** (the §3.3 severance is ruled WON'T-DO, FIXME 0626).
- `src/session_v4/index_worker.rs` — the seam; `src/imports.rs`, `src/process_form/` — the
  installer/prelude writers it drives.
