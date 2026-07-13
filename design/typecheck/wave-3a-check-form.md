> **HISTORICAL — sprint-scoped working doc (Sprint 72 Wave 3a-β).** A completed cluster-atomic-shape design, retained for the audit trail; NOT a durable subsystem reference. The durable per-form-pipeline design lives in `check-form-api.md` + `typecheck.md`. Verify any detail here against current source before relying on it. (Triaged S109, FIXME 0578.)

# Wave 3a-β — `check_form_signatures` + `check_form_body` cluster-atomic shape

> **Superseded 2026-05-13:** §1's two-function shape (`check_form_signatures` + `check_form_body`) is **superseded by Decision 44's 2026-05-13 third amendment** — the typecheck facade collapses to a single `check_forms(parsed: Vec<ParsedEntry>, ctx: &mut ClusterContext, symbol_tables: &SymbolTables) -> Result<(), CheckError>` free function with the two-pass discipline internal to its frame. The rest of this document remains useful for cluster-atomic protocol context (`ClusterContext`, staging-vs-live accessor, View, mutual-recursion via union view, Pass-1/Pass-2 algorithmic content). The canonical surface is `design/arch/facades/typecheck.md` §"check_forms — cluster check". `/dev (typecheck)` will refresh §§1, 7, 10 of this document in detail when implementing the collapsed shape.

**Status.** Sprint 66 Wave 3a-β design (Phase 5 Stage 2 — D/D/R cycle).
**Author.** /design (typecheck), 2026-05-12.
**Scope.** This document refines the master design `design/typecheck/typecheck.md` §§2, 5, 6 (drift register; pipeline structure; mutation discipline) to lock down the **as-designed** shape `/dev` will implement for the Wave 3a-β shape pivot — the two-pass per-form typecheck surface that the orchestrator drives across a cluster.

**Reads.** `design/typecheck/typecheck.md`; `design/typecheck/implementation-slice-s66.md` §1.B + §1.C; `design/arch/facades/typecheck.md` §"Public surface" + §"Bounded-context invariants"; `design/arch/facades/int.md` §"`process_cluster` — the cluster-atomic orchestration loop"; `design/arch/facades/types.md` §"`ParsedEntry`" + §"`View`"; `design/arch/decisions/0044-cluster-atomic-typecheck-orchestrator-staging.md` (amended FIXME 0167); `design/arch/decisions/0045-traitimpl-storage-in-trait-defining-module.md`; `design/arch/principles/17-module-locality-in-typecheck.md`; `tests/process_form_dispatch.rs` (Wave 3a-β gate); `tests/stdlib_trait_impls.rs::stdlib_*` (P17 short-name follow-up).

**Supersedes.** `design/typecheck/check-form-api.md` (single-call shape; `&mut SymbolTable`; pre-Decision-44 framing) for the post-Wave-3a-β shape. `check-form-api.md`'s algorithmic content (Pass-1/Pass-2 dispatch matrix, accumulator pattern, mutual-recursion invariant) survives and is reproduced where it remains correct under the cluster-atomic frame; what does not survive is the single-call entry shape, the `&mut SymbolTable` parameter, and `FormCheckResult` as a per-call return value.

---

## 1. Target signatures

Per `facades/typecheck.md` §"Public surface (as-designed)" + Decision 44 (amended FIXME 0167):

```rust
pub fn check_form_signatures<C, L>(
    parsed: ParsedEntry,
    ctx: &mut ClusterContext<'_, C, L>,
    symbol_tables: &SymbolTables<C, L>,
) -> Result<(), CheckError>
where
    C: CodeStore,
    L: LinkerStore;

pub fn check_form_body<C, L>(
    parsed: ParsedEntry,
    ctx: &mut ClusterContext<'_, C, L>,
    symbol_tables: &SymbolTables<C, L>,
) -> Result<(), CheckError>
where
    C: CodeStore,
    L: LinkerStore;
```

Both are **free functions** at the crate root (`cranelisp_typecheck::check_form_signatures`, `cranelisp_typecheck::check_form_body`). Both are pure with respect to live state; their only observable side effect is mutation of the orchestrator-handed staging `SymbolTable` via `ctx.current_symbol_table_mut()`. Typecheck cannot distinguish staging from live — the accessor abstracts the distinction.

### 1.1 Note on the prompt's `Vec<(Symbol, ModuleEntry)>` framing

The Wave 3a brief (`sprints/SPRINT.md` §"Wave 3a — Critical-path triad…", lines 230–238) describes the deliverable as `check_form` "pure function returning `Vec<(Symbol, ModuleEntry)>`". That framing predates the **FIXME 0167 amendment** to Decision 44 (Approach B + `ClusterContext` introduction). Under the amendment, the 91 register-call sites in `program.rs` continue to mutate **a** `SymbolTable` (now orchestrator-staging); the return-value shape collapses to `Result<(), CheckError>` because the entries are written through the accessor rather than returned. The facade `design/arch/facades/typecheck.md` reflects the post-amendment shape; Decision 44 §"Statement" reflects the post-amendment shape; this design doc binds the post-amendment shape. The earlier `Vec<(Symbol, ModuleEntry)>` brief survives as an intermediate framing only; the post-amendment surface is canonical.

The two surfaces are isomorphic up to where the writes physically land:
- `Vec<(Symbol, ModuleEntry)>` return + orchestrator commits — typecheck owns the registration shape.
- `&mut ClusterContext` + staging-mutation + orchestrator drains — orchestrator owns the registration shape; typecheck flows through the existing accessor API.

The amendment chose the second because the 91 register-call sites already exist and are correct against `current_symbol_table_mut(&mut self) -> &mut SymbolTable`; rewriting them into a return-value channel was a multi-week inversion the amendment explicitly rejected (Decision 44 §"transient-vs-durable" footnote).

### 1.2 Parameter rationale

- **`parsed: ParsedEntry` (by-value Clone).** Per `facades/types.md` §"`ParsedEntry`", the orchestrator clones `ParsedEntry` for retry-on-Gap; passing by value avoids any borrow tangle with the orchestrator's per-cluster `parsed_entries` vector. Pass 2 receives the same `ParsedEntry` instance Pass 1 received (orchestrator persists the vector across both passes).
- **`ctx: &mut ClusterContext<'_, C, L>` (mutable borrow).** Required because `current_symbol_table_mut()` returns `&mut staging`. Pass-internal code mutates staging through this accessor; no other write surface exists in the typecheck call.
- **`symbol_tables: &SymbolTables<C, L>` (shared borrow).** Cross-module FQ resolution (`symbol_tables.get(&fq.module).and_then(|t| t.get(&fq.symbol))`). Shared because other workers may concurrently read peer modules; the inner `DashMap` shards provide the per-module concurrency safety. Typecheck never iterates `symbol_tables` for short-name resolution (Principle 17).
- **Generic `<C, L>`.** Per Decision 32 / Principle 15 — typecheck is C/L-blind. `int` calls with `SymbolTables<Code, Linker>` in production; tests / fine-grained drivers may pass `SymbolTables<(), ()>`. The generic propagates through `ClusterContext<'_, C, L>` and `SymbolTables<C, L>`.

### 1.3 Return-type rationale

Both passes return `Result<(), CheckError>`:

- `Ok(())` — pass completed successfully for this `ParsedEntry`. Pass 1 has staged signature shells; Pass 2 has staged body-checked entries (overwriting Pass 1 shells where applicable). The orchestrator advances to the next form (Pass 1) or to commit (Pass 2 final form).
- `Err(CheckError::Gap(ResolutionGap::SymbolTypechecked(fq)))` — value reference whose target module has not finished typechecking. The orchestrator catches, registers `fq.module` if needed, calls `wait_for_typecheck_symbol(fq)`, retries the same pass with the same `ParsedEntry`. Staging may carry partial writes from before the Gap; the retry overwrites — staging is NOT rolled back on Gap (per facade §"Post-Gap state contract").
- `Err(CheckError::Gap(ResolutionGap::Type(fqt)))` — FQ type reference whose target module has not finished typechecking. Same retry pattern.
- `Err(CheckError::TypeError { message, location })` — genuine type error. Non-recoverable. The orchestrator drops the staging `SymbolTable` on the function-frame return; the live table is byte-identical to its pre-cluster state.

Both passes ask for `ResolutionGap::SymbolTypechecked` (not `SymbolInMemory`) for value references — typecheck needs the entry's `Scheme`, not its compiled code (`facades/typecheck.md` §"Returns"). `ResolutionGap::MacroInMem` is **never** raised by typecheck — by the time either pass runs, macros are already expanded by `cranelisp_frontend::expand`.

---

## 2. Where staging lives — orchestrator-local

Per Decision 44 §"`ClusterContext` (Approach B is canonical)":

```text
int::process_cluster (orchestrator stack frame)
├── let mut parsed_entries: Vec<ParsedEntry> = …;       // from build_form
├── let mut staging: SymbolTable<C, L> = SymbolTable::empty();   // orchestrator-local; transient
├── let mut ctx = ClusterContext::Cluster {
│       modules: &shared.symbol_tables,                          // for cross-module reads
│       staging: &mut staging,                                   // current-module writes
│       current_module: scope.clone(),
│   };
├── // Pass 1 across cluster
│   for parsed in &parsed_entries {
│       check_form_signatures(parsed.clone(), &mut ctx, &shared.symbol_tables)?;
│   }
├── // Pass 2 across cluster
│   for parsed in &parsed_entries {
│       check_form_body(parsed.clone(), &mut ctx, &shared.symbol_tables)?;
│   }
└── // Returned to caller; insert_cluster drains staging into live atomically.
    return Ok(ProcessedCluster { staging, … });
```

Two properties hold by construction:

1. **Staging is orchestrator-owned.** `process_cluster`'s stack frame owns the `SymbolTable` value. Other workers cannot reach it; no `Arc<RwLock<…>>` is involved; the orchestrator's `&mut` exclusive borrow holds for the cluster's duration.
2. **Staging is transient.** It dissolves with the function frame on any failure (Gap that the scheduler cannot resolve, TypeError, panic) — the live table is unchanged. On success the staging entries are drained into live atomically (per-entry, under the inner `DashMap`'s per-key locks).

This is why the live `SymbolTable` invariant ("if it's in the live table, it's checked AND committed") holds across cluster boundaries: staging is the **only** place a Pass-1 sig-shell or a half-checked Pass-2 entry ever lives, and staging is invisible outside the orchestrator's frame.

---

## 3. `ClusterContext` enum — the dispatch choke point

Per Decision 44 §"`ClusterContext` (Approach B is canonical)", the enum lives in `cranelisp-typecheck`:

```rust
pub enum ClusterContext<'a, C: CodeStore, L: LinkerStore> {
    /// Committed mode. Used outside cluster processing — REPL introspection,
    /// fine-grained drivers, code paths that read live state directly.
    Live {
        modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,
    },
    /// Cluster mode. Used by `int::process_cluster` for the duration of one
    /// cluster's processing.
    Cluster {
        modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,    // cross-module reads
        staging: &'a mut SymbolTable<C, L>,                          // current-module writes
        current_module: ModuleFullPath,
    },
}

impl<'a, C: CodeStore, L: LinkerStore> ClusterContext<'a, C, L> {
    pub fn current_symbol_table(&self) -> View<'_, C, L>;
    pub fn current_symbol_table_mut(&mut self) -> &mut SymbolTable<C, L>;
    pub fn current_module(&self) -> &ModuleFullPath;
}
```

### 3.1 Read dispatch

`current_symbol_table(&self) -> View<'_, C, L>`:

- `Cluster { modules, staging, current_module }` → `View::union(staging, modules.get(current_module).expect("current module exists in live by precondition"))`. Staging-first, live-fallback. The `expect` is sound because Wave 3a-α's registration discipline ensures the current module's live table exists before `process_cluster` constructs `Cluster`; cross-module reads through `modules.get(other)` are the standard shape-2 (FQ) path.
- `Live { modules }` → `View::union(empty, modules.get(current).unwrap())`. The `View` newtype is uniform across both modes — typecheck always receives a `View`. In `Live` mode the staging side is an empty `SymbolTable` (a constant; see §3.4 for the implementation note).

### 3.2 Write dispatch

`current_symbol_table_mut(&mut self) -> &mut SymbolTable<C, L>`:

- `Cluster { staging, .. }` → `staging`. The 91 register-call sites in `program.rs` (e.g., `register_type_def`, `register_trait_decl`, `register_trait_impl`, `register_defn_signature`, `register_mono_entry`) write here. Typecheck does not know it is writing staging.
- `Live { modules }` → the per-module live table from `modules.get_mut(current)`. Used by:
  - REPL append paths that mutate live directly (e.g., `append_defn_order` per Decision 39; called by `int` outside the cluster frame).
  - Any future code path that wants direct live mutation (rare; the cluster frame is the canonical path).

Cross-module writes (e.g., a `(impl Trait Type …)` form whose `Trait` lives in another module per Decision 45 Pattern B) are resolved by the orchestrator selecting the target module BEFORE calling typecheck — `current_module` in the `Cluster` variant is set to the trait's defining module for the impl-write scope, not the writer's source file's module. This is the chain-follow primitive (Principle 17 shape 3) operating at the write side, symmetrical to the read side. **Within one cluster** the `ClusterContext` may need to be reconfigured (or composed) across writes that target different `current_module`s; the orchestrator owns this dispatch.

### 3.3 ClusterContext-per-target-module accommodation

For an impl-write whose trait is in module M but the source form was parsed in module N, the orchestrator has two implementation choices for the `Cluster` variant:

- **(i) One staging table per touched module.** `process_cluster` holds `HashMap<ModuleFullPath, SymbolTable<C, L>>` for staging; the `Cluster` variant carries `&mut staging[current_module]`. Cluster commit drains each staging table into the corresponding live table atomically. Cost: per-touched-module allocation; no clone of live.
- **(ii) Single staging table indexed by `(ModuleFullPath, Symbol)`.** `process_cluster` holds one `HashMap<(ModuleFullPath, Symbol), ModuleEntry<C>>`; `current_symbol_table_mut` returns a thin shim that inserts into this map keyed by current_module. Cost: one `HashMap` insert per write; no per-module allocation.

**Selected: (i).** Choice (i) makes the `current_symbol_table_mut() -> &mut SymbolTable<C, L>` signature continue to return the existing `SymbolTable` type — the 91 register-call sites' inserts are byte-identical. Choice (ii) would require changing the accessor's return type or wrapping `SymbolTable` in a shim, adding API surface and conflicting with Decision 44's "the surgery is on the accessors, not on every call site" intent. The per-touched-module allocation cost is microscopic (impl-writes to a foreign trait's home are O(impl count); the staging tables stay empty for unaffected modules and are dropped on cluster end).

For Wave 3a-β implementation: start with the **typical case** — a cluster touches one module (the file's or REPL input's current module) — using a single `staging: SymbolTable<C, L>` in the orchestrator. When an impl-write to a different module is performed, the orchestrator looks up (or lazily allocates) the staging table for that module and reconfigures the `ClusterContext::Cluster { staging, current_module }` to point at it for the duration of that write. This is one `&mut`-reborrow per cross-module write; lifetimes are friendly because `process_cluster` owns all staging tables in its stack frame.

If the lazy-allocation pattern proves awkward in practice (`/dev` will surface this in Stage 2 implementation feedback), the orchestrator can switch to pre-allocating staging tables for every module mentioned in any of the cluster's parsed entries (cheap; staging tables are empty if untouched). The accessor surface does not change either way.

### 3.4 `Live` mode empty-staging implementation note

`ClusterContext::Live` returns a `View` whose staging side is empty. Two implementations:

- **Sentinel empty `SymbolTable`** — `OnceCell` / `LazyLock` holding `SymbolTable::empty()` shared across all `Live` accesses. `View::union(&EMPTY, live)` reads from live (since `empty.lookup(_) == None` for every key). Allocation: one per process; lifetime: 'static.
- **`View` constructor variant** — `View::single(live)` for `Live` mode; `View::union(staging, live)` for `Cluster` mode. Two named constructors; one internal storage shape. Typecheck calls `view.lookup(name)` either way.

**Selected: `View::single` variant.** Adds one constructor to `View`'s API (already `non_exhaustive`); removes the need for a static sentinel. The implementation cost is identical (a one-of-two read dispatch); the surface is cleaner.

This is a minor `View` API addition. `View::union` stays as defined in `facades/types.md` §"`View`"; `View::single(live: &'a SymbolTable<C, L>) -> Self` is added. **FIXME `target: /arch` proposed in §10** to confirm the addition to `facades/types.md` §"`View`".

---

## 4. `View<'a, C, L>::union(staging, live)` — confirmation

Per `facades/types.md` §"`View`" — `View` lives in `cranelisp-types`. This design doc confirms that placement and adds the `View::single` constructor (§3.4). Properties stand:

- No allocation per lookup; the newtype holds two references.
- Read-only; typecheck reads via `view.lookup(name)` / `view.iter()`.
- Lifetime-bounded by `'a` (the borrow of the underlying tables).
- `#[non_exhaustive]`; `Debug`; not `Clone`; not `Serialize/Deserialize`.

The read dispatch (staging-first, live-fallback) is the contract Pass 2 depends on for **mutual recursion within a cluster**: Pass 1 stages `g`'s signature shell; Pass 2 of `f`'s body reads `g` via `view.lookup` → staging hit → `f` typechecks against `g`'s shell. After Pass 2 of `g`, its body-checked entry supersedes the shell (staging is keyed by `Symbol`, so the body-checked entry overwrites Pass 1's shell on `current_symbol_table_mut().insert(g, body_checked_entry)`). Pass 2 reads of `g` from later forms in the cluster see the body-checked entry, not the shell — which is what Algorithm-W body checking needs for self-referential types in mutually-recursive cliques.

### 4.1 Iteration over the union

`View::iter()` is used by `defined_symbols()`-style passes that need to enumerate the cluster's union. Staging-first; live entries shadowed by staging keys are skipped (i.e., iteration produces each key exactly once). Order is iteration order of the underlying `DashMap`s; not stable across runs. This is sufficient for the typecheck consumers (which use enumeration for cross-validation and side-effect-free traversal); if a stable iteration order is needed elsewhere, the orchestrator composes it at the integration layer.

### 4.2 No View::clone

`View` does not implement `Clone`. The intended construction is at the accessor call site (`ctx.current_symbol_table()` returns a fresh `View`); cloning the borrow has no value. If a consumer wants to thread a `View` through multiple helpers, it passes the `&View` by reference.

---

## 5. Cluster-atomic commit protocol

The protocol stretches across `int::process_cluster` (the orchestrator) and `int::insert_cluster` (the commit step). This design doc binds the **typecheck side** of the contract; the orchestrator side is `facades/int.md` §"`process_cluster`".

### 5.1 Per-pass invariants typecheck guarantees

- **Pass 1 (`check_form_signatures`) writes only signature shells.** Each `ParsedEntry::Defn { name, params, return_type, .. }` becomes a `ModuleEntry::Def { scheme: signature_only_scheme, ast: None, code: None, got_slot: assigned, .. }` in staging. Bodies are NOT checked. `ParsedEntry::TypeDef`, `ParsedEntry::TraitDecl`, `ParsedEntry::TraitImpl` similarly stage shape-only entries (type def + constructors; trait decl + method signatures; impl shell with method names assigned but bodies un-checked).
- **Pass 1 reads via `ctx.current_symbol_table()`.** For each Pass-1 step, the unified View carries previously-staged shells from earlier forms in this cluster (so e.g., the third form's TypeDef can reference the first form's TypeDef by FQ name — though the typical case is no Pass-1-to-Pass-1 dependency).
- **Pass 2 (`check_form_body`) reads the unified View; writes body-checked entries.** Bodies are inferred via Algorithm-W against the `View` that contains all cluster signatures (staged in Pass 1) plus the live table (modules already committed). Mutual recursion within a cluster works because Pass 1 staged all signatures before any Pass 2 ran. Body-checked entries overwrite Pass 1 shells in staging.
- **Pass 2 produces side products on `ParsedEntry`** (in place; or on a `CheckResult`-equivalent map keyed by FQSymbol) — `method_resolutions`, `expr_types`, `callees`, `mono_defns` — that the orchestrator threads into `ModuleEntry::Def` on commit. The exact mechanism (in-place on `ParsedEntry`, or a separate `Vec<FormCheckResult>` returned by reference) is `/dev`-internal; the **public surface** is just `Result<(), CheckError>`. See §5.4 for the in-place mutation note.

### 5.2 Failure modes and atomicity

- **`Err(CheckError::Gap(_))` mid-Pass-1.** Orchestrator catches; dispatches the gap (registers the missing module, waits for typecheck completion); retries the **same form** at Pass 1. Staging may carry partial writes; the retry overwrites. Other cluster forms have not yet been Pass-1-processed; their state is unstaged.
- **`Err(CheckError::Gap(_))` mid-Pass-2.** Orchestrator catches; dispatches; retries the same form at Pass 2. Pass-1 shells of all cluster forms are still in staging (Pass 1 completed across the cluster before Pass 2 began). The retry of Pass 2 sees the same staging it saw on the prior attempt, plus any newly-committed peer module.
- **`Err(CheckError::TypeError(_))` at any point.** Orchestrator does NOT retry. The function frame returns Err; staging dissolves on the frame return; the live table is byte-identical to its pre-cluster state. The orchestrator surfaces the error to the eval loop / CLI.

### 5.3 Commit step (`insert_cluster`)

After Pass 2 completes successfully across all cluster forms, the orchestrator hands the staging table(s) to `int::insert_cluster`, which drains them into the live tables atomically — per-entry, under the inner `DashMap`'s per-key locks. The orchestrator additionally publishes:

- `Introspection.source` entries (Decision 39) for any defn whose source the orchestrator captured at parse time.
- Call-graph edges to `ModuleEntry::Def.callees` (Decision 21) — these flow from Pass 2's `method_resolutions` side product.
- Mono-defn entries — generated as a Pass 2 side product, staged as additional `ModuleEntry::Def` entries, drained in the same commit.

**Atomicity boundary.** "Atomic" here means **structural** — staging-then-drain ensures no half-cluster state is ever visible to other workers. The drain is sequential per-entry; another worker reading mid-drain may see N of the N+M new entries. The drain is sequenced such that **every entry visible in live is a committed entry**, never a Pass-1 shell. This is the live-table invariant (`facades/typecheck.md` invariant 2).

### 5.4 In-place `ParsedEntry` mutation note

`ParsedEntry` derives `Clone` so the orchestrator can retry-on-Gap. If Pass 2 in-place-mutates the `ParsedEntry` to attach `method_resolutions` / `expr_types`, the retry's clone-then-replace pattern means the retry starts from a fresh `ParsedEntry`. **This is correct** — the retry should not see partial Pass-2 work from the previous attempt; the retry re-derives the body annotations from scratch against the (now-resolved) View.

Practical implementation: `check_form_body` may either mutate `parsed` in place (since it takes by-value, the orchestrator's cloned copy is the local) and return the mutated value back through a `&mut` channel — OR the orchestrator owns a `Vec<FormCheckResult>` parallel to `parsed_entries` and `check_form_body` accumulates into that. The latter is cleaner because `ParsedEntry` is meant to be parse-time-only (per `facades/types.md` §"`ParsedEntry`"). **Selected: parallel `Vec<FormCheckResult>` accumulated by the orchestrator, written through a `&mut Vec<…>` parameter or a per-form return.** This conflicts mildly with the `Result<(), CheckError>` return shape per §1.3 — see open question Q1 in §10.

---

## 6. Begin-cluster forms — feeding multiple `ParsedEntry` values

Per `facades/types.md` §"`ParsedEntry`" + `facades/int.md` §"`process_cluster`":

```text
REPL input "(begin (defn f [] (g 1)) (defn g [x] x))"
↓ frontend::parse → Sexp
↓ frontend::expand (no macros to expand) → Sexp
↓ frontend::build_form per `begin` cluster → Vec<ParsedEntry> = [
    ParsedEntry::Defn { name: "f", … },
    ParsedEntry::Defn { name: "g", … },
  ]
↓ orchestrator: Pass 1 sweep across the Vec, then Pass 2 sweep across the Vec.
```

The `Vec<ParsedEntry>` is the orchestrator's per-cluster collection. The typecheck surface processes **one `ParsedEntry` at a time**; the orchestrator drives the sweep. This is the same shape `check-form-api.md` Invariants 1 + 4 describe (all signatures before all bodies; generalisation after all bodies); the Wave 3a-β refinement is:

- **The orchestrator's sweep replaces the in-typecheck `check()` orchestrator** that `check-form-api.md` retains as a back-compat wrapper. Wave 3a-β removes the in-typecheck whole-program loop entirely; only per-form passes remain. The duplicate `check_program*` / `check_repl_input*` paths flagged by audit Finding 1 are deleted as part of this wave.
- **`ModuleCheckAccumulator` becomes orchestrator-side, not typecheck-side.** Its fields (`method_resolutions`, `expr_types`, `constrained_fn_names`, `mono_defns`, `default_method_defns`, `multi_sig_defns`, `warnings`, `defn_type_vars`, `call_graph_edges`) live in `int`'s `process_cluster` stack frame (or in a return-type wrapper `ProcessedCluster` per `facades/int.md`). Typecheck mutates pieces of it via `&mut` reference (or `int` collects them per-form via the staging table — bodies' `Scheme` carry `defn_type_vars` already; `method_resolutions` need a per-form side channel).
- **`CheckState` remains typecheck-side**, per-call transient. The orchestrator constructs one `CheckState` per cluster (Pass 1 + Pass 2 share it; `CheckState` carries the type-var pool, substitution, deferred resolutions). On a cluster failure, the `CheckState` dissolves with the function frame; on success, the `ReplSnapshot` primitive provides rollback at REPL boundaries (Decision 44 §"Bounded-context invariants" item 7).

### 6.1 Single-form clusters

A non-`begin` REPL input is a one-form cluster (per Decision 44 + `/spec` FIXME 0165). The orchestrator's sweep is degenerate (one Pass-1 call, one Pass-2 call); the same code path serves single-form and multi-form clusters — Principle 11.

### 6.2 Batch (file) clusters

A file's non-structural forms are one big cluster (per spec §5.13.1's MAY-reference-freely rule at file scope). The orchestrator drives Pass 1 across every form in the file, then Pass 2 across every form in the file, then commits. Forward references across the file work via the same Pass-1-stages-shells, Pass-2-reads-the-union mechanism; the cluster boundary is the whole file.

### 6.3 Cross-input forward refs are an error (negative)

Without `(begin)`, a REPL forward reference like `(defn f [] (g 1))` followed on a separate input by `(defn g [x] x)` does not typecheck — `g` is not in staging (single-form cluster), not in live (not yet defined). Pass 2 raises `CheckError::TypeError { message: "undefined symbol: g", … }` (NOT a Gap — Gap is only raised for FQ refs to other modules; bare `g` is a current-module short-name that genuinely doesn't exist). The orchestrator drops staging; `f` does not commit; the user sees a clear error. This is the **negative path** tested by `process_form_dispatch_function_gap_does_not_speculatively_jit`.

---

## 7. Facade-compliance delta — `public-api.txt` changes

Comparing `crates/cranelisp-typecheck/public-api.txt` (as-built) to `design/arch/facades/typecheck.md` §"Public surface (as-designed)":

### 7.1 Additions

- **`pub fn check_form_signatures<C, L>(parsed: ParsedEntry, ctx: &mut ClusterContext<'_, C, L>, symbol_tables: &SymbolTables<C, L>) -> Result<(), CheckError>`** — the Pass 1 free function. Not present in current public-api.txt.
- **`pub fn check_form_body<C, L>(parsed: ParsedEntry, ctx: &mut ClusterContext<'_, C, L>, symbol_tables: &SymbolTables<C, L>) -> Result<(), CheckError>`** — the Pass 2 free function. Not present.
- **`pub enum ClusterContext<'a, C: CodeStore, L: LinkerStore>`** with variants `Live { modules }` and `Cluster { modules, staging, current_module }`. Not present.
- **`pub fn ClusterContext::current_symbol_table(&self) -> View<'_, C, L>`** and **`pub fn ClusterContext::current_symbol_table_mut(&mut self) -> &mut SymbolTable<C, L>`**. Not present.

### 7.2 Removals (existing items the wave deletes)

- **`pub fn TypeCheckEnv::check(…)`** (current public-api.txt L207). The whole-program entry deprecated; replaced by the orchestrator-driven per-form sweep. Removed.
- **`pub fn TypeCheckEnv::check_program(…)`** (L209) and **`pub fn TypeCheckEnv::check_repl_input(…)`** (L210). Duplicate pipelines per audit Finding 1; removed as Wave 3a-β prerequisite (audit remediation #1).
- **`pub fn TypeCheckEnv::check_form(_module, form, pass, &mut state, &mut accumulator) -> Result<FormCheckResult, CranelispError>`** (L208). Method form replaced by the two free functions; removed.
- **`pub enum CheckPass`** (L50–L68) — `Register`/`CheckBody`. The pass discriminator becomes implicit in which free function is called; `CheckPass` is no longer needed as a public enum. **Considered: keep as `#[non_exhaustive] pub enum` per facade §"Per-form-pass scaffolding"** for the test/fine-grained-caller use case. **Selected: remove.** The facade documents `CheckPass` as available for finer-grained callers, but the two free functions are themselves the finer-grained shape — the discriminator is redundant once the dispatch is by function. Doc-clarity FIXME proposed in §10 to reconcile the facade.
- **`pub struct FormCheckResult`** (L115–L132). Removed as a public type (its fields' destinations are: AST annotations via `method_resolutions` → ModuleEntry / Introspection; `constrained_fn` → trait registry flag on Def; `mono_defns` → ModuleEntry::Def with mangled names staged; `default_method_defns` / `multi_sig_defns` → additional `ParsedEntry`s the orchestrator threads through both passes; `warnings` → orchestrator-collected; `call_graph_edges` → ModuleEntry::Def.callees per Decision 21). If `/dev` finds a Stage-2 need for `FormCheckResult` as an internal-but-public type (e.g., the parallel `Vec<FormCheckResult>` per §5.4), it stays as a `#[non_exhaustive]` public type and the facade is amended.

### 7.3 Modifications

- **`pub fn register_builtins<C, L>(modules: &DashMap<…>, next_id: &AtomicU32)`** (L5, L225) — current signature takes the universe-scoped `modules` + a type-var allocator. Facade calls for `register_builtins(&mut SymbolTable<Code, ()>)` (one table). The pivot to one-table is **deferred to a later wave** (per facade §2.1 drift register row; tracked by FIXME 0008's free-function migration). Wave 3a-β does NOT pivot this signature — it remains a separate wave. The current signature is preserved in public-api.txt; the facade's target signature is the eventual destination.
- **`pub struct TypeCheckEnv<'a, C, L>`** (L170–) — retains its non-table state (type-var pool, deferred resolutions, side-map snapshots) but loses its `modules: &'a DashMap<…>` field (replaced by `&mut ClusterContext<'_, C, L>` parameters on the methods that need table access). Many methods on `TypeCheckEnv` become `pub(crate)` because their callers are now the two free functions inside the crate, not external code. The `#[non_exhaustive] pub struct TypeCheckEnv` shell stays for advanced/test callers per facade §"Per-form-pass scaffolding", but its surface shrinks.
- **`pub struct CheckState`** (L104) — unchanged. Per-call transient; carries `current_module`, type-var pool, deferred resolutions. The `pub fn new(module: ModuleFullPath) -> Self` constructor stays.

### 7.4 Types crate (cranelisp-types) changes

Per `facades/types.md`, the boundary types this wave depends on are already in `cranelisp-types`: `ParsedEntry`, `View`, `ResolutionGap`, `SymbolTable`, `ModuleEntry`. Additions this wave proposes:

- **`View::single(live)` constructor.** §3.4. FIXME `target: /arch` proposed in §10 to extend `facades/types.md` §"`View`".

No removals from `cranelisp-types`. The single-consumer types (`CheckError`, `CheckState`, `TypeCheckEnv`, `ClusterContext`, etc.) live in `cranelisp-typecheck` per Principle 15.

### 7.5 Net public-api.txt delta

Roughly:
- 4 additions (`check_form_signatures`, `check_form_body`, `ClusterContext` enum + 2 method impls, `View::single` upstream in types).
- 7 removals (`check`, `check_program`, `check_repl_input`, `check_form` method, `CheckPass` enum + impls, `FormCheckResult` struct + impls, eventually `ModuleCheckAccumulator` if it migrates to int).
- ~6 modifications (`TypeCheckEnv`'s method surface shrinks; `register_builtins` signature unchanged this wave).

The net result aligns the as-built surface with the facade — the drift register §2.1 in `typecheck.md` master design closes by ~80% on this wave (the remaining 20% is `register_builtins` + a handful of `pub use` cleanups deferred to FIXME 0100 / FIXME 0098 follow-ups).

---

## 8. Analysis — the 4 `stdlib_trait_impls` failures (P17 short-name follow-up)

The four failures share a single shape:

```
(show 42)                              → undefined variable: show
(show 3.14)                            → undefined variable: show
(let [f =] (f "hi" "hi"))              → undefined variable: =     (mappable path)
(let [f not] (f true))                 → undefined variable: not
```

Trait methods (`show`, `=`, `not`) are not resolving when used **bare** in user code. The interaction is between **Principle 17** (short-name resolution is current-module-only; no fallback) and the **trait-method resolution path** (which historically scanned for impls across modules).

### 8.1 Root cause

A trait method `show` is conceptually defined in the trait's defining module (e.g., `core/Display.show`) and reaches user code via the **prelude's per-symbol Import bindings** (spec §8.8.1). Under Principle 17:

> A short name `foo` resolves by lookup in the **current module's `SymbolTable` only**. … Universally-feeling symbols (`Int`, `+`, `not`) are reachable because the **prelude** (spec §8.8.1) injects per-symbol `ModuleEntry::Import` bindings into user modules.

For `(show 42)` to typecheck under P17, the user module's `SymbolTable` must contain a `ModuleEntry::Import { source: FQSymbol { module: "core/Display", symbol: "show" }, … }` entry placed there by the prelude. The current source's failure to resolve `show` indicates **the prelude is not injecting that Import binding** for trait methods — either because (a) the prelude file doesn't `(export [show])` the trait method, (b) the prelude does export but the user-mode import pass doesn't inject per-method bindings, or (c) the trait method lives in a synthetic module whose import discipline is different.

For `not`, FIXME 0150 explicitly flags that `not` has only the inline backend path (`backend/operators.rs:64`) and no symbol-table entry. This is a **distinct sub-issue**: `not` is a primitive, not a trait method, and it has no Def entry in the `primitives` synthetic module — so even with a prelude that imports `not` from `primitives`, the source FQ would resolve to a `ModuleEntry::Import` whose `source.module = "primitives"` and `source.symbol = "not"`, but probing `primitives.get("not")` returns `None`. The Import binding is a dangling reference.

For `=` (mappable path), `let [f =]` forces `=` to be resolved as a **value** (not a call site). The trait-method resolution path that handles `(= a b)` as a call goes through `try_resolve_trait_method`; the mappable path needs `=` to resolve as a `Symbol` to a `ModuleEntry::Def` (the trait-method binding). If trait methods don't have per-method `ModuleEntry::Def` entries (and instead are only reachable through the trait dispatch machinery on call sites), the mappable path has no entry to capture into a GOT slot.

### 8.2 Disposition

These are **NOT Wave 3a-β cluster-atomic concerns.** They are P17 short-name follow-up issues bounded to:

- Bootstrap-time registration of trait-method `ModuleEntry::Def` entries (or `ModuleEntry::Import` bindings) in the trait's defining module and the prelude's destination modules — the FIXME 0172 territory.
- D43 Phase 4 stdlib trait-impl audit — `(show 42)` and `(let [f =] …)` are the highest-risk reshapes per the slice §2.3 (per `tests/CLAUDE.md`).
- Primitive `not` seeding — FIXME 0150 names this directly; `not` needs a `primitives/not` `ModuleEntry::Def` to support the mappable path; a backend-only intrinsic without a typecheck-side Def is exactly the pre-D43 shape that the D43 split + Principle 17 are supposed to retire.

Wave 3a-β's cluster-atomic shape pivot does NOT touch these resolution paths; it touches the **per-form dispatch surface and the staging accessor**. Once Wave 3a-β lands, the four failing tests should still fail with the same `undefined variable: …` message — the cluster-atomic surgery doesn't add or remove any prelude/primitive registration.

### 8.3 Proposed handoff

- **`stdlib_not_*` (2 tests)** → FIXME 0150 Phase 4. The `not` primitive needs a `primitives/not` `ModuleEntry::Def` seeded by `register_builtins` (or by `cranelisp-primitives` post-D43 split). This is a primitives-crate concern, not a typecheck concern.
- **`stdlib_display_*` (2 tests)** → FIXME 0150 Phase 3 + 4. The `Display.show` trait needs to be defined (today it lives in `stdlib/`, not `primitives/`), and the prelude must inject `show` as a per-method `ModuleEntry::Import { source: core_display_fqsym, … }` into user-mode. Cross-touches `/stdlib` (the trait declaration) + `/typecheck` (per-method registration discipline at impl time) + `/int` (prelude-loading import discipline).
- **`stdlib_eq_string_mappable_path`** → same as Display: trait method needs per-method symbol-table entries reachable via prelude Import bindings. The mappable path is the diagnostic — it exercises whether a trait method has a value-side representation, not just a call-site representation.

**Recommend:** file a new FIXME `target: /typecheck` (or amend FIXME 0172) tracking "trait-method short-name resolution under P17 — per-method `ModuleEntry::Import` bindings via prelude". Wave 3a-β proceeds independently; these 4 tests fail until the FIXME resolves.

### 8.4 Why this is NOT a "design the resolution differently" call

The four failures look like a P17 violation in disguise — "trait methods should resolve via some magic global lookup". They are not. The design IS:

- Trait method `Display.show` lives canonically in `Display`'s defining module.
- Per-method `ModuleEntry::Def` entries (with `trait_origin: Some(FQTraitName)` per checker.rs:1492) live in that defining module.
- User modules reach `show` via prelude-injected per-method `ModuleEntry::Import` bindings.
- Call-site resolution `(show x)` goes through the import binding → chain-follow to home → Def's scheme → instantiate → resolve impl via Principle 17 shape 3 (chain-follow trait reference + probe trait's home for `impl$FQTypeName$FQTraitName`).
- Mappable resolution `(let [f show] f)` goes through the import binding → chain-follow to home → Def → return the Def's `code` pointer (for GOT capture).

What's missing is the **per-method Import injection in user-mode prelude loading**. The design is right; the implementation hasn't completed the prelude-injection step for trait methods. This is the FIXME 0172 + FIXME 0150 territory, not a Wave 3a-β architectural call.

---

## 9. Sequencing and dependencies

Wave 3a-β depends on:

1. **Wave 3a-α landed** (Decision 46). The 40+ `self.modules.X` access sites replaced; chain-follow primitive in place; cross-module impl writes targeting trait's home; synthetic glob imports removed. This is the precondition — without it, the `ClusterContext::current_symbol_table_mut()` surgery doesn't deliver atomicity because orphaned pierces bypass the accessor.
2. **`ParsedEntry` enum landed in `cranelisp-types`** (FIXME 0156). Frontend's `build_form` returns `Vec<ParsedEntry>`.
3. **`ResolutionGap` + `CheckError` landed in `cranelisp-types`** (FIXME 0098 Phase 1). Typed gap returns; typed type errors.
4. **`View` newtype landed in `cranelisp-types`** (this design's §4 + §3.4 `View::single` extension).

Wave 3a-β does NOT depend on:

- Audit remediation #1 (`check_program*` / `check_repl_input*` consolidation). Wave 3a-β subsumes it — these duplicate paths are deleted as part of removing the in-typecheck whole-program loop.
- FIXME 0150 / FIXME 0172 (the trait-method short-name resolution). Independent track; the 4 `stdlib_trait_impls` failures stay failing through Wave 3a-β.
- `register_builtins` signature pivot (drift register §2.1 row). Deferred wave.

---

## 10. Open questions / proposed FIXMEs

### Q1 — `Result<(), CheckError>` vs `Result<FormCheckResult, CheckError>`

**Issue.** §5.4 noted that Pass 2 produces side products (`method_resolutions`, `expr_types`, `mono_defns`) that the orchestrator needs. The facade pins `Result<(), CheckError>`. Implementation choices:
- (a) `&mut FormCheckResult` parameter on `check_form_body` — accumulator passed by reference; pass writes into it; return stays `Result<(), CheckError>`. Public API surface increases by one type.
- (b) Mutate `ParsedEntry` in place (annotate fields like `parsed.expr_types = …`). Conflicts with `ParsedEntry`'s parse-time-only intent; messy semantic overload.
- (c) Side products land in staging entries themselves (each `ModuleEntry::Def` accumulates `method_resolutions` / `expr_types` / `callees` / mono entries during Pass 2). Requires fattening `ModuleEntry::Def` with annotation-stage fields that backend then consumes.
- (d) Return `Result<FormCheckResult, CheckError>` after all — facade revision.

**Proposal.** (c) is the cleanest because side products belong on the symbol-table entry anyway (call-graph edges → `Def.callees` per Decision 21; expr types → AST annotations on `Def.ast`; mono entries → additional `Def` entries staged). `ModuleEntry::Def` already carries these fields (per Decision 39); writing them during Pass 2 is just filling them in. Staging holds the entries; commit drains them with their annotations intact. No new public types; no `ParsedEntry` mutation; no facade revision. **FIXME `target: /arch`** to confirm (c) is the intended approach (§5.4 — "in-place `ParsedEntry` mutation note") and the facade `Result<(), CheckError>` shape is durable.

### Q2 — `View::single` addition to `cranelisp-types`

**Issue.** §3.4 selected `View::single(live)` as the `Live`-mode constructor. The facade `facades/types.md` §"`View`" pins `View::union(staging, live)` only. **FIXME `target: /arch`** to extend the facade to include `View::single`, OR to confirm that `Live` mode uses `View::union(&EMPTY, live)` with a `static EMPTY: SymbolTable<C, L>` sentinel. The choice is cosmetic-ish but affects `cranelisp-types`'s API surface.

### Q3 — Multi-target-module staging accommodation

**Issue.** §3.3 selected (i) "one staging table per touched module" with lazy allocation. The orchestrator reconfigures the `ClusterContext::Cluster { staging, current_module }` per write-target. The `&mut`-reborrow pattern may be awkward in practice; alternatives include pre-allocating staging for every module the cluster references, or using a `HashMap<ModuleFullPath, SymbolTable<C, L>>` inside the orchestrator with a per-write lookup. **FIXME `target: /int`** to confirm the orchestrator-side ergonomics during Stage 2 implementation feedback.

### Q4 — `CheckPass` enum disposition

**Issue.** §7.2 selected to remove `CheckPass` from the public API (the two free functions are the dispatch). The facade `facades/typecheck.md` §"Per-form-pass scaffolding" still lists `pub enum CheckPass { Pass1Signatures, Pass2Bodies }` as exposed. **FIXME `target: /arch`** to reconcile: either remove `CheckPass` from the facade, or keep it as a public enum used for tests/diagnostics.

### Q5 — `ModuleCheckAccumulator` relocation

**Issue.** §6 noted that `ModuleCheckAccumulator` migrates to `int` (orchestrator-side). Currently it's a `pub struct` in `cranelisp-typecheck`. The relocation removes it from `cranelisp-typecheck::*` per Principle 15 (single-consumer types live with the consumer). **FIXME `target: /int`** if accepted; this is a follow-up wave concern, not Wave-3a-β-critical.

### Q6 — Trait-method short-name resolution under P17 (the 4 stdlib failures)

**Issue.** §8. The four `stdlib_trait_impls` failures need per-method `ModuleEntry::Import` injection in user-mode prelude loading. **FIXME `target: /int`** (or amend FIXME 0172) to track the prelude-injection completion. Out of scope for Wave 3a-β.

---

## 11. Test acceptance

Wave 3a-β closes when:

1. `tests/process_form_dispatch.rs::process_form_dispatch_begin_cluster_resolves_mutual_forward_ref` passes — `(begin (defn f [] (g 1)) (defn g [x] x))` typechecks atomically; `(f)` evaluates to 1.
2. `tests/process_form_dispatch.rs::process_form_dispatch_function_gap_does_not_speculatively_jit` passes — bare cross-input forward ref produces a clear `undefined variable` error; staging is dropped; live is unchanged; no `JitWrite` event from the speculative path (`CRANELISP_GOT_TRACE=1`).
3. `tests/process_form_dispatch.rs::process_form_dispatch_macro_after_import_succeeds_in_one_eval` passes — `(import [helper [my-double]]) (my-double 21)` in one REPL eval produces `:primitives/Int 42`.

The four `stdlib_trait_impls` failures (§8) remain failing through Wave 3a-β; their resolution is tracked separately.

---

## 12. Quality attributes assessment

Per `/design` skill workflow §"Quality attributes":

| Attribute | This wave's impact |
|---|---|
| Simplicity | Removes duplicate `check_program*` / `check_repl_input*` paths (audit Finding 1). One pipeline; explicit Pass 1 / Pass 2 free functions; staging accessor as single mutation surface. Net complexity reduction. |
| Maintainability | The 91 register-call sites in `program.rs` don't change individually — the surgery is at the accessor. Future field additions to `ModuleEntry::Def` continue to flow through `register_*` helpers. Drift register §2.1 closes by ~80%. |
| Observability | No new trace hooks; existing `trace.rs` surface unchanged. `CheckError::TypeError` carries `ErrorLocation` per Decision 39 (already in place). |
| Concurrency-safety | Cluster-atomic invariant holds by construction: staging is orchestrator-local; live commits are per-entry under inner DashMap locks; the live table invariant ("if it's in the live table, it's checked AND committed") holds across cluster boundaries. |
| Performance | No performance impact intended. Staging is a small per-cluster `SymbolTable` (most clusters have ≤ 10 entries); allocation cost is negligible compared to inference cost. The `View::union` is two-ref dispatch; no allocation per lookup. |
| Testability | Pass-1 / Pass-2 separation aids per-pass unit testing. The free-function shape with explicit `&mut ClusterContext` makes constructing test contexts straightforward (`ClusterContext::Cluster { … }` with a hand-built staging table is a valid test driver). |

This wave touches concurrency-safety (cluster atomicity) and simplicity (duplicate-path removal) materially; the other attributes are preserved without active stewardship.

---

## 13. Cross-references

- `design/typecheck/typecheck.md` §§2, 5, 6 — master design; this doc refines §6 (mutation discipline) for Wave 3a-β.
- `design/typecheck/implementation-slice-s66.md` §1.B + §1.C — wave delta tables for α and β; this doc is the β design.
- `design/arch/facades/typecheck.md` §"Public surface" + §"Bounded-context invariants" — the as-designed surface this doc binds.
- `design/arch/facades/int.md` §"`process_cluster`" — orchestrator-side contract.
- `design/arch/facades/types.md` §"`ParsedEntry`" + §"`View`" — boundary types consumed.
- `design/arch/decisions/0044-cluster-atomic-typecheck-orchestrator-staging.md` (amended FIXME 0167) — the cluster-atomic Decision.
- `design/arch/decisions/0045-traitimpl-storage-in-trait-defining-module.md` — Pattern B; chain-follow.
- `design/arch/decisions/0046-wave3a-locality-refactor-precedes-triad.md` — α/β split.
- `design/arch/principles/17-module-locality-in-typecheck.md` — the four access-pattern shapes.
- `design/arch/fixmes/0098-*.md` — `CheckError` / `ResolutionGap` migration.
- `design/arch/fixmes/0156-*` — `ParsedEntry` introduction (frontend `build_form`).
- `design/arch/fixmes/0167-*` (resolved into Decision 44 amendment) — Approach B + ClusterContext.
- `design/arch/fixmes/0172-eliminate-short-name-fallback-chains-in-typecheck-bootstrap.md` — P17 short-name follow-up; intersects with §8.
- `design/arch/fixmes/0150-*` — D43 runtime split; intersects with §8 (`not` primitive seeding; trait-method per-method entries).
- `tests/process_form_dispatch.rs` — Wave 3a-β acceptance gate.
- `tests/stdlib_trait_impls.rs` — the 4 failures analysed in §8.
- `design/typecheck/check-form-api.md` — superseded for the entry shape; algorithm content survives where reproduced here.
