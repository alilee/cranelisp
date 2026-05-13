---
number: 0044
title: Cluster-atomic typecheck via orchestrator-owned staging + ClusterContext; single `check_forms` facade
status: pre-implementation
filed: sprint 66 (Phase 5 Wave 3a structural-finding resolution)
amended: sprint 66 Phase 3 (FIXME 0167 — Approach B; staging mutation via `current_symbol_table_mut` accessor; ClusterContext introduction; invariant 2 revision; pass return type changes to `Result<(), CheckError>`); sprint 66 Phase 3 (FIXME 0168 — Sequencing α/β split; Wave 3a-α locality-correctness refactor precedes Wave 3a-β triad re-fire — see Decision 0046); 2026-05-13 (state-threading resolution — two-pass split collapsed into single `check_forms` function; Pass-1-to-Pass-2 working state internalised; state-threading hole closed by construction)
canonical_location: design/arch/facades/typecheck.md §"check_forms — cluster check"; design/arch/facades/int.md §"process_cluster — the cluster-atomic orchestration loop"; design/arch/facades/types.md §"`ParsedEntry`" + §"`View`"; design/arch/sequences/exec-flow-compilation.mmd, exec-flow-repl.mmd, concurrency-symbol-table-entry.mmd
amends: []
amended_by: []
retracts: []
reframes: [0038]
filed_by_fixme: 0166
amended_by_fixme: 0167, 0168
---

# 0044 — Cluster-atomic typecheck via orchestrator-owned staging + two pure passes

## Statement

> **2026-05-13 third amendment — single `check_forms` facade (state-threading resolution).** The two-pass facade split (`check_form_signatures` + `check_form_body`) below is **superseded** by a single free function `cranelisp_typecheck::check_forms`. The two-pass discipline (Pass 1 signatures, Pass 2 bodies — spec §5.13.1) is preserved as an implementation-phase ordering inside `check_forms`; it does not cross the facade. Pass-1-to-Pass-2 working state lives inside that one stack frame, dropped when the call returns. The state-threading hole (FIXME 0177 — `defn_type_vars`, default-method-defn deferrals, etc. could not survive across two separate free-function calls without a public accumulator) is closed by construction: no working state crosses the facade because there is only one call. `ClusterContext`, the staging-vs-live accessor, `&mut ctx` threading, the 91-register-call-site preservation, whole-cluster atomic commit, and every other structural commitment below remain. What changes: a single canonical signature, and the retirement of `ModuleCheckAccumulator` from public-API consideration (neither typecheck-side nor `int`-side — see facades for the new shape). The orchestrator retries the whole `check_forms` call on `Err(Gap)` (no per-form retry granularity, because there is no per-form facade call). Canonical surface:
>
> ```rust
> pub fn check_forms<C, L>(
>     parsed: Vec<ParsedEntry>,
>     ctx: &mut ClusterContext<'_, C, L>,
>     symbol_tables: &SymbolTables<C, L>,
> ) -> Result<(), CheckError>;
> ```
>
> The rest of this Statement and the body that follows describe the pre-amendment two-pass facade shape; read it as illustrative of the cluster-atomic protocol's intent (the protocol carries forward verbatim), not as the canonical surface. The canonical facade is `facades/typecheck.md` §"check_forms".

`cranelisp_typecheck::check_form` (the single per-form pure call introduced by FIXME 0160) splits into two passes that the orchestrator drives across every form in a cluster:

```rust
pub fn check_form_signatures<C, L>(
    parsed: ParsedEntry,
    ctx: &mut ClusterContext<'_, C, L>,
    symbol_tables: &SymbolTables<C, L>,
) -> Result<(), CheckError>;

pub fn check_form_body<C, L>(
    parsed: ParsedEntry,
    ctx: &mut ClusterContext<'_, C, L>,
    symbol_tables: &SymbolTables<C, L>,
) -> Result<(), CheckError>;
```

Both passes are **pure with respect to live state**: neither mutates the live `SymbolTable` nor any state visible outside the cluster. Both passes MAY mutate the orchestrator-handed staging `SymbolTable` via the same accessor API used in committed-mode (`ctx.current_symbol_table_mut()`); typecheck cannot distinguish staging from live because the accessor abstracts the difference. Pass 1 stages signature-only `ModuleEntry` shells (Algorithm W fresh return-type variables); Pass 2 body-checks against the unified (staging ∪ live) view with all cluster signatures visible, staging body-checked entries that supersede Pass 1's shells.

The orchestrator (`int::process_cluster`) constructs a `ClusterContext::Cluster { modules, staging, current_module }` for the duration of one cluster's processing, with `staging` an empty per-cluster `SymbolTable`. It runs Pass 1 across every form, then Pass 2 across every form, then commits the staging table atomically into the live `SymbolTable` on success — drained per-entry under inner-DashMap locks. Any `Err` from either pass drops the staging table on the floor when the function frame returns; the live table is unchanged.

`ClusterContext` is the choke point that preserves Decision 44's structural intent: cluster atomicity is preserved because staging is orchestrator-local and is committed (drained into live) only on Pass-2 success across all forms. The 91 register-call sites and 51 access sites in `crates/cranelisp-typecheck/src/program.rs` do **not** change individually — they continue to flow through the `current_symbol_table` / `current_symbol_table_mut` accessors. The surgery is on the accessors themselves, not on every call site.

A `View<'a, C, L>` is the read-side abstraction: a thin newtype on `cranelisp-types` that holds two `&SymbolTable` references (staging + live) and routes lookups (staging-first, then live). `View` is constructed inside `ClusterContext::current_symbol_table()` for cluster mode; in committed (`Live`) mode the same method returns a single-source view. Typecheck reads `ctx.current_symbol_table()` whenever it would have read `&SymbolTable` directly; it cannot tell whether the view unions staging+live or hits live alone.

**Cluster boundaries**:

- A REPL input is a one-form cluster (per the parallel `/spec` resolution of FIXME 0165 — non-`begin`-grouped REPL inputs are processed as single-form clusters; cross-input forward references are NOT supported).
- A `(begin form₁ ... formN)` REPL input is the explicit multi-form cluster boundary — the orchestrator unwraps and processes the whole list as one cluster.
- Batch (file) compilation is one big cluster covering the file's non-structural forms (per spec §5.13.1's MAY-reference-freely rule at file scope).

## `ClusterContext` (Approach B is canonical)

A new enum in `cranelisp-typecheck` (replaces the prior `TypeCheckEnv` `modules: &DashMap<...>` field; existing `TypeCheckEnv` retains its other state and acquires a `&mut ClusterContext` for table access):

```rust
pub enum ClusterContext<'a, C: CodeStore, L: LinkerStore> {
    /// Committed mode. Used outside cluster processing — REPL introspection,
    /// fine-grained drivers, code paths that read live state without staging.
    Live {
        modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,
    },
    /// Cluster mode. Used by `int::process_cluster` for the duration of one
    /// cluster's processing. `staging` is orchestrator-owned, transient,
    /// `&mut`-borrowed for the life of the cluster; cross-module reads still
    /// route through `modules` (live, shared-read).
    Cluster {
        modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,    // for cross-module reads
        staging: &'a mut SymbolTable<C, L>,                          // current-module writes go here
        current_module: ModuleFullPath,
    },
}

impl<'a, C: CodeStore, L: LinkerStore> ClusterContext<'a, C, L> {
    /// Read access. In `Cluster` mode returns `View::union(staging, live)`
    /// (staging shadows live for the current module); in `Live` mode returns
    /// a single-source view.
    pub fn current_symbol_table(&self) -> View<'_, C, L>;

    /// Write access. In `Cluster` mode returns `&mut staging`; in `Live` mode
    /// returns the per-module live table (used by REPL append paths and the
    /// rare code path that wants direct live mutation).
    pub fn current_symbol_table_mut(&mut self) -> &mut SymbolTable<C, L>;
}
```

The two accessors are the **single point of surgery**. The 91 register-call sites in `crates/cranelisp-typecheck/src/program.rs` (e.g., `register_type_def`, `register_trait_decl`, `register_trait_impl`, `register_defn_signature`, `register_mono_entry`) and the 51 read access sites all flow through these methods unchanged. The accessors absorb the staging-vs-live distinction; typecheck cannot observe which mode it is in.

**Approach B is canonical** for cranelisp because cluster writes are typically purely additive (define new fns / types / impls). Modifying existing live entries during a cluster is rare and is its own code path (redefinition semantics — handled outside the cluster's pure-staging frame). At cluster start the orchestrator allocates an empty `SymbolTable` for `staging`; reads via `View::union(staging, live)`; writes go directly to staging; commit drains staging entries into live. Cost: zero clone per cluster.

**Approach A** (clone live into staging at cluster start; commit replaces live entry; cost: O(N) clone per cluster) is reserved for hypothetical future need only — if a workload surfaces in which staging needs initial-equal-to-live semantics (e.g., a redefinition cluster that mutates pre-existing entries), the same `ClusterContext` shape can be reconfigured to populate staging from a clone at construction. The accessor API does not change between the two realisations; only the orchestrator-side construction differs. The current sprint locks B as the implementation; A is a forward door, not a planned step.

## Rationale

The pre-S66 `check_form` was a single in-place mutator; FIXME 0160 purified it to a single-call pure function returning entries-to-insert, with the caller committing on `Ok`. Wave 3a's first contact with implementation surfaced a structural conflict: spec §5.13.1 mandates a two-pass typecheck (Pass 1 Registration; Pass 2 Checking) to support forward references / mutual recursion at top level. A single per-form pure `check_form` cannot satisfy this — when checking `(defn f [] (g 1))`'s body, `g`'s signature must already be in scope, but a per-form caller has no opportunity to register `g`'s signature first.

The cluster-atomic shape resolves the conflict without compromising purity:

- **Typecheck stays pure** (Principle 1 — Decoupling). Both passes return entries; neither mutates a `SymbolTable`. Typecheck does not know whether it is reading staging, live, or a unioned view.
- **Live `SymbolTable` invariant restored** (Principle 7 — Single source of truth). The pre-S66 invariant — "if it's in the live table, it's checked AND committed" — is restored. Staging is a separate, orchestrator-local, transient table that is never globally visible. There is no second authoritative store; staging dissolves on cluster commit (entries move to live) or on any failure (drops on the floor).
- **Cluster-atomic commit**. A failure mid-cluster leaves the live table byte-identical to its pre-cluster state. Mutual recursion / forward references work via Pass 1 sig-registration into staging followed by Pass 2 body-check that sees all cluster signatures.
- **Single REPL form is one-form cluster**; batch is one-big-cluster. The same `process_cluster` code path serves both — Principle 11 (Single pipeline mode parameters): a uniform pipeline parameterised by the orchestrator's cluster construction.
- **Spec coupling explicit**. `(begin ...)` gains a normative role as the REPL atomicity primitive — handled by the spec twin (FIXME 0165 → `/spec` extension of §5.13.2). The architectural commitment is: clusters are the unit of typecheck atomicity; the spec defines what counts as a cluster.

### Rejected alternatives

> **2026-05-13 third-amendment note.** The "single function with a `Pass` enum parameter" rejection below remains valid for that specific shape (run-time pass discriminator passed by the consumer). The third amendment's single `check_forms` function is **different**: it consumes the whole cluster (`Vec<ParsedEntry>`) and runs both passes internally — the consumer never passes a pass discriminator. The narrow-interfaces concern that justified rejecting the enum-parameter approach (every consumer has to dispatch on `Pass`) does not apply to `check_forms` (consumers see one entry, one return). The two-function split was reaction against the enum-parameter shape but over-corrected — it exposed implementation phasing across the facade and created the FIXME-0177 state-threading hole. The third amendment lands the canonical shape: one cluster-scoped function, internal pass ordering.

- **Single function with a `Pass` enum parameter** (`fn check_form(parsed, table, symbol_tables, pass: Pass) -> Result<...>`). Rejected: forces dispatch noise on every consumer; collapses two narrow surfaces into one wide one (Principle 2 — narrow interfaces); makes per-pass return-type evolution awkward (Pass 1 sig-shells vs Pass 2 body-checked entries with mono variants are conceivably distinct shapes in future evolution); makes per-pass test targeting clumsier. Two explicit functions is cleaner — *but see the third-amendment note above: subsequent experience showed that the two-function shape, while narrower than the enum-parameter shape, exposed implementation phasing across the facade and created a state-threading hole; the canonical surface collapses to one cluster-scoped function.*
- **Staging lives on `SymbolTable`** (e.g., a `SymbolTable::with_staging()` mode). Rejected: violates Principle 7 — there would be two write surfaces on the canonical store, with the live invariant ("checked AND committed") qualified by mode. Orchestrator-owned staging keeps the live `SymbolTable` invariant un-qualified.[^transient-vs-durable]

[^transient-vs-durable]: **Transient-vs-durable footnote (FIXME 0167 amendment).** The original "two write surfaces on the canonical store" objection conflated transient with durable. Under Approach B the canonical store has **one durable write surface** (live, committed via cluster atomic drain). Staging is a **transient orchestrator-local frame** — a separate `SymbolTable` value owned by `process_cluster`'s stack, dropped on failure, drained on success. It is never published; other workers cannot observe it. The Principle 7 objection (two write surfaces on a single canonical store) does not apply because staging is not the canonical store; it is a per-cluster frame with the same shape as the canonical store, used to absorb cross-pass write-side intent before atomic commit. The amendment in FIXME 0167 records this distinction: typecheck is structurally a stateful engine whose 91 register-call sites must mutate *something* across passes; the orchestrator hands it a transient `&mut SymbolTable` that satisfies the API while preserving cluster atomicity and live-table invariants. The `current_symbol_table_mut` accessor abstracts staging-vs-live so typecheck still cannot distinguish the two — preserving Decision 44's Principle 1 (decoupling) and Principle 7 (single durable source of truth) intent without forcing a multi-week inversion of every register-call site.
- **Single-pass per cluster with multi-pass internal**. Rejected: hides the spec-mandated two-pass structure inside typecheck and removes the orchestrator's atomic-commit hook point. The Pass 1 / Pass 2 boundary is where the orchestrator gets its chance to fail-and-drop or success-and-commit; making it implicit forfeits the structural seam.
- **`SymbolTableView` as a separate trait that `&SymbolTable` implements**. Rejected for now: adds a trait that has one production caller pattern (orchestrator passes a 2-level view); a thin newtype `View<'a, C, L>` with explicit construction is simpler. If future needs require N-level staging or alternate read shapes, a trait can be introduced then.

## Bounded-context shift

No BC moves. Typecheck's BC ("AST → typed AST + symbol tables; pure transform") tightens — both passes are pure. Int's BC ("pipeline orchestration") absorbs cluster construction and staging ownership as a refinement of the existing `process_form` retry-loop responsibility. The new function name `process_cluster` replaces `process_form` at the orchestrator entry; the old per-form retry loop becomes a one-form-cluster degenerate case of the new shape.

## Cross-references

- `design/arch/facades/typecheck.md` §"check_forms — cluster check" — the as-designed single-call surface (post-2026-05-13-third-amendment: `Vec<ParsedEntry>` parameter; `&mut ClusterContext`; `Result<(), CheckError>` return; staging-mutation through accessor; internal two-pass ordering)
- `design/arch/facades/int.md` §"`process_cluster` — the cluster-atomic orchestration loop" — orchestrator shape, ClusterContext::Cluster construction, staging drain on cluster commit
- `design/arch/facades/types.md` §"`ParsedEntry`" + §"`View`" — boundary types; `View` is constructed inside `ClusterContext::current_symbol_table`
- `design/arch/interfaces.md` §"`check_form` is pure" — narrative companion update describing the split
- `design/arch/sequences/exec-flow-compilation.mmd` — typecheck-phase loop body updated for two-pass cluster shape
- `design/arch/sequences/exec-flow-repl.mmd` — REPL eval path updated for one-form-cluster + `(begin)` cluster
- `design/arch/sequences/concurrency-symbol-table-entry.mmd` — concurrent worker view updated to reference the View read surface
- `design/arch/principles.md` — Principle 1 (Decoupling), Principle 2 (Narrow interfaces), Principle 7 (Single source of truth), Principle 11 (Single pipeline mode parameters) cited as rationale
- `design/arch/decisions/0038-sharedstate-formal-worker-shareable-subset.md` (legacy) — reframes its `check_form` shape commitment to the two-pass split
- `design/arch/fixmes/0165-spec-repl-non-macro-forward-refs-and-begin-clusters.md` — `/spec` twin: §5.13.2 extension to non-macro defns; `(begin)` as REPL cluster boundary
- `spec/05-definitions.md` §5.13.1 (file scope two-pass) and §5.13.2 (REPL) — the normative grounding

## Sequencing

This Decision unblocks Sprint 66 Wave 3a re-fire. The original sequencing (~+2 days vs the prior Wave 3a triad estimate) is amended by FIXME 0168's α/β split — see Decision 0046. Wave 3a-β cannot start before Wave 3a-α completes because cluster-atomic correctness depends on every typecheck read and write flowing through `ctx.current_symbol_table[_mut]()`; the ~40+ orphaned `self.modules.X` accesses (Sprint 66 third-re-attempt audit, 2026-05-12) bypass the accessor and would render the staging surgery ineffective if left in place.

Sequencing (post-FIXME 0168 amendment):

1. `/arch` lands this Decision + facade + sequence updates (FIXME 0167 commit).
2. `/spec` lands FIXME 0165 (§5.13.2 extension; `(begin)` cluster role).
3. `/arch` lands Decisions 0045 + 0046 + Principle 17 + facade locality updates (FIXME 0168 commit).
4. **Wave 3a-α — locality-correctness refactor** (precondition; ~3–5 days). Per Decision 0046 + Principle 17. Replace the ~40+ direct `self.modules.X` access sites with the four principled access-pattern shapes; retarget the ~6 cross-module impl writes to the writer's module per Decision 0045. `/dev` narrow per typecheck.
5. **Wave 3a-β — triad re-fires atop locality-correct typecheck** (~3–4 days; revised per 2026-05-13 third amendment):
   - Frontend: `build_form` per FIXME 0156 (unchanged from prior plan).
   - Typecheck: single `check_forms(parsed: Vec<ParsedEntry>, ctx: &mut ClusterContext, symbol_tables: &SymbolTables) -> Result<(), CheckError>` per Decision 44's third amendment. Internal two-pass ordering: Pass 1 sweeps `parsed` registering signatures into staging via the accessor; Pass 2 sweeps `parsed` body-checking against `View::union(staging, live)`. The 91 register-call sites do not change individually — the surgery is in the `ClusterContext::current_symbol_table_mut` accessor adaptation. Pass-1-to-Pass-2 working state (`defn_type_vars`, default-method-defn deferrals, generalisation inputs) is internal to the `check_forms` frame. `TypeCheckEnv` retains its other state and is reshaped to consume `ClusterContext` for table access.
   - Int: `process_cluster` constructs `ClusterContext::Cluster { modules, staging, current_module }` per cluster; transient staging `SymbolTable`; one `check_forms` call per cluster; cluster-atomic drain on `Ok`; whole-cluster retry on `Err(Gap)`; `(begin)` unwrapping. `ProcessedCluster` carries warnings + resolved_imports + introspection_records in addition to staged entries; no separate `ModuleCheckAccumulator` exists on either side.
6. Wave 1 gate test `tests/process_form_dispatch.rs` revises (forward-ref defns wrapped in `(begin)`; second test asserts cross-input forward-ref produces a clear error).

Total Wave 3a envelope: ~6–9 days (α + β), within the Sprint 66 envelope per `sprints/SPRINT.md`.

The `View<'_, C, L>` newtype is `/arch`-authored as a `cranelisp-types` addition (per "boundary types live in `cranelisp-types`"). The `ClusterContext` enum lives in `cranelisp-typecheck` (single-consumer pair: typecheck owns the structural shape; `int` constructs and threads instances). The two-pass typecheck surface is `/dev`-implemented per the facade.
