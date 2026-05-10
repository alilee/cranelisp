---
number: 0044
title: Cluster-atomic typecheck — split `check_form` into two passes; orchestrator owns staging via ClusterContext
status: pre-implementation
filed: sprint 66 (Phase 5 Wave 3a structural-finding resolution)
amended: sprint 66 Phase 3 (FIXME 0167 — Approach B; staging mutation via `current_symbol_table_mut` accessor; ClusterContext introduction; invariant 2 revision; pass return type changes to `Result<(), CheckError>`)
canonical_location: design/arch/facades/typecheck.md §"check_form_signatures + check_form_body"; design/arch/facades/int.md §"process_cluster — the cluster-atomic orchestration loop"; design/arch/facades/types.md §"`ParsedEntry`" + §"`View`"; design/arch/sequences/exec-flow-compilation.mmd, exec-flow-repl.mmd, concurrency-symbol-table-entry.mmd
amends: []
amended_by: []
retracts: []
reframes: [0038]
filed_by_fixme: 0166
amended_by_fixme: 0167
---

# 0044 — Cluster-atomic typecheck via orchestrator-owned staging + two pure passes

## Statement

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

- **Single function with a `Pass` enum parameter** (`fn check_form(parsed, table, symbol_tables, pass: Pass) -> Result<...>`). Rejected: forces dispatch noise on every consumer; collapses two narrow surfaces into one wide one (Principle 2 — narrow interfaces); makes per-pass return-type evolution awkward (Pass 1 sig-shells vs Pass 2 body-checked entries with mono variants are conceivably distinct shapes in future evolution); makes per-pass test targeting clumsier. Two explicit functions is cleaner.
- **Staging lives on `SymbolTable`** (e.g., a `SymbolTable::with_staging()` mode). Rejected: violates Principle 7 — there would be two write surfaces on the canonical store, with the live invariant ("checked AND committed") qualified by mode. Orchestrator-owned staging keeps the live `SymbolTable` invariant un-qualified.[^transient-vs-durable]

[^transient-vs-durable]: **Transient-vs-durable footnote (FIXME 0167 amendment).** The original "two write surfaces on the canonical store" objection conflated transient with durable. Under Approach B the canonical store has **one durable write surface** (live, committed via cluster atomic drain). Staging is a **transient orchestrator-local frame** — a separate `SymbolTable` value owned by `process_cluster`'s stack, dropped on failure, drained on success. It is never published; other workers cannot observe it. The Principle 7 objection (two write surfaces on a single canonical store) does not apply because staging is not the canonical store; it is a per-cluster frame with the same shape as the canonical store, used to absorb cross-pass write-side intent before atomic commit. The amendment in FIXME 0167 records this distinction: typecheck is structurally a stateful engine whose 91 register-call sites must mutate *something* across passes; the orchestrator hands it a transient `&mut SymbolTable` that satisfies the API while preserving cluster atomicity and live-table invariants. The `current_symbol_table_mut` accessor abstracts staging-vs-live so typecheck still cannot distinguish the two — preserving Decision 44's Principle 1 (decoupling) and Principle 7 (single durable source of truth) intent without forcing a multi-week inversion of every register-call site.
- **Single-pass per cluster with multi-pass internal**. Rejected: hides the spec-mandated two-pass structure inside typecheck and removes the orchestrator's atomic-commit hook point. The Pass 1 / Pass 2 boundary is where the orchestrator gets its chance to fail-and-drop or success-and-commit; making it implicit forfeits the structural seam.
- **`SymbolTableView` as a separate trait that `&SymbolTable` implements**. Rejected for now: adds a trait that has one production caller pattern (orchestrator passes a 2-level view); a thin newtype `View<'a, C, L>` with explicit construction is simpler. If future needs require N-level staging or alternate read shapes, a trait can be introduced then.

## Bounded-context shift

No BC moves. Typecheck's BC ("AST → typed AST + symbol tables; pure transform") tightens — both passes are pure. Int's BC ("pipeline orchestration") absorbs cluster construction and staging ownership as a refinement of the existing `process_form` retry-loop responsibility. The new function name `process_cluster` replaces `process_form` at the orchestrator entry; the old per-form retry loop becomes a one-form-cluster degenerate case of the new shape.

## Cross-references

- `design/arch/facades/typecheck.md` §"`check_form_signatures` + `check_form_body`" — the as-designed two-call surface (post-amendment: `&mut ClusterContext` parameter; `Result<(), CheckError>` return; staging-mutation through accessor)
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

This Decision unblocks Sprint 66 Wave 3a re-fire. Implementation cost (~+2 days vs the original Wave 3a triad estimate) sits within the sprint envelope per `sprints/SPRINT.md`. Sequencing:

1. `/arch` lands this Decision + facade + sequence updates (this commit).
2. `/spec` lands FIXME 0165 (§5.13.2 extension; `(begin)` cluster role).
3. Wave 3a triad re-fires:
   - Frontend: `build_form` per FIXME 0156 (unchanged from prior plan).
   - Typecheck: TWO passes (`check_form_signatures` + `check_form_body`); each takes `&mut ClusterContext` and returns `Result<(), CheckError>`. The 91 register-call sites do not change individually — the surgery is in the `ClusterContext::current_symbol_table_mut` accessor adaptation. `TypeCheckEnv` retains its other state and is reshaped to consume `ClusterContext` for table access.
   - Int: `process_cluster` constructs `ClusterContext::Cluster { modules, staging, current_module }` per cluster; transient staging `SymbolTable`; cluster-atomic drain on Pass-2 success; `(begin)` unwrapping.
4. Wave 1 gate test `tests/process_form_dispatch.rs` revises (forward-ref defns wrapped in `(begin)`; second test asserts cross-input forward-ref produces a clear error).

The `View<'_, C, L>` newtype is `/arch`-authored as a `cranelisp-types` addition (per "boundary types live in `cranelisp-types`"). The `ClusterContext` enum lives in `cranelisp-typecheck` (single-consumer pair: typecheck owns the structural shape; `int` constructs and threads instances). The two-pass typecheck surface is `/dev`-implemented per the facade.
