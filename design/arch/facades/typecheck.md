# Facade spec — `crates/cranelisp-typecheck/`

**Bounded context citation.** AST → typed AST + symbol tables. Owns Hindley-Milner inference, trait resolution, and monomorphisation analysis. Does not produce code. See `bounded-contexts.md` §2 — Typecheck.

This spec is **target-stating**. Drift detection between as-designed and as-built is the job of `cargo-public-api` (M4-pending) and `/review`'s per-PR audit, not this document.

---

## Public surface (as-designed)

### Free function — cluster check

The typecheck entry surface used by `int`'s shared `process_cluster` (see `facades/int.md`). Per Decision 44 (amended FIXME 0167 for Approach B + ClusterContext; third amendment 2026-05-13 collapsing the two-pass split into a single function), the typecheck entry surface is **one** free function per cluster. The internal two-pass discipline (Pass 1 register signatures, then Pass 2 check bodies — spec §5.13.1) is preserved as an implementation-phase ordering inside `check_forms`; it does not cross the facade. The whole function is pure with respect to live state; staging mutation flows through the same accessor API used in committed-mode (`current_symbol_table_mut`) and is invisible to typecheck. Cluster atomicity is preserved because staging is orchestrator-local and is committed (drained into live) only on whole-cluster success.

```rust
pub fn check_forms<C, L>(
    parsed: Vec<ParsedEntry>,
    ctx: &mut ClusterContext<'_, C, L>,           // staging-or-live access via accessor; see Decision 44 + ClusterContext
    symbol_tables: &SymbolTables<C, L>,
) -> Result<(), CheckError>;
```

Parameters:
- `parsed` — the full cluster's `ParsedEntry` list, produced by repeated `cranelisp_frontend::build_form` calls (per FIXME 0156 resolution) accumulated by the orchestrator across every form in the cluster. One `build_form` call may produce multiple `ParsedEntry` items (e.g., a multi-clause `defmacro` yields one per clause); the orchestrator hands the concatenated list to `check_forms`. `check_forms` internally drives Pass 1 (register signatures into staging via the accessor) over every entry, then Pass 2 (check bodies against the unioned staging+live view) over every entry. Pass-1-to-Pass-2 working state (e.g., `defn_type_vars`, default-method-defn deferrals, generalisation inputs) is internal to `check_forms`'s frame — never crosses the facade.
- `ctx` — `&mut ClusterContext<'_, C, L>` constructed by the orchestrator. In `ClusterContext::Cluster` mode (the cluster-processing flow), `ctx.current_symbol_table()` returns a `View<'_, C, L>` unioning staging + live (staging-first); `ctx.current_symbol_table_mut()` returns `&mut staging`. Typecheck calls these accessors uniformly — the 91 register-call sites in `program.rs` (e.g., `register_type_def`, `register_trait_decl`, `register_defn_signature`, `register_mono_entry`) and the 51 read access sites continue to use the existing API; the staging-vs-live distinction is absorbed inside the accessors. `ClusterContext` lives in `cranelisp-typecheck`.
- `symbol_tables` — read-only access to all other modules' tables for resolving FQ symbol references (`m2/foo`) and FQ type references (`m2/SomeType`). Generic over `<C, L>` per Decision 32 — typecheck is C/L-blind in production (caller passes `SymbolTables<Code, ()>`), and tests / fine-grained drivers pass `SymbolTables<(), ()>`.

Returns:
- `Ok(())` on success — Pass 1 staged signature shells, Pass 2 staged body-checked entries that superseded the shells, per-symbol Pass-2 side products landed on staging `ModuleEntry::Def` fields per invariant 3a. The orchestrator commits the whole staging table atomically into live on cluster completion.
- `Err(CheckError::Gap(ResolutionGap::SymbolTypechecked(fq)))` when an FQ value reference cannot be resolved (its module is not yet typechecked). The orchestrator catches, registers `fq.module` if needed, calls `wait_for_typecheck_symbol(fq)`, and **retries the whole `check_forms` call** with the same `parsed` list. Staging is discarded on the gap return (orchestrator drops the previous staging frame and constructs a fresh one for the retry — the cluster is atomic: there is no partial commit and no per-pass retry granularity below the cluster).
- `Err(CheckError::Gap(ResolutionGap::Type(fqt)))` — same pattern for FQ type references.
- `Err(CheckError::TypeError { message, location })` — genuine type errors (non-recoverable). The orchestrator drops the staging table on the floor when the function frame returns; the live table is byte-identical to its pre-cluster state. `location: ErrorLocation` per Decision 39.

**Post-Gap state contract (per FIXME 0160 + Decision 44 + 2026-05-13 third amendment).** On any `Err`, no live mutation has occurred — the orchestrator commits only on whole-cluster `Ok`. On `Err(Gap)`, the orchestrator dispatches via `handle_gap`, drops the staging frame, constructs a fresh one, and retries the whole `check_forms` call. On `Err(TypeError)`, the orchestrator drops staging and propagates. The live table is byte-identical to its pre-cluster state across any failure. `ReplSnapshot` remains the type-var-pool rollback primitive within `CheckState` between calls (e.g., across the retry boundary on Gap); the live table is unaffected by either error return because the cluster body never writes live, and staging dissolves with the function frame.

`check_forms` asks for `ResolutionGap::SymbolTypechecked` (not `SymbolInMemory`) for value references because typecheck only needs the entry's `Scheme`, not its compiled code. Macro expansion's need for code happens earlier, in `frontend::expand` — by the time `check_forms` runs, any macros have already been expanded out.

**Cluster atomicity**. `check_forms` is the unit of typecheck atomicity. A cluster is one form (REPL non-`begin` input), the contents of `(begin form₁ … formN)` (REPL explicit cluster), or a file's non-structural forms (batch). See `facades/int.md` §"`process_cluster` — the cluster-atomic orchestration loop" for the orchestrator side.

### Cluster check scaffolding (exposed for tests / finer-grained callers)

```rust
pub struct CheckState { /* per-call state — type-var pool, substitution, deferred resolutions */ }

impl CheckState {
    pub fn new(module: ModuleFullPath) -> Self;
    pub fn current_module(&self) -> &ModuleFullPath;
}

pub enum ClusterContext<'a, C: CodeStore, L: LinkerStore> {
    Live {
        modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,
        current_module: ModuleFullPath,
    },
    Cluster {
        modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,
        staging: &'a mut SymbolTable<C, L>,
        current_module: ModuleFullPath,
    },
}

impl<'a, C: CodeStore, L: LinkerStore> ClusterContext<'a, C, L> {
    pub fn live(modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>, current_module: ModuleFullPath) -> Self;
    pub fn cluster(modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>, staging: &'a mut SymbolTable<C, L>, current_module: ModuleFullPath) -> Self;
    pub fn current_module(&self) -> &ModuleFullPath;
    pub fn current_symbol_table(&self) -> ClusterRead<'_, C, L>;       // borrow guard; call `.view()` to get the unioned `View<'_, C, L>`
    pub fn current_symbol_table_mut(&mut self) -> ClusterWrite<'_, C, L>; // Deref/DerefMut → SymbolTable<C, L>; in Live mode wraps the DashMap RefMut, in Cluster mode wraps &mut staging
}

/// Read-side borrow guard returned by `ClusterContext::current_symbol_table()`.
/// Holds either a DashMap one-ref (Live) or both the staging-ref + a live one-ref
/// (Cluster), and exposes `.view() -> View<'_, C, L>` to obtain the unioned
/// staging-first `View` per Decision 44. Internal-but-exposed (a public type),
/// because the cluster-mode return must hold two borrows simultaneously and
/// returning `View<'_, C, L>` directly would force the caller's borrow lifetime
/// to outlive the staging borrow it depends on. Callers obtain `View` via
/// `ctx.current_symbol_table().view()`.
pub enum ClusterRead<'a, C, L> {
    Live(dashmap::mapref::one::Ref<'a, ModuleFullPath, SymbolTable<C, L>>),
    Cluster {
        staging: &'a SymbolTable<C, L>,
        live: dashmap::mapref::one::Ref<'a, ModuleFullPath, SymbolTable<C, L>>,
    },
}

impl<'a, C, L> ClusterRead<'a, C, L> {
    pub fn view(&self) -> View<'_, C, L>;  // Cluster → View::union(staging, live); Live → View::single(live)
}

/// Write-side borrow guard returned by `ClusterContext::current_symbol_table_mut()`.
/// Implements `Deref<Target = SymbolTable<C, L>>` and `DerefMut`, so all 91
/// register-call sites in typecheck (`register_type_def`, `register_trait_decl`,
/// etc.) call methods on it as if it were a direct `&mut SymbolTable`. In `Live`
/// mode wraps a DashMap `RefMut`; in `Cluster` mode wraps `&mut staging`. The
/// staging-vs-live distinction is absorbed inside the guard so callers don't
/// thread it through. Internal-but-exposed for the same reason as `ClusterRead`
/// (RAII boundary; cannot collapse to `&mut SymbolTable` without losing the
/// DashMap lock-discipline in Live mode).
pub enum ClusterWrite<'a, C, L> {
    Live(dashmap::mapref::one::RefMut<'a, ModuleFullPath, SymbolTable<C, L>>),
    Cluster(&'a mut SymbolTable<C, L>),
}

pub struct TypeCheckEnv<'a, C, L> { /* per-form environment — wraps &mut ClusterContext + read-only symbol_tables */ }

impl<'a, C, L> TypeCheckEnv<'a, C, L> {
    pub fn new(modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>, next_id: &'a AtomicU32) -> Self;
    pub fn next_type_id(&mut self) -> TypeId;
}
```

`CheckState`, `ClusterContext`, `ClusterRead`, `ClusterWrite`, and `TypeCheckEnv` exist for tests and for crates that want to construct typecheck driver state directly. `int` uses `check_forms` exclusively in production. `TypeCheckEnv` carries `&mut ClusterContext<'_, C, L>` per Decision 38 + Decision 44 (amended FIXME 0167) — table access flows through `ClusterContext::current_symbol_table()` (read, returning `ClusterRead`) / `current_symbol_table_mut()` (write, returning `ClusterWrite`) so the 91 register-call sites and 51 access sites in `program.rs` do not change individually. In production cluster-processing flow, the orchestrator hands `ClusterContext::Cluster { staging, … }`; in REPL introspection / fine-grained-test paths the caller may construct `ClusterContext::Live { modules, current_module }` for direct live access. Per-symbol writes in committed (Live) mode go through the inner DashMap's per-key locks; in cluster mode they go through the `&mut staging` exclusive borrow held by the orchestrator's stack frame.

**`TypeCheckEnv` target shape — narrowing target (per Sprint 67 PIF row 21).** As-built `TypeCheckEnv` exposes ~30 methods (per-symbol lookups, snapshot/restore, module-table accessors, exhaustiveness checks, display-info computation, register helpers, etc. — see `crates/cranelisp-typecheck/public-api.txt` lines 164–202). The facade prescribes exactly **2 methods**:

- `pub fn new(modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>, next_id: &'a AtomicU32) -> Self`
- `pub fn next_type_id(&mut self) -> TypeId`

The remaining ~28 methods drop from the public surface during /dev (typecheck) Wave 3 narrowing: per-symbol lookups (`lookup_type_def`, `lookup_trait_decl`, `lookup_constructor_type`, `get_type_constructors`, `get_implementing_types`, `get_impls_for_type`, `get_trait_methods`, `has_impl`, `method_to_trait`, `method_belongs_to_trait`, `is_internal_constructor_check`, `defining_module_for`, `fqtn_for_type`, `resolve_module_by_name`) become `pub(crate)` callee-side helpers — all callers are inside `check_forms`'s frame; module-table accessors (`module_table`, `module_table_cloned`, `modules`, `modules_ref`, `has_module`, `ensure_module_exists`, `insert_module`, `remove_module`) likewise become internal (cluster-mode access flows through `ClusterContext::current_symbol_table()`; cross-module probes follow the per-symbol shapes in Invariant 10 below); snapshot/restore (`snapshot`, `restore`, `snapshot_type_defs`, `restore_cached_module`, `restore_cached_impls`) is `pub(crate)`-scoped to typecheck-internal callers (REPL eval rollback flows through the orchestrator's staging-drop instead — Decision 44); aggregate enumerations (`all_type_defs`, `all_type_defs_map`) become `pub(crate)`; `register_imports`, `register_exports`, `clear_module_for_replace_public`, `compute_display_info_public`, `unregister_trait`, `get_got_slot`, `check_exhaustiveness` all become `pub(crate)` (called from inside `check_forms`).

FIXME 0172 (short-name fallback chains in `defining_module_for` / `fqtn_for_bare_type_name`) closes alongside this narrowing — the fallback chain code is rewritten into Invariant 10's principled per-shape probes, and the two methods become `pub(crate)` chain-follow helpers (or drop entirely if every callsite is reachable from `resolve::*`'s lift). Tests that pre-S67 reached into `TypeCheckEnv` for ad-hoc probes (e.g., `module_table_cloned`) migrate to either constructing a `ClusterContext::Live` and using the public read accessor, or to inspecting `CheckResult` / `SymbolTable` directly.

**No public pass discriminator.** The pre-S66 `pub enum CheckPass { Pass1Signatures, Pass2Bodies }` and the intermediate `check_form_signatures` / `check_form_body` two-function split are both removed from the public API per Decision 44's 2026-05-13 third amendment. The two-pass discipline (spec §5.13.1) is an **implementation-phase ordering inside `check_forms`** — Pass 1 sweeps `parsed`, Pass 2 sweeps `parsed` — not a facade-exposed surface. Internal multi-pass scaffolding may retain a `pub(crate)` enum or two `pub(crate)` helpers if convenient; they do not cross the crate boundary. The state-threading hole that the two-function split exposed (Pass-1-to-Pass-2 working state could not be carried across two separate calls without a public accumulator) is closed by construction: no working state crosses the facade because there is only one call.

**No public accumulator type.** The pre-S66 `pub struct ModuleCheckAccumulator` and the briefly-considered relocation of that struct to `int` are both retired. Per-symbol Pass-2 side products (method resolutions, expr types, mono defns, callees) land on staging `ModuleEntry::Def` fields per invariant 3a. Pass-1-to-Pass-2 working state and cluster-scoped algorithmic aggregates (`defn_type_vars`, default-method-defn deferrals, generalisation inputs) are internal to `check_forms`'s frame and never publicly visible. Cross-symbol bookkeeping that `int` itself collects during cluster processing (warnings, resolved-import bindings, introspection records) lives on `int`-side data structures — see `facades/int.md` §"Cluster orchestration result".

### Builtin registration (called once per workspace init — cluster-atomic post-S66)

```rust
pub fn register_builtins<C, L>(
    modules: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    next_id: &AtomicU32,
)
where C: CodeStore, L: LinkerStore;
```

Builtin registration now operates against the whole modules-map: it inserts the `primitives` and `macros` synthetic modules' `SymbolTable`s (per `spec/08-modules.md §8.7`) and threads `next_id` so the registration's type-var allocations remain monotonic with the rest of the session's `TypeCheckEnv`-allocated type ids. Called once per session init (the int binary's `compile_to_module` path; tests construct an empty `DashMap + AtomicU32` and call `register_builtins` themselves). Idempotent — safe to call once per fresh modules map. Per Decision 38 this remains a brief `&mut SymbolTable` write window, but the access is mediated through the DashMap's per-key lock rather than the caller-held `&mut`.

Seeds the modules-map with primitive type defs (`Int`, `Bool`, `String`, `Float`, `Unit`), primitive functions (per `cranelisp_types::primitives()`), and the synthetic `primitives`/`macros` modules' contents.

### Trace hooks (for diagnostics — observability layer)

```rust
pub mod trace {
    /// Outcome enum surfaced when typecheck would create-or-find a per-module
    /// `SymbolTable`. Two variants: `Created` (this call inserted the entry),
    /// `AlreadyPresent` (the entry was already there). `as_u8(self) -> u8` for
    /// numeric trace encoding. Derives Clone, Copy, Eq, PartialEq, Debug.
    pub enum SymbolTableEnsureOutcome {
        AlreadyPresent,
        Created,
    }

    /// Hook signature: `fn(module: &ModuleFullPath, outcome: SymbolTableEnsureOutcome)`.
    /// Public function-pointer type (not a trait — observability is one-shot
    /// global install, per Principle 14 callback discipline).
    pub type SymbolTableEnsureHook = fn(&ModuleFullPath, SymbolTableEnsureOutcome);

    /// Install a global hook for `SymbolTable` ensure events. Called once at
    /// session startup by int's observability layer (per FIXME 0103 trace plan,
    /// Decision 40). Re-installing overwrites the previous hook — no
    /// composition; observers chain externally.
    pub fn install_symbol_table_ensure_hook(hook: SymbolTableEnsureHook);

    /// Emit a `SymbolTableEnsure` event to the installed hook (if any).
    /// Called by typecheck whenever it would touch a per-module `SymbolTable`
    /// during cluster check or builtin registration. No-op if no hook is
    /// installed.
    pub fn emit_symbol_table_ensure(module: &ModuleFullPath, outcome: SymbolTableEnsureOutcome);
}

// re-exported at crate root for convenience:
pub use trace::{
    SymbolTableEnsureOutcome,
    SymbolTableEnsureHook,
    install_symbol_table_ensure_hook,
};
```

Exposes the cross-crate trace-install hook described in `design/int/heisenbug-race-closure.md §3d''` — `int`'s observability layer wires this to its scheduler trace sink at startup. The three submodule items + the two crate-root re-exports (`SymbolTableEnsureOutcome`, `install_symbol_table_ensure_hook`) form the observable surface; `emit_symbol_table_ensure` is called only from inside typecheck but is pub so the observability split (per Decision 40) is consistent across crates.

### Public consts

None.

### Module-lifecycle free functions (S67 hack-back — FIXME 0192)

```rust
pub fn register_imports<C, L>(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    next_id: &AtomicU32,
    state: &mut CheckState,
    specs: &[ImportSpec],
) -> Result<(), CranelispError>;

pub fn register_exports<C, L>(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    next_id: &AtomicU32,
    state: &mut CheckState,
    specs: &[ExportSpec],
) -> Result<(), CranelispError>;

pub fn advance_next_id_past_table<C, L>(
    next_id: &AtomicU32,
    table: &SymbolTable<C, L>,
);
```

Free fns that perform module-lifecycle work without requiring a fully-constructed `TypeCheckEnv` borrow. `register_imports` / `register_exports` were lifted off `TypeCheckEnv` in the Sprint 67 hack-back (FIXME 0192) so cross-crate callers (`int`'s import-form handler) do not need to construct a typecheck env. `advance_next_id_past_table` is the TypeId-consistency primitive split out of the pre-S67 `restore_cached_module` — composed by the `int`-side cache-hit branch alongside `cranelisp_types::install_module` (see `facades/types.md` §"Module-lifecycle primitives").

The data-home counterpart of `register_imports`/`register_exports` is `cranelisp_types::install_module` + `ensure_module_exists`; together these form the lifecycle pair used by `CompilerSession::introduce_module`'s four-branch orchestration.

---

## FQTypeName binding at typecheck boundaries

Per Decision 0047 + `facades/types.md` §"FQTypeName migration plan (Sprint 67)" §"typecheck", every resolved-stage API on the typecheck surface that names a type uses `FQTypeName`; bare `TypeName` is reserved for the three exception classes (syntactic-lift sites, receiver-pinned helpers, reverse-lookup primitives). The per-API direction list lives in the types-facade migration plan, NOT duplicated here — that table is the single source of truth for both /dev (typecheck) execution and /review acceptance at Wave 5. Typecheck carries the largest /dev burden of the six crates' migration (per Decision 0047 §"Status pointer"): ~7 PIF conversions + ~3 syntactic-lift-site keeps + ~5 receiver-pinned keeps.

Most of those APIs become `pub(crate)` per the `TypeCheckEnv` narrowing above and stop crossing the facade boundary entirely. The hits that remain at the public surface after Wave 3 narrowing are: (a) `register_builtins`'s internal allocations (receiver-pinned, exception 2), (b) `resolve::*`'s syntactic-stage entry points if kept public (exception 1: syntactic lift site), (c) any debug/introspection helper escape hatches if kept (each must cite an exception by name in a code comment per the Wave 5 /review checkpoint).

---

## Types originated here

Per Principle 15's placement heuristic — `CheckResult`, `CheckError`, `CheckState`, `TypeCheckEnv`, `ClusterContext`, and `ReplSnapshot` live in `cranelisp-typecheck` (referenced by `int` only — single implementation-crate consumer). `CheckPass`, `FormCheckResult`, and `ModuleCheckAccumulator` are removed from the public surface entirely per Decision 44's 2026-05-13 third amendment — `check_forms` is the single entry; pass discriminator and cross-pass working state are internal to its frame. `ResolutionGap` is the cross-cutting exception: it is referenced by the frontend facade (`ExpansionError::Gap`) and the typecheck facade (`CheckError::Gap`), so it lives in `cranelisp-types` per the multi-consumer rule. `int` pattern-matches both gap-bearing errors against the same shared variants. `View<'a, C, L>` lives in `cranelisp-types` (multi-consumer at the boundary type level — see `facades/types.md` §"`View<'a, C, L>`"); `ClusterContext` consumes it via the read accessor.

```rust
// In cranelisp-typecheck:
//
// Per Decision 44's 2026-05-13 third amendment, CheckResult is pared to
// the two cross-cluster items that the orchestrator surfaces to the REPL
// display layer; per-symbol Pass-2 side products land on staging
// ModuleEntry::Def fields per invariant 3a, NOT on CheckResult.
pub struct CheckResult {
    pub display: Option<DisplayInfo>,      // last-form display info for REPL value-printing
    pub warnings: Vec<Warning>,             // cluster-scope warnings (e.g., unused imports)
}
pub enum   CheckError { Gap(ResolutionGap), TypeError { message, location: ErrorLocation } }
// CheckPass, FormCheckResult, ModuleCheckAccumulator are removed from the public surface
// per Decision 44's 2026-05-13 third amendment — pass ordering and cross-pass state are
// internal to check_forms's frame.
pub struct CheckState { /* current_module + per-call state — type-var pool, substitution, deferred resolutions */ }
pub enum   ClusterContext<'a, C, L> { Live { … }, Cluster { … } }   // Decision 44 (amended FIXME 0167) — staging-vs-live abstraction
pub enum   ClusterRead<'a, C, L>  { Live(...), Cluster { staging, live } }  // Decision 44 — read-side borrow guard; `.view()` yields View<'_, C, L>
pub enum   ClusterWrite<'a, C, L> { Live(...), Cluster(&'a mut SymbolTable<C, L>) }  // Decision 44 — write-side borrow guard; Deref/DerefMut → SymbolTable<C, L>
pub struct TypeCheckEnv<'a, C, L> { /* … */ }
/// REPL eval rollback primitive. Captured before a cluster check; restored
/// on cluster Err to wind back type-var pool + substitution + per-symbol
/// staging state. Per invariant 7 — typecheck provides the primitive, the
/// caller (REPL eval) drives the snapshot/restore.
pub struct ReplSnapshot {
    pub next_type_id: TypeId,                       // restores TypeCheckEnv's monotonic type-var counter
    pub scope_depth: usize,                         // restores CheckState's scope stack depth
    pub subst_len: usize,                           // restores the substitution log length (truncation rolls back unifications)
    pub symbol_keys: HashSet<Symbol>,               // symbols that existed in the current module pre-cluster — survivors after rollback
}

// In cranelisp-types (multi-consumer):
pub enum ResolutionGap {
    /// Symbol's typecheck not yet complete — orchestrator waits for `notify_symbol_typechecked(fq)`.
    /// Produced by `cranelisp_typecheck::check_forms` (per Decision 44 — single-call cluster
    /// surface, 2026-05-13 third amendment) for FQ value references whose target module has not
    /// finished typechecking. (Macros are already expanded by the time `check_forms` runs, so
    /// this variant is never produced from typecheck for macro lookups; `MacroInMem` is the
    /// macro-side variant produced by frontend's `expand`.)
    SymbolTypechecked(FQSymbol),
    /// Macro target needs in-mem JIT — orchestrator does `ensure_registered` +
    /// `wait_for_typecheck_symbol`, peeks at the entry, and if it's a Macro with `code` missing
    /// additionally `priority_boost_jit(fq)` + `wait_for_inmem(fq)`. One retry round-trip
    /// regardless of macro-vs-fn. Produced exclusively by `cranelisp_frontend::expand`.
    MacroInMem(FQSymbol),
    /// Type reference needs typecheck — orchestrator waits for `notify_type_resolved(fqt)`.
    /// Produced by `cranelisp_typecheck::check_forms` for FQ type references in
    /// `TypeExpr::Named` / `TypeExpr::Applied` whose target module has not finished typechecking.
    Type(FQTypeName),
}
```

The multi-consumer types `CheckResult` depends on (`Scheme`, `Subst`, `Type`, `TypeId`, `ResolvedCall`, `MethodResolutions`, `ConstructorInfo`, `FieldInfo`, `TypeDefInfo`, `DisplayInfo`, `MonoDefn`, `Warning`, `TraitDecl`) live in `cranelisp-types` because backend codegen also consumes them — see Principle 15's placement heuristic. `CheckResult.warnings: Vec<Warning>` and the public `lookup_trait_decl(..) -> Option<TraitDecl>` (and other queries that surface `TraitDecl`) reference types-hosted definitions; `TraitDecl` carries the trait header (name, type params, method signatures) that typecheck reads during impl resolution and that REPL introspection (`/info <trait>`) renders. `CheckError::TypeError.location: ErrorLocation` carries Decision 39's coordinates-as-data carrier; `int`'s formatter resolves through `shared.introspection[fq].source` for inline source snippets in REPL/trace mode (per Decision 38's mode-conditional Introspection store).

**Two legacy crate-root re-exports** (`pub use cranelisp_types::CranelispError` and `pub use cranelisp_types::TopLevel`) appear at `cranelisp_typecheck::CranelispError` / `cranelisp_typecheck::TopLevel`. Internal-but-exposed convenience re-exports: callers that import `cranelisp_typecheck::*` for the typecheck surface also reach for these types in error-handling and AST-input paths. Per Principle 15 these are not endorsed at the facade level — new callers should import `CranelispError` / `TopLevel` directly from `cranelisp-types`. Removal is a /dev (typecheck) Wave 3 follow-on once external import sites are confirmed clean (no S67 close requirement; tracked as housekeeping).

Otherwise no re-exports of `cranelisp-types` items per Principle 15 — `int` imports `Type`, `Scheme`, `Symbol`, `ResolutionGap`, `Warning`, `TraitDecl` etc. from `cranelisp-types` and `CheckResult`, `CheckError`, etc. from `cranelisp-typecheck`.

---

## Consumed surface

The typecheck crate imports from:

- **`cranelisp-types`** — the full set: `Sexp`, `Expr`, `TopLevel`, `Defn`, `Pattern`, `MatchArm`, `TypeExpr`, `Type`, `Scheme`, `TypeId`, `Subst`, `Span`, `CranelispError`, `Symbol`, `ModuleFullPath`, `FQSymbol`, `FQTypeName`, `TypeName`, `TraitName`, `ImportSpec`, `ExportSpec`, `ImportNames`, `SymbolTable`, `ModuleEntry`, `DefKind`, `PrimitiveKind`, `MacroClauseInfo`, `MacroParam`, `Visibility`, `CallGraph`, `CallEdge`, `CallInfo`, `PrimitiveDef`, `primitives`, `apply`, `free_vars`, `max_type_var_id`, `type_var_names`, `format_type_display`, `format_type_with_vars`.

The typecheck crate imports from no other workspace crate — not `cranelisp-frontend`, not `cranelisp-backend`. (Frontend builds the input; backend consumes the output. Typecheck is a pure transform between them.)

---

## Sealed traits

None implemented. Typecheck does not implement traits from `cranelisp-types`.

---

## `#[non_exhaustive]` DTOs

`CheckState`, `TypeCheckEnv`, `ClusterContext` are all `#[non_exhaustive]`. (`CheckPass`, `FormCheckResult`, and `ModuleCheckAccumulator` are no longer public typecheck-side types per Decision 44's 2026-05-13 third amendment — they are internal to `check_forms`'s frame, with internal scaffolding `pub(crate)` if at all.) Types re-exported from `cranelisp-types` are `#[non_exhaustive]` per the types-crate facade.

---

## Bounded-context invariants

These hold across sprints — the contract `cranelisp-typecheck` makes with the rest of the workspace:

1. **No code generation.** Typecheck never invokes Cranelift, never produces JIT or object output. Its product is annotated AST + symbol-table entries.
2. **No commits to live `SymbolTable` from `check_forms`.** Per FIXME 0160 resolution + Decision 44 (amended FIXME 0167 for Approach B + ClusterContext; 2026-05-13 third amendment collapsing the two-pass split into a single call) — `check_forms` is pure with respect to **live state**: it does not mutate the live `SymbolTable` nor any state visible outside the cluster. It MAY mutate the orchestrator-handed staging `SymbolTable` via the same accessor API used in committed-mode (`ctx.current_symbol_table_mut()`); typecheck cannot distinguish staging from live because the accessor abstracts the difference. The 91 register-call sites in `program.rs` and the 51 read access sites continue to use the existing API; the `ClusterContext` accessors are the single point of staging-vs-live surgery. Cluster atomicity is preserved because staging is orchestrator-local and is committed (drained into live) only on whole-cluster `Ok`. The caller (`int::process_cluster`) drops staging on the floor on any `Err`; on `Err(Gap)` the orchestrator dispatches and **retries the whole `check_forms` call** against a fresh staging frame (cluster atomicity has no sub-cluster granularity). The live table is byte-identical to its pre-cluster state across any failure — this is what makes the temp-closure path in REPL eval work, and what preserves Decision 44's structural intent (Principle 1 decoupling + Principle 7 single durable source of truth) without requiring a multi-week inversion of every register-call site. Resolved import bindings are installed by `int` (post-cluster Ok arm) via `SymbolTable::install_import_bindings(&self, …)`; this is `int`'s call, not typecheck's.
3. **Single source of truth via `defined_symbols()`.** Per Decision 22 — the codegen-compilable predicate is `SymbolTable::defined_symbols()`. Typecheck writes entries that satisfy or fail this predicate; it does not maintain a parallel store.

3a. **Per-symbol Pass-2 side products land on staging `ModuleEntry::Def` fields. Pass-1-to-Pass-2 working state is internal to `check_forms`, not visible at the facade.** Two distinct categories of intra-pass data must be distinguished (the conflation of which produced the state-threading hole that triggered Decision 44's 2026-05-13 third amendment):
    - **Per-symbol Pass-2 side products** (the data that survives the cluster and is consumed by downstream stages — codegen, the call graph, REPL display) are written into the staging `ModuleEntry::Def` entry's existing fields during Pass 2 inside `check_forms`: call-graph edges into `Def.callees` (Decision 21); expr type annotations onto `Def.ast` (Decision 22); mono entries staged as additional `Def` entries with mangled names; method resolutions accumulated on the corresponding entry; per-form side products (`method_resolutions: HashMap<Span, ResolvedCall>`, `expr_types: HashMap<Span, Type>`, `mono_defns: Vec<MonoDefn>`, `callees: Vec<FQSymbol>`) all land here. The orchestrator's drain into live (`int::insert_cluster`) carries these annotations with each entry.
    - **Pass-1-to-Pass-2 working state and cluster-scoped algorithmic intermediaries** (the data that flows internally between Pass 1's signature registration and Pass 2's body check — `defn_type_vars`, default-method-defn deferrals from trait-impl registration, generalisation inputs, multi-sig variant accumulation, the deferred-resolutions working set) are **internal to `check_forms`'s stack frame**. They are not exposed at the facade — no `&mut ModuleCheckAccumulator` parameter, no `pub` accumulator type. They are constructed when `check_forms` enters, consumed across the Pass 1 → Pass 2 boundary internally, and dropped when `check_forms` returns. By construction, no caller can lose them between calls — there is only one call.

    The orchestrator therefore needs to know only about category 1 (carried on staging `Def` entries; drained by `insert_cluster`). Cross-symbol bookkeeping that the orchestrator itself collects during cluster processing (warnings, resolved-import bindings, introspection records) is `int`-side data not typecheck-side data; it is produced inside `check_forms` (or alongside it) and surfaced to `int` via the cluster return shape — see `facades/int.md` §"Cluster orchestration result".
4. **TC-sourced call graph.** Per Decision 21 — call graph edges are extracted during typechecking from method resolutions. `CheckResult.callees: Vec<FQSymbol>` is the per-symbol call graph; the rich `CallGraph` (with tail-position info) is for within-module codegen analysis.
5. **Trait method dispatch via `ResolvedCall::TraitMethod`.** Typecheck always emits `TraitMethod` for trait-dispatched operators; backend handles lowering. Typecheck stays clean of backend-specific concerns. The prior `(TraitName, Symbol, TypeName) → primitive` collusion-table approach in backend is retired per Decision 43 — backend has no trait knowledge; primitive emission goes through `cranelisp-primitives` + `cranelisp-intrinsics` directly.
6. **Constraint propagation in `generalize`.** Per Decision 19 — `Scheme.constraints` is populated by collecting trait constraints from active type variables during generalisation. Non-empty constraints mark a constrained polymorphic function (monomorphised at call sites).
7. **TC snapshot/restore for error rollback.** `check_forms` allocates type vars within `CheckState`; the symbol-table writes that pre-S66 stages performed are gone (FIXME 0160 + Decision 44 — `check_forms` is pure with respect to live state). On `Err`, `int` (or the caller) restores via `ReplSnapshot` before retrying. Typecheck provides the snapshot/restore primitive but does not invoke it itself; the caller decides when to take and restore snapshots. (REPL eval is the primary consumer — a failed cluster must not leave residual type-var bindings visible to the next eval.) The orchestrator's transient staging table (per Decision 44) is the layer that absorbs cross-pass write-side intent — it is not visible to typecheck and is dropped on cluster failure.
8. **FQ resolution surfaces via `CheckError::Gap`.** Per the gap-return pattern (`facades/int.md`, `exec-flow-compilation`) — when `check_forms` encounters an FQ symbol or FQ type reference whose target isn't typechecked, it returns `Err(CheckError::Gap(ResolutionGap::SymbolTypechecked(fq)))` or `Err(CheckError::Gap(ResolutionGap::Type(fqt)))`. Typecheck does NOT block, does NOT call the scheduler, does NOT register modules — it surfaces the dependency to its caller (`int::process_cluster`), which dispatches via `handle_gap` and retries the whole `check_forms` call.
9. **No `Sess` / `CompileScheduler` dependency.** Same as frontend — typecheck stays a pure function from inputs (`ParsedEntry`, `SymbolTable`, `SymbolTables`) to outputs (`Vec<(Symbol, ModuleEntry)>` or `CheckError`). Principle 3.
10. **Module locality — typecheck never iterates the universe of modules.** Per Principle 17 (Module locality in typecheck), every cross-module access in `cranelisp-typecheck` fits one of four principled shapes; unbounded scans of `self.modules` for short-name resolution, impl resolution, or method-of-type aggregation are forbidden. The shapes are:

    ```rust
    // 1. Unqualified short-name lookup — current module only; follow Import bindings to FQ home.
    match ctx.current_symbol_table().lookup(&name) {
        Some(ModuleEntry::Import { source, .. }) => {
            // `source` is the FQSymbol that the import binding points at; cross-module read
            // is direct (Q2 shape 2), not an unbounded scan.
            symbol_tables.get(&source.module).and_then(|t| t.get(&source.symbol))
        }
        Some(entry) => Some(entry),
        None => None,
    }

    // 2. Qualified (FQ) lookup — direct, single named module.
    symbol_tables.get(&fq.module).and_then(|t| t.get(&fq.symbol))

    // 3. Impl resolution — chain-follow the trait reference back to its
    //    defining module (per shape 1) and probe that one module's table for
    //    `impl$FQTypeName$FQTraitName`. Storage placement is the trait's
    //    defining module per Decision 0045. No closure walk; no cycle
    //    detection; per-symbol point-to-point navigation only.
    let trait_home = chain_follow_to_home(trait_fq, &symbol_tables);
    symbol_tables.get(&trait_home)
        .and_then(|t| t.get(&Symbol::from(impl_synthetic_key(trait_fq, type_fq))))

    // 4. Bulk introspection — current module only.
    let local_type_defs: Vec<_> = ctx.current_symbol_table()
        .iter()
        .filter_map(|(_, e)| matches!(e, ModuleEntry::TypeDef { .. }).then(|| e))
        .collect();
    // Multi-module aggregation is composed at the orchestrator (session/REPL) layer, not inside check_forms.
    ```

    Mutating writes always go through `ctx.current_symbol_table_mut()` — a typecheck pass MUST NOT mutate a foreign module's table directly. `ModuleEntry::TraitImpl` writes target the **trait's defining module** per Decision 0045; the orchestrator selects the target table by chain-following the trait reference at write time, identically to the read side. Cross-module impl writes that pre-S66 source carries (~6 sites in `builtins.rs` + `checker.rs`, audited 2026-05-12) are Wave 3a-α retargets per Decision 0046 — the redo retargets to the trait's home, not the writer's home. This invariant is the structural prerequisite for invariant 2's cluster-atomic guarantee — the `ClusterContext` accessor surgery only delivers cluster atomicity if every read and write actually flows through it; the absence of orphaned `self.modules.X` pierces is what makes that the case.
