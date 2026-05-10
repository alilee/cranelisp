# Facade spec — `crates/cranelisp-typecheck/`

**Bounded context citation.** AST → typed AST + symbol tables. Owns Hindley-Milner inference, trait resolution, and monomorphisation analysis. Does not produce code. See `bounded-contexts.md` §2 — Typecheck.

This spec is **target-stating**. Drift detection between as-designed and as-built is the job of `cargo-public-api` (M4-pending) and `/review`'s per-PR audit, not this document.

---

## Public surface (as-designed)

### Free functions — the two-pass per-form check

The typecheck entry surface used by `int`'s shared `process_cluster` (see `facades/int.md`). Per Decision 44 (amended FIXME 0167 for Approach B + ClusterContext), the per-form check splits into two passes that the orchestrator drives across every form in a cluster: Pass 1 across all forms, then Pass 2 across all forms. Both passes are pure with respect to live state; staging mutation flows through the same accessor API used in committed-mode (`current_symbol_table_mut`) and is invisible to typecheck. Cluster atomicity is preserved because staging is orchestrator-local and is committed (drained into live) only on Pass-2 success across all forms.

```rust
pub fn check_form_signatures<C, L>(
    parsed: ParsedEntry,
    ctx: &mut ClusterContext<'_, C, L>,           // staging-or-live access via accessor; see Decision 44 + ClusterContext
    symbol_tables: &SymbolTables<C, L>,
) -> Result<(), CheckError>;

pub fn check_form_body<C, L>(
    parsed: ParsedEntry,
    ctx: &mut ClusterContext<'_, C, L>,           // cluster signatures from Pass 1 visible via current_symbol_table()
    symbol_tables: &SymbolTables<C, L>,
) -> Result<(), CheckError>;
```

Parameters:
- `parsed` — the parse-time-only `ParsedEntry` produced by `cranelisp_frontend::build_form` (per FIXME 0156 resolution). One `build_form` call may produce multiple `ParsedEntry` items (e.g., a multi-clause `defmacro` yields one per clause); the orchestrator drives both passes once per `ParsedEntry`. The same `ParsedEntry` instance is passed to Pass 2 that was passed to Pass 1 — `ParsedEntry` persists across both passes within one cluster's processing (see `facades/types.md` §"`ParsedEntry`").
- `ctx` — `&mut ClusterContext<'_, C, L>` constructed by the orchestrator. In `ClusterContext::Cluster` mode (the cluster-processing flow), `ctx.current_symbol_table()` returns a `View<'_, C, L>` unioning staging + live (staging-first); `ctx.current_symbol_table_mut()` returns `&mut staging`. Typecheck calls these accessors uniformly — the 91 register-call sites in `program.rs` (e.g., `register_type_def`, `register_trait_decl`, `register_defn_signature`, `register_mono_entry`) and the 51 read access sites continue to use the existing API; the staging-vs-live distinction is absorbed inside the accessors. `ClusterContext` lives in `cranelisp-typecheck`.
- `symbol_tables` — read-only access to all other modules' tables for resolving FQ symbol references (`m2/foo`) and FQ type references (`m2/SomeType`). Generic over `<C, L>` per Decision 32 — typecheck is C/L-blind in production (caller passes `SymbolTables<Code, ()>`), and tests / fine-grained drivers pass `SymbolTables<(), ()>`.

Returns (both passes):
- `Ok(())` on success — entries Pass 1 staged are visible via the View for Pass 2; Pass 2 entries supersede Pass 1's shells in staging. The orchestrator commits the whole staging table atomically into live on cluster completion (Pass 2 `Ok` for every `ParsedEntry`).
- `Err(CheckError::Gap(ResolutionGap::SymbolTypechecked(fq)))` when an FQ value reference cannot be resolved (its module is not yet typechecked). The orchestrator catches, registers `fq.module` if needed, calls `wait_for_typecheck_symbol(fq)`, and retries the same pass with the same `ParsedEntry`. Per the gap-return pattern in `facades/int.md`.
- `Err(CheckError::Gap(ResolutionGap::Type(fqt)))` — same pattern for FQ type references. The orchestrator registers `fqt.module` if needed and calls `wait_for_typecheck_type(fqt)`.
- `Err(CheckError::TypeError { message, location })` — genuine type errors (non-recoverable). The orchestrator drops the staging table on the floor when the function frame returns; the live table is byte-identical to its pre-cluster state. `location: ErrorLocation` per Decision 39.

**Post-Gap state contract (per FIXME 0160 + Decision 44 + FIXME 0167 amendment).** On `Err`, no live mutation has occurred — the orchestrator commits only on whole-cluster Pass-2 success. Staging may carry partial entries written before the Gap; the orchestrator does NOT roll staging back on a Gap because the same pass is about to be retried with the same `ParsedEntry` and the same accessors will overwrite. On `Err(TypeError)`, the orchestrator drops staging and propagates the error; the live table is unchanged. On a Gap return, the orchestrator dispatches via `handle_gap` and retries the same pass. `ReplSnapshot` remains the type-var-pool rollback primitive within `CheckState` between calls (multi-form cluster processing); the live table is unaffected by either error return because no pass writes live, and staging dissolves with the function frame on TypeError.

Both passes ask for `ResolutionGap::SymbolTypechecked` (not `SymbolInMemory`) for value references because typecheck only needs the entry's `Scheme`, not its compiled code. Macro expansion's need for code happens earlier, in `frontend::expand` — by the time either pass runs, any macros have already been expanded out.

**Cluster atomicity**. The orchestrator drives Pass 1 across every `ParsedEntry` in the cluster, then Pass 2 across every `ParsedEntry` in the cluster, then commits the staging table atomically into the live `SymbolTable` on success. A cluster is one form (REPL non-`begin` input), the contents of `(begin form₁ … formN)` (REPL explicit cluster), or a file's non-structural forms (batch). See `facades/int.md` §"`process_cluster` — the cluster-atomic orchestration loop" for the orchestrator side.

### Per-form-pass scaffolding (called from within both pass functions — exposed for finer-grained callers)

```rust
pub struct CheckState { /* per-call state — type-var pool, substitution, deferred resolutions */ }

impl CheckState {
    pub fn new<C, L>(symbol_tables: &SymbolTables<C, L>) -> Self;
}

pub enum ClusterContext<'a, C: CodeStore, L: LinkerStore> {
    Live { modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>> },
    Cluster {
        modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,
        staging: &'a mut SymbolTable<C, L>,
        current_module: ModuleFullPath,
    },
}

impl<'a, C: CodeStore, L: LinkerStore> ClusterContext<'a, C, L> {
    pub fn current_symbol_table(&self) -> View<'_, C, L>;            // Cluster → View::union(staging, live); Live → single
    pub fn current_symbol_table_mut(&mut self) -> &mut SymbolTable<C, L>;  // Cluster → &mut staging; Live → &mut live[current]
}

pub struct TypeCheckEnv<'a, C, L> { /* per-form environment — wraps &mut ClusterContext + read-only symbol_tables */ }

impl<'a, C, L> TypeCheckEnv<'a, C, L> {
    pub fn new(ctx: &'a mut ClusterContext<'a, C, L>, symbol_tables: &'a SymbolTables<C, L>) -> Self;
    pub fn next_type_id(&mut self) -> TypeId;
}

pub enum CheckPass { Pass1Signatures, Pass2Bodies }                         // current internal multi-pass shape — visible because tests assert per-pass behaviour
pub struct FormCheckResult { /* per-form internal product — accumulated by ModuleCheckAccumulator */ }
pub struct ModuleCheckAccumulator { /* whole-module accumulator — used by tests; not the per-form path */ }
```

These exist for tests and for crates that want to drive typecheck at finer granularity than the two-pass surface. `int` uses `check_form_signatures` + `check_form_body` exclusively in production. `TypeCheckEnv` carries `&mut ClusterContext<'_, C, L>` per Decision 38 + Decision 44 (amended FIXME 0167) — table access flows through `ClusterContext::current_symbol_table()` (read) / `current_symbol_table_mut()` (write) so the 91 register-call sites and 51 access sites in `program.rs` do not change individually. In production cluster-processing flow, the orchestrator hands `ClusterContext::Cluster { staging, … }`; in REPL introspection / fine-grained-test paths the caller may construct `ClusterContext::Live { modules }` for direct live access. Per-symbol writes in committed (Live) mode go through the inner DashMap's per-key locks; in cluster mode they go through the `&mut staging` exclusive borrow held by the orchestrator's stack frame.

### Builtin registration (called once per `SymbolTable::new`)

```rust
pub fn register_builtins<C, L>(table: &mut SymbolTable<C, L>);
```

Builtin registration runs at `SymbolTable` construction time on the initiator thread, while a brief `&mut` window is held — this is one of the two `&mut SymbolTable` operations per Decision 38 (the other is `write_structural_decls` at parse-time Phase 0).

Seeds the symbol table with primitive type defs (`Int`, `Bool`, `String`, `Float`, `Unit`), primitive functions (per `cranelisp_types::primitives()`), and the synthetic `primitives`/`macros` modules' contents per `spec/08-modules.md §8.7`. Idempotent — safe to call once per fresh `SymbolTable`.

### Trace hooks (for diagnostics — observability layer)

```rust
pub use trace::{install_symbol_table_ensure_hook, /* … */};
```

Exposes the cross-crate trace-install hook described in `design/int/heisenbug-race-closure.md §3d''` — `int`'s observability layer wires this to its scheduler trace sink at startup.

### Public consts

None.

---

## Types originated here

Per Principle 15's placement heuristic — `CheckResult`, `CheckError`, `FormCheckResult`, `CheckPass`, `CheckState`, `TypeCheckEnv`, `ClusterContext`, `ModuleCheckAccumulator`, and `ReplSnapshot` live in `cranelisp-typecheck` (referenced by `int` only — single implementation-crate consumer). `ResolutionGap` is the cross-cutting exception: it is referenced by the frontend facade (`ExpansionError::Gap`) and the typecheck facade (`CheckError::Gap`), so it lives in `cranelisp-types` per the multi-consumer rule. `int` pattern-matches both gap-bearing errors against the same shared variants. `View<'a, C, L>` lives in `cranelisp-types` (multi-consumer at the boundary type level — see `facades/types.md` §"`View<'a, C, L>`"); `ClusterContext` consumes it via the read accessor.

```rust
// In cranelisp-typecheck:
pub struct CheckResult { /* annotated_ast, scheme, callees, method_resolutions, type_defs, mono_defns */ }
pub enum   CheckError { Gap(ResolutionGap), TypeError { message, location: ErrorLocation } }
pub struct FormCheckResult { /* … */ }                // per-form internal product (for fine-grained callers + tests)
pub enum   CheckPass { Pass1Signatures, Pass2Bodies }
pub struct CheckState { /* … */ }
pub enum   ClusterContext<'a, C, L> { Live { … }, Cluster { … } }   // Decision 44 (amended FIXME 0167) — staging-vs-live abstraction
pub struct TypeCheckEnv<'a, C, L> { /* … */ }
pub struct ModuleCheckAccumulator { /* … */ }
pub struct ReplSnapshot { /* … */ }                   // typecheck snapshot/restore primitive for REPL eval rollback

// In cranelisp-types (multi-consumer):
pub enum ResolutionGap {
    /// Symbol's typecheck not yet complete — orchestrator waits for `notify_symbol_typechecked(fq)`.
    /// Produced by either pass of `cranelisp_typecheck`'s two-pass surface
    /// (`check_form_signatures` + `check_form_body`, per Decision 44) for FQ value references
    /// whose target module has not finished typechecking. (Macros are already expanded by the
    /// time either pass runs, so this variant is never produced from typecheck for macro lookups;
    /// `MacroInMem` is the macro-side variant produced by frontend's `expand`.)
    SymbolTypechecked(FQSymbol),
    /// Macro target needs in-mem JIT — orchestrator does `ensure_registered` +
    /// `wait_for_typecheck_symbol`, peeks at the entry, and if it's a Macro with `code` missing
    /// additionally `priority_boost_jit(fq)` + `wait_for_inmem(fq)`. One retry round-trip
    /// regardless of macro-vs-fn. Produced exclusively by `cranelisp_frontend::expand`.
    MacroInMem(FQSymbol),
    /// Type reference needs typecheck — orchestrator waits for `notify_type_resolved(fqt)`.
    /// Produced by either pass of `cranelisp_typecheck`'s two-pass surface for FQ type
    /// references in `TypeExpr::Named` / `TypeExpr::Applied` whose target module has not
    /// finished typechecking.
    Type(FQTypeName),
}
```

The multi-consumer types `CheckResult` depends on (`Scheme`, `Subst`, `Type`, `TypeId`, `ResolvedCall`, `MethodResolutions`, `ConstructorInfo`, `FieldInfo`, `TypeDefInfo`, `DisplayInfo`, `MonoDefn`) live in `cranelisp-types` because backend codegen also consumes them — see Principle 15's placement heuristic. `CheckError::TypeError.location: ErrorLocation` carries Decision 39's coordinates-as-data carrier; `int`'s formatter resolves through `shared.introspection[fq].source` for inline source snippets in REPL/trace mode (per Decision 38's mode-conditional Introspection store).

No re-exports of `cranelisp-types` items per Principle 15 — `int` imports `Type`, `Scheme`, `Symbol`, `ResolutionGap` etc. from `cranelisp-types` and `CheckResult`, `CheckError`, etc. from `cranelisp-typecheck`.

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

`CheckState`, `TypeCheckEnv`, `ClusterContext`, `CheckPass`, `FormCheckResult`, `ModuleCheckAccumulator` are all `#[non_exhaustive]`. (Types re-exported from `cranelisp-types` are `#[non_exhaustive]` per the types-crate facade.)

---

## Bounded-context invariants

These hold across sprints — the contract `cranelisp-typecheck` makes with the rest of the workspace:

1. **No code generation.** Typecheck never invokes Cranelift, never produces JIT or object output. Its product is annotated AST + symbol-table entries.
2. **No commits to live `SymbolTable` from `check_form_signatures` / `check_form_body`.** Per FIXME 0160 resolution + Decision 44 (amended FIXME 0167 for Approach B + ClusterContext) — both passes are pure with respect to **live state**: neither mutates the live `SymbolTable` nor any state visible outside the cluster. Both passes MAY mutate the orchestrator-handed staging `SymbolTable` via the same accessor API used in committed-mode (`ctx.current_symbol_table_mut()`); typecheck cannot distinguish staging from live because the accessor abstracts the difference. The 91 register-call sites in `program.rs` and the 51 read access sites continue to use the existing API; the `ClusterContext` accessors are the single point of staging-vs-live surgery. Cluster atomicity is preserved because staging is orchestrator-local and is committed (drained into live) only on Pass-2 success across all forms. The caller (`int::process_cluster`) drops staging on the floor on any `Err(TypeError)`; on `Err(Gap)` the orchestrator dispatches and retries the same pass with the same `ParsedEntry` (staging may carry partial writes from before the Gap; the retry overwrites). The live table is byte-identical to its pre-cluster state across any failure — this is what makes the temp-closure path in REPL eval work, and what preserves Decision 44's structural intent (Principle 1 decoupling + Principle 7 single durable source of truth) without requiring a multi-week inversion of every register-call site. Resolved import bindings are installed by `int` (post-cluster Ok arm) via `SymbolTable::install_import_bindings(&self, …)`; this is `int`'s call, not typecheck's.
3. **Single source of truth via `defined_symbols()`.** Per Decision 22 — the codegen-compilable predicate is `SymbolTable::defined_symbols()`. Typecheck writes entries that satisfy or fail this predicate; it does not maintain a parallel store.
4. **TC-sourced call graph.** Per Decision 21 — call graph edges are extracted during typechecking from method resolutions. `CheckResult.callees: Vec<FQSymbol>` is the per-symbol call graph; the rich `CallGraph` (with tail-position info) is for within-module codegen analysis.
5. **Trait method dispatch via `ResolvedCall::TraitMethod`.** Typecheck always emits `TraitMethod` for trait-dispatched operators; backend handles lowering. Typecheck stays clean of backend-specific concerns. The prior `(TraitName, Symbol, TypeName) → primitive` collusion-table approach in backend is retired per Decision 43 — backend has no trait knowledge; primitive emission goes through `cranelisp-primitives` + `cranelisp-intrinsics` directly.
6. **Constraint propagation in `generalize`.** Per Decision 19 — `Scheme.constraints` is populated by collecting trait constraints from active type variables during generalisation. Non-empty constraints mark a constrained polymorphic function (monomorphised at call sites).
7. **TC snapshot/restore for error rollback.** Both pass functions allocate type vars within `CheckState`; the symbol-table writes that pre-S66 stages performed are gone (FIXME 0160 + Decision 44 — both passes are pure). On `Err`, `int` (or the caller) restores via `ReplSnapshot` before the next pass is invoked. Typecheck provides the snapshot/restore primitive but does not invoke it itself; the caller decides when to take and restore snapshots. (REPL eval is the primary consumer — a failed cluster must not leave residual type-var bindings visible to the next eval.) The orchestrator's transient staging table (per Decision 44) is the layer that absorbs cross-pass write-side intent — it is not visible to typecheck and is dropped on cluster failure.
8. **FQ resolution surfaces via `CheckError::Gap`.** Per the gap-return pattern (`facades/int.md`, `exec-flow-compilation`) — when either pass encounters an FQ symbol or FQ type reference whose target isn't typechecked, it returns `Err(CheckError::Gap(ResolutionGap::SymbolTypechecked(fq)))` or `Err(CheckError::Gap(ResolutionGap::Type(fqt)))`. Typecheck does NOT block, does NOT call the scheduler, does NOT register modules — it surfaces the dependency to its caller (`int::process_cluster`), which dispatches via `handle_gap` and retries the same pass.
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
    // Multi-module aggregation is composed at the orchestrator (session/REPL) layer, not inside check_form*.
    ```

    Mutating writes always go through `ctx.current_symbol_table_mut()` — a typecheck pass MUST NOT mutate a foreign module's table directly. `ModuleEntry::TraitImpl` writes target the **trait's defining module** per Decision 0045; the orchestrator selects the target table by chain-following the trait reference at write time, identically to the read side. Cross-module impl writes that pre-S66 source carries (~6 sites in `builtins.rs` + `checker.rs`, audited 2026-05-12) are Wave 3a-α retargets per Decision 0046 — the redo retargets to the trait's home, not the writer's home. This invariant is the structural prerequisite for invariant 2's cluster-atomic guarantee — the `ClusterContext` accessor surgery only delivers cluster atomicity if every read and write actually flows through it; the absence of orphaned `self.modules.X` pierces is what makes that the case.
