# Facade spec — `crates/cranelisp-typecheck/`

**Bounded context citation.** AST → typed AST + symbol tables. Owns Hindley-Milner inference, trait resolution, and monomorphisation analysis. Does not produce code. See `bounded-contexts.md` §2 — Typecheck.

This spec is **target-stating**. Drift detection between as-designed and as-built is the job of `cargo-public-api` (M4-pending) and `/review`'s per-PR audit, not this document.

---

## Public surface (as-designed)

### Free functions — the two-pass per-form check

The typecheck entry surface used by `int`'s shared `process_cluster` (see `facades/int.md`). Per Decision 44, the per-form check splits into two pure passes that the orchestrator drives across every form in a cluster: Pass 1 across all forms, then Pass 2 across all forms. Both passes are pure (FIXME 0160 structural Option B holds for both); orchestrator-owned staging is invisible to typecheck — it sees only a `View<'a, C, L>` read surface.

```rust
pub fn check_form_signatures<C, L>(
    parsed: ParsedEntry,
    table: &View<'_, C, L>,                       // staging ∪ live composite read view (orchestrator-constructed)
    symbol_tables: &SymbolTables<C, L>,
) -> Result<Vec<(Symbol, ModuleEntry<C>)>, CheckError>;

pub fn check_form_body<C, L>(
    parsed: ParsedEntry,
    table: &View<'_, C, L>,                       // staging ∪ live; cluster signatures from Pass 1 are visible
    symbol_tables: &SymbolTables<C, L>,
) -> Result<Vec<(Symbol, ModuleEntry<C>)>, CheckError>;
```

Parameters:
- `parsed` — the parse-time-only `ParsedEntry` produced by `cranelisp_frontend::build_form` (per FIXME 0156 resolution). One `build_form` call may produce multiple `ParsedEntry` items (e.g., a multi-clause `defmacro` yields one per clause); the orchestrator drives both passes once per `ParsedEntry`. The same `ParsedEntry` instance is passed to Pass 2 that was passed to Pass 1 — `ParsedEntry` persists across both passes within one cluster's processing (see `facades/types.md` §"`ParsedEntry`").
- `table` — the read surface, a `View<'_, C, L>` newtype constructed by the orchestrator (`int::process_cluster`) wrapping `(staging, live)` symbol tables. Lookups route staging-first then live; both passes call `table.lookup(name)` and get an answer regardless of where the entry resides. Typecheck does not know whether it is reading staging, live, or unioned content. `View` lives in `cranelisp-types` per the `View<'_, C, L>` boundary-type entry in `facades/types.md`.
- `symbol_tables` — read-only access to all other modules' tables for resolving FQ symbol references (`m2/foo`) and FQ type references (`m2/SomeType`). Generic over `<C, L>` per Decision 32 — typecheck is C/L-blind in production (caller passes `SymbolTables<Code, ()>`), and tests / fine-grained drivers pass `SymbolTables<(), ()>`.

Returns (both passes):
- `Ok(Vec<(Symbol, ModuleEntry<C>)>)` on success — the entries the orchestrator should write into the staging table for this pass. Pass 1 returns signature-only `ModuleEntry` shells (Algorithm W fresh return-type variables; bodies un-checked); Pass 2 returns body-checked entries that supersede Pass 1's shells (and may include additional entries — multi-sig variants, mono specializations, ADT per-constructor entries, multi-clause macro entries). Each pass overwrites Pass-1 shells with their Pass-2 counterparts in the staging table.
- `Err(CheckError::Gap(ResolutionGap::SymbolTypechecked(fq)))` when an FQ value reference cannot be resolved (its module is not yet typechecked). The orchestrator catches, registers `fq.module` if needed, calls `wait_for_typecheck_symbol(fq)`, and retries the same pass with the same `ParsedEntry`. Per the gap-return pattern in `facades/int.md`.
- `Err(CheckError::Gap(ResolutionGap::Type(fqt)))` — same pattern for FQ type references. The orchestrator registers `fqt.module` if needed and calls `wait_for_typecheck_type(fqt)`.
- `Err(CheckError::TypeError { message, location })` — genuine type errors (non-recoverable). The orchestrator drops the staging table on the floor; the live table is byte-identical to its pre-cluster state. `location: ErrorLocation` per Decision 39.

**Post-Gap state contract (per FIXME 0160 + Decision 44): structural Option B, applied per pass.** Both passes are pure; on `Err` nothing has been written — neither to the live table (the orchestrator commits only at cluster end) nor to staging (the orchestrator commits each pass's `Ok` returns to staging only on `Ok`). On a Gap return, the orchestrator dispatches and retries the same pass with the same `ParsedEntry`; on a TypeError, the orchestrator drops staging and propagates the error. `ReplSnapshot` remains the type-var-pool rollback primitive within `CheckState` between calls (multi-form cluster processing); the `View` and the underlying tables are unaffected by either error return because neither pass wrote.

Both passes ask for `ResolutionGap::SymbolTypechecked` (not `SymbolInMemory`) for value references because typecheck only needs the entry's `Scheme`, not its compiled code. Macro expansion's need for code happens earlier, in `frontend::expand` — by the time either pass runs, any macros have already been expanded out.

**Cluster atomicity**. The orchestrator drives Pass 1 across every `ParsedEntry` in the cluster, then Pass 2 across every `ParsedEntry` in the cluster, then commits the staging table atomically into the live `SymbolTable` on success. A cluster is one form (REPL non-`begin` input), the contents of `(begin form₁ … formN)` (REPL explicit cluster), or a file's non-structural forms (batch). See `facades/int.md` §"`process_cluster` — the cluster-atomic orchestration loop" for the orchestrator side.

### Per-form-pass scaffolding (called from within both pass functions — exposed for finer-grained callers)

```rust
pub struct CheckState { /* per-call state — type-var pool, substitution, deferred resolutions */ }

impl CheckState {
    pub fn new<C, L>(symbol_tables: &SymbolTables<C, L>) -> Self;
}

pub struct TypeCheckEnv<'a, C, L> { /* per-form environment — wraps shared symbol table + read-only symbol_tables */ }

impl<'a, C, L> TypeCheckEnv<'a, C, L> {
    pub fn new(table: &'a SymbolTable<C, L>, symbol_tables: &'a SymbolTables<C, L>) -> Self;
    pub fn next_type_id(&mut self) -> TypeId;
}

pub enum CheckPass { Pass1Signatures, Pass2Bodies }                         // current internal multi-pass shape — visible because tests assert per-pass behaviour
pub struct FormCheckResult { /* per-form internal product — accumulated by ModuleCheckAccumulator */ }
pub struct ModuleCheckAccumulator { /* whole-module accumulator — used by tests; not the per-form path */ }
```

These exist for tests and for crates that want to drive typecheck at finer granularity than the two-pass surface. `int` uses `check_form_signatures` + `check_form_body` exclusively in production. `TypeCheckEnv` carries a shared `&View<'_, C, L>` per Decision 38 + Decision 44 — concurrent forms may share access via the View's underlying `&SymbolTable` refs; per-symbol writes (in tests that opt to mutate directly) go through the inner DashMap's per-key locks.

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

Per Principle 15's placement heuristic — `CheckResult`, `CheckError`, `FormCheckResult`, `CheckPass`, `CheckState`, `TypeCheckEnv`, `ModuleCheckAccumulator`, and `ReplSnapshot` live in `cranelisp-typecheck` (referenced by `int` only — single implementation-crate consumer). `ResolutionGap` is the cross-cutting exception: it is referenced by the frontend facade (`ExpansionError::Gap`) and the typecheck facade (`CheckError::Gap`), so it lives in `cranelisp-types` per the multi-consumer rule. `int` pattern-matches both gap-bearing errors against the same shared variants.

```rust
// In cranelisp-typecheck:
pub struct CheckResult { /* annotated_ast, scheme, callees, method_resolutions, type_defs, mono_defns */ }
pub enum   CheckError { Gap(ResolutionGap), TypeError { message, location: ErrorLocation } }
pub struct FormCheckResult { /* … */ }                // per-form internal product (for fine-grained callers + tests)
pub enum   CheckPass { Pass1Signatures, Pass2Bodies }
pub struct CheckState { /* … */ }
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

`CheckState`, `TypeCheckEnv`, `CheckPass`, `FormCheckResult`, `ModuleCheckAccumulator` are all `#[non_exhaustive]`. (Types re-exported from `cranelisp-types` are `#[non_exhaustive]` per the types-crate facade.)

---

## Bounded-context invariants

These hold across sprints — the contract `cranelisp-typecheck` makes with the rest of the workspace:

1. **No code generation.** Typecheck never invokes Cranelift, never produces JIT or object output. Its product is annotated AST + symbol-table entries.
2. **No commits to `SymbolTable` from `check_form_signatures` / `check_form_body`.** Per FIXME 0160 resolution + Decision 44 — both passes are pure functions: `(ParsedEntry, &View<'_, C, L>, &SymbolTables) → Result<Vec<(Symbol, ModuleEntry)>, CheckError>`. Neither calls `insert_or_update`, neither installs import bindings, neither mutates any `SymbolTable` (live or staging). The caller (`int::process_cluster`) writes returned entries into staging on each pass's `Ok` and commits the staging table atomically into the live `SymbolTable` only on whole-cluster success. On `Err(Gap | TypeError)` from any pass, no mutation has occurred — the orchestrator either retries the same pass (Gap) or drops staging on the floor (TypeError); the live table is byte-identical to its pre-cluster state. This is what makes the temp-closure path in REPL eval work — for expression evals the orchestrator runs the cluster (one form) without committing to a module (per `facades/int.md` and `exec-flow-repl`). Resolved import bindings are installed by `int` (post-cluster Ok arm) via `SymbolTable::install_import_bindings(&self, …)`; this is `int`'s call, not typecheck's.
3. **Single source of truth via `defined_symbols()`.** Per Decision 22 — the codegen-compilable predicate is `SymbolTable::defined_symbols()`. Typecheck writes entries that satisfy or fail this predicate; it does not maintain a parallel store.
4. **TC-sourced call graph.** Per Decision 21 — call graph edges are extracted during typechecking from method resolutions. `CheckResult.callees: Vec<FQSymbol>` is the per-symbol call graph; the rich `CallGraph` (with tail-position info) is for within-module codegen analysis.
5. **Trait method dispatch via `ResolvedCall::TraitMethod`.** Typecheck always emits `TraitMethod` for trait-dispatched operators; backend handles lowering. Typecheck stays clean of backend-specific concerns. The prior `(TraitName, Symbol, TypeName) → primitive` collusion-table approach in backend is retired per Decision 43 — backend has no trait knowledge; primitive emission goes through `cranelisp-primitives` + `cranelisp-intrinsics` directly.
6. **Constraint propagation in `generalize`.** Per Decision 19 — `Scheme.constraints` is populated by collecting trait constraints from active type variables during generalisation. Non-empty constraints mark a constrained polymorphic function (monomorphised at call sites).
7. **TC snapshot/restore for error rollback.** Both pass functions allocate type vars within `CheckState`; the symbol-table writes that pre-S66 stages performed are gone (FIXME 0160 + Decision 44 — both passes are pure). On `Err`, `int` (or the caller) restores via `ReplSnapshot` before the next pass is invoked. Typecheck provides the snapshot/restore primitive but does not invoke it itself; the caller decides when to take and restore snapshots. (REPL eval is the primary consumer — a failed cluster must not leave residual type-var bindings visible to the next eval.) The orchestrator's transient staging table (per Decision 44) is the layer that absorbs cross-pass write-side intent — it is not visible to typecheck and is dropped on cluster failure.
8. **FQ resolution surfaces via `CheckError::Gap`.** Per the gap-return pattern (`facades/int.md`, `exec-flow-compilation`) — when either pass encounters an FQ symbol or FQ type reference whose target isn't typechecked, it returns `Err(CheckError::Gap(ResolutionGap::SymbolTypechecked(fq)))` or `Err(CheckError::Gap(ResolutionGap::Type(fqt)))`. Typecheck does NOT block, does NOT call the scheduler, does NOT register modules — it surfaces the dependency to its caller (`int::process_cluster`), which dispatches via `handle_gap` and retries the same pass.
9. **No `Sess` / `CompileScheduler` dependency.** Same as frontend — typecheck stays a pure function from inputs (`ParsedEntry`, `SymbolTable`, `SymbolTables`) to outputs (`Vec<(Symbol, ModuleEntry)>` or `CheckError`). Principle 3.
