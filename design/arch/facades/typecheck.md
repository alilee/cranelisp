# Facade spec — `crates/cranelisp-typecheck/`

**Bounded context citation.** AST → typed AST + symbol tables. Owns Hindley-Milner inference, trait resolution, and monomorphisation analysis. Does not produce code. See `bounded-contexts.md` §2 — Typecheck.

This spec is **target-stating**. Drift detection between as-designed and as-built is the job of `cargo-public-api` (M4-pending) and `/review`'s per-PR audit, not this document.

---

## Public surface (as-designed)

### Free function — the per-form check

The single typecheck entry point used by `int`'s shared `process_form` (see `facades/int.md`). Compilation worker invokes once per form; REPL eval invokes once per parsed input form.

```rust
pub fn check_form(
    node: Ast,
    table: &mut SymbolTable<Code, ()>,
    symbol_tables: &SymbolTables,
) -> Result<CheckResult, CheckError>;
```

Parameters:
- `node` — the AST produced by `cranelisp_frontend::build_ast`. Untyped on entry; annotated in place during inference.
- `table` — the typecheck target's own symbol table. `check_form` reads it for forward-resolved local names and may emit type-var allocations against it. Does NOT call `insert_or_update` — committing the new entry is the caller's job (via `int::insert_symbol`).
- `symbol_tables` — read-only access to all other modules' tables for resolving FQ symbol references (`m2/foo`) and FQ type references (`m2/SomeType`).

Returns:
- `Ok(CheckResult)` on success — the annotated AST + scheme + callees + resolved method calls + monomorphisation requests.
- `Err(CheckError::Gap(ResolutionGap::SymbolTypechecked(fq)))` when an FQ value reference cannot be resolved (its module is not yet typechecked). The orchestrator (`int::process_form`) catches this, registers `fq.module` if needed, calls `wait_for_typecheck_symbol(fq)`, and retries `check_form`. Per the gap-return pattern in `facades/int.md`.
- `Err(CheckError::Gap(ResolutionGap::Type(fqt)))` — same pattern for FQ type references. The orchestrator registers `fqt.module` if needed and calls `wait_for_typecheck_type(fqt)`.
- `Err(CheckError::TypeError { … })` — genuine type errors (non-recoverable; eval rolls back the inference state per `pipeline-v4.md §6.2` via `ReplSnapshot`).

`check_form` asks for `ResolutionGap::SymbolTypechecked` (not `SymbolInMemory`) for value references because typecheck only needs the entry's `Scheme`, not its compiled code. Macro expansion's need for code happens earlier, in `frontend::expand` — by the time `check_form` runs, any macros have already been expanded out.

### Per-form-pass scaffolding (called from within `check_form`'s body — exposed for finer-grained callers)

```rust
pub struct CheckState { /* per-call state — type-var pool, substitution, deferred resolutions */ }

impl CheckState {
    pub fn new(symbol_tables: &SymbolTables) -> Self;
}

pub struct TypeCheckEnv<'a> { /* per-form environment — wraps mutable symbol table + read-only symbol_tables */ }

impl<'a> TypeCheckEnv<'a> {
    pub fn new(table: &'a mut SymbolTable<Code, ()>, symbol_tables: &'a SymbolTables) -> Self;
    pub fn next_type_id(&mut self) -> TypeId;
}

pub enum CheckPass { Pass1Signatures, Pass2Bodies }                         // current internal multi-pass shape — visible because tests assert per-pass behaviour
pub struct FormCheckResult { /* per-form internal product — accumulated by ModuleCheckAccumulator */ }
pub struct ModuleCheckAccumulator { /* whole-module accumulator — used by tests; not the per-form path */ }
```

These exist for tests and for crates that want to drive typecheck at finer granularity than `check_form`. `int` uses `check_form` exclusively in production.

### Builtin registration (called once per `SymbolTable::new`)

```rust
pub fn register_builtins(table: &mut SymbolTable<Code, ()>);
```

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

Per Principle 15 — these types are typecheck-originated (only `int` consumes them downstream of typecheck) and live in `cranelisp-typecheck`, not `cranelisp-types`:

```rust
pub struct CheckResult { /* … */ }                    // top-level per-form check result + diagnostics
pub enum   CheckError { Gap(ResolutionGap), TypeError { … } }
pub enum   ResolutionGap { SymbolTypechecked(FQSymbol), MacroInMem(FQSymbol), Type(FQTypeName) }
pub struct FormCheckResult { /* … */ }                // per-form internal product (for fine-grained callers + tests)
pub enum   CheckPass { Pass1Signatures, Pass2Bodies }
pub struct CheckState { /* … */ }
pub struct TypeCheckEnv<'a> { /* … */ }
pub struct ModuleCheckAccumulator { /* … */ }
pub struct ReplSnapshot { /* … */ }                   // typecheck snapshot/restore primitive for REPL eval rollback
```

The multi-consumer types these depend on (`Scheme`, `Subst`, `Type`, `TypeId`, `ResolvedCall`, `MethodResolutions`, `ConstructorInfo`, `FieldInfo`, `TypeDefInfo`, `DisplayInfo`, `MonoDefn`) live in `cranelisp-types` because backend codegen also consumes them — see Principle 15's placement heuristic. Consumers import them from there directly.

No re-exports of `cranelisp-types` items per Principle 15 — `int` imports `Type`, `Scheme`, `Symbol`, etc. from `cranelisp-types` and `CheckResult`, `CheckError`, etc. from `cranelisp-typecheck`.

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
2. **No commits to `SymbolTable`.** `check_form` annotates `node` in place but does not call `insert_or_update`. The caller (`int::insert_symbol`) commits. This is what makes the temp-closure path in REPL eval work — `process_form` for an expression returns the typed AST without persisting it (per `facades/int.md` and `exec-flow-repl`).
3. **Single source of truth via `defined_symbols()`.** Per Decision 22 — the codegen-compilable predicate is `SymbolTable::defined_symbols()`. Typecheck writes entries that satisfy or fail this predicate; it does not maintain a parallel store.
4. **TC-sourced call graph.** Per Decision 21 — call graph edges are extracted during typechecking from method resolutions. `CheckResult.callees: Vec<FQSymbol>` is the per-symbol call graph; the rich `CallGraph` (with tail-position info) is for within-module codegen analysis.
5. **Trait method dispatch via `ResolvedCall::TraitMethod`.** Typecheck always emits `TraitMethod` for trait-dispatched operators; backend handles lowering. Typecheck stays clean of backend-specific concerns. (NB: the prior `(TraitName, Symbol, TypeName) → primitive` collusion-table approach in backend was retracted; the `cranelisp-runtime` → `cranelisp-primitives` + `cranelisp-intrinsics` crate split is the replacement direction, scheduled for a future sprint.)
6. **Constraint propagation in `generalize`.** Per Decision 19 — `Scheme.constraints` is populated by collecting trait constraints from active type variables during generalisation. Non-empty constraints mark a constrained polymorphic function (monomorphised at call sites).
7. **TC snapshot/restore for error rollback.** Per `pipeline-v4.md §6.2` — `check_form` allocates type vars and may write intermediate state; on `Err`, `int` (or the caller) restores via `ReplSnapshot` before the next form is processed. Typecheck provides the snapshot/restore primitive but does not invoke it itself; the caller decides when to take and restore snapshots.
8. **FQ resolution surfaces via `CheckError::Gap`.** Per the gap-return pattern (`facades/int.md`, `exec-flow-compilation`) — when `check_form` encounters an FQ symbol or FQ type reference whose target isn't typechecked, it returns `Err(CheckError::Gap(ResolutionGap::SymbolTypechecked(fq)))` or `Err(CheckError::Gap(ResolutionGap::Type(fqt)))`. Typecheck does NOT block, does NOT call the scheduler, does NOT register modules — it surfaces the dependency to its caller (`int::process_form`), which dispatches via `handle_gap` and retries.
9. **No `Sess` / `CompileScheduler` dependency.** Same as frontend — typecheck stays a pure function from inputs (Ast, SymbolTable, SymbolTables) to outputs (CheckResult or CheckError). Principle 3.
