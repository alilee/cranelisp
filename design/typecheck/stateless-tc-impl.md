# Stateless TypeChecker: Implementation Design

Sprint 51 critical path. This document covers how to make the `cranelisp-typecheck` crate stateless by extracting persistent state to `SharedState` and replacing registry lookups with module-system queries.

## 1. State extraction

The `TypeChecker` struct currently has 7 fields. Each moves as follows:

### `modules: DashMap<ModuleFullPath, SymbolTable>`

**Moves to**: SharedState (already session-scoped shared state).

The DashMap is the most important piece. It is the canonical store for all per-module symbol information. After extraction, every TC method that currently reads `self.modules` takes a `&DashMap<ModuleFullPath, SymbolTable>` parameter (or a wrapper reference like `&SharedState`).

**Key call sites**: `current_symbol_table()`, `current_symbol_table_mut()`, `ensure_module_exists()`, `lookup()`, `resolve_fq_symbol()`, `register_imports()`, `restore_cached_module()`. These all become functions (or methods on a stateless struct) that take the modules map as a parameter.

**REPL snapshot/restore** (`snapshot()`, `restore()`) currently reach into `self.modules` to snapshot/rollback symbol table entries. These move to the session layer, which owns the DashMap.

### `type_defs: RwLock<TypeDefRegistry>`

**Moves to**: DELETED. Replaced by `ModuleEntry::TypeDef` lookups on SymbolTables.

The `TypeDefRegistry` is a derived cache of data already present on per-module SymbolTables. Every `register_type_def()` call writes both the registry AND a `ModuleEntry::TypeDef` entry. The registry is redundant.

After deletion, `known_type_names()` (used by `resolve_type_expr` for ADT lookup + arity validation) must scan SymbolTables instead. See section 2 for details.

### `trait_registry: RwLock<TraitRegistry>`

**Moves to**: DELETED. Replaced by `ModuleEntry::TraitDecl` lookups + a transient `method_to_trait` cache.

The `TraitRegistry` stores `decls` (redundant with `ModuleEntry::TraitDecl`) and `method_to_trait` (a convenience reverse index). See section 2 for the replacement pattern.

### `impl_registry: RwLock<ImplRegistry>`

**Moves to**: DELETED. Replaced by `ModuleEntry::TraitImpl` entries on SymbolTables + `impl_index` on SharedState.

Per `traitimpl-symbol-table.md`, the session-level `impl_index: HashMap<(FQTypeName, FQTraitName), ModuleFullPath>` provides O(1) lookup. The `ImplRegistry`'s `has_impl()` becomes an `impl_index.contains_key()` call.

### `next_id: AtomicU32`

**Moves to**: SharedState (session-scoped).

The TypeId counter must be globally unique across all concurrent TC invocations. It is already `AtomicU32` with lock-free `fetch_add`. Moving it to SharedState is trivial — pass `&AtomicU32` to all `fresh_var()` / `fresh_var_id()` calls.

Alternatively, keep it as a field on a lightweight `TypeCheckEnv` struct that wraps references to SharedState fields. The key point is that it is not owned by any single check invocation.

### `module_locks: Mutex<HashMap<ModuleFullPath, Arc<AtomicBool>>>`

**Moves to**: Scheduler (or SharedState).

Module compilation locks are a scheduling concern, not a typechecking concern. The scheduler already decides which modules to compile and in what order. `try_lock_module()` and `ModuleGuard` move out of the TC entirely.

### `state: CheckState`

**Moves to**: Stack-local (per check invocation). See section 5.

The `CheckState` is already conceptually per-invocation. The only reason it lives on `TypeChecker` is for REPL additive mode, where three fields persist across evals: `subst`, `env`, and `overloads`/`resolved_overloads`. See section 5 for the solution.

## 2. Registry elimination

### TypeDefRegistry replacement

Currently `TypeDefRegistry` is used for:

1. **`known_type_names()`** — builds `HashMap<TypeName, usize>` for `resolve_type_expr`. Called 6 times across the crate.
2. **`get(name)`** — looks up a `TypeDefInfo` by bare `TypeName`. Used in `register_trait_impl` for HKT arity checks, in match exhaustiveness, and in constructor resolution.
3. **`constructor_type(ctor_name)`** — reverse lookup from constructor to parent type. Used in match codegen and pattern checking.
4. **`is_internal_constructor()`** — checks the `internal` flag.

**Replacement pattern for `known_type_names()`**: Build the map by scanning the SymbolTables for `ModuleEntry::TypeDef` entries in modules that are in scope (current module's import chain + loaded modules). With `FQTypeName`, the scan returns `HashMap<FQTypeName, usize>` instead of bare `TypeName`.

This is the trickiest replacement because `resolve_type_expr` currently works with bare `TypeName` keys. After FQTypeName migration, `resolve_type_expr` needs module context to resolve a bare name like `"Option"` to `FQTypeName("core.option", "Option")`. The resolution path becomes:

1. Check primitive types (no module needed — dedicated `Type` variants).
2. Look up bare name in current module's SymbolTable. If found as `ModuleEntry::TypeDef { info, .. }`, use `FQTypeName::new(info_module, name)`.
3. Follow import chains (same as variable lookup — the module system already does this).

This means `resolve_type_expr` gains a `modules` parameter and a `current_module` parameter. Its signature changes from:

```rust
fn resolve_type_expr(texpr, var_map, known_types, span) -> Result<Type>
// to:
fn resolve_type_expr(texpr, var_map, modules, current_module, span) -> Result<Type>
```

**Replacement for `get(name)` and `constructor_type()`**: Follow the same module-system lookup path. Given `FQTypeName`, look up the module's SymbolTable and extract the `TypeDefInfo` from `ModuleEntry::TypeDef`. Given a constructor name, look it up in the current module's SymbolTable; the `ModuleEntry::Constructor { type_name, .. }` carries the parent type name (migrating to `FQTypeName`).

**Replacement for `is_internal_constructor()`**: Same module lookup. The `internal` flag is on `ConstructorInfo` within the `TypeDefInfo`.

### TraitRegistry replacement

**`decls` map**: Redundant with `ModuleEntry::TraitDecl` on SymbolTables. Replace `trait_registry.read().decls.get(&name)` with a module-system lookup: resolve `name` in the current module's scope, follow import chains to find the `ModuleEntry::TraitDecl`.

**`method_to_trait` reverse index**: This is used in `try_resolve_trait_method()` to quickly determine whether a method name belongs to a trait. Without it, resolving `+` would require scanning all in-scope TraitDecl entries for a method named `+`.

Three options (from `traitimpl-symbol-table.md` open question 3):

1. **Build a transient cache at the start of each `check()` invocation.** Scan imported TraitDecls, build `HashMap<Symbol, FQTraitName>`. Cost: O(imported_traits * methods_per_trait) per module check. Typically small (<50 entries).
2. **Store `trait_origin: Option<FQTraitName>` on `ModuleEntry::Def`** for trait method entries. The information is already known at registration time. This turns the reverse lookup into a field read.
3. **Accept the scan cost.** Number of TraitDecls in scope is small.

**Decision: Option 2.** When `register_trait_method` creates the `ModuleEntry::Def` for a trait method, add a `trait_origin` field. This is the cleanest solution — no transient caches, no scans, and the information flows through the existing module system (imports propagate it). The `ModuleEntry::Def` already has `kind: Box<DefKind>` which could carry this, but a top-level field is more explicit.

Concretely, add to `ModuleEntry::Def`:
```rust
/// If this def is a trait method, the defining trait. None for regular fns.
trait_origin: Option<FQTraitName>,
```

This replaces `method_to_trait` lookups with: resolve the name, check `trait_origin` on the resulting `ModuleEntry::Def`.

### ImplRegistry replacement

Per `traitimpl-symbol-table.md`:

- `has_impl(trait_name, impl_type)` becomes `impl_index.contains_key(&(fq_type, fq_trait))`.
- `register_trait_impl()` step 3 (insert into ImplRegistry) becomes: insert `ModuleEntry::TraitImpl` on current module's SymbolTable + register in `impl_index`.
- `restore_cached_impls()` is deleted entirely — cached SymbolTables already contain `TraitImpl` entries, and cache restore populates the `impl_index` from them.

### Walk-through of registration methods

**`register_type_def()`**: Currently writes to `TypeDefRegistry` AND inserts `ModuleEntry::TypeDef`. After: writes ONLY `ModuleEntry::TypeDef`. The pre-seed for recursive types (line 116-124 in adt.rs) inserts a placeholder `ModuleEntry::TypeDef` instead of a placeholder in `type_defs` HashMap. `known_type_names()` scans SymbolTables, so the placeholder is immediately visible.

**`register_trait_decl()`**: Currently writes to `TraitRegistry.decls` and `.method_to_trait`, AND inserts `ModuleEntry::TraitDecl`. After: writes ONLY `ModuleEntry::TraitDecl` and sets `trait_origin` on method Def entries. The duplicate check (`decls.contains_key`) becomes a SymbolTable key check.

**`register_trait_impl()`**: Currently writes to `ImplRegistry`. After: inserts `ModuleEntry::TraitImpl` + registers in `impl_index`. The trait decl lookup (`trait_registry.read().decls.get(&impl_.trait_name)`) becomes a module-system lookup.

## 3. FQTypeName migration within the typecheck crate

### Construction sites

There are ~114 `Type::ADT(` occurrences in the typecheck crate. They fall into patterns:

**Pattern A — Registration (`register_type_def`)**: Line 110 in adt.rs constructs `Type::ADT(name.clone(), type_args)`. After: `Type::ADT(FQTypeName::new(state.current_module.clone(), name.clone()), type_args)`. The module is `state.current_module`, always available.

**Pattern B — Constructor lookup (inference)**: When a constructor like `Some` is used in code, the typechecker looks it up via the module system and finds `ModuleEntry::Constructor { type_name, scheme, .. }`. The constructor's scheme already contains the ADT type with the correct type name. After FQTypeName migration, the scheme carries `FQTypeName` — no change needed at the lookup site, only at the registration site (Pattern A).

**Pattern C — `resolve_type_expr`**: `resolve_named()` (line 69 in resolve.rs) constructs `Type::ADT(name.clone(), vec![])` for zero-arg ADTs. After: needs module context. The function must resolve the bare name through the module system to determine which module defines the type, then construct `Type::ADT(FQTypeName::new(defining_module, name), vec![])`.

**Pattern D — Builtins**: builtins.rs has ~55 `Type::ADT(` sites, mostly for synthetic types (Sexp, SList, IO, Trace, TestResult). These use known module paths: `"macros"` for Sexp/SList, `"primitives"` for IO/Trace. After: `Type::ADT(FQTypeName::new(ModuleFullPath::from("macros"), TypeName::from("Sexp")), vec![])`. Verbose but mechanical.

**Pattern E — Tests**: ~20 sites in test code construct `Type::ADT(TypeName::from("Color"), vec![])`. After: use a test helper `Type::test_adt("Color")` that uses `ModuleFullPath::from("test")`.

### `resolve_type_expr()` changes

Current signature:
```rust
fn resolve_type_expr(texpr, var_map, known_types, span) -> Result<Type>
```

New signature:
```rust
fn resolve_type_expr(texpr, var_map, modules, current_module, span) -> Result<Type>
```

The `known_types: HashMap<TypeName, usize>` parameter is eliminated. Instead, `resolve_named()` and `resolve_applied()` look up the name in the current module's SymbolTable (following import chains). When they find a `ModuleEntry::TypeDef { info, .. }`, they read the type parameter count from `info.type_params.len()` and the defining module from the SymbolTable path where the entry was found.

This is the highest-risk change in the crate because `resolve_type_expr` is called from 6 sites, and each must now provide the modules map and current module.

### Unification

`unify()` in unify.rs matches `(Type::ADT(name1, args1), Type::ADT(name2, args2))`. Currently compares bare `TypeName` (line 48: `if name1 != name2`).

After: compares `FQTypeName` (module + name). This is the correct behavior — `user/Point` and `geometry/Point` are different types. The `PartialEq` derive on `FQTypeName` gives field-wise comparison automatically. No logic change needed, just the type change.

The `TyConApp` vs `ADT` unification (lines 71-85) binds the constructor variable to `Type::ADT(name.clone(), vec![])`. After: `Type::ADT(fqtn.clone(), vec![])` — the FQTypeName is cloned directly. Same semantics.

### Constraints

`Scheme.constraints: HashMap<TypeId, Vec<TraitName>>` migrates to `HashMap<TypeId, Vec<FQTraitName>>`.

`ActiveConstraints` stores `HashMap<TypeId, Vec<TraitName>>` — same migration to `Vec<FQTraitName>`.

At `register_trait_method()`, where constraints are created (line 313 in traits.rs), the `trait_name` is currently bare `TraitName`. After: `FQTraitName::new(state.current_module.clone(), trait_name.clone())`. The module is the one where the trait is being defined.

At `generalize()` (checker.rs line 818), constraints are propagated from `ActiveConstraints` to `Scheme.constraints`. No structural change — the types flow through.

At `verify_constraints()` (called during monomorphisation), each constraint's `FQTraitName` is used to look up the impl via `impl_index`. Currently uses bare `TraitName` + `ImplRegistry.has_impl()`. After: `impl_index.contains_key(&(fq_type, fq_trait))`.

## 4. New public API

### Exported types

The crate exports:
- `CheckState` — per-invocation state (created by caller, passed to check functions)
- `CheckPass`, `FormCheckResult`, `ModuleCheckAccumulator` — per-form API types
- `ModuleGuard` — DELETED (moves to scheduler)

### Stateless struct vs free functions

**Decision: Keep a lightweight `TypeCheckEnv` struct** that holds immutable references to shared state. This avoids threading 4-5 parameters through every internal function.

```rust
/// Immutable references to shared state needed for type checking.
/// No owned mutable state — all mutation goes through CheckState
/// or DashMap interior mutability.
pub struct TypeCheckEnv<'a> {
    pub modules: &'a DashMap<ModuleFullPath, SymbolTable>,
    pub impl_index: &'a HashMap<(FQTypeName, FQTraitName), ModuleFullPath>,
    pub next_id: &'a AtomicU32,
}
```

All current `TypeChecker` methods become methods on `TypeCheckEnv`. The struct is trivially constructible (just references) and carries no mutable state.

### `check_form()` signature

```rust
impl<'a> TypeCheckEnv<'a> {
    pub fn check_form(
        &self,
        state: &mut CheckState,
        module: &ModuleFullPath,
        form: &TopLevel,
        pass: CheckPass,
        accumulator: &mut ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError>;
}
```

The `&mut self` → `&self` conversion is the main payoff. Multiple workers can hold `TypeCheckEnv` references concurrently (it's `Send + Sync` because it holds shared references + atomics). Each worker has its own `CheckState` on the stack.

### Test helper

```rust
#[cfg(test)]
fn test_env() -> (DashMap<ModuleFullPath, SymbolTable>, TypeCheckEnv<'static>) {
    // Build shared state with builtins registered, return env
}
```

Or simpler — a `TestFixture` struct that owns the DashMap and hands out `TypeCheckEnv` references:

```rust
#[cfg(test)]
struct TestFixture {
    modules: DashMap<ModuleFullPath, SymbolTable>,
    impl_index: HashMap<(FQTypeName, FQTraitName), ModuleFullPath>,
    next_id: AtomicU32,
}

impl TestFixture {
    fn new() -> Self { /* register builtins */ }
    fn env(&self) -> TypeCheckEnv<'_> { /* borrow fields */ }
}
```

## 5. CheckState as stack-local

### Truly per-invocation fields

These fields are created fresh for each check and drained into the result:

- `expr_types` — accumulated, drained into `FormCheckResult`
- `method_resolutions` — accumulated, drained into `FormCheckResult`
- `warnings` — accumulated, drained into `FormCheckResult`
- `active_constraints` — populated during inference, consumed during generalize
- `in_call_position` — transient flag, reset between forms
- `pending_auto_curry` — accumulated within a form, resolved in finalize
- `pending_overload_resolutions` — same as above
- `module_aliases` — set during import processing, read during inference
- `current_module` — set once per check invocation

All of these are straightforwardly stack-local.

### Fields that persist across REPL evals

Three fields carry state between REPL evaluations:

1. **`subst: Subst`** — Unification bindings accumulate across REPL lines. `(let [x 3])` in one eval creates bindings that `x` references in the next eval.

2. **`env: ScopeStack`** — REPL top-level bindings persist. `(defn foo ...)` in one eval is visible in the next.

3. **`overloads` / `resolved_overloads`** — Multi-sig registrations accumulate across evals.

**Solution**: These persistent REPL fields live on the session (e.g., on `ReplSession` or a dedicated `ReplTypeState` struct on SharedState). For batch compilation, they are empty / fresh. For REPL mode, the session constructs a `CheckState` that includes the persistent fields before each eval, and extracts them back after.

```rust
/// REPL-persistent typecheck state. Lives on the session.
pub struct ReplTypeState {
    pub subst: Subst,
    pub env: ScopeStack,
    pub overloads: HashMap<Symbol, Vec<(Symbol, usize)>>,
    pub resolved_overloads: HashMap<Symbol, Vec<(Vec<Type>, Type, Symbol)>>,
}
```

The flow for a REPL eval:
1. Session builds `CheckState` incorporating `ReplTypeState` fields.
2. TC processes the form (using `&TypeCheckEnv` + `&mut CheckState`).
3. Session extracts the persistent fields back from `CheckState` into `ReplTypeState`.
4. Transient fields (`expr_types`, `method_resolutions`, etc.) are drained into the result.

### `take_state()` / `restore_state()` pattern

This pattern exists solely because `CheckState` lives on `TypeChecker`. With stack-local `CheckState`, the pattern is unnecessary — the caller already holds `&mut CheckState` separately from `&TypeCheckEnv`. The `SymbolTableMacroResolver` (worker.rs line 352) that motivated this pattern simply receives `&TypeCheckEnv` and `&mut CheckState` as separate parameters. No take/restore needed.

## 6. Migration risks

### Hardest part: `resolve_type_expr` threading

The biggest challenge is threading module context through `resolve_type_expr`. It is called from 6 sites, and each of those sites is called from multiple parents. The `known_types` parameter is easy to construct today (`TypeDefRegistry.known_types()` — a simple HashMap copy). The replacement requires access to the modules DashMap and the current module path.

The mitigant is that every call site already has access to `&TypeChecker` (which owns the DashMap) and `&CheckState` (which has `current_module`). After migration, they pass `&self.modules` (or `&env.modules`) and `&state.current_module`. The parameter change is mechanical.

### Borrow-checker challenge: DashMap guards

The crate already solved the DashMap borrow-splitting challenge in Sprint 50 (see `dashmap-migration.md`). The "clone-and-drop discipline" is established: clone entries from guards, drop the guard, then process. With `TypeCheckEnv` holding `&DashMap`, this discipline continues unchanged.

The one new challenge: `resolve_type_expr` now reads the DashMap (to find TypeDef entries). If a caller holds a write guard on the current module's SymbolTable while calling `resolve_type_expr`, and `resolve_type_expr` tries to read the same shard, DashMap will deadlock. This already applies to all `lookup()` calls — the existing crate has solved it by always dropping guards before calling methods that read other guards. Same discipline applies.

### Ordering of changes

**Phase 1: FQTypeName + FQTraitName in cranelisp-types** (boundary crate). Add the new types, change `Type::ADT`, `Scheme.constraints`, etc. Tree breaks.

**Phase 2: Fix typecheck crate** (largest blast radius — 114 `Type::ADT` sites).
- 2a: Update `resolve_type_expr` to take module context, resolve bare names to FQTypeName.
- 2b: Update `register_type_def`, `register_trait_decl`, `register_trait_impl` to use FQTypeName/FQTraitName.
- 2c: Update unification (mechanical — `TypeName` → `FQTypeName` in patterns).
- 2d: Update builtins (mechanical — add module paths to all `Type::ADT` constructions).
- 2e: Update tests (use test helper).

**Phase 3: Delete registries**.
- 3a: Delete `TypeDefRegistry`. Replace `known_type_names()` with SymbolTable scan. Remove `type_defs` field.
- 3b: Delete `TraitRegistry`. Add `trait_origin` field to `ModuleEntry::Def`. Remove `trait_registry` field.
- 3c: Delete `ImplRegistry`. Add `ModuleEntry::TraitImpl` support. Replace `has_impl()` calls with `impl_index` lookups. Remove `impl_registry` field.

**Phase 4: Extract remaining state**.
- 4a: Move `modules` to SharedState. TypeChecker becomes `TypeCheckEnv` with references.
- 4b: Move `next_id` to SharedState.
- 4c: Move `module_locks` to scheduler.
- 4d: Make `CheckState` stack-local. Extract REPL-persistent fields to `ReplTypeState`.
- 4e: Delete `take_state()` / `restore_state()`.

**Phase 5: Fix backend and integration crates** (downstream consumers of changed types).

Phases 2 and 3 are the most work but are internal to the typecheck crate. Phase 1 and 5 are the blast-radius phases that break other crates. Phase 4 is the structural payoff.

The FQTypeName change (Phases 1-2) and the registry deletion (Phase 3) can be done in the same commit since the tree is already broken by Phase 1. Phase 4 (state extraction) is a separate, cleaner change once the registries are gone.

### Risk: cache compatibility

Existing `.meta.json` cache files serialize `TypeName` (bare strings) inside `Type::ADT`. After migration, they serialize `FQTypeName`. Old caches are incompatible. The cache should detect this and invalidate. Source-hash changes will naturally trigger recompilation for modified modules, but unmodified modules with valid source hashes but incompatible type serialization need explicit version bumping. Add a version field to the cache format, or simply clear the cache on first run after migration.

## Sketch comparison

The sketch (`sketch/src/typechecker.rs`) uses a monolithic `TypeChecker` struct with all state mixed together:

```rust
pub struct TypeChecker {
    next_id: TypeId,
    subst: Subst,
    local_env: HashMap<Symbol, Scheme>,
    pending_resolutions: Vec<...>,
    overloads: HashMap<...>,
    // ... all state in one struct
}
```

There is no state separation — per-invocation and persistent state are interleaved. The sketch never attempted to make the typechecker stateless because it was a single-threaded prototype with no pipeline concurrency.

The sketch also uses bare string type names everywhere (`Type::ADT(String, Vec<Type>)`), with no module qualification. It has `qualify_adt_name()` for display-time module recovery and `all_impls()` for global impl scans — both are derived lookups that the reimplementation eliminates by embedding module context at construction time.

**Divergence**: The reimplementation takes a fundamentally different approach:
1. **State split**: Persistent shared state (modules, next_id) separated from per-invocation transient state (subst, env, resolutions). The sketch has no such split.
2. **Module-qualified types**: `FQTypeName` eliminates derived caches and prevents name collisions. The sketch never attempted this.
3. **Registry-free**: Type/trait/impl information lives on SymbolTables (single source of truth). The sketch duplicates this information across `CompiledModule` fields and typechecker-internal HashMaps.

The reimplementation follows the sketch's Algorithm W core (unification, instantiation, generalization) but diverges completely on state management, which is the subject of this design.
