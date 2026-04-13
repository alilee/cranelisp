# TraitImpl on SymbolTable: Design and Impl Search Strategy

Design sketch for making trait implementations first-class module entries and defining how impl lookup works after `ImplRegistry` deletion. Part of Sprint 51 (Stateless TypeChecker).

## Problem

Today, trait impls exist only in the global `ImplRegistry` — a `HashMap<TraitName, HashMap<TypeName, RegisteredImpl>>` on `TypeChecker`. They are NOT recorded as entries on any module's `SymbolTable`. This creates several problems:

1. **Global mutable state on TC**: `ImplRegistry` is one of three `RwLock` registries that make the TypeChecker stateful. Deleting it requires an alternative lookup mechanism.

2. **Cache reconstruction is fragile**: `restore_cached_impls()` reconstructs the `ImplRegistry` by parsing mangled JIT symbol names (`"Num.+$Int"` → trait=Num, impl_type=Int). This reverse-engineering is brittle and loses information (e.g., polymorphic impl type args, method-to-primitive mappings).

3. **No module provenance**: `RegisteredImpl` records `(trait_name, impl_type)` but not which module the impl was defined in. With no orphan rules (spec §7.12.1), impls can be anywhere. Without module provenance, you cannot reason about impl visibility or detect conflicting impls from different modules.

4. **Inconsistency with other definitions**: Type defs have `ModuleEntry::TypeDef`. Trait decls have `ModuleEntry::TraitDecl`. Constructors have `ModuleEntry::Constructor`. But impls are invisible to the module system — they only exist as a side effect in a global registry.

## Proposed `ModuleEntry::TraitImpl`

Add a new variant to `ModuleEntry`:

```rust
ModuleEntry::TraitImpl {
    trait_name: FQTraitName,
    impl_type: FQTypeName,
    /// Method names defined in this impl (local names, not mangled).
    /// Used for impl search — you need to know which methods an impl covers.
    methods: Vec<Symbol>,
    /// Visibility is always Public (spec §5.11).
    /// Not stored as a field — `is_public()` returns true unconditionally for this variant.
}
```

### Key for SymbolTable insertion

SymbolTables are `HashMap<Symbol, ModuleEntry>`. The key for a `TraitImpl` entry is a synthetic name encoding the fully qualified trait-type pair:

```
impl$primitives/Int$core.num/Num
impl$user/Option$core.formats/Display
impl$user/Option$core.collections/Functor
```

Format: `impl${FQTypeName}${FQTraitName}`. Type-first ordering so lexicographic sorting groups all impls for a type together. Fully qualified to avoid bare-name collisions. The `$` separator cannot appear in user-defined symbols.

The mangled method Def entries on the same SymbolTable follow the same type-first convention:

```
impl$primitives/Int$core.num/Num       ← TraitImpl metadata entry
impl$primitives/Int$core.num/Num.+     ← method Def entry
impl$primitives/Int$core.num/Num.-     ← method Def entry
impl$primitives/Int$core.num/Num.*     ← method Def entry
```

The fully qualified form `implementing_module/impl$type/Type$trait/Trait.method` gives O(1) lookup when the implementing module is known.

### Fields rationale

- **`trait_name: FQTraitName`**: Identifies which trait is being implemented, with module qualification. Used during search. Fully qualified so search can distinguish same-named traits from different modules.
- **`impl_type: FQTypeName`**: The concrete type this impl covers. Fully qualified so backend and display code can use it directly. For impls in the type's own module, the module matches `table.path`. For orphan impls, the module references the type's defining module.
- **`methods: Vec<Symbol>`**: The method names this impl provides. Needed because:
  - An impl may cover only some methods (defaults fill the rest).
  - Search needs to verify the impl covers the specific method being resolved.
  - During cache restoration, method names are available from the SymbolTable.

### Why not store method bodies / primitives mapping?

The impl entry records the *existence* of the impl and which methods it covers. The actual method implementations are already stored as `ModuleEntry::Def` entries with mangled names (`Num.+$Int`). The impl entry serves as an index — "this module has an impl of Num for Int covering methods +, -, *" — not as a container for method code.

## Impl search strategy

The central question: when resolving `(+ x y)` where `x: Int`, how do you find the concrete method `Num.+$Int` without a global registry?

### Key insight: impls are loaded, not imported

Impls are NOT imported through the module system. You don't write `(import [core.num [impl$Num$Int]])`. Impls are a side effect of loading a module — when the scheduler compiles a module containing `(impl Num Int ...)`, the mangled method `Def` entries (`Num.+$Int`, etc.) and the `TraitImpl` metadata entry are registered on that module's SymbolTable.

Spec §5.11: "`impl` has no private variant. Trait implementations are always visible wherever both the trait and the type are in scope."

The visibility rule is: **an impl is visible if the module containing it has been loaded.** Not "imported" — loaded. The scheduler's module dependency graph determines which modules are loaded. Any loaded module's impls are potentially in play.

### What the search actually looks for

The search target is a **concrete mangled method Def**, not the abstract impl relationship. When resolving `(+ x y)` where `x: Int`:

- You know: trait = `core.num/Num`, method = `+`, dispatch type = `primitives/Int`
- The mangled name is deterministic: `Num.+$Int`
- You're scanning loaded modules for a `ModuleEntry::Def` keyed by `Num.+$Int`
- The `ModuleEntry::TraitImpl` is an index that helps find which module has it, but the Def is what matters

You don't need to know anything else about how the impl was formed (default methods vs explicit, polymorphic vs concrete). The mangled Def entry is the compiled, concrete result.

### Full resolution path: `(+ x y)` where `x: Int`

1. **Resolve `+` in scope**: Follow import chain from current module. Find `ModuleEntry::Def` for `+` with scheme `(Fn [a a] a)` constrained `{a: [core.num/Num]}`. Note the trait `FQTraitName("core.num", "Num")`.

2. **Resolve dispatch type**: Unify `a` with the concrete argument type → `Int`. Now seeking mangled method: `Num.+$Int`.

3. **Scan loaded modules for `Num.+$Int`**: Search all loaded modules' SymbolTables for a `Def` keyed `Num.+$Int`.

   **Search order (heuristic for fast path):**
   
   a. **Trait's defining module** (`core.num`): Core impls typically live alongside the trait declaration. `impl Num Int` is usually defined in the same module as `deftrait Num`.
   
   b. **Type's defining module** (for ADTs): `impl Display Point` is typically in the module where `Point` is defined.
   
   c. **All other loaded modules**: Fallback full scan. Required for orphan impls (spec §7.12.1: "No orphan rules").
   
   In practice, (a) and (b) cover >99% of cases. The full scan is a fallback.

4. **Found**: Module `core.num` has `Def` keyed `impl$primitives/Int$core.num/Num.+`. The fully qualified call target is `core.num/impl$primitives/Int$core.num/Num.+`. Emit `ResolvedCall::TraitMethod { trait_name: FQTraitName("core.num", "Num"), method_name: "+", impl_type: FQTypeName("primitives", "Int"), mangled_name: "impl$primitives/Int$core.num/Num.+", defining_module: "core.num" }`.

### Loaded-modules scan

The full scan (step 3c) covers all modules the scheduler has loaded. This is bounded:

- The number of loaded modules is typically small (10-50 for real programs).
- Each module's SymbolTable has at most a handful of impl-related entries.
- Scanning is O(loaded_modules * entries_per_module) which is small.
- For performance-critical paths, a per-check-invocation cache `HashMap<(FQTraitName, FQTypeName), (ModuleFullPath, Symbol)>` (mapping trait+type to defining module + mangled name) avoids repeated scans within a single type-check pass.

### What about orphan impls?

Spec §7.12.1: "No orphan rules." Any module can define an impl for any trait-type pair.

Example: `stdlib/json.cl` defines `(impl Display JsonValue ...)` — the Display trait is in `core.formats`, the JsonValue type is in `json`, and the impl is also in `json`. This is the heuristic step (b) (type's defining module).

More exotic: a third module `my-app.cl` defines `(impl MyTrait SomeLibType ...)` where neither MyTrait's module nor SomeLibType's module is the impl's home. This hits the full scan (step 3c). It works because the scheduler loaded `my-app.cl` — the impl's Def entries are on its SymbolTable.

An impl in an *unloaded* module has no effect. This is correct — if the module isn't loaded, its code hasn't been compiled, so there's no Def to call.

### Duplicate impls — conflict detection

Duplicate impls are errors, detected at two levels:

**1. Same module, same impl**: Defining `(impl Num Foo ...)` twice in the same module is an error at typecheck time, just like defining the same function name twice. The second `TraitImpl` entry would have the same synthetic key and be rejected.

**2. Different modules, same impl**: Two loaded modules both define `(impl Num Foo ...)`. This is an error at module load time — analogous to how importing the same bare symbol from two different modules causes an ambiguity error. Loading a module that re-implements an already-registered trait-type pair is an error.

**Session-level impl index**: To detect cross-module duplicates at load time without scanning all SymbolTables, maintain an index on the session:

```rust
/// Maps (FQTypeName, FQTraitName) → implementing module.
/// Type-first key order matches the mangled name convention.
/// Populated when a module's TraitImpl entries are registered.
/// Duplicate registration is an error.
impl_index: HashMap<(FQTypeName, FQTraitName), ModuleFullPath>
```

This lives on SharedState (or CompilerSession — it's session-scoped shared state). When a module is loaded and its `TraitImpl` entries are processed, each is checked against the index. If the `(trait, type)` pair already maps to a different module, emit:

```
error: conflicting trait impl — impl core.num/Num for primitives/Foo
  defined in mod1 and mod2
```

This index also serves as the fast-path for resolution — step 3 of the resolution path becomes an O(1) lookup:

```rust
// Step 3: find the implementing module
let impl_module = shared.impl_index.get(&(fq_type, fq_trait))
    .ok_or_else(|| no_impl_error(trait_name, impl_type, span))?;

// Step 4: look up the mangled Def on that module's SymbolTable
let mangled = format!("impl${}${}.{}",
    fq_type, fq_trait, method_name);
let def = shared.symbol_tables.get(impl_module)
    .and_then(|table| table.get(&mangled.into()))?;
```

The heuristic scan (trait's module first, type's module second, full scan) is no longer needed — the index gives O(1) access. The index is also useful for introspection (`/info Num` lists all impls).

**Cache-hit loading**: When a cached module is restored, its `TraitImpl` entries are registered in the impl index. A conflict detected during cache-hit loading means the cache is stale (a new module added a conflicting impl since the cache was written). Invalidate and recompile.

## What happens to `ImplRegistry.has_impl()` — the call sites

`has_impl()` is called at ~9 sites. Each maps to a module-system query:

| Call site | Current purpose | Replacement |
|-----------|----------------|-------------|
| `register_trait_impl()` line 464 | Register new impl | Insert `ModuleEntry::TraitImpl` on current module's SymbolTable |
| `try_resolve_trait_method()` line 808 | Check impl exists before resolving | Search for `TraitImpl` in trait's module, type's module, loaded modules |
| `verify_constraints()` line 990 | Verify constrained type has required impls | Same search as above |
| `restore_cached_impls()` line 1460 | Skip already-registered impls during cache restore | Check if `TraitImpl` entry already exists on the module's SymbolTable |
| Tests (lines 1738, 1742, 1854, 1855) | Test assertions | Assert `TraitImpl` entry exists on SymbolTable |

The replacement in each case is a helper function:

```rust
/// Search for a trait impl across loaded modules.
fn find_trait_impl(
    modules: &DashMap<ModuleFullPath, SymbolTable>,
    trait_name: &FQTraitName,
    impl_type: &FQTypeName,
    search_scope: &[ModuleFullPath],  // modules to search
) -> Option<ModuleFullPath>  // module where impl was found
```

Or a simpler targeted check:

```rust
/// Check if a specific module has a TraitImpl entry.
fn module_has_impl(
    table: &SymbolTable,
    trait_name: &FQTraitName,
    impl_type_name: &TypeName,
) -> bool {
    let key = Symbol::from(format!("impl${}${}", trait_name, impl_type_name));
    matches!(table.get(&key), Some(ModuleEntry::TraitImpl { .. }))
}
```

## What happens to `restore_cached_module()`

Currently `restore_cached_module()` reconstructs registries from SymbolTable entries:

- **TypeDef/Constructor** → `TypeDefRegistry` entries — **deleted** (registry eliminated)
- **TraitDecl** → `TraitRegistry` entries — **deleted** (registry eliminated)

After migration, `restore_cached_module()` just installs the SymbolTable on `SharedState.modules`. The SymbolTable already contains `ModuleEntry::TraitImpl` entries (serialized to/from `.meta.json`). No reconstruction needed.

The `restore_cached_impls()` method (which reverse-engineers impls from mangled JIT names) is deleted entirely. The `TraitImpl` entries are the source of truth, serialized alongside the rest of the SymbolTable.

This is a significant simplification — the cache path and the fresh-compilation path produce the same data structure (SymbolTable with TraitImpl entries), rather than fresh compilation populating a registry and cache reconstruction reverse-engineering it.

## What happens to `register_trait_impl()`

Currently `register_trait_impl()` does:

1. Validate the impl (trait exists, methods present, types match)
2. Generate default method implementations
3. Insert into `ImplRegistry`
4. Type-check each method body
5. Return generated `Defn` nodes

After migration, step 3 changes:

```rust
// Before (step 3):
self.impl_registry.write().unwrap().impls
    .entry(impl_.trait_name.clone())
    .or_default()
    .insert(impl_.target_type.clone(), RegisteredImpl { ... });

// After (step 3):
let impl_key = Symbol::from(format!("impl${}${}", impl_.trait_name, impl_.target_type));
let fq_impl_type = FQTypeName::new(
    state.current_module.clone(),
    impl_.target_type.clone(),
);
state.current_symbol_table_mut().insert(impl_key, ModuleEntry::TraitImpl {
    trait_name: impl_.trait_name.clone(),
    impl_type: fq_impl_type,
    methods: impl_.methods.iter().map(|m| m.name.clone()).collect(),
});
```

The method `Defn` entries (mangled names like `Num.+$Int`) continue to be inserted as `ModuleEntry::Def` on the same SymbolTable, as they are today. The `TraitImpl` entry is the *index*; the `Def` entries are the *implementations*.

## TraitRegistry disposition

`TraitRegistry` holds two maps:
- `decls: HashMap<TraitName, TraitDecl>` — trait declarations
- `method_to_trait: HashMap<Symbol, TraitName>` — reverse lookup from method name to trait

**`decls`** is already redundant with `ModuleEntry::TraitDecl` on SymbolTables. Lookups change from `trait_registry.decls.get(&name)` to a module-system search: find the `TraitDecl` entry by following import chains from the current module.

**`method_to_trait`** is a convenience index. It can be reconstructed on demand: given a method name like `+`, resolve it through the module system. If the `ModuleEntry::Def` for `+` came from a module that has a `ModuleEntry::TraitDecl` containing `+` in its methods, that's the trait. Alternatively, this mapping can be kept as a transient per-check-invocation cache.

## Sketch comparison

The sketch stores impls directly on `CompiledModule`:

```rust
// sketch/src/module.rs (simplified)
pub struct CompiledModule {
    pub impls: Vec<TraitImpl>,
    // ... many other fields
}
```

The sketch's `all_impls()` method flat-maps across ALL loaded modules:

```rust
fn all_impls(&self) -> impl Iterator<Item = &TraitImpl> {
    self.modules.values().flat_map(|cm| cm.impls.iter())
}
```

And `find_impl_for_type()` iterates through `all_impls()` checking `trait_name` and `target_type` for each, with a priority order: concrete ADT match → bare match → polymorphic match.

**What the sketch gets right**: Impls live on per-module data structures, not in a separate global registry. The scan across modules is conceptually sound.

**What the sketch gets wrong**: The scan is unbounded — it checks every impl in every module regardless of import relationships. This works in the sketch because it has a single `HashMap<ModuleFullPath, CompiledModule>` that's small. But it's semantically wrong — an impl in an unimported module should not affect the current compilation.

**Divergence**: The reimplementation improves on the sketch in two ways:
1. Impls are `ModuleEntry::TraitImpl` entries on `SymbolTable` rather than a `Vec<TraitImpl>` on a god object — participates in the module system like every other definition.
2. Impl search is scoped to the import graph rather than scanning all loaded modules — semantically correct and will scale to larger programs.

The reimplementation follows the sketch's core insight (impls are per-module data) but fixes the lookup to use import-scoped search instead of global scan.

## Open questions

1. **Synthetic key naming**: The `impl$Trait$Type` naming convention for SymbolTable keys is a proposal. Alternative: use a separate map on `SymbolTable` (e.g., `impl_entries: Vec<TraitImplEntry>`) instead of stuffing impls into the `symbols` HashMap. The separate map avoids polluting symbol lookups but adds a new field to `SymbolTable` and requires updating serialization. The synthetic-key approach keeps everything in one map but introduces a naming convention. Which is preferable?

2. **Polymorphic impls**: `(impl Display (Option :Display a) ...)` targets `Option` with a type variable constraint. The `impl_type: FQTypeName` in the proposed `TraitImpl` variant stores just the base type name (`Option`), not the type args or constraints. Is this sufficient for search? Yes — the search matches on base type name, and the constraint checking happens after the impl is found (during method type-checking). But this should be verified against the polymorphic impl resolution path.

3. **`method_to_trait` replacement**: The `TraitRegistry.method_to_trait` reverse index is used in `try_resolve_trait_method()` to quickly determine if a name is a trait method. Without it, every method call would need to scan TraitDecl entries. Options:
   - Build a transient `method_to_trait` map at the start of each `check()` invocation from the current module's imported TraitDecls.
   - Store the mapping on `ModuleEntry::Def` entries for trait methods (add a `trait_origin: Option<FQTraitName>` field).
   - Accept the scan cost — number of TraitDecls in scope is small.

4. **Performance of impl search**: Is the per-check-invocation cache necessary, or is the loaded-modules scan fast enough? The sketch's `all_impls()` scan works fine at current scale. Add caching only if profiling shows it's needed.

## Resolved questions

- **Import vs loading**: Impls are loaded, not imported. Visibility rule is "module has been loaded by the scheduler." See "Key insight" section.
- **Search target**: The search finds a concrete mangled `Def` entry (`impl$primitives/Int$core.num/Num.+`), not the abstract impl relationship. `TraitImpl` is an index/metadata entry. The FQ key includes implementing module, FQ trait member, and FQ type — avoids all bare-name collisions.
- **Conflicting impls**: Detected at load time via session-level `impl_index`. Duplicate impl registration across modules is an error (like importing the same bare name from two modules). Same-module duplicate is a typecheck error. See "Duplicate impls" section.
- **Search scope construction**: O(1) via `impl_index` on SharedState. No scan needed. Index populated at module load time (both fresh compilation and cache-hit restoration).
- **Qualified disambiguation for duplicate impls**: Not needed for Sprint 51 — duplicate impls are simply errors. Qualified references (`mod1/Num.+ x y`) noted as a possible future feature if the spec evolves to permit controlled duplicate impls.
