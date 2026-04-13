# Sprint 51: FQTypeName Migration and Cache Fix — Backend Design

Backend implementation design for Sprint 51 changes: FQTypeName/FQTraitName migration, CheckResult field deletions, SymbolTable access pattern, cache manifest fix, and CodegenInput slimming.

Upstream designs: `design/arch/fqtypename.md`, `design/arch/traitimpl-symbol-table.md`.

## 1. CheckResult.type_defs and constructor_to_type Deletion

### Current state

`CompileContext` (in `compiler/mod.rs`) holds two borrowed HashMap references:

```rust
pub type_defs: &'a HashMap<TypeName, TypeDefInfo>,
pub constructor_to_type: &'a HashMap<Symbol, TypeName>,
```

These are cloned from `CheckResult` fields and threaded into every `FnCompiler` instance. Call sites span four files:

| File | Usage |
|------|-------|
| `compiler/match_codegen.rs` | `compile_constructor_pattern`: constructor lookup, tag info, `is_mixed_adt` |
| `compiler/match_codegen.rs` | `resolve_field_types`: constructor → type def → field types |
| `compiler/match_codegen.rs` | `dec_temporary_scrutinee`, `bind_data_pattern_fields`, data pattern auto-upgrade: `HeapCategory::classify(..., Some(self.ctx.type_defs))` |
| `compiler/literals.rs` | `nullary_constructor_tag`, `data_constructor_info`: tag/field lookup |
| `heap.rs` | `is_mixed_adt(type_defs, type_name)` |
| `display.rs` | `format_value`, `format_result_value`, `format_adt_value`, `format_field_value`, `format_vec_elements` — all take `&HashMap<TypeName, TypeDefInfo>` |
| `lib.rs` | `build_compile_context`, `compile_program` — clones from CheckResult |
| `cache/object.rs` | `ObjectCompileInput.type_defs`, `constructor_to_type` — snapshotted for .o codegen |

### Replacement: direct DashMap access

The backend crate adds `dashmap` as a dependency (the typecheck crate already depends on it). `CompileContext` holds a reference to the shared symbol tables DashMap directly:

```rust
// CompileContext changes:
// Before:
pub type_defs: &'a HashMap<TypeName, TypeDefInfo>,
pub constructor_to_type: &'a HashMap<Symbol, TypeName>,

// After:
pub symbol_tables: &'a DashMap<ModuleFullPath, SymbolTable>,
pub current_module: ModuleFullPath,
```

All type/constructor lookups go through the DashMap. No snapshot HashMaps, no derived caches, no traits. Single source of truth.

### Call site migration patterns

**match_codegen.rs — compile_constructor_pattern:**
```rust
// Before:
let type_name = self.ctx.constructor_to_type.get(bare_name)?;
let type_def = self.ctx.type_defs.get(type_name)?;

// After:
let table = self.ctx.symbol_tables.get(&self.ctx.current_module)?;
let ctor = match table.get(bare_name) {
    Some(ModuleEntry::Constructor { type_name: fqtn, info, .. }) => (fqtn, info),
    _ => return Err(...),
};
let type_table = self.ctx.symbol_tables.get(&fqtn.module)?;
let type_def = match type_table.get(&fqtn.name.as_symbol()) {
    Some(ModuleEntry::TypeDef { info, .. }) => info,
    _ => return Err(...),
};
```

**HeapCategory::classify:**
```rust
// Before:
HeapCategory::classify(&ty, Some(self.ctx.type_defs))

// After:
// HeapCategory::classify signature changes to take &DashMap:
HeapCategory::classify(&ty, Some(self.ctx.symbol_tables))
```

`HeapCategory::classify` in `cranelisp-types` changes its signature from `Option<&HashMap<TypeName, TypeDefInfo>>` to `Option<&DashMap<ModuleFullPath, SymbolTable>>`. It looks up type info via `ModuleEntry::TypeDef` when classifying ADT types. `cranelisp-types` adds `dashmap` as a dependency (it already depends on `serde`, `hashbrown` etc. — `dashmap` is a data structure, not a framework).

### heap.rs — is_mixed_adt

```rust
// Before:
pub fn is_mixed_adt(type_defs: &HashMap<TypeName, TypeDefInfo>, type_name: &TypeName) -> bool

// After:
pub fn is_mixed_adt(symbol_tables: &DashMap<ModuleFullPath, SymbolTable>, fqtn: &FQTypeName) -> bool {
    symbol_tables.get(&fqtn.module)
        .and_then(|table| match table.get(&fqtn.name.as_symbol()) {
            Some(ModuleEntry::TypeDef { info, .. }) => {
                let has_nullary = info.constructors.iter().any(|c| c.fields.is_empty());
                let has_data = info.constructors.iter().any(|c| !c.fields.is_empty());
                Some(has_nullary && has_data)
            }
            _ => None,
        })
        .unwrap_or(false)
}
```

## 2. FQTypeName Migration in Backend

### Type::ADT pattern match changes

Every `Type::ADT(name, args)` destructure becomes `Type::ADT(fqtn, args)` where `fqtn: FQTypeName`. The bare `name: TypeName` is replaced by `fqtn.name` when the local name is needed, or used as a full `FQTypeName` for lookups.

**Files affected:**
- `compiler/mod.rs`: `concrete_type_name()`, `build_mangled_name()`
- `compiler/match_codegen.rs`: `resolve_field_types()`, `dec_temporary_scrutinee()`
- `compiler/literals.rs`: `nullary_constructor_tag()`, `data_constructor_info()`
- `display.rs`: 10+ functions
- `heap.rs`: `is_mixed_adt()`
- `lib.rs`: `compile_program()`, `expand_multi_sig_defn()`
- `cache/object.rs`: `ObjectCompileInput`, test fixtures

All changes are mechanical: replace `name` with `fqtn` in destructuring, use `fqtn.name` where bare TypeName was needed (e.g., display, constructor matching), use full `fqtn` for lookups.

### Mangled name construction

**Current format**: `Num.+$Int` (trait name + method + dollar + type name)

**New format** (from `traitimpl-symbol-table.md`): `impl$primitives/Int$core.num/Num.+`

This change is in how mangled JIT symbols are constructed. The backend's `build_mangled_name` and `concrete_type_name` need updating:

```rust
// Before (in lib.rs):
fn concrete_type_name(ty: &Type) -> Option<TypeName> {
    match ty {
        Type::ADT(name, _) => Some(name.clone()),
        ...
    }
}

// After:
fn concrete_type_name(ty: &Type) -> Option<FQTypeName> {
    match ty {
        Type::ADT(fqtn, _) => Some(fqtn.clone()),
        Type::Int => Some(FQTypeName::new("primitives".into(), "Int".into())),
        Type::Float => Some(FQTypeName::new("primitives".into(), "Float".into())),
        Type::Bool => Some(FQTypeName::new("primitives".into(), "Bool".into())),
        Type::String => Some(FQTypeName::new("primitives".into(), "String".into())),
        _ => None,
    }
}
```

For multi-sig mangling (`name$Type1+Type2`), we use `fqtn.name` (local type name) in the mangled string since multi-sig dispatch is module-local. For trait method mangling, the new format uses FQ names.

**ResolvedCall::TraitMethod.mangled_name**: Already a `JitSymbol`. The typecheck crate generates the mangled name using the new `impl$FQType$FQTrait.method` format. The backend just uses the `mangled_name` field as-is for JIT lookup — no backend-side mangling logic change needed for trait methods.

### format_type_qualified() simplification

```rust
// Before:
pub fn format_type_qualified(ty: &Type, type_modules: &HashMap<TypeName, ModuleFullPath>) -> String

// After:
pub fn format_type_qualified(ty: &Type) -> String
```

The `type_modules` parameter is deleted. Inside the function:

```rust
// Before:
Type::ADT(name, args) => {
    let qname = qualify_type_name(name, type_modules);
    ...
}

// After:
Type::ADT(fqtn, args) => {
    let qname = format!("{}/{}", fqtn.module, fqtn.name);
    ...
}
```

The `qualify_type_name()` helper is deleted entirely.

### format_value() and format_result_value() simplification

Both functions lose their `type_modules: &HashMap<TypeName, ModuleFullPath>` parameter. The `type_defs: &HashMap<TypeName, TypeDefInfo>` parameter changes to `&HashMap<FQTypeName, TypeDefInfo>` (or `&dyn TypeDefLookup` if we adopt the trait throughout display).

All callers in `session_v4.rs` that currently call `build_type_modules()` before display stop doing that. The display functions read module info directly from `FQTypeName`.

### format_scheme_display() simplification

```rust
// Before:
pub fn format_scheme_display(
    name: &str,
    scheme: &Scheme,
    module: &ModuleFullPath,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String

// After:
pub fn format_scheme_display(
    name: &str,
    scheme: &Scheme,
    module: &ModuleFullPath,
) -> String
```

Constraint traits change from `Vec<TraitName>` to `Vec<FQTraitName>`, so the inline constraint display uses `fq_trait.name` for the `:TraitName var` notation.

## 3. Cache Manifest Fix

### Root cause

The nice worker writes `.meta.json` by reading from `shared.typecheck_products`:

```rust
// session_v4.rs:3122-3125
let symbol_table = shared.typecheck_products
    .get(module)
    .map(|tp| tp.symbols.clone())
    .unwrap_or_else(|| SymbolTable::new(module.clone()));
```

`TypecheckProduct.symbols` is a `SymbolTable` that was populated during typecheck and installed on `SharedState.typecheck_products`. The 11 cache test failures occur because:

1. **The TC's internal DashMap was never synced to TypecheckProduct.symbols.** The TC maintains its own `modules: DashMap<ModuleFullPath, SymbolTable>`. After checking, the symbol table entries exist on the TC's internal DashMap but are not copied to `TypecheckProduct.symbols` on `SharedState`.

2. As a result, `tp.symbols` is empty (or stale), and the `.meta.json` contains an empty symbol table. On cache-hit reload, there are no symbols to restore.

### After Sprint 51

The TypeChecker becomes stateless. Per-module symbol tables live on `SharedState` as the single source of truth. The TC reads from and writes to `SharedState.typecheck_products[module].symbols` directly during checking. There is no separate TC-internal DashMap to sync.

This fixes the root cause: the nice worker reads from the same `SharedState.typecheck_products` that the TC wrote to. No sync step needed.

### .meta.json write path changes (session_v4.rs:3070-3133)

```rust
// Before (lines 3069-3081):
let check_result = CheckResult {
    type_defs: input.type_defs,
    constructor_to_type: input.constructor_to_type,
    ...
};

// After:
// No type_defs or constructor_to_type on CheckResult — these fields are deleted.
// The nice worker builds a minimal CheckResult without them:
let check_result = CheckResult {
    method_resolutions: input.method_resolutions,
    constrained_fn_names: HashSet::new(),
    mono_defns: input.mono_defns,
    expr_types: input.expr_types,
    default_method_defns: input.default_method_defns,
    warnings: Vec::new(),
    display: None,
};
```

The `.meta.json` serialization (lines 3119-3133) remains the same structurally — it serializes the `SymbolTable` from `shared.typecheck_products`. The fix is that the SymbolTable is now populated correctly.

### TypecheckProduct.symbols field — DELETED

This field is deleted. Symbol tables move to `SharedState.symbol_tables` (a `DashMap<ModuleFullPath, SymbolTable>`) as the single authoritative store. The nice worker's `.meta.json` write path reads from `shared.symbol_tables.get(&module)` instead of `tp.symbols`. `TypecheckProduct` retains only `got`, `file_path`, and `source_text`.

### Cache test fix: cache_multi_module_transitive_imports

This test fails because the cached `.meta.json` had an empty symbol table (the sync bug above). After the stateless TC migration, the `.meta.json` write reads from `SharedState.symbol_tables` which is the authoritative store populated during typecheck. The test should pass without changes to the test itself — the symbol table is populated correctly at the source.

If the test also has file layout issues (e.g., expecting cache files in wrong directories), those are addressed by the existing `module_cache_path()` logic which correctly maps `core.numerics` to `core/numerics.{meta.json,o}`.

## 4. CodegenInput Changes

### Fields deleted

```rust
// Before:
pub struct CodegenInput {
    pub method_resolutions: MethodResolutions,
    pub expr_types: HashMap<Span, Type>,
    pub mono_defns: Vec<MonoDefn>,
    pub default_method_defns: Vec<Defn>,
    pub program: Vec<TopLevel>,
    pub cross_module_func_sigs: Vec<(Symbol, usize)>,
    pub type_defs: HashMap<TypeName, TypeDefInfo>,       // DELETED
    pub constructor_to_type: HashMap<Symbol, TypeName>,  // DELETED
}

// After:
pub struct CodegenInput {
    pub method_resolutions: MethodResolutions,
    pub expr_types: HashMap<Span, Type>,
    pub mono_defns: Vec<MonoDefn>,
    pub default_method_defns: Vec<Defn>,
    pub program: Vec<TopLevel>,
    pub cross_module_func_sigs: Vec<(Symbol, usize)>,
}
```

### How the nice worker (.o codegen) accesses type info

Nice workers hold `Arc<SharedState>` and can access `shared.symbol_tables` directly — same DashMap as priority workers. The `compile_module_to_object` function receives `&SharedState` (or `&DashMap<ModuleFullPath, SymbolTable>`) and queries type info on demand.

`ObjectCompileInput` loses its `type_defs` and `constructor_to_type` fields:

```rust
// Before:
pub type_defs: HashMap<TypeName, TypeDefInfo>,
pub constructor_to_type: HashMap<Symbol, TypeName>,

// After: both fields deleted
```

The nice worker passes `&shared.symbol_tables` to the backend's compilation functions. Same access pattern as JIT compilation — single source of truth.

## 5. Migration Risks

### DashMap guard lifetimes

**Risk**: `DashMap::get()` returns a `Ref<'_, K, V>` guard. Code that holds two guards simultaneously (e.g., looking up a constructor in the current module then its type def in the defining module) must be careful about ordering.

**Mitigation**: The existing `resolve_in_module()` pattern in the typecheck crate already handles multi-guard DashMap access with an `IMPORT_CHAIN_DEPTH_LIMIT`. The backend follows the same pattern: get guard, extract data, drop guard, get next guard. For cases where both the constructor entry and type def are needed simultaneously, extract the `FQTypeName` from the constructor guard first, drop it, then look up the type def.

### Performance: DashMap vs HashMap lookup

**Low concern**. DashMap uses per-shard locking. During codegen, only one thread is compiling a given module, so there's no contention on the same shard. The overhead vs. `HashMap::get` is a single atomic read for the shard lock — negligible relative to Cranelift IR generation. If profiling later shows this matters, a per-compilation-unit snapshot can be introduced as an optimization without changing the API.

### Display function signature changes

**Risk**: Many callers pass `&HashMap<TypeName, ModuleFullPath>` (the `type_modules` map). All these call sites change.

**Mitigation**: The `type_modules` parameter is deleted entirely. All display functions lose it. The call sites are simplified (fewer arguments). Callers that currently call `build_type_modules()` can delete that call. This is a net reduction in code.

**Affected public signatures** (all in `display.rs`):
- `format_value()` — loses `type_modules`
- `format_result_value()` — loses `type_modules`
- `format_type_qualified()` — loses `type_modules`
- `format_scheme_display()` — loses `type_modules`
- `format_adt_type_qualified()` — loses `type_modules`
- `format_result()` — unchanged (already convenience wrapper with empty maps)

The `type_defs` parameter on display functions changes to `&DashMap<ModuleFullPath, SymbolTable>`. Lookup changes from `type_defs.get(name)` to `symbol_tables.get(&fqtn.module).and_then(|t| t.get_type_def(&fqtn.name))` where `fqtn` comes from the `Type::ADT(fqtn, args)` destructure. Display functions that need `TypeDefInfo` (e.g., `format_adt_value` for field names) query the DashMap directly.

### Test fixture ergonomics

Many backend tests construct `Type::ADT(TypeName::from("Foo"), vec![])`. These change to `Type::ADT(FQTypeName::new(ModuleFullPath::from("test"), TypeName::from("Foo")), vec![])`.

Add a test helper:

```rust
#[cfg(test)]
fn test_adt(name: &str) -> Type {
    Type::ADT(FQTypeName::new(ModuleFullPath::from("test"), TypeName::from(name)), vec![])
}
```

## Sketch Comparison

The sketch's backend accesses type info through `Option<&HashMap<String, TypeDefInfoCg>>` passed directly on the `FnState` struct (equivalent to our `CompileContext`):

```rust
// sketch/src/codegen.rs:143-145
pub(crate) type_defs: Option<&'a HashMap<String, TypeDefInfoCg>>,
pub(crate) constructor_to_type: Option<&'a HashMap<String, String>>,
```

Key observations:

1. **No module qualification**: The sketch uses bare `String` names everywhere. `type_defs` is keyed by bare type name, `constructor_to_type` maps bare constructor name to bare type name. This works because the sketch has no real module isolation — name collisions are undetected.

2. **No abstraction**: The sketch passes raw HashMaps. No trait, no indirection. This is fine for a single-module prototype but breaks with concurrent multi-module compilation where type info comes from different sources (TC state vs. cache vs. SharedState).

3. **Display requires scanning**: The sketch's `qualify_adt_name()` scans all modules to find where a type lives. `all_impls()` flat-maps across all modules. These are O(N) scans that `FQTypeName` eliminates.

**Divergence**: The reimplementation embeds module context in the type system (`FQTypeName`) and accesses type definitions through a snapshot HashMap keyed by fully-qualified names. This eliminates the sketch's global scan patterns and prevents the cross-module name collision bug that the sketch's bare-name approach allows. The HashMap snapshot pattern is the same as the sketch (pass a HashMap on the compilation context), just with qualified keys. No new architectural complexity is introduced.
