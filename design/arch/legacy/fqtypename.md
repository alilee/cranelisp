# FQTypeName Migration

Design sketch for migrating `TypeName` (bare string) to `FQTypeName { module: ModuleFullPath, name: TypeName }` in boundary types. Part of Sprint 51 (Stateless TypeChecker).

## Motivation

`TypeName` is a bare string newtype (`"Option"`, `"Color"`, `"Int"`). It carries no module information. This creates two problems:

1. **Name collisions**: Two modules defining `(deftype Point ...)` produce the same `TypeName("Point")`. The global `TypeDefRegistry` keyed by bare `TypeName` silently overwrites one definition with the other.

2. **Derived lookup maps**: The session must maintain `type_modules: HashMap<TypeName, ModuleFullPath>` (built by `build_type_modules()`, called ~10 times during REPL display) to recover the module qualification that was discarded when the `TypeName` was created. This is a derived cache over data that already exists on per-module SymbolTables.

`FQTypeName` embeds the module at construction time, eliminating both problems.

## Definition

Following the existing `FQSymbol` pattern:

```rust
/// Fully qualified type name: module path + local type name.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FQTypeName {
    pub module: ModuleFullPath,
    pub name: TypeName,
}

impl std::fmt::Display for FQTypeName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.module, self.name)
    }
}
```

Lives in `cranelisp-types/src/newtype.rs` alongside `FQSymbol`.

Convenience constructor for the common case:

```rust
impl FQTypeName {
    pub fn new(module: ModuleFullPath, name: TypeName) -> Self {
        FQTypeName { module, name }
    }
}
```

## FQTraitName

The same qualification problem applies to `TraitName`. Two modules could define traits with the same name; the global `TraitRegistry` keyed by bare `TraitName` has the same collision risk. `ModuleEntry::TraitImpl` references `trait_name` — if bare, impl search across modules is ambiguous.

```rust
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FQTraitName {
    pub module: ModuleFullPath,
    pub name: TraitName,
}

impl std::fmt::Display for FQTraitName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.module, self.name)
    }
}
```

### What changes for FQTraitName

- `Scheme.constraints: HashMap<TypeId, Vec<TraitName>>` → `Vec<FQTraitName>`
- `ResolvedCall::TraitMethod.trait_name` → `FQTraitName`
- `TraitDecl.name` → `FQTraitName`
- `TraitImpl.trait_name` (AST) stays bare `TraitName` (pre-resolution, like `ImplSexp.target`)
- `ModuleEntry::TraitImpl.trait_name` → `FQTraitName` (post-resolution)
- `ModuleEntry::TraitDecl.decl.name` → `FQTraitName`
- Mangled name `Num.+$Int` stays string-based (JIT symbol) — constructed from `fq_trait.name` + `fq_type.name`

## Primitive type scoping

Spec §8.9.1 is clear: builtin types (`Int`, `Bool`, `String`, `Float`, `Vec`, `IO`) live in the `primitives` module. They are *"NOT available as bare names unless imported through the prelude chain."*

This means:
- `FQTypeName` for `Int` is `FQTypeName { module: "primitives", name: "Int" }`
- `FQTypeName` for `IO` is `FQTypeName { module: "primitives", name: "IO" }`
- IO detection becomes: `fqtn.module == "primitives" && fqtn.name == "IO"` — clean, unambiguous
- A user-defined `IO` type gets `FQTypeName { module: "user", name: "IO" }` — no confusion

### Dedicated `Type` variants for primitives — kept

`Type::Int`, `Type::Bool`, `Type::Float`, `Type::String` are dedicated `Type` enum variants (not `Type::ADT`). They are used pervasively for pattern matching in unification and codegen. Converting them to `Type::ADT(FQTypeName("primitives", "Int"), vec![])` would be a huge change with minimal benefit — primitives don't need tag info, constructors, or heap layout. The display convention (`primitives/Int`) is already hardcoded in `format_type_qualified_inner()`.

**Decision**: Keep dedicated `Type` variants. The `primitives/` prefix is a display convention for these variants, not a runtime type system concern. The dedicated variants are the "built-in" optimization that the spec allows.

## What changes

### `Type::ADT` — the core change

```rust
// Before:
ADT(TypeName, Vec<Type>)

// After:
ADT(FQTypeName, Vec<Type>)
```

Every pattern match on `Type::ADT` throughout all crates must be updated. This is the highest-blast-radius change (~182 sites per the existing FIXME estimate). The change is mechanical but must be done atomically — the tree does not compile in an intermediate state.

### `TypeDefInfo.name`

```rust
// Before:
pub name: TypeName,

// After:
pub name: FQTypeName,
```

`TypeDefInfo` is the canonical record of a type definition. Its name must be fully qualified so downstream consumers (backend match codegen, display, cache) can identify which module owns the type without external lookups.

### `CheckResult.type_defs` — DELETED

```rust
// Before:
pub type_defs: HashMap<TypeName, TypeDefInfo>,

// After: field removed entirely
```

This HashMap is a derived copy of data already on per-module SymbolTables as `ModuleEntry::TypeDef { info, ... }`. The backend currently uses it for ADT tag info and match codegen. After migration, the backend reads TypeDef info directly from the SymbolTable on SharedState:

```rust
// Before (backend match codegen):
let type_def = self.ctx.type_defs.get(type_name)?;

// After:
let type_def = shared.symbol_tables.get(&fqtn.module)
    .and_then(|table| match table.get(&fqtn.name.as_symbol()) {
        Some(ModuleEntry::TypeDef { info, .. }) => Some(info),
        _ => None,
    })?;
```

The backend's `CompilationContext` (or equivalent) holds a reference to SharedState instead of owned HashMap copies. This eliminates two `.clone()` calls per CheckResult and removes a sync point between typecheck and codegen.

### `CheckResult.constructor_to_type` — DELETED

```rust
// Before:
pub constructor_to_type: HashMap<Symbol, TypeName>,

// After: field removed entirely
```

Constructor → parent type mapping is already on the SymbolTable as `ModuleEntry::Constructor { type_name, ... }`. The backend resolves constructors the same way typecheck does — through the module system.

```rust
// Before (backend match codegen):
let type_name = self.ctx.constructor_to_type.get(bare)?;
let type_def = self.ctx.type_defs.get(type_name)?;

// After:
// Look up constructor in current module's SymbolTable (follows import chains)
let (fq_type_name, type_def_info) = resolve_constructor_type(shared, module, bare)?;
```

### `CodegenInput` fields — DELETED

```rust
// Before:
pub type_defs: HashMap<TypeName, TypeDefInfo>,
pub constructor_to_type: HashMap<Symbol, TypeName>,

// After: both fields removed
```

`CodegenInput` mirrors `CheckResult`. Same deletion applies — both JIT (priority workers) and .o (nice workers) read type/constructor info from SharedState SymbolTables.

### `ModuleEntry::Constructor.type_name`

```rust
// Before:
Constructor {
    type_name: Symbol,  // note: currently Symbol, not even TypeName
    ...
}

// After:
Constructor {
    type_name: FQTypeName,
    ...
}
```

This field is currently `Symbol` (a pre-existing type mismatch — it holds a type name in a `Symbol` field). Migrating directly to `FQTypeName` fixes both the qualification gap and the semantic type mismatch.

### `ResolvedCall::TraitMethod.impl_type`

```rust
// Before:
TraitMethod {
    impl_type: TypeName,
    ...
}

// After:
TraitMethod {
    impl_type: FQTypeName,
    ...
}
```

The resolved call carries the concrete type that the trait method was dispatched against. Must be qualified for consistent display and mangling.

### `ImplSexp.target`

```rust
// Before:
pub target: TypeName,

// After: 
pub target: TypeName,  // NO CHANGE
```

`ImplSexp` stores deferred impl S-expressions before type resolution. At parse time, the target type's module is not yet known. Stays as bare `TypeName`; resolution to `FQTypeName` happens during type checking.

## What does NOT change

### `ConstructorInfo.name` — stays `Symbol`

Constructor names are local identifiers (e.g., `"Some"`, `"None"`, `"Red"`). They are symbols, not type names. They live on a SymbolTable keyed by `Symbol`. The module information is on the SymbolTable itself (`table.path`). Adding module qualification to `ConstructorInfo.name` would be redundant with its SymbolTable location.

### `Scheme.constraints` — changes to `HashMap<TypeId, Vec<FQTraitName>>`

See FQTraitName section above. Constraints carry the defining module of each trait.

### `Type::from_name()` / `Type::type_name()` — stays with bare names

These map between primitive type strings (`"Int"`, `"Bool"`) and `Type` variants. They don't produce `ADT` variants, so `FQTypeName` doesn't apply. However, a new convenience method may be useful:

```rust
impl Type {
    /// Create a named ADT type with module qualification.
    pub fn adt(module: ModuleFullPath, name: TypeName, args: Vec<Type>) -> Type {
        Type::ADT(FQTypeName::new(module, name), args)
    }
}
```

### `Type::Display` — changes but deserves mention

The `Display` impl for `Type::ADT` currently writes just the type name. After migration it should write `module/Name` for foreign types and just `Name` for... well, actually `Display` on `Type` is a debug/internal format. The existing `format_type_qualified()` in the backend already does module-qualified display. `Type::Display` should use `FQTypeName::Display` which writes `module/name`.

## What gets eliminated

### `build_type_modules()` — deleted

`session_v4.rs:1638` builds `HashMap<TypeName, ModuleFullPath>` by scanning all module SymbolTables. Called ~10 times during REPL display. With `FQTypeName`, the module is already embedded in every `Type::ADT`. The function and all its callers are deleted.

### `format_type_qualified()` signature simplification

```rust
// Before:
pub fn format_type_qualified(ty: &Type, type_modules: &HashMap<TypeName, ModuleFullPath>) -> String

// After:
pub fn format_type_qualified(ty: &Type) -> String
```

The `type_modules` parameter becomes unnecessary — `Type::ADT(fqtn, args)` already carries the module. All call sites that pass `&type_modules` are simplified.

### `format_scheme_display()` — same simplification

Loses its `type_modules` parameter.

### `format_value()` and `format_result_value()` — same simplification

These display functions currently take `type_modules: &HashMap<TypeName, ModuleFullPath>`. With `FQTypeName`, the parameter is dropped from signatures throughout `cranelisp-backend/src/display.rs`.

### `CheckResult.type_defs` and `CheckResult.constructor_to_type` — deleted

These derived HashMap copies are eliminated. Backend reads from SharedState SymbolTables directly. See "What changes" section above for the replacement pattern. Also deletes the same fields from `CodegenInput`.

### `TypeDefRegistry` — deleted (see traitimpl-symbol-table.md)

The global `TypeDefRegistry` keyed by bare `TypeName` is replaced by per-module `ModuleEntry::TypeDef` lookups using `FQTypeName`.

## Migration strategy

This is a big-bang change in `cranelisp-types`. All downstream crates break simultaneously.

### Approach: feature branch, two waves

**Wave A — cranelisp-types (boundary crate)**:
1. Add `FQTypeName` struct to `newtype.rs`
2. Change `Type::ADT(TypeName, Vec<Type>)` → `Type::ADT(FQTypeName, Vec<Type>)`
3. Change `TypeDefInfo.name`, `CheckResult.type_defs` key, `CheckResult.constructor_to_type` value
4. Change `ModuleEntry::Constructor.type_name` from `Symbol` to `FQTypeName`
5. Change `ResolvedCall::TraitMethod.impl_type` from `TypeName` to `FQTypeName`
6. Tree does not compile after this wave.

**Wave B — all downstream crates**:
1. `cranelisp-typecheck`: Update all `Type::ADT` construction sites to provide module context. Update `register_type_def()`, `register_trait_impl()`, unification, constraint checking. Delete `TypeDefRegistry` (replaced by module-system lookups).
2. `cranelisp-backend`: Update match codegen, display functions, ADT tag lookup. Remove `type_modules` parameters from display API.
3. `cranelisp-frontend`: Update any `Type::ADT` construction in AST builder (likely minimal — frontend produces `TypeExpr`, not `Type`).
4. `src/` (binary crate): Update `session_v4.rs` (`CodegenInput`, `build_type_modules` deletion), `worker.rs` (TC call sites). Delete `build_type_modules()`.

**Wave C — cleanup**:
1. Delete `build_type_modules()` and all `type_modules` parameters
2. Delete `TypeDefRegistry` struct and its `type_defs` field on `TypeChecker`
3. Simplify display function signatures
4. Run full test suite

### Construction-site challenge

The key challenge is that `Type::ADT` construction sites need module context. Currently code writes `Type::ADT(TypeName::from("Option"), vec![...])` without knowing which module `Option` lives in. After migration, every construction site must provide `FQTypeName::new(module, name)`.

Most construction sites fall into categories:
- **Typechecker during type def registration**: module is `state.current_module` or the module being processed — available.
- **Typechecker during inference**: `Type::ADT` is produced by constructor lookup, which goes through the module system — module is available from the `ModuleEntry::TypeDef`.
- **Type resolution (`resolve_type_expr`)**: Resolves a `TypeExpr` to a `Type`. Currently returns bare `Type::ADT(name, args)`. Needs access to the defining module to construct `FQTypeName`. This is the most impactful change — `resolve_type_expr` needs a module context parameter or must look up the type through the module system.
- **Backend (rare)**: Backend mostly receives `Type` values from `CheckResult`; it rarely constructs `Type::ADT` from scratch. `Type::from_name()` produces primitives, not ADTs.
- **Tests**: Many test fixtures construct `Type::ADT` with bare names. These need a module (e.g., `ModuleFullPath::from("test")` or a fixture helper).

## Impact on display / formatting

The REPL already shows qualified type names (e.g., `primitives/Int`, `core.option/Option`). Currently this requires `build_type_modules()` + `format_type_qualified()`. After migration:

- `Type::ADT(fqtn, args)` carries the module directly
- `format_type_qualified()` reads `fqtn.module` instead of looking up `type_modules[&name]`
- Primitive types (`Int`, `Bool`, etc.) are NOT `Type::ADT` — they have dedicated `Type` variants. Their display as `primitives/Int` is hardcoded in `format_type_qualified_inner()` and is unaffected by this change.

## Sketch comparison

The sketch uses bare type names (`String`) everywhere — `Type::ADT(String, Vec<Type>)`. There is no `FQTypeName` in the sketch.

For display, the sketch has `qualify_adt_name()` on `TypeChecker` which scans all modules to find where a type is defined, returning `"module/TypeName"` for foreign types and bare `"TypeName"` for local types. This is equivalent to the reimplementation's `build_type_modules()` — a derived lookup that reconstructs module context that was discarded.

The sketch also uses `all_impls()` which flat-maps across all modules' impl lists — another scan that wouldn't be needed if type names carried their module.

**Divergence**: The reimplementation embeds module context at construction time (`FQTypeName`) rather than recovering it at display time. This is a strict improvement — it eliminates derived caches, prevents name collisions, and simplifies display logic. The sketch never attempted this because it predated the module system's maturity.

## Open questions

1. **Unification of FQTypeNames**: When unifying `Type::ADT(fqtn1, args1)` with `Type::ADT(fqtn2, args2)`, should unification compare the full `FQTypeName` (module + name) or just the `name`? Full comparison is correct — `user/Point` and `geometry/Point` are different types. But this could break code that currently works because bare names accidentally matched. Need to verify no tests rely on cross-module bare-name matching.

2. **Cache compatibility**: Existing `.meta.json` cache files serialize `TypeName` (bare strings). After migration, they serialize `FQTypeName` (module + name). Old cache files are incompatible. The cache should detect version mismatch and invalidate. This is likely already handled by source hash changes, but should be verified.

3. **Test fixture ergonomics**: Many tests construct `Type::ADT(TypeName::from("Foo"), vec![])`. After migration these need `Type::ADT(FQTypeName::new(ModuleFullPath::from("test"), TypeName::from("Foo")), vec![])`. Consider a test helper or a `FQTypeName::test(name)` convenience that uses a fixed test module path.

4. **Backend SymbolTable access pattern**: With `CheckResult.type_defs` deleted, the backend needs `&SharedState` (or `&DashMap<ModuleFullPath, SymbolTable>`) to resolve type/constructor info. The current `CompilationContext` is constructed from CheckResult fields. It would instead hold a SharedState reference. Need to verify the backend crate can depend on the SharedState type (or receives a trait/reference that abstracts it).

## Resolved questions

- **Primitive types as FQTypeName**: Dedicated `Type` variants (`Type::Int`, etc.) kept for efficiency. Display uses `primitives/` prefix convention. See "Primitive type scoping" section.
- **IO type detection**: Resolved. `is_io()` checks `fqtn.module == "primitives" && fqtn.name == "IO"`. User-defined IO types in other modules don't match. See "Primitive type scoping" section.
- **FQTraitName needed**: Yes. See "FQTraitName" section above.
