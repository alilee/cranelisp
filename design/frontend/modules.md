<!-- FIXME(/frontend): lib/ renamed to stdlib/ (Sprint 11). §2.1 reference updated.
     Please review. -->

# Module System Design

Solution design for the Cranelisp module system as implemented in Ring 2. This document is the authoritative design reference for Ring 3 and later implementers who need to understand how modules work -- particularly for macro system integration (the `macros` synthetic module, cross-module macro exports, and module-aware compilation).

**Spec reference**: `spec/08-modules.md`

## Overview

The module system provides:

1. **File-to-module mapping** -- each `.cl` file defines one module, identified by its filesystem path relative to the project root.
2. **Declarations** -- `mod`/`mod-` to declare submodules, `import` to bring names into scope, `export` to re-export names.
3. **Per-module symbol tables** -- each module has an isolated `SymbolTable` storing its definitions, imports, and re-exports.
4. **Topological compilation** -- modules are compiled leaves-first so dependencies are available before dependents.
5. **Name resolution** -- a layered lookup: local scope, module scope (following import/reexport chains), then qualified names.

```
Source text
  --[reader]--> Vec<Sexp>
  --[module_extract]--> (ModuleStructure, remaining_sexps)
  --[ast_builder]--> Vec<TopLevel>
  --[typecheck]--> CheckResult   (uses per-module SymbolTable)
  --[codegen]--> JIT code        (uses shared JIT + GOT)
```

Module declarations (`mod`, `import`, `export`) are extracted from raw S-expressions **before** macro expansion (spec section 8.12.1). The remaining sexps proceed through the normal AST builder pipeline.

---

## 1. Module Structure

### 1.1 Core Types

All types live in `crates/cranelisp-types/src/module.rs` and `crates/cranelisp-types/src/newtype.rs`.

**String newtypes** (defined via the `string_newtype!` macro in `newtype.rs`):

| Type | Purpose |
|------|---------|
| `ModuleFullPath` | Dotted module path: `"user"`, `"core.option"`, `"main.util"` |
| `ModuleName` | Single component name: `"util"`, `"option"` |
| `Symbol` | Any identifier: function names, variable names, import names |
| `FQSymbol` | Fully qualified: `{ module: ModuleFullPath, symbol: Symbol }` |

All are `String` newtypes with `Deref<Target=str>`, `From<String>`, `From<&str>`, `Display`, `Hash`, `Eq`, `Serialize`/`Deserialize`.

### 1.2 SymbolTable

```rust
pub struct SymbolTable {
    pub path: ModuleFullPath,
    pub symbols: HashMap<Symbol, ModuleEntry>,
}
```

Pure data, no runtime state. Owned by the `TypeChecker`, read by the backend for type information. Provides:

- `get(name) -> Option<&ModuleEntry>` -- single-symbol lookup
- `public_symbols() -> Iterator` -- all entries where `is_public()` is true
- `all_symbols() -> Iterator` -- all entries (public and private)
- `insert(name, entry)` -- add or overwrite an entry

### 1.3 ModuleEntry Variants

`ModuleEntry` is the enum stored in each symbol table slot:

| Variant | Fields | Purpose |
|---------|--------|---------|
| `Def` | `scheme`, `visibility`, `docstring`, `param_names`, `kind: Box<DefKind>` | A function, primitive, or special form definition |
| `Import` | `source: FQSymbol` | A name imported from another module; `source` points to the origin |
| `Reexport` | `source: FQSymbol` | A re-exported name; same chain-following semantics as `Import` |
| `TypeDef` | `info: TypeDefInfo`, `visibility`, `constructor_scheme`, `sexp` | A type definition (`deftype`) |
| `TraitDecl` | `decl: TraitDecl`, `visibility`, `sexp` | A trait declaration (`deftrait`) |
| `Constructor` | `type_name`, `info: ConstructorInfo`, `scheme`, `visibility` | An ADT constructor (from `deftype`) |
| `Macro` | `name`, `clauses: Vec<MacroClauseInfo>`, `docstring`, `visibility`, `sexp`, `source` | A macro definition (`defmacro`, Ring 3) |
| `PlatformDecl` | `dll_path`, `platform_module` | A platform DLL declaration (Ring 4) |
| `Ambiguous` | (none) | Poisoned: two different sources registered the same bare name |

**Visibility rule**: `Import` and `Reexport` entries are always considered public (they expose whatever they point to). `Ambiguous` is never public. All others check their `visibility` field.

### 1.4 DefKind

Classifies what kind of definition a `Def` entry represents:

| Variant | Purpose |
|---------|---------|
| `SpecialForm { description }` | Built-in special form (`if`, `let`, `fn`, `match`, `do`, ...) |
| `Primitive { primitive_kind, jit_name }` | Built-in primitive function (Inline IR, Extern FFI, or PlatformEffect) |
| `UserFn { constrained_fn }` | User-defined function. If `constrained_fn` is `Some`, it is a constrained polymorphic function awaiting monomorphisation |
| `Overloaded { variants }` | Multi-signature overloaded function base name (Ring 2) |

### 1.5 ModuleStructure

Intermediate representation produced by `module_extract.rs` -- captures the structural metadata parsed from a file before AST building:

```rust
pub struct ModuleStructure {
    pub path: ModuleFullPath,
    pub file_path: Option<PathBuf>,
    pub mod_decls: Vec<ModDecl>,
    pub import_specs: Vec<ImportSpec>,
    pub export_specs: Vec<ExportSpec>,
    pub impl_sexps: Vec<ImplSexp>,
    pub impls: Vec<TraitImpl>,
    pub dll_path: Option<PathBuf>,
}
```

### 1.6 Import/Export Specification Types

```rust
pub enum ImportNames {
    Specific(Vec<Symbol>),   // [Some None]
    Glob,                     // [*]
    MemberGlob(Symbol),       // [Display.*]
    None,                     // [] (alias-only)
}

pub struct ImportSpec {
    pub module_path: ModuleFullPath,
    pub alias: Option<ModuleName>,
    pub names: ImportNames,
    pub span: Span,
}

pub struct ExportSpec {
    pub module_path: ModuleFullPath,
    pub names: ImportNames,
    pub span: Span,
}
```

---

## 2. Module Discovery and Loading

Implemented in `src/pipeline.rs`.

### 2.1 `discover_module_graph(entry: &Path) -> Result<ModuleGraph>`

Entry point for multi-file compilation. Starting from the entry file:

1. Canonicalizes the entry path, derives the project root (parent directory).
2. Checks for a `stdlib/` subdirectory in the project root.
3. Recursively discovers modules via `discover_module_recursive`.
4. Returns a `ModuleGraph` containing all `ModuleNode`s and the entry path.

### 2.2 Recursive Discovery

`discover_module_recursive` performs DFS discovery:

1. **Cycle detection**: maintains a `visiting` stack of `ModuleFullPath`s. If the current module is already on the stack, a circular dependency error is reported.
2. **Already discovered**: if the module path is already in the `nodes` map, returns immediately (avoids re-processing shared dependencies).
3. **Parse**: reads and parses the file into `Vec<Sexp>`.
4. **Extract declarations**: calls `extract_module_declarations` to separate `mod`/`import`/`export` from remaining definitions.
5. **Recurse into submodules**: for each `ModDecl`, builds the child module's full path (e.g., parent `"main"` + child `"util"` = `"main.util"`) and resolves its file.
6. **Register**: adds the module to the graph with its dependencies.

### 2.3 File Resolution

`resolve_submodule_file` implements spec section 8.2.5. Search order:

1. **Child directory**: `{parent_dir}/{stem}/{name}.cl` -- e.g., `app/handler.cl` when `app.cl` declares `(mod handler)`.
2. **Sibling file**: `{parent_dir}/{name}.cl` -- e.g., `handler.cl` alongside `app.cl`.
3. **Project root**: `{project_root}/{name}.cl` (if different from parent_dir).
4. **Lib directory**: `{lib_dir}/{name}.cl` -- standard library modules.

The child-directory form takes priority, so `app/handler.cl` shadows a sibling `handler.cl`.

### 2.4 `mod` Declaration Syntax

Parsed by `module_extract.rs`:

| Form | Meaning |
|------|---------|
| `(mod name)` | Public submodule, loaded from file |
| `(mod- name)` | Private submodule, loaded from file |
| `(mod name form1 form2 ...)` | Inline public submodule (body extracted to file on first compilation) |
| `(mod- name form1 form2 ...)` | Inline private submodule |

Inline submodules are a one-time creation syntax. Currently, `discover_module_graph` skips inline modules during discovery (they need file extraction first).

---

## 3. Import/Export

### 3.1 Import Syntax

Parsed by `parse_import` / `parse_import_entries` in `module_extract.rs`:

```clojure
(import [module-spec names-list ...])
```

The bracket contents are pairs: `module-spec names-list module-spec names-list ...`

**Module specifiers**:
- Bare symbol: `core.option` -- absolute module path
- `super` -- parent module (strips last `.component` from current path)
- `(module alias)` -- e.g., `(core.string str)` registers `str` as an alias

**Names lists**:
- `[name1 name2]` -- specific named imports
- `[*]` -- glob import (all public symbols)
- `[Display.*]` -- member glob (all constructors of a type or methods of a trait)
- `[]` -- alias-only import (no bare names)

Multiple module/names pairs may appear in a single `import` form. Multiple `import` forms accumulate.

### 3.2 Import Registration

`TypeChecker::register_imports(specs)` in `crates/cranelisp-typecheck/src/checker.rs` processes each `ImportSpec`:

1. **Alias registration**: if `spec.alias` is `Some`, inserts into `self.module_aliases` (`Symbol -> ModuleFullPath`).
2. **Source table lookup**: finds the source module's `SymbolTable` in `self.modules`. Error if not found.
3. **Name collection** (by `ImportNames` variant):
   - `Glob`: collects all public symbols from the source table, each wrapped as `ModuleEntry::Import { source: FQSymbol }`.
   - `Specific(names)`: looks up each named symbol in the source table. Errors if not found or not public (unless the importer is in the source module's subtree).
   - `MemberGlob(parent)`: filters for constructors whose `type_name` matches `parent`, or trait methods whose trait name matches.
   - `None`: no names collected (alias-only).
4. **Ambiguity detection**: for each name being inserted, checks if the current symbol table already has an entry. If the existing entry is an `Import` from the same source, it is not ambiguous (same-source duplicate per spec section 8.6.4). If from a different source, the entry is replaced with `ModuleEntry::Ambiguous`.

### 3.3 Export Syntax

```clojure
(export [module names-list ...])
```

Parsed by `parse_export` / `parse_export_entries` in `module_extract.rs`. Structure mirrors imports: module-path / names-list pairs, supporting `Specific`, `Glob`, and `MemberGlob` name lists.

Exports create `Reexport` entries in the exporting module's symbol table. These behave identically to `Import` entries during chain-following resolution but are semantically distinct: they declare that the name is part of this module's public API.

### 3.4 Visibility

Defined as an enum in `crates/cranelisp-types/src/ast.rs`:

```rust
pub enum Visibility { Public, Private }
```

- **Public by default**: all `defn`, `deftype`, `deftrait`, `defmacro` forms are `Visibility::Public`.
- **Private variants**: `defn-`, `deftype-`, `deftrait-`, `defmacro-`, `mod-` produce `Visibility::Private`.
- **Private semantics**: a private name is accessible within the defining module and its submodule subtree. It cannot be imported from outside the subtree, and glob exports/imports skip private names.

Visibility is checked in:
- `register_imports` -- specific-name imports of private symbols from outside the subtree produce errors.
- `resolve_qualified` -- qualified references to private names from outside the subtree produce errors.
- `public_symbols()` -- used by glob imports and exports to filter.

---

## 4. Name Resolution

Implemented primarily in `TypeChecker::lookup()` in `crates/cranelisp-typecheck/src/checker.rs`.

### 4.1 Resolution Layers

For a bare (unqualified) name, resolution proceeds through three layers (spec section 8.6.1):

1. **Local environment** (`ScopeStack`): `let` bindings, `fn` parameters, `match` pattern variables. Checked first via `self.env.lookup(name)`.

2. **Module scope** (`SymbolTable`): definitions in the current module plus imported names. Checked via `lookup_in_current_module(name)`, which calls `current_symbol_table().get(name)` and then follows `Import`/`Reexport` chains.

3. **Qualified name fallback**: if the name contains `/`, it is split into `module_part/name_part` and resolved via `resolve_qualified`.

### 4.2 Import/Reexport Chain Following

`extract_scheme_from_entry(entry, depth)` follows `Import` and `Reexport` chains:

```
Import { source: FQSymbol { module, symbol } }
  -> look up source module's symbol table
  -> get entry for symbol
  -> recurse (depth + 1)
```

**Depth limit**: `IMPORT_CHAIN_DEPTH_LIMIT = 10`. If exceeded, returns `None` (silently fails rather than erroring -- pathological chain detection). This prevents infinite loops from misconfigured re-export chains.

Terminal entries that produce a `Scheme`:
- `Def { scheme, .. }` -- returns the scheme directly
- `Constructor { scheme, .. }` -- returns the constructor's scheme
- `TypeDef { constructor_scheme: Some(scheme), .. }` -- returns the product type's constructor scheme

### 4.3 Qualified Name Resolution

For names containing `/` (e.g., `util/helper`, `core.option/Some`):

```rust
fn lookup(&self, name: &str) -> Option<Scheme> {
    // ... local scope check ...
    // ... module scope check ...

    if let Some(slash_pos) = name.find('/') {
        let module_part = &name[..slash_pos];
        let name_part = &name[slash_pos + 1..];

        // 1. Try child-of-current-module: "util" in module "main"
        //    -> resolves to "main.util"
        let child_path = format!("{}.{}", self.current_module, module_part);
        if let Ok(Some(scheme)) = self.resolve_qualified(&child_path, name_part) {
            return Some(scheme);
        }

        // 2. Try absolute module path
        let abs_path = ModuleFullPath::from(module_part);
        if let Ok(Some(scheme)) = self.resolve_qualified(&abs_path, name_part) {
            return Some(scheme);
        }
    }
    None
}
```

`resolve_qualified(module_path, name)`:
1. Resolves the first path component through `module_aliases` (from aliased imports).
2. Looks up the resolved module in `self.modules`.
3. Looks up the name in that module's symbol table.
4. **Visibility check**: if the entry is not public and the current module is not in the target module's subtree, returns a `TypeError`.
5. Follows chains via `extract_scheme_from_entry`.

**Subtree check** (`is_in_subtree`): module `"foo.bar"` is in the subtree of `"foo"`, and `"foo"` is in its own subtree. This allows private names to be accessed by child modules.

---

## 5. Cross-Module Compilation

Implemented in `compile_module_graph()` in `src/pipeline.rs`.

### 5.1 Pipeline

```
discover_module_graph(entry)
  -> ModuleGraph { nodes, entry, project_root, lib_dir }

toposort(graph)
  -> Vec<ModuleFullPath>  (leaves first, entry last)

for each module in topological order:
    1. Read and parse source file
    2. Extract module declarations (mod, import, export)
    3. Build AST from remaining sexps
    4. Set TypeChecker to current module (tc.set_current_module)
    5. Register imports (tc.register_imports)
    6. Type-check the program
    7. Compile into the shared JIT (compile_module_program)
    8. Accumulate function signatures for downstream modules

Finalize shared JIT (resolves all cross-references)
Execute entry module's last zero-arg defn
```

### 5.2 Topological Sort

`toposort(graph)` uses Kahn's algorithm:

1. Build in-degree map from dependency edges.
2. Seed queue with zero in-degree nodes (leaf modules).
3. Process queue: emit each node, decrement in-degree of dependents.
4. If sorted count differs from node count, remaining nodes form a cycle.

### 5.3 Shared JIT and Function Signatures

All modules compile into a **single shared JIT** instance (`cranelisp_backend::jit::Jit`). This means cross-module function calls resolve through the JIT's symbol table -- no separate linking step.

Each compiled module produces `CompiledModuleInfo.func_signatures: Vec<(Symbol, usize)>` -- a list of `(function_name, param_count)` pairs. These are accumulated in `all_func_sigs` and passed to downstream modules via `compile_module_program(..., &all_func_sigs)`.

For submodule functions, **qualified aliases** are registered:
```rust
// Module "main.util", function "helper"
// -> alias "util/helper" for use by module "main"
let qualified = format!("{}/{}", last_component, name);
all_func_sigs.push((qualified, arity));
```

The backend's `compile_module_program` merges these prior function signatures into the current module's `func_ids` map. Qualified aliases (containing `/`) are resolved by stripping the module prefix and reusing the base function's `FuncId`.

### 5.4 Cross-Module GOT (Interactive Mode)

In interactive/REPL mode, cross-module function calls use the **cross-module GOT**:

```rust
// CompileContext field:
pub cross_module_got: Option<&'a HashMap<(ModuleFullPath, Symbol), (i64, usize)>>
```

`resolve_got_entry(name, span)` in the backend compiler checks:
1. **Local GOT** first (`ctx.got_slots` + `ctx.got_base_ptr`).
2. **Cross-module GOT** (`ctx.cross_module_got`) -- maps `(module_path, symbol_name)` to `(got_base_ptr, slot_index)`.

This two-level lookup allows a function compiled in one module's GOT to be called from another module's code.

### 5.5 `set_current_module` Bootstrapping

When `TypeChecker::set_current_module(path)` is called for a new module:

1. Creates a new `SymbolTable` for the path.
2. **Seeds builtins**: copies the following entry kinds from the `"user"` module (which was seeded by `register_builtins()` at `TypeChecker::new()`) into the new module as `ModuleEntry::Import { source: FQSymbol { module: "user", symbol: name } }` entries:
   - **Primitives** — inline and extern primitive functions (`add-i64`, `str-len`, etc.)
   - **Special forms** — `if`, `let`, `fn`, `match`, `do`, `defn`, `deftype`, etc.
   - **Constructors** — ADT constructors for builtin types (e.g., `IOVal`, `True`, `False`)
   - **Type definitions** — builtin type entries (`Int`, `Bool`, `String`, `Float`, `Vec`, `IO`)
   - **Constrained Def entries** — trait method schemes with non-empty constraints (e.g., `+`, `-`, `*`, `/`, `=`, `<`, `show`). These are `Def` entries whose `Scheme.constraints` map is non-empty, making trait-dispatched operators available in every module without explicit imports.

   **Not copied**: `TraitDecl` entries are **not** seeded into new modules via the symbol table. Trait declarations (`Num`, `Eq`, `Ord`, `Display`) and their implementations are resolved through the typechecker's global `trait_registry` and `impl_registry`, which are shared across all modules. This means trait lookup does not depend on per-module symbol tables — `deftrait` and `impl` forms register into global registries, and trait dispatch queries those registries directly.
3. Inserts the new table into `self.modules`.
4. Sets `self.current_module = path`.

This bootstrapping ensures that every module has access to builtins (`+`, `if`, `Int`, `Bool`, etc.) without explicit imports. The `"user"` module serves as the initial builtin container.

**Ring 3 note**: This approach works but is a transitional measure. The TODO in the code notes it should become a proper `primitives` module with explicit imports. Ring 3's prelude system (spec section 8.8) will provide the correct mechanism: an implicit `(import [prelude [*]])` injection.

---

## 6. Synthetic Modules

Synthetic modules are registered by the compiler without corresponding `.cl` source files. They provide compiler-seeded types, built-in functions, and platform bindings.

### 6.1 The `primitives` Module

**Spec reference**: section 8.9.1

The `primitives` module contains:
- **Builtin types**: `Int`, `Bool`, `String`, `Float`, `Vec`
- **The IO ADT**: `(deftype (IO a) (IOVal [:a ioval]))`
- **Primitive functions**: 19 Ring 0 inline primitives (arithmetic, comparison, boolean), 8 Ring 1 extern primitives (string/conversion), 4 polymorphic Vec primitives
- **Core traits**: `Num`, `Eq`, `Ord`, `Display` (Ring 2)
- **Special forms**: `if`, `let`, `fn`, `match`, `do`, `defn`, `deftype`, `deftrait`, `impl`, etc.

In the current implementation, builtins are registered by `register_builtins()` during `TypeChecker::new()`. As of Sprint 9, trait-related registrations (trait declarations, method schemes, and implementations) are registered into the `primitives` module context rather than the `user` module, following the trait module fix. Specifically, `register_builtins()` performs:

- **Primitive functions and special forms** — registered as `Def` entries into `"user"`.
- **Builtin type definitions and constructors** — registered as `TypeDef` and `Constructor` entries into `"user"`.
- **Core trait declarations** — `Num`, `Eq`, `Ord`, `Display` are registered as `TraitDecl` entries into the `"primitives"` module's symbol table, and into the global `trait_registry`.
- **Trait method schemes** — constrained `Def` entries for trait methods (`+`, `-`, `*`, `/`, `=`, `<`, `show`, etc.) are registered with `Scheme.constraints` mapping their type variables to the required trait.
- **Trait implementations for primitive types** — `impl Num Int`, `impl Eq Bool`, `impl Ord Float`, `impl Display String`, etc. are registered into the global `impl_registry`. These map `(TraitName, TypeName)` pairs to method implementations.

When new modules are created, primitive and special form `Def` entries (including constrained trait method schemes) are copied as imports from `"user"`. `TraitDecl` entries are not copied per-module — trait resolution goes through the global registries (see §5.5 above).

**Ring 3 migration path**: when the prelude system is implemented, all builtins should be registered into a dedicated `"primitives"` module. The prelude would import from `primitives` and re-export. User modules would receive builtins through the implicit prelude import. Decision 17 in `design/arch/CLAUDE.md` notes this is interim and should eventually be replaced by evaluating `deftrait`/`impl` declarations through the normal pipeline.

### 6.2 The `macros` Module

**Spec reference**: section 8.9.2

The `macros` module is a synthetic module containing the `Sexp` and `SList` algebraic data types used by the macro system:

- `Sexp` -- the S-expression ADT with constructors: `SexpInt`, `SexpStr`, `SexpSym`, `SexpList`, `SexpBracket`
- `SList` -- a cons-list type with `SCons` and `SNil` constructors

**Key design points for Ring 3 implementers**:
- The `macros` module is **NOT auto-imported**. Modules that need direct Sexp pattern matching must use explicit `(import [macros [*]])`.
- The macro expander and `quote-sexp` primitive emit **qualified references** (`macros/SexpSym`, `macros/SCons`, etc.), so quasiquote-based macros work without importing the module.
- `Sexp` and `SList` types, their constructors, and field accessors must be registered in a `SymbolTable` with path `ModuleFullPath::from("macros")`.
- Constructor schemes must be polymorphic where appropriate (e.g., `SexpList` holds an `SList`).
- The `macros` module must be seeded before any user module that uses macros is compiled, since macro expansion happens before AST building but after module declaration extraction.

### 6.3 Platform Modules (Ring 4)

Loaded from dynamic libraries via `(platform name)`. Creates a synthetic module named `platform.{name}` containing functions exported by the DLL. Stored as `ModuleEntry::PlatformDecl` in the declaring module and as `Def` entries in the platform module's own symbol table.

---

## 7. REPL Module Integration

Implemented in `src/repl.rs`.

### 7.1 Default Module

`ReplSession::new()` creates a `TypeChecker` with the default module `"user"`. All REPL inputs are evaluated in the context of the current module.

### 7.2 Module Switching

The `/mod` REPL command (spec section 8.13.2) switches the active module:

```
user> /mod math
math> ...
```

This calls `tc.set_current_module(ModuleFullPath::from("math"))`, which creates a new symbol table if one does not exist (seeded with builtins from `"user"`). The current module path is tracked by `self.tc.current_module`.

### 7.3 REPL Import Handling

When `(import ...)` is entered at the REPL:
1. The input is parsed into sexps.
2. Module declarations are extracted by `extract_module_declarations`.
3. If import specs are found, `tc.register_imports(&specs)` is called to install imported names into the current module's symbol table.
4. The module referenced by the import must already be loaded (compiled and registered in `tc.modules`).

For modules not yet loaded, the REPL should support lazy loading via qualified name references (spec section 8.5.4), though this is not yet fully implemented.

### 7.4 Current Module Path in Display

The REPL uses `tc.current_module_path()` when formatting definition displays. Function definitions show `:{type} {module}/{name}`, and type definitions show `:{module}/{TypeName}`. This provides the user with fully-qualified context for every definition.

### 7.5 Snapshot/Restore

`TypeChecker::snapshot()` captures `next_type_id`, `symbol_count`, and `subst_len`. On error, `restore(snapshot)` rolls back the type variable counter and clears transient state (`expr_types`, `method_resolutions`, `warnings`). This prevents failed REPL inputs from corrupting the type environment.

Note: snapshot/restore does not perfectly undo symbol table mutations (it uses count-based heuristics since `HashMap` does not preserve insertion order). This is a known limitation accepted for Ring 0-2.

---

## 8. Per-Module Symbol Tables

### 8.1 Storage

`TypeChecker` stores all module symbol tables in a single map:

```rust
pub(crate) modules: HashMap<ModuleFullPath, SymbolTable>,
pub(crate) current_module: ModuleFullPath,
```

### 8.2 Population During Compilation

Symbol tables are populated incrementally as forms are type-checked:

1. **`set_current_module(path)`** -- creates the table (if new) and seeds builtins.
2. **`register_imports(specs)`** -- adds `Import` entries for imported names.
3. **`check_program` / `check_repl_input`** -- as each top-level form is processed:
   - `defn` -- inserts a `Def` entry with the inferred `Scheme`.
   - `deftype` -- inserts `TypeDef` and `Constructor` entries for the type and each constructor.
   - `deftrait` -- inserts a `TraitDecl` entry and `Def` entries for each method signature.
   - `impl` -- updates trait dispatch tables (does not create new symbol table entries, but may register method implementations).
4. **Export processing** -- `export` specs create `Reexport` entries pointing to the source module.

### 8.3 Symbol Table Access Patterns

- **`current_symbol_table()`** / **`current_symbol_table_mut()`** -- access the active module's table. Panics (via `unreachable!`) if the current module is not in the map, which is a programmer invariant guaranteed by `set_current_module`.
- **`self.modules.get(&path)`** -- direct access to any module's table by path. Used for import resolution, qualified name lookup, and cross-module introspection.

### 8.4 Module Keys

`tc.modules` uses `ModuleFullPath` as keys. These are the **full dotted paths**:

- `"user"` -- REPL default module
- `"main"` -- batch entry module
- `"main.util"` -- submodule of main
- `"core.option"` -- standard library module
- `"primitives"` -- synthetic module (future)
- `"macros"` -- synthetic module (Ring 3)

---

## 9. Invariants

The following invariants must always hold:

### 9.1 No Circular Imports

The module dependency graph must be a DAG. Circular dependencies are detected at two levels:
- **Discovery time**: `discover_module_recursive` maintains a `visiting` stack and errors if a module path appears twice.
- **Toposort time**: `toposort()` detects any remaining cycles by checking that the sorted output has the same length as the input graph.

### 9.2 Depth-Limited Chain Resolution

Import and reexport chains must terminate within `IMPORT_CHAIN_DEPTH_LIMIT = 10` steps. This prevents infinite loops from pathological re-export configurations. If the limit is exceeded, resolution returns `None` (the name is treated as not found).

### 9.3 Deterministic Resolution Order

Name resolution follows a fixed priority:
1. Local scope (innermost binding wins)
2. Module scope (current module's symbol table)
3. Qualified name (child-of-current-module, then absolute path, then alias)

This order is deterministic and does not depend on HashMap iteration order. Within module scope, ambiguity is explicitly handled: two different sources for the same bare name produce `ModuleEntry::Ambiguous`, and attempting to use an ambiguous name produces an error.

### 9.4 Current Module Always Exists

`self.current_module` always has a corresponding entry in `self.modules`. This is enforced by:
- `TypeChecker::new()` creating the `"user"` entry.
- `set_current_module()` creating the entry if it does not exist.
- No code path removes the current module's entry.

Violation of this invariant triggers `unreachable!` in `current_symbol_table()`.

### 9.5 Compilation Order Respects Dependencies

Modules are compiled in topological order. A module's `register_imports` succeeds only if the source module's symbol table has already been populated (it was compiled earlier in the sort order). This is guaranteed by the toposort: dependencies come before dependents.

### 9.6 Module Declarations Before Macro Expansion

`mod`, `import`, and `export` forms are extracted from raw S-expressions by `extract_module_declarations` **before** the AST builder runs (and therefore before any macro expansion). These forms are not subject to macro expansion. This ensures that the module structure is known before any code in the module is processed.

---

## Design Decisions

### Why extract module declarations at the Sexp level?

Module declarations must be processed before macro expansion (spec section 8.12.1) because:
1. Macros from imported modules must be available before expansion.
2. The dependency graph must be known before any compilation.
3. Module structure is purely syntactic -- no type information or macro expansion is needed.

`extract_module_declarations` operates on `Vec<Sexp>`, not on AST nodes. It partitions the sexp stream into structural declarations and remaining code, letting the remaining code go through the normal AST builder pipeline.

### Why a shared JIT rather than per-module JIT?

A single shared `Jit` instance for all modules simplifies cross-module function calls: all functions are in the same symbol table, and Cranelift resolves references during finalization. This avoids the complexity of a separate linker or GOT-based cross-module dispatch in batch mode.

In interactive mode, the GOT provides an additional indirection layer that allows function redefinition and cross-module references.

### Why copy builtins from "user" to new modules?

This is a pragmatic transitional approach. The correct solution (spec section 8.8) is the prelude system, where builtins live in a `primitives` module and are re-exported through a prelude that is implicitly imported. The current approach copies builtin entries as `Import` references, which achieves the same effect but lacks the clean module boundary.

Ring 3 should:
1. Create a `"primitives"` `SymbolTable` and register builtins there.
2. Create a `"macros"` `SymbolTable` and register Sexp/SList there.
3. Implement implicit `(import [prelude [*]])` injection.
4. Remove the builtin-copying logic from `set_current_module`.
