# Name Resolution

How Cranelisp resolves names — from bare symbols in source code to typed definitions across modules.

## 1. The Problem

A flat symbol table works when everything lives in one file. Once you add modules, re-exports, REPL redefinition, and synthetic builtins, you need a system that can:

- Resolve bare names (`print`) to their defining module (`platform.stdio/print`)
- Limit visibility — only imported names are accessible without qualification
- Allow qualified access (`util/helper`) at any time, regardless of imports
- Support REPL namespace switching without losing definitions
- Track re-export provenance (`prelude/print` → `platform.stdio/print`)
- Detect ambiguity when two modules export the same bare name

## 2. Architecture — Per-Module Symbol Tables

All name resolution goes through per-module symbol tables — `CompiledModule` structs keyed by `ModuleFullPath`.

```
modules: HashMap<ModuleFullPath, CompiledModule>

CompiledModule {
    symbols: HashMap<Symbol, ModuleEntry>,
}

ModuleEntry enum:
    Def { scheme, visibility, meta, constrained_fn,
          got_slot, code_ptr, source, sexp, defn, clif_ir, disasm, ... }
    Import { source: FQSymbol }
    Reexport { source: FQSymbol }
    TypeDef { info, visibility, constructor_scheme }
    TraitDecl { decl, visibility }
    Constructor { type_name, info, scheme, visibility }
    Macro { name, fixed_params, rest_param, docstring, visibility }
    Ambiguous   // bare name poisoned by conflicting registrations
```

Type definitions are stored as `ModuleEntry::TypeDef` entries in `symbols`. For single-constructor product types where the type and constructor share a name (e.g., `Point`), the `constructor_scheme` field holds the constructor's scheme so the entry serves double duty — both type definition and constructor. For sum types and enums, `constructor_scheme` is `None` and constructors have separate `Constructor` entries.

There is a distinguished **root module** — unqualified and implicitly accessible from everywhere. Special forms (`if`, `let`, `fn`, `match`) live here. The root module is always consulted during resolution, so special forms are findable without imports or qualification.

Resolution becomes a walk:

1. `local_env` (transient, per-function — unchanged)
2. Current module's `symbols` — if `Import`/`Reexport`, follow edge to source module
3. Root module's `symbols` — special forms and language-level builtins
4. Qualified access — see below

### Qualified name resolution

A qualified name (`path/Symbol`) is resolved relative to the current module's position in the module tree. Three forms:

**Fully qualified** — `core.option/Option`. The path before `/` is a complete `ModuleFullPath`. Works from anywhere. The target symbol must be public.

**Partially qualified** — `option/Option`. The path before `/` is a `ModulePathLeaf`, resolved as a child or sibling of the current module. From inside `core`, `option` resolves to child module `core.option`. The child module must be declared as a public `(mod option)`, and the symbol must be public.

**Super-relative** — `super/foo`. The keyword `super` refers to the parent module. From inside `core.option`, `super/foo` resolves to `core/foo`. The symbol must be public in the parent.

Resolution order for a qualified name `path/sym`:

1. If `path` is `super` → resolve in parent module
2. If `path` matches a module alias (from `(import [(core.option opt) []])` or `(export [...])`) → resolve in the aliased module
3. If `path` matches a child module of the current module → resolve there
4. If `path` is a full `ModuleFullPath` → resolve directly
5. Error: unknown module

Visibility is checked at each step — both the module (must be `pub mod`) and the symbol (must be public) must be accessible from the caller's position.

```
  Module tree:
    core
    core.option       (mod option) in core.cl
    core.option.util  (mod util) in core/option.cl
    app

  From core.option:
    Option              → bare lookup in core.option's symbols
    util/helper         → child: core.option.util/helper
    super/show          → parent: core/show
    core.option.util/x  → fully qualified (same as util/x from here)
    app/main            → fully qualified (cross-tree)
```

### Key properties

- **Self-contained modules.** No transient entries in any shared structure — each module owns its symbol table. No begin/end scope lifecycle, no cleanup phase.
- **Read-only dependencies.** A module being compiled only needs read access to its already-compiled dependencies. No shared mutable state between modules.
- **Parallel compilation.** Modules at the same level in the dependency graph can compile concurrently, since they only read from (never write to) their dependencies.
- **Persistence.** A `CompiledModule` can be serialized to skip recompilation on reload. Deserialize it and you have types + object code together, ready to link against.
- **REPL is slow-motion compilation.** The current module (whichever `/mod` selected) stays mutable, accepting new definitions and redefinitions one form at a time. There is nothing special about the "user" module; any module can accrete and redefine in the REPL.
- **Unified definition.** Resolving a name gives you everything: type scheme, visibility, GOT slot, code pointer, source text, CLIF IR, disassembly. No separate lookups across `TypeChecker`, `Jit`, and `ReplSession`.

## 3. What This Unifies

Module-related data that was previously scattered across multiple structures is now consolidated in `CompiledModule`:

| Data | Stored in |
|---|---|
| `Scheme` per name | `ModuleEntry::Def.scheme` |
| Per-module name+visibility | `CompiledModule.symbols` keys + `ModuleEntry.visibility` |
| Re-export provenance | `ModuleEntry::Reexport` edges (structural, not reconstructed) |
| Imported bare names | `ModuleEntry::Import` edges |
| Symbol metadata (docstrings, param names, kind) | `ModuleEntry::Def.meta` |
| Type definitions | `ModuleEntry::TypeDef` in `CompiledModule.symbols` |
| Constructor→type mapping | `ModuleEntry::Constructor.type_name` |
| Constrained function data | `ModuleEntry::Def.constrained_fn` |
| Trait declarations | `ModuleEntry::TraitDecl` (sole source of truth) |
| Method-to-trait mapping | Derived: `find_trait_for_method()` walks `ModuleEntry::TraitDecl` entries |
| HKT method param index | `TraitMethodSig.hkt_param_index` (set during `register_hkt_trait()`) |
| Codegen artifacts (GOT slot, code ptr, CLIF IR, disasm) | `ModuleEntry::Def` codegen fields |
| Macro definitions (name, params, docstring) | `ModuleEntry::Macro` (expansion func_ptr stays in `MacroEnv`) |

Re-export provenance is structural: `ModuleEntry::Reexport { source: FQSymbol(platform.stdio, print) }` in the prelude module directly points to the source, rather than being reconstructed by walking a flat map.

## 4. Name Types

Cranelisp uses newtype wrappers (defined in `src/names.rs`) to make each name's role explicit at the type level.

| Type | Example values | Role |
|------|---------------|------|
| `Symbol` | `"print"`, `"add"`, `"None"` | A resolved bare name — the part after `/` in a qualified name |
| `ModuleFullPath` | `"core.option"`, `"app.util"` | The full dotted module path — used as `CompiledModule` keys |
| `FQSymbol` | `(prelude, print)`, `(core, None)` | A fully-qualified symbol: `(ModuleFullPath, Symbol)` pair. Used in `ModuleEntry::Import/Reexport` and returned by `qualified_name()`. `Display` impl formats as `"prelude/print"` (or bare `"main"` for root module). |

`Symbol` and `ModuleFullPath` implement `Deref<Target=str>` and `Borrow<str>`, so `HashMap::get()` works with `&str` keys — read sites need no wrapping. Only insert sites require explicit construction (e.g. `Symbol::from("print")`).

## 5. Resolution Examples

### Prelude chain — how `print` reaches user code

```
  Step 1: init_builtins()
  ───────────────────────────────────────────
    modules["platform.stdio"].symbols["print"] = Def { scheme, Public, ... }

  Step 2: compile core.cl — (import [platform.stdio [*]])
  ───────────────────────────────────────────
    modules["core"].symbols["print"] = Import { source: FQSymbol(platform.stdio, print) }
    modules["core"].symbols["show"]  = Def { scheme, Public, ... }

  Step 3: compile prelude.cl — (import [core [*]]) (export [platform.stdio [*]])
  ───────────────────────────────────────────
    modules["prelude"].symbols["show"]  = Import { source: FQSymbol(core, show) }
    modules["prelude"].symbols["print"] = Reexport { source: FQSymbol(platform.stdio, print) }

  Step 4: REPL — implied (import [prelude [*]])
  ───────────────────────────────────────────
    modules["user"].symbols["print"] = Import { source: FQSymbol(prelude, print) }
    modules["user"].symbols["show"]  = Import { source: FQSymbol(prelude, show) }

  Step 5: User types (print "hello")
  ───────────────────────────────────────────
    resolve("print") in module "user":
      local_env: miss
      symbols["print"] = Import { source: FQSymbol(prelude, print) }
        → follow to modules["prelude"].symbols["print"]
        = Reexport { source: FQSymbol(platform.stdio, print) }
        → follow to modules["platform.stdio"].symbols["print"]
        = Def { scheme } ✓

    Provenance for display:
      follow Import/Reexport chain → FQSymbol(platform.stdio, print) → "platform.stdio/print"
```

### REPL module switching

```
  user> (defn greet [name] (concat "Hello " name))
  ───────────────────────────────────────────
    modules["user"].symbols["greet"] = Def { scheme, Public, ... }
    resolve("greet") → Def ✓

  user> /mod math
  ───────────────────────────────────────────
    Switch current module to "math". No cleanup needed —
    "user" module's symbols are untouched.

  math> greet                           → Unknown symbol
  ───────────────────────────────────────────
    resolve("greet") in module "math":
      local_env: miss
      modules["math"].symbols: no "greet" entry
      root module: no "greet" entry
      → error

  math> user/greet                      → (fn [String] String)  ✓
  ───────────────────────────────────────────
    Qualified access: go directly to modules["user"].symbols["greet"]
    = Def { scheme } ✓

  math> /mod user
  ───────────────────────────────────────────
    Switch back. modules["user"].symbols still has "greet".
    resolve("greet") → Def ✓
```

### Multi-file import with visibility

```
  Project:
    main.cl         (mod util) (import [util [helper]])
    util.cl         (defn helper [x] ...) (defn- internal [x] ...)

  ── compile util.cl ──────────────────────────
    modules["util"].symbols["helper"]  = Def { scheme, Public, ... }
    modules["util"].symbols["internal"] = Def { scheme, Private, ... }

  ── compile main.cl ──────────────────────────
    modules["main"].symbols["helper"] = Import { source: FQSymbol(util, helper) }

    (helper 42)
      resolve("helper") → Import → modules["util"].symbols["helper"]
      visibility: Public ✓

    (internal 1)
      resolve("internal") → miss in "main" symbols → error: Unknown symbol

    (util/internal 1)
      qualified access → modules["util"].symbols["internal"]
      visibility: Private → error: private name
```

## 6. Synthetic Modules

Cranelisp's builtins are organized into synthetic modules — `CompiledModule` instances registered by the Rust runtime rather than compiled from `.cl` source files.

```
  Rust runtime                        Module system
  ────────────                        ─────────────
  intrinsics.rs  ──┐
  platform.rs   ───┤── init_builtins() ──→  modules["platform.stdio"]  (print, read-line)
  primitives/*.rs ──┘                   →  modules["primitives"] (add-i64, int-to-string, ...)
```

Synthetic modules contain `Entry::Def` entries like any other module. They're invisible to user code unless imported — no special treatment in the resolution walk.

### The Import Chain

```
  root (special forms) ──→ always accessible
  primitives      ──→ core submodules ──→ core.cl ──→ prelude.cl ──→ user code
  macros          ──↗ (syntax only)     ↗
```

1. **core submodules** (numerics, formats, collections, option, sequences, syntax) each import from `primitives` and sibling submodules as needed
2. **core.cl** declares submodules via `(mod ...)` and re-exports everything via `(export [numerics [*] formats [*] ...])`
3. **prelude.cl** imports `[core [*]]` and re-exports `[primitives [...]]`
4. **User code** gets an implied `(import [prelude [*]])` — everything flows through

## 7. Ambiguity Rules

### Bare-name poisoning

When two sources register the same bare name in a module's symbol table, the entry becomes `ModuleEntry::Ambiguous`. This is called **poisoning**. Poisoned bare names cannot be used — attempting to reference one produces a type error listing qualified alternatives. Qualified names (`Trait.method`, `Type.Constructor`, `Type.field`, `module/name`) are never affected by poisoning and always resolve directly.

**Sources of ambiguity:**
- **Trait method collision**: Two traits define a method with the same name (e.g. `Display.show` and `Debug.show` both register bare `show`)
- **Import collision**: Two glob imports bring the same name from different modules
- **Import-then-definition collision**: An imported name is shadowed by a later trait/type registration

When poisoning occurs, the system emits a warning at registration time:
```
warning: bare name 'show' is now ambiguous — use 'Display.show' or 'Debug.show'
```

Using the poisoned name produces an error:
```
error: ambiguous bare name 'show' — use 'Display.show' or 'Debug.show'
```

The `find_ambiguous_alternatives()` method scans `TraitDecl` entries for matching methods and `TypeDef` entries for matching constructors/fields to generate the alternatives list.

### Dotted-name bypass

Dotted names resolve directly from the defining trait/type, bypassing the current module's potentially-poisoned bare name:

- `Display.show` → looks up `show` in the trait `Display`'s method signatures
- `Option.Some` → looks up `Some` in the type `Option`'s constructor list
- `Point.x` → looks up `x` in the type `Point`'s field definitions

These bypasses construct schemes directly from `TraitDecl` method signatures or `TypeDefInfo` constructor/field definitions rather than relying on `ModuleEntry::Def` entries (which may be `Ambiguous`).

### Import ambiguity

Duplicate imports are handled by `insert_import_checked()` on `CompiledModule`. If two imports bring the same bare name from different sources, the entry becomes `Ambiguous` and a warning is emitted. Same-source duplicates (e.g. arriving via two re-export paths) are not ambiguous.

```clojure
(import [math [add]] [util [add]])   ;; warning: bare name 'add' is now ambiguous
(add 1 2)                            ;; error: ambiguous bare name 'add'
(math/add 1 2)                       ;; ok — qualified name bypasses ambiguity
```

### Local bindings shadow freely

`let`, `fn` parameters, and `match` variables shadow imports without error — they're lexically scoped and always take priority through `local_env`:
```clojure
(import [math [pi]])
(let [pi 3]            ;; local "pi" shadows import — no error
  (+ pi 1))            ;; → 4
```

### Known limitation: dotted trait method codegen

While `Display.show` type-checks correctly even when bare `show` is ambiguous, the method resolution system (`resolve_methods`) does not currently track which trait a dotted call belongs to. When two traits define the same method name and both have implementations for the same type, `Display.show 42` may dispatch through the wrong trait. This is a known limitation tracked in KNOWN_ISSUES.md.

## 8. Migration History

The migration from flat dictionaries to per-module symbol tables was completed in 6 incremental steps:

| Step | Change | Status |
|------|--------|--------|
| 1 | Fix `FQSymbol` to use `ModuleFullPath` instead of `ModulePathLeaf` | **Done** (f000ec4) |
| 2 | Introduce `CompiledModule` struct alongside existing structures | **Done** (8475798) |
| 3 | Dual-write `TypeChecker` data into `CompiledModule` | **Done** (b429a6d) |
| 4 | Dual-write `Jit` codegen data into `CompiledModule` | **Done** (9b7be48) |
| 5 | Replace `universal` flat lookup with module-walk resolution | **Done** (f6c5fc8) |
| 6 | Remove `scope`/`universal`/`reexport_origins` and migrate secondary maps | **Done** (db17182) |
| 7 | Remove redundant global fields (`traits`, `method_to_trait`, `operator_methods`, `hkt_method_info`) | **Done** |
| 8 | Remove `module_defined_names` and `current_module_imports` — sole source of truth is `CompiledModule` | **Done** |
| 9 | Merge `type_defs` into unified `symbols` map — `ModuleEntry::TypeDef` with `constructor_scheme` for product types | **Done** |

### Current state

All name resolution goes through `CompiledModule` module-walk (`lookup_via_modules` → `resolve_in_module`). The former flat dictionaries (`universal`, `scope`, `reexport_origins`) and the `LocalOrFQSymbol` String newtype have been removed. `FQSymbol` is a `(ModuleFullPath, Symbol)` struct used in `ModuleEntry::Import/Reexport` and returned by `qualified_name()`.

All trait-related data is derived from `ModuleEntry::TraitDecl` entries in `CompiledModule`. The `traits` HashMap, `method_to_trait` HashMap, `operator_methods` HashSet, and `hkt_method_info` HashMap have been removed. Trait declarations are the sole source of truth, with helper methods (`find_trait_decl`, `find_trait_for_method`) walking module entries on demand. The method resolution pipeline is unified — operators and non-operator trait methods use the same `resolve_methods()` pass.

**Secondary maps — all migrated into CompiledModule:**

- **`constructor_to_type`**: Flat map removed. Constructor entries stored as `ModuleEntry::Constructor` in `CompiledModule.symbols`. Reads via `resolve_constructor_type_via_modules()`. JIT uses `collect_all_constructor_to_type()`.
- **`symbol_meta`**: Flat map removed. SymbolMeta stored as `Option<SymbolMeta>` field on `ModuleEntry::Def`. Reads via `resolve_symbol_meta_via_modules()` (convenience wrapper: `get_symbol_meta()`). Writes via `update_current_module_meta()` or directly during `insert_def()` / `register_builtin()`. Trait declarations written into `CompiledModule.symbols` as `ModuleEntry::TraitDecl` during `register_trait()`. Builtin type names (Int, Bool, String, Float, Vec) registered as placeholder Def entries in the `primitives` synthetic module during `init_builtins()`.
- **`type_defs`**: Flat map removed. TypeDefInfo stored as `ModuleEntry::TypeDef` entries in `CompiledModule.symbols`. Product types with same-named constructors use the `constructor_scheme` field on `TypeDef` to serve double duty. Reads via `resolve_type_def_via_modules()` which follows import/reexport chains. JIT uses `collect_all_type_defs()`.
- **`constrained_fns`**: Flat map removed. ConstrainedFn stored as `Option<ConstrainedFn>` field on `ModuleEntry::Def`. Reads via `resolve_constrained_fn_via_modules()` which follows import/reexport chains. Writes happen in `detect_constrained_fns()` (batch) and `register_constrained_fn()` (REPL).
- **`traits`**: Flat map removed. Trait declarations stored as `ModuleEntry::TraitDecl` entries in `CompiledModule.symbols`. Reads via `find_trait_decl()` which walks all module entries. Written during `register_trait_internal()`.
- **`method_to_trait`**: Flat map removed. Derived by `find_trait_for_method()` which walks all `ModuleEntry::TraitDecl` entries and checks their method lists.
- **`operator_methods`**: HashSet removed. Operator detection now uses `is_operator_name()` — a character-based check matching the parser's `operator_char` rule.
- **`hkt_method_info`**: HashMap removed. HKT constructor-carrying param index stored as `hkt_param_index: Option<usize>` field on `TraitMethodSig`, set during `register_hkt_trait()`. Read via `hkt_param_idx_for_method()` which walks module entries.

**Lifecycle methods — simplified:**

- **Removed**: `reexport_name()`, `register_qualified_aliases()`, `reinstall_module_names()`, `set_qualified_scope()`, `register_universal()`.
- **Renamed**: `register_qualified_aliases()` → `register_module_prefix()` — only inserts module name into `module_names` set (for qualified name parsing). No longer takes a names list.
- **Simplified**: `begin_module_scope()` — writes Import entries directly to CompiledModule. `install_imported_names()` — same. `end_module_scope()` — now a no-op (Import entries persist in CompiledModule).

**Resolution methods on TypeChecker:**

| Method | Purpose |
|--------|---------|
| `lookup(name)` | Main entry point: local_env → `lookup_via_modules()` |
| `lookup_via_modules(name)` | Qualified or bare name → scheme via module-walk |
| `lookup_entry_via_modules(name)` | Qualified or bare name → `&ModuleEntry` |
| `resolve_in_module(module, name, depth, require_public)` | Resolve name within a module, following Import/Reexport chains (depth-limited) |
| `resolve_entry_in_module(module, name, depth, require_public)` | Same but returns `&ModuleEntry` |
| `resolve_type_def_via_modules(name)` | Resolve name to `&TypeDefInfo` via `ModuleEntry::TypeDef` entries |
| `qualify_adt_name(name)` | For display: qualify a bare ADT name with its module if not in current/root scope |
| `resolve_constructor_type_via_modules(name)` | Resolve constructor name to its parent type name |
| `resolve_symbol_meta_via_modules(name)` | Resolve name to `&SymbolMeta` |
| `resolve_constrained_fn_via_modules(name)` | Resolve name to `&ConstrainedFn` |
| `find_trait_decl(name)` | Walk modules for `TraitDecl` entry matching trait name |
| `find_trait_for_method(name)` | Walk modules for `TraitDecl` containing a method with this name |
| `collect_all_type_defs()` | Gather all type_defs across modules (for JIT codegen) |
| `collect_all_constructor_to_type()` | Gather all constructor→type mappings across modules (for JIT codegen) |

---

## Appendix A: Former Implementation (Flat Universal Dict)

> **Historical.** The `universal`/`scope`/`reexport_origins` dictionaries described here were removed in Step 6 of the migration. All name→scheme resolution now goes through `CompiledModule` module-walk. This appendix is retained for architectural context.

### A.1. The Two Dictionaries

All name resolution currently flows through two `HashMap`s on the `TypeChecker`:

```
  Code says: "print"
       |
       v
  +-----------+     +--------------------------+
  |   scope   | --> |       universal          |
  +-----------+     +--------------------------+
  | "print"  -|---->| "platform.stdio/print": Scheme |
  | "show"   -|---->| "core/show"     : Scheme |
  | "map"    -|---->| "prelude/map"   : Scheme |
  +-----------+     | "math/sin"      : Scheme |
                    | "user/greet"    : Scheme |
                    +--------------------------+
```

**`universal: HashMap<LocalOrFQSymbol, Scheme>`** — the master registry. Every definition ever compiled gets an entry keyed by its qualified name (`FQSymbol`: `"core/show"`, `"platform.stdio/print"`, `"primitives/add-i64"`). Qualified entries are **permanent** — once `"math/add"` is registered, it never leaves. However, during module compilation, temporary bare entries (keyed by `Symbol` as `LocalOrFQSymbol`) are also inserted so that in-module code can resolve them. These bare entries are **deleted** by `end_module_scope()` after the qualified aliases have been created.

**`scope: HashMap<Symbol, LocalOrFQSymbol>`** — the bare-to-qualified mapping. Controls which bare names are available *right now*. Maps `Symbol("print")` → `LocalOrFQSymbol("platform.stdio/print")`, etc. This dictionary is **ephemeral** — it gets rebuilt when switching modules or compiling a new module scope.

#### Why two dictionaries?

Separation of *what exists* from *what's visible*:

- `universal` is the source of truth. Every compiled definition lives here under its qualified name. Qualified access (`util/helper`) always works by going directly to `universal`.
- `scope` is a lens. It determines which bare names resolve in the current context. When you switch from `user>` to `math>` in the REPL, `scope` is rebuilt — but nothing is lost from `universal`.

This means definitions survive namespace switching. When you switch back, the scope is restored from the qualified entries that never left `universal`.

### A.2. The Three-Layer Lookup

`TypeChecker::lookup()` checks three layers in order:

```
  lookup("x")
       |
       v
  +-----------+
  | local_env |  params, let bindings, match vars
  +-----------+
       | not found
       v
  +-----------+     +-----------+
  |   scope   | --> | universal |  bare → qualified → scheme
  +-----------+     +-----------+
       | not found
       v
  +-----------+
  | universal |  direct lookup (qualified names, single-file mode)
  +-----------+
```

The implementation (`src/typechecker/mod.rs:289`):

```rust
pub fn lookup(&self, name: &str) -> Option<&Scheme> {
    // 1. Local bindings (params, let, match vars)
    if let Some(s) = self.local_env.get(name) {
        return Some(s);
    }
    // 2. Scope (module imports + defs) → universal
    if let Some(qualified) = self.scope.get(name) {
        return self.universal.get(qualified.as_str());
    }
    // 3. Direct lookup in universal (qualified names, or bare names during single-file mode)
    self.universal.get(name)
}
```

**Layer 1: `local_env`** — function parameters, `let` bindings, and `match` pattern variables. These are lexically scoped (pushed/popped by the typechecker as it enters/exits binding forms). They shadow everything.

**Layer 2: `scope` → `universal`** — the module-aware lookup. The bare name is mapped to its qualified form, then looked up in `universal`. This is how `print` resolves to `platform.stdio/print`'s scheme.

**Layer 3: `universal` directly** — handles two cases:
- Qualified names like `util/helper` — they contain `/`, so they won't be in `scope`, but they'll be in `universal` directly.
- Single-file mode — when there's no module system active, bare names are inserted directly into `universal` (no scope indirection).

### A.3. Supporting Data Structures

Beyond the two main dictionaries, several structures support module-aware resolution:

| Structure | Type | Purpose |
|-----------|------|---------|
| `local_env` | `HashMap<Symbol, Scheme>` | Params, let, match vars. Pushed/popped lexically. |
| `module_defined_names` | `HashMap<ModulePathLeaf, Vec<(Symbol, Visibility)>>` | Per-module registry: which names each module defines, and whether they're public or private. |
| `current_module_imports` | `HashMap<Symbol, ModulePathLeaf>` | Bare names imported into the current scope, mapped to their source module. Used for ambiguity detection. |
| `reexport_origins` | `HashMap<FQSymbol, FQSymbol>` | Provenance chain: `"prelude/print"` → `"platform.stdio/print"`. Followed by `qualified_name()`. |
| `module_names` | `HashSet<ModulePathLeaf>` | All known module short names. Used to validate qualified references. |

**Lifecycles:**
- `local_env` — changes constantly during type inference (enter/exit scopes)
- `module_defined_names` — grows monotonically as modules compile; never shrinks
- `current_module_imports` — cleared at the start of each `begin_module_scope()`
- `reexport_origins` — grows monotonically as re-exports are processed
- `module_names` — grows as modules are discovered and compiled

### A.4. Lifecycle of a Name — Module Compilation

When a module compiles, its names go through a four-phase lifecycle:

```
  compile_module_graph("math")
  ─────────────────────────────────────────────────────────

  Phase 1: begin_module_scope(imports)
    scope:     { "print" -> "platform.stdio/print" }     ← from imports
    universal: { "print" -> Scheme }                ← bare alias, temporary

  Phase 2: compile definitions
    (defn add [x y] (+ x y))
    universal: { "add" -> Scheme }                  ← bare entry
    scope:     { "add" -> "add" }                   ← self-referencing

  Phase 3: register_qualified_aliases("math", ["add"])
    universal: { "math/add" -> Scheme }             ← qualified, permanent

  Phase 4: end_module_scope("math")
    scope:     remove "print", "add"                ← bare names gone
    universal: remove "print", "add"                ← bare entries gone
    universal: { "math/add" } still present         ← qualified survives
  ─────────────────────────────────────────────────────────
```

After compilation, the module's names exist only in qualified form in `universal`. Bare access requires importing.

### A.5. Worked Example: Prelude Chain

This traces how `print` travels from the Rust runtime to user code.

```
  Step 1: init_builtins()
  ───────────────────────────────────────────
    register_builtin("platform.stdio", "print", Scheme, meta)
      universal: { "platform.stdio/print": Scheme }
      module_defined_names: { "platform.stdio": [("print", Public)] }
      scope: {}
    (bare "print" is NOT in scope — only qualified)


  Step 2: compile core.cl — (import [platform.stdio [*]])
  ───────────────────────────────────────────
    begin_module_scope([("print", "platform.stdio")])
      scope:     { "print" -> "platform.stdio/print" }
      universal: { "print" -> Scheme }              ← temporary bare alias

    ... core defines show, concat, etc. ...

    register_qualified_aliases("core", ["show", "concat", ...])
      universal += { "core/show": Scheme, "core/concat": Scheme, ... }

    end_module_scope("core")
      scope:     cleared
      universal: bare "print", "show", "concat" removed
      universal: "core/show", "core/concat" persist


  Step 3: compile prelude.cl — (import [core [*]]) (export [platform.stdio [*]])
  ───────────────────────────────────────────
    begin_module_scope([("show", "core"), ...])
      scope: { "show" -> "core/show", ... }

    reexport_name("print", "platform.stdio", "prelude")
      universal += { "prelude/print": Scheme }
      reexport_origins: { "prelude/print" -> "platform.stdio/print" }

    register_qualified_aliases("prelude", [...])

    end_module_scope("prelude")
      scope: cleared


  Step 4: REPL — implied (import [prelude [*]])
  ───────────────────────────────────────────
    install_imported_names([("print", "prelude"), ("show", "prelude"), ...])
      scope:     { "print" -> "prelude/print", "show" -> "prelude/show", ... }
      universal: bare aliases installed


  Step 5: User types (print "hello")
  ───────────────────────────────────────────
    lookup("print")
      local_env: miss
      scope["print"] = "prelude/print"
      universal["prelude/print"] = Scheme ✓

    REPL display calls qualified_name("print"):
      scope["print"] = "prelude/print"
      reexport_origins["prelude/print"] = "platform.stdio/print"
      → shows "platform.stdio/print" (original defining module)
```

### A.6. Worked Example: User Module in REPL

User defines functions, switches modules, and switches back.

```
  user> (defn greet [name] (concat "Hello " name))
  ───────────────────────────────────────────
    track_repl_defn("greet"):
      module_defined_names["user"] += ("greet", Public)
      register_qualified_aliases("user", ["greet"]):
        universal["user/greet"] = Scheme
      set_qualified_scope("greet", "user"):
        scope["greet"] = "user/greet"

    lookup("greet") → scope → "user/greet" → Scheme ✓


  user> /mod math                       (loads math module)
  ───────────────────────────────────────────
    end_module_scope("user"):
      scope: remove "greet" and all prelude imports
      universal: remove bare aliases

    reinstall_module_names("math"):
      scope += { "sin" -> "math/sin", "cos" -> "math/cos", ... }
      universal: restore bare aliases from qualified entries


  math> greet                           → Unknown symbol
  math> user/greet                      → (fn [String] String)  ✓
  ───────────────────────────────────────────
    lookup("greet"):
      local_env: miss, scope: miss, universal: miss → error

    lookup("user/greet"):
      local_env: miss, scope: miss
      universal["user/greet"] = Scheme ✓  (qualified always works)


  math> /mod user
  ───────────────────────────────────────────
    end_module_scope("math")
    reinstall_module_names("user"):
      scope += { "greet" -> "user/greet", ... }
      also reinstalls prelude imports

  user> greet                           → (fn [String] String)  ✓
```

### A.7. Worked Example: Multi-File Import

A project with selective imports and visibility.

```
  Project layout:
    main.cl         (mod util) (import [util [helper]])
    util.cl         (defn helper [x] ...) (defn- internal [x] ...)


  Compilation (topological order: util first, then main)

  ── util.cl ──────────────────────────────────
    begin_module_scope([prelude imports])
    compile (defn helper ...) and (defn- internal ...)
    register_qualified_aliases("util", ["helper", "internal"])
      universal["util/helper"]   = Scheme           ← public
      universal["util/internal"] = Scheme           ← private (no external access)
    end_module_scope("util")


  ── main.cl ──────────────────────────────────
    resolve_module_imports([(import [util [helper]])])
      check "helper" is Public in module_defined_names["util"] ✓
      → [("helper", "util")]

    begin_module_scope([("helper", "util"), prelude...])
      scope["helper"] = "util/helper"

    (helper 42)
      lookup("helper") → scope → "util/helper" → Scheme ✓

    (internal 1)
      lookup("internal") → miss everywhere → error: Unknown symbol

    (util/internal 1)
      lookup("util/internal") → universal → Scheme found
      but visibility check → Private → error: private name
```

### A.8. Synthetic Modules

Cranelisp's builtins are organized into two synthetic modules — modules registered by the Rust runtime rather than compiled from `.cl` source files.

```
  Rust runtime                        Module system
  ────────────                        ─────────────
  intrinsics.rs  ──┐
  platform.rs   ───┤── init_builtins() ──→  "platform.stdio"  (print, read-line)
  primitives/*.rs ──┘                   →  "primitives" (add-i64, int-to-string, ...)
```

Synthetic modules use `register_builtin()`, which inserts names **only** under their qualified form (`"platform.stdio/print"`, `"primitives/add-i64"`). No bare names are added to scope — builtins are invisible to user code unless imported.

#### The Import Chain

```
  primitives      ──→ core submodules ──→ core.cl ──→ prelude.cl ──→ user code
  macros          ──↗ (syntax only)     ↗
```

1. **core submodules** (numerics, formats, collections, option, sequences, syntax) each import from `primitives` and sibling submodules as needed
2. **core.cl** declares submodules via `(mod ...)` and re-exports everything via `(export [numerics [*] formats [*] ...])`
3. **prelude.cl** imports `[core [*]]` and re-exports `[primitives [...]]`
4. **User code** gets an implied `(import [prelude [*]])` — everything flows through

#### Single-File Backwards Compatibility

When running without the module system (`check_program()` path), there's no import chain. `install_synthetic_bare_names()` creates Import entries in the current module's CompiledModule so module-walk resolution can find them:

```rust
pub fn install_synthetic_bare_names(&mut self) {
    for module in &["primitives", "platform.stdio"] {
        let names = self.get_module_public_names(module);
        let imports: Vec<(String, String)> = names
            .into_iter()
            .map(|n| (n, module.to_string()))
            .collect();
        self.install_imported_names(&imports);
    }
}
```

### A.9. Re-Export Resolution

When a module re-exports a name from another module, the system tracks the provenance chain so that introspection can display the original defining module.

#### How re-exports work

`reexport_name(name, source_module, dest_module)` copies the definition from `source/name` to both the bare position and `dest/name`, then records the link:

```
  prelude.cl: (export [platform.stdio [print]])
  ────────────────────────────────────────
    reexport_name("print", "platform.stdio", "prelude")
      universal["prelude/print"] = universal["platform.stdio/print"]   ← copy
      reexport_origins["prelude/print"] = "platform.stdio/print"       ← provenance
```

#### Following the chain

`qualified_name()` resolves a bare name to its *original* defining module by following `reexport_origins`:

```rust
pub fn qualified_name<'a>(&'a self, bare: &'a str) -> &'a str {
    if let Some(qualified) = self.scope.get(bare) {
        if qualified != bare {
            let mut result = qualified.as_str();
            while let Some(origin) = self.reexport_origins.get(result) {
                result = origin.as_str();
            }
            return result;
        }
    }
    bare
}
```

Example chain:
```
  "concat" → scope → "prelude/concat" → reexport_origins → "core/concat"
```

The REPL uses this to display `core/concat` rather than `prelude/concat` — showing where the function was actually defined, not where it was re-exported from.
