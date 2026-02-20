# Modules

## Overview

Cranelisp currently operates in a single flat namespace with single-file programs. This design document specifies a module system covering: directory-mirrored modules, local preludes, import/export, dot-notation for type/trait member access, trait disambiguation, ambiguity rules, and compiled artifact caching.

Reference languages: Rust (module declaration, visibility), Carp (Lisp + static types + modules), Clojure (namespace separator, import idioms).

## 1. Namespace Separator

The module-to-name separator is `/`, consistent with Clojure. The `.` character serves dual purpose: module hierarchy separator and type/trait member access.

| Separator | Language | Pros | Cons |
|-----------|----------|------|------|
| `/` | Clojure | Clojure convention; natural reading | `/` is division operator — needs parser disambiguation |
| `.` | Carp | Not used in grammar; clean look | Reserves `.` for future field access; not Clojure |
| `::` | Rust | Visually distinct | Conflicts with `:` type annotation; complex parsing |

The parser adds a `qualified_symbol` PEG rule requiring an alpha character before `/`, so `(/ 10 2)` still parses as division. Qualified operators are legal: `(core.math/+ 1 2)`.

Examples:

```
core.option/Option.Some     ; fully qualified constructor
std.string/join             ; fully qualified function
core.math/+                 ; fully qualified operator
(/ 10 2)                    ; division — no alpha before /, not qualified
```

## 2. Dot Notation for Types and Traits

`.` provides access to members of types and traits through their parent name. This applies to ADT constructors and trait methods.

### Constructors

```clojure
(Option.Some 42)
Option.None
(List.Cons 1 List.Nil)
```

### Trait Methods

```clojure
(Display.show 42)
(Num.+ 1 2)
```

### Import Interaction

How dot notation interacts with imports (see Section 6 for full import syntax):

- Import `Option` → use `Option.Some`, `Option.None`
- Import `Some` directly → bare `Some`
- Import `Display` → use `Display.show`
- Import `Display.*` → bare `show`

### Fully Qualified Access

Fully qualified names always work for public symbols, no import needed:

```clojure
(core.option/Option.Some 42)
(core.fmt/Display.show 42)
```

## 3. Module Declaration and File Mapping

Module identity is implicit from file path, following modern Rust convention — `app.cl` defines module `app`, submodules live in the `app/` directory. There is no `mod.cl`.

```
src/
  main.cl             ; entry point, root module: (mod app) (mod config)
  app.cl              ; module app: (mod handler) (mod- internal)
  app/
    handler.cl        ; module app.handler (public)
    internal.cl       ; module app.internal (private to app subtree)
  config.cl           ; module config
  prelude.cl          ; project prelude, auto-imported by convention
```

- File path = module identity: `src/app/handler.cl` → `app.handler`
- Parent declares submodules: `(mod handler)` in `app.cl`
- `(mod- internal)` — private submodule, accessible within module subtree only
- Path mapping: dots → directory separators, hyphens preserved in filenames

## 4. Parent Module References — `super`

`super` is a keyword that refers to the parent module, providing explicit upward traversal:

```clojure
super/helper          ; symbol 'helper' from parent module
super.super/config    ; symbol 'config' from grandparent module
```

Search order for unqualified module names:

1. Submodule of current module
2. Project root
3. Site library

`super` provides explicit upward traversal when the search order doesn't reach what you need.

## 5. Prelude — Convention, Not Magic

Preludes are regular modules. The compiler applies a naming convention:

The compiler auto-discovers `prelude.cl` by searching:
1. Sibling of the entry file
2. Project root directory (cwd)
3. Development fallback (`CARGO_MANIFEST_DIR/examples/prelude.cl`)

When found, the compiler injects an implicit dependency and import for every module (except prelude itself and its transitive dependencies):

```clojure
(import [prelude [*]])     ; implicit — import all from local prelude
```

The default `prelude.cl` re-exports from the core library, platform functions, and selected primitives:

```clojure
;; prelude.cl
(export [core [*] platform [*]
        primitives [vec-len vec-get vec-set vec-push vec-map vec-reduce parse-int]])
```

The core library (`lib/core.cl`) is a thin re-export shell that declares domain-oriented submodules in `lib/core/`:

```clojure
;; lib/core.cl
(mod numerics)    ;; Num, Eq, Ord traits + Int/Float impls + inc
(mod formats)     ;; Display trait + show impls
(mod collections) ;; Functor trait + List type + list ops
(mod option)      ;; Option type + Functor Option impl
(mod sequences)   ;; Seq type + lazy ops + unified collection API
(mod syntax)      ;; SList helpers + macro fold helpers + all macros

(export [numerics [*] formats [*] collections [*]
        option [*] sequences [*] syntax [*]])
```

Each submodule imports only what it needs from `primitives` and sibling submodules (e.g. `sequences` imports `numerics` and `collections`).

Library files are found via `find_lib_dir()`:
1. `CRANELISP_LIB` environment variable
2. `{project_root}/lib/`
3. Development fallback (`CARGO_MANIFEST_DIR/examples/lib/`)

The prelude and core are compiled as regular modules in topological order — no special loading path. The module graph naturally orders core before prelude before user modules.

## 5b. Synthetic Modules — `primitives` and `platform.stdio`

Two modules are registered by the Rust runtime without corresponding `.cl` files:

- **`primitives`** — All inline and extern primitive functions (`add-i64`, `eq-f64`, `int-to-string`, `vec-len`, etc.). Registered by `register_primitives()` in `typechecker/primitives.rs`.
- **`platform.stdio`** — Platform effect functions (`print`, `read-line`). Registered by `init_builtins()`.

Both use `register_builtin()` which stores names **qualified-only** in `universal` (e.g., `"primitives/add-i64"`, `"platform.stdio/print"`). No bare names are installed — visibility comes entirely through the import/export chain:

```
primitives      ──import──> core ──export──> prelude ──implied import──> user
platform.stdio  ──import──> core ──export──> prelude ──implied import──> user
```

For the single-file `check_program()` path (no module system), `install_synthetic_bare_names()` installs bare aliases from both synthetic modules, providing backwards-compatible access.

Synthetic module names are seeded into the `mod_name_to_short` map so that `(import [primitives [*]])` resolves without file discovery.

## 6. Import and Export Syntax

### `import` — Private

Bracket syntax, similar to `let`. Imported names are available within the current module but not re-exported:

```clojure
(import [core.option       [Some None]       ; refer Some, None unqualified. No alias.
         (core.string str) [concat join]      ; alias str, refer concat, join
         (core.fmt fmt)    [Display.*]        ; alias fmt, refer all Display methods
         core.math         [*]])              ; refer all, no alias
```

- Module spec: bare `core.option` = no alias. `(core.option opt)` = alias `opt`.
- Names list: `[name1 name2]` = specific. `[*]` = all public. `[Type.*]` = all type/trait members. `[]` = none (alias-only use, alias required).

### `export` — Re-export

Makes imported names part of this module's public API:

```clojure
(export [core.option [Option Some None]
         core.fmt    [Display.*]])
```

Both `import` and `export` are top-level forms, parsed from raw Sexp before macro expansion.

## 7. Search Path Strategy

Three-tier resolution for module names:

1. **Submodule of current** — `app/handler.cl` when inside `app`
2. **Project root** — `config.cl`
3. **Site library** — `~/.cranelisp/lib/core/option.cl`

Shadowing higher tiers is intentional — creating a local submodule with the same name as a root module is a deliberate choice.

Path mapping: `core.option` → `~/.cranelisp/lib/core/option.cl`

## 8. Visibility and Ambiguity

### Visibility

Public by default. Private variants use a trailing `-` on the definition form:

- `defn-` — private function
- `deftype-` — private type
- `deftrait-` — private trait
- `defmacro-` — private macro
- `mod-` — private submodule

These are special forms, not macros. Private definitions are accessible within the defining module and its submodule subtree.

### Name Resolution Architecture

> For a detailed walkthrough with ASCII diagrams and worked examples, see [Name Resolution](name-resolution.md).

The typechecker uses a three-layer name resolution system:

1. **`local_env`** — Function parameters, `let` bindings, `match` pattern variables. Lexically scoped, pushed/popped by scope.
2. **`scope`** — Maps bare names to qualified names (`"print"` → `"prelude/print"`). Populated by `begin_module_scope()` (imports) and `install_imported_names()` (REPL prelude). Controls what bare names are available in the current compilation unit.
3. **`universal`** — All definitions keyed by their qualified name (`"core/show"`, `"platform.stdio/print"`, `"primitives/add-i64"`). Persists across module boundaries. The source of truth for type schemes.

Lookup order in `TypeChecker::lookup()`:
1. `local_env` (params, let, match vars)
2. `scope` → resolve bare to qualified → look up in `universal`
3. `universal` directly (qualified names, or bare names in single-file mode)

### Key Functions

| Function | Purpose |
|---|---|
| `register_builtin(module, name, scheme, meta)` | Register in `CompiledModule` under synthetic module |
| `begin_module_scope(imports)` | Install Import entries into current module's `CompiledModule` |
| `end_module_scope()` | No-op (Import entries persist in `CompiledModule`) |
| `install_imported_names(imports)` | Add Import entries incrementally (REPL implied prelude import) |
| `get_module_public_names(module)` | Return public names from `CompiledModule.public_names()` |

### Ambiguity Rules

- Two unqualified imports of the same name → **compile error**
- `defn` over an imported name → **compile error** (no accidental shadowing)
- Local `let`/`fn` bindings shadow imports (allowed — lexically scoped)

## 9. Trait Disambiguation

When multiple traits define methods with the same name, dot notation disambiguates:

```clojure
(Display.show x)        ; calls Display's show
(Debug.show x)          ; calls Debug's show
```

Type inference resolves when unambiguous — if only one `show` is in scope and the argument type has exactly one matching impl, bare `show` works.

Fully qualified always works:

```clojure
(core.fmt/Display.show x)
```

### Orphan Rules

Relaxed — any module can implement any trait for any type. Coherence is checked at link time: duplicate impls for the same trait+type combination across modules is a compile error.

## 10. Macro Interaction

- `import`, `export`, `mod` are parsed from raw Sexp before macro expansion
- Module dependencies are loaded recursively before expanding the current module
- Macros from imported modules are available for expansion in the importing module
- Macro authors should use qualified names for non-prelude references in macro bodies
- Cyclic imports are banned (compile error)

## 11. REPL Integration

The REPL starts in a default `user` namespace. Module switching uses a slash command:

```
cranelisp> /mod app.sandwich
app.sandwich>
```

The current namespace is displayed in the prompt.

Additional REPL behaviors:

- Entering a module name at the REPL shows module info (consistent with self-documenting REPL design)
- `(import ...)` and `(export ...)` work at the REPL prompt
- Loaded modules are cached in `ReplSession`

## 12. Internal Representation — Per-Module GOT

Currently the JIT uses a single flat GOT (`Box<[*const u8; 1024]>`) — all functions in one table, `call_indirect` dispatches through it.

With modules: **per-module GOT with double indirection for cross-module calls**.

- Each module owns its own fixed-size GOT (`Box<[*const u8; 1024]>` — same as current single GOT)
- Fixed size keeps GOT address stable for `iconst` embedding in compiled code
- **Intra-module calls**: single indirect — load fn pointer from own GOT, call
- **Cross-module calls**: double indirect — module A holds pointer to module B's GOT base → load base → index into B's GOT → call

### Incremental Compilation Property

Recompiling module B updates B's GOT entries in place. Module A's pointer to B's GOT base is unchanged — A auto-picks-up B's new code on the next call. No need to patch A's code or GOT. This mirrors dynamic linking PLT/GOT and enables watch-mode hot reload.

### Cross-Module Constrained Polymorphism

Constrained polymorphic functions use **defining-module-lazy monomorphisation**: specializations are compiled into the defining module's GOT, triggered on demand by the first cross-module call site. This preserves the incremental property — if the defining module changes the function, recompiling that module recompiles all its specializations. Callers pick up the new versions automatically via GOT pointer stability, without being recompiled themselves.

### Compilation Units

Whole-module compilation: each module is fully compiled (parse → expand → build → typecheck → codegen) before dependent modules begin. This is required because macro exports must be fully compiled before importers can expand. Future goal: single-function recompilation granularity within a module.

### Additional Internal Changes

- `HashMap<String, _>` keys become fully qualified: `app.util/foo`
- `ModuleContext` struct for per-module import resolution
- Batch compilation: module graph → topological sort → compile leaves first
- JIT symbols use qualified names
- Each module's type environment, trait impls, and macros scoped to its GOT

## 13. Compiled Object Caching (Future)

```
~/.cranelisp/lib/core/option.cl                     ; lib source
~/.cranelisp/cache/{version-hash}/core/option.clo   ; lib compiled

~/projects/myproject/src/foo.cl                      ; project source
~/projects/myproject/build/foo.clo                   ; project compiled
```

- `{version-hash}` enables shared precompiled `core`/`std` across projects
- Content-hash staleness detection
- `.clo` = serialized types + compiled code

## 14. Watch Mode (Future)

- Filesystem watching triggers incremental recompilation of changed modules
- Hot-reload into running JIT state via GOT pointer stability
- REPL against live state
- Object cache for fast rebuilds

## 15. Implementation Plan

Eight phases, each independently useful and testable. Later phases build on earlier ones.

### Phase 1: Dot Notation ✓

**Status:** Complete.

**Goal:** `Type.Constructor` and `Trait.method` syntax — useful immediately, no multi-file support needed.

**Parser (`sexp.rs`):**
- Add `.` to `symbol_char()` so `Option.Some` parses as a single symbol
- Dotted symbols only: no `/` yet

**AST builder (`ast_builder.rs`):**
- When a symbol contains `.`, split into `parent.member`
- Constructor resolution: look up `parent` as type name, `member` as constructor
- Method resolution: look up `parent` as trait name, `member` as method

**Typechecker (`typechecker.rs`):**
- `lookup_env` handles dotted names by checking `constructor_to_type` and `method_to_trait`
- Disambiguation: `Display.show` resolves even when bare `show` would be ambiguous

**Tests:** `(Option.Some 42)`, `(Display.show 42)`, `(match x (Option.Some v) v Option.None 0)`.

**Touched files:** `sexp.rs`, `ast_builder.rs`, `typechecker.rs`

### Phase 2: Qualified Names ✓

**Status:** Complete.

**Goal:** Parser support for `module/name` syntax. Internal plumbing for qualified symbols.

**Parser (`sexp.rs`):**
- `qualified_symbol` PEG rule: module path (alpha segments joined by `.`) + `/` + local name (dotted, plain, or operator)
- `core.option/Some`, `core.option/Option.Some`, `core.math/+` parse as single `Sexp::Symbol`
- Disambiguation: `(/ 10 2)` still works — `/` alone (no alpha prefix) remains the division operator

**Internal representation (`names.rs`):**
- `split_qualified(name)` splits on first `/` → `Option<(&str, &str)>`
- `QualifiedName { module: Option<&str>, local: &str }` and `parse_name()` utility
- `resolve_bare_name()` strips both module prefix and type/trait prefix

**Validation:**
- Typechecker validates module prefix in qualified names against `module_names` set — unknown modules produce "unknown module 'xyz'" error
- REPL `describe_symbol` returns `None` for qualified names (pending Phase 7 REPL integration)

**Tests:** 9 parser tests, 7 names tests, 1 typechecker test.

**Touched files:** `sexp.rs`, `names.rs`, `typechecker/inference.rs`, `typechecker/introspect.rs`

### Phase 3: Multi-File Loading and Module Graph ✓

**Status:** Complete.

**Goal:** Load multiple `.cl` files as modules, compile in dependency order. The core infrastructure.

**Module discovery (`module.rs` — new):**
- `extract_mod_decls()` — separates `(mod name)` from other sexps before macro expansion
- `resolve_mod_path()` — search order: child directory (`parent_dir/stem/name.cl`) then sibling (`parent_dir/name.cl`)
- `path_to_module_id()` — file path → dot-separated module identity (e.g., `app.handler`)
- `ModuleId`, `ModuleInfo`, `ModuleGraph` types

**Module graph:**
- `ModuleGraph::build(entry_path)` — recursive discovery with cycle detection
- Topological sort (Kahn's algorithm) → compile leaves first
- Compile unit is whole-module (parse → expand → build → typecheck → codegen)

**Batch mode (`batch.rs`):**
- `run_project(entry_path)` — builds module graph, single-file delegates to `run()`, multi-file uses `ReplSession`-style incremental compilation
- Each non-entry module's definitions registered with qualified aliases (`module/name`)
- `call_main()` on `Jit` invokes the entry point

**Qualified name resolution (`typechecker/inference.rs`):**
- `Expr::Var` with `module/name` → look up `"module/name"` in env (registered by `register_qualified_aliases`)
- `Pattern::Constructor` with `module/Ctor` → same qualified lookup
- Dotted qualified names (`module/Type.Ctor`) validate parent type then look up qualified member
- Unknown module names produce clear error: "unknown module 'xyz'"

**Shared TypeChecker:**
- Single TypeChecker with `register_qualified_aliases()` for cross-module name visibility
- `module_names: HashSet<String>` tracks compiled modules for error messages

**Error handling:**
- `CranelispError::ModuleError { message, file, span }` variant for module-specific errors
- `format_error_in_file()` includes file path in error output
- Safety net: `(mod ...)` in `build_top_level` / `build_repl_input` → error if not intercepted

**Tests:** Module graph unit tests (10), integration tests (6): two-file project, three-file project, single-file via `run_project`, missing file error, cycle detection, qualified name resolution, unknown module error.

**Touched files:** new `module.rs`, `batch.rs`, `main.rs`, `error.rs`, `ast_builder.rs`, `typechecker/mod.rs`, `typechecker/inference.rs`, `jit.rs`, `lib.rs`, `Cargo.toml`

### Phase 4: Import, Export, and Visibility ✓

**Status:** Complete.

**Goal:** `(import ...)` and `(export ...)` forms with name resolution across modules. Visibility enforcement.

**Sexp-level parsing (`module.rs`):**
- `extract_module_decls()` extracts `mod`, `import`, and `export` from raw Sexp before macro expansion
- `ImportSpec`, `ExportSpec`, `ImportNames` data structures
- Bracket syntax: `[module-spec [names]]` pairs
- Alias syntax: `(core.string str)` vs bare `core.string`
- Glob imports: `[*]`, `[Type.*]`, `[]` (alias-only)

**Visibility (`ast.rs`, `ast_builder.rs`, `macro_expand.rs`):**
- `Visibility` enum (`Public`/`Private`) on `Defn`, `TraitDecl`, `TopLevel::TypeDef`, `TopLevel::DefnMulti`
- AST builder recognises `defn-`, `deftype-`, `deftrait-`, `defmacro-` suffix variants
- Private names excluded from qualified alias registration and cross-module import

**Module scope management (`typechecker/mod.rs`):**
- `begin_module_scope()` — installs Import entries into current module's `CompiledModule`, detects ambiguity
- `end_module_scope()` — no-op (Import entries persist in `CompiledModule`)
- `check_definition_conflict()` — errors if definition shadows explicit import (checks Import entries in `CompiledModule`)

**Import resolution (`batch.rs`):**
- `resolve_module_imports()` resolves `ImportSpec` entries to `(bare_name, source_module)` pairs
- Specific names validated against source module's public names
- Glob imports include all public names
- Member glob imports (`[Type.*]`) import type constructors or trait methods
- Module aliases register in `module_names` for qualified access

**Export processing (`batch.rs`):**
- After module compilation, export declarations re-register names from source modules
- Re-exported names become part of the exporting module's public API

**Ambiguity enforcement:**
- Two unqualified imports of same name from different sources → compile error
- `defn` over imported name → compile error
- Local `let`/`fn` bindings shadow imports (allowed — lexically scoped)
- Import shadows prelude → allowed

**Tests:** 13 unit tests for import/export parsing, 11 unit tests for scope management, 19 integration tests covering: specific imports, glob imports, alias access, re-exports, visibility enforcement (private defn/deftype), ambiguity detection, definition conflicts.

**Touched files:** `module.rs`, `ast.rs`, `ast_builder.rs`, `macro_expand.rs`, `batch.rs`, `typechecker/mod.rs`, `typechecker/tests.rs`, plus visibility field additions across 15+ files

### Phase 5: Per-Module GOT — Status: Complete

**Goal:** Each module owns its function pointer table, enabling future incremental recompilation.

**Implementation:**
- GOT tables live on `CompiledModule`: `got_table: Option<Box<[*const u8; GOT_TABLE_SIZE]>>` with `GOT_TABLE_SIZE = 1024`
- `CompiledModule` methods: `ensure_got()` (lazy allocation), `got_table_addr()`, `allocate_got_slot(span)`, `write_got_slot(slot, code_ptr)`, `restore_got_entries(saved)`
- `Jit` has no GOT state — `build_fn_slots_from_modules()` iterates `CompiledModule` GOTs to build `FnSlot` maps
- `FnSlot` carries `got_ref: GotReference::Immediate(addr)` — the GOT base address of the owning module
- Cross-module calls use the **same** cost as intra-module calls — just a different `iconst` base address per call site. No double indirection needed because `Box<[_; N]>` has a stable heap address
- Callers allocate GOT slots via `CompiledModule::allocate_got_slot()`, compile via `Jit::compile_defn()`, then write the code pointer back via `CompiledModule::write_got_slot()`

**Incremental property:**
- Recompiling module B updates B's GOT in place
- A's compiled code embeds B's stable GOT address → A picks up new code automatically

**Deferred: Cross-module constrained polymorphism**
- When module B calls a constrained fn from module A, the monomorphised specialization should be compiled into A's GOT
- Currently, cross-module constrained polymorphism is not supported — documented as a known limitation

**Touched files:** `module.rs`, `jit.rs`, `codegen/mod.rs`, `codegen/apply.rs`, `codegen/closures.rs`, `batch.rs`, `repl/input.rs`

### Phase 6: Core Library + Prelude Mechanism ✓

**Status:** Complete.

**Goal:** Extract embedded prelude to a library file loaded via the module graph. Implement auto-import convention. Builtins registered as synthetic modules.

**File layout:**
```
lib/
  prelude.cl              ← (export [core [*] primitives [...]])
  core.cl                 ← thin re-export shell: (mod numerics) (mod formats) ... (export [...])
  core/
    numerics.cl           ← Num, Eq, Ord traits + Int/Float impls + inc
    formats.cl            ← Display trait + show impls
    collections.cl        ← Functor trait + List type + list ops + Functor List impl
    option.cl             ← Option type + Functor Option impl
    sequences.cl          ← Seq type + lazy ops + Functor Seq + unified API
    syntax.cl             ← SList helpers + macro fold helpers + all macros
examples/
  hello.cl                ← finds prelude via lib/ directory
  modules/
    main.cl               ← finds prelude via project root fallback
```

**Synthetic modules (`typechecker/primitives.rs`):**
- `init_builtins()` registers `print`/`read-line` under `"platform.stdio"` module via `register_builtin()`
- `register_primitives()` registers all inline/extern primitives under `"primitives"` module
- Names stored qualified-only in `universal` — no bare names. Bare access comes through the import chain.
- `install_synthetic_bare_names()` provides backwards-compatible bare access for the single-file `check_program()` path

**Library directory resolution (`module.rs`):**
- `find_lib_dir(project_root)` searches: `CRANELISP_LIB` env → `{project_root}/lib` → `{CARGO_MANIFEST_DIR}/examples/lib` (dev fallback)
- `resolve_mod_path_with_lib()` extends standard child/sibling resolution with lib directory fallback
- Export declarations trigger discovery of referenced modules through lib fallback

**Prelude auto-discovery (`module.rs`):**
- `find_prelude(entry_path)` searches: sibling of entry → project root → `{CARGO_MANIFEST_DIR}/examples/prelude.cl` (dev fallback)
- `ModuleGraph::build()` auto-discovers prelude and injects it as a synthetic dependency of all non-prelude modules
- Each non-prelude module gets an implied `(import [prelude [*]])`
- Prelude is just a regular module — compiled in topological order like any other

**Batch mode (`batch.rs`):**
- `run()` is the truly-no-prelude path for single-module projects (no prelude found)
- `run_project()` compiles core → prelude → user modules via the module graph — no separate `load_prelude()` call
- `mod_name_to_short` map seeded with synthetic module names from `tc.module_names`
- Sequential per-sexp compilation: each item fully processed before the next, allowing macros to reference earlier definitions

**REPL (`repl/mod.rs`):**
- `compile_module_graph()` — shared method for compiling a module graph into the session. Handles imports, GOTs, type defs, sequential compilation, exports, qualified aliases, and scope cleanup. Used by both `load_prelude()` and `load_module_by_name()`.
- `load_prelude()` discovers `prelude.cl`, builds a `ModuleGraph`, calls `compile_module_graph()`, then installs prelude's public names as bare names via `install_imported_names()` (the implied `(import [prelude [*]])`).
- No special `load_prelude_module()` — prelude uses the same compilation path as all other modules.

**Test infrastructure:**
- `src/unittest_prelude.cl` + `tests/test_prelude.cl` — trimmed test fixtures (duplicated, can diverge)
- Each test module uses `include_str!` directly — no shared `prelude.rs` module
- Excludes macros, macro helpers, and Sexp type (macro compilation uses the disk-based module graph)
- Decoupled from the standard library: tests don't slow down as the stdlib grows

**Re-export mechanism (`typechecker/mod.rs`):**
- `reexport_name()` copies universal, type_defs, constructor_to_type, symbol_meta, and constrained_fns from source module's qualified names to bare and destination module's qualified names
- `reexport_origins` map tracks provenance (`dest_qualified → source_qualified`), so `qualified_name()` resolves through re-export chains to the original defining module

**Touched files:** `module.rs`, `batch.rs`, `repl/mod.rs`, `typechecker/mod.rs`, `typechecker/primitives.rs`, `sexp.rs`, `typechecker/tests.rs`, `typechecker/inference.rs`, `typechecker/introspect.rs`, `typechecker/traits.rs`, `tests/integration.rs`, `tests/rc.rs`. New: `examples/lib/core.cl`. Changed: `examples/prelude.cl`

### Phase 7: REPL Integration ✓

**Status:** Complete.

**Goal:** Module-aware REPL with namespace switching, self-documenting module forms, on-demand module loading, and module-qualified display.

**7A: Self-documentation via `SymbolMeta` enum:**
- Replaced `FnMeta` with `SymbolMeta` enum (`SpecialForm`, `Primitive { kind: PrimitiveKind }`, `UserFn`)
- `PrimitiveKind`: `Inline`, `Extern`, `Platform` — classifies built-in functions
- `SpecialForm` and `Primitive` variants require `String` docstring (not `Option`) — Rust compiler enforces documentation
- Registered `mod`, `import`, `export` as special forms — typing them at the REPL shows usage description
- Removed static `is_inline_primitive()`/`is_extern_primitive()` — replaced with `get_symbol_meta(name)` queries (resolves via module-walk)

**7B: Namespace state + prompt:**
- `current_module: ModuleId` field on `ReplSession`, defaults to `ModuleId("user")`
- Prompt shows module name: `user> `, continuation line padded to match

**7C: `/mod` command:**
- `/mod` (no arg) switches back to `user` module
- `/mod <name>` loads (if needed) and switches to the named module
- Listed in `/help`

**7D: Module loading infrastructure:**
- `resolve_module_imports()` moved from `batch.rs` to `module.rs` (shared by both batch and REPL)
- `resolve_module_path_from_name()` in `module.rs` — converts module name to file path from cwd
- `compile_module_graph()` on `ReplSession` — shared method for compiling a module graph. Used by both `load_prelude()` and `load_module_by_name()`.
- `load_module_by_name()` — discovers module file, builds module graph, calls `compile_module_graph()`, skips already-loaded modules
- `LoadedModule` struct tracks per-module `defined_names`
- `prelude_module_ids: HashSet<ModuleId>` — skip prelude modules on reload
- Lazy loading: sexps scanned for qualified names (containing `/`), module prefixes auto-loaded before evaluation

**7E: Namespace scope switching:**
- Each module's names live in its own `CompiledModule` — switching modules changes `current_module_path`
- User definitions tracked via `track_repl_defn()` — writes into `CompiledModule` and registers module prefix
- Switching to another module changes which `CompiledModule` is consulted for bare-name resolution

**7F: Module-scoped `/l`, module info, REPL import:**
- `/l` shows in-scope symbols grouped by category; `list_symbols()` walks the current module's `symbols` and `type_defs` maps — all names flow through the module system (traits via `ModuleEntry::TraitDecl`, builtin types via `primitives` module imports, overloads via `Def` entries)
- `/l <module>` shows that module's public definitions with types
- Typing a module name at the REPL shows module info (equivalent to `/l <module>`)
- `(import [<module> [names]])` at the REPL loads the module on demand and installs imported names as bare names
- `install_imported_names()` on TypeChecker — incremental import without clearing existing imports

**7G: Module-qualified display names:**
- `TypeChecker::qualified_name(bare)` resolves bare names to their qualified form via `scope` mapping, then follows `reexport_origins` to the defining module (e.g., `concat` shows as `core/concat` not `prelude/concat`)
- REPL displays qualified names for functions and primitives (e.g., `core/concat`, `platform.stdio/print`)
- Trait methods, constructors, types, and traits display with their natural qualifiers (`Display.show`, `Option.None`) — not module-qualified
- `/l <filter>` shows qualified names in full type info mode
- Inline primitives not re-exported by prelude are hidden from user scope (e.g., `add-f64` → "Unknown symbol")
- Private fold helpers (`defn-` in core) hidden from user scope

**Tests:** All 351 unit + 361 integration tests pass.

**Touched files:** `typechecker/mod.rs`, `typechecker/primitives.rs`, `typechecker/introspect.rs`, `typechecker/inference.rs`, `typechecker/overloads.rs`, `repl/format.rs`, `repl/input.rs`, `repl/handlers.rs`, `repl/mod.rs`, `repl/commands.rs`, `batch.rs`, `module.rs`

### Phase 8: Caching and Watch Mode (Future)

**Compiled object caching:**
- `.clo` files: serialized types + compiled native code
- Content-hash staleness detection
- `~/.cranelisp/cache/{version-hash}/` for shared library cache
- Project `build/` directory for project-specific cache

**Watch mode:**
- Filesystem watcher on project source files
- Incremental recompilation of changed modules (per-module GOT enables this)
- Hot-reload into running JIT state
- REPL against live, continuously-updated state

### Phase Dependencies

```
Phase 1: Dot Notation
    |
Phase 2: Qualified Names
    |
Phase 3: Multi-File Loading ──────────┐
    |                                  |
Phase 4: Import/Export/Visibility      |
    |                                  |
    ├──────────────────────────────────┘
    |
Phase 5: Per-Module GOT
    |
Phase 6: Prelude Migration
    |
Phase 7: REPL Integration
    |
Phase 8: Caching + Watch Mode
```

Phases 1–2 are parser/resolution changes that benefit the language immediately (trait disambiguation, cleaner constructor access) even without multi-file support. Phase 3 is the big infrastructure phase. Phases 4–5 complete the core module system. Phases 6–7 polish the developer experience. Phase 8 is future work.

## 16. Open Questions

- **Macro hygiene with modules** — how do macro-introduced symbols interact with the importing module's namespace?
- **Circular type references** — forward declarations across module boundaries
- **`core` vs `std` boundary** — what goes in `core` (always available) vs `std` (importable)?
- **Match patterns with dot notation** — `(match opt (Option.Some x) x Option.None 0)` may require pattern syntax changes
