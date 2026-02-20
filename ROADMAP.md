# Cranelisp Roadmap

## What we have today

Working pipeline from source to JIT execution with a rich type system, closures, traits, monadic IO, algebraic data types, macros, reference counting, and lazy sequences.

- **Parser**: two-phase pipeline — S-expression reader (`sexp.rs`) then AST builder (`ast_builder.rs`); full source spans
- **Type system**: Hindley-Milner inference (Algorithm W), let-polymorphism, constrained polymorphism with monomorphisation, optional type annotations
- **Types**: `Int`, `Bool`, `String`, `Float`, `(Fn [params] ret)`, `(IO a)`, `(Option a)`, `(List a)`, `(Seq a)`, `(Vec a)`, `Sexp` (7 data constructors), `(SList a)` (macro-internal list)
- **ADTs**: `deftype` with product (`(deftype Point [:Int x :Int y])`), sum (`(deftype (Option a) None (Some [:a val]))`), and enum (`(deftype Color Red Green Blue)`) forms; shortcut syntax for bare field names
- **Pattern matching**: `match` expression with constructor, wildcard (`_`), and variable patterns
- **Expressions**: integer/boolean/float/string literals, variables, operators via trait dispatch (`+ - * / = < > <= >=`), `let`, `if`, `fn` (lambda), function application, `match`
- **Top-level**: `defn` (single and multi-signature) with forward references and mutual recursion, `deftrait`, `impl`, `deftype`, `defmacro`
- **Closures**: first-class functions, lambda capture, auto-currying
- **Traits**: `Num`, `Eq`, `Ord`, `Display`, `Functor` with static dispatch; user-defined traits; operators are trait methods; trait impls for ADTs (concrete and polymorphic)
- **Multi-signature functions**: dispatch by arity and type, mangled names
- **Auto-currying**: partial application returns closure capturing applied args
- **Constrained polymorphism**: functions using trait methods are monomorphised at call sites (e.g. `(defn add [x y] (+ x y))` works for both Int and Float); cross-module mono specializations are compiled into the defining module's GOT and `.o` file
- **Tail call optimization**: loop-based self-TCO for recursive functions
- **Reference counting**: full RC with drop glue (Phases 2A-2F); `alloc_with_rc`/`free` with size header; `HeapCategory` discrimination; per-type drop functions for recursive types
- **Macro system**: `defmacro` with quasiquote/unquote/splice-unquote, 8-phase implementation; compile-time expansion with depth limit; return-type validation (must return `Sexp`); bare-symbol expansion for zero-arg macros; `begin` multi-form expansion (macro results can splice multiple top-level forms); defmacro-in-results (expansion output containing `defmacro` forms are compiled and registered)
- **Prelude macros**: `list`, `do`, `bind!`, `->` (thread-first), `->>` (thread-last), `cond`, `case`, `vec`, `const`/`const-` (named constants via bare-symbol macro expansion), `def`/`def-` (named values via zero-arg function + macro)
- **Lazy sequences**: thunk-based `Seq` type with `range-from`, `iterate`, `repeat`; unified collection API (`map`, `filter`, `take`, `drop`, `reduce`) dispatching across Vec, List, and Seq
- **Vec type**: `[1 2 3]` bracket syntax, `get`, `set`, `len`, `push`, `concat`
- **Higher-kinded types**: `Functor` trait with `fmap` for List, Option, Seq
- **Docstrings**: on `defn`, `deftrait`, `deftype`, and constructors; accessible via `/doc` in REPL
- **Type annotations**: `:Type` and `[:Type param]` syntax on function parameters and return types
- **Monadic IO**: `IO` is a compiler-seeded ADT `(deftype (IO a) (IOVal [:a ioval]))`; `pure` and `bind` are library functions in `lib/core/io.cl`; `do` and `bind!` are prelude macros; `main` must return `IO _`; platform functions return IOVal-wrapped results via `CLIO<CL>` type in the platform crate
- **Prelude**: traits, operators, types, and macros defined in domain-oriented submodules under `lib/core/` (numerics, formats, collections, option, sequences, syntax); `lib/core.cl` is a thin re-export shell; `lib/prelude.cl` re-exports core; auto-discovered via implicit `(import [prelude [*]])` injection and unified module resolution; optional — an empty prelude is valid
- **Codegen**: Cranelift JIT, all values are `i64` at runtime (Bool as 0/1, String as heap pointer, Float as f64 bitcast)
- **REPL**: interactive evaluation with introspection commands (`/sig`, `/doc`, `/type`, `/info`, `/source`, `/sexp`, `/ast`, `/clif`, `/disasm`, `/time`, `/mem`, `/list`, `/expand`, `/mod`, `/reload`, `/help`); function redefinition; self-documenting feedback for all language constructs; module-aware namespace switching with `/mod`; on-demand module loading; REPL `(import ...)` support; `SymbolMeta` enum enforces self-documentation for all built-in symbols; `/list` with category grouping and partial/module filtering; `/info` with multi-line consolidated view (classification, definition form, trait impls, specializations, JIT info); **save-to-file**: every successful definition automatically regenerates the backing `.cl` source file with consistent formatting, section ordering, dependency-sorted functions, and qualified constructor/trait method references; **file watching**: automatic detection of external `.cl` file changes with incremental module reload, type compatibility validation, and rollback on failure — locked modules reject new definitions but allow expression evaluation; **cross-module ADT display**: values of ADT types defined in other modules display with module-qualified type and constructor names (e.g. `(foo/Point2 3 4) :: foo/Point2`)
- **String primitives**: `str-concat` (String → String → String), `quote-sexp` (Sexp → Sexp); SList helpers in core: `sfold`, `sreverse`, `sconcat`, `sempty?`
- **stdin**: `read-line` (IO String), `parse-int` (String → Option Int)
- **Platform effects**: all IO functions come from dynamically-loaded platform DLLs — no built-in default. `(platform name)` declares a platform DLL dependency, creating a `platform.<name>` module; `(import [platform.<name> [*]])` brings functions into scope. Shared `cranelisp-platform` crate defines the C-ABI contract (`PlatformFn`, `HostCallbacks`, `PlatformManifest`, `ABI_VERSION`), safe wrapper types (`CLInt`, `CLString`, `CLBool`, `CLFloat` — `#[repr(transparent)]` over `i64` with `From`/`Into` conversions), `HostContext` for global allocator storage, `declare_platform!` macro for declarative metadata-driven manifest generation, and `manifest_to_descriptors()` / `OwnedPlatformFnDescriptor` shared between host and DLL. Platform authors write zero `unsafe` code — all marshalling via standard Rust idioms (`s.as_str()`, `.into()`). Platform functions participate in resolution-based dispatch via `ResolvedCall::BuiltinFn` and `DefKind::Primitive` module entries. `resolve_platform_path()` searches `./platforms/`, `./target/debug/`, `./target/release/`, and `~/.cranelisp/platforms/`. `Jit` uses `symbol_lookup_fn` closure with dynamic symbol map for post-construction DLL loading. Two platform DLLs: `platforms/stdio/` (reference stdio: `print`, `read-line`) and `platforms/test-capture/` (in-memory buffers for test harnesses). Standard library (`lib/core.cl`, `lib/core/`, `lib/prelude.cl`) is platform-independent. REPL intercepts `(platform ...)` directly, stores `ModuleEntry::PlatformDecl` in declaring module. `/list` shows "Platforms" category
- **Errors**: span-aware error reporting with source context for parse, type, and codegen errors
- **Dot notation**: `Type.Constructor` and `Trait.method` syntax for disambiguation (e.g. `Option.Some`, `Display.show`, `Num.+`)
- **Qualified names**: `module/name` syntax resolves across modules (e.g. `util/helper`, `math/double`)
- **CLI modes**: `cranelisp` (bare REPL), `cranelisp foo.cl` (REPL with file loaded), `cranelisp --run foo.cl` (batch: compile + call main + exit), `cranelisp --run` (batch with `user.cl` from CWD), `cranelisp --exe <output> [file.cl]` (compile to standalone native executable)
- **Module system**: multi-file projects with `(mod name)` declarations, dependency graph with cycle detection, topological compilation order, qualified name access (`module/name`), `(import ...)` with specific/glob/member-glob names and auto-discovery of root modules, `(export ...)` for re-exports, visibility (`defn-`, `deftype-`, `deftrait-`, `defmacro-`), per-module scoping, ambiguity detection, per-module GOTs for incremental recompilation, unified module resolution (`resolve_module`: submodule→project root→lib), implicit `(import [prelude [*]])` for all non-prelude modules, standard library in `lib/` directory
- **Synthetic modules**: `primitives` and `macros` registered by Rust runtime — builtins are qualified-only (`primitives/add-i64`), accessible to user only through the import/export chain (core imports them, prelude re-exports). The `macros` module provides `Sexp` and `SList` types for the macro system (compiler-seeded, not user-modifiable); implicit `(import [macros [*]])` injected for all modules. Platform modules (`platform.stdio`, etc.) are created dynamically when DLLs are loaded
- **Per-module symbol tables**: `CompiledModule` struct with unified `symbols` map — `ModuleEntry` enum (Def, Import, Reexport, TypeDef, TraitDecl, Constructor, Macro, PlatformDecl, Ambiguous) keyed by `Symbol` newtype. TypeDef entries in `symbols` use `constructor_scheme: Option<Scheme>` for product types where constructor and type share a name. Module-walk resolution (`resolve_in_module`) follows Import/Reexport chains with depth limit. All legacy flat-dicts removed — name→scheme resolution, `SymbolMeta`, constructors, type definitions, constrained functions, trait declarations, method-to-trait mapping, HKT param indices, and operator sets all stored in or derived from `CompiledModule` and resolved via module-walk methods. Newtype wrappers (`Symbol`, `ModuleFullPath`) make each name's role explicit at the type level. `list_symbols()` walks current module's `symbols`; `describe_symbol()` classifies via single `lookup_entry_via_modules()` + `ModuleEntry` match. REPL displays module-qualified names for functions and primitives, resolving through re-export chains to the defining module (e.g., `core/concat` not `prelude/concat`). Unified method resolution pipeline — operators and non-operator trait methods share the same `resolve_methods()` pass
- **Jit.defs elimination**: `CompiledModule` is now the sole authority for all function metadata (source, sexp, defn, CLIF IR, disasm, code_size, compile_duration, got_slot, code_ptr, param_count). Jit no longer stores `DefEntry`, `DefKind`, or per-function maps (`defs`, `def_module`). `build_fn_slots_from_modules()` builds the fn_slots map from `CompiledModule` data
- **Bare-name ambiguity handling**: When two sources register the same bare name (e.g. two traits defining `show`, or two glob imports bringing `add`), the entry becomes `ModuleEntry::Ambiguous` with a warning. Using the ambiguous bare name produces a type error listing qualified alternatives (`Display.show`, `Debug.show`, `module/name`). Dotted names (`Trait.method`, `Type.Constructor`, `Type.field`) and qualified names (`module/name`) always resolve directly, bypassing ambiguity
- **E2E tests**: data-driven REPL transcript tests — `.cl`/`.out` file pairs in `tests/e2e/`, piped stdin with full transcript comparison (banner, prompts, input echo, output)
- **Tests**: 825 total (unit + integration + e2e + RC + platform, 5 ignored)
- **Examples**: 20 runnable files (including multi-file module and import examples)

## Near-term priorities

Small items that build on the existing foundation with minimal architectural change.

| Feature | Rationale |
|---|---|
| **Division-by-zero handling** | `sdiv` traps on zero; need a runtime check or error, not a process crash |
| **Better error recovery** | Parser currently stops at first error; accumulating multiple errors improves the edit cycle |
| **Map type** | Persistent hash map — the missing core collection alongside List and Vec |
| **Default method implementations** | Derive `<=` from `<` and `=`, etc. |

## Medium-term goals

Features that require meaningful new infrastructure but keep the core architecture intact.

| Feature | Rationale |
|---|---|
| **File watch mode (cascade)** | Cascade recompilation to dependent modules when a dependency's types change |
| ~~**Compilation to standalone executable (AOT)**~~ | ~~Cranelift supports object file output; generate distributable binaries without requiring the JIT runtime~~ — **done**: `--exe` CLI flag and `/exe` REPL command; links cached `.o` files with `cranelisp-exe-bundle` staticlib via system linker; produces native macOS aarch64 executables |
| ~~**Improve platform type abstraction**~~ | ~~Fully encapsulate cranelisp runtime types behind Rust-native types~~ — **done**: `CLInt`/`CLString`/`CLBool`/`CLFloat` wrapper types with `From`/`Into`, `HostContext`, declarative `declare_platform!` macro; platform authors write zero unsafe |
| **Parallel build/recompile** | Compile independent modules in parallel during batch build and cascade reload |
| **Backend abstraction** | Extract `Backend` trait from `Jit` facade; backend-neutral naming; enables alternative code generators (`docs/backend-selection.md`) |
| **Deriving** | Auto-generate Eq/Ord/Display impls for data types |
| **Effect system extensions** | Roc-style Task values, `!` suffix syntax, typed error channels |

Recently completed medium-term goals (now documented in "What we have today"):
- **Compiled object caching** — two-tier cache with SHA-256 source invalidation and binary fingerprinting (batch and REPL)
- **Platform DLL loading** — all IO from dynamically-loaded platform DLLs
- **Standalone executable export (AOT)** — `--exe` CLI flag and `/exe` REPL command; links cached `.o` files with runtime staticlib via system linker; platform initialization via `cranelisp_init_platform()` in startup stub

## Long-term / deferred

Features that represent major architectural shifts or are speculative.

| Feature | Rationale |
|---|---|
| **Stack objects / box** | Value types on the stack by default, explicit `box` for heap allocation; reduces GC pressure for small structs |
| **Threading** | Concurrency support via shared-nothing tasks with typed channels and inferred ownership (`docs/concurrency.md`) |
| **Polymorphic recursion** | Requires extensions beyond standard HM; rare in practice |
| **Optimization passes** | Constant folding, dead code elimination, inlining |

## Known rough edges

| Issue | Impact |
|---|---|
| Division by zero traps the process | Runtime crash on `(/ x 0)` |
| No stack overflow protection | Silent crash on deep recursion |
| No integer overflow checks | `iadd`/`isub`/`imul` wrap silently |
