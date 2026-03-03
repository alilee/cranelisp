# Cranelisp Roadmap

## What we have today

Working pipeline from source to JIT execution with a rich type system, closures, traits, monadic IO, algebraic data types, macros, reference counting, and lazy sequences.

- **Language specification**: Implementation-agnostic spec in `docs/spec/` (14 files) covering lexical structure, grammar, type system, expression semantics, definitions, pattern matching, traits, modules, macros, IO model, standard library, and runtime model. Includes EBNF grammars, typing judgments, and a complete builtin reference. Normative sections (1-10, 12) define language-level requirements; Section 11 and Appendix A are non-normative reference documentation for the standard library. Sufficient for a conforming re-implementation in any language.

- **Parser**: two-phase pipeline — S-expression reader (`sexp.rs`) then AST builder (`ast_builder.rs`); full source spans
- **Type system**: Hindley-Milner inference (Algorithm W), let-polymorphism, constrained polymorphism with monomorphisation, optional type annotations
- **Types**: `Int`, `Bool`, `String`, `Float`, `(Fn [params] ret)`, `(IO a)`, `(Option a)`, `(List a)`, `(Seq a)`, `(Vec a)`, `Sexp` (7 data constructors), `(SList a)` (macro-internal list)
- **ADTs**: `deftype` with product (`(deftype Point [:Int x :Int y])`), sum (`(deftype (Option a) None (Some [:a val]))`), and enum (`(deftype Color Red Green Blue)`) forms; shortcut syntax for bare field names
- **Pattern matching**: `match` expression with constructor, wildcard (`_`), and variable patterns
- **Expressions**: integer/boolean/float/string literals, variables, operators via trait dispatch (`+ - * / = < > <= >=`), `let`, `if`, `fn` (lambda), function application, `match`
- **Top-level**: `defn` (single and multi-signature) with forward references and mutual recursion, `deftrait`, `impl`, `deftype`, `defmacro`
- **Closures**: first-class functions, lambda capture, auto-currying
- **Traits**: `Num` (checked arithmetic), `Eq`, `Ord`, `Display`, `Functor`, `Unchecked` (raw arithmetic) with static dispatch; trait-qualified mangling (`Trait.method$Type`); user-defined traits; operators are trait methods; trait impls for ADTs (concrete and polymorphic); default method implementations (not on HKT traits); same-named methods across traits with scope-aware disambiguation
- **Multi-signature functions**: dispatch by arity and type, mangled names
- **Auto-currying**: partial application returns closure capturing applied args
- **Constrained polymorphism**: functions using trait methods are monomorphised at call sites (e.g. `(defn add [x y] (+ x y))` works for both Int and Float); cross-module mono specializations are compiled into the defining module's GOT and `.o` file
- **Tail call optimization**: loop-based self-TCO for recursive functions
- **Reference counting**: sound RC with atomic operations (Phases 2A-2F + Step 11); `alloc_with_rc`/`free` with size header; `HeapCategory` discrimination; per-type drop functions for recursive types; closure drop glue with per-lambda drop functions; consuming calling convention for cranelisp calls (callee owns heap-typed params), borrowed convention for extern calls (caller decs all heap-typed temps); match scrutinee dec; constructor Var arg inc; accessor field inc; liveness-based last-use ownership transfer; `atomic_rmw` for thread safety with par-let/par-bind!; `CLOwned<T>` for safe Effect closure captures; uniqueness tracking with borrowed reads from unique owners (skip inc/dec for field reads); static COW bypass (skip runtime rc check when Vec is known-unique + last-use)
- **Macro system**: `defmacro` with quasiquote/unquote/splice-unquote, 8-phase implementation; compile-time expansion with depth limit; return-type validation (must return `Sexp`); bare-symbol expansion for zero-arg macros; `begin` multi-form expansion (macro results can splice multiple top-level forms); defmacro-in-results (expansion output containing `defmacro` forms are compiled and registered); reader shortcuts: quote (`'expr`), auto-gensym (`x#` in quasiquote), anonymous function (`#(...)`)
- **Reader shortcuts**: `'expr` → Sexp value (quote), `x#` → auto-gensym in quasiquote (hygienic bindings), `#(+ % 1)` → anonymous function shorthand with `%`/`%1`-`%9` params
- **Prelude macros**: `list`, `do`, `bind!`, `->` (thread-first), `->>` (thread-last), `cond`, `case`, `vec`, `const`/`const-` (named constants via bare-symbol macro expansion), `def`/`def-` (named values via zero-arg function + macro)
- **Lazy sequences**: thunk-based `Seq` type with `range-from`, `iterate`, `repeat`; unified collection API (`map`, `filter`, `take`, `drop`, `reduce`) dispatching across Vec, List, and Seq
- **Vec type**: `[1 2 3]` bracket syntax, `get`, `set`, `len`, `push`, `concat`
- **Higher-kinded types**: `Functor` trait with `fmap` for List, Option, Seq
- **Docstrings**: on `defn`, `deftrait`, `deftype`, and constructors; accessible via `/doc` in REPL
- **Type annotations**: `:Type` and `[:Type param]` syntax on function parameters and return types
- **Monadic IO**: `IO` is a compiler-seeded ADT with four constructors: `Pure` (tag=0), `Effect` (tag=1, 24 bytes: `[tag, thunk_ptr, resource_token]`), `Bind` (tag=2, internal), `Par` (tag=3, internal). `pure` is a library function; `bind` is an inline primitive; `do` and `bind!` are prelude macros. Platform functions return `Effect` nodes via `CLIO::effect()` (token=0) or `CLIO::effect_on_resource(token, f)` (for `ResourceSerial` effects). Effects are deferred and forced by a flat trampoline loop (`IoTask::run()`) with O(1) stack depth. **Automatic IO scheduling** (`src/schedule.rs`): after macro expansion, the compiler analyses `bind!` chains for data-independent non-Sequential calls and inserts `Par` nodes automatically; the trampoline serialises `ResourceSerial` branches sharing the same runtime token. `par-bind!` is removed — users write `bind!` and the compiler handles parallelism. Platform scheduling classes: `Sequential`, `Commutative`, `ResourceSerial` (ABI_VERSION=3)
- **Prelude**: traits, operators, types, and macros defined in domain-oriented submodules under `lib/core/` (numerics, formats, collections, option, sequences, syntax, derive); `lib/core.cl` is a re-export shell with explicit export lists — `syntax` exports only user-facing macros (`const`, `def`, `list`, `do`, `cond`, `str`, `->`, `->>`, `case`, `bind!`, `vec`); `sequences` exports the public API (`Seq`, `range-from`, `iterate`, `repeat`, `to-list`, `seq`, `map`, `filter`, `take`, `drop`, `reduce`) with lazy-sequence internals and `SeqCons`/`SeqNil` constructors hidden; `lib/prelude.cl` re-exports core with selective primitives; auto-discovered via implicit `(import [prelude [*]])` injection and unified module resolution; optional — an empty prelude is valid
- **Codegen**: Cranelift JIT, all values are `i64` at runtime (Bool as 0/1, String as heap pointer, Float as f64 bitcast)
- **REPL**: interactive evaluation with introspection commands (`/sig`, `/doc`, `/type`, `/info`, `/source`, `/sexp`, `/ast`, `/clif`, `/disasm`, `/time`, `/mem`, `/list`, `/expand`, `/mod`, `/reload`, `/run-tests`, `/help`); function redefinition; self-documenting feedback for all language constructs; module-aware namespace switching with `/mod`; on-demand module loading; REPL `(import ...)` support; `SymbolMeta` enum enforces self-documentation for all built-in symbols; `/list` with category grouping and partial/module filtering; `/info` with multi-line consolidated view (classification, definition form, trait impls, specializations, JIT info); **save-to-file**: every successful definition automatically regenerates the backing `.cl` source file with consistent formatting, section ordering, dependency-sorted functions, and qualified constructor/trait method references; **file watching**: automatic detection of external `.cl` file changes with incremental module reload, cascade reload of transitive dependents, type compatibility validation, and rollback on failure — locked modules reject new definitions but allow expression evaluation; **safety guards**: type-breaking redefinitions of previously compiled functions are refused (must edit file to trigger cascade recompile); **background cache writes**: REPL cache writes happen on a background thread via mpsc channel for responsiveness; **cross-module ADT display**: values of ADT types defined in other modules display with module-qualified type and constructor names (e.g. `(foo/Point2 3 4) :: foo/Point2`)
- **String primitives**: `str-concat` (String → String → String), `quote-sexp` (Sexp → Sexp); SList helpers in `core.syntax`: `sfold`, `sreverse`, `sconcat`, `sempty?` (internal to `core.syntax`; available via direct `(import [core.syntax [*]])`)
- **stdin**: `read-line` (IO String), `parse-int` (String → Option Int)
- **Platform effects**: all IO functions come from dynamically-loaded platform DLLs — no built-in default. `(platform name)` declares a platform DLL dependency, creating a `platform.<name>` module; `(import [platform.<name> [*]])` brings functions into scope. Shared `cranelisp-platform` crate defines the C-ABI contract (`PlatformFn`, `HostCallbacks`, `PlatformManifest`, `ABI_VERSION`), safe wrapper types (`CLInt`, `CLString`, `CLBool`, `CLFloat` — `#[repr(transparent)]` over `i64` with `From`/`Into` conversions), `HostContext` for global allocator storage, `declare_platform!` macro for declarative metadata-driven manifest generation, and `manifest_to_descriptors()` / `OwnedPlatformFnDescriptor` shared between host and DLL. Platform authors write zero `unsafe` code — all marshalling via standard Rust idioms (`s.as_str()`, `.into()`). Platform functions participate in resolution-based dispatch via `ResolvedCall::BuiltinFn` and `DefKind::Primitive` module entries. `resolve_platform_path()` searches `./platforms/`, `./target/debug/`, `./target/release/`, and `~/.cranelisp/platforms/`. `Jit` uses `symbol_lookup_fn` closure with dynamic symbol map for post-construction DLL loading. Two platform DLLs: `platforms/stdio/` (reference stdio: `print`, `read-line`) and `platforms/test-capture/` (in-memory buffers for test harnesses). Standard library (`lib/core.cl`, `lib/core/`, `lib/prelude.cl`) is platform-independent. REPL intercepts `(platform ...)` directly, stores `ModuleEntry::PlatformDecl` in declaring module. `/list` shows "Platforms" category
- **Errors**: span-aware error reporting with source context for parse, type, and codegen errors
- **Dot notation**: `Type.Constructor` and `Trait.method` syntax for disambiguation (e.g. `Option.Some`, `Display.show`, `Num.+`)
- **Qualified names**: `module/name` syntax resolves across modules (e.g. `util/helper`, `math/double`)
- **CLI modes**: `cranelisp` (bare REPL), `cranelisp foo.cl` (REPL with file loaded), `cranelisp --run foo.cl` (batch: compile + call main + exit), `cranelisp --run` (batch with `user.cl` from CWD), `cranelisp --exe <output> [file.cl]` (compile to standalone native executable)
- **Module system**: multi-file projects with `(mod name)` declarations, inline modules `(mod name forms...)` with file extraction, `super` import for parent module access, dependency graph with cycle detection, topological compilation order, qualified name access (`module/name`), `(import ...)` with specific/glob/member-glob names and auto-discovery of root modules, `(export ...)` for re-exports, visibility (`defn-`, `deftype-`, `deftrait-`, `defmacro-`), per-module scoping, ambiguity detection, per-module GOTs for incremental recompilation, unified module resolution (`resolve_module`: submodule→project root→lib), implicit `(import [prelude [*]])` for all non-prelude modules, standard library in `lib/` directory
- **Synthetic modules**: `primitives` and `macros` registered by Rust runtime — builtins are qualified-only (`primitives/add-i64`), accessible to user only through the import/export chain (core imports them, prelude re-exports). The `macros` module provides `Sexp` and `SList` types for the macro system (compiler-seeded, not user-modifiable); NOT auto-imported — quasiquote-based macros work via qualified references emitted by the expander; direct Sexp constructor use requires explicit `(import [macros [*]])`. Platform modules (`platform.stdio`, etc.) are created dynamically when DLLs are loaded
- **Per-module symbol tables**: `CompiledModule` struct with unified `symbols` map — `ModuleEntry` enum (Def, Import, Reexport, TypeDef, TraitDecl, Constructor, Macro, PlatformDecl, Ambiguous) keyed by `Symbol` newtype. TypeDef entries in `symbols` use `constructor_scheme: Option<Scheme>` for product types where constructor and type share a name. Module-walk resolution (`resolve_in_module`) follows Import/Reexport chains with depth limit. All legacy flat-dicts removed — name→scheme resolution, `SymbolMeta`, constructors, type definitions, constrained functions, trait declarations, method-to-trait mapping, HKT param indices, and operator sets all stored in or derived from `CompiledModule` and resolved via module-walk methods. Newtype wrappers (`Symbol`, `ModuleFullPath`) make each name's role explicit at the type level. `list_symbols()` walks current module's `symbols`; `describe_symbol()` classifies via single `lookup_entry_via_modules()` + `ModuleEntry` match. REPL displays module-qualified names for functions and primitives, resolving through re-export chains to the defining module (e.g., `core/concat` not `prelude/concat`). Unified method resolution pipeline — operators and non-operator trait methods share the same `resolve_methods()` pass
- **Jit.defs elimination**: `CompiledModule` is now the sole authority for all function metadata (source, sexp, defn, CLIF IR, disasm, code_size, compile_duration, got_slot, code_ptr, param_count). Jit no longer stores `DefEntry`, `DefKind`, or per-function maps (`defs`, `def_module`). `build_fn_slots_from_modules()` builds the fn_slots map from `CompiledModule` data
- **Bare-name ambiguity handling**: When two sources register the same bare name (e.g. two traits defining `show`, or two glob imports bringing `add`), the entry becomes `ModuleEntry::Ambiguous` with a warning. Using the ambiguous bare name produces a type error listing qualified alternatives (`Display.show`, `Debug.show`, `module/name`). Dotted names (`Trait.method`, `Type.Constructor`, `Type.field`) and qualified names (`module/name`) always resolve directly, bypassing ambiguity
- **E2E tests**: data-driven REPL transcript tests — `.cl`/`.out` file pairs in `tests/e2e/`, piped stdin with full transcript comparison (banner, prompts, input echo, output)
- **Tests**: ~996 total (unit + integration + e2e + trace + RC + run_tests + platform, 8 ignored)
- **Testing**: `lib/testing.cl` assertion library (`assert-eq`, `assert-true`, `assert-false`, `check` macro); `/run-tests` REPL command; `(run-tests init pass-fn fail-fn)` special form with GOT-swap tracing, fold-based result collection, and `Trace` ADT delivery to fail callbacks; `run-tests-report`/`run-tests-pass-default`/`run-tests-fail-default` stdlib helpers; convention-based, no registration needed
- **Examples**: 21 runnable files (including multi-file module and import examples)
- **Reimplementation design**: strategy doc (`docs/reimplementation.md`), deployment environment design (`docs/deployment-environment.md`), two-tier backend selection (`docs/backend-selection.md`)

## Post-sketch additions

Features added after the design sketch closed.

### Testing infrastructure

| Feature | Status |
|---|---|
| **Inline modules** `(mod name ...)` | ✓ — inline body extracted to file on first compilation; parent rewritten to `(mod name)` |
| **`super` import** | ✓ — `(import [super [*]])` resolves to parent module |
| **Assertion library** `lib/testing.cl` | ✓ — `assert-eq`, `assert-true`, `assert-false` returning `(Option String)`; `check` macro chains assertions; `run-tests-pass-default`, `run-tests-fail-default`, `run-tests-report` fold helpers |
| **`/run-tests [prefix]`** REPL command | ✓ — discovers `test-*` functions in `.test` modules, runs via GOT code pointers |
| **`(run-tests init pass-fn fail-fn)` special form** | ✓ — REPL-only; GOT-swap tracing per test; fold-based result collection; `Trace` ADT to `fail-fn`; batch mode returns `init` unchanged |

See `docs/testing.md` for design details, `examples/test-demo.cl` for a working example.

### Execution tracing

| Feature | Status |
|---|---|
| **`(trace expr)` special form** | ✓ — GOT copy-swap interception; returns `Trace` ADT |
| **`Trace` ADT** | ✓ — 5-field `TraceCall(tname, tparams, tresult, tchildren, tnanos)` |
| **Runtime trace stack** | ✓ — `cranelisp-runtime/src/trace.rs`; `TRACE_THREAD_ID` for thread safety |
| **JIT wrapper compilation** | ✓ — thin wrappers format params/result via `cranelisp_trace_format` |
| **`cranelisp_trace_format` JIT symbol** | ✓ — calls `format_result_value` via thread-local `TRACE_TC_PTR`; handles ADTs/Vecs |
| **`lib/core/trace` stdlib** | ✓ — accessors + `trace-show`, `trace-show-tree`, `trace-call-string` |
| **`in_trace_body` lenient-eval guard** | ✓ — disables sparking inside trace bodies for complete call trees |
| **Thread-safe trace role** | ✓ — stable thread IDs via `thread_local!` counter; CAS-based ownership; nested/concurrent traces skip safely |

See `docs/trace.md` for design details and runtime mechanism.

## Pre-reimplementation plan

The design sketch is complete. All 8 phases of the sketch are closed — the language, type system, macro system, IO model, memory management, parallelism, and build infrastructure have been explored and documented. The spec, architecture docs, and reimplementation strategy are ready for a clean rewrite (`docs/reimplementation.md`).

The following work remains before beginning reimplementation:

| # | Work | Status | Notes |
|---|---|---|---|
| A | **Automatic IO scheduling** — complete step 9b; remove `par-bind!` | ✓ Done | `SchedulingClass` (Sequential/Commutative/ResourceSerial) added to platform ABI (ABI_VERSION=3); `Effect` node extended to 24 bytes with runtime resource token; `CLIO::effect_on_resource(token, f)` for ResourceSerial effects; compiler analyses `bind!` chains for data-independent non-Sequential effects and inserts `Par` nodes automatically; trampoline serialises same-token branches; `par-bind!` user form removed. |
| B | **Test coverage** — fill 6 gaps from KNOWN_ISSUES.md | ✓ Done | RC tests for closures returned/stored in ADTs, user-defined recursive ADTs with drop glue, Vec out-of-bounds (marked `#[ignore]` — kills process), ~10 error-path tests, 8 REPL slash command tests, `dotted_field_accessor_resolution` annotated with root-cause explanation. |
| C | **Code audits** — typechecker, codegen, module, cache | ✓ Done | All four audit documents produced in `audits/`. Typechecker re-audited with new findings for IO scheduling, run-tests, trace, and mono+multi-sig. Key cross-cutting findings: ISA constructed separately on JIT vs cache paths (HIGH); RC/trace intrinsics missing from ObjectModule declaration (HIGH); discover() god-function (HIGH); visibility check bypassed through Import chains (HIGH); FnCompiler initialized at three sites (HIGH). |
| D | **Stack overflow protection** | ✓ Done | 64 MB main thread stack via `build.rs` `cargo:rustc-link-arg-bins` (macOS + Linux). Self-TCO covers self-recursion; deep mutual recursion crash risk greatly reduced. Depth counter deferred to reimplementation. |
| E | **KNOWN_ISSUES cleanup** — remove resolved entries | ✓ Done | Removed: `super` references (implemented), limited closure RC tests (added), recursive ADT RC tests (added). Updated: stack overflow (64 MB), single-file import/export (clarified), Vec OOB tests (marked ignored), error-path coverage (improved), REPL command tests (8/16 done). |

## Deferred to reimplementation

Items explicitly out of scope for the current implementation:

| Feature | Rationale |
|---|---|
| **Map type** (persistent hash map) | `{:key val}` literal syntax; `get`, `assoc`, `dissoc`, `keys`, `vals`, `contains?`, `merge`. Requires spec section first, then clean implementation from scratch. |
| **User-defined reader macros** (`defreader`) | Generalise hardcoded quasiquote/unquote dispatch to user-extensible registry; requires reader architecture changes better suited to reimplementation |
| **Deployment environment** | `cranelisp.toml` project config, unified search path, version constraints, lockfile, HTTP package repository. Design complete: `docs/deployment-environment.md`. Full implementation belongs in reimplementation where module resolution can be designed with it from the start. |
| **Threading / channels** | Library-only via platform DLL (`spawn`, `send`, `recv`, `chan` as IO-typed platform functions); no language changes needed |
| **Backend trait abstraction** | Architectural concern; extract `Backend` trait from `Jit` during reimplementation. Two-tier strategy: Cranelift JIT for interactive use, LLVM or C-emission release compiler for optimized builds (`docs/backend-selection.md`) |
| **Better error recovery** | Parser accumulating multiple errors; quality concern for reimplementation |
| **Polymorphic recursion** | Requires extensions beyond standard HM; rare in practice |
| **Optimization passes** | Constant folding, dead code elimination, inlining, escape analysis, unboxing, stack allocation — addressed by Tier 2 release compiler (LLVM -O2 or C emission with `cc -O2`) |
| **RRB vector / rope strings** | The current COW Vec and heap-allocated String are sufficient for the reference implementation. Persistent RRB and rope would require substantial new codegen with little benefit at this scale. |
