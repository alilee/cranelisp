# Architecture

The Cranelisp reimplementation is a clean-room rebuild from the extracted specification and architecture. The prototype (`sketch/`) remains as a reference oracle. This document defines the crate structure, pipeline design, and key architectural decisions that all skills implement against.

## Crate Structure

Seven pipeline crates form a strict DAG, plus one build-time artifact crate. Cargo enforces acyclicity at build time.

```
cranelisp (binary: pipeline orchestration, batch, REPL, executable linking)
  |
  +-- cranelisp-frontend (reader, AST builder, macro expander trait)
  |     |
  |     +-- cranelisp-types
  |
  +-- cranelisp-typecheck (inference, traits, monomorphisation)
  |     |
  |     +-- cranelisp-types
  |
  +-- cranelisp-backend (codegen, JIT, RC emission, object compilation, caching)
  |     |
  |     +-- cranelisp-types
  |     +-- cranelisp-runtime
  |
  +-- cranelisp-runtime (alloc, RC, panic, intrinsics)
  |     |
  |     +-- cranelisp-platform
  |     +-- cranelisp-types
  |
  +-- cranelisp-platform (C-ABI contract for platform DLLs)
  |
  +-- cranelisp-types (shared boundary types, no logic)

cranelisp-exe-bundle (staticlib: runtime symbols for standalone executables)
  |
  +-- cranelisp-runtime
  +-- cranelisp-platform
```

### Crate Responsibilities

#### `cranelisp-types`

All boundary types that cross crate boundaries. Contains type definitions, Display impls, constructors, and serde derives. **No business logic.** Every other crate depends on this.

Contents:
- `Sexp`, `Span` — reader output
- `Expr`, `TopLevel`, `Defn`, `Pattern`, `MatchArm`, `TypeExpr` — AST
- `Type`, `TypeId`, `Scheme`, `Subst` — type system
- `CheckResult`, `ResolvedCall`, `MethodResolutions`, `MonoDefn` — typecheck output
- `SymbolTable`, `ModuleEntry`, `DefKind`, `ImportSpec`, `ExportSpec` — module system
- `CranelispError`, `Warning` — error types
- `Symbol`, `ModuleFullPath`, `FQSymbol`, `TraitName`, `TypeName`, `ModuleName`, `JitSymbol` — string newtypes
- `CompileMode`, `ReplInput`, `Visibility` — pipeline configuration

#### `cranelisp-frontend`

Reader (source text to `Sexp`) and AST builder (`Sexp` to `Expr`/`TopLevel`). Defines the `MacroExpander` trait but does not implement it — the binary crate provides the implementation by wiring frontend + typecheck + backend.

Contents:
- PEG-based S-expression reader
- AST builder (Sexp to typed AST)
- `MacroExpander` trait definition
- Module declaration extraction (mod, import, export, platform)

#### `cranelisp-typecheck`

Hindley-Milner type inference with extensions: ADTs, traits, constrained polymorphism, monomorphisation, exhaustiveness checking.

Contents:
- Algorithm W (unification, generalization, instantiation)
- Trait registry and method resolution
- Constrained polymorphism detection
- Monomorphisation engine
- Module-scoped type environments
- Exhaustiveness checker for pattern matching

#### `cranelisp-backend`

Cranelift IR codegen, JIT compilation, reference counting emission, platform call dispatch, object compilation, and caching.

Contents:
- Expression codegen (all `Expr` variants to Cranelift IR)
- Function compilation and JIT execution
- RC emission (alloc, inc, dec, drop glue, consuming conventions)
- Closure compilation and auto-curry wrappers
- GOT management (per-module global offset tables)
- Platform DLL loading and effect dispatch
- Module caching (`.o` generation, cache metadata, `Linker` loading)
- `build_isa()` — single ISA construction point shared by JIT and object compilation

#### `cranelisp-runtime`

Rust-side runtime support linked into the JIT. Provides allocation, reference counting primitives, panic handler, and intrinsics callable from compiled code.

Contents:
- `runtime/alloc` / `runtime/dealloc` (Rust: `heap_alloc` / `heap_dealloc`) — RC-aware heap allocation
- RC inc/dec are emitted inline by the backend (not extern functions)
- `runtime/panic` (Rust: `runtime_panic`) — match exhaustiveness failure handler
- String intrinsics: `str-concat`, `str-eq`, `int-to-string`, etc. (Rust: `str_concat`, `str_eq`, `int_to_string`, etc.)
- Trace runtime: `runtime/trace_enter`, `runtime/trace_exit`, etc.
- IO trampoline

#### `cranelisp-platform`

C-ABI contract that platform DLLs implement. No dependencies on any other crate. DLL authors depend only on this crate.

Contents:
- `PlatformInit` function signature
- `CLOwned`, `CLString`, `CLInt`, `CLFloat`, `CLBool` — marshalling types
- `CLIO<CL>` — deferred effect wrapper
- `HostCallbacks` — allocation callbacks from host to DLL
- ABI version constant

#### `cranelisp-exe-bundle` (staticlib)

Bundles `cranelisp-runtime` and `cranelisp-platform` symbols into a static library (`libcranelisp_exe_bundle.a`) for standalone executable generation. Not a pipeline crate — it is a build-time artifact consumed by `--link`. Owned by `/platform`.

Contents:
- Re-exports all `cranelisp-runtime` extern symbols (alloc, dealloc, panic, intrinsics, IO trampoline)
- `cranelisp_init_platform` — platform manifest initialisation bridge
- Rust standard library subset (allocator, process::exit, etc.) — included automatically by `staticlib` crate type

#### `cranelisp` (binary)

Pipeline orchestration. Wires the five library crates into a working compiler. Owns batch mode, REPL, the `MacroExpander` implementation, and standalone executable linking.

Contents:
- `compile_unit()` — single pipeline entry point (batch + REPL share this)
- Batch mode orchestrator
- REPL session (thin loop over `compile_unit()` with persistent state)
- `MacroExpander` implementation (wires frontend + typecheck + backend)
- Module graph discovery and compilation ordering
- `ModuleRegistry` — composes `SymbolTable` (from typecheck) + codegen state (from backend)
- CLI argument parsing
- File watcher for hot-reload
- Executable linking: startup stub generation, system linker invocation, bundle/rlib locators, `main` validation

## Single Pipeline Principle

The prototype's most problematic structural debt was dual batch/REPL pipelines with divergent code paths. The reimplementation eliminates this.

Both batch and REPL call the same function:

```rust
/// Compile a single compilation unit (one module's worth of top-level forms).
pub fn compile_unit(
    frontend: &Frontend,
    typechecker: &mut TypeChecker,
    backend: &mut Backend,
    source: &str,
    mode: CompileMode,
) -> Result<CompileResult, CranelispError>
```

`CompileMode` controls the differences:

```rust
pub enum CompileMode {
    /// GOT-indirect calls for hot-reload. Used for REPL and multi-module batch
    /// compilation. Cached .o files are compiled in this mode so they are
    /// interchangeable between REPL and batch contexts.
    Interactive,
    /// Direct function calls, no GOT indirection. Used only for single-file
    /// test execution where no module caching or hot-reload is needed.
    Batch,
    /// Whole-program optimisation, standalone binary. Ring 4+ / Phase H.
    /// Future LLVM backend target — no GOT, no caching, full LTO.
    Release,
}
```

The REPL is a thin loop that:
1. Reads input (via rustyline)
2. Calls `compile_unit()` with `CompileMode::Interactive`
3. Executes the result
4. Displays the value and type
5. Updates session state (symbol tables, GOT entries)

No REPL-specific compilation logic exists. If something works in batch, it works in the REPL.

## CompiledModule Decomposition

The prototype's `CompiledModule` (133 references across 18 files) conflated four concerns. The reimplementation separates them:

| Concern | New type | Owner crate | Description |
|---|---|---|---|
| Symbol metadata | `SymbolTable` | `cranelisp-types` | Symbols, schemes, visibility, docstrings, DefKind. Pure data. |
| Code artifacts | `ModuleCodegenState` | `cranelisp-backend` | GOT table, code pointers, CLIF IR, disassembly, code sizes. |
| Module structure | `ModuleStructure` | `cranelisp-types` | File path, mod decls, import/export specs, impl sexps. |
| Cache metadata | `CacheMetadata` | `cranelisp-backend` | Content hash, method resolutions cache, expr types cache. Ring 4 only. |

The binary crate composes these through `ModuleRegistry`:

```rust
/// Per-module state composed from separate concerns.
/// Lives in the binary crate — the only place all four crates meet.
pub struct ModuleRegistry {
    /// Symbol tables — owned by TypeChecker, borrowed here for lookup
    pub symbol_tables: HashMap<ModuleFullPath, SymbolTable>,
    /// Module structure metadata
    pub structures: HashMap<ModuleFullPath, ModuleStructure>,
    /// Codegen state — owned by Backend
    pub codegen: HashMap<ModuleFullPath, ModuleCodegenState>,
    /// Cache metadata — Ring 4 only
    pub cache: HashMap<ModuleFullPath, CacheMetadata>,
}
```

Each skill works with only the types it needs:
- `/typecheck` sees `SymbolTable` — never touches GOT or code pointers
- `/backend` sees `ModuleCodegenState` + reads `SymbolTable` for type info — never modifies symbols
- `/qa` sees `ModuleRegistry` — wires everything together

## Macro Mini-Pipeline

The macro system requires a circular dependency: the frontend needs macros expanded, but macro expansion needs the backend to compile macro bodies. The reimplementation resolves this through dependency inversion.

`cranelisp-frontend` defines a trait:

```rust
/// Trait for expanding macros during AST building.
/// The binary crate implements this by wiring frontend + typecheck + backend.
pub trait MacroExpander {
    /// Expand a macro invocation, returning the expanded Sexp.
    fn expand(
        &mut self,
        name: &Symbol,
        args: &[Sexp],
        span: Span,
    ) -> Result<Sexp, CranelispError>;
}
```

Before Ring 3, the binary crate provides a no-op implementation that returns `Err(CranelispError::ModuleError { message: "macros not yet available" })`. In Ring 3, the real implementation compiles macro bodies through the full pipeline and executes them.

This means:
- `cranelisp-frontend` has no dependency on `cranelisp-backend`
- The circular dependency is broken at the crate level
- Macro expansion is testable with mock expanders

## Audit Findings Resolution

The 5 audit files document 59 findings (15 HIGH, 23 MEDIUM, 21 LOW). The architecture addresses each HIGH finding:

### Codegen HIGH findings

| Finding | Resolution |
|---|---|
| **HIGH-1**: `FnCompiler` init duplicated 3 times (28 fields) | `FnCompiler::new()` constructor in `cranelisp-backend`. Single construction point. |
| **HIGH-2**: `heap_category` duplicated as method and function | Single `HeapCategory::classify(ty: &Type)` method in `cranelisp-types`. |
| **HIGH-3**: `compile_vec_set/push` tripled ~230 lines | Extract `VecMutator` helper struct encapsulating COW + RC logic. |
| **HIGH-4**: `compile_run_tests` 233 lines with inline struct | Decompose: test discovery, per-test execution, result folding as separate methods. |
| **HIGH-5**: `compile_par_bind_continuation` duplicates lambda pattern | Extract `compile_continuation_lambda()` shared helper. |

### Typechecker HIGH findings

| Finding | Resolution |
|---|---|
| **HIGH-1**: `infer_expr()` 603 lines | Dispatch table: one method per `Expr` variant (`infer_let`, `infer_apply`, etc.). |
| **HIGH-2**: `check_program()` 318 lines, 17 phases | Named phases as separate methods. `check_program` becomes a short orchestrator. |
| **HIGH-3**: `resolve_one_method()` 142 lines, 3-4 nesting levels | Early-return guards, extract helper for each resolution strategy. |
| **HIGH-4**: 5 `panic!()` in production code | Replace with `CranelispError::TypeError`. Use `unreachable!("invariant: ...")` only for true programmer errors. |
| **HIGH-5**: 6 `.expect()` in production paths | Replace with `?` and `CranelispError`. |
| **HIGH-6**: Thin test coverage | Each module gets a `#[cfg(test)] mod tests` with targeted unit tests from Ring 0. |

### Module HIGH findings

| Finding | Resolution |
|---|---|
| **HIGH-1**: `discover()` 329 lines, 7-8 phases | Split into: `scan_module_files()`, `parse_declarations()`, `resolve_dependencies()`, `build_compile_order()`. |
| **HIGH-3**: `Vec::contains` for cycle detection (O(n^2)) | Use `HashSet` for visited tracking. |

### Cache HIGH findings

| Finding | Resolution |
|---|---|
| **HIGH-1**: Intrinsics not declared in ObjectModule | Resolved in prototype. Maintain: single intrinsic registration point in `cranelisp-backend`. |
| **HIGH-2**: Duplicate ISA construction | Single `fn build_isa()` in `cranelisp-backend`, shared by JIT and cache paths. |
| **HIGH-3**: `compile_module_to_object()` 21 positional params | Group into `ObjectCompileContext` struct. |

### Cross-cutting resolutions

| Pattern | Resolution |
|---|---|
| String-based dispatch | `ResolvedCall` enum (already typed in prototype); `DefKind` enum for all definition classification. |
| Dual batch/REPL pipelines | Single `compile_unit()` with `CompileMode` parameter. |
| `CompiledModule` god object | Decomposed into `SymbolTable` + `ModuleCodegenState` + `ModuleStructure` + `CacheMetadata`. |
| 29 `.expect()`/`.unwrap()` in codegen | `?` with `CranelispError::CodegenError` throughout. `unwrap()` permitted only in tests. |
| `eprintln!` for diagnostics | `Vec<Warning>` accumulated in `CheckResult` and `CompileResult`. |
| Magic numbers (1024 threshold, GOT size) | Named constants in `cranelisp-types` and `cranelisp-backend`. |
| `env.clone()` for scopes | Scope stack (push/pop) in both typechecker and codegen. No `HashMap::clone()`. |

## Key Design Decisions

1. **`cranelisp-types` is data-only.** No algorithms, no IO, no state. Any crate can depend on it without pulling in logic. This is the "design book" in code form.

2. **Span is a struct, not a tuple.** `struct Span { start: u32, end: u32 }` — typed, Copy, smaller than `(usize, usize)`. 4GB source limit is sufficient.

3. **TypeId narrows to u32.** 4 billion type variables is more than enough. Halves memory compared to `usize` on 64-bit.

4. **Ring 0 defines the full `Type` enum.** All variants (`Int`, `Bool`, `String`, `Float`, `Fn`, `ADT`, `Var`, `TyConApp`) exist from Ring 0. Ring 0 exercises only `Int`, `Bool`, `Float`, and simple `Fn`. This prevents rework when later rings add types.

5. **`CompileMode` replaces dual pipelines.** Batch and REPL share `compile_unit()`. Three variants — `Interactive` (GOT-indirect; REPL + multi-module batch + caching), `Batch` (direct calls; single-file tests only), `Release` (whole-program optimisation; Phase H) — with `Interactive` as the default for any compilation that produces or consumes cached `.o` files.

6. **`MacroExpander` trait breaks the circular dep.** Frontend defines the trait; binary crate implements it. Before Ring 3, it's a no-op stub.

7. **One ISA construction point.** `build_isa()` in `cranelisp-backend` is the single source of truth for Cranelift target configuration.

8. **Warnings are data, not side effects.** No `eprintln!` in library crates. Warnings accumulate as `Vec<Warning>` and flow to the caller.

## Cranelift Version

Pin Cranelift at **0.125** (same as prototype). This is a known-good version with a stable API. Upgrade only with explicit `/arch` review.

## Serde Strategy

All types in `cranelisp-types` derive `Serialize` + `Deserialize` for module caching (Ring 4). Types that contain non-serializable fields (function pointers, JIT module handles) use `#[serde(skip)]` with sensible defaults.

## Error Strategy

Every error carries a `Span` for source location. The error type is a flat enum — no nesting:

```rust
pub enum CranelispError {
    ParseError { message: String, span: Span },
    TypeError { message: String, span: Span },
    CodegenError { message: String, span: Span },
    ModuleError { message: String, file: Option<PathBuf>, span: Span },
}
```

`ParseError` uses byte offset (converted to span at the reader boundary). Library crates return `Result<T, CranelispError>`. The binary crate formats errors for display with source context.
