# Sketch-vs-Reimplementation Architecture Audit

**Date**: 2026-03-20
**Author**: `/arch`
**Scope**: Systematic comparison of reimplementation crates against sketch counterparts

## Summary

The reimplementation has reached feature completeness through Ring 4 (20 sprints, 1241 tests) with a fundamentally improved architecture. The 7-crate DAG, string newtypes, decomposed CompiledModule, and single-pipeline design all address the sketch's 59 audit findings. Most sketch design knowledge has been successfully absorbed. This audit identifies remaining gaps and divergences.

**Scale comparison:**
- Sketch: ~37K lines across 49 Rust source files in a single crate
- Reimplementation: ~53K lines across 7 crates + binary, 60+ source files

---

## 1. cranelisp-types (2,822 lines) vs sketch `types.rs`, `ast.rs`, `sexp.rs`, `error.rs`

### Feature Parity

| Feature | Sketch | Reimpl | Status |
|---------|--------|--------|--------|
| `Type` enum (Int, Bool, String, Float, Fn, ADT, Var, TyConApp) | `types.rs` | `types.rs` | Present |
| `Scheme` with constraints | `types.rs` | `types.rs` | Present |
| `Subst`, `apply`, `free_vars` | `types.rs` | `types.rs` | Present |
| `TypeId = usize` vs `u32` | `usize` | `u32` | Divergent (justified) |
| `Sexp` 7-variant enum | `sexp.rs` | `sexp.rs` | Present |
| `Expr` variants (all forms) | `ast.rs` | `ast.rs` | Present |
| `ParLet` / `ParBind` expr variants | `ast.rs` | -- | Missing (deferred) |
| `Span` type alias `(usize, usize)` | `error.rs` | `span.rs` | Divergent (justified) |
| String newtypes (`Symbol`, `TypeName`, etc.) | `names.rs` (partial) | `newtype.rs` | Present (improved) |
| `HeapCategory` classification | Inline in codegen | `heap.rs` | Present (improved) |
| `format_type_display` with user-friendly var names | `display.rs` | `types.rs` | Present |
| `desugar_type_def` | `ast.rs` | -- | Missing |
| `mangle_sig`, `mangle_impl_method` | `ast.rs` | -- | Not in types crate |
| `CheckResult` / `ReplCheckResult` | Scattered | `check.rs` | Present (improved) |
| `ModuleEntry` / `SymbolTable` | `module.rs` (CompiledModule) | `module.rs` | Present (decomposed) |
| `ModuleStructure` | `module.rs` (CompiledModule) | `module.rs` | Present (decomposed) |
| `PrimitiveDef` tables | `typechecker/primitives.rs` | `operator.rs` | Present (improved) |
| `MacroClauseInfo`, `MacroParam` | `module.rs` | `module.rs` | Present |
| `CompileMode` enum | -- | `pipeline.rs` | Present (new) |
| `MacroExpander` trait | -- | `pipeline.rs` | Present (new) |
| Sexp marshal tag constants | `marshal.rs` | `marshal.rs` | Present |

### Divergences

1. **`Span` is a struct, not a type alias.** Sketch uses `type Span = (usize, usize)`. Reimplementation uses `struct Span { start: u32, end: u32 }`. Justified: smaller footprint, distinct type prevents accidental misuse, `u32` sufficient for source offsets.

2. **`TypeId` is `u32`, not `usize`.** Justified per CLAUDE.md: 4 billion type vars sufficient. Saves memory in substitution maps.

3. **String newtypes are pervasive.** Sketch has `Symbol`, `ModuleFullPath`, `FQSymbol` in `names.rs` but most code still uses bare `String`. Reimplementation enforces `Symbol`, `TypeName`, `TraitName`, `ModuleName`, `ModuleFullPath`, `JitSymbol`, `FQSymbol` throughout. This is a significant improvement.

4. **`HeapCategory::classify` is centralized with optional type_defs registry.** Sketch uses `Type::is_heap_type()` with conservative ADT=true. Reimplementation uses a three-way classifier (NeverHeap/AlwaysHeap/Mixed) that consults the type definition registry for exact ADT classification. This is a clear improvement that prevents the sketch's overcounting of RC operations on pure enums.

### Gaps

1. **`desugar_type_def` lives in sketch `ast.rs` but has been correctly placed in the frontend crate's `ast_builder.rs`.** This function handles the shortcut syntax `(deftype Pair [first second])` by assigning fresh type vars. The reimplementation places it where it belongs (the frontend that builds ASTs), rather than in the shared types crate. No gap.

2. **`ParLet` / `ParBind` AST variants** exist in the sketch for IO scheduling. Not present in the reimplementation. These are Ring 4+ features that depend on the auto-scheduling pass. Acceptable deferral if the language spec positions them as future work.

### Sketch Lessons Absorbed

- **Single source of truth for type names** (`Type::from_name()`, `Type::type_name()`) -- addresses sketch audit finding of 9 duplicate mappings.
- **Decomposed CompiledModule** -- sketch's 133-reference god object is split into `SymbolTable` + `ModuleStructure` + backend-only `ModuleCodegenState`.
- **`CompileMode` enum** prevents the sketch's dual batch/REPL pipeline divergence.

---

## 2. cranelisp-frontend (3,432 lines) vs sketch `sexp.rs`, `ast_builder.rs`, `macro_expand.rs`

### Feature Parity

| Feature | Sketch | Reimpl | Status |
|---------|--------|--------|--------|
| S-expression reader (PEG parser) | `sexp.rs` (peg crate) | `reader.rs` (hand-written) | Divergent |
| Quasiquote desugaring | `sexp.rs` reader macros | `quasiquote.rs` | Present |
| AST builder (Sexp -> Expr/TopLevel) | `ast_builder.rs` | `ast_builder.rs` | Present |
| Module declaration extraction | `module.rs` | `module_extract.rs` | Present |
| `defmacro` parsing | `macro_expand.rs` | `defmacro.rs` | Present |
| Multi-clause defmacro | `macro_expand.rs` | `defmacro.rs` | Present |
| Bracket destructuring in macros | `macro_expand.rs` | `defmacro.rs` | Present |
| `begin` form flattening | `macro_expand.rs` | `defmacro.rs` | Present |
| `build_repl_input_from_sexps` (2-sexp annotation) | `ast_builder.rs` | `ast_builder.rs` | Present |
| Sexp `format_flat` / `format_indented` | `sexp.rs` | -- | Missing |
| AST `format_tree` pretty-printer | `ast.rs` | -- | Missing |
| `defns()`, `trait_impls()`, `type_defs()` extractors | `ast.rs` | -- | Not in frontend |

### Divergences

1. **Hand-written reader vs PEG parser.** The sketch uses the `peg` crate (`peg::parser!` macro). The reimplementation uses a hand-written recursive-descent parser. Justified: removes build-time dependency on proc-macro crate, gives full control over error messages and span tracking, aligns with Principle 5 (testability).

2. **Module extraction is a separate module.** Sketch embeds import/export/mod parsing in `module.rs` (the god object). Reimplementation cleanly separates it into `module_extract.rs` in the frontend crate. This is a clear architectural improvement.

### Gaps

1. **Sexp pretty-printing (`format_flat`, `format_indented`)** is present in the sketch for `/sexp` slash command and macro debugging. If the REPL's `/sexp` command works, this logic must exist somewhere (likely in the display module or binary crate). Not a hard gap but worth verifying.

2. **AST pretty-printing (`format_tree`)** is used by the sketch's `/ast` command. Same consideration.

### Sketch Lessons Absorbed

- **`MacroExpander` trait for dependency inversion** -- breaks the sketch's circular dependency where macro expansion needed codegen (to compile macro bodies) but codegen depended on the expanded AST. The trait lives in `cranelisp-types`, implemented in the binary crate.
- **Module extraction before macro expansion** per spec section 8.12.1 -- the sketch also does this, but the reimplementation makes it explicit as a separate pipeline stage.

---

## 3. cranelisp-typecheck (11,620 lines) vs sketch `typechecker/` (8 files)

### Feature Parity

| Feature | Sketch | Reimpl | Status |
|---------|--------|--------|--------|
| Algorithm W unification | `unification.rs` | `unify.rs` | Present |
| Expression inference (per-variant dispatch) | `inference.rs` (monolithic) | `infer.rs` | Present (decomposed) |
| Program checking (2-pass: sigs then bodies) | `program.rs` | `program.rs` | Present |
| Generalization / Scheme construction | `inference.rs` | `scheme.rs` | Present |
| Scope stack (push/pop) | -- (env clone) | `scope.rs` | Divergent (improved) |
| ADT registration and constructor checking | `adt.rs` | `adt.rs` | Present |
| Trait registry + impl resolution | `traits.rs` | `traits.rs` | Present |
| Overload resolution (multi-sig dispatch) | `overloads.rs` | -- | Partial |
| Constrained polymorphism (monomorphisation) | `mono.rs` | `program.rs` | Present |
| Method resolution (TraitMethod emit) | `inference.rs` | `infer.rs` | Present |
| Builtin registration (primitives, special forms) | `primitives.rs` | `builtins.rs` | Present |
| Exhaustiveness checking for match | `adt.rs` | `adt.rs` | Present |
| `ReplSnapshot` / error recovery | `inference.rs` | `checker.rs` | Present |
| Module import/export resolution | `inference.rs` / `module.rs` | `checker.rs` | Present |
| `SymbolMeta` / REPL introspection | `introspect.rs` | -- | Partial |
| HKT type constructor support | `inference.rs` | `infer.rs` | Present |
| Default trait method expansion | `traits.rs` | `traits.rs` | Present |
| `platform_scheduling` map | `inference.rs` | -- | Missing |
| Test module (inline unit tests) | `tests.rs` | (inline `#[cfg(test)]`) | Present |

### Divergences

1. **Scope stack vs env cloning.** Sketch clones `local_env: HashMap<String, Scheme>` at every scope boundary. Reimplementation uses `ScopeStack` (push/pop frames). This is a major improvement: O(1) scope entry/exit vs O(n) clone. Addresses sketch audit finding.

2. **Decomposed inference.** Sketch's `inference.rs` is a monolithic 2000+ line file with `infer_expr` doing all work. Reimplementation splits into `infer.rs` (one method per Expr variant), `scheme.rs`, `scope.rs`, `resolve.rs`. Addresses sketch audit HIGH-1.

3. **Borrow-splitting pattern.** Reimplementation uses `pub(crate)` fields on `TypeChecker` so that `impl TypeChecker` blocks in other modules can access fields directly. This avoids the sketch's pattern of passing 6+ `&mut` parameters through every call.

### Gaps

1. **`platform_scheduling` map** -- sketch's TypeChecker stores a `HashMap<String, SchedulingClass>` populated during platform DLL loading. The auto-scheduling pass consults this to decide which IO bind chains can be parallelized. Missing from the reimplementation typecheck crate. This is a Ring 4+ feature but represents hard-won design knowledge about where scheduling metadata belongs.

2. **Overload resolution (`overloads.rs`)** -- the sketch has a dedicated module for multi-sig dispatch resolution (`resolve_overloads`, `unify_overload_candidates`). The reimplementation handles this in `program.rs` but the sketch's `overloads.rs` contains specific edge-case handling (curry disambiguation, unification-based candidate narrowing) that may not be fully reproduced. Worth a targeted comparison.

3. **`SymbolMeta` / introspection** -- the sketch's `introspect.rs` has `SymbolInfo` enum variants for REPL `/info`, `/sig`, `/doc` commands. The reimplementation uses `ModuleEntry` variants and `DefKind` for classification, which serves the same purpose but through a different mechanism.

### Sketch Lessons Absorbed

- **Two-pass program checking** (declare sigs first, then check bodies) -- both systems use this.
- **`CheckResult` as the typecheck->backend boundary** rather than passing the entire TypeChecker state.
- **Constrained fn detection runs before method resolution** -- sketch's hard-won ordering (documented in MEMORY.md) is preserved.

---

## 4. cranelisp-backend (9,845 lines) vs sketch `codegen/` (6 files), `liveness.rs`, `captures.rs`, `schedule.rs`

### Feature Parity

| Feature | Sketch | Reimpl | Status |
|---------|--------|--------|--------|
| Per-function compiler (FnCompiler) | `codegen/expr.rs` (21-param fn) | `compiler/mod.rs` | Present (improved) |
| Expression compilation (dispatch per variant) | `codegen/expr.rs` | `compiler/*.rs` | Present (decomposed) |
| Function application | `codegen/apply.rs` | `compiler/apply.rs` | Present |
| Closure compilation (env capture) | `codegen/closures.rs` | `compiler/control_flow.rs` | Present |
| Drop glue generation | `codegen/closures.rs` | `compiler/control_flow.rs` | Present |
| Match compilation | `codegen/match_compile.rs` | `compiler/match_codegen.rs` | Present |
| Inline primitives | `codegen/primitives.rs` | `operators.rs` | Present |
| Vec operations codegen | `codegen/vec_ops.rs` | `compiler/vec_codegen.rs` | Present |
| Trace expression codegen | `codegen/trace.rs` | `compiler/trace_codegen.rs` | Present |
| Liveness analysis (last-use) | `liveness.rs` (separate module) | `heap.rs` (embedded) | Present |
| Free variable analysis (captures) | `captures.rs` (separate module) | `heap.rs` / `compiler/*.rs` | Present |
| GOT (Global Offset Table) | `codegen/mod.rs` | `got.rs` | Present |
| JIT module lifecycle | `jit.rs` | `jit.rs` | Present |
| ISA construction (single point) | `jit.rs` (3 constructions!) | `jit.rs` (1 construction) | Present (fixed) |
| Heap emission helpers | Inline in codegen | `heap.rs` | Present (improved) |
| RC inc/dec emission | Inline in codegen | `heap.rs` | Present (improved) |
| Display / value formatting | `repl/format.rs` | `display.rs` | Present |
| `borrowed_vars` (match field borrowing) | `codegen.rs` | `compiler/mod.rs` | Present |
| Tail call optimization (self-TCO) | `codegen/expr.rs` | `compiler/mod.rs` + `control_flow.rs` | Present |
| Auto-curry compilation | `codegen/apply.rs` | -- | Missing |
| Auto-scheduling pass (ParBind) | `schedule.rs` | -- | Missing |
| Cache/object compilation | `cache.rs`, `linker.rs` | -- | Missing |
| `GotReference::DataSymbol` (ObjectModule) | `codegen/mod.rs` | -- | Missing |
| Embedded drop_glue_ptr in closures | -- (side table) | `compiler/mod.rs` | Divergent (improved) |
| Base-pointer convention | Interior pointer | Base pointer | Divergent (justified) |
| Atomic RC from Ring 1 | Non-atomic RC | Atomic RC | Divergent (justified) |
| `CompileContext` struct | 21 parameters | `CompileContext<'a>` | Present (improved) |

### Divergences

1. **Base-pointer convention.** Sketch uses interior pointers (heap ptr points past the header). Reimplementation uses base pointers (ptr at offset 0 = alloc_size). Justified: positive offsets throughout, simpler dealloc, single address for both size and RC fields. See `design/arch/CLAUDE.md` Key Decision 10.

2. **Embedded drop_glue_ptr in closures.** Sketch uses a side table (`code_ptr -> drop_fn` HashMap). Reimplementation embeds the drop glue pointer at offset 24 in the closure struct. Justified: cross-module closures can't look up the creating module's side table. See Key Decision 11.

3. **Atomic RC from Ring 1.** Sketch uses non-atomic RC. Reimplementation uses `atomic_rmw` with sequential consistency. Justified: avoids ABI-breaking change when concurrency arrives in Ring 4. See Key Decision 13.

4. **`CompileContext` struct.** Sketch passes 21 parameters to `compile_function`. Reimplementation bundles shared immutable context into a `Copy` struct. This is the single most impactful structural improvement in the backend.

5. **Decomposed compiler modules.** Sketch has a 6192-line codegen module. Reimplementation splits into `mod.rs` (1161), `apply.rs` (707), `control_flow.rs` (783), `match_codegen.rs` (592), `vec_codegen.rs` (1108), `trace_codegen.rs` (379), `literals.rs` (163). No file exceeds 1200 lines.

### Gaps

1. **Auto-curry compilation.** Sketch's `compile_auto_curry` generates wrapper functions for partial application. The reimplementation handles `AutoCurry` in the `ResolvedCall` enum but the actual codegen for curry wrappers needs verification. If the test suite passes curry tests, the implementation exists somewhere.

2. **Auto-scheduling pass (`schedule.rs`).** Sketch transforms `bind!` chains into `ParBind` nodes for IO parallelism. Missing from the reimplementation. This is a Ring 4+ optimization that depends on `ParLet`/`ParBind` AST variants (also missing). Acceptable deferral but represents hard-won design knowledge about IO scheduling.

3. **Module cache system (`cache.rs`, `cache_writer.rs`, `linker.rs`).** Sketch has a complete SHA-256 based compilation cache with `.o` file persistence, background cache writes, and a minimal linker for loading cached object files. Missing from the reimplementation. This is a significant performance feature for multi-module projects (cache avoids recompiling unchanged modules). The sketch's cache system was itself audited (59 findings) and had structural debts, so the reimplementation should study it carefully before adopting.

4. **`GotReference::DataSymbol` for ObjectModule.** Sketch supports both immediate (JIT) and data-symbol (ObjectModule) GOT references. Reimplementation only supports immediate GOT. This is needed for the cache/linking system.

5. **Standalone executable generation (`exe.rs`).** Sketch can produce native executables via `--exe`. Missing from reimplementation. Ring 4+ / Phase H feature.

### Sketch Lessons Absorbed

- **Single ISA construction** -- sketch had 3 ISA constructions (audit finding), reimplementation has exactly 1 in `jit.rs::build_isa()`.
- **`borrowed_vars` for match field bindings** -- the Sprint 20 RC double-free bug was caused by initially missing this mechanism. Now present and functional.
- **Heap emission helpers are centralized** in `heap.rs` -- addresses sketch audit finding about raw byte offsets scattered through codegen.
- **Liveness analysis exists** as `compute_last_uses` in `heap.rs` -- sketch lesson about ownership transfer at last use sites.

---

## 5. cranelisp-runtime (2,674 lines) vs sketch `intrinsics.rs`, `codegen/rc.rs`

### Feature Parity

| Feature | Sketch | Reimpl | Status |
|---------|--------|--------|--------|
| Heap allocator with RC header | `intrinsics.rs` | `alloc.rs` | Present |
| Heap dealloc | `intrinsics.rs` | `alloc.rs` | Present |
| RC trace logging | `intrinsics.rs` | `rc.rs` | Present |
| RC underflow check | `intrinsics.rs` | `rc.rs` | Present |
| LIVE_ALLOCS double-free detection | `intrinsics.rs` | `alloc.rs` | Present |
| Allocation tracking counters | `intrinsics.rs` | `alloc.rs` | Present |
| Runtime panic handler | `intrinsics.rs` | `panic.rs` | Present |
| HeapString layout and operations | `intrinsics.rs` | `string.rs` | Present |
| String primitives (concat, eq, len, ...) | `intrinsics.rs` | `string.rs` | Present |
| Extended string ops (substring, split, join, etc.) | `intrinsics.rs` | `string.rs` | Present |
| Type conversion (int-to-string, parse-int, ...) | `intrinsics.rs` / `primitives/` | `primitives/` | Present |
| Vec runtime (new, len, set, push, drop) | `intrinsics.rs` | `vec.rs` | Present |
| IO trampoline (Pure/Effect/Bind tree forcing) | `intrinsics.rs` | `io.rs` | Present |
| Par IO execution (rayon thread pool) | `intrinsics.rs` | -- | Missing |
| Trace runtime (enter/exit/collect) | `intrinsics.rs` | `trace.rs` | Present |
| Sexp marshal / quote-sexp | `marshal.rs` | `marshal.rs` | Present |

### Divergences

1. **Base-pointer convention.** Sketch allocator returns an interior pointer (past the header). Reimplementation returns a base pointer (offset 0). All field offsets derive from `HeapHeader` constants in `cranelisp-types`.

2. **Module decomposition.** Sketch has everything in one `intrinsics.rs` file (with re-exports from `cranelisp-runtime`). Reimplementation cleanly separates into `alloc.rs`, `rc.rs`, `string.rs`, `vec.rs`, `io.rs`, `trace.rs`, `panic.rs`, `primitives/`.

### Gaps

1. **Par IO execution with resource-token ordering.** Sketch's `execute_par_with_resource_ordering` uses rayon to run independent IO branches in parallel, grouping branches by resource token. Missing from the reimplementation. This is a Ring 4+ feature that requires `ParBind` AST support and the auto-scheduling pass. Hard-won design knowledge: the resource token grouping prevents race conditions on shared resources (e.g., file handles) while allowing unrelated IO operations to run concurrently.

### Sketch Lessons Absorbed

- **`HeapHeader` as a `repr(C)` struct** with compile-time offset assertions -- prevents layout drift between codegen and runtime.
- **`LIVE_ALLOCS` for debug-build double-free detection** -- preserved from sketch.
- **RC trace logging gated behind environment variable** -- same `CRANELISP_RC_TRACE=1` pattern.

---

## 6. cranelisp-platform (814 lines) vs sketch `platforms/`, `codegen/io.rs`, `platform.rs`

### Feature Parity

| Feature | Sketch | Reimpl | Status |
|---------|--------|--------|--------|
| C-ABI contract types | `cranelisp-platform` crate | `cranelisp-platform` crate | Present |
| `SchedulingClass` enum | Platform crate | Platform crate | Present |
| IO task tree tags | Platform crate | Platform crate | Present |
| `declare_platform!` macro | Platform crate | Platform crate | Present |
| Safe wrapper types (CLInt, CLString, etc.) | Platform crate | Platform crate | Present |
| `HostCallbacks` for runtime<->platform comms | Platform crate | Platform crate | Present |
| `OwnedPlatformFnDescriptor` | Platform crate | Platform crate | Present |
| `manifest_to_descriptors()` | Platform crate | Platform crate | Present |
| `IO_TAG_PAR` (parallel IO) | Platform crate | -- | Missing |

### Divergences

1. **ABI version 1 (reimplementation) vs version 3 (sketch).** The reimplementation starts fresh. This is intentional -- the sketch iterated through breaking changes.

2. **`IO_TAG_PAR` not included.** The reimplementation's platform crate deliberately excludes the parallel IO tag, deferring it to "Ring 4 later sprint." This is consistent with the missing `ParBind` and auto-scheduling support.

### Gaps

1. **`IO_TAG_PAR` and parallel IO support** -- deferred. When implemented, needs resource-token-aware scheduling (sketch lesson).

### Sketch Lessons Absorbed

- **Platform contract types are shared** between host and DLLs via the platform crate.
- **`HEAP_HEADER_SIZE` derives from `cranelisp_types::HeapHeader::SIZE`** -- single source of truth for header layout.

---

## 7. src/ (7,312 lines) vs sketch `main.rs`, `repl.rs`, `batch.rs`, `pipeline.rs`

### Feature Parity

| Feature | Sketch | Reimpl | Status |
|---------|--------|--------|--------|
| CLI argument parsing | `main.rs` | `main.rs` | Present |
| Batch compile-and-run | `batch.rs` | `pipeline.rs` | Present |
| REPL session loop | `repl/mod.rs` | `repl.rs` | Present |
| Error recovery (snapshot/restore) | `repl/input.rs` | `repl.rs` | Present |
| Slash commands (17 commands) | `repl/commands.rs` + `handlers.rs` | `repl.rs` | Present |
| Value formatting | `repl/format.rs` | `display.rs` (backend) | Present |
| Macro expansion pipeline | `macro_expand.rs` | `expander.rs` | Present |
| Marshal (Rust Sexp <-> JIT Sexp) | `marshal.rs` | `marshal.rs` | Present |
| Module graph compilation | `batch.rs` | `pipeline.rs` | Present |
| Platform loading/registration | `batch.rs` + `platform.rs` | `platform.rs` | Present |
| Prelude loading | `repl/mod.rs` | `repl.rs` / `pipeline.rs` | Present |
| `--run` batch mode | `main.rs` | `main.rs` | Present |
| `--exe` standalone binary | `main.rs` | -- | Missing |
| `--cwd` working directory | `main.rs` | -- | Missing |
| REPL-with-file mode | `main.rs` | -- | Missing |
| File watching / cascade reload | `repl/watch.rs` + `save.rs` | -- | Missing |
| Background cache writer | `cache_writer.rs` | -- | Missing |
| Redefn safety checking | `repl/input.rs` | `repl.rs` | Present |
| Trace display state (thread-local) | `repl/format.rs` | `repl.rs` | Present |
| Lib directory resolution | `module.rs` | `pipeline.rs` | Present |
| Implicit prelude injection | `module.rs` | `pipeline.rs` | Present |

### Divergences

1. **Single pipeline, two modes.** Sketch has separate `batch.rs` and `repl/mod.rs` with duplicated logic. Reimplementation shares `compile_and_run()` and `compile_module_graph()` in `pipeline.rs`, with `CompileMode` controlling GOT usage. This is a major improvement addressing the sketch's dual-pipeline audit finding.

2. **Macro expansion lives in binary crate.** The `CraneliftExpander` struct in `expander.rs` implements the `MacroExpander` trait, wiring together frontend parsing, typecheck, and backend codegen to compile macro clause bodies. This is architecturally necessary because macro compilation requires the full pipeline, which only the binary crate has access to.

### Gaps

1. **`--exe` standalone binary generation.** Sketch supports `cranelisp --exe <output> [file.cl]` to produce native executables. Missing from reimplementation. Requires cache/object compilation and linking.

2. **`--cwd` flag and REPL-with-file mode.** Sketch supports starting the REPL pre-loaded with a file, and specifying working directory. Missing from reimplementation.

3. **File watching / cascade reload.** Sketch's `repl/watch.rs` watches source files and reloads dependents when changes are detected. Missing. This is a developer experience feature.

4. **Background cache writer.** Sketch uses a background thread to write module caches without blocking the REPL. Missing (no cache system at all).

### Sketch Lessons Absorbed

- **Single pipeline** shared between batch and REPL -- the reimplementation's design directly addresses the sketch's most complained-about structural debt.
- **`CraneliftExpander` for macro compilation** -- dependency inversion avoids the sketch's circular dependency between macro expansion and codegen.
- **Project root = entry file's parent** for batch mode, with CRANELISP_LIB for additional library directories.

---

## Cross-Cutting Findings

### 1. Missing Subsystems (Not Just "Not Yet Implemented")

These represent hard-won sketch design knowledge that should be studied before implementing:

| Missing Feature | Sketch Location | Design Knowledge |
|----------------|----------------|------------------|
| Module cache system | `cache.rs`, `cache_writer.rs`, `linker.rs` | SHA-256 hashing, `.o` files, background writes, parallel rayon processing, atomic file writes, cache manifest versioning |
| Auto-scheduling pass | `schedule.rs` | Bind-chain detection, data-dependency analysis, ParBind grouping, integration with `platform_scheduling` map |
| Par IO execution | `intrinsics.rs` | Resource-token grouping, rayon thread pool, sequential execution within resource groups |
| Standalone executable | `exe.rs` | ObjectModule compilation, startup stub generation, linker invocation |
| REPL file watching | `repl/watch.rs`, `repl/save.rs` | fsnotify integration, cascade reload ordering, dependency tracking |

### 2. Structural Improvements in the Reimplementation

These are areas where the reimplementation clearly surpasses the sketch:

| Improvement | Impact |
|-------------|--------|
| 7-crate DAG vs monolithic crate | Parallel compilation, independent testing, clear ownership |
| String newtypes throughout | Type-safe identifier handling, prevents mixing module paths with symbols |
| `CompileContext` vs 21 parameters | Readable codegen code, easy to add context fields |
| Scope stack vs env cloning | O(1) scope operations vs O(n) clone |
| Decomposed codegen (7 files vs 1) | Each file under 1200 lines, testable in isolation |
| Base-pointer convention | Simpler dealloc, consistent positive offsets |
| Atomic RC from Ring 1 | Future-proof for concurrency, no ABI break needed |
| Embedded drop_glue_ptr | Cross-module closures work correctly |
| `HeapCategory` with registry | Exact classification prevents RC over-counting |
| `CompileMode` enum | Single pipeline, mode-specific behavior via enum dispatch |

### 3. Potential Risk Areas

| Risk | Description | Severity |
|------|-------------|----------|
| `lib.rs` in backend is 2317 lines | Contains `compile_program`, `compile_defn_with_got`, `compile_and_run_defn_with_got`, etc. Largest single file. Could benefit from splitting batch vs REPL compilation entry points into separate modules. | Medium |
| `vec_codegen.rs` is 1108 lines | Vec operations with COW semantics are inherently complex. Monitor for growth. | Low |
| No unit tests in some backend files | `operators.rs`, `got.rs`, `codegen_types.rs` have no `#[cfg(test)]` modules (verified by file sizes). Integration tests provide coverage but unit tests would improve structural quality. | Medium |
| `repl.rs` is 3283 lines | Largest file in `src/`. Contains slash command handlers, value formatting logic, module graph orchestration, trace display state, and the main REPL loop. The sketch split this across 5 files (`mod.rs`, `commands.rs`, `handlers.rs`, `input.rs`, `format.rs`). Consider similar decomposition. | High |

### 4. Verified Sketch Lesson Adoption

| Sketch Lesson | Status |
|----------------|--------|
| `CompiledModule` decomposition (audit module.md) | Adopted: `SymbolTable` + `ModuleStructure` + `ModuleCodegenState` |
| Monolithic codegen functions (audit codegen.md) | Adopted: per-variant dispatch, max ~100 lines per function |
| String-based dispatch (audit codegen.md) | Adopted: typed enums (`ResolvedCall`, `DefKind`, etc.) |
| Dual batch/REPL pipelines (audit codegen.md) | Adopted: single `compile_and_run` with `CompileMode` |
| Multiple ISA constructions (audit codegen.md) | Adopted: single `build_isa()` in `jit.rs` |
| 9 duplicate primitive-name mappings (audit typechecker.md) | Adopted: `Type::from_name()` / `Type::type_name()` |
| `borrowed_vars` for match field RC | Adopted: present in `FnCompiler`, tested |
| Consuming calling convention | Adopted: split convention (user=consuming, builtin=borrowing) |
| `expr_types` map for heap classification | Adopted: `CheckResult.expr_types` flows to backend |

---

## Recommendations

1. **Study `schedule.rs` before implementing IO scheduling.** The auto-scheduling pass represents significant design effort around data-dependency analysis and resource-token grouping. The reimplementation should study this approach rather than designing from scratch.

2. **Study `cache.rs` before implementing module caching.** The sketch's cache system handles many edge cases (mono specializations landing in earlier modules, parallel rayon writes, atomic file operations). It also has audit findings -- the reimplementation can improve on the sketch's approach while preserving the core design.

3. **Split `src/repl.rs` (3283 lines).** This file is approaching the sketch's `repl/mod.rs` problem. Consider splitting into: `repl/mod.rs` (session + loop), `repl/commands.rs` (slash command dispatch), `repl/handlers.rs` (command implementations), `repl/display.rs` (formatting).

4. **Split `crates/cranelisp-backend/src/lib.rs` (2317 lines).** Consider separating batch compilation entry points from REPL compilation entry points.

5. **Add unit tests to `operators.rs` and `got.rs`.** These modules have no `#[cfg(test)]` sections.
