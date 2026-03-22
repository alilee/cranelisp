# Pipeline Convergence Analysis

Evaluation of Options A and B from `design/backend/module-caching.md` section 8, "Path unification strategy", for reducing REPL/batch code divergence. Written by `/int` as Sprint 22 Wave 2 deliverable.

## 1. Current State Measurements

### 1.1 File sizes

| File | Total lines | Production lines | Test lines |
|------|-------------|------------------|------------|
| `src/pipeline.rs` | 1,850 | ~1,175 | ~675 |
| `src/repl/mod.rs` | 2,104 | ~1,340 | ~764 |
| `src/repl/commands.rs` | 1,004 | ~1,004 | 0 |
| `src/repl/trace.rs` | 222 | ~222 | 0 |
| `src/repl/run_tests.rs` | 167 | ~167 | 0 |
| `src/repl/io_format.rs` | 50 | ~50 | 0 |

### 1.2 Key function sizes (production code only)

**Batch path** (in `pipeline.rs`):

| Function | Lines | Role |
|----------|-------|------|
| `compile_and_run()` | 41 | Single-file batch entry: parse, process, check_program, compile_program, execute |
| `compile_module_graph()` | 158 | Multi-file batch entry: discover, toposort, per-module loop (parse, extract, process, check_program, compile_module_program, execute entry) |
| `load_prelude()` | 79 | Compile prelude modules into shared JIT (same structure as compile_module_graph inner loop) |
| `process_forms_sequentially()` | 15 | **Shared**: iterate forms through `process_single_form` |
| `process_single_form()` | 29 | **Shared**: defmacro interception, expand, flatten |
| `compile_and_register_macro()` | 47 | **Shared**: compile defmacro, register in expander + symbol table |
| `discover_module_graph()` | 47 | Module graph discovery (batch-only infrastructure) |
| `discover_module_recursive()` | 122 | Recursive module file discovery |
| `discover_import_dependencies()` | 84 | Import/export-driven module discovery |
| `toposort()` | 56 | Kahn's algorithm topological sort |
| Module resolution helpers | ~110 | `resolve_submodule_file`, `resolve_prelude`, `assemble_lib_dirs`, etc. |
| `inject_prelude_import()` | 22 | Inject `(import [prelude [*]])` |
| `parse_and_extract_module()` | 20 | Parse file, extract mod/import/export declarations |
| `accumulate_func_sigs()` | 32 | Register qualified function aliases for cross-module calls |
| Platform pre-scan | ~35 | `scan_for_platform_decls`, `filter_platform_forms` |

**REPL path** (in `repl/mod.rs`):

| Function | Lines | Role |
|----------|-------|------|
| `eval()` | 44 | REPL entry: parse, snapshot, dispatch to `eval_sexp` |
| `eval_sexp()` | 36 | Defmacro/import/platform interception, expand, flatten |
| `eval_flattened_forms()` | 38 | Process multiple forms, accumulate last result |
| `eval_defmacro()` | 52 | Compile defmacro in REPL context (parallel to `compile_and_register_macro`) |
| `eval_import()` | 30 | Handle interactive import |
| `eval_platform()` | 35 | Handle platform loading |
| `compile_and_execute()` | 16 | Dispatch by ReplInput variant |
| `execute_expr()` | 80 | Compile expr with GOT, trace setup, JIT call |
| `execute_defn()` | 58 | Compile defn, register in GOT, execute if zero-arg |
| `execute_typedef()` | 28 | Accumulate type_defs for display |
| `execute_trait_decl()` | 29 | Compile default method bodies |
| `execute_trait_impl()` | 35 | Compile impl methods + mono defns |
| `compile_and_register_defn_with_context()` | 74 | Core defn compilation: JIT create, declare, compile, GOT update |
| `compile_mono_defns()` | 10 | Compile monomorphised specializations |
| `build_check_for_backend()` | 15 | Convert ReplCheckResult to CheckResult |
| `check_bare_symbol_introspection()` | 51 | REPL-only: intercept macros/special forms for display |
| REPL loop infrastructure | ~170 | `run_repl`, `eval_and_display`, `parse_slash_command`, `dispatch_slash_command`, prompt formatting, paren balancing |

### 1.3 Classification: shared vs. divergent vs. infrastructure

**Shared code** (called by both paths, already factored out):

| Function | Lines | Notes |
|----------|-------|-------|
| `process_forms_sequentially()` | 15 | Form processing loop |
| `process_single_form()` | 29 | Defmacro interception + expansion |
| `compile_and_register_macro()` | 47 | Macro compilation (pipeline.rs version) |
| `cranelisp_frontend::build_program()` | (frontend) | AST construction |
| `cranelisp_frontend::build_repl_input()` | (frontend) | Single-form AST construction |

**Total shared**: ~91 lines in pipeline.rs (called by both batch paths and structurally paralleled by REPL).

**Batch-only code** (no REPL equivalent):

| Category | Lines | Notes |
|----------|-------|-------|
| `compile_and_run()` | 41 | Single-file batch entry |
| `compile_module_graph()` | 158 | Multi-file batch with entry-point execution |
| `load_prelude()` | 79 | Prelude compilation into shared JIT |
| Module graph infrastructure | ~420 | Discovery, toposort, resolution |
| Platform pre-scan | 35 | Batch platform handling |
| `infer_result_type()` | 20 | Batch result type inference |
| **Total batch-only** | **~753** | |

**REPL-only code** (no batch equivalent):

| Category | Lines | Notes |
|----------|-------|-------|
| ReplSession struct + constructor | ~60 | Session state management |
| `eval()` + snapshot/restore | 44 | Error recovery |
| `eval_sexp()` / `eval_flattened_forms()` | 74 | Per-form REPL dispatch |
| `eval_defmacro()` | 52 | REPL defmacro (parallel to shared `compile_and_register_macro`) |
| `eval_import()` / `eval_platform()` | 65 | Interactive import/platform |
| `compile_and_execute()` dispatch | 16 | Per-variant routing |
| `execute_expr/defn/typedef/trait_*` | 230 | Per-variant compilation + execution |
| `compile_and_register_defn_with_context()` | 74 | GOT-based defn compilation |
| `compile_mono_defns()` + `build_check_for_backend()` | 25 | Mono compilation helpers |
| `check_bare_symbol_introspection()` | 51 | REPL introspection |
| `build_traced_fns()` | 40 | Trace infrastructure |
| REPL loop + slash commands | ~1,170 | Loop, commands, display, formatting |
| **Total REPL-only** | **~1,901** | (including slash commands) |

**Duplicated logic** (same intent, different implementation):

| Concern | Batch location | REPL location | Duplication size |
|---------|---------------|---------------|-----------------|
| Defmacro compilation | `compile_and_register_macro()` (47 lines) | `eval_defmacro()` (52 lines) | ~45 lines overlapping logic |
| Per-module loop body | `compile_module_graph` inner loop (30 lines) / `load_prelude` inner loop (30 lines) | `eval_flattened_forms()` (38 lines) | ~25 lines structural parallel |
| Typecheck entry point | `tc.check_program(&program)` | `tc.check_repl_input(&input)` | Divergent APIs |
| Codegen entry point | `compile_program()` / `compile_module_program()` | Per-defn `compile_and_register_defn_with_context()` | Fundamentally different |

### 1.4 CompileMode branch points

144 total `CompileMode` occurrences across the codebase (18 files), but most are in tests. Production branch points on `CompileMode`:

| Location | Branch | Effect |
|----------|--------|--------|
| `backend/compiler/apply.rs:384` | `Batch\|Release` vs `Interactive` | Direct call vs GOT-indirect call |
| `backend/compiler/control_flow.rs:641` | `Batch\|Release` vs `Interactive` | Direct self-call vs GOT-indirect self-call (TCO) |
| `backend/compiler/trace_codegen.rs:69` | `Batch` | Trace degrades to no-swap in batch |
| `backend/compiler/trace_codegen.rs:421` | `Batch` | run-tests degrades in batch |
| `backend/lib.rs:206` | `Interactive` | GOT setup for single-file batch |
| `pipeline.rs:881,1074` | hardcoded `Batch` | Module compilation uses Batch mode |
| `repl/mod.rs:871` | hardcoded `Interactive` | REPL compilation uses Interactive mode |

The `CompileMode` branching is concentrated in the backend (4 branch points) and is clean -- it controls call convention (direct vs GOT-indirect) and trace behavior. The pipeline layer merely passes the mode through.

### 1.5 Key observation

The batch and REPL paths diverge at **two levels**:

1. **Typecheck API**: batch uses `check_program` (whole-program, returns `CheckResult`); REPL uses `check_repl_input` (per-form, returns `ReplCheckResult`).

2. **Codegen API**: batch uses `compile_program` / `compile_module_program` (whole-program, shared JIT); REPL uses per-defn `compile_and_register_defn_with_context` (fresh JIT per defn, GOT-indirect).

These are not superficial duplications -- they reflect genuinely different compilation strategies. `compile_program` declares all functions in one JIT upfront (enabling direct cross-function calls), while the REPL compiles each defn into its own JIT and wires them through the GOT (enabling function redefinition).

## 2. Option A Analysis: Per-Form Batch Pipeline

### 2.1 Concept

Batch compilation feeds forms one at a time through the same `check_repl_input` + per-defn codegen path the REPL uses. Eliminates `compile_program` / `compile_module_program` entirely. Both modes use `check_repl_input` + GOT-indirect calling.

### 2.2 What would need to change

**Typecheck crate** (`cranelisp-typecheck`):
- `check_program()` would be retired (or kept only for Release mode)
- All batch type checking goes through `check_repl_input()` per form
- `check_repl_input` already handles all form types (Expr, Defn, TypeDef, TraitDecl, TraitImpl)

**Backend crate** (`cranelisp-backend`):
- `compile_program()` (50 lines + helpers) eliminated
- `compile_module_program()` (74 lines) eliminated
- `compile_expr_with_got()` becomes the universal codegen entry
- Per-defn compilation via existing `Jit::compile_defn` with GOT context
- All batch compilation uses `CompileMode::Interactive` (GOT-indirect calls)

**Pipeline** (`src/pipeline.rs`):
- `compile_and_run()` rewritten to use a `ReplSession`-like state object
- `compile_module_graph()` inner loop rewritten: per-form processing replaces whole-program check+compile
- `load_prelude()` inner loop similarly rewritten
- `infer_result_type()` adapted to per-form tracking

**REPL** (`src/repl/mod.rs`):
- REPL-specific concerns (error recovery via snapshot, definition display formatting, slash command state, introspection metadata) must be **factored out** so the shared per-form path does not carry REPL baggage
- The GOT management (`ModuleCodegenState`) becomes shared state

### 2.3 REPL-specific concerns that need factoring

| Concern | Current home | Option A treatment |
|---------|-------------|-------------------|
| Snapshot/restore on error | `eval()` | Batch wrapper skips this (errors are fatal in batch) |
| Definition display formatting | `execute_defn`, `execute_typedef`, etc. | Batch wrapper discards display output |
| Slash command dispatch | `eval()` entry point | Only wired in REPL entry point |
| `check_bare_symbol_introspection()` | `eval_sexp()` | Only in REPL path |
| Trace GOT-swap setup | `execute_expr()` | Stays REPL-only (trace degrades in batch) |
| `DefCodegen` introspection metadata | `execute_defn` | Batch skips or stores minimal |
| `type_defs` accumulation for display | `execute_typedef` | Batch could skip entirely |

### 2.4 Estimated code impact

**Eliminated**:
- `compile_program()` + helpers in backend: ~200 lines
- `compile_module_program()`: ~74 lines
- `compile_and_run()` current form: ~41 lines
- `compile_module_graph()` inner loop: ~60 lines (replaced with per-form loop)
- Batch-specific `infer_result_type()`: ~20 lines
- **Total removed**: ~395 lines

**Added**:
- Shared per-form compilation core (extracted from REPL): ~150 lines
- Batch adapter (thin wrapper calling shared core per form): ~80 lines
- State object shared between batch and REPL (extracted from ReplSession): ~60 lines
- **Total added**: ~290 lines

**Net**: ~105 lines removed. More importantly, the duplication between batch `compile_and_register_macro` and REPL `eval_defmacro` is eliminated.

### 2.5 Risks

1. **Performance regression**: Per-form typecheck is fundamentally less efficient than whole-program typecheck. Pass 1 (type pre-registration) currently scans the whole program to register all deftypes before Pass 2 checks expressions. Per-form processing cannot look ahead -- a forward reference to a type defined later in the file would fail. This is already the REPL's limitation but has not been a problem because REPL users naturally define types before using them. In batch mode, existing source files may depend on forward references.

2. **GOT overhead in batch**: All function calls go through GOT indirection. For batch compilation this is unnecessary overhead. The cache design doc (section 8) already decided that batch module compilation uses GOT-indirect calls (for cache interchangeability), so this is architecturally consistent. But `compile_and_run()` (single-file batch, used in tests) currently uses `CompileMode::Batch` with direct calls -- switching to GOT adds latency to every test.

3. **Test compatibility**: The 1,609 existing tests include many that call `compile_and_run()` with `CompileMode::Batch`. These would need to work with the new per-form pipeline. Since `check_repl_input` handles the same form types, this should be mechanical, but regressions are possible.

4. **Forward references**: `check_program` does Pass 1 (register all deftypes) then Pass 2 (check all forms). Per-form processing cannot do this. If any batch code has forward type references, it would break. The REPL already has this limitation and it has not been a problem in practice (the spec does not guarantee forward references work), but it is a compatibility risk.

### 2.6 Would existing batch tests pass?

Likely yes, with caveats:
- Tests that define types before using them (the vast majority): yes
- Tests that rely on forward type references: would break
- Tests that check for `CompileMode::Batch` direct-call behavior: would need updating
- Tests that measure compilation speed: per-form is slower

## 3. Option B Analysis: Shared Compilation Core

### 3.1 Concept

Extract the shared logic from both paths into a common set of functions that both batch and REPL call. Batch accumulates forms and calls `check_program` + `compile_program` as today; REPL calls `check_repl_input` + per-defn compile as today. But the surrounding orchestration (form processing, macro compilation, module setup) is unified.

### 3.2 What the shared core would look like

```rust
/// Shared module compilation context.
/// Both batch and REPL create one of these per module.
struct ModuleCompileContext {
    tc: &mut TypeChecker,
    expander: &mut CraneliftExpander,
    jit_modules: &mut Vec<Jit>,  // for macro function pointers
}

/// Process a module's forms through the shared pipeline.
///
/// Handles: defmacro interception, macro expansion, begin flattening.
/// Returns accumulated non-macro sexps ready for AST building.
fn process_module_forms(
    sexps: Vec<Sexp>,
    ctx: &mut ModuleCompileContext,
) -> Result<Vec<Sexp>, CranelispError>;

/// Set up a module's context (imports, exports, prelude injection).
fn setup_module_context(
    structure: &ModuleStructure,
    tc: &mut TypeChecker,
    prelude_loaded: bool,
) -> Result<(), CranelispError>;

/// Install a compiled module's scope (shared between fresh compile and cache load).
fn install_module_scope(
    module_path: &ModuleFullPath,
    // ... scope data
) -> Result<(), CranelispError>;
```

### 3.3 What remains in each entry point

**Batch** (`compile_module_graph`):
- Module graph discovery and toposort (unchanged)
- Per-module: `setup_module_context` + `process_module_forms` (shared) + `build_program` + `check_program` + `compile_module_program` (batch-specific)
- Entry point execution

**REPL** (`eval`):
- Parse + snapshot (REPL-specific)
- `process_module_forms` equivalent via `eval_sexp`/`eval_flattened_forms` (calls shared helpers)
- `check_repl_input` + per-defn compile (REPL-specific)
- Display formatting, introspection metadata (REPL-specific)

### 3.4 Estimated code impact

**Extracted to shared**:
- `process_forms_sequentially` / `process_single_form` / `compile_and_register_macro`: already shared (~91 lines)
- `setup_module_context` (new, extracted from batch loop + REPL import handling): ~30 lines
- REPL `eval_defmacro` unified with `compile_and_register_macro`: saves ~45 lines

**Remaining duplication**:
- Typecheck: `check_program` (batch) vs `check_repl_input` (REPL) -- still divergent
- Codegen: `compile_program` / `compile_module_program` (batch) vs per-defn (REPL) -- still divergent
- Module loop structure: batch accumulates then batch-compiles; REPL compiles per-form -- structurally different

**Net**: ~45 lines saved from defmacro unification, ~30 lines added for module context helper. ~15 lines net reduction. The major duplication (typecheck + codegen entry points) remains.

### 3.5 Risks

1. **Continued divergence**: With two entry points retained, new features will continue to need implementation in both paths. The cache design doc specifically warns about this: "two entry points remain -- divergence can still accumulate."

2. **Testing burden**: Cache equivalence requires testing both paths independently (already required today, but the cache makes it more critical).

3. **Low impact**: Most of the current duplication is in the typecheck/codegen split, which Option B does not address.

## 4. Recommendation

**Option A (per-form batch pipeline)**, with two mitigations for the identified risks.

### 4.1 Rationale

The core architectural principle from `design/int/` (via `/int` role definition) is: "Single pipeline. Batch and REPL share the same compilation logic. No dual paths." Option A is the only option that fulfills this constraint.

The current duplication is manageable (the codebase is only ~4,000 lines across the two files), but it will grow as Sprint 22+ adds caching. Cache equivalence (the "single most important invariant" per the cache design doc) is trivially verifiable with one path and requires independent testing with two.

The key technical concern with Option A -- forward type references -- is a non-issue because:
- The spec does not guarantee forward references within a module
- The REPL has never supported them and no user code relies on them
- `check_program`'s Pass 1 pre-registration only applies to deftypes, which are typically module-leading declarations

### 4.2 Mitigations

**M1: GOT overhead in tests.** Single-file batch (`compile_and_run`) used in unit tests currently uses `CompileMode::Batch` for direct calls. To avoid adding GOT overhead to every test, retain a lightweight `compile_and_run` that creates a temporary `ModuleCodegenState`, compiles per-form with GOT, then executes. The GOT overhead (one pointer indirection per call) is negligible for test correctness. If it becomes measurable, a `CompileMode::Batch` fast-path can be restored as an optimization without architectural impact.

**M2: Extract REPL concerns.** Factor the shared per-form compilation into a `CompilationSession` (or similar) that owns `TypeChecker`, `CraneliftExpander`, `ModuleCodegenState`, and `Vec<Jit>`. `ReplSession` wraps this and adds REPL-specific state (display metadata, slash commands, trace state, platform symbols). The batch path creates a `CompilationSession` directly, without the REPL wrapper.

### 4.3 Implementation plan

**Phase 1: Extract CompilationSession** (prerequisite, safe refactor)
1. Create `CompilationSession` struct in `src/pipeline.rs` holding: `tc`, `expander`, `got_state`, `jit_modules`
2. Move `process_forms_sequentially`, `process_single_form`, `compile_and_register_macro` to be methods on `CompilationSession`
3. Add `compile_form()` method that does: build AST -> typecheck via `check_repl_input` -> compile defn into GOT -> return result
4. `ReplSession` wraps `CompilationSession` (delegates core compilation, adds REPL concerns)
5. Existing tests continue to pass -- this is a pure refactor

**Phase 2: Unify batch path** (the actual convergence)
1. Rewrite `compile_and_run()` to use `CompilationSession::compile_form()` per form
2. Rewrite `compile_module_graph()` inner loop to use `CompilationSession::compile_form()` per form
3. Rewrite `load_prelude()` inner loop similarly
4. Remove `compile_program()` and `compile_module_program()` from backend (or keep behind feature flag for Release mode)
5. Run full test suite, fix any forward-reference failures

**Phase 3: Validate cache equivalence** (Sprint 22 later wave)
1. With one compilation path, cache load produces identical state to fresh compile -- verifiable by comparing `ModuleCodegenState` snapshots
2. Add `install_module_scope()` as the shared post-compile/post-load entry point

### 4.4 Estimated effort

- Phase 1: ~2 hours (safe refactor, mechanical extraction)
- Phase 2: ~3 hours (rewrite batch entry points, fix test regressions)
- Phase 3: integrated into cache implementation work

## 5. Project Root Resolution (FIXME Resolved)

The FIXME described in `exemplar/plan-exemplar.md:859` identified that batch mode derives `project_root` from the entry file's parent directory, which breaks stdlib resolution for files in subdirectories (e.g., `cranelisp --run exemplar/solver.cl` from the project root sets project_root to `exemplar/`, which lacks `stdlib/`).

**Resolution**: Use `std::env::current_dir()` as `project_root` for all modes (batch, REPL, and `--link`). The REPL already uses cwd and works correctly; batch mode must match. The entry file's parent directory is the wrong choice because module resolution needs the project root (where `stdlib/`, `.cranelisp-cache/`, and project configuration live), not the source file's directory.

Full design rationale is in `design/int/repl-lifecycle.md` §6. The implementation fix is a one-line change in `src/main.rs`:

```rust
let project_root = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
```

This will be applied during Sprint 23 implementation.
