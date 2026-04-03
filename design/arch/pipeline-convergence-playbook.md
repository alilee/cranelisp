# Pipeline Convergence Playbook

Status as of Sprint 49, 2026-04-04. Two commits landed:
- `a642185` — phase 1 structural detach (inner removed, EvalResult redesigned, test adapter built)
- `9c6a475` — ADT display qualification fix + FQTypeName FIXME

## What's Done

### Phase 1 Steps
- [x] 1.3 Delete `load_prelude()` — was dead code
- [x] 1.4 Delete `link()`, `run_with_workers()`, `run_with_nice_workers()`, stub spawners
- [x] 1.5 Remove `inner: Option<CompilationSession>` from `CompilerSession`
- [x] 1.6 (partial) Test adapter `ReplSession` in `tests/helpers/mod.rs` wrapping `CompilerSession`
- [ ] 1.7 Delete old pipeline code — blocked on test migration
- [ ] 1.6 (complete) Port ALL test files to v4 helpers

### EvalResult Redesign
`EvalResult` is now an enum:
```rust
pub enum EvalResult {
    Def { symbol: FQSymbol, ty: Type, warnings: Vec<Warning> },
    Val { value: i64, ty: Type, warnings: Vec<Warning> },
}
```
Accessor methods: `.value()` (returns 0 for Def), `.ty()`, `.is_def()`, `.warnings()`.

### Test Infrastructure
Three test entry points, all through v4 `CompilerSession`:

| Helper | Purpose | Prelude |
|--------|---------|---------|
| `helpers::ReplSession` | Incremental eval (Additive) | Depends on constructor |
| `helpers::batch_run(src)` | Single-source batch (defn main + trampoline) | None (bare session) |
| `helpers::batch_run_file(path, lib_dirs)` | Multi-file batch (file discovery + trampoline) | Via lib_dirs |

**ReplSession constructors:**
- `new()` — bare, no prelude. Uses `tests/fixtures` as project_root + empty lib_dirs to avoid accidental stdlib discovery.
- `new_with_prelude(project_root, &[lib_dir])` — loads prelude from lib_dir via `register_module("user")`.
- `new_for_file(entry_path, &[lib_dirs])` — project_root from entry file's parent. For multi-file batch.

**ReplSession methods (delegating to CompilerSession):**
- `eval(src)` — returns `Result<EvalResult, CranelispError>` (None→synthetic Val)
- `register_module(name)` — resolves file from lib_dirs
- `register_module_with_source(name, source)` — explicit source
- `trampoline(module_name)` — execute main, returns `(i64, Type)`. Auto-unwraps IO.

### ADT Display
`type_modules` map populated by `sync_type_defs()` scanning TC module symbol tables. This is a temporary workaround — the real fix is `FQTypeName` (see below).

## Test File Status

| File | Tests | Status | Notes |
|------|-------|--------|-------|
| ring0.rs | 108 | **106/108 pass** | 2 checked_div pre-existing |
| repl_experience.rs | 181 | **179/181 pass** | 2 fixture prelude gaps (Functor) |
| io.rs | 74 | **batch tests pass** | Full suite not run yet |
| ring2.rs | ~80 | **Broken** | 10 errors: false `.value()` on CompiledModuleGraph, needs `batch_run_file` port |
| ring3_repl.rs | ~30 | **Broken** | 19 errors: ReplSession type ref |
| repl_negative.rs | ~30 | **Broken** | 2 errors: .core → .session, unused import |
| macros.rs | ~20 | **Broken** | 7 errors: needs mechanical fix |
| ring4_trace.rs | ~20 | **Compiles** | Not run yet |
| modules.rs | ~20 | **Compiles but uses old helpers** | Uses `compile_module_graph` (old pipeline) |
| stdlib.rs | ~20 | **Compiles but uses old helpers** | Uses `compile_module_graph` with stdlib_dir |
| exemplar.rs | ~5 | **Compiles but uses old helpers** | Uses `compile_module_graph` |
| cache.rs | ~20 | **Unknown** | May use old pipeline |
| e2e.rs | ~10 | **Unknown** | |
| examples.rs | ~5 | **Unknown** | |
| lenient.rs | ~10 | **Unknown** | |
| rc.rs | ~20 | **Unknown** | |
| ring1.rs | ~40 | **Unknown** | |
| sketch_port.rs | ~30 | **Known 11 pre-existing failures** | |
| sprint23.rs | ~20 | **Unknown** | |
| pipeline_v2.rs | ~5 | **Unknown** | |
| v4_pipeline.rs | ~5 | **Unknown** | |
| v4_repl_eval.rs | ~10 | **Unknown** | |
| scheduler.rs | ~20 | **Unknown** | |

## Remaining Work

### 1. Mechanical test migration (field→method)
For files with EvalResult field access errors, apply this python regex:
```python
import re
content = re.sub(r'(\w)\.value(?!\(|_)', r'\1.value()', content)
content = re.sub(r'(\w)\.ty(?!\(|_|p)', r'\1.ty()', content)
content = re.sub(r'(\w)\.warnings(?!\(|_)', r'\1.warnings()', content)
content = content.replace('.is_definition', '.is_def()')
# Fix assert_eq! type comparisons (single and multi-line)
content = re.sub(r'assert_eq!\((\w+)\.ty\(\),', r'assert_eq!(*\1.ty(),', content)
content = re.sub(r'(assert_eq!\(\s*\n\s*)(\w+)\.ty\(\)', r'\1*\2.ty()', content)
```
**IMPORTANT:** This regex has false positives on non-EvalResult types (e.g., `CompiledModuleGraph.value`, `PipelineResult.ty`). After applying, grep for `.value()` on struct types that aren't EvalResult and revert those.

### 2. Port old pipeline callers to v4 helpers

**`compile_and_run(src)` → `batch_run(src)`:**
- io.rs — DONE
- pipeline.rs unit tests — still on old path (internal tests, lower priority)

**`compile_module_graph(entry, libs)` → `batch_run_file(entry, libs)`:**
These callers use `result.value` and `result.ty` (struct fields on `CompiledModuleGraph`). Replace with `let (value, ty) = batch_run_file(path, libs)?;`.
- modules.rs (~12 calls)
- ring2.rs (~5 calls, lines 1598-1849)
- stdlib.rs (~4 calls)
- exemplar.rs (uses compile_module_graph)

**Note:** `batch_run` and `batch_run_file` auto-trampoline IO. Tests that manually trampolined must be simplified to just check final values (see io.rs as example).

### 3. Fix import references
Replace `cranelisp::repl::ReplSession` → `helpers::ReplSession`
Replace `cranelisp::repl::{format_result, ...}` → `cranelisp_backend::display::format_result` or `cranelisp::session_v4::format_result_value`
Replace `.core.tc.` → `.session.tc.` (repl_negative.rs line 64-65)

### 4. Three prelude modes for tests
1. **No prelude** — `ReplSession::new()` or `batch_run(src)`. Source can include `(import [prelude []])` to explicitly suppress injection if using Replace strategy.
2. **Fixture prelude** — `repl_session_with(Some("fixtures/prelude.cl"), ...)`. Prelude loaded from `tests/fixtures/`.
3. **Real stdlib prelude** — pass `stdlib_dir` in lib_dirs. E.g., `ReplSession::new_with_prelude(project_root, &[stdlib_dir])`.

Tests that use Replace strategy (via `register_module` / `batch_run_file`) trigger prelude injection. If no prelude file is found in lib_dirs, injection is silently skipped (worker.rs line 1618). Tests using Additive strategy (via `eval`) skip prelude injection entirely.

### 5. Delete old pipeline code (step 1.7)
After all test callers are ported:
- Delete `CompilationSession` from `src/session.rs` (keep shared state types: `InMemWorkerState`, `SharedCodegenState`, `WorkerJitState`, `CacheState`, `ObjectWorkerState`)
- Delete `compile_unit()` family from `src/pipeline.rs` (keep module resolution: `resolve_module_file`, `discover_module_graph`, `toposort`, `compile_and_execute_expr`)
- Delete old `compile_and_run`, `compile_module_graph`, `compile_module_graph_cached`, `CompiledModuleGraph`, `PipelineResult` from pipeline.rs
- Delete `src/repl/mod.rs`'s `ReplSession` struct (keep display functions, slash command handlers as free functions or methods on CompilerSession)
- Delete `run_with_workers`, `register_module_by_name` (already done)
- Delete `main_new.rs` (orphan file, not in any module)

### 6. FQTypeName migration (separate task)
FIXME on `Type::ADT` in `crates/cranelisp-types/src/types.rs`.

Create `FQTypeName { module: ModuleFullPath, name: TypeName }` paralleling `FQSymbol { module, symbol }`. Change `Type::ADT(TypeName, Vec<Type>)` → `Type::ADT(FQTypeName, Vec<Type>)`. The typechecker stamps the module at type resolution time. ~182 sites across crates.

This eliminates:
- `type_modules: HashMap<TypeName, ModuleFullPath>` on CompilerSession
- `sync_type_defs` module scanning
- `TC.modules()` accessor added as workaround
- The `type_modules` parameter on `format_result_value`, `format_type_qualified`, etc.

Do interactively, not via subagent — construction sites in the typechecker need judgment about which module path to use.

## Key Decisions Made
- **IO trampoline**: `batch_run` / `batch_run_file` auto-trampoline IO via `CompilerSession::trampoline()`. Tests check post-trampoline values, not raw IO heap pointers. IO internals testing belongs in unit tests.
- **EvalResult design**: `Def | Val` enum with `ty` on both variants. `.value()` returns 0 for Def. Display formatting via `session.format_eval_result()`.
- **Bare sessions**: Use `tests/fixtures` as project_root with empty lib_dirs to prevent accidental stdlib discovery. Old code used cwd which picked up `stdlib/` from repo root.
- **ADT display**: Spec requires fully-qualified type names (`:user/Point`). Old unqualified display was a bug. Workaround via `type_modules` map until FQTypeName migration.
