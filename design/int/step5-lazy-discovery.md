# Step 5+6: Lazy Dependency Discovery + MacroExpander Removal — Implementation Design

Sprint 43. Owned by `/int`. Covers pipeline-v4-roadmap Steps 5 and 6.

## 1. Problem Statement

The current `process_module_forms` (delivered Sprint 42, Step 4) handles single-module programs with inline macros. It cannot handle:

1. **Import forms.** When the worker encounters `(import [core.option [Some None]])`, it has no mechanism to resolve the module file, parse it, register it with the scheduler, or block until its symbols are typechecked.

2. **Prelude injection.** Non-prelude modules need `(import [prelude [*]])` injected as the first form. The current worker hardcodes `inject_primitives_import` and `inject_macros_import` but has no prelude path.

3. **Platform forms.** `(platform "name")` requires loading a DLL and registering type signatures — currently only handled by the old path's `compile_unit_inner`.

4. **Export forms.** `(export ...)` forms declare public symbols but are not processed by the worker.

5. **Mod forms.** `(mod name)` declares submodules but is not handled.

6. **Operator symbols.** `+`, `-`, `*` etc. are trait methods resolved via prelude imports. Without prelude loading, the C2 filter rejects any program using operators.

7. **MacroExpander trait.** `CraneliftExpander` and the `MacroExpander` trait are dead code once all batch compilation routes through the v4 worker path. The REPL old path still uses them (until Step 7).

Steps 5+6 solve all of these. Step 5 makes the worker discover dependencies lazily during form processing. Step 6 removes the `MacroExpander` trait from the frontend API. After this sprint, `--v4 --run` handles any program the old path handles.

## 2. WorkerContext Struct (G-1)

The current `process_module_forms` takes 6 parameters. Lazy discovery adds `lib_dirs` and `project_root`, bringing it to 8+. Bundle into a context struct:

```rust
/// Shared context for the priority worker loop and process_module_forms.
/// Borrows session-owned data needed by workers. Read-only except for
/// tc and inmem_worker which are mutated during compilation.
pub struct WorkerContext<'a> {
    pub tc: &'a mut cranelisp_typecheck::TypeChecker,
    pub scheduler: &'a mut CompileScheduler,
    pub inmem_worker: &'a mut InMemWorkerState,
    pub platform_symbols: &'a mut Vec<(String, *const u8)>,
    pub lib_dirs: &'a [PathBuf],
    pub project_root: &'a Path,
}
```

All functions that currently take the 6-param spread (`process_module_forms`, `pass2_check_bodies_with_expansion`, `try_expand_for_pass2`, `compile_macro_if_needed`) change to take `&mut WorkerContext`. The `priority_worker_loop` signature changes to take `&mut WorkerContext` plus `module_sexps`.

`platform_symbols` becomes `&'a mut Vec<...>` (not `&'a [(String, *const u8)]`) because platform loading appends new entries.

## 3. Form Recognition Strategy

The current old path uses upfront extraction: `extract_module_declarations` strips import/export/mod/platform forms from the sexp stream before processing. The v4 path does NOT do upfront extraction. Forms are recognized during per-sexp processing in Pass 2.

### 3.1 Form Classification

At the top of Pass 2's per-sexp loop, classify each sexp:

```rust
enum FormKind {
    Import(Vec<ImportSpec>),
    Export(Vec<ExportSpec>),
    Mod(ModuleName, Option<Vec<Sexp>>),
    Platform(PlatformSpec),
    Defmacro,           // already handled in Pass 1
    Regular,            // defn, deftype, deftrait, impl, expr
}

fn classify_form(sexp: &Sexp) -> Result<FormKind, CranelispError> {
    match sexp {
        Sexp::List(items, span) if !items.is_empty() => {
            if let Sexp::Symbol(name, _) = &items[0] {
                match name.as_ref() {
                    "import" => {
                        let specs = parse_import_from_sexp(items, *span)?;
                        Ok(FormKind::Import(specs))
                    }
                    "export" => {
                        let specs = parse_export_from_sexp(items, *span)?;
                        Ok(FormKind::Export(specs))
                    }
                    "mod" => {
                        let (name, body) = parse_mod_from_sexp(items, *span)?;
                        Ok(FormKind::Mod(name, body))
                    }
                    "platform" => {
                        let spec = parse_platform_from_sexp(items, *span)?;
                        Ok(FormKind::Platform(spec))
                    }
                    "defmacro" => Ok(FormKind::Defmacro),
                    _ => Ok(FormKind::Regular),
                }
            } else {
                Ok(FormKind::Regular)
            }
        }
        _ => Ok(FormKind::Regular),
    }
}
```

The parsing functions (`parse_import_from_sexp`, etc.) reuse the existing `cranelisp_frontend::module_extract` parsing logic. These are currently private to `extract_module_declarations`; they need to be either made `pub(crate)` or extracted as free functions that `classify_form` can call. The preferred approach is to add public wrappers to `cranelisp-frontend`:

```rust
// In cranelisp-frontend lib.rs:
pub fn parse_import_sexp(sexp: &Sexp) -> Result<Vec<ImportSpec>, CranelispError>;
pub fn parse_export_sexp(sexp: &Sexp) -> Result<Vec<ExportSpec>, CranelispError>;
pub fn parse_mod_sexp(sexp: &Sexp) -> Result<(ModuleName, Option<Vec<Sexp>>), CranelispError>;
pub fn parse_platform_sexp(sexp: &Sexp) -> Result<PlatformSpec, CranelispError>;
```

### 3.2 Pass 1 Handling

Pass 1 (Register) skips import/export/mod/platform forms — they do not contribute type signatures. Pass 1 only registers defn/deftype/deftrait/impl/defmacro signatures. Form classification runs during Pass 2 only.

Exception: `(mod name (forms...))` with inline body writes the body to disk and registers the submodule name. This happens during Pass 1 so the submodule is available when imported later. The `mod` form itself does not register a type signature.

### 3.3 Pass 2 Dispatch

```
for each sexp in source order:
    match classify_form(sexp)?:
        FormKind::Import(specs):
            handle_import(ctx, module, specs)?
            // may block — returns BlockAction
        FormKind::Export(specs):
            handle_export(ctx, module, specs)?
        FormKind::Mod(name, body):
            handle_mod(ctx, module, name, body)?
            // may block — returns BlockAction
        FormKind::Platform(spec):
            handle_platform(ctx, module, spec)?
        FormKind::Defmacro:
            continue  // registered in Pass 1
        FormKind::Regular:
            // existing expand-then-check logic from Step 4
```

## 4. Import Handling and Blocking

When the worker encounters `(import [some.module [Foo bar]])`:

```rust
fn handle_import(
    ctx: &mut WorkerContext,
    module: &ModuleFullPath,
    specs: Vec<ImportSpec>,
) -> Result<BlockAction, CranelispError> {
    for spec in &specs {
        let dep = &spec.module_path;

        // 1. Already loaded — skip.
        if ctx.tc.has_module(dep) {
            ctx.tc.register_import(spec)?;
            continue;
        }

        // 2. Resolve file path.
        let dep_file = resolve_module_path(dep, ctx.lib_dirs)
            .ok_or_else(|| module_not_found_error(dep, module))?;

        // 3. Read and parse source.
        let source = std::fs::read_to_string(&dep_file).map_err(|e| {
            read_error(dep, &dep_file, e)
        })?;
        let dep_sexps = cranelisp_frontend::parse(&source)?;

        // 4. Register with scheduler — delays the current module.
        ctx.scheduler.register_module(dep.clone(), true);

        // 5. Store parsed sexps for the worker loop to pick up.
        //    (G-2: module_sexps grows dynamically.)
        return Ok(BlockAction::Block {
            dep_module: dep.clone(),
            dep_sexps,
            import_spec: spec.clone(),
        });
    }

    Ok(BlockAction::Continue)
}
```

The `BlockAction` enum signals the Pass 2 loop:

```rust
enum BlockAction {
    /// Continue processing the next form.
    Continue,
    /// Block: a dependency was discovered. Store state and return.
    Block {
        dep_module: ModuleFullPath,
        dep_sexps: Vec<Sexp>,
        import_spec: ImportSpec,
    },
}
```

When `BlockAction::Block` is returned, the Pass 2 loop:
1. Stores the parsed dep sexps in `module_sexps` for the worker loop.
2. Calls `ctx.scheduler.block_for_typecheck(module, &dep, &wildcard_symbol)` where `wildcard_symbol` is a sentinel (e.g., `Symbol::from("*")`) meaning "block until the dep module's typecheck is done". Alternatively, for named imports, block on each specific symbol.
3. Returns from `process_module_forms` with a suspension marker.

### 4.1 Block-for-Typecheck Symbol Granularity

For glob imports `(import [mod [*]])`, we need the entire module typechecked. We use `block_for_typecheck` with a well-known sentinel symbol that `notify_typecheck_done` satisfies. The simplest approach: when the scheduler sees `notify_typecheck_done(dep)`, it satisfies ALL Typecheck waiters on that module, regardless of which specific symbol they named. This is already the behavior — `notify_typecheck_done` transitions the module to `TypecheckDone`, and the unblock path checks all waiters.

For named imports `(import [mod [foo bar]])`, blocking on each specific name is more precise but the module must be fully typechecked anyway for its exports to be resolved. Use `block_for_typecheck` with a sentinel symbol `"*"` and register the import after unblocking.

**Decision**: Block on sentinel `"*"` for all imports. The scheduler's `notify_typecheck_done` already satisfies all Typecheck waiters. Simpler, no per-symbol import waiter logic.

Actually, re-examining the scheduler API: `block_for_typecheck` registers a waiter on a specific (module, symbol) pair, and `notify_symbol_typechecked` fires per-symbol. For glob imports we need the whole module done. Two options:

- **(a)** Add a `block_for_module_typecheck_done` API to the scheduler. Waiter is satisfied by `notify_typecheck_done` rather than `notify_symbol_typechecked`.
- **(b)** Use `notify_typecheck_done` to sweep all remaining `WaitKind::Typecheck` waiters on the module, regardless of symbol name.

**Decision**: Option (b). When `notify_typecheck_done(module)` fires, sweep all Typecheck waiters on that module and unblock them. This requires no new scheduler API — just ensure the existing `notify_typecheck_done` walks `ModuleState.waiters` and unblocks all `WaitKind::Typecheck` entries. This is a small addition to the existing method.

The `block_for_typecheck` call uses `Symbol::from("*")` as the waiter key. The important thing is that `notify_typecheck_done` sweeps ALL typecheck waiters regardless of symbol name.

## 5. Resumption Mechanism

### 5.1 Suspension State

When `process_module_forms` blocks on a dependency, it must save enough state to resume from the blocked form. Add a `resume_from_form` field to `ModuleState`:

```rust
// In scheduler.rs, add to ModuleState:
pub struct ModuleState {
    // ... existing fields ...

    /// Form index to resume from when unblocked.
    /// None = start from the beginning.
    pub resume_from_form: Option<usize>,
}
```

### 5.2 Suspension and Resume Flow

`process_module_forms` gains a `start_form_index` parameter (default 0 for fresh modules):

```rust
pub fn process_module_forms(
    ctx: &mut WorkerContext,
    module: &ModuleFullPath,
    sexps: Vec<Sexp>,
    start_form_index: usize,
) -> Result<ProcessResult, CranelispError>
```

Where `ProcessResult` replaces the current `(CheckResult, Vec<TopLevel>)`:

```rust
pub enum ProcessResult {
    /// Module fully typechecked.
    Complete {
        check_result: CheckResult,
        program: Vec<TopLevel>,
    },
    /// Blocked on a dependency. Resume from the given form index.
    Blocked {
        form_index: usize,
        dep_module: ModuleFullPath,
        dep_sexps: Vec<Sexp>,
    },
}
```

The Pass 2 loop tracks its position:

```rust
// Pass 2: per-sexp expand-then-check, starting from start_form_index.
for form_idx in start_form_index..sexps.len() {
    let sexp = &sexps[form_idx];

    match classify_form(sexp)? {
        FormKind::Import(specs) => {
            match handle_import(ctx, module, specs)? {
                BlockAction::Continue => {}
                BlockAction::Block { dep_module, dep_sexps, import_spec } => {
                    // Save resume point.
                    // form_idx (not form_idx+1) because we need to
                    // re-process this import form after unblocking
                    // to register the import in the typechecker.
                    return Ok(ProcessResult::Blocked {
                        form_index: form_idx,
                        dep_module,
                        dep_sexps,
                    });
                }
            }
        }
        // ... other kinds
    }
}
```

When the blocked module is unblocked and the worker reclaims it, it calls `process_module_forms` with `start_form_index = saved_form_index`. The import form is re-processed; this time `tc.has_module(dep)` is true, so the import is registered and processing continues.

### 5.3 State Preservation Across Suspension

The `ModuleCheckAccumulator` holds accumulated typecheck state across forms. It must survive across suspension/resume. Two options:

- **(a)** Store the accumulator in a session-level map `HashMap<ModuleFullPath, ModuleCheckAccumulator>`.
- **(b)** Re-run Pass 1 and Pass 2 from the beginning on resume, but skip forms before `start_form_index` in Pass 2.

**Decision**: Option (a). The accumulator is lightweight (per-form type vars, method resolutions). Store it in a new `HashMap<ModuleFullPath, ModuleCheckAccumulator>` on `WorkerContext` or on the session. On suspension, the accumulator is saved. On resume, it is restored and Pass 2 continues from `start_form_index`.

Pass 1 (Register) runs only once at the beginning (form_index 0). On resume, Pass 1 is skipped — all signatures are already registered.

### 5.4 Sexp Preservation

The sexps for a blocked module must survive across suspensions. Currently, `process_module_forms` takes `sexps: Vec<Sexp>` by value. Change the worker loop to store sexps in `module_sexps` keyed by module path. When a module blocks, its sexps remain in `module_sexps`. When it resumes, they are borrowed (not removed) until the module completes.

## 6. Prelude Injection Placement

When a non-prelude module starts processing (form_index == 0), inject prelude import:

```rust
// At the top of process_module_forms, before Pass 1:
if start_form_index == 0 {
    inject_primitives_import(ctx.tc)?;
    inject_macros_import(ctx.tc)?;

    let prelude_path = ModuleFullPath::from("prelude");
    if *module != prelude_path {
        // Inject (import [prelude [*]]) as if it were the first form.
        let prelude_spec = ImportSpec {
            module_path: prelude_path.clone(),
            names: ImportNames::Glob,
            alias: None,
            span: Span::SYNTHETIC,
        };

        if !ctx.tc.has_module(&prelude_path) {
            // Discover and load prelude through the same lazy path.
            let prelude_file = resolve_prelude(ctx.project_root, ctx.lib_dirs)
                .ok_or_else(|| no_prelude_error())?;
            let source = std::fs::read_to_string(&prelude_file)?;
            let prelude_sexps = cranelisp_frontend::parse(&source)?;

            ctx.scheduler.register_module(prelude_path.clone(), true);

            return Ok(ProcessResult::Blocked {
                form_index: 0,
                dep_module: prelude_path,
                dep_sexps: prelude_sexps,
            });
        }

        // Prelude already loaded — register the import.
        ctx.tc.register_import(&prelude_spec)?;
    }
}
```

This is the ONLY place prelude is mentioned. It flows through exactly the same `register_module` + `block_for_typecheck` + resume path as any user import. No special prelude logic beyond the initial "is this the prelude module?" guard (which prevents the prelude from importing itself).

**Operators** (`+`, `-`, etc.) resolve naturally: prelude defines traits `Num`, `Eq`, etc. and their impls. Once the prelude import is registered, operators resolve via normal trait dispatch in the typechecker. No operator-specific logic.

## 7. Export and Mod Handling

### 7.1 Export

```rust
fn handle_export(
    ctx: &mut WorkerContext,
    module: &ModuleFullPath,
    specs: Vec<ExportSpec>,
) -> Result<(), CranelispError> {
    ctx.tc.register_exports(&specs)
}
```

Exports are metadata — they mark which symbols are public. No blocking, no dependency discovery. The typechecker records them and enforces visibility during import resolution.

### 7.2 Mod

```rust
fn handle_mod(
    ctx: &mut WorkerContext,
    module: &ModuleFullPath,
    name: ModuleName,
    body: Option<Vec<Sexp>>,
) -> Result<BlockAction, CranelispError> {
    // If inline body: write to disk as {module_dir}/{name}.cl
    if let Some(body_sexps) = body {
        write_inline_mod_to_disk(module, &name, &body_sexps, ctx.project_root)?;
    }

    // Register submodule for later import resolution.
    // The submodule is not immediately loaded — it will be discovered
    // lazily when another module imports from it.
    let sub_path = ModuleFullPath::from(format!("{}.{}", module, name));
    ctx.tc.register_submodule(module, &sub_path);

    Ok(BlockAction::Continue)
}
```

`(mod name)` without inline body just registers the submodule relationship. The submodule file is resolved when imported.

## 8. Platform Handling

```rust
fn handle_platform(
    ctx: &mut WorkerContext,
    module: &ModuleFullPath,
    spec: PlatformSpec,
) -> Result<(), CranelispError> {
    let (platform, jit_syms) = crate::platform::load_and_register_platform(
        ctx.tc,
        &spec.name,
        ctx.project_root,
        spec.span,
    )?;

    // Register platform function pointers for codegen.
    ctx.platform_symbols.extend(jit_syms);

    // Store DLL handle to keep it alive — needs a session-level
    // Vec<Platform> that WorkerContext borrows.
    // For now, platform DLLs are leaked (kept alive for process lifetime).

    Ok(())
}
```

Platform loading is NOT a cross-module blocking operation. The DLL is loaded synchronously by the worker. Type signatures are registered in the TC immediately. No scheduler interaction needed.

## 9. Worker Loop Changes (G-2)

The `priority_worker_loop` changes to handle `ProcessResult::Blocked`:

```rust
pub fn priority_worker_loop(
    ctx: &mut WorkerContext,
    module_sexps: &mut HashMap<ModuleFullPath, Vec<Sexp>>,
    accumulators: &mut HashMap<ModuleFullPath, ModuleCheckAccumulator>,
) -> Result<(), CranelispError> {
    loop {
        let work = ctx.scheduler.take_priority_work();
        match work {
            Some(PriorityWork::Typecheck(module)) => {
                let start_idx = ctx.scheduler.module_state(&module)
                    .and_then(|ms| ms.resume_from_form)
                    .unwrap_or(0);

                // Borrow sexps (don't remove — needed on resume).
                let sexps = module_sexps.get(&module)
                    .ok_or_else(|| no_sexps_error(&module))?
                    .clone();

                match process_module_forms(ctx, &module, sexps, start_idx)? {
                    ProcessResult::Complete { check_result, program } => {
                        codegen_module_symbols(
                            ctx.inmem_worker, ctx.platform_symbols,
                            ctx.scheduler, &module, &program, &check_result,
                        )?;
                        // Remove sexps — module is done.
                        module_sexps.remove(&module);
                        accumulators.remove(&module);
                    }
                    ProcessResult::Blocked { form_index, dep_module, dep_sexps } => {
                        // Save resume state.
                        if let Some(ms) = ctx.scheduler.module_state_mut(&module) {
                            ms.resume_from_form = Some(form_index);
                        }
                        // Store dep sexps for the scheduler to pick up.
                        module_sexps.insert(dep_module.clone(), dep_sexps);
                        // block_for_typecheck was already called inside
                        // handle_import before returning Blocked.
                        ctx.scheduler.block_for_typecheck(
                            &module, &dep_module, &Symbol::from("*"),
                        );
                    }
                }
            }
            Some(PriorityWork::BlockingJitCodegen(module, symbol)) => {
                // Cross-module macro dep compilation.
                compile_blocking_jit_symbol(ctx, &module, &symbol)?;
                ctx.scheduler.notify_priority_codegen_complete(&module, &symbol);
            }
            Some(PriorityWork::JitCodegen(module, symbol)) => {
                // Background JIT for TypecheckDone modules.
                compile_jit_symbol(ctx, &module, &symbol)?;
                ctx.scheduler.notify_inmem_codegen_complete(&module, &symbol, false);
            }
            None => break,
        }
    }
    Ok(())
}
```

Key changes from Step 4:
- `module_sexps` grows dynamically as dependencies are discovered (G-2).
- `BlockingJitCodegen` is now handled (cross-module macro deps).
- `ProcessResult::Blocked` triggers save-and-block, not an error.

## 10. Delete C2 Filter

Remove from `session_v4.rs`:
- `qualifies_for_scheduler` function
- `sexp_qualifies` function
- `is_operator_symbol` function
- `register_module_old` method
- The `if qualifies_for_scheduler` branch in `register_module`

`register_module` always uses the v4 scheduler path:

```rust
pub fn register_module(
    &mut self,
    module_name: &str,
    source: &str,
    _entry_module_path: &Path,
) -> Result<Vec<Warning>, CranelispError> {
    let module = ModuleFullPath::from(module_name);
    let sexps = cranelisp_frontend::parse(source)?;

    self.scheduler.register_module(module.clone(), false);
    let mut module_sexps = HashMap::new();
    module_sexps.insert(module.clone(), sexps);
    let mut accumulators = HashMap::new();

    let mut ctx = WorkerContext {
        tc: &mut self.inner.tc,
        scheduler: &mut self.scheduler,
        inmem_worker: &mut self.inner.inmem_worker,
        platform_symbols: &mut self.inner.platform_symbols,
        lib_dirs: &self.inner.lib_dirs,
        project_root: &self.inner.project_root,
    };

    priority_worker_loop(&mut ctx, &mut module_sexps, &mut accumulators)?;

    self.scheduler.wait_inmem_complete().map_err(/* ... */)?;

    // Register GOT aliases.
    crate::session::register_module_aliases_filtered(
        &mut self.inner.inmem_worker, &module, None,
    );

    Ok(Vec::new())
}
```

## 11. Old-Path Coexistence (Step 7 Boundary)

### 11.1 What Remains Alive

The REPL `eval` path (Step 7) still uses:
- `CompilationSession.compile_unit()` — the old monolithic entry point
- `CompilationSession.process_forms_sequentially()` — old sequential expansion
- `CraneliftExpander` (via `CompilationSession.expander`) — the old macro expander
- `MacroEnv` — the old macro function pointer registry
- `compile_unit_inner` + `load_dependencies` + `extract_module_declarations` — the old pipeline stages

These remain alive until Step 7 replaces REPL eval with the scheduler path.

### 11.2 What Is Deleted in This Sprint

- **C2 filter**: `qualifies_for_scheduler`, `sexp_qualifies`, `is_operator_symbol` from `session_v4.rs`
- **`register_module_old`**: fallback to old `compile_unit` from `session_v4.rs`
- **`MacroExpander` trait**: from `cranelisp-types/src/pipeline.rs` (Step 6)
- **`NoOpExpander`**: from `cranelisp-types` (Step 6)
- **`CraneliftExpander`**: struct and `MacroEnv` from `src/expander.rs` (Step 6)
- **`MacroExpander` parameter**: from `build_program`, `build_top_level`, and ~30 internal functions in `cranelisp-frontend/src/ast.rs` (Step 6)

### 11.3 REPL Old-Path Adjustment for MacroExpander Removal

The old REPL path currently passes `&self.expander` (a `CraneliftExpander`) to `build_program` and `build_repl_input`. After trait deletion, the old path must expand sexps before calling `build_program` — same as the v4 worker does. The REPL's `process_forms_sequentially` already detects and expands macros. The adjustment:

1. In `process_forms_sequentially`, expand each sexp via the existing `MacroEnv` logic.
2. Pass expanded sexps to `build_program(&expanded_sexps)` (no expander parameter).
3. The `MacroEnv` struct stays alive as a standalone type (not behind the trait) for the REPL's use until Step 7.

Wait — this conflicts with "delete `MacroEnv` from `src/expander.rs`" above. Revised plan:

- `MacroEnv` stays alive in `src/expander.rs` until Step 7.
- `CraneliftExpander` (the struct that wraps `MacroEnv` and implements `MacroExpander`) is deleted.
- The `MacroExpander` trait is deleted from `cranelisp-types`.
- `NoOpExpander` is deleted from `cranelisp-types`.
- The REPL old path calls `expander::expand_sexp_recursive` (a free function) directly, using macro entries from its `MacroEnv`, before calling `build_program`.
- `build_program` and all downstream functions lose the `&dyn MacroExpander` parameter.

`MacroEnv` is a concrete type, not behind the trait — it can survive trait deletion.

## 12. MacroExpander Removal Sequencing (Step 6)

Exact order of changes:

### Phase 6a: Route all batch through v4

After Step 5 lands, all batch programs go through the scheduler path. The C2 filter is deleted (Section 10). Verify: `--v4 --run` on every integration test produces identical results.

### Phase 6b: Remove MacroExpander from frontend API

1. Delete the 3 expansion call sites in `ast_builder.rs` (lines ~147, ~256, ~1001 where `expander.expand()` is called).
2. Remove `&dyn MacroExpander` parameter from `build_program`, `build_repl_input`, `build_repl_input_from_sexps`, and all ~30 internal functions.
3. If an unexpanded macro call reaches the AST builder, it becomes a regular function application (will fail at typecheck with a type error — acceptable, as all callers should expand before building).

### Phase 6c: Delete trait and NoOpExpander

1. Delete `MacroExpander` trait from `cranelisp-types/src/pipeline.rs`.
2. Delete `NoOpExpander` from `cranelisp-types`.
3. Delete `impl MacroExpander for CraneliftExpander` from `src/expander.rs`.
4. Delete the `CraneliftExpander` struct (it only existed to implement the trait).

### Phase 6d: Adjust REPL old path

1. In `CompilationSession`, remove `expander: CraneliftExpander` field.
2. `process_forms_sequentially`: change from `self.expander.expand(sexp)` to `expander::expand_sexp_recursive(sexp, &macro_entries, 0)` (free function).
3. Macro registration: change from `self.expander.macro_env.register(...)` to direct `MacroEnv` calls on a standalone `MacroEnv` owned by `CompilationSession`.

`MacroEnv` and the free expansion functions (`expand_sexp_recursive`, `marshal_args`, `unmarshal_result`) survive in `src/expander.rs`. The file is renamed or refactored in Step 7 when the REPL moves to the v4 path.

## 13. Cycle Detection (G-3)

Circular imports (A imports B, B imports A) produce a cycle of `TypecheckBlocked` modules. Detection is added to the scheduler.

### 13.1 When to Check

After every `block_for_typecheck` call, check for cycles. This is O(N) in the number of blocked modules, where N is small (bounded by the dependency depth of the program).

### 13.2 Algorithm

Walk the waiter graph starting from the newly blocked module:

```rust
fn detect_cycle(
    &self,
    start: &ModuleFullPath,
) -> Option<Vec<ModuleFullPath>> {
    let mut visited = HashSet::new();
    let mut path = Vec::new();
    self.walk_blocked_chain(start, &mut visited, &mut path)
}

fn walk_blocked_chain(
    &self,
    current: &ModuleFullPath,
    visited: &mut HashSet<ModuleFullPath>,
    path: &mut Vec<ModuleFullPath>,
) -> Option<Vec<ModuleFullPath>> {
    if !visited.insert(current.clone()) {
        // Found a cycle — return the path from the cycle start.
        let cycle_start = path.iter().position(|m| m == current).unwrap();
        let mut cycle: Vec<_> = path[cycle_start..].to_vec();
        cycle.push(current.clone());
        return Some(cycle);
    }

    path.push(current.clone());

    // Find what modules `current` is waiting on.
    if let Some(ms) = self.state.modules.get(current) {
        if ms.pool == ModulePool::TypecheckBlocked {
            // Walk each module that has a waiter from `current`.
            for (dep_module, waiters) in &ms.waiters {
                // Wrong direction — waiters is "who waits on me".
                // We need "who am I waiting on".
            }
        }
    }

    // Actually, the scheduler tracks waiters in the REVERSE direction:
    // ModuleState.waiters maps (symbol -> waiters waiting ON this module).
    // We need to find which modules the current module is BLOCKED ON.
    //
    // Approach: scan all modules' waiter maps to find where `current`
    // appears as a waiter. This is O(total waiters) which is fine.
    for (other_module, other_state) in &self.state.modules {
        for waiters in other_state.waiters.values() {
            for w in waiters {
                if w.module == *current && w.need == WaitKind::Typecheck {
                    if let Some(cycle) = self.walk_blocked_chain(
                        other_module, visited, path
                    ) {
                        return Some(cycle);
                    }
                }
            }
        }
    }

    path.pop();
    visited.remove(current);
    None
}
```

This is not efficient for large module graphs, but Cranelisp programs have small module counts (tens, not thousands). Optimize later if needed.

### 13.3 Better: Track Blocked-On Edges

For cleaner cycle detection, add a forward edge to `ModuleState`:

```rust
pub struct ModuleState {
    // ... existing fields ...

    /// Module(s) this module is currently blocked on.
    /// Set when entering TypecheckBlocked, cleared when unblocked.
    pub blocked_on: Option<ModuleFullPath>,
}
```

Cycle detection becomes a simple linked-list walk:

```rust
fn detect_cycle(&self, start: &ModuleFullPath) -> Option<Vec<ModuleFullPath>> {
    let mut tortoise = start.clone();
    let mut hare = start.clone();
    let mut path = vec![start.clone()];

    loop {
        // Advance hare two steps, tortoise one step (Floyd's).
        // But simpler: just walk and check for revisit.
        let next = self.state.modules.get(&hare)
            .and_then(|ms| ms.blocked_on.clone());
        match next {
            None => return None,  // chain ends, no cycle
            Some(next_mod) => {
                if next_mod == *start {
                    path.push(next_mod);
                    return Some(path);
                }
                if path.contains(&next_mod) {
                    // Cycle doesn't include start — shouldn't happen
                    // since we only check after blocking start.
                    return None;
                }
                path.push(next_mod.clone());
                hare = next_mod;
            }
        }
    }
}
```

**Decision**: Use the `blocked_on` field approach. Simpler, O(depth) per check, and the field is useful for diagnostics ("module X is blocked on module Y").

### 13.4 Error Reporting

When a cycle is detected, call `scheduler.notify_module_failed` on all modules in the cycle with a descriptive error:

```
circular dependency detected: user -> core.a -> core.b -> core.a
```

This replaces the old `compile_stack`-based detection in `compile_unit_inner`.

## 14. `notify_typecheck_done` Waiter Sweep

Add to `notify_typecheck_done` in `scheduler.rs`: after transitioning the module to `TypecheckDone`, sweep all remaining `WaitKind::Typecheck` waiters on the module and unblock them:

```rust
pub fn notify_typecheck_done(&mut self, module: &ModuleFullPath) {
    self.set_pool(module, ModulePool::TypecheckDone);
    self.state.typecheck_done.push_back(module.clone());

    // Sweep: unblock all modules waiting for typecheck on any symbol
    // in this module. This handles glob imports where the waiter
    // blocked on "*" and needs the whole module done.
    if let Some(ms) = self.state.modules.get_mut(module) {
        let all_waiters: Vec<ModuleFullPath> = ms.waiters
            .values()
            .flat_map(|ws| ws.iter())
            .filter(|w| w.need == WaitKind::Typecheck)
            .map(|w| w.module.clone())
            .collect();
        // Clear typecheck waiters.
        ms.waiters.retain(|_, ws| {
            ws.retain(|w| w.need != WaitKind::Typecheck);
            !ws.is_empty()
        });
        // Unblock each waiting module.
        for waiter_module in all_waiters {
            self.try_unblock(&waiter_module);
        }
    }
}
```

## 15. Sketch Comparison

### 15.1 Module Resolution Order

The sketch (`sketch/src/module.rs:1102`) uses a 4-level resolution:

1. **Child directory**: `parent_dir/stem/name.cl` (submodule in parent's subdirectory)
2. **Sibling**: `parent_dir/name.cl` (peer module in same directory)
3. **Project root**: `project_root/name.cl`
4. **Library root**: `lib_dir/name.cl`

The reimplementation's `resolve_module_path` (`src/pipeline.rs:424`) uses a simpler approach: convert the dotted module path to a relative file path (`core.option` -> `core/option.cl`) and search each `lib_dir` in order. The `lib_dirs` list is assembled at session creation: `[entry_dir, stdlib_dir]`.

**Divergence**: The reimplementation does not have the child-dir or sibling resolution levels. It relies on dotted paths (`core.option`) which encode the directory structure directly. This is simpler and avoids ambiguity when a name could resolve to either a child or sibling.

**Rationale**: The sketch's 4-level resolution was driven by a flat module naming convention (bare `option` instead of `core.option`). The reimplementation uses qualified module paths everywhere, making child/sibling disambiguation unnecessary. The reimplementation's `lib_dirs` search (entry dir first, then stdlib) achieves the same practical effect: local modules override library modules.

### 15.2 Prelude Loading

The sketch loads the prelude eagerly in `batch.rs` before compiling the entry module. The reimplementation loads it lazily via the same import mechanism as any other module — the worker injects `(import [prelude [*]])` and discovers the prelude on demand.

**Divergence**: Lazy vs eager. The reimplementation approach is simpler (one code path for all modules) and composes naturally with the scheduler.

### 15.3 Dependency Discovery

The sketch uses upfront recursive `compile_unit` calls: `load_dependencies` walks all imports and compiles each dependency synchronously before the current module proceeds. The reimplementation discovers dependencies lazily during per-form processing: each import form triggers discovery of one dependency, blocking only if needed.

**Divergence**: Lazy vs eager. Lazy discovery enables parallel typechecking (Step 11) and avoids building the full dependency graph upfront.

### 15.4 Cycle Detection

The sketch uses a `compile_stack: Vec<ModuleFullPath>` passed through recursive `compile_unit` calls. The reimplementation uses the scheduler's `blocked_on` graph — a module entering `TypecheckBlocked` records its dependency, and a cycle walk detects loops.

**Divergence**: Same semantics (detect circular imports, report error), different mechanism (call-stack tracking vs blocked-module graph).

## 16. Summary of Changes by File

| File | Changes |
|------|---------|
| `src/worker.rs` | `WorkerContext` struct, `ProcessResult` enum, `FormKind` enum, `classify_form`, `handle_import`, `handle_export`, `handle_mod`, `handle_platform`, modify `process_module_forms` (add `start_form_index`, return `ProcessResult`), modify `priority_worker_loop` (use `WorkerContext`, handle `Blocked`, handle `BlockingJitCodegen`). |
| `src/session_v4.rs` | Delete `qualifies_for_scheduler`, `sexp_qualifies`, `is_operator_symbol`, `register_module_old`. Simplify `register_module` (always v4 path). Build `WorkerContext` in `register_module`. |
| `src/scheduler.rs` | Add `resume_from_form: Option<usize>` and `blocked_on: Option<ModuleFullPath>` to `ModuleState`. Add `module_state_mut` accessor. Add cycle detection (`detect_cycle`). Modify `notify_typecheck_done` to sweep Typecheck waiters. Modify `block_for_typecheck` to set `blocked_on` and check for cycles. |
| `src/expander.rs` | Delete `CraneliftExpander` struct and its `impl MacroExpander`. Keep `MacroEnv`, `MacroEntry`, `MacroClauseEntry`, `expand_sexp_recursive`, marshal/unmarshal functions. |
| `crates/cranelisp-types/src/pipeline.rs` | Delete `MacroExpander` trait, `NoOpExpander` struct. |
| `crates/cranelisp-frontend/src/ast.rs` | Remove `&dyn MacroExpander` from `build_program`, `build_top_level`, and ~30 internal functions. Remove 3 expansion call sites. |
| `crates/cranelisp-frontend/src/module_extract.rs` | Add public `parse_import_sexp`, `parse_export_sexp`, `parse_mod_sexp`, `parse_platform_sexp` wrappers. |
| `src/pipeline.rs` | No changes to `resolve_module_path` (reused by worker via import). Old `compile_unit` path stays for REPL. |
| `src/session.rs` | Remove `expander: CraneliftExpander` field. Add standalone `MacroEnv` field. Adjust `process_forms_sequentially` to use free expansion function. |

## 17. Acceptance Criteria

1. `--v4 --run` compiles all programs that the old `--run` path compiles.
2. Results match between old and v4 paths for every existing integration test.
3. C2 filter is deleted — no `qualifies_for_scheduler` or `sexp_qualifies`.
4. `MacroExpander` trait is deleted from `cranelisp-types`.
5. `NoOpExpander` is deleted from `cranelisp-types`.
6. `CraneliftExpander` struct is deleted from `src/expander.rs`.
7. Circular import detection works (cycle produces a clear error).
8. REPL eval still works via old path (Step 7 boundary preserved).
