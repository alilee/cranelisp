# Step 7: REPL Eval via Scheduler — Implementation Design

Sprint 44. Owned by `/int`. Reviewed by `/arch`.

## 1. Problem Statement

The v4 `session_v4.rs::eval()` delegates to the old compilation path: `compile_unit` + `send_codegen` + `flush_codegen`. This means the REPL does not use the v4 scheduler or `process_module_forms`. After Steps 2-6 unified batch compilation, the REPL is the last caller of the old path.

Step 7 replaces `eval()` with a path that processes each top-level sexp serially through `process_module_forms(Additive)`, with a bare-symbol introspection check as the only special case.

## 2. Simplified Eval Path

The old REPL accumulated interception points for annotations, trace, and bare symbols. The v4 eval eliminates all interceptions except bare symbol:

- **Annotation** (`:Int 42`): A language feature (spec §4.9) with `Expr::Annotate` in the AST. Not yet implemented in the reader. When it is, it will work as a normal expression everywhere — not Step 7 scope.
- **Trace** (`(trace (fib 5))`): `Expr::Trace` is a special form handled end-to-end by the backend. No REPL-side trace setup needed.
- **Bare symbol** (`foo`): The single check. If input is one symbol token that resolves to a macro or special form, return introspection display. Otherwise, compile normally.

## 3. ModuleStrategy::Additive Parameter

### 3.1 Problem

`process_module_forms` currently assumes a fresh module on every invocation. Three things break for REPL additive input:

- **(A)** `clear_module_for_replace_public()` wipes existing symbols on `is_fresh`.
- **(B)** `inject_primitives_import` / `inject_macros_import` / `inject_prelude_if_needed` re-inject on every fresh invocation.
- **(C)** `finalize_module` hardcodes `ModuleStrategy::Replace` in `finalize_check_result`.

### 3.2 Solution

Add a `strategy: ModuleStrategy` parameter to `process_module_forms`. The `is_fresh` logic branches on strategy:

```rust
pub fn process_module_forms(
    ctx: &mut WorkerContext,
    module: &ModuleFullPath,
    sexps: &[Sexp],
    start_form_index: usize,
    accumulator: &mut ModuleCheckAccumulator,
    expanded_program: &mut Vec<TopLevel>,
    strategy: ModuleStrategy,              // NEW
) -> Result<ProcessResult, CranelispError> {
    let is_fresh = start_form_index == 0;

    if is_fresh && strategy == ModuleStrategy::Replace {
        // Existing fresh-start block: clear, inject primitives,
        // inject macros, inject prelude. Unchanged.
        ctx.tc.set_current_module(module.clone());
        ctx.tc.clear_module_for_replace_public();
        inject_primitives_import(ctx.tc)?;
        inject_macros_import(ctx.tc)?;
        if let Some(result) = inject_prelude_if_needed(ctx, module)? {
            return Ok(result);
        }
    } else if is_fresh && strategy == ModuleStrategy::Additive {
        // Additive: just set the active module. Module state persists
        // from previous evals — no clear, no re-injection.
        ctx.tc.set_current_module(module.clone());
    } else {
        // Resume from suspension (unchanged).
        ctx.tc.set_current_module(module.clone());
    }

    // Pass 1 and Pass 2 unchanged...
```

The `finalize_module` helper passes `strategy` through to `finalize_check_result`:

```rust
fn finalize_module(
    ctx: &mut WorkerContext,
    module: &ModuleFullPath,
    expanded_program: &[TopLevel],
    accumulator: &mut ModuleCheckAccumulator,
    strategy: ModuleStrategy,              // NEW
) -> Result<ProcessResult, CranelispError> {
    // ...
    let mut check_result = ctx.tc.finalize_check_result(
        module,
        accumulator,
        &final_working,
        strategy,      // was hardcoded Replace
    )?;
    // ...
}
```

All existing callers in `priority_worker_loop` pass `ModuleStrategy::Replace` (unchanged behavior). Only the REPL eval path passes `Additive`.

### 3.3 Pass 1 Scoping for Additive

Pass 1 (register signatures) runs for the new sexps only — it does not re-register existing definitions. The accumulator is freshly created per eval. This means `accumulator.defn_type_vars` contains only new definitions, and `finalize_check_result` generalizes only new functions.

Existing definitions remain in the module's symbol table from previous evals. New definitions that shadow existing names overwrite the symbol table entry during Pass 1 registration — correct REPL redefinition semantics.

## 4. Eval Function Structure

### 4.1 Return Type

```rust
/// Result of evaluating a single REPL form through the v4 path.
pub struct EvalResult {
    /// Raw i64 result value (for expressions).
    pub value: i64,
    /// Inferred type of the result.
    pub ty: Type,
    /// Whether this form was a definition.
    pub is_definition: bool,
    /// Display override (for definition display text, bare symbol introspection).
    pub display_override: Option<String>,
    /// Warnings from typecheck and codegen.
    pub warnings: Vec<Warning>,
}
```

### 4.2 Top-Level Eval: Serial Per-Form

The session's `eval` method parses input into sexps, then processes each one individually. This replaces the old batch approach where all forms were sent together.

```rust
pub fn eval(&mut self, source: &str) -> Result<Vec<EvalResult>, CranelispError> {
    let sexps = cranelisp_frontend::parse(source)?;
    if sexps.is_empty() {
        return Ok(Vec::new());
    }

    let mut results = Vec::new();

    for sexp in &sexps {
        match self.eval_one_form(sexp) {
            Ok(result) => results.push(result),
            Err(e) => {
                // Display the error, continue to next form.
                // The caller (REPL main loop) formats and prints the error.
                results.push(EvalResult {
                    value: 0,
                    ty: Type::Int,
                    is_definition: false,
                    display_override: Some(format!("{}", e)),
                    warnings: Vec::new(),
                });
            }
        }
    }

    // Session persistence: if any definitions were made, regenerate source.
    if results.iter().any(|r| r.is_definition) {
        self.regenerate_module_source();
    }

    Ok(results)
}
```

### 4.3 Per-Form Eval

Each form goes through: bare-symbol check, then TC snapshot, then `process_module_forms(Additive)` as a single-element slice, then codegen, then execute (for expressions).

```rust
fn eval_one_form(&mut self, sexp: &Sexp) -> Result<EvalResult, CranelispError> {
    // 1. Bare symbol check — introspect macros and special forms.
    if let Some(result) = self.check_bare_symbol(sexp) {
        return Ok(result);
    }

    // 2. TC snapshot for error recovery.
    let snapshot = self.inner.tc.snapshot();

    // 3. Process the single form through the v4 worker.
    let result = self.process_single_form(sexp);

    match result {
        Ok(eval_result) => Ok(eval_result),
        Err(e) => {
            // Restore TC state on error.
            self.inner.tc.restore(snapshot);
            Err(e)
        }
    }
}
```

### 4.4 Processing a Single Form

This is the core: send one sexp to `process_module_forms(Additive)`, then codegen, then execute if the form produced an expression.

```rust
fn process_single_form(&mut self, sexp: &Sexp) -> Result<EvalResult, CranelispError> {
    let module = self.inner.tc.current_module_path().clone();
    let mut accumulator = ModuleCheckAccumulator::new();
    let mut expanded_program = Vec::new();

    let single_sexp = [sexp.clone()];

    let mut wctx = WorkerContext {
        tc: &mut self.inner.tc,
        scheduler: &mut self.scheduler,
        inmem_worker: &mut self.inner.inmem_worker,
        platform_symbols: &mut self.inner.platform_symbols,
        lib_dirs: &self.inner.lib_dirs,
        project_root: &self.inner.project_root,
    };

    let result = process_module_forms(
        &mut wctx,
        &module,
        &single_sexp,
        0,                             // start_form_index
        &mut accumulator,
        &mut expanded_program,
        ModuleStrategy::Additive,
    )?;

    match result {
        ProcessResult::Complete { check_result, program } => {
            // Codegen: compile new definitions, register in GOT.
            codegen_module_symbols(
                &mut self.inner.inmem_worker,
                &self.inner.platform_symbols,
                &mut self.scheduler,
                &module,
                &program,
                &check_result,
            )?;

            // Execute if the form produced an expression result.
            self.execute_and_format(&program, &check_result)
        }
        ProcessResult::Blocked { dep_module, dep_sexps, .. } => {
            // REPL additive should not normally block — imports should
            // already be loaded. If it does block, compile the dependency
            // inline (same approach as macro dep compilation in Step 4),
            // then retry the form.
            self.compile_dependency_inline(&dep_module, &dep_sexps)?;
            self.process_single_form(sexp)
        }
    }
}
```

### 4.5 Execute and Format

After codegen, determine whether the form was a definition or an expression, and produce the appropriate `EvalResult`.

```rust
fn execute_and_format(
    &mut self,
    program: &[TopLevel],
    check: &CheckResult,
) -> Result<EvalResult, CranelispError> {
    // Definitions: return display text from CheckResult.
    // Expressions: the codegen compiled a temporary closure — execute it.
    //
    // `codegen_module_symbols` handles both: defns are registered in GOT,
    // exprs are compiled as zero-arg wrappers. The distinction is in whether
    // the program contains TopLevel::Expr entries.

    let has_expr = program.iter().any(|tl| matches!(tl, TopLevel::Expr(_)));
    let is_definition = !has_expr;

    if has_expr {
        // The last compiled item is the expression wrapper.
        // Execute it via the GOT.
        let expr_name = last_expr_wrapper_name(program);
        let code_ptr = self.inner.inmem_worker.got_state
            .get_code_ptr(&expr_name)
            .ok_or_else(|| CranelispError::CodegenError {
                message: format!("expression wrapper '{}' not found in GOT", expr_name),
                span: Span::SYNTHETIC,
            })?;

        let _ = cranelisp_runtime::panic::take_runtime_error();

        // SAFETY: code_ptr points to a zero-arg extern "C" fn() -> i64
        // compiled by Cranelift via codegen_module_symbols.
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
        let value = func();

        if let Some(err) = cranelisp_runtime::panic::take_runtime_error() {
            return Err(CranelispError::CodegenError {
                message: format!("runtime panic: {}", err),
                span: Span::SYNTHETIC,
            });
        }

        let ty = check.display.as_ref()
            .map(|d| d.ty.clone())
            .unwrap_or(Type::Int);

        Ok(EvalResult {
            value,
            ty,
            is_definition: false,
            display_override: None,
            warnings: check.warnings.clone(),
        })
    } else {
        // Definition-only: return display text.
        let display = check.display.as_ref()
            .map(|d| d.text.clone());

        Ok(EvalResult {
            value: 0,
            ty: Type::Int,
            is_definition: true,
            display_override: display,
            warnings: check.warnings.clone(),
        })
    }
}
```

### 4.6 Bare Symbol Introspection

Moved from `ReplSession::check_bare_symbol_introspection` with minimal changes. Returns introspection display for macros and special forms; returns `None` for everything else (regular functions, variables, constructors — these compile and execute normally).

```rust
fn check_bare_symbol(&self, sexp: &Sexp) -> Option<EvalResult> {
    let name = match sexp {
        Sexp::Symbol(name, _) => name,
        _ => return None,
    };

    // Look up in current module scope.
    let module = self.inner.tc.current_module_path();
    let entry = self.inner.tc.lookup_in_module(module, name)?;

    match entry {
        ModuleEntry::Macro { clauses, .. } => {
            // Zero-arg macro: let expander handle it (it has a value).
            let has_zero_arg = clauses.iter().any(|c|
                c.params.is_empty() && c.rest_param.is_none()
            );
            if has_zero_arg { return None; }
            // Non-zero-arg macro: introspect.
            Some(EvalResult {
                value: 0,
                ty: Type::Int,
                is_definition: false,
                display_override: Some(format_macro_display(name, &clauses)),
                warnings: Vec::new(),
            })
        }
        ModuleEntry::Def { kind, .. } => {
            if let DefKind::SpecialForm { description } = kind.as_ref() {
                Some(EvalResult {
                    value: 0,
                    ty: Type::Int,
                    is_definition: false,
                    display_override: Some(format_special_form_display(name, description)),
                    warnings: Vec::new(),
                })
            } else {
                None // Regular symbol — compile normally.
            }
        }
        _ => None,
    }
}
```

The display formatting functions (`format_macro_display`, `format_special_form_display`) are reused from `src/repl/commands.rs`.

## 5. GOT Consistency

Slash commands read from `inmem_worker.got_state`:
- `def_codegen: HashMap<Symbol, DefCodegen>` — stores per-definition metadata (source, sexp, GOT slot, code_ptr, param_count, etc.).
- `get_slot(slot) -> *const u8` — reads function pointers for `/disasm`, `/time`, etc.

The v4 codegen path populates GOT state through `codegen_module_symbols` -> `compile_and_register_defn`, which is the same function the old pipeline uses. This function:
1. Calls `compile_defn_with_got` to compile the definition.
2. Registers the code pointer in `got_state.def_codegen[name]`.
3. Sets `got_slot`, `code_ptr`, `param_count`, `code_size`, `compile_duration` on the `DefCodegen` entry.

Since `codegen_module_symbols` already calls `compile_and_register_defn`, the GOT is populated identically. No changes needed.

**Expression wrappers**: expressions are compiled by `codegen_module_symbols` as part of the program (wrapped as zero-arg defns by `wrap_exprs_as_defns`). They are registered in the GOT like any other defn. After execution, the wrapper entry can be left in the GOT (harmless) or cleaned up — this is an implementation detail, not architecturally significant.

**Pre-register GOT slots**: `codegen_module_symbols` calls `pre_register_got_slots` before compiling definitions. For additive input, `ensure_slot_for` is idempotent — existing slots are preserved, new slots are allocated. Redefined functions get their existing slot updated with the new code pointer.

## 6. Session Persistence

After successful eval with definitions, regenerate the REPL module source:

```rust
fn regenerate_module_source(&mut self) {
    // Delegate to existing save logic in src/repl/save.rs.
    // Reads from inmem_worker.got_state.def_codegen (source text per defn)
    // and current module structure (imports, exports, impls).
    // Writes to {project_root}/{module}.cl
    self.save_current_module();
}
```

The existing `save_current_module()` on `ReplSession` generates source from `got_state.def_codegen` entries. Since v4 codegen populates `def_codegen` the same way (Section 5), save works unchanged.

**Module structure tracking**: when definitions include `import`, `export`, or `impl` forms, these are handled by `process_module_forms` during Pass 2 (via `classify_form`). The module structure is updated in the typechecker's module table. For session persistence, the eval path syncs `current_module_structure` after any successful definition:

```rust
// After successful process_single_form that produced definitions:
fn sync_module_structure(&mut self, module: &ModuleFullPath) {
    // Read import/export specs from TC module table,
    // update self.current_module_structure.
    if let Some(table) = self.inner.tc.module_table(module) {
        self.current_module_structure.update_from(table);
    }
}
```

## 7. Error Recovery

TC snapshot/restore wraps each form individually (§4.3):

```
for each sexp:
    snapshot TC
    try process_single_form(sexp)
    on error: restore TC, report error, continue to next sexp
    on success: committed (no restore)
```

**TC snapshot limitation (F4)**: `tc.snapshot()` / `tc.restore()` does not restore `type_defs`, `overloads`, or `traits`. This is a pre-existing limitation shared with the old REPL — a failed `deftype` or `deftrait` may leave partial state. Not Step 7 scope.

**GOT state on error**: if `process_single_form` fails after `codegen_module_symbols` has partially run, GOT entries from `pre_register_got_slots` may exist with null code pointers. This is harmless — the TC restore means the definitions "never happened" from the type system's perspective, and no future code will reference the orphaned GOT entries. If the user retries the same definition, `ensure_slot_for` reuses the existing slot.

**Blocked resumption (F5)**: if `process_module_forms` returns `Blocked`, the form is retried after compiling the dependency inline. The existing `ProcessResult::Blocked` carries `form_index`, `dep_module`, and `dep_sexps` — the same resumption mechanism used by the batch scheduler. No recursion on Blocked; the inline dependency compilation resolves the block, and the retry succeeds or fails normally. (In practice, REPL input rarely blocks — imports are typically already loaded.)

## 8. What Gets Deleted

After Step 7 is complete, the following old-path code is no longer used by the REPL:

- `session_v4.rs::eval()` — the delegation to `compile_unit` + `send_codegen` + `flush_codegen`. Replaced entirely.
- `src/repl/mod.rs::eval()` — the old REPL eval with annotation/trace/bare-symbol interceptions.
- `src/repl/mod.rs::eval_via_compile_unit()` — the old REPL compilation path.
- `src/repl/mod.rs::eval_annotation_expr()` — annotations are a language feature, not REPL-specific.
- `src/repl/trace.rs::expr_contains_trace()` — trace is handled by the backend.
- `src/repl/mod.rs::build_traced_fns()` — trace setup is handled by the backend.
- `InMemWorkerState::traced_fns`, `InMemWorkerState::trace_extra_symbols` — REPL-side trace state.

These are not deleted in this sprint — they may still be referenced by tests or the old REPL path. They become dead code, candidates for cleanup in a later sprint.

## 9. Sketch Comparison

The sketch's REPL (`sketch/src/repl.rs`) uses `run_repl_loop` which:

1. Reads input with rustyline.
2. Dispatches slash commands.
3. Calls into a monolithic pipeline that parses, expands, typechecks, and compiles per-input.
4. Has separate handling for annotations, trace, and bare symbols — the same interception pattern the reimplementation accumulated.

**Divergences from sketch** (all justified):

| Aspect | Sketch | Reimplementation (v4) |
|--------|--------|-----------------------|
| Compilation path | Monolithic per-input pipeline | Serial per-form via `process_module_forms(Additive)` — shared with batch |
| Per-form processing | Batches all input together | Each sexp processed individually — immediate feedback, independent error recovery |
| Annotation handling | Separate interception | Language feature (spec §4.9) — not REPL-specific, not Step 7 scope |
| Trace handling | REPL-side `traced_fns` setup, format overrides | Backend handles `Expr::Trace` end-to-end |
| Bare symbol | Interception before compilation | Same approach — single check before compilation |
| Error recovery | TC snapshot/restore around entire input | Per-form TC snapshot/restore — one bad form doesn't prevent processing the next |
| Session persistence | Save to `.cl` file after definitions | Same approach |
| Dual pipeline | Separate batch/REPL paths | Single pipeline with strategy parameter (Principle 11) |

The key divergence is the serial per-form model. The sketch batches all input into one pipeline call, which means a definition error prevents the expression after it from running. The v4 REPL processes each form independently — the user gets results for every form that succeeds.

The elimination of annotation and trace interceptions follows from the reimplementation's backend design: `Expr::Trace` is compiled as a regular expression node, and type annotations will be parsed as `Expr::Annotate` when the reader supports them. The sketch built interceptions because its backend did not handle these cleanly as expressions.

## 10. Acceptance Criteria

1. REPL eval works through the v4 scheduler path for definitions.
2. Expressions compile and execute with correct result display.
3. `(trace (fib 5))` works without REPL-side trace setup.
4. Bare symbol introspection works (macros, special forms).
5. TC snapshot/restore recovers from errors per-form.
6. Session persistence saves after definitions.
7. All REPL demo files play cleanly.
8. Old `compile_unit` delegation in `session_v4.rs::eval()` is deleted.
9. Slash commands continue to work (GOT state populated correctly).
