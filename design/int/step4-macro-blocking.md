# Step 4: Macro Expansion Blocking — Implementation Design

Sprint 42, Wave 1. Owned by `/int`. Revised for Decision 21 and Wave 2 review findings (I-1 through I-4, S-1 through S-3). Revised again to replace suspension/resumption with inline compile-and-continue (per `pipeline-v4-roadmap.md` line 122: single-threaded worker alternates typecheck and priority codegen on the same thread).

## 1. Problem Statement

The current `process_module_forms` in `src/worker.rs` (delivered in Sprint 41, Step 3) uses `NoOpExpander` and calls `build_program` on all sexps at once before typechecking. This structure cannot support macros because:

1. **No expansion.** `NoOpExpander` passes sexps through unchanged. Macro calls are not recognized or expanded. The C2 filter in `session_v4.rs` rejects any program containing `defmacro`.

2. **Bulk AST building.** `build_program(&sexps, &expander)` converts all sexps to AST in one call. Macro expansion must happen per-sexp before AST building because a `defmacro` form encountered at position N must be available for expansion at position N+1. The current bulk approach cannot interleave defmacro registration with subsequent expansion.

3. **No inline compilation.** When a macro call requires a compiled function pointer that does not yet exist, the worker must compile the macro and its dependencies inline before expanding the call. The current linear structure has no mechanism for interleaving codegen within the typecheck pass.

Step 4 restructures `process_module_forms` to process sexps individually, interleaving expansion, AST building, and typechecking per form, with the ability to compile macro dependencies inline when needed.

## 2. Per-Sexp Expansion Flow

The restructured `process_module_forms` processes forms in two passes. Pass 1 is unchanged (register signatures). Pass 2 changes from bulk body-check to per-sexp expand-then-check.

### 2.1 Pass 1 (Register) — Unchanged

Iterate all sexps. For each: build AST via `build_top_level` (with `NoOpExpander` -- no expansion needed during registration), call `tc.check_form(Register)`. When a `defmacro` sexp is encountered:

- Parse it via `cranelisp_frontend::parse_defmacro` to extract clause info.
- Typecheck the macro body to register its signature (the macro clause is a function `(SList Sexp) -> Sexp`).
- Register the macro in the module table as `ModuleEntry::Macro` with clause info and the original sexp.
- Do NOT compile the macro. Codegen is deferred until first use.

All other forms (defn, deftype, deftrait, impl, expr) register normally via `check_form(Register)`.

### 2.2 Pass 2 (CheckBody) — Per-Sexp with Inline Compilation

Iterate sexps in source order. For each sexp:

```
for idx in 0..sexps.len():
    sexp = sexps[idx]

    // Step A: Expand
    if sexp is a defmacro form:
        skip (already registered in Pass 1, no body check needed)
    else:
        result = try_expand_for_pass2(sexp, module, tc, inmem_worker, platform_symbols)?
        match result:
            None:
                pass  // sexp unchanged, not a macro call
            Some(new_sexp):
                sexp = new_sexp

    // Step B: Build AST
    top_level = build_top_level(&sexp, &NoOpExpander)?

    // Step C: Wrap Expr if needed
    if top_level is Expr: wrap as synthetic zero-arg Defn

    // Step D: Typecheck body
    result = tc.check_form(module, &top_level, CheckBody, &mut accumulator)?
    tc.merge_form_result(module, &mut accumulator, result)

    // Step E: Notify
    if top_level is Defn: scheduler.notify_symbol_typechecked(module, &defn.name)
```

After all forms complete: finalize check result, call `scheduler.notify_typecheck_done`.

### 2.3 Inline Compile-and-Continue

When `try_expand_for_pass2` encounters a macro call whose function pointer is missing, it does NOT block or suspend. Instead, it compiles the macro and its dependencies inline on the same thread:

1. Read the macro's `callees` from `ModuleEntry` (populated during Pass 2 via `merge_form_result`, per Decision 21).
2. Walk callees transitively via `tc.symbol_table(module).get(name).callees` (section 3.5).
3. Filter for uncompiled symbols (no GOT pointer).
4. Compile each dependency inline via `compile_and_register_defn`.
5. Compile the macro function itself.
6. Expand the macro call.
7. Return the expanded sexp. Continue Pass 2.

The scheduler is notified of completions as a side effect (`scheduler.notify_priority_codegen_complete`), but does NOT drive the blocking. All state stays on the stack — no suspension struct, no worker-local HashMap, no saved/restored state.

**Builtin Sexp-handling deps.** The macro's Sexp-handling dependencies (`macros/SexpSym`, `macros/SexpInt`, `macros/SCons`, `macros/SNil`, etc.) are builtins — always compiled and available in the GOT. For typical quasiquote macros that only manipulate Sexp values, there may be zero user-defined codegen deps. Only macros that call user-defined helper functions at expansion time need inline compilation of those helpers.

### 2.4 Step 11 Note (Future Multi-Threaded Mode)

In single-threaded Step 4, inline compile-and-continue is sufficient because the same thread that encounters the macro call can compile the deps immediately. Multi-threaded Step 11 will need:

- Real suspension/resumption (`SuspendedState` stored on the session, not worker-local).
- A `ResumeTypecheck` variant on `PriorityWork`.
- A different worker may resume what another started.

This is Step 11 scope, not Step 4. The inline approach here is simpler and correct for single-threaded execution.

## 3. Expander Extraction

The v4 worker must expand macros without going through the `MacroExpander` trait or the `CraneliftExpander` struct. The trait exists to break a circular dependency (frontend cannot depend on backend), but the v4 worker is in the binary crate and has access to everything.

### 3.1 Functions to Extract as Free Functions

These functions in `src/expander.rs` are already module-level free functions and remain so. The v4 worker calls them directly:

| Function | Current signature | Notes |
|----------|------------------|-------|
| `clause_matches` | `fn(clause: &MacroClauseEntry, args: &[Sexp]) -> bool` | Already free. No change needed. |
| `find_matching_clause` | `fn(clauses: &[MacroClauseEntry], args: &[Sexp]) -> Option<&MacroClauseEntry>` | Already free. No change needed. |
| `invoke_clause` | `fn(clause: &MacroClauseEntry, args: &[Sexp], span: Span) -> Result<Sexp, CranelispError>` | Already free. No change needed. |
| `rewrite_spans` | `fn(sexp: &mut Sexp, call_site_span: Span)` | Already free. No change needed. |
| `expand_sexp_recursive` | `fn(sexp: Sexp, macros: &HashMap<Symbol, MacroEntry>, depth: usize) -> Result<Sexp, CranelispError>` | Already free. Enforces depth limit of 100 (see section 7.3). No change needed. |

The key issue is **visibility**: `MacroClauseEntry`, `MacroEntry`, `clause_matches`, `find_matching_clause`, `invoke_clause`, `rewrite_spans`, and `expand_sexp_recursive` are currently private to `src/expander.rs`. They must be made `pub(crate)` so the worker can call them.

### 3.2 Return Type for Per-Sexp Expansion

Since inline compilation means expansion either succeeds or errors, the return type is simply:

```rust
Result<Option<Sexp>, CranelispError>
```

- `Ok(Some(expanded))` — the sexp was a macro call and was expanded (recursively to fixed point).
- `Ok(None)` — the sexp is not a macro call. Unchanged.
- `Err(e)` — expansion error (no matching clause, runtime panic, depth exceeded, invalid return value, inline compilation failure).

No `NeedsBlock` variant is needed because deps are compiled inline before expansion.

### 3.3 New Worker-Side Expansion Function

A new function in `src/worker.rs` orchestrates expansion using the extracted functions:

```rust
/// Attempt to expand a sexp that may be a macro call.
///
/// If the sexp is a macro call and the macro's function pointer is not yet
/// compiled, compiles the macro and its transitive dependencies inline
/// before expanding. Returns Ok(Some(expanded)) for macro calls,
/// Ok(None) for non-macro forms, Err for errors.
fn try_expand_for_pass2(
    sexp: &Sexp,
    module: &ModuleFullPath,
    tc: &mut cranelisp_typecheck::TypeChecker,
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    scheduler: &mut CompileScheduler,
) -> Result<Option<Sexp>, CranelispError>
```

This function:

1. Checks if the sexp head is a known macro (by looking up the module table via `tc.symbol_table(module).get(name)`, not the `MacroEnv`).
2. If not a macro: returns `Ok(None)`.
3. If a macro: checks if all clause function pointers exist in the GOT.
4. If pointers missing: calls `compile_macro_deps_inline` (section 3.6) to compile the macro and its transitive uncompiled dependencies. Notifies the scheduler of each completion as a side effect.
5. Marshals args, invokes clause, unmarshals result, rewrites spans, recursively re-expands (to fixed point via `expand_sexp_recursive` with depth limit 100). Returns `Ok(Some(sexp))`.
6. If any error occurs (no matching clause, runtime panic, depth limit exceeded, invalid return value, compilation failure): returns `Err(CranelispError)`.

### 3.4 Macro Function Pointer Lookup

The macro's function pointer is looked up in the GOT (`inmem_worker.got_state`), not in `MacroEnv`. The v4 path does not use `MacroEnv` at all. Instead:

- Macro clause info (params, rest_param) comes from `ModuleEntry::Macro` in the tc module table, accessed via `tc.symbol_table(module).get(name)`.
- The function pointer comes from the GOT, keyed by the macro clause's JIT symbol name (e.g., `__macro_name_clause0`).

This requires that `compile_and_register_defn` registers the macro clause function in the GOT under the same name used for lookup. The naming convention follows the existing `synthesize_macro_clause_defn` output.

### 3.5 Transitive Callee Walk Utility (S-3)

Extract the transitive callee walk as a reusable utility so both the worker and future incremental recompilation can use it:

```rust
/// Walk the transitive closure of a symbol's callees via the TC symbol table.
///
/// Starting from the given symbol, reads `ModuleEntry.callees` from
/// `tc.symbol_table(module).get(name)` and recursively follows each
/// callee's own `callees`. Returns the full set of transitive dependencies.
///
/// Each callee's `ModuleEntry.callees` is already populated because
/// it was typechecked before the starting symbol (per spec section 9.2.5:
/// macro body can only call functions defined before it).
///
/// The walk uses a visited set to handle diamond dependencies
/// (A calls B and C, both call D — D appears once in the result).
pub fn collect_transitive_callees(
    tc: &cranelisp_typecheck::TypeChecker,
    start_module: &ModuleFullPath,
    start_symbol: &Symbol,
) -> Vec<(ModuleFullPath, Symbol)>
```

A wrapper filters to only uncompiled symbols:

```rust
/// Collect the transitive callees of a symbol that do not yet have
/// compiled code pointers in the GOT. These are the symbols that
/// must be compiled before the starting symbol can be called.
fn collect_transitive_uncompiled_deps(
    tc: &cranelisp_typecheck::TypeChecker,
    inmem_worker: &InMemWorkerState,
    start_module: &ModuleFullPath,
    start_symbol: &Symbol,
) -> Vec<(ModuleFullPath, Symbol)>
```

Implementation: `collect_transitive_callees` does a breadth-first walk. For each `FQSymbol` in `ModuleEntry.callees`, it looks up `tc.symbol_table(callee.module).get(callee.symbol)` and reads that entry's `callees` in turn. A `HashSet<(ModuleFullPath, Symbol)>` tracks visited symbols to avoid revisiting diamond dependencies. The walk terminates because the call graph is acyclic (spec section 9.2.5 guarantees forward-only references).

The wrapper `collect_transitive_uncompiled_deps` calls `collect_transitive_callees` and filters the result to symbols whose GOT slot is empty (no code pointer yet). It also includes the starting symbol itself if it is uncompiled.

This utility lives in `src/worker.rs` (or a new `src/call_graph_util.rs` if the file grows large). It reads from `tc.symbol_table(module).get(name).callees` -- no new TC API is needed (Decision 21).

### 3.6 Inline Compilation of Macro Dependencies

```rust
/// Compile a macro and all its transitive uncompiled dependencies inline.
///
/// Called from try_expand_for_pass2 when a macro's function pointer is missing.
/// Compiles deps in dependency order (callees before callers), then compiles
/// the macro clause itself. Notifies the scheduler of each completion.
fn compile_macro_deps_inline(
    tc: &mut cranelisp_typecheck::TypeChecker,
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    scheduler: &mut CompileScheduler,
    module: &ModuleFullPath,
    macro_symbol: &Symbol,
    accumulator: &ModuleCheckAccumulator,
) -> Result<(), CranelispError>
```

This function:

1. Calls `collect_transitive_uncompiled_deps` to get the ordered list of uncompiled deps.
2. For each dep (in dependency order — callees first):
   - Look up the symbol's defn AST from the typechecked forms (or synthesize it for macro clause symbols).
   - Build a `CheckResult` from the accumulator's accumulated state (method_resolutions, expr_types, etc. — all forms typechecked so far in Pass 2 are available).
   - Call `compile_and_register_defn`.
   - Call `scheduler.notify_priority_codegen_complete` as a side effect.
3. Compile the macro clause function itself (section 3.7).

### 3.7 Macro Clause Compilation

When the macro clause function needs compilation (e.g., `__macro_name_clause0`):

1. Look up the macro's original sexp from `ModuleEntry::Macro` via `tc.symbol_table(module).get(macro_name)`.
2. Parse via `parse_defmacro`, extract the relevant clause.
3. Synthesize the defn sexp via `synthesize_macro_clause_defn`.
4. Expand quasiquotes via `expand_quasiquotes`.
5. Build AST via `build_program`.
6. Typecheck via `tc.check` (additive, in the macro's module context).
7. Compile via JIT, extract function pointer, register in GOT.

This mirrors the existing `compile_single_clause` in `src/expander.rs`. The function reuses that (or a refactored version of it) with the worker's JIT instance instead of creating a fresh JIT per clause.

## 4. BlockingJitCodegen Handler

In single-threaded Step 4, the `BlockingJitCodegen` handler in `priority_worker_loop` is **NOT used** for macro deps — those are compiled inline by `compile_macro_deps_inline` within `process_module_forms` (section 3.6). The handler stub remains for Step 5+ where cross-module macro dependencies may exist: the dep is in another module's codegen queue, and the scheduler dispatches it as `BlockingJitCodegen` to compile the dep before the blocked module can continue.

The current stub at `worker.rs` line 380 is left as-is for Step 4:

```rust
Some(PriorityWork::BlockingJitCodegen(_module, _symbol)) => {
    // Step 4: macro deps compiled inline in process_module_forms.
    // Step 5+: cross-module macro deps dispatched here.
    unreachable!("BlockingJitCodegen not expected in Step 4 single-module mode");
}
```

## 5. C2 Filter Change

In `session_v4.rs`, function `sexp_qualifies` (line 70), remove the `defmacro` rejection:

```rust
// Before:
if name == "defmacro" {
    return false;
}

// After: (line removed)
```

Programs with `defmacro` forms now qualify for the v4 path, provided they have no imports, no operators, and no cross-module dependencies.

## 6. Edge Cases

### 6.1 Multiple Macros in One Module

A module may define multiple macros that each require different helper functions:

```lisp
(defn helper-a [] 1)
(defmacro macro-a [x] ...)   ; calls helper-a
(defn helper-b [] 2)
(defmacro macro-b [x] ...)   ; calls helper-b
(macro-a 10)                  ; inline compile: helper-a + macro-a, then expand
(macro-b 20)                  ; inline compile: helper-b + macro-b, then expand
```

Each macro call triggers inline compilation of its uncompiled deps. By the time `(macro-b 20)` is encountered, `helper-a` and `macro-a` are already compiled (from the first call). `helper-b` and `macro-b` are compiled inline at this point. This works naturally because `collect_transitive_uncompiled_deps` only returns symbols that are not yet in the GOT.

### 6.2 Macro Calling Another Macro

A macro's expansion may produce a form that is itself a macro call:

```lisp
(defmacro inner [x] `(add-i64 ~x 1))
(defmacro outer [x] `(inner ~x))
(outer 5)  ; expands to (inner 5), then to (add-i64 5 1)
```

The recursive expansion in `expand_sexp_recursive` handles this: after expanding `outer`, the result `(inner 5)` is re-expanded. Both macros must have compiled function pointers before `(outer 5)` can be expanded.

The `compile_macro_deps_inline` function compiles the outermost macro and all its deps. On recursive re-expansion, `inner` is also a macro call — but since we compiled all macros' clause functions during the inline compilation step (the transitive walk includes macro clause deps), `inner`'s function pointer is already available.

If `inner` has deps that were not in `outer`'s transitive closure, `try_expand_for_pass2` will compile them inline when processing the re-expanded form. This is handled naturally by the recursive expansion checking for missing function pointers at each level.

### 6.3 Recursive Expansion Depth Limit (I-2)

`expand_sexp_recursive` already implements depth-limited recursive expansion with a hard limit of 100. The v4 path reuses this unchanged. If expansion produces another macro call, it is expanded in the same invocation until a fixed point or the depth limit.

The depth limit catches:
- **Infinite expansion loops**: macro A expands to a call to macro A (direct cycle).
- **Indirect cycles**: macro A expands to macro B which expands to macro A.
- **Excessive nesting**: macro A expands to macro B which expands to macro C... beyond 100 levels.

When the depth limit is exceeded, `expand_sexp_recursive` returns `CranelispError::MacroError` with a message indicating the expansion depth was exceeded and the macro name at the point of failure. This propagates through `try_expand_for_pass2` as `Err(e)`, which the Pass 2 loop handles by calling `scheduler.notify_module_failed`.

Note: cycle detection at the call graph level (before expansion) is not needed because the call graph is acyclic by construction (spec section 9.2.5: macro body can only call functions defined before it). The depth limit guards against cycles that arise from expansion output, not from the static call graph.

### 6.4 Error Handling During Expansion (I-4)

Errors during expansion fall into categories:

| Error | Source | Handling |
|-------|--------|----------|
| No matching clause | `find_matching_clause` returns None | `CranelispError::MacroError`, returned as `Err` |
| Runtime panic in macro | JIT code calls `runtime_panic` | Caught by `invoke_jit_protected`, converted to `CranelispError`, returned as `Err` |
| Hardware trap (SIGFPE, etc.) | JIT code | Caught by signal handler + `siglongjmp`, converted to `CranelispError`, returned as `Err` |
| Expansion depth exceeded | `expand_sexp_recursive` | `CranelispError::MacroError`, returned as `Err` |
| Invalid return value | `invoke_clause` validates heap pointer | `CranelispError::MacroError`, returned as `Err` |
| Inline compilation failure | `compile_and_register_defn` | `CranelispError`, returned as `Err` |

**Error propagation path**: `try_expand_for_pass2` catches all expansion and inline-compilation errors and returns `Err(CranelispError)`. The Pass 2 loop matches on this and calls `scheduler.notify_module_failed(module, error)`, which moves the module to the `Failed` pool and cascades failure to any modules waiting on this one (per `concurrent-pipeline.md` section 2.3). The worker then returns from `process_module_forms` without further processing.

This is the same error propagation model used by typecheck errors: the worker catches the error, reports it to the scheduler, and moves on. The scheduler handles cascade and the session's `wait_inmem_complete` returns the error to the caller.

### 6.5 Defmacro-in-Results

A macro expansion may produce a `defmacro` form (the `defmacro-in-results` pattern from the old pipeline). The per-sexp expansion flow handles this naturally:

1. Expand the macro call, get result sexp.
2. Flatten `(begin ...)` forms.
3. For each resulting form: if it is a `defmacro`, register it (same as Pass 1 for defmacro). Otherwise, continue with AST building and typecheck.

This requires the Pass 2 loop to handle multi-form expansion results (a single sexp expanding to multiple forms via `begin` flattening).

## 7. Debug Logging (S-2)

Add `log::debug!` calls at key points in the macro expansion flow:

1. **On inline compilation**: log the module name, form index, and the full list of uncompiled dependencies being compiled inline.
2. **On each dep compiled**: log the module and symbol being compiled, and whether it is a regular defn or macro clause.
3. **On expansion**: log the macro name and whether expansion succeeded, produced another macro call (recursive), or hit the depth limit.

These use the standard `log` crate at `debug` level, so they are silent in normal operation and activated with `RUST_LOG=cranelisp=debug`.

## 8. Sketch Comparison

### 8.1 How the Sketch Handles Macro Compilation

The sketch (`sketch/src/batch.rs`, `sketch/src/macro_expand.rs`) compiles macros inline and eagerly:

1. During the per-sexp processing loop in `batch.rs`, when `is_defmacro(sexp)` is true, `compile_macro` is called immediately.
2. `compile_macro` creates a fresh JIT per clause, typechecks the clause body, compiles it, and extracts the function pointer.
3. The macro is registered in `MacroEnv` (a standalone HashMap of name to compiled clauses).
4. Subsequent sexps that are macro calls are expanded immediately via `expand_sexp`.
5. The sketch handles `defmacro-in-results` by checking expanded forms for nested defmacros.

Key characteristic: **synchronous, eager, inline compilation**. The macro is fully compiled when encountered. No blocking, no deferred codegen, no scheduler.

### 8.2 Whether v4 Follows or Diverges

**Partially follows, partially diverges:**

| Aspect | Sketch | v4 | Rationale |
|--------|--------|----|-----------|
| Timing | Eager (compile on encounter) | Demand-driven (compile on first *call*) | A module may define macros used only by importers; compiling them eagerly wastes work if never called locally. But when a call IS encountered, compilation is inline and synchronous — same as the sketch. |
| Compilation context | Fresh JIT per clause | Worker's shared JIT | Eliminates JIT-per-clause overhead. |
| Blocking | None (synchronous inline) | None (synchronous inline) | Single-threaded Step 4 compiles deps inline, same as the sketch. No scheduler-driven blocking needed. |
| Macro storage | `MacroEnv` (standalone) | Module table (`ModuleEntry::Macro`) + GOT | Consolidates macro state with the rest of the module system. No separate macro registry to keep in sync. |
| Expansion locus | `MacroExpander` trait in frontend | Free functions called by the worker | Keeps compilation logic in the worker (binary crate) rather than pushing it into the frontend crate, maintaining crate boundary cleanliness. |
| Call graph | Not tracked | TC-sourced `ModuleEntry.callees` (Decision 21) | Enables pre-codegen dependency discovery. The sketch doesn't need this because it compiles eagerly inline. In v4, the call graph enables smart filtering: only compile what's actually needed. |

### 8.3 What the Sketch Solved That We Preserve

- **Sequential form processing**: both approaches process sexps in source order, with macros available from the next form.
- **Inline compilation**: both compile macro deps synchronously when needed — no deferred/async codegen for single-threaded mode.
- **Marshal/unmarshal/invoke**: the core expansion machinery (sexp-to-runtime, invoke function pointer, runtime-to-sexp) is reused from the sketch via `src/expander.rs` and `src/marshal.rs`.
- **Signal protection**: `invoke_jit_protected` with `sigsetjmp`/`siglongjmp` for hardware trap recovery is preserved unchanged.
- **Depth-limited recursive expansion**: the 100-depth limit from the sketch is preserved (section 6.3).
- **Defmacro-in-results**: the sketch's pattern of checking expansion output for nested defmacros is preserved.
- **Clause matching**: `clause_matches` logic (fixed params, rest params, bracket destructuring) is reused unchanged.

## 9. Implementation Order

1. Make `MacroClauseEntry`, `MacroEntry`, `clause_matches`, `find_matching_clause`, `invoke_clause`, `rewrite_spans`, `expand_sexp_recursive` `pub(crate)` in `src/expander.rs`.
2. Write `collect_transitive_callees` and `collect_transitive_uncompiled_deps` (section 3.5).
3. Write `compile_macro_deps_inline` (section 3.6) and the macro clause compilation helper (section 3.7).
4. Write `try_expand_for_pass2` in `src/worker.rs` (section 3.3).
5. Restructure `process_module_forms`: change Pass 2 to per-sexp expand-then-check loop. Pass `inmem_worker`, `platform_symbols`, and `scheduler` through so inline compilation can happen.
6. Update `BlockingJitCodegen` stub with `unreachable!` and Step 5 comment (section 4).
7. Remove `defmacro` rejection from `sexp_qualifies` in `session_v4.rs` (section 5).
8. Add debug logging (section 7).
9. Test: programs with inline `defmacro` + macro calls produce identical results on `--v4 --run` vs old path.

## Next Skills

- `/typecheck` — populate `call_graph_edges` during Pass 2 typecheck and write `callees` to `ModuleEntry` during `finalize_check_result()` (Decision 21). Verify `check_form(CheckBody)` works for macro clause defns when called outside normal Pass 2 flow.
- `/qa` — write integration tests for macro programs through the v4 path (simple defmacro + call, macro calling helper, macro calling macro, multi-clause dispatch, expansion error reporting).
- `/arch` — review this design doc for architectural coherence with `pipeline-v4.md` and `concurrent-pipeline.md`.
