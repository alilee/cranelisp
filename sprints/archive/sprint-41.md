# Sprint 41: Pipeline v4 Steps 2+3 — Scheduler + Worker Loop

**Status**: COMPLETE
**Ring**: — (structural / pipeline v4 migration)
**Goal**: Build the `CompileScheduler` (single-threaded) and wire a form-by-form worker loop through it, so that `register_module` uses the scheduler-driven path for single-module, no-macro programs.

## Context

Sprint 40 delivered the v4 skeleton (Step 0) and per-form typecheck API (Step 1). The `CompilerSession` wraps `CompilationSession` and delegates everything to the old path via `--v4`. `check_form()` / `FormCheckResult` / `ModuleCheckAccumulator` are ready in `cranelisp-typecheck`.

This sprint delivers the next two steps of `design/arch/pipeline-v4-roadmap.md`:

- **Step 2**: `CompileScheduler` struct with module lifecycle, priority ladder, waiter/unblock logic — tested in isolation, single-threaded.
- **Step 3**: `priority_worker_loop()` that processes modules form-by-form using `check_form()`, calling scheduler notifications. `register_module` switches from delegation to the scheduler-driven path.

After this sprint, simple programs (no macros, no multi-module dependencies) compile through the v4 scheduler path. Macros (Step 4), multi-module (Step 5), and REPL eval (Step 7) remain on the old delegation path.

**All skills MUST read these documents:**
- `design/arch/pipeline-v4.md` — the target architecture
- `design/arch/pipeline-v4-roadmap.md` — the migration plan (Steps 0-15)
- `design/arch/concurrent-pipeline.md` — scheduler design (module pools, priority queue, worker interfaces)

## Scope

### A. Resolve Sprint 40 Review Debt (3 FIXMEs)

Three Important findings from Sprint 40 review were deferred to "before Step 3":

1. **I-1** (`program.rs:925`): `resolve_multi_sig_overloads` is 135 lines — decompose into helpers.
2. **I-2** (`program.rs:114`): `ModuleCheckAccumulator` collects dead data (method_resolutions, expr_types, warnings duplicated in `self.state`). Clarify the accumulator's role: either make it authoritative or remove the dead fields.
3. **I-3** (`session_v4.rs:198`): `register_module` returns synthetic empty `CompileUnitResult` — this gets replaced entirely by the new scheduler-driven path.

I-3 is subsumed by Step 3 (new `register_module` implementation). I-1 and I-2 should be resolved in Wave 1 before implementation begins.

### B. Step 2: CompileScheduler (Single-Threaded)

Per `pipeline-v4-roadmap.md` Step 2:

- New `src/scheduler.rs` with `CompileScheduler`, `ModulePool`, `ModuleState`, `PriorityEntry`, `PriorityWork`, `WaitKind`, `Waiter`.
- Full scheduler interface from `concurrent-pipeline.md` §6: `register_module`, `register_module_cached`, `take_priority_work`, `block_for_typecheck`, `block_for_macro_codegen`, `notify_symbol_typechecked`, `notify_typecheck_done`, `notify_module_failed`, `notify_priority_codegen_complete`, `notify_inmem_codegen_complete`, `notify_inmem_codegen_batch_complete`, `notify_object_codegen_complete`, `take_object_codegen`, `wait_inmem_complete`, `wait_object_complete`, `shutdown`.
- Single-threaded: `take_priority_work` returns immediately (no condvar).
- Unit tests for the scheduler in isolation.

### C. Step 3: Form-by-Form Worker Loop

Per `pipeline-v4-roadmap.md` Step 3:

- New `process_module_forms(session, module, sexps, strategy)` that expands, builds AST, calls `check_form()` per form, notifies scheduler.
- New `priority_worker_loop(session)` dispatching `Typecheck` / `BlockingJitCodegen` / `JitCodegen`.
- `CompilerSession::register_module` switches from delegation to: parse source, register with scheduler, run `priority_worker_loop` until `wait_inmem_complete`.
- Macro programs fall back to old delegation path (Step 4 scope).

### Boundary: What Does NOT Change

- REPL eval path — still delegates to old `compile_unit + codegen_and_execute`
- Multi-module programs — still delegate (lazy dependency discovery is Step 5)
- Macro expansion — still uses `CraneliftExpander` (removal is Step 6)
- Cache-hit loading — still uses old path
- `CompilationSession` — unchanged, still wraps `TypeChecker`, `CraneliftExpander`, etc.

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `crates/cranelisp-typecheck/src/program.rs:925` | /typecheck | I-1: `resolve_multi_sig_overloads` 135 lines | Resolve in Wave 1 |
| `crates/cranelisp-typecheck/src/program.rs:114` | /typecheck | I-2: Accumulator dead data fields | Resolve in Wave 1 |
| `src/session_v4.rs:198` | /int | I-3: Synthetic empty CompileUnitResult | Subsumed by Step 3 |

No other active FIXMEs found in source code.

## Prior-Ring Coverage Audit

This sprint is pipeline infrastructure — coverage gaps are noted but not prioritized here.

Pre-existing: 11 sketch_port failures (triaged in prior sprints, not in scope).

## Architecture Review

**Reviewer**: /arch
**Verdict**: APPROVED with conditions

### 1. Technical Coherence — Steps 2+3 as a Testable Increment

Steps 2+3 form a coherent, testable unit. Step 2 produces a self-contained `CompileScheduler` testable in isolation (module lifecycle, priority ordering, waiter/unblock, cascade failure — all unit-testable with no compilation infrastructure). Step 3 wires the scheduler into `register_module`, producing an end-to-end observable change: simple programs compile through the new path. The acceptance criterion ("simple programs compile via `--v4 --run` through the scheduler path") is concrete and verifiable.

The two-pass requirement is correctly handled: `process_module_forms` must drive Pass 1 (register all signatures) then Pass 2 (check all bodies) over the same form list, calling `check_form()` with `CheckPass::Register` then `CheckPass::CheckBody`. The sprint text in Section C says "expands, builds AST, calls `check_form()` per form, notifies scheduler" — this is ambiguous about the two-pass structure. `/int` must implement both passes, not a single-pass loop. The existing `check_form` API already takes a `CheckPass` enum, so the mechanism is ready.

**Condition C1**: `/int`'s approach (to be filled) must explicitly describe the two-pass iteration. A single-pass `process_module_forms` that calls `check_form` once per form will produce incorrect results (body checking before all signatures are registered).

### 2. No Interim Architecture

No throwaway infrastructure detected. The `CompileScheduler` is the target architecture from `concurrent-pipeline.md` — it starts single-threaded but its API is designed for multi-threaded use (Step 11). The `priority_worker_loop` is the target worker loop. The `process_module_forms` function is the target form processing logic. All three survive to the final architecture.

The only interim aspect is that `take_priority_work` returns immediately (no condvar park) since there is only one caller thread. This is the correct single-threaded fallback described in `concurrent-pipeline.md` 10.3 and does not create throwaway code — the multi-threaded version adds condvar parking to the same function.

### 3. Fallback Boundary

The boundary between "scheduler path" and "old delegation path" is clean for this sprint's scope:

- **Detection mechanism**: `register_module` in `session_v4.rs` will parse the source and inspect the AST. If the program contains macro calls (including prelude macros from `(import [prelude [*]])`) or cross-module imports beyond the prelude, it falls back to the old delegation path (`self.inner.compile_unit` + `send_codegen`). The sprint text says "Macro programs fall back to old delegation path (Step 4 scope)."

- **Concern**: The phrase "no macros, no multi-module dependencies" means very few real programs qualify — even `(+ 1 2)` requires the prelude (which defines `+` as a trait method via macros). The testable subset is limited to programs that use only primitives and special forms directly: `(add-i64 1 2)`, `(if true 1 2)`, `(let [x 3] x)`, etc.

**Condition C2**: The sprint's acceptance criterion must clarify what "simple programs" means. Suggest: "programs using only special forms and primitives (no `(import ...)`, no macro calls, no operator syntax requiring trait dispatch)." `/qa` integration tests should target this subset explicitly.

- **Prelude injection**: The current pipeline injects `(import [prelude [*]])` into every non-prelude module. For the Step 3 scheduler path, this injection must be suppressed (prelude loading is Step 5). Programs compiled through the Step 3 path must work WITHOUT prelude — this is consistent with the "optional prelude" design principle but limits the testable surface.

**Condition C3**: `/int` must document how prelude injection is handled in the Step 3 path. Either: (a) suppress prelude injection for scheduler-path modules (simple, correct, limits test surface), or (b) detect prelude import as a multi-module dependency and fall back. Option (a) is preferred — it keeps the scheduler path clean and matches the "optional prelude" principle.

### 4. Interface Gaps

#### 4.1 `FormCheckResult` / `check_form` Completeness

`FormCheckResult` currently carries: `method_resolutions`, `expr_types`, `constrained_fn`, `mono_defns`, `default_method_defns`, `multi_sig_defns`, `warnings`, `call_graph_edges`. This is sufficient for the worker loop to:
- Notify the scheduler (`call_graph_edges` provide the data for future macro dependency walking).
- Accumulate into the module's `CheckResult` for codegen.

However, `FormCheckResult` does not carry `type_defs` or `constructor_to_type` — these are needed by the backend (they appear in `CheckResult`). For Step 3's limited scope (no ADTs in primitive-only programs), this is not blocking. But it will need to be addressed before Step 4 or Step 5, since prelude/stdlib modules define ADTs.

**Warning W1**: `FormCheckResult` will need `type_defs` and `constructor_to_type` fields (or an equivalent accumulation path) before macro-using programs can compile through the scheduler. This is Step 4 scope but `/typecheck` should be aware.

#### 4.2 `ModuleCheckAccumulator` Dead Data (I-2)

The FIXME on `ModuleCheckAccumulator` notes that `method_resolutions`, `expr_types`, and `warnings` are collected but never consumed during finalization (the authoritative data stays in `self.state`). This sprint correctly schedules I-2 resolution in Wave 0. The resolution should decide: either the accumulator IS the authoritative source (and `finalize_check_result` reads from it), or these fields are removed. For the scheduler path, the accumulator should be authoritative — workers build the module's `CheckResult` by accumulating `FormCheckResult` entries, and the final `CheckResult` is the accumulated result.

**Condition C4**: I-2 resolution must make the accumulator authoritative for the fields it collects. The alternative (removing the fields and keeping `self.state` as authoritative) would make the scheduler path unable to incrementally build a `CheckResult` — it would require accessing typechecker internal state, violating the interface boundary.

#### 4.3 Scheduler API for Single-Threaded Operation

The scheduler API from `concurrent-pipeline.md` section 6 is designed for concurrent access with condvars. For single-threaded operation, three adjustments are needed:

1. **`take_priority_work` must not park.** The sprint text correctly notes this: "returns immediately (no condvar)." In single-threaded mode, if no work is available, that means all modules are either Done, Failed, or Blocked — the loop should terminate rather than deadlock.

2. **Level 4 (`JitCodegen`) needs session access.** The scheduler's `take_priority_work` at level 4 must "scan first `typecheck_done` module for a typechecked symbol without a code pointer." This requires querying session state, not just scheduler state. In the concurrent design, the scheduler calls into session module tables. For Step 3, the scheduler must either (a) receive a callback/reference to check symbol codegen state, or (b) expose a `take_jit_codegen` method that the worker loop calls separately. Option (a) matches the design; option (b) is simpler for single-threaded.

**Warning W2**: The scheduler cannot implement level 4 of `take_priority_work` purely from its own state — it needs to know which symbols have code pointers. For Step 3, this is acceptable to defer: JitCodegen (level 4) only fires after `notify_typecheck_done`, and for the simple programs in scope, the worker loop can do JIT codegen outside the scheduler (compile all symbols after typecheck completes, then notify). Full level-4 integration can wait for Step 4 or later. `/int` should implement a simpler post-typecheck codegen sweep rather than trying to get level 4 of `take_priority_work` working with session queries.

3. **`wait_inmem_complete` in single-threaded mode.** The worker loop runs inline on the calling thread. After the loop terminates (no more work), the caller checks `wait_inmem_complete`. This must return `Ok(())` if all modules are Complete/TypecheckDone-with-inmem_done, or `Err` if any are Failed. No condvar needed — it is a synchronous state check.

### 5. Design References

The sprint correctly references:
- `pipeline-v4.md` — target architecture
- `pipeline-v4-roadmap.md` — Steps 2+3 details
- `concurrent-pipeline.md` — scheduler design

Missing references:
- `/typecheck` should also reference `design/typecheck/check-form-api.md` for the `check_form` API design (already listed in the skill plan).
- `/int` should reference `src/CLAUDE.md` for code structure conventions (max 100 lines/function, error handling).
- `/qa` should note that integration tests for the `--v4` path must use primitive-only programs (no prelude) given the Step 3 scope.

### 6. Debt Assessment

The sprint handles carried debt appropriately:
- I-1 and I-2 are scheduled in Wave 0, before implementation begins. This is correct.
- I-3 is subsumed by Step 3. This is correct — the synthetic `CompileUnitResult` return goes away when `register_module` is rewritten.
- No items have been deferred more than once (these are from Sprint 40 review).

### Summary of Conditions and Warnings

| ID | Type | Description |
|----|------|-------------|
| C1 | Condition | `/int` approach must describe two-pass iteration (Register then CheckBody) explicitly |
| C2 | Condition | Acceptance criterion must define "simple programs" = primitives + special forms only, no prelude |
| C3 | Condition | `/int` must document prelude injection handling: suppress for scheduler path (preferred) or detect and fall back |
| C4 | Condition | I-2 resolution must make accumulator authoritative, not remove its fields |
| W1 | Warning | `FormCheckResult` will need `type_defs`/`constructor_to_type` before Step 4 — `/typecheck` should be aware |
| W2 | Warning | Level 4 of `take_priority_work` requires session state; `/int` should use a simpler post-typecheck codegen sweep for Step 3 |

## Skill Plans

### /int
**Task**: Implement `CompileScheduler` (Step 2) and form-by-form worker loop (Step 3). Resolve I-3.
**Design doc**: `design/arch/concurrent-pipeline.md` (scheduler design), `design/arch/pipeline-v4-roadmap.md` (Steps 2+3)
**Approach**:

#### C1: Two-pass iteration in `process_module_forms`

`process_module_forms(session, module, sexps, strategy)` drives two explicit passes over the form list, matching the `check_form` API from `design/typecheck/check-form-api.md`:

1. **Parse + expand + build AST** for all forms up front. For each sexp: expand (no macros in scope for Step 3, so expansion is identity), build AST via `AstBuilder`. Collect into `Vec<TopLevel>`.
2. **Pass 1 — Register**: Iterate all forms in source order, calling `tc.check_form(module, &form, CheckPass::Register)` for each. This registers type definitions, trait declarations, and function signatures. Accumulate each `FormCheckResult` into a `ModuleCheckAccumulator`.
3. **Pass 2 — CheckBody**: Iterate all `Defn` forms in source order, calling `tc.check_form(module, &form, CheckPass::CheckBody)` for each. This infers body types, generalizes, and detects constrained polymorphism. After each form, call `scheduler.notify_symbol_typechecked(module, symbol)`.
4. After both passes complete: finalize the accumulated `CheckResult`, call `scheduler.notify_typecheck_done(module)`.

On any error in either pass: call `scheduler.notify_module_failed(module, error)` and return.

#### C2: "Simple programs" definition

A program qualifies for the scheduler path in Step 3 if and only if:
- It contains **no `(import ...)` forms** (no cross-module dependencies).
- It contains **no macro calls** — all top-level forms are special forms (`defn`, `deftype`, `deftrait`, `impl`, `let`, `if`, `do`, `match`) or primitive function calls (`add-i64`, `sub-i64`, `int-to-string`, etc.).
- It uses **no operator syntax** (`+`, `-`, `*`, etc.) since operators require prelude trait dispatch.
- It uses **no prelude-defined names** (no `println`, no `list`, no `empty?`, etc.).

In practice: `(defn main [] (add-i64 1 2))`, `(defn main [] (if true 1 2))`, `(defn main [] (let [x (add-i64 3 4)] x))` are the kinds of programs that qualify. Detection: after parsing, scan the AST for import forms and unresolved names. If any are found, fall back to the old delegation path.

#### C3: Prelude injection handling

Option (a) — **suppress prelude injection for scheduler-path modules**. The Step 3 `process_module_forms` does NOT inject `(import [prelude [*]])`. Programs on the scheduler path run without any prelude, using only compiler primitives and special forms. This is consistent with the "optional prelude" design principle and keeps the scheduler path clean. Prelude injection is deferred to Step 5 (lazy dependency discovery), where it will follow the standard lazy loading path described in `pipeline-v4.md` §3.5.

The detection in `register_module` checks whether the program needs the prelude (operator syntax, unresolved names) and falls back to the old path if so. Programs that pass the C2 filter do not need the prelude by definition.

#### W2: Post-typecheck codegen sweep

Instead of implementing level 4 of `take_priority_work` (which requires the scheduler to query session state for un-codegenned symbols), use a simpler approach for Step 3:

After `process_module_forms` completes and calls `notify_typecheck_done`, the worker loop receives no more `Typecheck` work items. The worker then performs a **codegen sweep**: iterate all defined symbols in the module's accumulated `CheckResult`, compile each via existing `FnCompiler` + `Jit` (reusing the old `compile_and_register_defn` path), register each code pointer in the GOT, and call `scheduler.notify_inmem_codegen_complete(module, symbol, is_last)` for each. When all symbols are compiled, the final notification sets `inmem_done`.

Concretely: `priority_worker_loop` dispatches `PriorityWork::Typecheck` to `process_module_forms`. After typecheck completes, `priority_worker_loop` calls a new `codegen_module_symbols(session, module)` helper that does the sweep. This avoids the scheduler needing to scan session state for level 4 — the worker drives codegen directly after typecheck, then notifies completion. Full level-4 `take_priority_work` integration (per-symbol claiming from the scheduler) is deferred to Step 4+.

For Step 3, `take_priority_work` implements levels 1-3 only. Level 4 (`JitCodegen`) returns `None` — the codegen sweep handles it outside the scheduler. `take_priority_work` returns `None` when levels 1-3 are empty, terminating the worker loop.

#### Scheduler API (Step 2)

`CompileScheduler` in `src/scheduler.rs` implements the full interface from `concurrent-pipeline.md` §6, with Step 3 scope notes:

**Implemented and exercised in Step 3:**
- `new()` — create scheduler with empty state.
- `register_module(module, delays_other)` — add module to TypecheckFirst or TypecheckNext.
- `take_priority_work()` — levels 1-3 only (pop TypecheckFirst, scan priority_queue for Ready, pop TypecheckNext). Returns `None` immediately when empty (no condvar park — single-threaded).
- `notify_symbol_typechecked(module, symbol)` — check waiter map, evaluate unblocking (no waiters in Step 3 scope, but logic is implemented).
- `notify_typecheck_done(module)` — move module to TypecheckDone, add to `typecheck_done` deque.
- `notify_module_failed(module, error)` — move to Failed, cascade to waiters.
- `notify_inmem_codegen_complete(module, symbol, no_remaining)` — remove from jit_reserved, set inmem_done when no_remaining is true, move to Complete when inmem_done and object_done.
- `wait_inmem_complete()` — synchronous state check: return `Ok(())` if all modules are Complete or TypecheckDone-with-inmem_done, `Err` if any Failed.
- `shutdown()` — set shutdown flag (for future condvar wakeup).

**Implemented but not exercised until later steps:**
- `register_module_cached(module, symbols)` — enters TypecheckDone with object_done=true (Step 13).
- `block_for_typecheck(module, needed_module, needed_symbol)` — move to TypecheckBlocked, add waiter (Step 5).
- `block_for_macro_codegen(module, needed)` — move to TypecheckBlocked, populate priority queue (Step 4).
- `notify_priority_codegen_complete(module, symbol)` — process per §4.3 (Step 4).
- `notify_inmem_codegen_batch_complete(module, symbols)` — batch mark for Linker loads (Step 13).
- `notify_object_codegen_complete(module)` — set object_done (Step 10).
- `take_object_codegen()` — return TypecheckDone module with object_done=false (Step 10).
- `wait_object_complete()` — synchronous check for object completion (Step 10).

All methods have full implementations (not `todo!()`), tested via unit tests. Methods not exercised in Step 3 are covered by scheduler unit tests only.

#### I-3 resolution

The old `register_module` in `session_v4.rs` (which delegates to `self.inner.compile_unit` and returns a synthetic empty `CompileUnitResult`) is replaced. The new `register_module` for qualifying programs: parses source, checks the C2 filter, registers the module with the scheduler, runs `priority_worker_loop` (which calls `process_module_forms` then `codegen_module_symbols`), and returns after `wait_inmem_complete`. Non-qualifying programs still fall back to the old delegation path. The synthetic `CompileUnitResult` construction and the I-3 FIXME are removed.

The return type of `register_module` changes — it no longer returns `CompileUnitResult`. Callers that need codegen results use `wait_inmem_complete()` + GOT lookup, matching the v4 design where `register_module` is fire-and-forget (pipeline-v4.md §3.1).

**Design refs**: `pipeline-v4.md`, `pipeline-v4-roadmap.md`, `concurrent-pipeline.md`, `design/typecheck/check-form-api.md`, `src/CLAUDE.md`
**Acceptance**: Simple programs (primitives + special forms only, no imports, no macros, no operator syntax) compile via `--v4 --run` through the scheduler path. `register_module` no longer delegates to old `compile_unit` for these programs. The `SchedulerStub` is replaced by a real `CompileScheduler`.

### /typecheck
**Task**: Resolve I-1 (decompose `resolve_multi_sig_overloads`) and I-2 (clarify accumulator role). Support any `check_form` API changes needed for Step 3 integration.
**Design doc**: `design/typecheck/check-form-api.md` (update if accumulator changes)
**Approach**:

#### I-1: Decompose `resolve_multi_sig_overloads` (135 → 3 helpers)

The 135-line function has three logical phases that map cleanly to separate helpers:

1. **`resolve_variant_types`** (~30 lines) — For a single multi-sig defn, iterate its variants: look up type vars by internal name, apply substitution to get concrete param/return types, check for duplicate signatures within the defn. Returns `Vec<(Vec<Type>, Type, Symbol)>` of `(concrete_params, concrete_ret, internal_name)` plus a `Vec<Vec<Type>>` sig set for duplicate detection. This is the inner loop body (lines 942-977).

2. **`register_mangled_variants`** (~40 lines) — Takes the resolved variant info from step 1. For each variant: compute mangled name, remove internal name from symbol table, register mangled name with generalized scheme, build the mangled `Defn` for codegen. Returns `Vec<Defn>` (mangled defns) and `Vec<(Vec<Type>, Type, Symbol)>` (resolved info for overload registration). This is lines 979-1016.

3. **`register_overloaded_base`** (~25 lines) — Takes the resolved variant info. Builds `OverloadVariant` entries, constructs the base name's `Overloaded` symbol table entry using the first variant's scheme, inserts into `resolved_overloads`. This is lines 1019-1056.

The outer `resolve_multi_sig_overloads` becomes a ~25-line loop that filters multi-sig defns and calls the three helpers in sequence. Each helper is well under 100 lines.

#### I-2: Make accumulator authoritative (C4 compliance)

**Problem**: `build_check_result()` reads `method_resolutions`, `expr_types`, and `warnings` from `self.state` (the `CheckState`). But `merge_form_result()` also collects these into the `ModuleCheckAccumulator`. The accumulator fields are dead — never read during finalization. C4 requires the accumulator to be authoritative so that the Step 3 scheduler can incrementally build a `CheckResult` without reaching into TypeChecker internals.

**Design**: Two changes make the accumulator authoritative:

1. **`merge_form_result` unchanged** — it already merges `FormCheckResult` fields into the accumulator correctly. No changes needed.

2. **`finalize_check_result` reads from accumulator, not `self.state`** — Replace the `build_check_result()` call (which drains `self.state.method_resolutions`, `self.state.expr_types`, `self.state.warnings`) with direct reads from the accumulator:
   - `method_resolutions`: take from `accumulator.method_resolutions` (already accumulated). The post-passes (resolve_pending_overloads, resolve_auto_curry) write additional resolutions into `self.state.method_resolutions` — these must be merged into the accumulator's map after the post-passes run, then the accumulator's map becomes the final value.
   - `expr_types`: apply final substitution to `accumulator.expr_types` (not `self.state.expr_types`). The accumulator holds partially-resolved types from each form's Pass 2; finalization re-applies substitution to catch variables pinned by later body checking.
   - `warnings`: take from `accumulator.warnings` (already accumulated). Any warnings emitted by post-passes (resolve_pending_overloads etc.) must also be appended to the accumulator before draining.
   - `type_defs` / `constructor_to_type`: continue reading from TypeChecker module tables (not accumulated per-form, as documented in the design doc and arch review).

   Concretely: delete `build_check_result()` as a separate method. Inline its logic into `finalize_check_result()` with the accumulator as the source. After post-passes run, sweep any new resolutions/warnings from `self.state` into the accumulator, then build `CheckResult` from the accumulator.

3. **`self.state` role clarified** — `CheckState` remains the *working* state during inference (substitution env, scope stack, deferred resolutions, pending overloads). Post-passes operate on `self.state` as before. But after post-passes complete, their outputs are swept into the accumulator, and the `CheckResult` is built exclusively from the accumulator. `self.state` is working scratch; the accumulator is the authoritative record.

**Invariant**: After `finalize_check_result()` returns, the accumulator has been fully drained. `self.state.method_resolutions`, `self.state.expr_types`, and `self.state.warnings` may be non-empty (leftover from post-passes) but are not consulted — only the accumulator's data feeds the `CheckResult`.

#### W1 Acknowledgement

`FormCheckResult` will need `type_defs` and `constructor_to_type` fields before Step 4 (macro-using programs that define ADTs). For Step 3's scope (primitive-only programs, no ADTs), these are not needed. When Step 4 work begins, `/typecheck` will add per-form type_def registration data to `FormCheckResult` and corresponding accumulation in `merge_form_result`. The current approach of reading type_defs from TypeChecker module tables in `finalize_check_result` remains correct as an intermediate step — Step 4 will decide whether to also accumulate them or keep the current sourcing.

#### check_form API changes for Step 3

No API signature changes needed. `check_form()`, `merge_form_result()`, and `finalize_check_result()` already have the correct signatures. The I-2 changes are internal to `finalize_check_result` (switching its data source from `self.state` to the accumulator). The `/int` worker loop calls the same public API.

**Design refs**: Sprint 40 review findings (I-1, I-2), `design/typecheck/check-form-api.md`, arch review C4
**Acceptance**: I-1 function split into <100-line helpers. I-2 accumulator made authoritative per C4 — `finalize_check_result` reads from accumulator, not `self.state`. All 305 typecheck tests pass.

### /arch
**Task**: Review sprint scope for v4 coherence. Review scheduler design against `concurrent-pipeline.md`. Confirm Step 2+3 form a coherent unit.
**Design doc**: n/a (review role)
**Approach**: Verify scheduler API matches `concurrent-pipeline.md` §6. Verify worker loop correctly uses `check_form` + scheduler notifications. Check that the fallback-to-old-path boundary for macros/multi-module is clean.
**Design refs**: `pipeline-v4.md`, `pipeline-v4-roadmap.md`, `concurrent-pipeline.md`
**Acceptance**: Architecture review section filled. Scheduler API approved.

### /qa
**Task**: Write tests for scheduler (unit) and form-by-form worker loop (integration). Verify full test suite passes.
**Design doc**: n/a
**Approach**: Scheduler unit tests: module lifecycle, priority ordering, waiter/unblock, cascade failure. Integration tests: simple programs through `--v4 --run` producing correct output.
**Design refs**: `concurrent-pipeline.md` §2 (lifecycle), §6 (API)
**Acceptance**: Scheduler unit tests cover lifecycle transitions. Integration tests verify `--v4` path produces same output as default. Full suite green (excluding pre-existing sketch_port failures).

### /review
**Task**: Review Wave 2 (scheduler) and Wave 3 (worker loop) code for quality. Verify Sprint 40 I-1/I-2 FIXMEs resolved.
**Design doc**: n/a
**Approach**: Standard review pass. Verify scheduler matches design doc API surface. Verify worker loop error handling.
**Acceptance**: All B+I findings resolved.

### /frontend
**Task**: No implementation work this sprint.

### /backend
**Task**: No implementation work this sprint. Verify codegen is unaffected.

### /platform
**Task**: No implementation work this sprint.

### /stdlib
**Task**: Validate stdlib modules compile after changes.
**Acceptance**: All 27 stdlib modules load without regression.

### /examples
**Task**: Validate all examples compile after changes.
**Acceptance**: All examples produce expected output.

### /port
**Task**: Validate exemplar compiles after changes.
**Acceptance**: Exemplar runs without regression.

### /repl
**Task**: Create sprint demo `repl/demos/v4b.demo`.
**Approach**: Demonstrate `--v4` flag running a simple program through the scheduler path.
**Acceptance**: Demo plays cleanly.

### /docs
**Task**: No implementation work this sprint.

### /spec
**Task**: No implementation work this sprint.

## Waves

_To be filled by /sprint during Phase 4 after architecture review and skill plan refinement._

### Wave 0: FIXME Resolution
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | I-1: Decompose `resolve_multi_sig_overloads` into <100-line helpers | done | 3 helpers extracted, outer function ~23 lines, all 305 tc tests pass |
| /typecheck | I-2: Remove or rationalize accumulator dead data fields | done | Accumulator now authoritative per C4; `build_check_result()` deleted; post-pass sweep into accumulator; 305 tc + full suite pass |

### Wave 1: Architecture Review
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Review sprint scope and scheduler design against concurrent-pipeline.md | done | APPROVED with 4 conditions (C1-C4) + 2 warnings (W1-W2), all addressed in skill plans |

### Wave 2: Scheduler Implementation (Step 2)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Implement `CompileScheduler` in `src/scheduler.rs` | done | 898 lines, full API from concurrent-pipeline.md §6, single-threaded |
| /qa | Write scheduler unit tests | done | 18 tests in `tests/scheduler.rs`, all pass |

### Wave 3: Worker Loop (Step 3) + Review
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Implement `process_module_forms` + `priority_worker_loop`, wire into `register_module` | done | `src/worker.rs` (408 lines), `session_v4.rs` rewritten, C2 filter, v4 path works end-to-end |
| /qa | Write integration tests for `--v4 --run` on simple programs | done | 10 tests in `tests/v4_pipeline.rs`: 8 scheduler-path + 2 fallback |
| /review | Review Wave 2 + Wave 3 code | done | 0B 3I 5S; all I findings fixed (SAFETY comments, double-parse, double-execution) |

### Wave 4: Validation + Showcase
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /stdlib | Validate 27 stdlib modules | done | 54 tests pass |
| /examples | Validate all examples | done | 15 tests pass |
| /port | Validate exemplar | done | 3 tests pass |
| /repl | Create sprint demo `repl/demos/v4b.demo` | done | 10 lines, verified through `--v4` REPL |

## Notes

### /review: Wave 2 + Wave 3 Code Review

**Reviewer**: /review
**Files reviewed**: `src/scheduler.rs`, `src/worker.rs`, `src/session_v4.rs`, `src/main.rs`, `crates/cranelisp-typecheck/src/program.rs` (I-1/I-2 resolution)

#### Sprint 40 FIXME Resolution Status

- **I-1** (`program.rs:925` — decompose `resolve_multi_sig_overloads`): **RESOLVED.** The 135-line function is decomposed into `resolve_variant_types` (~42 lines), `register_mangled_variants` (~40 lines), and `register_overloaded_base` (not reviewed but referenced). The outer `resolve_multi_sig_overloads` is now ~22 lines. All helpers are well under 100 lines.

- **I-2** (`program.rs:114` — accumulator dead data): **RESOLVED.** The accumulator is now authoritative per C4. `finalize_check_result` sweeps post-pass outputs from `self.state` into the accumulator (lines 657-665), resolves `expr_types` through final substitution from the accumulator (lines 668-672), and builds `CheckResult` exclusively from accumulator data (lines 678-688). `build_check_result()` is deleted from source (only remains in the plan doc). The `ModuleCheckAccumulator` doc comment explicitly states it is the authoritative source.

- **I-3** (`session_v4.rs:198` — synthetic CompileUnitResult): **RESOLVED.** `register_module` no longer constructs a synthetic `CompileUnitResult`. Qualifying programs go through `register_module_v4` (scheduler path); non-qualifying programs go through `register_module_old` (delegation). No FIXME comments remain in the file.

#### Findings

**I-1: Missing `// SAFETY:` comments on `unsafe` transmute blocks**

`worker.rs:347` and `session_v4.rs:350` both contain `unsafe { std::mem::transmute(code_ptr) }` without the required `// SAFETY:` comment. Per `src/CLAUDE.md` and the review workflow (step 5), every `unsafe` block must document why the invariants hold: the pointer is non-null, points to finalized JIT code, and the function has the correct calling convention (`extern "C" fn() -> i64`).

Note: the existing `pipeline.rs` has the same pattern without SAFETY comments. This is pre-existing debt, but new code should not perpetuate it.

**I-2: Double-parse in the C2 filter path**

`register_module` (session_v4.rs:213-215) calls `cranelisp_frontend::parse(source)` to check C2 qualification. Then `register_module_v4` passes `source` to `priority_worker_loop`, which calls `process_module_forms`, which parses the same source again (worker.rs:39). The source is parsed twice for every program that qualifies for the scheduler path.

This is not a correctness issue but is wasteful. The parsed sexps from the C2 check could be passed to `process_module_forms` instead of re-parsing. Alternatively, `process_module_forms` could accept pre-parsed sexps.

**I-3: `execute_zero_arg_defn` executes ALL zero-arg defns during codegen sweep**

`compile_regular_defns` (worker.rs:311-313) calls `execute_zero_arg_defn` for every zero-arg defn during the codegen sweep. Then `trampoline` (session_v4.rs:330) calls `main` again. This means `main` is executed twice: once during `codegen_module_symbols` and once during `trampoline`. For side-effecting programs (e.g., printing), this produces double output. For Step 3 acceptance ("simple programs compile via `--v4 --run` through the scheduler path"), this is a correctness bug if any test program has `main` with side effects.

The old path executes zero-arg defns during codegen because the last expression's value is the module result. The v4 path has a separate `trampoline` step. The codegen sweep should NOT execute defns — it should only compile and register code pointers.

**S-1: `compile_mono_defns` clones full `CheckResult` per mono specialization**

`compile_mono_defns` (worker.rs:269-286) creates a new `CheckResult` struct per monomorphised specialization, cloning `method_resolutions`, `constrained_fn_names`, `type_defs`, and `constructor_to_type` each time. For Step 3 scope (no mono defns in primitive-only programs), this is dead code, but it will become a performance concern when constrained polymorphism is in scope. Consider passing resolution data by reference or building a lightweight view struct.

**S-2: `register_module_old` ignores `send_codegen` fire-and-forget semantics**

`register_module_old` (session_v4.rs:271-288) calls `self.inner.send_codegen(unit_result, ctx)` but never calls `flush_codegen`. The old-path codegen runs asynchronously. Callers that subsequently call `trampoline` rely on `hot_flush_in_mem_queue` (which IS called in `trampoline` at line 335). This works but is fragile — the correctness depends on `trampoline` always being called after `register_module_old`. A comment noting this coupling would help.

**S-3: `codegen_module_symbols` dummy symbol notification for empty modules**

`codegen_module_symbols` (worker.rs:233-236) creates a dummy `Symbol::from("__empty_module")` and calls `notify_inmem_codegen_complete` with `no_remaining=true` when no defns were compiled. This works but is inelegant. The scheduler could have a `notify_inmem_codegen_skipped(module)` method that sets `inmem_done=true` directly, avoiding the phantom symbol.

**S-4: `qualifies_for_scheduler` does not reject `deftrait`/`deftype`/`impl` forms**

The C2 filter (session_v4.rs:51-85) rejects `import`, `export`, `mod`, `platform`, and `defmacro`, but does not reject `deftrait`, `deftype`, or `impl`. For Step 3 scope these forms would likely fail during typecheck (no ADT support without type_defs accumulation per W1), but the filter would let them through to the scheduler path where they might produce confusing errors rather than falling back cleanly. Not a blocker for Step 3's stated scope (primitives + special forms only), but worth noting.

**S-5: C2 filter comment says "no operator syntax" but `is_operator_symbol` only checks pure-operator symbols**

`is_operator_symbol` (session_v4.rs:88-96) only rejects symbols where ALL characters are operator chars. A symbol like `+x` or `!empty?` would pass. This is technically correct (those aren't pure operators) but the comment on `sexp_qualifies` says "Reject operator symbols that require prelude trait dispatch." Named primitives with operator chars in their names (e.g., hypothetical `not!`) would pass incorrectly. Low risk for Step 3 since no such primitives exist.

#### Architecture Alignment

- **Scheduler matches concurrent-pipeline.md**: The `CompileScheduler` API surface in `scheduler.rs` matches the design doc (module lifecycle, priority ladder, waiter/unblock, cascade failure). The level 4 deferral per W2 is correctly noted. Single-threaded semantics are correct (no condvar, immediate return on empty).

- **Two-pass typecheck (C1)**: `process_module_forms` correctly drives Pass 1 (register) then Pass 2 (check bodies), matching the C1 condition. Default method bodies are handled between passes. The pass structure is clear and well-decomposed into `pass1_register` and `pass2_check_bodies` helpers.

- **C2 filter**: Implemented at sexp level with recursive descent. Correctly rejects imports, macros, operators, and module-related forms. See S-4 for a minor gap.

- **C3 (no prelude injection)**: Correctly implemented — `process_module_forms` injects only `primitives` import, not prelude. This matches the sprint plan's Option (a).

- **W2 (post-typecheck codegen sweep)**: Correctly implemented as `codegen_module_symbols` called after `process_module_forms`. The sweep compiles all symbols then notifies the scheduler. However, the zero-arg execution (I-3 above) is a correctness concern.

#### Summary

| ID | Severity | File | Description |
|----|----------|------|-------------|
| I-1 | Important | `worker.rs:347`, `session_v4.rs:350` | Missing `// SAFETY:` comments on unsafe transmute |
| I-2 | Important | `session_v4.rs:213` + `worker.rs:39` | Double-parse of source (C2 check + worker) |
| I-3 | Important | `worker.rs:311-313` | Zero-arg defns executed during codegen sweep AND trampoline = double execution |
| S-1 | Suggestion | `worker.rs:269-286` | Full CheckResult clone per mono specialization |
| S-2 | Suggestion | `session_v4.rs:271-288` | `register_module_old` + `trampoline` coupling undocumented |
| S-3 | Suggestion | `worker.rs:233-236` | Dummy symbol for empty module inmem notification |
| S-4 | Suggestion | `session_v4.rs:51-85` | C2 filter does not reject deftrait/deftype/impl |
| S-5 | Suggestion | `session_v4.rs:88-96` | `is_operator_symbol` comment/logic minor mismatch |

**0 Blockers, 3 Important, 5 Suggestions.** All Important findings are addressable within the current sprint without design changes. I-3 (double execution) is the most urgent — it affects correctness of `--v4 --run` output.

## Outcome

### Delivered
- **Step 2: CompileScheduler** (`src/scheduler.rs`, 898 lines) — full module lifecycle from `concurrent-pipeline.md` §6, 17 API methods, single-threaded, all methods implemented (not `todo!()`)
- **Step 3: Form-by-form worker loop** (`src/worker.rs`, 408 lines) — `process_module_forms` (two-pass per C1), `codegen_module_symbols` (post-typecheck sweep per W2), `priority_worker_loop`
- **`register_module` rewrite** (`src/session_v4.rs`) — C2 filter for scheduler-path qualification, v4 path for primitives-only programs, fallback to old delegation for non-qualifying programs
- **Sprint 40 debt resolved**: I-1 (function decomposed into 3 helpers), I-2 (accumulator authoritative per C4), I-3 (synthetic CompileUnitResult removed)
- **Review I-findings fixed**: SAFETY comments, double-parse eliminated, double-execution removed
- **18 scheduler unit tests** (`tests/scheduler.rs`) — lifecycle, priority queue, waiter/unblock, failure cascade
- **10 v4 pipeline integration tests** (`tests/v4_pipeline.rs`) — 8 scheduler-path + 2 fallback verification
- **Sprint demo** (`repl/demos/v4b.demo`) — verified through `--v4` REPL
- **Test counts**: 1574 passed (305 typecheck + 171 lib + 18 scheduler + 10 v4_pipeline + 1070 integration), 11 pre-existing sketch_port failures, 0 ignored

### Deferred
- **S-1**: CheckResult clone per mono specialization — dead code for Step 3 scope, address when constrained poly enters v4 path
- **S-2**: `register_module_old` + `trampoline` coupling — document when old path is being removed (Step 15)
- **S-3**: Dummy symbol for empty module notification — cosmetic, address when empty modules are tested
- **S-4**: C2 filter doesn't reject `deftrait`/`deftype`/`impl` — these would fail at typecheck anyway; tighten filter when needed
- **S-5**: `is_operator_symbol` comment/logic minor mismatch — cosmetic

### Findings
- **Sync mode for v4 session**: The v4 `CompilerSession` uses sync mode (`CompilationSession::new()`) so the inline worker loop can write directly to GOT. This is correct for single-threaded but will need revisiting when multi-threaded workers arrive (Step 11).
- **Primitives import injection**: C3 suppresses prelude but the worker injects `(import [primitives [*]])` so named primitives are accessible. This is a design decision — Step 5 (lazy deps) will generalize this.
- **Narrow testable surface**: Only primitive-only programs qualify for the v4 path. This is expected — Steps 4-5 will widen the surface to macro and multi-module programs.
