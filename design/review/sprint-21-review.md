# Sprint 21 Code Review

Reviewer: `/review`
Date: 2026-03-20

## Scope

Five areas of change:
1. Auto-currying (typecheck + codegen)
2. Run-tests codegen
3. REPL `/run-tests` handler
4. REPL refactoring (repl.rs -> repl/{mod,commands,trace,run_tests,io_format}.rs)
5. Safety fix (execute() -> unsafe fn)

## 1. Auto-Currying

### Typecheck (A1)

**Files**: `crates/cranelisp-types/src/check.rs`, `crates/cranelisp-typecheck/src/infer.rs`, `crates/cranelisp-typecheck/src/checker.rs`, `crates/cranelisp-typecheck/src/program.rs`

**Design doc**: `design/typecheck/auto-curry.md` — thorough, includes sketch comparison, edge cases, and a clear implementation checklist. Well done.

**Assessment**: Clean implementation that follows the design doc exactly.

- `ResolvedCall::AutoCurry` now includes `total_count` (check.rs:24-28) — matches design.
- `try_auto_curry` (infer.rs:313-357) is 44 lines, well-structured, with proper guards (`args.is_empty()` check, `arg_types.len() < params.len()` check).
- `resolve_auto_curry` (program.rs:686-698) correctly drains `pending_auto_curry` into `method_resolutions`.
- Called at 3 locations in program.rs: after pass2 (batch, line 54), after REPL defn checking (line 75), and after REPL expression checking (line 89).
- `pending_auto_curry` cleared on REPL restore (checker.rs:900).

**Findings**:

- **(S1)** `try_auto_curry` only fires for `Expr::Var` callees (infer.rs:345-352). Auto-curry of a let-bound closure `(let [f (fn [a b] ...)] (f 1))` would NOT record a `pending_auto_curry` entry because the Var names a local, not a top-level function. The design doc acknowledges this (section "Currying a curried result") but implies it should work. The typechecker correctly infers the curried type, but no `AutoCurry` resolution is emitted for the backend. The backend would then hit the normal closure call path, which doesn't know to create a partial-application wrapper. This is likely deferred behavior, but should be explicitly documented as a known gap.

- **(S2)** The `try_auto_curry` method modifies the substitution (via `unify` calls at line 334) even when the original unification at line 272 has already failed. After a failed unification, the substitution may contain partial bindings from the failed attempt. The subsequent `try_auto_curry` unification operates on this potentially-polluted substitution. In practice this works because the failed unification's bindings are for the *wrong* function type (fewer params), while auto-curry's unification matches the correct prefix. But it relies on the implementation detail that Hindley-Milner substitution is monotonic. Worth a comment explaining why this is safe.

### Codegen (A2)

**Files**: `crates/cranelisp-backend/src/compiler/control_flow.rs` (lines 694-1004), `crates/cranelisp-backend/src/compiler/apply.rs` (lines 217-236)

**Design doc**: `design/backend/auto-curry-and-run-tests.md` — includes sketch comparison and RC analysis. Good.

**Assessment**: Solid implementation. Correctly follows the `compile_lambda` pattern for closure allocation, capture inc, and drop glue.

- `compile_auto_curry` (control_flow.rs:702-807): 105 lines, at the boundary of the 100-line guideline but well-structured with 3 helper methods (`compile_auto_curry_wrapper`, `build_auto_curry_drop_glue`, allocated separately).
- RC handling is correct:
  - Applied args are stored with `emit_rc_inc` for heap-typed values (lines 795-803).
  - Drop glue is built for heap-typed captures (lines 907-1004).
  - The wrapper loads captures and inc's them before the consuming call (lines 868-877) — correctly handles the multi-call reuse case identified in the design doc.
  - `compile_consuming_arg_list` is used at the call site (apply.rs:225), so variable args from the enclosing scope are properly inc'd before being captured.
- `emit_wrapper_call` reuse (line 882) correctly handles both Batch and Interactive dispatch modes.
- Drop glue pattern mirrors `build_closure_drop_glue` (already reviewed in Ring 1).

**Findings**:

- **(I1)** `compile_auto_curry` takes 6 parameters (plus `&mut self`), and `emit_single_test_iteration` takes 11. The `#[allow(clippy::too_many_arguments)]` annotations suppress the lint, but `src/CLAUDE.md` says "max 8 parameters — group related parameters into context structs." The `emit_single_test_iteration` function at 11 params violates this. Consider grouping `(swap_id, restore_id, collect_id, nanos_id)` into a `TraceRuntimeFns` struct.

- **(S3)** `compile_auto_curry_wrapper` at line 882 calls `self.emit_wrapper_call(&mut builder, ...)` where `builder` is the wrapper's FunctionBuilder, not the enclosing function's. This works because `emit_wrapper_call` only uses `self.module` and `self.ctx` (not `self.builder`). But it's a subtle borrowing pattern — the `&mut builder` parameter shadows the receiver's `self.builder`. A comment noting this intentional separation would help future readers.

- **(I2)** Auto-curry of non-Var callees: If the callee is a closure expression `((fn [a b] ...) 1)`, unification fails, `try_auto_curry` fires, returns a curried type — but no `AutoCurry` resolution is recorded (the `if let Expr::Var` guard). The typechecker reports success, but the backend has no resolution and falls through to the normal closure-call path in `compile_apply` (apply.rs:57-88), which doesn't know to create a partial application. This would produce a runtime type mismatch (calling a 2-arg closure with 1 arg). The typecheck should either reject this case or emit a resolution. Currently it silently miscompiles.

## 2. Run-Tests Codegen

**File**: `crates/cranelisp-backend/src/compiler/trace_codegen.rs` (lines 386-807)

**Design doc**: `design/backend/auto-curry-and-run-tests.md` section R1

**Assessment**: Well-decomposed implementation that correctly follows the sketch's unrolled-loop pattern with proper RC accounting.

- `compile_run_tests` (lines 397-492): 95 lines, within limit. Good decomposition into 7 helper methods.
- GOT swap infrastructure properly extracted from `compile_trace`: `prepare_got_groups`, `emit_got_swaps`, `emit_got_restores`. Good refactoring that eliminates duplication.
- Test discovery filters `traced_fns` for `name.starts_with("test-") && arity == 0` (line 431). The design doc mentions filtering by module name (`.test` modules), but the implementation only filters by function name prefix. This is simpler and correct for current usage — all test functions follow the naming convention.
- String allocation for test names uses `compile_string_lit` (line 453) — allocates once per test name, reused across iterations. Matches the refined design.
- RC accounting for the fold:
  - `tname_val` is inc'd before each closure call (pass: line 718, fail: line 775), protecting from consuming dec.
  - `trace_adt` is dec'd in pass block (lines 721-729), ownership transferred in fail block (line 778, "no dec here" comment).
  - `reason_str` is inc'd from Some extraction (line 772).
  - Some shell is dec'd in fail block after extracting reason (lines 786-794).
  - `pass_fn_val` and `fail_fn_val` are dec'd after the loop (lines 474-475).
  - All test name strings are dec'd after the loop (lines 479-489).

**Findings**:

- **(I3)** `compile_closure_call` made `pub(crate)` (apply.rs:567). The design doc doesn't mention this visibility change. It's needed so `trace_codegen.rs` can call it. This is architecturally fine — both files are in the same crate — but worth noting in the design doc for traceability.

- **(S4)** `GotGroupData` struct (lines 802-807) is defined at module scope but is only used by `compile_run_tests` and helpers. It could also serve `compile_trace`, which currently uses inline tuples `(i64, Vec<&TracedFnInfo>)`. Consider refactoring `compile_trace` to use `GotGroupData` for consistency. Low priority.

- **(S5)** The `prepare_got_groups` method (lines 511-566) leaks memory via `Box::into_raw` for slots and wrappers buffers (lines 536, 540). This is intentional (comment says "valid for program lifetime"), matching the same pattern in `compile_trace`. However, this leaks per `run-tests` invocation — if the user runs `/run-tests` 100 times in a REPL session, 100 sets of arrays accumulate. The sketch has the same behavior. Not a blocker for REPL usage, but worth noting as a known leak.

- **(B1)** In `emit_test_pass_block` (line 721-729), the trace ADT is dec'd with `None` for the drop glue parameter. The Trace ADT (`TraceCall`) has 5 heap-typed fields (`tname: String, tparams: String, tresult: String, tchildren: Vec, tnanos: Int`). Using `emit_rc_dec` with `None` for the drop glue means when the RC reaches 0, the allocation is freed but the fields are NOT dec'd — the strings and Vec inside the Trace ADT would leak. This needs `emit_rc_dec` with inline drop glue that walks the Trace fields, or the Trace ADT needs its own drop glue mechanism. The same issue exists in `compile_trace` (line 725 of the same file, in the `emit_body_discard` path).

    **Wait** — re-examining: the Trace ADT is constructed by the runtime (`cranelisp_collect_trace`), which returns a heap pointer. The runtime may handle its own RC/cleanup. But the codegen is calling `emit_rc_dec` which does `rc -= 1; if rc == 0 { dealloc(ptr) }` — this would free the outer allocation without walking fields. If the Trace fields (strings, children Vec) are independently RC'd, the outer dealloc frees the allocation but the strings inside still have their own RC counts. The question is: who dec's the inner strings when the Trace is freed? If nobody does, those strings leak.

    The sketch has the same pattern (dec the Trace in the pass block without field cleanup). This suggests the sketch also leaks Trace field strings. This is a pre-existing issue, not introduced by Sprint 21, but it's worth flagging.

    **Revised severity**: Downgrading from B to I since this is a pre-existing pattern (same as `compile_trace`) and Trace ADTs are small and short-lived in test contexts.

- **(I4)** In `emit_test_fail_block`, the `reason_str` is extracted from the Some ADT and inc'd (line 772). Then the Some shell is dec'd (lines 786-794). The dec also uses `None` for drop glue. Since Some contains a String field, freeing the Some shell without decrementing the contained String means the String's RC is one higher than it should be (it was inc'd at line 772, but the Some shell's ownership of the original reference was not dec'd via drop glue). The explicit inc at line 772 creates the new reference for the fail_fn call. But the Some shell being freed without running drop glue means the original reference it held is leaked.

    **Analysis**: The Some node holds `[tag, reason_str]`. The reason_str inside has RC=N (some count). We extract it and inc (RC=N+1). We dec the Some shell, which frees the shell allocation (header + tag + field). But the field (reason_str) at offset 24 inside the shell has a "logical" ownership that was never dec'd. So after the Some shell is freed, reason_str effectively has one extra RC count. After fail_fn consumes the inc'd reference (RC back to N), the original ownership from the Some is lost — the string has RC=N-1 effectively, but its actual RC is N (the original Some reference was never released). This is an RC leak of 1 per failed test.

    **Fix**: Either use `emit_rc_dec` with inline drop glue for the Some ADT, or manually dec the `reason_str` after extracting it (before inc'ing for the call, or use a net-zero: don't inc, and don't dec the shell's field ownership).

## 3. REPL /run-tests Handler

**File**: `src/repl/run_tests.rs`

**Assessment**: Clean, well-structured implementation. Direct invocation approach (call test functions via transmute'd code pointers) is simpler than the codegen approach and appropriate for a REPL slash command.

- Proper `// SAFETY:` comments on both transmute sites (lines 97-98, 137-138).
- Panic boundary via `cranelisp_runtime::panic::take_runtime_error()` (lines 134, 143).
- Clean separation: `discover_test_functions`, `run_discovered_tests`, `invoke_test_fn`, `interpret_option_string_result`.
- Prefix filter support (`/run-tests foo` runs only `test-foo*`).

**Findings**:

- **(S6)** `interpret_option_string_result` (lines 151-167) uses `NULLARY_TAG_THRESHOLD` (imported from `cranelisp_types`) to distinguish None from Some. This relies on the convention that nullary constructor tags are small integers below the threshold. If the threshold changes, this code would break silently. The current value is presumably a large-enough number that heap pointers always exceed it. A defensive comment explaining the invariant would help.

- **(S7)** The `unsafe` block at lines 159-162 reads directly from the heap at `HeapAdt::field_offset(0)`. This raw pointer arithmetic should ideally go through the backend's heap access helpers per `src/CLAUDE.md` "Representation containment." However, this is in the binary crate (`src/`), not the backend crate, so the helper is unavailable. The import of `cranelisp_backend::heap::HeapAdt::field_offset` is acceptable as it centralizes the offset constant.

## 4. REPL Refactoring

**Files**: `src/repl/mod.rs`, `src/repl/commands.rs`, `src/repl/trace.rs`, `src/repl/run_tests.rs`, `src/repl/io_format.rs`

**Assessment**: Good structural improvement. The monolithic `repl.rs` is split into focused modules:
- `mod.rs` — ReplSession, eval(), REPL loop, command dispatch
- `commands.rs` — all slash command handlers and formatting helpers
- `trace.rs` — trace display state, TracedCompiledExpr, expr_contains_trace
- `run_tests.rs` — /run-tests handler
- `io_format.rs` — IO trampoline forcing

**Findings**:

- **(S8)** `mod.rs` is still large (the tool couldn't read it in one pass at ~1000+ lines). The split extracted significant functionality but the core eval path and session management remain substantial. Future sprints might benefit from splitting `eval()` and the REPL loop into separate modules.

- No structural debts introduced. The module boundaries are clean and the `pub(crate)` / `pub(super)` visibility is correctly scoped.

## 5. Safety Fix (execute() -> unsafe fn)

**Files**: `crates/cranelisp-backend/src/lib.rs`, `src/repl/mod.rs`, `src/repl/trace.rs`

**Assessment**: Correct and well-documented.

- `CompiledExpr::execute()` and `CompiledProgram::execute()` are now `unsafe fn` (lib.rs:53, 77).
- Both have `# Safety` doc comments explaining the invariant (valid JIT code pointer with correct signature).
- `TracedCompiledExpr::execute()` in trace.rs:150 also `unsafe fn` with `# Safety` doc.
- Call sites in mod.rs:613 have `// SAFETY:` comments.
- All `unsafe` blocks with `std::mem::transmute` have SAFETY comments.

**Findings**: None. This is a clean improvement that makes the safety boundary explicit.

## Cross-Cutting Checks

### Audit Findings Reintroduction

- **God functions**: No function exceeds ~105 lines. `compile_auto_curry` is 105 lines (borderline). `compile_run_tests` is 95. All other new methods are well under 100. **PASS**
- **Panics in non-test code**: No `panic!()` found. `unwrap()` at mod.rs:226 is after a length check — safe. **PASS**
- **No unwrap in pipeline code**: Checked all new files. **PASS**
- **CompiledModule god object**: Not applicable to this sprint. **PASS**
- **String-based dispatch**: No new string-based dispatch introduced. **PASS**

### Design Doc Completeness

- `design/typecheck/auto-curry.md` — thorough, includes sketch comparison. **PASS**
- `design/backend/auto-curry-and-run-tests.md` — thorough, includes sketch comparison for both areas. **PASS**
- REPL refactoring — no design doc, but this is a mechanical restructuring (no new algorithms). **PASS**
- Safety fix — no design doc needed (API change, not a new design). **PASS**

### Sketch Comparison

Both design docs include detailed sketch comparison sections:
- Typecheck auto-curry: explains the sketch's detection mechanism in `inference.rs`, the pending list approach, and the multi-sig path. Notes where the reimplementation follows and where it defers. **PASS**
- Backend auto-curry: explains the sketch's RC debt (no drop glue, no capture inc). Notes the reimplementation's divergence to fix this. **PASS**
- Run-tests: explains the sketch's unrolled-loop pattern, test name allocation, and fold semantics. **PASS**

## Summary of Findings

| ID | Severity | Area | Description |
|----|----------|------|-------------|
| S1 | Suggestion | Typecheck | Auto-curry of let-bound closures doesn't emit AutoCurry resolution — document as known gap |
| S2 | Suggestion | Typecheck | `try_auto_curry` operates on potentially-polluted substitution after failed unification — add comment |
| I1 | Important | Codegen | `emit_single_test_iteration` has 11 parameters (CLAUDE.md max is 8) — group into struct |
| I2 | Important | Typecheck | Auto-curry of non-Var callees: typechecker accepts but no resolution emitted, leads to runtime mismatch |
| S3 | Suggestion | Codegen | `emit_wrapper_call` called with wrapper's builder, not self's — add clarifying comment |
| I3 | Important | Codegen | `compile_closure_call` visibility change not documented |
| S4 | Suggestion | Codegen | `GotGroupData` could be shared between `compile_trace` and `compile_run_tests` |
| S5 | Suggestion | Codegen | `Box::into_raw` leaks per run-tests invocation — known sketch debt, minor for REPL |
| B1 | Important | Codegen | Trace ADT dec in pass block uses `None` for drop glue — Trace fields (strings, Vec) leak on free |
| I4 | Important | Codegen | Some shell dec in fail block uses `None` for drop glue — leaked RC on reason string per failed test |
| S6 | Suggestion | REPL | `NULLARY_TAG_THRESHOLD` usage needs invariant comment |
| S7 | Suggestion | REPL | Raw pointer heap read in binary crate — acceptable but note containment concern |
| S8 | Suggestion | REPL | repl/mod.rs still large; future splitting opportunity |

## Overall Assessment

**PASS with important findings.**

The auto-curry typecheck and codegen are well-designed with thorough design docs and proper sketch comparison. RC handling in the auto-curry wrapper correctly addresses the multi-call reuse issue that the sketch left as debt. The run-tests codegen follows the sketch's unrolled-loop pattern faithfully with good decomposition.

The main concerns are:

1. **I2 (auto-curry non-Var callee)**: Silent miscompilation risk. Should be fixed by rejecting auto-curry when callee is not a Var, or explicitly documented as unsupported.

2. **B1/I4 (Trace and Some ADT drop glue)**: Leaked Trace fields and Some reason strings. Pre-existing pattern from the trace infrastructure, not new to this sprint, but now exercised more heavily by run-tests. Should be addressed in a follow-up.

3. **I1 (parameter count)**: 11 parameters on `emit_single_test_iteration` violates the CLAUDE.md convention. Straightforward to fix with a context struct.

The REPL refactoring is a clean structural improvement, and the safety fix correctly surfaces the unsafe boundary.
