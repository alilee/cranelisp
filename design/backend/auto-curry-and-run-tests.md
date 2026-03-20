# Auto-Curry Codegen (A2) and Run-Tests Codegen (R1)

Design notes for implementing auto-curry partial application and `run-tests` special form codegen in the reimplementation.

## A2: Auto-Curry Codegen

### Sketch Comparison

The sketch implements auto-curry in `sketch/src/codegen/closures.rs` (`compile_auto_curry`, lines 492-637). The typechecker resolves partial applications to `ResolvedCall::AutoCurry { target_name, applied_count, total_count }`, and codegen produces a closure that captures the applied arguments and forwards remaining arguments to the target function.

**Sketch approach:**

1. **Wrapper function**: Declares an anonymous function with signature `(env_ptr: i64, remaining_0: i64, ..., remaining_k: i64) -> i64` where `k = total_count - applied_count`.

2. **Wrapper body**: Loads the captured (applied) args from `env_ptr` at offsets `(i + 2) * 8` (sketch closure layout: `[code_ptr, drop_ptr, cap0, cap1, ...]`), then concatenates with the remaining args from block params to form the full argument list. Calls the target function (via direct call in batch mode, GOT-indirect in REPL mode).

3. **Closure allocation**: Allocates `[code_ptr, drop_ptr(null), applied_arg0, applied_arg1, ...]` and stores the wrapper code pointer and applied values.

4. **RC handling**: The sketch stores `null` for `drop_ptr` — no closure drop glue for auto-curry closures. The captured applied args are stored directly without RC inc. This is a **sketch debt**: if any applied args are heap-typed, the closure env holds a reference without its own RC increment, and no drop glue frees them.

**Key sketch detail — call dispatch within the wrapper**: The wrapper needs to call the target function, which may be in a different module. The sketch handles this by checking `self.builtin_methods` first (for operator builtins like `+`), then dispatching via `CallMode::Direct` (batch — `func_ids[target_name]`) or `CallMode::Indirect` (REPL — GOT lookup via `fn_slots[target_name]`).

### Reimplementation Approach

The reimplementation diverges from the sketch in two ways:

1. **Heap layout**: Closures have an RC header (16 bytes) before the payload. Layout is `[rc_header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]`. The `HeapClosure` type defines offsets: `CODE_PTR_OFFSET=16`, `DROP_GLUE_PTR_OFFSET=24`, `CAPTURES_START=32`, `capture_offset(i) = 32 + i * 8`.

2. **RC correctness**: Unlike the sketch, the reimplementation must emit proper RC inc for heap-typed applied args when storing them in the closure env, and must generate closure drop glue if any applied args are heap-typed. This is the same pattern used by `compile_lambda` for captured variables.

**What `compile_auto_curry` should do:**

```
compile_auto_curry(target_name, applied_vals, applied_count, total_count, span):
    remaining_count = total_count - applied_count

    // 1. Compile the wrapper function
    wrapper_sig = (env_ptr: i64, remaining_0..remaining_k: i64) -> i64
    declare wrapper as Local function

    wrapper body:
        entry_block:
            env_ptr = block_params[0]
            remaining_args = block_params[1..]

            // Load captured args from env_ptr
            for i in 0..applied_count:
                cap_i = heap_load(env_ptr, HeapClosure::capture_offset(i))

            all_args = [cap_0, ..., cap_n, remaining_0, ..., remaining_k]

            // Call the target function (reuse emit_wrapper_call)
            result = emit_wrapper_call(target_name, all_args, span)

            return result

    // 2. Allocate closure with captured applied args
    payload_size = HeapClosure::payload_size(applied_count)
    base_ptr = emit_alloc(payload_size)
    heap_store(wrapper_code_ptr, base_ptr, CODE_PTR_OFFSET)

    // 3. Build and store drop glue for heap-typed applied args
    drop_glue = build_auto_curry_drop_glue(applied_vals, span)
    heap_store(drop_glue_ptr_or_null, base_ptr, DROP_GLUE_PTR_OFFSET)

    // 4. Store applied args as captures, with RC inc for heap-typed values
    for (i, val) in applied_vals:
        heap_store(val, base_ptr, capture_offset(i))
        if val is heap-typed:
            emit_rc_inc(val)  // closure env needs its own reference

    return base_ptr
```

### RC Considerations

1. **Capture inc**: When storing applied args into the closure env, each heap-typed value needs `emit_rc_inc` (or `emit_rc_inc_guarded` for Mixed types). This mirrors `compile_lambda`'s capture handling.

2. **Drop glue**: If any applied args are heap-typed, generate a drop glue function `(ptr: i64) -> ()` that loads each heap-typed capture from its offset and calls `emit_rc_dec`. Use the same pattern as `build_closure_drop_glue` in `control_flow.rs`.

3. **Consuming convention within the wrapper**: The wrapper calls the target function, which uses consuming convention (callee dec's heap params). The loaded captures are unowned borrows from the env — the callee's dec will reduce the capture's RC. But the closure env also holds a reference (from the inc at capture time). When the closure itself is freed, drop glue dec's the captures. This double-accounting is correct: one inc at capture, one dec when the closure is freed, and the callee's consuming dec is balanced by the fact that loading from env doesn't create a new reference — it's already accounted for by the capture inc.

   **Wait — this needs care.** The wrapper loads captures from the env and passes them to the target function. The target function's consuming convention will dec them. But the closure env also holds references. So after the wrapper returns, the captures in the env are still alive (RC didn't go to 0 from the callee's dec, because the env holds a separate reference). When the closure is freed later, drop glue dec's the captures.

   The wrapper itself does NOT need to inc the loaded captures before passing them — the callee's dec reduces the capture-inc reference, and the closure's drop glue handles the env reference. This means the wrapper body is simple: load, concatenate, call, return. No RC ops needed inside the wrapper.

   **Exception**: If the wrapper is called multiple times (closure reused), the first call's callee dec would reduce the env's reference. The second call would then pass a value with RC potentially at 0. This is a **critical bug** if not handled.

   **Fix**: The wrapper MUST inc each heap-typed capture before passing it to the consuming callee. The callee dec's it (balanced). The env's reference (from capture-time inc) remains intact across calls. Drop glue eventually dec's the env reference. This is the same pattern as `compile_consuming_arg_list` — inc variable args before consuming calls.

### Implementation Steps

1. **Add `compile_auto_curry` method to `FnCompiler`** in `crates/cranelisp-backend/src/compiler/control_flow.rs` (or a new `curry.rs` module):

   - Accept `target_name: &Symbol`, `applied_vals: &[Value]`, `applied_count: usize`, `total_count: usize`, `span: Span`, and the `args: &[Expr]` (for type info).
   - Compile wrapper body using `emit_wrapper_call` (already exists — handles both Batch and Interactive dispatch).
   - Wrapper body must load captures, inc heap-typed captures, concatenate with remaining args, call target.
   - Allocate closure env, store code ptr, build/store drop glue, store captures with inc.

2. **Build drop glue for auto-curry closures**: Reuse the pattern from `build_closure_drop_glue`. The applied args' types come from `ctx.expr_types` on the corresponding arg expressions.

3. **Wire into `compile_resolved_call`** in `apply.rs`: Replace the stub error for `ResolvedCall::AutoCurry` with:
   ```rust
   ResolvedCall::AutoCurry { target_name, applied_count } => {
       let total_count = /* need this from typechecker */;
       let arg_vals = self.compile_arg_list(args)?;
       self.in_tail_position = saved_tail;
       self.compile_auto_curry(&target_name, &arg_vals, applied_count, total_count, args, span)
   }
   ```

4. **ResolvedCall shape**: The reimplementation's `ResolvedCall::AutoCurry` currently has `target_name: Symbol` and `applied_count: usize` but is **missing `total_count`**. The sketch has `total_count`. The typechecker must provide this. File a `FIXME(/typecheck)` if not already present. The total arity can alternatively be looked up via `ctx.func_arities[&target_name]` at codegen time, which avoids changing the type.

5. **Testing**: The auto-curry tests should exercise:
   - Partial application of user functions: `(map (+ 1) [1 2 3])` where `(+ 1)` is auto-curried.
   - Partial application of multi-arg functions: `(let [f (add 1)] (f 2))`.
   - Heap-typed captured args: `(let [s "hello"] (let [f (str-concat s)] (f " world")))`.
   - Closure reuse: `(let [f (+ 1)] (list (f 2) (f 3)))` — wrapper called twice.


## R1: Run-Tests Codegen

### Sketch Comparison

The sketch implements `compile_run_tests` in `sketch/src/codegen/trace.rs` (lines 452-694). It is a REPL-only form that discovers test functions, runs each with GOT-swap tracing, and folds results via user-supplied pass/fail closures.

**Sketch approach (per-test unrolled IR loop):**

1. **Batch fallback**: If `CallMode::Direct`, returns `init` unchanged (no GOT available).

2. **Collect traced functions**: Reuses `collect_traced_fns(modules)` from trace codegen — scans `tc.modules` for all user-defined functions with GOT slots and code pointers.

3. **Compile trace wrappers**: For every traced function (not just test functions), compiles a trace wrapper via `compile_trace_wrapper_fn` — same wrappers used by `(trace ...)`.

4. **Identify test functions**: Filters `all_wrappers` for zero-arg functions in modules with short name "test" whose names start with "test-".

5. **GOT group setup**: Groups all wrappers by GOT base address. Allocates persistent host-side arrays for slot indices and wrapper code pointers. Emits JIT-time `func_addr` stores to fill the wrapper buffer.

6. **Compile fold expressions**: Compiles `init`, `pass_fn`, `fail_fn` as expressions — they evaluate to closure values.

7. **Per-test unrolled loop** (one IR chunk per test function):
   - **Swap GOTs**: `cranelisp_trace_swap_got(got_base, n, slots_ptr, wrappers_ptr)` for each GOT group → returns saved state.
   - **Call test wrapper**: `call test_wrapper()` (zero args) → returns the test's result value (an `Option String` — `None` for pass, `Some(reason)` for fail).
   - **Restore GOTs**: `cranelisp_trace_restore_got(got_base, saved)` in reverse order.
   - **Collect trace**: `cranelisp_collect_trace()` → Trace ADT.
   - **Extract timing**: `cranelisp_trace_first_child_nanos(trace)` → nanos for this test.
   - **Allocate test name**: Uses `cranelisp_runtime::primitives::alloc_string()` — a *host-side Rust call at compile time* that returns a heap string pointer baked into IR as `iconst`.
   - **Branch on result**: `icmp_imm(raw_result, 0)` — None (tag 0, bare i64) vs Some (heap pointer).
     - **Pass block**: Inc test name string (for consuming closure call), dec the trace (pass_fn doesn't receive it), call `pass_fn(acc, test_name, nanos)` via `compile_closure_call` → new acc.
     - **Fail block**: Load reason string from `Some` at offset 8, inc test name, call `fail_fn(acc, test_name, nanos, reason, trace)` via `compile_closure_call` → new acc.
     - **Merge block**: Block param receives new acc from whichever branch executed.
   - `current_acc` = merge result, fed to next iteration.

8. **Cleanup**: Dec `pass_fn_val` and `fail_fn_val` closures after all tests.

**Key sketch detail — test name as static string**: The sketch calls `cranelisp_runtime::primitives::alloc_string()` at JIT-compile time (Rust function that allocates a heap string with RC=1), then embeds the resulting pointer as an `iconst`. The string lives for the program's lifetime. Before each closure call, it emits `emit_inc` on the string so the closure's consuming dec doesn't free it.

**Key sketch detail — test result discrimination**: Tests return `Option String` where `None` is bare i64 value 0 (nullary constructor tag) and `Some(reason)` is a heap pointer `[tag=1, str_ptr]`. The `icmp_imm(result, 0)` check distinguishes pass from fail.

### Reimplementation Approach

The reimplementation already has:
- Trace codegen (`trace_codegen.rs`) with `compile_trace`, `compile_trace_wrapper_fn`, GOT swap/restore
- `TracedFnInfo` struct and `CompileContext.traced_fns`
- `Expr::RunTests { modules, init, pass_fn, fail_fn, span }` in the AST
- A stub in `compile_expr` that returns an error for `Expr::RunTests`

The reimplementation diverges from the sketch:
1. **Heap layout**: RC header is 16 bytes (sketch has no header before tag). ADT layout: `[rc_header(16) | tag(8) | fields...]`. So `Some(reason)` is at `base_ptr`, with tag at offset 16 and the string field at offset 24 (field_offset(0) = 24). None is bare i64 tag value 0 (no heap allocation — nullary constructors are still bare i64).
2. **Traced function info**: The reimplementation gets `TracedFnInfo` from `CompileContext.traced_fns` rather than scanning modules directly during codegen. The integration layer populates this.
3. **No `cranelisp_runtime::primitives::alloc_string`**: The reimplementation's runtime is a separate crate. Need an equivalent mechanism for compile-time string allocation, or use `declare_trace_extern` to call a runtime function at JIT-runtime instead.

**Approach for `compile_run_tests`:**

Follow the sketch's unrolled-loop pattern closely. It is correct, efficient for the expected number of tests (tens to low hundreds), and avoids the complexity of a real loop construct in CLIF.

### Detailed Design

#### Test Discovery

The integration layer (src/) must filter `TracedFnInfo` entries to identify test functions:
- Module short name ends with ".test" or equals "test"
- Function name starts with "test-"
- Arity is 0

This filtering happens at codegen time within `compile_run_tests`, using `ctx.traced_fns`.

Alternatively, `CompileContext` could receive a separate `test_fns: Option<&[TestFnInfo]>` field to separate test discovery from trace function collection. However, since run-tests needs ALL functions traced (not just test functions), the sketch's approach of reusing the full traced functions list and filtering at codegen time is simpler.

#### Per-Test GOT-Swap: Reuse Trace Codegen's GOT Pattern

The GOT swap infrastructure is identical to `compile_trace`:
1. Group traced functions by GOT base.
2. Compile trace wrappers for ALL traced functions (not just test fns).
3. Allocate slots/wrappers arrays at compile time.
4. Emit `func_addr` stores at JIT runtime.
5. Call `cranelisp_trace_swap_got` / `cranelisp_trace_restore_got`.

This should be extracted into shared helper methods on `FnCompiler` rather than duplicated:
- `prepare_got_groups(&[TracedFnInfo]) -> Vec<GotGroupData>`
- `emit_got_swap(groups, swap_id) -> Vec<(i64, Value)>` — swap GOTs, return saved state
- `emit_got_restore(saved, restore_id)` — restore GOTs

#### Runtime Extern: `cranelisp_trace_first_child_nanos`

Already registered as an extern primitive in `apply.rs` (line 700). Needs to be declared in the runtime crate with signature `(trace_ptr: i64) -> i64`. Extracts the nanos field from the first child of the root Trace frame.

#### Test Name Strings

Two options:

**Option A (sketch approach)**: Call a Rust function at JIT-compile time to allocate a heap string, embed the pointer as `iconst`. Requires linking against the runtime's allocator at compile time.

**Option B (JIT-runtime approach)**: Declare `cranelisp_alloc_string_from_bytes(ptr: i64, len: i64) -> i64` as a runtime extern. At JIT-compile time, leak the test name bytes (`Box::into_raw`), embed the byte ptr and len as `iconst`, and call the runtime function during execution. The string is allocated at JIT-runtime with RC=1.

Option B is cleaner — it doesn't require compile-time access to the runtime's allocator. It also means the string is allocated fresh each time `run-tests` is evaluated (which is fine for REPL-only usage).

Alternatively, use `compile_string_lit` with a synthetic `Expr::StringLit` — but this stores bytes one-at-a-time via `istore8`, which is fine for short test names.

**Recommendation**: Use `compile_string_lit` pattern (emit the bytes inline as `istore8`s). This avoids any new runtime dependency. For a test name like "test-foo", this is ~8 istore8 instructions — negligible.

Actually, simpler: just allocate the string at Rust compile-time using `cranelisp_runtime::primitives::alloc_string` like the sketch does. The reimplementation has the `cranelisp-runtime` crate available. Add `cranelisp-runtime` as a dependency to `cranelisp-backend` (or pass a string-allocation function pointer through `CompileContext`).

**Simplest approach**: Leak a `Box<[u8]>` for name bytes and emit an inline string allocation sequence in the generated IR (same pattern as `compile_string_lit`). The string will be allocated each time the test runs, with RC=1. Inc before each closure call so the consuming closure doesn't free it. This is self-contained — no new runtime dependency needed.

#### Fold Pattern

```
current_acc = compile_expr(init)
pass_fn_val = compile_expr(pass_fn)
fail_fn_val = compile_expr(fail_fn)

for each test_fn in test_fns:
    // Swap all GOTs
    saved_vals = emit_got_swap(got_groups, swap_id)

    // Call test wrapper (zero args, direct call via FuncId)
    raw_result = call test_wrapper_id()

    // Restore all GOTs
    emit_got_restore(saved_vals, restore_id)

    // Collect trace
    trace_adt = call cranelisp_collect_trace()

    // Extract timing
    nanos = call cranelisp_trace_first_child_nanos(trace_adt)

    // Allocate test name string (inline, like string_lit)
    tname_val = emit_string_allocation(test_name_bytes)

    // Branch: None (pass) vs Some(reason) (fail)
    //   None = bare i64 tag 0
    //   Some = heap pointer, tag at HeapAdt::TAG_OFFSET(16)=1, field at field_offset(0)=24
    is_none = icmp_imm(raw_result, 0)
    brif(is_none, pass_block, fail_block)

    pass_block:
        emit_rc_inc(tname_val)  // protect from consuming closure dec
        emit_rc_dec(trace_adt)  // pass_fn doesn't receive trace
        pass_acc = compile_closure_call(pass_fn_val, [current_acc, tname_val, nanos])
        jump merge_block(pass_acc)

    fail_block:
        reason_str = heap_load(raw_result, HeapAdt::field_offset(0))  // offset 24
        emit_rc_inc(reason_str)  // extract from Some, inc for consuming call
        emit_rc_inc(tname_val)  // protect from consuming closure dec
        // Note: trace_adt ownership transfers to fail_fn (no dec here)
        fail_acc = compile_closure_call(fail_fn_val, [current_acc, tname_val, nanos, reason_str, trace_adt])
        // Dec the Some shell (controlled leak in sketch; we should dec it)
        emit_rc_dec(raw_result)  // free Some node, but reason_str was inc'd
        jump merge_block(fail_acc)

    merge_block:
        current_acc = block_param[0]

// Cleanup: dec pass_fn and fail_fn closures
emit_closure_dec(pass_fn_val)
emit_closure_dec(fail_fn_val)

// Dec the test name string (it was inc'd N times for N test executions,
// and N consuming closure calls dec'd it N times, leaving RC=1 from
// original allocation — need one final dec to free it)
// Actually: each test iteration allocates a FRESH string (via the
// inline string lit pattern). So each string has RC=1, gets inc'd once
// before the closure call, closure dec's it back to 1, and then...
// nobody dec's it. This is a minor leak per test name.
//
// Better approach: allocate the string ONCE before the loop (like the
// sketch does with alloc_string at compile time). Inc before each
// closure call (bump to 2), closure dec brings back to 1 for the next
// iteration. After all tests, emit one final dec to free it.
//
// Since we compile string_lit inline, just do it once and store the ptr.
// This means using compile_string_lit to create one Value, then reusing
// that Value across all iterations. The string lives on the heap with
// RC=1. Each iteration: inc -> closure dec -> RC=1 again. Final dec: free.

return current_acc
```

**Refined test name approach**: Allocate each test name string ONCE (before the per-test loop), reuse across iterations. The string starts at RC=1. Before each pass/fail closure call, `emit_rc_inc` bumps to RC=2. The consuming closure dec brings back to RC=1. After all tests, emit a final `emit_rc_dec` to free the string. For N test functions, we allocate N strings total, each freed after the loop.

Wait — each test has a DIFFERENT name. So we need N different string values. Allocate all N before the loop, then in the per-test unrolled code, use the corresponding string value. After the loop, dec all N strings.

Since the loop is unrolled (one IR chunk per test), this is naturally handled: each iteration uses its own string value, inc'd and dec'd.

#### Some/None Discrimination in the Reimplementation

The reimplementation uses RC headers. Key difference from sketch:

- `None` (nullary constructor): bare i64 tag value 0. No heap allocation. `icmp_imm(raw_result, 0)` works.
- `Some(reason)`: heap allocation `[rc_header(16) | tag(8) | field_0(8)]`. The base_ptr is returned. Tag value 1 is at offset 16 (`HeapAdt::TAG_OFFSET`). The reason string is at offset 24 (`HeapAdt::field_offset(0)`).

So the discrimination is: `raw_result == 0` means None (pass), `raw_result != 0` means Some (fail). This is the same as the sketch.

To extract the reason from `Some(reason)`: `heap_load(raw_result, HeapAdt::field_offset(0))` = offset 24.

### Key Functions Needed

1. **`compile_run_tests`** — main method on `FnCompiler` in `trace_codegen.rs`
2. **GOT swap helpers** — factor out from `compile_trace` for reuse:
   - `group_traced_fns_by_got` — group `TracedFnInfo` by GOT base
   - `prepare_got_swap` — allocate arrays, emit func_addr stores, return per-group data
   - `emit_swap_and_restore` — swap/restore convenience
3. **`cranelisp_trace_first_child_nanos`** — already in extern list; needs runtime implementation if not present
4. **String allocation helper** — reuse the inline string-lit pattern from `compile_string_lit` for test names

### Implementation Steps

1. **Refactor GOT swap logic** from `compile_trace` into shared helpers:
   - Extract `GotGroupData` struct (or equivalent).
   - `prepare_got_groups(&self, traced: &[TracedFnInfo], span: Span) -> Result<(Vec<GotGroupData>, Vec<FuncId>), CranelispError>` — compiles wrappers, allocates arrays, emits func_addr stores.
   - `emit_got_swaps(&mut self, groups: &[GotGroupData], swap_id: FuncId) -> Vec<(i64, Value)>`.
   - `emit_got_restores(&mut self, saved: &[(i64, Value)], restore_id: FuncId)`.

2. **Add `compile_run_tests` to `trace_codegen.rs`**:
   ```rust
   pub(crate) fn compile_run_tests(
       &mut self,
       modules: &[Symbol],
       init: &Expr,
       pass_fn: &Expr,
       fail_fn: &Expr,
       span: Span,
   ) -> Result<Value, CranelispError> { ... }
   ```

3. **Wire into `compile_expr`** in `mod.rs`: Replace the stub error:
   ```rust
   Expr::RunTests { modules, init, pass_fn, fail_fn, span } => {
       self.compile_run_tests(modules, init, pass_fn, fail_fn, *span)
   }
   ```

4. **Test filtering**: Within `compile_run_tests`, filter `ctx.traced_fns` for test functions:
   ```rust
   let test_fns: Vec<(&TracedFnInfo, FuncId)> = all_wrappers
       .iter()
       .filter(|(tf, _)| tf.name.starts_with("test-") && tf.arity == 0)
       .collect();
   ```
   Note: the module name filtering (`.test` modules) should be handled by the integration layer when populating `traced_fns`, or by checking the `TracedFnInfo` for a module indicator. The `TracedFnInfo` struct currently has `name` and `got_base` but no module name. **Add `module_short: String` to `TracedFnInfo`** so codegen can filter by module.

5. **RC for the fold pattern**:
   - `init`: evaluated once, ownership transfers to fold.
   - `pass_fn` / `fail_fn`: evaluated once, live for the duration of run-tests, dec'd at the end.
   - `tname_val`: allocated once per test name, inc'd before each closure call, dec'd after the loop.
   - `trace_adt`: dec'd in pass block, ownership transferred in fail block.
   - `reason_str`: extracted from Some, inc'd for consuming call. The Some shell should be dec'd in the fail block after extracting reason (so fields don't leak).
   - `raw_result` in pass block: it's 0 (None), no heap — no dec needed.

6. **Batch mode fallback**: Return `compile_expr(init)` unchanged (same as sketch).

### Open Questions

1. **`TracedFnInfo.module_short`**: Currently missing. The integration layer needs to populate it, and the struct definition in `mod.rs` needs updating. This is a minor addition.

2. **Total count for auto-curry**: The `ResolvedCall::AutoCurry` in the reimplementation lacks `total_count`. Either add it to the enum variant, or look up `ctx.func_arities[&target_name]` at codegen time. The latter is simpler and avoids a cross-skill change.

3. **String allocation for test names**: The inline `istore8` pattern from `compile_string_lit` requires `alloc_func_id`. This is available in Ring 1+. For very long test names, this generates many instructions, but test names are short in practice.
