# Codegen Module Audit

**Module**: `src/codegen/` (8 files, 6,192 lines) + supporting `src/liveness.rs` (322 lines) + `src/captures.rs` (235 lines)
**Date**: 2026-03-03
**Scope**: Simplicity, maintainability, complexity, duplication, data modeling, test coverage

## Module Overview

The codegen module translates typed AST (`Defn`, `Expr`) into Cranelift IR and ultimately into JIT-compiled machine code. It operates in two modes: *Direct* (batch, `compile_function`) with statically-known `FuncId`s, and *Indirect* (REPL/module, `compile_function_indirect`) with GOT-based indirect calls via `FnSlot`. The central struct is `FnCompiler<'a, M: Module>`, which carries the `FunctionBuilder`, RC tracking state, TCO state, and all codegen context.

Key subsystems:
- **Expression compilation** (`expr.rs`): literals, `let`, `if`, lenient eval, `par-let`, `par-bind!`
- **Function application** (`apply.rs`): direct/indirect/closure calls, TCO self-calls, accessor calls
- **Closure codegen** (`closures.rs`): lambda, constructor-as-closure, accessor-as-closure, auto-curry, builtin-as-closure
- **Match compilation** (`match_compile.rs`): test-and-branch chain for ADT patterns
- **Primitive IR** (`primitives.rs`): checked/unchecked arithmetic, float ops, `bind`
- **Trace codegen** (`trace.rs`): GOT-swap tracing wrappers, `run-tests` test runner
- **Vec operations** (`vec_ops.rs`): COW vec-get/vec-set/vec-push with RC and inline IR
- **Drop/RC infrastructure** (`codegen.rs`): `emit_inc`, `emit_dec`, `pop_scope_for_value`, drop function generation, `FnCompiler` construction

### File Metrics

| File | Lines | Responsibility | Tests |
|---|---|---|---|
| `src/codegen.rs` | 1,964 | `FnCompiler` struct, RC emit, drop fn generation, `compile_function`/`compile_body` | 0 |
| `src/codegen/expr.rs` | 859 | `compile_expr`, `compile_let_*`, `compile_par_let`, `compile_par_bind` | 0 |
| `src/codegen/closures.rs` | 849 | Lambda, constructor/accessor/builtin/func-as-closure, auto-curry | 0 |
| `src/codegen/trace.rs` | 694 | GOT-swap trace, `compile_trace`, `compile_run_tests` | 0 |
| `src/codegen/vec_ops.rs` | 773 | COW vec-get/vec-set/vec-push inline IR, elem inc fn | 0 |
| `src/codegen/apply.rs` | 456 | `compile_apply`, TCO self-call, direct/closure call | 0 |
| `src/codegen/match_compile.rs` | 288 | `compile_match` test-and-branch chain | 0 |
| `src/codegen/primitives.rs` | 309 | Inline primitive IR, checked arithmetic | 0 |
| `src/liveness.rs` | 322 | Last-use analysis for RC ownership decisions | 8 |
| `src/captures.rs` | 235 | Free variable analysis for closure capture lists | 13 |

**Total tests in codegen**: 0 (all tests are in `liveness.rs` and `captures.rs`, which are supporting analysis modules)

---

## Findings

### HIGH-1: `FnCompiler` struct initialization duplicated verbatim three times

**File**: `src/codegen.rs:1897-1933`, `src/codegen/closures.rs:111-147`, `src/codegen/expr.rs:523-559`
**Severity**: High (duplication)

`FnCompiler` has 28 fields. Constructing an inner `FnCompiler` for a lambda body, a `par-bind!` continuation, and the top-level `compile_body` all initialize the struct from scratch with essentially identical field lists. The lambda and continuation initializations are byte-for-byte identical except for the `builder` field name.

```rust
// closures.rs:111-147 — lambda inner compiler
let mut inner = FnCompiler {
    builder: lambda_builder,
    module: self.module,
    variables: HashMap::new(),
    call_mode: inner_call_mode,
    alloc_func_id: self.alloc_func_id,
    globals: self.globals.clone(),
    liveness_globals: self.liveness_globals.clone(),
    // ... 20 more fields identically copied from self ...
    last_uses: crate::liveness::compute_last_uses(body, &self.liveness_globals),
    consumed_vars: std::collections::HashSet::new(),
    in_trace_body: self.in_trace_body,
};

// expr.rs:523-559 — par-bind continuation — identical except builder name
let mut inner = super::FnCompiler {
    builder: cont_builder,
    // ... all 27 other fields identical ...
};
```

Every time a field is added to `FnCompiler` (which has grown from the original design), all three construction sites must be updated. Omitting a field from one site silently compiles with the default or causes a type error only when the missing field has no `Default`.

**Impact**: Any new field added to `FnCompiler` requires editing three separate struct literals. Missing a field causes subtle bugs (e.g., forgetting to propagate `in_trace_body` would silently enable lenient eval inside traces). The `drop_fn_cache` and `vec_elem_inc_cache` start empty in lambdas, forcing redundant re-generation of the same drop functions inside nested lambdas.

**Recommendation**: Add a `fn inner_compiler(&mut self, builder: FunctionBuilder<'a>, body: &Expr) -> FnCompiler<'a, M>` method on `FnCompiler` that creates the inner struct with all shared-reference fields propagated from `self` and fresh mutable state initialized. The single call replaces all three struct literals.

---

### HIGH-2: `heap_category` and `classify_heap_type` are identical logic duplicated as method and free function

**File**: `src/codegen.rs:734-759` (method), `src/codegen.rs:1057-1085` (free function)
**Severity**: High (duplication)

The method `FnCompiler::heap_category` and the free function `classify_heap_type` implement exactly the same match on `ty` with exactly the same arms and return values. The only difference is that the method reads `self.type_defs` while the free function takes `type_defs` as a parameter.

```rust
// codegen.rs:734 — instance method
fn heap_category(&self, ty: &Type) -> HeapCategory {
    match ty {
        Type::String | Type::Fn(_, _) => HeapCategory::AlwaysHeap,
        Type::ADT(name, _) if name == "Vec" => HeapCategory::AlwaysHeap,
        // ... 20 more lines ...
    }
}

// codegen.rs:1057 — free function, same logic
fn classify_heap_type(ty: &Type, type_defs: Option<&HashMap<String, TypeDefInfoCg>>) -> HeapCategory {
    match ty {
        Type::String | Type::Fn(_, _) => HeapCategory::AlwaysHeap,
        Type::ADT(name, _) if name == "Vec" => HeapCategory::AlwaysHeap,
        // ... 20 identical lines ...
    }
}
```

The method exists because `FnCompiler` methods need to call it on `self.type_defs`, but free functions (`emit_dec_in_drop_fn`, `resolve_drop_fn`, `emit_scope_cleanup_for_tco`) cannot call it through `self`. The free function was extracted to serve that need.

**Impact**: Any future change to heap category logic (e.g., adding a new always-heap type, changing the nullary threshold) must be made in two places. The `Mixed` conservative fallback for unknown ADTs is duplicated, including a comment difference ("// conservative" appears in one but not the other on the unknown ADT path).

**Recommendation**: Delete the `heap_category` method and replace all call sites with `classify_heap_type(ty, self.type_defs)`. The method adds no value once the free function exists.

---

### HIGH-3: `compile_vec_set_inline` and `compile_vec_push_inline` are each ~230 lines with tripled code paths

**File**: `src/codegen/vec_ops.rs:191-422` (`vec-set`), `src/codegen/vec_ops.rs:426-677` (`vec-push`)
**Severity**: High (complexity, duplication)

Each of these functions contains three top-level branches: *static COW* (known-unique, last-use), *dynamic COW* (last-use, runtime rc check), and *always-copy*. The dynamic COW branch itself contains nested in-place vs grow sub-branches. The bounds-check IR sequence (load len, create panic\_block, create do\_block, icmp, brif, panic message, trap, switch/seal both blocks, load data\_ptr, imul, iadd) is emitted three times inside `compile_vec_set_inline` and four times across both functions.

```rust
// vec_ops.rs:229-257 — bounds check in static-COW path of vec-set
let len = self.builder.ins().load(types::I64, MemFlags::trusted(), vec_val, 0);
let panic_block = self.builder.create_block();
let do_block = self.builder.create_block();
let zero = self.builder.ins().iconst(types::I64, 0);
let neg = self.builder.ins().icmp(IntCC::SignedLessThan, idx_val, zero);
let oob = self.builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, idx_val, len);
let bad = self.builder.ins().bor(neg, oob);
self.builder.ins().brif(bad, panic_block, &[], do_block, &[]);
// ... switch, seal, panic message, trap ...

// vec_ops.rs:316-342 — identical sequence inside dynamic-COW path
```

**Impact**: ~100 lines of identical Cranelift IR emission exist in two places just within `vec-set`. Bugs in bounds-check logic (e.g., wrong IntCC, wrong offset arithmetic) must be fixed in every copy. Adding a new vec operation (e.g., `vec-splice`) means copying ~200 lines again.

**Recommendation**: Extract `emit_vec_bounds_check(&mut self, vec_val: Value, idx_val: Value, msg: &str, span: Span) -> Result<(Value, Value), CranelispError>` that emits the bounds check and returns `(data_ptr, elem_addr)`. Extract `emit_vec_mutate_inplace` for the load/dec-old/store sequence. The three code paths (static COW, dynamic COW, copy) reduce to a helper that selects the path and delegates mutation to the extracted primitive.

---

### HIGH-4: `compile_run_tests` is 233 lines with an inline struct definition and unrolled IR loop

**File**: `src/codegen/trace.rs:461-693`
**Severity**: High (complexity)

`compile_run_tests` is the longest function in the module at 233 lines. It defines a local struct `GotGroupData` at line 525, builds wrapper IR for all test functions, then emits an *unrolled* loop: for each test function, the GOT-swap, call, restore, collect, and pass/fail branch are emitted as inline IR. The GOT grouping logic (linear scan over `got_groups` with `iter_mut().find(|(b, _)| *b == ...)`) is copy-pasted from `compile_trace` (trace.rs:68).

```rust
// trace.rs:525 — local struct inside a function body
struct GotGroupData {
    got_base: i64,
    n: usize,
    slots_ptr: i64,
    wrappers_buf_ptr: i64,
}

// trace.rs:577-682 — unrolled per-test IR emission (no runtime loop)
for (test_name, test_wrapper_id) in &test_fns {
    // a. Swap all GOTs
    let mut saved_vals: Vec<(i64, Value)> = Vec::new();
    for gg in &got_group_data {
        let swap_ref = self.module.declare_func_in_func(swap_id, self.builder.func);
        // ...emit swap call...
    }
    // b. Call wrapper, c. Restore, d. Collect, e. Timing, f. Branch...
}
```

The unrolled design is intentional (each test gets its own IR), but the per-test GOT swap/restore boilerplate (steps a and c) is duplicated from `compile_trace` (lines 86-153). If the swap/restore protocol changes, both functions need updating.

**Impact**: The local struct is visible only to this function but is a sign that the function has outgrown its scope. The linear GOT grouping scan is O(n²) in the number of modules with traced functions, though this is unlikely to matter in practice. The swap/restore logic must be kept in sync with `compile_trace`.

**Recommendation**: Move `GotGroupData` to module scope. Extract `emit_got_swap_group(got_group_data: &[GotGroupData]) -> Vec<(i64, Value)>` and `emit_got_restore(swap_results: &[(i64, Value)])` shared by both `compile_trace` and `compile_run_tests`. Extract the per-test IR emission into `emit_single_test_run(test_name, wrapper_id, ...)`.

---

### HIGH-5: `compile_par_bind_continuation` is 200 lines constructing a nested `FnCompiler` manually

**File**: `src/codegen/expr.rs:464-663`
**Severity**: High (complexity)

`compile_par_bind_continuation` builds a new Cranelift `Function`, manually creates a `FnCompiler`, loads captures from env, binds par result values, compiles the body, and defines the function. This is a 200-line inline closure compiler that duplicates the pattern of `compile_lambda` (closures.rs:15-268) step for step, including the `CallMode` clone dance, the sorted capture extraction, the `FnCompiler` struct literal (HIGH-1), and the closure allocation at the end. The key difference is that the continuation signature is `(env_ptr, results_ptr) -> i64` instead of the standard `(env_ptr, params...) -> i64`.

**Impact**: Any bug fix to the lambda compilation path (capture loading offsets, RC tracking, `inner_call_mode` propagation) must also be applied to this 200-line duplicate. The two functions are almost impossible to diff visually because of the different variable names for the builder.

**Recommendation**: Refactor `compile_lambda` to accept an optional custom entry-block setup callback, or extract the common infrastructure (function declaration, builder setup, `FnCompiler` construction, definition, closure allocation) into a `compile_anonymous_fn` helper. `compile_par_bind_continuation` would then only need to provide its custom signature and the body-compilation hook.

---

### MED-1: 29 `.expect()` and `.unwrap()` calls in production codegen paths

**File**: Multiple files, see list
**Severity**: Medium (robustness)

There are 29 total `.expect()`/`.unwrap()` calls across the codegen module (excluding test code). The most impactful ones are in non-obvious positions:

```rust
// codegen.rs:277 — in emit_rc_underflow_check, called on every dec
.expect("failed to declare cranelisp_rc_underflow_check");

// codegen.rs:382, 407, 435 — in emit_dec_guarded, called on every extern call cleanup
.expect("cranelisp_dec_closure_guarded not registered");
.expect("cranelisp_dec_guarded not registered");
.expect("cranelisp_dec_mixed_guarded not registered");

// codegen.rs:684 — in emit_scope_cleanup_for_tco
self.builder.current_block().unwrap();

// codegen.rs:1437-1448 — triple unwrap on Option<Block> fields
loop_setup.unwrap(); loop_header.unwrap(); loop_body.unwrap();

// apply.rs:366 — in compile_tail_self_call
let loop_block = self.tail_loop_block.unwrap();

// vec_ops.rs:383, 412, 518, 617, 639, 668 — builtin lookup panics
.expect("vec-set-rc not registered");
.expect("vec-push-cow-grow not registered");
.expect("vec-push-rc not registered");

// codegen.rs:1138, 1278, 1299, 1346, 1380, 1521 — drop/inc fn declaration panics
.expect("failed to declare drop function");
.expect("failed to define drop function");
```

The `tail_loop_block.unwrap()` at `apply.rs:366` is invoked only when `self.in_tail_position && self.tail_loop_block.is_some()` was verified at line 26, so logically it cannot panic — but the invariant is not captured in the type. The `current_block().unwrap()` at `codegen.rs:684` assumes the builder always has a current block during TCO cleanup, which is true by construction but not checked.

The `builtin_methods.get(name).expect(...)` calls at `vec_ops.rs:383`, etc. will panic if the JIT startup sequence omits registering a builtin. This is a setup-time invariant that only manifests at the first vec operation use, making it hard to diagnose.

**Impact**: Any panic in production generates an unrecoverable crash instead of a `CranelispError` with a span and message. Panics in `emit_dec_guarded` are particularly bad because they occur during common scope cleanup.

**Recommendation**: For the `tail_loop_block.unwrap()` and `current_block().unwrap()` cases, use `debug_assert!` plus a safe fallback or change the call site to return a `Result`. For builtin lookups (`vec-set-rc`, etc.), validate all builtins are registered during JIT initialization and return a `CranelispError` with a diagnostic message if one is missing at call time. For the drop-function declaration `.expect()` calls, propagate errors via `Result<FuncId, CranelispError>`.

---

### MED-2: `compile_apply` is 310 lines with six sequential dispatch phases

**File**: `src/codegen/apply.rs:13-322`
**Severity**: Medium (complexity)

`compile_apply` dispatches through six sequential phases: (1) TCO self-call check, (2) data constructor call, (3) field accessor call, (4) resolved call (trait method / sig dispatch / auto-curry / builtin fn), (5) known top-level function, (6) general closure call. Each phase has its own nested `if let` to check whether the callee is a `Var`. The accessor call path alone is 100 lines (lines 99-205) and duplicates the panic/merge block pattern from `compile_match`.

```rust
// apply.rs:47-96 — constructor dispatch
if let Expr::Var { name, .. } = callee {
    if let Some(ctor_info) = self.data_constructor_info(name) { /* 50 lines */ }
}
// apply.rs:102-205 — accessor dispatch
if let Expr::Var { name, .. } = callee {
    if !self.variables.contains_key(name) {
        if let Some(acc) = self.accessor_info(name) { /* 100 lines */ }
    }
}
// apply.rs:207-288 — resolved call dispatch
if let Some(resolved) = resolved { match resolved { /* 4 arms, 80 lines */ } }
// apply.rs:291-315 — known function dispatch
if let Expr::Var { name, .. } = callee { /* 25 lines */ }
// apply.rs:317-321 — general closure fallback
```

**Impact**: Adding a new call category requires inserting a new `if let` block in the correct position in the chain. The function is difficult to reason about because control flow can return from any of the six phases. The accessor inline path (sum-type accessor with tag check, panic block, merge block) at lines 136-201 is essentially `compile_match` with one arm and a panic, adding IR block count for every accessor call on a sum type.

**Recommendation**: Extract the data constructor path into `compile_constructor_call` and the accessor path into `compile_accessor_call_inline`. This reduces `compile_apply` to a clean dispatch table pattern under ~100 lines.

---

### MED-3: Leaked `Box` raw pointers in trace.rs with no cleanup

**File**: `src/codegen/trace.rs:95-99, 343-350, 539-542`
**Severity**: Medium (robustness)

`compile_trace_wrapper_fn` and `compile_run_tests` call `Box::into_raw` on allocations that must persist for the program lifetime: function name bytes, `Box<Type>` values for trace format, and GOT slot/wrapper arrays. These leaks are necessary because the JIT embeds the raw pointers as `iconst` values in the generated code.

```rust
// trace.rs:341-350
let name_bytes: Box<[u8]> = tf.name.as_bytes().to_vec().into_boxed_slice();
let name_ptr = Box::into_raw(name_bytes) as *mut u8 as i64;

let param_type_ptrs: Vec<i64> = tf.param_types.iter()
    .map(|ty| Box::into_raw(Box::new(ty.clone())) as i64)
    .collect();
let result_type_ptr = Box::into_raw(Box::new(tf.result_type.clone())) as i64;
```

There is no registry of these leaks, no cleanup on REPL session end, and no documentation of the total memory consumed. Each `(trace ...)` call at the REPL leaks one `Box<[u8]>` per traced function plus one `Box<Type>` per parameter plus one per result. In a long-running REPL session with many trace invocations over growing programs, this accumulates.

**Impact**: Memory leak in REPL sessions. No mechanism to reclaim trace wrapper overhead when functions are redefined. The leaks are not visible via CRANELISP_RC_TRACE because they bypass the RC allocator.

**Recommendation**: Introduce a `TraceLeakRegistry` stored on the REPL session that collects raw pointers from each trace compilation. On session teardown or REPL `/reload`, reconstruct the boxes and drop them. Alternatively, use static interning: intern function names and types in a global arena that is cheap to allocate and never needs to be freed.

---

### MED-4: `pop_scope_for_value` generates O(n) Cranelift blocks per scope, one per binding

**File**: `src/codegen.rs:576-655`
**Severity**: Medium (performance)

`pop_scope_for_value` iterates over each binding in the scope frame and emits 2 blocks per binding for the "is this the return value?" guard (upgrade for borrowed vars) and 2 blocks per binding for the dec guard. With `n` heap-typed bindings in scope, this emits up to `4n` basic blocks before the function actually returns. For the common case of a function with several string or closure parameters, this expands the IR significantly.

```rust
// codegen.rs:614-626 — 2 blocks emitted per borrowed var in scope
let is_result = self.builder.ins().icmp(IntCC::Equal, val, result_val);
let upgrade_block = self.builder.create_block();
let skip_block = self.builder.create_block();
self.builder.ins().brif(is_result, upgrade_block, &[], skip_block, &[]);
// ...
self.builder.switch_to_block(skip_block);

// codegen.rs:641-653 — 2 more blocks per non-consumed, non-borrowed binding
let is_result = self.builder.ins().icmp(IntCC::Equal, val, result_val);
let dec_block = self.builder.create_block();
let skip_block = self.builder.create_block();
self.builder.ins().brif(is_result, skip_block, &[], dec_block, &[]);
```

Cranelift's optimizer eliminates trivially dead blocks, but the number of IR nodes created at codegen time still scales linearly with scope size. For a function with 5 heap-typed parameters all eligible for scope cleanup, this emits up to 20 blocks just for the return sequence.

**Impact**: Larger IR graphs slow down Cranelift's optimization passes and increase JIT compilation time. The pattern is especially pronounced for closures with many captures (each capture generates scope cleanup blocks).

**Recommendation**: For the common case where `result_val` is not a heap-typed SSA value from any binding in scope (i.e., the result type is NeverHeap or is a fresh allocation), skip the guard entirely. Track in the scope pop whether any binding is a candidate for the result identity check and only generate the guard blocks if there is an actual ambiguity.

---

### MED-5: `emit_dec_inline` and `emit_closure_dec_inline` share identical RC-atomic-dec preamble

**File**: `src/codegen.rs:860-916` (`emit_dec_inline`), `src/codegen.rs:922-995` (`emit_closure_dec_inline`)
**Severity**: Medium (duplication)

Both functions begin with the same sequence: null/low-value guard (check val < 1024, branch to cont\_block if low), atomic subtract from `val-8`, optional underflow check, compare old\_rc to 1, branch to free\_block or cont\_block. The only difference is what happens in free\_block: `emit_dec_inline` calls a type-specific drop function or `cranelisp_free`, while `emit_closure_dec_inline` loads the runtime `drop_ptr` from `closure[8]` and dispatch-branches on null.

```rust
// codegen.rs:860-895 — emit_dec_inline preamble (36 lines)
let dec_block = self.builder.create_block();
let cont_block = self.builder.create_block();
let threshold = self.builder.ins().iconst(types::I64, 1024);
let is_low = self.builder.ins().icmp(IntCC::UnsignedLessThan, val, threshold);
self.builder.ins().brif(is_low, cont_block, &[], dec_block, &[]);
// ... switch/seal dec_block, atomic sub, underflow check, icmp old_rc to 1 ...

// codegen.rs:922-956 — emit_closure_dec_inline preamble (35 lines, identical)
let dec_block = self.builder.create_block();
let cont_block = self.builder.create_block();
// ... identical sequence ...
```

**Impact**: Bug fixes to the atomic dec preamble (e.g., the underflow check call or the threshold constant) must be applied in both functions.

**Recommendation**: Extract `emit_dec_preamble(&mut self, val: Value) -> Option<(Block, Block, Value)>` that emits the guard, atomic sub, and underflow check, and returns `(free_block, cont_block, old_rc)` or `None` if already positioned past the guard. Both `emit_dec_inline` and `emit_closure_dec_inline` call this then add their type-specific free block logic.

---

### MED-6: `accessor_info` is an O(n×m) linear scan over all type definitions

**File**: `src/codegen.rs:473-492`
**Severity**: Medium (performance)

`accessor_info` searches all type definitions and all constructors and all fields to find a field named `bare`. It also recomputes `non_internal_count` (a second full scan of constructors) on every match. This is called on every `Expr::Var` resolution in `compile_expr` and every callee check in `compile_apply`.

```rust
pub(crate) fn accessor_info(&self, name: &str) -> Option<AccessorInfoCg> {
    let bare = resolve_bare_name(name);
    let tds = self.type_defs.as_ref()?;
    for td in tds.values() {
        for ctor in td.constructors.iter().filter(|c| !c.internal) {
            for (fi, fname) in ctor.fields.iter().enumerate() {
                if fname == bare {
                    let non_internal_count = td.constructors.iter()
                        .filter(|c| !c.internal).count(); // re-scan
                    // ...
                }
            }
        }
    }
    None
}
```

**Impact**: For a program with many ADT types, every Var-expression compilation performs a full scan of all field names. In practice the number of types is small (tens), so this is not yet measurable, but it is a latent scalability issue. The double-scan to count non-internal constructors is wasted work on every successful match.

**Recommendation**: Pre-build an `accessor_map: HashMap<String, AccessorInfoCg>` at `FnCompiler` construction time (or in `build_type_defs_cg`), keyed by field name. `accessor_info` becomes a single hash lookup.

---

### MED-7: String literal IR emission copies bytes one `istore8` at a time inside `emit_panic_with_message` and `compile_accessor_as_closure`

**File**: `src/codegen.rs:529-550` (`emit_panic_with_message`), `src/codegen/closures.rs:447-453` (`compile_accessor_as_closure`)
**Severity**: Medium (duplication)

Both functions build a cranelisp heap string (`[len: i64][bytes...]`) via inline IR, looping over each byte and emitting an `istore8` per byte. The loop pattern in `compile_accessor_as_closure` is a direct copy of `emit_panic_with_message`:

```rust
// codegen.rs:529-550 — emit_panic_with_message
let msg_bytes = msg.as_bytes();
let size = (8 + msg_bytes.len()) as i64;
let ptr = self.compile_alloc(size, span)?;
let len_val = self.builder.ins().iconst(types::I64, msg_bytes.len() as i64);
self.builder.ins().store(MemFlags::trusted(), len_val, ptr, 0);
for (bi, &byte) in msg_bytes.iter().enumerate() {
    let byte_val = self.builder.ins().iconst(types::I64, byte as i64);
    self.builder.ins().istore8(MemFlags::trusted(), byte_val, ptr, (8 + bi) as i32);
}

// closures.rs:436-453 — compile_accessor_as_closure panic string, same pattern
// but using bare `builder` (not self.builder) with self.alloc_func_id
```

The `compile_accessor_as_closure` version cannot call `self.emit_panic_with_message` because it uses a separate bare `FunctionBuilder` for the anonymous wrapper function.

**Impact**: Both emit quadratically large IR for long panic messages (N instructions for N bytes). For a 40-character panic message, this is 40 `istore8` instructions emitted as individual IR nodes. The per-byte loop also prevents future use of `data_flow_graph.write_many_bytes`.

**Recommendation**: For panic messages that are compile-time constants, allocate them at program startup (host-side, via `cranelisp_runtime::primitives::alloc_string`) and embed the pointer as an `iconst`, the same pattern used in `compile_run_tests:631`. This eliminates all per-byte `istore8` instructions and allows the panic string allocation to be shared across all call sites.

---

### LOW-1: Magic number `1024` used as nullary/heap pointer threshold without a named constant

**File**: `src/codegen.rs:774, 840, 864, 926, 1545`; `src/codegen/vec_ops.rs:729, 733`; `src/codegen/match_compile.rs:181`
**Severity**: Low (code clarity)

The value `1024` appears 8 times across the module as the discriminant threshold distinguishing nullary ADT tags from heap pointers. There is no named constant for it.

```rust
// codegen.rs:774
let threshold = self.builder.ins().iconst(types::I64, 1024);
// codegen.rs:864
let threshold = self.builder.ins().iconst(types::I64, 1024);
// vec_ops.rs:733
let threshold = builder.ins().iconst(types::I64, 1024);
```

**Impact**: If the threshold changes (e.g., because a future GC reserves more low addresses), every occurrence must be found and updated manually.

**Recommendation**: Define `pub(crate) const NULLARY_TAG_THRESHOLD: i64 = 1024;` in `codegen.rs` and replace all literal `1024` uses.

---

### LOW-2: `compile_function` has 21 parameters; `compile_body` has 23 parameters

**File**: `src/codegen.rs:1688-1710` (`compile_function`), `src/codegen.rs:1850-1873` (`compile_body`)
**Severity**: Low (maintainability)

Both public entry points carry `#[allow(clippy::too_many_arguments)]` suppressions. `compile_function` takes 21 arguments, `compile_function_indirect` takes 22, and `compile_body` takes 23. Most of these are IDs and references that are forwarded directly into `FnCompiler`.

**Impact**: Adding any new intrinsic function requires updating three function signatures and all call sites in `batch.rs` and `repl/`. The suppression hides a legitimate warning.

**Recommendation**: Group the fixed infrastructure parameters (`alloc_func_id`, `free_func_id`, `par_eval_func_id`, `ivar_create_func_id`, `ivar_spark_func_id`, `ivar_force_func_id`) into a `CodegenIntrinsics` struct. Group the type-resolution parameters (`type_defs`, `constructor_to_type`, `builtin_methods`, `modules`) into a `CodegenContext` struct. The public functions then take `intrinsics: &CodegenIntrinsics` and `ctx: &CodegenContext`, reducing the signature to ~10 parameters.

---

### LOW-3: `compile_inline_primitive` accepts only 2-argument calls but the check silently returns `None` for any other arity

**File**: `src/codegen/primitives.rs:19-21`
**Severity**: Low (robustness)

`compile_inline_primitive` early-returns `Ok(None)` if `args.len() != 2`. The `bind` primitive (lines 164-179) is a 2-argument case that fits, but any future 1-argument or 3-argument primitive added to this function would silently fall through to the non-primitive path and fail with a confusing "undefined variable" error.

```rust
pub(crate) fn compile_inline_primitive(&mut self, name: &str, args: &[Value], span: Span)
    -> Result<Option<Value>, CranelispError>
{
    if args.len() != 2 {
        return Ok(None);  // Silent: no 1-arg or unary primitives are dispatched here
    }
    // ...
}
```

**Impact**: `not`, `neg-f64`, or any future unary inline primitive would be silently skipped and fail elsewhere.

**Recommendation**: Replace the arity guard with per-arm arity checks inside the match, or add explicit `1 => { match name { ... } }` and `2 => { match name { ... } }` outer branches.

---

### LOW-4: `got_groups` linear scan for grouping by GOT base address

**File**: `src/codegen/trace.rs:66-73`, `src/codegen/trace.rs:499-504`
**Severity**: Low (performance)

Both `compile_trace` and `compile_run_tests` group `TracedFn` entries by `got_base` (an `i64`) using `iter_mut().find(|(addr, _)| *addr == tf.got_base)`. With `n` traced functions across `k` modules, this is O(n × k).

```rust
// trace.rs:68
if let Some(grp) = got_groups.iter_mut().find(|(addr, _)| *addr == tf.got_base) {
    grp.1.push(tf);
} else {
    got_groups.push((tf.got_base, vec![tf]));
}
```

**Impact**: In practice this is negligible (small number of modules). It is flagged as low priority.

**Recommendation**: Replace `Vec<(i64, Vec<TracedFn>)>` with `IndexMap<i64, Vec<TracedFn>>` (insertion-ordered HashMap) to get O(1) lookup while preserving deterministic iteration order.

---

### LOW-5: Zero unit tests for all codegen paths

**File**: `src/codegen/` (all files)
**Severity**: Low (quality assurance)

The entire codegen module — 6,192 lines — has zero `#[test]` functions. All correctness verification happens through integration tests in `tests/`. The liveness analysis (`liveness.rs`) and capture analysis (`captures.rs`) have 8 and 13 unit tests respectively, but the actual IR generation is never tested in isolation.

Critical paths with no direct test coverage:
- `emit_inc` / `emit_dec` RC correctness (only tested end-to-end)
- `pop_scope_for_value` borrowed-var upgrade logic (codegen.rs:606-626)
- `compile_tail_self_call` TCO jump generation
- `resolve_drop_fn` drop glue generation for sum types with mixed nullary/data constructors
- `classify_heap_type` / `heap_category` classification decisions

**Impact**: When RC bugs occur (use-after-free, double-dec), it is difficult to isolate whether the bug is in liveness analysis, `emit_consuming_caller_rc`, `pop_scope_for_value`, or the drop function generator. Integration tests that exercise the symptom (wrong output value, LIVE_ALLOCS failure) do not point to the causally faulty codegen function.

**Recommendation**: Add unit tests for at least `classify_heap_type`, `resolve_field_types`, `mangle_type_for_drop`, `emit_dec_inline` (by generating a simple function that decrements a ref count and verifying the emitted IR via `func.display()`), and `compute_last_uses` edge cases involving lambdas and match arms. The existing `FunctionBuilder` test pattern from Cranelift's own tests is a suitable template.

---

## Prioritized Improvement Plan

### Phase 1: Safety — Remove panics and fix correctness risks

1. **HIGH-4 partial**: Move `GotGroupData` to module scope to eliminate the in-function struct (low effort, immediate code clarity improvement).
2. **MED-1**: Replace `.expect()` calls on builtin registrations (`vec-set-rc`, etc.) with `Result`-returning lookups that produce `CranelispError`. Fix the `tail_loop_block.unwrap()` at `apply.rs:366` by restructuring the control flow to prove the invariant at the type level (e.g., return early before reaching the unwrap).
3. **MED-3**: Introduce a `TraceLeakRegistry` on `ReplSession` to collect and eventually reclaim leaked trace compilation allocations.

### Phase 2: Deduplication — Reduce the RC logic surface area

4. **HIGH-2**: Delete `FnCompiler::heap_category` and replace with `classify_heap_type(ty, self.type_defs)`.
5. **MED-5**: Extract `emit_dec_preamble` to unify the guard/atomic-sub/underflow-check pattern shared by `emit_dec_inline` and `emit_closure_dec_inline`.
6. **MED-7**: Replace per-byte `istore8` loops in panic string emission with host-side `alloc_string` followed by `iconst` for constant panic messages.
7. **LOW-1**: Add `pub(crate) const NULLARY_TAG_THRESHOLD: i64 = 1024;` and replace all literal uses.

### Phase 3: Function Decomposition — Reduce god-function sizes

8. **HIGH-1**: Add `FnCompiler::inner_compiler(builder, body) -> FnCompiler` method; replace the three struct-literal construction sites.
9. **HIGH-5**: Extract shared anonymous-fn compilation infrastructure from `compile_lambda` and `compile_par_bind_continuation` into `compile_anonymous_fn`.
10. **HIGH-3**: Extract `emit_vec_bounds_check` and `emit_vec_mutate_inplace` to reduce `compile_vec_set_inline` and `compile_vec_push_inline` from ~230 lines each to ~80 lines each.
11. **MED-2**: Extract `compile_constructor_call` and `compile_accessor_call_inline` from `compile_apply`.
12. **HIGH-4**: Extract `emit_got_swap_group` / `emit_got_restore` shared between `compile_trace` and `compile_run_tests`.

### Phase 4: Data Modeling — Structural improvements

13. **LOW-2**: Introduce `CodegenIntrinsics` and `CodegenContext` parameter structs to reduce `compile_function` / `compile_function_indirect` / `compile_body` argument lists.
14. **MED-6**: Pre-build `accessor_map: HashMap<String, AccessorInfoCg>` in `build_type_defs_cg` to replace the O(n×m) scan in `accessor_info`.
15. **LOW-4**: Replace GOT grouping `Vec<(i64, Vec<TracedFn>)>` with `IndexMap<i64, Vec<TracedFn>>`.

### Phase 5: Test Coverage

16. **LOW-5**: Add unit tests in `src/codegen/tests.rs` for:
    - `classify_heap_type` / `heap_category` for all ADT cases (pure nullary, pure data, mixed, unknown)
    - `mangle_type_for_drop` for nested ADTs and Vec
    - `resolve_field_types` with concrete type substitution
    - `compile_inline_primitive` for all arithmetic variants (using a minimal test module)
    - `compute_last_uses` for lambda and match arm edge cases (already in `liveness.rs` but missing lambda-capture and match binding cases)

---

## Verification

```sh
# Full test suite (must pass before and after any change)
just test

# Clippy (remove the #[allow(clippy::too_many_arguments)] after Phase 4)
just check

# Verify no remaining magic-number threshold after LOW-1
grep -rn 'iconst(types::I64, 1024)' src/codegen/

# Verify no remaining duplicate heap_category method after HIGH-2
grep -n 'fn heap_category' src/codegen.rs

# Count remaining .expect() / .unwrap() in codegen non-test code after MED-1
grep -n '\.expect(\|\.unwrap()' src/codegen.rs src/codegen/*.rs | grep -v '#\[cfg(test)\]'

# Smoke-test RC tracing (exercises emit_inc/emit_dec paths)
CRANELISP_RC_TRACE=1 just run examples/factorial.cl

# Verify no LIVE_ALLOCS leaks in integration tests
just test 2>&1 | grep -i 'live alloc\|double.free\|underflow'
```
