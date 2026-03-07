# Ring 2 Reference Counting Design

## Overview

Ring 2 activates the RC scaffolding laid down in Ring 1 (see `ring1-codegen.md` for foundation). It implements automatic memory management for all heap-allocated values: Strings, ADTs with data constructors, closures (Fn types), and Vecs. The key contribution is the **split calling convention** that determines which party (caller or callee) is responsible for RC decrements, plus the **scope cleanup** protocol that ensures no leaks on function exit.

This document is the authoritative reference for Ring 3 implementers. If you are compiling functions (macros, auto-curry wrappers, trace instrumentation), you must follow these conventions exactly or introduce leaks or use-after-free.

## 1. Heap Layout

All heap objects share a common header defined in `cranelisp-types::HeapHeader`:

```
Offset 0:  alloc_size  (i64)   -- total bytes (header + payload)
Offset 8:  rc          (i64)   -- reference count, initial = 1
Offset 16: ... payload ...
```

**Base-pointer convention**: pointers point to offset 0 (where `alloc_size` lives). All field accesses use positive offsets from the base. This is enforced by the representation containment rule: only `heap.rs` may import layout constants. All other codegen code calls `heap_load`, `heap_store`, `emit_alloc`, `emit_rc_inc`, `emit_rc_dec`.

### 1.1 HeapHeader (cranelisp-types)

```rust
#[repr(C)]
pub struct HeapHeader {
    pub alloc_size: i64,   // ALLOC_SIZE_OFFSET = 0
    pub rc: i64,           // RC_OFFSET = 8
}
// HeapHeader::SIZE = 16
```

### 1.2 HeapAdt (cranelisp-backend)

ADT data constructors (values with at least one field):

```
[header(16) | tag(8) | field_0(8) | field_1(8) | ... | field_n(8)]
 ^-- base pointer
```

- `TAG_OFFSET = 16`
- `FIELDS_START = 24`
- `field_offset(i) = 24 + i * 8`
- `payload_size(n_fields) = 8 + n_fields * 8`

Nullary constructors (e.g., `None`, `Red`) are **not** heap-allocated. They are bare i64 tags (0, 1, 2, ...). This means a value of a Mixed ADT type (e.g., `Option`) might be either a bare tag or a heap pointer. The `NULLARY_TAG_THRESHOLD` constant (1024) discriminates: values below the threshold are bare tags; values at or above are heap pointers.

### 1.3 HeapClosure (cranelisp-backend)

Closures carry a drop glue pointer embedded in the struct:

```
[header(16) | code_ptr(8) | drop_glue_ptr(8) | cap_0(8) | ... | cap_n(8)]
 ^-- base pointer
```

- `CODE_PTR_OFFSET = 16`
- `DROP_GLUE_PTR_OFFSET = 24`
- `CAPTURES_START = 32`
- `capture_offset(i) = 32 + i * 8`
- `payload_size(n_captures) = 16 + n_captures * 8`

The `drop_glue_ptr` is 0 when no captures are heap-typed. When non-zero, it points to a JIT-compiled function `(closure_ptr: i64) -> ()` that dec's each heap-typed capture before the closure itself is freed.

### 1.4 HeapVec (cranelisp-backend)

Vecs use a two-allocation design:

```
Vec struct: [header(16) | len(8) | cap(8) | data_ptr(8)]   = 40 bytes
Data buffer: [elem_0(8) | elem_1(8) | ... | elem_{cap-1}(8)]  (plain allocation, no header)
```

- `LEN_OFFSET = 16`
- `CAP_OFFSET = 24`
- `DATA_PTR_OFFSET = 32`

Only the Vec struct has an RC header. The data buffer is a plain `alloc`/`dealloc` allocation. `vec_drop` frees both the data buffer and the Vec struct.

### 1.5 HeapCategory

The `HeapCategory` enum classifies types for RC decisions:

| Category | Types | RC treatment |
|---|---|---|
| `NeverHeap` | Int, Bool, Float, pure-enum ADTs | No RC ops |
| `AlwaysHeap` | String, Fn, ADTs with only data constructors, Vec | Unconditional inc/dec |
| `Mixed` | ADTs with both nullary and data constructors (e.g., Option), unresolved type vars | Guarded inc/dec: skip if value < `NULLARY_TAG_THRESHOLD` |

`HeapCategory::classify(ty, type_defs)` is the single source of truth. When `type_defs` is available (after typechecking), classification is exact. Without it, ADTs conservatively classify as Mixed.

## 2. Reference Counting Protocol

### 2.1 Atomic Operations

RC operations are emitted as **inline atomic instructions**, not extern function calls:

- **Increment** (`emit_rc_inc`): `atomic_rmw(Add, ptr + RC_OFFSET, 1)` with `MemFlags::trusted()`.
- **Decrement** (`emit_rc_dec`): `atomic_rmw(Sub, ptr + RC_OFFSET, 1)` with `MemFlags::trusted()`. The old value is compared to 1: if equal (last reference), an Acquire fence is emitted, optional drop glue is called, and `runtime/dealloc` frees the object.

The atomics use `MemFlags::trusted()` (Cranelift's ordering for single-threaded code with potential future multi-threaded extension). The Acquire fence on the free path ensures all prior writes to the object are visible before deallocation.

### 2.2 Guarded Operations

For `Mixed` types, guarded variants skip the RC operation entirely when the value is a bare nullary tag:

```
if value < NULLARY_TAG_THRESHOLD:
    skip (bare tag, not a heap pointer)
else:
    perform rc_inc / rc_dec
```

- `emit_rc_inc_guarded`: branches around the inc.
- `emit_rc_dec_guarded(guard_nullary=true)`: branches around the dec.

### 2.3 When Inc Happens

An `rc_inc` is emitted whenever a new reference to a heap value is created:

1. **Consuming call arguments** (variable args): caller inc's before the call so the caller's binding survives the callee's dec.
2. **Closure capture**: each heap-typed capture is inc'd when stored into the closure env.
3. **Match field extraction**: when binding a field from a data constructor in a match arm, the field is inc'd to give the new binding its own reference.
4. **`vec-get` element read**: the loaded element is inc'd (it now has an independent reference outside the Vec).
5. **Return value protection**: `protect_return_value` inc's the body result before scope cleanup if the return value might alias a scope binding.

### 2.4 When Dec Happens

An `rc_dec` is emitted when a reference is released:

1. **Scope cleanup** (`pop_scope_with_cleanup`): at the end of a `let` body or function body, all heap-typed bindings are dec'd (except the return value).
2. **Borrowing call temporaries** (`dec_temporary_args`): after a builtin/extern call, any non-variable heap-typed argument expression is dec'd.
3. **Temporary closure callee**: after calling a closure expression (not a named variable), the closure is dec'd.
4. **Match scrutinee temporary**: if the scrutinee is a non-variable expression, it is dec'd after all arms have been compiled.
5. **Vec COW mutate-in-place**: the old element is dec'd before storing the new value.

### 2.5 What Triggers Free

When `rc_dec` brings the old RC to 1 (meaning it was the last reference):

1. **Acquire fence** to ensure write visibility.
2. **Drop glue** (if provided) is called to recursively dec any heap-typed sub-values.
3. **`runtime/dealloc`** reads `alloc_size` from offset 0 and frees the allocation.

## 3. Split Calling Convention

This is the central design decision of Ring 2. There are three conventions, determined statically at each call site.

### 3.1 Consuming Convention (User Functions)

**Applies to**: direct calls to user-defined functions, closure calls, trait method calls to user-defined impls, sig-dispatch calls.

**Protocol**:
1. **Caller** compiles args via `compile_consuming_arg_list`:
   - For each argument that is a variable reference (`Expr::Var`), check its type via `variable_types`. If heap-typed, emit `rc_inc` (or `rc_inc_guarded` for Mixed). This gives the callee its own reference to the caller's binding.
   - For each argument that is a temporary expression (not a Var), no caller-side action is needed. The temporary starts at rc=1 from its allocation, and the callee's dec will free it.
2. **Callee** owns all parameters. At function exit, `pop_scope_with_cleanup` dec's all heap-typed parameters (and let-bindings), except the return value variable.

**Why this works**: A variable argument has rc >= 2 after the inc (one for the caller's binding, one for the callee). The callee's dec brings it back to rc >= 1. A temporary argument has rc=1. The callee's dec brings it to 0, freeing it.

### 3.2 Borrowing Convention (Builtins/Externs)

**Applies to**: inline arithmetic/boolean/comparison operators, extern string primitives (`str-concat`, `str-eq`, etc.), primitive trait methods that compile to inline IR.

**Protocol**:
1. **Caller** compiles args via `compile_arg_list` (plain, no RC adjustments).
2. After the call, **caller** calls `dec_temporary_args`: for each argument that is NOT a `Expr::Var` and IS heap-typed, emit `rc_dec` (with drop glue if needed). Variable arguments are left alone; they are owned by their scope.

**Why this convention exists**: Builtin operations are compiled inline (no function body exists to dec parameters). String externs are Rust functions that do not touch RC. In both cases, the caller is the only party that can clean up temporaries.

### 3.3 Data Constructor Convention

**Applies to**: calls to ADT data constructors (e.g., `(Some x)`, `(Pair 1 2)`).

**Protocol**:
1. **Caller** compiles args via `compile_arg_list` (plain, no RC adjustments).
2. No post-call dec is emitted. The arguments become fields of the newly allocated ADT. When the ADT is dec'd and freed, **drop glue** handles decrementing each heap-typed field.

**Why no inc/dec at call site**: The constructor stores the field values directly into the new heap object. If the field value is a temporary (rc=1), it now has exactly one owner (the ADT). If it is a variable, the variable still holds its reference, and the ADT field shares the same pointer value — but no inc is emitted because the two references serve different lifetimes, managed by separate mechanisms.

**Variable-into-constructor ownership detail**: Consider `(let [s "hello"] (Some s))`. At the `(Some s)` call site, no inc or dec is emitted (plain `compile_arg_list`). Two things now reference the string: the variable `s` and the `Some` ADT's field. These are tracked independently:

- The variable `s` is owned by its scope. When `s` goes out of scope, `pop_scope_with_cleanup` dec's it. This is a dec of the *variable's* reference, not the ADT's field.
- The ADT `(Some s)` is itself a new heap allocation at rc=1. It is tracked by whatever scope or calling convention governs the ADT value. The ADT's drop glue will dec the field when the ADT reaches rc=0.

Between these two dec paths, the underlying string stays alive as long as either reference exists. If the ADT is later passed to a user function (consuming convention), the inc at *that* call site is on the ADT itself — it has nothing to do with the original constructor call. The constructor call site emits no RC operations at all.

### 3.4 Convention Decision Table

| Call type | Convention | Arg compilation | Post-call cleanup |
|---|---|---|---|
| User-defined function (direct) | Consuming | `compile_consuming_arg_list` | Callee dec's at exit |
| Closure call (named variable callee) | Consuming | `compile_consuming_arg_list` | Callee dec's at exit |
| Closure call (temporary expression callee) | Consuming + callee dec | `compile_consuming_arg_list` | Callee dec's args; caller dec's closure |
| Trait method (user impl) | Consuming | `compile_consuming_arg_list` | Callee dec's at exit |
| Trait method (primitive impl, inline IR) | Borrowing | `compile_arg_list` | `dec_temporary_args` |
| Trait method (primitive impl, extern) | Borrowing | `compile_arg_list` | `dec_temporary_args` |
| Sig-dispatch (multi-sig) | Consuming | `compile_consuming_arg_list` | Callee dec's at exit |
| Inline builtin operator | Borrowing | `compile_arg_list` | `dec_temporary_args` |
| Extern primitive (str-concat, etc.) | Borrowing | `compile_arg_list` | `dec_temporary_args` |
| Vec primitive (vec-get, etc.) | Borrowing (special) | `compile_arg_list` | Internal cleanup via `emit_vec_drop_if_temporary` |
| Data constructor | None (field store) | `compile_arg_list` | Drop glue handles fields |

### 3.5 Temporary Closure Callee

When the callee itself is a temporary expression (e.g., `((make-adder 5) 3)`), the result of the callee expression is a closure at rc=1. After the call:

1. The return value is **protected**: if heap-typed, emit `rc_inc` on the result before dec'ing the closure. This prevents premature deallocation if the result aliases a captured value.
2. The temporary closure is dec'd via `emit_closure_dec`.

## 4. Drop Glue

Drop glue is the mechanism by which composite heap values recursively release their sub-values when freed.

### 4.1 Closure Drop Glue

Closure drop glue is generated by `build_closure_drop_glue` when a lambda has heap-typed captures. The generated function:

1. Receives the closure base pointer.
2. For each heap-typed capture at offset `capture_offset(i)`, loads the value and emits `rc_dec` (guarded for Mixed types).

The drop glue pointer is **embedded** in the closure at `DROP_GLUE_PTR_OFFSET` (offset 24). This is essential because the caller often does not know the closure's capture layout at compile time (e.g., when a `Fn` parameter is received from another module).

At dec time, `emit_closure_dec_inline`:
1. Atomically decrements RC.
2. If old RC was 1 (last reference):
   a. Acquire fence.
   b. Loads `drop_glue_ptr` from offset 24.
   c. If non-zero, calls it via `call_indirect`.
   d. Calls `runtime/dealloc`.

### 4.2 ADT Inline Drop Glue

ADT field cleanup uses two approaches:

**Inline drop glue** (`emit_inline_drop_glue` on FnCompiler): Emitted directly into the caller's function body. Used by `pop_scope_with_cleanup` and `dec_temporary_args`. For each data constructor with heap-typed fields:
- Single data constructor: directly load and dec each heap-typed field.
- Multiple data constructors: load the tag, branch to the correct constructor's field-dec block.
- For Mixed ADTs, the entire drop glue is guarded by a heap-pointer check.

**Standalone drop glue** (`build_adt_drop_glue_fn`): A separate JIT function `(ptr: i64) -> ()`. Used by Vec element dec functions. The generated function has the same tag-dispatch logic but lives as an independent function that can be referenced by function pointer.

### 4.3 Vec Drop Glue

Vec uses a two-level approach:

1. **Element-level**: `build_elem_dec_fn` generates a standalone `(val: i64) -> i64` function per element type. If the element type is an ADT with heap fields, `build_adt_drop_glue_fn` generates a nested drop glue function that is passed to `emit_rc_dec_guarded` inside the element dec function.

2. **Vec-level**: `vec_drop(vec_ptr, elem_dec_fn_ptr)` in the runtime iterates over live elements (indices 0..len), calls the element dec function on each, then frees the data buffer and the Vec struct.

Element inc/dec functions are generated by:
- `build_elem_inc_fn`: emits `rc_inc` (or guarded inc for Mixed) on the element value.
- `build_elem_dec_fn`: emits `rc_dec_guarded` (with optional ADT drop glue) on the element value.

Both are called from the runtime via function pointer during Vec copy operations and Vec drop.

## 5. Scope Cleanup

### 5.1 pop_scope_with_cleanup

`pop_scope_with_cleanup(skip_var)` is the workhorse of automatic memory management. Called at the end of every `let` body and every function body:

1. Iterates over the current scope frame's bindings.
2. Skips the `skip_var` (the binding whose value is being returned -- its ownership transfers to the caller).
3. Skips consumed variables (already transferred to a callee).
4. For each remaining heap-typed binding:
   - `Type::Fn`: calls `emit_closure_dec_inline` (runtime drop glue dispatch).
   - ADT types: calls `emit_inline_drop_glue` then `emit_rc_dec` (or guarded variants for Mixed).
   - Other heap types (String): calls `emit_rc_dec` directly.
5. Pops the scope frame, removing bindings from `variables` and `variable_types`.

### 5.2 return_var_in_scope

Determines which variable (if any) should be skipped by scope cleanup:

```rust
fn return_var_in_scope(body: &Expr, scope_frame: Option<&Vec<Symbol>>) -> Option<Symbol>
```

If the body is a direct `Expr::Var` reference to a name in the current scope frame, that name is returned as the skip_var. Scope cleanup then dec's everything except this binding, whose ownership is transferred to the parent.

### 5.3 protect_return_value

When `skip_var` is `None` (the body is not a direct variable reference -- e.g., it's an `if`, `match`, or function call), the return value might alias a scope binding. For example:

```clojure
(let [s "hello"]
  (if cond s "world"))
```

Here the `if` expression's result might be `s`, but `return_var_in_scope` returns `None` (the body is `if`, not a `Var`). Scope cleanup will dec `s`, which could free it before the result is returned.

`protect_return_value` handles this by emitting `rc_inc` on the result value before scope cleanup runs, but only when:
1. `skip_var` is `None`.
2. The body is not a fresh allocation (`Lambda` or `StringLit`) that cannot alias scope bindings.
3. The current scope has at least one heap-typed binding.
4. The result type is heap-typed.

The caller's subsequent dec (at its own scope exit) restores the net count.

### 5.4 Match Interaction with Scope Cleanup

Match arms introduce their own scope frames:

1. **Variable pattern** (`x`): binds the scrutinee to `x`, pushes a scope. The arm body is compiled, then `pop_scope_with_cleanup` dec's the binding (unless it's the return value).

2. **Constructor pattern** (`(Some val)`): pushes a scope, binds each extracted field. Extracted fields get `rc_inc` at extraction time (they need their own reference independent of the scrutinee). The arm body is compiled, then `pop_scope_with_cleanup` dec's the field bindings.

3. **Scrutinee temporary**: After all arms converge at the merge block, if the scrutinee was a temporary expression (not a Var), inline drop glue is emitted and the scrutinee is dec'd.

The scope cleanup per arm ensures that field bindings extracted in constructor patterns are properly released even when the arm body doesn't return them.

### 5.5 Captured Variables and Last-Use

Two rules modify scope cleanup behavior:

- **Captured variables** (`captured_vars`): Variables closed over by a lambda are NEVER eligible for last-use transfer. The closure env holds its own inc'd reference, and the enclosing scope must dec its own reference at scope exit regardless.

- **Last-use analysis** (`compute_last_uses`): Walks the expression tree in pre-order to determine the final use of each variable. The last use of a variable reference is a candidate for ownership transfer (skip the inc at the call site because the callee gets the caller's last reference). Currently used by Vec COW to determine mutate-in-place eligibility, but the general mechanism is available for future optimization.

## 6. Invariants

These invariants must hold at all times. Violation indicates a bug.

### 6.1 RC Invariants

1. **RC never negative**: Every `rc_dec` that brings RC to 0 triggers deallocation. If RC would go below 0, `rc_underflow_check` fires a debug assertion.

2. **RC starts at 1**: `alloc_with_rc` initializes RC to 1. The allocating expression is the initial owner.

3. **Every inc has a matching dec**: Inc-dec pairs are balanced across ownership transfers. A calling convention violation (wrong convention for a call type) will cause either a leak (missing dec) or a use-after-free (extra dec).

4. **Drop glue runs before dealloc**: When a value reaches rc=0, its drop glue recursively dec's sub-values before the object is freed. Skipping drop glue causes field leaks.

### 6.2 Calling Convention Invariants

5. **User function parameters are consumed**: A user function's `compile_body` always ends with `pop_scope_with_cleanup` that dec's all heap-typed parameters. The caller must inc variable arguments before the call to preserve its own bindings.

6. **Builtin/extern parameters are borrowed**: The caller dec's temporaries after the call. Variable arguments are untouched and remain owned by their scope.

7. **Data constructor fields are owned by the ADT**: No inc/dec at the constructor call site. Drop glue handles fields at destruction time.

### 6.3 Debugging Invariants

8. **LIVE_ALLOCS tracking** (debug builds): Every `alloc_with_rc` call adds the pointer to a `HashSet`. Every `dealloc` removes it (asserting it was present). A double-free triggers a debug assertion.

9. **RC trace logging**: `CRANELISP_RC_TRACE=1` enables per-operation logging to stderr, showing pointer address and RC value for every alloc, free, inc, and dec.

## 7. Implementation Locations

| Component | File | Key functions |
|---|---|---|
| HeapHeader | `cranelisp-types/src/heap.rs` | `HeapHeader`, `HeapCategory::classify` |
| Heap layout structs | `cranelisp-backend/src/heap.rs` | `HeapAdt`, `HeapClosure`, `HeapVec` |
| RC emission | `cranelisp-backend/src/heap.rs` | `emit_rc_inc`, `emit_rc_inc_guarded`, `emit_rc_dec`, `emit_rc_dec_guarded` |
| Last-use analysis | `cranelisp-backend/src/heap.rs` | `compute_last_uses` |
| Calling convention | `cranelisp-backend/src/compiler/apply.rs` | `compile_consuming_arg_list`, `compile_arg_list`, `dec_temporary_args` |
| Scope cleanup | `cranelisp-backend/src/compiler/mod.rs` | `pop_scope_with_cleanup`, `return_var_in_scope`, `protect_return_value` |
| Inline drop glue | `cranelisp-backend/src/compiler/mod.rs` | `emit_inline_drop_glue`, `emit_field_decs` |
| Closure drop glue | `cranelisp-backend/src/compiler/control_flow.rs` | `build_closure_drop_glue`, `emit_closure_dec_inline` |
| Standalone ADT drop glue | `cranelisp-backend/src/compiler/vec_codegen.rs` | `build_adt_drop_glue_fn`, `emit_standalone_field_decs` |
| Vec element inc/dec | `cranelisp-backend/src/compiler/vec_codegen.rs` | `build_elem_inc_fn`, `build_elem_dec_fn` |
| Runtime allocator | `cranelisp-runtime/src/alloc.rs` | `alloc_with_rc`, `dealloc`, `heap_alloc`, `heap_dealloc` |
| Runtime Vec | `cranelisp-runtime/src/vec.rs` | `vec_new`, `vec_drop`, `vec_set_copy`, `vec_push_copy`, `vec_push_grow` |
| RC debug/trace | `cranelisp-runtime/src/rc.rs` | `rc_trace`, `rc_underflow_check` |
| Intrinsic registration | `cranelisp-backend/src/jit.rs` | `register_intrinsics` |

## 8. Guidance for Ring 3 Implementers

### 8.1 Compiling a New Function

If you are generating a JIT function (e.g., a macro expansion helper, a trace wrapper):

1. **Parameters**: If the function will be called with the consuming convention, its parameters are owned. You MUST ensure `pop_scope_with_cleanup` runs at function exit with the return variable excluded.
2. **Calling user functions**: Use `compile_consuming_arg_list` for the args. The callee will dec everything.
3. **Calling builtins/externs**: Use `compile_arg_list`, then call `dec_temporary_args` after.
4. **Allocating closures**: Call `build_closure_drop_glue` and store the result at `DROP_GLUE_PTR_OFFSET`. Inc heap-typed captures.

### 8.2 TCO and RC

Self-recursive tail calls currently do NOT emit scope cleanup before jumping to the loop header. This means heap-typed parameters from the previous iteration may leak. TCO+RC interaction is a known gap: the sketch's `emit_scope_cleanup_for_tco` was not carried forward to the reimplementation. Ring 3 should either implement this or document the restriction.

### 8.3 Common Pitfalls

- **Missing inc for variable args in consuming calls**: Causes use-after-free. The callee dec's the parameter at exit; without the caller's inc, the caller's binding is freed.
- **Missing dec for temporary args in borrowing calls**: Causes leaks. Nobody else will dec the temporary.
- **Wrong convention for a call type**: A user function called with borrowing convention will have its parameters dec'd twice (once by callee, once by caller). An extern called with consuming convention will have its parameters dec'd by the callee's scope cleanup, but externs have no scope cleanup -- the dec never happens, causing leaks.
- **Forgetting protect_return_value**: Causes use-after-free when the return value aliases a scope binding that gets dec'd by scope cleanup.
- **Captured variables treated as last-use**: Captured variables must NEVER skip inc at consuming call sites. The closure env needs its reference to remain valid.

## 9. Rejected Alternatives

### 9.1 Drop Function Side Table (Ring 1)

Ring 1 considered using a `HashMap<code_ptr, drop_fn>` for closure drop glue instead of embedding the pointer in the closure struct. This was rejected because:
- The side table requires locking or thread-local storage for lookups.
- Embedding the pointer costs 8 bytes per closure but makes closure dec a self-contained operation.
- Critical benefit: `emit_closure_dec_inline` can handle closures from any module without a global side table lookup.

### 9.2 Unified Calling Convention

Considered making all calls consuming. Rejected because:
- Builtins/externs compile to inline IR or Rust functions with no function body to dec parameters.
- Forcing consuming convention on builtins would require wrapper functions around every arithmetic operation, adding overhead and complexity.

### 9.3 Deferred Reference Counting

Considered deferring RC operations to epoch boundaries (like Nim). Rejected because:
- Deterministic destruction is a language design goal.
- Deferred RC complicates reasoning about when side effects (via destructors/drop glue) occur.
- The inline atomic approach has acceptable overhead for the current single-threaded model.
