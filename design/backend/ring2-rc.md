# Ring 2 Reference Counting Design

## Overview

Ring 2 activates the RC scaffolding laid down in Ring 1 (see `ring1-codegen.md` for foundation). It implements automatic memory management for all heap-allocated values: Strings, ADTs with data constructors, closures (Fn types), and Vecs. The key contribution is the **uniform consuming calling convention** (Decision 24) — every call site compiles identically for RC management, with the callee responsible for dec'ing heap parameters it does not return — plus the **scope cleanup** protocol that ensures no leaks on function exit.

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

1. **Scope cleanup** (`pop_scope_with_cleanup`): at the end of a `let` body or function body, all heap-typed bindings are dec'd (except the return value). For user-defined functions, this includes all heap-typed parameters (the consuming convention).
2. **Callee-side extern dec**: extern primitives implemented in Rust (`str-concat`, `string-length`, Vec ops, Sexp marshaling, IO trampolines, etc.) dec any heap argument they do not return. This is part of the uniform consuming convention — there is no caller-side post-call temporary dec.
3. **Temporary closure callee**: after calling a closure expression (not a named variable), the closure is dec'd.
4. **Match scrutinee temporary**: if the scrutinee is a non-variable expression, it is dec'd after all arms have been compiled.
5. **Vec COW mutate-in-place**: the old element is dec'd before storing the new value.

### 2.5 What Triggers Free

When `rc_dec` brings the old RC to 1 (meaning it was the last reference):

1. **Acquire fence** to ensure write visibility.
2. **Drop glue** (if provided) is called to recursively dec any heap-typed sub-values.
3. **`runtime/dealloc`** reads `alloc_size` from offset 0 and frees the allocation.

## 3. Calling Convention

**Historical note**: Prior to Sprint 56 Step 2c, this section described a split convention (Decision 20, retracted) with three classifications — consuming for user functions, borrowing for builtins/externs, and none for data constructors — plus a caller-side `dec_temporary_args` helper. The current target is **Decision 24** — a uniform consuming convention applied to every call type. The split form is gone; data constructors are reclassified as consuming (the ADT inherits ownership of field values); extern primitives now dec their own heap arguments before return.

There is exactly one calling convention, applied identically to direct user-function calls, closure calls (named or temporary callee), trait method dispatch (user impls and primitive/extern impls), sig-dispatch, data constructors, inline builtin operators, Vec primitives, and every extern Rust function that takes heap arguments.

### 3.1 The Uniform Consuming Convention

**Protocol**:
1. **Caller** compiles args via `compile_consuming_arg_list`:
   - For each argument that is a variable reference (`Expr::Var`), check its type via `variable_types`. If heap-typed, emit `rc_inc` (or `rc_inc_guarded` for Mixed). This gives the callee its own reference to the caller's binding while preserving the caller-side binding. (Future optimisation: skip this inc when last-use analysis proves the variable is not reused after the call — direct transfer.)
   - For each argument that is a temporary expression (not a Var), no caller-side action is needed. The temporary starts at rc=1 from its allocation; ownership transfers to the callee.
2. **Callee** owns all heap parameters. It is responsible for dec'ing anything it does not return. The form of that dec depends on what the callee is:
   - **User-defined function**: `pop_scope_with_cleanup` at function exit dec's all heap-typed parameters (and let-bindings) except the return variable. This is automatic — the backend emits it for every user function.
   - **Extern Rust primitive**: the Rust implementation itself dec's its heap arguments before returning. See §3.3 Extern Consumption Audit.
   - **Data constructor**: the field-store implicitly consumes the argument (the new heap object holds the only reference to the transferred value; the ADT's own drop glue will dec each heap-typed field when the ADT itself reaches rc=0). The constructor emits no explicit dec because the dec happens later through the ADT's lifetime.
   - **Inline builtin operator**: operators whose operands are NeverHeap (integers, booleans, floats, comparison results) need no dec — there is nothing to free. Operators whose operands are heap-typed (e.g., a hypothetical string arithmetic) behave like externs: they dec their heap args inline before producing the result.
   - **Closure call**: the code pointer leads to a user function body, so `pop_scope_with_cleanup` in the target applies. When the closure callee is a temporary expression, the caller additionally dec's the closure value itself after the call (it was a one-shot temporary, not a named binding).

**Why this works**: With uniform consuming semantics, every heap-typed argument has exactly one dec responsibility — the callee. The caller's inc for variable args preserves the caller-side binding; the callee's dec matches it. Temporary args transfer rc=1 directly; the callee's dec releases them. There is no divergent code path, no attribute annotation on extern symbols, no `dec_temporary_args` post-call cleanup.

### 3.2 Variable-into-Constructor Ownership

Consider `(let [s "hello"] (Some s))`. At the `(Some s)` call site, `compile_consuming_arg_list` emits an `rc_inc` on `s` (it is a heap-typed Var). The constructor stores the string pointer as a field; the ADT now holds one reference. Two things now reference the string: the variable `s` (held by the enclosing `let` scope) and the `Some` ADT's field.

- The variable `s` is owned by its scope. When `s` goes out of scope, `pop_scope_with_cleanup` dec's it.
- The ADT `(Some s)` is itself a new heap allocation at rc=1. It is tracked by whatever scope or calling convention governs the ADT value. The ADT's drop glue will dec the field when the ADT reaches rc=0.

Between these two dec paths, the underlying string stays alive as long as either reference exists. If the ADT is later passed to a user function, the inc at *that* call site is on the ADT pointer itself.

For temporary-into-constructor (e.g. `(Some (str-concat a b))`): the temporary result of `str-concat` has rc=1, no caller-side inc is emitted (it is not a Var), and the field store transfers ownership directly to the ADT. No extra inc/dec is required.

### 3.3 Extern Consumption Audit (Sprint 56 Step 2c)

Under Decision 24, every extern primitive implemented in Rust that takes a heap argument MUST dec that argument before returning, unless the argument is returned unchanged (in which case ownership flows out through the return value) or stored in a runtime-owned structure that will outlive the call (in which case the extern has inc'd it and the caller's passed-in reference must not be dec'd by the extern — use the "retains" column).

The authoritative per-extern table is:

| Extern name | Crate/file | Heap arg(s) | Returns arg unchanged? | Retains arg? | Action (Sprint 56 Step 2c) |
|---|---|---|---|---|---|
| `str-concat` | runtime/string.rs | `a`, `b` (String) | No (returns new String) | No | **DONE**: dec both via `rc::consume_shallow` before return; caller uses `compile_consuming_arg_list` |
| `str-eq` | runtime/string.rs | `a`, `b` (String) | No (returns Bool) | No | **DONE**: dec both |
| `str-len` | runtime/string.rs | `s` (String) | No (returns Int) | No | **DONE**: dec |
| `string-identity` | runtime/string.rs | `s` (String) | Yes (returns same ptr after inc) | Yes (inc'd) | **DONE** (semantics-preserving): inc-and-return is already consuming — the returned pointer carries the caller's consumed reference plus a fresh inc. Caller uses `compile_arg_list` (no inc) because inc-and-return would double-up otherwise. |
| `substring` | runtime/string.rs | `s` | No (returns new String) | No | **DONE**: dec |
| `char-at` | runtime/string.rs | `s` | No (returns new String) | No | **DONE**: dec |
| `split` | runtime/string.rs | `s`, `sep` | No (returns Vec of Strings) | No | **DONE**: dec both |
| `join` | runtime/string.rs | `sep`, `vec` | No (returns new String) | No | **DONE**: `consume_shallow` on sep; `drop::consume_vec_of_string` on vec (walks String elements, frees data buffer, frees Vec struct). |
| `replace` | runtime/string.rs | `s`, `from`, `to` | No | No | **DONE**: dec all three |
| `trim` | runtime/string.rs | `s` | No | No | **DONE**: dec |
| `starts-with?` | runtime/string.rs | `s`, `prefix` | No | No | **DONE**: dec both |
| `ends-with?` | runtime/string.rs | `s`, `suffix` | No | No | **DONE**: dec both |
| `contains?` | runtime/string.rs | `s`, `needle` | No | No | **DONE**: dec both |
| `to-upper` | runtime/string.rs | `s` | No | No | **DONE**: dec |
| `to-lower` | runtime/string.rs | `s` | No | No | **DONE**: dec |
| `int-to-string` | runtime/primitives/int.rs | none (Int arg) | — | — | no heap arg |
| `float-to-string` | runtime/primitives/float.rs | none (Float bits) | — | — | no heap arg |
| `bool-to-string` | runtime/primitives/bool.rs | none (Bool arg) | — | — | no heap arg |
| `parse-int` | runtime/primitives/int.rs | `s` (String) | No (returns Option Int) | No | **DONE**: dec |
| `sconcat` | runtime/marshal.rs | `xs`, `ys` (SList) | Sometimes (ys if xs empty — inc'd) | Sometimes (ys deep inc; xs items shallow inc) | **DONE**: after building result (which shares items from xs and reuses ys as tail with deep inc), `drop::consume_slist` releases both inputs — on the last-ref path it recursively walks SCons nodes and Sexp heads. |
| `quote-sexp` | runtime/marshal.rs | `val` (Sexp) | No (returns new Sexp) | No | **DONE**: split into `quote_sexp` (extern entry — builds then `drop::consume_sexp(val)`) and `quote_sexp_build` (internal, non-consuming, used by `quote_slist` recursion since sub-items are owned by the parent SList). |
| `vec-len` | runtime/vec.rs | `vec` (Vec) | No (returns Int) | No | handled inline in vec codegen via `emit_vec_drop_if_temporary` (Vec-op caller handling — see below). Not routed through the extern-primitive consuming path. |
| `vec-set-copy` | runtime/vec.rs | `vec` | No (returns new Vec) | No | handled by caller (`emit_vec_drop_if_temporary`) — no change here; vec-codegen path is already correct |
| `vec-push-copy` | runtime/vec.rs | `vec` | No (returns new Vec) | No | handled by caller (`emit_vec_drop_if_temporary`) |
| `vec-push-grow` | runtime/vec.rs | `vec` | Yes (returns same pointer) | Yes (keeps ownership) | ok — mutation in place; semantically consuming-then-re-returning |
| `heap_alloc_string` | runtime/string.rs | none (raw bytes ptr, len) | — | — | no heap arg (raw, not a Cranelisp heap) |
| `string_read` | runtime/string.rs | `s` | out-params only, no return | borrowed for the call | ok — called from Rust side (ValueFormatter), not from JIT |
| `cranelisp_trace_name` | runtime/trace.rs | `trace` (Trace ADT) | No (returns field value) | No | **DONE**: inc the returned field (heap-typed — now has its own reference), then `drop::consume_trace_call` releases the Trace (walks sub-refs tname/tparams/tresult/tchildren on last ref). |
| `cranelisp_trace_params` | runtime/trace.rs | `trace` | No | No | **DONE**: same as cranelisp_trace_name |
| `cranelisp_trace_result` | runtime/trace.rs | `trace` | No | No | **DONE**: same as cranelisp_trace_name |
| `cranelisp_trace_children` | runtime/trace.rs | `trace` | No | No | **DONE**: same as cranelisp_trace_name |
| `cranelisp_trace_nanos` | runtime/trace.rs | `trace` | No | No | **DONE**: Int return — no inc; `drop::consume_trace_call` on the Trace. |
| `cranelisp_trace_first_child_nanos` | runtime/trace.rs | `trace` | No | No | **DONE**: Int return — no inc; `drop::consume_trace_call` on the Trace. |
| `cranelisp_run_io` | runtime/io.rs | `io_ast` (IO ADT) | No | No (evaluates to completion) | **TOP-LEVEL DONE**: after `run_io_trampoline` returns the final value, `drop::consume_io_tree(io_ptr)` releases the whole tree (tag-dispatched: Pure/Effect are leaves, Bind recurses into inner + consumes the continuation closure, Par walks all branches). **INTERNAL-LOOP OPEN (Sprint 57 Phase 4 G8 fix)**: intermediate Pure/Effect/Bind/Par nodes produced or replaced during the trampoline walk, and continuation closures popped from `cont_stack` and invoked, are leaked. See §3.5. |
| IVar intrinsics | runtime/ivar.rs | various | varies | varies | separately reviewed — IVar code already has RC management for its specific semantics |
| Platform DLL functions | cranelisp-platform/src/lib.rs | varies per DLL | varies | varies | see platform CLAUDE.md; platform fns are consuming per Decision 24, most already use CLString::own() pattern |

**Full migration complete**: all 36 externs consume correctly under Decision 24 (Sprint 56 Step 2c). Caller-side inc runs via `compile_consuming_arg_list` (apply.rs) for every heap-typed Var argument. Callee-side dec runs via:

- `rc::consume_shallow` — simple-heap externs whose heap args have no heap sub-refs (all 14 string externs + `parse-int`).
- `drop::consume_slist` / `consume_sexp` — SList/Sexp runtime marshaling (`sconcat`, `quote-sexp`).
- `drop::consume_vec_of_string` — Vec of Strings (`join`).
- `drop::consume_trace_call` — Trace ADT accessors (6 functions).
- `drop::consume_io_tree` — IO trampoline (`cranelisp_run_io`).

Each `drop::consume_*` function mirrors the backend's `emit_rc_dec_with_inline_drop_glue` in Rust: atomic dec with Release ordering; on last-ref path, Acquire fence → walk heap-typed fields → recursively consume each → dealloc the outer allocation. Non-last-ref paths short-circuit after the outer dec, matching the inline-drop-glue invariant that sub-refs are dec'd only when the outer reaches rc=0.

RC balance is: Var arg → caller +1, callee −1 = net 0 (Var's own scope still holds its original ref); Temp arg → caller +0 (no inc), callee −1 = net −1 (frees the temp, which started at rc=1).

**`string-identity`**: the one exception remains consuming-compatible. Semantically it is "inc and return" — the input pointer flows out through the return value with a fresh inc. Callers use `compile_arg_list` (no caller-side inc) because inc-and-return on an already-inc'd arg would double-count.

**Vec-op caller handling**: `compile_vec_op` in backend emits `emit_vec_drop_if_temporary(vec_arg)` for the old Vec when the copy path is taken. This is a caller-side dec that predates Decision 24 and is tied to COW semantics (the old Vec is structurally replaced). It is NOT a post-call `dec_temporary_args` — it is a COW-specific cleanup that runs in the copy branch only. Keep it as is.

**Data constructor calls** (`compile_var_apply` → `compile_data_constructor_call`): now uses `compile_consuming_arg_list` for its args. Variable args get inc'd at the call site so the caller's scope still holds a reference while the ADT holds its own independent reference (released via the ADT's drop glue at destruction). Previously used plain-arg compilation, which caused use-after-free when the ADT outlived the caller's scope (the field stored a pointer to a heap object whose only reference was about to be dec'd by scope cleanup). Fixed in Step 2c.

**Operator wrappers (`cranelisp_op_add` etc.)**: No heap args — Int/Bool/Float bit-patterns only. No action.

**Guidance for adding new externs**: default to consuming. For each heap-typed parameter decide: (a) does it flow out unchanged through the return? If yes, inc-and-return or just return-as-is with ownership transfer. (b) does it get stored/retained? If yes, inc it into the storage. (c) otherwise: dec it before return. Write a test per §4 of this doc.

### 3.4 Temporary Closure Callee

When the callee itself is a temporary expression (e.g., `((make-adder 5) 3)`), the result of the callee expression is a closure at rc=1. After the call:

1. The return value is **protected**: if heap-typed, emit `rc_inc` on the result before dec'ing the closure. This prevents premature deallocation if the result aliases a captured value.
2. The temporary closure is dec'd via `emit_closure_dec`.

### 3.5 IO Trampoline Intermediate-Node Leak (Sprint 57 Wave 3 — LANDED)

The IO trampoline in `crates/cranelisp-runtime/src/io.rs` is the Ring 4 counterpart to the user-function consuming convention: it executes an IO ADT tree built by the frontend/prelude (Pure / Effect / Bind / Par) and returns the final value. Under Decision 24, the extern entry `cranelisp_run_io(io_ptr)` consumes the **top-level** IO argument via `crate::drop::consume_io_tree(io_ptr)` after the trampoline returns. Before Sprint 57 Wave 3, intermediate Pure/Effect nodes produced by continuations during the walk were leaked: each continuation's returned node became the new `current` and the prior `current` was dropped from the local without a matching dec/dealloc.

Before the Wave 3 fix, this was a real leak, not cosmetic (per `/arch` review condition 6). Every Bind-chain step through a continuation produces a fresh IO node (typically a Pure or Effect) that replaces the previous `current`; the previous `current` — an earlier intermediate produced by an earlier continuation — had no further reference and no matching dec. Under a Ring-4 program doing many binds, the leak was O(binds).

The Wave 3 fix distinguishes **caller-tree** nodes (reachable from the original `io_ptr`, released by the top-level `consume_io_tree`) from **fresh** nodes (produced by continuations during the walk, released inline by the trampoline). See §3.5.4 for the landed implementation.

#### 3.5.1 What `run_io_trampoline` does

`run_io_trampoline(io_ptr: i64) -> i64` walks the IO ADT iteratively with an explicit `cont_stack: Vec<i64>` of continuation closures. On each iteration, it reads `current`'s tag (offset 16) and dispatches:

| Tag | Action | How `current` is replaced |
|---|---|---|
| Pure | Read field0 (payload). Pop a continuation or return. | If cont popped: `current = call_continuation(cont_ptr, val)` — the continuation returns a fresh IO node. If no cont: return val to caller (Pure node is not consumed here; dec'd by `cranelisp_run_io` via `consume_io_tree` on the top-level root — but only if `current` IS the top-level root at return time, which it is not after the first continuation). |
| Effect | Read field0 (thunk ptr), invoke the thunk via `call_effect_thunk`. Pop a continuation or return. | Same as Pure — continuation returns a fresh IO node, or trampoline returns the result value directly. |
| Bind | Read field0 (inner), field1 (cont). Push cont on stack. | `current = inner` — the Bind node itself has no further use; its inner pointer is now the new current. The Bind node is leaked unless later consumed. |
| Par | Read count + branch pointers. Dispatch rayon parallel evaluation. Allocate results buffer. Pop a continuation or return. | `current = call_continuation(cont_ptr, results_ptr)` or return results_ptr. |

#### 3.5.2 Where the intermediate nodes come from

Two sources:

1. **Continuation returns.** A Cranelisp continuation is a lambda `(fn [x] <expr>)` where `<expr>` builds and returns an IO value — typically `(pure (+ x 1))` or `(bind <another-io> <next-cont>)`. The returned IO node is a fresh heap allocation at rc=1 (the continuation allocated it via the backend's normal allocation path). The trampoline assigns it into `current` and proceeds. When the NEXT iteration replaces `current` again, the previous IO node — a fresh Pure / Effect / Bind / Par at rc=1 — has no remaining reference.

2. **Bind dispatch.** When `current.tag == IO_TAG_BIND`, the trampoline reads `field0` (inner IO) and `field1` (continuation closure), pushes the closure on `cont_stack`, and replaces `current = inner`. The Bind node itself is now unreferenced by the trampoline. The top-level `consume_io_tree` call in `cranelisp_run_io` does dec the Bind node — but only if the Bind node is still reachable from the top-level root pointer at that time. The dec is only correct for Bind nodes directly on the root's spine; a Bind node produced by a continuation mid-walk is NOT on the root's spine.

Combined effect: every continuation-produced node and every mid-walk Bind node is leaked. The rc=1 reference is never dec'd.

#### 3.5.3 The RC-balance rule

Under Decision 24, the extern `cranelisp_run_io(io_ptr)` is a consuming callee: it fully releases the IO tree handed in. The internal trampoline (`run_io_trampoline`) is a non-consuming helper — it walks the caller-owned tree read-only and dec's only the nodes IT allocates (continuation-produced intermediates). The extern wrapper handles the caller's tree via `consume_io_tree(io_ptr)` post-return.

Stated as an invariant:

- Caller-tree nodes (reachable from the original `io_ptr` by following Bind spines, Par branches, and Bind continuations) are owned by the top-level extern caller. They are released by one transitive `consume_io_tree(io_ptr)` call after the trampoline returns.
- Fresh nodes (allocated during the trampoline's walk by invoked continuations) are owned by the trampoline. They are released inline via `rc::dec_shallow_io` at the point of replacement, and a final shallow dec on the no-continuation return path.
- Continuations popped from `cont_stack` carry their parent Bind's freshness. Caller-tree closures are not dec'd by the trampoline (the tree walks them); fresh closures are `consume_closure`-dec'd after invocation (one-shot semantics).
- The trampoline returns a scalar `i64` — whatever payload the final Pure/Effect/Par yielded. If that payload is a heap pointer (e.g., a String from `Pure "hello"`), its rc is managed by the caller's scope, as for any heap-typed return value.

See §3.5.4 for the landed implementation of these rules.

#### 3.5.4 Fix shape — LANDED Sprint 57 Wave 3

The minimal fix is to dec the replaced node inside each loop iteration WHEN the trampoline owns it (not when the caller does). The earlier formulation of this section proposed unconditional shallow-dec at every replace site — that turned out to double-dec the caller's tree because `cranelisp_run_io` still needs to run `consume_io_tree(io_ptr)` post-return to release the top-level tree (closures embedded in caller-tree Binds are transitively released by that walk). The correct discipline is ownership-aware shallow dec: shallow-dec only the nodes and closures the trampoline itself produced.

**Landed implementation (Approach 4)**. `run_io_trampoline` is non-consuming of `io_ptr`:

- The trampoline tracks `current_is_fresh: bool` — initially false (the caller's tree). It flips to true after the first `call_continuation` (continuation returns a freshly-allocated IO node) and stays true for the rest of that subtree (stepping into a fresh Bind's inner descends to another fresh node because the continuation allocated the whole subtree).
- At every transition where `current` is replaced (Bind → inner, Pure/Effect/Par pop → continuation result), shallow-dec the old `current` via `rc::dec_shallow_io` **only if `current_is_fresh` was true**.
- `cont_stack` stores `(cont_ptr, cont_is_fresh)` — the freshness inherited from the enclosing Bind at push time. When popped, `call_continuation(cont_ptr, val, cont_is_fresh)` invokes the closure and, if `cont_is_fresh`, `drop::consume_closure(cont_ptr)` after the call to dec the continuation-produced closure. Caller-tree closures (is_fresh=false) are left alone; `consume_io_tree(io_ptr)` releases them post-return.
- `cranelisp_run_io(io_ptr)` wrapper: runs the trampoline, then `drop::consume_io_tree(io_ptr)` to transitively release the caller's tree.

**Ownership invariant**. Every IO ADT node is dec'd exactly once:
- Caller-tree nodes (Pure/Effect/Bind/Par and their cont closures) — released by the post-return `consume_io_tree(io_ptr)` transitive walk.
- Fresh nodes (allocated by a continuation during the trampoline's walk) — released inline by the trampoline's ownership-aware shallow dec.

The two sets are disjoint: caller-tree nodes are reachable only via `io_ptr`; fresh nodes are reachable only via `current` after the first `call_continuation`. There is no overlap, so no node gets double-dec'd, and none leaks.

**Primitives introduced in Wave 3**:

- `rc::dec_shallow_io(ptr)` — landed in `crates/cranelisp-runtime/src/drop.rs` (Decision 29). Atomically dec's the RC with Release ordering; on last-ref, emits an Acquire fence and deallocs the outer allocation only — no field walk. Safe on bare nullary tags.
- `call_continuation(cont_ptr, val, cont_is_fresh: bool)` — existing helper gains the freshness flag; when true, invokes `consume_closure(cont_ptr)` post-call.

**Rejected alternatives**:

- **Unconditional shallow-dec at every replace site** (the earlier §3.5.4 recommendation): double-dec's caller-tree closures because `consume_io_tree(io_ptr)` still walks them. The pre-landing analysis missed this because the two dec paths (inline + post-return) were not modelled together.
- **Track-and-drop** (keep a `Vec<i64>` of owned nodes and dec them at returns): allocates a Vec per trampoline invocation; the `current_is_fresh` bool is a simpler invariant.
- **Consume io_ptr at the trampoline level** (make `run_io_trampoline` consuming): cleanest in theory but changes the contract of a public Rust function, breaking all direct Rust-level callers (tests in `tests/io.rs` that call `run_io_trampoline` then `heap_dealloc(value)`). Keeping the post-return `consume_io_tree(io_ptr)` at the extern wrapper preserves backward compat.

**Freshness flag is viral within a subtree**. Once set to true (by a continuation returning a fresh node), freshness is inherited by Bind's inner (same continuation allocated both), Par's branches (same), and popped continuations (stored with their enclosing Bind's freshness). Freshness never flips back to false — a fresh subtree cannot contain a caller-tree node.

#### 3.5.5 Why `call_effect_thunk` is NOT affected

`call_effect_thunk` consumes its thunk pointer by design (the `Box<Box<dyn FnOnce>>` is taken out and dropped by the invocation). The Effect node's field0 (thunk ptr) is a raw Rust heap pointer, not a Cranelisp heap allocation with an RC header; it is outside the RC regime and does not interact with this fix. The Effect node's field1 (resource token) is a scalar Int; likewise no RC. Only the Effect node's OWN allocation (the wrapping heap slot with header + tag + thunk_ptr + token) is a Cranelisp heap object requiring an RC-dec — and that dec is the shallow one from §3.5.4.

#### 3.5.6 Par-specific note

`dispatch_par_branches` invokes `run_io_trampoline` recursively on each branch. Under the fix, each recursive trampoline call is itself RC-balanced — every intermediate node produced inside the branch walk is dec'd inline by the branch's own trampoline instance. The outer trampoline then allocates a fresh `results_buf` via `alloc_with_rc` to hold the scalar results; this buffer is passed to the continuation and eventually dec'd by whatever scope owns it (typically the continuation's `pop_scope_with_cleanup`). The outer Par node itself is shallow-dec'd at the point where `current` is replaced with the continuation's return (or at the `return results_ptr` path at the top-level).

#### 3.5.7 Testing — RC balance required, not just "tests pass"

Per `/arch` review condition 6, the acceptance criterion for this fix is NOT "IO platform tests pass" but a real RC-balance integration test. `/qa` owns the integration test; the backend/runtime-side unit test is:

```text
Setup:  record alloc_count / dealloc_count; build an IO tree with N
        intermediate Bind steps, each continuation producing a Pure node.
Act:    call cranelisp_run_io on the root.
Assert: (alloc_count - baseline) == (dealloc_count - baseline) + returned-heap.
        For scalar-payload programs, returned-heap == 0, so alloc delta == dealloc delta.
```

The existing `decision24_run_io_pure_rc_balanced` test (at `io.rs:554`) already exercises the no-continuation path and is balanced. The fix MUST enable analogous tests for bind-chains and par-chains to pass with the same alloc/dealloc invariant.

Pre-existing `test_run_io_deep_bind_chain` (1000 binds) is a natural stress test — under the fix, it must run with `(alloc_count - baseline) == (dealloc_count - baseline)` at the end. Today it leaks 1000+ intermediate nodes; post-fix, zero.

#### 3.5.8 Sketch comparison

The sketch (`sketch/src/intrinsics.rs` line ~157, `IoTask::run()`) has the same trampoline shape and **the same leak**. The sketch operates under a different overall convention (per-call borrowing in the sketch's codegen, per `sketch/docs/codegen.md`) which masked the leak in early Ring 4 prototyping — the sketch did not universally claim that extern entry points consume their heap arguments, so a leak of intermediate IO nodes was not obviously a convention violation. In the reimplementation under Decision 24, the leak IS a convention violation: the trampoline's extern entry commits to consuming, and the internal loop must honour that commitment. The divergence from sketch is: we fix the leak; the sketch did not.

Rationale for divergence: Decision 24's uniform consuming convention makes every extern's RC balance auditable (§3.3 is the audit table). An unaudited leak inside `cranelisp_run_io` breaks the audit's credibility. The sketch's per-call borrowing convention did not have the same audit story, so the sketch could tolerate the leak in practice. The reimplementation cannot.

#### 3.5.9 Cross-references

- `crates/cranelisp-runtime/src/io.rs` — the landed fix (non-consuming trampoline + `current_is_fresh` flag).
- `crates/cranelisp-runtime/src/drop.rs` — `consume_io_tree` (transitive) for caller-tree release; `consume_closure` for fresh-closure release; `dec_shallow_io` (Decision 29, Wave 3) for fresh IO-node release.
- `§3.3 Extern Consumption Audit` — the row for `cranelisp_run_io` that describes the top-level `consume_io_tree(io_ptr)` behaviour; remains accurate after the fix.
- `design/arch/CLAUDE.md` Decision 24 — the uniform consuming convention.
- `design/arch/CLAUDE.md` Decision 29 — `rc::dec_shallow_io` primitive introduced by the Wave 3 fix.
- `sprints/SPRINT.md` §"Architecture Review" condition 6 — the `/qa` RC-balance integration test (Wave 3 acceptance criterion).
- `repl/demos/…` — platform demos that exercise the trampoline (behaviour-preserving; memory behaviour fixed).

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

**Inline drop glue** (`emit_inline_drop_glue` on FnCompiler): Emitted directly into the caller's function body. Used by `pop_scope_with_cleanup` (the historical `dec_temporary_args` helper was deleted in Sprint 56 Step 2c — see §3 historical note). For each data constructor with heap-typed fields:
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

5. **All call sites use consuming convention (Decision 24)**: The caller incs heap-typed variable arguments before the call; the callee is responsible for dec'ing heap arguments it does not return. This applies uniformly to user functions, trait methods, sig-dispatch, data constructors, closure calls, inline builtins, Vec ops, and extern primitives.

6. **Extern primitives dec their own heap args**: A Rust-implemented extern that takes a heap pointer MUST dec that pointer before returning (unless it returns the pointer unchanged, i.e. ownership flows out through the return value, or it stores the pointer in a runtime-owned structure). The caller emits no post-call dec. See §3.3 Extern Consumption Audit.

7. **Data constructor fields are owned by the ADT**: The caller incs variable args (consuming convention); the constructor stores the field values into the new heap object and emits no explicit dec. Drop glue handles fields at destruction time when the ADT itself reaches rc=0.

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
| Calling convention | `cranelisp-backend/src/compiler/apply.rs` | `compile_consuming_arg_list`, `compile_arg_list` (plain args; consuming dispatch applies uniformly — no caller-side `dec_temporary_args`) |
| Scope cleanup | `cranelisp-backend/src/compiler/mod.rs` | `pop_scope_with_cleanup`, `return_var_in_scope`, `protect_return_value` |
| Inline drop glue | `cranelisp-backend/src/compiler/mod.rs` | `emit_inline_drop_glue`, `emit_field_decs` |
| Closure drop glue | `cranelisp-backend/src/compiler/control_flow.rs` | `build_closure_drop_glue`, `emit_closure_dec_inline` |
| Standalone ADT drop glue | `cranelisp-backend/src/compiler/vec_codegen.rs` | `build_adt_drop_glue_fn`, `emit_standalone_field_decs` |
| Vec element inc/dec | `cranelisp-backend/src/compiler/vec_codegen.rs` | `build_elem_inc_fn`, `build_elem_dec_fn` |
| Runtime allocator | `cranelisp-runtime/src/alloc.rs` | `alloc_with_rc`, `dealloc`, `heap_alloc`, `heap_dealloc` |
| Runtime Vec | `cranelisp-runtime/src/vec.rs` | `vec_new`, `vec_drop`, `vec_set_copy`, `vec_push_copy`, `vec_push_grow` |
| RC debug/trace | `cranelisp-runtime/src/rc.rs` | `rc_trace`, `rc_underflow_check`, `consume_shallow` |
| Runtime drop glue | `cranelisp-runtime/src/drop.rs` | `consume_slist`, `consume_sexp`, `consume_vec_of_string`, `consume_vec_with`, `consume_trace_call`, `consume_io_tree`, `consume_closure` |
| Intrinsic registration | `cranelisp-backend/src/jit.rs` | `register_intrinsics` |

## 8. Guidance for Ring 3 Implementers

### 8.1 Compiling a New Function

If you are generating a JIT function (e.g., a macro expansion helper, a trace wrapper):

1. **Parameters**: All user-defined functions are called with consuming convention — their parameters are owned. You MUST ensure `pop_scope_with_cleanup` runs at function exit with the return variable excluded.
2. **Calling any function (user, extern, trait method, data constructor, closure)**: Use `compile_consuming_arg_list` for the args. The callee is responsible for dec'ing anything it does not return.
3. **Writing an extern primitive in Rust**: Decide per heap-typed parameter — return unchanged (ownership flows out), retain/store (inc it into storage), or consume (dec before return). See §3.3 for the audit table.
4. **Allocating closures**: Call `build_closure_drop_glue` and store the result at `DROP_GLUE_PTR_OFFSET`. Inc heap-typed captures.

### 8.2 TCO and RC

Self-recursive tail calls currently do NOT emit scope cleanup before jumping to the loop header. This means heap-typed parameters from the previous iteration may leak. TCO+RC interaction is a known gap: the sketch's `emit_scope_cleanup_for_tco` was not carried forward to the reimplementation. Ring 3 should either implement this or document the restriction.

### 8.3 Common Pitfalls

- **Missing inc for variable args in consuming calls**: Causes use-after-free. The callee dec's the parameter at exit; without the caller's inc, the caller's binding is freed.
- **Missing dec in a new extern primitive**: Causes leaks. Under Decision 24 the extern owns its heap args — write the dec before return, or verify the arg flows out through the return value.
- **Extra dec in an existing extern primitive**: Causes use-after-free / double-free. Since Decision 24 the caller no longer emits `dec_temporary_args`; if an extern was previously dec'ing AND the caller was dec'ing, removing one without fixing the other flips the balance wrong.
- **Forgetting protect_return_value**: Causes use-after-free when the return value aliases a scope binding that gets dec'd by scope cleanup.
- **Captured variables treated as last-use**: Captured variables must NEVER skip inc at consuming call sites. The closure env needs its reference to remain valid.

## 9. Rejected Alternatives

### 9.1 Drop Function Side Table (Ring 1)

Ring 1 considered using a `HashMap<code_ptr, drop_fn>` for closure drop glue instead of embedding the pointer in the closure struct. This was rejected because:
- The side table requires locking or thread-local storage for lookups.
- Embedding the pointer costs 8 bytes per closure but makes closure dec a self-contained operation.
- Critical benefit: `emit_closure_dec_inline` can handle closures from any module without a global side table lookup.

### 9.2 Unified Calling Convention (ADOPTED — Sprint 56 Step 2c, Decision 24)

This is now the implemented convention — see §3. Historical context: it was initially rejected in favour of a split convention (Decision 20) because requiring builtins/externs to dec their own heap args was seen as adding overhead and complexity. In practice:

- Inline builtins operate on NeverHeap operands (Int/Bool/Float) — no dec required.
- Extern Rust primitives that take heap args are a finite, enumerable set (§3.3 audit). Adding a dec before return is a small, localised change per extern.
- The complexity saved on the caller side (no `dec_temporary_args`, no per-call-type classification, no `Option<dealloc_func_id>` conditional) dwarfs the per-extern cost. Every call site now compiles identically for RC management; the code path no longer branches on callee classification.

The split convention created a divergent compile path at every application site, exactly the kind of parallel structure Principle 7 (single source of truth) and Principle 11 (single pipeline) exist to prevent.

### 9.3 Deferred Reference Counting

Considered deferring RC operations to epoch boundaries (like Nim). Rejected because:
- Deterministic destruction is a language design goal.
- Deferred RC complicates reasoning about when side effects (via destructors/drop glue) occur.
- The inline atomic approach has acceptable overhead for the current single-threaded model.
