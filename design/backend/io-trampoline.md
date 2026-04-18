# IO Trampoline Design

Sprint 16 I2 — codegen and runtime for deferred IO execution.

## Overview

The IO model is a deferred-execution system. When user code calls `(print "hello")`, no side effect occurs. Instead, an `Effect` node is allocated on the heap. When user code calls `(bind io cont)`, a `Bind` node links the IO computation with a continuation closure. The resulting IO tree is forced by the runtime trampoline, which walks the tree iteratively with an explicit continuation stack.

This document covers:
1. IO node heap layout and allocation (backend codegen responsibility)
2. `bind` inline primitive codegen (backend responsibility)
3. Drop glue for IO nodes (backend responsibility)
4. Trampoline interpreter (runtime responsibility, `cranelisp-runtime`)
5. Effect thunk mechanics (platform/runtime boundary)
6. Integration points (batch entry and REPL eval, `/int` responsibility)

## 1. IO Node Layout

IO nodes are heap-allocated ADTs participating in the standard RC system. They use the same `HeapHeader` as all other heap objects (see `ring2-rc.md` §1):

```
HeapHeader: [alloc_size: i64 (offset 0) | rc: i64 (offset 8)]
```

Three node types, discriminated by tag at offset 16:

### 1.1 Pure Node (tag = 0)

A completed value. Created by `(Pure x)` — the `Pure` constructor, which is an ordinary ADT data constructor.

```
[header(16) | tag=0 (8) | value (8)]
 offset 0     offset 16   offset 24
 total: 32 bytes (header) + 16 bytes (payload) = 32 bytes
 alloc_size = 32
```

- `value` (offset 24): the completed value, any Cranelisp type as i64.

Allocation: standard ADT data constructor path. `(Pure 42)` allocates 16 bytes of payload via `emit_alloc(16)` (which adds the 16-byte header to get 32 total), stores tag 0 at offset 16, stores the value at offset 24. Uses the data constructor calling convention (see `ring2-rc.md` §3.3): no RC adjustments at the call site; drop glue handles field cleanup.

### 1.2 Effect Node (tag = 1)

A deferred side effect containing an opaque thunk pointer. Created by platform functions via `CLIO::effect()`.

```
[header(16) | tag=1 (8) | thunk_ptr (8) | resource_token (8)]
 offset 0     offset 16   offset 24       offset 32
 total: 40 bytes
 alloc_size = 40
```

- `thunk_ptr` (offset 24): double-boxed Rust closure pointer (`Box<Box<dyn FnOnce() -> i64>>`).
- `resource_token` (offset 32): i64 for parallel scheduling (0 = unrestricted). Not used in Sprint 16 (no `Par` node), but included in the layout from the start to avoid a layout-breaking change when auto-scheduling lands.

Allocation: Effect nodes are allocated by platform DLL code using the host allocator callback, not by JIT-compiled Cranelisp code. The platform crate's `CLIO::effect()` method calls `get_global_alloc()(24)` to allocate 24 bytes of payload (3 fields x 8 bytes), stores the tag, thunk pointer, and resource token. The host allocator adds the 16-byte header, so total allocation is 40 bytes.

**Critical**: The thunk pointer is NOT a Cranelisp heap value. It is a raw Rust `Box` pointer. The RC system does not manage it. Ownership semantics are different from normal fields (see §3.2 and §4).

### 1.3 Bind Node (tag = 2)

A chain linking an inner IO computation with a continuation closure. Created by the `bind` inline primitive.

```
[header(16) | tag=2 (8) | inner_io (8) | cont (8)]
 offset 0     offset 16   offset 24      offset 32
 total: 40 bytes
 alloc_size = 40
```

- `inner_io` (offset 24): pointer to another IO node (Pure, Effect, or Bind).
- `cont` (offset 32): pointer to a Cranelisp closure `(Fn [a] (IO b))`.

Allocation: inline by the `bind` primitive codegen (see §2).

**Bind is internal**: the typechecker marks Bind's `ConstructorInfo` with `internal: true`. User code cannot construct or pattern-match on Bind. Only the `bind` inline primitive creates Bind nodes, and only the trampoline reads them.

### 1.4 Tag Constants

Defined in `cranelisp-platform` (shared between platform DLLs and runtime):

```rust
pub const IO_TAG_PURE: i64 = 0;
pub const IO_TAG_EFFECT: i64 = 1;
pub const IO_TAG_BIND: i64 = 2;
// IO_TAG_PAR (tag=3) deferred to auto-scheduling sprint
```

These match the ADT constructor definition order in the compiler-seeded IO type. The backend uses these constants when emitting `bind` codegen; the runtime uses them in the trampoline dispatch.

## 2. `bind` Codegen

`bind` is an inline primitive: `bind :: (Fn [(IO a) (Fn [a] (IO b))] (IO b))`. It produces no function call. The backend emits IR directly into the caller's function body.

### 2.1 IR Sequence

Given compiled argument values `l` (inner IO) and `r` (continuation closure):

```
// 1. Allocate Bind node: 24 bytes payload (tag + inner_io + cont)
ptr = call emit_alloc(24)

// 2. Store fields
store tag=2    at ptr + 16    // TAG_OFFSET
store l        at ptr + 24    // inner_io field
store r        at ptr + 32    // cont field

// 3. RC: inc both arguments
emit_rc_inc(l)    // inner IO tree gains a new reference from the Bind node
emit_rc_inc(r)    // continuation closure gains a new reference from the Bind node

// 4. Return ptr
```

### 2.2 Why Both Arguments Are Inc'd

The Bind node holds references to both `l` (inner IO) and `r` (continuation). These are independent of whatever references the caller already holds. Without inc:

- If `l` was a temporary (rc=1 from its allocation), and the caller drops it at scope exit, the inner IO tree could be freed while the Bind node still references it.
- If `r` was a named variable (rc=1 from its scope binding), and scope cleanup dec's it, the continuation closure could be freed while the Bind node still holds a pointer.

Both incs ensure the Bind node's references are accounted for. The Bind node's drop glue (§3) will dec both fields when the Bind node itself is freed.

### 2.3 Calling Convention

Under Decision 24 (Sprint 56 Step 2c), `bind` uses the **uniform consuming convention**. The caller compiles arguments via `compile_consuming_arg_list`, which incs heap-typed Var args so the Var's scope retains its reference; temporary args transfer directly (no caller action). The Bind node owns its two field references.

**Historical note**: prior to Decision 24, `bind` was classified as a borrowing inline primitive — the caller used `compile_arg_list` (no per-arg inc) and emitted a caller-side `dec_temporary_args` after the IR. The `bind` IR inc'd both args explicitly because it was nominally borrowing. The consuming convention subsumes that behaviour: the caller's inc for Var args is performed once by `compile_consuming_arg_list`, and the explicit inc inside the `bind` IR is NO LONGER needed — the Bind node's field-store now inherits ownership from the consuming arg list directly. See `compile_bind_inline` in `crates/cranelisp-backend/src/compiler/apply.rs` — the "no explicit inc needed" comment reflects the Decision 24 state.

- **Variable argument `l`** (e.g., `(bind some-io cont)`): `compile_consuming_arg_list` incs `l`. The Bind node stores the inc'd reference; the Var's scope retains its original reference. Correct.
- **Temporary argument `l`** (e.g., `(bind (print "hello") cont)`): no inc from the caller (it is not a Var). The temporary's rc=1 transfers directly into the Bind node's field. Correct.

The same reasoning applies symmetrically to `r`.

## 3. Drop Glue for IO Nodes

IO nodes are ADTs, so their drop glue follows the standard ADT drop glue mechanism (see `ring2-rc.md` §4.2). However, each constructor has different field cleanup requirements.

### 3.1 Pure Drop Glue

When a Pure node reaches rc=0:
1. Load `value` from offset 24.
2. If `value`'s type is heap-typed, emit `rc_dec` on it (guarded for Mixed types).
3. Free the Pure node.

In practice, Pure nodes carry the inner value's type information via `expr_types`. The type of the `value` field is the type parameter `a` in `IO a`. At codegen time, the exact inner type may not be statically known at the dec site (the dec may come from generic scope cleanup). The drop glue must handle this:

- If the IO type is `IO Int` or `IO Bool`: the value field is `NeverHeap`, no dec needed.
- If the IO type is `IO String` or `IO (Fn ...)`: the value field is `AlwaysHeap`, unconditional dec.
- If the IO type is `IO (Option T)`: the value field is `Mixed`, guarded dec.
- If the IO type parameter is unresolved (polymorphic `IO a`): treat as `Mixed` (conservative).

### 3.2 Effect Drop Glue

When an Effect node reaches rc=0:
1. The `thunk_ptr` field is **NOT dec'd**. It is not a Cranelisp heap value — it is a raw `Box<Box<dyn FnOnce() -> i64>>` pointer owned by Rust.
2. The `resource_token` field is a plain i64 — no cleanup needed.
3. Free the Effect node.

**The thunk's lifetime is managed by the trampoline, not by RC.** When the trampoline processes an Effect node, it calls `call_effect_thunk(thunk_ptr)`, which does `Box::from_raw(thunk_ptr)` to reclaim ownership and invoke the closure. This consumes the thunk. If an Effect node is dropped without being forced (e.g., `(if cond (print "a") (print "b"))` — the unchosen branch's Effect is dropped), the thunk is leaked. This is a known, acceptable trade-off: thunk leaks are bounded by the program's IO tree structure, and adding a Rust-side destructor would require the drop glue to call into a Rust function with knowledge of the double-box layout, which crosses the backend/platform boundary inappropriately.

**Sprint 16 note**: For the initial implementation, this leak is acceptable. If measurement shows it matters, a future sprint can add a `drop_effect_thunk` extern that the Effect drop glue calls. This is an additive change (new extern + new drop glue branch) that does not affect the existing architecture.

### 3.3 Bind Drop Glue

When a Bind node reaches rc=0:
1. Load `inner_io` from offset 24. Emit `rc_dec` (guarded for Mixed — the inner IO could be a bare nullary tag in theory, though IO nodes are always heap-allocated in practice; the guard is for safety).
2. Load `cont` from offset 32. Emit `emit_closure_dec_inline` — the continuation is a closure, so its drop path follows the standard closure drop glue protocol (load `drop_glue_ptr` from closure offset 24, call if non-zero, then dealloc).
3. Free the Bind node.

### 3.4 Drop Glue Generation Strategy

IO is a standard ADT with three data constructors. The existing ADT inline drop glue mechanism (`emit_inline_drop_glue`) handles it: load the tag, branch to the correct constructor's cleanup block.

However, the Effect constructor's thunk field requires special handling (skip dec). This is implemented by classifying the `thunk_ptr` field as `NeverHeap` in the type system — the field type is opaque (i64 from the compiler's perspective), not a Cranelisp heap type. The `resource_token` field is also `NeverHeap` (plain i64). This means the existing drop glue generation produces correct code for Effect nodes without any special-casing: it simply finds no heap-typed fields and emits no dec operations.

For Pure: the `value` field's heap category depends on the IO type parameter.
For Bind: `inner_io` is `AlwaysHeap` (it is always a pointer to an IO node), `cont` is `AlwaysHeap` (it is always a closure pointer).

## 4. Effect Thunk Mechanics

### 4.1 Double-Boxing

Platform functions create effect thunks by double-boxing a Rust closure:

```rust
let thunk: Box<Box<dyn FnOnce() -> i64>> =
    Box::new(Box::new(move || { /* side effect */ result }));
let thunk_ptr = Box::into_raw(thunk) as i64;
```

The inner `Box<dyn FnOnce() -> i64>` is a fat pointer (16 bytes on 64-bit). The outer `Box` wraps it to produce a thin pointer (8 bytes) that fits in a single i64 field.

### 4.2 Thunk Consumption

The trampoline calls `call_effect_thunk` to execute and reclaim the thunk:

```rust
pub unsafe fn call_effect_thunk(thunk_ptr: i64) -> i64 {
    let thunk: Box<Box<dyn FnOnce() -> i64>> =
        Box::from_raw(thunk_ptr as *mut Box<dyn FnOnce() -> i64>);
    (*thunk)()
}
```

`Box::from_raw` reclaims ownership of the outer box. Dereferencing and calling the inner `FnOnce` consumes it. After `call_effect_thunk` returns, both boxes are dropped. The thunk is consumed exactly once.

### 4.3 Captured Value RC

Platform functions that capture Cranelisp heap values (e.g., the string argument to `print`) must ensure those values stay alive until the thunk executes. The `cranelisp-platform` crate provides `CLOwned<T>` for this:

```rust
pub extern "C" fn print_string(s: CLString) -> CLIO<CLInt> {
    let owned = s.own();  // CLOwned::new(s) — calls inc_rc
    CLIO::effect(move || {
        println!("{}", owned.as_str());
        // owned dropped here — calls dec_rc
        CLInt::from(0i64)
    })
}
```

`CLOwned::new(val)` calls `val.inc_rc()` on creation. When the closure executes, `owned` is moved into the closure body. When the closure's Rust `Drop` runs (after the thunk is consumed), `CLOwned::drop` calls `val.dec_rc()`. This ensures the captured string is live for the entire thunk lifetime.

### 4.4 Single-Execution Invariant

Each Effect node's thunk MUST be executed at most once. The `FnOnce` trait enforces this at the Rust level. The backend must not emit code that could force the same Effect node twice. This is naturally satisfied because:

1. The trampoline processes each node once and advances to the next.
2. IO trees are structurally trees (not DAGs with shared nodes) — each `bind` creates a fresh Bind node pointing to its arguments.
3. Bind nodes cannot be user-constructed, so users cannot create sharing in the IO tree.

If an Effect node is dropped without being forced (unchosen branch), its thunk is not executed and is leaked (see §3.2).

## 5. Trampoline Architecture

The trampoline lives in `cranelisp-runtime`. It is the `cranelisp_run_io` extern function, called from JIT-compiled code (batch entry) or from the Rust REPL loop (direct call).

### 5.1 Algorithm

```rust
pub extern "C" fn cranelisp_run_io(io_ptr: i64) -> i64 {
    let mut cont_stack: Vec<i64> = Vec::new();  // stack of continuation closure pointers
    let mut current: i64 = io_ptr;

    loop {
        let tag = unsafe { *(current as *const i64) };  // offset 16 from base... see note below
        match tag {
            IO_TAG_PURE => {
                let val = unsafe { *((current as *const i64).add(1)) };
                match cont_stack.pop() {
                    Some(cont_ptr) => {
                        // Call continuation: code_ptr(env_ptr, val) -> IO ptr
                        let code_ptr = unsafe { *(cont_ptr as *const i64) };
                        let call: extern "C" fn(i64, i64) -> i64 =
                            unsafe { transmute(code_ptr as *const ()) };
                        current = call(cont_ptr, val);
                    }
                    None => return val,
                }
            }
            IO_TAG_EFFECT => {
                let thunk_ptr = unsafe { *((current as *const i64).add(1)) };
                let result = unsafe { call_effect_thunk(thunk_ptr) };
                match cont_stack.pop() {
                    Some(cont_ptr) => {
                        let code_ptr = unsafe { *(cont_ptr as *const i64) };
                        let call: extern "C" fn(i64, i64) -> i64 =
                            unsafe { transmute(code_ptr as *const ()) };
                        current = call(cont_ptr, result);
                    }
                    None => return result,
                }
            }
            IO_TAG_BIND => {
                let inner = unsafe { *((current as *const i64).add(1)) };
                let cont = unsafe { *((current as *const i64).add(2)) };
                cont_stack.push(cont);
                current = inner;
            }
            _ => panic!("cranelisp_run_io: unknown IO tag {}", tag),
        }
    }
}
```

**Pointer convention note**: The pseudocode above reads from the payload directly (tag at `ptr.add(0)`, fields at `ptr.add(1)`, etc.). This assumes the pointer passed to the trampoline is a **payload pointer** (pointing past the header). In the reimplementation's base-pointer ABI (arch decision 10), the base pointer points to offset 0 (where `alloc_size` lives). The trampoline must add the header size (16 bytes) to get to the payload:

```rust
let payload = io_ptr + 16;  // skip HeapHeader
let tag = unsafe { *(payload as *const i64) };
let field_0 = unsafe { *((payload as *const i64).add(1)) };
let field_1 = unsafe { *((payload as *const i64).add(2)) };
```

Alternatively, the trampoline can use the ADT field offset constants (`TAG_OFFSET = 16`, `FIELDS_START = 24`):

```rust
let tag = unsafe { *((io_ptr + TAG_OFFSET) as *const i64) };
let field_0 = unsafe { *((io_ptr + FIELDS_START) as *const i64) };
let field_1 = unsafe { *((io_ptr + FIELDS_START + 8) as *const i64) };
```

The second form is preferred — it uses the same constants as the backend codegen, ensuring consistency.

### 5.2 Properties

- **Iterative**: no recursive calls. Stack depth is O(1) in the Rust call stack.
- **Continuation stack**: `Vec<i64>` grows proportionally to the depth of left-nested `bind` chains, which corresponds to the number of `bind!`/`do` steps in the program. This is typically small (tens to hundreds).
- **No RC operations**: The trampoline reads IO node fields by raw pointer. It does not inc or dec IO nodes. The IO tree must stay live during the trampoline run (see §6).
- **Effect dispatch**: Effects execute inline in the trampoline loop. The `call_effect_thunk` function reclaims and calls the thunk, performing the side effect.
- **Continuation calling**: When a continuation is called, it produces a new IO tree (the continuation closure is a `(Fn [a] (IO b))`). The trampoline replaces `current` with this new tree and continues the loop.

### 5.3 Continuation Representation

Continuations on the stack are Cranelisp closure pointers. A continuation closure has the standard `HeapClosure` layout:

```
[header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]
```

When calling a continuation, the trampoline:
1. Loads `code_ptr` from the closure's offset 16 (CODE_PTR_OFFSET).
2. Calls `code_ptr(closure_ptr, val)` — passing the closure itself as the first argument (the environment pointer) and the Pure/Effect result as the second argument.
3. The return value is a new IO tree pointer, which becomes `current`.

The trampoline does not dec the continuation closure after calling it. The continuation was inc'd when stored in the Bind node (§2.1). The Bind node's drop glue will dec it when the Bind node is freed. Since the trampoline does not touch RC at all, the continuation stays alive as long as the Bind node (and therefore the IO tree) stays alive.

## 6. IO Tree Liveness Invariant

**The IO tree must remain live (RC > 0) for the duration of the trampoline run.** The trampoline reads fields by raw pointer without participating in RC. If the tree were freed mid-trampoline, the trampoline would read freed memory.

### 6.1 Batch Mode

In batch mode, `main()` returns an IO tree pointer. The integration layer (`/int`) calls `cranelisp_run_io(result)`. The `result` is the return value of the JIT-compiled `main` function. It is live on the Rust stack (or in a register) for the duration of the `cranelisp_run_io` call. No scope cleanup runs between `main()` returning and the trampoline completing, so the tree remains live.

After the trampoline returns, the batch program exits. The IO tree is not explicitly freed — process exit reclaims all memory.

### 6.2 REPL Mode

In REPL mode, the eval function returns an IO tree pointer. The REPL loop detects the `IO` type, calls `IoTask::from_raw(result).run()` (the Rust-side entry to the trampoline), then formats the inner result for display. The `result` value is live in the REPL loop's local variable for the duration of the trampoline call.

After the trampoline returns, the REPL displays the result. The IO tree is then subject to normal cleanup when the REPL loop iteration ends. The IO tree's RC reaches 0 and drop glue runs, freeing the tree nodes. This is safe because the trampoline has already completed.

### 6.3 Intermediate IO Trees

When the trampoline calls a continuation, the continuation produces a *new* IO tree. This new tree is a return value from a JIT-compiled function and has rc=1 (freshly allocated). It becomes `current` in the trampoline loop.

The *old* Bind node (whose continuation just ran) is still alive — it is part of the original IO tree, which is still referenced by the top-level `result` variable. The old Bind node references the continuation and the inner IO, both of which may still be needed (the continuation just ran, but the inner IO was already processed). None of these are freed during the trampoline run because the top-level reference to the tree root keeps the entire tree alive.

After the trampoline finishes and the top-level reference is dropped, the entire tree is freed via cascading drop glue: root Bind dec's its inner and cont, which may cascade to nested Bind nodes, which dec their inners and conts, eventually reaching Pure and Effect leaf nodes.

## 7. Platform Dispatch

The trampoline does not know which platform function an Effect represents. Effect thunks are opaque: they capture the platform function pointer and its arguments inside the closure.

### 7.1 How Effects Are Created

When user code calls `(print "hello")`:

1. The compiler resolves `print` as a platform function with `PrimitiveKind::PlatformEffect`.
2. Codegen emits a call to the platform function's native symbol (e.g., `cranelisp_print`), passing the arguments per the C ABI.
3. The platform function (`print_string` in `cranelisp-stdio`) receives the arguments, creates a `CLOwned` handle for any heap captures, and returns `CLIO::effect(closure)`.
4. `CLIO::effect()` double-boxes the closure, allocates an Effect node via the host allocator, stores tag=1, thunk_ptr, and resource_token=0.
5. The Effect node pointer (as i64) is returned to the JIT-compiled code.

### 7.2 How Effects Are Executed

When the trampoline encounters an Effect node:

1. Loads `thunk_ptr` from offset 24.
2. Calls `call_effect_thunk(thunk_ptr)`.
3. Inside `call_effect_thunk`: `Box::from_raw` reclaims the outer box, dereferences to get the `FnOnce`, calls it.
4. The closure body executes the actual side effect (e.g., `println!`).
5. The closure returns the result value as i64.
6. `call_effect_thunk` returns the result to the trampoline.
7. The trampoline proceeds as with Pure (pop continuation or return).

### 7.3 Platform Function Registration

Platform functions are registered in the JIT module as extern symbols. The `PlatformManifest` provides the mapping from Cranelisp names (e.g., `"print"`) to native symbol names (e.g., `"cranelisp_print"`) with type signatures and scheduling class. The integration layer (`/int`) loads the platform DLL, reads the manifest, and registers each function in the typechecker (as `PrimitiveKind::PlatformEffect`) and the JIT (as an extern symbol).

## 8. `cranelisp_run_io` Extern

### 8.1 Signature

```rust
/// Force an IO task tree to completion.
///
/// Takes a base pointer to a heap-allocated IO node (Pure/Effect/Bind).
/// Returns the final result value (i64).
///
/// # Safety
/// `io_ptr` must be a valid base pointer to an IO node with rc > 0.
/// The IO tree must remain live for the duration of this call.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_run_io(io_ptr: i64) -> i64
```

### 8.2 Crate Location

Lives in `cranelisp-runtime`. Registered as a JIT builder symbol so it can be called from JIT-compiled code (batch entry stub) or called directly from Rust (REPL loop).

### 8.3 Dependencies

- `cranelisp-platform::call_effect_thunk` — to execute effect thunks.
- `cranelisp-platform::{IO_TAG_PURE, IO_TAG_EFFECT, IO_TAG_BIND}` — tag constants.
- ADT layout constants from `cranelisp-types` or `cranelisp-backend` — `TAG_OFFSET`, `FIELDS_START`.

The runtime crate already depends on `cranelisp-platform` (for `call_effect_thunk`). The layout constants should be in `cranelisp-types` (data-only, stable) since they are shared between the backend (codegen) and the runtime (trampoline).

### 8.4 Batch Invocation

The integration layer compiles `main()`, checks its return type. If it is `IO _`:

```rust
let result = main_fn();
let inner_val = cranelisp_run_io(result);
// Use inner_val as exit code (if Int) or default 0
```

### 8.5 REPL Invocation

The REPL loop compiles and executes an expression. If the result type is `IO _`:

```rust
let result = eval_fn();
if matches!(&resolved_type, Type::ADT(name, _) if name.as_ref() == "IO") {
    let inner_val = unsafe { cranelisp_run_io(result) };
    // Display inner_val with inner type
}
```

## 9. Rejected Alternatives

### 9.1 Recursive Interpreter

A recursive `run_io` that directly recurses on Bind nodes would overflow the Rust call stack for deep IO chains (e.g., an IO loop reading 100K lines). The spec (10.8.2) explicitly requires O(1) call stack depth. The iterative trampoline with explicit continuation stack satisfies this.

### 9.2 Trampoline Owns RC

An alternative where the trampoline inc's nodes before processing and dec's after would add RC overhead on every trampoline iteration. Since the IO tree is already held alive by the caller's reference, trampoline-level RC is unnecessary. The current design (trampoline does not touch RC) is simpler and faster.

### 9.3 Effect Thunk as Cranelisp Closure

Instead of a Rust `Box<Box<dyn FnOnce()>>`, effect thunks could be Cranelisp closures. This would integrate with RC naturally but would require platform DLLs to construct Cranelisp closures from C code, which is fragile and couples platform authors to the HeapClosure layout. The double-boxed Rust closure approach keeps platform code in safe Rust (via `CLIO::effect()`) and is well-isolated.

### 9.4 Separate Drop Path for Effect Thunks

Adding a `drop_effect_thunk` extern that the Effect node's drop glue calls (to properly free leaked thunks from unchosen branches) was considered but deferred. The leak is bounded (one thunk per unchosen branch, freed at process exit), and adding the extern adds a cross-crate dependency from the drop glue (emitted by backend) to a runtime function. This can be added later as an additive change if measurement shows the leak matters.

## 10. Summary of Responsibilities

| Component | Responsibility |
|---|---|
| `/typecheck` | Seeds IO ADT (Pure/Effect/Bind) in `primitives` module. Marks Bind as internal. Types `bind` as inline primitive. |
| `/backend` | Emits `bind` codegen (allocate Bind node, store fields, inc both args). Generates ADT drop glue for IO nodes. Registers `cranelisp_run_io` as a JIT symbol. |
| `/platform` | Provides `CLIO::effect()`, `call_effect_thunk()`, IO tag constants, `CLOwned<T>` for capture RC. |
| `cranelisp-runtime` | Implements `cranelisp_run_io` — the iterative trampoline. |
| `/int` | Calls trampoline at batch entry and REPL eval. Detects `IO` return type. Platform DLL loading. |
| `/stdlib` | Provides `pure` (wraps in Pure), `do`/`bind!` macros (expand to `bind` calls). |

## 11. Sketch Reference

| Sketch file | What it demonstrates |
|---|---|
| `sketch/src/intrinsics.rs` | `IoTask`, `Continuation`, `cranelisp_run_io`, trampoline loop with `cont_stack` |
| `sketch/src/codegen/primitives.rs:163-179` | `bind` codegen: allocate 24 bytes, store tag/inner/cont, inc both args |
| `sketch/cranelisp-platform/src/lib.rs:233-296` | `CLIO::pure()`, `CLIO::effect()`, `call_effect_thunk()`, double-boxing |
| `sketch/platforms/stdio/src/lib.rs` | `print_string` using `s.own()` for capture RC, `CLIO::effect(move \|\| ...)` |
| `sketch/src/repl/input.rs:796-810` | REPL IO detection and trampoline invocation |
| `sketch/src/jit.rs:1227-1236` | Batch IO detection and trampoline invocation |
