# IO Trampoline Design

Sprint 16 I2 — codegen and runtime for deferred IO execution.

## Overview

The IO model is a deferred-execution system. When user code calls `(print "hello")`, no side effect occurs. Instead, an `Effect` node is allocated on the heap. When user code calls `(bind io cont)`, a `Bind` node links the IO computation with a continuation closure. The resulting IO tree is forced by the runtime trampoline, which walks the tree iteratively with an explicit continuation stack.

This document covers:
1. IO node heap layout and allocation (backend codegen responsibility)
2. `bind` inline primitive codegen (backend responsibility)
3. Drop glue for IO nodes (backend responsibility)
4. Trampoline interpreter (runtime responsibility, `cranelisp-intrinsics`)
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

The trampoline lives in `cranelisp-intrinsics` (the backend-emitted runtime library; former `cranelisp-runtime`, split at D43). It is the `cranelisp_run_io` extern function, called from JIT-compiled code (batch entry) or from the Rust REPL loop (direct call). See `design/intrinsics/reactor.md`.

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

Lives in `cranelisp-intrinsics` (the backend-emitted runtime library; former `cranelisp-runtime`, split at D43). Registered as a JIT builder symbol so it can be called from JIT-compiled code (batch entry stub) or called directly from Rust (REPL loop).

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
| `cranelisp-intrinsics` | Implements `cranelisp_run_io` — the iterative trampoline (backend-emitted runtime library). |
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

## 12. Poll-shape Effect node construction — the backend poll-construction arm (S94, effect-concurrency slice 2)

Sprint 94 completes effect-concurrency slice 2: real poll-shape platform effect
*nodes* flow through the reactor's `EffectPoll` await. The backend's half is a
single, additive **poll-construction arm** at the effect site. This section is the
`/dev` design for that arm. It builds against the **ratified backend↔intrinsics
poll-shape Effect-node seam** (`design/arch/effect-concurrency.md` §13 "S94 R1" +
Appendix B §"the ratified backend↔intrinsics poll-shape Effect-node seam"; ABI-field
consequence in `design/arch/platform-interface.md` §6.8) — that seam is the contract,
this section is the codegen that realizes it. It reuses the closure-construction
codegen of `design/backend/ring2-rc.md` / `lambda.rs` (Principle 7 reuse) and the
GOT-indirect dispatch mechanism of §7 here + `apply.rs::emit_got_indirect_call_via_data_id`.

### 12.1 What is new vs. the blocking path (and what is byte-identical)

The blocking `IO_TAG_EFFECT` path (§1.2, §7) is **untouched** (arch R3,
byte-identical-when-off). It works by *calling* the platform DLL fn at the effect
site (`compile_direct_call` → `emit_got_indirect_call_via_data_id`); the DLL fn
allocates the Effect node, double-boxes its thunk, and returns the node pointer,
which the backend then fn-name-stamps (§7 / `apply.rs::stamp_platform_fn_name`). Every
real platform today is blocking, so this is every effect node constructed today.

The poll-shape arm is structurally different — it **does not call the platform fn**:

| Aspect | Blocking arm (`IO_TAG_EFFECT`, unchanged) | Poll-construction arm (`IO_TAG_EFFECT_POLL`, new) |
|---|---|---|
| Effect fn role | **called** at the site; returns the node | **loaded** from the GOT; baked as the node's `code_ptr`; called later by the trampoline's `EffectPoll::poll` |
| Who builds the node | the platform DLL (host-opaque thunk) | the **backend**, in-process, as a host-built state-closure |
| Node field-0 | thunk_ptr (a `Box<Box<dyn FnOnce>>`) | a **state-closure** pointer in the standard `HeapClosure` layout |
| Args | passed in the C-ABI call | **marshaled as closure captures** (poll takes only `(state, host, waker)`) |
| Result | returned by the call | written by the poll-fn into a **reserved result slot** in the closure env; read generically by `EffectPoll` on `Poll::Ready` |
| `HostCtx`/`Waker` | n/a | supplied by the **trampoline** at poll time, never at the backend site |

**Keying — no cargo feature (arch R3).** The arm is selected on the effect's
**declared shape**, read from the symbol table as `DefKind::PlatformEffect.poll_shape:
bool` (a `cranelisp-types` field; FIXME 0457): `poll_shape == true` ⇒ the
poll-construction arm, `poll_shape == false` ⇒ the unchanged blocking arm. The
`poll_shape` discriminator is **derived at platform-load time** (`poll_shape =
(descriptor.blocking == 0)`) and stamped onto the `DefKind`; the full
`ConcurrencyDescriptor` is deliberately **NOT carried on the symbol table** (it stays
`concurrency`-gated, off the frozen `cranelisp-types` edge — see
`effect-concurrency.md` §13 "S94 R1" + `platform-interface.md` §6.8). The backend
therefore never reads `ConcurrencyDescriptor` at the dispatch site; it reads only the
boolean `poll_shape`. Because poll-shape effects only exist in a `concurrency`-built
toolchain (the v7 `declare_platform!` poll-emission is itself feature-gated), the new
arm is *reachable* only when concurrency is in play; with a stock (blocking-only)
platform set every effect has `poll_shape == false`, so **no `IO_TAG_EFFECT_POLL`
node is ever constructed** and the emitted code is byte-identical to today's. The
backend needs **no `#[cfg]`** — the dual path is a data-driven branch on the
`poll_shape` field, not a compile-time fork (Principle 11 — mode by parameter, not by
build flag).

### 12.2 `IO_TAG_EFFECT_POLL` node layout

> **v9 note (S97, ctx-vtable handle model; §17).** The node keeps the v8 shape **unchanged** —
> no growth, no `role` field, no descriptor region (the intermediate descriptor-cut design that
> would have repurposed the two admission slots into `role`@32 + a `desc_out` `ResourceDesc`
> region @40 is **RETIRED** — §17.7). Under the ctx-vtable model the platform poll-fn computes
> the token from its handle and calls the trampoline-owned `ctx` vtable itself, so **nothing
> scheduling-related is baked on the node**; the two admission slots are inert. The v8
> `(token, capacity)`-from-positional-args bake is **deleted** (§14 superseded). The env layout
> below is **unchanged in shape** (result @ env+0, args follow) but the args are now
> `arg_vals[0..]` directly — no leading-pair peel. See §17 for the (deletion-only) v9 delta.

A new IO tag, `IO_TAG_EFFECT_POLL` (next free tag — `IO_TAG_PAR` is 3, so this is **4**;
the constant joins the others in `cranelisp-platform` / `cranelisp-types` per §1.4,
gated with the `concurrency` layout contracts). The node is deliberately *thin*: it
holds the tag plus a single pointer to the host-built state-closure, mirroring how the
Effect node holds a single thunk pointer.

```
Base pointer →
  +0   alloc_size: i64   (= 32)
  +8   rc: i64           (initial 1, atomic)
  +16  tag: i64          (= IO_TAG_EFFECT_POLL = 4)
  +24  state_closure: i64 (pointer to the state-closure, below)

Total allocation: 32 bytes (16 header + 16 payload)
```

The **state-closure** is an ordinary heap closure in the standard layout
(Decision 11; `lambda.rs`, `ring2-rc.md`), so it inherits RC + drop for free:

```
Base pointer →
  +0   alloc_size: i64
  +8   rc: i64
  +16  code_ptr: i64        (= the GOT-loaded poll-fn; PollFn ABI)
  +24  drop_glue_ptr: i64   (state-teardown glue — see §12.5)
  +32  env_0: result_slot: i64   (poll-fn writes its i64 result here)
  +40  env_1: arg_0 : i64        (marshaled effect arg 0)
  +48  env_2: arg_1 : i64        (marshaled effect arg 1)
  ...                            (one slot per effect arg)
  +N   scratch...                (optional leaf-private scratch)
```

This is exactly the ratified closure-env model (§13 decision 1): `code_ptr` = the
poll-fn, `drop_glue_ptr` = state teardown, `env` = result-slot + i64 args + scratch.
It adds **no new platform-DLL type** — the closure layout is an in-process host
convention, not a DLL-ABI struct (arch rejected a `#[repr(C)] PollDescriptor` for
exactly this reason). The result slot is placed **first in the env** (offset 32) so its
location is a fixed, descriptor-independent offset both the backend and `EffectPoll`
agree on; the args follow. (Result-slot *placement* — first-env-slot vs. a baked node
field — is the host↔intrinsics interior convention the seam left to /design backend +
int; **first-env-slot at offset 32 is the recommendation**: it needs no extra node
field, and `EffectPoll` already holds the state pointer, so `state + 32` is the read.)

### 12.3 Codegen — the construction sequence

At the effect site, after the dispatch fork in `compile_apply` recognizes a
`DefKind::PlatformEffect` target (the same recognition `compile_direct_call` /
`resolve_platform_effect_target` already do for the blocking stamp, §7), the backend
branches on the `DefKind::PlatformEffect.poll_shape` field. For `poll_shape == true`
(`resolve_poll_effect_target` returns the target):

```
;; args already compiled to Values via compile_consuming_arg_list (arg_0..arg_{k-1})

;; 1. Load the poll-fn pointer from the platform GOT — the SAME slab_base + slot
;;    load as emit_got_indirect_call_via_data_id, but LOAD ONLY (no call_indirect).
slab_base = global_value(__cranelisp_got_platform_<module>)   ; one relocation
slot_addr = iadd_imm slab_base, slot*8
poll_fn   = load.i64 slot_addr                                ; the PollFn pointer

;; 2. Allocate + populate the state-closure (reuse closure-construction codegen).
env_slots = 1 (result) + k (args) + scratch
clo = emit_alloc(16 + 8*(2 + env_slots))      ; header + code_ptr + drop_glue + env
store poll_fn       at clo + 16               ; code_ptr  = poll-fn
store drop_glue     at clo + 24               ; state-teardown glue (§12.5)
store 0             at clo + 32               ; result slot init (sentinel)
store arg_0         at clo + 40               ; marshal arg captures...
store arg_1         at clo + 48
...
;; RC: NO inc at the store. The args reached this arm via
;;     compile_consuming_arg_list, which ALREADY inc'd heap-typed Var args
;;     (and transfers temporaries directly). Storing them into the env is a
;;     plain ownership transfer (the Bind/ParBind constructor convention). The
;;     state-closure drop glue (§12.5) dec's each heap-typed arg slot when the
;;     node is consumed. Do NOT also run the borrowing emit_capture_inc loop —
;;     that double-incs every heap-typed Var arg and leaks it.

;; 3. Allocate + populate the IO_TAG_EFFECT_POLL node.
node = emit_alloc(16)                          ; header + tag + state_closure
store IO_TAG_EFFECT_POLL at node + 16
store clo                at node + 24          ; ownership transfer (rc=1), no inc

return node
```

Two reuse anchors, both load-bearing (Principle 7):

- **Step 1 is the GOT load already written** — `emit_got_indirect_call_via_data_id`
  loads `poll_fn` from `slab_base + slot*8` then `call_indirect`s it. The poll arm
  factors out the *load* (everything up to and including the `load.i64`) and **stops
  before the call**, baking `poll_fn` as the closure `code_ptr` instead. The
  recommendation is to extract a `emit_got_slot_load(data_id, slot) -> Value` helper
  that both the call path and the poll-construction path call, so the GOT-indirect
  mechanism stays single-source. The load is done **once at construction**; the baked
  `code_ptr` is the dispatch target — GOT-indirect dispatch is preserved, just deferred
  to poll time (§13 decision 2).
- **Step 2 is the closure-construction codegen already written** — the alloc + store
  `code_ptr` + store `drop_glue_ptr` + store-captures sequence is precisely
  `compile_lambda`'s closure-site emission (`lambda.rs` lines ~110–162). Three
  differences: `code_ptr` is the GOT-loaded poll-fn (not a `func_addr` of a generated
  inner fn); env slot 0 is a reserved result slot (not a capture); and the arg slots
  are stored under the **consuming convention** — a plain store with **no per-capture
  inc**, because the args were already inc'd upstream by `compile_consuming_arg_list`.
  This is the `Bind`/`ParBind` constructor convention (the node's field-store inherits
  ownership from the consuming arg list), **NOT** `compile_lambda`'s *borrowing*
  `emit_capture_inc` loop. Reusing that inc loop here would **double-inc** every
  heap-typed Var arg (once in the consuming list, once in the loop) and leak it. /dev
  reuses the capture-*store* sequence verbatim, but **omits the `emit_capture_inc`**.

**Arg marshaling = closure captures (§13 decision 2).** The effect's i64 args become
the closure's captures. The poll-fn does its first-poll setup (open fd, issue the
non-blocking syscall) from these captured args on its first `poll` call. This is why
there is **no `make_state` platform export** — the host marshals the args itself using
established closure codegen; the poll-fn reads them out of `state` (= the env). RC of
heap-typed args follows the **consuming convention**: the args arrive already inc'd
from `compile_consuming_arg_list`, the env stores them with **no further inc**
(ownership transfer), and the state-closure drop glue dec's each heap-typed arg slot
when the node is consumed (§12.5). Scalar/temporary args carry no glue.

**No fn-name stamp on this arm.** The §7 `stamp_platform_fn_name` exists so the
intrinsics fault guard can name a *blocking* effect whose DLL-built node faulted. The
poll node is host-built and its dispatch failure surfaces through the reactor's
`EffectPoll`, not the blocking fault guard; the stamp is a blocking-arm concern and is
**not** emitted here. (If a poll-arm diagnostic name is later wanted, it rides the
state-closure env as another reserved slot — not in scope for S94.)

### 12.4 Trampoline interaction (intrinsics-owned — stated here for the contract)

The node construction is the backend's whole job; the **call** is the trampoline's
(`run_io_trampoline_inner_async`, `cranelisp-intrinsics`, intrinsics-owned — see
`design/intrinsics/reactor.md`). Stated here only so the seam is unambiguous: the async
Effect arm `.await`s an `EffectPoll` future whose `Future::poll(cx)` builds a C-ABI
`Waker` over `cx.waker()` and calls `poll(state = clo, host, waker) -> Poll`. On
`Poll::Ready` it reads the i64 result generically from `state + 32` (the reserved
result slot, §12.2) — the S93 fixture's per-effect `ResultReader` fn-pointer collapses
to this single generic offset read (§13 decision 3). The sync (feature-off) stepper
only ever sees `IO_TAG_EFFECT`; it never encounters `IO_TAG_EFFECT_POLL` because none
is ever constructed without concurrency.

### 12.5 Drop glue — RC + the reserved `drop_state` hook

The poll node is a standard ADT (one tag, one heap-typed field), so its drop glue
(§3) dec's `state_closure` when the node reaches rc=0; the trampoline's existing
`consume_io_tree` drop walk reaches it for free (§13 decision 1 — "inherits RC + drop").

> **Arg-lifetime across suspension — the backend obligation is UNCHANGED (invariant 15;
> S98, FIXME 0486).** A reactor-deferred poll effect's baked args must stay live from
> establish until the reactor resolves it (Ready or cancel-drop) — see
> `bounded-contexts.md §4b` **invariant 15** + `reactor.md §2.20`. `/arch`'s Phase-2 ruling
> (S98, `effect-concurrency.md §6`) places that keep-alive on the **runtime** side: the
> `EffectPoll` holds the state-closure alive across the `await` and consumes it exactly-once
> on the `reg`-keyed two-path. **The backend contributes nothing new for this** — the
> state-closure layout (§12.2), the capture-**consuming** store (§12.3, no extra inc), and
> the `build_closure_drop_glue` capture-dec glue above are exactly what the keep-alive rides;
> backend-emitted keep-alive would require modelling suspension points (the deferred Level-2).
> **Residual bug-#2 caveat.** The invariant-15 keep-alive is landed + necessary but **not
> sufficient** for the launched-strand heap corruption: the state-closure RC is balanced, and
> the residual UAF is a **separate backend codegen defect** — a borrowed-`Var` two-live-vec RC
> double-dec on the launched strand (`ring2-rc.md §5.5` path), tracked as **FIXME 0494**
> (`target: /backend`). That fix IS backend codegen; the state-closure drop glue described here
> is not the culprit.

The state-closure's `drop_glue_ptr` is the **primary** teardown path: generated by the
backend exactly as `build_closure_drop_glue` (`lambda.rs`) — it dec's each heap-typed
arg capture. The result slot is a plain i64 written by the poll-fn; whether it needs a
dec depends on the effect's result type (`AlwaysHeap`/`Mixed`/`NeverHeap` — same
classification as Pure's value field, §3.1). For the S94 in-tree demo (`async-read`
returns an `Int` byte count) the result slot is `NeverHeap` — no dec.

The platform's optional `ConcurrentPlatformFn.drop_state` hook (the one reserved-inert
ABI field, §13 decision 4 / `platform-interface.md` §6.8) is the leaf's contribution
to this glue, for **leaf-private heap a host cannot free** (a libc buffer, a connection
struct). When present, the backend bakes a call to it into the state-closure's
`drop_glue_ptr` (passing `state = env`); when `None` (the C-ABI null fn-ptr — the S94
demo's case) the host glue alone suffices. **`drop_state` is RESERVED-BUT-INERT for
S94** — the demo passes `None`, so the backend's S94 deliverable bakes only the
capture-dec glue and **does not** emit a `drop_state` call. The hook's wiring lands
with the cancellation slice (≥ 7); designing the glue to *accept* it now (a null-check
+ conditional call, mirroring the closure `drop_glue_ptr != 0` guard in
`rc_emission.rs`) is the cheap shape-to-be-subsumed move (Principle 8) but is itself
deferrable — S94 may bake pure capture-dec glue and add the `drop_state` branch in the
cancellation slice.

### 12.6 Implementation steps for /dev

1. Add `IO_TAG_EFFECT_POLL = 4` to the IO tag constants (`cranelisp-platform` /
   `cranelisp-types`, gated with the `concurrency` layout contracts, §1.4).
2. Extract `emit_got_slot_load(data_id, slot) -> Value` from
   `emit_got_indirect_call_via_data_id` (the load prefix); have the existing call path
   call it (no behaviour change — refactor + its own equivalence is covered by the
   unchanged blocking tests).
3. At the `DefKind::PlatformEffect` dispatch recognition site, read the effect's
   `DefKind::PlatformEffect.poll_shape` field (via `resolve_poll_effect_target`).
   `poll_shape == false` → the unchanged blocking arm (§7). `poll_shape == true` →
   the poll-construction arm (§12.3). The backend reads only this boolean; the full
   `ConcurrencyDescriptor` is not on the symbol table (§12.1).
4. Implement the poll-construction arm: GOT-load the poll-fn (step 2), build the
   state-closure reusing the `compile_lambda` closure-site emission — but store the arg
   captures under the **consuming convention** (a plain store, **no**
   `emit_capture_inc`; the args are already inc'd by `compile_consuming_arg_list`),
   build the `IO_TAG_EFFECT_POLL` node (§12.3).
5. Generate the state-closure drop glue via the existing `build_closure_drop_glue`
   path (capture-dec only for S94; the `drop_state` branch is deferred, §12.5).
6. Confirm the blocking arm is reached for every stock-platform effect (every effect
   has `poll_shape == false` in a non-concurrency toolchain) so the default build is
   byte-identical (the negative guard, §12.7).

### 12.7 Unit-test seams for /dev (backend tier)

Per the project's unit-test-per-fix discipline, the mandatory backend-tier seams:

- **Byte-identical-off (the load-bearing negative guard).** A blocking effect
  (`poll_shape == false` — the only kind in a stock platform set) constructs an
  `IO_TAG_EFFECT` node and emits the unchanged §7 dispatch+stamp; **no
  `IO_TAG_EFFECT_POLL` node is constructed** and the emitted CLIF for a representative
  blocking effect call is unchanged. This is the R3 obligation expressed as a test.
- **Poll-node shape.** A `poll_shape == true` effect constructs an `IO_TAG_EFFECT_POLL`
  node whose field-0 points at a closure with `code_ptr` = the GOT-loaded poll-fn,
  whose env slot 0 is the (sentinel-initialized) result slot, and whose env slots 1..k
  hold the k marshaled args in order. Inspect via CLIF (`CRANELISP_CODEGEN_TRACE=1`) on
  a shrunk single-arg poll effect — the small repro produces small CLIF readable by eye
  (per root `CLAUDE.md` "keep reductions small").
- **GOT load, not call.** The poll arm emits a `load` of the GOT slot and **no
  `call_indirect`** of the poll-fn at the construction site (the call belongs to the
  trampoline). Asserts the load/call distinction that is the whole point of the arm.
- **Arg-capture RC (consuming, not borrowing).** A heap-typed effect arg (e.g. a
  `String`) reaches the arm already inc'd by `compile_consuming_arg_list`, is stored
  into the state-closure env with **no further inc** (ownership transfer), and the
  generated state-closure drop glue dec's it exactly once — the consuming RC balance
  (`ring2-rc.md`). The test must assert there is **no** second inc at the store site
  (the double-inc the borrowing `emit_capture_inc` loop would otherwise introduce).
- **`emit_got_slot_load` refactor parity.** The extracted load helper produces the
  same GOT-slot load the inline call path produced (guards the Principle-7 extraction).

End-to-end overlap/strand assertions (two poll leaves overlapping in ≈max on one
reactor; `EffectDispatched→Suspended→Resumed`; `--link` links no executor) are
`/qa` integration seams driven through `cranelisp_run_io` (the intrinsics + reactor
half); they are listed in `effect-concurrency.md` Appendix B §"What /qa can assert"
and are not backend-unit-tier.

### 12.8 Quality attributes touched

- **Simplicity / complexity budget (Principle 6).** The arm adds one tag, one thin
  node, and one data-driven branch; it reuses the GOT-load and closure-construction
  codegen wholesale rather than standing up a parallel mechanism. No `#[cfg]`, no mode
  fork.
- **Maintainability / single source of truth (Principle 7).** The GOT-indirect
  mechanism stays single-source via the extracted `emit_got_slot_load`; the closure
  build stays single-source via reuse of `compile_lambda`'s emission. A future ABI
  change to the GOT or closure layout lands in one place each.
- **Concurrency-safety (Principle 1).** The backend emits no concurrency primitive —
  it constructs a value (the node). All await/poll/wake lives in the trampoline. RC of
  the captured args is atomic (Decision 13) because the state-closure can be read on a
  reactor thread.
- **Testability (Principle 5).** The arm is decided on a data field (`blocking`) and
  emits an inspectable node shape, so it is unit-testable at the CLIF seam without a
  running reactor; the reactor-dependent behaviour is cleanly the trampoline's, tested
  separately.

## 13. Slice 3 + 6 — `(token, capacity)` node carrier, two-pool partition (S95)

Sprint 95 completes the IO transition (effect-concurrency slices 3 + 6).

> **REVISED 2026-06-28 (`/arch` re-blessed the slice-3 carrier — `effect-concurrency.md`
> §8.1/§8.2).** The earlier draft of this section (static `DefKind.cardinality` bake +
> a `scheduling_class`/`got_slot`-derived token) is **superseded and deleted.** The
> ratified seam is simpler: **capacity rides *with* the token — dynamic, on the IO node,
> platform-supplied at the effect site** — a one-field additive generalization of the
> *existing* `ResourceSerial` dynamic-token mechanism. Retired by that ruling: the
> `DefKind.cardinality`/`capacity` field, the loader lift of a static capacity, the
> `got_slot`-derived token (per-symbol forecloses the shared DB-pool case and is
> incorrect), and the two token-notions. The static descriptor `(token, capacity)` become
> documentation + the v6 default bridge; live values are platform-supplied at the effect
> site.

The slice-3 carrier is therefore **not** a backend bake of a symbol-table field. It is:

- **blocking `IO_TAG_EFFECT`:** an **additive** platform constructor
  `CLIO::effect_on_resource_with_capacity(token, capacity, f)` that appends a `capacity`
  field to the node (platform-crate code — `/platform`-owned; the backend's blocking-path
  codegen is **unchanged**). §13.2.
- **poll-shape `IO_TAG_EFFECT_POLL`:** the backend reserves the symmetric
  `(token, capacity)` slots on the node it builds (the one backend change). §13.3.
- the **token-keyed `Semaphore` pool** survives, but keys on the **node-read**
  `(token, capacity)` — not a symbol-table field. §13.4 (intrinsics/int-owned).
- the **two-pool partition + wakeable join** (slice 6) is unchanged from the prior draft —
  keyed on the node tag, no new backend codegen. §13.5 (intrinsics/int-owned).

This section is the `/dev` design for the (small) backend half and the precise statement
of where each boundary sits. It builds against `effect-concurrency.md` §8.1 (the ratified
`(token, capacity)` carrier + the first-writer-wins reconciliation rule), §8.2 (within-token
ordering), §7 (two-pool non-unifiability + coarse handoff).

### 13.1 What is new vs. S94 (and what is unchanged)

| Aspect | S94 (slice 2) | S95 (slices 3 + 6, ratified carrier) |
|---|---|---|
| Blocking `IO_TAG_EFFECT` node | `[tag \| thunk \| token \| fn_name]` (32-byte payload) | `[tag \| thunk \| token \| fn_name \| capacity]` (40-byte payload) — **capacity appended at payload offset 32, append-only**; built by the new platform constructor |
| Blocking-path backend codegen | GOT-indirect call + fn-name stamp (§7) | **unchanged**; the fn-name stamp stays at payload offset 24, unaffected by the append |
| `IO_TAG_EFFECT_POLL` node | thin: `[tag \| state_closure]` (1 payload field) | `[tag \| state_closure \| token \| capacity]` (3 payload fields) — backend **reserves** the symmetric `(token, capacity)` slots |
| Capacity source | — | **platform-supplied at the effect site** (dynamic), NOT a `DefKind` field, NOT `got_slot`-derived |
| Async `Par` arm | `join_all` of **all** branches on the one reactor (blocking effects serialize — the 3 RED guards) | **partitioned** by node tag: blocking → rayon dispatcher, poll-shape → reactor `join_all`; joined via a wakeable bridge |

The backend's whole slice-3 job is **reserving the poll node's `(token, capacity)`
slots** (§13.3) — the blocking carrier is platform-side, the pool read is intrinsics-side.
The backend's whole slice-6 job is **nothing new in codegen** — the partition key (which
pool a branch routes to) is the *node tag the existing two arms already emit*. See §13.5.

### 13.2 The blocking carrier — `effect_on_resource_with_capacity` (platform-owned; backend unaffected)

The blocking `IO_TAG_EFFECT` node is DLL-built: the user's `(some-effect args)` compiles
to a GOT-indirect call (§7) whose platform fn internally calls a `CLIO::effect*`
constructor that allocates + returns the node. Slice 3 adds an **additive sibling
constructor** in `cranelisp-platform`:

```
CLIO::effect_on_resource_with_capacity(token, capacity, f)
```

It appends a `capacity` field to the node payload — **append-only, no existing offset
moves**:

```
IO_TAG_EFFECT payload (offsets RELATIVE to the payload, after the 16-byte header):
   0   tag
   8   thunk_ptr
  16   resource_token           IO_EFFECT_RESOURCE_OFFSET   (unchanged)
  24   fn_name_handle           IO_EFFECT_FN_NAME_OFFSET    (unchanged)
  32   capacity                 IO_EFFECT_CAPACITY_OFFSET   (NEW — appended)

payload widens 32 → 40 bytes (total alloc 48 → 56 bytes).
```

`CLIO::effect_on_resource(token, f)` becomes exactly `…_with_capacity(token, 1, f)` —
today's serial-within-token (`ResourceSerial`, capacity 1) preserved by construction. This
is a one-field additive generalization of the **existing** dynamic-token mechanism: capacity
reaches the runtime the *same way the token already does* — dynamically, platform-supplied at
the effect site.

**The backend's blocking-path codegen is UNCHANGED.** The constructor is platform-crate
code called *inside* the DLL, not emitted by the backend. The backend's only blocking-path
write is the fn-name stamp (`stamp_platform_fn_name`, §7) at payload offset 24
(`IO_EFFECT_FN_NAME_OFFSET`, abs offset 40); the capacity append sits *after* it at payload
offset 32 (abs 48), so the stamp is **unaffected** — append-only is precisely what keeps the
backend's existing store correct. The capacity carrier on the blocking node is `/platform`'s
deliverable, recorded here only to pin the boundary; the backend touches none of it.

`capacity` is a plain `NeverHeap` i64 — the blocking node's DLL-side drop glue (which never
dec'd the token or fn-name fields) is unchanged.

### 13.3 The poll carrier — reserve the symmetric `(token, capacity)` slots (the one backend change)

The poll-shape `IO_TAG_EFFECT_POLL` node is **backend-built** (`compile_poll_effect`, §12.3),
so the backend reserves the symmetric `(token, capacity)` carrier on it. The seam left this
an interior choice (env reserved-slots vs. node fields, governed by the v7 env-layout
convention like the result-slot); **the recommendation is node fields**, for two reasons:

1. it keeps `token` at `FIELD_1_OFFSET` — **symmetric with the blocking node's token** (also
   field 1 / abs offset 32) — so `read_resource_token` is one tag-agnostic field-1 read for
   both effect tags;
2. it leaves the state-closure **env layout undisturbed** (result-slot @ env 0 + the
   marshaled args at `capture_offset(1+i)`, §12.2), so the **S94 poll demo's arg offsets are
   unbroken** — reserving env slots before the args would shift every arg.

Widened poll node:

```
Base pointer →
  +0   alloc_size: i64       (= 48)
  +8   rc: i64               (atomic)
  +16  tag: i64             (= IO_TAG_EFFECT_POLL = 4)   HeapAdt::TAG_OFFSET
  +24  state_closure: i64    (field 0 — host-built state-closure, §12.2)  field_offset(0)
  +32  token: i64            (field 1 — symmetric with the blocking node)  field_offset(1)
  +40  capacity: i64         (field 2 — permits on `token`)                field_offset(2)

Total allocation: 48 bytes (16 header + 32 payload = HeapAdt::payload_size(3))
```

Construction extends `compile_poll_effect` minimally — node alloc `payload_size(1)` →
`payload_size(3)`, plus two stores after the state-closure store (Principle 7 — same
construction site, no new arm):

```
;; (steps 1+2 unchanged: GOT-load the poll-fn, build the state-closure `clo`)

node = emit_alloc(HeapAdt::payload_size(3))
store IO_TAG_EFFECT_POLL at node + HeapAdt::TAG_OFFSET   ; tag = 4 (literal, §12.3)
store clo                at node + field_offset(0)       ; state-closure (rc=1, no inc)

;; (NEW, slice 3) RESERVE the (token, capacity) slots, sentinel-initialised.
store iconst(0)          at node + field_offset(1)       ; token   = 0 sentinel
store iconst(1)          at node + field_offset(2)       ; capacity = 1 sentinel

return node
```

**S95 reserves these slots; it does not yet wire live poll-shape values.** Capacity is
platform-supplied at the effect site (§8.1); for the *blocking* carrier that supplier is the
new constructor, and **the slice-3 acceptance is demonstrated on the blocking carrier**
(`effect-concurrency.md` §8.2). For the *poll* carrier the live-value supply (the poll-fn or
the reactor narrows `(token, capacity)` at first poll — the poll-fn sees only `state`, so a
dynamic narrowing rides the env) **plus the acquire-around-poll ordering is a Phase-3
refinement, NOT required for S95 acceptance** (`/arch`, §8.1/§8.2). So the backend's S95
deliverable is to **reserve the carrier** at the symmetric offsets with safe sentinels
(`token = 0` ⇒ unrestricted / no-acquire; `capacity = 1` ⇒ serial); the live narrowing +
acquire wiring lands with the poll-shape refinement. This is the shaped-to-be-subsumed move
(Principle 8): the slots exist at their final offsets, so the refinement fills them without a
layout change.

> **RESOLVED in S96 (Chunk A, item 3) — see §14.** The deferred live `(token, capacity)`
> supply lands as a **construction-time backend bake** (acquire-around-poll needs the values
> before the first poll, so the poll-fn/reactor first-poll-narrowing alternatives are
> retired — §14.1). The bake replaces the two sentinel `iconst` stores with live operand
> Values at the *same* offsets (token @ abs 32, capacity @ abs 40); the read sites are
> unchanged. §14 is the design.

Both reserved fields are `NeverHeap` scalars — the node's drop glue is unchanged in shape
(§13.6).

### 13.4 The token-keyed `Semaphore` pool — node-read `(token, capacity)` (intrinsics/int-owned)

The pool core **survives** the carrier revision; it now keys on the **node-read**
`(token, capacity)` rather than any symbol-table field:

| Half | Owner | What |
|---|---|---|
| Blocking node *carries* `(token, capacity)` | **`/platform`** (`effect_on_resource_with_capacity`, §13.2) | the constructor + the appended field |
| Poll node *reserves* `(token, capacity)` | **`/backend`** (`compile_poll_effect`, §13.3) | the two sentinel stores at `field_offset(1/2)` + the `payload_size(3)` widening |
| Trampoline *reads* `(token, capacity)` off the node + sizes the `Semaphore` | **`/design int`** (`reactor.md`, `io.rs`) | generalize `read_resource_token` to read field 1 for **both** effect tags; a `read_capacity` for the blocking carrier (payload offset 32) / poll carrier (`field_offset(2)`); the host-owned `HashMap<token, Semaphore>`; acquire-before-dispatch / release-on-completion; within-token source ordering (the capacity-1 sequential async block, §8.2) |
| Permit semantics | **`/design int`** | `token == 0 ⇒ no acquire (unrestricted)`; otherwise a `Semaphore(capacity)` keyed by token; the (capacity+1)th **parks** |
| Reconciliation: same token, different capacity | **`/design int`** | **first-writer-wins** (the value that created the token's semaphore) + a dev-facing strand event records the disagreement (`effect-concurrency.md` §8.1 — a capacity disagreement is a platform bug; first-writer never exceeds a declared ceiling) |

The backend emits **no concurrency primitive** (Principle 1 — it constructs a value; all
acquire/park/release lives in the trampoline). The node is self-describing —
`(token, capacity)` on the node — so the trampoline stays a pure function of the node, the
same property that already makes the blocking node carry its own token.

### 13.5 Two-pool partition + the wakeable join (slice 6) — node-shape is backend, the join is intrinsics/int

Slice 6 closes the feature-on regression: today's async `Par` arm
(`io.rs::run_par_node_async`) routes **all** branches through the single-reactor
`join_all`, so blocking effects serialize through the one reactor thread (3 RED
`nt-reactor-e2e` guards). The fix partitions branches and drives **both** pools.

**The partition key is the node tag the backend already emits** — there is **no new
backend codegen for slice 6**. A blocking effect compiles (unchanged, §7) to an
`IO_TAG_EFFECT` node; a poll-shape effect compiles (§12 + §13.3) to an
`IO_TAG_EFFECT_POLL` node. That tag *is* the `blocking?` axis (the routing axis is the node
tag — no new carrier; `effect-concurrency.md` §7/§8). The backend's slice-6 contribution
is the guarantee that a mixed `Par`'s branches carry the correct effect-leaf tags so the
trampoline can partition them — which the two existing arms already do.

**The join is intrinsics/int-owned (the load-bearing Principle-8 constraint).** Stated
here only to pin the boundary precisely; the authoritative design is `/design int`'s
(`reactor.md` §`run_par_node_async`). `run_par_node_async` partitions its branches by the
reachable effect-leaf tag, then **composes the two existing dispatchers** (gate (c) —
**do not fork a third dispatcher**):

- **blocking partition** (`IO_TAG_EFFECT` branches) → the **existing** rayon
  `dispatch_par_branches_with_trace` (it already does token-grouping +
  `SerialGroup` ordering + the worker-side `take_runtime_error()` → join-side
  `set_runtime_error()` error-ferry — nothing to re-build);
- **poll-shape partition** (`IO_TAG_EFFECT_POLL` branches) → the **existing** reactor
  `futures::future::join_all` of `run_io_trampoline_inner_async`;
- **top-level join** merges the two partition-futures by binding index.

**The rayon→reactor completion signal MUST be a wakeable future** (gate (c)): the rayon
partition runs on the rayon pool (`spawn`), and its completion is surfaced to the reactor
through a `futures` oneshot/channel **woken via `cx.waker()`** — so the reactor thread
`.await`s the rayon result without occupying its single thread. **`block_on(rayon_join)`
on the reactor thread is explicitly forbidden** — it re-introduces the exact starvation
slice 6 fixes (a non-yielding blocking wait pinning the one reactor thread). That wakeable
bridge is the permanent §7 cross-pool handoff (kept **coarse**, at the effect→render
boundary) reused by every later joined-pool slice — it is shaped-to-last (Principle 8),
not a throwaway.

**Branch classification is int-owned.** A `Par` branch can be a `Bind` chain rooted at
`IO_TAG_BIND`, not a bare effect node, so "partition by tag" is *classify by the branch's
reachable effect leaf*, not a naive root-tag read — an `io.rs`/`reactor.md` detail. The
backend guarantees the **leaf** tags are correct; the trampoline's classification of a
branch is `/design int`'s. This is the boundary item to coordinate for slice 6.

### 13.6 Drop glue — unchanged in shape

The widened poll node is still a standard ADT with exactly **one** heap-typed field
(field 0, the state-closure); the reserved `token` and `capacity` are `NeverHeap` scalars
(§13.3). The node's drop glue (the `consume_io_tree` walk reaching field 0 and running the
state-closure's `drop_glue_ptr`, §12.5) is therefore unchanged — the two reserved fields add
no dec. `build_poll_state_drop_glue` (the state-closure capture-dec glue) is likewise
untouched: the reserved fields live on the *node*, not the closure env. The `drop_state`
hook remains reserved-but-inert (§12.5; cancellation slice). The blocking node's appended
`capacity` (§13.2) is likewise `NeverHeap` — the DLL-side blocking drop glue is unchanged.

### 13.7 Implementation steps (by crate)

1. **`/platform`** — add `CLIO::effect_on_resource_with_capacity(token, capacity, f)`
   appending `capacity` at payload offset 32 (`IO_EFFECT_CAPACITY_OFFSET`, the new
   constant); redefine `effect_on_resource(token, f)` as `…_with_capacity(token, 1, f)`;
   widen the node alloc by one i64 (§13.2). **Backend unaffected.**
2. **`/backend`** (the one backend change) — widen `compile_poll_effect` (§13.3): node
   alloc `payload_size(1)` → `payload_size(3)`; add the two sentinel stores
   (`token = 0` at `field_offset(1)`, `capacity = 1` at `field_offset(2)`). **No
   `DefKind` read, no `cardinality`/`got_slot` derivation** — those are deleted.
3. **`/design int` + intrinsics** — the pool read (§13.4): generalize `read_resource_token`
   to both effect tags; add `read_capacity`; the `HashMap<token, Semaphore>`; acquire /
   release / park; the first-writer-wins capacity reconciliation + the strand event;
   within-token ordering for capacity-1 (§8.2).
4. **No backend change for the two-pool partition** (§13.5) — the partition key is the
   existing node tags; the partition + wakeable join are `io.rs`/`reactor.md`.
5. The **poll-shape live `(token, capacity)` supply + acquire-around-poll is deferred** to
   the Phase-3 refinement (`/arch`, §8.1/§8.2) — not in S95 scope; the backend only
   reserves the carrier. **(Resolved in S96 — §14: the backend bakes the live values into
   the reserved slots; the acquire-around-poll permit is intrinsics-side, `/design int`.)**

### 13.8 Unit-test seams for Phase 5 (by tier)

Per the unit-test-per-fix discipline. **NO `DefKind`-bake test, NO `got_slot` test** — both
retired with the static-carrier design.

**Backend tier** (inspect via CLIF, `CRANELISP_CODEGEN_TRACE=1`, on a shrunk single-arg poll
effect — small repro → small CLIF readable by eye):

- **Poll-node reserved-slots CLIF shape.** A poll effect constructs an `IO_TAG_EFFECT_POLL`
  node of `payload_size(3)` (48 bytes) with the state-closure at `field_offset(0)`, an
  `iconst 0` (token sentinel) at `field_offset(1)`, and an `iconst 1` (capacity sentinel)
  at `field_offset(2)`. Assert the widened alloc + the two sentinel stores at the symmetric
  offsets.
- **Two-pool partition by tag.** A mixed `Par` of one blocking effect + one poll effect
  emits exactly one `IO_TAG_EFFECT` node and one `IO_TAG_EFFECT_POLL` node — the partition
  key. Assert both tag constants appear in the `Par` branch CLIF (the backend's slice-6
  contribution: correct leaf tags; the partition logic itself is int-tested).
- **Byte-identical-off (the load-bearing negative guard).** A blocking effect constructs an
  unchanged `IO_TAG_EFFECT` node via the §7 dispatch+stamp; the fn-name stamp still lands at
  payload offset 24 and **no `IO_TAG_EFFECT_POLL` node is constructed**; the emitted backend
  CLIF for a representative blocking effect call is unchanged vs. S94. (The capacity append
  is platform-side, not backend CLIF — see the platform tier.)

**Platform tier** (`/platform`-owned, `cranelisp-platform`):

- **Capacity-append @ payload offset 32 + node-widen 32 → 40, append-only.**
  `effect_on_resource_with_capacity(token, N, f)` writes `capacity = N` at payload offset 32;
  `resource_token` (offset 16) and `fn_name_handle` (offset 24) are **unmoved**.
- **`effect_on_resource` cap-1 path unchanged.** `effect_on_resource(token, f)` produces a
  node with `capacity = 1` (today's serial-within-token) — the byte-identical generalization.

**Integration / int tier** (`/qa` + `/design int`, driven through `cranelisp_run_io`):
N effects on distinct tokens overlap; N on one token of capacity N run concurrently + the
(N+1)th parks; same-token capacity-1 serial + ordered; same-token capacity-disagreement →
first-writer-wins + strand event; a mixed blocking+poll `Par` overlaps on both pools in
≈max not sum; the 3 `nt-reactor-e2e` guards flip green; `--link` links no executor. These
exercise the **blocking carrier** (slice-3 acceptance is demonstrable there, §8.2), not the
deferred poll-shape acquire.

### 13.9 Public-API / baseline-diff impact (the `cranelisp-types` edge touch is GONE)

The ratified carrier **removes the `cranelisp-types` (`DefKind`) edge touch** the earlier
draft anticipated — there is **no `DefKind.cardinality` field**. The surface that moves is
`crates/cranelisp-platform/public-api.txt`:

- the new `CLIO::effect_on_resource_with_capacity` constructor (additive, **ungated**);
- the new `IO_EFFECT_CAPACITY_OFFSET` constant (additive, ungated).

Both are **additive** to the platform crate's public surface. **Flag for `/dev`** (the
`/platform`-side implementing change): regenerate `crates/cranelisp-platform/public-api.txt`
in the same change-set per the baseline-diff discipline, and name the two added items in the
platform crate's source rustdoc (BC §5 surface). The poll-node widening is an in-process
backend↔intrinsics convention — **no `cranelisp-types` edge, no `public-api` move on the
backend side, no `ABI_VERSION` bump** (the appended blocking field is governed by the v6/v7
node-layout convention, not a struct ABI freeze). The `_neg` gated-edge guard stays green.

### 13.10 Quality attributes touched

- **Simplicity / complexity budget (Principle 6).** The ratified carrier is *simpler* than
  the superseded draft: a one-field additive generalization of the existing dynamic-token
  mechanism, no static `DefKind` field, no loader lift, no two token-notions. The backend's
  contribution shrinks to two sentinel stores; slice 6 adds **zero** backend codegen.
- **Maintainability / single source of truth (Principle 7).** Capacity reaches the runtime
  the *same way the token already does* — one carrier, one read site per node kind;
  `compile_poll_effect` stays the single poll-node construction site; the two-pool join
  reuses the two existing dispatchers (no third dispatcher).
- **Concurrency-safety (Principle 1).** The backend emits no concurrency primitive — it
  reserves a self-describing `(token, capacity)` carrier. All acquire/park/release/wake lives
  in the trampoline; the wakeable rayon→reactor bridge (no `block_on` on the reactor thread)
  is the structural guard against re-starvation; the first-writer-wins reconciliation never
  exceeds a platform-declared capacity ceiling.
- **Testability (Principle 5).** The reserved carrier emits an inspectable node shape
  (offsets + sentinel constants), unit-testable at the CLIF seam without a running reactor;
  the pool/routing behaviour is cleanly the trampoline's, tested separately by `/qa`.

## 14. Poll-node LIVE `(token, capacity)` bake (S96 Chunk A, item 3)

> **SUPERSEDED by ABI v9 (S97, ctx-vtable handle model) — see §17.** This entire section
> designs the **v8 leading-pair bake**: the poll-shape lowering supplies `(token, capacity)` as
> the two leading operands of every poll effect (`arg_vals = [token, capacity, leaf_0, …]`) and
> the backend bakes them from those positional args into the poll node's offset-32/40 slots
> (§14.2–§14.4). **v9 deletes this mechanism.** Under the ratified ctx-vtable model the resource
> descriptor `(token, capacity)` is no longer a cranelisp operand, no longer a leaf argument,
> and is not stored anywhere (no node slot, no value-header slot) — the **platform poll-fn
> computes the token from the handle it holds and calls the trampoline-owned `ctx` vtable
> (`acquire`/`register_*`/`retire`) itself** (`effect-concurrency.md` §4.1.1). The backend
> **stops baking from positional args** — `compile_poll_effect`'s leaf-arg list is
> `arg_vals[0..]` directly (no leading-pair peel) — and bakes nothing in its place. §14 is
> retained as the historical v8 design record (the model the v8 server shipped on); read it for
> provenance, not as the live contract. The v9 backend delta is the deletion-only reshape in
> **§17** (the intermediate descriptor-cut header-slot/`desc_out` design is itself retired —
> §17.7).

Sprint 96 Chunk A lights up the **live** poll-shape `(token, capacity)` carrier — the
deferred half of §13.3. S95 reserved the poll node's `(token, capacity)` slots at
**sentinel** (`token = 0`, `capacity = 1`) at the symmetric offsets; S96 **replaces the two
sentinel `iconst` stores with stores of the live runtime values**, so the reactor's
acquire-around-poll admission gate reads a real `(token, capacity)` off the poll node — the
poll analogue of the S95 blocking-carrier capacity-N proof. This is the **whole backend
job** for item 3; the permit (RAII acquire-around-poll lifecycle) is intrinsics-side
(`design/intrinsics/reactor.md`, `/design int`).

This section is the `/design` intent for the bake. It builds against `effect-concurrency.md`
§8.1 (capacity rides WITH the token, **platform-supplied dynamically at the effect site** —
not a `DefKind` field, not `got_slot`-derived) and the S96 Phase-2 gate (a) ruling
(acquire-around-poll: the poll node carries live `(token, capacity)`; the permit is an
intrinsics-side RAII drop-guard; the backend's job is the **bake**).

### 14.1 Why the backend bakes at construction (not poll-fn / reactor narrowing at first poll)

§13.3 left the poll live-value supply as an interior choice between *backend bake at
construction* and *the poll-fn (or reactor) narrowing `(token, capacity)` at first poll*.
The S96 acquire-around-poll ruling **resolves it to backend-bake-at-construction**, and the
reason is load-bearing:

> Gate (a): "the acquire is the trampoline's single admission gate **wrapping the whole
> establish→ready arc**". The *establish* step is the **first poll** (open fd, issue the
> non-blocking syscall). So **acquire precedes the first poll**, and acquire needs
> `(token, capacity)` to size/key the `Semaphore` — therefore `(token, capacity)` MUST be
> on the node **before any poll runs**. A poll-fn that narrows them at first poll is
> structurally too late (the permit was already acquired). The values are known at the
> effect site (the resource handle is in hand; the pool ceiling is a runtime config the
> platform supplies), so the **construction-time bake is the only consistent placement.**

This retires the "poll-fn narrows / reactor narrows" alternatives §13.3 floated.

### 14.2 Where the live values come from — the bake source (and the cross-crate seam)

Both values are **runtime i64 Values available at the poll effect site**, baked by a plain
scalar store (both are `NeverHeap` — an opaque fd/handle identity and a count — so **no RC**,
§14.5):

- **token** (field 1, abs offset 32): the resource handle the poll effect operates on — the
  connection token for `read`/`send`, the listener/pool token for `accept`. It is a Value
  the backend already holds (it is also the poll-fn's syscall fd, so it is *also* marshaled
  into the state-closure env, §12.2). The bake copies that one i64 into the node's admission
  slot.
- **capacity** (field 2, abs offset 40): the resource's declared concurrency ceiling — the
  pool size (`(listen addr :pool N)`'s `N`, `(connect-pool url :size 16)`'s `16`), a runtime
  config value known when the pool/listener opens (`effect-concurrency.md` §8.1). It is
  **admission metadata only** (the poll-fn does not need it), so it is baked **node-only**,
  not into the env.

**The bake is positional and uniform — the recommended operand convention.** So that
`poll_shape: bool` stays the **sole** symbol-table discriminator (no `cranelisp-types` edge
touch, Phase-2 public-API ruling), the poll-shape lowering supplies `(token, capacity)` as
the **two leading operands** of every poll effect, ahead of the leaf args, with the resource
handle re-passed as the first leaf arg (so the poll-fn still finds its fd in the env). The
backend then bakes **uniformly, with no per-leaf discriminator**:

```
arg_vals = [ token, capacity, leaf_0, leaf_1, ... ]   ; the poll-shape operand convention
                                  └ leaf_0 = the re-passed resource handle (poll-fn fd)

token_val = arg_vals[0]       ; → node field 1 (and == leaf_0, the env fd)
cap_val   = arg_vals[1]       ; → node field 2 (node-only)
leaf args = arg_vals[2..]     ; → state-closure env captures (result @ capture(0), leaf i @ capture(1+i))
```

A **tokenless** poll leaf (a bare timer — no resource) carries the leading pair as the
explicit constants `(0, 1)`; the backend bakes them by the *same* path, so `token = 0`
(no-acquire) / `capacity = 1` (serial) — the S95 sentinel behaviour **preserved by value**,
not by special-case. This is why the convention is uniform: the backend always peels
`arg_vals[0]`/`arg_vals[1]`; there is no "tokened vs tokenless" branch and no new types
field.

> **SEAM — flag for `/sprint` reconciliation.** The backend's bake is positional; the
> **operand-injection convention** (the lowering that places `(token, capacity)` as the two
> leading operands + re-passes the resource handle as `leaf_0`) is owned jointly by
> `/platform` (the `concurrency`-gated `poll_support` poll-leaf lowering) and `/design int`
> (the reactor read), with `/arch` arbitrating the in-process convention. The **bake offsets
> and the no-types-touch constraint are fixed** (this doc + the S95 reservation); the precise
> operand *positions* are the reconcilable detail. The rejected-this-sprint alternative — keep
> the user-arg operand shape and discriminate token/capacity positions via a per-leaf
> `resource_arity` field — is rejected because it requires a `cranelisp-types` edge touch
> (forbidden by the Phase-2 public-API ruling). If the wave gate prefers a different
> operand placement, only §14.4's `arg_vals[..]` indices move; the offsets, RC treatment,
> and byte-identical-off properties are unchanged.

### 14.3 Codegen delta — minimal, same construction site

The change to `compile_poll_effect` (§12.3 / `apply.rs`) is **two store operands plus the
env-marshal start index** — no new node field, no alloc change (the node is already
`payload_size(3)` from S95), no new arm (Principle 7 — same single construction site):

```
;; (steps 1+2: GOT-load the poll-fn, build the state-closure — unchanged in shape;
;;  the env now marshals leaf args = arg_vals[2..] at capture(1+i), result @ capture(0))

node = emit_alloc(HeapAdt::payload_size(3))                       ; unchanged (48 bytes)
store IO_TAG_EFFECT_POLL at node + HeapAdt::TAG_OFFSET            ; unchanged
store clo                at node + HeapAdt::field_offset(0)       ; unchanged (state-closure, rc=1, no inc)

;; (S96, item 3) LIVE bake — replaces the two S95 sentinel iconst stores:
store arg_vals[0]        at node + HeapAdt::field_offset(1)       ; token   (was: iconst 0)
store arg_vals[1]        at node + HeapAdt::field_offset(2)       ; capacity (was: iconst 1)

return node
```

The S95 code (`apply.rs` ~lines 1002–1007) stored `iconst(0)` / `iconst(1)`; S96 stores the
two live operand Values. Everything else in `compile_poll_effect` is untouched.

### 14.4 Offset agreement — the cross-crate contract (the heap-offset class that silently breaks)

The bake offsets were **frozen at the S95 reservation** and the intrinsics read sites
**already read them** (they read the sentinels today); S96 changes only the *value stored*,
not the offset — so the read sites need **no change** and the contract cannot drift. Pinned
explicitly (this is the offset class the S95 close praised /dev for disciplining):

| Field | Backend bake (`compile_poll_effect`, `apply.rs`) | Intrinsics read (`cranelisp-intrinsics/src/io.rs`) | Abs offset |
|---|---|---|---|
| token | `HeapAdt::field_offset(1)` | `read_resource_token` → `FIELD_1_OFFSET` (tag-agnostic over both effect tags) | **32** |
| capacity | `HeapAdt::field_offset(2)` | `read_capacity` (poll arm) → `POLL_CAPACITY_ABS_OFFSET = FIELD_1_OFFSET + 8` | **40** |

Both sides already resolve to abs 32 / 40 (`HeapAdt::FIELDS_START = 24`, +8 = 32 = field 1,
+8 = 40 = field 2; intrinsics `FIELD_1_OFFSET = 32`, `POLL_CAPACITY_ABS_OFFSET = 40`). The
token offset is **symmetric with the blocking node's token** (also field 1 / abs 32), which
is exactly why `read_resource_token` is one tag-agnostic field-1 read for both effect tags
(§13.3 / §13.4) — S96 does not disturb that symmetry. **No backend or intrinsics offset
constant changes this sprint;** the only edit is the value the backend stores.

### 14.5 acquire-around-poll consumption (intrinsics-side — stated for the seam)

Stated only to pin the boundary; the authoritative design is `/design int`'s
(`reactor.md`). With a live token on the node, a poll branch in the per-branch acquire
(`io.rs::run_par_node_async` / `dispatch_*`, currently reading the sentinel `token == 0` ⇒
no-op acquire) now reads a **non-zero** token and **acquires its `Semaphore(capacity)` permit
before the first poll**, holding it across the establish→ready arc (whether the future parks
or is immediately ready) and **releasing on `Poll::Ready` AND on future-drop**. That
release-on-drop is the **RAII `Permit` drop-guard** (gate (a) requirement 1 — the named A→C
contract: Chunk A *builds* the drop-release path, Chunk C *exercises* it on
cancellation/timeout). The drop-guard and the `Semaphore` machinery are **intrinsics-owned**
(`/design int`); the backend's only contribution is supplying the live `(token, capacity)`
the gate reads off the node. The backend emits **no concurrency primitive** (Principle 1 — it
constructs a value; all acquire/park/release/drop lives in the reactor).

### 14.6 RC and drop glue — unchanged in shape

Both baked fields are `NeverHeap` i64 scalars (`token` = an opaque fd/handle identity;
`capacity` = a count), so the two stores take **no `rc_inc`** and the node's drop glue is
**unchanged from §13.6** — the poll node remains a one-heap-field ADT (only field 0, the
state-closure, is heap-typed). The token's appearance in **both** the node admission slot and
the env capture is a **scalar copy of one i64**, not a shared heap reference — there is no
extra reference to balance and no double-free risk. `build_poll_state_drop_glue` (the
capture-dec glue, §12.5) is untouched; the `drop_state` hook stays reserved-but-inert until
the cancellation slice.

### 14.7 Public-API / ABI impact — ZERO (per the Phase-2 public-API ruling)

- **`cranelisp-types`: no edge touch.** The dispatch discriminator stays the
  already-landed `poll_shape: bool`; `(token, capacity)` flow as ordinary i64 operands —
  no new `DefKind` field, no `cardinality`/`resource_arity` (the rejected alternative,
  §14.2). The `_neg`/frozen-edge guard stays green.
- **`cranelisp-platform`: no `public-api.txt` touch.** The operand-injection convention is
  the `concurrency`-gated `poll_support` lowering (off the default edge).
- **No `ABI_VERSION` bump.** The poll node layout is **unchanged** from S95 — same 48-byte,
  3-field (`state_closure`, `token`, `capacity`) shape; S96 changes only the *values stored*
  in the two reserved slots. The poll-node carrier is an in-process backend↔intrinsics
  convention (the offsets), not a struct ABI freeze (Phase-2 public-API ruling).

### 14.8 Byte-identical-when-feature-off

The live bake lives **inside** `compile_poll_effect`, which is reached only for a
`poll_shape == true` effect — and a poll-shape effect only exists in a `concurrency`-built
toolchain (the v7 `poll_support` poll-emission is feature-gated). A stock blocking-only
platform has `poll_shape == false` for every effect, so `compile_poll_effect` is **never
invoked**, **no `IO_TAG_EFFECT_POLL` node is constructed**, and the emitted CLIF for every
effect is **byte-identical** to today's default build. The selection is the existing
data-driven branch on `poll_shape` — **no `#[cfg]`, no mode fork** (Principle 11 — mode by
parameter, not by build flag). The bake is a value change within an already-gated-by-data
path.

### 14.9 Unit-test seams for /dev (backend tier)

Per the unit-test-per-fix discipline — inspect via CLIF (`CRANELISP_CODEGEN_TRACE=1`) on a
shrunk single-leaf poll effect (small repro → small CLIF readable by eye):

- **Live-token bake.** A tokened poll effect stores `arg_vals[0]` (the resource-handle
  operand Value) — **not** an `iconst 0` — at `field_offset(1)` (abs 32). Assert the store
  reads the live operand, not the sentinel.
- **Live-capacity bake.** Stores `arg_vals[1]` (the capacity operand Value) — **not** an
  `iconst 1` — at `field_offset(2)` (abs 40).
- **Tokenless leaf preserves sentinel-by-value.** A poll leaf whose lowering supplies the
  leading pair as constants `(0, 1)` bakes `token = 0` / `capacity = 1` through the same
  store path (the S95 behaviour preserved without a special-case).
- **Env layout under the leading-pair peel.** Leaf args (`arg_vals[2..]`) land at
  `capture(1+i)`; the result slot stays at `capture(0)`; the re-passed resource handle is
  `leaf_0` at `capture(1)` (the poll-fn's fd at `state+8`). This guards that peeling the two
  leading operands did not corrupt the env arg offsets the poll-fn relies on.
- **No-RC at the bake.** Neither node-field store emits an `rc_inc` (both `NeverHeap`
  scalars); the node's drop glue shape is unchanged (one heap field).
- **Byte-identical-off negative guard (unchanged from §12.7 / §13.8).** A blocking effect
  constructs an unchanged `IO_TAG_EFFECT` node and **no `IO_TAG_EFFECT_POLL` node** is built;
  the default-build CLIF is unchanged.

Update note for `/qa`: the S95 `poll_codegen_tests` assertions that pin the **sentinel
`iconst 0` / `iconst 1`** stores change to assert the **live operand stores**, and the env
arg-offset assertions update for the leading-pair peel (leaf args at `arg_vals[2..]`). The
overlap/parking end-to-end seams (poll capacity-N: N overlap, the (N+1)th parks; permit
released on `Poll::Ready` and on drop) are `/qa` integration seams driven through
`cranelisp_run_io`, not backend-unit-tier.

### 14.10 Quality attributes touched

- **Simplicity / complexity budget (Principle 6).** The backend's item-3 contribution is
  **two store operands + the env-marshal start index** — no new node field, no alloc change,
  no new arm. The live bake *replaces* sentinel constants at the same site; it does not add
  machinery.
- **Maintainability / single source of truth (Principle 7).** `compile_poll_effect` stays
  the single poll-node construction site; the offset contract is frozen at the S95
  reservation and the intrinsics read sites are untouched, so the cross-crate seam cannot
  silently drift (§14.4).
- **Concurrency-safety (Principle 1).** The backend emits no concurrency primitive — it
  bakes a self-describing `(token, capacity)` carrier; all acquire/park/release/RAII-drop
  lives in the reactor. The token's node/env duplication is a scalar copy, not a shared heap
  reference (§14.6).
- **Testability (Principle 5).** The live bake emits an inspectable node shape (live operand
  stores at fixed offsets), unit-testable at the CLIF seam without a running reactor; the
  acquire-around-poll lifecycle is cleanly the reactor's, tested separately by `/qa`.

## 15. The `IO_TAG_LAUNCH` launch-and-continue node (S96 Chunk B, slice 5)

Sprint 96 Chunk B lands the first user-facing control capability — **launch-and-continue**
(`spec/10-io.md §10.12.7`): a fire-and-forget effect launch (a detached strand with **no join
point**) that lets a server fan out request handlers with **no `spawn`** in the source. The
runtime side (acquire-a-global-permit → mint a child strand → transfer the sub-tree into a
supervised strand → yield `Pure Unit`) is the intrinsics agent's design
(`design/intrinsics/reactor.md §2.11`–§2.13); this section is the **backend counterpart**: the new IO
node tag, its construction bake (modeled on the §14 poll node), how the launchable site is
recognized (reusing — not forking — the existing `Par` independence analysis), and the one new
RC subtlety the detach introduces (sub-tree ownership transfer into the strand).

This builds against `spec/10-io.md §10.12.7` (eligibility = result-discarded + token-disjoint;
the detached-strand observable contract), `effect-concurrency.md §6` (launch → spawn the handler
future, don't await), and the S96 Phase-2 gate (b) ruling (supervisor co-lands; the detached
fan-out is memory-bounded by the global admission budget). The node tag + bake + the consumed
launch-marker are the backend↔intrinsics seam; the supervisor, the global budget, and the
strand-side sub-tree consumption are intrinsics-side (referenced, not duplicated).

### 15.1 What the node is, where it sits in the IO tree

`IO_TAG_LAUNCH` is the **next free IO tag after `IO_TAG_EFFECT_POLL = 4`**, so **`5`**. It is a
**thin, single-field** node — even thinner than the poll node — holding only a pointer to the
launched IO sub-tree (the detached arm). It carries **no `(token, capacity)`**: the launch-and-
continue backpressure is the **global** reactor-thread admission budget (`GLOBAL_BUDGET_TOKEN`
sentinel + `global_degree`, §2.13), which is a reactor constant/construction-knob, **not**
node-baked. A launched leaf that itself needs per-token admission carries that on its own
`IO_TAG_EFFECT`/`IO_TAG_EFFECT_POLL` leaf inside the sub-tree, unchanged.

```
IO_TAG_LAUNCH node (backend-built):
Base pointer →
  +0   alloc_size: i64       (= 32)
  +8   rc: i64               (atomic)
  +16  tag: i64             (= IO_TAG_LAUNCH = 5)            HeapAdt::TAG_OFFSET
  +24  launched_subtree: i64 (field 0 — the detached IO sub-tree, AlwaysHeap)  field_offset(0)

Total allocation: 32 bytes (16 header + 16 payload = HeapAdt::payload_size(1))
```

**Where it sits.** The launch site `(do (handle-conn conn) (serve listener))` macro-expands to
`(bind (handle-conn conn) (fn [_] (serve listener)))`. When the site is launch-eligible, the
backend lowers the inner arm under a `Launch` node, leaving the surrounding `Bind` **unchanged**:

```
Bind( Launch( <handle-conn IO sub-tree> ), cont = (fn [_] (serve listener)) )
└ tag=2          └ tag=5                     └ ordinary continuation closure
```

The trampoline walks this exactly as today until the inner node: `IO_TAG_BIND` pushes the
continuation and descends to the `Launch` node; the `IO_TAG_LAUNCH` arm detaches the sub-tree
into the supervisor and **yields `Pure Unit`** as the inner result, so the popped continuation
`(fn [_] (serve listener))` runs **immediately** — the accept loop tail-recurses to the next
`accept` without awaiting the handler (`design/intrinsics/reactor.md §2.11` steps 1–4). The `Launch`
node is therefore the `inner_io` of a `Bind`, the **same structural slot** a `Par` node occupies
in `Bind(Par(…), cont)` (§13.5 / `io-scheduling.md §4`) — the trampoline's "inner yields a value,
pop the continuation" contract is reused verbatim; `Launch`'s value is always `Unit`.

### 15.2 In-process convention — no `cranelisp-types`/public-API/ABI surface (the `IO_TAG_EFFECT_POLL` precedent)

`IO_TAG_LAUNCH = 5` is an **in-process backend↔intrinsics convention**, exactly as
`IO_TAG_EFFECT_POLL = 4` is (lib.rs:321 — now CORE/ungated under the single-ABI cutover). The
const's home is `cranelisp-platform` alongside the other `IO_TAG_*` constants (§1.4); the backend
emits it as the **literal `5`** at the construction site (the same convention `compile_poll_effect`
uses for the literal `4` and `par_bind.rs` for the literal `3` — the backend carries no
`concurrency` feature and reads no platform const at codegen). Consequences, all confirmed:

- **No `cranelisp-types` edge.** The node is heap data described by an in-process offset
  convention, not a `#[repr(C)]` struct on the frozen interface edge. No `DefKind` field, no
  `cranelisp-types/ast.rs` *runtime-node* type. (The launch **marker** the backend *consumes* is a
  separate AST-level question — §15.3 / FIXME 0466.)
- **No `cranelisp-platform` `public-api.txt` move on the backend side.** Adding the
  `IO_TAG_LAUNCH` const mirrors the `IO_TAG_EFFECT_POLL` addition — a `/platform` one-liner, off
  the default-edge baseline the same way the other CORE IO tags sit.
- **No `ABI_VERSION` bump.** The launch node is host-built and host-interpreted; it never crosses
  the platform DLL ABI (a launched leaf's DLL effect is an ordinary `IO_TAG_EFFECT`/`_POLL` node
  inside the sub-tree, unchanged). The node layout is an in-process convention, not a struct ABI
  freeze (the same ruling as the poll node, §14.7).

No `/arch` FIXME is warranted **for the runtime node tag**. (§15.3 *does* file one — but for the
AST-level launch *marker* + the `/int` analysis extension, not for this node.)

### 15.3 Independence detection — REUSE the `Par` analysis, do not fork it

Launch eligibility (`spec/10-io.md §10.12.7`) is **both**: (1) the effect's **result is discarded**
(a non-final `do`/`bind!` statement whose bound value is unused), and (2) its **resource tokens
are disjoint** from the continuation's effects (§10.12.4). Criterion (2) is **exactly the
token-disjointness the `Par` independence analysis already computes** to group data-independent,
non-`Sequential` effects into `Expr::ParBind`.

That independence-analysis pass is **`/int`-owned** (`design/int/bind-chain-analysis.md`; per
`io-scheduling.md §1` "The analysis pass that identifies parallelizable bindings and produces
`Expr::ParBind` nodes is owned by `/int`"). The backend does **not** perform independence
analysis and **must not** re-derive token-disjointness at the `Bind` codegen site — re-deriving it
would fork the analysis (the very thing this section forbids) and would require token info the
backend does not hold at lowering. Therefore:

> **The launch eligibility verdict is delivered to the backend as a launch-marked AST node, the
> direct `Expr::ParBind` precedent.** `/int`'s bind-chain analysis — extended once for the launch
> shape (result-discarded sequencing + token-disjoint continuation) — emits the marker; the
> backend consumes it and builds the `IO_TAG_LAUNCH` node, exactly as it consumes `Expr::ParBind`
> and builds the `IO_TAG_PAR` node. The two analyses share the same token-disjointness core
> (Principle 7 — single source of truth); the launch shape adds only the "result-discarded,
> single launched arm, continuation does not await" discriminator on top.

The marker variant (provisionally `Expr::LaunchContinue { launched, continuation }` — and its
`MonoExpr` twin, mirroring the `Expr::ParBind`/`MonoExpr::ParBind` pair) lives in
`cranelisp-types/ast.rs` (`/arch`-owned) and is produced by the `/int` analysis pass. **That is a
cross-crate interface decision and a `cranelisp-types` edit — outside `/design` backend's
boundary — so it is filed as FIXME 0466 (`target: /arch`, naming `/int`).** Until it lands, the
backend half is designed-and-blocked-on-the-marker; the node/bake/RC below are complete and
marker-shape-agnostic (they need only "the launched sub-tree `MonoExpr` + the continuation"). The
rejected alternative — backend detecting the launch shape during `Bind` codegen from a "bound var
unused" check alone — is rejected because it cannot see token-disjointness without forking the
analysis (and "result discarded" alone is *not* sufficient for §10.12.7 eligibility).

### 15.4 The bake — `compile_launch`, modeled on `compile_par_bind` / `compile_poll_effect`

The new construction is a single thin-node builder, structurally the simplest of the IO-node
codegen arms (no GOT load, no state-closure, no operand peel). Given the launched sub-tree's
compiled IO value `launched_val` (the result of `self.compile_expr(launched)`, a fresh IO tree at
rc=1):

```
;; compile_launch(launched: &MonoExpr) -> Value
launched_val = self.compile_expr(launched)              ; the detached sub-tree, rc=1 (temporary)

node = emit_alloc(HeapAdt::payload_size(1))             ; 32 bytes (header + tag + 1 field)
store iconst(IO_TAG_LAUNCH=5) at node + HeapAdt::TAG_OFFSET
store launched_val            at node + HeapAdt::field_offset(0)   ; ownership transfer, NO inc
return node
```

The surrounding `Bind(Launch, cont)` is built by the **existing** bind codegen — the backend's new
code is only the thin `Launch` node. The `field_offset(0)` store is a **plain ownership transfer
with no `rc_inc`**: the sub-tree arrives at rc=1 (a fresh temporary) and that single reference
moves into the node's field — **identical to how `compile_par_bind` stores its branch pointers**
(`par_bind.rs:89` "No RC inc — ownership transfer (constructor convention, Decision 20)") and how
`compile_poll_effect` stores its state-closure (§12.3). This is the Decision-24 single-consuming
convention: the node owns exactly the one reference handed to it.

`compile_launch` is the cleanest member of the IO-node-construction family — it reuses
`heap::emit_alloc` + `heap::heap_store` and adds **no** new helper, no new dispatch fork beyond the
marker match (Principle 7 — same construction machinery, no parallel mechanism).

### 15.5 RC sub-tree ownership transfer — the one new RC subtlety (the move-out + null-guarded drop glue)

The detached sub-tree **outlives** the `IO_TAG_LAUNCH` node's interpretation: the main trampoline
walks the launching tree to completion and returns on the **top** future, while the launched
sub-tree runs concurrently on the reactor as a supervised strand and is `consume_io_tree`'d by
**that strand** on completion (`design/intrinsics/reactor.md §2.11`–§2.12). So the sub-tree's single
reference must travel cleanly from the `Launch` node to the strand — an **owned-field move**, not a
copy and not a second owner. The discipline (consistent with the §2.9 RAII model and the
Decision-24 single-consuming convention):

**Construction (backend):** the sub-tree's one reference is transferred into `field_offset(0)` (no
inc, §15.4). At this point the `Launch` node is the sole owner of that reference.

**Detach (intrinsics, `design/intrinsics/reactor.md §2.11` — referenced, not authored here):** the
`IO_TAG_LAUNCH` trampoline arm **moves** the reference out of the node into the supervised strand —
it reads `field_offset(0)`, hands the sub-tree to `supervisor.spawn(sub_tree, …)`, and **writes the
`0` sentinel back into `field_offset(0)`** so the reference now lives only in the strand. This is
the move the intrinsics design names: *"the launch node releases its hold; the strand takes it …
an owned-field move, not a double-free or a leak."* The strand `consume_io_tree`s the sub-tree on
completion/drop — the single reference is consumed exactly once, by the strand.

**The one backend-side adaptation — `Launch` field-0 drop glue is a NULL-GUARDED dec, not an
unconditional `AlwaysHeap` dec.** Because the trampoline moves the reference out (nulling
`field_offset(0)`), "the field holds a live sub-tree" is a *runtime* fact, not a static one. The
`Launch` node's drop glue must therefore load `field_offset(0)` and **dec only if non-null**
(`if ptr != 0 { rc_dec; }`), exactly the guarded-dec shape used for `Mixed` fields (§3.1) and the
closure `drop_glue_ptr != 0` guard (`rc_emission.rs`). This single guard makes "released exactly
once" *representable* (Principle 20 — model invariants by representation; the null sentinel is the
"already moved out" witness, the IO-tree analogue of the §2.9 `Option<Permit>::take()`), and it is
correct on both paths:

| Path | `field_offset(0)` at node-drop | Drop glue action | Who frees the sub-tree |
|---|---|---|---|
| **Launch interpreted (detached)** | `0` (trampoline moved it out) | guarded dec → **no-op** | the supervised strand (`consume_io_tree` on completion/drop) |
| **Launch never interpreted** (unchosen `if`/`match` arm — the node is dropped without the trampoline reaching it) | the live sub-tree ptr | guarded dec → **frees the sub-tree** | the `Launch` node's own drop glue (no leak) |

The un-interpreted case is **strictly better than the `IO_TAG_EFFECT` thunk leak** (§3.2/§4.4): an
unchosen `Launch` arm fully reclaims its sub-tree via standard cascading drop glue, because the
sub-tree is a normal RC heap tree (unlike the Effect node's non-RC `Box` thunk). And there is **no
double-free**: the move-out nulls the field, so the strand and the node-drop never both dec the
same reference.

**Rejected alternative — inc-on-detach.** The strand could instead take a *fresh* owning reference
(`rc_inc` the sub-tree at detach, leaving the `Launch` field-0 as an unconditional `AlwaysHeap`
dec). This also balances (node-drop dec + strand `consume_io_tree` dec against construction-rc +
detach-inc), but it (a) adds an **atomic `rc_inc`** on every launch — on the server hot path the
accept loop fans out at volume — and (b) creates **two owners** of the sub-tree, contradicting the
single-consuming move the intrinsics design specified. The move-out (one reference, transferred,
exactly-once) is the chosen model; inc-on-detach is the documented fallback if a future shape needs
the node to retain an independent reference past detach (none does).

> **Cross-crate seam (backend ↔ intrinsics).** The backend guarantees: (1) the `Launch` node holds
> the sub-tree's single reference at field-0 after construction; (2) the field-0 drop glue is
> null-guarded. The intrinsics trampoline guarantees: (3) the `IO_TAG_LAUNCH` arm moves the
> reference into the strand and writes the `0` sentinel back to field-0 before yielding `Pure Unit`;
> (4) the strand `consume_io_tree`s the sub-tree exactly once. (1)+(3) are the move; (2)+(4) make it
> exactly-once on both paths. Pin the `0`-sentinel write as the contract — if the intrinsics arm
> ever stops nulling field-0, the node-drop would double-free the (now strand-owned) sub-tree.

### 15.6 Drop glue summary + RC of the launch node itself

The `Launch` node is a standard **one-heap-field ADT** (field 0, the sub-tree). Its drop glue is
generated by the existing `emit_inline_drop_glue` path (§3.4), with field-0 emitted under the
**guarded-dec** discipline of §15.5 (the only deviation from a plain `AlwaysHeap` field). The node
itself participates in RC normally: it is the `inner_io` of a `Bind`, inc'd/transferred into that
`Bind` like any inner IO (§2.1), and freed when the launching tree is freed (REPL cleanup / process
exit, §6). No `drop_state`-style hook and no state-closure are involved — the launch node carries no
captures, only the sub-tree pointer.

### 15.7 Byte-identical / no-regression — built only at launch sites

Under the single-ABI/single-trampoline cutover the project no longer polices a "byte-identical-off"
*feature* axis (the `concurrency`-gated off-state is retired — SPRINT.md scope pivot); the relevant
property here is **structural**: the `IO_TAG_LAUNCH` node is constructed **only** when `/int`'s
independence analysis marks a site launch-eligible (§15.3). A program with **no launch-eligible
site** — i.e. any program today, and the vast majority of programs — emits **no `Launch` node**, and
its codegen is **identical** to before this slice (the marker match falls through to the unchanged
`Bind`/`ParBind`/effect arms). The launch lowering is reachable only through the new marker variant,
which the analysis emits only for the `(do (effect-with-discarded-result) (token-disjoint-cont))`
shape of §10.12.7. So:

- **Non-launch programs are unaffected** — no new node, no new branch taken, no RC change.
- A launch site that the analysis declines to mark (e.g. result *used*, or tokens *not* disjoint)
  lowers as an **ordinary `Bind`** — the structured/sequential path, the conservative default. The
  detached path is opt-in by eligibility, never the fallback (matching §10.12.7's "whether a given
  eligible effect is run detached … is implementation-determined" — declining to detach is always
  sound).

### 15.8 Adjudication — A3-review finding #3 (fd-interest leak on `EffectPoll` drop) — DEFER to Chunk C

**Task 2 verdict: DO NOT pull forward into Chunk B — bounded-acceptable for Chunk B; defer the
active reactor-interest deregistration to Chunk C. Codegen implication: NONE.**

Finding #3 (`design/intrinsics/reactor.md §2.9` scope note + §2.14 finding #1): a dropped in-flight
`EffectPoll` that had armed real fd/timer interest releases its *permit* (the §2.9 `Option<Permit>`
drop-glue) but does **not** actively *deregister* its `fd_waiters`/`timer_waiters` entry + `mio`
registration — the entry leaks until that fd next readies. The supervisor (Chunk B) is the first
**volume** consumer of the drop path, so the question is whether the launch/supervisor shape makes
this a real Chunk-B hazard. Assessed from the codegen/runtime-shape angle:

1. **The leak's precondition — a *parked* poll leaf at the moment of drop — is NOT the common
   supervisor drop shape.** The supervisor drops a strand on three paths (§2.12/§2.14): (a)
   run-to-completion, (b) §10 policy after the body *finished* (caught panic / runtime-error), (c)
   graceful shutdown (Chunk C). On (a) and (b) the strand body has **already finished** — its
   `EffectPoll`s reached `Ready` and eager-released; **nothing is parked** at drop. A handler fault
   fires while the handler is *running synchronously* (a poll just returned `Ready` and control
   continued into the faulting code), **not** while a leaf is parked. So the finding's worst-case
   framing — "every faulting handler leaks" — does **not** generally materialize: a faulting handler
   is not parked when it faults.
2. **The only Chunk-B way to drop a *parked* leaf is narrow and bounded.** It requires either (i)
   **intra-handler concurrency** — a `Par`/join *inside* a handler where a sibling branch faults
   while another branch is parked mid-`read` — which the minimal serial-per-connection serve-loop
   demo (`(do (handle-conn conn) (serve listener))`, §16) does **not** exercise; or (ii) **drive-end
   shutdown** dropping all in-flight (parked) strands — which is one-time teardown, squarely the
   Chunk-C graceful-shutdown scenario.
3. **It is memory-safe and self-reclaiming.** Per §2.14/§2.9 the entry leak is a within-drive
   resource leak, **not** a deadlock or UB (`block_on_reactor` returns on the **top** future, never
   on `has_waiters`); the permit *is* released; the orphaned `fd_waiters` entry is reclaimed by the
   existing one-shot deregister when the orphaned fd next readies (an abandoned socket eventually
   errors/closes → readies → fires).
4. **The fix belongs with its real exerciser (Chunk C), mirroring the A→C contract rationale.** The
   literal fix — an `EffectPoll`-owned reactor-registration handle whose `Drop` removes the
   `fd_waiters`/`timer_waiters` entry + `mio`-deregisters — is the **same RAII drop-guard pattern**
   as the §2.9 `Permit`, and its **volume consumer is Chunk-C cancellation** (`race`/`select`/
   `timeout`/graceful-shutdown dropping *parked* leaves at volume). Building the drop-guard in Chunk
   B without that exerciser is the inverse of the A→C discipline (build the release path where the
   consumer is).
5. **Codegen/runtime-shape implication for the backend: NONE — and that holds whether deferred or
   pulled forward.** The reactor-registration handle lives on the `EffectPoll` future
   (intrinsics-side), exactly like the `Permit` — no backend codegen participates. The
   `fd_waiters`/`mio` interest is **host-owned** (reactor.rs §2.1), so even the already-reserved
   backend-baked `drop_state` hook (§12.5, reserved-but-inert) is **not** required for fd/timer
   deregistration. So the backend's `IO_TAG_LAUNCH`/poll-node codegen is identical under either
   disposition; pulling the fix forward would add **zero** backend work and would not change the node
   shape — which removes any "fold it in while we're here" codegen argument for pulling forward.

**Disposition:** DEFER to Chunk C; the bounded-acceptable rationale is **already recorded** by
`/design int` in `reactor.md §2.9` (scope note) and §2.14 (finding #1), so **no FIXME to `/design
int` is needed** — this section CONFIRMS their deferral from the codegen/runtime-shape angle. This
is **not a defect** (memory-safe, spec-conformant — no `--run`/`--link`/REPL divergence, no wrong
output), so no failing-test repro is owed; if `/qa` wants a known-bounded **observability** guard
(a panicking handler with a parked sibling poll leaf → assert the orphaned `fd_waiters` entry count
is bounded and self-reclaims), that is an optional stress/observability seam, not a defect guard.

### 15.9 Unit-test seams for `/dev` (backend tier)

Per the unit-test-per-fix discipline — inspect via CLIF (`CRANELISP_CODEGEN_TRACE=1`) on a shrunk
single-launch site (small repro → small CLIF readable by eye):

- **Launch-node shape.** A launch-marked site constructs an `IO_TAG_LAUNCH` node of
  `payload_size(1)` (32 bytes) storing the literal tag `5` at `TAG_OFFSET` and the compiled
  launched sub-tree pointer at `field_offset(0)`. Assert the alloc size + the two stores.
- **Wrapped by a `Bind`.** The launch site emits `Bind(Launch, cont)` — an `IO_TAG_BIND` node whose
  `inner_io` (field 0) is the `IO_TAG_LAUNCH` node and whose `cont` (field 1) is the continuation
  closure. Assert both tags appear and the nesting (the structural slot `Par` also occupies).
- **Ownership transfer, no inc at the field-0 store.** The launched sub-tree reaches the node at
  rc=1 and is stored with **no `rc_inc`** (constructor convention, like `par_bind.rs`). Assert there
  is no inc at the store site.
- **Null-guarded field-0 drop glue.** The `Launch` node's generated drop glue loads `field_offset(0)`
  and dec's **only if non-null** (the move-out guard, §15.5) — distinct from an unconditional
  `AlwaysHeap` dec. Assert the guard (a null-compare + conditional dec), so an un-interpreted
  `Launch` frees its sub-tree and a detached (nulled) one does not double-free.
- **No-launch negative guard.** A program with no launch-eligible site constructs **no
  `IO_TAG_LAUNCH` node**; an ineligible `(do a b)` (result used, or tokens not disjoint) lowers as an
  ordinary `Bind` — the structural no-regression property (§15.7).

End-to-end seams (launch-and-continue returns immediately; the accept loop keeps accepting; a
panicking handler → server lives; global-budget bounds in-flight strands; strand-drop releases its
permits + sub-tree) are `/qa` integration seams driven through `cranelisp_run_io` + the reactor —
they are listed in `design/intrinsics/reactor.md §2.10` and are not backend-unit-tier.

### 15.10 Implementation steps for `/dev` (backend half)

1. **Add `IO_TAG_LAUNCH = 5`** to the IO tag constants in `cranelisp-platform` (alongside
   `IO_TAG_EFFECT_POLL`, CORE/ungated — §15.2). The backend emits the literal `5` at the bake
   (no platform-const read at codegen, the §12.3/`par_bind.rs` convention).
2. **Consume the launch marker** (blocked on FIXME 0466 — the `Expr`/`MonoExpr::LaunchContinue`
   variant + the `/int` analysis extension; §15.3). Add the dispatch arm in `compile_expr`/the
   mono lowering that recognizes the marker and routes to `compile_launch`.
3. **Implement `compile_launch`** (§15.4): compile the launched sub-tree, `emit_alloc(payload_size(1))`,
   store tag `5` + the sub-tree pointer (ownership transfer, no inc). The surrounding `Bind(Launch,
   cont)` reuses the existing bind codegen.
4. **Generate the `Launch` drop glue with a null-guarded field-0 dec** (§15.5/§15.6) — the one
   deviation from a plain `AlwaysHeap` ADT field; pin the `0`-sentinel move-out contract with
   `/design int` (§15.5 cross-crate seam).
5. **Confirm the no-launch negative guard** (§15.7/§15.9) — ordinary programs and ineligible `do`
   sites emit no `IO_TAG_LAUNCH` node and unchanged codegen.

### 15.11 Quality attributes touched

- **Simplicity / complexity budget (Principle 6).** The slice adds **one tag, one thin single-field
  node, one bake arm, and one drop-glue guard** — the simplest IO-node construction (no GOT load, no
  state-closure, no operand peel). It reuses `emit_alloc`/`heap_store`/the bind codegen wholesale.
- **Maintainability / single source of truth (Principle 7).** Independence detection is **not
  forked** — the launch eligibility rides the existing `/int` `Par` token-disjointness analysis
  (§15.3); the launch node is consumed via the `Expr::ParBind` marker precedent; the construction
  reuses the constructor-convention store shared by `par_bind`/`compile_poll_effect`.
- **Concurrency-safety (Principle 1).** The backend emits **no concurrency primitive** — it
  constructs a value (the `Launch` node) and a null-guarded drop path. All spawn/supervise/global-
  budget/strand-consume lives in the reactor (`design/intrinsics/reactor.md`). The one new RC subtlety
  (sub-tree move-out) is modeled by representation (the `0` sentinel = "moved", §15.5) so "consumed
  exactly once" is structural, not a flag to keep in sync.
- **Testability (Principle 5).** The arm emits an inspectable node shape (tag + one field + a
  null-guarded dec), unit-testable at the CLIF seam without a running reactor; the detach/supervise
  behaviour is cleanly the reactor's, tested separately by `/qa`.

## 16. The `IO_TAG_SELECT` race/select combinator node (S96 Chunk C, slice 7)

Sprint 96 Chunk C lands the **explicit control surface** — the user-facing combinators
`race`/`select`/`timeout` (`effect-concurrency.md §9`, `spec/10-io.md §10.12` informative §3 +
the §12 typing FIXME 0447's second half). These are the "vocabulary for an uncooperative
environment at the I/O boundary": per-request timeout, cancel-on-disconnect, graceful
shutdown. The runtime side — poll all branches, first-ready wins, **cancel (drop) the
losers** — is the intrinsics agent's design (`design/intrinsics/reactor.md`, the combinator
trampoline arm + the A→C RAII-`Permit` drop-guard it exercises); this section is the
**backend counterpart**: the new IO node tag, its construction bake (modeled on the §15
launch node), how race/select are recognized and lowered (the `bind` inline-primitive
precedent — **not** an analysis marker), the result threading, and the RC discipline of the
N branches (the winner kept, the losers cancelled=dropped).

This builds against `effect-concurrency.md §9` (the combinator model — "ordinary typed
functions that construct trampoline-interpreted IO-ADT nodes, the same mechanism class as
`Par`"; `race`/`select` the irreducible primitives, `timeout` derived, cancellation = drop),
the S96 Phase-2 public-API ruling ("`race`/`select` are new **IO node tags** — in-process
backend↔intrinsics convention, the `IO_TAG_EFFECT_POLL` precedent, off the default edge; no
ABI bump"), and the gate (a) A→C contract (Chunk A **built** the `Permit`-on-drop release;
Chunk C's `race`/`select`/`timeout` are the volume **exerciser** that drops still-`Pending`
loser futures — `effect-concurrency.md §8` gate (a), `reactor.md §2.9`).

### 16.1 What the node is, where it sits — one thin list-carrier node for BOTH race and select

`IO_TAG_SELECT` is the **next free IO tag after `IO_TAG_LAUNCH = 5`**, so **`6`**. It is a
**thin, single-field** node — the same shape as the launch node (§15.1) — holding only a
pointer to the **branch list** (`List (IO a)`, the N candidate sub-trees):

```
IO_TAG_SELECT node (backend-built):
Base pointer →
  +0   alloc_size: i64       (= 32)
  +8   rc: i64               (atomic)
  +16  tag: i64             (= IO_TAG_SELECT = 6)              HeapAdt::TAG_OFFSET
  +24  branches: i64         (field 0 — the List (IO a) of N branch sub-trees, AlwaysHeap)  field_offset(0)

Total allocation: 32 bytes (16 header + 16 payload = HeapAdt::payload_size(1))
```

**ONE tag, no mode field — the verdict.** `race` and `select` have **identical runtime
semantics** (poll all branches, first-ready wins, drop the losers) and **identical winner
typing** (`IO a` — the winner's value; §16.6). The only surface difference is **how the
branches are supplied** — `race : IO a → IO a → IO a` (two static branches) vs
`select : List (IO a) → IO a` (a runtime list) — and that difference is resolved **at
construction**, both producing the same list-carrier node. So a second tag, or a mode field
on one tag, would be redundant machinery for a distinction the runtime does not make
(Principle 6 — complexity has a budget). `timeout` is the same node again (`timeout d io =
race io (sleep d)`, stdlib). `race` is the binary special case of `select`; the trampoline
sees one node kind.

**Why a list-carrier field, NOT a Par-style inline `count + branch_0..branch_{N-1}` array.**
The `Par` node (`par_bind.rs`) inlines its N branches because `Expr::ParBind` has **static
arity** (the bindings vec is known at lowering). `select`'s argument is a **runtime
`List (IO a)`** — N is dynamic, unknowable at codegen — so the branches **cannot** be inlined
as static slots. The list **is** the N-branch carrier, and it carries two further advantages
over an inline array: (1) it already provides **per-element drop glue**, so the Select node
stays a clean **one-heap-field ADT** (field 0 = the list) with a single unconditional dec
(§16.7) — simpler than `Par`'s custom N-slot drop walk; (2) it is robust to whatever surface
`/spec` lands (a `List`-typed `select`, a variadic `(select io1 io2 …)` that desugars to a
list, or a binary `race`) — every form reduces to "a list of branch sub-trees in field 0".
This list-carrier shape is the correct realization of `effect-concurrency.md §9`'s
`select : List (IO a) → IO a`; the task-brief's "N inline slots" framing is set aside
deliberately because the dynamic arity forbids it.

**Where it sits.** Like `Par` and `Launch`, the Select node is the **`inner_io` of a
surrounding `Bind`**. `(bind! [x (select branches)] body)` macro-expands to
`(bind (select branches) (fn [x] body))`:

```
Bind( Select( <branch list> ), cont = (fn [x] body) )
└ tag=2        └ tag=6              └ ordinary continuation closure
```

The trampoline walks this exactly as it walks `Bind(Par,cont)` / `Bind(Launch,cont)`:
`IO_TAG_BIND` pushes the continuation and descends to the Select node; the `IO_TAG_SELECT`
arm runs the branches, **yields the winner's value** as the inner result, and the popped
continuation `(fn [x] body)` runs with that value. The "inner yields a value, pop the
continuation" contract (§5.1) is **reused verbatim** — `Select`'s value is the winner's `a`.
Crucially, **`compile_select` does NOT build a continuation** (unlike `compile_par_bind`/
`compile_launch_continue`, which bundle the body): `(select …)` is an ordinary expression
returning `IO a`, so the surrounding `Bind` is built by the **existing bind codegen**
(`compile_bind_inline`) and `compile_select` returns just the thin node. This makes
`compile_select` the **simplest** IO-node construction of all (§16.4).

### 16.2 In-process convention — no `cranelisp-types`/public-API/ABI, and (the load-bearing verdict) NO AST marker

`IO_TAG_SELECT = 6` is an **in-process backend↔intrinsics convention**, exactly as
`IO_TAG_LAUNCH = 5` (§15.2) and `IO_TAG_EFFECT_POLL = 4` (§14.7) are. Const home:
`cranelisp-platform` alongside the other `IO_TAG_*` constants (§1.4, `lib.rs:301–333`);
the backend emits the **literal `6`** at the bake (the backend carries no `concurrency`
feature and reads no platform const at codegen — the `par_bind.rs` literal-`3` /
`compile_poll_effect` literal-`4` / `launch.rs` literal-`5` convention). Consequences, all
confirmed against the S96 Phase-2 public-API ruling:

- **No `cranelisp-types` *runtime-node* edge.** The node is heap data described by an
  in-process offset convention, not a `#[repr(C)]` struct on the frozen interface edge.
- **No `cranelisp-platform` `public-api.txt` move on the backend side.** Adding the
  `IO_TAG_SELECT` const mirrors the `IO_TAG_LAUNCH`/`IO_TAG_EFFECT_POLL` additions — a
  `/platform` one-liner alongside the other CORE IO tags.
- **No `ABI_VERSION` bump.** The Select node is **host-built and host-interpreted**; it never
  crosses the platform DLL ABI (a branch's leaf effect is an ordinary `IO_TAG_EFFECT`/`_POLL`
  node inside its sub-tree, unchanged). Node layout = in-process convention, not a struct ABI
  freeze (the §14.7/§15.2 ruling).

**NO `cranelisp-types` AST marker is needed — and this is the decisive structural verdict
that separates the combinators from `Par`/`Launch`.** `Par` lowers from `Expr::ParBind` and
`Launch` from `Expr::LaunchContinue` (FIXME 0466) **because they are INFERRED** — the `/int`
bind-chain independence analysis *produces* those AST nodes; they have no source-level
operator. `race`/`select`/`timeout` are the **opposite**: they are **user-written explicit
combinator calls** that appear in source as ordinary `Apply` of a `race`/`select`/`timeout`
name. They are recognized and lowered by **name-match at the backend's `BuiltinFn`
apply-dispatch arm** — **exactly the `bind` inline-primitive precedent**
(`apply.rs:269`, `if op_name.as_ref() == "bind"` → `compile_bind_inline`). No new
`Expr`/`MonoExpr` variant, no `PrimitiveKind` (that enum is retired — S69; inline-eligibility
is encoded per-call-site by the backend recognizing the operator name, `module.rs:1934`).

> **Verdict: NO `/arch` FIXME is warranted for a `cranelisp-types` marker.** This **contrasts
> with §15.3** (launch *did* file FIXME 0466 for the `LaunchContinue` marker — because launch
> is inferred). The combinators are the `bind` shape: explicit, name-matched, no marker. The
> only seeding required is registering `race`/`select`/`timeout` as **inline builtins with
> their signatures** in the primitives/bootstrap module + `/typecheck` resolving them to
> `ResolvedCall::BuiltinFn { name }` — the *same* path `bind` already takes, using the
> *existing* `DefKind` machinery (no new variant). That seeding is `/int` (bootstrap) +
> `/typecheck` (resolution) + `/spec` (the §12 typing, FIXME 0447 second half) work; the
> backend's contract is only "I name-match `select` (and optionally `race`) and build the
> `IO_TAG_SELECT` node." If `/spec`/`/typecheck` discover the combinators need a typing facility
> the inline-builtin path cannot express (e.g. a row/sum result, §16.6), THAT would be the
> trigger for a FIXME — but the node design below is typing-agnostic and needs none.

### 16.3 Recognition + lowering — `select` the sole backend node primitive; `race`/`timeout` are stdlib sugar

`effect-concurrency.md §9`: "**Minimize the irreducible primitive set.** The trampoline needs
to interpret only `race`/`select` + structured cancellation. Everything else is derived." The
backend takes this one step further at the *node* level: **`select` is the sole
backend-built node primitive**, and `race` (binary) + `timeout` (Duration) are **derived
`.cl` stdlib** over it:

- `race a b` = `(select (list a b))` — a 2-element branch list, then `select`. No backend
  code; `race` never reaches `compile_select` directly, it reaches it *through* its stdlib
  body's `(select …)`.
- `timeout d io` = `(select (list (map Some io) (do (sleep d) (pure None))))` — both branches
  `IO (Option a)`; the `Some`/`None` wrapping is stdlib `map`/`pure`. Derived; no backend.

So the backend's whole Chunk-C codegen surface is **one recognition arm + one thin-node
builder** (`compile_select`). This is the leanest realization of the §9 minimization.

> **Optional binary fast-path (documented alternative, not the recommendation).** If
> `/stdlib`/`/spec` find the 2-element `(list a b)` allocation on the per-request-`timeout`
> hot path measurably costly, `race` MAY instead be a **second name-matched backend
> primitive** `compile_race(a, b)` that builds the 2-element list inline and reuses the
> **identical** `IO_TAG_SELECT` construction — **same tag, same trampoline arm, same RC**.
> This keeps the §16.1 one-tag/no-mode verdict intact (it only adds a second *recognition*
> arm, not a second node kind). Default to stdlib `race`; promote to `compile_race` only on
> evidence (Principle 6 — no premature machinery).

### 16.4 The bake — `compile_select`, the simplest IO-node construction

Recognized in `compile_resolved_call`'s `BuiltinFn` arm (the `bind` precedent, `apply.rs:259`),
the combinator takes the **consuming convention** (like `bind`): `compile_consuming_arg_list`
incs heap-typed `Var` args and transfers temporaries, so the node owns the one reference it
stores. Given the compiled branch-list value `branches_val` (the `List (IO a)`):

```
;; compile_select(arg_vals) -> Value      (arg_vals = [ branch_list ])
branches_val = arg_vals[0]                 ; the List (IO a) — rc owned via the consuming list

node = emit_alloc(HeapAdt::payload_size(1))                  ; 32 bytes (header + tag + 1 field)
store iconst(IO_TAG_SELECT=6) at node + HeapAdt::TAG_OFFSET
store branches_val            at node + HeapAdt::field_offset(0)   ; ownership transfer, NO extra inc
return node
```

This is **byte-for-byte the launch-node bake shape** (§15.4) minus the null-guard concern —
`emit_alloc(payload_size(1))` + store tag + store the one field. No GOT load, no
state-closure, no operand peel, no continuation. The `field_offset(0)` store is a **plain
ownership transfer with no `rc_inc`** (the Decision-24 single-consuming convention — a `Var`
branch-list arg was already inc'd by `compile_consuming_arg_list`; a temporary transfers its
rc=1): the node owns exactly the one list reference handed to it, identical to how
`compile_bind_inline` (`apply.rs:1478`) and `compile_par_bind` (`par_bind.rs:89`) take
ownership of their stored fields. `compile_select` reuses `heap::emit_alloc` +
`heap::heap_store` and adds **no** new helper.

### 16.5 RC — list-carrier ownership; NO null-guard, NO per-branch backend RC (the cancellation=drop seam)

The Select node's RC is the **simplest of the IO-node family** — simpler than both `Par`
(custom N-slot drop) and `Launch` (move-out + null-guard):

**The node owns the branch list for the whole tree lifetime.** Unlike `Launch`, the Select
node does **not detach** anything: every branch is polled, won, or cancelled **within** the
trampoline's processing of the Select node — there is **no sub-tree that outlives the node**.
So there is **no move-out and NO null-guarded drop glue** (the §15.5 null-guard is the
*contrast* case here, not the model). The node retains its field-0 list reference until the
**whole launching tree** is freed (REPL cleanup / process exit, §6), exactly as `Par` retains
its branch references.

**The backend does NO per-branch RC.** Because the branches live inside the `List (IO a)`,
the list — not the backend — owns the N branch references and provides the per-element drop
glue. The backend stores **one** field (the list); it never iterates the branches. This is
the payoff of the list-carrier shape over a `Par`-style inline array (where the backend's
drop glue must dec each of N inline slots).

**Cancellation = drop is a *futures* concern, not a *heap-RC* concern — the load-bearing
division with `/design int`.** The runtime (`reactor.md`) polls all branch sub-trees as
futures on the reactor (first-ready-wins); the **losers are cancelled by dropping their
in-flight futures** (`EffectPoll`s), which releases their permits via the **RAII `Permit`
drop-guard** (the A→C contract, gate (a) / §2.9) and — under Chunk C's volume — actively
deregisters their reactor fd/timer interest (A3 finding #3, `reactor.md §2.9`/§2.14). That
drop operates on the **Rust-side futures + reactor registrations**; it does **NOT** dec the
loser **heap** sub-trees. The loser (and winner) branch sub-trees are reclaimed **uniformly**
by the Select node's drop glue → the list's element drop glue, at the end of the run — the
same liveness model the trampoline already relies on (§6: read by raw pointer, no per-node
RC; the tree stays live via the top reference). 

> **Cross-crate seam (backend ↔ intrinsics).** The backend guarantees: (1) the Select node
> owns the branch `List` at field 0 after construction (one reference, consuming-transfer);
> (2) field-0 drop glue is a **standard unconditional `AlwaysHeap` dec** of the list (it
> cascades to every branch). The intrinsics trampoline guarantees: (3) it reads the branches
> by raw pointer (no RC, §5.2/§6) and never frees a branch sub-tree itself; (4)
> "cancellation = drop" drops the **loser futures** (releasing permits + deregistering
> interest), leaving the loser **heap** sub-trees for the node's drop glue (2) to reclaim
> with the rest of the list. (1)+(2)+(4) make every branch — winner and loser — freed
> **exactly once**, by the node drop glue, with **no move-out, no null-guard, and no new RC
> subtlety on the backend side** (the opposite of §15.5). This is the clean contrast to
> launch's detach.

### 16.6 How the winner's value threads back — via the surrounding `Bind`, NO result slot on the node

The winner's value becomes the Select node's result and threads back through the **existing
"inner yields a value, pop the continuation" contract** (§5.1) — the *same* path `Pure`,
`Effect`, and `Par` use. When the trampoline's `IO_TAG_SELECT` arm determines the winner, it
forces the winning branch's sub-tree to its `Pure`/`Effect` value and yields that value; the
continuation popped from the surrounding `Bind` (§16.1) runs with it. So:

- **The Select node carries NO result slot.** The §14 poll node has a `state+0` result slot
  **because the platform poll-fn writes its i64 result into the env** for `EffectPoll` to read
  generically — that is a *leaf* concern. A combinator's "result" is not produced by the node;
  it is whichever **branch's own forced value** the trampoline selects. The branch's value
  comes from that branch's `Pure`/`Effect` leaf the ordinary way, so no result slot is
  reserved on the Select node (the result-slot convention is the poll-leaf's, not the
  combinator's — an important contrast to model on §14 only by *negation*).
- **Winner-value RC needs no special handling.** The winner's `Pure` value lives in the
  winner branch sub-tree, which lives in the list, which the Select node owns, which the top
  tree holds live (§6) — so the value stays live for the continuation, and is freed with the
  tree at the end like every other heap value the trampoline threads. No inc, no move.
- **Typing = `IO a` (the winner's value), per `effect-concurrency.md §9`.** `race`/`select`
  both yield the winner's `a` — **no index, no `(Which, a)` sum**. The node design is
  **typing-agnostic**: it threads back whatever the winning branch produced. IF `/spec`/`/typecheck`
  later land an index-carrying surface (e.g. `select : List (IO a) → IO (Nat, a)`), that is a
  **runtime** concern — the trampoline would pair the winning index with the value — and it
  changes **no node shape and no backend codegen** (the backend never inspects the result). 
  Coordinate the final typing with `/spec` (FIXME 0447 second half) and the runtime
  index-pairing with `/design int`; neither touches §16.4/§16.5.

### 16.7 Drop glue — standard one-heap-field ADT

The Select node is a standard **one-heap-field ADT** (field 0, the `List (IO a)`). Its drop
glue is generated by the existing `emit_inline_drop_glue` path (§3.4): field 0 is a plain
**unconditional `AlwaysHeap` dec** (the list is always a heap pointer) — **no null-guard**
(§16.5, contrast §15.5/§15.6), no per-branch walk. The list's own element drop glue cascades
to dec each branch IO sub-tree. The node itself participates in RC normally: it is the
`inner_io` of a `Bind`, transferred into that `Bind` like any inner IO (§2.1), and freed when
the launching tree is freed (§6). No `drop_state` hook, no state-closure — the Select node
carries only the list pointer.

### 16.8 Trampoline interaction (intrinsics-owned — stated for the seam)

The node construction is the backend's whole job; the **interpretation** is the trampoline's
(`run_io_trampoline_inner_async`, `cranelisp-intrinsics`; authoritative design `/design int`,
`reactor.md`). Stated here only to pin the seam: the `IO_TAG_SELECT` arm reads the branch list
off field 0, **partitions the branches by reachable leaf tag** (poll-shape → reactor,
blocking → rayon — the **same two-pool partition `Par` already uses**, §13.5, no new backend
codegen), polls them **first-ready-wins** (`futures` `select`/`select_all` over the poll
partition + a wakeable bridge to the blocking partition, §13.5), yields the winner's value,
and **drops the loser futures** (cancellation = drop → RAII `Permit` release + active
interest deregistration, §16.5). The backend's contribution to the partition is the
guarantee that each branch sub-tree carries the **correct leaf tags** (which the existing
effect arms already emit) — "partition by tag" is the trampoline's *classification* of each
branch's reachable effect leaf, an `io.rs`/`reactor.md` detail (the §13.5 boundary item),
not a backend concern.

### 16.9 Unit-test seams for `/dev` (backend tier)

Per the unit-test-per-fix discipline — inspect via CLIF (`CRANELISP_CODEGEN_TRACE=1`) on a
shrunk `(bind! [x (select branches)] x)` repro (small repro → small CLIF readable by eye):

- **Select-node shape.** A `select` call constructs an `IO_TAG_SELECT` node of
  `payload_size(1)` (32 bytes) storing the literal tag `6` at `TAG_OFFSET` and the compiled
  branch-list pointer at `field_offset(0)`. Assert the alloc size + the two stores.
- **Wrapped by a `Bind`.** A `(bind! [x (select …)] …)` site emits `Bind(Select, cont)` — an
  `IO_TAG_BIND` node whose `inner_io` (field 0) is the `IO_TAG_SELECT` node and whose `cont`
  (field 1) is the ordinary continuation closure (built by `compile_bind_inline`, not by
  `compile_select`). Assert both tags appear and the nesting (the structural slot `Par`/`Launch`
  also occupy).
- **Ownership transfer, no extra inc at the field-0 store.** A temporary branch-list
  (rc=1) is stored with **no `rc_inc`** at the store site (consuming convention); a `Var`
  branch-list is inc'd **once** by `compile_consuming_arg_list` and not again. Assert there is
  no double-inc (the `bind`/`par_bind` RC balance).
- **Unconditional (not null-guarded) field-0 drop glue.** The Select node's generated drop
  glue dec's field 0 **unconditionally** (`AlwaysHeap`) — **distinct from the launch node's
  null-guarded dec** (§15.5/§16.7). Assert there is no null-compare before the dec (the
  contrast that proves the no-move-out model).
- **No-combinator negative guard.** A program with no `race`/`select`/`timeout` call
  constructs **no `IO_TAG_SELECT` node** — the structural no-regression property (ordinary
  programs are unaffected; the recognition arm falls through to the unchanged `bind`/effect/
  `Apply` arms).

End-to-end seams (`race`/`timeout` returns the winner; the loser's permit is released on
drop; `timeout` fires after `d`; cancel-on-disconnect drops the request's in-flight polls;
graceful shutdown drops all in-flight strands) are `/qa` integration seams driven through
`cranelisp_run_io` + the reactor — they are listed in `effect-concurrency.md §9`/`reactor.md`
and are **not** backend-unit-tier.

### 16.10 Implementation steps for `/dev` (backend half) — in this order

1. **Add `IO_TAG_SELECT = 6`** to the IO tag constants in `cranelisp-platform`
   (`lib.rs`, alongside `IO_TAG_LAUNCH = 5`, CORE/ungated — §16.2). The backend emits the
   literal `6` at the bake (no platform-const read at codegen, the `par_bind.rs`/`launch.rs`
   convention).
2. **Recognize `select`** (and, only if the §16.3 fast-path is taken, `race`) by name in
   `compile_resolved_call`'s `BuiltinFn` arm (`apply.rs:259`), the `bind` precedent — compile
   args via `compile_consuming_arg_list`, then dispatch to `compile_select`. **No** new
   `Expr`/`MonoExpr` variant, **no** `PrimitiveKind` (§16.2). (Depends on `/int` bootstrap +
   `/typecheck` seeding `select`/`race`/`timeout` as inline builtins with their `§9`
   signatures — that is their work, not the backend's; the backend only name-matches.)
3. **Implement `compile_select`** (§16.4): `emit_alloc(payload_size(1))`, store tag `6` +
   the branch-list pointer (ownership transfer, no inc). The simplest IO-node builder — reuse
   `heap::emit_alloc`/`heap::heap_store`; add no helper. The surrounding `Bind(Select, cont)`
   reuses the existing `compile_bind_inline`.
4. **Generate the Select drop glue as a standard unconditional one-heap-field ADT dec**
   (§16.7) — the existing `emit_inline_drop_glue` path, field 0 `AlwaysHeap`, **no**
   null-guard (the explicit contrast with launch). Pin the §16.5 cross-crate seam with
   `/design int`: the node owns the list for the tree lifetime; cancellation drops the loser
   **futures**, not the loser heap.
5. **Confirm the no-combinator negative guard** (§16.9) — ordinary programs construct no
   `IO_TAG_SELECT` node and emit unchanged codegen.

### 16.11 Quality attributes touched

- **Simplicity / complexity budget (Principle 6).** The slice adds **one tag, one thin
  single-field node, one recognition arm, one bake, and one standard drop-glue field** — the
  simplest IO-node construction (simpler than `Par`'s N-slot drop and `Launch`'s move-out).
  **One tag, no mode field, no second node kind** for race+select+timeout; `race`/`timeout`
  are derived stdlib (the §9 minimization). No `#[cfg]`, no new AST variant.
- **Maintainability / single source of truth (Principle 7).** Recognition reuses the `bind`
  inline-primitive arm; construction reuses the constructor-convention store shared by
  `bind`/`par_bind`/`launch`/`compile_poll_effect`; the two-pool branch partition reuses
  `Par`'s (§13.5, no new dispatcher). One node kind serves all three combinators.
- **Concurrency-safety (Principle 1).** The backend emits **no concurrency primitive** — it
  constructs a value (the Select node) and a standard drop path. All poll/first-ready/
  cancel-drop/permit-release lives in the reactor. The RC division (node owns the heap list;
  cancellation drops only the futures) means the combinators introduce **no new backend RC
  subtlety** — the cleanest member of the family.
- **Testability (Principle 5).** The arm emits an inspectable node shape (tag + one field +
  an unconditional dec), unit-testable at the CLIF seam without a running reactor; the
  first-ready/cancel/timeout behaviour is cleanly the reactor's, tested separately by `/qa`.

> **§16.12 — Fresh-continuation-produced `select`/`par` node leak (S97, FIXME 0474).** The
> §16.5/§16.7 RC model (node owns the branch list; drop glue cascades to free every branch
> exactly once) is correct for **caller-tree** select/par nodes — `consume_io_tree`'s
> `IO_TAG_SELECT`/`IO_TAG_PAR` arms walk the branch container. A node produced **fresh by a
> bind continuation** (`(bind X (fn [_] (select […])))`) is instead released by the
> trampoline's *shallow* fresh-node path (`dec_shallow_io`), which frees the node header but
> **not** its branch container → the branches leak. The ruling (apply to **BOTH** tags) is
> **`ring2-rc.md §3.5.10`** — the fresh-node release path becomes shape-aware for these two
> multi-child tags and deep-frees the branch container (reusing the `consume_io_tree` branch
> arm), keeping the spine tags (Pure/Effect/Bind) shallow. See there for the full design call.

---

## 17. ABI v9 — the ctx-vtable handle model: poll-node emit is a DELETION pass (S97, Wave 0 re-cascade)

> **REWRITTEN for the `/arch`-ratified ctx-vtable handle model (2026-06-30; supersedes the
> descriptor cut).** §17.1–§17.6 below are the **live** backend delta. Conforms to
> `design/arch/effect-concurrency.md` §4.1.1 (the ctx-vtable model), `platform-interface.md`
> §6.8.0b, `bounded-contexts.md` §3, and the platform-side leaf-authoring contract
> `design/platform/poll-support.md` §3.1/§3.5/§3.6 (the uniform poll-fn skeleton). The earlier
> §17 descriptor-cut design — a fixed-offset `ResourceDesc` **header slot @24** on
> resource-handle ADTs, a baked poll-node **`role`@32** + **`desc_out` `ResourceDesc` region
> @40**, the **§17.5 offset contract**, and the **§17.7/§17.8** wiring/QA notes written to it —
> is **RETIRED**; it is preserved under the **[SUPERSEDED]** banner at §17.7 (provenance only,
> read for the rejected shape + why). FIXME 0482 is **deleted** (resolved-by-supersession).
>
> **The whole backend delta under the new model is a *subtraction*.** Scheduling state
> (`token`/`capacity`) never rides on a value and never rides on the poll node — it flows
> entirely through a trampoline-owned `ctx` vtable the **platform poll-fn** calls
> (`acquire`/`register_*`/`retire`), with **trampoline-owned release** on `Ready`/cancel
> (`effect-concurrency.md` §4.1.1). So there is **no header slot to reserve, no `role` to bake,
> no `desc_out` slot to allocate, no per-role stamp/read hook to emit**. `PollFn`/`Poll` are
> **unchanged**. The hard parts of the dead design (the resource-handle ADT slot reservation +
> the undesigned DLL-mint→host-alloc seam that STOPPED Wave 2) are **gone**. The v9 cut still
> lands as ONE atomic change-set (the `cranelisp-types` ABI bump reds the tree until consumers
> catch up; `ABI_VERSION` 8 → 9), but the backend's contribution to it is the two deletions in
> §17.3 + a `CACHE_SCHEMA_VERSION` bump.

### 17.1 What changes, in one paragraph

**The poll node stays the v8 uniform shape; the only backend change is deletion.** Under the
ctx-vtable model the descriptor `(token, capacity)` is neither a cranelisp value, nor a leaf
argument, nor anything stored on the node or on a handle: the platform's poll-fn **computes the
token from the handle it holds** (web: `token == fd`, off `Connection`'s genuine `fd` field —
`poll-support.md` §3.5.1) and **calls `ctx.acquire(token, capacity, waker)` itself**
(`effect-concurrency.md` §4.1.1 skeleton). The v8 backend baked `(token, capacity)` into the
poll node from the **two leading positional leaf args** (§14, the `inject_poll_leading_pair`
convention). **v9 deletes that pass and its positional peel** — there is nothing to bake in its
place. The poll node retains its v8/§13/§14 layout (`state_closure` heap field + the two
admission slots, now simply **unused / zero**), and `compile_poll_effect` treats the leaf args
as `arg_vals[0..]` directly. That single deletion is the backend's entire v9 reshape (§17.3).
`ring2-rc.md §3.5.10` (the 0474 fresh-select/par deep-free ruling) is **model-independent and
unaffected** (§17.4 cross-ref).

### 17.2 The poll node is UNIFORM — no header slot, no role, no desc_out

There is **no resource-handle ADT layout change**. The opaque handle `web/Connection` is an
**ordinary 1-field ADT** — `(deftype Connection [:primitives/Int fd])` — laid out as the
standard `HeapAdt` (`header(16)` + ctor-`tag @ 16` + `fd @ FIELDS_START = 24`). It is minted by
the normal `CLAdt::construct` path (the platform built the handle; `r == fd` lives in its
genuine field). **No reserved descriptor region, no `RESOURCE_DESC_OFFSET`, no `FIELDS_START`
shift, no zero-init of any slot, no "resource-handle type set" the backend must derive from
manifests at layout time.** Every ADT — resource handle or not — keeps `FIELDS_START = 24`.
This is the dissolution of the Wave-2 blocker: a 1-field `Connection` is a normal N-field
object, so the 24-vs-40-byte DLL-mint overrun **cannot arise** (`effect-concurrency.md` §4.1.1;
`poll-support.md` MODEL-PIVOT banner).

The poll node (`IO_TAG_EFFECT_POLL = 4`) keeps the v8 shape exactly (§12.2 / §13.3 / §14):
`state_closure` heap field (RC'd, drop-glue'd) + the two admission slots that v8 baked
`(token, capacity)` into. **Under v9 those two slots carry nothing the trampoline reads** — the
backend bakes neither the v8 positional `(token, capacity)` nor any v9 `role`/descriptor; they
are inert (left at the §13.3 zero/sentinel `iconst`s, or elided — `/dev`'s call, no semantic
content either way). **No node growth** (it does NOT grow 48→56), **no `role` field at +32**,
**no `desc_out` region at +40**. The node remains a one-heap-field ADT, so §13.6/§14.6 drop
glue is untouched.

Because `PollFn`/`Poll` are unchanged (`poll(state, *HostCtx, *Waker) -> Poll`, single-register
`#[repr(i32)]`), **`cranelisp-types` poll-node codegen is untouched** — the host-built
state-closure env layout (§12.2: result @ `state+0`, args @ `state + 8 + 8·i`, scratch after)
is byte-for-byte the same. The only consequence of v9 for that codegen is the bake-deletion in
§17.3 (the env now packs `arg_vals[0..]` with no leading-pair peel).

### 17.3 The delete — `inject_poll_leading_pair` + the positional peel

Two deletions, both in `cranelisp-backend`:

1. **Delete `inject_poll_leading_pair`** (`lib.rs`, the `MonoExpr` pass — its ~14 call sites
   and the `compile_to_module_impl` invocation) entirely: the pass, its `scheduling_class`
   keying, and its `(0,1)`-sentinel synthesis all go away. There is no surviving caller — under
   the ctx-vtable model nothing prepends a leading pair, because the platform leaf acquires the
   token itself (§17.1).
2. **Delete the `arg_vals[0..1]` positional peel in `compile_poll_effect`** (§12.3 / `apply.rs`):
   the leaf-arg list is `arg_vals[0..]` directly, marshaled into the state-closure env at
   `capture(1+i)` (result @ `capture(0)`). The §14.2/§14.3 leading-pair peel is removed — a poll
   leaf's natural args are its only args.

Everything else in `compile_poll_effect` (the node alloc, the state-closure build, the
`code_ptr`/`drop_glue_ptr` wiring, the RC) is unchanged. There is **no per-role branch, no node
shape branch, no manifest read at layout time** — the construction site is the uniform v8 path
minus the peel.

### 17.4 Cache invalidation, public-api, and the 0474 cross-ref

- **`CACHE_SCHEMA_VERSION` bump (required).** The emitted poll-node arg handling changes (the
  env now packs the natural leaf args at `capture(1..)` with no leading-pair displacement), so a
  stale `.o` cached under the v8 leading-pair convention would marshal args at the wrong
  capture slots. The cutover change-set bumps `CACHE_SCHEMA_VERSION` so every cached artifact
  re-derives (`module-caching.md` — the schema-version gate). This is the v8→v9 marker on the
  backend side.
- **`public-api.txt` — almost certainly UNCHANGED for `cranelisp-backend`.** v9 is a pure
  *deletion* of an internal pass (`inject_poll_leading_pair` is not a public export) plus an
  internal peel removal — neither moves the backend's public surface. **Flag:** regenerate it
  in the cutover change-set regardless (baseline-diff discipline, `design/arch/CLAUDE.md`) and
  include the diff; the expectation is an **empty backend diff**. If `/dev` finds the pass *was*
  re-exported (it should not be), that removal is the only line and `/review` confirms it.
  (The ABI-surface regen the arch ruling names — `cranelisp-types` + `cranelisp-platform` for
  the `ResourceDesc`-delete / `ConcurrencyDescriptor.role` / `HostCtx` ctx-vtable additions —
  rides the same change-set but is `/dev`-on-those-crates, not backend.)
- **0474 stands, model-independent (§17.5 cross-ref → `ring2-rc.md §3.5.10`).** The fresh
  `IO_TAG_SELECT`/`IO_TAG_PAR` deep-free ruling is about IO-node branch-`Vec` freeing in the
  trampoline's fresh-node release path; it has nothing to do with descriptors or scheduling
  state. It is **unaffected by the S97 model pivot** and STANDS as written. FIXME 0474 stays
  **open** (Phase-5 /qa heap-balance guard + /dev fix; do not delete the FIXME).

### 17.5 The codegen↔trampoline boundary under the ctx-vtable model

This is the boundary statement the `/design` (int) pass implements against. **There is no
shared offset contract anymore** — the §17.5 frozen offset table of the dead descriptor design
(`RESOURCE_DESC_OFFSET = 24` / poll-node `role @ 32` / `POLL_DESC_OUT_OFFSET = 40`) is
**RETIRED**, because nothing crosses the codegen↔trampoline seam by baked offset under the new
model. Crisply:

**Codegen (backend) owns** — only the uniform poll node + the leaf args:
- emit the v8-shape `IO_TAG_EFFECT_POLL` node with its `state_closure` (unchanged);
- pack the leaf's natural args `arg_vals[0..]` into the state-closure env (no leading-pair
  peel); the env convention (§12.2) is unchanged, so the platform poll-fn reads its handle at
  `PollEnv::arg(0)` = `state + 8` exactly as before;
- bake **nothing** scheduling-related onto the node (no `role`, no `(token, capacity)`, no
  `desc_out`). The backend emits **no acquire, no register, no retire, no stamp, no read, no
  header write** — it never names a scheduling primitive.

**Trampoline (int, runtime) owns the entire ctx vtable** (`effect-concurrency.md` §4.1.1;
`reactor.md` §7, /design int Wave-0 re-cascade):
- it implements the `ctx`/`HostCtx` the platform poll-fn calls — `acquire(token, capacity,
  waker) -> Acquired | Parked`, `register_{readable,writable,timer}(source, waker)`,
  `retire(token)` — backed by the §8.1 per-token permit map (semaphore-per-token, keyed by the
  waker's effect identity) + the reactor interest table;
- it owns **release** (tramp-owned, on poll `Ready` or cancel, keyed by effect identity; cancel
  never re-enters the poll-fn) — release is **not** a vtable call;
- it never introspects the handle and holds no handle→token scoreboard — the platform poll-fn
  computes the token from its own handle each poll and the host recomputes nothing.

So the seam is: **backend hands the trampoline a uniform poll node + the leaf's natural args;
the platform poll-fn drives all scheduling through the trampoline-owned ctx vtable.** The
backend↔trampoline interface for poll effects is exactly its v8 shape *minus* the leading-pair
convention — there is no v9-specific offset either side must agree on.

### 17.6 Quality attributes touched

- **Simplicity / complexity budget (Principle 6).** v9 is a **net subtraction at the backend
  layer** — it deletes a whole codegen pass (`inject_poll_leading_pair` + its `scheduling_class`
  keying + its `(0,1)` synthesis) and the positional peel, and adds **nothing** (no header slot,
  no role bake, no desc_out — all of which the dead descriptor design would have added). This is
  strictly less machinery than even the v8 baseline.
- **No-interim-implementations (Principle 8).** v9 *removes* the v8 leading-pair interim; the
  uniform poll node + platform-driven ctx vtable is the end-state. The backend builds nothing to
  be discarded.
- **Maintainability / single source of truth (Principle 7).** All scheduling lives in **one
  place** — the trampoline's ctx vtable + permit map (int). The backend no longer holds any
  scheduling knowledge (no offset constant, no manifest-derived resource-handle type set, no
  role), so the cross-crate offset-drift class the dead §17.5 table guarded against **cannot
  exist** — there is no shared baked offset to drift.
- **Concurrency-safety (Principle 1).** Unchanged: the backend emits no concurrency primitive;
  it lays out a uniform node and passes leaf args. All acquire/register/retire/park/release lives
  in the trampoline.
- **Testability (Principle 5).** The deletion is inspectable at the CLIF seam on a shrunk repro
  (`CRANELISP_CODEGEN_TRACE=1`): a poll effect's construct has **no `arg_vals[0]/[1]` positional
  store displaced ahead of the natural args** (the deleted bake is the negative guard) and the
  node is the v8 shape (no growth, no `role` at +32). A resource-handle ADT (`Connection [fd]`)
  is a plain 1-field ADT at `FIELDS_START = 24` (the byte-identical-to-ordinary-ADT witness).
  The runtime ctx-vtable behaviour is the trampoline's, tested separately by `/qa` + /design int.

### 17.7 [SUPERSEDED — provenance only] the descriptor-cut emit design (RETIRED by the ctx-vtable pivot)

> **RETIRED (2026-06-30) — do not implement.** Everything in §17.7.x below is the dead
> descriptor-cut design (`ResourceDesc` header slot @24, poll-node `role`@32 + `desc_out`
> region @40, the per-role stamp/read hooks, the frozen offset contract, the resource-handle
> type-set wiring). It is kept for provenance — the rejected shape + the Wave-2 blocker that
> killed it — and is **superseded in full** by §17.1–§17.6 above and `effect-concurrency.md`
> §4.1.1. The descriptor never rides a value (no header slot), `PollFn`/`Poll` are unchanged
> (no `desc_out`), and the trampoline owns the ctx vtable (no baked `role`, no offset contract).
> The blocker that retired it: an opaque zero-field `Connection []` minted inside the DLL via
> `CLAdt::construct` was a 24-byte object with no room for a 16-byte header slot stamped at
> `value+24`, and reserving that slot at the DLL-mint→host-alloc boundary was an undesigned
> cross-crate interface (SPRINT.md "Wave 2 STOP" note). The ctx-vtable model dissolves it by
> giving `Connection` a genuine `fd` field and never touching the value with scheduling state.

#### 17.7.1 [retired] Job (a) — reserve the `ResourceDesc` header slot on resource-handle ADTs

**Which ADTs.** A type `T` is a **resource handle** iff a loaded platform manifest marks some
effect `Produce`/`Consume` (`ConcurrencyDescriptor.role`) with `T` as the produced/consumed
handle type — e.g. `web/Connection` (produced by `accept-conn`, consumed by `read-conn`/
`send-conn`). The backend computes this **resource-handle type set** from the loaded manifests
and consults it at ADT layout + field-access codegen. (Wiring note — §17.7: the set is
derived where the backend already resolves effect targets; this is the one new piece of
manifest-derived state the backend reads.)

**The slot — fixed offset 24, uniform across all resource-handle types.** A resource-handle
ADT lays out as the standard `HeapAdt` (`header(16)` + ctor-`tag @ 16`) **plus a 16-byte
`ResourceDesc` region immediately after the tag**, with logical fields shifted to start
after it:

```
resource-handle ADT (e.g. web/Connection):
  +0   alloc_size : i64        HeapHeader
  +8   rc         : i64        HeapHeader
  +16  ctor tag   : i64        HeapAdt::TAG_OFFSET (unchanged — every ADT has it)
  +24  ResourceDesc.token    : u64    ⟍ the fixed-offset DESCRIPTOR HEADER SLOT
  +32  ResourceDesc.capacity : u32    │ (16 bytes; RESOURCE_DESC_OFFSET = 24, uniform)
  +36  ResourceDesc._pad     : [u8;4] ⟋
  +40  logical field 0 …             (RESOURCE_HANDLE_FIELDS_START = 40, NOT 24)
```

`RESOURCE_DESC_OFFSET = HeapAdt::FIELDS_START = 24` is the **single fixed offset** the
trampoline reads with **no per-ADT "token is field N" knowledge** (the property the arch
ruling requires; `interfaces.md` §"Resource descriptor"). For a resource-handle ADT the
logical fields shift to `FIELDS_START + 16 = 40`; field-access codegen for these types uses
`40` (only these types — every other ADT is unchanged at `24`). **web `Connection` is empty
(`deftype Connection []`)**, so it has **zero** logical fields → a 40-byte object
(`header 16 + tag 8 + ResourceDesc 16`); nothing shifts this sprint. The escape-hatch
(`token != fd`, a future `Connection [fd]`) puts its genuine datum at the shifted `40` —
the descriptor region and logical fields **never share a slot** (`poll-support.md` §3.5.1).

**Construction zero-inits the slot.** When the backend emits a resource-handle ADT
constructor (e.g. `accept-conn`'s ready-phase `CLAdt::<Connection>::construct`), it
**zero-inits** the 16-byte descriptor region (`token = 0, capacity = 0`). The trampoline
**stamps** the real `(token, capacity)` into it later from the produce leaf's `desc_out`
(§17.5); a handle is "born unstamped" and becomes stamped at production. **No RC** on the
region — both fields are `NeverHeap` scalars (an opaque identity + a count), so the slot adds
**no drop-glue obligation** (the ADT's logical-field drop glue is unchanged).

**Rejected:** placing the descriptor **after** the logical fields (offset = `24 + 8·n`) — it
would make the slot a per-type offset the trampoline must compute from field count, defeating
"uniform, no per-ADT knowledge." Offset 24 (between tag and logical fields) is the only fixed
uniform choice that leaves the header + ctor-tag undisturbed.

#### 17.7.2 [retired] Job (b) — the poll-node shape: `role` + the `desc_out` `ResourceDesc` slot

The poll node grows from the v8 3-field (48-byte) shape to a 4-field (56-byte) shape; the
v8 `(token, capacity)` slots are repurposed. **The poll node is an in-process backend↔
intrinsics convention (not a struct ABI freeze — §14.7), so this shape change is free of any
`cranelisp-types`/`public-api` touch** — it costs only a `CACHE_SCHEMA_VERSION` bump (§17.6).

```
v9 IO_TAG_EFFECT_POLL node — payload_size(4) = 56 bytes:
  +16  tag           : i64   (= IO_TAG_EFFECT_POLL = 4)        HeapAdt::TAG_OFFSET
  +24  field 0: state_closure : i64   (heap, RC'd)             — UNCHANGED from v8
  +32  field 1: role          : i64   (baked from manifest ConcurrencyDescriptor.role: 0/1/2)
  +40  field 2: desc.token     : u64    ⟍ the 16-byte ResourceDesc region = the `desc_out` slot
  +48  field 3: desc.capacity  : u32    │ (RESOURCE_DESC fields baked-or-zero per role, §17.4)
  +52         desc._pad        : [u8;4] ⟋   POLL_DESC_OUT_OFFSET = HeapAdt::field_offset(2) = 40
```

- **`role` (field 1, abs 32)** is the per-effect static `ResourceRole {None=0, Produce=1,
  Consume=2}` read off the effect's manifest `ConcurrencyDescriptor.role`, baked as a literal
  `iconst`. It tells the trampoline stamp-vs-read-vs-nothing **without a manifest lookup at
  poll time** — the node stays self-describing for admission, exactly the v8 philosophy (the
  node carried `(token, capacity)`; it now carries `role` + the descriptor region).
- **The `ResourceDesc` region (fields 2–3, abs 40–55)** is the **`desc_out` slot**: the
  trampoline passes `node + 40` as the `desc_out: *mut ResourceDesc` argument to the poll-fn
  (`poll(state, host, waker, desc_out) -> Poll`). What the backend bakes into it depends on
  role (§17.4). Both descriptor fields are `NeverHeap` scalars → **no RC, no drop-glue change**
  — the node remains a one-heap-field ADT (only field 0, the state-closure, is heap-typed), so
  §13.6/§14.6's drop glue is untouched.

#### 17.7.3 [retired] Job (c) — delete the positional bake; what the backend stores per role

`compile_poll_effect` (§12.3 / `apply.rs`) **stops** peeling `arg_vals[0]`/`arg_vals[1]` as
`(token, capacity)`. Leaf args are `arg_vals[0..]` directly, marshaled into the state-closure
env at `capture(1+i)` (result @ `capture(0)`) — **the leading-pair peel of §14.2/§14.3 is
removed**; `inject_poll_leading_pair` no longer prepends anything (the pass is deleted, not
re-keyed — its `scheduling_class` discriminator and its `(0,1)` synthesis go away with it).

What the backend bakes into the node, by the effect's manifest `role` (a compile-time
constant from the resolved effect target — **not** from any operand):

| `role` | field 1 (`role`) | `ResourceDesc` region (fields 2–3) at construction |
|---|---|---|
| **Produce** (`accept-conn`) | `iconst 1` | **zero-init** — the produce leaf writes it through `desc_out`; the trampoline reads it back on `Ready` to stamp (§17.5) |
| **Consume** (`read-conn`/`send-conn`; `read-line`) | `iconst 2` | **bake the effect's manifest-static `ConcurrencyDescriptor {token, capacity}`** — `token == 0` (the per-value `ResourceSerial` default, `read-conn`) signals the trampoline to read the **dynamic** descriptor off the consumed handle's header; `token ≠ 0` (a singleton, `read-line`'s `{STDIN_TOKEN, 1}`) signals it to acquire the **manifest-static** token directly with no handle to read (`poll-support.md` §3.1/§3.6.1) |
| **None** (bare timer, `bind-listener`) | `iconst 0` | **zero-init** — never read |

This is the v9 replacement for §14's "synthesize `(0,1)` for tokenless / bake live pair for
resource": **one uniform construction site**, role-keyed, **no positional peel**, **no per-leaf
node-shape branch**. The two Consume cases are the **same** bake — the manifest-static
descriptor — distinguished only by the baked `token`'s zero-ness (effect-concurrency §5:
"token 0 = unrestricted/dynamic"), not by a second node field or a codegen branch.

#### 17.7.4 [retired] Job (d) — the per-role hooks: who does the stamp, who does the read

**The backend reserves slots and emits the node; the trampoline does the runtime stamp/read.**
This is the load-bearing boundary `/design int` and Phase-5 `/dev` implement against. Crisply:

**Codegen (backend) owns:**
1. the `RESOURCE_DESC_OFFSET = 24` header slot on resource-handle ADTs + the shifted
   `FIELDS_START = 40` field-access; zero-init at construction (§17.2);
2. the poll-node `role` bake + the `desc_out` `ResourceDesc` region at `POLL_DESC_OUT_OFFSET =
   40`, baked-or-zero per §17.4 (§17.3);
3. deletion of the positional `(token, capacity)` bake / `inject_poll_leading_pair` (§17.4);
4. the resource-handle type set derived from manifests (§17.7).
   The backend emits **no acquire, no stamp, no header write** — it only lays out storage.

**Trampoline (int, runtime) owns** — reading `role` off `node + 32` and acting:
- **`role == Produce`:** pass `node + 40` (the `desc_out` slot) to `poll(…, desc_out)`. The
  leaf writes `*desc_out = {token, capacity}` before `Ready`. On `Ready` the trampoline reads
  `node + 40` and **stamps** it into the produced value's header (`produced_value +
  RESOURCE_DESC_OFFSET(24)`) — the produced value is a resource-handle ADT (`Connection`) the
  backend laid out with the slot. No pre-poll acquire (accept is structurally serial,
  `poll-support.md` §3.5.2).
- **`role == Consume`:** read the node's baked `ResourceDesc` (`node + 40`). If `token ≠ 0`
  (singleton, §17.4) acquire that manifest-static token. If `token == 0` (dynamic), **read**
  the descriptor off the **consumed handle's header** — the handle is the first leaf arg
  (`arg(0)`), marshaled as the state-closure's `capture(1)` = env offset `state + 8` (the
  poll-fn's `PollEnv::arg(0)`, §12.2: `state` = env base, result @ `state+0`, arg_0 @
  `state+8`); the trampoline reads that handle pointer, then `handle +
  RESOURCE_DESC_OFFSET(24)` → `(token, capacity)` → acquire. Acquire
  **before** the first poll (acquire-around-poll, §14.1 ordering unchanged); release on `Ready`/
  drop (RAII `Permit`). `desc_out` is passed but the leaf ignores it.
- **`role == None`:** poll with a `desc_out` pointer the leaf ignores; no acquire, no stamp.

The **cross-crate offset contract** (the §14.4-style frozen seam — the class that silently
breaks if the two sides disagree):

| Constant | Value | Backend site | Trampoline site |
|---|---|---|---|
| `RESOURCE_DESC_OFFSET` (handle header slot) | **24** | resource-handle ADT layout + construct zero-init | `handle + 24` read (consume); `produced + 24` write (produce-stamp) |
| poll-node `role` | `field_offset(1)` = **32** | `role` bake | `node + 32` read |
| `POLL_DESC_OUT_OFFSET` (= `desc_out`) | `field_offset(2)` = **40** | `desc_out` region bake/zero | `node + 40` passed as `desc_out`; read-back on Produce `Ready` |

#### 17.7.5 [retired] Job (e) — cache invalidation + baseline regen

- **`CACHE_SCHEMA_VERSION` bump (required).** Both baked shapes change vs v8: the poll node
  grows `48 → 56` bytes with a new field meaning (`role` + `desc_out` region, no positional
  `(token, capacity)`), and resource-handle ADTs gain the 16-byte header slot + shifted
  fields. A stale `.o` cached under the v8 shape would mis-read the node/handle at the new
  offsets. The cutover change-set bumps `CACHE_SCHEMA_VERSION` so every cached artifact
  re-derives (`module-caching.md` — the schema-version gate).
- **`public-api.txt` baseline regen rides the cutover (baseline-diff discipline,
  `design/arch/CLAUDE.md`).** `cranelisp-backend`'s baseline is regenerated in the **same**
  change-set as the source reshape (`cargo public-api --omit … -p cranelisp-backend >
  crates/cranelisp-backend/public-api.txt`) and the diff is included alongside. Whether the
  backend edge actually moves depends on what `/dev` exposes (e.g. a new `RESOURCE_DESC_OFFSET`
  const); the discipline is to regen + include the diff regardless, side-by-side with the
  `cranelisp-types`/`cranelisp-platform` regen the arch ruling already names (`ABI_VERSION`
  8 → 9 surface). `/review` (backend) confirms the regen is present in the diff.

#### 17.7.6 [retired] Phase-5 watch items + the resource-handle type-set wiring

- **Resource-handle type set.** The backend must know, at ADT layout + field-access codegen,
  which ADTs are resource handles. Derive it once per session from the loaded manifests where
  the backend already resolves effect targets (`resolve_poll_effect_target` /
  `DefKind::PlatformEffect`): a type is a resource handle iff some effect's
  `ConcurrencyDescriptor.role ∈ {Produce, Consume}` names it as the produced/consumed handle
  type. This is the one new manifest-derived input to layout. **If this set cannot be made
  available at ADT-layout time without a cross-crate interface change, STOP and file a FIXME
  `target: /arch`** — the layout shift (§17.2) depends on it.
- **Empty-bodied `Connection []` marshalling** through `CLAdt`/`web.platform-schema` (the
  platform doc's flagged watch item, `poll-support.md` §3.5.7): the schema regen
  (`/platform-schema web`) must accept a zero-logical-field resource handle whose only
  in-object storage is the descriptor header slot. Confirm `CLAdt::<Connection>::construct`
  emits a 40-byte object (header + tag + descriptor region, no field stores) and that schema
  derivation does not treat the descriptor region as a logical field.
- **`set_result` value still flows the old path.** v9 adds **only** the descriptor channel;
  the leaf's i64 result still lands in the env result slot (`state + 0`) read generically on
  `Ready` (§12.4). The produced `Connection` pointer is that result; the trampoline stamps its
  header after reading it — `set_result` and the stamp are two independent writes (the result
  slot vs the value header), neither widening `Poll` (still single-register `#[repr(i32)]`).

#### 17.7.7 [retired] Quality attributes touched (descriptor-cut)

- **Simplicity / complexity budget (Principle 6).** v9 is a **net subtraction**: it deletes
  `inject_poll_leading_pair` (a whole codegen pass + its `scheduling_class` keying + its
  `(0,1)` synthesis) and the leading-pair peel. What it adds — a fixed-offset header slot, a
  role-keyed node bake — is **less** machinery than the pass it removes (Principle 8 — v9
  removes an interim, it is not one).
- **Maintainability / single source of truth (Principle 7).** Both new offsets
  (`RESOURCE_DESC_OFFSET = 24`, `POLL_DESC_OUT_OFFSET = 40`) are frozen cross-crate constants
  (§17.5) — one backend write site, one trampoline read site each. The descriptor-slot offset
  lives in **one** place per side (`PollEnv::desc_of`/`set_desc` on the platform side,
  `poll-support.md` §3.6.2; the layout const on the backend side), so a slot move is a single
  edit, not a per-leaf drift — the same discipline §12.2's result-slot offset already has.
- **Concurrency-safety (Principle 1).** The backend still emits **no concurrency primitive** —
  it lays out a self-describing carrier (header slot + role + `desc_out`); all
  acquire/stamp/read/park/release/RAII-drop lives in the trampoline. The descriptor is a value
  the backend reserves space for, never one it manipulates.
- **Testability (Principle 5).** Both reshapes are inspectable at the CLIF seam on a shrunk
  repro (`CRANELISP_CODEGEN_TRACE=1`): a resource-handle ADT construct stores zero into
  `+24/+32` and (for `Connection []`) no logical fields; a poll effect bakes `role` at `+32`
  and zero/static into the `+40` region with **no `arg_vals[0]/[1]` positional store** (the
  deleted bake is the negative guard). A non-resource ADT keeps `FIELDS_START = 24`
  unchanged (the byte-identical-off witness). The runtime stamp/read is the trampoline's,
  tested separately by `/qa`.
