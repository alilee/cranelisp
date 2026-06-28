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
`design/int/reactor.md`). Stated here only so the seam is unambiguous: the async
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
