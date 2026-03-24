# Lenient Evaluation Design

Sprint 25 — automatic parallelization of independent `let` bindings.

## 1. Problem

Cranelisp is a pure functional language: all `let` binding expressions are side-effect-free and referentially transparent. When multiple bindings in a `let` block are independent (no binding references an earlier binding's name), they produce the same result regardless of evaluation order. The compiler can evaluate them concurrently without changing program semantics.

Spec §12.4.3 mandates this: an implementation MUST evaluate independent `let` bindings in parallel where a cost heuristic determines it is beneficial.

## 2. Sparkability Analysis

The sparkability analysis is a codegen-internal function. It runs inside `compile_let` at IR generation time, after typechecking is complete. It does not affect the AST, `CheckResult`, or any cross-crate interface.

### 2.1 Algorithm: `find_sparkable_bindings`

Given a `let` block with bindings `[(x0, e0), (x1, e1), ..., (xN, eN)]`:

```rust
fn find_sparkable_bindings(
    bindings: &[(Symbol, Expr)],
    globals: &HashSet<Symbol>,
) -> Vec<usize> {
    let mut bound_names: HashSet<Symbol> = HashSet::new();
    let mut sparkable: Vec<usize> = Vec::new();

    for (i, (name, val_expr)) in bindings.iter().enumerate() {
        let fv = free_vars(val_expr, globals);
        let depends_on_earlier = fv.iter().any(|v| bound_names.contains(v));

        if !depends_on_earlier && is_worth_sparking(val_expr) {
            sparkable.push(i);
        }

        bound_names.insert(name.clone());
    }

    // No point sparking a single binding — need at least 2
    if sparkable.len() < 2 {
        Vec::new()
    } else {
        sparkable
    }
}
```

A binding at index `i` is **sparkable** if:
1. **Independence**: its free variables do not include any name bound by bindings `0..i` in the same `let` block.
2. **Cost threshold**: it is a non-trivial function call (see §2.2).

The full sparkable set must have **at least 2 members**. A single independent binding gains nothing from parallel dispatch — the overhead of IVar creation and thread pool submission exceeds any benefit.

### 2.2 Cost Heuristic: `is_worth_sparking`

A binding expression is worth sparking only if it is a function call (`Expr::Apply`) whose callee is NOT a known-cheap builtin. Known-cheap builtins are:

```
+  -  *  /  =  <  >  <=  >=  not  and  or
```

These operations are single-instruction or near-single-instruction at the hardware level. The cost of IVar creation (~allocation + atomic store), thread pool submission (~deque push), and forcing (~CAS + potential spin) vastly exceeds the cost of evaluating them sequentially.

Expressions that are NOT function calls — literals, variable references, lambda expressions (without application) — are also excluded. Only `Expr::Apply` with a non-cheap callee qualifies.

Non-variable callees (e.g., `((get-fn) arg)` — an application of a computed function) are conservatively treated as worth sparking, since the callee's cost is unknown.

### 2.3 Trace Body Exclusion

Inside `(trace ...)` bodies, sparkability analysis is disabled. Lenient evaluation would interleave traced execution across threads, producing non-deterministic trace output. When `self.in_trace_body` is true, `find_sparkable_bindings` returns an empty vec.

### 2.4 `CRANELISP_NO_LENIENT` Opt-Out

The environment variable `CRANELISP_NO_LENIENT=1` disables automatic sparking entirely. This is a debugging escape hatch — when concurrent evaluation makes a bug harder to reproduce, sequential evaluation restores deterministic binding order.

Implementation: a `LazyLock<bool>` static, checked once per process:

```rust
static LENIENT_DISABLED: LazyLock<bool> =
    LazyLock::new(|| std::env::var("CRANELISP_NO_LENIENT").map_or(false, |v| v == "1"));
```

When `*LENIENT_DISABLED` is true, `compile_let` skips sparkability analysis and compiles all bindings sequentially.

## 3. IVar Runtime Primitives

IVars are write-once synchronization cells. They live in `cranelisp-runtime` as `extern "C"` functions registered as JIT builder symbols.

### 3.1 Heap Layout

IVars are heap-allocated, RC-managed values using the base-pointer convention (arch Decision 10):

```
Base pointer →
  +0   alloc_size: i64   (= 40)
  +8   rc: i64           (initial: 1, atomic)
  +16  state: i64        (atomic — PENDING/EVALUATING/RESOLVED)
  +24  value: i64        (result, valid when state = RESOLVED)
  +32  thunk: i64        (closure pointer — zero-arg thunk)

Total allocation: 40 bytes (16 header + 24 payload)
```

The base pointer points to offset 0 (alloc_size), not the payload. This follows the reimplementation's base-pointer ABI. All field accesses use positive offsets from the base pointer.

### 3.2 State Machine

Three atomic states, using i64 constants:

| State | Value | Meaning |
|---|---|---|
| PENDING | 0 | Thunk has not been evaluated; value field is invalid |
| EVALUATING | 1 | A thread has claimed the thunk and is executing it |
| RESOLVED | 2 | Thunk has been evaluated; value field contains the result |

State transitions:
- `PENDING → EVALUATING`: via CAS in `ivar_force`. Exactly one thread succeeds.
- `EVALUATING → RESOLVED`: via atomic store in `ivar_force`, after storing the result. Only the thread that won the CAS performs this transition.

No other transitions are valid. There is no `PENDING → RESOLVED` shortcut.

### 3.3 `cranelisp_ivar_create`

```rust
#[unsafe(export_name = "cranelisp_ivar_create")]
pub extern "C" fn ivar_create(thunk: i64) -> i64
```

**Semantics**: Allocate an IVar cell. Set `state = PENDING`, store the thunk pointer, return the base pointer.

**Implementation**:
1. Call `alloc_with_rc(24)` — 24 bytes payload (16 header added by allocator = 40 bytes total). The allocator sets `alloc_size = 40` at offset 0 and `rc = 1` at offset 8.
2. Store `PENDING (0)` at offset 16 (state).
3. Store `0` at offset 24 (value — unused until resolved).
4. Store `thunk` at offset 32 (thunk closure pointer).
5. Return the base pointer.

The thunk pointer is a Cranelisp closure with the reimplementation's `HeapClosure` layout: `[header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]`. It is a zero-argument thunk — the code_ptr has signature `extern "C" fn(env_ptr: i64) -> i64`.

### 3.4 `cranelisp_ivar_spark`

```rust
#[unsafe(export_name = "cranelisp_ivar_spark")]
pub extern "C" fn ivar_spark(ivar: i64) -> i64
```

**Semantics**: Increment the IVar's RC (the spark task holds a reference), then submit a force-and-dec task to the rayon global thread pool.

**Implementation**:
1. Atomically increment RC at `ivar + 8` using `fetch_add(1, SeqCst)`. The spark task needs the IVar to stay alive until it finishes.
2. Call `rayon::spawn(move || { ... })` with a closure that:
   a. Calls `ivar_force(ivar)` — evaluates the thunk if still PENDING.
   b. Atomically decrements RC at `ivar + 8` using `fetch_sub(1, SeqCst)`.
   c. If the old RC was 1 (now 0), emits an Acquire fence and frees the IVar.
3. Return 0 (return value unused).

**RC ordering**: All atomic RC operations use `SeqCst` ordering, per arch Decision 13. The sketch uses `Relaxed` for the inc and `Release` for the dec — the reimplementation uses `SeqCst` throughout for consistency with the atomic RC convention established in Ring 1 (`ring2-rc.md` §2.1).

### 3.5 `cranelisp_ivar_force`

```rust
#[unsafe(export_name = "cranelisp_ivar_force")]
pub extern "C" fn ivar_force(ivar: i64) -> i64
```

**Semantics**: Resolve the IVar. Returns the value. May evaluate the thunk (if PENDING), spin-wait (if another thread is EVALUATING), or return immediately (if RESOLVED).

**Implementation**:
1. **Fast path**: Load state from `ivar + 16` with `SeqCst`. If `RESOLVED`, load and return value from `ivar + 24`.
2. **CAS**: Attempt `compare_exchange(PENDING, EVALUATING, SeqCst, SeqCst)` on the state field.
   - **Success** (we won the race):
     a. Load `thunk` from `ivar + 32`.
     b. Load `code_ptr` from `thunk + 16` (closure's code_ptr offset in reimplementation layout).
     c. Call `code_ptr(thunk)` — the thunk evaluates the binding expression, returning the result as i64.
     d. Store result at `ivar + 24`.
     e. Store `RESOLVED` at `ivar + 16` with `SeqCst` ordering — this publishes the result to other threads.
     f. Return the result.
   - **Failure** (another thread claimed it):
     a. Spin-wait: loop loading state with `SeqCst`, calling `spin_loop()` hint, until state becomes `RESOLVED`.
     b. Load and return value from `ivar + 24`.

**CAS ordering**: The sketch uses `AcqRel`/`Acquire` for the CAS. The reimplementation uses `SeqCst`/`SeqCst` for consistency with Decision 13.

**Thunk closure calling convention**: The thunk is a zero-arg closure. The code_ptr is at offset 16 from the base pointer (past the 16-byte heap header). The calling convention is `code_ptr(env_ptr: i64) -> i64`, where `env_ptr` is the closure's base pointer. This matches the reimplementation's closure layout (Decision 11): `[header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]`.

## 4. Codegen Path

### 4.1 `compile_let` Decision Point

When `compile_let` processes a `Let` expression:

```
if *LENIENT_DISABLED || self.in_trace_body {
    compile_let_sequential(bindings, body)
} else {
    let sparkable = find_sparkable_bindings(bindings, &self.globals);
    if sparkable.is_empty() {
        compile_let_sequential(bindings, body)
    } else {
        compile_let_lenient(bindings, body, &sparkable, span)
    }
}
```

### 4.2 `compile_let_lenient`

Three phases:

**Phase 1 — Create and spark IVars** (for sparkable bindings only):

For each sparkable index `idx`:
1. Wrap `bindings[idx].1` (the value expression) in a synthetic `Expr::Lambda { params: [], body: val_expr }`.
2. Compile the lambda — this produces a zero-arg thunk closure pointer with captures for any free variables.
3. Emit `call cranelisp_ivar_create(thunk_ptr) -> ivar_ptr`.
4. Emit `call cranelisp_ivar_spark(ivar_ptr)`.
5. Store `(idx, ivar_ptr)` in a map.

**Phase 2 — Process bindings in order** (all bindings, sparkable and non-sparkable):

For each binding `(name, val_expr)` at index `i`:
- If `i` is sparkable: emit `call cranelisp_ivar_force(ivar_map[i]) -> forced_val`. Then emit `emit_dec(ivar_ptr)` — the main thread's reference to the IVar cell is released. Bind `forced_val` to `name`.
- If `i` is non-sparkable: compile `val_expr` normally. Bind the result to `name`.

This is the **barrier model**: all IVars are forced before the body executes. The order of forcing matches the source order of bindings, ensuring deterministic behavior when the forced values are used.

**Phase 3 — Compile body**:

Compile the `let` body expression normally. All bindings are in scope.

### 4.3 Thunk Closure Layout

Thunk closures use the reimplementation's standard `HeapClosure` layout (Decision 11):

```
Base pointer →
  +0   alloc_size: i64
  +8   rc: i64
  +16  code_ptr: i64        (extern "C" fn(env_ptr: i64) -> i64)
  +24  drop_glue_ptr: i64   (or 0 if no heap captures)
  +32  capture_0: i64
  +40  capture_1: i64
  ...
```

The thunk's captures are the free variables of the binding expression that are in scope in the enclosing function. The code_ptr points to a generated function that loads captures from the closure struct, evaluates the expression, and returns the result.

## 5. IVar Drop Glue

**Not needed under the barrier model.** All IVars are created, sparked, and then forced within the same `let` compilation. After forcing, the main thread dec's the IVar (Phase 2). The spark task also dec's the IVar when it finishes (§3.4). One of these dec's brings the RC to zero and frees the cell.

Because IVars are always forced before scope exit, there is no scenario where an IVar is dropped while still PENDING. The barrier model guarantees this structurally.

If a future enhancement moves to per-use-site forcing (Phase 8 in the sketch's roadmap), IVar drop glue would be needed to handle the case where an IVar is never forced. That is out of scope for the current design.

**Thunk panic behaviour**: If a sparked thunk panics on a rayon worker thread, the IVar remains in EVALUATING state and the main thread's `ivar_force` will spin indefinitely. This is accepted for Sprint 25 — rayon propagates panics at `scope` boundaries, and a poison mechanism can be added later if needed.

## 6. RC Lifecycle

The full RC lifecycle of an IVar and its thunk:

1. Thunk closure compiled with `rc = 1` (normal closure compilation).
2. `ivar_create(thunk)` — IVar cell allocated with `rc = 1`. Thunk pointer stored in the cell. Thunk ownership is conceptually transferred to the IVar (the thunk's rc remains 1; the IVar holds the sole reference).
3. `ivar_spark(ivar)` — IVar `rc` incremented to 2 (spark task holds a reference).
4. One thread calls `ivar_force`:
   - Thunk is called, producing a result value (with `rc = 1` if heap-allocated).
   - Result stored in the IVar's value field.
   - State set to `RESOLVED`.
5. Main thread forces the IVar (may be the same or different from step 4): gets the result value.
6. Main thread dec's the IVar: `rc` goes from 2 to 1 (or 1 to 0 if spark already finished).
7. Spark task dec's the IVar: `rc` goes from 1 to 0 (or was already 0 if main dec'd second).
8. Whichever dec brings `rc` to 0 frees the IVar cell.
9. The forced result value is bound to the `let` variable with `rc = 1` and tracked in `scope_stack` for normal RC cleanup.

**Note**: The thunk closure is consumed by `ivar_force` (it is called exactly once). After forcing, the thunk pointer in the IVar cell is stale. This is safe because the IVar is freed before the thunk pointer could be reused, and no code reads the thunk pointer after forcing.

**Note**: The forced value's RC is not affected by the IVar mechanism. The thunk produces a result with `rc = 1`, and that value is returned through the IVar cell. It is then bound to the `let` variable and managed by the normal scope cleanup.

## 7. Sketch Comparison

### 7.1 What the Sketch Does

The sketch implements lenient evaluation with the same barrier-force model:

- `find_sparkable_bindings()` (`sketch/src/codegen/expr.rs:42-65`): same algorithm — free variable check, same `CHEAP_BUILTINS` list, same minimum-2 threshold.
- `compile_let_lenient()` (`sketch/src/codegen/expr.rs:735+`): three-phase compilation — create/spark IVars, force in order, compile body.
- `cranelisp_ivar_create/spark/force` (`sketch/cranelisp-runtime/src/intrinsics.rs:369-460`): same IVar state machine (PENDING/EVALUATING/RESOLVED), same CAS-based claiming, same spin-wait.
- `CRANELISP_NO_LENIENT` env var (`sketch/src/codegen/expr.rs:17-18`): identical mechanism.

### 7.2 Where the Reimplementation Follows

- **Sparkability algorithm**: identical. Same independence check, same cost heuristic, same cheap-builtins list, same minimum-2 requirement.
- **Barrier model**: identical. All IVars forced before body executes. No per-use-site forcing.
- **IVar state machine**: identical states and transitions (PENDING=0, EVALUATING=1, RESOLVED=2).
- **No IVar drop glue**: same decision, for the same reason (barrier model guarantees all IVars are forced).
- **Rayon global pool**: same thread pool choice.

### 7.3 Where the Reimplementation Diverges

| Aspect | Sketch | Reimplementation | Rationale |
|---|---|---|---|
| **Base pointer convention** | Interior pointer (payload pointer returned by `alloc_with_rc`) — IVar fields at offsets 0, 8, 16 from payload ptr; RC at payload-8 | Base pointer (offset 0 = alloc_size, offset 8 = rc, offset 16+ = payload) — IVar fields at offsets 16, 24, 32 from base ptr | Arch Decision 10. Positive offsets throughout; consistent with all other heap types. |
| **RC atomics ordering** | `Relaxed` for inc, `Release` for dec, `AcqRel`/`Acquire` for CAS | `SeqCst` for all atomic operations | Arch Decision 13. Consistency with the atomic RC convention used for all heap objects. Slightly more conservative but eliminates a class of ordering bugs. |
| **Closure layout** | `[code_ptr(8) \| captures...]` at payload pointer; no drop_glue_ptr | `[header(16) \| code_ptr(8) \| drop_glue_ptr(8) \| captures...]` at base pointer; `CAPTURES_START = 32` | Arch Decision 11. Embedded drop_glue_ptr enables self-contained closure dec without side tables. code_ptr is at offset 16 (not 0). |
| **Thunk code_ptr offset** | Offset 0 from payload pointer | Offset 16 from base pointer | Follows from the two divergences above. `ivar_force` reads code_ptr from `thunk + 16`. |
| **IVar alloc size** | `alloc_with_rc(24)` — 24 bytes payload, header size implicit | `alloc_with_rc(24)` — 24 bytes payload (allocator adds 16-byte header = 40 total) | `alloc_with_rc` takes payload size, not total size. Both sketch and reimplementation pass 24. |
| **`ivar_spark` RC access** | `(ivar as *mut i64).sub(1)` — negative offset to reach RC | `ivar + 8` — positive offset | Base-pointer convention: RC at fixed offset +8. |
