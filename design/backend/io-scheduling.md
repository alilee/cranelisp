# Automatic IO Scheduling Design

Sprint 25 — compiler-inserted parallel dispatch for commutative, data-independent IO effects in `bind!` chains.

## 1. Problem

Users write sequential `bind!` chains for IO operations. When multiple bindings in a chain call platform functions that are data-independent and declared `Commutative` (or `ResourceSerial`), the compiler must insert `Par` nodes so the trampoline can dispatch them concurrently. This is a spec requirement (§10.12): there is no `par-bind!` form — automatic scheduling is mandatory.

The analysis pass that identifies parallelizable bindings and produces `Expr::ParBind` nodes is owned by `/int` (see `design/int/bind-chain-analysis.md`). This document covers the backend's responsibilities: compiling `ParBind` to IR, emitting Par nodes, and extending the trampoline to handle them.

## 2. `Expr::ParBind` — The Input

The `/int` independence analysis pass transforms expanded `bind!` chains, replacing groups of data-independent, non-Sequential bindings with `Expr::ParBind` nodes:

```rust
// In cranelisp-types:
Expr::ParBind {
    bindings: Vec<(Symbol, Expr)>,  // ≥2 bindings, all data-independent
    body: Box<Expr>,                // continuation body (may reference binding names)
    span: Span,
}
```

By the time the backend sees a `ParBind`, all analysis is done. The backend's job is to compile it into IO tree nodes that the trampoline can dispatch concurrently.

## 3. Par Node Heap Layout

The Par node is an internal IO constructor (tag = 3). It is not user-constructable — only the backend emits it during `ParBind` codegen.

Using the base-pointer convention (arch Decision 10):

```
Base pointer →
  +0   alloc_size: i64    (= 16 + 8 + 8 + N*16)
  +8   rc: i64            (initial: 1, atomic)
  +16  tag: i64           (= IO_TAG_PAR = 3)
  +24  branch_count: i64  (N, number of IO branches)
  +32  branch_0: i64      (pointer to IO subtree 0)
  +40  disposer_0: i64    (canonical drop<a0>, or 0)
  +48  branch_1: i64      (pointer to IO subtree 1)
  +56  disposer_1: i64    (canonical drop<a1>, or 0)
  ...
  +32+(N-1)*16  branch_{N-1}: i64
  +40+(N-1)*16  disposer_{N-1}: i64

Total allocation: 32 + N*16 bytes
```

This is a variable-size internal node. Each inline branch pointer is paired with
the disposal authority for the value that branch may produce. The scalar
function address is not traversed by IO-tree teardown; the trampoline arms it
only while a produced value has not yet transferred to the Par continuation.

The `IO_TAG_PAR` constant (= 3) is already defined in `cranelisp-platform` alongside the existing `IO_TAG_PURE` (0), `IO_TAG_EFFECT` (1), and `IO_TAG_BIND` (2).

## 4. `ParBind` Codegen

### 4.1 Strategy

A `ParBind` with bindings `[(x0, e0), (x1, e1), ..., (xN-1, eN-1)]` and body `B` compiles as:

1. Compile each IO expression `ei` — these produce IO tree pointers.
2. Allocate a Par node containing all N `(IO tree, result disposer)` pairs.
3. Transfer each IO tree reference into its branch slot.
4. Build a continuation closure that unpacks the Par results and evaluates the body.
5. Allocate a Bind node linking the Par node to the continuation. The Bind
   carries a zero input disposer because the runtime-private Par buffer owns its
   per-slot disposal before handoff.
6. Transfer the Par node and continuation into the Bind node.
7. Return the Bind node pointer.

When the trampoline encounters this Bind node, it will:
- Process the inner node (the Par node) — dispatching branches concurrently.
- Collect results into a results array.
- Call the continuation with the results array pointer.
- The continuation unpacks results, binds them to names, and evaluates the body.

### 4.2 IR Emission

```
// Phase 1: Compile IO expressions
io_0 = compile_expr(e0)
io_1 = compile_expr(e1)
...
io_{N-1} = compile_expr(e_{N-1})

// Phase 2: Allocate Par node
payload_size = 8 + 8 + N*16         // tag + count + N (branch, disposer) pairs
par_ptr = call emit_alloc(payload_size)

// Store fields
store IO_TAG_PAR (3)  at par_ptr + 16   // tag
store N               at par_ptr + 24   // branch_count
store io_0            at par_ptr + 32   // branch_0
store drop<a0>         at par_ptr + 40   // disposer_0, or 0
store io_1            at par_ptr + 48   // branch_1
store drop<a1>         at par_ptr + 56   // disposer_1, or 0
...

// No RC inc — ownership transfer (constructor convention, Decision 20).
// IO expressions at rc=1 transfer directly into Par node slots.

// Phase 3: Build continuation closure
// Signature: (env_ptr: i64, results_ptr: i64) -> i64
// The continuation loads N values from results_ptr (alloc_with_rc buffer)
// at FIELD_0_OFFSET + i*8 (offsets 24, 32, 40, ...), binds to x0..xN-1,
// compiles body B, then dec's the results_ptr buffer.
cont_ptr = compile_par_bind_continuation(bindings, body, span)

// Phase 4: Allocate Bind node
bind_ptr = call emit_alloc(32)      // payload: tag + inner + cont + disposer
store IO_TAG_BIND (2)  at bind_ptr + 16
store par_ptr          at bind_ptr + 24
store cont_ptr         at bind_ptr + 32
store 0                at bind_ptr + 40 // Par buffer has its own slot disposers

// No RC inc — ownership transfer (constructor convention, Decision 20).
// Par node and continuation at rc=1 transfer directly into Bind node.

return bind_ptr
```

### 4.3 Continuation Closure

The continuation closure has signature `extern "C" fn(env_ptr: i64, results_ptr: i64) -> i64`.

It is compiled as an anonymous function that:
1. Loads N result values from `results_ptr` (an `alloc_with_rc` buffer) at offsets `FIELD_0_OFFSET + i*8` (24, 32, 40, ...).
2. Binds each result to the corresponding name `x0, x1, ..., xN-1`.
3. Compiles the body `B` in this extended scope.
4. Dec's the `results_ptr` buffer (it's an `alloc_with_rc` allocation with rc=1).
5. Returns the body result (which is an IO tree pointer).

The continuation captures any free variables of the body that are not among the binding names and are in scope in the enclosing function. These captures are stored in the closure struct at offset 32+ (after header, code_ptr, and drop_glue_ptr per Decision 11).

**Calling convention note**: Par-Bind continuations receive a `results_ptr`
(pointer to an array of N i64 result values) as their second argument, unlike
regular Bind continuations which receive a single language value. The Par arm
returns that pointer as an armed `ProducedValue`; the shared trampoline
`feed_continuation` path then transfers it to the Par-Bind continuation. The
continuation is compiled specifically for this buffer-shaped argument and
shallow-consumes the carrier after loading its slots.

### 4.4 Drop Glue

Par nodes follow the standard ADT drop glue pattern:
- When a Par node reaches `rc = 0`, dec each `branch_i` pointer. All branches are IO tree pointers (AlwaysHeap), so unconditional dec is correct.
- The branch_count field tells drop glue how many branches to dec, but since branch_count is known at compile time (the Par node is generated by the backend for a specific ParBind), the drop glue can be generated with a fixed count.

In practice, the IO tree's liveness invariant (§6 of `io-trampoline.md`) means Par nodes are not freed during trampoline execution. They are freed during cascading drop glue when the top-level IO tree reference is released after the trampoline completes.

## 5. Trampoline Par Handler

### 5.1 New Match Arm

The `run_io_trampoline` function in `cranelisp-runtime/src/io.rs` gains a new match arm for `IO_TAG_PAR`:

```rust
t if t == IO_TAG_PAR => {
    let count = unsafe {
        *((current as isize + FIELD_0_OFFSET) as *const i64)
    } as usize;

    // Read `(branch IO, result disposer)` pairs (stride 16 from offset 32).
    let branches: Vec<(i64, i64)> = (0..count)
        .map(|i| unsafe {
            let base = current as isize + FIELD_1_OFFSET + (i as isize) * 16;
            (*(base as *const i64), *((base + 8) as *const i64))
        })
        .collect();

    // Dispatch with resource token serialization
    let results = dispatch_par_branches(&branches);

    // Allocate results buffer via alloc_with_rc so the continuation
    // can dec it when done. Results stored at FIELD_0_OFFSET + i*8
    // (offsets 24, 32, 40, ...) matching HeapAdt::field_offset(i).
    let results_buf = alloc_with_rc(8 + count * 8) as i64;
    for (i, &val) in results.iter().enumerate() {
        unsafe {
            *((results_buf as isize + FIELD_0_OFFSET + (i as isize) * 8) as *mut i64) = val;
        }
    }
    // Until shared feed_continuation transfers this buffer, the runtime carrier
    // owns one disposer per initialized slot. Cancellation or fault drops the
    // armed carrier and disposes those slots exactly once.
    ProducedValue::par_buffer(results_buf, branch_disposers)
}
```

Note: `FIELD_0_OFFSET` is `TAG_OFFSET + 8` = 24, which is where
`branch_count` lives. Branch/disposer pairs start at `FIELD_1_OFFSET` = 32
with a 16-byte stride. The results buffer remains
`alloc_with_rc(8 + N*8)` — the 8-byte padding at offset 16 aligns result
values to `FIELD_0_OFFSET + i*8` (24, 32, 40, ...) matching
`HeapAdt::field_offset(i)`. The surrounding trampoline passes the armed buffer
through the same `feed_continuation` state transition used for every other IO
result. Transfer disarms runtime ownership; the compiled continuation then emits
`emit_rc_dec` on the shallow buffer after consuming its values.

### 5.2 Resource Token Serialization

This is a spec requirement (§10.12.4) that the **sketch does NOT implement**. The sketch's Par handler (`sketch/cranelisp-runtime/src/intrinsics.rs:272-299`) uses `par_iter` on all branches indiscriminately, ignoring resource tokens.

The reimplementation MUST group branches by resource token and serialize branches with the same non-zero token.

#### 5.2.1 Algorithm: `dispatch_par_branches`

```rust
fn dispatch_par_branches(branch_ptrs: &[i64]) -> Vec<i64> {
    use std::collections::HashMap;
    use rayon::prelude::*;

    // Step 1: Read resource tokens from Effect nodes.
    // For non-Effect branches (Pure, Bind, Par), use token=0 (unrestricted).
    let mut token_groups: HashMap<i64, Vec<(usize, i64)>> = HashMap::new();
    for (i, &io_ptr) in branch_ptrs.iter().enumerate() {
        let token = read_resource_token(io_ptr);
        token_groups.entry(token).or_default().push((i, io_ptr));
    }

    // Step 2: Build work items.
    // - token=0 entries: each is an independent work item
    // - non-zero token group: entire group is a single sequential work item
    let mut results = vec![0i64; branch_ptrs.len()];

    let work_items: Vec<WorkItem> = build_work_items(&token_groups);

    // Step 3: Dispatch via rayon.
    let item_results: Vec<Vec<(usize, i64)>> = work_items
        .into_par_iter()
        .map(|item| execute_work_item(item))
        .collect();

    // Step 4: Place results in correct positions.
    for batch in item_results {
        for (idx, val) in batch {
            results[idx] = val;
        }
    }

    results
}
```

#### 5.2.2 Reading Resource Tokens

Resource tokens are stored in Effect nodes at offset 32 (the `resource_token` field — see `io-trampoline.md` §1.2). For non-Effect nodes (Pure, Bind, Par), the token is 0 (unrestricted):

```rust
fn read_resource_token(io_ptr: i64) -> i64 {
    let tag = unsafe { *((io_ptr as isize + TAG_OFFSET) as *const i64) };
    if tag == IO_TAG_EFFECT {
        // Effect layout: [header(16) | tag(8) | thunk_ptr(8) | resource_token(8)]
        unsafe { *((io_ptr as isize + FIELD_1_OFFSET) as *const i64) }
    } else {
        0 // Non-Effect nodes are unrestricted
    }
}
```

#### 5.2.3 Work Items

```rust
enum WorkItem {
    /// A single branch to run independently.
    Single(usize, i64),          // (original_index, io_ptr)
    /// A group of branches to run sequentially (same non-zero resource token).
    SerialGroup(Vec<(usize, i64)>), // [(original_index, io_ptr), ...]
}

fn build_work_items(token_groups: &HashMap<i64, Vec<(usize, i64)>>) -> Vec<WorkItem> {
    let mut items = Vec::new();
    for (&token, entries) in token_groups {
        if token == 0 {
            // Each unrestricted branch is independent
            for &(idx, io_ptr) in entries {
                items.push(WorkItem::Single(idx, io_ptr));
            }
        } else {
            // Same non-zero token: run sequentially as one work item
            items.push(WorkItem::SerialGroup(entries.clone()));
        }
    }
    items
}
```

#### 5.2.4 Executing Work Items

Each work item runs its IO branch(es) through a recursive `run_io_trampoline` call — each branch gets its own trampoline instance:

```rust
fn execute_work_item(item: WorkItem) -> Vec<(usize, i64)> {
    match item {
        WorkItem::Single(idx, io_ptr) => {
            let result = run_io_trampoline(io_ptr);
            vec![(idx, result)]
        }
        WorkItem::SerialGroup(entries) => {
            let mut results = Vec::with_capacity(entries.len());
            for (idx, io_ptr) in entries {
                let result = run_io_trampoline(io_ptr);
                if take_runtime_error().is_some() {
                    break; // abort before any later same-token effect starts
                }
                results.push((idx, result));
            }
            results
        }
    }
}
```

#### 5.2.5 Correctness Properties

Per spec §10.12.4:
- **Token=0 branches run independently**: each dispatched as a separate rayon work item. They may execute in any order or concurrently.
- **Same non-zero token groups run sequentially**: all branches in a token group are executed in source order within a single work item. Different token groups run concurrently with each other.
- **First error stops its token group**: because later entries have not started,
  the group aborts before starting them, preserving sequential left-to-right
  behaviour. Other token groups may already be in flight and still require
  structured cleanup.
- **Result ordering**: the results array preserves the original binding order (indexed by original position), regardless of dispatch order.

### 5.3 Continuation Calling Convention

After dispatch, the results array is allocated via `alloc_with_rc(8 + N*8)` —
an RC-managed buffer with results stored at `FIELD_0_OFFSET + i*8` (offsets
24, 32, 40, ...) matching `HeapAdt::field_offset(i)`. While it has not been
handed to the continuation, the runtime pairs the buffer with the branch
disposers and releases every initialized slot if cancellation or fault abandons
it. At continuation handoff, ordinary compiled ownership takes over. The
continuation loads the values and emits `emit_rc_dec` on the shallow carrier.

The continuation is a closure with signature `extern "C" fn(env_ptr: i64, results_ptr: i64) -> i64`. It loads result values from the results buffer at `FIELD_0_OFFSET + i*8` and binds them to the corresponding names.

Par-Bind continuations receive a `results_ptr` (pointer to an `alloc_with_rc`
buffer of N i64 result values) as their second argument, unlike regular Bind
continuations which receive a single language value. The Par handler returns
the armed buffer to the common trampoline step; `feed_continuation` performs the
same explicit transfer used by other IO results, then invokes the continuation
compiled specifically for this buffer-shaped argument.

## 6. Integration Points

### 6.1 Trampoline ↔ Par

The trampoline calls `dispatch_par_branches` when it encounters a Par tag. Each branch gets its own trampoline instance (recursive call to `run_io_trampoline`). This means nested Par nodes, Bind chains, or Effect nodes within branches are handled correctly.

### 6.2 Backend ↔ Type System

The typechecker treats `ParBind` identically to a sequential `let` binding for type inference purposes — per §12.4.3, lenient/parallel evaluation is "semantically transparent." The `ParBind` match arm in the typechecker simply infers each binding expression, extends the environment, and infers the body.

### 6.3 Backend ↔ Platform

The backend does not directly interact with `SchedulingClass`. The independence analysis pass (`/int`) uses platform scheduling data to decide which bindings to group into `ParBind`. By the time the backend sees `ParBind`, the decision is made.

The resource tokens, however, are a runtime concern: they are embedded in Effect nodes by platform DLL code and read by the trampoline's `dispatch_par_branches`. The backend emits the Par node structure; the trampoline reads tokens from the branches.

> **S95 (effect-concurrency slices 3 + 6) extends this.** Under the
> `concurrency-runtime` async substrate the `Par` arm splits into a **two-pool
> partition** (blocking `IO_TAG_EFFECT` branches → this rayon `dispatch_par_branches`
> dispatcher; poll-shape `IO_TAG_EFFECT_POLL` branches → the reactor `join_all`), joined
> via a **wakeable** rayon→reactor bridge (no `block_on` on the reactor thread). The
> partition key is the node tag the backend already emits — **no new Par codegen**. The
> token-`Semaphore` pool keys on a `(token, capacity)` pair read **off the node** (ratified
> `effect-concurrency.md` §8.1): the blocking node gets `capacity` appended by a new
> platform constructor (`effect_on_resource_with_capacity` — `/platform`), and the
> backend reserves the symmetric `(token, capacity)` slots on the poll node it builds.
> The backend half and the precise backend↔intrinsics boundary are in `io-trampoline.md`
> §13; the partition + join + pool sizing are intrinsics/int-owned
> (`design/intrinsics/reactor.md`).

**Scheduling class in trampoline trace events (resolution of FIXME 0011).** The `PlatformEffect` trace event emitted at the trampoline site (`crates/cranelisp-intrinsics/src/io.rs`) carries `scheduling_class: 0`, and that zero is deliberate rather than a placeholder. The effect's real class is not on the node: the host derives it at manifest load onto `OwnedPlatformFnDescriptor.scheduling_class` from `PlatformFn.concurrency` via `nearest_scheduling_class` (`crates/cranelisp-platform/src/lib.rs`; the former `PlatformFn.scheduling_class: u32` was replaced by the `ConcurrencyDescriptor` at the single-ABI cutover), and the trampoline has no back-reference to the platform symbol. FIXME 0011 asked whether the Effect node payload should be extended with an extra field so trampoline events carry the real class inline. The disposition, confirmed against Slice-4 evidence, is **resolution (b): no IR-payload extension**. No Slice-4 consumer requires the class to be present on the trampoline event itself; where the scheduling class is needed for trace interpretation it is recovered by **cross-trace correlation** — joining the trampoline event to the originating `ParBind` classification trace by event ordering — rather than by threading the class through the Effect node. The live site therefore keeps `scheduling_class: 0` deliberately.

### 6.4 Dependencies

The Par handler requires:
- `rayon` crate (already used for lenient evaluation IVar sparking)
- `cranelisp_platform::IO_TAG_PAR` constant (already defined)

## 7. Rejected Alternatives

### 7.1 Separate Array Indirection for Par Branches

Storing branch pointers in a separate heap-allocated array (with a `branches_ptr` in the Par node) was considered. This adds an indirection, an extra allocation, and more complex drop glue. Since the branch count is known at compile time, inline storage is simpler and avoids the extra allocation.

### 7.2 Flat Dispatch Without Token Grouping

Running all branches via `par_iter` without token grouping (the sketch's approach) is simpler but violates §10.12.4. `ResourceSerial` functions with the same token MUST be serialized. The grouping overhead is minimal (a HashMap lookup per branch) and correctness requires it.

### 7.3 Par Node as Results Combiner

An alternative where the Par node itself combines results was considered. The current design delegates result combination to the continuation closure, which is more flexible — the continuation can bind results to named variables and compute arbitrary expressions over them. This matches the `bind!` chain semantics naturally.
