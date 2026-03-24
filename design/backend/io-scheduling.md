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
  +0   alloc_size: i64    (= 16 + 8 + 8 + N*8)
  +8   rc: i64            (initial: 1, atomic)
  +16  tag: i64           (= IO_TAG_PAR = 3)
  +24  branch_count: i64  (N, number of IO branches)
  +32  branch_0: i64      (pointer to IO subtree 0)
  +40  branch_1: i64      (pointer to IO subtree 1)
  ...
  +32+(N-1)*8  branch_{N-1}: i64

Total allocation: 32 + N*8 bytes
```

This is a variable-size ADT node. The branch pointers are inline (not behind a separate array indirection), since the count is known at compile time and the trampoline can read them at fixed offsets.

The `IO_TAG_PAR` constant (= 3) is already defined in `cranelisp-platform` alongside the existing `IO_TAG_PURE` (0), `IO_TAG_EFFECT` (1), and `IO_TAG_BIND` (2).

## 4. `ParBind` Codegen

### 4.1 Strategy

A `ParBind` with bindings `[(x0, e0), (x1, e1), ..., (xN-1, eN-1)]` and body `B` compiles as:

1. Compile each IO expression `ei` — these produce IO tree pointers.
2. Allocate a Par node containing all N IO tree pointers.
3. Inc RC on each IO tree pointer (the Par node holds references).
4. Build a continuation closure that unpacks the Par results and evaluates the body.
5. Allocate a Bind node linking the Par node to the continuation.
6. Inc RC on the Par node and the continuation (the Bind node holds references).
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
payload_size = 8 + 8 + N*8          // tag + count + N branches
total_size = 16 + payload_size      // header + payload
par_ptr = call emit_alloc(total_size)

// Store fields
store IO_TAG_PAR (3)  at par_ptr + 16   // tag
store N               at par_ptr + 24   // branch_count
store io_0            at par_ptr + 32   // branch_0
store io_1            at par_ptr + 40   // branch_1
...

// Inc each branch (Par node holds references)
emit_rc_inc(io_0)
emit_rc_inc(io_1)
...

// Phase 3: Build continuation closure
// Signature: (env_ptr: i64, results_ptr: i64) -> i64
// The continuation loads N values from results_ptr, binds to x0..xN-1,
// compiles body B.
cont_ptr = compile_par_bind_continuation(bindings, body, span)

// Phase 4: Allocate Bind node
bind_ptr = call emit_alloc(40)      // 16 header + 24 payload (tag + inner + cont)
store IO_TAG_BIND (2)  at bind_ptr + 16
store par_ptr          at bind_ptr + 24
store cont_ptr         at bind_ptr + 32

emit_rc_inc(par_ptr)
emit_rc_inc(cont_ptr)

return bind_ptr
```

### 4.3 Continuation Closure

The continuation closure has signature `extern "C" fn(env_ptr: i64, results_ptr: i64) -> i64`.

It is compiled as an anonymous function that:
1. Loads N result values from `results_ptr` at offsets `0, 8, 16, ...` (these are the results of forcing each Par branch).
2. Binds each result to the corresponding name `x0, x1, ..., xN-1`.
3. Compiles the body `B` in this extended scope.
4. Returns the body result (which is an IO tree pointer).

The continuation captures any free variables of the body that are not among the binding names and are in scope in the enclosing function. These captures are stored in the closure struct at offset 32+ (after header, code_ptr, and drop_glue_ptr per Decision 11).

**Calling convention note**: Par-Bind continuations receive a `results_ptr` (pointer to an array of N i64 result values) as their second argument, unlike regular Bind continuations which receive a single i64 value. This divergence is structurally safe because the Par handler directly calls the continuation rather than going through the normal trampoline result-passing flow — the continuation is compiled specifically for the ParBind codegen path.

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

    // Read branch IO pointers
    let branch_ptrs: Vec<i64> = (0..count)
        .map(|i| unsafe {
            *((current as isize + FIELD_0_OFFSET + 8 + (i as isize) * 8) as *const i64)
        })
        .collect();

    // Dispatch with resource token serialization
    let results = dispatch_par_branches(&branch_ptrs);

    // Allocate a transient results array (raw, no RC — short-lived buffer).
    // We use a Vec<i64> rather than alloc_with_rc because:
    // (a) the buffer has no RC semantics — it is filled, passed to the
    //     continuation, and freed immediately after;
    // (b) alloc_with_rc returns a base pointer whose first 16 bytes are
    //     the HeapHeader — writing results at offset 0 would clobber it.
    let mut results_buf: Vec<i64> = vec![0i64; count];
    for (i, &val) in results.iter().enumerate() {
        results_buf[i] = val;
    }
    let results_ptr = results_buf.as_ptr() as i64;
    std::mem::forget(results_buf); // ownership transferred to continuation

    // Pop continuation and call with results array
    match cont_stack.pop() {
        Some(cont_ptr) => {
            current = call_continuation(cont_ptr, results_ptr);
        }
        None => return results_ptr,
    }
}
```

Note: `FIELD_0_OFFSET` is `TAG_OFFSET + 8` = 24, which is where `branch_count` lives. The branch pointers start at `FIELD_0_OFFSET + 8` = 32.

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
            entries
                .into_iter()
                .map(|(idx, io_ptr)| {
                    let result = run_io_trampoline(io_ptr);
                    (idx, result)
                })
                .collect()
        }
    }
}
```

#### 5.2.5 Correctness Properties

Per spec §10.12.4:
- **Token=0 branches run independently**: each dispatched as a separate rayon work item. They may execute in any order or concurrently.
- **Same non-zero token groups run sequentially**: all branches in a token group are executed in source order within a single work item. Different token groups run concurrently with each other.
- **Result ordering**: the results array preserves the original binding order (indexed by original position), regardless of dispatch order.

### 5.3 Continuation Calling Convention

After dispatch, the results array is allocated as a raw `Vec<i64>` buffer (no RC header). The continuation receives it as a single i64 pointer argument and loads individual results at offsets `0, 8, 16, ...` directly from the pointer. The continuation is responsible for freeing the buffer (via `Vec::from_raw_parts`) after extracting all values.

The continuation is a closure with signature `extern "C" fn(env_ptr: i64, results_ptr: i64) -> i64`. It loads result values from the results array at offsets `0, 8, 16, ...` and binds them to the corresponding names.

Par-Bind continuations receive a `results_ptr` (pointer to an array of N i64 result values) as their second argument, unlike regular Bind continuations which receive a single i64 value. This divergence is structurally safe because the Par handler directly calls the continuation rather than going through the normal trampoline result-passing flow — the continuation is compiled specifically for the ParBind codegen path.

## 6. Integration Points

### 6.1 Trampoline ↔ Par

The trampoline calls `dispatch_par_branches` when it encounters a Par tag. Each branch gets its own trampoline instance (recursive call to `run_io_trampoline`). This means nested Par nodes, Bind chains, or Effect nodes within branches are handled correctly.

### 6.2 Backend ↔ Type System

The typechecker treats `ParBind` identically to a sequential `let` binding for type inference purposes — per §12.4.3, lenient/parallel evaluation is "semantically transparent." The `ParBind` match arm in the typechecker simply infers each binding expression, extends the environment, and infers the body.

### 6.3 Backend ↔ Platform

The backend does not directly interact with `SchedulingClass`. The independence analysis pass (`/int`) uses platform scheduling data to decide which bindings to group into `ParBind`. By the time the backend sees `ParBind`, the decision is made.

The resource tokens, however, are a runtime concern: they are embedded in Effect nodes by platform DLL code and read by the trampoline's `dispatch_par_branches`. The backend emits the Par node structure; the trampoline reads tokens from the branches.

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

## 8. Sketch Comparison

### 8.1 What the Sketch Does

The sketch implements Par nodes and auto-scheduling:

- **`schedule.rs`** (`sketch/src/schedule.rs`, 367 lines): a post-expansion, pre-typecheck pass that flattens `bind` chains, classifies each step by `SchedulingClass`, checks data independence via `free_vars`, groups data-independent non-Sequential bindings into `Segment::Parallel`, and rebuilds the chain with `Expr::ParBind` nodes. Single-entry parallel groups are demoted back to sequential.
- **`compile_par_bind`** (`sketch/src/codegen/expr.rs:397-458`): compiles IO expressions, allocates a Par node with inline branch pointers (tag=3, count, io_0, io_1, ...), builds a continuation closure, wraps in a Bind node.
- **Trampoline Par handler** (`sketch/cranelisp-runtime/src/intrinsics.rs:272-299`): reads count and branch pointers, calls `par_iter` on all branches (each gets a recursive `run_io` call), allocates results array, calls continuation.

### 8.2 Where the Reimplementation Follows

- **Par node layout**: same inline structure — tag, count, branch pointers in a contiguous allocation. No separate array indirection.
- **ParBind codegen strategy**: same approach — compile IO expressions, allocate Par node, build continuation closure, wrap in Bind node.
- **Independence analysis location**: same placement — after macro expansion, before typechecking. The reimplementation places this in the binary crate (`/int`) rather than the backend, since it needs platform scheduling data from DLL loading.
- **Continuation closure pattern**: same — takes `(env_ptr, results_ptr)`, loads results by offset, binds to names, compiles body.

### 8.3 Where the Reimplementation Diverges

| Aspect | Sketch | Reimplementation | Rationale |
|---|---|---|---|
| **Resource token serialization** | Ignored. `par_iter` dispatches all branches indiscriminately. | Groups branches by resource token. Token=0 branches run independently; same non-zero token groups run sequentially as single work items. | Spec §10.12.4 requires it. The sketch acknowledges this as unfinished. |
| **Base-pointer convention** | Interior pointer. Par fields at offsets 0, 8, 16+ from payload pointer. | Base pointer. Par fields at offsets 16, 24, 32+ from base pointer. | Arch Decision 10. |
| **RC atomics** | Non-atomic RC acknowledged as a known issue. | Atomic RC from Ring 1 (Decision 13). Par branches run on rayon threads that may inc/dec shared values concurrently. | Atomic RC was designed from Ring 1 to support exactly this use case. |
| **Closure layout** | No drop_glue_ptr. `[code_ptr \| captures...]`. | drop_glue_ptr at offset 24. `[header(16) \| code_ptr(8) \| drop_glue_ptr(8) \| captures...]`. | Arch Decision 11. |
| **Analysis pass location** | `src/schedule.rs` — part of the compiler binary, accesses `tc.platform_scheduling` directly. | Binary crate (`/int`) — owns the pass since it has platform scheduling data from DLL loading. | Ownership follows the data: platform scheduling info is loaded by `/int`, so the pass that consumes it lives there too. |
| **`Expr::ParBind` definition** | In `ast.rs` alongside other Expr variants. | In `cranelisp-types` crate (shared boundary types). | Arch Decision: boundary types in `cranelisp-types`. Cross-crate interface change. |
