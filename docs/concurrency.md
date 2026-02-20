# Concurrency

**Status**: Design phase — no implementation yet.

## Design Constraints

Current runtime properties that constrain the concurrency design space:

### Non-atomic reference counting

`emit_inc` and `emit_dec` generate plain Cranelift `load`/`iadd`/`store` sequences (see `src/codegen/mod.rs`). There is no atomic compare-and-swap, no memory fence, and no lock. Multiple threads mutating the same RC field would corrupt it. This rules out any shared-heap model without first upgrading to atomic RC.

### RC known gaps

Several RC lifetime scenarios are incomplete (see `KNOWN_ISSUES.md`):
- Match scrutinee not decremented after match
- Closure drop glue deferred (captured heap values leak)
- Function arguments not decremented by callee
- Let bindings embedded in return values cause use-after-free

These must be fixed before values can be safely moved across thread boundaries, since a thread that receives a value must be able to rely on correct RC semantics.

### Eager IO execution

`IO a` = `a` at runtime (see `docs/io.md`). Effects execute immediately when reached. There is no lazy thunk, no Task descriptor, and no runtime scheduler that could intercept and redistribute effects across threads. Concurrency must work within this eager model.

### Pure functional immutable values

All user-visible values are immutable. There is no mutable variable, no `set!`, no mutable reference. This is the strongest asset for concurrency: any value can be shared without synchronisation as long as its backing memory is not mutated — and the only mutation is the RC field itself.

### Platform DLL model

All IO effects come from dynamically-loaded platform DLLs via `(platform name)`. Concurrency primitives (spawn, channels, thread pools) can be introduced as platform functions without language changes, following the same pattern as `print` and `read-line`.

### Static dispatch via monomorphisation

Trait methods and constrained polymorphic functions are resolved at compile time and monomorphised to concrete specialisations. There is no vtable, no dynamic dispatch table to synchronise. Spawned tasks compile the same way as sequential code.

## Models Considered

### Shared-nothing + message passing (Erlang/Go)

Each task owns its heap. Communication via typed channels. Values are copied (or moved) across boundaries. Fits non-atomic RC perfectly — no shared mutable state. Requires deep-copy or move infrastructure.

**Fit**: Excellent. Aligns with purity and non-atomic RC.

### Atomic RC + shared heap (Rust Arc)

Upgrade all RC operations to atomic. Any task can hold a reference to any heap object. Enables zero-copy sharing but requires atomic ops on every inc/dec, even in single-threaded code.

**Fit**: Poor. Adds ~2-10x overhead on every RC operation for a benefit (zero-copy sharing) that purity makes less necessary. Values are immutable, so the main advantage of sharing (avoiding copies) can often be achieved by move semantics instead.

### Software transactional memory (Clojure)

Shared mutable references (`Ref`) with optimistic concurrency. Transactions retry on conflict. Requires a GC (retry means objects must survive indefinitely) and mutable state.

**Fit**: Poor. No GC, no mutable state. Fundamentally incompatible with the current runtime.

### Platform-controlled tasks (Roc)

`main` returns a Task description; the platform interprets and schedules it. Enables structured concurrency but requires switching from eager to lazy IO execution.

**Fit**: Possible long-term, but requires an IO model change. The eager `IO a = a` identity would need to become a thunk/closure. Too large a change for an initial concurrency story.

### Parallel collections (data parallelism only)

`pmap`, `pfilter`, etc. that process collection elements in parallel. No general concurrency, just embarrassingly parallel loops.

**Fit**: Good as a first step. Can be implemented entirely in a platform DLL with zero language changes. Limited to data parallelism.

## Recommended Model

**Shared-nothing tasks with typed channels**, following Erlang's isolation model but with Lean4/Koka-style inferred ownership to minimise copies.

### Why this fits

1. **Respects non-atomic RC**: Each task has its own heap. No concurrent RC mutation.
2. **Aligns with purity**: Immutable values can be deep-copied across boundaries without observable difference. The absence of mutable state means there's nothing to synchronise beyond the channel endpoints.
3. **No annotation burden**: Users don't write lifetime annotations, borrow markers, or `Arc` wrappers. The compiler infers whether a value can be moved or must be copied.
4. **Platform-native**: `spawn`, `send`, `recv` can be IO-typed platform functions, introduced without parser or type system changes.
5. **Incremental**: Start with parallel collections (`pmap`), graduate to explicit channels, then optimise with ownership analysis.

## Ownership and Memory

### Why full Rust-style borrows are wrong here

Rust's borrow checker enforces memory safety in the presence of mutation. Cranelisp has no mutation — every value is immutable once constructed. The entire justification for `&`, `&mut`, and lifetime annotations evaporates when there's nothing to mutate.

Adding Rust-style borrows would impose significant annotation burden (`'a` lifetimes, explicit `&`/`&mut` markers) for zero safety benefit in a pure language. It would also fight the existing RC system — Rust's borrowing model is an alternative to RC, not a complement.

### The Lean4/Koka insight: inferred ownership with RC fallback

Lean4 and Koka demonstrate that a pure functional language can get most of the performance benefits of ownership without any user-visible annotations:

1. **Unique values** (RC = 1): The compiler can prove via static usage analysis that a value has exactly one reference. These values can be mutated in place (reuse optimisation) or moved to another thread at zero cost — no deep copy needed.

2. **Shared values** (RC > 1): Multiple references exist. Moving across a thread boundary requires a deep copy (or an atomic RC upgrade for the specific value).

3. **The default is safe**: Without the optimisation pass, every cross-thread transfer deep-copies. The analysis only removes unnecessary copies — it never introduces unsafety.

This is the right fit for Cranelisp: the compiler already tracks RC, and a static usage analysis can be layered on top as an optimisation without changing the language surface.

### Interaction with stack allocation

If stack-allocated value types are added (see ROADMAP "Stack objects / box"), these are always unique by construction and can be moved freely. The ownership analysis only matters for heap-allocated values.

### Behaviour at thread boundaries

When a value crosses a thread boundary via `send`:

- **Unique (RC = 1)**: Move the pointer. The sending task relinquishes ownership. No copy, no RC manipulation. The receiving task owns it.
- **Shared (RC > 1)**: Deep copy the entire value graph. The copy starts with RC = 1 in the receiving task's heap. The original's RC is decremented.
- **Without analysis**: Always deep copy. Correct but slower. This is the safe default for initial implementation.

## Implementation Roadmap

### Prerequisites

1. **Fix RC gaps**: Resolve the known issues (scrutinee, closures, arguments, embedded let bindings) so values have correct reference counts at all times. Without this, deep copy cannot reliably traverse a value's object graph.
2. **Deep-copy infrastructure**: Implement `deep_copy(val, ty) -> val` as an intrinsic that walks the heap structure of a value (guided by type information) and produces an independent copy. This is needed for cross-thread value transfer.
3. **Type-guided traversal**: The deep-copy function needs type information at runtime to know which fields are heap pointers. Options: (a) embed a type descriptor pointer in heap objects, (b) generate per-type copy functions at compile time (analogous to drop glue), or (c) monomorphise the copy at each `send` call site.

### Phase 0: Parallel collections via platform DLL

Add `pmap` and `pfilter` as platform DLL functions. Each element is processed independently by a thread pool. Results are collected into a new collection. No channels, no explicit task management.

```clojure
(pmap (fn [x] (* x x)) (range 1 1000000))
```

Implementation: The platform DLL receives a function pointer and a collection pointer, spawns work on a Rayon thread pool, deep-copies each element into the worker, calls the function, deep-copies the result back.

This phase validates the deep-copy infrastructure and gives users practical parallelism with zero new language concepts.

### Phase 1: `spawn` / `send` / `recv` as platform functions

Introduce explicit task creation and one-shot channels:

```clojure
(bind! [ch (chan)]
  (do
    (spawn (fn [] (send ch (expensive-computation))))
    (recv ch)))
```

Types:
- `spawn : (fn [] (IO a)) -> IO Handle`
- `chan : IO (Chan a)`
- `send : (Chan a) -> a -> IO Unit`
- `recv : (Chan a) -> IO a`

All IO-typed, all from the platform DLL. The type checker enforces that channel endpoints carry a consistent type. Cross-thread values are always deep-copied.

### Phase 2: Typed `(Chan a)` and lightweight process runtime

Refine channels to be multi-use with buffering. Optionally introduce lightweight green threads (M:N scheduling) in the platform runtime, making `spawn` cheap enough for thousands of tasks.

```clojure
(defn worker [in out]
  (bind! [msg (recv in)]
    (do
      (send out (process msg))
      (worker in out))))
```

### Phase 3: Usage analysis for move optimisation

Add a compiler pass (after type inference, before codegen) that performs static usage analysis to identify unique values. At `send` call sites, the compiler emits a move instead of a deep copy when the value is provably unique.

This is purely an optimisation — behaviour is identical to Phase 1/2 but faster for the common case where a value is computed, sent, and never used again by the sender.

### Phase 4: Selective atomic RC at thread boundaries

For values that are shared (RC > 1) but too large to deep-copy efficiently, optionally upgrade their RC to atomic at the point of `send`. This is a targeted optimisation, not a global change — single-threaded code never pays the atomic cost.

This phase may not be necessary if the usage analysis in Phase 3 is effective enough. Defer until profiling shows deep-copy overhead is a bottleneck.

## Open Questions

Decisions deferred for implementation time:

1. **Deep-copy strategy**: Per-type generated copy functions (like drop glue) vs runtime type descriptor traversal? Generated functions are faster; descriptors are more flexible for polymorphic code.

2. **Channel flavour**: Unbounded vs bounded channels? Bounded channels provide backpressure but can deadlock. Start unbounded and add bounded variants later?

3. **Error propagation**: What happens when a spawned task panics? Options: (a) terminate the whole process (current `cranelisp_panic` behaviour), (b) propagate the error to `recv` as an `(Error String)` variant, (c) ignore and let the channel hang.

4. **Task cancellation**: Should `Handle` support cancellation? Cooperative cancellation (check a flag) or preemptive (kill the thread)?

5. **Platform-specific vs language-level**: Should `spawn`/`chan` remain platform functions forever, or eventually become special forms with compiler support for ownership analysis?

6. **Interaction with file watching**: If a module is reloaded while a background task is running code from it, what happens? The GOT-based dispatch means the running task sees the old function pointers until the next call through the GOT. Reload during execution needs careful thought.

7. **Closure capture and send**: Closures capture values from their environment. Sending a closure across a thread boundary requires deep-copying all captures. The current lack of captured-type metadata (the same gap that prevents closure drop glue) must be resolved first.
