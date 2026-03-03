# Concurrency

**Status**: Phases 5-7 complete. `par-let`, automatic IO scheduling, and lenient evaluation are all implemented. Threading/channels deferred to reimplementation.

## Design Constraints

Runtime properties that constrain the concurrency design space:

### Atomic reference counting (Step 11 — done)

RC operations use `atomic_rmw` (atomic read-modify-write) for thread safety with `par-let` and compiler-inserted `Par` nodes. Sound RC is implemented: consuming calling convention, liveness-based last-use, closure drop glue, match scrutinee dec, constructor Var arg inc, accessor field inc, uniqueness tracking with borrowed reads, static COW bypass. See `KNOWN_ISSUES.md` for remaining edge cases.

### ~~Eager IO execution~~ (resolved)

~~`IO a` = `a` at runtime. Effects execute immediately when reached.~~ This constraint has been removed. IO now uses a deferred Task + trampoline model (see `docs/io.md`). Effects are captured in `Effect` nodes and only execute when the trampoline forces the IO task tree. This enables the runtime to inspect and schedule pending work.

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

**Fit**: Target direction. The Task + trampoline IO model is now implemented (see `docs/io.md`). The runtime can inspect the IO task tree. `Par` nodes enable scheduling independent operations concurrently — the compiler inserts them automatically for data-independent `Commutative` effects in `bind!` chains.

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

## Implicit Parallelism from Purity

### The opportunity

Pure immutable values enable transparent parallelism. Independent computations produce the same result regardless of evaluation order, so the runtime can evaluate them concurrently without changing program semantics.

Natural parallelism sites in cranelisp:

- **Independent let bindings**: `(let [a (fib 40) b (fib 39)] (+ a b))` — `b`'s expression doesn't reference `a`
- **Function argument evaluation**: `(+ (fib 40) (fib 39))` — both arguments are independent pure computations
- **Collection operations**: `pmap`, `pfilter` — each element processed independently (already in the roadmap)

### The granularity challenge

Spawning a thread to compute `(+ 1 2)` in parallel is vastly worse than just doing it. The cost of starting a parallel task determines the threshold for what's worth parallelizing:

| Mechanism | Spawn cost | Worth parallelizing |
|---|---|---|
| OS thread | ~10-100 μs, ~MB stack | Only heavy work (seconds) |
| Green thread / fiber | ~100s ns, ~KB stack | Medium work (ms) |
| Thread-per-core + work stealing | ~10s ns (push pointer to deque) | Modest work (μs) |
| Spark (GHC-style) | ~1 ns (write pointer) | Almost anything non-trivial |

With thread-per-core + work stealing (the Rayon model), N OS threads sit in a pool and never change. "Spawning" is pushing a work item onto a lock-free deque. If nobody steals it before the creator reaches the sync point, it's evaluated inline — the waste is just one pointer write.

### RC at the boundary: scoped-join borrowing

The main obstacle for parallel pure evaluation is non-atomic RC. Parallel tasks that capture the same parent value would race on inc/dec of its RC field.

The solution is **scoped-join semantics**: the parent thread guarantees it will wait for all children before continuing. Since the parent holds a reference, shared values won't be freed during the parallel section. Children can **borrow** parent values with no RC manipulation at all:

```
Parent:
  inc(x) once per child that uses it   (sequential, before spawn)
  spawn child1: compute f(x) — no inc/dec on x
  spawn child2: compute g(x) — no inc/dec on x
  join both
  dec(x) once per child                (sequential, after join)
```

Children allocate new results on the shared heap (Rust's global allocator is already thread-safe). Results have RC = 1, owned by whoever receives them. No concurrent RC mutation anywhere.

This requires the compiler to distinguish "borrowed from parent scope" (no RC manipulation) from "newly allocated" (normal RC) within parallel regions.

## `par-let` and Automatic IO Scheduling

### `par-let`: explicit parallel pure evaluation

```clojure
;; par-let evaluates all bindings in parallel, joins, then evaluates body
(par-let [a (fib 40)
          b (fib 39)
          c (fib 38)]
  (+ a (+ b c)))
```

`par-let` is a macro that desugars to a spawn-join pattern over a thread-per-core pool. It gives users explicit control over what's worth parallelizing. Structurally guarantees the scoped-join property — the body cannot execute until all bindings are resolved.

### Connection to the Task model

`par-let` (pure) uses a thread-per-core pool with work stealing. Concurrent IO uses the same pool but the decision of whether to parallelize is made by the compiler — not the programmer. See "Automatic IO Scheduling" below.

| Domain | Form | Who decides? | Mechanism |
|---|---|---|---|
| Pure parallelism | `par-let` | Programmer (explicit) | Spawn + join on pool |
| IO concurrency | `bind!` | Compiler + platform | `Par` node, compiler-inserted |
| Pure parallelism | (automatic) | Compiler (analysis) | Compiler-inserted sparks |

## Automatic IO Scheduling

### Motivation

The user should not have to decide which IO operations are safe to parallelise. Platform authors know the scheduling semantics of their effects: `read-line` consumes a sequential stream (each call advances the read position); `http-get` is reorderable (each URL is independent). That knowledge belongs in the platform, not in user code.

The result: users write ordinary `bind!` chains; the compiler and platform together determine what can run concurrently. The `par-bind!` user form is not part of the language.

### Platform scheduling classes

Each platform function declares a **scheduling class** in its manifest descriptor:

```rust
pub enum SchedulingClass {
    Sequential,     // must execute in order relative to other calls to this function
    Commutative,    // reorderable; no shared mutable state between calls
    ResourceSerial, // parallel unless runtime resource tokens conflict
}
```

Examples:
- `read-line` → `Sequential` (stdin is a shared stream; read order matters)
- `print` → `Sequential` (stdout ordering determines observable output)
- `http-get` → `Commutative` (each URL is independent; no shared state between calls)
- `time-now` → `Commutative` (clock read; no ordering constraint)
- `file-read(fd)` → `ResourceSerial` (concurrent across different fds, serial for the same fd)
- `log(handle, msg)` → `ResourceSerial` (concurrent across different log handles, serial within one)

The scheduling class is statically available to the compiler at the point each platform is loaded.

### Independence analysis on `bind!` chains

The compiler (`src/schedule.rs`) applies an independence analysis to each `bind!` chain after macro expansion. For a group of contiguous bindings `(n1, e1), ..., (nk, ek)`:

1. **Data independence**: none of `n1..n(i-1)` (earlier bound names) appear free in `ei`.
2. **Non-Sequential**: `ei` calls a platform function tagged `Commutative` or `ResourceSerial`. (Conservative default: calls to unknown functions or Sequential platform functions stay sequential.)

When both conditions hold, entries are grouped into a `ParBind` node. The trampoline dispatches `Par` branches concurrently; `ResourceSerial` branches with the same runtime resource token are serialised automatically.

Sequential bindings remain strictly ordered; mixed chains produce partial Par groupings between Sequential boundaries.

```clojure
;; User writes:
(bind! [r1 (http-get "url1")
        r2 (http-get "url2")]
  (pure (process r1 r2)))

;; Compiler sees both calls are Commutative + data-independent:
;; inserts Par node automatically — both requests in flight simultaneously
```

```clojure
;; Sequential chain: read-line is Sequential, so order is preserved
(bind! [line1 (read-line)
        line2 (read-line)]
  (pure (str-concat line1 line2)))
;; Always reads in order: line1 first, line2 second
```

### Mixed chains

When Sequential and Commutative effects appear in the same `bind!` chain, the compiler preserves all Sequential ordering constraints and parallelises the Commutative groups between them:

```clojure
(bind! [line  (read-line)         ; Sequential — must come first
        r1    (http-get "url1")   ; Commutative
        r2    (http-get "url2")]  ; Commutative, independent of r1
  (pure (combine line r1 r2)))

;; read-line executes first (Sequential).
;; Then http-get "url1" and http-get "url2" execute concurrently (Commutative + independent).
```

### `ResourceSerial`: runtime resource tokens ✓ Done

The three-class system (`Sequential`, `Commutative`, `ResourceSerial`) enables fine-grained resource-aware scheduling. `ResourceSerial` platform functions call `CLIO::effect_on_resource(token, f)` where `token` is an i64 uniquely identifying the resource they access:

- `token = 0` → unrestricted (same as `Commutative`)
- Non-zero token → serialised with all other effects sharing the same token in the same `Par` group

Resource tokens must be **globally unique** — recommended patterns:
- **Singleton resource** (e.g. internal log): `&MY_STATIC as *const _ as i64`
- **Per-instance resource** (e.g. per-fd state): store the `Box::into_raw()` pointer as the handle and reuse it as the token

This allows `print` (`stdout` token) and `read-line` (`stdin` token) to run concurrently with `http-get` (token=0), while two writes to the same log handle are serialised automatically.

## Toward Lenient Evaluation

### What lenient evaluation is

Lenient evaluation is implicit `par`/`deref` for all expressions. Every binding site is a potential spark (start computation) and every use site is a potential sync (block until result is ready). In a pure language, this is semantically identical to strict evaluation — the only difference is performance.

```clojure
;; Looks like normal code:
(let [a (fib 40)
      b (fib 39)]
  (+ a b))

;; Under lenient evaluation, the runtime evaluates it as:
;;   1. Spark (fib 40) → IVar_a (placeholder)
;;   2. Spark (fib 39) → IVar_b (placeholder)
;;   3. (+ a b) syncs on both IVars, blocks until filled
;;   4. Returns result
```

Every value is potentially an **IVar** (write-once cell). Reading an unresolved IVar blocks the reader until the producer fills it.

### Runtime representation change

Lenient evaluation requires distinguishing resolved values from pending computations at runtime. Since all values are i64, options include:

- **Tag bit**: Reserve the low bit (all heap pointers are 8-byte aligned, so bit 0 is free). `0` = resolved i64, `1` = pointer to IVar.
- **Sentinel range**: Reserve a range of i64 values (e.g., very high addresses) as IVar pointers.
- **Indirection through IVars everywhere**: All values are IVar pointers; resolving is always a load.

### The progression

The path from explicit to implicit parallelism is incremental:

1. **`par-let` (explicit, macro)**: User marks what's worth parallelizing. No compiler changes — just a macro over platform spawn/join. Available as soon as spawn primitives exist.

2. **Compiler-inserted `par-let` (automatic)**: The compiler performs independence analysis on `let` bindings and argument evaluation. When it can prove independence and estimate sufficient work (cost heuristic), it inserts parallel evaluation automatically. The user writes normal `let`; the compiler decides when to parallelize.

3. **Lenient evaluation (all bindings)**: Every binding is a potential spark. The runtime decides at execution time whether to evaluate in parallel (based on work-stealing pressure) or inline (if the deque is empty). Requires the IVar runtime representation. This is the GHC sparks / pH (parallel Haskell) model.

### Pure vs IO

Pure parallelism and IO concurrency use the same runtime pool but differ in policy:

- **Pure code**: The compiler can insert parallelism implicitly at any stage — the result is always the same.
- **IO code**: Concurrency is controlled by platform scheduling classes. `Sequential` effects preserve ordering; `Commutative` effects may be parallelised automatically by the compiler when data-independent. The programmer does not opt in or out — the platform declaration carries the semantic information.

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

### ~~Phase 5: Deferred IO (Task + trampoline)~~ ✓ DONE

The IO execution model has been switched from eager to deferred. Platform functions return `Effect` nodes containing opaque Rust closures. The runtime interprets the IO task tree with a flat trampoline loop. See `docs/io.md` for the full design.

Completed changes:
- Platform functions return `Effect` nodes (via `CLIO::effect()`) instead of executing effects
- `pure` constructs `Pure` nodes; `bind` is an inline primitive constructing `Bind` nodes
- The runtime forces `main`'s return value with a trampoline (`IoTask::run()`)
- User code unchanged (`bind!`, `do`, `pure` keep their types and syntax)
- `do` is now IO-specific (expands to `bind` chains instead of `let`)

### Phase 6: `par-let` and automatic IO scheduling ✓ Done

`par-let` is implemented as a special form (not a macro) with a rayon work-stealing thread pool:

- `par-let`: wraps each binding in a zero-arg thunk closure, calls `cranelisp_par_eval` to run them in parallel, loads results
- Enforces minimum 2 bindings at parse time
- Enforces binding independence at type-check time (names not in scope during binding inference)
- RC is non-atomic — accepted for sketch phase, documented in KNOWN_ISSUES.md

The `Par` IO node (tag=3, internal IO constructor) exists in the runtime for the trampoline to dispatch concurrent branches via `rayon::par_iter`. It is compiler-inserted, not user-constructable.

Automatic IO scheduling (`src/schedule.rs`) runs after macro expansion, before typechecking. It analyses each `bind!` chain for data-independent non-Sequential calls and inserts `Par` (`ParBind` AST node) automatically. `ResourceSerial` branches with the same runtime token are serialised by the trampoline. `par-bind!` has been removed — users write `bind!` and the compiler handles parallelism.

```clojure
;; Pure parallelism (explicit)
(par-let [a (fib 40) b (fib 39)]
  (+ a b))

;; Concurrent IO (automatic — compiler inserts Par node)
(bind! [r1 (http-get "url1") r2 (http-get "url2")]
  (pure (process r1 r2)))
```

### Phase 7: Lenient evaluation ✓

Automatic parallelism via IVars and the barrier-force model. The compiler analyses `let` bindings at compile time, identifies independent non-trivial bindings, and evaluates them in parallel without any user annotation. The user writes normal `let`; the compiler decides what to parallelise.

#### IVar runtime representation

An IVar is a heap-allocated, RC-managed write-once synchronisation cell:

```
Heap layout: [total_size: i64 | rc: i64 | state: i64 | value: i64 | thunk: i64]
                                          ^-- payload pointer (returned by alloc)
```

- `state` (offset 0): atomic i64 — `0` = PENDING, `1` = EVALUATING, `2` = RESOLVED
- `value` (offset 8): result i64, valid when state = RESOLVED
- `thunk` (offset 16): closure pointer (zero-arg thunk)

Three runtime intrinsics:

| Function | Signature | Behaviour |
|---|---|---|
| `cranelisp_ivar_create` | `(thunk: i64) -> i64` | Allocate IVar cell (24-byte payload), set state=PENDING, store thunk |
| `cranelisp_ivar_spark` | `(ivar: i64) -> i64` | Atomically inc IVar RC, submit force+dec to rayon pool |
| `cranelisp_ivar_force` | `(ivar: i64) -> i64` | CAS PENDING→EVALUATING: call thunk, store result, set RESOLVED. EVALUATING: spin-wait. RESOLVED: return value |

#### Barrier-force model

Each `let` block is analysed at compile time. Independent non-trivial bindings are sparked (IVar created + submitted to rayon). All IVars are forced in binding order before the body executes. This is a barrier — all sparks resolve before any body code runs.

#### Independence analysis

A binding at index `i` is **sparkable** if:
1. Its free variables don't include any name bound by bindings `0..i` in the same `let`
2. It is a function call (`Expr::Apply`) whose callee is not a known-cheap builtin (`+`, `-`, `*`, `/`, `=`, `<`, `>`, `<=`, `>=`, `not`, `and`, `or`)

The full sparkable set must have **≥ 2** members (no point sparking a single binding).

#### Opt-out

Environment variable `CRANELISP_NO_LENIENT=1` disables automatic sparking. All `let` bindings evaluate sequentially.

#### RC lifecycle

1. Thunk closure created with rc=1 (normal closure compilation)
2. `ivar_create(thunk)` — IVar cell allocated with rc=1; thunk ownership transferred
3. `ivar_spark(ivar)` — runtime inc's IVar rc to 2 (spark holds reference)
4. Worker or main thread calls `ivar_force`: thunk called, result (rc=1) stored in IVar
5. Main thread forces IVar: gets value
6. Worker's spark closure dec's IVar rc from 2→1
7. Main thread dec's IVar rc from 1→0, frees cell
8. The forced value is tracked in scope_stack as a normal binding

#### Sketch simplifications

- Barrier model (all sparks forced before body) instead of per-use-site forcing
- No IVar drop glue (IVars are always forced before scope exit in the barrier model)
- Cost heuristic is simple (function call vs not) — no recursion depth estimation

### Phase 8: Per-use-site forcing (long-term)

True lenient evaluation where every use site forces its IVar individually, avoiding the barrier. Requires SSA-level tracking of which values are IVars vs resolved values. Deferred to reimplementation.

## Open Questions

Decisions deferred for implementation time:

1. **Deep-copy strategy**: Per-type generated copy functions (like drop glue) vs runtime type descriptor traversal? Generated functions are faster; descriptors are more flexible for polymorphic code.

2. **Channel flavour**: Unbounded vs bounded channels? Bounded channels provide backpressure but can deadlock. Start unbounded and add bounded variants later?

3. **Error propagation**: What happens when a spawned task panics? Options: (a) terminate the whole process (current `cranelisp_panic` behaviour), (b) propagate the error to `recv` as an `(Error String)` variant, (c) ignore and let the channel hang.

4. **Task cancellation**: Should `Handle` support cancellation? Cooperative cancellation (check a flag) or preemptive (kill the thread)?

5. **Platform-specific vs language-level**: Should `spawn`/`chan` remain platform functions forever, or eventually become special forms with compiler support for ownership analysis?

6. **Interaction with file watching**: If a module is reloaded while a background task is running code from it, what happens? The GOT-based dispatch means the running task sees the old function pointers until the next call through the GOT. Reload during execution needs careful thought.

7. **Closure capture and send**: Closures capture values from their environment. Sending a closure across a thread boundary requires deep-copying all captures. The current lack of captured-type metadata (the same gap that prevents closure drop glue) must be resolved first.

8. **IVar representation**: Lenient evaluation requires distinguishing resolved values from pending computations at runtime. Tag bit (low bit of i64, since heap pointers are 8-byte aligned) vs sentinel range vs universal indirection?

9. **Cost heuristic for automatic parallelism**: How does the compiler estimate whether a computation is worth parallelizing? Options: conservative (only parallelize explicit recursion or known-expensive calls), annotation-guided (user marks expensive functions), or profile-guided (use runtime measurements from previous runs).

10. **Deferred IO and the REPL**: The REPL benefits from eager IO for interactive feedback — typing `(print "hello")` should print immediately, not defer until `main` returns. The REPL may need to force IO thunks immediately while batch mode defers. Alternatively, the REPL could force after each top-level expression.

11. **Task model interaction with module hot-reload**: If the runtime holds an unforced Task tree referencing function pointers from a module, and that module is reloaded, the Task tree holds stale pointers. The GOT-based dispatch helps (calls through GOT see new code), but direct function pointers in closures captured by Task continuations do not.
