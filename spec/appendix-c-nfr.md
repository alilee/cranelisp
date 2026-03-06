# Appendix C: Non-Functional Requirements

> **This appendix is normative.** It defines properties and constraints that a conforming implementation MUST preserve or MUST NOT preclude. These requirements do not specify language features — they constrain how features are implemented, ensuring the architecture supports the language's long-term direction.

Non-functional requirements (NFRs) differ from functional specification (Sections 1–12) in that they constrain the implementation space rather than the observable behavior. A program that runs correctly under one memory management strategy may violate NFRs if that strategy forecloses future capabilities the language commits to.

## C.1 Memory Management Properties [Tested]

### C.1.1 Deterministic Deallocation [Tested tests/rc.rs::rc_string_alloc_and_drop]

A conforming implementation MUST deallocate heap values deterministically — at a point in the program that is statically predictable from the source code, not deferred to a later collection phase. This rules out tracing garbage collectors as the primary strategy (though a tracing collector MAY supplement a deterministic allocator for cycle detection if the language later introduces mutable references).

**Rationale**: Deterministic deallocation enables copy-on-write optimization (§C.1.2), predictable latency for interactive and real-time use, and resource cleanup patterns where deallocation triggers side effects (e.g., closing file handles in drop glue).

**Design constraint**: The implementation must track ownership or reference counts — not rely on periodic tracing. Reference counting is the expected strategy given that Cranelisp's immutable values cannot form reference cycles.

**Activation**: Ring 1 (heap introduction).

### C.1.2 Reference-Count-Equals-One Optimization (RC=1 COW) [Tested tests/rc.rs::rc_vec_set_copy]

When a heap value has a reference count of exactly 1, operations that would otherwise copy MUST be permitted to mutate in place. This is the **copy-on-write** property: the implementation checks the reference count at runtime and either copies (rc > 1) or mutates (rc == 1). The optimization is semantically invisible — the caller observes pure functional behavior regardless.

This applies to:

1. **Vec operations** (`vec-set`, `vec-push`): When the Vec's reference count is 1, the backing storage MAY be mutated directly.
2. **String operations** (future: `string-set`, `string-append`): When the String's reference count is 1, the backing storage MAY be modified directly.
3. **ADT field update** (future: functional record update): When the ADT's reference count is 1, fields MAY be overwritten in place.

**Rationale**: RC=1 COW bridges the gap between functional semantics and imperative performance. A Vec built by repeated `vec-push` in a linear pipeline runs in amortized O(1) per element — identical to a mutable array — because each intermediate Vec has rc=1.

**Design constraint**: Heap headers MUST include a reference count field accessible at a fixed offset. The implementation MUST support a two-level check: compile-time liveness analysis (is this the last use of the binding?) combined with runtime rc==1 check. When both pass, the operation mutates in place.

**Activation**: Ring 1 (Vec COW in Ring 1 Chunk D or Sprint 3).

### C.1.3 Consuming Calling Convention [Tested tests/rc.rs::rc_string_passed_to_function]

Heap-typed function parameters MUST use a consuming calling convention: the callee owns the argument and is responsible for decrementing it (or transferring ownership onward). The caller performs a reference count increment for non-last-use arguments and transfers ownership (no increment) for last-use arguments.

**Rationale**: The consuming convention minimizes reference count operations. Combined with last-use analysis, a value passed through a chain of functions incurs zero RC overhead — ownership transfers at each call without increment/decrement pairs.

**Design constraint**: The implementation MUST perform last-use analysis to identify the final use of each variable binding. Captured variables (closed over by a lambda) are NEVER eligible for last-use transfer — the closure environment holds an implicit reference that drop glue manages.

**Activation**: Ring 1 (heap introduction).

### C.1.4 Per-Type Drop Glue [Tested tests/rc.rs::rc_adt_in_match_arms]

When a heap value's reference count reaches zero, the implementation MUST invoke type-specific drop glue that recursively decrements any heap-typed fields before freeing the allocation. Drop glue functions MUST be generated per type — not dispatched through a generic mechanism that examines runtime type tags.

**Rationale**: Static monomorphisation means the compiler knows the concrete type at every deallocation site. Per-type drop glue avoids runtime type dispatch overhead and enables the compiler to elide drop calls for types with no heap-typed fields.

**Design constraint**: Drop glue generation must be contained to a single codegen subsystem. The drop glue for a type depends only on the type's field layout — not on how the value was constructed.

**Activation**: Ring 1 (heap introduction).

## C.2 Data Structure Strategies [R3 S9]

### C.2.1 Persistent Vec (RRB Tree) [Tested tests/ring1.rs::vec_get_first]

The implementation MUST NOT commit to a flat-array Vec representation in a way that precludes upgrading to a persistent data structure based on Relaxed Radix Balanced (RRB) trees. RRB trees provide O(log₃₂ n) random access, O(log₃₂ n) update, and O(log₃₂ n) concatenation — with structural sharing that makes persistent functional updates cheap.

**Current status**: The reference implementation MAY use a flat contiguous array with RC=1 COW. This is simpler and sufficient for small-to-medium workloads.

**Future direction**: When workloads grow, or when persistent data structures become important for concurrent evaluation (§C.4), the Vec representation SHOULD transition to RRB trees. This transition MUST be semantically invisible — no user code changes.

**Design constraint**: Vec primitives (`vec-get`, `vec-set`, `vec-push`, `vec-len`, `vec-concat`) MUST be accessed through extern functions, NOT inline codegen. This ensures the representation can change from flat array to RRB tree without modifying the backend or typechecker. The type `(Vec a)` MUST remain opaque — user code cannot inspect Vec internals.

**Activation**: Post-Ring 4. The flat-array representation is acceptable through the ring sequence. RRB upgrade is a runtime-only change that does not affect language semantics.

### C.2.2 Persistent Map (HAMT) [R3 S9]

When the `Map` type is introduced, the implementation SHOULD use a Hash Array Mapped Trie (HAMT) as the backing data structure. HAMTs provide O(log₃₂ n) lookup, insert, and delete with structural sharing.

**Alternatives considered**:
- **Red-black tree** (Haskell-style): O(log n) operations, ordered keys, but no structural sharing in the Clojure sense. Requires `Ord` trait on keys.
- **Sorted vector**: O(n) insert/delete, O(log n) lookup. Simple but does not scale.
- **CHAMP** (Compressed Hash-Array Mapped Prefix-tree): An optimized HAMT variant with better memory locality. Preferred over standard HAMT if implementation complexity is acceptable.

**Design constraint**: Map operations MUST be accessed through extern functions. The `(Map k v)` type MUST be opaque. Key types MUST implement a `Hash` trait (to be specified when Map is introduced). The HAMT implementation lives in `cranelisp-runtime`, not in codegen.

**Activation**: Ring 2 or Ring 3 (when trait dispatch enables `Hash` and `Eq` constraints on key types).

### C.2.3 Rope Strings [Tested tests/ring1.rs::string_concat]

The implementation MUST NOT commit to a flat byte-array String representation in a way that precludes upgrading to a rope data structure. Ropes provide O(log n) concatenation and O(log n) indexing for large strings.

**Current status**: The reference implementation MAY use flat heap-allocated byte arrays. This is simpler and sufficient for strings under ~1MB.

**Future direction**: When string-heavy workloads (parsers, template engines, log processing) become important, the String representation SHOULD transition to ropes. This transition MUST be semantically invisible.

**Design constraint**: All string operations MUST go through extern functions in `cranelisp-runtime`. The backend MUST NOT read or write string bytes directly — all access goes through runtime helpers. The `String` type is opaque to codegen.

**Activation**: Post-Ring 4. The flat representation is acceptable through the ring sequence.

### C.2.4 Collection Extensibility [R3 S9]

The standard library SHOULD be able to provide alternative collection implementations alongside the built-in primitives. Users SHOULD be able to choose the collection type that best fits their use case, and write code that works generically across collection types via traits.

**Rationale**: Different use cases demand different data structures. A flat `Vec` with RC=1 COW gives O(1) random access — ideal for linear pipelines and small collections. An RRB tree gives O(log₃₂ n) persistent updates with structural sharing — ideal for concurrent access and large persistent workloads. Forcing all users onto one implementation serves neither case well.

**Design constraint**: The trait system MUST support collection-level abstraction. Specifically:
1. Multi-parameter traits (e.g., `(Indexed c a)` parameterized over container and element type) MUST be expressible.
2. Higher-kinded traits (e.g., `(Functor f)` parameterized over a type constructor) SHOULD be expressible, enabling `map` to work generically across collection types.
3. Opaque runtime-backed types (extern functions providing the implementation) MUST be registerable as first-class types participating in the trait system.
4. Alternative collection types (e.g., `PersistentVec`, `PersistentMap`, `Deque`) SHOULD be addable as stdlib types without modifying the compiler — only the runtime needs new extern functions.

**Model**: The primitive `Vec` and `Map` types use simple implementations with stable, predictable performance characteristics. The stdlib provides advanced alternatives (`PersistentVec` backed by RRB, `PersistentMap` backed by HAMT/CHAMP) as separate types. Both primitive and advanced types implement shared collection traits.

**Activation**: Ring 2 (when trait dispatch enables collection-level abstraction). Advanced collection types are post-Ring 4.

## C.3 Evaluation Properties [R4 S11]

### C.3.1 Lenient Evaluation [R4 S11]

An implementation MUST evaluate independent `let` bindings in parallel where a cost heuristic determines it is beneficial. This is normatively specified in [§12.4.3](12-runtime.md#1243-lenient-evaluation).

**Design constraint for architecture**: The implementation MUST design the function calling convention and stack layout to support spawning lightweight evaluation tasks for independent bindings. This does not require OS threads — lightweight tasks (green threads, work-stealing, or continuation-passing) are sufficient. The cost heuristic is implementation-defined but MUST exist (to avoid parallelizing trivially cheap operations).

**Activation**: Ring 4 (effects and runtime infrastructure). The mechanism requires safe stack management for parallel evaluation of pure sub-expressions.

### C.3.2 Automatic IO Scheduling [R4 S11]

The compiler MUST perform independence analysis on `bind!` chains and insert parallel execution nodes for commutative, data-independent effect pairs. This is normatively specified in [§10.12](10-io.md).

**Design constraint for architecture**: The IO trampoline MUST support concurrent execution of independent effect branches. The resource serialization model (token-based) MUST ensure that effects sharing a resource are sequenced while independent effects may run concurrently.

**Activation**: Ring 4 (IO and platform infrastructure).

### C.3.3 Tail Call Optimization [Tested tests/ring0.rs::tco_deep_countdown]

An implementation SHOULD optimize self-recursive tail calls into loops. This is normatively specified in [§12.5](12-runtime.md#125-tail-call-optimization).

**Future direction**: Mutual tail calls (tail calls between different functions) and tail calls through closures are desirable but not required. The implementation SHOULD design the calling convention to not preclude these optimizations — specifically, the closure calling convention (env_ptr as first argument) SHOULD be compatible with a future tail-call instruction if one becomes available in the compilation target.

**Activation**: Self-TCO in Ring 0. Mutual TCO and closure TCO are future extensions.

## C.4 Concurrency Preparation [R4 S11]

### C.4.1 Thread-Safe Reference Counting [Tested tests/rc.rs::rc_string_alloc_and_drop]

Reference count operations MUST use atomic instructions (or equivalent memory ordering guarantees) so that values can be shared across concurrent evaluation contexts without data races.

**Rationale**: Lenient evaluation (§C.3.1) and automatic IO scheduling (§C.3.2) both create concurrent evaluation contexts. If reference count operations are not atomic, sharing a heap value between two parallel let bindings would cause a data race.

**Design constraint**: RC increment MUST use at least Release ordering. RC decrement MUST use at least Release ordering, with an Acquire fence before deallocation (to ensure all prior writes to the object are visible before it is freed). This matches the pattern established by `std::sync::Arc` in Rust.

**Activation**: Ring 1 (heap introduction). Atomic operations MUST be used from the start — retrofitting atomicity is error-prone and requires auditing every RC operation site.

### C.4.2 Value Immutability [Tested tests/rc.rs::rc_vec_set_copy]

All user-visible values MUST be immutable after construction. There is no `set!` or mutable reference. This is a language-level guarantee that enables safe concurrent access without synchronization beyond reference counting.

**Rationale**: Immutability is the foundation that makes RC=1 COW safe (the optimization is invisible because no other reference can observe the mutation), lenient evaluation correct (parallel evaluation of pure expressions is deterministic), and structural sharing sound (shared subtrees cannot be modified by any holder).

**Design constraint**: The implementation MUST NOT expose mutable references to user code. Internal mutability (e.g., within the runtime's allocation tracking) MUST use appropriate synchronization.

**Activation**: Always (language invariant from Ring 0).

### C.4.3 No Global Mutable State in Generated Code [R4 S11]

Generated code MUST NOT use global mutable state (static mutable variables, global registries) for value-level operations. Module-level definitions are immutable after initialization. The GOT (Global Offset Table) used for JIT linking is a compile-time mechanism, not a runtime-mutable store.

**Rationale**: Global mutable state prevents safe parallel evaluation. If two parallel let bindings both write to a global, the result is non-deterministic.

**Design constraint**: Per-function state (locals, parameters) lives on the stack or in closure environments. Per-module state (definitions, type info) is write-once during compilation and read-only during execution. Runtime bookkeeping (allocation counters, trace state) MUST use thread-safe mechanisms (atomics or thread-local storage).

**Activation**: Always (structural invariant from Ring 0).

### C.4.4 Concurrent Communication [R4 S11]

The architecture MUST NOT preclude adding CSP-style (Communicating Sequential Processes) concurrent channels as a stdlib capability. Channels would enable coordination between concurrent tasks, complementing the automatic parallelism provided by lenient evaluation (§C.3.1) and IO scheduling (§C.3.2).

**Rationale**: Lenient evaluation and IO scheduling provide implicit parallelism (the compiler decides what runs in parallel). Channels provide explicit coordination (the user decides when to communicate). Both patterns are needed for a complete concurrency story. Channels enable producer-consumer patterns, fan-out/fan-in, and pipeline parallelism that cannot be expressed through `let` binding independence alone.

**Design constraint**:
1. The IO type and trampoline MUST be extensible with new effect kinds (channel operations are just new `Effect` node types) without modifying the trampoline's core dispatch logic.
2. The runtime task infrastructure built for lenient evaluation (§C.3.1) MUST be reusable for channel-based concurrency — the same lightweight task pool serves both.
3. Channel types (e.g., `(Chan a)`) MUST be registerable as opaque types in the type system, parameterized by element type, with operations exposed as extern functions returning `IO`.
4. Atomic RC (§C.4.1) and value immutability (§C.4.2) MUST be in place before channels are introduced, as values sent through channels are shared across concurrent tasks.

**Future direction**: A `go`-style macro (inspired by Clojure's core.async) MAY transform code bodies into state machines for cooperative scheduling, enabling parking channel operations inside lightweight tasks. This is a macro-level transformation — no compiler changes required, but it depends on a sufficiently powerful macro system (Ring 3+).

**Activation**: Post-Ring 4. Channels are a stdlib + runtime addition, not a language change. The shared infrastructure with lenient evaluation must be in place first.

## C.5 Compilation Properties [R4 S11]

### C.5.1 Static Monomorphisation [Tested tests/ring2.rs::constrained_add_int]

All constrained polymorphic functions MUST be monomorphised at call sites. The compiler generates specialized code for each concrete type instantiation. There is no runtime type dispatch for polymorphic functions.

**Rationale**: Static monomorphisation enables the compiler to know the concrete type at every expression node. This means: no runtime type tags needed for reference counting, per-type drop glue with no dispatch overhead, inlineable operations (e.g., `inc` on `Int` is a no-op), and predictable performance.

**Design constraint**: The type system and codegen must collaborate: the typechecker records concrete types at all expression nodes (`expr_types`), and the backend uses these to emit specialized RC operations, drop glue, and calling conventions.

**Activation**: Ring 0 (type inference), Ring 2 (trait dispatch and constrained polymorphism).

### C.5.2 Representation Containment [Tested crates/cranelisp-backend/src/heap.rs]

For each heap-allocated type (String, Vec, ADT, Closure), knowledge of the runtime representation MUST be confined to at most three locations:

1. **Layout constants** — offset definitions and size calculations
2. **Codegen emit helpers** — the functions that emit load/store instructions using layout constants
3. **Runtime primitives** — extern functions that operate on the type's internals

No other part of the compiler (parser, AST builder, typechecker, pipeline wiring) should know how a type is laid out in memory. This ensures that changing a type's representation (e.g., Vec from flat array to RRB tree) is a localized change, not a cross-cutting refactor.

**Rationale**: The prototype had heap layout knowledge spread across 6+ files, making representation changes impractical. This NFR prevents that pattern.

**Design constraint**: Backend codegen for heap types MUST use helper functions that abstract over offsets. The typechecker MUST use `HeapCategory` classification without knowing layouts. Pipeline wiring MUST treat heap values as opaque pointers.

**Activation**: Ring 1 (heap introduction).

### C.5.3 Three-Mode Compilation Strategy [R4 S11]

The architecture MUST support three compilation modes sharing a common frontend and typechecker:

1. **Dev mode (REPL)**: Cranelift JIT, function-by-function compilation, GOT-indirect calls for hot-reload. Optimised for interactive latency (<10ms per expression, §C.6.1).
2. **Quick build mode**: Link cached relocatable object files via system linker to produce a standalone executable. No re-compilation — linking only. Optimised for fast build cycles.
3. **Release mode**: Recompile reachable source through an optimising backend (LLVM via inkwell, or C emission) with whole-program optimisation (inlining, dead-code elimination, devirtualisation). Optimised for runtime performance at the cost of build time.

**Design constraint**: The primary abstraction boundary is `CheckResult + Program` — the output of the frontend + typechecker pipeline. This boundary type MUST be self-contained: no hidden state from the typechecker may leak to the backend. Any backend (Cranelift or LLVM) MUST be able to produce executable code from `CheckResult + Program` alone.

Within the Cranelift backend, a secondary boundary separates IR production from consumption: `FnCompiler` produces Cranelift `Function` objects; a consumer (`JITModule` for dev mode, `ObjectModule` for quick build) links them. `FnCompiler` MUST NOT call consumer-specific APIs (e.g., `JITModule::declare_function`). Module-level operations belong to the consumer, not the producer.

The runtime extern function contract (function names, calling conventions, signatures) MUST be shared across all backends. Both Cranelift and LLVM backends call the same `cranelisp_alloc`, `cranelisp_str_concat`, etc.

**Rationale**: Every mature functional language compiler maintains multiple compilation tiers (GHC: native codegen vs LLVM; Roc: dev backend vs LLVM; Julia: tiered JIT). The three modes serve distinct use cases that cannot be optimised simultaneously.

**Activation**: Dev mode and quick build mode in Ring 4 (module caching produces relocatable objects). Release mode is post-Ring 4 (LLVM backend is a future crate addition).

### C.5.4 Target Portability [R4 S11]

The architecture MUST NOT preclude targeting compilation platforms beyond the host native platform. Specifically, the architecture MUST support a future WASM (WebAssembly) target, enabling Cranelisp programs to run in browser and WASI environments.

**Design constraint**:
1. **Pointer-width containment.** Codegen emit helpers MUST distinguish values that represent pointers (target-width: i64 on native, i32 on wasm32) from values that represent data (always i64: Int, Float, Bool, tags). The backend MUST NOT assume that pointers and data values have the same width. In practice, this means emit helpers should use named constants or type aliases (e.g., `PTR_TYPE`) for pointer-width values, not hardcoded `i64`.
2. **Runtime portability.** The `cranelisp-runtime` allocation subsystem MUST be abstractable over allocation strategies — system `malloc`/`free` on native, WASM linear memory management on wasm32. The runtime extern function signatures MUST use opaque handles for heap pointers, not raw addresses.
3. **No OS-specific assumptions in library crates.** `cranelisp-types`, `cranelisp-frontend`, and `cranelisp-typecheck` are pure computation. They MUST compile to WASM without changes. OS-specific code (filesystem access, dynamic linking, mmap) MUST be confined to `cranelisp-runtime`, `cranelisp-backend`, and the binary crate.
4. **Platform DLL abstraction.** The platform loading mechanism MUST be abstractable over native dynamic linking and WASM module instantiation. The `cranelisp-platform` C-ABI contract (function signatures, `HostCallbacks`) MUST be expressible as WASM imports/exports.
5. **Thread-local storage abstraction.** Runtime bookkeeping that uses thread-local storage (trace state, allocation tracking) MUST have a WASM-compatible path (e.g., single-threaded `static` on wasm32, `thread_local!` on native).

**Rationale**: WASM is an increasingly important deployment target. A compiler that can target WASM enables browser-based REPLs (the compiler itself runs as WASM), server-side WASI deployment, and embedded use cases. The representation containment strategy (§C.5.2) is the primary enabler — if heap layout knowledge is confined, adapting to wasm32's address space is a localized change.

**Activation**: Post-Ring 4. No WASM targeting is required during the ring sequence, but architectural decisions during Rings 1–4 MUST NOT foreclose it.

## C.6 Performance Targets [Tested]

### C.6.1 Compilation Latency [Tested tests/repl_experience.rs::simple_eval_is_fast]

REPL expressions SHOULD compile and execute in under 10ms for simple expressions and under 100ms for module-sized compilation units. This is not a hard requirement but guides architectural decisions — e.g., preferring Cranelift (fast compilation) over LLVM (slow compilation, faster output) for the JIT tier.

### C.6.2 Allocation Pressure [Tested tests/rc.rs::rc_adt_enum_no_alloc]

The implementation SHOULD minimize allocation pressure for common patterns:
- Scalar operations (arithmetic, comparison, boolean logic) MUST NOT allocate.
- Function calls with no heap-typed arguments SHOULD NOT allocate.
- Nullary ADT constructors MUST NOT allocate (bare tag representation).
- RC=1 COW operations MUST NOT allocate when the reference count is 1.

### C.6.3 Test Suite Performance [Tested tests/repl_experience.rs::simple_eval_is_fast]

The full test suite SHOULD complete in under 30 seconds. Individual tests SHOULD complete in under 100ms. These targets guide decisions about test infrastructure (in-process vs. subprocess) and compilation caching.

## Cross-References

- [§12.3](12-runtime.md#123-memory-management) — Memory management requirements
- [§12.3.3](12-runtime.md#1233-vec-copy-on-write) — Vec COW specification
- [§12.4.3](12-runtime.md#1243-lenient-evaluation) — Lenient evaluation specification
- [§10.12](10-io.md) — Automatic IO scheduling specification
- [§12.5](12-runtime.md#125-tail-call-optimization) — Tail call optimization
- [§7](07-traits.md) — Traits, higher-kinded types, multi-parameter traits (collection extensibility)
- `design/arch/architecture.md` — Architectural decisions informed by these NFRs
- `design/arch/design-space.md` — Forward-compatibility analysis against these NFRs (Part 1: Ring 1 decisions, Part 2: beyond-ring resilience)
