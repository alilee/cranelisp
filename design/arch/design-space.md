# Design Space Analysis

Forward-looking analysis of architectural decisions against the non-functional requirements in `spec/appendix-c-nfr.md` and the broader direction the language may take.

**Part 1 (§1–9)** analyzes Ring 1 decisions: what they commit to, what they leave open, what would break if an NFR were activated, and the containment strategy.

**Part 2 (§10–14)** looks beyond the current ring roadmap at directions that could reshape the compiler: multi-mode compilation, deployment targets, stdlib-level data structures, concurrency primitives, and patterns from peer languages.

This is a risk-informed analysis, not a commitment to implement any feature. Its purpose is to ensure architectural decisions are made with eyes open — no "we can't do X later because Ring 1 baked in Y" surprises.

## Part 1: Ring 1 Decision Areas

### 1. Heap Header Layout

**Ring 1 commits to:**
- 16-byte `HeapHeader` with `alloc_size: i64` at offset 0 and `rc: i64` at offset 8.
- `alloc` returns the **base pointer** (start of struct). All offsets are positive. This departs from the sketch (which returned payload pointer with negative RC offset).
- `#[repr(C)]` structs with `offset_of!`-derived constants. Compile-time assertions verify offsets.
- RC initialized to 1 on allocation.

**What this leaves open:**
- Header could be extended (e.g., type tag, generation counter) by growing the header and updating `HeapHeader::SIZE`. All downstream code uses `HeapHeader::SIZE` for payload offset calculation — no hardcoded `16`.
- The header fields could change type (e.g., `rc` from `i64` to `AtomicI64`) without affecting codegen, since RC access goes through `HeapHeader::RC_OFFSET`.

**NFR interaction — C.4.1 Thread-Safe Reference Counting:**
Ring 1 MUST use atomic operations for RC from day one (per NFR C.4.1). The Cranelift `atomic_rmw` instruction provides Release-ordered add/sub. The header layout itself (i64 at a fixed offset) is compatible with atomic access — atomics operate on the same memory location regardless of whether the access is via `load`/`store` or `atomic_rmw`. No layout change required.

**What would break if activated later:** If Ring 1 used non-atomic `load`/`add`/`store` for RC and we later needed atomics for lenient evaluation, every RC emission site would need auditing. Since NFR C.4.1 says "from the start," this is a Ring 1 requirement, not a future concern.

**Containment:** RC access is emitted by `emit_rc_inc` and `emit_rc_dec` helpers in the backend — two functions. Switching between non-atomic and atomic is a change to these two functions only. But per the NFR, we start atomic.

**Decision:** Use `atomic_rmw` (Release ordering) for RC operations from Ring 1. The `HeapHeader` layout (i64 at offset 8) is compatible with both atomic and non-atomic access.

---

### 2. String Representation

**Ring 1 commits to:**
- Strings are Rust-managed via extern functions in `cranelisp-runtime`.
- The backend treats strings as opaque heap pointers — it never reads or writes string bytes directly.
- All string operations go through extern calls: `runtime/alloc_string`, `str-concat`, `str-eq`, etc.
- `HeapString` layout: `[HeapHeader | len: i64 | bytes: u8...]`.
- String literal codegen: store bytes in JIT data section, call `runtime/alloc_string(ptr, len)` at runtime.

**What this leaves open:**
- The `HeapString` struct is only known to `cranelisp-runtime`. The backend imports no string layout constants — it uses `HeapHeader` for RC and calls runtime functions for everything else.
- The runtime could change strings from flat arrays to ropes without any backend change.
- The extern function signatures (`(ptr, len) -> ptr`, `(ptr, ptr) -> ptr`) are representation-agnostic.

**NFR interaction — C.2.3 Rope Strings:**
The NFR requires not precluding rope upgrade. Ring 1's design satisfies this fully: the backend is opaque, all access is through extern calls, and the `HeapString` layout is internal to the runtime. A rope implementation would:
1. Change `HeapString` to a rope node struct in `cranelisp-runtime`.
2. Change `str_concat` (JIT: `str-concat`) from "alloc + memcpy" to "alloc rope branch node."
3. Change nothing in the backend, typechecker, or frontend.

**NFR interaction — C.1.2 RC=1 COW:**
Future string append-in-place (when rc==1) would be a change within `cranelisp-runtime` only. The backend never emits string mutation — it calls runtime functions that can internally check `rc==1`.

**What would break:** Nothing. This is the cleanest containment in the design.

**Containment:** Representation knowledge confined to `cranelisp-runtime/src/primitives/string.rs` (or equivalent). Zero codegen knowledge of string internals.

**Decision:** The Ring 1 string design is fully forward-compatible with ropes and RC=1 COW. No changes needed.

---

### 3. ADT Layout

**Ring 1 commits to:**
- `HeapAdt`: `[HeapHeader | tag: i64 | field_0: i64 | ... | field_n: i64]`.
- Nullary constructors are bare i64 tags (< `NULLARY_TAG_THRESHOLD`), NOT heap-allocated.
- Data constructors are heap-allocated with tag at offset 16, fields at offsets 24, 32, ...
- `NULLARY_TAG_THRESHOLD = 1024` — values below this are tag integers, above are heap pointers.
- Mixed nullary/data discrimination: runtime check `value < NULLARY_TAG_THRESHOLD`.
- Fields are accessed by positional offset: `HeapAdt::field_offset(i)`.

**What this leaves open:**
- The tag/field layout could change (e.g., fields-then-tag, or tagged pointer instead of separate tag field) by updating `HeapAdt` and the emit helpers. No other code knows the layout.
- Field access is through `heap_load(ptr, HeapAdt::field_offset(i))` — the offset calculation is centralized.

**NFR interaction — C.1.2 RC=1 COW (functional record update):**
Future `(with-fields point {:x 5})` would need to check `rc==1` on the ADT and either mutate in place or copy. This is a codegen concern: the backend emits the check and either stores directly or allocates+copies. The ADT layout supports both paths — field offsets are known at compile time, and `HeapHeader::RC_OFFSET` provides the refcount check.

**NFR interaction — C.1.4 Per-Type Drop Glue:**
Drop glue for ADTs loads each field by offset and decs heap-typed ones. The layout must support random field access by index — which it does (contiguous i64 slots). If fields were variable-width (e.g., inlined sub-structs), drop glue would need a different strategy, but NFR C.5.1 (monomorphisation) ensures the compiler always knows concrete field types, so variable-width fields are unlikely.

**NFR interaction — C.4.2 Value Immutability:**
ADT fields are write-once (at construction time) and read-only thereafter. The layout doesn't need to support concurrent writes — only the RC field needs atomic access (§1 above). Field reads are safe without synchronization because values are immutable after construction.

**What would break:** If ADTs needed variable-width fields (e.g., for unboxed nested structs), the `field_offset(i) = FIELDS_START + i * 8` formula breaks. But this would require a fundamental change to the value representation model (currently: all values are i64), which is beyond the NFR scope.

**Containment:** ADT layout knowledge confined to `HeapAdt` constants + `emit_adt_alloc` + `compile_match` field extraction + drop glue generation. Four sites, all in the backend.

**Decision:** ADT layout is forward-compatible with RC=1 COW and per-type drop glue. No changes needed.

---

### 4. Closure Environment Layout

**Ring 1 commits to:**
- `HeapClosure`: `[HeapHeader | code_ptr: i64 | cap_0: i64 | ... | cap_n: i64]`.
- Lambda body signature: `(env_ptr: i64, params...) -> i64` — env_ptr is the closure base pointer.
- Non-capturing lambdas and named-function wrappers allocate a minimal closure `[HeapHeader | code_ptr]`.
- Drop glue strategy: per-lambda drop function stored in a **side table** (`HashMap<*const u8, *const u8>` mapping code_ptr to drop_fn), NOT inline in the closure struct. This differs from the sketch (which stored `drop_ptr` at offset 8 in the closure).

**What this leaves open:**
- The side table could be replaced by inline `drop_ptr` if the space overhead (8 bytes per closure) becomes acceptable. The side table approach saves space (most closures have no heap captures, so drop glue is a no-op free).
- Capture ordering is compiler-determined and stable within a compilation unit. It could change between compilations without affecting correctness (closures are opaque to user code).

**NFR interaction — C.3.3 Tail Call Optimization (closure TCO):**
Mutual TCO through closures would require a tail-call-through-indirect mechanism. The current closure calling convention (`call_indirect(sig, code_ptr, [env_ptr, args...])`) is compatible: a future `tail_call_indirect` instruction (if Cranelift adds one) would use the same argument layout. The `env_ptr`-first convention doesn't block this.

Self-TCO within a closure (the closure calls itself recursively in tail position) is already possible with the loop-header pattern from Ring 0 — the closure body is just a function with an extra `env_ptr` parameter.

**NFR interaction — C.4.1 Thread-Safe RC:**
Closure environments are shared when a closure is passed to multiple consumers (e.g., stored in two bindings). The RC on the closure itself is atomic (per §1). Captured values inside the closure are read-only after construction (immutability guarantee, C.4.2), so no synchronization is needed for field access.

**NFR interaction — C.1.3 Consuming Calling Convention:**
Closures participate in the consuming convention as heap values. When passed as an argument at last-use, ownership transfers (no RC inc). The closure env is a single allocation — ownership of the env includes ownership of the captures (drop glue handles recursive dec).

**What would break:** If closures needed mutable state (e.g., for generators or coroutines), the current layout (immutable after construction) would be insufficient. But Cranelisp's purity guarantee (C.4.2) means closures are always immutable. Generators would be implemented as lazy sequences (Seq type with thunks), not mutable closures.

**Containment:** Closure layout knowledge confined to `HeapClosure` constants + `emit_closure_alloc` + closure call codegen in `apply.rs` + drop glue side table in the backend. The side table is entirely within the backend — no other crate knows about it.

**Decision:** The closure layout is forward-compatible with future closure TCO and thread-safe sharing. The side-table drop strategy is swappable. No changes needed.

---

### 5. Reference Counting Calling Convention

**Ring 1 commits to:**
- **Consuming convention** for cranelisp-to-cranelisp calls: callee owns heap-typed parameters, tracks them in a scope stack, and decs at scope exit.
- **Borrowed convention** for extern/platform calls: callee doesn't track params; caller decs temps after the call.
- **Last-use optimization**: liveness analysis identifies final use of each binding; at last-use, ownership transfers without RC inc.
- Capture variables are NEVER eligible for last-use transfer.
- Drop glue recursively decs heap-typed fields before freeing.

**What this leaves open:**
- The convention could be refined (e.g., "borrowed reads" from the sketch — skip inc/dec when loading a field from a known-unique owner). This is a pure codegen optimization; the convention is compatible.
- Static COW (skip runtime rc==1 check when the compiler can prove uniqueness + last-use) is an optimization within the existing framework.
- The consuming/borrowed split could be extended with a third convention if needed (e.g., "arena-allocated" for region-based future).

**NFR interaction — C.1.2 RC=1 COW:**
RC=1 COW for Vec requires the runtime rc==1 check at mutation sites. The consuming convention means the Vec argument is owned by the callee — so the callee can check `rc==1` and mutate in place. This is precisely the design: consume + check + mutate-or-copy. Forward-compatible.

**NFR interaction — C.1.3 Consuming Convention:**
This is the NFR itself — Ring 1 implements it directly.

**NFR interaction — C.3.1 Lenient Evaluation:**
Lenient evaluation spawns parallel tasks for independent let bindings. Each task may receive heap values as arguments. Under the consuming convention, each parallel task owns its arguments — no shared mutable state. When tasks complete, the let body receives the results. Atomic RC (§1) ensures safe sharing when a value is passed to multiple parallel tasks (rc incremented once per task, decremented when each task completes). The convention is compatible.

**What would break:** If we needed non-owning references across tasks (e.g., for zero-copy parallel reads), the consuming convention would require unnecessary rc inc/dec pairs. The sketch's "borrowed reads" optimization addresses this case: when a task only reads a field from a value it doesn't own, skip the inc/dec. This optimization can be added later within the existing framework — it doesn't require changing the convention itself.

**Containment:** Convention logic lives in `emit_consuming_caller_rc`, `emit_post_call_rc`, and `pop_scope_for_value` in the backend. Three functions.

**Decision:** The consuming/borrowed convention is forward-compatible with RC=1 COW, lenient evaluation, and future optimizations (borrowed reads, static COW). No changes needed.

---

### 6. Vec Representation (Sprint 3, but design space matters now)

**Ring 1 does NOT implement Vec** (deferred to Sprint 3, Chunk D). But Ring 1 decisions affect Vec's future.

**What Ring 1 establishes that Vec depends on:**
- `HeapHeader` layout — Vec will use the same header.
- `HeapCategory::classify` — already classifies Vec (via `Type::ADT` with args, returning `Mixed`). When Vec gets its own `Type::Vec` variant (if needed) or remains as a built-in ADT, the classification will be updated.
- Consuming convention — Vec arguments will be consumed/transferred like other heap values.
- Atomic RC — Vec's refcount will use the same atomic operations.

**NFR interaction — C.2.1 Persistent Vec (RRB Tree):**
The NFR requires Vec primitives go through extern functions, not inline codegen. This is critical: if `vec-get` were emitted as `heap_load(ptr, data_ptr_offset + i * 8)`, switching to RRB would require changing every `vec-get` emission site. By routing through `vec-get(vec_ptr, index) -> value` (Rust: `vec_get`), the representation is entirely in the runtime.

**Design space:**

| Approach | Pros | Cons | RRB upgrade cost |
|----------|------|------|-----------------|
| Flat array, all extern | Simple, forward-compatible | Function call overhead for `vec-get` | Runtime-only change |
| Flat array, inline `vec-get` | Fast reads | Codegen knows layout | Must change backend + runtime |
| RRB from day one | No upgrade needed | Complex, premature | N/A |

**Decision for Sprint 3:** All Vec primitives through extern functions. Accept the function-call overhead (likely <5ns per access). This preserves the RRB upgrade path as a runtime-only change.

**Containment:** `HeapVec` struct in backend layout module (for header + alloc sizing only). All element access through runtime extern calls. The backend emits `call vec-get(ptr, idx)`, never `heap_load(ptr, data_offset + idx * 8)`.

---

### 7. Map Representation (Ring 2+, design space only)

**Ring 1 establishes nothing that constrains Map.** Map is a new type that will be introduced when traits are available (Ring 2: `Hash` + `Eq` constraints on key types).

**NFR interaction — C.2.2 Persistent Map (HAMT):**
Map operations MUST go through extern functions. The `(Map k v)` type is opaque. The HAMT implementation lives in `cranelisp-runtime`.

**Design space:**

| Approach | Requires | RC complexity | Structural sharing |
|----------|----------|--------------|-------------------|
| HAMT (Clojure-style) | Hash trait on keys | Per-node RC | Yes |
| CHAMP (optimized HAMT) | Hash trait on keys | Per-node RC | Yes, better locality |
| Red-black tree | Ord trait on keys | Per-node RC | Limited |
| Sorted Vec | Eq trait on keys | Single RC + elements | None |

**Key constraint:** Per-node RC for tree structures (HAMT, RBT) means drop glue must recursively dec through the tree. This is the same pattern as nested ADTs — Ring 1's per-type drop glue infrastructure handles it. The drop glue for a HAMT node would dec its children (branches) and entries (key-value pairs), which may themselves be heap values.

**Decision:** Deferred to Ring 2. Ring 1 infrastructure (HeapHeader, atomic RC, consuming convention, per-type drop glue) supports all four approaches. The HAMT/CHAMP decision can be made when `Hash` trait dispatch is available.

---

### 8. Lenient Evaluation Runtime

**Ring 1 does NOT implement lenient evaluation** (Ring 4). But Ring 1's runtime model must not preclude it.

**What would a lenient evaluator need?**
1. A lightweight task abstraction (green threads, work-stealing pool, or continuation-passing).
2. Atomic RC (for values shared between tasks) — Ring 1 provides this.
3. No global mutable state in generated code — Ring 0/1 maintain this invariant.
4. A cost heuristic to avoid parallelizing trivial bindings.

**What Ring 1 decisions interact:**
- **Stack layout:** Each parallel task needs its own stack (or a segmented/growable stack). Ring 1 uses Cranelift's default stack frames. Cranelift doesn't support green threads natively — the runtime would need to provide them (e.g., via `mmap`-allocated stacks and manual switching, or by spawning OS threads for each parallel binding).
- **Closure convention:** If a let binding's expression is compiled to a closure (thunked for parallel evaluation), the closure convention (env_ptr + params) supports this. The binding expression becomes `(fn [] expr)` compiled as a closure with captures.
- **RC atomicity:** Already decided (atomic from Ring 1).

**What would break:** Nothing in the value representation or calling convention. The challenge is purely in the runtime task infrastructure, which is additive (new code in `cranelisp-runtime`, new compilation strategy in the backend for parallel let).

**Containment:** Lenient evaluation is a backend + runtime concern. The typechecker identifies independent bindings (no data dependency). The backend decides whether to parallelize (cost heuristic). The runtime provides the task infrastructure. No changes to types, frontend, or existing calling conventions.

**Decision:** Ring 1 is forward-compatible with lenient evaluation. No action required now.

---

### 9. Two-Tier Compilation (JIT + AOT)

**Ring 1 commits to:**
- Cranelift JIT as the sole compilation target.
- `FnCompiler` encapsulates per-function codegen.
- `Jit` struct wraps `JITModule` and provides compile/link/execute.

**NFR interaction — C.5.3 Two-Tier Compilation:**
The NFR requires that codegen logic be separable from JIT infrastructure. Ring 1 should maintain a clean boundary between "produce IR for this function" (portable) and "link into JIT module and execute" (JIT-specific).

**Design space:**

| Abstraction level | What changes for AOT | Risk |
|-------------------|---------------------|------|
| **No abstraction** — codegen calls JIT directly | AOT rewrite of all codegen | High: expensive retrofit |
| **`FnCompiler` is portable** — produces `Function` objects, `Jit` consumes them | AOT provides alternative consumer | Low: clean separation |
| **`Backend` trait** — full abstraction over JIT vs AOT | Two implementations of every operation | Medium: premature abstraction |

**Ring 1 position:** `FnCompiler` produces Cranelift `Function` objects. `Jit::compile_defn` consumes them into the JIT module. This is the second approach — portable IR production, JIT-specific consumption. An AOT backend would take the same `Function` objects and serialize them to an object file via Cranelift's `ObjectModule` instead of `JITModule`.

**What would break:** If `FnCompiler` directly calls `JITModule` methods (e.g., to declare or define functions), those calls are JIT-specific and would need abstraction. Ring 1 should keep `FnCompiler` producing `Function` objects and have `Jit` handle module-level operations.

**Containment:** Keep the `FnCompiler` → `Function` → `Jit.compile_defn` pipeline. The AOT path replaces `Jit.compile_defn` with `ObjectModule.define_function`. No `Backend` trait needed yet — the separation is structural (different structs), not polymorphic (trait objects).

**Decision:** Maintain `FnCompiler` as a portable IR producer. No trait abstraction needed in Ring 1, but `FnCompiler` must not reach into `JITModule` directly.

---

## Part 1 Summary: Ring 1 Forward-Compatibility

| Decision Area | NFRs Affected | Forward-Compatible? | Action Required |
|--------------|---------------|---------------------|-----------------|
| Heap header | C.4.1 (atomic RC) | Yes | Use `atomic_rmw` from Ring 1 |
| String repr | C.2.3 (ropes), C.1.2 (COW) | Yes, fully | None — opaque to codegen |
| ADT layout | C.1.2 (COW), C.1.4 (drop glue) | Yes | None |
| Closure env | C.3.3 (TCO), C.4.1 (atomic RC) | Yes | None |
| RC convention | C.1.2 (COW), C.1.3 (consuming), C.3.1 (lenient) | Yes | None |
| Vec (Sprint 3) | C.2.1 (RRB) | Yes, if extern-only | All primitives through extern calls |
| Map (Ring 2+) | C.2.2 (HAMT) | Yes | Deferred — Ring 1 infra supports all options |
| Lenient eval | C.3.1, C.4.1, C.4.3 | Yes | Runtime-only addition in Ring 4 |
| Two-tier compile | C.5.3 | Yes, if FnCompiler stays portable | Keep FnCompiler → Function boundary |

**Overall assessment:** Ring 1's proposed architecture is forward-compatible with all NFRs. The single required action is using atomic RC operations from the start (per NFR C.4.1), rather than deferring atomicity. All other NFR paths remain open through the representation containment strategy (§C.5.2) and the extern-function abstraction for opaque types.

---

## Part 2: Beyond-Ring Architectural Resilience

Part 2 examines directions that extend beyond the current ring roadmap. These are not commitments — they are structural properties the architecture should preserve to remain resilient to likely and potential evolution.

### 10. Three-Mode Compilation Pipeline

The compiler must support three distinct compilation modes, each serving a different use case.

**Mode 1 — Dev (REPL):**
- Compile function-by-function via Cranelift JIT.
- GOT-indirect calls for hot-reload.
- Cached .o files per function for incremental rebuilds.
- Target: interactive development, <10ms per expression (NFR C.6.1).

**Mode 2 — Quick build (standalone executable):**
- Link cached .o files from Mode 1 via system linker.
- No re-compilation — just linking. Seconds, not minutes.
- Target: CI, testing, distribution of non-optimised builds.
- Requires: module caching (Ring 4) produces relocatable object files, not just JIT code.

**Mode 3 — Release build (globally optimised executable):**
- Recompile reachable source through an optimising backend (LLVM via inkwell, or C emission).
- Whole-program optimisation: inlining, dead-code elimination, devirtualisation.
- Target: production deployment where runtime performance matters more than build time.

**Architectural implications:**

The real abstraction boundary is not `FnCompiler` → Cranelift `Function` — it is **frontend + typecheck → CheckResult + Program**. Modes 1 and 2 share the Cranelift backend (differing only in `JITModule` vs `ObjectModule` consumers). Mode 3 is a different backend entirely that produces LLVM IR (or C code) from the same AST + CheckResult.

```
Source → Frontend → TypeCheck → CheckResult + Program
                                        │
                                ┌───────┴───────┐
                                │               │
                    Cranelift Backend    LLVM Backend (future)
                         │                      │
                    ┌────┴────┐            ┌────┴────┐
                    │         │            │         │
                 JITModule  ObjectModule  inkwell   (C emit)
                  (Mode 1)   (Mode 2)    (Mode 3)  (Mode 3 alt)
```

**What the architecture must preserve:**

1. **CheckResult + Program is self-contained.** No hidden state leaks from the typechecker to the backend. The backend must be able to produce code from CheckResult + Program alone. Currently satisfied — `CheckResult` carries `expr_types`, `method_resolutions`, `mono_defns`, everything codegen needs.

2. **Runtime extern function contract is backend-agnostic.** Both Cranelift and LLVM backends call the same runtime functions (`runtime/alloc`, `str-concat`, etc.) with the same signatures. The JIT registration names and calling conventions are the shared contract.

3. **Module caching metadata is format-agnostic.** `CacheMetadata` stores content hashes, method resolutions, and expr types. These are backend-independent. The cached object file format (ELF .o vs LLVM .bc) is a separate concern stored alongside the metadata.

4. **`FnCompiler` must not call JIT-specific APIs.** It produces Cranelift `Function` objects. `Jit::compile_defn` consumes them. An `ObjectCompiler` would consume the same objects. `FnCompiler` must not reach into `JITModule` directly (e.g., to declare or define functions). Module-level operations belong to the consumer, not the producer.

**What `CompileMode` becomes:**

```rust
pub enum CompileMode {
    /// GOT-indirect calls for hot-reload. REPL and module reloading.
    Interactive,
    /// Direct calls, Cranelift ObjectModule output. Fast linking.
    Batch,
    /// Whole-program optimisation via LLVM. Slow build, fast output.
    Release,
}
```

The existing `CompileMode` enum already has these three variants. The architecture supports all three; the LLVM backend is a future crate addition, not a structural change.

**Peer patterns:** Roc maintains a dev backend (fast, custom codegen) and LLVM backend (optimised). GHC has native codegen vs LLVM backend, both consuming STG. Julia traces JIT-compiled methods and bundles them for AOT. The consensus: shared IR production with swappable consumers.

**Risk:** If `FnCompiler` accumulates JIT-specific concerns (e.g., direct GOT manipulation, JIT symbol resolution), it becomes non-portable. Ring 1 `/review` should watch for this.

---

### 11. Target Portability (WASM and Beyond)

Two scenarios for WASM deployment:

**Scenario A — Compile Cranelisp programs to WASM:**
The compiled output runs in a browser or WASI environment. This is Mode 2 or 3 targeting wasm32 instead of native.

**Scenario B — Run the compiler itself as WASM:**
The REPL runs in the browser. The entire compiler toolchain compiles to WASM. Cranelift-in-WASM produces WASM output. Instead of mapping executable memory, the compiler emits WASM modules and instantiates them via `WebAssembly.instantiate`.

**Architectural risks:**

1. **Pointer width.** All Cranelisp values are i64. On wasm32, pointers are i32 but data values (Int, Float) remain 64-bit. The current "everything is i64" simplification conflates data values with pointers. A WASM target would need to distinguish them.

   **Containment:** Introduce a `RawPointer` type alias in `cranelisp-types` alongside the existing i64 value type. In codegen, use `RawPointer` (which is `i64` on native, `i32` on wasm32) for heap pointers and `i64` for data values. The current architecture already treats heap values as opaque — the typechecker uses `HeapCategory` without knowing pointer width. The change is localized to backend emit helpers.

   **Current action required:** None. But Ring 1's emit helpers should document which i64 values are pointers vs data, to make a future wasm32 port tractable. A comment convention (`// ptr-width` vs `// data-width`) would suffice.

2. **Runtime portability.** `cranelisp-runtime` uses Rust extern functions linked at JIT time. For WASM, these would be compiled to WASM and imported via WASM module linking. The function signatures (all `extern "C"`) are WASM-compatible. The allocation strategy would change from `malloc`/`free` to WASM linear memory management.

   **Containment:** The runtime's allocation subsystem is already behind `runtime/alloc`/`runtime/dealloc`. Switching from system malloc to WASM linear memory allocator (e.g., `wee_alloc` or a bump allocator) is a change within the runtime crate only.

3. **Thread-local storage.** Trace state and allocation tracking use thread-local storage. WASM's threading model (SharedArrayBuffer + Web Workers) is fundamentally different from OS threads. TLS patterns need a WASM-compatible path.

   **Containment:** Use a `target_storage` abstraction in `cranelisp-runtime` that compiles to `thread_local!` on native and `static` (single-threaded) on wasm32. This is a runtime-only concern.

4. **Platform DLLs.** WASM uses module imports/exports, not dynamic linking. The `cranelisp-platform` C-ABI contract (`PlatformInit`, `HostCallbacks`) maps to WASM imports with adaptation. A WASM platform would be a WASM module that exports the same function signatures.

   **Containment:** Platform loading is already abstracted in the binary crate (`cranelisp`). The DLL loading mechanism can be swapped for WASM module instantiation without changing the platform contract itself.

**What the architecture must preserve:**

- Representation containment (NFR C.5.2) — heap layout knowledge confined to ≤3 locations per type. This is the primary enabler: if the backend doesn't hardcode pointer widths, wasm32 is a localized change.
- Runtime extern function signatures — must not assume pointer width in their interfaces. Use opaque `i64` handles for heap pointers in the extern function API (the runtime maps handles to actual pointers internally).
- No OS-specific assumptions in library crates. `cranelisp-types`, `cranelisp-frontend`, `cranelisp-typecheck` are pure computation — they should compile to WASM without changes.

**Peer patterns:** GHC's WASM backend targets wasm32-wasi. Roc uses its dev backend for WASM. Both demonstrate that a well-structured compiler can target WASM without fundamental rewrites — provided representation concerns are contained. The common lesson: the frontend and type system are trivially portable; the challenge is always in the runtime and backend.

---

### 12. Collection Extensibility (Data Structures as Stdlib)

The current plan assumes one `Vec` type that might upgrade from flat array to RRB tree (§6), and one `Map` type backed by HAMT (§7). An alternative: **primitive types stay simple, and the stdlib provides advanced alternatives alongside them.**

**Two models:**

| Model | Example | Philosophy |
|-------|---------|------------|
| **Upgrade** (Clojure) | One `Vec` type, runtime swaps flat → RRB invisibly | Users don't choose; the platform decides |
| **Extensible** (Haskell) | `Vec` (flat), `PersistentVec` (RRB), `Deque` (finger tree) — all separate types | Users choose the right tool; traits abstract over them |

**The extensible model has advantages for Cranelisp:**

1. **Predictable performance.** A flat `Vec` with RC=1 COW has O(1) random access. An RRB tree has O(log₃₂ n). Users writing performance-sensitive code need to know which they're getting.

2. **No magic runtime upgrade.** The behavior of `Vec` is stable across all versions. New data structures are additive — they don't change existing code's performance characteristics.

3. **Trait-based polymorphism.** The trait system (Ring 2) enables code to work generically across collection types. A function written against `(Indexed c a)` works with both `Vec` and `PersistentVec`.

4. **Independent iteration.** The RRB implementation can be developed, tested, and optimised without touching the primitive `Vec` at all.

**Language support required:**

The trait system must support collection-level abstraction. Key traits:

```clojure
;; Collection access
(deftrait (Indexed c a)
  (get [c Int] a)
  (len [c] Int))

;; Collection construction
(deftrait (Buildable c a)
  (empty [] c)
  (conj [c a] c))

;; Key-value access
(deftrait (Associative m k v)
  (assoc [m k v] m)
  (dissoc [m k] m)
  (lookup [m k] (Option v)))
```

These require:
- **Multi-parameter traits** (already in the spec, §7) — `Indexed` is parameterized over container and element.
- **Higher-kinded types** (already in the spec, §3/§7) — `Functor`, `Foldable` abstract over the container type constructor.
- **Opaque types through extern functions** (already the plan) — each collection implementation lives in the runtime.

**The runtime requirement:** Advanced data structures (RRB trees, HAMTs, finger trees) cannot be efficiently implemented in pure Cranelisp because each tree node would be a separate heap allocation with RC overhead. They must be Rust code in `cranelisp-runtime` exposed through extern functions. The type system sees them as opaque `Type::ADT` values; the runtime manages their internal structure.

**What this means for the current NFRs:**

- NFR C.2.1 (Persistent Vec / RRB) and C.2.2 (Persistent Map / HAMT) remain valid but shift meaning: instead of "upgrade `Vec`", they become "provide `PersistentVec` as a stdlib alternative". The constraint on extern-function-only access still applies — it enables both the primitive and advanced implementations.
- The primitive `Vec` and `Map` SHOULD start as simple implementations (flat array, hash table). Their performance characteristics are documented and stable.
- A `PersistentVec` (RRB) and `PersistentMap` (HAMT/CHAMP) SHOULD be provided as stdlib types when the trait system enables them (Ring 2+).

**Small-collection optimization (from Clojure):** For maps with <8 entries, a flat array scan is faster than a HAMT lookup. This is a runtime-internal optimization — the `map-get` function (Rust: `map_get`) checks the size and chooses the strategy. No language or compiler changes needed.

**Risk:** If the trait system cannot express collection abstractions (e.g., due to HKT limitations), users are forced to commit to specific collection types throughout their code. The spec already includes HKT (§3, §7), but the implementation complexity of HKT in Ring 2 is a known risk. Mitigation: even without HKT, multi-parameter traits like `(Indexed c a)` work for most collection-generic code.

---

### 13. Concurrent Channels

Channels enable CSP-style (Communicating Sequential Processes) coordination between concurrent tasks. The question: does this require language-level support, or can it be pure stdlib + runtime?

**What channels require at minimum:**

1. A channel type: `(Chan a)` — an opaque heap type, parameterized by element type.
2. Operations: `(chan-new)`, `(chan-put! ch val)`, `(chan-take! ch)` — all returning `IO`.
3. Select/alt: `(chan-select chans)` — wait on multiple channels.
4. A task/lightweight-thread runtime in `cranelisp-runtime`.

**All of this can be implemented without language changes:**

- `Chan` is an opaque type registered in the `primitives` module (like `IO`).
- Channel operations are extern functions in the runtime, returning `IO` values.
- `chan-put!` and `chan-take!` produce `Effect` nodes in the IO tree.
- The IO trampoline executes them, potentially on different threads.

**Where macros add value (Ring 3+):**

Clojure's `core.async` provides `go` blocks — a macro that transforms a code body into a state machine for cooperative scheduling. Inside a `go` block, `<!` (channel take) "parks" the block instead of blocking a thread, allowing thousands of concurrent `go` blocks on a small thread pool.

A similar `go` macro could work in Cranelisp:

```clojure
(go
  (let [x (chan-take! ch1)   ;; parks until value available
        y (chan-take! ch2)]
    (chan-put! ch3 (+ x y))))
```

The macro would rewrite this into a state machine that yields at each channel operation. This is a macro transformation — no compiler changes, but it requires:
- A runtime-provided task scheduler (shared with lenient evaluation, NFR C.3.1).
- A parking/resumption mechanism in the channel implementation.
- A sufficiently powerful macro system (CPS transformation of arbitrary expressions).

**Shared infrastructure with lenient evaluation:**

NFR C.3.1 (lenient evaluation) needs lightweight tasks, a thread/task pool, and safe value sharing. Channels need exactly the same infrastructure. The runtime task pool built for lenient evaluation serves both purposes. This is why C.3.1 is architecturally important even before channels are considered.

**What the architecture must preserve:**

- The IO type and trampoline must support new effect kinds without modification. Channel operations are just new `Effect` node types — the trampoline dispatches them like any other effect.
- Atomic RC (C.4.1) ensures safe value sharing across concurrent tasks.
- The runtime must be extensible with new extern functions (channel operations) without recompiling the compiler.

**Peer patterns:**
- **Clojure core.async**: Pure macro library, no JVM changes. `go` blocks compile to state machines at macro-expansion time. Parking works only inside `go` blocks (lexical scope limitation).
- **Haskell STM**: Library types (`TVar`, `STM` monad) + GHC runtime support (green threads). Composable transactions without deadlocks — enabled by purity (transactions can safely retry).
- **Roc**: Delegates all concurrency to the platform. No language-level concurrency primitives.
- **Go**: Channels are language-level primitives. Goroutines are M:N scheduled by the runtime. Deep language/runtime integration.

**Decision:** Channels do not require language changes. They are runtime extern functions + IO types + stdlib wrappers + optional macro sugar. The shared infrastructure with lenient evaluation means the runtime task pool serves both. Defer to post-Ring 4.

---

### 14. Peer Language Patterns — Cross-Cutting Lessons

Survey of Clojure, Roc, Carp, Haskell, Julia, and Common Lisp reveals architectural patterns relevant to Cranelisp's long-term resilience.

#### 14.1 Representation Containment is Universal

The most successful compiler architectures share a common property: the representation of a concept is hidden behind a narrow interface, allowing the implementation to change without ripple effects.

- **Roc's platforms**: Pure language code cannot observe how effects are executed.
- **Clojure's persistent data structures**: User code interacts through the `IPersistentCollection` interface; the backing trie structure is invisible.
- **GHC's STG**: The runtime's closure representation is hidden from Core optimisations.
- **SBCL's VOPs**: Value operations abstract over representation; the same Lisp code works with different tagging strategies.

Cranelisp's NFR C.5.2 (representation containment to ≤3 locations per heap type) codifies this principle. The design-space analysis confirms it holds across all nine Ring 1 decisions.

#### 14.2 The Evaluation Strategy Shapes Everything

Haskell's laziness enables `Data.Map` to use red-black trees (spine nodes aren't allocated until needed), makes STM possible (transactions retry by re-executing pure code), and enables stream fusion (lazy producers compose without intermediate allocations). Clojure's strictness (with lazy seqs) drives the persistent data structure commitment.

Cranelisp's lenient evaluation (strict by default, parallel when beneficial) is a middle ground. Key implication: data structures must be efficient under strict evaluation (no "spine laziness" to amortise allocation), but the parallelism story resembles Haskell's `par`/`pseq` more than Go's goroutines.

#### 14.3 Platform System Comparison

| Language | Effect System | Platform Abstraction | FFI |
|----------|--------------|---------------------|-----|
| Roc | `Task` + abilities | Platform provides all effects | Via platform only |
| Haskell | `IO` monad | Libraries + FFI | `foreign import` |
| Clojure | None (impure) | JVM interop | Java interop |
| Carp | None (impure) | C interop | `register` |
| Cranelisp | `IO` type + trampoline | Platform DLLs | Via platform only |

Cranelisp's platform system is closest to Roc's: the language is pure, all effects come from platforms, and user code cannot call foreign functions directly. This provides a natural security boundary and deployment portability — the same Cranelisp code runs on any platform that provides the required effect API.

**Roc's planned evolution** (effect capabilities as first-class values) is worth watching. If platforms could declare fine-grained capabilities ("this platform provides filesystem but not network"), the type system could enforce capability restrictions. This would require trait-like capability declarations — compatible with Cranelisp's trait system but not yet specified.

#### 14.4 Dual-Backend Compilation is Standard

Every mature functional language compiler maintains multiple backends or optimisation tiers:

| Language | Fast tier | Optimising tier |
|----------|-----------|-----------------|
| GHC | Native codegen (-fasm) | LLVM backend (-fllvm) |
| Roc | Dev backend (custom) | LLVM backend (--optimize) |
| Julia | Tier 1 JIT (quick) | Tier 2 JIT (LLVM optimised) |
| SBCL | Minimal compile | Block compilation + type inference |

Cranelisp's three-mode plan (§10) aligns with this pattern. The key lesson from GHC: the native codegen and LLVM backend share the same IR (Cmm). Both backends consume Cmm; neither influences how Cmm is produced. Cranelisp's equivalent is CheckResult + Program — the shared contract between frontend/typecheck and any backend.

#### 14.5 Carp's Ownership Model as Validation

Carp is a statically typed Lisp with ownership-based memory management (linear types) instead of garbage collection or reference counting. Key insight: Carp's ownership tracking eliminates the need for persistent data structures — mutation-in-place is always safe when you have ownership.

Cranelisp's RC=1 COW (NFR C.1.2) achieves a similar property for linear use patterns: a `Vec` built by repeated `vec-push` in a pipeline runs at mutable-array speed because each intermediate has rc=1. The difference: Carp enforces linearity at compile time (type error if you use a value twice); Cranelisp checks at runtime (rc==1 → mutate, rc>1 → copy). Carp's approach is zero-cost but restrictive; Cranelisp's is flexible but has a runtime check.

This validates the architectural decision to not require persistent data structures from day one. For linear use patterns (the common case), RC=1 COW on flat arrays matches persistent data structure performance without the complexity.

---

## Part 2 Summary: Beyond-Ring Architectural Resilience

| Direction | NFRs Affected | Architecture Resilient? | Key Constraint |
|-----------|---------------|------------------------|----------------|
| Three-mode compilation | C.5.3, C.5.4 | Yes | CheckResult + Program must be self-contained; FnCompiler must not call JIT APIs |
| WASM/target portability | C.5.4, C.5.2 | Yes, with care | Pointer-width containment in emit helpers; runtime allocation abstraction |
| Collection extensibility | C.2.1, C.2.2, C.2.4 | Yes | Trait system must support collection-level abstraction (HKT, multi-param traits) |
| Concurrent channels | C.3.1, C.4.1, C.4.4 | Yes | Shared task-pool infrastructure with lenient evaluation; IO trampoline extensibility |
| Peer patterns | All | Validated | Representation containment (C.5.2) is the linchpin — it enables all future directions |

**Overall assessment:** The 7-crate DAG, representation containment principle, extern-function pattern, platform system, and IO trampoline are resilient to all examined future directions. Two specific risks require attention:

1. **Pointer-width conflation** (§11): Ring 1 emit helpers should distinguish pointer-width values from data-width values via documentation/comments, so a future wasm32 port is tractable without auditing every i64 usage.

2. **FnCompiler portability** (§10): `FnCompiler` must produce Cranelift `Function` objects without reaching into `JITModule`. `/review` should enforce this boundary at each ring gate.

No immediate architectural changes are required. The current design is forward-compatible.

### 15. ANF with Defunctionalized Continuations (Stack-Safe General Recursion)

Cranelisp currently provides only self-recursive tail call optimization (loop-header pattern in Cranelift). This handles accumulator-style recursion (`fact-acc`, `fold`) but leaves structurally recursive algorithms (tree traversals, divide-and-conquer) relying on the system call stack. A user writing `(defn depth [t] (match t [(Leaf _) 1] [(Node l r) (+ 1 (max (depth l) (depth r)))]))` has implicit stack usage at every non-tail recursive call.

**The problem space:**

With first-class functions + TCO, any recursion is *expressible* via manual continuation-passing style (CPS) — the user threads a continuation through every call. But forcing users to write CPS is antithetical to the language's design. The question is whether and how the compiler could automate this.

**Three approaches, from lightest to heaviest:**

| Approach | Transform | Output | Type complexity | Cranelisp fit |
|----------|-----------|--------|----------------|---------------|
| **CPS transform** | Every function gets extra `k` parameter | All tail calls; "stack" is closure chain on heap | Polymorphic answer type `R` is fiddly in HM | Medium — closure chain = heap pressure |
| **ANF (naming intermediates)** | Every non-trivial sub-expression gets a `let` binding | Explicit evaluation order; NOT stack-safe by itself | None — trivial | Good as IR but insufficient alone |
| **ANF + defunctionalized continuations** | CPS transform, then replace continuation closures with ADT constructors | All tail calls; "stack" is a linked list of ADT frames on heap | Monomorphic per-function Kont type | **Best fit** — uses existing ADTs + TCO |

**How defunctionalized continuations work in Cranelisp's setting:**

The compiler internally generates a `Kont` ADT per function (or per SCC for mutual recursion), reifying each continuation point as a constructor:

```clojure
;; Source (user writes this):
(defn depth [t]
  (match t
    [(Leaf _) 1]
    [(Node l r) (+ 1 (max (depth l) (depth r)))]))

;; Compiler-internal output (user never sees this):
(deftype Kont
  Done
  (HaveLeft [:Kont k] [:Tree r])
  (HaveRight [:Kont k] [:Int dl]))

(defn depth [t] (depth-go t Done))

(defn depth-go [t k]
  (match t
    [(Leaf _)   (apply-k k 1)]
    [(Node l r) (depth-go l (HaveLeft k r))]))

(defn apply-k [k val]
  (match k
    [Done             val]
    [(HaveLeft k2 r)  (depth-go r (HaveRight k2 val))]
    [(HaveRight k2 dl) (apply-k k2 (+ 1 (max dl val)))]))
```

`depth-go` and `apply-k` are mutually tail-recursive. The `Kont` linked list on the heap is morally the call stack, but managed by RC like any other ADT value. When `apply-k` matches `Done`, the entire `Kont` chain is freed through normal drop glue.

**Why this fits Cranelisp particularly well:**

1. **ADTs already exist.** The generated `Kont` type uses the same representation as user ADTs — same heap layout, same tag dispatch, same drop glue. No new runtime infrastructure.

2. **Purity eliminates ordering constraints.** The ANF pass can freely reorder bindings since all expressions are pure. This gives the compiler maximum freedom during the transform.

3. **Static types make `Kont` monomorphic.** Each function's continuation type is fully determined at compile time — no polymorphic answer-type headache that plagues CPS in HM systems. The `Kont` type for `depth` holds exactly `Tree` and `Int` values.

4. **Mutual recursion maps to mutual TCO.** The output (`depth-go` / `apply-k`) is mutually tail-recursive. The current TCO infrastructure handles self-recursion; extending to mutual TCO within an SCC (strongly connected component) is an incremental change — both functions compile to a shared loop with a dispatch tag.

5. **RC manages the "stack" lifetime.** Each `Kont` frame is heap-allocated with RC. When the computation completes, frames are freed in reverse order through `apply-k`'s pattern matching. No separate stack deallocation mechanism needed.

**Architectural implications:**

- **Pipeline position**: The transform would sit between typechecking and codegen — it rewrites `CheckResult`'s AST and adds synthetic ADT types. The typechecker sees the original; the backend sees the transformed version. This preserves the `CheckResult` boundary contract.

- **Selectivity**: The transform only fires for functions with non-tail recursive self-calls. Functions already in tail form pass through unchanged (principle 9: accretive). A simple walk identifies candidates: any `Apply` node targeting the current function where the `Apply` is not in tail position.

- **Mutual recursion**: For SCCs, a combined `Kont` type covers frames from all functions in the SCC. The analysis is whole-SCC, not per-function. SCC detection is a standard graph algorithm on the call graph.

- **Space behavior**: Naive defunctionalized CPS builds heap-allocated `Kont` chains proportional to recursion depth. For tree traversal of depth `d`, this is O(d) — same as a call stack. For pathological cases (e.g., processing a million-deep linked list), the heap pressure is real. Potential mitigations: detect linear recursion (single recursive call in tail-of-continuation) and optimize to iterative form; or use a flat Vec as a stack for the `Kont` frames instead of a linked list.

- **Ring placement**: This is a Ring 4+ optimization. Rings 0-3 establish the language surface; the defunctionalization pass is an internal optimization that doesn't change semantics. Users who need stack safety before Ring 4 can write tail-recursive code manually (which is always possible in a pure language with ADTs).

**What the architecture must preserve:**

- `CheckResult + Program` must remain the boundary contract. The transform produces a new `Program` with additional `TypeDef` and `Defn` nodes — it does not change the contract shape.
- Synthetic ADT types generated by the transform must not collide with user types. A naming convention (e.g., `__Kont_depth__`) or a synthetic module handles this.
- Drop glue generation must handle `Kont` types correctly — they are ordinary ADTs with heap-typed fields.

**Decision:** No action required now. The architecture is compatible. When implemented (Ring 4+), the transform is a pass between typecheck and codegen that rewrites AST nodes and generates synthetic ADT types. All existing infrastructure (ADT layout, drop glue, mutual TCO) supports it. The main design work is the transform itself — identifying continuation points, building the `Kont` type, and splitting functions into dispatch + apply.

---

### 16. AI-Integrated REPL (Claude as Conversational Partner)

An alternative REPL model where the interactive session integrates an LLM (Claude) as a conversational partner alongside the language evaluator. The two share a single prompt — the dispatch rule determines which handles each input.

**The dispatch rule:**

```
Input starts with ( or is a literal  →  language evaluator (as today)
Anything else                        →  Claude (natural language)
```

Bare identifiers (`foo`) evaluate as today (symbol lookup). Natural language is distinguished syntactically — Cranelisp expressions always start with `(` or are literals/identifiers. A sentence like "how do I sum the leaves?" is unambiguously not a Cranelisp form.

**Claude's context:**

Each Claude turn receives a system prompt populated from the live session:

- Current module name and import list
- Signatures and docstrings of all visible bindings (from the `CompiledModule` symbol table)
- A doc manifest showing which `.md` files exist and their coverage
- Session notes (see Memory below)

This reuses existing infrastructure: `ModuleEntry` already stores types, docstrings, and classification. The `/list` and `/sig` handlers already serialize this information — the AI context is the same data in a different format.

**Tool interface:**

Claude gets tools that operate on the live REPL session:

| Tool | Effect | Maps to |
|------|--------|---------|
| `eval` | Evaluate a form, return result + type | `ReplSession::eval()` |
| `type-of` | Return type without evaluating | `/type` handler |
| `expand` | Macro-expand a form | `/expand` handler |
| `define` | Add a binding to the session | `ReplSession::eval()` on a `defn` |
| `read-doc` | Read a `.md` file | filesystem read |
| `write-doc` | Create/overwrite a doc file | filesystem write |
| `patch-doc` | Edit a section of a doc by heading | structured edit |
| `list-docs` | List available doc files | filesystem scan |
| `note` | Append to session memory | write to `.repl/session.md` |

The key property: Claude doesn't just describe code — it executes it in the running environment and shows real results. Type errors feed back as tool results, enabling self-correction. The user sees the working version or a clear explanation of why it can't work.

**Memory model (layered `.md` files):**

| File | Scope | Content |
|------|-------|---------|
| `~/.repl/preferences.md` | Global, user-level | Style preferences, interaction patterns, documentation tone |
| `project/.repl/context.md` | Project-level | Architecture decisions, naming conventions, domain knowledge |
| `project/.repl/session.md` | Per-session, ephemeral | Working decisions, current focus, Claude's self-notes via `note` tool |

All memory is plain markdown files the user owns, can read, hand-edit, and version control. No opaque database. Claude reads them in context and can write to them with tools, but the user has final authority.

**Architectural implications for Cranelisp:**

1. **No language changes required.** The AI integration is entirely in the binary crate's REPL implementation. The language evaluator, type system, and compilation pipeline are unchanged. Claude is a consumer of existing APIs (`ReplSession::eval`, symbol table queries), not a new pipeline stage.

2. **`ReplSession` as the API surface.** The existing `ReplSession` struct provides everything Claude's tools need: `eval()` for execution, `tc` for type queries, `got_state` for symbol lookup. The AI integration layer wraps `ReplSession` rather than modifying it.

3. **Context serialization reuses `/list` + `/sig` infrastructure.** The code that formats symbol information for `/list`, `/sig`, and `/info` already converts `ModuleEntry` data into human-readable strings. The AI context format is a superset — same data, formatted for an LLM system prompt instead of terminal output.

4. **Offline graceful degradation.** When no API connection is available, the REPL works exactly as today — all expression evaluation is local. Only the natural-language path is unavailable. The language is never dependent on the AI service.

5. **Doc tools are filesystem operations.** `read-doc`, `write-doc`, `patch-doc`, `list-docs` are thin wrappers around filesystem I/O. They don't interact with the compilation pipeline. The `patch-doc` tool needs a markdown-aware section editor (find heading, insert/replace content), but this is straightforward string manipulation.

6. **Provenance transparency.** Claude's tool calls should be visible in the REPL output (e.g., `[eval: (sum-tree ...)]` → `Result: 6`) so the user always sees exactly what was executed. This aligns with the self-documentation principle — the REPL shows everything, hides nothing.

**Interaction with existing design:**

- **Platform model**: The AI integration is NOT a platform. Platforms provide IO effects for Cranelisp programs. The AI integration provides a conversational layer around the REPL — it doesn't execute as part of user programs.

- **Module system**: Claude sees the same module structure the user sees. When the user switches modules (`/mod math`), Claude's context updates to show `math`'s bindings. Module privacy is respected — Claude cannot access private bindings any more than the user can.

- **Macro system**: Claude can use `expand` to understand macro behavior, and `define` to create macros. The macro expansion pipeline is used as-is.

**Ring placement:** Post-Ring 4. The AI integration depends on a fully functional REPL (all slash commands, module system, macros, IO). It is additive — no existing code changes, just a new dispatch layer in the binary crate's REPL loop.

**Decision:** No architectural changes required. The existing `ReplSession` API, symbol table infrastructure, and slash command handlers provide the foundation. The AI integration is a binary-crate-only addition that wraps the existing REPL with a dispatch rule and tool interface. File as a post-Ring-4 enhancement.

---

## Part 2 Summary: Beyond-Ring Architectural Resilience

| Direction | NFRs Affected | Architecture Resilient? | Key Constraint |
|-----------|---------------|------------------------|----------------|
| Three-mode compilation | C.5.3, C.5.4 | Yes | CheckResult + Program must be self-contained; FnCompiler must not call JIT APIs |
| WASM/target portability | C.5.4, C.5.2 | Yes, with care | Pointer-width containment in emit helpers; runtime allocation abstraction |
| Collection extensibility | C.2.1, C.2.2, C.2.4 | Yes | Trait system must support collection-level abstraction (HKT, multi-param traits) |
| Concurrent channels | C.3.1, C.4.1, C.4.4 | Yes | Shared task-pool infrastructure with lenient evaluation; IO trampoline extensibility |
| ANF + defunctionalized continuations | C.3.3 (TCO) | Yes | Transform between typecheck and codegen; synthetic ADTs use existing infrastructure |
| AI-integrated REPL | None (additive) | Yes | `ReplSession` API is sufficient; binary-crate-only addition; offline graceful degradation |
| Peer patterns | All | Validated | Representation containment (C.5.2) is the linchpin — it enables all future directions |

**Overall assessment:** The 7-crate DAG, representation containment principle, extern-function pattern, platform system, and IO trampoline are resilient to all examined future directions. Two specific risks require attention:

1. **Pointer-width conflation** (§11): Ring 1 emit helpers should distinguish pointer-width values from data-width values via documentation/comments, so a future wasm32 port is tractable without auditing every i64 usage.

2. **FnCompiler portability** (§10): `FnCompiler` must produce Cranelift `Function` objects without reaching into `JITModule`. `/review` should enforce this boundary at each ring gate.

No immediate architectural changes are required. The current design is forward-compatible.

## Cross-References

- `spec/appendix-c-nfr.md` — The NFRs this document analyzes (including C.2.4, C.4.4, C.5.4 added alongside this analysis)
- `design/arch/architecture.md` — Crate structure and key decisions
- `design/arch/interfaces.md` — Current boundary type definitions
- `design/arch/roadmap.md` — Ring-by-ring progression plan
- `sketch/docs/heap_layout.md` — Prototype heap layout (reference for offset strategy)
- `sketch/docs/data-structures.md` — Prototype RC and COW design
- `sketch/docs/closures.md` — Prototype closure layout
