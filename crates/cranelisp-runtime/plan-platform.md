# Platform Plan

Survey of the prototype platform and runtime crates, with a reimplementation plan organized by ring. This document inventories the C-ABI contract, maps crate responsibilities to the 7-crate DAG, proposes a panic handler redesign, and identifies per-ring deliverables.

## Source Material

Prototype crates surveyed:

- `sketch/cranelisp-platform/src/lib.rs` (769 lines) -- C-ABI contract, safe wrappers, `declare_platform!` macro
- `sketch/cranelisp-runtime/src/lib.rs` -- module root (4 submodules)
- `sketch/cranelisp-runtime/src/intrinsics.rs` (487 lines) -- alloc, RC, IO trampoline, IVar, panic
- `sketch/cranelisp-runtime/src/marshal.rs` (167 lines) -- Sexp/SList runtime marshalling
- `sketch/cranelisp-runtime/src/trace.rs` (317 lines) -- execution tracing (GOT swap, frame stack)
- `sketch/cranelisp-runtime/src/primitives/` -- int (86 lines), float (77 lines), bool (9 lines), string (77 lines), vec (429 lines)
- `sketch/platforms/stdio/src/lib.rs` (57 lines) -- reference stdio DLL
- `sketch/platforms/test-capture/src/lib.rs` (127 lines) -- test harness DLL

Specifications: `spec/10-io.md`, `spec/12-runtime.md`

Architecture: `design/arch/architecture.md`, `design/arch/interfaces.md`, `design/arch/ring0-interfaces.md`, `design/arch/roadmap.md`

Audit findings: `sketch/audits/codegen.md` (panic-related), `sketch/KNOWN_ISSUES.md` (process::exit)

---

## 1. C-ABI Contract Inventory

### 1.1 cranelisp-runtime: Functions Exported to JIT Code

Every function below uses `extern "C"` with all-`i64` parameters and return values. The JIT declares them as external symbols and calls them from compiled code.

#### Allocation and RC (intrinsics.rs)

| Export Name | Signature | Ring | Purpose |
|---|---|---|---|
| `cranelisp_alloc` | `(size: i64) -> i64` | 1 | Allocate `size` bytes with RC header (total_size + rc=1), return payload pointer |
| `cranelisp_free` | `(ptr: i64) -> i64` | 1 | Free heap object (reads total_size from `ptr-16`, deallocates) |
| `cranelisp_dec_guarded` | `(val: i64, guard: i64, drop_fn_ptr: i64) -> i64` | 1 | Guarded RC decrement: skip if val==guard or val<1024; call drop_fn on rc->0 |
| `cranelisp_dec_closure_guarded` | `(val: i64, guard: i64) -> i64` | 1 | Closure-specific guarded dec: loads drop_ptr from closure[1] |
| `cranelisp_dec_mixed_guarded` | `(val: i64, guard: i64, drop_fn_ptr: i64) -> i64` | 1 | Mixed (nullary/data) ADT guarded dec: skip if val<1024 (nullary tag) |
| `cranelisp_rc_underflow_check` | `(val: i64, old_rc: i64) -> i64` | 1 | Debug-mode RC underflow assertion + trace logging |

#### Panic Handler (intrinsics.rs)

| Export Name | Signature | Ring | Purpose |
|---|---|---|---|
| `cranelisp_panic` | `(msg_ptr: i64) -> i64` | 0 | Runtime panic (match failure, etc.) -- currently calls `process::exit(1)` |

#### IO Trampoline (intrinsics.rs)

| Export Name | Signature | Ring | Purpose |
|---|---|---|---|
| `cranelisp_run_io` | `(io_ptr: i64) -> i64` | 4 | Force IO task tree: trampoline loop over Pure/Effect/Bind/Par |

#### Parallel Evaluation (intrinsics.rs)

| Export Name | Signature | Ring | Purpose |
|---|---|---|---|
| `cranelisp_par_eval` | `(thunks_ptr: i64, count: i64) -> i64` | 4 | Evaluate N thunks in parallel (rayon), return results array |
| `cranelisp_ivar_create` | `(thunk: i64) -> i64` | 4 | Allocate IVar cell (state=PENDING, stores thunk closure) |
| `cranelisp_ivar_spark` | `(ivar: i64) -> i64` | 4 | Submit IVar to rayon thread pool for evaluation |
| `cranelisp_ivar_force` | `(ivar: i64) -> i64` | 4 | Force IVar: evaluate if PENDING, spin-wait if EVALUATING, return if RESOLVED |

#### Trace Runtime (trace.rs)

| Export Name | Signature | Ring | Purpose |
|---|---|---|---|
| `cranelisp_trace_swap_got` | `(got_base, n_slots, slots_ptr, wrappers_ptr) -> i64` | 4 | Save GOT, install trace wrappers, claim thread ownership |
| `cranelisp_trace_restore_got` | `(got_base, saved_got) -> ()` | 4 | Restore GOT from saved copy |
| `cranelisp_trace_enter` | `(name_ptr, name_len, params_count, params_array_ptr) -> ()` | 4 | Push trace frame at function entry |
| `cranelisp_trace_exit` | `(result, result_str_ptr) -> i64` | 4 | Pop trace frame at function exit, build TraceCall ADT |
| `cranelisp_collect_trace` | `() -> i64` | 4 | Collect root frame, release thread ownership, return Trace ADT |
| `cranelisp_trace_first_child_nanos` | `(trace_adt: i64) -> i64` | 4 | Extract nanos from first child (for run-tests timing) |

#### Sexp Marshalling (marshal.rs)

| Export Name | Signature | Ring | Purpose |
|---|---|---|---|
| `sconcat` | `(xs: i64, ys: i64) -> i64` | 3 | Concatenate two runtime SList values |
| `quote-sexp` | `(val: i64) -> i64` | 3 | Quote a runtime Sexp into constructor source code |

#### Primitive Functions (primitives/)

**Int (primitives/int.rs)**

| Export Name | Signature | Ring | Purpose |
|---|---|---|---|
| `int-to-string` | `(value: i64) -> i64` | 1 | Int to string representation |
| `cranelisp_op_add` | `(a, b) -> i64` | 0 | `+` as first-class value (checked) |
| `cranelisp_op_sub` | `(a, b) -> i64` | 0 | `-` as first-class value (checked) |
| `cranelisp_op_mul` | `(a, b) -> i64` | 0 | `*` as first-class value (checked) |
| `cranelisp_op_div` | `(a, b) -> i64` | 0 | `/` as first-class value (checked, div-by-zero guard) |
| `cranelisp_op_eq` | `(a, b) -> i64` | 0 | `=` as first-class value |
| `cranelisp_op_lt` | `(a, b) -> i64` | 0 | `<` as first-class value |
| `cranelisp_op_gt` | `(a, b) -> i64` | 0 | `>` as first-class value |
| `cranelisp_op_le` | `(a, b) -> i64` | 0 | `<=` as first-class value |
| `cranelisp_op_ge` | `(a, b) -> i64` | 0 | `>=` as first-class value |

**Float (primitives/float.rs)**

| Export Name | Signature | Ring | Purpose |
|---|---|---|---|
| `float-to-string` | `(value: i64) -> i64` | 1 | Float (bitcast i64) to string representation |
| `cranelisp_op_fadd` | `(a, b) -> i64` | 0 | Float `+` |
| `cranelisp_op_fsub` | `(a, b) -> i64` | 0 | Float `-` |
| `cranelisp_op_fmul` | `(a, b) -> i64` | 0 | Float `*` |
| `cranelisp_op_fdiv` | `(a, b) -> i64` | 0 | Float `/` |
| `cranelisp_op_feq` | `(a, b) -> i64` | 0 | Float `=` |
| `cranelisp_op_flt` | `(a, b) -> i64` | 0 | Float `<` |
| `cranelisp_op_fgt` | `(a, b) -> i64` | 0 | Float `>` |
| `cranelisp_op_fle` | `(a, b) -> i64` | 0 | Float `<=` |
| `cranelisp_op_fge` | `(a, b) -> i64` | 0 | Float `>=` |

**Bool (primitives/bool.rs)**

| Export Name | Signature | Ring | Purpose |
|---|---|---|---|
| `bool-to-string` | `(value: i64) -> i64` | 1 | Bool to "true"/"false" string |

**String (primitives/string.rs)**

| Export Name | Signature | Ring | Purpose |
|---|---|---|---|
| `string-identity` | `(value: i64) -> i64` | 1 | Identity (show on String) |
| `str-concat` | `(a, b) -> i64` | 1 | Concatenate two heap strings |
| `str-eq` | `(a, b) -> i64` | 1 | String equality comparison |
| `parse-int` | `(ptr: i64) -> i64` | 1 | Parse string as int, return Option Int ADT |

**Vec (primitives/vec.rs)**

| Export Name | Signature | Ring | Purpose |
|---|---|---|---|
| `vec-get` | `(vec_ptr, index) -> i64` | 1 | Bounds-checked element access |
| `vec-set` | `(vec_ptr, index, val) -> i64` | 1 | Always-copy set |
| `vec-push` | `(vec_ptr, val) -> i64` | 1 | Always-copy push |
| `vec-set-rc` | `(vec_ptr, index, val, inc_fn) -> i64` | 1 | Copy-set with element RC via fn ptr |
| `vec-push-rc` | `(vec_ptr, val, inc_fn) -> i64` | 1 | Copy-push with element RC via fn ptr |
| `vec-push-cow-grow` | `(vec_ptr, val) -> i64` | 1 | COW realloc when capacity exhausted and rc==1 |
| `vec-len` | `(vec_ptr) -> i64` | 1 | Return element count |
| `vec-map` | `(closure_ptr, vec_ptr) -> i64` | 1 | Apply closure to each element |
| `vec-reduce` | `(closure_ptr, init, vec_ptr) -> i64` | 1 | Left-fold over elements |

### 1.2 cranelisp-platform: C-ABI Contract for DLLs

**ABI Version**: 3 (prototype); reimplementation will reset to 1.

**Constants**:
- `IO_TAG_PURE = 0`, `IO_TAG_EFFECT = 1`, `IO_TAG_BIND = 2`, `IO_TAG_PAR = 3`
- `IO_EFFECT_RESOURCE_OFFSET = 16` (byte offset of resource token in Effect node)
- `STRING_HEADER_BYTES = 8` (length prefix size)

**C-ABI Structs** (all `#[repr(C)]`):

| Struct | Purpose | Fields |
|---|---|---|
| `PlatformFn` | Single function descriptor | name, jit_name, ptr, param_count, type_sig, docstring, param_names, scheduling_class |
| `HostCallbacks` | Host services for DLL | `alloc: extern "C" fn(i64) -> i64` |
| `PlatformManifest` | Manifest returned by DLL entry point | abi_version, name, version, functions, function_count |

**Safe Wrapper Types** (all `#[repr(transparent)]` over i64):

| Type | Purpose |
|---|---|
| `CLInt` | Integer value (i64 passthrough) |
| `CLString` | String value (pointer to `[len: i64][bytes...]`) |
| `CLBool` | Boolean value (0/1) |
| `CLFloat` | Float value (f64 bitcast to i64) |
| `CLIO<CL>` | IO-wrapped return value (allocates Pure or Effect node) |
| `CLOwned<T>` | RAII RC wrapper for heap CL types (inc on create, dec on drop) |

**Traits**:
- `CLType` -- marker trait for CL value types; provides `to_raw() -> i64`
- `CLHeap` -- trait for heap-allocated CL types; provides `inc_rc()`, `dec_rc()`, `own()`

**SchedulingClass** (`#[repr(u32)]`):
- `Sequential = 0` -- ordered relative to other calls
- `Commutative = 1` -- freely reorderable, no shared state
- `ResourceSerial = 2` -- parallel unless same resource token

**DLL Entry Point**: Every DLL exports exactly one function:
```c
extern "C" PlatformManifest cranelisp_platform_manifest(const HostCallbacks* callbacks);
```

**`declare_platform!` Macro**: Generates the entry point, handles host callback initialization, builds PlatformFn descriptors, derives JIT symbol names.

### 1.3 Platform DLL Functions

**stdio** (2 functions):

| CL Name | JIT Name | Signature | Scheduling |
|---|---|---|---|
| `print` | `cranelisp_print` | `(CLString) -> CLIO<CLInt>` | Sequential |
| `read-line` | `cranelisp_read_line` | `() -> CLIO<CLString>` | Sequential |

**test-capture** (2 platform functions + 4 test utilities):

| CL Name | JIT Name | Signature | Scheduling |
|---|---|---|---|
| `print` | (unnamed) | `(CLString) -> CLIO<CLInt>` | Sequential |
| `read-line` | (unnamed) | `() -> CLIO<CLString>` | Sequential |

Test utilities (not registered with JIT, accessed via libloading):
- `test_capture_set_input(lines, lens, count)`
- `test_capture_get_output(out_ptr, out_len)`
- `test_capture_free_output(ptr, len)`
- `test_capture_reset()`

### 1.4 Data Layout Assumptions

All values are i64 at the ABI boundary:

| Type | Layout |
|---|---|
| Int | i64 directly |
| Bool | 0 (false) / 1 (true) in i64 |
| Float | IEEE 754 f64 bits in i64 |
| String | Pointer to `[len: i64][bytes: u8...]` |
| Heap object | `[total_size: i64][rc: i64][payload...]`, pointer points to payload |
| Nullary ADT | Bare i64 tag (0, 1, 2, ...) -- threshold 1024 |
| Data ADT | Heap pointer to `[tag: i64][field0: i64]...` |
| Closure | Heap pointer to `[code_ptr: i64][cap0: i64]...` |
| Vec | Heap pointer to `[len: i64][cap: i64][data_ptr: i64]` |
| IO Pure | Heap `[tag=0, value]` -- 16 bytes |
| IO Effect | Heap `[tag=1, thunk_ptr, resource_token]` -- 24 bytes |
| IO Bind | Heap `[tag=2, inner_io_ptr, cont_closure_ptr]` -- 24 bytes |
| IO Par | Heap `[tag=3, count, io_ptr0, io_ptr1, ...]` |

---

## 2. Per-Ring Deliverables

### 2.1 Ring 0: Core (No Heap, No IO)

**`cranelisp-platform`**: No work required. The crate stub exists (`crates/cranelisp-platform/`). Ring 0 exercises zero platform functionality.

**`cranelisp-runtime`**: Minimal deliverables:

1. **`cranelisp_panic`** -- The panic handler is needed from Ring 0 for match exhaustiveness failures. However, it must be redesigned (see Section 3). The Ring 0 version takes a message string pointer and panics -- but instead of `process::exit(1)`, it should `panic!()` or use a recoverable mechanism.

<!-- FIXME(/platform): Operator wrappers may not be needed in Ring 0. The backend plan (Section 4.8) says Ring 0 does not support function values ("function values require closures -- not yet supported"). If operators-as-values like (let [f +] (f 1 2)) are not Ring 0, defer the 18 operator wrappers to Ring 1 when closures enable first-class function values. If they ARE Ring 0, the backend plan needs updating to support this pattern. -->
2. **Operator wrappers** -- When operators are used as first-class values (e.g., `(let [f +] (f 1 2))`), the backend emits a call to an extern function. Ring 0 needs the 18 operator wrappers (9 int, 9 float) from `primitives/int.rs` and `primitives/float.rs`.

3. **Allocation stub** -- `cranelisp_alloc` as a stub that panics ("heap not available in Ring 0") if called. This prevents accidental heap allocation in Ring 0 while allowing the symbol to be declared in the JIT.

**Decision**: The prototype places operator wrappers in `cranelisp-runtime`. In the reimplementation, these could live in `cranelisp-runtime` as well, since they are `extern "C"` functions that the JIT calls. They have no dependency on the heap.

**`platforms/`**: No platform DLLs in Ring 0.

### 2.2 Ring 1: Heap

**`cranelisp-runtime`**: Primary deliverables:

1. **Allocator** (`cranelisp_alloc`, `cranelisp_free`)
   - Heap layout: `[total_size: i64][rc: i64][payload...]`
   - Allocation counter, deallocation counter, bytes tracking, live-alloc set (debug)
   - `alloc_with_rc(size)` -- Rust-callable helper (shared by runtime and platform)

2. **RC primitives** (`cranelisp_dec_guarded`, `cranelisp_dec_closure_guarded`, `cranelisp_dec_mixed_guarded`, `cranelisp_rc_underflow_check`)
   - Guarded decrement with nullary tag check (val < 1024)
   - Drop function dispatch (type-specific or closure[1])
   - Atomic RC operations (Relaxed for inc, Release for dec, Acquire fence before free)

3. **String primitives** (`str-concat`, `str-eq`, `int-to-string`, `float-to-string`, `bool-to-string`, `string-identity`, `parse-int`)
   - String layout: `[len: i64][bytes: u8...]`
   - `alloc_string(bytes)` -- Rust-callable helper

4. **Vec primitives** (`vec-get`, `vec-set`, `vec-push`, `vec-set-rc`, `vec-push-rc`, `vec-push-cow-grow`, `vec-len`, `vec-map`, `vec-reduce`)
   - Vec layout: `[len: i64][cap: i64][data_ptr: i64]`
   - COW semantics for set/push when rc==1

5. **Panic handler redesign** (see Section 3)

**`cranelisp-platform`**: Begin platform C-ABI contract:

1. Define `HostCallbacks` with `alloc` callback
2. Define safe wrapper types (`CLInt`, `CLString`, `CLBool`, `CLFloat`)
3. Define `CLType` trait and `CLHeap` trait with RC operations
4. Define `CLOwned<T>` RAII wrapper
5. Define `CLIO<CL>` with `pure()` and `effect()` methods
6. Define IO tag constants
7. Define `PlatformFn`, `PlatformManifest`, `SchedulingClass`
8. Implement `declare_platform!` macro
9. Implement `manifest_to_descriptors()` safe conversion

**`platforms/`**: No DLLs yet -- platform contract being defined.

### 2.3 Ring 2: Abstraction

**`cranelisp-platform`**: Contract finalized and tested.

**`platforms/stdio/`**: Implement reference stdio DLL:
- `print :: (Fn [String] (IO Int))` -- Sequential
- `read-line :: (Fn [] (IO String))` -- Sequential
- Uses `declare_platform!` macro
- Uses `CLIO::effect()` for deferred execution
- Uses `CLOwned` for string parameter capture

**`cranelisp-runtime`**: No new deliverables beyond Ring 1. Sexp marshalling (`marshal.rs`) and trace (`trace.rs`) are deferred.

### 2.4 Ring 3: Meta

**`cranelisp-runtime`**: Sexp marshalling:
- `sconcat` -- SList concatenation
- `quote-sexp` -- quote runtime Sexp to constructor source
- ADT tag constants for Sexp, SList
- `alloc_adt()` and `build_runtime_list()` helpers

### 2.5 Ring 4: Effects

**`cranelisp-runtime`**: Full runtime:

1. **IO trampoline** (`cranelisp_run_io`) -- iterative Pure/Effect/Bind/Par loop
2. **Par node handling** -- rayon-based parallel IO branch execution
3. **Lenient evaluation** (`cranelisp_ivar_create`, `cranelisp_ivar_spark`, `cranelisp_ivar_force`) -- IVar write-once cells, rayon sparking, CAS-based evaluation
4. **Execution tracing** (`cranelisp_trace_swap_got`, `cranelisp_trace_restore_got`, `cranelisp_trace_enter`, `cranelisp_trace_exit`, `cranelisp_collect_trace`, `cranelisp_trace_first_child_nanos`) -- GOT-swap based tracing with thread ownership

**`platforms/test-capture/`**: Test harness DLL:
- Same `print`/`read-line` signatures as stdio
- In-memory buffers (`Mutex<Vec<String>>`, `Mutex<VecDeque<String>>`)
- Test utility exports for Rust test code

**`platforms/`**: Platform documentation, ergonomics validation.

---

## 3. Panic Handler Redesign

### 3.1 Prototype Behavior

The prototype's `cranelisp_panic` calls `std::process::exit(1)`:

```rust
#[unsafe(export_name = "cranelisp_panic")]
pub extern "C" fn panic(msg_ptr: i64) -> i64 {
    // ... extract message from heap string ...
    eprintln!("panic: {}", msg);
    std::process::exit(1);
}
```

The prototype's checked arithmetic operators (`cranelisp_op_add`, etc.) also call `process::exit(1)` on overflow/divide-by-zero. Vec bounds checks (`vec-get`, `vec-set`) do the same.

### 3.2 Why It Needs Redesign

Three documented problems from `sketch/KNOWN_ISSUES.md` and `sketch/audits/codegen.md`:

1. **Test harness kills**: `process::exit(1)` terminates the entire OS process, not just the current thread or test. Integration tests that trigger panics (match exhaustiveness, arithmetic overflow, vec bounds) must run with `--test-threads=1` and are `#[ignore]`. The `dotted_field_accessor_resolution` test is documented as sometimes killing the entire test process.

2. **REPL unrecoverable**: A panic in the REPL exits the process. The user loses their session state.

3. **No error information**: `process::exit(1)` produces no backtrace, no span, no structured error. The only output is an `eprintln!` to stderr.

Audit finding (codegen.md, HIGH-5): "Any panic in production generates an unrecoverable crash instead of a `CranelispError` with a span and message."

### 3.3 Proposed Approach

**Strategy**: Replace `process::exit(1)` with a Rust `panic!()` that is caught at the pipeline boundary.

**Ring 0 implementation**:

```rust
#[unsafe(export_name = "cranelisp_panic")]
pub extern "C" fn cranelisp_panic(msg_ptr: i64) -> i64 {
    let msg = extract_string(msg_ptr);
    panic!("cranelisp runtime error: {}", msg);
}
```

The binary crate wraps JIT function execution in `std::panic::catch_unwind()`:

```rust
let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
    unsafe { jit_fn() }
}));
match result {
    Ok(val) => Ok(val),
    Err(payload) => Err(CranelispError::RuntimeError { message, span }),
}
```

**Benefits**:
- Tests can catch runtime panics without process death
- REPL survives runtime errors and continues the session
- Structured error with message (and eventually span) propagated to the user

**Concerns and mitigations**:
- **Unwind safety**: JIT-compiled code is `extern "C"`, and unwinding through `extern "C"` frames is UB in Rust. The panic must be caught at the boundary between Rust and JIT code. Since `cranelisp_panic` is a Rust function called by JIT code, the panic originates in Rust, unwinds through Rust frames back to the `catch_unwind` boundary. JIT frames are not on the call stack at this point -- the JIT function called `cranelisp_panic` via an extern "C" function pointer, so the Rust runtime owns the panic propagation.
  - **IMPORTANT**: If the JIT code calls `cranelisp_panic` from within a deeply nested JIT call chain (e.g., JIT -> Rust runtime -> JIT -> Rust runtime), the intermediate JIT frames must not be on the unwind path. The `cranelisp_panic` function should use `longjmp`-style recovery rather than Rust panics for this case. A simpler alternative: register a thread-local "panic flag" that the JIT checks on return from extern calls, and propagate errors cooperatively.
- **RC cleanup**: A panic during execution leaks heap allocations. This is acceptable for the REPL (session state is preserved) and tests (allocations are short-lived). For batch mode, the process is about to exit anyway.
- **Operator overflow**: The spec says "integer overflow: silent wraparound (two's complement)". The prototype's checked arithmetic with `process::exit` on overflow contradicts the spec. The reimplementation should follow the spec: wrapping arithmetic for `+`, `-`, `*`, and a structured error for division by zero.

**Ring-by-ring rollout**:
<!-- FIXME(/platform): Commit to a specific panic recovery mechanism for Ring 0 before implementation begins. The current text leaves the deeply-nested case unresolved (panic!() vs longjmp vs thread-local flag). For Ring 0 (no nested JIT->Rust->JIT calls, no closures calling runtime functions), panic!() + catch_unwind is sound. State this explicitly and add a forward-reference that Ring 1+ (closures, callbacks) requires the thread-local error flag approach. -->
- **Ring 0**: `cranelisp_panic` uses Rust `panic!()`. Binary crate uses `catch_unwind`. Operator wrappers use wrapping arithmetic per spec (no panic on overflow). Division by zero returns a `CranelispError`.
- **Ring 1**: Vec bounds errors use the same mechanism. RC underflow check remains `debug_assert!` only.
- **Ring 4**: IO trampoline errors propagate through the continuation stack.

---

## 4. Crate Structure

### 4.1 Mapping to the 7-Crate DAG

```
cranelisp (binary)
  +-- cranelisp-backend
  |     +-- cranelisp-runtime
  |           +-- cranelisp-platform
  +-- cranelisp-platform (also direct dep for platform loading)
```

**`cranelisp-platform`** (`crates/cranelisp-platform/`):
- No cranelisp dependencies
- Defines the C-ABI contract: `PlatformFn`, `PlatformManifest`, `HostCallbacks`
- Defines safe wrapper types: `CLInt`, `CLString`, `CLBool`, `CLFloat`, `CLIO<CL>`, `CLOwned<T>`
- Defines `SchedulingClass` enum
- Provides `declare_platform!` macro for DLL authors
- Provides `manifest_to_descriptors()` for the host
- Provides `call_effect_thunk()` for the trampoline
- Provides `derive_jit_name()` utility

**`cranelisp-runtime`** (`crates/cranelisp-runtime/`):
- Depends on: `cranelisp-platform` (for IO tag constants, `call_effect_thunk`, `alloc_with_rc` use in CLIO)
- Submodules:
  - `intrinsics` -- alloc, free, RC primitives, panic handler, IO trampoline, IVar, par_eval
  - `primitives/` -- int, float, bool, string, vec extern functions
  - `marshal` -- Sexp/SList runtime marshalling (Ring 3)
  - `trace` -- execution tracing GOT swap (Ring 4)
- External dependency: `rayon` (for parallel evaluation in Ring 4; can be feature-gated)

**Platform DLLs** (`platforms/stdio/`, `platforms/test-capture/`):
- Depend only on `cranelisp-platform`
- Compiled as `cdylib` + `rlib`
- Not workspace members of the main workspace (they are independent crates that depend on the published `cranelisp-platform` interface)

**`cranelisp-backend`**:
- Depends on `cranelisp-runtime` (links its extern "C" symbols into the JIT)
- Owns platform DLL loading logic (`load_platform_dll`, `resolve_platform_path`)
- Owns `populate_builtin_func_ids()` for backfilling FuncIds onto DefKind::Primitive entries

**`cranelisp` (binary)**:
- Owns REPL `(platform ...)` interception
- Owns `ModuleEntry::PlatformDecl` creation
- Wires platform loading into the module graph build

### 4.2 Build Order

1. `cranelisp-platform` (no deps)
2. `cranelisp-types` (serde only)
3. `cranelisp-runtime` (depends on cranelisp-platform)
4. `cranelisp-frontend` (depends on cranelisp-types)
5. `cranelisp-typecheck` (depends on cranelisp-types)
6. `cranelisp-backend` (depends on cranelisp-types, cranelisp-runtime)
7. `cranelisp` (depends on all six)
8. Platform DLLs (depend on cranelisp-platform; built separately)

### 4.3 Platform DLL Build Integration

The prototype uses `just test` to build DLLs before running tests:

```
cargo build -p cranelisp-stdio -p cranelisp-test-capture
```

The reimplementation should follow the same pattern but with platform crates outside the main workspace (to avoid cdylib targets polluting the workspace build). A `justfile` recipe builds them separately.

DLL search paths (from prototype):
1. `./platforms/<name>.<ext>`
2. `./target/debug/libcranelisp_<name>.<ext>` (Cargo dev convenience)
3. `./target/release/libcranelisp_<name>.<ext>`
4. `~/.cranelisp/platforms/<name>.<ext>`

Where `<ext>` is `.dylib` (macOS), `.so` (Linux), `.dll` (Windows).

---

## 5. Known Issues and Risks

### 5.1 Platform DLL Loading Gotchas

1. **Library lifetime**: `libloading::Library` handles must be kept alive for the JIT's lifetime. The prototype stores them in `Vec<Library>` on the JIT. Dropping a Library unloads the DLL and invalidates all function pointers.

2. **Global state in DLLs**: Each DLL gets its own copy of `GLOBAL_ALLOC` (separate compilation unit). The `HostContext::init()` call must happen before any allocation. The `declare_platform!` macro calls it from the manifest function, which is correct. But if a DLL is loaded twice (or if two DLLs share a dependency), static state may collide.

3. **Thread safety of test-capture**: The test-capture DLL uses `Mutex<Vec<String>>` and `Mutex<VecDeque<String>>` as global state. Integration tests must run with `--test-threads=1` to avoid interleaving. The reimplementation should consider per-session capture state rather than global state.

4. **ABI version mismatch**: If a DLL is compiled against a different version of `cranelisp-platform`, the struct layouts may differ. The `abi_version` check catches this, but the error message should clearly say "rebuild the platform DLL".

5. **Symbol name collisions**: Two platforms exporting functions with the same JIT name would collide in the dynamic symbol map. The prototype does not guard against this. The reimplementation should prefix platform function JIT names with the platform name or check for collisions at load time.

### 5.2 ABI Stability Concerns

1. **Version reset**: The reimplementation resets ABI_VERSION to 1. All platform DLLs must be recompiled against the new `cranelisp-platform` crate.

2. **HostCallbacks evolution**: Adding a new callback (e.g., `free`, `panic`) changes the struct layout, requiring an ABI version bump. The prototype notes this as an open question. Options:
   - Strict version matching (simplest, current approach)
   - Nullable function pointers with sentinel values
   - Version field within HostCallbacks

   **Recommendation**: Keep strict version matching for simplicity. Version bumps are infrequent and platform DLL rebuilds are quick.

3. **String layout dependency**: Both the runtime and platform crates assume `[len: i64][bytes: u8...]` at the payload pointer. This is a deep assumption -- changing it requires changing every string operation in both crates. Document it as a frozen layout.

4. **RC header layout dependency**: The `CLHeap` trait in `cranelisp-platform` contains `inc_rc()` and `dec_rc()` methods that directly manipulate `ptr - 8` (RC) and `ptr - 16` (total_size). This couples the platform crate to the runtime's heap layout. The reimplementation should ensure the heap layout is documented as part of the ABI contract, not an implementation detail.

### 5.3 Cross-Platform Considerations

1. **DLL extensions**: `.dylib` (macOS), `.so` (Linux), `.dll` (Windows). The path resolution logic must handle all three.

2. **Calling convention**: `extern "C"` is SystemV on x86-64/aarch64 (macOS, Linux) and different on Windows. All-i64 parameters and return values avoid ABI complexity.

3. **Atomic ordering**: The prototype uses `Ordering::Relaxed` for most RC operations and `Ordering::Release`/`Ordering::Acquire` for dec-then-free. This is correct for single-threaded use and for the rayon-based parallelism model. Document the ordering requirements.

4. **Memory allocation alignment**: `Layout::from_size_align(total, 8)` assumes 8-byte alignment is sufficient. This is correct for i64-word-based layouts on all current targets.

### 5.4 Prototype Design Decisions to Reconsider

1. **Operator overflow behavior**: The prototype uses checked arithmetic and `process::exit(1)` on overflow. The spec says "silent wraparound (two's complement)". The reimplementation must follow the spec: use wrapping arithmetic for `+`, `-`, `*`. Keep checked division (division by zero is a runtime error per spec).

2. **Double-boxed thunks**: `CLIO::effect()` uses `Box<Box<dyn FnOnce() -> i64>>` to get a thin pointer. This adds an indirection. An alternative is to allocate the closure directly in the Effect node. The double-boxing is simple and correct; optimize only if profiling shows it matters.

3. **rayon dependency**: `cranelisp-runtime` depends on `rayon` for `par_eval` and IVar sparking. This is a heavy dependency. Consider feature-gating it behind `parallel` so Ring 0-3 builds do not pull in rayon.

4. **Global alloc in LIVE_ALLOCS**: The prototype tracks all live allocations in a `Mutex<HashSet<usize>>`. This is expensive in production. The reimplementation should make it debug-only (behind `cfg(debug_assertions)` or a feature flag).

5. **CLOwned RC manipulation**: `CLOwned::new()` increments RC and `Drop` decrements it. This is correct for the consuming calling convention (callee owns parameters). But it introduces a Rust Drop + atomic RC pair for every captured parameter in an Effect closure. Consider whether a non-incrementing "move" semantic is possible for the last-use case.

---

## 6. Summary: Implementation Order

| Ring | cranelisp-platform | cranelisp-runtime | platforms/ |
|---|---|---|---|
| 0 | Stub (exists) | `cranelisp_panic` (redesigned), 18 operator wrappers, `cranelisp_alloc` stub | -- |
| 1 | Full C-ABI contract, safe wrappers, `declare_platform!` macro | `cranelisp_alloc`/`cranelisp_free`, RC primitives, string primitives, vec primitives | -- |
| 2 | -- (finalized) | -- (stable) | `platforms/stdio/` |
| 3 | -- | `sconcat`, `quote-sexp`, marshal helpers | -- |
| 4 | -- | IO trampoline, IVar, par_eval, trace runtime | `platforms/test-capture/` |

---

## Next skills

- `/backend` -- Ring 0 codegen needs `cranelisp_panic` and operator wrapper symbols declared in the JIT; coordinate on the extern function registration pattern
- `/qa` -- Integration tests need the redesigned panic handler to be catchable; coordinate on `catch_unwind` boundary placement
- `/arch` -- Review the panic handler redesign (crosses crate boundaries: runtime -> backend -> binary) and the decision to feature-gate rayon
