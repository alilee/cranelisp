# Runtime Solution Design

This document describes the `cranelisp-runtime` crate design: how the runtime supports JIT-compiled code with heap allocation, reference counting infrastructure, opaque string operations, and type conversion primitives.

## Architectural Context

The runtime is a Rust crate exposing `extern "C"` functions that JIT-compiled code calls at runtime. It sits below the backend in the crate DAG:

```
cranelisp-backend → cranelisp-runtime → cranelisp-types
                                       → cranelisp-platform
```

The backend emits Cranelift IR that calls these functions by JIT symbol name (see `src/CLAUDE.md` §"JIT Symbol Names"). Runtime infrastructure functions are registered under the `runtime/` namespace (e.g., `runtime/alloc`, `runtime/panic`). User-visible primitives use their spec name in kebab-case (e.g., `str-concat`, `int-to-string`). The runtime does NOT own the RC inc/dec operations — those are emitted inline by the backend as `atomic_rmw` instructions (see `design/arch/interfaces.md` §RC Operations). The runtime provides supporting infrastructure: allocation, deallocation, trace logging, and the underflow check diagnostic.

## Base-Pointer Convention

All heap pointers point to offset 0 of the allocation — the `alloc_size` field. This differs from the sketch prototype, which used an interior-pointer convention (pointer to payload, header at negative offsets).

**Rationale**: Base-pointer is simpler for the backend to codegen (all field access uses positive offsets), simpler to debug (pointer value = allocation address), and simpler for deallocation (no offset arithmetic needed).

**Trade-off**: Every field access from JIT code requires adding the header size as offset. With the interior-pointer convention, payload field 0 would be at offset 0. The added constant offsets are a minor code-size cost, offset by the elimination of negative-offset complexity.

## Heap Layout

Defined in `cranelisp-types::HeapHeader`:

```
Offset  Size  Field
─────── ───── ─────────────────
0       8     alloc_size (i64) — total allocation size in bytes
8       8     rc (i64)         — reference count (atomic)
16+     var   payload          — type-specific data
```

All heap objects share this header. The `alloc_size` field enables deallocation without tracking layout externally — `heap_dealloc()` reads it from the object itself.

`HeapHeader` lives in `cranelisp-types` (not runtime) because both the backend (codegen offset constants) and the runtime (allocation/deallocation) need it. The `#[repr(C)]` annotation and compile-time offset assertions guarantee ABI stability.

## Allocator (`alloc.rs`)

### Allocation

`alloc_with_rc(payload_size)` allocates `HeapHeader::SIZE + payload_size` bytes via `std::alloc::alloc_zeroed`, writes the header (alloc_size, rc=1), and returns the base pointer.

Zero payload is valid — produces a bare 16-byte header. This supports nullary ADT constructors that need heap representation (though currently nullary constructors use bare i64 tags, this provides forward compatibility).

### Deallocation

`heap_dealloc(base)` reads `alloc_size` from offset 0, reconstructs the `Layout`, and calls `std::alloc::dealloc`. Registered as `runtime/dealloc` in the JIT. This is called when RC reaches zero — either by the backend's inline dec sequence or by the runtime itself (e.g., string operations that produce temporary results).

### Tracking Counters

Five atomic counters track allocation behaviour:

| Counter | Purpose |
|---------|---------|
| `ALLOC_COUNT` | Total allocations (monotonic) |
| `DEALLOC_COUNT` | Total deallocations (monotonic) |
| `BYTES_ALLOCATED` | Total bytes ever allocated (monotonic) |
| `BYTES_CURRENT` | Bytes currently live |
| `BYTES_PEAK` | High-water mark (CAS loop update) |

All use `AtomicUsize` with `Ordering::Relaxed` — sufficient for counters that don't synchronise other data.

### Debug: LIVE_ALLOCS

In debug builds (`#[cfg(debug_assertions)]`), a `Mutex<HashSet<usize>>` tracks live allocation addresses. `alloc_with_rc` inserts, `heap_dealloc` removes. A missing entry on dealloc triggers `debug_assert!` failure with "double free" diagnostic.

The mutex uses poison recovery (`unwrap_or_else(|e| e.into_inner())`) to handle the case where a `#[should_panic]` test panics while holding the lock. Stale entries from panicked tests are harmless.

### Test Strategy

Global counters are shared across Rust's parallel test threads. Tests use delta-based assertions (snapshot before, check `>=` delta after) rather than absolute values to avoid races. Header field checks (alloc_size, rc values) are deterministic and checked with exact assertions.

## RC Infrastructure (`rc.rs`)

### Design Decision: Inline RC, Not Extern Functions

The sketch prototype used `cranelisp_dec_guarded` extern functions for RC operations. The reimplementation emits RC inc/dec **inline** as Cranelift `atomic_rmw` instructions. This is specified in `design/arch/interfaces.md` §"Reference Counting Operations".

**Rationale**: Inline atomic operations avoid function call overhead on every RC change — the most frequent heap operation. The backend emits a small sequence (atomic_rmw, compare, conditional branch to dealloc path) directly in the compiled function body.

The runtime's role in RC is limited to:
1. **Trace logging** — `rc_trace(op, ptr, rc)` logs alloc/free/inc/dec events to stderr when `CRANELISP_RC_TRACE=1`
2. **Underflow check** — `rc_underflow_check(ptr, old_rc)` (JIT: `runtime/rc_underflow_check`) is called from JIT code when the backend detects an RC value ≤ 0 after decrement (debug builds only)

### Trace Logging

`CRANELISP_RC_TRACE=1` environment variable enables RC trace output. Checked once at process start via `LazyLock<AtomicBool>`. All trace output is gated behind `#[cfg(debug_assertions)]` — zero cost in release builds.

Format: `[RC]  alloc 0x1234 rc=1`

### Underflow Check

`extern "C-unwind"` (not `extern "C"`) to allow panic unwinding through the FFI boundary. This is critical: `extern "C"` with a panic causes immediate abort, preventing test harness recovery. The function uses `debug_assert!` so it's a no-op in release builds.

## String Runtime (`string.rs`)

### HeapString Layout

```
Offset  Size  Field
─────── ───── ─────────────────
0       8     alloc_size (i64) — from HeapHeader
8       8     rc (i64)         — from HeapHeader
16      8     len (i64)        — byte length
24+     var   bytes            — UTF-8 data
```

`HeapString` is a `#[repr(C)]` struct with `HeapHeader` + `len` field. Byte data follows immediately at offset 24. The struct itself doesn't include a bytes field (dynamic length); access is via `base_ptr.byte_add(DATA_OFFSET)`.

### Opacity Principle

**The backend treats strings as opaque heap pointers.** All string content access goes through the extern functions in this module. The backend never reads string bytes directly — it emits calls to the JIT symbols `str-concat`, `str-eq`, etc.

This containment enables future representation changes (e.g., rope strings per NFR C.2.3) as runtime-only modifications, with no backend changes.

### Extern Functions

| Rust function | JIT symbol | Signature | Purpose |
|---------------|------------|-----------|---------|
| `heap_alloc_string` | `runtime/alloc_string` | `(*const u8, i64) -> i64` | Allocate from raw bytes |
| `str_concat` | `str-concat` | `(i64, i64) -> i64` | Concatenate two strings (new allocation) |
| `str_eq` | `str-eq` | `(i64, i64) -> i64` | Byte-wise equality (returns 0/1) |
| `str_len` | `str-len` | `(i64) -> i64` | Byte length |
| `string_identity` | `string-identity` | `(i64) -> i64` | Increment RC, return same pointer |
| `string_read` | `runtime/string_read` | `(i64, *mut *const u8, *mut i64) -> ()` | Read bytes for display |

`string_identity` (JIT: `string-identity`) is used for String-to-String "conversion" — increments RC and returns the same pointer, creating a shared reference.

`string_read` (JIT: `runtime/string_read`) is NOT called from JIT code. It's used by the binary crate's value formatter to display string values at the REPL.

### Rejected: String Interning

String interning (deduplicating identical strings) was considered but rejected for Ring 1. It adds complexity (intern table, weak references, concurrent access) for uncertain benefit. If profiling shows string allocation as a bottleneck, interning can be added as a runtime-only change thanks to the opacity principle.

## Type Conversion Primitives (`primitives/`)

Three modules provide type-to-string conversion for REPL display:

| Rust function | JIT symbol | Input | Output |
|---------------|------------|-------|--------|
| `int_to_string` | `int-to-string` | `i64` | HeapString with decimal representation |
| `float_to_string` | `float-to-string` | `i64` (IEEE 754 bits) | HeapString (ensures "3.0" not "3") |
| `bool_to_string` | `bool-to-string` | `i64` (0/nonzero) | HeapString "true"/"false" |
| `parse_int` | `parse-int` | `i64` (HeapString ptr) | Option ADT: 0 for None, heap `[header\|tag=1\|n]` for Some(n) |

### Float Bit Pattern Convention

Floats are passed as `i64` containing the IEEE 754 double bit pattern (`f64::to_bits() as i64`). The runtime reinterprets via `f64::from_bits(f_bits as u64)`. This avoids floating-point register ABI differences in the extern "C" calling convention.

### parse_int Option ADT

`parse_int` returns the Option type as a heap ADT directly, without depending on the type system. This mirrors how the backend will emit Option values:
- **None**: bare i64 tag 0 (no heap allocation)
- **Some(n)**: heap-allocated `[HeapHeader | tag=1 | n]` (16-byte payload)

## Module Structure

```
cranelisp-runtime/src/
├── lib.rs          — module declarations + re-exports
├── alloc.rs        — heap allocator, dealloc, tracking
├── rc.rs           — RC trace logging, underflow check
├── string.rs       — HeapString layout and operations
├── panic.rs        — runtime_panic (match exhaustiveness)
└── primitives/
    ├── mod.rs      — submodule declarations
    ├── int.rs      — int_to_string, parse_int
    ├── float.rs    — float_to_string
    └── bool.rs     — bool_to_string
```

`lib.rs` re-exports all `extern "C"` functions at crate root so the backend can register them with the JIT builder by function pointer via `JITBuilder::symbol()`. Each function is registered under its JIT symbol name — `runtime/`-prefixed for infrastructure, kebab-case spec names for user-visible primitives (see §"JIT Symbol Registration" below). It also re-exports public Rust API items (`alloc_with_rc`, `bytes_current`, `read_string_as_str`, etc.) for use by the binary crate and integration tests.

## JIT Symbol Registration

The runtime registers all extern functions with the JIT using the naming convention from `src/CLAUDE.md` §"JIT Symbol Names". The complete mapping:

| Rust function | JIT symbol | Category |
|---------------|------------|----------|
| `heap_alloc` | `runtime/alloc` | Runtime infrastructure |
| `heap_dealloc` | `runtime/dealloc` | Runtime infrastructure |
| `runtime_panic` | `runtime/panic` | Runtime infrastructure |
| `rc_underflow_check` | `runtime/rc_underflow_check` | Runtime infrastructure |
| `heap_alloc_string` | `runtime/alloc_string` | Runtime infrastructure |
| `string_read` | `runtime/string_read` | Runtime infrastructure |
| `str_concat` | `str-concat` | Extern primitive |
| `str_eq` | `str-eq` | Extern primitive |
| `str_len` | `str-len` | Extern primitive |
| `string_identity` | `string-identity` | Extern primitive |
| `int_to_string` | `int-to-string` | Extern primitive |
| `float_to_string` | `float-to-string` | Extern primitive |
| `bool_to_string` | `bool-to-string` | Extern primitive |
| `parse_int` | `parse-int` | Extern primitive |

**Runtime infrastructure** (`runtime/` prefix) is internal — never callable from user code. **Extern primitives** (kebab-case) are user-visible via the `primitives` module.

## Ring Evolution

### Ring 0 (complete)
- `runtime_panic` (JIT: `runtime/panic`) — match exhaustiveness failure handler

### Ring 1 (current)
- Heap allocator with base-pointer convention
- RC trace logging and underflow check
- Full string runtime (7 extern functions)
- Type conversion primitives (int, float, bool)

### Ring 2 (planned)
- ADT construction helpers (if needed beyond backend inline emission)
- Closure environment helpers (if needed)

### Ring 4 (planned)
- Platform DLL loading and dispatch
- IO effect execution infrastructure
