# Facade spec — `crates/cranelisp-runtime/`

**Bounded context citation.** Drop glue, intrinsic helpers, and RC primitives consumed by backend-emitted code. Implementation-paired with backend. See `bounded-contexts.md` §4 — Runtime.

This spec is **target-stating**. Drift detection between as-designed and as-built is the job of `cargo-public-api` (M4-pending) and `/review`'s per-PR audit, not this document.

---

## Public surface (as-designed)

The runtime crate's public surface is unusual: it's exposed primarily as **fn pointers registered with the JIT** (via `JITBuilder::symbol`) and as **named extern symbols in `.o` files** (resolved at link time by the system linker). Backend emits Cranelift IR that calls these by string name; `int` registers the corresponding fn pointers per session.

### Heap allocator (Decision-11 base-pointer convention)

```rust
#[no_mangle]
pub extern "C" fn heap_alloc(payload_size: i64) -> i64;             // alloc total_size = payload_size + 16; returns base pointer (offset 0)
#[no_mangle]
pub extern "C" fn heap_alloc_payload(payload_size: i64) -> i64;     // alias — same semantics, distinct name for codegen clarity
#[no_mangle]
pub extern "C" fn heap_dealloc(ptr: i64);                           // reads total_size from ptr+0; frees the full allocation

// Rust-callable accessor (used by tests + observability)
pub fn alloc_with_rc(payload_size: usize) -> *mut u8;

// Stats accessors (read by `/mem` slash command in int)
pub fn alloc_count() -> usize;
pub fn dealloc_count() -> usize;
pub fn bytes_allocated() -> usize;
pub fn bytes_current() -> usize;
pub fn bytes_peak() -> usize;
pub fn reset_counts();
pub fn is_live(ptr: usize) -> bool;
```

Layout (per `src/CLAUDE.md` "Heap Access" + Decision 11):
```
offset 0  | total_size: u64           (used by heap_dealloc)
offset 8  | rc: AtomicI64             (atomic_rmw target — written inline by backend)
offset 16 | payload bytes...          (data)
```

### RC primitive (debug-only — backend emits inc/dec inline)

```rust
#[no_mangle]
pub extern "C-unwind" fn rc_underflow_check(ptr: i64, old_rc: i64) -> i64;
```

Backend emits `atomic_rmw add 1` (Ordering::Relaxed) for inc and `atomic_rmw sub 1` (Ordering::Release) for dec directly in CLIF — NO runtime call. `rc_underflow_check` is invoked only in debug builds when an inc would overflow or a dec would underflow.

Atomic from Ring 1 per Decision 13 — even in single-threaded code, RC ops use `atomic_rmw` to avoid an ABI break when concurrency arrives. A separate Acquire fence is emitted on the free path (when `old_rc == 1`) before reading object fields for drop glue.

```rust
pub fn is_rc_trace_enabled() -> bool;                                // observability — checked by backend at codegen time
```

### Drop glue (per-type — emitted by backend, declared in runtime per Decision 11)

Drop glue is BACKEND-EMITTED — one fn per type/closure/Vec layout. The runtime does not provide drop-glue functions; it only provides the underlying `heap_dealloc`. Closures carry an embedded `drop_glue_ptr` at offset 24 per Decision 11 — `[header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]`, `CAPTURES_START = 32`.

The runtime exposes a transitive consume helper for IO-tree walks:

```rust
pub fn consume_io_tree(ptr: i64);                                    // recursive RC dec walk over an IO tree (see Decision 29)
```

### Vec primitives (Cow-checked per `data-structures.md`)

```rust
#[no_mangle] pub extern "C" fn vec_new(elem_size: i64) -> i64;
#[no_mangle] pub extern "C" fn vec_len(vec_ptr: i64) -> i64;
#[no_mangle] pub extern "C" fn vec_set_copy(vec_ptr: i64, idx: i64, val: i64) -> i64;     // last-use → in place; else copy
#[no_mangle] pub extern "C" fn vec_push_copy(vec_ptr: i64, val: i64) -> i64;              // last-use + capacity → in place; else copy
#[no_mangle] pub extern "C" fn vec_push_grow(vec_ptr: i64, val: i64) -> i64;              // capacity exceeded → realloc + copy
#[no_mangle] pub extern "C" fn vec_drop(vec_ptr: i64);                                    // recursive dec on element refs + dealloc
```

### String primitives

```rust
#[no_mangle] pub extern "C" fn heap_alloc_string(bytes: i64, len: i64) -> i64;
#[no_mangle] pub extern "C" fn string_read(ptr: i64, idx: i64) -> i64;

// Rust-callable accessors
pub fn alloc_string(s: &str) -> *mut u8;
pub fn read_string_as_str(ptr: *const u8) -> &'static str;

#[non_exhaustive]
pub struct HeapString {
    pub len: u64,
    /* opaque bytes follow */
}
```

`HeapString` layout is owned by runtime per Decision 12 — backend never reads or writes string bytes; all string ops route through these extern functions. Enables a future rope upgrade as a runtime-only change.

### Primitive type conversions

```rust
#[no_mangle] pub extern "C" fn int_to_string(n: i64) -> i64;
#[no_mangle] pub extern "C" fn parse_int(s: i64) -> i64;
#[no_mangle] pub extern "C" fn float_to_string(f: f64) -> i64;
#[no_mangle] pub extern "C" fn bool_to_string(b: i64) -> i64;
// (plus parse_float, int comparison primitives, etc. per primitives/int.rs and primitives/float.rs and primitives/bool.rs)
```

### Sexp marshaling (for macro args + quote_sexp)

```rust
#[no_mangle] pub extern "C" fn sconcat(a: i64, b: i64) -> i64;
#[no_mangle] pub extern "C" fn quote_sexp(sexp_ptr: i64) -> i64;
```

Use the marshaling tags from `cranelisp-types` (`TAG_SEXP_INT`, `TAG_SCONS`, etc.) to interpret heap-allocated Sexp values.

### IO trampoline (Decision 29)

```rust
#[no_mangle]
pub extern "C" fn cranelisp_run_io(io_root_ptr: i64) -> i64;        // outer entry — consuming convention, calls run_io_trampoline internally

pub fn run_io_trampoline(io_ptr: i64) -> i64;                        // Rust-callable internal walker (non-consuming on the Rust side)
```

Walks the IO tree node-by-node, dispatching `Effect` nodes through `cranelisp_platform::HostContext` (see `facades/platform.md`). `Pure` returns the inner value; `Bind` reduces lhs then continues with the continuation closure; `Par` fork-joins via rayon. Each outer node allocation is consumed via `rc::dec_shallow_io` (single-node dec — see Decision 29) as the walker advances.

The IO trampoline is the runtime's bridge into platform — `int`'s `Sess::trampoline(code_ptr, expected_type)` calls into JIT'd user code which builds an IO tree, then calls `cranelisp_run_io(io_root_ptr)` to reduce it.

### IO observation (extension point per Decision 40)

NOT diagnostics — an extension point in the same shape as `register_alloc_callback`. Runtime defines the observation taxonomy and a registration API; `int` implements all observer state. The IO trampoline emits events via the registered observer (with a relaxed-load null check; no-op if unregistered). All observer state — ring buffers, panic hook, formatter, dump, merge-sort — lives in `int`'s `src/io_trace/`. Production batch (`--link`, non-trace `--run`) does not register and pays one relaxed null-check load per call site (one conditional branch after optimisation).

```rust
#[non_exhaustive]
pub enum IoEventTag { TrampolineEnter, PureStep, PlatformEffect, ContPop, /* … */ }
#[non_exhaustive]
pub struct IoEvent { /* per-variant payload — same variants as today's IoTracePayload, moved here */ }
pub type IoObserver = fn(IoEventTag, &IoEvent);

pub fn register_io_observer(observer: Option<IoObserver>);
pub fn trace_anchor() -> &'static Instant;     // shared monotonic anchor (kept here so int's scheduler trace and the IO trace use the same origin)
```

`IoEventTag` and `IoEvent` move with the API to runtime — they ARE the callback's type contract; they belong where the trampoline lives. Naming parallels the GotObserver pattern in `facades/backend.md` (`GotEventTag` + `GotEvent` + `GotObserver`); existing implementation `io_trace::IoTraceTag`/`IoTracePayload` rename to `IoEventTag`/`IoEvent` as part of FIXME 0103's relocation work. `int`'s session startup (REPL mode or `--run` with `CRANELISP_IO_TRACE=1`) calls `runtime::register_io_observer(Some(int::io_trace::record))`. Decision 40 closes the runtime BC drift by relocation: the orchestration of `(trace ...)` (GOT-swap, wrapper machinery, frame stack, slash-command handlers) and the consumer-side observer state both live in `int`; runtime keeps only this ~50-line extension-point API.

### IVar primitives (lenient evaluation per spec §12.4.3)

```rust
#[no_mangle] pub extern "C" fn ivar_create() -> i64;                 // alloc empty IVar cell — returns base ptr
#[no_mangle] pub extern "C" fn ivar_spark(ivar: i64, thunk: i64);    // schedule thunk to fill the IVar (rayon spawn)
#[no_mangle] pub extern "C" fn ivar_force(ivar: i64) -> i64;         // block until filled — return value
```

Backend emits `ivar_create` + `ivar_spark` for `let` bindings whose RHS is independent and expensive (cost heuristic per spec §12.4.3); `ivar_force` is emitted at use sites.

### Panic helper (called from match exhaustiveness, intrinsic failures)

Sentinel-pattern panic: Cranelift cannot unwind through JIT frames, so `runtime_panic` does NOT `!`-return. It stores a message sentinel in a thread-local; the host MUST call `take_runtime_error()` after every JIT entry to check for a pending panic and surface it as the program's exit signal. Per spec §12.7.2 — bare message is the contract; no enrichment per §2.10 (runtime panics are being driven to zero, not enriched).

```rust
#[no_mangle]
pub extern "C" fn runtime_panic(msg_ptr: *const u8, msg_len: usize);

pub fn take_runtime_error() -> Option<String>;
```

### Public consts

None.

---

## Types originated here

Per Principle 15 — the following are runtime-originated and live in `cranelisp-runtime`:

- `HeapString`
- `IoEvent`, `IoObserver`, `register_io_observer` (the IO observation contract per Decision 40)
- `IoTraceFlushGuard`, `SchedulerTraceFlushGuard`

The multi-consumer types runtime depends on (`Span`, `CranelispError`, marshaling tags `TAG_SNIL`/`TAG_SCONS`/etc., `SchedulingClass`) live in `cranelisp-types`. Consumers (backend codegen names them in emitted code; `int` reads them when interpreting marshaled values) import directly.

No re-exports of `cranelisp-types` items per Principle 15.

---

## Consumed surface

The runtime crate imports from:

- **`cranelisp-types`** — `Span`, `CranelispError`, marshaling tags, `SchedulingClass`. No types-crate trait implementations.
- **`cranelisp-platform`** — `HostContext` for the IO trampoline's Effect dispatch path. Per `bounded-contexts.md` §4 — runtime is paired with platform; the IO trampoline calls `HostContext::dispatch` to invoke platform fns.

The runtime imports from no other workspace crate — not `cranelisp-frontend`, not `cranelisp-typecheck`, not `cranelisp-backend`. (Backend names runtime extern functions by string at codegen time — relocation-time dependency, not a Rust-source dependency.)

---

## Sealed traits

None implemented. Runtime does not implement traits from `cranelisp-types`.

---

## `#[non_exhaustive]` DTOs

`HeapString`, `IoTraceFlushGuard`, `SchedulerTraceFlushGuard` are `#[non_exhaustive]`.

No `#[repr(C)]` layout types currently surface from this crate — string and Sexp marshaling cross the FFI boundary as opaque `i64` tags + extern functions, not as layout-stable structs. If a future runtime extension publishes a `#[repr(C)]` DTO, Principle 14 applies: omit `#[non_exhaustive]` and govern evolution via an explicit version bump.

---

## Bounded-context invariants

These hold across sprints — the contract `cranelisp-runtime` makes with the rest of the workspace:

1. **Representation containment.** Per `src/CLAUDE.md` "Heap Access" — only `alloc.rs`, `string.rs`, `vec.rs` may import layout constants (`HEAP_HEADER_SIZE`, field offsets). Backend reads the layout through the named extern functions, never by hard-coding offsets.

2. **Atomic RC discipline (Decision 13).** RC inc/dec emit `atomic_rmw` at all rings, even Ring 1 single-threaded. Acquire fence on the free path before drop_glue reads object fields. Avoids an ABI break when concurrency arrives at Ring 4.

3. **Strings opaque to backend (Decision 12).** `HeapString` layout is runtime-owned. All string operations go through extern functions. Enables future rope upgrade.

4. **Embedded `drop_glue_ptr` in closures (Decision 11).** Closures carry their drop fn at offset 24 — `[header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]`. The drop glue function is per-lambda generated by backend; null for closures with no heap captures. Cross-module closures self-describe; no side-table lookup required.

5. **Consuming convention at extern boundary (Decision 24).** Every `#[no_mangle]` extern function MUST consume its heap-typed arguments — dec any heap arg it does not return. Internal Rust helpers may use any local convention; the extern boundary enforces consuming so backend's call sites can emit uniformly.

6. **IO trampoline shallow dec (Decision 29).** `cranelisp_run_io` reduces IO trees node-by-node, consuming each outer allocation via `rc::dec_shallow_io` — a distinct primitive from transitive `consume_io_tree` because field pointers are already re-owned by other holders during the walk.

7. **No state across sessions.** Stats accessors (`alloc_count`, etc.) are process-global — `int`'s `reset_counts` should be called at session start in test contexts. Production runs do not call `reset_counts`.
