# Facade spec — `crates/cranelisp-intrinsics/`

**Bounded context citation.** Backend-emitted-call targets — runtime support code with stable ABI contracts called by JIT-emitted code. NOT callable from user code; ABI tightly coupled to backend's codegen choices. Backend-driven evolution. See `bounded-contexts.md` §4b — Intrinsics.

This spec is **target-stating**. Drift detection between as-designed and as-built is the job of `cargo-public-api` (M4-pending) and `/review`'s per-PR audit, not this document.

`cranelisp-intrinsics` is one of the two crates produced by Decision 43's split of `cranelisp-runtime`. The other is `cranelisp-primitives` (`facades/primitives.md`). Intrinsics live in their own crate so that:

- Backend depends on `cranelisp-intrinsics` (for emitted-symbol declarations) WITHOUT pulling in user-callable primitives.
- The deployment artefact for `--link` is self-evident: every program needs intrinsics; `cranelisp-primitives` is needed only for programs that reference user-callable conversions / operators-as-values.
- Evolution drivers separate cleanly: changing how RC dec works is an intrinsics + backend co-design (backend-driven evolution), not a spec change.

---

## Public surface (as-designed)

The intrinsics crate's public surface is exposed primarily as **fn pointers registered with the JIT** (via `JITBuilder::symbol` — `int`'s session init resolves names to fn ptrs and registers them) and as **named extern symbols in `.o` files** (resolved at link time by the system linker against the `cranelisp-intrinsics` archive). Backend emits Cranelift IR that calls these by string name; nothing in the symbol table; nothing in any GOT.

### Heap allocator (Decision-11 base-pointer convention)

```rust
#[no_mangle] pub extern "C" fn cranelisp_alloc(payload_size: i64) -> i64;          // alloc total_size = payload_size + 16; returns base pointer
#[no_mangle] pub extern "C" fn heap_alloc_payload(payload_size: i64) -> i64;       // alias — same semantics, distinct name for codegen clarity
#[no_mangle] pub extern "C" fn heap_dealloc(ptr: i64);                             // reads total_size from ptr+0; frees the full allocation

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

### RC primitives (debug-only — backend emits inc/dec inline)

```rust
#[no_mangle] pub extern "C-unwind" fn rc_underflow_check(ptr: i64, old_rc: i64) -> i64;

// Per Decision 13 — these are the consuming-convention helpers backend may emit
// when a heap value is consumed by a callee that owns it (vs inlining the dec).
#[no_mangle] pub extern "C" fn rc_inc(ptr: i64);                                   // atomic_rmw add 1, Ordering::Relaxed
#[no_mangle] pub extern "C" fn rc_dec(ptr: i64);                                   // atomic_rmw sub 1, Ordering::Release; on old_rc==1, Acquire fence + drop glue
```

Backend may emit `atomic_rmw add 1` (Ordering::Relaxed) for inc and `atomic_rmw sub 1` (Ordering::Release) for dec directly in CLIF, or call `rc_inc` / `rc_dec` — both shapes coexist as the codegen-choice allows. `rc_underflow_check` is invoked only in debug builds when an inc would overflow or a dec would underflow.

```rust
pub fn is_rc_trace_enabled() -> bool;                                              // observability — checked by backend at codegen time
```

### Drop glue (per-type — emitted by backend, declared in intrinsics per Decision 11)

Drop glue is BACKEND-EMITTED — one fn per type/closure/Vec layout. Intrinsics does not provide drop-glue functions; it provides only the underlying `heap_dealloc` and the consume helpers. Closures carry an embedded `drop_glue_ptr` at offset 24 per Decision 11 — `[header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]`, `CAPTURES_START = 32`.

```rust
#[no_mangle] pub extern "C" fn consume_shallow(ptr: i64);                          // single-node dec for IO trampoline + general use
pub fn consume_io_tree(ptr: i64);                                                  // recursive RC dec walk over an IO tree (see Decision 29)
#[no_mangle] pub extern "C" fn dec_shallow_io(ptr: i64);                           // distinct from transitive consume — see IO trampoline below
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

### String primitives (allocator + reader; user-visible string ops route through primitives)

Backend never reads or writes string bytes per Decision 12; allocation + read are intrinsics. User-callable conversions (`int_to_string`, `parse_int`, etc.) live in `cranelisp-primitives` and use these intrinsic helpers under the hood.

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

`HeapString` layout is intrinsics-owned per Decision 12 — backend never reads or writes string bytes; all string ops route through these extern functions. Enables a future rope upgrade as an intrinsics-only change. `cranelisp-platform`'s `CLString` (`facades/platform.md` §"Wrapper types") is a `#[repr(transparent)]` `i64` newtype carrying a `*const HeapString` for cross-DLL boundary use; platform DLL code reaches the bytes via `CLString::as_str()` which calls back through this crate's `read_string_as_str`.

### Sexp marshaling (for macro args + quote_sexp)

```rust
#[no_mangle] pub extern "C" fn sconcat(a: i64, b: i64) -> i64;
#[no_mangle] pub extern "C" fn quote_sexp(sexp_ptr: i64) -> i64;
```

Use the marshaling tags from `cranelisp-types` (`TAG_SEXP_INT`, `TAG_SCONS`, etc.) to interpret heap-allocated Sexp values.

### IO trampoline (Decision 29)

```rust
#[no_mangle] pub extern "C" fn cranelisp_run_io(io_root_ptr: i64) -> i64;          // outer entry — consuming convention, calls run_io_trampoline internally
pub fn run_io_trampoline(io_ptr: i64) -> i64;                                      // Rust-callable internal walker
#[no_mangle] pub extern "C" fn io_run(io_root_ptr: i64) -> i64;                    // alternative entry — same semantics, distinct name for codegen clarity
```

Walks the IO tree node-by-node, dispatching `Effect` nodes through `cranelisp_platform::HostContext` (see `facades/platform.md`). `Pure` returns the inner value; `Bind` reduces lhs then continues with the continuation closure; `Par` fork-joins via rayon. Each outer node allocation is consumed via `dec_shallow_io` (single-node dec — see Decision 29) as the walker advances.

The IO trampoline is the intrinsics' bridge into platform — `int`'s `Sess::trampoline(code_ptr, expected_type)` calls into JIT'd user code which builds an IO tree, then calls `cranelisp_run_io(io_root_ptr)` to reduce it.

The IO node tags consumed by the trampoline (`IO_TAG_PURE`, `IO_TAG_EFFECT`, `IO_TAG_BIND`, `IO_TAG_PAR`) are public consts on `cranelisp-platform` — see `facades/platform.md` §"Public consts". Intrinsics consumes them; the constants are NOT duplicated here.

### IO observation (extension point per Decision 40)

NOT diagnostics — an extension point in the same shape as `register_alloc_callback`. Intrinsics defines the observation taxonomy and a registration API; `int` implements all observer state. The IO trampoline emits events via the registered observer (with a relaxed-load null check; no-op if unregistered). All observer state — ring buffers, panic hook, formatter, dump, merge-sort — lives in `int`'s `src/io_trace/`. Production batch (`--link`, non-trace `--run`) does not register and pays one relaxed null-check load per call site (one conditional branch after optimisation).

```rust
#[non_exhaustive]
pub enum IoEventTag { TrampolineEnter, PureStep, PlatformEffect, ContPop, /* … */ }

#[non_exhaustive]
pub struct IoEvent { /* per-variant payload — same variants as today's IoTracePayload, moved here */ }

pub type IoObserver = fn(IoEventTag, &IoEvent);

/// Replaces the current observer atomically. Thread-safe from any thread;
/// last write wins under happens-before ordering. Pass `None` to unregister.
/// Subsequent IO events emitted by the trampoline are delivered to the
/// observer most recently registered (in happens-before order). Callers
/// do not reason about Acquire/Release — the API commits to the contract.
pub fn register_io_observer(observer: Option<IoObserver>);
pub fn trace_anchor() -> &'static Instant;     // shared monotonic anchor (kept here so int's scheduler trace and the IO trace use the same origin)
```

`IoEventTag` and `IoEvent` move with the API into intrinsics — they ARE the callback's type contract; they belong where the trampoline lives. Naming parallels the GotObserver pattern in `facades/backend.md` (`GotEventTag` + `GotEvent` + `GotObserver`). `int`'s session startup (REPL mode or `--run` with `CRANELISP_IO_TRACE=1`) calls `intrinsics::register_io_observer(Some(int::io_trace::record))`. Decision 40 closes the runtime BC drift by relocation: the orchestration of `(trace ...)` (GOT-swap, wrapper machinery, frame stack, slash-command handlers) and the consumer-side observer state both live in `int`; intrinsics keeps only this ~50-line extension-point API.

### IVar primitives (lenient evaluation per spec §12.4.3)

```rust
#[no_mangle] pub extern "C" fn ivar_create() -> i64;                               // alloc empty IVar cell — returns base ptr
#[no_mangle] pub extern "C" fn ivar_spark(ivar: i64, thunk: i64);                  // schedule thunk to fill the IVar (rayon spawn)
#[no_mangle] pub extern "C" fn ivar_force(ivar: i64) -> i64;                       // block until filled — return value
```

Backend emits `ivar_create` + `ivar_spark` for `let` bindings whose RHS is independent and expensive (cost heuristic per spec §12.4.3); `ivar_force` is emitted at use sites.

### Panic helper (called from match exhaustiveness, intrinsic failures)

Sentinel-pattern panic: Cranelift cannot unwind through JIT frames, so `runtime_panic` does NOT `!`-return. It stores a message sentinel in a thread-local; the host MUST call `take_runtime_error()` after every JIT entry to check for a pending panic and surface it as the program's exit signal. Per spec §12.7.2 — bare message is the contract; no enrichment per substance-scoping §2.10 (runtime panics are being driven to zero, not enriched).

```rust
#[no_mangle]
pub extern "C" fn runtime_panic(msg_ptr: *const u8, msg_len: usize);

pub fn take_runtime_error() -> Option<String>;
```

### Public consts

None. (The IO node-tag consts `IO_TAG_PURE` / `IO_TAG_EFFECT` / `IO_TAG_BIND` / `IO_TAG_PAR` live on `cranelisp-platform` — see `facades/platform.md` §"Public consts". Intrinsics consumes them.)

---

## Types originated here

Per Principle 15 — the following are intrinsics-originated and live in `cranelisp-intrinsics`:

- `HeapString`
- `IoEvent`, `IoEventTag`, `IoObserver`, `register_io_observer` (the IO observation contract per Decision 40)

`IoTraceFlushGuard` and `SchedulerTraceFlushGuard` are NOT intrinsics surface — they are `int`'s consumer-side machinery (RAII guards over the ring buffers in `src/io_trace/` and `src/scheduler_trace/`). Intrinsics exposes only the `IoObserver` extension point per Decision 40; what consumers do with observed events (ring buffers, flush guards, panic hooks, dump formatters) is consumer-specific machinery owned by `int`. See `facades/int.md` for the guards' public surface.

The multi-consumer types intrinsics depends on (`Span`, `CranelispError`, `ErrorLocation`, marshaling tags `TAG_SNIL`/`TAG_SCONS`/etc., `SchedulingClass`) live in `cranelisp-types`. Consumers (backend codegen names them in emitted code; `int` reads them when interpreting marshaled values) import directly.

No re-exports of `cranelisp-types` items per Principle 15.

---

## Consumed surface

The intrinsics crate imports from:

- **`cranelisp-types`** — `Symbol`, `ErrorLocation`, `Span`, `CranelispError`, marshaling tags (`TAG_SNIL`, `TAG_SCONS`, `TAG_SEXP_*`), `SchedulingClass`. No types-crate trait implementations.
- **`cranelisp-platform`** — the `IO_TAG_*` consts (`IO_TAG_PURE`, `IO_TAG_EFFECT`, `IO_TAG_BIND`, `IO_TAG_PAR`) consumed by the IO trampoline; `HostContext` for the IO trampoline's Effect dispatch path. Per `bounded-contexts.md` §4b + §5 — intrinsics is paired with platform; the IO trampoline reaches platform fns through the per-entry `fn_ptr` on `ModuleEntry::Def` (per Decision 26, S66-amended — `fn_ptr` is the unified per-entry call-address field, replacing the previously-named `platform_fn_ptr`) rather than through a centralised dispatch wrapper. See `facades/platform.md` §"Host context" — no `HostContext::dispatch` is exposed; the per-entry pointer IS the dispatch path.

Intrinsics imports from no other workspace crate — not `cranelisp-frontend`, not `cranelisp-typecheck`, not `cranelisp-backend`, not `cranelisp-primitives`. (Backend names intrinsics extern functions by string at codegen time — relocation-time dependency, not a Rust-source dependency.)

---

## Sealed traits

None implemented. Intrinsics does not implement traits from `cranelisp-types`.

---

## `#[non_exhaustive]` DTOs

`HeapString`, `IoEvent`, `IoEventTag` are `#[non_exhaustive]`.

No `#[repr(C)]` layout types currently surface from this crate — string and Sexp marshaling cross the FFI boundary as opaque `i64` tags + extern functions, not as layout-stable structs. If a future intrinsics extension publishes a `#[repr(C)]` DTO, Principle 14 applies: omit `#[non_exhaustive]` and govern evolution via an explicit version bump.

---

## Bounded-context invariants

These hold across sprints — the contract `cranelisp-intrinsics` makes with the rest of the workspace:

1. **Backend-emitted-call targets only.** Per Decision 43 — every fn in this crate is called by JIT-emitted code or by the IO trampoline; nothing here is callable from user code. Not in any symbol table; not in any GOT. Adding an intrinsic is a backend + intrinsics co-design; deleting one requires backend co-evolution.

2. **Representation containment.** Per `src/CLAUDE.md` "Heap Access" — only `alloc.rs`, `string.rs`, `vec.rs` may import layout constants (`HEAP_HEADER_SIZE`, field offsets). Backend reads the layout through the named extern functions, never by hard-coding offsets.

3. **Atomic RC discipline (Decision 13).** RC inc/dec emit `atomic_rmw` at all rings, even Ring 1 single-threaded. Acquire fence on the free path before drop_glue reads object fields. Avoids an ABI break when concurrency arrives at Ring 4.

4. **Strings opaque to backend (Decision 12).** `HeapString` layout is intrinsics-owned. All string operations go through extern functions. Enables future rope upgrade.

5. **Embedded `drop_glue_ptr` in closures (Decision 11).** Closures carry their drop fn at offset 24 — `[header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]`. The drop glue function is per-lambda generated by backend; null for closures with no heap captures. Cross-module closures self-describe; no side-table lookup required.

6. **Consuming convention at extern boundary (Decision 24).** Every `#[no_mangle]` extern function MUST consume its heap-typed arguments — dec any heap arg it does not return. Internal Rust helpers may use any local convention; the extern boundary enforces consuming so backend's call sites can emit uniformly.

7. **IO trampoline shallow dec (Decision 29).** `cranelisp_run_io` reduces IO trees node-by-node, consuming each outer allocation via `dec_shallow_io` — a distinct primitive from transitive `consume_io_tree` because field pointers are already re-owned by other holders during the walk.

8. **No state across sessions.** Stats accessors (`alloc_count`, etc.) are process-global — `int`'s `reset_counts` should be called at session start in test contexts. Production runs do not call `reset_counts`.

9. **Backend-driven evolution.** Intrinsics changes are typically driven by backend codegen choices (a new RC inlining strategy, a new IO node, a new trampoline shape). The crate does not accrete intrinsics for spec convenience; spec-defined operations live in `cranelisp-primitives`. The categorical line is the load-bearing distinction Decision 43 formalised.

---

## Cross-references

- `bounded-contexts.md` §4b — Intrinsics BC (full statement)
- `decisions/0043-runtime-split-into-primitives-intrinsics.md` — the split decision
- `decisions/0040-runtime-trace-io-trace-relocate-to-int.md` — IoObserver callback contract; the registration API resides here post-D43
- `decisions/0011-embedded-drop-glue-ptr-in-closures.md` — drop-glue layout
- `decisions/0013-atomic-rc-from-ring-1.md` (legacy) — atomic RC discipline (subsumed into BC invariant 3 above)
- `facades/primitives.md` — sibling crate from the same split
- `facades/backend.md` §"Consumed surface" — backend names intrinsics by string at codegen
- `facades/int.md` §"Consumed surface" — int registers intrinsic fn ptrs with the JIT at session init
- `facades/platform.md` §"Public consts" — `IO_TAG_*` consts intrinsics consumes
- `principles.md` Principle 1 (decoupling), Principle 7 (no duplicate addressable forms), Principle 14 (FFI layout discipline), Principle 15 (facade types live with behaviour)
