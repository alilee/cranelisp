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

**Rust consumers (not only backend).** A second category of consumer reaches intrinsics by **Rust path**, not by emitted-call relocation: `cranelisp-primitives` Rust-depends on `cranelisp-intrinsics` and calls its allocator (`alloc_string`, `alloc_with_rc`, `vec_new`), its drop/RC/panic helpers (`consume_sexp`, `consume_slist`, `consume_shallow`, `runtime_panic`), and reads its **heap-layout-ABI consts** (`HeapString::{LEN_OFFSET, DATA_OFFSET}`, `vec_runtime::{LEN_OFFSET, CAP_OFFSET, DATA_PTR_OFFSET}`) — see FIXME 0245 + `facades/primitives.md` §"Consumed surface" for the pinned contract. This is the only in-tree Rust consumer of intrinsics; the framing that "backend is the consumer" (singular) is corrected here. Because primitives is a named Rust consumer, the heap-object layout is treated as intrinsics' **blessed, stable public ABI** (the consts in §"Heap allocator", §"String allocator + reader", §"Vec runtime"), governed by the baseline-diff discipline.

### `JITBuilder::symbol(name, ptr)` narrows to intrinsics-only — post-S68

**Post-S68 / Decision 0048**, the `JITBuilder::symbol(name, ptr)` direct-registration dispatch path is reserved **exclusively for intrinsics**. Intrinsics are runtime infrastructure — RC inc/dec underflow check, `heap_alloc` / `heap_dealloc`, `runtime_panic`, per-type drop helpers, IO trampoline (`cranelisp_run_io`), Vec runtime, allocator family, IVar primitives, IO-observation `emit` registration — none of which is a module, none of which has user-visible symbol-table entries, none of which has GOT slots. They cannot route through a per-module GOT because **there is no `intrinsics` module**: intrinsics are backend-emitted-call targets categorically distinct from user-callable surfaces (BC §4b).

Primitives (`add-i64`, `int-to-string`, `str-concat`, `parse-int`, `not`, the full Decision-43 primitive set) **no longer use `JITBuilder::symbol`** as of S68. They flow through the standard cross-module GOT-indirect dispatch path (Decision 23 two-GOT model, Decision 31 GOT-indirect emission) against `cranelisp-primitives`' statically-constructed `PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable>>` (Decision 0048). The session's primitives `ModuleEntry`s reach fn pointers via `symbol_table.got().load_slot(entry.got_slot.unwrap())` — byte-identical to any user-module dispatch.

#### Asymmetry justification

The asymmetry between primitives (GOT-uniform) and intrinsics (`JITBuilder::symbol`-direct) is **load-bearing** and intentional, not residual. Decision 0048 is the boundary-of-asymmetry document: primitives have become uniform via the static `Arc<GotTable>` shape because primitives **are** a module (the synthetic `primitives` module); intrinsics retain `JITBuilder::symbol` because intrinsics are genuinely runtime-special — they aren't a module, they have no `SymbolTable` entries, they have no GOT slots, they're called by emitted IR using extern-name relocation only. Forcing intrinsics through a synthetic GOT would introduce a categorical fiction (a module that has no user-visible surface) for no semantic gain. The categorical line traces directly back to Decision 43 (primitives are user-callable; intrinsics are backend-emitted-call targets) and crystallises at Decision 0048 — post-S68 the asymmetry becomes the explicit binding shape.

#### Public-API impact

**None at S68.** The `JITBuilder::symbol` narrowing is a **consumer-side change** — `int`'s session-init path stops registering primitives via `JITBuilder::symbol` and starts referencing `cranelisp_primitives::PRIMITIVES_TABLE` instead. The intrinsics crate's published Rust API is unchanged: every fn enumerated below remains pub with the same signature; the registration call site that names them remains in `int`. This facade refresh is doc-level only; no pub-api items are added, changed, or removed by S68 on this crate. The S68 facade-compliance test for `cranelisp-intrinsics` should be green with no baseline regeneration required.

### Heap allocator (Decision-11 base-pointer convention)

```rust
#[export_name = "runtime/alloc"] pub extern "C" fn heap_alloc(payload_size: i64) -> i64;    // alloc total_size = payload_size + 16; returns base pointer. Linker symbol is the kebab-case "runtime/alloc"; the alias `cranelisp_alloc` (cf. `pub use` at root in pre-S67 builds) is the historical name, retired in favour of the kebab-case `#[export_name]`.
#[no_mangle] pub extern "C" fn heap_alloc_payload(payload_size: i64) -> i64;                // alias — same semantics, distinct name for codegen clarity
#[export_name = "runtime/dealloc"] pub extern "C" fn heap_dealloc(base_ptr: i64) -> i64;    // reads total_size from ptr+0; frees the full allocation

// Rust-callable accessor (used by tests + observability)
pub fn alloc_with_rc(payload_size: usize) -> *mut u8;

// Rust-callable dealloc (test + audit path; mirrors the linker symbol semantics)
pub unsafe fn dealloc(base: *mut u8);

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
#[export_name = "runtime/rc_underflow_check"] pub extern "C-unwind" fn rc_underflow_check(ptr: i64, old_rc: i64) -> i64;

// Per Decision 13 — backend MAY emit `atomic_rmw add 1` (Ordering::Relaxed) for inc
// and `atomic_rmw sub 1` (Ordering::Release) for dec directly in CLIF — both shapes
// coexist as the codegen-choice allows. The `rc_inc` / `rc_dec` extern-name path is
// reserved for re-introduction if and when out-of-line emit becomes desirable;
// the current implementation inlines all RC ops in CLIF.
```

`rc_underflow_check` is invoked only in debug builds when an inc would overflow or a dec would underflow.

```rust
pub fn is_rc_trace_enabled() -> bool;                                              // observability — checked by backend at codegen time
pub fn rc_trace(op: &str, ptr: i64, rc: i64);                                      // Rust-callable trace emit — used by backend's debug-build CLIF probes and by intrinsics' own inc/dec inline tracing scaffolding (gated by `is_rc_trace_enabled`)
```

### Drop glue (two kinds — backend-emitted vs Rust-callable per-type helpers)

There are TWO kinds of drop-related functions on this crate's surface, and the distinction is load-bearing:

1. **Backend-emitted drop glue for user-defined types and closures** — one fn per `deftype` / closure layout / Vec element type; generated by backend at codegen time, attached to closures via the embedded `drop_glue_ptr` at offset 24 per Decision 11 — `[header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]`, `CAPTURES_START = 32`. Intrinsics does NOT host these; backend emits them into the JIT/object module per defn.

2. **Rust-callable per-type drop helpers for intrinsics-owned heap shapes** — one fn per *intrinsic* heap-resident shape that needs a recursive RC dec walk (Sexp trees, IO trees, vec-of-string, trace ADTs, closures with non-uniform capture layouts). These ARE on this facade — they belong here because the layout they walk is intrinsics-owned (Sexp marshaling tags from `cranelisp-types`; IO node tags from `cranelisp-platform`; vec layout from `vec_runtime`). Backend names them at codegen time when it knows the source value is of a shape covered by one of these helpers; otherwise backend emits its own per-defn drop glue per (1).

```rust
// (1) — backend-emitted per-defn drop glue is NOT a function on this surface.

// (2) — Rust-callable per-type drop helpers (the layout is intrinsics-owned):
pub fn consume_sexp(ptr: i64);                                                     // recursive RC dec walk over a Sexp tree (uses TAG_SEXP_* from cranelisp-types)
pub fn consume_slist(ptr: i64);                                                    // recursive RC dec walk over an SList (Sexp container)
pub fn consume_closure(ptr: i64);                                                  // closure-shape walk: dec captures via the embedded drop_glue_ptr at offset 24 (Decision 11)
pub fn consume_vec_of_string(ptr: i64);                                            // recursive RC dec walk over Vec<String>
pub fn consume_vec_with(ptr: i64, elem_consume: fn(i64));                          // recursive RC dec walk over Vec<T> with caller-supplied per-element consumer
pub fn consume_io_tree(ptr: i64);                                                  // recursive RC dec walk over an IO tree (see Decision 29)
pub fn consume_shallow(ptr: i64);                                                  // single-node dec for IO trampoline + general use (NOT recursive — re-owns field pointers; see Decision 29)
pub fn dec_shallow_io(ptr: i64);                                                   // single-node dec for the IO trampoline outer-node walk — distinct from transitive consume (field pointers already re-owned by other holders during the walk; see Decision 29)
```

Where the per-type Rust helper exists, backend emits a call to it (by Rust-name resolved at JIT-symbol registration time) in lieu of generating bespoke drop glue. Where no helper exists (user-defined `deftype`, ad-hoc closures), backend emits per-defn glue per (1).

The `TraceCall` ADT consumer (`consume_trace_call`) was previously hosted here; it relocated to int's `src/trace.rs` at S67 Wave 4 per Decision 40 (Path B1) — the ADT layout is owned by int and the consumer fn lives with the layout. See `facades/int.md` §"Tracing helpers — `src/trace.rs`".

### Vec runtime (module `vec_runtime`; Cow-checked per `data-structures.md`)

The Vec runtime lives in the `cranelisp_intrinsics::vec_runtime` module (renamed from the historical `vec.rs` — FIXME 0190). The actual signatures take element-callback fn-ptrs so element RC inc/dec is per-element-type without backend hard-coding the element layout:

```rust
#[export_name = "runtime/vec_new"]   pub extern "C" fn vec_new(cap: i64) -> i64;
#[export_name = "vec-set-copy"]      pub extern "C" fn vec_set_copy(vec: i64, idx: i64, val: i64, elem_inc_fn: i64) -> i64;     // last-use → in place; else copy + inc element refs via elem_inc_fn
#[export_name = "vec-push-copy"]     pub extern "C" fn vec_push_copy(vec: i64, val: i64, elem_inc_fn: i64) -> i64;              // last-use + capacity → in place; else copy + inc
#[export_name = "vec-push-grow"]     pub extern "C" fn vec_push_grow(vec: i64, val: i64) -> i64;                                // capacity exceeded → realloc + copy
#[export_name = "runtime/vec_drop"]  pub extern "C" fn vec_drop(vec: i64, elem_dec_fn: i64);                                    // recursive dec on element refs via elem_dec_fn + dealloc
```

The kebab-case `#[export_name]` is the linker symbol (`vec-push-copy`, etc.); the `runtime/`-prefixed ones (`runtime/vec_new`, `runtime/vec_drop`) follow the codegen-internal naming convention. Both shapes coexist for the same reason as the alloc family. (`vec-len` is a **user-callable primitive** — it lives in `cranelisp-primitives::vec`, not here; relocated with the rest of the user-callable surface, see the §"Sprint 67 disposition snapshot".)

#### Vec heap-layout ABI — blessed stable public contract (FIXME 0245, S73)

The Vec heap object's field offsets are a **stable, pinned public ABI** of `cranelisp-intrinsics`, exposed as `pub const`s on `vec_runtime` — the dual of the `HeapString::{LEN_OFFSET, DATA_OFFSET}` consts (§"Heap allocator" / §"String allocator + reader"). The Vec object is RC-headered (`HeapHeader { total_size, rc }` at offset 0, 16 bytes per Decision 11) followed by a 24-byte control block:

```rust
// crates/cranelisp-intrinsics/src/vec_runtime.rs — pub const layout-ABI:
pub const LEN_OFFSET:      usize = 16;   // i64 element count, immediately after the 16-byte header
pub const CAP_OFFSET:      usize = 24;   // i64 capacity
pub const DATA_PTR_OFFSET: usize = 32;   // *mut i64 to the heap-allocated element buffer
```

```
offset 0  | header: HeapHeader { total_size: u64, rc: AtomicI64 }   (16 bytes, Decision 11)
offset 16 | len: i64                                                (LEN_OFFSET)
offset 24 | cap: i64                                                (CAP_OFFSET)
offset 32 | data_ptr: *mut i64                                      (DATA_PTR_OFFSET)
```

These three consts are **new pub items** added by `/dev (intrinsics)` this sprint (FIXME 0245 — small additive change; `vec_runtime`'s own read/write helpers switch to its consts, eliminating the previous magic-number `+16`/`+24`/`+32` sites). They are governed by Principle 14 (FFI layout discipline; evolution via explicit version bump, not source-level guards) — the same regime as `HeapString`'s consts. **Named Rust consumer:** `cranelisp-primitives` (`vec.rs`, `string.rs`) reads these offsets for its `vec-len`, `split`, and `join` primitives and holds NO duplicate copies post-S73 (Principle 7; see §"Consumed surface" of `facades/primitives.md`). Adding/changing a Vec-layout const is a baseline-diff event with primitives as a named downstream.

**Baseline regeneration is a Phase-5 `/dev (intrinsics)` co-deliverable.** Exposing the three consts changes `crates/cranelisp-intrinsics/public-api.txt` (additive — three `pub const` lines under `vec_runtime`). `/dev (intrinsics)` regenerates the baseline in the same change-set per `design/arch/CLAUDE.md` §"Baseline-diff discipline"; `/arch`/`/design (intrinsics)` does not regen it here — this facade states the expectation.

### String allocator + reader + `HeapString` layout ABI (module `heap_string`)

Backend never reads or writes string bytes per Decision 12; the **allocator**, the **reader**, and the **`HeapString` layout** are the intrinsic surface that lives here, in the `cranelisp_intrinsics::heap_string` module (renamed from the historical `string.rs` — FIXME 0190). The **user-callable string ops** (`str-concat`, `substring`, `char-at`, `contains?`, `split`, `join`, `replace`, …) are NOT on this crate — they are primitives in the Decision-43 sense and were physically relocated to `cranelisp-primitives` (FIXME 0180, landed; see the §"Sprint 67 disposition snapshot" — "Relocated to `cranelisp-primitives` at Wave 3"). The pre-S67 facade text that listed the `str_*` family here and described it as "physically-here-until-FIXME-0180" is **retired** (FIXME 0213): the family is gone from this crate's pub-api, and `cranelisp-intrinsics/public-api.txt` confirms `heap_string` exposes only the allocator, reader, and `HeapString`.

```rust
// Allocator + reader (backend-emitted-call: intrinsic):
#[export_name = "runtime/alloc_string"] pub extern "C" fn heap_alloc_string(bytes_ptr: *const u8, byte_len: i64) -> i64;
#[export_name = "runtime/string_read"]  pub extern "C" fn string_read(s: i64, out_ptr: *mut *const u8, out_len: *mut i64);

// Rust-callable accessors (used by tests + `cranelisp-platform`'s CLString::as_str
// + `cranelisp-primitives`' string ops + intrinsics' own internal paths):
pub fn alloc_string(bytes: &[u8]) -> *mut u8;
pub unsafe fn read_string_as_str(base_ptr: i64) -> &'static str;

#[repr(C)]
pub struct HeapString {
    pub header: cranelisp_types::heap::HeapHeader,                                  // standard `HeapHeader { total_size, rc }` per Decision 11
    pub len: i64,
    /* opaque bytes follow */
}

impl HeapString {
    pub const LEN_OFFSET: i32;                                                     // codegen-time constant: offset of `len` from the base pointer
    pub const DATA_OFFSET: usize;                                                  // codegen-time constant: offset of the byte payload from the base pointer
    pub const fn payload_size(byte_len: usize) -> usize;                           // total payload bytes (len field + byte_len) used by callers of `alloc_with_rc` allocating a HeapString
}
```

**`HeapString` layout is a blessed, stable public ABI** (FIXME 0245). It is `#[repr(C)]` (not `#[non_exhaustive]`) per Principle 14 — its layout is the FFI contract; evolution governed by explicit version bump. The two const offsets `LEN_OFFSET` / `DATA_OFFSET` and `payload_size` are public layout-ABI items because two distinct consumers read them directly without re-deriving the layout:

- **backend** codegen sites that emit string-poking CLIF sequences;
- **`cranelisp-primitives`** (`string.rs`) for its user-callable string ops (`read_string_parts` reads `HeapString::LEN_OFFSET` / `DATA_OFFSET`) — a **named Rust consumer** of these consts (FIXME 0245; see `facades/primitives.md` §"Consumed surface"). Post-S73 primitives holds no duplicate copy of the string offsets.

These consts already exist on the current pub-api (`crates/cranelisp-intrinsics/public-api.txt`) — pinning them as the blessed contract is doc-level, no source/baseline change. `cranelisp-platform`'s `CLString` (see `crates/cranelisp-platform/src/lib.rs` `///` rustdoc on `CLString`; facade retired S71 W4) is a `#[repr(transparent)]` `i64` newtype carrying an alloc-base pointer to a `HeapString`; platform DLL code reaches the bytes via `CLString::as_str()` which calls back through this crate's `read_string_as_str`.

A future rope upgrade is an intrinsics-only change provided the surface above stays stable.

### Sexp marshaling (consumed via per-type drop helpers; no separate extern surface)

Macro-arg + `quote-sexp` Sexp construction is performed by backend-emitted code calling the heap allocator + writing layout-stable Sexp nodes (see marshaling tags `TAG_SEXP_*` on `cranelisp-types`). The previously-facade-named `sconcat` / `quote_sexp` externs are **not present** on the current pub-api surface — they were either absorbed into emitted CLIF (`quote_sexp` is now CLIF-only construction) or expressed at user level via `str-concat` for the string-concatenation case. The Sexp-recursive-walk drop helper `consume_sexp` (per §"Drop glue" above) is the only Rust-callable Sexp-shape function on this crate.

Use the marshaling tags from `cranelisp-types` (`TAG_SEXP_INT`, `TAG_SCONS`, etc.) to interpret heap-allocated Sexp values.

### IO trampoline (Decision 29)

```rust
#[no_mangle] pub extern "C" fn cranelisp_run_io(io_root_ptr: i64) -> i64;          // outer entry — consuming convention, calls run_io_trampoline internally
pub fn run_io_trampoline(io_ptr: i64) -> i64;                                      // Rust-callable internal walker (used by int's trampoline + tests)
```

(The pre-S67 facade-named `io_run` alternative entry has been retired; `cranelisp_run_io` is the single extern-name entry. The Rust-callable `run_io_trampoline` remains for non-extern paths.)

Walks the IO tree node-by-node, dispatching `Effect` nodes through `cranelisp_platform::HostContext` (see `crates/cranelisp-platform/src/lib.rs` rustdoc + `bounded-contexts.md` §5; facade retired S71 W4). `Pure` returns the inner value; `Bind` reduces lhs then continues with the continuation closure; `Par` fork-joins via rayon. Each outer node allocation is consumed via `dec_shallow_io` (single-node dec — see Decision 29) as the walker advances.

The IO trampoline is the intrinsics' bridge into platform — `int`'s `Sess::trampoline(code_ptr, expected_type)` calls into JIT'd user code which builds an IO tree, then calls `cranelisp_run_io(io_root_ptr)` to reduce it.

The IO node tags consumed by the trampoline (`IO_TAG_PURE`, `IO_TAG_EFFECT`, `IO_TAG_BIND`, `IO_TAG_PAR`) are public consts on `cranelisp-platform` — see `crates/cranelisp-platform/src/lib.rs` `IO_TAG_*` rustdoc (facade retired S71 W4). Intrinsics consumes them; the constants are NOT duplicated here.

### IO observation (extension point per Decision 40)

NOT diagnostics — an extension point in the same shape as `register_alloc_callback`. Intrinsics defines the observation taxonomy and a registration API; `int` implements all observer state. The IO trampoline emits events via the registered observer (with a relaxed-load null check; no-op if unregistered). All observer state — ring buffers, panic hook, formatter, dump, merge-sort — lives in `int`'s `src/io_trace.rs`. Production batch (`--link`, non-trace `--run`) does not register and pays one relaxed null-check load per call site (one conditional branch after optimisation).

```rust
#[non_exhaustive]
#[repr(u8)]
pub enum IoEventTag {
    TrampolineEnter, TrampolineExit,
    PureStep,
    BindEnter, BindExit,
    ContPush, ContPop,
    PlatformEffect,
    ParSpark, ParSerialGroupEnter, ParJoin, ParBarrierForce,
}

#[non_exhaustive]
pub enum IoEvent {
    TrampolineEnter { io_ptr: i64 },
    TrampolineExit  { result: i64 },
    PureStep        { value: i64, is_fresh: bool },
    BindEnter       { inner_ptr: i64, cont_ptr: i64, is_fresh: bool },
    BindExit        { new_current: i64 },
    Cont            { cont_ptr: i64, new_depth: u32, is_fresh: bool },          // ContPush + ContPop tag-paired payload
    PlatformEffect  { thunk_ptr: i64, scheduling_class: u8, resource_token: i64 },
    ParSpark              { parent_ptr: i64, branch_idx: u32, token: i64 },
    ParSerialGroupEnter   { branch_count: u32, token: i64 },
    ParJoin               { parent_ptr: i64, count: u32 },
    ParBarrierForce       { token: i64 },
}

pub type IoObserver = fn(IoEventTag, &IoEvent);

/// Replaces the current observer atomically. Thread-safe from any thread;
/// last write wins under happens-before ordering. Pass `None` to unregister.
/// Subsequent IO events emitted by the trampoline are delivered to the
/// observer most recently registered (in happens-before order). Callers
/// do not reason about Acquire/Release — the API commits to the contract.
pub fn register_io_observer(observer: Option<IoObserver>);
pub fn trace_anchor() -> &'static Instant;     // shared monotonic anchor (kept here so int's scheduler trace and the IO trace use the same origin)

/// Emits an event to the currently-registered observer (no-op if unregistered).
/// Called inline by the IO trampoline at the per-call-site emission points;
/// also Rust-callable for tests + cross-trace synthesis.
pub fn emit(tag: IoEventTag, event: &IoEvent);
```

`IoEventTag` and `IoEvent` move with the API into intrinsics — they ARE the callback's type contract; they belong where the trampoline lives. Naming parallels the GotObserver pattern in `facades/backend.md` (`GotEventTag` + `GotEvent` + `GotObserver`). `int`'s session startup (REPL mode or `--run` with `CRANELISP_IO_TRACE=1`) calls `intrinsics::register_io_observer(Some(int::io_trace::record))`. Decision 40 closes the runtime BC drift by relocation: the orchestration of `(trace ...)` (GOT-swap, wrapper machinery, frame stack, slash-command handlers) and the consumer-side observer state both live in `int`; intrinsics keeps only this ~50-line extension-point API.

### IVar primitives (lenient evaluation per spec §12.4.3)

```rust
#[export_name = "cranelisp_ivar_create"] pub extern "C" fn ivar_create(thunk: i64) -> i64;     // alloc empty IVar cell, attach thunk — returns base ptr
#[export_name = "cranelisp_ivar_spark"]  pub extern "C" fn ivar_spark(ivar: i64) -> i64;       // schedule the IVar's thunk to run on a worker (rayon spawn)
#[export_name = "cranelisp_ivar_force"]  pub extern "C" fn ivar_force(ivar: i64) -> i64;       // block until filled — return value
```

Backend emits `ivar_create` + `ivar_spark` for `let` bindings whose RHS is independent and expensive (cost heuristic per spec §12.4.3); `ivar_force` is emitted at use sites.

### Panic helper (called from match exhaustiveness, intrinsic failures)

Sentinel-pattern panic: Cranelift cannot unwind through JIT frames, so `runtime_panic` does NOT `!`-return. It stores a message sentinel in a thread-local; the host MUST call `take_runtime_error()` after every JIT entry to check for a pending panic and surface it as the program's exit signal. Per spec §12.7.2 — bare message is the contract; no enrichment per substance-scoping §2.10 (runtime panics are being driven to zero, not enriched).

```rust
#[no_mangle]
pub extern "C" fn runtime_panic(msg_ptr: *const u8, msg_len: usize);

pub fn take_runtime_error() -> Option<String>;
```

Also update the runtime_panic signature to reflect the `#[export_name]` linker form used in pub-api:

```rust
#[export_name = "runtime/panic"] pub extern "C" fn runtime_panic(msg_ptr: *const u8, msg_len: usize);
```

### `ops::cranelisp_op_*` — RETIRED AT S67 WAVE 2 (Decision 43 close)

The following 10 extern functions are the D43-banned "operator-as-value" duplicates of `cranelisp-primitives::ring0::*` (`add-i64`, `sub-i64`, etc.). They are listed on the Wave-1 pub-api baseline; **S67 Wave 2 deletes them** following `/design (backend)` Wave 1 REV-5 audit clearance (zero current consumers in backend codegen — backend's call sites migrated to `cranelisp-primitives::ring0` per the S66 Wave 4b uniform-dispatch landing). Listed here for traceability:

```rust
// S67 Wave 2 deletes — pre-S67 residue:
#[no_mangle] pub extern "C" fn cranelisp_op_add(a: i64, b: i64) -> i64;
#[no_mangle] pub extern "C" fn cranelisp_op_sub(a: i64, b: i64) -> i64;
#[no_mangle] pub extern "C" fn cranelisp_op_mul(a: i64, b: i64) -> i64;
#[no_mangle] pub extern "C" fn cranelisp_op_div(a: i64, b: i64) -> i64;
#[no_mangle] pub extern "C" fn cranelisp_op_eq(a: i64, b: i64) -> i64;
#[no_mangle] pub extern "C" fn cranelisp_op_neq(a: i64, b: i64) -> i64;
#[no_mangle] pub extern "C" fn cranelisp_op_lt(a: i64, b: i64) -> i64;
#[no_mangle] pub extern "C" fn cranelisp_op_le(a: i64, b: i64) -> i64;
#[no_mangle] pub extern "C" fn cranelisp_op_gt(a: i64, b: i64) -> i64;
#[no_mangle] pub extern "C" fn cranelisp_op_ge(a: i64, b: i64) -> i64;
```

The Decision-43 final-state intrinsics crate has **NO `ops::*` module**. Post-Wave-2, every operator call site routes through `cranelisp-primitives::ring0` and backend's name-keyed inline substitution table.

### Forbidden patterns

Mirroring `facades/backend.md` §"Non-goals" — load-bearing prohibitions for intrinsics callers + maintainers:

1. **No conditional registration of intrinsics.** Every intrinsic enumerated in this facade MUST be registered with the JIT unconditionally at session setup (`JITBuilder::symbol(...)` per `int`'s init path). Per-program syntactic scans gating which intrinsic to register are forbidden — they have repeatedly drifted (Sprint 59 Defect 8; S66 Wave 3a-β regression). The JIT's `Linkage::Import` set is the only correct scope; the cost of registering an unused intrinsic is one `HashMap` entry, the cost of missing one is a JIT-finalize panic. (Per FIXME 0178; implementation half landed in S66 Wave 3a-γ.)

   **Post-S68 narrowing**: only intrinsics enumerated on this facade are eligible for `JITBuilder::symbol` direct registration. Primitives — including the user-callable `str_*` family, now resident in `cranelisp-primitives` (FIXME 0180 landed) — flow through the standard GOT-indirect dispatch path against `cranelisp_primitives::PRIMITIVES_TABLE` (Decision 0048). Adding a primitive to `JITBuilder::symbol` registration is a regression of the post-S68 categorical line.

2. **No trait-knowledge keys in inline-substitution tables.** Per Decision 43 — backend's `primitives_inline.rs` substitution table is keyed on `Symbol` only (`add-i64 → iadd`), never on `(TraitName, Symbol, TypeName)` triples. The post-D43 final-state forbids the pattern; the `cranelisp_op_*` family above (Wave 2 deletes) was its last residue.

3. **No backend-emitted-call functions exposed on the primitives crate's public surface.** Per BC §4b — intrinsics are NOT callable from user code; they are not in any symbol table or GOT. `cranelisp-primitives` Rust-consumes a defined subset of intrinsics' surface — the allocator, the `HeapString`/`vec_runtime` layout-ABI consts, drop/RC/panic helpers (FIXME 0245; §"Consumed surface" of `facades/primitives.md`) — but it does NOT re-export those intrinsic externs as user-callable; the user-callable string/vec ops are primitives authored *in* `cranelisp-primitives` that *call into* intrinsics. User code never references an intrinsic name.

### Public consts

None. (The IO node-tag consts `IO_TAG_PURE` / `IO_TAG_EFFECT` / `IO_TAG_BIND` / `IO_TAG_PAR` live on `cranelisp-platform` — see `crates/cranelisp-platform/src/lib.rs` `IO_TAG_*` rustdoc; facade retired S71 W4. Intrinsics consumes them.)

The `IO_TRACE_BUFFER_CAPACITY` const relocated to `int` at S67 Wave 4 along with the rest of the `io_trace` ring-buffer machinery per Decision 40 (Path B1). See `facades/int.md` §"Observability — `src/io_trace.rs`".

---

## Types originated here

Per Principle 15 — the following are intrinsics-originated and live in `cranelisp-intrinsics`:

- `HeapString` (`#[repr(C)]`; with `LEN_OFFSET`, `DATA_OFFSET`, `payload_size` impl consts)
- `IoEvent`, `IoEventTag`, `IoObserver`, `register_io_observer`, `emit`, `trace_anchor` (the IO observation extension point per Decision 40)

**Previously here, relocated to `int` at S67 Wave 4** (per Decision 40 Path B1 — listed for traceability, not currently resident):
- `io_trace::{IoTracePayload, IoTraceTag, TraceFilter, IoTraceEvent, FlushGuard, IO_TRACE_BUFFER_CAPACITY}` — consumer-side ring-buffer types; relocated to `int`'s `src/io_trace.rs`.
- The `trace::*` extern functions (12 fns) and the `consume_trace_call` Rust helper — `(trace ...)` GOT-swap machinery + ADT walker; relocated to `int`'s `src/trace.rs`.

Post-Wave-4 final-state: intrinsics exposes only the `IoObserver` extension point per Decision 40 + 43; what consumers do with observed events (ring buffers, flush guards, panic hooks, dump formatters) is consumer-specific machinery owned by `int`. See `facades/int.md` §"Observability — `src/io_trace.rs`" and §"Tracing helpers — `src/trace.rs`" for the destination shapes.

The multi-consumer types intrinsics depends on (`Span`, `CranelispError`, `ErrorLocation`, marshaling tags `TAG_SNIL`/`TAG_SCONS`/etc., `SchedulingClass`) live in `cranelisp-types`. Consumers (backend codegen names them in emitted code; `int` reads them when interpreting marshaled values) import directly.

No re-exports of `cranelisp-types` items per Principle 15.

---

## Consumed surface

The intrinsics crate imports from:

- **`cranelisp-types`** — `Symbol`, `ErrorLocation`, `Span`, `CranelispError`, marshaling tags (`TAG_SNIL`, `TAG_SCONS`, `TAG_SEXP_*`), `SchedulingClass`. No types-crate trait implementations.
- **`cranelisp-platform`** — the `IO_TAG_*` consts (`IO_TAG_PURE`, `IO_TAG_EFFECT`, `IO_TAG_BIND`, `IO_TAG_PAR`) consumed by the IO trampoline; `HostContext` for the IO trampoline's Effect dispatch path. Per `bounded-contexts.md` §4b + §5 — intrinsics is paired with platform; the IO trampoline reaches platform fns through the per-entry GOT slot on `ModuleEntry::Def` (read via `symbol_table.got().load_slot(entry.got_slot.unwrap())` per Decision 26, S66 amendment + rollback `1dc57ae` — GOT is the single source of truth for callable addresses) rather than through a centralised dispatch wrapper. See `crates/cranelisp-platform/src/lib.rs` `///` rustdoc on `HostContext` (facade retired S71 W4) — no `HostContext::dispatch` is exposed; the per-entry GOT slot IS the dispatch path.

Intrinsics imports from no other workspace crate — not `cranelisp-frontend`, not `cranelisp-typecheck`, not `cranelisp-backend`, not `cranelisp-primitives`. (Backend names intrinsics extern functions by string at codegen time — relocation-time dependency, not a Rust-source dependency.)

---

## Sealed traits

None implemented. Intrinsics does not implement traits from `cranelisp-types`.

---

## `#[non_exhaustive]` DTOs and `#[repr(C)]` layout types

`#[non_exhaustive]`: `IoEvent`, `IoEventTag` (post-D40 IO observation contract — variants evolve as new event kinds land).

`#[repr(C)]` layout types: `HeapString` (per Principle 14 — string layout is the FFI contract with platform DLLs through `CLString::as_str()`; omits `#[non_exhaustive]` and governs evolution via explicit version bump). Its public consts `LEN_OFFSET` / `DATA_OFFSET` / `payload_size` are the codegen-time access pattern.

---

## Bounded-context invariants

These hold across sprints — the contract `cranelisp-intrinsics` makes with the rest of the workspace:

1. **Backend-emitted-call targets only.** Per Decision 43 — every fn in this crate is called by JIT-emitted code or by the IO trampoline; nothing here is callable from user code. Not in any symbol table; not in any GOT. Adding an intrinsic is a backend + intrinsics co-design; deleting one requires backend co-evolution.

2. **Representation containment.** Per `src/CLAUDE.md` "Heap Access" — within intrinsics, only `alloc.rs`, `heap_string.rs`, `vec_runtime.rs` define the layout constants (`HEAP_HEADER_SIZE`, field offsets). **Backend** reads the layout through the named extern functions, never by hard-coding offsets. **`cranelisp-primitives`** reads it through the blessed layout-ABI consts (`HeapString::{LEN_OFFSET, DATA_OFFSET}`, `vec_runtime::{LEN_OFFSET, CAP_OFFSET, DATA_PTR_OFFSET}`) — the one sanctioned cross-crate reader of the offsets (FIXME 0245), and only via those single-source consts, never by re-deriving them.

3. **Atomic RC discipline (Decision 13).** RC inc/dec emit `atomic_rmw` at all rings, even Ring 1 single-threaded. Acquire fence on the free path before drop_glue reads object fields. Avoids an ABI break when concurrency arrives at Ring 4.

4. **Strings opaque to backend (Decision 12).** `HeapString` layout is intrinsics-owned. All string operations go through extern functions. Enables future rope upgrade.

5. **Embedded `drop_glue_ptr` in closures (Decision 11).** Closures carry their drop fn at offset 24 — `[header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]`. The drop glue function is per-lambda generated by backend; null for closures with no heap captures. Cross-module closures self-describe; no side-table lookup required.

6. **Consuming convention at extern boundary (Decision 24).** Every `#[no_mangle]` extern function MUST consume its heap-typed arguments — dec any heap arg it does not return. Internal Rust helpers may use any local convention; the extern boundary enforces consuming so backend's call sites can emit uniformly.

7. **IO trampoline shallow dec (Decision 29).** `cranelisp_run_io` reduces IO trees node-by-node, consuming each outer allocation via `dec_shallow_io` — a distinct primitive from transitive `consume_io_tree` because field pointers are already re-owned by other holders during the walk.

8. **No state across sessions.** Stats accessors (`alloc_count`, etc.) are process-global — `int`'s `reset_counts` should be called at session start in test contexts. Production runs do not call `reset_counts`.

9. **Backend-driven evolution.** Intrinsics changes are typically driven by backend codegen choices (a new RC inlining strategy, a new IO node, a new trampoline shape). The crate does not accrete intrinsics for spec convenience; spec-defined operations live in `cranelisp-primitives`. The categorical line is the load-bearing distinction Decision 43 formalised — and Decision 0048 reinforces post-S68 by binding the dispatch asymmetry: intrinsics use `JITBuilder::symbol` direct registration; primitives use the standard GOT-indirect path. The dispatch shape is the runtime embodiment of the categorical line; drifting either side toward the other reopens the BC overlap Decision 43 closed.

10. **No `FQTypeName` at the intrinsics public surface.** Per `/arch` Sprint 67 Phase 3 Wave 0 verification — zero pub-api items on this crate name `FQTypeName` or `TypeName`. Intrinsics operates on raw heap pointers + marshaling tags (Sexp tags, IO tags) drawn from `cranelisp-types`; types are never named at the surface. This holds across the FQTypeName-migration sweep (FIXME 0151); no boundary lifts on this crate.

---

## Sprint 67 disposition snapshot

This facade was last refreshed at S67 Wave 4 close (FIXME 0207) against `crates/cranelisp-intrinsics/public-api.txt` (248 lines, down from 434 pre-Wave-4 / 474 pre-Wave-2). Disposition for every pub-api item:

- **Named in facade as-of S67**: allocator family + `dealloc` + stats; RC primitives (`rc_underflow_check`, `is_rc_trace_enabled`, `rc_trace`, `consume_shallow`); per-type Rust drop helpers (`consume_sexp/slist/closure/vec_of_string/vec_with/io_tree`, `dec_shallow_io`); IO trampoline (`cranelisp_run_io`, `run_io_trampoline`); IVar family; Vec primitives (with element-callback signatures); String allocator + reader + `HeapString` `#[repr(C)]` + impl consts (user-callable `str_*` family relocated to `cranelisp-primitives` at Wave 3 per FIXME 0180); `IoEvent` / `IoEventTag` / `IoObserver` / `register_io_observer` / `emit` / `trace_anchor`; `runtime_panic` / `take_runtime_error`.
- **Relocated to `int` at Wave 4** (no longer here; named for traceability in §"Types originated here" and §"Drop glue"): `io_trace::*` ring-buffer machinery (12 items); `trace::cranelisp_trace_*` (12 fns); `consume_trace_call` Rust helper. Destination: `int`'s `src/io_trace.rs` + `src/trace.rs`. See `facades/int.md`.
- **Retired at Wave 2**: `ops::cranelisp_op_*` (10 fns) — deleted per Decision 43. The Decision-43 final-state intrinsics crate has no `ops::*` module.
- **Relocated to `cranelisp-primitives` at Wave 3**: user-callable `str_*` family (15 fns) + `vec-len` per FIXME 0180. The backend-emitted-call string allocator + reader + `HeapString` layout remain here under the `heap_string` module; the Vec runtime remains here under `vec_runtime`.
- **Internal-but-exposed (no facade action)**: none.

**Orphan accounting:** the facade names every pub-api item in the current baseline; the facade-compliance test's intrinsics-side orphan count is zero.

---

## Cross-references

- `bounded-contexts.md` §4b — Intrinsics BC (full statement)
- `decisions/0043-runtime-split-into-primitives-intrinsics.md` — the split decision (primitives vs intrinsics categorical line)
- `decisions/0048-primitives-static-symboltable-and-got-in-crate.md` — **the boundary-of-asymmetry document for S68**: primitives go GOT-uniform via `PRIMITIVES_TABLE`; intrinsics retain `JITBuilder::symbol` direct registration as the load-bearing exception
- `decisions/0040-runtime-trace-io-trace-relocate-to-int.md` — IoObserver callback contract; the registration API resides here post-D43; `trace::*` and `io_trace::*` relocate to `int` at S67 Wave 4
- `decisions/0011-embedded-drop-glue-ptr-in-closures.md` — drop-glue layout
- `decisions/0013-atomic-rc-from-ring-1.md` (legacy) — atomic RC discipline (subsumed into BC invariant 3 above)
- `decisions/0047-fqtypename-binding-at-resolved-stage-boundaries.md` — FQTypeName binding; intrinsics surface verified zero-impact (BC invariant 10)
- `facades/primitives.md` — sibling crate from the same split; the in-tree **Rust consumer** of this crate's allocator + heap-layout-ABI consts (FIXME 0245; the `str_*` family now lives in primitives, FIXME 0180 landed); §"Consumed surface" pins the exact items
- `facades/primitives.md` — sibling cascade target (S68): single-pub-item shape (`PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<(), ()>>>`, S73 sever) is the GOT-uniform counterpart to this crate's `JITBuilder::symbol`-intrinsics-only narrowing
- `facades/backend.md` §"Consumed surface" — backend names intrinsics by string at codegen; §"`intrinsic_symbols()`" body shrinks at S68 (primitives entries retire; FIXME 0191) as the consumer-side embodiment of the asymmetry confirmed here
- `facades/int.md` §"Consumed surface" — int registers intrinsic fn ptrs with the JIT at session init (and at S68 references `cranelisp_primitives::PRIMITIVES_TABLE` directly for primitives — no `JITBuilder::symbol` route for those); §"Observability — `src/io_trace.rs`" + §"Tracing helpers — `src/trace.rs`" — destination homes for the Wave-4 relocations
- `crates/cranelisp-platform/src/lib.rs` `IO_TAG_*` rustdoc + `bounded-contexts.md` §5 — `IO_TAG_*` consts intrinsics consumes (facade retired S71 W4)
- `fixmes/0103-...` — io_trace + trace relocation tracker (in-flight; closes at Wave 4)
- `fixmes/0150-runtime-split-primitives-intrinsics.md` — D43 implementation tracker (closes alongside Wave 2 `ops::*` deletion + the previously-landed primitives_inline trait-knowledge removal)
- `fixmes/0178-arch-intrinsics-inventory-and-forbid-conditional-registration.md` — codified in §"Forbidden patterns" above
- `fixmes/0180-arch-primitives-physical-relocation-blocked-by-runtime-shims.md` — physical relocation of `str_*` family from intrinsics to primitives (landed; the family is gone from this crate's pub-api per the disposition snapshot)
- `fixmes/0245-arch-heap-layout-blessed-public-abi-of-intrinsics.md` — heap/Vec layout = intrinsics' blessed public ABI (option A); primitives is a named Rust consumer; this facade's §"Vec runtime" layout-ABI subsection + §"String allocator + reader" + the "Rust consumers" preamble are its `/arch` half
- (resolved this pass) FIXME 0190 — facade now names the renamed `heap_string` / `vec_runtime` modules. FIXME 0213 — the stale §"String primitives" section is reworked to the post-S67 state (allocator + reader + `HeapString` only; user-callable `str_*` relocated to primitives).
- `principles.md` Principle 1 (decoupling), Principle 7 (no duplicate addressable forms / single source of truth — operative test for the layout-const dedup), Principle 14 (FFI layout discipline — the blessed layout ABI), Principle 15 (facade types live with behaviour), Principle 17 (uniform dispatch)
