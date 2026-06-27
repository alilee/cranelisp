# Runtime — master design

Owner: `/design`. Single source of design intent for `crates/cranelisp-runtime/`. Authored Sprint 63; refreshed Sprint 64 against the pinned-Decision-40/41/42 + Principle-14/15 configuration.

This document elaborates *within* the bounded context fixed by `design/arch/bounded-contexts.md` §4 and the public surface fixed by `design/arch/facades/runtime.md`. Where this document and either of those drift, the bounded-context statement and facade win — file FIXME `target: /arch` or update this doc accordingly.

---

## 1. Bounded-context recap

The runtime is the C-ABI surface JIT-emitted code calls into. Per BC §4, it owns:

- the heap memory model (allocation, layout, base-pointer convention);
- atomic reference counting primitives (inc/dec emitted inline by backend; underflow check + `bytes_*` accounting here);
- drop glue helpers — both the per-type recursive consume functions (`drop::consume_*`) and the shallow single-node dec primitive `dec_shallow_io` (Decision 29);
- the `HeapString` representation (opaque to backend per Decision 12);
- `Vec` runtime primitives with COW discipline;
- the IO trampoline that reduces IO trees built by user code, dispatching `Effect` nodes through `cranelisp-platform::HostContext`;
- IVars (lenient evaluation cells) with rayon-backed sparking;
- `Sexp` / `SList` marshaling helpers (`sconcat`, `quote_sexp`);
- the panic intrinsic for match-exhaustiveness failures (`runtime_panic` thread-local sentinel pattern);
- runtime stats accessors (alloc/dealloc counts, bytes peak/current, live-allocs set in debug);
- the **`IoObserver` extension-point API** (Decision 40) — the trampoline emits events through a registered callback; runtime defines the taxonomy (`IoEventTag`, `IoEvent`), int implements observer state.

It does NOT own: codegen, scheduling, REPL session state, language types, DLL session lifecycle, or the platform manifest contract. It also does NOT own diagnostics or observability orchestration (per BC §4 + Decision 40) — `(trace ...)` GOT-swap orchestration and IO-trace ring-buffer state both live in int. Runtime's contribution to observability is a callback registration API plus the shared monotonic anchor used to merge-sort cross-cadence event streams.

**As-designed vs as-built.** The crate currently still hosts `trace.rs` (740 LOC) and `io_trace.rs` (952 LOC). Decision 40 (operative this sprint) commits to relocating both to int; runtime keeps a ~50-line `io_observer` module. The relocation is `/dev` work tracked by FIXME 0103. This doc describes the *as-designed* shape — the crate after the relocation lands. The as-built deviation is called out in §3 and §10 so it stays visible.

---

## 2. Public surface

The facade spec at `design/arch/facades/runtime.md` is the authoritative as-designed surface. This document does not restate the surface; it elaborates the rationale and the internal architecture that backs it.

Three structural notes about the surface worth naming:

1. **Surface-by-symbol-name, not by Rust path.** Backend names runtime extern functions by string at codegen time, so the public-API stability budget is paid in `#[no_mangle]` / `#[unsafe(export_name = ...)]` attributes, not in `pub use` lines. A rename of `vec_push_grow` is a backend-codegen change as much as it is a runtime-API change.
2. **Two callable conventions per item.** Many primitives expose both an `extern "C"` JIT entry point and a `pub fn` Rust accessor (`alloc_with_rc` / `heap_alloc`; `alloc_string` / `heap_alloc_string`; `run_io_trampoline` / `cranelisp_run_io`). The Rust form is for tests + integration callers (`Sess::trampoline`); the extern is for JIT'd code. They share the same logic but have different RC discipline (the Rust form is non-consuming; the extern enforces the Decision-24 consuming contract).
3. **Types originate here, no re-exports of `cranelisp-types`** (Principle 15). The runtime-originated boundary types are `HeapString`, `IoEventTag`, `IoEvent`, `IoObserver`, `IoTraceFlushGuard`, `SchedulerTraceFlushGuard`. Multi-consumer types runtime depends on (`Span`, `CranelispError`, marshaling tags `TAG_SNIL` / `TAG_SCONS` / etc., `SchedulingClass`, `HeapHeader`) live in `cranelisp-types` and are imported directly by consumers. The runtime `lib.rs` carries no `pub use cranelisp_types::*` ceremony.

**`#[repr(C)]` policy (Principle 14).** No `#[repr(C)]` types currently surface from this crate. `HeapString` is `#[repr(C)]` for layout determinism but is treated as opaque from the backend's POV — the backend never reads it as a layout-stable struct, only via extern functions. Sexp marshaling crosses as `i64` tags + extern functions, not as layout-stable structs. If a future runtime extension publishes a `#[repr(C)]` DTO (e.g., a callback table layout for an inversion-of-control hook), Principle 14 binds: omit `#[non_exhaustive]`, govern evolution by an explicit `ABI_VERSION` bump, and document the exemption inline in the facade.

---

## 3. Current-state summary (per file)

The runtime crate has no audit. The summary below is read directly from `crates/cranelisp-runtime/src/`.

| File | LOC | Primary responsibility | As-designed status |
|---|---:|---|---|
| `lib.rs` | 110 | Module registry + the public re-export wall (the surface backend names by string). | Stable. Loses the `io_trace::*` and `trace::*` re-export blocks; gains the `io_observer::*` block. |
| `alloc.rs` | 304 | `alloc_with_rc` / `dealloc` core; atomic alloc/dealloc/byte counters; debug `LIVE_ALLOCS` set; `heap_alloc` / `heap_alloc_payload` / `heap_dealloc` extern entry points. Decision 10 base-pointer layout enforced here. | Stable. |
| `rc.rs` | 199 | Atomic dec helper `consume_shallow`; `rc_underflow_check` debug-only callable from inline backend dec; RC trace logging (`CRANELISP_RC_TRACE=1`). Single discriminator for "is i64 a heap pointer?": `NULLARY_TAG_THRESHOLD` from `cranelisp-types`. | Stable. |
| `drop.rs` | 864 | Per-type recursive consume functions: `consume_slist`, `consume_sexp`, `consume_vec_of_heap`, `consume_trace_call`, `consume_io_tree`, `consume_closure`, plus the IO-trampoline-only shallow `dec_shallow_io` (Decision 29). The "Decision 24 backstop" — every extern primitive whose heap arg is shape-rich routes through here. | Stable. `consume_trace_call` becomes vestigial when trace.rs relocates — it serves the trace-ADT walk only — and follows trace.rs to int at relocation time. |
| `string.rs` | 717 | `HeapString` layout + alloc; ~15 string primitives (`str_concat`, `str_eq`, `str_len`, `str_substring`, `str_split`, `str_join`, `str_replace`, `str_trim`, `str_starts_with`, `str_ends_with`, `str_contains`, `str_to_upper`, `str_to_lower`, etc.). Layout opaque to backend per Decision 12. | Stable. |
| `vec.rs` | 666 | Two-allocation Vec (`[header(16) | len | cap | data_ptr]` + plain `cap*8` data buffer). COW-checking primitives (`vec_set_copy`, `vec_push_copy`, `vec_push_grow`, `vec_drop`). Backend pre-compiles args and passes through. | Stable. |
| `io.rs` | 966 | The IO trampoline. Iterative state machine over `Pure | Effect | Bind | Par`; explicit cont stack with per-cont `is_fresh` flag for RC discipline; rayon Par dispatch with resource-token serialisation; `cranelisp_run_io` extern wrapper enforces Decision 24 consuming via `consume_io_tree` post-walk. | Stable in shape. The ~17 inline `io_trace::record_event` calls swap to invoke the registered `IoObserver` (Decision 40) — same call sites, different sink. |
| `io_trace.rs` | 952 | Thread-local ring-buffer event log of trampoline transitions; merge-sortable across threads via shared `TRACE_ANCHOR` `Instant`; gated by `CRANELISP_IO_TRACE`. | **Relocates to int** per Decision 40. Replaced in this crate by `io_observer.rs` (~50 LOC) carrying `IoEventTag` / `IoEvent` / `IoObserver` / `register_io_observer` / `trace_anchor`. |
| `ivar.rs` | 314 | Write-once cells for spec §12.4.3 lenient evaluation. State CAS PENDING → EVALUATING → RESOLVED; rayon `spawn` for sparked thunks; force blocks. Atomic discipline per Decision 13. Sprint 92: `ivar_spark` gains a **global in-flight-spark budget** (module-static `AtomicIsize` counter + `CRANELISP_SPARK_BUDGET` cap) — over-budget sparks resolve inline on the caller instead of spawning, bounding spark explosion from syntactic-cost over-sparking. Runtime-only decision (codegen unchanged); no public-API diff. Design home `design/backend/lenient-eval.md` §3.6. | Stable. |
| `marshal.rs` | 389 | `quote_sexp` (compile-time Sexp → runtime heap layout) + `sconcat` (runtime SList concatenation for unquote-splicing). Tag constants imported from `cranelisp-types`. | Stable. |
| `trace.rs` | 740 | The runtime side of the language `(trace ...)` special form: GOT swap, frame stack, marshaling to `Trace` ADT. Process-global mutex-guarded state. | **Relocates to int** per Decision 40. The GOT-swap orchestration is "one-time setup performed by int" — it happens once before execution; after the swap the runtime is just runtime, dispatching through whatever GOT it has. The relocation does not require a runtime extension point — int can install the wrappers via the existing GOT discipline without runtime help. |
| `panic.rs` | 95 | `runtime_panic` thread-local sentinel + `take_runtime_error` polled by the host after every JIT call. Replaces `catch_unwind` (which would unwind through Cranelift frames lacking unwind tables). | Stable. Per Decision 42 §"Scope clarification", `runtime_panic` stays flat-`String` (panics are being driven to zero per spec §2.10, not enriched with `ErrorLocation`). |
| `primitives/int.rs` + `float.rs` + `bool.rs` | 369 total | Conversion primitives (`int_to_string`, `parse_int`, `float_to_string`, `bool_to_string`) + the named-primitive operator surface (`cranelisp_op_add`, `..._sub`, `..._eq`, etc. — Ring 0 named primitives that survive Ring 2's `+`-via-trait dispatch per Principle 9). | Stable. |

Total today: ~6 690 LOC. Post-Decision-40 relocation: ~4 990 LOC (~25% reduction). Of the LOC that stays, `io.rs` (966) and `drop.rs` (864) remain the two largest single subsystems.

Test density is high — every file ships a `mod tests` with a `// spec:` comment per test, and the Decision 24 / 29 RC-balance tests are present in `io.rs` and `rc.rs`.

---

## 4. Internal architecture (post-Decision-40)

```
            backend-emitted CLIF              integration layer
                 │                                   │
                 │ (extern "C" calls by name)        │ (Rust fn calls)
                 ▼                                   ▼
   ┌─────────────────────────────────────────────────────────┐
   │                       lib.rs                            │
   │   re-exports the surface; module structure declared     │
   └─────────────────────────────────────────────────────────┘
        │             │              │              │
        ▼             ▼              ▼              ▼
   alloc.rs       string.rs       vec.rs        io.rs   ───▶ cranelisp-platform::HostContext
        │             │              │              │
        └────► rc.rs ◄─────── drop.rs ◄────────────  │
                                  │                  │
        ivar.rs ──────────────────┘                  │
        marshal.rs ───────────────┘                  │
        primitives/ ──────────────┘                  │
        panic.rs (orthogonal — thread-local)         │
                                                     │
        io_observer.rs ◄── (Decision 40) ────────────┘
            ▲
            │ register_io_observer(Some(int::io_trace::record))
            │
        int (session startup)
```

`alloc.rs` is the foundation: every other file allocates through it. `rc.rs` provides the simple-case dec; `drop.rs` provides the shape-aware recursive consumes. `io.rs` is the largest single subsystem and the only one that crosses out (into platform via `HostContext::dispatch` — invoked through `cranelisp_platform::call_effect_thunk`). `io_observer.rs` is the new (Decision 40) extension point: a 50-line module that declares the observation taxonomy, holds an `AtomicPtr<()>`-shaped registry slot for the observer fn pointer, and exposes the shared `TRACE_ANCHOR` `Instant`.

Internal coupling is acceptable: `drop.rs` is the only file that knows the ADT and IO heap shapes in detail (one place, Principle 7). `alloc.rs` is the only file that touches `LIVE_ALLOCS` or the global counters (one place). `rc.rs::consume_shallow` is intentionally not the right tool for `drop.rs::consume_*` — the split keeps the simple case fast and the complex cases honest. The IO trampoline calls into the observer through one function pointer load + null check per event site; if no observer is registered (the `--link` and non-trace `--run` case), the cost is one relaxed load + one conditional branch.

---

## 5. Quality attributes

### Simplicity (Principle 6)

Post-Decision-40 the crate is genuinely small in scope: a heap, an RC system, a string runtime, a Vec runtime, an IO trampoline, IVars, marshaling, panic, and a thin observer extension point. `io.rs` (966 LOC) and `drop.rs` (864 LOC) are the two non-trivial files. Both are justified: the IO trampoline implements the spec §10 evaluation model with explicit RC accounting per Decision 24, and `drop.rs` is the single-source-of-truth implementation of recursive RC dec for every shape-rich heap layout. There is no obvious dead simplification.

### Maintainability

Per-file responsibilities are clean. Adding a new heap-typed ADT requires adding a `consume_*` to `drop.rs` and a corresponding caller in whichever extern receives it; the change is bounded. Adding a new platform-fn scheduling class is a `cranelisp-platform` change, not runtime — runtime reads `scheduling_class` off the destructured variant per Decision 26 (currently emitted as 0 in `io.rs:178-184`; see §10).

### Observability

Strong on RC: `CRANELISP_RC_TRACE` produces per-op log lines tied to pointer values; `LIVE_ALLOCS` catches double-free in debug builds; `bytes_peak` / `bytes_current` / `alloc_count` accessible to `/mem` slash command.

Strong on IO: per Decision 40, the trampoline emits typed events (`IoEventTag` + `IoEvent`) through whatever observer int has registered. The runtime defines the taxonomy and the call sites; int owns the ring-buffer state, env-var activation, panic hook, formatter, dump, and merge-sort. This is structurally identical to the existing `register_alloc_callback` host-callback pattern: runtime defines the contract, host implements. (Naming parallels the GotObserver pattern in `facades/backend.md` — `GotEventTag` + `GotEvent` + `GotObserver`.)

`TRACE_ANCHOR` (`trace_anchor() -> &'static Instant`) is exposed by the runtime side because both int's scheduler trace and int's IO trace need to share a single monotonic origin to merge-sort. Keeping the anchor in the runtime crate avoids a callback round-trip per anchor lookup and locates the shared origin where the trampoline's event-emission timestamps come from.

### Concurrency-safety (Principle 4)

Atomic RC from Ring 1 per Decision 13. Acquire fence on free path before reading drop-glue fields. Rayon-backed Par dispatch in `io.rs` and IVar sparking in `ivar.rs` are the only places runtime spawns work. No shared mutable runtime state across sessions other than: the global counters (intentional, atomic), `LIVE_ALLOCS` (debug, mutex), `RUNTIME_ERROR` thread-local (intentional — per-thread sentinel), and the observer fn pointer slot (single atomic-ptr write at registration).

The IO trampoline's per-cont `is_fresh` flag is the load-bearing concurrency invariant: continuation-produced subtrees are fresh and shallow-dec'd inline; caller-tree subtrees are not. The flag is documented in `io.rs:67-91` and tested by `decision24_run_io_pure_rc_balanced` and `run_io_trampoline_rc_balanced`.

### Performance

Hot paths:
- `heap_alloc` / `heap_dealloc`: one `Layout::from_size_align` + one global allocator call + 5 atomic RMWs (count, allocated, current, peak CAS, optional `LIVE_ALLOCS` mutex).
- RC inc/dec: emitted inline by backend as `atomic_rmw`. Runtime path entered only on dec to zero (drop glue) or debug underflow.
- `consume_shallow`: one atomic sub + branch on old_rc == 1.
- `run_io_trampoline`: per-step is one tag load + one branch + one stack push/pop + per-fresh-node a shallow dec. Per emitted event: one relaxed load of the observer pointer + null-check branch. Production batch with no observer: one branch per event site.

No premature optimisation visible. The `LIVE_ALLOCS` mutex is debug-only; the `BYTES_PEAK` CAS loop is a single relaxed CAS loop (no fence). The `HashMap` in `dispatch_par_branches_with_trace` (token grouping) is per-Par-node and small; not a hot-path concern.

### Testability (Principle 5)

Excellent. Every module has a `#[cfg(test)]` block with `// spec:` annotations. The Decision 24 / 29 RC-balance tests in `io.rs` and `rc.rs` directly assert `alloc_count - alloc_count_before == dealloc_count - dealloc_count_before` on representative shapes (Pure, Bind, deep bind chain, Par with effects). `reset_counts` exists for test isolation. Doublefree detection is a `#[should_panic]` test.

The crate is testable in isolation — no other workspace crate is imported except `cranelisp-types` (data) and `cranelisp-platform` (for `IO_TAG_*` constants and `call_effect_thunk`). Both are stable boundary types.

---

## 6. Memory model

The heap layout is the crate's load-bearing contract. Cite Decisions 10, 11, 12, 13.

**Layout (Decision 10).** All heap pointers point to offset 0 of the allocation:

```
+0   alloc_size: i64       (used by heap_dealloc to recover layout)
+8   rc: AtomicI64          (atomic_rmw target; backend writes inline)
+16  payload bytes ...      (per-type)
```

`HeapHeader::SIZE = 16`, `HeapHeader::RC_OFFSET = 8`. The base-pointer convention departs from the sketch's interior-pointer convention; positive offsets throughout means backend never needs to subtract.

**Closure layout (Decision 11).** Closures embed their drop glue:

```
+16  code_ptr: i64         (function address — dispatched via GOT in callable contexts)
+24  drop_glue_ptr: i64    (per-lambda backend-generated dec'r; null if no heap captures)
+32  captures...
```

`drop::consume_closure` reads `+24` and indirect-calls if non-null; otherwise just dec+free. Cross-module closures self-describe — no side-table lookup. This is what made the embedded-pointer design win over the rejected side-table earlier.

**Strings (Decision 12).** `HeapString` layout (`+16 = len`, `+24+ = bytes`) is owned by `string.rs`. Backend never reads or writes string bytes directly — every operation routes through an extern. This containment is what makes a future rope upgrade a runtime-only change.

**Atomic discipline (Decision 13).** Inc uses `Ordering::Relaxed`. Dec uses `Ordering::Release`. On the free path (old_rc == 1), an explicit `fence(Ordering::Acquire)` fires before reading payload fields for drop glue. The pattern is repeated everywhere RC-zero handling occurs (`rc::consume_shallow:92-95`, `drop::*` consume functions). Ring 1 single-threaded code pays the atomic cost up-front to avoid an ABI break when concurrency arrives.

**Vec is two allocations.** The Vec struct is RC'd; the data buffer is not. Backend pre-compiles last-use information and dispatches `vec_set_copy` (last-use fast path) vs the always-copy path. `vec_drop` recursively dec's heap-typed elements.

**Nullary tags.** Values below `NULLARY_TAG_THRESHOLD` (defined in `cranelisp-types`) are bare integer tags, not heap pointers. Every consume function and `consume_shallow` checks this before dereferencing. The threshold is the single discriminator for "is this an i64 a heap pointer?" — no other test exists, no other test should exist (Principle 7).

---

## 7. IO trampoline architecture

The trampoline is a synchronous reducer over IO-tree heap nodes. Cite Decisions 24, 26, 29, 31, 40.

**Tree shape.** Four constructors: `Pure(value)`, `Effect(thunk, resource_token)`, `Bind(inner, cont)`, `Par(branches...)`. Tags from `cranelisp-platform::IO_TAG_*` (placed in platform because both runtime and platform DLLs need to construct nodes).

**Iteration.** Explicit `cont_stack: Vec<(cont_ptr, is_fresh)>`, single mutable `current` + `current_is_fresh`. `Pure` pops next cont (or returns); `Effect` calls into platform via `call_effect_thunk`; `Bind` pushes the cont and descends into `inner`; `Par` dispatches branches via rayon. Deep bind chains run in O(stack-depth-of-cont-stack) on the heap, not the stack — `test_run_io_deep_bind_chain` exercises 1000 binds.

**RC discipline (Decision 24 + 29).** The trampoline is non-consuming of its input tree (caller owns it); the extern wrapper `cranelisp_run_io` calls `drop::consume_io_tree(io_root)` post-walk to release the caller's tree. *Within* the walk, every continuation-produced node is shallow-dec'd inline via `dec_shallow_io` (Decision 29's rationale: field pointers are already re-owned by other holders during the walk). The `current_is_fresh` flag tracks whether the active node belongs to the caller's tree (initially false) or to a continuation-produced subtree (true after the first `call_continuation`). Once true, it stays true — the entire continuation-rooted subtree is owned by the trampoline. Closures popped from `cont_stack` carry their own `is_fresh` flag inherited from the Bind that owned them; consume vs leave-alone branches on that flag.

This split is the canonical illustration of Decision 24's *scope* clarification: extern boundary (`cranelisp_run_io`) is consuming; internal Rust helper (`run_io_trampoline`) is non-consuming. Both are correct because the boundary contract is preserved at the right place.

**Par dispatch (`dispatch_par_branches_with_trace`).** Branches grouped by resource token: `token == 0` branches dispatch independently to rayon; same non-zero token branches form a serial group. Results placed back in original order. The token comes from the Effect node's `+32` field; non-Effect branches read 0.

**Scheduling class plumbing (Decision 26 + open).** `scheduling_class` lives on `PrimitiveKind::PlatformEffect` per Decision 26. The trampoline currently emits `0` as a placeholder in the `PlatformEffect` event payload (`io.rs:178-184`) because it has no back-reference from an Effect node to the platform symbol that constructed it. Two paths exist: (a) thread the class through Effect node payload (one extra field at +40); (b) consume the class via int's scheduler trace at correlation time. This is a real open question — see §10.

**Bridge to platform.** `cranelisp_platform::call_effect_thunk(thunk_ptr)` is the one boundary call. It accepts a `Box<Box<dyn FnOnce() -> i64>>` that the user code (or platform DLL) constructed when building the Effect node. Platform's `HostContext::dispatch` is the as-designed entry point for richer dispatch (typed args, scheduling-class-aware) — runtime currently invokes the simpler thunk form. When `HostContext::dispatch` lands in production, the trampoline's `IO_TAG_EFFECT` arm is the migration point.

**Observer emission (Decision 40).** Each state transition (`TrampolineEnter`, `PureStep`, `PlatformEffect`, `ContPop`, `BindDescend`, `ParDispatch`, `TrampolineExit`, etc.) calls into the registered `IoObserver`. The call site shape is:

```rust
if let Some(obs) = io_observer::current() {
    obs(IoEventTag::PureStep, &IoEvent::PureStep { node_ptr, value });
}
```

The relaxed atomic-ptr load + null branch costs ~one cycle on hot CPUs and is folded by the optimiser. When no observer is registered (production `--link`, non-trace `--run`), the trampoline pays exactly that — no allocation, no formatting, no buffer write. When the observer is registered (REPL, dev `--run` with `CRANELISP_IO_TRACE=1`), all observer state — ring buffer, panic hook, formatter, dump, merge-sort — lives in int's `src/io_trace/`. The runtime never sees the events again; it just emits.

---

## 8. Calling convention contract

Per Decision 24 (uniform consuming convention; scope clarified Sprint 58 Wave 1).

**Contract.** Every `extern "C"` (or `extern "C-unwind"`) function in this crate that receives heap-typed arguments MUST dec any heap arg it does not return. Internal Rust helpers (`run_io_trampoline`, `read_string_parts`, etc.) MAY use whatever local convention is convenient — the contract is enforced *only at the extern boundary*.

**How.** Three primitives implement the contract:

- `rc::consume_shallow(ptr)` — for heap values with no heap sub-references (HeapString, simple ADTs without heap fields). Atomic dec; if last ref, fence + dealloc.
- `drop::consume_*(ptr)` — for heap values with shape-known sub-references (`consume_slist`, `consume_sexp`, `consume_vec_of_heap`, `consume_io_tree`, `consume_closure`, plus `consume_trace_call` until trace.rs relocates). Atomic dec; if last ref, fence + recursively dec sub-refs + dealloc.
- `drop::dec_shallow_io(ptr)` — Decision 29's IO-trampoline-specific shallow dec. Distinct from `consume_shallow` because the IO node's sub-fields are already re-owned by other holders (the new `current` for Bind's inner, the `cont_stack` for Bind's cont, the rayon dispatch for Par's branches).

**Backend's role.** Backend emits inc-before-call for non-last-use heap-typed arguments, transferring ownership uniformly. The runtime's extern signature does not need to know whether its caller used a last-use or non-last-use path — the inc-before-call discipline makes both look the same from the callee's POV.

**Invariant preserved by tests.** `decision24_run_io_pure_rc_balanced`, `run_io_trampoline_rc_balanced`, `run_io_trampoline_deep_bind_chain_rc_balanced`, `decision24_consume_shallow_*` directly assert `delta(alloc_count) == delta(dealloc_count)` for representative programs.

---

## 9. Decision register (runtime-relevant)

| Decision | One-line takeaway | Effect on this crate |
|---|---|---|
| 10 — base-pointer ABI | Heap pointer = offset 0; `+8 = rc`; positive offsets only. | `alloc.rs` enforces; every other file consumes via `HeapHeader` constants. |
| 11 — embedded `drop_glue_ptr` | Closures self-describe drop. | `drop::consume_closure` reads `+24` and indirect-calls. |
| 12 — strings opaque to backend | `HeapString` runtime-owned. | `string.rs` is the sole layout authority. |
| 13 — atomic RC from Ring 1 | `atomic_rmw` even single-threaded. | `rc.rs`, `drop.rs` use `Ordering::Release` on dec, fence on free. |
| 24 — uniform consuming convention | Extern boundary consumes its heap args. | `rc::consume_shallow`, `drop::consume_*` are how. Tests in §8. |
| 26 — `scheduling_class` on `PlatformEffect` variant | Static manifest field; runtime reads off destructured variant. | `io.rs:178-184` emits 0 placeholder pending plumbing — see §10. |
| 29 — `dec_shallow_io` IO trampoline primitive | Single-node dec for nodes whose fields are already re-owned. | `drop::dec_shallow_io`; load-bearing in `io.rs`. |
| 31 — per-batch JIT + heap-closure callback safety | Closures hold GOT-indirect dispatch, not raw code ptrs. | Runtime side is "do not retain raw code ptrs" — already true: thunks are `Box<Box<dyn FnOnce>>`, closures dispatched via code_ptr loaded from heap each time. |
| 40 — `trace.rs` and `io_trace.rs` relocate to int; runtime keeps `IoObserver` callback contract; BC §4 unchanged | New module `io_observer.rs` carries the taxonomy + registration; trampoline event sites swap to observer-driven; trace/io_trace directories move to int. | **Major surface change** — see §3, §4, §7. As-built work tracked by FIXME 0103 (`/dev`); this doc describes the as-designed shape post-relocation. |
| 41 — `compile_to_module` per-symbol JIT cardinality; `Code` moves to `cranelisp-backend`; backend writes shared state directly | Backend-internal change; `Code` enum no longer in `cranelisp-types`. | **No direct runtime impact.** Runtime does not name `Code`. The closure-side discipline (no retained raw code ptrs) is unchanged. |
| 42 — `PlatformError` adopts `ErrorLocation` | `PlatformError` lives in `cranelisp-types`; constructed by platform; surfaces via `CranelispError::Platform`. | **Light runtime impact.** Decision 42's §"Scope clarification" explicitly excludes `runtime_panic` from the enrichment — runtime panics are being driven to zero per spec §2.10, not enriched. Runtime keeps the flat-`String` panic shape. The facade truth-tells the actual signature (Sprint 64). |

Decisions 14–23, 25, 27, 28, 30, 32–39 are typecheck/backend/int-internal and have no direct runtime impact.

**Operative-active vs legacy.** Per `design/arch/CLAUDE.md`'s "active register holds Decisions whose outcome is NOT yet fully embodied" rule, Decisions 12, 13, 24, 26, 29 are now legacy (outcome embodied in this crate's structure + tests + the facade). Decisions 11, 31, 40, 41, 42 are operative-active because they carry forward-handoff or pre-implementation work. Decision 10 is environmental (rejected-alternative capture).

---

## 10. Open questions / proposed FIXMEs

The Sprint 64 sweep resolved most of the prior FIXMEs in this section. What remains:

### Effect-node scheduling class plumbing (existing FIXME territory)

**Issue.** `io.rs:178-184` emits `scheduling_class: 0` as a placeholder when recording `PlatformEffect` events. The class is statically-known per-platform-fn (Decision 26: lives on `PrimitiveKind::PlatformEffect.scheduling_class`), but the trampoline has no back-reference from an Effect node to the platform-fn symbol that constructed it. Two paths: (a) extra field on Effect node payload at `+40` carrying the class; (b) consume the class via int's scheduler trace at merge-sort correlation time.

**Status.** This is forward-handoff work that benefits from Decision 40's relocation landing first — once the observer call sites are int-side, option (b) becomes cheaper. Defer the path choice until post-FIXME-0098 evidence is in. Not filing a new FIXME here; the inline FIXME at `io.rs:174` already marks the site.

### Runtime audit pass (proposed FIXME — `/sprint`)

**Issue.** The 2026-04-23 audit pass covered four crates (frontend, typecheck, backend, int). Runtime + platform were not yet covered. The runtime crate has no `audits/runtime-*.md` document, no current-state structural diagram, no HIGH/MEDIUM/LOW finding list. This document is a stand-in based on source-reading; an audit would catch what source-reading does not (architectural drift, hidden coupling, monoliths, duplication). LOC distribution (`io.rs` 966, `drop.rs` 864, plus the relocating `io_trace.rs` 952) suggests at least three candidates for monolith review.

**Proposed.** Schedule a runtime audit pass (and a platform audit pass) to complete the crate-audit set, with paired current-state and target-state diagrams. The audit should follow the Decision 40 relocation so it audits the post-relocation shape, not a transient one.

→ Filed as `0101-sprint-runtime-platform-audit-pass.md`.

### Subordinate RC discipline doc (proposed FIXME — `/design`, deferred)

**Issue.** `drop.rs` (864 LOC) and `rc.rs` (199 LOC) together implement the recursive RC discipline; the IO trampoline's RC accounting (§7) sits adjacent. This is large enough to warrant its own `design/runtime/rc-discipline.md` subordinate doc covering: per-shape consume function rationale, the simple-vs-complex split (`consume_shallow` vs `consume_*`), the IO `dec_shallow_io` carve-out, and the test coverage matrix.

**Proposed.** Author `design/runtime/rc-discipline.md` next time `/design` narrow-deploys to runtime *and* the sprint introduces a non-trivial change in this area. Not filing — the master doc is sufficient as a first pass.

### Runtime CLAUDE.md missing (proposed FIXME — `/dev`)

**Issue.** `crates/cranelisp-runtime/CLAUDE.md` does not exist. Other crates have one carrying local conventions, API gotchas, and crate-specific data structures. `/dev` next-narrowing to runtime would have nothing to read.

**Proposed.** When `/dev` next narrow-deploys to runtime, author `crates/cranelisp-runtime/CLAUDE.md` covering: heap layout offsets, RC discipline (consume vs dec_shallow), the IO-trampoline `is_fresh` invariant, the Decision 24 extern boundary contract, the Decision 40 observer pattern, and the JIT-symbol-naming gotchas (rename = backend codegen change).

→ Filed as `0102-dev-runtime-claude-md-missing.md`.

### As-built drift: trace.rs and io_trace.rs still present

**Status.** Decision 40 commits to relocation; the work is `/dev` territory tracked by FIXME 0103 (`design/arch/fixmes/0103-dev-runtime-int-trace-io-trace-relocation-and-io-observer.md`). Distinct from FIXME 0098 (the typed-error migration of `ResolutionGap`/`CheckError`/`ExpansionError`) and FIXME 0099 (GotObserver implementation). The three FIXMEs are sibling observability/error-shape concerns that all follow the same pattern (callback contract registered by `int`'s session startup) but are independent work units.

---

## Cross-references

- `design/arch/bounded-contexts.md` §4 — Runtime bounded context.
- `design/arch/facades/runtime.md` — Public surface (target).
- `crates/cranelisp-platform/src/lib.rs` `//!` + per-item `///` rustdoc + `design/arch/bounded-contexts.md` §5 — Paired platform surface (`HostContext`, `IO_TAG_*`); facade retired S71 Wave 4.
- `design/arch/principles.md` — Architectural principles (cited throughout).
- `design/arch/principles/14-ffi-layout-discipline.md` — `#[repr(C)]` layout policy (§2 application).
- `design/arch/principles/15-facade-types-live-with-behavior.md` — types-originate-here policy (§2 application).
- `design/arch/CLAUDE.md` Decisions 10, 11, 12, 13, 24, 26, 29, 31, 40, 41, 42 — runtime-relevant decisions (active and legacy).
- `design/backend/ring2-rc.md` — Backend's view of RC discipline (the caller-side of the contract this crate enforces).
- `design/backend/io-trampoline-trace.md` — IO-trace observability spec.
- `crates/cranelisp-runtime/src/` — the implementation surface (see §3 for per-file map).
- `spec/12-runtime.md` — language definition for runtime semantics.
