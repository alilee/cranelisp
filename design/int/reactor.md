# The slice-2 effect reactor — interior design (int / intrinsics-hosted)

**Owner**: `/design` (int). **Status**: AS-BUILT (Sprint 93 — effect-concurrency
slice 2, the reactor gate). **Subordinate to**: `design/arch/effect-concurrency.md`
Appendix B (the implementable plan — canonical, `/arch`-owned),
`design/arch/bounded-contexts.md` §6 (int reactor policy + impl-location) / §4b
(intrinsics) / §5 (platform), `design/arch/platform-interface.md` §6.8 (ABI-v7
substrate). **Implements**: `crates/cranelisp-intrinsics/src/{reactor.rs,strand.rs,io.rs}`.

This is the **per-crate interior** elaboration the arch plan (Appendix B) does not
author: *how* the slice-2 reactor + async-trampoline twin are built, and — crucially
— **how far the as-built actually reaches** (§4). It is the `/dev` implementation
reference. It does not re-litigate the substrate choice, the one await boundary, the
demo leaf, or the spill marker — those are settled in Appendix B; this doc elaborates
the interior beneath them and pins the as-built boundary so a future reader does not
over-assume.

> **Reactor location: `cranelisp-intrinsics`, NOT `src/`.** The C-ABI entry
> `cranelisp_run_io` and the whole reactor live in `cranelisp-intrinsics`. A
> `--link`'d program does **not** contain `src/` at runtime (int is the compiler
> binary), so the reactor must live in the trampoline crate to serve `--run`/REPL now
> **and** `--link` concurrency later. int owns only **construction-for-REPL/--run,
> policy, and feature-gating** — the same split as `io_observer` (int registers the
> sink + drives the dev surface; the runtime mechanism is intrinsics-owned). See BC §6.

---

## 1. Substrate

Per Appendix B (rejecting tokio): a **mio reactor** + a **`futures::executor::block_on`
single-future executor** + a **C-ABI waker projection**. mio is reaction-agnostic
(register a raw fd, project a `std::task::Waker`); `futures` is small and supplies
`block_on` + `join_all`; neither hides the host-reactor C-ABI the platform ABI needs.

**Feature topology** (`crates/cranelisp-intrinsics/Cargo.toml`):

| Feature | Gates | Deps |
|---|---|---|
| `concurrency` (exists) | ABI-v7 layout contracts only — `StrandId`, `StrandEvent`, the v7 `cranelisp-types`/`cranelisp-platform` types | **none** (zero runtime deps; the C-ABI surface platforms compile against) |
| `concurrency-runtime` (slice 2) | the reactor implementation — async trampoline twin + `block_on` executor + mio `HostCtx` reactor + strand sink | `["concurrency", "dep:mio", "dep:futures"]` |

`mio`/`futures` are `dep:`-gated **optional** deps, so with the feature off cargo
never links them. **`--link` / the exe-bundle build path must never request
`concurrency-runtime`** → the linked binary is byte-identical executor-free. This is
the deployment invariant: feature-off is the production default; the reactor is opt-in.

---

## 2. The reactor interior (`reactor.rs`, gated `concurrency-runtime`)

### 2.1 The mio reactor loop

`pub struct Reactor` (`reactor.rs:221`) owns a `mio::Poll`, an `Events` buffer, an
fd-waiter map (`fd_waiters: HashMap<usize, (RawFd, OwnedCWaker)>`), and a timer wheel
(`timer_heap: BinaryHeap<Reverse<TimerEntry>>` + `timer_waiters`). Key methods:

- `Reactor::new() -> io::Result<Self>` — fresh `mio::Poll`.
- `register_fd(fd, waker, interest)` (`:276`) — idempotent (`EEXIST` ⇒ keep the
  existing registration; the poll-fn re-registers on every `Pending`, so this must
  tolerate a still-parked fd). Any other error panics.
- `register_timer(deadline_nanos, waker)` (`:298`) — push into the min-heap.
- `turn(max_block: Duration)` (`:310`) — compute `timeout = min(soonest_timer − now,
  max_block)`, block in `mio::poll`, then fire ready fd waiters (one-shot deregister)
  and expired timers. Called by the executor **only between future polls**.

### 2.2 The C-ABI waker projection (the one new designed artifact)

A Rust `std::task::Waker` is projected across the platform C-ABI as a `CWaker`
(`{ data, vtable }`) over a static `WakerVTable` (`{ wake, wake_by_ref, clone, drop }`,
`:123`). `make_cabi_waker(w: std::task::Waker) -> CWaker` (`:130`) boxes the waker and
hands the platform a pointer + vtable; `drop_cabi_waker` releases it. `OwnedCWaker`
(`:151`) is the reactor-side owned wrapper (Clone + Wake + Drop) the waiter maps hold.
This is the A2 host-owned-reactor contract: the platform poll-fn receives the waker,
arms the host (`register_readable`/`register_timer`), and the reactor wakes it on
readiness — the platform owns the *what*, the host owns the *when*.

### 2.3 The `HostCtx` vtable

`make_host_ctx(reactor_ptr: *mut Reactor) -> HostCtx` (`:382`) builds the vtable the
platform poll-fn calls back through: `host_register_readable` / `_writable` /
`_timer` (`:363`–`:380`), each reborrowing `&mut *(host as *mut Reactor)` **inside its
own body only**. The `host` field carries **raw-pointer provenance** (never derived
from a `&Reactor`) so poll-fn reborrows and `turn()`'s reborrow are non-overlapping
in time — sound under Stacked/Tree Borrows (the B1 provenance invariant, `:384`).

### 2.4 The `block_on` driver

`block_on_reactor<F, T>(make_future: F) -> io::Result<T>` where
`F: AsyncFnOnce(&HostCtx) -> T` (`:520`): construct a fresh `Reactor`, take a raw
`*mut Reactor`, build the `HostCtx`, `Box::pin(make_future(&host))`, then loop —
poll the future; on `Pending` call `reactor.turn(MAX_TURN_BLOCK)` (between polls
only). Liveness guards: `MAX_TURN_BLOCK = 5s` per mio block, `MAX_TOTAL_BLOCK = 30s`
total.

### 2.5 The one await boundary — `EffectPoll`

`EffectPoll<'h>` (`reactor.rs:422`) is the **single** `Future` in the design:
`{ state: *mut c_void, poll_fn: PollFn, host: &'h HostCtx, result_fn: ResultReader,
strand: StrandId, polls: u32 }`. Its `Future::poll` (`:458`):

1. emit `EffectDispatched` (first poll, `polls == 0`) or `EffectResumed` (re-poll);
2. build a C-ABI waker from `cx.waker().clone()`;
3. call the platform `poll_fn(state, host, &cwaker)`;
4. `CPoll::Ready` ⇒ read the leaf's result via `result_fn(state)` → `TaskPoll::Ready(i64)`;
   `CPoll::Pending` ⇒ emit `EffectSuspended`, return `TaskPoll::Pending` (the leaf has
   armed the reactor against its fd/timer via the waker).

`state` carries the leaf's `#[repr(C)]` state struct (fd + result buffer); `Ready`'s
i64 result is read by the leaf-supplied `ResultReader` fn pointer. Bind / Pure /
`call_continuation` stay **synchronous** (straight-line between awaits) — `EffectPoll`
is the only suspension point.

### 2.6 The `Par`-overlap path

`join_io_leaves(leaves: Vec<EffectPoll<'_>>) -> Vec<i64>` (`:720`) is
`futures::future::join_all(leaves).await` — concurrent I/O-effect leaves on the **one**
reactor thread (no thread-per-read). This is the async `Par` overlap. It is distinct
from the retained CPU-spark path: feature-off `Par` and CPU sparks still dispatch via
rayon `dispatch_par_branches_with_trace` (`io.rs:530`) — the two pools (rayon CPU +
reactor I/O) are not unifiable (Appendix B).

### 2.7 The demo leaves

Hand-written fixture poll-fns (no `declare_platform!` macro change — that is slice 3+):
`async_read_pollfn(state, host, waker) -> CPoll` (`:613`) over a non-blocking fd
(`recv(NONBLOCK)` ⇒ bytes = `Ready`; `EWOULDBLOCK` ⇒ `register_readable` + `Pending`,
re-arming on every `Pending`), state `AsyncReadState { fd, result, registered }`
(`:575`); plus a `timer_write_pollfn` feeder (`:687`). Acceptance: two `async-read`s
over socketpairs run as `Par` branches, complete in ≈max(delay) on one reactor thread,
and produce an interleaved `Dispatched → Suspended → Resumed` strand stream for two
distinct strands.

---

## 3. The strand observability sink (`strand.rs`)

`StrandId(pub u64)` (`:24`, `#[repr(transparent)]`, `ROOT = StrandId(0)`) is the
correlation id threaded through every dispatch/suspend/resume — the indispensable
primitive (the `turn`-correlation precedent). `StrandEvent` (`:50`,
`#[non_exhaustive]`): `EffectDispatched` / `EffectSuspended` / `EffectResumed`
(slice-2 live) + `SparkCreated` / `SparkForced` (present in the enum, **emit deferred
to slice 3+**).

The sink is a sibling of `io_observer`: a process-global `static BUFFER:
Mutex<Option<Vec<StrandEvent>>>` (`:136`) with `start_strand_recording()` /
`emit_strand_event(ev)` / `drain_strand_events()` (`:141`–`:164`). `emit` is a no-op
(one lock + `is_none`) when not recording — minimal, dev-facing, and byte-identical-
when-off in spirit (the whole sink is behind `concurrency-runtime`). `next_strand()`
(`:175`, `AtomicU64` from 1) mints a fresh `StrandId` per `Par` branch (child of the
current strand; root is `ROOT`). Emit sites: `EffectDispatched` before the await in the
Effect arm, `EffectSuspended` in `EffectPoll::poll` on `Pending`, `EffectResumed` on
re-poll. int owns the dev surface (an OPTIONAL/spillable `/strand` dump); the buffer +
emit are intrinsics-owned.

---

## 4. AS-BUILT BOUNDARY — the await is NOT reachable through `cranelisp_run_io` yet

**This is the load-bearing accuracy note (`/review`-flagged). A future reader must
not assume real effects suspend yet.**

`cranelisp_run_io(io_ptr) -> i64` (`io.rs:75`) cfg-splits in `drive_io`:

- **feature off** (`:105`): `run_io_trampoline(io_ptr)` — today's sync stepper,
  byte-identical.
- **feature on** (`:111`): `block_on_reactor(async |_host|
  run_io_trampoline_inner_async(io_ptr).await)`.

But the async twin **`run_io_trampoline_inner_async`** (`io.rs:128`) currently has a
**fully synchronous body** — it `delegates` straight to `run_io_trampoline(io_ptr)`,
the proven sync stepper. The node walk (`run_io_trampoline_inner`, `io.rs:350`) steps
Pure / Effect / Bind / Par **synchronously**; its Effect arm forces the thunk via
`force_effect_node` — there is **no `.await`** on the real-IO-tree path. The in-source
comment (`io.rs:118`) states this plainly: *"in the minimal slice the body is fully
synchronous … poll-shape await nodes are a later backend slice … When the `.await`
Effect arm lands, this regains a real async body around that same shared bookend."*

**Consequence (state this plainly):**

> The `EffectPoll` await boundary is exercised **only by the fixture demo leaf**
> (`async_read_pollfn` / `timer_write_pollfn` driven through `EffectPoll` +
> `join_io_leaves` in tests). It is **NOT reachable through `cranelisp_run_io` for
> real IO-tree effect nodes** — real platform effects do **not** suspend on the
> reactor yet; they run through the synchronous stepper exactly as before the slice.

Wiring real poll-shape effect **nodes** through the await needs the **backend
poll-emission** that does not exist yet: the `declare_platform!` macro emitting
poll-fns + a backend GOT-indirect dispatch arm that passes `HostCtx`/`Waker` to the
effect call. That is **deferred to a later slice** (Appendix B per-crate table:
backend = *"NONE"* this slice; the dispatch arm is the deferred column). Slice 2
proves the substrate (reactor + waker projection + EffectPoll + Par overlap + strand
stream) against the fixture leaf; it does **not** route production effects through it.

The shared `TrampolineEnter`/`TrampolineExit` bookend is reused across the cfg-split
(Principle 7) precisely so the IO trace stays identical whether or not the runtime is
on — another reason the feature-on path is currently observationally identical to
feature-off for real effects.

---

## 5. What later slices (≥3) add — forward-looking, NOT designed here

One line each; these are arch-track items, elaborated when their slice opens:

- **Slice 3 — real effect-node await**: `declare_platform!` poll-fn emission + the
  backend GOT-indirect poll-dispatch arm, so `run_io_trampoline_inner_async` grows a
  real async Effect arm and production effects suspend on the reactor.
- **Token-cardinality `Semaphore`**: per-resource-token `Par` grouping/admission
  (the CPU-spark create-gate's I/O analogue) — bounds concurrent leaves per token.
- **Backpressure**: a per-kind in-flight budget table generalizing the S92 CPU
  spark-budget counter (FIXME 0442) into the reactor's I/O dimension.
- **Supervisor**: launch-and-continue + the 500/log/drop policy for detached strands,
  co-landing with structured cancellation.
- **Cancellation**: structured cancellation (the `race`/`select`/`timeout` combinator
  layer — the control half of the model) threaded through strand identity.

---

## 6. Cross-references

- `design/arch/effect-concurrency.md` Appendix B — the implementable plan (canonical).
- `design/arch/bounded-contexts.md` §6 (int reactor policy + impl-location), §4b
  (intrinsics hosting), §5 (platform C-ABI async leaf).
- `design/arch/platform-interface.md` §6.8 — ABI-v7 layout contracts (`ConcurrencyDescriptor`,
  `Poll`, `PollFn`, `HostCtx`, `Waker`, `WakerVTable`, `ConcurrentPlatformFn`).
- `design/arch/sequences/concurrency-scheduler.mmd` — reactor participant (intrinsics-hosted).
- `crates/cranelisp-intrinsics/src/{reactor.rs,strand.rs,io.rs}` — the implementation;
  `crates/cranelisp-intrinsics/Cargo.toml` — the feature gates.
- `design/int/io-integration.md`, `design/int/observability.md` — the sync IO
  trampoline + `io_observer` precedent this sink mirrors.
