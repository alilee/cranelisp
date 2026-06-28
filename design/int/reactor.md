# The slice-2 effect reactor — interior design (int / intrinsics-hosted)

**Owner**: `/design` (int). **Status**: S94 DESIGN REFRESH — slice-2 completion
(real effect-node await). The S93 substrate is AS-BUILT; S94 **closes the as-built
boundary** (§4) by routing real poll-shape effect nodes through the `EffectPoll`
await, per the R1-ratified backend↔intrinsics poll-shape Effect-node seam
(`design/arch/effect-concurrency.md` Appendix B §"the ratified backend↔intrinsics
poll-shape Effect-node seam" + §13 "S94 R1"). This doc is refreshed to the S94 design
target; `/dev` implements in Phase 5. **Subordinate to**:
`design/arch/effect-concurrency.md` Appendix B (the implementable plan — canonical,
`/arch`-owned),
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

### 2.5 The one await boundary — `EffectPoll` (S94: generic over the node seam)

`EffectPoll<'h>` is the **single** `Future` in the design. Its `Future::poll`:

1. emit `EffectDispatched` (first poll, `polls == 0`) or `EffectResumed` (re-poll);
2. build a C-ABI waker from `cx.waker().clone()`;
3. call the platform `poll_fn(state, host, &cwaker)`;
4. `CPoll::Ready` ⇒ read the leaf's i64 result by a **generic offset read** of the
   reserved result slot in `state` → `TaskPoll::Ready(i64)`;
   `CPoll::Pending` ⇒ emit `EffectSuspended`, return `TaskPoll::Pending` (the leaf has
   armed the reactor against its fd/timer via the waker).

**S94 seam change (R1 decision 3 — ratified).** `state` is the env of a **host-built
state-closure** that field-0 of a new `IO_TAG_EFFECT_POLL` node points at, reusing the
existing heap-closure layout `[header(16) | code_ptr@16 = GOT-loaded poll-fn |
drop_glue_ptr@24 = state teardown | env@32 = result-slot + i64 args + scratch]`. The
**backend** builds this closure at the effect site (R1 decision 2: poll-fn loaded from
`__cranelisp_got_platform_<name>` and baked as `code_ptr`, the effect's i64 args
marshaled as captures — the established closure-construction codegen; **no `make_state`
platform export**). The poll-fn writes its single i64 result (scalar or heap base
pointer) into the reserved env result slot; `EffectPoll` reads it generically once
`Poll::Ready`. **The S93 leaf-supplied `ResultReader` fn-pointer collapses to this
offset read** — there is no per-effect result reader and no platform-DLL result field.

> **Env-layout is a v7 host↔platform convention governed by `ABI_VERSION`.** The slot
> ordering — **result-slot first, then the i64 args in declaration order, then leaf
> scratch** — is the contract the backend's marshaling codegen and the poll-fn both
> obey. The carrier of the result location (a baked node field vs. a fixed env offset)
> is /design backend+int's interior choice, but the offset convention itself is part of
> the ABI-v7 surface; a change to it is an `ABI_VERSION` bump.

Bind / Pure / `call_continuation` stay **synchronous** (straight-line between awaits) —
`EffectPoll` is the only suspension point. Both node kinds flow through
`run_io_trampoline_inner_async`; the Effect arm `.await`s an `EffectPoll` for
`IO_TAG_EFFECT_POLL` and forces synchronously (no await) for the unchanged
`IO_TAG_EFFECT` (R3 byte-identical-off — the sync stepper only ever sees
`IO_TAG_EFFECT`).

### 2.6 The `Par`-overlap path

`join_io_leaves(leaves: Vec<EffectPoll<'_>>) -> Vec<i64>` (`:720`) is
`futures::future::join_all(leaves).await` — concurrent I/O-effect leaves on the **one**
reactor thread (no thread-per-read). This is the async `Par` overlap. It is distinct
from the retained CPU-spark path: feature-off `Par` and CPU sparks still dispatch via
rayon `dispatch_par_branches_with_trace` (`io.rs:530`) — the two pools (rayon CPU +
reactor I/O) are not unifiable (Appendix B).

### 2.7 The demo leaf — S94: a real `declare_platform!`-emitted in-tree leaf (R2)

**S94 promotes the demo from a hand-written fixture to a real leaf (R2/R6).** The
acceptance leaf MUST be a real `declare_platform!`-emitted async-capable
`DefKind::PlatformEffect` (a `blocking == 0` poll-shape effect), driven end-to-end
through the full macro → backend (poll-construction arm) → loader → `cranelisp_run_io`
path — **in-tree, no separate cdylib test-DLL** (R6: an in-tree `PlatformEffect`
satisfies R2 and keeps the wave self-contained). This is the load-bearing change: a
hand-written intrinsics fixture poll-fn would leave the new macro/backend/loader code
unexercised scaffolding.

Behaviour (unchanged in shape from the fixture): `async-read` holds a non-blocking raw
fd + a reserved result slot in its state-closure env; `poll` does `recv(fd, …,
NONBLOCK)` ⇒ on bytes, write the result into the slot + `Ready`; on `EWOULDBLOCK`,
`register_readable(host, fd, waker)` + `Pending` (re-arming on every `Pending`). The
write side is fed after a delay via the host reactor's `register_timer` (single-reactor,
**no** per-read OS thread).

**Acceptance:** two `async-read`s over two socketpairs run as `Par` branches, complete
in ≈**max**(delay) not sum on **one** reactor thread, the leaf's i64 result is read back
correctly via the generic env-offset read (§2.5), and the `StrandEvent` stream shows
`EffectDispatched → EffectSuspended → EffectResumed` interleaved for two distinct
strands. Feature-off: **no `IO_TAG_EFFECT_POLL` node is ever constructed** and the v6
blocking path is byte-identical; `--link` links no executor.

**The S93 hand-written fixture poll-fns are RETAINED as the substrate regression guard.**
`async_read_pollfn` / `timer_write_pollfn` (over `EffectPoll` + `join_io_leaves` in
intrinsics unit tests) continue to prove the reactor + waker projection + `EffectPoll`
+ `Par` overlap in isolation of the macro/backend/loader path — the lower-tier guard
beneath the new R2 end-to-end leaf.

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

## 4. AS-BUILT BOUNDARY — closed in S94: the await reaches real effect nodes

**S93 left a load-bearing boundary; S94 (this design) closes it.** This section
records the S93 starting point and the S94 design that routes real poll-shape effect
nodes through the await. **/dev implements in Phase 5** — until that lands, the S93
limitation below is the live as-built reality; a reader checking *as-built* before the
Phase-5 land must consult `io.rs` rather than assume this design has shipped.

**The S93 starting point.** `cranelisp_run_io(io_ptr) -> i64` (`io.rs:75`) cfg-splits
in `drive_io`: feature-off ⇒ `run_io_trampoline(io_ptr)` (the sync stepper,
byte-identical); feature-on ⇒ `block_on_reactor(async |_host|
run_io_trampoline_inner_async(io_ptr).await)`. In S93 the async twin
**`run_io_trampoline_inner_async`** (`io.rs:128`) had a **fully synchronous body** —
it delegated straight to `run_io_trampoline(io_ptr)`. So the `EffectPoll` `.await` was
exercised **only by the fixture demo leaf** and was **NOT reachable through
`cranelisp_run_io` for real IO-tree effect nodes**.

**The S94 close (the ratified seam).** Three coordinated changes route real nodes
through the await:

1. **Backend poll-construction arm (R3, byte-identical-off).** A second, additive
   effect-site arm keyed on the effect's declared shape (no cargo feature): for a
   `blocking == 0` effect it loads the poll-fn from `__cranelisp_got_platform_<name>`
   and builds an `IO_TAG_EFFECT_POLL` node over a host-built state-closure (§2.5).
   Blocking effects — every real platform today — take the **unchanged** v6
   `IO_TAG_EFFECT` arm. The poll arm is reached only by `concurrency`-gated poll
   effects, so the default build constructs no poll node.
2. **Real async Effect arm in `run_io_trampoline_inner_async`** (`io.rs:128`). The
   async twin grows a genuine `.await` body around the **shared
   `TrampolineEnter`/`TrampolineExit` bookend** (Principle 7 reuse) instead of
   delegating to the sync stepper. Its loop is the sync body verbatim except the
   Effect arm: `IO_TAG_EFFECT_POLL` ⇒ `.await` an `EffectPoll`; `IO_TAG_EFFECT` ⇒ the
   synchronous force, exactly as before. The sync stepper (feature-off) only ever sees
   `IO_TAG_EFFECT`.
3. **A real `declare_platform!`-emitted in-tree leaf (R2/R6)** driven end-to-end (§2.7).

**Consequence (state this plainly):**

> Under a `concurrency-runtime` build, real poll-shape platform effect **nodes**
> (`IO_TAG_EFFECT_POLL`) **suspend and resume on the reactor through
> `cranelisp_run_io`** via the real async Effect arm — no longer just the fixture
> leaf. Two such effects in a `Par` overlap on one reactor thread (≈max not sum).
> **Feature-off is byte-identical**: no `IO_TAG_EFFECT_POLL` node is ever constructed,
> the v6 blocking path is unchanged, and `--link` links no executor. The S93 fixture
> leaf is retained as the lower-tier substrate regression guard (§2.7).

The shared `TrampolineEnter`/`TrampolineExit` bookend reused across the cfg-split
(Principle 7) keeps the IO trace identical whether or not the runtime is on — so the
feature-on path stays observationally identical to feature-off for **blocking**
effects, and adds suspend/resume strand events only for genuine poll-shape effects.

---

## 5. What later slices (≥3) add — forward-looking, NOT designed here

> **Done in slice-2 completion (S94), no longer a "slice 3" item:** *real effect-node
> await* — `declare_platform!` poll-fn emission + the backend poll-construction arm +
> the real async Effect arm in `run_io_trampoline_inner_async` — is the headline of
> S94 (§2.5, §2.7, §4) per the R1-ratified seam. The naming reconciliation (App-B / §13
> / §6.8 previously labelled this "slice 3 / deferred") is /arch's R3 land-time task.

One line each; these remain arch-track items, elaborated when their slice opens:

- **Token-cardinality `Semaphore`**: per-resource-token `Par` grouping/admission
  (the CPU-spark create-gate's I/O analogue) — bounds concurrent leaves per token.
- **Backpressure**: a per-kind in-flight budget table generalizing the S92 CPU
  spark-budget counter (FIXME 0442) into the reactor's I/O dimension.
- **Supervisor**: launch-and-continue + the 500/log/drop policy for detached strands,
  co-landing with structured cancellation.
- **Cancellation**: structured cancellation (the `race`/`select`/`timeout` combinator
  layer — the control half of the model) threaded through strand identity.

---

## 6. Host-construction sharability (FIXME 0419, R4) — divergence-proofing

**The S94 wiring must not re-create the DEF-6 two-mirrored-sites divergence class.**
FIXME 0419 (`target: /arch`, kept open + decoupled from 0407 per R4) is **off the S94
critical path** — only the `--run`/REPL host-construction site is active this sprint;
`--link` concurrency is a later slice. But the reactor *freshly re-creates the hazard*
the DEF-6 heap corruption came from (two hand-mirrored host-construction sites), so the
S94 wiring is designed here so a later `--link` site can share **one** builder **by
construction**. This section is the int-side commitment; the actual shared-builder
introduction + its home/ABI surface is `/arch`'s call (0419) — int does not author it,
int wires S94 so it slots in without a rewrite.

### 6.1 Two host-construction surfaces — keep them on opposite trajectories

There are two distinct host-built values at the platform/host boundary; they have
**opposite** divergence exposure, and the design must not conflate them:

- **The reactor `HostCtx` / `Waker` / waker-vtable — already divergence-proof by
  construction.** The reactor (the mio loop + `make_host_ctx` + `make_cabi_waker` +
  `block_on_reactor`) lives in **`cranelisp-intrinsics`**, behind the single C-ABI
  entry `cranelisp_run_io` that **both** `--run`/REPL and `--link` link (BC §6; §4 of
  this doc; the `io_observer` precedent). There is exactly ONE construction site for
  the `HostCtx` vtable and the C-ABI waker — `make_host_ctx(reactor_ptr)` — reached by
  every mode through `cranelisp_run_io`. **This is the shape 0419 wants, achieved for
  free by the intrinsics-hosting decision**: a future `--link` program drives its
  effects through the *same* `cranelisp_run_io` → `block_on_reactor` → `make_host_ctx`,
  so no second reactor-host-construction site is ever hand-written. S94 must **preserve
  this** — the reactor host-construction stays in intrinsics; int never grows a parallel
  `HostCtx`/waker builder in `src/` or in `cranelisp-exe-bundle`.
- **The platform-DLL `HostCallbacks` (`alloc` + `alloc_with_tag`) — the LIVE DEF-6
  hazard, hand-mirrored at two sites.** `src/platform.rs` (`load_platform_dll`, the
  `--run`/REPL/JIT site) and `crates/cranelisp-exe-bundle/src/lib.rs`
  (`cranelisp_init_platform`, the `--link` startup-stub site) each construct a
  `HostCallbacks { alloc: heap_alloc_payload, alloc_with_tag: cranelisp_alloc_with_tag }`
  **by hand**, agreeing only by manual mirroring + a 10-line cross-file comment. DEF-6
  was exactly the window where they did NOT agree (one wired `heap_alloc`
  base-returning, the other `heap_alloc_payload` payload-returning — heap corruption).
  This is the 0419 target.

### 6.2 The int-side S94 commitment

1. **Reactor host-construction stays single-sited in intrinsics.** S94 adds no
   `HostCtx`/`Waker`/reactor builder to `src/` or `cranelisp-exe-bundle`. The dev-sink
   surface (the OPTIONAL `/strand` dump, §3) and the feature-gating are int's only
   reactor-adjacent code; neither constructs host-callback values. This keeps the
   reactor's host-construction divergence-proof-by-hosting — the property 0419 seeks,
   already held, must not be eroded by pulling reactor construction up into int.

2. **Do NOT widen the hand-mirrored `HostCallbacks` for the reactor.** The R1-ratified
   seam deliberately adds **no** new host-callback the platform poll-fn calls back
   through at *construction* time: the poll-fn receives `HostCtx`/`Waker` **at poll
   time** (in `EffectPoll::poll`), not through `HostCallbacks` at DLL-load time (§2.5,
   R1 decisions 2+3). State construction is **backend-built, host-internal** — no
   `make_state` export, no new `HostCallbacks` field. So S94 keeps `HostCallbacks` at
   its current two fields and does **not** multiply the 2-site hand-mirror. (This is the
   same reason 0407's 3-field widening is blocked behind the shared builder — do not
   pre-empt it from the reactor side either.)

3. **When `--link` concurrency lands (a later slice), it routes through the existing
   single entry — no new mirror.** Because the reactor lives in intrinsics and is
   reached via `cranelisp_run_io`, the `--link` startup stub
   (`cranelisp-exe-bundle`) gains **no** reactor-construction code — it continues to
   only build the platform `HostCallbacks` (the value 0419 consolidates). So the
   *only* host-construction `cranelisp-exe-bundle` ever hand-writes is the one
   `HostCallbacks` that 0419 will replace with a shared builder call. S94 leaves that
   site shaped exactly like the `src/platform.rs` site (same two fields, same intrinsic
   pointers) so 0419's "both sites call one builder" lands as a mechanical swap, not a
   refactor that has to untangle reactor wiring first.

### 6.3 Hand-off to `/arch` (0419) + open question

- **0419 stays `/arch`-owned.** int does not introduce the shared `HostCallbacks`
  builder (the lowest-crate `fn host_callbacks() -> HostCallbacks` both `src/platform.rs`
  and `cranelisp-exe-bundle` call); `/arch` decides its home (candidate:
  `cranelisp-intrinsics`, the lowest crate that can name both intrinsic pointers) and
  ABI surface. int's commitment above keeps S94 compatible with that landing.
- **Open question for `/arch`:** confirm that the reactor's `HostCtx`/waker
  construction is **explicitly out of 0419's scope** (it is already single-sited in
  intrinsics, not a hand-mirror) so 0419 stays narrowly the `HostCallbacks`
  consolidation and does not accidentally pull the (already-sound) reactor construction
  into a "host-construction builder" that would over-generalize. Cite: Principle 7
  (single source of truth), Principle 1 (decoupling over convenience) — the
  intrinsics-hosting already gives the reactor the single-source property; 0419's job is
  to give `HostCallbacks` the same property, not to merge two differently-shaped values.

Principle citations: **Principle 7 (single source of truth)** — one construction site
per host-built value; **Principle 3 (dependency flows toward stability)** — the shared
builder's home is the lowest crate that can name the pointers, never an upward
dependency; **Principle 8 (no mode divergence)** — `--run`/REPL and `--link` build the
same host values by calling the same code, not by hand-mirroring.

## 7. Cross-references

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
