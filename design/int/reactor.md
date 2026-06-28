# The slice-2 effect reactor — interior design (int / intrinsics-hosted)

**Owner**: `/design` (int). **Status**: S95 DESIGN REFRESH — *complete the IO
transition* (slices 3 + 6). The S94 substrate (real poll-shape effect-node await
through `cranelisp_run_io`) is AS-BUILT; S95 adds, all `concurrency`-gated and
byte-identical-off: the **host token-capacity `Semaphore` pool** (§2.8 — `(token,
capacity)` **dynamic on the IO node**, platform-supplied at the effect site via
`effect_on_resource_with_capacity`, keyed `HashMap<token, Semaphore>`; capacity-1 =
today's `SerialGroup`, capacity-N = the bounded pool, token-0 = no-acquire, with
first-writer-wins reconciliation + within-token capacity-1 ordering carried on purpose);
and the **two-pool join** (§2.6 refresh — the async `Par` arm partitions by node tag,
admission wraps **both** partitions, and the rayon CPU pool + reactor I/O pool run
concurrently across a **wakeable** rayon→reactor bridge). **Carrier re-blessed by /arch**
(`effect-concurrency.md` §8.1/§8.2): capacity rides dynamic on the node — **no
`DefKind.cardinality` field, no loader lift, no `cranelisp-types` edge touch** (this
supersedes the earlier static-field gate-(b) plan). `/dev` implements in Phase 5. **Prior layer**: S94 DESIGN REFRESH —
slice-2 completion (real effect-node await), the S93 substrate AS-BUILT, per the
R1-ratified backend↔intrinsics poll-shape Effect-node seam
(`design/arch/effect-concurrency.md` Appendix B §"the ratified backend↔intrinsics
poll-shape Effect-node seam" + §13 "S94 R1"). This doc is refreshed to the S95 design
target. **Subordinate to**:
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
total. **`MAX_TOTAL_BLOCK` is a poll-leaf-hang backstop, NOT a blocking-I/O ceiling** —
it does not fire while a rayon→reactor bridge is outstanding (`pending_bridges > 0`); see
§2.6 "Blocking-I/O ceiling" for the ruling and rationale.

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

### 2.6 The async `Par` arm — two-pool join (slice 6) + token-capacity admission (slice 3)

`join_io_leaves(leaves: Vec<EffectPoll<'_>>) -> Vec<i64>` (`:720`) is
`futures::future::join_all(leaves).await` — concurrent I/O-effect leaves on the **one**
reactor thread (no thread-per-read).

**S95 refresh (slice 6 — close the feature-on regression).** The S94-minimal
`run_par_node_async` (`:281`) was `join_all` over **every** branch on the one reactor
thread — correct for poll-shape leaves, but a regression for **blocking** effects: a
blocking `Par` serialized through the single reactor thread instead of parallelizing on
rayon (the 3 RED `nt-reactor-e2e` guards). Slice 6 closes this by partitioning the arm
by **node tag** and driving **both** pools concurrently; slice 3 adds the
token-capacity admission gate (§2.8) **wrapping both partitions** (the
`(token, capacity)` pair is node-read for blocking *and* poll effects alike — arch
`effect-concurrency.md` §8.1). The refreshed `run_par_node_async`:

1. Read `branch_ptrs` in source/binding order (the existing `read_par_branches`).
2. **Partition by dispatch tag** (gate (c) — the tag is already on the node, no symbol
   back-ref): `IO_TAG_EFFECT_POLL`-rooted branches → the **reactor** partition;
   everything else (`IO_TAG_EFFECT` blocking, `Bind`, `Pure`, nested `Par`) → the
   **rayon** partition. Original binding indices ride along so results re-merge in order.
3. **Token-capacity admission wraps BOTH partitions (§2.8).** Each branch acquires its
   node-read `(token, capacity)` permit from the **one shared** host-owned
   `HashMap<token, Semaphore>` **before** dispatch and releases on completion; `token ==
   0` ⇒ no acquire. Admission runs on the **reactor thread** for both partitions (that is
   what keeps the §2.8 permit map non-atomic): a poll leaf is admitted before its first
   `EffectPoll` poll; a blocking branch is admitted before its `rayon::spawn`, the permit
   held across the bridge and released when the bridge completion wakes back.
4. **Blocking partition → inline per-branch `rayon::spawn` + a wakeable `oneshot`
   error-ferry** (`io.rs::run_blocking_branch`), across a **wakeable rayon→reactor
   bridge**: each blocking branch is `rayon::spawn`'d and its completion is signalled
   through a `futures` `oneshot` **woken via `cx.waker()`**; the runtime error produced on
   the rayon worker is carried back across the bridge by a `take_runtime_error` (worker
   side) → `set_runtime_error` (reactor side) **ferry**. **Why not reuse
   `dispatch_par_branches_with_trace` verbatim:** that dispatcher does a **blocking
   `into_par_iter().collect()`**, which cannot be made wakeable without a
   `block_on(rayon_join)` on the reactor thread — the exact forbidden blocking-join (gate
   (c), load-bearing) that re-introduces the starvation slice 6 removes. So the as-built
   does **not** call that dispatcher; it inlines the **pieces** that carry over — the
   per-branch `rayon::spawn` and the error-ferry — beneath the wakeable bridge instead.
   **This is not a third dispatcher** (gate (c) holds): the §2.8 token-capacity semaphore
   *is* the scheduler; only the dispatcher's rayon-spawn + error-ferry plumbing is what
   carries over, not a new admission/grouping policy. **Still forbidden (gate (c)):**
   `block_on(rayon_join)` on the reactor thread, and a bespoke third dispatcher that
   re-implements admission. The wakeable bridge is the permanent §7 cross-pool handoff
   every later joined-pool slice reuses. The dispatcher's internal `SerialGroup`
   token-grouping is the capacity-1 degenerate the shared §2.8 pool now subsumes — it
   **dissolves toward** the uniform permit-acquire (arch §8).

   > **P7 watch-item — the fork-join error-ferry is now mirrored in two sites.** The
   > `take_runtime_error` → `set_runtime_error` ferry pattern lives in **both**
   > `dispatch_par_branches_with_trace` (the sync / feature-off and the
   > `concurrency`-feature-disabled blocking-`Par` path) **and** `run_blocking_branch`
   > (the async bridge path). A future change to ferry semantics must touch **both**
   > sites. Extract a shared `spawn-branch-and-ferry` helper **only if a third caller
   > appears** (Principle 6 — complexity has a budget; do not pre-abstract a two-site
   > mirror). Until then this is a recorded, accepted duplication, not silent drift.
5. **Poll-shape partition → the reactor `join_all`** of admitted leaves.
6. **Top-level join** the two partition-futures concurrently on the reactor thread
   (`futures::join!`), then **merge by original binding index** into the single
   `alloc_with_rc` results buffer the continuation consumes (the shape the sync
   `run_par_node` produces).

**Feature-off / `--link`:** byte-identical — the sync stepper + the rayon
`dispatch_par_branches_with_trace` are unchanged, no `IO_TAG_EFFECT_POLL` node is ever
constructed, no partition runs, and no executor links (§1). The two pools (rayon CPU +
reactor I/O) remain **not unifiable** (Appendix B §7): blocking work that occupies a
thread must not sit on the reactor; the reactor holds many pending poll futures no rayon
worker could.

**Blocking-I/O ceiling — UNCAPPED by design (the `MAX_TOTAL_BLOCK` ruling).** The
`block_on_reactor` liveness backstop `MAX_TOTAL_BLOCK = 5s`/`30s` (§2.4) exists to bound a
**genuinely-stuck** reactor — a *poll leaf that never completes* (a hang with no fd/timer
readiness ever arriving). It MUST NOT bound a legitimate **slow-but-completing** blocking
I/O branch running on rayon across the wakeable bridge (item 4): a long DB query or a slow
socket read that *will* finish is not a hang, and capping it would make **feature-on worse
than feature-off** — feature-off runs blocking I/O on rayon **uncapped** (it just blocks a
worker thread to completion). The cap firing on a healthy in-flight blocking branch is a
divergence, not a safety property. **Ruling (landing in parallel in
`cranelisp-intrinsics`): the `MAX_TOTAL_BLOCK` cap does not fire while
`pending_bridges > 0`** — i.e. it fires only for the genuinely-stuck case (**no bridge
pending AND no poll progress**). While any rayon→reactor bridge is outstanding the reactor
is legitimately waiting on off-thread work, exactly as feature-off would block. This is the
intended **blocking-I/O ceiling**: blocking branches are uncapped to match feature-off
parity (Principle 8 — no mode divergence); the backstop is reserved for the poll-leaf hang
it was designed for. Recorded here as a deliberate, documented decision so the divergence
from "everything is capped" is not silent.

> **backend↔intrinsics boundary.** The partition reads only the **node tag** baked by
> the backend (`IO_TAG_EFFECT` vs `IO_TAG_EFFECT_POLL`) — no descriptor, no symbol
> lookup. A branch that is a `Bind` chain mixing blocking and poll-shape effects is
> dispatched by its **root** tag for the minimal slice (the auto-IO independence
> analysis yields effect-rooted branches); a poll-rooted branch's nested blocking
> effects still force synchronously inside `run_io_trampoline_inner_async`'s
> `IO_TAG_EFFECT` arm. Refining mixed-chain routing (a nested blocking effect on a
> poll-rooted branch also offloading to rayon) is a later-slice question — coordinate
> with /design backend; out of scope for the S95 minimal two-pool join.

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

### 2.8 The token-capacity `Semaphore` pool (slice 3)

**Authority: `effect-concurrency.md` §8.1 (the ratified carrier) + §8.2 (ordering).**
The async analogue of the CPU-spark create-gate: a host-owned `Semaphore`-per-token that
bounds how many of a token's effects are concurrently in flight. It **generalizes**
today's `SerialGroup` (`dispatch_par_branches_with_trace`, io.rs — exactly capacity 1)
to an arbitrary pool size, and is the mechanism the bespoke group-by-token dispatcher
**dissolves toward**: *every effect acquires its token's permit before dispatch and
releases on completion* (arch §8).

**The carrier — `(token, capacity)` DYNAMIC on the node, platform-supplied at the effect
site (NOT a `DefKind` field, NOT a loader lift).** Capacity reaches the runtime the same
way the token already does — on the IO node, supplied by the platform at the effect site
(arch §8.1):

- Today `CLIO::effect_on_resource(token, f)` bakes a dynamic `resource_token` onto the
  `IO_TAG_EFFECT` node (payload offset 16); the trampoline reads it (`read_resource_token`).
- Slice 3 adds an additive sibling `effect_on_resource_with_capacity(token, capacity, f)`
  that appends `capacity` at **payload offset 32** (the node widens 32 → 40 bytes,
  **append-only — no existing offset moves**, so the fn-name handle stays at offset 24).
  `effect_on_resource(token, f)` becomes `…_with_capacity(token, 1, f)` — today's
  serial-within-token. An `IO_TAG_EFFECT_POLL` node reserves the **same**
  `(token, capacity)` slots (env-vs-node carrier is the interior choice — coordinate with
  /design backend), so **both effect kinds feed one pool**.
- The trampoline reduces to: *read `(token, capacity)` off the node; run a
  `Semaphore(capacity)` per token.* **No `DefKind.cardinality`/`capacity` field, no loader
  lift, no `cranelisp-types` edge touch** (this supersedes the prior gate-(b) static-field
  design; arch §8.1 "Consequences"). The static descriptor `token`/`capacity` become
  documentation + the v6 default bridge (Sequential ⇒ token 1/capacity 1; Commutative ⇒
  token 0/unbounded; ResourceSerial ⇒ per-instance token/capacity 1); the **live** values
  are platform-supplied.

> **S95 demo scope — capacity-N proven on the BLOCKING carrier; poll-shape live capacity
> → S96 (user-confirmed).** The §2.8 pool design is **carrier-agnostic** (it reads
> `(token, capacity)` off either node kind and runs one `Semaphore(capacity)` per token),
> and that design is what lands. But the S95 **demonstration** of capacity-N (pool sizing,
> first-writer-wins, parking) runs on the **blocking carrier** — `effect_on_resource_with_capacity`
> on blocking effects, admitted before `rayon::spawn` (§2.6). **Poll-shape nodes RESERVE
> the `(token, capacity)` slots at the sentinel (capacity 1) in S95**; live poll-shape
> capacity-N supply + the **acquire-around-poll lifecycle** (the permit wrapping the
> establish→ready arc of an `EffectPoll`, not just a one-shot dispatch) is an **S96 item**,
> co-landing with the web-platform rewrite — its real consumer — which is why /design
> backend deferred it as a Phase-3 refinement. So this sprint: the pool MECHANISM is fully
> proven on blocking (capacity-N, parking, reconciliation); the poll/reactor side proves
> only **distinct-token overlap** (the slice-2 mechanism, capacity 1), not capacity-N.
> Admission still wraps both partitions in S95 — poll branches simply run at the sentinel
> capacity 1.

**Semantics:**

| `(token, capacity)` | Behaviour | Maps to |
|---|---|---|
| `token == 0` | no acquire — full overlap | `Commutative` / unrestricted |
| `token T`, capacity 1 | strictly serial **and source-ordered** within `T` | today's `ResourceSerial` / `SerialGroup` |
| `token T`, capacity N≥2 | ≤ N concurrent on `T`; the (N+1)th **parks** until a permit frees | the bounded pool not previously expressible |

**Reconciliation — same token, different capacity ⇒ FIRST-WRITER-WINS (/arch-pinned,
§8.1).** Capacity is a property of the *resource*, so all effects on one token should
declare the same N (the DB case reads N from one pool handle — they agree by
construction); a disagreement is a platform (trust-boundary) bug. The semaphore for a
token is sized by the **first** value that creates it; later disagreeing values do **not**
resize it, and a dev-facing `TokenCapacityMismatch` strand event (§3) records the
disagreement. This is conservative and deterministic: it **never exceeds a declared
ceiling** (unlike taking the `max`, which would raise the bound past a capacity the
platform declared unsafe) and is not an `assert`/abort (the violation mis-sizes a pool, it
does not corrupt memory). The slice-4 *degree* throttle later composes as
`min(capacity, degree)` regardless.

**Placement — intrinsics-side mechanism, int-side policy (the BC §6 / S94 split).** The
`Semaphore` machinery lives in `cranelisp-intrinsics` (with the reactor), NOT `src/`, for
the same decisive reason the reactor does: a `--link`'d program does not contain `src/` at
runtime, so a pool hosted in int could never gate a linked program's effects. The pool is
created **single-sited in `block_on_reactor`** alongside the `Reactor` and `HostCtx` (§6.2
— divergence-proof by the same intrinsics-hosting argument; int grows no parallel pool
builder) and threaded through the async trampoline. **int's policy role shrinks to
feature-gating + the dev surface** — there is **no loader lift** now: the `concurrency-runtime`
gating (default + exe-bundle/`--link` never enable it) and the OPTIONAL `/strand` dev dump
(§3) that renders token acquire/park/release + the capacity-mismatch event. The capacity
VALUE never crosses the int boundary — it is platform-supplied at the effect site and
node-read by the trampoline.

**Mechanism — a single-threaded permit map (no atomics, no `Mutex`).** Admission runs on
the **one reactor thread** for both partitions (§2.6 item 3 — a blocking branch is admitted
on the reactor thread *before* its `rayon::spawn`, the permit held across the wakeable
bridge), so the pool is a plain `RefCell<HashMap<u64, TokenSlot>>` where `TokenSlot {
permits: u32, waiters: VecDeque<Waker> }` — no locking needed (mirroring the reactor's own
`fd_waiters` map, §2.1). An `AcquirePermit` future: `poll` ⇒ if `permits > 0`, decrement +
`Ready(Permit)`; else push `cx.waker()` into `waiters` (FIFO) + `Pending`. `Permit`-on-drop
increments `permits` and wakes the **front** waiter. The token's slot is created on first
acquire, sized to that first node-read capacity (first-writer-wins, above). (`futures`
ships no `Semaphore`; this hand-rolled single-threaded permit-counter is smaller and avoids
an added dep — coordinate the exact home/shape with /design backend, who owns the
node-keying half. If cross-thread admission is ever needed instead of reactor-thread
admission, the fallback is a `Mutex`/atomic-permit map — but reactor-thread admission keeps
it lock-free.)

**Within-token source ordering — carried on purpose, NOT a free consequence of permits
(arch §8.2).** A bare semaphore gives *exclusion* but not *order*, and order is observable
for same-resource effects (log appends to one file must land in source order):

- **Capacity 1 = the `SerialGroup` equivalent.** A capacity-1 same-token group is a
  **sequential async block** — exclusion *and* source order — mirroring today's
  `SerialGroup`. With one permit the token admits exactly one effect at a time, in FIFO
  order; the async `Par` arm constructs the leaf futures in source/binding order and
  `join_all`'s first poll visits them in that order (the leaf's **first** action is the
  acquire, before any suspension point), so admission/FIFO order = source order. This is
  the case §8.2 names as requiring deliberate ordering.
- **Capacity ≥ 2 promises no order beyond the permit discipline.** Arch §8.2: a
  capacity-N pool is "by definition an unordered bag of N slots" — the effects genuinely
  overlap, so ordering is not promised past exclusion. (The `VecDeque` admits FIFO for
  fairness, but that is an implementation nicety, not a guarantee callers may rely on at
  N ≥ 2.)

> **Robustness note for /dev.** The capacity-1 "first-poll enqueue = source order" leans
> on `join_all` polling its vec in order on the first poll. If that proves fragile, the
> fallback is to stamp each branch with a source sequence number at construction and admit
> in sequence order — but this matters **only** for capacity 1 (N ≥ 2 promises no order).
> Coordinate the carrier with /design backend; the FIFO form is the minimal design.

### 2.9 Testability seams (/dev unit + /qa e2e)

| Seam | Tier | What it pins |
|---|---|---|
| node-read `(token, capacity)` carrier | intrinsics unit | a node built by `effect_on_resource_with_capacity(T, N, f)` reads back `token == T` (offset 16) + `capacity == N` (offset 32); `effect_on_resource(T, f)` reads `capacity == 1`; **append-only** — the fn-name handle still at offset 24 |
| `AcquirePermit` over a fixture pool | intrinsics unit | capacity N: N acquires return `Ready`, the (N+1)th `Pending` until a `Permit` drops |
| **capacity-N parking** (S95: **blocking carrier**) | qa e2e | a **blocking** effect declaring `token T`, `capacity N` (via `effect_on_resource_with_capacity` on a blocking effect), with N+1 `Par` branches ⇒ the (N+1)th completes only after one frees; strand stream shows `TokenParked → TokenAcquired`. **Blocking-carrier only this sprint** — admission wraps both partitions (§2.6), but live poll-shape capacity-N is S96 (see §2.8 "S95 demo scope") |
| **distinct-token overlap** (poll/reactor) | qa e2e | N poll-shape effects on **distinct** tokens overlap on the reactor (≈max(delay) not sum). This is the slice-2 reactor mechanism — the poll side proves distinct-token overlap, NOT capacity-N, this sprint |
| **within-token order** | intrinsics unit + qa e2e | same-token **capacity-1** effects run serial **and** in source order (an ordered-append / admission-witness leaf); capacity ≥ 2 promises no order |
| **capacity-mismatch reconciliation** | intrinsics unit | two effects on one token with different capacities ⇒ the semaphore is sized by the **first** value (never resized), and a `TokenCapacityMismatch` strand event is emitted |
| **two-pool overlap** (slice 6) | qa e2e | a mixed blocking + poll-shape `Par` overlaps on **both** pools (≈max not sum); the 3 RED guards (`resource_serial_diff_token_parallelizes`, `auto_io_independent_diff_token_parallelizes_e2e`, `auto_io_par_grouping_uniform_across_modes`) flip green |
| **byte-identical-off** | qa e2e + int unit | feature-off: no `IO_TAG_EFFECT_POLL` / no pool constructed; the v6 rayon `SerialGroup` path is unchanged and blocking-`Par` parallelizes |
| **`--link` no executor** | qa e2e | the linked binary links no mio/futures/pool (the `dep:`-gated optional-dep guarantee, §1) |

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

**S95 — token-pool events.** Slice 3's admission gate (§2.8) adds four `StrandEvent`
variants (the §11 "token acquired / released — pool contention" surface):
`TokenAcquired { strand, token }` (permit granted), `TokenParked { strand, token }`
(the (N+1)th effect blocked on a full token — the user-observable capacity-N park,
FIXME 0447), `TokenReleased { strand, token }` (permit returned), and
`TokenCapacityMismatch { strand, token }` (a same-token capacity disagreement, recorded
under first-writer-wins reconciliation — §2.8 / arch §8.1; carries the first vs
disagreeing capacity for the dev sink, not an abort). Emit sites: `AcquirePermit::poll`
(granted vs parked), `Permit`-drop, and the pool's first-writer-wins check. The enum is
`#[non_exhaustive]`, so they join without breaking consumers. These are what /qa asserts
for the park/resume + reconciliation acceptance and what int's OPTIONAL `/strand` dump
renders. (The variant set + emit is intrinsics-owned, in `strand.rs`, behind
`concurrency-runtime`; coordinate the carrier with /design backend.)

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

### 4.1 Note — `capacity` does NOT ride this loader channel (the re-blessed slice-3 seam)

The channel above lifts **only `poll_shape`** (the blocking-vs-poll routing axis) onto
`DefKind::PlatformEffect`. It does **NOT** lift capacity. The /arch re-blessing of the
slice-3 seam (`effect-concurrency.md` §8.1) **retired** the earlier plan to lift a static
`DefKind.cardinality` field: there is **no `DefKind.cardinality`/`capacity` field, no
loader lift of capacity, and no `cranelisp-types` edge touch** this sprint. Capacity rides
**dynamically on the IO node**, platform-supplied at the effect site via
`effect_on_resource_with_capacity(token, capacity, f)` (node payload offset 32,
append-only), node-read by the trampoline to size the token's `Semaphore` — see §2.8 "The
carrier". The static descriptor `token`/`capacity` fields remain documentation + the v6
default bridge only; live values are platform-supplied. (`poll_shape`'s loader lift is
unaffected — it is the orthogonal routing axis, not the capacity carrier.)

---

## 5. What later slices (≥3) add — forward-looking, NOT designed here

> **Done in slice-2 completion (S94):** *real effect-node await* — `declare_platform!`
> poll-fn emission + the backend poll-construction arm + the real async Effect arm in
> `run_io_trampoline_inner_async` — per the R1-ratified seam (§2.5, §2.7, §4).
>
> **Done in S95 (this refresh), no longer "later slices":** the **token-capacity
> `Semaphore` pool** (slice 3 — §2.8; carrier = `(token, capacity)` dynamic on the node,
> no loader lift, per the re-blessed §8.1 seam) and the **blocking/CPU two-pool routing**
> (slice 6 — §2.6). Both are designed above; `/dev` implements in Phase 5. **Demo-scope
> caveat:** S95 proves capacity-N (sizing, parking, first-writer-wins) on the **blocking
> carrier**; live **poll-shape capacity-N + the acquire-around-poll lifecycle** is an
> **S96 item** co-landing with the web-platform rewrite (poll nodes reserve the slots at
> sentinel capacity 1 this sprint — see §2.8 "S95 demo scope").

One line each; these remain arch-track items, elaborated when their slice opens
(S96/S97 per `sprints/SPRINT.md`):

- **Backpressure / *degree* throttle** (slice 4 → S96): the *program's* in-flight cap
  (memory/fairness), always ≤ capacity — composes with the §2.8 pool as
  `min(capacity, degree)` (arch §5/§8.1). Generalizes the S92 CPU spark-budget counter
  (FIXME 0442) into the reactor's I/O dimension; the descriptor's inert `global_budget`
  field rides here.
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
   **S95 preserves this for the token pool.** The token-capacity `Semaphore` pool
   (§2.8) is constructed **single-sited in `block_on_reactor`** alongside the `Reactor`
   and `HostCtx` — int grows no parallel pool builder in `src/` or `cranelisp-exe-bundle`.
   It is a host-internal value (not a `HostCallbacks` field — it is reached through the
   trampoline, not the platform poll-fn at construction), so it adds nothing to the
   hand-mirrored callbacks and inherits the same single-source property by hosting;
   `--link` concurrency reaches it through the same `cranelisp_run_io` → `block_on_reactor`
   entry with no new mirror.

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

- `sprints/SPRINT.md` — S95 scope (slices 3 + 6) + the Phase-2 architecture review
  (gate (c) two-pool wakeable bridge). **Carrier re-blessed post-review** — see §8.1.
- `design/arch/effect-concurrency.md` **§8.1 (the ratified slice-3 carrier — `(token,
  capacity)` dynamic on the node, first-writer-wins reconciliation; the AUTHORITY for
  §2.8 / §2.6)** + §8.2 (within-token ordering), §5 (capacity vs *degree*), §7 (the
  two-pool model), Appendix B — the implementable plan (canonical).
- `design/arch/bounded-contexts.md` §6 (int reactor policy + impl-location), §4b
  (intrinsics hosting), §5 (platform C-ABI async leaf).
- `design/arch/platform-interface.md` §6.8 — ABI-v7 layout contracts (`ConcurrencyDescriptor`,
  `Poll`, `PollFn`, `HostCtx`, `Waker`, `WakerVTable`, `ConcurrentPlatformFn`).
- `design/arch/sequences/concurrency-scheduler.mmd` — reactor participant (intrinsics-hosted).
- `crates/cranelisp-intrinsics/src/{reactor.rs,strand.rs,io.rs}` — the implementation;
  `crates/cranelisp-intrinsics/Cargo.toml` — the feature gates.
- `design/int/io-integration.md`, `design/int/observability.md` — the sync IO
  trampoline + `io_observer` precedent this sink mirrors.
