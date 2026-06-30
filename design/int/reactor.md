# The slice-2 effect reactor — interior design (int / intrinsics-hosted)

**Owner**: `/design` (int). **Status**: S96 DESIGN REFRESH (Chunk C — slice 7) —
*the explicit control surface + the cancellation=drop completion of the A→C contract*:
the **combinator runtime** (`race`/`select` over the branch futures on the one reactor
thread; the winner resolves, **the losers are dropped = cancelled**, §2.15) + the
**trampoline-frame cancellation drop-guard** (frees a dropped branch's unconsumed
sub-tree, §2.15.1); the **two A3-review drop-path completions** now in-scope — finding #3
(`EffectPoll`-owned `ReactorInterest` RAII handle whose drop ACTIVELY deregisters
fd/timer interest, §2.16) + finding #4 (`Drop for AcquirePermit` removes its stale FIFO
waker by identity, §2.17); **`sleep`** (the runtime timer poll leaf) + **`timeout` =
`race io (sleep d)`** (§2.18); and **cancel-on-disconnect** (`race` the handler against a
disconnect-watch leaf) + **graceful shutdown** (drain-or-`clear` the supervisor, §2.19).
The unifying invariant: **cancellation = future-drop, and every drop path — permit (§2.9),
fd/timer interest (§2.16), FIFO waker (§2.17), unconsumed sub-tree (§2.15.1) —
releases/deregisters cleanly** so cancellation at volume neither leaks nor lost-wakes. All
on the **single-ABI, single-trampoline, lazy-reactor** post-cutover runtime (no feature
gate; no byte-identical-off invariant — the off-state is gone). **Prior layer**: S96
DESIGN REFRESH (Chunk B — slice 5 +
slice 4) — *the fan-out / control-flow layer on the Chunk-A substrate*: **launch-and-
continue** (the detached-launch node, §2.11), the **supervisor** (a `JoinSet`-equivalent
that owns each detached strand, catches its outcome, applies the §10 500/log/drop policy —
never re-raising into a nonexistent parent, never aborting the server, §2.12), and
**backpressure / admission budget** (`effective permits = min(capacity, degree)` on the
§2.8 token-permit map **plus** one **global** reactor-thread admission `Semaphore` bounding
total in-flight detached strands, §2.13). Both slices **co-land** (gate (b): the supervisor
is co-requisite with launch-and-continue, and detached fan-out MUST be bounded by admission
or it is a memory-exhaustion hazard — §14 step 4). All built on the **unchanged** Chunk-A
substrate: the §2.8 permit map, the error-ferry, the §7 wakeable bridge, and the §2.9 RAII
`Permit` — **gates (b) and (d) confirmed to HOLD post-cutover** (§2.14). **Prior layer**:
S96 Chunk A — *light up the poll-shape carrier*: the **acquire-around-poll lifecycle + RAII
`Permit` drop-guard** (§2.9). S95 proved the token-capacity `Semaphore` pool on
the BLOCKING carrier and reserved the poll-node `(token, capacity)` slots at the
sentinel; S96 lights up the poll carrier — the capacity permit now wraps the full
`EffectPoll` establish→`Pending`→…→`Ready` arc, **owned by the `EffectPoll`
future** so it releases on `Ready` AND on future-drop (the named **A→C contract**:
acquire-around-poll BUILDS the drop-release path; Chunk C cancellation EXERCISES
it). All `concurrency`-gated, byte-identical-off. **Prior layer**: S95 DESIGN REFRESH — *complete the IO
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

**S96 — `EffectPoll` owns the capacity `Permit` (§2.9).** The S96 acquire-around-poll
refresh adds one field to `EffectPoll`: `permit: Option<Permit>`, the token-capacity
permit acquired BEFORE establish and held across the whole establish→ready arc. On
`CPoll::Ready` the future `take()`s and drops the permit (eager release + FIFO wake)
*before* returning `TaskPoll::Ready`; on future-drop the `Option<Permit>` field's own
drop glue releases it if still `Some` (the cancellation path). See §2.9 for the full
lifecycle. (`EffectPoll` stays `Unpin` — `Option<Permit>` is movable; no `Drop for
EffectPoll` is hand-written, the field's drop glue is the cancellation release path.)

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
>
> **S96 update — the poll carrier is now lit (§2.9).** S96 replaces the S95 sentinel
> with LIVE poll-shape `(token, capacity)`: the poll node now carries a real
> `(token, capacity)` baked by the backend (token @ abs offset 32, capacity @ abs
> offset 40 — §2.9), and the permit is acquired at the **leaf establishment**
> (`await_poll_node`) and **owned by the `EffectPoll`** so it wraps the establish→ready
> arc and releases on `Ready`/drop. The branch-level no-op acquire S95 placed in
> `run_poll_partition` is removed — the single admission gate moves down onto the leaf
> future (the structural owner the A→C drop-release contract requires). The pool
> MECHANISM (the `RefCell<HashMap<u64, TokenSlot>>` permit map, `AcquirePermit`,
> `Drop for Permit`) is unchanged from S95 — it is carrier-agnostic; S96 only changes
> *who acquires and who owns the permit* on the poll side.

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

### 2.9 Acquire-around-poll lifecycle + RAII `Permit` drop-guard (slice 3, S96)

**Authority: `sprints/SPRINT.md` Phase-2 architecture review gate (a) + `effect-concurrency.md`
§8.1 (the pool carrier) / §7 (the wakeable bridge).** S95 proved the §2.8 pool on the
**blocking** carrier (admit → `rayon::spawn` → release on completion — a one-shot dispatch).
S96 lights up the **poll** carrier, where admission is qualitatively different: a poll-shape
effect does not run-to-completion off-thread; it *establishes, parks (Pending), resumes, and
eventually completes (Ready)* across many reactor turns on the one reactor thread. The permit
must wrap that **whole establish→ready arc**, not a one-shot dispatch — this is the
*acquire-around-poll* lifecycle, and it is why the permit must be an RAII drop-guard owned by
the `EffectPoll` future.

#### The lifecycle

The single admission gate wraps the whole arc, taken **once** at the leaf's establishment:

1. **Read `(token, capacity)` off the poll node** (`await_poll_node`, io.rs). For an
   `IO_TAG_EFFECT_POLL` node the backend's poll-construction arm bakes — and int READS —
   **token @ abs offset 32** (`FIELD_1_OFFSET`, via `read_resource_token`) and **capacity @
   abs offset 40** (`FIELD_1_OFFSET + 8` = `field_offset(2)`, via `read_capacity` /
   `POLL_CAPACITY_ABS_OFFSET`). The state-closure pointer is at abs offset 24
   (`FIELD_0_OFFSET`). These are the offsets the cross-crate agreement pins (see "Offsets read"
   below) — the heap-offset class that silently breaks if write-side (backend bake) and
   read-side (this trampoline) drift.
2. **Acquire BEFORE establish** — `let permit = env.acquire(token, capacity, strand).await;`
   on the reactor thread, BEFORE the first poll-fn call. `token == 0` ⇒ an inert no-op permit
   (unrestricted overlap). This is the trampoline's single admission gate; the `AcquirePermit`
   future resolves to a `Permit` once a slot is free, parking (FIFO) on a full token meanwhile
   (`TokenParked`/`TokenAcquired` events, §3).
3. **Move the `Permit` into the `EffectPoll`** — `EffectPoll::new(env, poll_fn, host, strand,
   permit)` stores it as `permit: Option<Permit>` (`Some` at construction). The permit is now
   **owned by the future** whose drop must release it. This is the load-bearing ownership move:
   the permit's lifetime is bound to the `EffectPoll`, so every way the future can end —
   `Ready`, or dropped-before-`Ready` — runs the release.
4. **`.await` the `EffectPoll` across establish→`Pending`→…→`Ready`.** While parked (a `Pending`
   poll has armed fd/timer interest via the waker, §2.5) the permit *slot* is held but the
   **reactor thread is freed** to drive other futures — a parked poll is a counter, not a
   thread (gate (a)). N same-token poll leaves each wait on their **own independent** external
   readiness; none depends on another *releasing* a permit, so park-while-holding-permit does
   **not** deadlock, and the (N+1)th same-token acquire parking on the token semaphore is
   correct backpressure.
5. **Release on `Ready` (EAGER).** When the poll-fn returns `CPoll::Ready`, `EffectPoll::poll`
   does `let _ = this.permit.take();` — moving the `Permit` out of the `Option` and dropping it
   (which increments the slot + FIFO-wakes the front parked waiter, via the existing `Drop for
   Permit`) — **before** returning `TaskPoll::Ready(value)`. Eager release is deliberate, NOT a
   reliance on future-drop: in a `join_all` an individual leaf future is **not dropped until
   the whole join completes**, so deferring release to future-drop would hold the permit past
   the leaf's own completion and starve same-token waiters until the slowest sibling finishes.
   The `take()` frees the slot the instant the result is available.

#### The RAII drop-guard (the A→C contract)

The `Permit` is an RAII drop-guard owned by `EffectPoll` as `permit: Option<Permit>`. There
are exactly two release paths, and the `Option` makes "released exactly once" *representable*
(Principle 20 — model invariants by representation; no boolean `released` flag to keep in
sync):

- **Release-on-`Ready`** — explicit `Option::take()` + drop in `EffectPoll::poll` (step 5
  above). After this the field is `None`.
- **Release-on-drop** — the `EffectPoll` future's **auto-generated drop glue** drops the
  `Option<Permit>` field. If the future is dropped while still `Some` — i.e. it never reached
  `Ready` because it was **cancelled / timed-out / race-lost / its connection disconnected** —
  the inner `Permit::drop` releases (increment + FIFO wake). **No `Drop for EffectPoll` is
  hand-written**; the field's own drop glue *is* the cancellation release path. This is the
  structural minimum — a leaked permit on a capacity-N token is exactly how the pool bleeds to
  deadlock, and binding the permit's lifetime to the future's makes the leak unrepresentable.

- **No double-release.** The two paths are mutually exclusive by the `Option`: `take()` on
  `Ready` leaves `None`, so the subsequent field-drop sees `None` and is a **no-op**. A
  dropped-before-`Ready` future never ran `take()`, so the field is `Some` and drops exactly
  once. `Drop for Permit` itself is already idempotent-safe against a missing slot
  (`slots.get_mut` → `None` ⇒ early return, reactor.rs:700) and against `token == 0` (inert),
  but the `Option` is the primary guarantee: the `Permit` is constructed once and consumed by
  exactly one of the two paths.

This is the named **A→C contract**: acquire-around-poll (Chunk A, this surface) **BUILDS** the
drop-release path — the permit owned by `EffectPoll`, released on both `Ready` and drop; Chunk
C cancellation **EXERCISES** it — a `race`/`select`/`timeout` combinator that drops a
still-`Pending` `EffectPoll` (the loser of a race, the timed-out branch) relies on this
drop-release to not leak the permit. The two MUST be co-reviewed for the `Permit`-on-drop path
(gate (a) requirement 1). Designing the drop-release path **now**, before any cancellation
combinator exists, is the point: Chunk C inherits a correct permit-release for free, with no
cancellation-specific permit plumbing.

> **Scope of the drop-release (A3-review reframing, recorded here per the §2.14 cross-ref).**
> Chunk A delivers **permit-only** release on drop (the `Option<Permit>` drop-glue) — a dropped
> in-flight `EffectPoll` releases its *permit* but does NOT actively *deregister its reactor
> interest* (the `fd_waiters`/`timer_waiters` entry + `mio` registration persist until that fd
> next readies). This is memory-safe and benign for one-shot `--run`/REPL, but it is a
> within-drive resource leak under **volume cancellation in a long-running reactor**. **Active
> reactor-interest deregistration is now DESIGNED in §2.16 (Chunk C — A3 finding #3 DISCHARGED):**
> the `EffectPoll` gains a second RAII field `_interest: ReactorInterest` whose drop removes the
> `fd_waiters`/`timer_waiters` entry + `mio`-deregisters — binding the interest's lifetime to the
> future exactly as this section binds the permit's. The Chunk-B supervisor panic-path instance
> (§2.14) is subsumed by it. (Pre-§2.16 this was deferred-to-Chunk-C; that deferral is resolved
> there.)

#### Non-re-entry (Requirement 2) + the §2.8 single-thread invariant

- **Acquire is non-re-entrant on its own token.** The acquire is taken **once**, at establish,
  before the poll-fn is ever called. The platform poll-fn receives only `(state, host, waker)`
  at poll time (§2.5) — it has **no handle to the `TokenPool`** and cannot call `acquire`. So a
  poll-fn cannot re-enter admission (on its own or any token) and cannot self-deadlock by
  dispatching a second effect on its own exhausted token (gate (a) requirement 2). The web case
  is sound by construction: `accept` mints a *fresh* connection token; the per-connection
  `read`/`send` ride that fresh token — never a re-entry on the listener/pool token.
- **The §2.8 lock-free single-reactor-thread permit-map invariant holds VERBATIM for the poll
  carrier.** Every permit operation for a poll leaf runs on the **one reactor thread**: the
  `AcquirePermit` future polls on the reactor thread; `EffectPoll::poll` (including the eager
  `take()`+drop on `Ready`) runs on the reactor thread; the cancellation field-drop runs
  wherever the combinator drops the future — which is also the reactor thread (the executor and
  all `EffectPoll`s live on it). So the pool stays a plain `RefCell<HashMap<u64, TokenSlot>>` —
  no atomics, no `Mutex` — exactly as §2.8/S95 established for the blocking carrier. (The poll
  carrier holds the permit *across reactor turns* rather than *across a rayon bridge*, but in
  both cases acquire and release are reactor-thread events.)

#### What changes from S95 (the acquire moves down onto the leaf)

S95 placed a **branch-level** no-op acquire in `run_poll_partition` (`io.rs` — at sentinel
token 0, held across `run_io_trampoline_inner_async`, owned by the partition async block). That
owner is wrong for the A→C contract — the permit must live on the future whose drop releases
it. S96:

- moves the acquire **down** to the leaf establishment (`await_poll_node`), where it reads the
  LIVE `(token, capacity)` and hands the resulting `Permit` to `EffectPoll::new(...)`;
- **removes** the branch-level no-op acquire from `run_poll_partition` — the single admission
  gate is now on the leaf future (no double-acquire);
- leaves the pool machinery (`TokenPool`, `AcquirePermit`, `TokenSlot`, `Drop for Permit`)
  **unchanged** — it is carrier-agnostic; only *who acquires and who owns the permit* changes on
  the poll side.

A poll branch that is a `Bind` chain with a poll leaf mid-chain acquires its permit at each
poll leaf's own establishment (each `EffectPoll` owns its own permit lifecycle) — correct by
construction. Refining mixed-chain routing (a nested blocking effect on a poll-rooted branch)
stays the later-slice question of §2.6; out of scope here.

#### Offsets read (the cross-crate agreement — designed-in)

The poll-node layout is baked by the backend's poll-construction arm (`/design backend` owns
`design/backend/io-trampoline.md §12/§13`) and READ by this trampoline. The agreement is
stated on both sides so the write/read offsets cannot silently drift:

| Field | Abs offset | int read site | Backend write site (sibling /design) |
|---|---|---|---|
| state-closure ptr | **24** (`FIELD_0_OFFSET`) | `await_poll_node` (`read_node_field`) | poll node field 0 |
| `token` (u64) | **32** (`FIELD_1_OFFSET`) | `read_resource_token` (IO_TAG_EFFECT_POLL arm) | poll node `field_offset(1)` |
| `capacity` (i64) | **40** (`FIELD_1_OFFSET + 8` = `field_offset(2)`) | `read_capacity` (`POLL_CAPACITY_ABS_OFFSET`) | poll node `field_offset(2)` |

S95 already reserved offsets 32/40 at sentinel; S96 only changes the baked **values** from
sentinel to live `(token, capacity)` — **no offset moves**, append-only. A change to any of
these offsets is an `ABI_VERSION` bump (§2.5 note).

#### Byte-identical-when-feature-off

Everything in this section is `concurrency-runtime`-gated. **Feature-off:** no
`IO_TAG_EFFECT_POLL` node is ever constructed (the backend poll-construction arm is gated, §4),
so no `EffectPoll`, no permit acquire, no pool — byte-identical to v6. The poll-node capacity
slot (offset 40) is baked only by the gated arm; the sync stepper never reads it. `--link`
links no executor and no pool (§1).

### 2.10 Testability seams (/dev unit + /qa e2e)

| Seam | Tier | What it pins |
|---|---|---|
| node-read `(token, capacity)` carrier | intrinsics unit | a node built by `effect_on_resource_with_capacity(T, N, f)` reads back `token == T` (offset 16) + `capacity == N` (offset 32); `effect_on_resource(T, f)` reads `capacity == 1`; **append-only** — the fn-name handle still at offset 24 |
| `AcquirePermit` over a fixture pool | intrinsics unit | capacity N: N acquires return `Ready`, the (N+1)th `Pending` until a `Permit` drops |
| **capacity-N parking** (S95: **blocking carrier**) | qa e2e | a **blocking** effect declaring `token T`, `capacity N` (via `effect_on_resource_with_capacity` on a blocking effect), with N+1 `Par` branches ⇒ the (N+1)th completes only after one frees; strand stream shows `TokenParked → TokenAcquired`. **Blocking-carrier only this sprint** — admission wraps both partitions (§2.6), but live poll-shape capacity-N is S96 (see §2.8 "S95 demo scope") |
| **distinct-token overlap** (poll/reactor) | qa e2e | N poll-shape effects on **distinct** tokens overlap on the reactor (≈max(delay) not sum). This is the slice-2 reactor mechanism — the poll side proves distinct-token overlap |
| **acquire-around-poll capacity-N** (S96: **poll carrier**, §2.9) | qa e2e | a **poll-shape** effect declaring `token T`, `capacity N` (live `(token, capacity)` baked at offset 32/40), with N+1 `Par` poll branches ⇒ the (N+1)th establishes (first `EffectPoll` poll) only after one of the first N reaches `Ready`; the permit is held across each leaf's establish→`Pending`→`Ready` arc; strand stream shows `TokenParked → … → TokenAcquired` |
| **permit released on `Ready`** (S96, §2.9) | intrinsics unit | an `EffectPoll` carrying a `Some(Permit)` on a full token: when its poll-fn returns `CPoll::Ready`, the permit is dropped **before** `TaskPoll::Ready`, freeing the slot + waking the front parked waiter (assert the next `AcquirePermit` resolves immediately after the leaf's `Ready`) |
| **permit released on future-drop** (S96, **the A→C contract**, §2.9) | intrinsics unit | an `EffectPoll` carrying a `Some(Permit)` that is **dropped while still `Pending`** (never reaches `Ready`) releases the permit (assert a parked `AcquirePermit` on the same token resolves after the drop). This is the cancellation/timeout/race-lost guard Chunk C exercises — **no permit leak** |
| **no double-release** (S96, §2.9) | intrinsics unit | after a `Ready` release (`Option::take`), dropping the `EffectPoll` is a no-op (slot count incremented exactly once across the `Ready`-then-drop sequence) |
| **within-token order** | intrinsics unit + qa e2e | same-token **capacity-1** effects run serial **and** in source order (an ordered-append / admission-witness leaf); capacity ≥ 2 promises no order |
| **capacity-mismatch reconciliation** | intrinsics unit | two effects on one token with different capacities ⇒ the semaphore is sized by the **first** value (never resized), and a `TokenCapacityMismatch` strand event is emitted |
| **two-pool overlap** (slice 6) | qa e2e | a mixed blocking + poll-shape `Par` overlaps on **both** pools (≈max not sum); the 3 RED guards (`resource_serial_diff_token_parallelizes`, `auto_io_independent_diff_token_parallelizes_e2e`, `auto_io_par_grouping_uniform_across_modes`) flip green |
| **byte-identical-off** | qa e2e + int unit | feature-off: no `IO_TAG_EFFECT_POLL` / no pool constructed; the v6 rayon `SerialGroup` path is unchanged and blocking-`Par` parallelizes |
| **`--link` no executor** | qa e2e | the linked binary links no mio/futures/pool (the `dep:`-gated optional-dep guarantee, §1) |
| **launch-and-continue returns immediately** (S96 B, §2.11) | qa e2e | an accept loop with a detached `(do (handle-conn conn) (serve listener))` keeps accepting **without** waiting for the handler — N connections all in flight at once (≈max not sum), result of the launched arm never consumed; strand stream shows `StrandLaunched` for each handler under the root accept strand |
| **panicking handler → server lives** (S96 B, §2.12) | qa e2e | a handler strand that panics (or produces a runtime error) is caught by the supervisor → `StrandFailed` emitted, the request dropped, **the accept loop continues serving** the next connection (never aborts the drive); a subsequent good request still succeeds |
| **supervisor catches both panic and runtime-error** (S96 B, §2.12) | intrinsics unit | a supervised strand future whose body (i) `panic!`s and (ii) sets the runtime-error slot are BOTH caught (`catch_unwind` + `take_runtime_error` at the completion boundary) → policy applied, no unwind escapes the executor, the executor keeps draining |
| **global admission budget bounds in-flight strands** (S96 B / gate (d), §2.13) | qa e2e | with global degree D, the (D+1)th launch **parks the accept loop** (admission-park, `GlobalBudgetParked`) until a strand completes and frees a global permit (`GlobalBudgetReleased`); at no point are more than D handler strands concurrently in flight (saturate-not-oversaturate) |
| **degree throttle `min(capacity, degree)`** (S96 B / gate (d), §2.13) | intrinsics unit | a token with node-read capacity N sized under reactor degree d < N admits only d concurrently (the (d+1)th parks); with d ≥ N it admits N (capacity binds) — the slot is sized `min(capacity, degree).max(1)` |
| **strand-drop releases its permits** (S96 B, the A→C volume consumer, §2.14) | intrinsics unit | dropping a supervised strand future (panic-after-catch / shutdown) drops its in-flight `EffectPoll`(s) → their `Option<Permit>` drop-glue releases the per-token permit (§2.9) AND the strand's global-budget `Permit` releases → a parked acquire / a parked launch proceeds (no permit leak under volume) |
| **`race` picks the winner, drops the loser** (S96 C, §2.15) | qa e2e | a `race` of two poll leaves with different delays resolves to the **faster** one's value; the slower (loser) branch is dropped — strand stream shows `StrandCancelled { reason: RaceLost }` for it |
| **race-lost releases the loser's permit** (S96 C, the A→C contract VERIFIED, §2.15/§2.9) | intrinsics unit | a `race` whose loser holds a `Some(Permit)` on a full token: when the winner resolves, the loser drops → its `Option<Permit>` drop-glue releases the permit → a parked `AcquirePermit` on that token resolves (no leak). This is gate (a) requirement 1 verified at the combinator |
| **finding #3 — drop deregisters reactor interest** (S96 C, §2.16) | intrinsics unit | a `Pending` `EffectPoll` that armed **real fd** interest, when dropped (race-lost / cancelled), removes its `fd_waiters` entry + mio-deregisters (assert `!reactor.has_waiters()` / the entry is gone after drop) — no waiter leak under volume |
| **finding #4 — drop-while-parked frees the next live waiter** (S96 C, §2.17) | intrinsics unit | `AcquirePermit` A and B both parked on a full capacity-1 token (A in front); drop A (cancel); a `Permit` release then wakes **B** (the next live waiter), not A's stale waker → B acquires (no lost-wakeup, no unclaimable permit). Also: capacity-1 source order preserved across a mid-queue cancel |
| **`sleep` resumes at its deadline** (S96 C, §2.18) | intrinsics unit | a bare `sleep d` poll leaf returns `Pending` then `Ready(Unit)` after ≈`d` (timer armed on the reactor; no thread-per-sleep) |
| **`timeout` fires + cancels the slow `io`** (S96 C, §2.18) | qa e2e | `timeout d io` where `io` exceeds `d` ⇒ `None` and the `io` branch is cancelled (its permit/interest released); where `io` completes within `d` ⇒ `Some v` and the `sleep` is cancelled |
| **graceful shutdown cancels outstanding strands** (S96 C, §2.19) | qa e2e | with N supervised strands in flight, a shutdown signal stops accepting and (hard) `clear()`s the stragglers → each emits `StrandCancelled { reason: Shutdown }` and releases its permits/interest (no leak); graceful drain lets them finish first |
| **frame-guard frees a dropped branch's sub-tree** (S96 C, §2.15.1) | intrinsics unit | dropping a mid-flight trampoline branch future `consume_io_tree`s its unconsumed `current` + `cont_stack` (no heap leak); normal finish disarms the guard (no double-free) |

> **Section order note.** §2.10 is the seam *summary* (it forward-references the slice-5/4
> seams); §2.11–§2.14 below are the slice-5/4 *design* the Chunk-B refresh adds. They are part
> of §2 (the reactor interior), not a new top-level section.

### 2.11 Launch-and-continue — the detached-launch node (slice 5, S96 Chunk B)

**Authority: `sprints/SPRINT.md` Phase-2 gate (b) + `effect-concurrency.md` §6 (`launch-and-
continue → spawn the handler future, don't await; JoinSet for supervision`) / §16 (the
reference workload).** Launch-and-continue is a **fire-and-forget effect launch**: a detached
strand with **no join point**. It arises in the §16 accept loop, where the handler's result
is *discarded* and the loop continues:

```clojure
(defn serve [listener]
  (bind! [conn (accept listener)]
    (do (handle-conn conn)        ; ⟂ IO Unit, result UNUSED, tokens disjoint from the next accept
        (serve listener))))       ; tail call → next accept, WITHOUT waiting for handle-conn
```

### How it differs from the structured fork-join `Par`

| | `Par` (§2.6 — structured fork-join) | Launch-and-continue (§2.11 — detached) |
|---|---|---|
| Join point | **Yes** — the bind continuation does not run until **all** branches join; results collected into the merge buffer (`run_par_node_async`) | **None** — the launched arm's result is never consumed; the continuation runs **immediately** |
| Result | the branches' values, merged by binding index | discarded — the node yields `Pure Unit` to the continuation at once |
| Error path | worker-side `take_runtime_error` → join-side **re-raise** into the parent (the expression's dynamic extent, §2.6 item 4) | worker-side capture → **supervisor** (no parent to re-raise into — §2.12) |
| Lifetime | bounded by the expression (all branches complete before it returns) | **detached-but-supervised** — outlives the spawning expression; owned by the supervisor; never joined by pure code |
| Backpressure | bounded by the §2.8 per-token pool | bounded by the **global** admission `Semaphore` (§2.13) — unbounded fan-out is a memory-exhaustion hazard |

### Lowering — a new detached-launch IO node (backend↔intrinsics seam)

The backend's auto-IO independence analysis (the same machinery that yields `Par` branches)
detects the launch shape — *a `do`/sequencing whose first arm is an `IO` whose result is
discarded and is data-independent of the continuation* — and bakes a **detached-launch node**
(proposed tag `IO_TAG_LAUNCH`, the next free IO tag after `IO_TAG_EFFECT_POLL = 4`). The node
carries one field: the launched IO sub-tree pointer. **This is a backend↔intrinsics in-process
convention (a pinned const, the `IO_TAG_EFFECT_POLL` precedent — no `cranelisp-types` edge, no
ABI bump, the gate-(b)/public-API ruling); the tag value + the bake + the independence
detection are `/design backend`'s — coordinate the const + the field offset there.** This doc
designs the **intrinsics interior**: how the trampoline interprets the node.

The async stepper (`run_io_trampoline_inner_async`) gains a `IO_TAG_LAUNCH` arm:

1. **Acquire a global-budget permit** for the new strand (`env.acquire(GLOBAL_BUDGET_TOKEN,
   global_degree, child_strand)` — §2.13). If a global permit is free ⇒ proceed; **if
   exhausted ⇒ this arm `.await`s the acquire (admission-park), parking the accept loop
   itself** until a strand completes (the backpressure point — §2.13 / §14 step 4).
2. **Mint a child strand id** (`next_strand()`), emit `StrandLaunched { strand, parent }`.
3. **Transfer ownership of the launched sub-tree** to a supervised strand future and **push it
   into the supervisor** (`env.supervisor.spawn(sub_tree, child_strand, global_permit)`, §2.12).
   The global-budget `Permit` is **moved into** the supervised strand (it owns it for its whole
   lifetime — RAII, released on completion/drop, exactly mirroring the §2.9 `EffectPoll` permit).
4. **Yield `Pure Unit` as the node's result** immediately — the continuation (`serve listener`)
   proceeds at once. The launch does **not** `.await` the strand.

> **RC ownership of the launched sub-tree (flag for /dev + /design backend).** The main
> trampoline is non-consuming of the caller's tree (§ the `run_io_trampoline` RC-balance
> note); the detached sub-tree, however, **outlives** the `IO_TAG_LAUNCH` node's
> interpretation and must **not** be freed by the main `consume_io_tree` — its ownership
> **transfers to the supervised strand**, which `consume_io_tree`s it on completion. Coordinate
> with `/design backend` on how the launch node holds its sub-tree so the transfer is an
> owned-field move (the launch node releases its hold; the strand takes it), not a double-free
> or a leak. This is the one new RC subtlety slice 5 introduces.

**Spec interaction (`/spec`, FIXME 0447 first half — NOT authored here, flagged).** The
launch arm is an *un-joined* strand; its TCO + observational-equivalence interaction with the
accept loop's tail call is the §10.12/§12.5 surface `/spec` actions this sprint. From the
reactor's side: the tail call `(serve listener)` is the continuation that runs after the
`Pure Unit`, so the accept loop is an ordinary trampoline tail-recursion (no native stack
growth — IO is reified data, §6 of effect-concurrency.md); the detached strands accumulate in
the supervisor, bounded by the global budget.

### 2.12 The supervisor — a `JoinSet`-equivalent on the reactor (slice 5, S96 Chunk B)

**Authority: `sprints/SPRINT.md` Phase-2 gate (b) + `effect-concurrency.md` §10 (supervisor
semantics) / §11 (supervisor drops vanish without the sink).** A detached strand that panics
has **no join point** for its error to ferry to — the S95 fork-join ferry's *join-side
re-raise has nowhere to land*. Gate (b)'s ruling: **reuse the worker-side capture verbatim;
replace the re-raise with a supervisor handle** that **owns** each detached strand, catches
its outcome, and applies the §10 per-effect-kind policy — never re-raising into a nonexistent
parent, never aborting the server.

### The handle — a single-threaded `FuturesUnordered`

The supervisor is the **`JoinSet`-equivalent**: a single-threaded `FuturesUnordered<Pin<Box<dyn
Future<Output = ()>>>>` of **supervised detached-strand futures**, owned by the reactor.
Constructed **single-sited in `block_on_reactor`** alongside the `Reactor`, `HostCtx`, and
`TokenPool` (§6.2 — divergence-proof by the intrinsics-hosting argument; int grows no parallel
supervisor builder), and reached through `ReactorEnv` as `supervisor: &'h Supervisor` (interior
mutability, single-reactor-thread — same pattern as the §2.8 pool). `FuturesUnordered` is
chosen because it is exactly the single-threaded concurrent-future set tokio's `JoinSet` is for
a multi-thread runtime: `push` is `&self` (so the `IO_TAG_LAUNCH` arm can add a strand while the
set is being driven), it is `Unpin`, and draining it (`poll_next_unpin`) drives all member
strands concurrently and removes each as it completes. Because the **outcome handling lives
inside the supervised future** (below), the set's item type is `()` and the executor only has to
**drain** it — no per-item outcome plumbing in the drive loop.

```rust
// sketch — the intrinsics interior, /dev authors the real code
pub(crate) struct Supervisor {
    strands: RefCell<FuturesUnordered<Pin<Box<dyn Future<Output = ()> + 'h>>>>,
    policy: SupervisorPolicy,   // reactor-construction config (int src/), default LogAndDrop
}
```

### The supervised-strand wrapper — catch + §10 policy + RAII release

Each launched sub-tree is wrapped so **every way it can end is caught** and the policy applied
inside the future (so a panic can never unwind out into the executor and abort the drive):

```rust
async fn supervised(sub_tree: i64, env: &ReactorEnv<'_>, strand: StrandId,
                    _global_permit: Permit, policy: SupervisorPolicy) {
    // catch_unwind around the strand body so a Rust-level panic (bad tag, RC mid-panic, a
    // handler `(panic …)`) is caught, NOT propagated into the executor:
    let outcome = AssertUnwindSafe(async {
        let r = run_io_trampoline_inner_async(sub_tree, env, strand).await;
        // reuse the S95 worker-side CAPTURE (gate (b)) at the completion boundary —
        // SYNCHRONOUS with the resolve (no .await between), so no other strand interposes:
        let err = crate::panic::take_runtime_error();
        (r, err)
    }).catch_unwind().await;

    match outcome {
        Ok((_r, None))      => emit_strand_event(StrandCompleted { strand }),
        Ok((_r, Some(msg))) => apply_policy(policy, strand, msg),   // runtime error
        Err(_panic)         => apply_policy(policy, strand, "<panicked>".into()),
    }
    crate::drop::consume_io_tree(sub_tree);   // the strand owns its detached sub-tree (§2.11)
    // `_global_permit` drops HERE → frees a global-budget slot → wakes a parked launch (§2.13).
}
```

**The §10 policy — 500 + log + drop, split by layer.** `apply_policy` at the **intrinsics**
layer does **catch + record + drop**: emit `StrandFailed { strand, message }` to the strand
sink (the `/strand` dev surface + `/qa`'s panic-survival assertion read it) and drop the strand
(free its sub-tree, release its budget permit). It **never** re-raises and **never** aborts the
drive. The **"500 response to the client"** is the *application/platform* mapping layered on
top — the web serve-loop / handler decides what a dropped request returns to the socket (a
default 500, or the handler's own `catch`); the intrinsics supervisor does not synthesize HTTP.
The per-effect-kind *choice* (what a failure of THIS kind maps to) is the
`SupervisorPolicy` — a **reactor-construction config** supplied by int `src/` (gate (b): "a
scheduler-/platform-declared default, so it stays out of the pure language"). The minimal
default is `LogAndDrop`; the web "500" mapping is supplied by the serve-loop. **Coordinate the
`SupervisorPolicy` shape + the "500-on-dropped-connection" mapping with the sibling /design
platform (web serve loop) + /design int src/ (reactor-construction config) surfaces** — the
reactor owns the *mechanism* (catch/record/drop), the platform/int own the *response mapping*.

### Driving the supervisor — the executor loop extension

`block_on_reactor`'s drive loop currently polls one **top** future (the accept loop) and turns
the reactor between polls. It is **extended** to also drain the supervisor each iteration so the
detached strands make progress concurrently with the accept loop:

1. poll the top future (the accept loop / `serve`);
2. **drain the supervisor**: `while let Poll::Ready(Some(())) = supervisor.poll_next(cx) {}` —
   drives every member strand, removing each as it completes (a completed strand has already run
   its policy + released its permit + freed its sub-tree inside its own body);
3. `turn(MAX_TURN_BLOCK)` as today.

The borrow of the `RefCell<FuturesUnordered>` is taken **only** for the synchronous
`poll_next` call and dropped before any `.await` (single-thread invariant — no borrow held
across a suspension; the `IO_TAG_LAUNCH` arm's `push` is `&self` and momentary). **Liveness:**
the existing `pending_bridges`/`has_waiters` no-progress logic (§2.4) extends to "**a non-empty
supervisor is also progress**" — `block_on_reactor` returns on the **top** future's completion
(the server's `main`/accept loop), and outstanding supervised strands are then dropped at drive
end (their permits + interest release on drop — §2.14); the `MAX_TOTAL_BLOCK` no-progress cap
must NOT fire while the supervisor is non-empty (the same exemption `pending_bridges > 0`
already gets — a server with live handlers is legitimately busy, not stuck).

> **The §10 honest caveat stands.** For detached strands there is **no "first error"
> ordering** — each supervisor action is independent (gate (b)). A further sharp edge the
> shared-thread-local capture introduces: `take_runtime_error()` reads a **single reactor-
> thread slot** shared by all concurrently-running detached strands; capturing it
> *synchronously at each strand's own completion boundary* (above) keeps the common case
> correct, but a runtime error ferried by one strand's blocking branch (`run_blocking_branch`'s
> `set_runtime_error`, first-writer-wins) could in principle be mis-attributed to a sibling
> strand that completes first. This is consistent with §10's named non-determinism, but it is a
> **layered concern** (per the cross-skill defect-handoff discipline): if mis-attribution is
> observed, the structural fix is a **per-strand error channel** (each supervised strand carries
> its own `oneshot`/slot rather than reading the global one) — flagged for /qa to pin with a
> narrow repro and for a follow-up if it bites; not built speculatively (Principle 6).

### 2.13 Backpressure / admission budget (slice 4, S96 Chunk B — gate (d) / FIXME 0442)

**Authority: `sprints/SPRINT.md` Phase-2 gate (d) + `effect-concurrency.md` §5 (the
descriptor: capacity vs *degree*) / the FIXME 0442 ruling (TWO substrate-bound mechanisms, ONE
shared *concept*).** Slice 4 is the I/O *degree* throttle. Per 0442 it is **not new admission
machinery** — it is two parameterizations of the **existing §2.8 permit-counter** (`TokenPool`
/ `TokenSlot` / `AcquirePermit` / `Permit`), reused wholesale:

### (1) `degree` on the per-token pool — `effective permits = min(capacity, degree)`

*capacity* is the **platform's** per-resource ceiling (rides on the node, §2.8); *degree* is
the **program's** chosen in-flight throttle (policy — memory / fairness), always ≤ capacity.
The effective per-token limit is `min(capacity, degree)`.

- **Where `degree` comes from.** It is a **program/reactor-construction knob** (the policy
  axis), threaded into `TokenPool` at construction (`block_on_reactor`) by int `src/`. The
  per-resource override carrier is the descriptor's already-reserved, now-core
  `ConcurrencyDescriptor.global_budget` field (the gated-carrier 0442 names — node-read
  alongside `(token, capacity)` when a resource declares its own degree). **Coordinate with
  /design int src/ (the construction knob) + /design backend (node-read of `global_budget` if a
  per-resource degree is baked).** No `cranelisp-types` edge (the field exists), no ABI bump.
- **Mechanism — sizing, not a new structure.** The **only** change to §2.8: when a `TokenSlot`
  is created (first-writer-wins, `AcquirePermit::poll`), size it `permits = capacity = min(
  node_capacity, degree).max(1)` instead of `node_capacity`. Everything else — park on a full
  token, FIFO release, `TokenAcquired`/`TokenParked`/`TokenReleased` — is **unchanged**. The
  over-budget action is **admission-PARK** (the existing async suspension), NOT inline-fold
  (that is the CPU axis — a separate mechanism per 0442; the reactor never folds).

### (2) The global admission `Semaphore` — the detached-fan-out memory bound

A single **global** reactor-thread admission `Semaphore` bounds **total in-flight detached
strands** (the launch-and-continue memory bound, §2.11 / §14 step 4). It **reuses the same
`AcquirePermit`/`TokenSlot`/`Permit` machinery** via a reserved well-known token
`GLOBAL_BUDGET_TOKEN` (a sentinel that is never a resource token — e.g. `u64::MAX`), **pre-sized
to the global degree at pool construction** (not first-writer-wins — it is program policy, set
once by int `src/` at `block_on_reactor`). The `IO_TAG_LAUNCH` arm acquires a global permit
**before** spawning a strand (§2.11 step 1):

- a free global permit ⇒ the strand spawns; the `Permit` is **moved into** the supervised strand
  (owned for its lifetime, released on completion/drop — §2.12 / §2.14);
- an exhausted global budget ⇒ the launch arm **parks** (admission-park) — **the accept loop
  itself suspends** until a strand completes and frees a global permit, which FIFO-wakes the
  parked launch. This is "backpressure on accept under load" (§16): the server stops accepting
  new work when in-flight handlers hit the global bound — **saturate-not-oversaturate**.

New strand events for the global gate (§3): `GlobalBudgetParked` / `GlobalBudgetAcquired` /
`GlobalBudgetReleased` (or, equivalently, the existing `Token*` events keyed on
`GLOBAL_BUDGET_TOKEN` — distinct variants are clearer for the `/strand` dev surface; the enum is
`#[non_exhaustive]`).

**Why this is not a unified abstraction (0442 honoured).** The two backpressure parameters and
the CPU spark budget share only the **permit-counter shape**, realized once per substrate — the
reactor's lock-free single-thread permit map here; a cross-thread `AtomicIsize` on rayon for the
CPU axis. The over-budget actions diverge irreducibly (I/O admission-parks; CPU folds inline).
This design touches **only** the reactor's I/O side — `min(capacity, degree)` + the global gate,
both on the existing permit map — and adds no shared type with the CPU counter.

### 2.14 Interaction with acquire-around-poll (§2.9) + the A3 RAII Permit — the first VOLUME consumer

**Confirmation gates (b) + (d) HOLD post-cutover.** The Chunk-A single-ABI + single-trampoline
cutover collapsed `drive_io` to one async body and made the reactor unconditional/eager-cheap,
but it left **untouched** the substrate both gates rely on: the §2.8 permit map
(`TokenPool`/`TokenSlot`/`AcquirePermit`/`Permit`, reactor.rs), the error-ferry
(`take_runtime_error` → `set_runtime_error`, used in `run_blocking_branch`), the §7 wakeable
bridge (`ExecutorWaker`/`bridge_waker`/`pending_bridges`), and the §2.9 RAII `Permit`. The only
adaptation slices 5/4 require of the substrate is **always-present** (no longer feature-gated)
`ReactorEnv` — which the cutover already delivers (single trampoline, reactor always linked).
So:

- **Gate (b)** — supervisor reuses the worker-side `take_runtime_error` capture (intact) + a
  new `JoinSet`-equivalent (`FuturesUnordered`) built on the intact substrate. **HOLDS.**
- **Gate (d)** — degree + global gate reuse the intact §2.8 permit-counter; the
  `ConcurrencyDescriptor.global_budget` carrier is now core (cutover ungated the descriptor) and
  still present. **HOLDS.**

No `/arch` FIXME is warranted — the gates were specified against the §8.1 pool / error-ferry /
wakeable bridge, all of which survived the cutover verbatim.

**The supervisor drops detached strands — and is the FIRST volume consumer of the §2.9 drop
path.** A supervised strand is dropped on three paths: (a) completion (its `supervised` body
ran to the end — its `EffectPoll`s already reached `Ready` and eager-released, §2.9 step 5);
(b) the §10 policy after a panic/runtime-error (the body finished, caught); (c) graceful
shutdown (Chunk C — outstanding strands dropped mid-flight). On every path the strand future's
drop releases — **for free, via the A3 RAII `Permit` drop-guard**:

- any in-flight `EffectPoll`'s `Option<Permit>` per-token permit (§2.9 release-on-drop), and
- the strand's **global-budget `Permit`** (§2.13, owned as a field — same RAII pattern).

This is exactly the A→C contract designed in §2.9 paying off: **the supervisor adds zero
permit-release plumbing** — binding both permits' lifetimes to the strand future makes "released
when the strand ends" structural. Confirmed: the §2.9 drop-release path is correct for the
volume case (each strand's permits release on its own drop, independent of siblings).

### Chunk-C prerequisites that the supervisor's VOLUME starts to bite (the two A3-review findings)

> **STATUS (S96 Chunk C): both findings are now DESIGNED — #3 in §2.16, #4 in §2.17.** This
> sub-section is the original Chunk-B *diagnosis* (where each bites); the *designs* live below in
> §2.16/§2.17 and the `/dev` order in §5.2. Read on for the bite-analysis, then §2.16/§2.17 for
> the resolutions.

The A3 adversarial review (`sprints/SPRINT.md` Chunk-C-design-prerequisites box) flagged two
findings latent in the §2.8/§2.9 machinery, memory-safe for one-shot `--run`/REPL but biting
under **volume cancellation in a long-running reactor**. The supervisor is the first volume
consumer, so noting where each bites in **Chunk B** vs strictly **Chunk C**:

1. **Active fd-interest deregistration on `EffectPoll` drop (A3 finding #3) — TOUCHES Chunk B
   on the panic path.** A dropped in-flight `EffectPoll` that had armed fd interest leaves its
   `fd_waiters` entry + live `mio` registration + `OwnedCWaker` until that fd next readies (a
   within-drive leak, not a deadlock — `block_on_reactor` returns on the TOP future, not on
   `has_waiters`). **In Chunk B this fires on the §10 panic path**: a handler that panics
   *while a poll leaf is parked* (e.g. mid-`read`) has its `EffectPoll` dropped by `catch_unwind`
   → if that leaf had armed fd interest, the entry leaks until the (now-orphaned) fd readies. In
   a **long-running server loop** these accumulate per panicking request. The §2.9-named "no
   `Drop for EffectPoll`" reframing (permit-only release; stale wake harmless) is correct for the
   *permit* but does NOT remove the *reactor-interest* leak. **Disposition:** the literal active
   deregistration the plan named — an `EffectPoll`-owned reactor-registration handle whose drop
   removes the `fd_waiters`/`timer_waiters` entry + `mio`-deregisters — is **Chunk C** work
   (volume cancellation), but it has a **Chunk-B instance** (the panic path). Recommend: assess
   in Chunk B whether the panic-path leak is bounded-acceptable for the demo (a panicking handler
   is rare; one orphaned `fd_waiters` entry per panic until that fd readies) **or** pull the
   active-dereg forward. Recorded in §2.9 as: *"Chunk A — permit-only release; active reactor-
   interest deregistration deferred to Chunk C (needed for volume cancellation); a Chunk-B
   instance exists on the supervisor panic path."*

2. **`AcquirePermit` cancellation stale-waker lost-wakeup (A3 finding #4) — strictly Chunk C.**
   If an `AcquirePermit` is dropped **while parked** (a future cancelled *before* it acquires),
   its waker stays in `slot.waiters`; a later `Permit`-release `pop_front()`s that **stale**
   waker (a no-op), the freed permit goes unclaimed, and the next live waiter starves
   (lost-wakeup). **In Chunk B this does NOT fire**: a detached strand is never dropped *while
   parked on an acquire* — the supervisor lets each strand run to completion, then drops it (its
   acquires have all resolved). It bites only under **Chunk C** (graceful shutdown / `race` /
   `timeout` dropping a strand that is *parked* on a per-token OR global-budget acquire).
   **Disposition:** Chunk C needs either `Drop for AcquirePermit` (remove own waker on cancel) or
   pop-until-live release (skip dropped/`will_wake`-stale wakers). Out of scope for Chunk B;
   flagged here so the global-budget `AcquirePermit` (§2.13) is co-reviewed when Chunk C adds it.

Both findings live in the pool/acquire machinery §2.9 deliberately left unchanged — latent in
S95, made live by volume (the supervisor) / cancellation (Chunk C). They are Chunk-C design, not
A3 reworks; the Chunk-B panic-path instance of #1 is the only one that may need attention this
chunk.

### 2.15 The combinator runtime — `race` / `select` + cancellation = future-drop (slice 7, S96 Chunk C)

> **RECONCILIATION (S96 C3 as-built — supersedes the node-seam draft below).** The node
> layout was settled by `/design backend` (`io-trampoline.md §16`, the authority for the bake)
> as **ONE tag, `IO_TAG_SELECT = 6`**, a thin single-field node whose field-0 is a **`Vec (IO a)`
> branch carrier** (the `[..]` literal *is* a `Vec`; `race a b` builds a 2-element branch `Vec`
> and wraps the **same** node). There is **NO `IO_TAG_RACE`, NO variadic-slot layout, and NO
> move-out / `0`-sentinel write-back** — the proposed-const table + "move them out" steps below
> are the pre-decision draft and do NOT describe the landed code. The Select node **owns the
> branch `Vec` for the whole tree lifetime** (select never detaches); `consume_io_tree`'s
> `IO_TAG_SELECT` arm reclaims it via `consume_vec_with(field0, consume_io_tree)` — every branch
> (winner + losers) freed exactly once, no per-branch backend RC (`io-trampoline.md §16.5`). The
> runtime arm is **`io::run_select_node`**: read the branch ptrs **by raw pointer (no RC)** off
> the `Vec`, mint a child strand + build a branch future per sub-tree, race with
> `futures::future::select_all` (which re-polls ALL pending branches each turn), drop the losers
> (= cancellation) after emitting `StrandCancelled { reason: RaceLost }`, and return the winner.
> **The §2.15.1 `TrampolineFrame` cancellation drop-guard needs NO C3 change**: with no
> move-out, every branch sub-tree ROOT is non-fresh (owned by the `Vec`), so the C2 fresh-only
> guard already does exactly the right thing — it frees only the fresh continuation-produced
> in-flight nodes a cancelled branch held, leaving the non-fresh roots for `consume_io_tree`.
> The "C3 wires the non-fresh moved-out branch-root RC balance" task framing is therefore MOOT
> under the no-move-out list-carrier model. The drop-path release plumbing below (§2.16/§2.17
> permit + reactor-interest deregistration, and the C3 woken-then-cancelled permit-FORWARDING
> in `Drop for AcquirePermit`) is accurate and load-bearing for cancellation at volume.

**Authority: `sprints/SPRINT.md` Chunk C (slice 7) + `effect-concurrency.md` §9 (the control
half — the combinator layer).** Chunk C lands the **explicit control surface**: the in-language
combinators `race` / `select` (`timeout` derived, §2.18) that branch on *when* sub-computations
complete, plus **structured cancellation** — the consequence of losing a race or leaving a
scope. Per §9 these are **ordinary typed functions constructing trampoline-interpreted IO-ADT
nodes** (the same mechanism class as `Par` / launch-and-continue) — **NOT special forms, NOT
platform effects**. The entire control vocabulary lives in the runtime; platforms never see it
(the thin-platform thesis holds even for the explicit surface). The irreducible primitive set
the trampoline must interpret is **`race` / `select` + cancellation**; everything else derives.

> **Post-cutover framing.** Chunk C is authored against the **single-ABI, single-trampoline,
> lazy-reactor** end-state the A4c cutover delivered (both `concurrency`/`concurrency-runtime`
> features RETIRED — the reactor IS the runtime; a pure-blocking program constructs no mio
> `Poll`). There is **no feature gate** on the combinator runtime and **no byte-identical-off
> invariant** to police — the off-state is gone. The lazy reactor init is triggered by the first
> poll-shape leaf / `Par` / **combinator** node scheduled (a combinator that races only blocking
> branches still needs the reactor to drive the concurrent set). The `IO_TAG_RACE`/`IO_TAG_SELECT`
> tags are pinned in-process consts (the `IO_TAG_LAUNCH` precedent) — **no `ABI_VERSION` bump,
> no `cranelisp-types`/`cranelisp-platform` public-api touch** (SPRINT.md "Slice 7 combinators /
> cancellation: NO ABI bump").

#### The node seam (backend↔intrinsics — sibling /design backend owns the bake)

The combinators lower to two new IO node tags (the next free after `IO_TAG_LAUNCH = 5`):

| Tag | Proposed const | Node shape (field layout — /design backend owns) | Runtime arm |
|---|---|---|---|
| `IO_TAG_RACE` | `6` | two owned branch sub-tree ptrs (field 0 = left, field 1 = right) — the binary `race` | `run_race_node` (§ below) |
| `IO_TAG_SELECT` | `7` | a variadic owned branch-vector (the `read_par_branches`-shaped count+slots layout `Par` already uses) — `select : List (IO a) -> IO a` | `run_select_node` (§ below) |

**This is a backend↔intrinsics in-process convention** (a pinned const + a node bake + the
codegen that detects a `race`/`select` *application* and lowers it to the node — the same class
as `Par`/`IO_TAG_LAUNCH`). **The tag values, the node field layout, the per-branch owned-field
shape, and whether new `Expr`/`MonoExpr` variants are warranted** (the `LaunchContinue` precedent
— FIXME 0466 added a dedicated marker variant rather than a discriminator) are **`/design
backend`'s** — coordinate the const + offsets + the cancel-time branch-ownership contract there
(the RC seam below). This doc designs the **intrinsics interior**: how the trampoline runs the N
branches, picks the winner, and **drops the losers** (the cancellation).

#### The runtime — a single-reactor-thread race over the branch futures

Both arms slot into the `run_io_trampoline_inner_async` dispatch loop (io.rs) exactly like the
`IO_TAG_PAR` / `IO_TAG_LAUNCH` arms:

```
t if t == IO_TAG_RACE   => run_race_node(current, env, strand).await,
t if t == IO_TAG_SELECT => run_select_node(current, env, strand).await,
```

`run_race_node` / `run_select_node` (io.rs):

1. **Read the owned branch sub-tree ptrs** off the node (race: fields 0/1; select: the variadic
   vector via the existing `read_par_branches`). **Move them out** of the node — write the `0`
   sentinel back into each consumed field — so the node's own drop glue does **not** double-free
   them; ownership transfers to the per-branch futures (the move-out contract, mirroring the
   `IO_TAG_LAUNCH` §2.11 step 3 / the launch sibling-doc §15.5). *(Coordinate the move-out + the
   node-drop arm with /design backend, as for launch.)*
2. **Mint a child strand per branch** (`next_strand()`, child of the race strand), so the
   `/strand` dump shows *"this race fanned out into these branches; this one won, the others were
   cancelled."* Emit a `StrandLaunched`-analogue is **not** wanted (these are not detached) — the
   branches are children of the awaiting race expression; the winner resolves into it, the losers
   emit `StrandCancelled` (§3) when dropped.
3. **Build one branch future per sub-tree** — `run_io_trampoline_inner_async(branch_ptr, env,
   child_strand)` (each a `Pin<Box<dyn Future<Output = i64>>>`), wrapped in the **cancellation
   drop-guard** of §2.15.1 so a dropped-mid-flight branch frees its unconsumed sub-tree.
4. **Race them on the one reactor thread** — a `futures::future::select` (binary `race`) /
   `FuturesUnordered::next` (variadic `select`) over the branch futures. The **first to resolve
   `Ready(v)` wins**; `v` is the node's result. This is the `select!` the §6 host-runtime map
   names — a single-threaded concurrent race, no thread-per-branch (the same substrate the
   reactor already runs `Par`/the supervisor on).
5. **DROP the losers.** When the winner resolves, the remaining branch futures are **dropped**
   (the `select`/`FuturesUnordered` losers go out of scope, or are explicitly `drop`ped before
   returning the winner's value). **The drop IS the cancellation** (§9: *"cancel is not a
   standalone combinator — it is the consequence of losing a race"*). Emit `StrandCancelled {
   strand: child, reason: RaceLost }` for each loser before/as it drops.
6. **Return the winner's value** to the continuation (the trampoline's `produced` for the node).

#### The unifying invariant — cancellation = drop, and every drop path releases cleanly

Dropping a loser branch future drops, transitively, every resource the partially-interpreted
branch held — and **this is exactly the A→C contract Chunk A built, now exercised** (gate (a)
requirement 1: the `Permit`-on-drop path is co-reviewed *here*). A dropped branch future is at
one of two suspension points, each with its release path:

- **parked on a per-token / global `AcquirePermit`** (mid-acquire, before it got its permit) →
  the `AcquirePermit` drops → **finding #4 (§2.17)**: it removes its own stale waker from the
  token's FIFO (no lost-wakeup);
- **awaiting an in-flight `EffectPoll`** (it holds a `Permit` and has armed fd/timer interest) →
  the `EffectPoll` drops → its `Option<Permit>` drop-glue releases the per-token permit
  (**§2.9**, Chunk A) **and** **finding #3 (§2.16)**: its reactor-registration handle drop
  actively deregisters the `fd_waiters`/`timer_waiters` entry + mio-deregisters (no waiter leak);
- **mid-step in the trampoline body** (between awaits) → the **trampoline-frame drop-guard**
  (§2.15.1) frees the unconsumed sub-tree (no heap leak).

So **every drop path — permit, fd/timer interest, FIFO waker, and the unconsumed IO sub-tree —
releases / deregisters cleanly.** This is the Chunk-C completion of the A→C RAII contract:
cancellation at volume (per-request `timeout`, `race` per connection, graceful shutdown over many
strands) neither **leaks** (findings #3 + the frame-guard) nor **lost-wakes** (finding #4).
Principle 20 (model invariants by representation) governs throughout: each resource's release is
bound to the drop of the value that owns it — no cancellation-specific teardown code path, no
"on cancel, remember to also free X" checklist; the ownership graph *is* the teardown order.

##### 2.15.1 The trampoline-frame cancellation drop-guard (the new RC subtlety)

A branch future is `run_io_trampoline_inner_async` over the branch sub-tree. Its async state holds
the loop's owned manual-RC pointers — `current: i64` (the live node) and `cont_stack: Vec<(i64,
bool)>` (pushed continuations) — which are **not** Rust-owned (they are raw heap-node addresses
under manual RC). On **normal completion** the loop consumes them as it steps (the existing
`dec_shallow_io` on `Bind`, the final value extraction). On **drop-before-completion** (a race
loser) the boxed future's drop tears down the async state machine but would **leak** the
still-live `current` + the un-popped `cont_stack` entries — the manual-RC nodes are never freed.

**Design: a frame drop-guard owning the in-flight pointers.** The trampoline loop's owned
pointers move into a small RAII `TrampolineFrame { current: i64, cont_stack: Vec<(i64, bool)> }`
whose `Drop` `consume_io_tree`s the live `current` and each remaining `cont_stack` continuation —
**run only if the future is dropped before `Step::Finish`**. On normal finish the frame is
**disarmed** (the value has been extracted and the stepped tree already balanced) so its drop is a
no-op — exactly the `Option`-take / "released exactly once" discipline §2.9 uses for the permit
(Principle 20: the "consumed-exactly-once" invariant is representable, not a flag to keep in
sync). This is the **one genuinely-new RC piece** Chunk C introduces, parallel to §2.11's launch
ownership transfer. **It is partly a backend seam** — the *per-branch* root ownership (the
move-out in step 1, and how `consume_io_tree` balances a partially-stepped tree against the
backend's emitted RC) must be **co-designed with /design backend** (who owns the node bake +
`io-trampoline.md`'s RC-balance contract). The intrinsics side owns the frame-guard; the backend
side owns the node's owned-branch fields + the cancel-time `consume_io_tree` arm. Until that
contract is pinned, this is the named coordination seam, not a settled mechanism.

> **Scope note — `race`/`select` only need the reactor; they do not need a new pool.** The
> combinator runtime reuses the executor, the `EffectPoll`, the `TokenPool`, the supervisor's
> `FuturesUnordered`-class concurrency, and the §2.9 RAII drop paths **verbatim**. Slice 7 adds
> **no new admission machinery** — it adds two trampoline arms, the frame drop-guard, and the
> two §2.16/§2.17 drop-path completions. Principle 6 (complexity has a budget): the irreducible
> primitive set is `race`/`select` + drop; `timeout` (§2.18), cancel-on-disconnect and graceful
> shutdown (§2.19) are all **compositions** of these, not new primitives.

### 2.16 A3 finding #3 — active reactor-interest deregistration on `EffectPoll` drop (slice 7, S96 Chunk C)

**Authority: `sprints/SPRINT.md` Chunk-C-design-prerequisites box, finding #3 + the A3 review
adjudication (`reactor.rs` review §3).** §2.9 (Chunk A) deliberately delivered **permit-only**
release on `EffectPoll` drop: a dropped in-flight `EffectPoll` releases its `Option<Permit>` but
does **not** deregister the reactor interest it armed — its `fd_waiters`/`timer_waiters` entry +
live `mio` registration + `OwnedCWaker` persist until that fd next readies (or for the whole
drive, if it never does — an fd that never readies does not self-clear; a timer entry self-clears
at its deadline). This is **memory-safe and benign for one-shot `--run`/REPL** (bounded by drive
end, and `block_on_reactor` returns on the **top** future, not on `has_waiters()` — so it is a
**leak, not a deadlock**), but under **Chunk C's volume cancellation in a long-running server
loop** (`race`/`timeout`/disconnect dropping in-flight poll futures per request, the drive never
ending) the `fd_waiters` entries + mio registrations accumulate **without bound**. The supervisor
panic path (§2.14) is the first place this bit (one orphaned entry per panicking handler);
cancellation makes it the common case.

#### The design — an `EffectPoll`-owned `ReactorInterest` RAII handle whose `Drop` deregisters

The fix is the literal active-deregistration the A3 §2B plan row named: bind the *reactor
interest's* lifetime to the `EffectPoll` future, exactly as §2.9 bound the *permit's*. The
`EffectPoll` gains a second RAII field, `_interest: ReactorInterest`, whose `Drop` actively
removes the entries this leaf armed. **Still no hand-written `Drop for EffectPoll`** — the field's
own drop glue *is* the dereg path, the same structural-minimum the permit uses (the two release
fields, `permit: Option<Permit>` + `_interest: ReactorInterest`, drop together when the future
drops; Principle 18 — enforce invariants structurally).

**Reactor changes (`reactor.rs`):**

1. **Tag each registration with the leaf that armed it.** Add a monotonic `RegId` (a `next_reg`
   counter on `Reactor`) and a scratch `current_registrant: Option<RegId>`. Extend the waiter
   maps to carry the tag: `fd_waiters: HashMap<usize, (RawFd, OwnedCWaker, RegId)>` and
   `timer_waiters: HashMap<u64, (OwnedCWaker, RegId)>`. The `register_fd`/`register_timer` callback
   bodies stamp each new entry with `current_registrant` (the leaf currently being polled).
2. **Bracket the poll-fn call.** `EffectPoll::poll`, before calling `poll_fn`, reborrows the
   reactor (via `host.host` — the raw `*mut Reactor`, the **B1 provenance invariant**: a transient
   `&mut` that does not overlap `turn()` or the callbacks' reborrows, since the poll-fn runs only
   *inside* `Future::poll` on the reactor thread) and sets `current_registrant = Some(self.reg)`;
   after the call it clears it to `None`. So every fd/timer the poll-fn arms during *this* poll is
   tagged with this `EffectPoll`'s `RegId`. (The re-arm-on-every-`Pending` + EEXIST-keep + one-shot
   `turn()` deregister discipline of §2.1 is unchanged — the *source of truth for what is live* is
   the map, keyed by tag; re-arming re-stamps the same tag, so at any instant the live entries
   tagged `reg` are exactly this leaf's current arm.)
3. **`Reactor::deregister(reg: RegId)`** — remove every `fd_waiters` entry tagged `reg`
   (mio-`deregister` each `SourceFd`) and every `timer_waiters` entry tagged `reg` (drop from the
   map; the matching `timer_heap` entry becomes a tombstone that `turn()` already tolerates — its
   `if let Some(waker) = self.timer_waiters.remove(...)` guard finds nothing and skips). Scanning
   by tag is O(live waiters); cancellation is rarer than steady-state, and the map is bounded by
   in-flight leaves — acceptable (the O(1) alternative, a per-`reg` `Vec<Token>`, is noted but not
   built; Principle 6).
4. **`ReactorInterest { reactor: *mut Reactor, reg: RegId }`** with `impl Drop` calling
   `(*reactor).deregister(reg)` (the B1 reborrow again — drop runs on the reactor thread between
   polls/turns, never concurrently with one). Minted in `EffectPoll::new` (the `reg` allocated
   from the reactor via the `env`/`host`, alongside the permit acquire in `await_poll_node`).

**Lifecycle parity with the permit:**

- **drop-while-`Pending`** (cancellation — a race loser, a timed-out branch, a disconnected
  handler, a shutdown-cleared strand) → `ReactorInterest::drop` actively deregisters the live fd/
  timer interest. **This is the leak fix.**
- **`Ready`** → the firing already removed the fd entry in `turn()` (one-shot deregister), and a
  timer self-clears at its deadline, so `deregister` on the eventual future-drop is a **safe
  no-op** for the common case. **No eager dereg is added** (unlike the permit's eager `take()` on
  `Ready`): the permit needed eager release because `join_all` holds a completed leaf until the
  whole join finishes (starving same-token waiters); reactor interest has no such hold — the
  fired fd entry is already gone, and a stray still-live timer self-clears. Keeping dereg
  drop-only is the smaller design and correct (documented here so the asymmetry with the permit is
  deliberate, not an oversight). *(If a leaf that arms BOTH an fd and a timer, fd-fires-`Ready`
  while the timer is still pending is ever observed to matter, the timer self-clears at deadline;
  eager dereg-on-`Ready` is the available tightening, not needed for the slice.)*

**Co-review with the supervisor panic path (§2.14).** The §2.14 Chunk-B panic-path instance of
this finding (a handler that panics while a poll leaf is parked) is **subsumed** by this design:
`catch_unwind` drops the handler strand → its `EffectPoll`s drop → `ReactorInterest::drop`
deregisters. The §2.9 "Chunk A: permit-only release; active reactor-interest deregistration
deferred to Chunk C" record is now **discharged** — update §2.9's deferral note to point here.

### 2.17 A3 finding #4 — `Drop for AcquirePermit` (stale-waker removal) (slice 7, S96 Chunk C)

**Authority: `sprints/SPRINT.md` Chunk-C-design-prerequisites box, finding #4 + the A3 review
(`reactor.rs` review §4).** An `AcquirePermit` that is dropped **while parked** (a future
cancelled *before* it acquires its permit — exactly what `race`/`timeout`/shutdown do to a branch
that is queued behind a full token or a full global budget) leaves its waker in `slot.waiters`. A
later `Drop for Permit` does `pop_front()` and wakes that **stale** waker (a no-op — the future is
gone), while the freed permit goes unclaimed and the **next live** waiter behind it is never woken
→ **lost-wakeup / a free permit nobody can take**. Unreachable in Chunk A/B (no future is dropped
while parked on an acquire — `await_poll_node` runs the acquire to completion; the supervisor lets
each strand finish before dropping it), but **Chunk C hits it deliberately**: a parked branch is
precisely what a race loser / a timed-out / a shutdown-cleared strand often is.

#### The design — `Drop for AcquirePermit` removes its own waiter by identity (FIFO/order preserved)

The clean fix is **explicit removal on drop**, which keeps the release path's single-front-`pop`
FIFO intact — and that FIFO is **load-bearing**: §2.8/§8.2 require **capacity-1 within-token
SOURCE ORDER**, which the FIFO front-pop provides. (The tempting "pop-until-live" / "wake-all on
release" alternatives are **rejected**: a Waker carries no reliable liveness or identity signal,
so "skip stale" needs an identity marker anyway, and "wake everyone, let one win" is a thundering
herd that **destroys the capacity-1 source-order guarantee**. Explicit removal-by-identity is both
deterministic and order-preserving — the right primitive.)

**Changes (`reactor.rs`):**

1. **Give each parked waiter an identity.** The slot's queue carries `(WaiterId, Waker)`:
   `waiters: VecDeque<(u64, Waker)>`, with a monotonic `next_waiter: Cell<u64>` on `TokenPool`
   (single-thread, no atomic). `Drop for Permit`'s front-`pop` already wakes the front — it now
   pops `(_, waker)` and wakes `waker` (FIFO/order **unchanged**; `_neg` for source order still
   holds).
2. **`AcquirePermit` tracks its own parked identity:** add `parked_id: Option<u64>`. In
   `AcquirePermit::poll`, when parking: if `parked_id` is `None`, allocate an id, push `(id,
   waker)`, store `Some(id)`; on a re-poll that is *still* parked (rare under the single executor —
   the waiter is normally popped+woken before re-poll), **replace** the stored waker for that id
   in place rather than pushing a duplicate (this also closes the latent push-on-every-`Pending`
   duplication the current code has). On acquire, clear `parked_id` to `None` (the releaser already
   popped it, or it was never parked).
3. **`impl Drop for AcquirePermit`:** if `parked_id` is `Some(id)`, borrow the pool, get the slot
   for `self.token`, and `waiters.retain(|(wid, _)| *wid != id)` — remove **only** this future's
   stale waker, leaving the rest of the FIFO (and its order) intact. `token == 0` never parks
   (`parked_id` stays `None`) ⇒ the drop is a no-op. The **global-budget** `AcquirePermit`
   (`GLOBAL_BUDGET_TOKEN`, §2.13) shares this machinery, so this finding's fix **co-covers** the
   accept-loop launch parked on a full global budget that is then cancelled by shutdown — the A3
   review's explicit co-review request.

**Single-thread invariant holds verbatim.** All `AcquirePermit` ops — `poll`, the drop's
`retain`, and `Drop for Permit`'s front-pop — run on the **one reactor thread** (§2.8/§2.9), so
the pool stays a plain `RefCell<HashMap<…>>` — no atomics, no `Mutex`. The drop's `retain` is O(slot
waiters) per cancel; cancellation is rarer than steady-state and slots are bounded by contended
in-flight acquires — acceptable (Principle 6).

### 2.18 `sleep` (the timer leaf) + `timeout` = `race io (sleep d)` (slice 7, S96 Chunk C)

**Authority: `effect-concurrency.md` §9 (`timeout d io = race io (sleep d)` — derivable in
stdlib).** `timeout` is **not a primitive** — it composes `race` (§2.15) with one new leaf,
`sleep`, and lives mostly in stdlib `.cl`.

#### `sleep` — a runtime-provided timer poll leaf (NOT a platform effect)

`sleep : Duration -> IO Unit` arms the reactor's timer and resumes when it fires. It is a
**tokenless poll leaf** — `(token = 0, capacity = 1)`, i.e. unrestricted overlap (many `sleep`s
race concurrently) — that reuses the **entire** `IO_TAG_EFFECT_POLL` / `EffectPoll` /
acquire-around-poll / timer-`turn()` machinery already built. The poll-fn (a small **intrinsics**
poll-fn, NOT a platform-DLL export — §9: the control vocabulary is runtime-hosted, platforms
never see it; this is the same shape as the retained `timer_write_pollfn` substrate fixture
§2.7):

- first poll → compute `deadline = monotonic_nanos() + d`, call `host_register_timer(host,
  deadline, waker)`, write nothing yet, return `CPoll::Pending`;
- resume (timer fired, `turn()` woke the waker) → write `Unit` (`0`) into the reserved result slot,
  return `CPoll::Ready`.

**Lowering seam (/design backend).** `(sleep d)` lowers to an `IO_TAG_EFFECT_POLL` node whose
`code_ptr` is this intrinsics timer poll-fn and whose env carries `d` (the duration), with the
leading `(token = 0, capacity = 1)` pair (the §2.9 offsets 32/40, the "tokenless leaf passes
`(0,1)` constants" convention the /arch Phase-3 ruling pinned). **Coordinate with /design backend:
how `sleep` resolves to the intrinsics timer poll-fn** (a well-known runtime symbol, not a GOT
platform slot — distinct from a `declare_platform!` effect). This is the only backend touch
`sleep` needs; everything downstream is the existing poll path.

#### `timeout` — stdlib `.cl` composition (mostly /stdlib)

`timeout` is `race` over the two arms, mapping the winner to `Option`:

```clojure
(defn timeout [d io]
  (race (map Some io)              ; io wins → (Some v); the sleep loser is dropped (cancelled)
        (map (fn [_] None) (sleep d))))  ; sleep wins → None; the io loser is dropped (cancelled)
```

The cancellation of the **loser** (the still-running `io` when the timer wins; the pending
`sleep` when `io` wins) is **automatic** — it is the §2.15 race-loser drop, which releases the
loser's permit (§2.9), deregisters its reactor interest (§2.16), removes any parked acquire waker
(§2.17), and frees its unconsumed sub-tree (§2.15.1). **`timeout` adds no cancellation plumbing**
— it inherits all four release paths from `race`. This is the §1 "throughput is free; control is
explicit" thesis paying off: per-request timeout is one stdlib line over the `race` primitive.
*(The exact `.cl` surface + `Option`/`map` availability is **/stdlib + /spec (FIXME 0447 second
half)** — flagged, not authored here.)*

### 2.19 cancel-on-disconnect + graceful shutdown — the runtime hooks (slice 7, S96 Chunk C)

**Authority: `sprints/SPRINT.md` Chunk C witnessable (cancel-on-disconnect + graceful shutdown) +
`effect-concurrency.md` §9 (cancellation = losing a race or exiting a scope).** Both are
**compositions** of the §2.15 race-loser drop + the §2.12 supervisor — no new cancellation
primitive.

#### cancel-on-disconnect = `race` the handler against a disconnect-watch leaf

A per-connection handler strand must be cancelled if its peer disconnects mid-request. This is
**not** a new mechanism — it is `race` (§2.15): the serve loop wraps each handler body in

```clojure
(race (handle-conn conn)
      (until-disconnect conn))   ; a poll leaf that resolves when the connection fd signals HUP / read-EOF
```

When `until-disconnect` wins (the peer closed), the `handle-conn` branch is the **loser** → it is
**dropped → cancelled**, releasing every resource it held via the four §2.15 drop paths. `cancel`
is, exactly per §9, the *consequence* of losing this race — there is no `cancel(strand)` call.
**`until-disconnect` is a platform poll leaf** (the web platform knows how to arm `EPOLLHUP` /
detect read-EOF on the connection fd) — **coordinate the leaf + the serve-loop `race` wrap with
/design platform** (the web serve loop) + /spec (0447). The reactor side is just `race`.

#### graceful shutdown = stop accepting, then drain-or-cancel the supervisor

Graceful shutdown cancels outstanding **supervised** strands (Chunk B, §2.12). The supervisor
already has `Supervisor::clear()` — *"drop all in-flight strands; each dropped strand's owned
`EffectPoll`(s) release their per-token permits and its global `Permit` releases."* §2.16/§2.17
**complete** that drop path (clear() now also deregisters each cleared strand's reactor interest
and removes any parked-acquire waker — no leak, no lost-wakeup, even when clearing many strands at
once). The shutdown hooks:

1. **A shutdown signal** observed by the accept loop (a flag in `ReactorEnv` / a reactor-construction
   knob set by int `src/` — e.g. a `Cell<bool>` the serve loop reads each accept). On signal, the
   accept loop **stops accepting** and returns — completing the **top** future, which is how
   `block_on_reactor` already terminates a drive.
2. **Graceful drain vs. hard cancel** — the policy at the drive boundary:
   - **graceful** (let in-flight handlers finish): the executor keeps **draining** the supervisor
     to empty (`supervisor.drive()` each turn until `is_empty()`) **before** returning — the
     existing "a non-empty supervisor is progress" liveness rule (§2.12) already keeps the drive
     alive for this; no clear().
   - **hard / deadline** (cancel stragglers): `supervisor.clear()` drops the outstanding strands
     (the §2.16/§2.17-completed cancel path). Emit `StrandCancelled { reason: Shutdown }` for each.
   - **graceful-with-deadline** composes the two via `timeout` (§2.18): `race (drain-to-empty)
     (sleep grace_period)` — if the timer wins, `clear()` the stragglers. Pure composition of the
     primitives.
3. **The shutdown-policy knob is reactor-construction config** (int `src/`, the same place
   `SupervisorPolicy`/`degree`/global-budget live — §6.2). **Coordinate the knob + the
   serve-loop's shutdown-signal wiring with /design int src/** (reactor-construction) + /design
   platform (the web serve loop). The reactor owns the **mechanism** (drain / `clear` / the
   `StrandCancelled` emit); int/platform own the **trigger + policy**.

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

**S96 Chunk B — supervisor + global-budget events.** Slice 5 + slice 4 add the
supervisor/launch-and-continue + backpressure surface (§2.11–§2.13), all `#[non_exhaustive]`
joiners:

- `StrandLaunched { strand, parent }` — a detached strand spawned into the supervisor
  (`IO_TAG_LAUNCH` arm, §2.11). The `parent` ties the handler strand to the accept-loop root
  strand so the `/strand` dump reconstructs *"this request fanned out into this handler."*
- `StrandCompleted { strand }` — a supervised strand finished cleanly (§2.12).
- `StrandFailed { strand, message }` — a supervised strand panicked or produced a runtime error;
  the supervisor caught it and applied the §10 policy (log + drop). **This is the load-bearing
  event of §11 point 2: supervisor drops vanish without it** — it is the only trace a 500-and-
  dropped request leaves. `/qa`'s panic-survival acceptance asserts it; the web serve loop reads
  it (or its own catch) to emit the client 500.
- `GlobalBudgetParked { strand }` / `GlobalBudgetAcquired { strand }` / `GlobalBudgetReleased {
  strand }` — the global admission gate (§2.13): the accept-loop launch parked on a full global
  budget (backpressure), then admitted, then a completing strand freed a slot. (`/qa` asserts the
  park under load; the dump renders saturate-not-oversaturate.)

Emit sites: the `IO_TAG_LAUNCH` arm (`StrandLaunched`, `GlobalBudget*`), the `supervised`
wrapper completion match (`StrandCompleted`/`StrandFailed`, §2.12). The per-strand `degree`
parks reuse the existing `TokenParked`/`TokenAcquired`/`TokenReleased` (the §2.8 events — degree
only changes the slot *size*, not the event surface). The variant set + emit stay
intrinsics-owned (`strand.rs`); int owns the dev surface.

**S96 Chunk C — cancellation events.** Slice 7 adds the §11 "cancellation (race loser / timeout
fired → what was cancelled)" surface — one `#[non_exhaustive]` joiner:

- `StrandCancelled { strand, reason }` — a branch / strand was **dropped** (cancelled) rather than
  completing. `reason` is a small enum: `RaceLost` (a `race`/`select` loser, §2.15 step 5),
  `TimedOut` (the `io` arm of a `timeout` whose `sleep` won — a `RaceLost` specialization the
  `/strand` dump labels distinctly), `Disconnected` (cancel-on-disconnect, §2.19), `Shutdown`
  (graceful/hard shutdown `clear()`, §2.19). **This is the only trace a cancellation leaves** —
  cancellation = drop is silent in the source (the §11 invisible-concurrency argument applies
  verbatim: the race, the timeout, the disconnect-cancel never appear in user code), so without
  this event a cancelled request vanishes. `/qa` asserts it for the timeout/race acceptance; the
  `/strand` dump renders *"this branch won; these were cancelled (race-lost / timed-out)."*

Emit sites: `run_race_node`/`run_select_node` as each loser drops (§2.15 step 5); the §2.19
shutdown `clear()` for each cleared strand. The variant set + emit stay intrinsics-owned
(`strand.rs`); int owns the dev surface. (No new event is needed for the finding-#3 dereg or the
finding-#4 waker-removal — those are silent resource-release internals beneath the
`StrandCancelled` that names the user-observable cancellation.)

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
> carrier**; live **poll-shape capacity-N + the acquire-around-poll lifecycle** was the
> deferred half (poll nodes reserved the slots at sentinel capacity 1 in S95).
>
> **Done in S96 (Chunk A, item 3) — §2.9:** the **acquire-around-poll lifecycle + RAII
> `Permit` drop-guard** lights up the poll carrier. The permit is acquired at leaf
> establishment (live `(token, capacity)` baked at offset 32/40), owned by the
> `EffectPoll` future, wraps the establish→`Pending`→…→`Ready` arc, and releases on
> `Ready` (eager `Option::take`) AND on future-drop (the cancellation path) — the named
> A→C contract Chunk C cancellation exercises. `/dev` implements in Phase 5.
>
> **Done in S96 (Chunk B — slices 5 + 4) — §2.11/§2.12/§2.13/§2.14:** **launch-and-
> continue** (the detached-launch `IO_TAG_LAUNCH` node — fire-and-forget, no join point,
> yields `Pure Unit` at once, §2.11), the **supervisor** (a single-threaded
> `FuturesUnordered` `JoinSet`-equivalent that owns each detached strand, `catch_unwind` +
> the reused `take_runtime_error` capture, applies the §10 log/drop policy, never re-raises,
> never aborts the drive, §2.12), and **backpressure** (`min(capacity, degree)` on the §2.8
> pool + a **global** admission `Semaphore` on a reserved token bounding total in-flight
> detached strands, §2.13). Both reuse the unchanged Chunk-A substrate; gates (b)/(d)
> confirmed to hold post-cutover (§2.14). `/dev` implements in Phase 5.
>
> **Done in S96 (Chunk C — slice 7) — §2.15/§2.16/§2.17/§2.18/§2.19:** the **combinator
> runtime** (`race`/`select` over the branch futures on the one reactor thread, winner
> resolves, **losers dropped = cancelled**, §2.15) + the **trampoline-frame cancellation
> drop-guard** (frees a dropped branch's unconsumed sub-tree, §2.15.1); the **two A3-review
> drop-path completions** — finding #3 (`EffectPoll`-owned `ReactorInterest` RAII handle whose
> drop actively deregisters fd/timer interest, §2.16) + finding #4 (`Drop for AcquirePermit`
> removes its stale FIFO waker by identity, §2.17); **`sleep`** (the runtime timer poll leaf)
> + **`timeout` = `race io (sleep d)`** (mostly stdlib, §2.18); and the **cancel-on-disconnect**
> (`race` the handler against a disconnect-watch leaf) + **graceful shutdown** (drain-or-`clear`
> the supervisor) hooks (§2.19). The unifying invariant: **cancellation = future-drop**, and
> every drop path (permit §2.9, fd/timer interest §2.16, FIFO waker §2.17, sub-tree §2.15.1)
> releases/deregisters cleanly — the Chunk-C completion of the A→C contract. `/dev` implements
> in Phase 5.

Cancellation is no longer a forward-looking item — it is designed above (§2.15–§2.19). What
remains beyond this sprint's combinator surface stays an arch-track item:

- **Nested launch + nested combinators under volume** — a launched strand that itself launches,
  or a `race` whose branch launches detached strands, currently trips the supervisor's
  single-borrow `drive()` re-entry guard (§2.12 note). Active nested-fan-out support is a
  later-slice concern (the Chunk-C acceptance shapes race/timeout/cancel from the top serve loop,
  not from inside a launched strand). Coordinate with /arch when it opens.

### 5.1 /dev Chunk-B intrinsics implements, in this order

1. **Strand events** (`strand.rs`) — add the `#[non_exhaustive]` variants `StrandLaunched
   { strand, parent }`, `StrandCompleted { strand }`, `StrandFailed { strand, message }`,
   `GlobalBudgetParked`/`GlobalBudgetAcquired`/`GlobalBudgetReleased { strand }`. Zero-behaviour
   first; gives /qa the assertion surface. (§3)
2. **`degree` on the §2.8 pool** (`reactor.rs`) — `TokenPool` gains a construction-time `degree`;
   slot sizing becomes `permits = min(node_capacity, degree).max(1)`. The smallest, most
   isolated change; unit-test `min(capacity, degree)` before anything fans out. (§2.13 part 1)
3. **The global admission `Semaphore`** (`reactor.rs`) — reserve `GLOBAL_BUDGET_TOKEN`,
   pre-size its slot to the global degree at `block_on_reactor` construction, add a
   `ReactorEnv::acquire_global(strand)` helper over the existing `acquire`. (§2.13 part 2)
4. **The supervisor** (`reactor.rs`) — `Supervisor { strands: RefCell<FuturesUnordered<…>>,
   policy }`, constructed single-sited in `block_on_reactor` alongside the pool, threaded through
   `ReactorEnv`; the `supervised` wrapper (`catch_unwind` + `take_runtime_error` capture +
   `apply_policy` + `consume_io_tree` + global-`Permit` drop); extend the `block_on_reactor`
   drive loop to drain the supervisor + exempt a non-empty supervisor from the `MAX_TOTAL_BLOCK`
   no-progress cap. (§2.12)
5. **The `IO_TAG_LAUNCH` trampoline arm** (`io.rs`, `run_io_trampoline_inner_async`) — read the
   launched sub-tree field, acquire the global-budget permit (park if exhausted), mint the child
   strand, `supervisor.spawn(sub_tree, strand, permit)`, yield `Pure Unit`. **Co-requisite seam:
   the `IO_TAG_LAUNCH` const + node bake + independence detection are /design backend's** —
   coordinate before this lands. (§2.11)
6. **RC ownership transfer of the launched sub-tree** — confirm the launch node releases its hold
   and the supervised strand `consume_io_tree`s it exactly once (no double-free / no leak); the
   one new RC subtlety. Coordinate with /design backend on the node's owned-field shape. (§2.11)

**Coordination seams (named, not built here):** /design backend — the `IO_TAG_LAUNCH` tag const
+ node bake + launch-shape independence detection + per-resource `global_budget` node-read (if
baked); /design int src/ — the reactor-construction knobs (`degree`, global budget, the
`SupervisorPolicy` config); /design platform — the web serve-loop's "500-on-dropped-connection"
response mapping that reads `StrandFailed`. /spec (FIXME 0447 first half) — the §10.12/§12.5
launch-and-continue + supervisor-policy user-facing surface (NOT authored here).

### 5.2 /dev Chunk-C intrinsics implements, in this order

The order is dependency-first and smallest-blast-radius-first: the two drop-path completions
(findings #3/#4) are self-contained `reactor.rs` changes unit-testable *before* any combinator
exists; `sleep` reuses the existing poll path; the combinator runtime + frame-guard land last
(they consume all of the above). Each step is `/dev` → `/review` per the per-crate D/D/R cycle.

1. **Finding #4 — `Drop for AcquirePermit`** (`reactor.rs`, §2.17). Give the slot's FIFO waiter
   identity (`VecDeque<(u64, Waker)>` + a `next_waiter: Cell<u64>` on `TokenPool`); add
   `parked_id: Option<u64>` to `AcquirePermit` (allocate on first park, replace-not-duplicate on
   re-park, clear on acquire); add `impl Drop for AcquirePermit` doing `waiters.retain(by id)`.
   The smallest, most isolated change — unit-test "drop-while-parked frees the next live waiter"
   (no lost-wakeup) + "source order preserved at capacity 1" *before* any combinator. Co-covers
   the global-budget `AcquirePermit`.
2. **Finding #3 — `ReactorInterest` active deregistration** (`reactor.rs`, §2.16). Add `RegId` +
   `next_reg` + `current_registrant` scratch; tag `fd_waiters`/`timer_waiters` entries with the
   registrant; add `Reactor::deregister(reg)`; add the `ReactorInterest { reactor, reg }` RAII
   struct; bracket the `poll_fn` call in `EffectPoll::poll` to set/clear `current_registrant`; add
   the `_interest: ReactorInterest` field to `EffectPoll` (minted in `EffectPoll::new`, `reg`
   allocated in `await_poll_node`). Unit-test "dropping a `Pending` `EffectPoll` that armed fd
   interest removes its `fd_waiters` entry + mio-deregisters" (extend the §2B drop-release unit to
   a real-fd fixture, not the noop-host). Subsumes the §2.14 supervisor-panic-path leak.
3. **`StrandCancelled` event** (`strand.rs`, §3) — the `#[non_exhaustive]` variant + the `reason`
   enum (`RaceLost`/`TimedOut`/`Disconnected`/`Shutdown`). Zero-behaviour first; gives /qa the
   cancellation assertion surface.
4. **`sleep` timer poll leaf** (`reactor.rs`/`io.rs`, §2.18) — the intrinsics timer poll-fn
   (register_timer + Pending → write Unit + Ready). **Co-requisite seam: how `(sleep d)` resolves
   to this runtime poll-fn (a well-known symbol, not a GOT platform slot) + the `(0,1)`-leading
   `IO_TAG_EFFECT_POLL` bake is /design backend's** — coordinate before this lands. Unit-test a
   bare `sleep` resumes at its deadline.
5. **The trampoline-frame cancellation drop-guard** (`io.rs`, §2.15.1) — move the loop's
   `current` + `cont_stack` into a `TrampolineFrame` RAII whose `Drop` `consume_io_tree`s the
   unconsumed pointers when the future is dropped before `Step::Finish`, disarmed on normal
   finish. Unit-test "dropping a mid-flight trampoline future frees its sub-tree (no leak)".
   **Co-requisite seam: the per-branch root ownership + the cancel-time `consume_io_tree`
   RC-balance against the backend's emitted RC is /design backend's** (`io-trampoline.md`).
6. **The `IO_TAG_RACE`/`IO_TAG_SELECT` trampoline arms** (`io.rs`, `run_io_trampoline_inner_async`,
   §2.15) — read+move-out the branch sub-trees, mint a child strand each, build one frame-guarded
   branch future per sub-tree, race them (`futures::future::select` / `FuturesUnordered::next`),
   return the winner, drop+`StrandCancelled` the losers. **Co-requisite seam: the
   `IO_TAG_RACE`/`IO_TAG_SELECT` consts + node bake + the combinator-application lowering (and
   whether new `Expr`/`MonoExpr` marker variants are warranted, the `LaunchContinue`/FIXME-0466
   precedent) are /design backend's** — coordinate before this lands. Steps 1+2+5 are the
   release/teardown paths this step exercises; land them green first.
7. **Graceful-shutdown drive hook** (`reactor.rs`, §2.19) — the shutdown signal in `ReactorEnv`,
   the drive-boundary drain-to-empty (graceful) vs `supervisor.clear()` (hard) policy, the
   `StrandCancelled { reason: Shutdown }` emit on clear. **Co-requisite seam: the shutdown-signal
   wiring + the policy knob is /design int src/ (reactor-construction) + /design platform (serve
   loop).** `timeout` (§2.18) + cancel-on-disconnect (§2.19) are stdlib/platform compositions over
   steps 4+6 — no further intrinsics arm.

**Coordination seams (named, not built here):** /design backend — the `IO_TAG_RACE`/`IO_TAG_SELECT`
tag consts + node bake + combinator-application lowering + the per-branch owned-field + cancel-time
`consume_io_tree` RC-balance contract + the `sleep` runtime-poll-fn resolution; /design int src/ —
the shutdown-policy + graceful-vs-hard reactor-construction knob; /design platform — the web serve
loop's `race`-against-disconnect wrap + the `until-disconnect` poll leaf; /stdlib + /spec (FIXME
0447 second half) — the `timeout`/`race`/`select` `.cl` surface + the §12 typing/semantics of the
in-language combinators + structured cancellation. **No public-api / ABI change** (SPRINT.md
"Slice 7: NO ABI bump"; the tags are in-process consts).

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
   entry with no new mirror. **S96 Chunk B preserves this for the supervisor + the global
   admission budget too.** The `Supervisor` (§2.12) and the global-budget slot (§2.13) are
   **also** constructed single-sited in `block_on_reactor` alongside the `Reactor`,
   `HostCtx`, and `TokenPool`, and threaded through `ReactorEnv` — both host-internal
   (reached through the trampoline, not the platform poll-fn), so neither widens
   `HostCallbacks` nor grows a parallel int-side builder. The `SupervisorPolicy` *value* (a
   reactor-construction config from int `src/`) crosses in as a plain argument to
   `block_on_reactor`, not as a host-callback — it adds no mirror.

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

- `sprints/SPRINT.md` — S95 scope (slices 3 + 6) + S96 Chunk A item 3 (poll-shape live
  capacity + acquire-around-poll) + S96 **Chunk B** (slice 5 + slice 4) + the Phase-2
  architecture review **gate (a)** (acquire-around-poll deadlock-freedom + the TWO structural
  requirements: RAII `Permit` drop-guard / non-re-entry — the AUTHORITY for §2.9), **gate (b)**
  (launch-and-continue lifetime + supervisor: reuse the capture, replace the re-raise; new
  `JoinSet` machinery; co-land with backpressure — the AUTHORITY for §2.11/§2.12), **gate (c)**
  (two-pool wakeable bridge), and **gate (d) / FIXME 0442** (degree + global budget mechanism —
  the AUTHORITY for §2.13). The **Chunk-C-design-prerequisites box** (the two A3-review findings)
  is the AUTHORITY for §2.14 + §2.16 (finding #3) + §2.17 (finding #4). **S96 Chunk C** (slice 7 —
  `race`/`select`/`timeout` + structured cancellation; "NO ABI bump", the in-process tag consts)
  is the AUTHORITY for §2.15/§2.18/§2.19. **Carrier re-blessed post-review** — see §8.1.
- `design/arch/effect-concurrency.md` **§8.1 (the ratified slice-3 carrier — `(token,
  capacity)` dynamic on the node, first-writer-wins reconciliation; the AUTHORITY for
  §2.8 / §2.6 / §2.9)** + §8.2 (within-token ordering), **§5 (the descriptor: capacity vs
  *degree*; the FIXME 0442 two-mechanisms-one-concept ruling — AUTHORITY for §2.13)**, §6
  (launch-and-continue → spawn-don't-await + `JoinSet`; the host-runtime primitive map), §7 (the
  two-pool model + the permanent wakeable bridge), **§9 (the control half — `race`/`select` +
  structured cancellation; `timeout = race io (sleep d)`; "cancel = the consequence of losing a
  race or exiting a scope (drop the future)"; the AUTHORITY for §2.15/§2.18/§2.19)**, **§10
  (supervisor semantics — 500/log/drop, the honest first-error caveat; AUTHORITY for
  §2.12)**, §11 (observability — supervisor drops vanish without the sink), **§14 (build
  sequencing — slice 4+5 co-land, step 4)**, §16 (the reference workload — the accept loop),
  Appendix B — the implementable plan (canonical).
- `design/arch/bounded-contexts.md` §6 (int reactor policy + impl-location), §4b
  (intrinsics hosting), §5 (platform C-ABI async leaf).
- `design/arch/platform-interface.md` §6.8 — ABI-v7 layout contracts (`ConcurrencyDescriptor`,
  `Poll`, `PollFn`, `HostCtx`, `Waker`, `WakerVTable`, `ConcurrentPlatformFn`).
- `design/arch/sequences/concurrency-scheduler.mmd` — reactor participant (intrinsics-hosted).
- `crates/cranelisp-intrinsics/src/{reactor.rs,strand.rs,io.rs}` — the implementation;
  `crates/cranelisp-intrinsics/Cargo.toml` — the feature gates.
- `design/int/io-integration.md`, `design/int/observability.md` — the sync IO
  trampoline + `io_observer` precedent this sink mirrors.
