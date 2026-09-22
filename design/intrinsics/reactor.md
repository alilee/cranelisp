# The effect reactor and async trampoline — interior design

Owner: `/design` (intrinsics). Implements
`crates/cranelisp-intrinsics/src/{reactor.rs,strand.rs,io.rs}`: the mio
reactor, the async IO trampoline and its executor, the host `ctx` vtable, the
token permit pool, the two-pool `Par` join, launch-and-continue with its
supervisor, the `race`/`select` runtime and every cancellation release path.

Consumes without restating: `design/arch/effect-concurrency.md` (the
concurrency model — §4.1.1 the `ctx`-vtable handle model, §7 the two pools,
§8 the permit carrier and ordering, §9 the control half, §10 supervisor
semantics, §11 observability, Appendix B the delivered status);
[intrinsics bounded context](../arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics),
especially invariant 15 (argument lifetime across suspension is runtime-owned);
`design/arch/platform-interface.md` §6.8 (the async-leaf ABI);
`spec/10-io.md` §10.12.7–§10.12.10 and `spec/12-runtime.md` §12.4.4 and
§12.7.9 (the observable contract).

Out of scope: the emitted node layouts and their drop glue
(`design/backend/io-trampoline.md` §12, §15, §16, §17); poll-leaf authoring
(`design/platform/poll-leaf-authoring.md`); heap ownership, node teardown and
result-handoff authority ([`ownership-and-disposal.md`](ownership-and-disposal.md));
the RC/alloc diagnostic surface ([`diagnostic-modes.md`](diagnostic-modes.md)).

Section numbers are stable: source comments and sibling designs cite them.

---

## 0. The host-client seam

The binary (`src/`, `design/int/`) is a host client of this runtime. Its whole
contact surface:

- **Force an IO tree through `cranelisp_run_io`.** JIT code reaches it as the
  catalog import `runtime/run_io`; a `--link`ed program's startup object calls
  the unaliased symbol. `cranelisp_run_io` builds the reactor, pool,
  supervisor and bridge join itself (§6), drives the tree, then consumes the
  caller's tree. The binary constructs no reactor, `HostCtx`, waker, pool or
  supervisor.
- **Propagate the platform loader's `ABI_VERSION` refusal.** The constant is
  `cranelisp-platform`'s; the loader in `src/` only enforces it.
- **The strand sink (§3) is not part of this seam.** It is crate-private; a
  binary reader would be a new inter-crate public-API edge (`arch`, user gate).

Everything else in this document is runtime interior that `cranelisp-backend`
emits calls into. A defect in it is an intrinsics or backend concern, not a
host-orchestration one.

## 1. Substrate and construction

- The substrate is `mio` readiness polling plus a hand-written single-future
  executor over `futures` combinators. There is no tokio and no fiber; every
  suspension is a compiler-generated `async` state machine.
- `mio` and `futures` are unconditional dependencies. There is one ABI, one
  top-level trampoline and one executor for every mode.
- **Each top-level drive constructs its reactor eagerly** (`epoll_create` plus
  one eventfd). A pure-blocking tree never returns `Pending`, so it never turns
  the reactor; the two syscalls are its whole cost. This is the architecture's accepted form
  (`effect-concurrency.md` §6; `platform-interface.md` §6.8.0a). Lazy
  construction is a potential extension (`design/intrinsics/reactor.md` §5).
- The reactor lives here, not in `src/`, because a `--link`ed program does not
  contain the binary: `--run`, REPL and `--link` reach the same reactor through
  the same entry.

---

## 2. The reactor interior

### 2.1 The reactor loop

`Reactor` owns one `mio::Poll`, an fd-waiter map, a timer min-heap with a
live timer-waiter map, the cross-thread bridge waker (§2.21), the permit pool
handle and the per-effect held-permit ledger (§7.2).

- **fd registration is idempotent.** A poll-fn re-registers on every
  `Pending`. `EEXIST` keeps the live registration and its stored waker; any
  other registration error panics as a reactor defect.
- **Every registration is stamped** with the registrant id of the `EffectPoll`
  currently being polled (§2.16), or `0` outside a poll bracket.
- **`turn(max_block)`** blocks in `mio::poll` for at most
  `min(soonest timer − now, max_block)`, then fires ready fd waiters (one-shot:
  deregistered as they fire) and expired timers. A timer whose waiter was
  removed leaves a heap tombstone that `turn` skips.
- **The bridge eventfd is registered edge-triggered and never drained.**
  Level-triggered registration would spin; an explicit drain under
  edge-triggering can lose a wake. Neither may be introduced.

### 2.2 The C-ABI waker projection

A `std::task::Waker` crosses the platform C-ABI as a `(data, vtable)` pair
whose data is a boxed waker. The poll-fn borrows it for the call; the reactor
clones its own owned copy when it stores a waiter. The platform owns *what* to
wait on; the host owns *when* to re-poll.

### 2.3 The `HostCtx` vtable

`HostCtx` carries five entries — `register_readable`, `register_writable`,
`register_timer`, `acquire`, `retire` — plus the host pointer. The layout is
`platform-interface.md` §6.8's. The entry bodies are §2.1 and §7.2.

**The host pointer is a raw `*mut Reactor`, never derived from `&Reactor`.**
Callbacks reborrow `&mut` only inside a poll-fn call; the executor reborrows the
same raw pointer only between polls to turn the reactor. Both lifetimes never
overlap. Deriving the pointer from a shared reference is undefined behaviour
under Stacked and Tree Borrows.

### 2.4 The executor drive loop

`block_on_reactor` builds, in one place, the reactor, the task waker, the bridge
join, the permit pool (sized by the degree knob, §2.13), the `HostCtx` and the
supervisor. It then repeats:

1. clear the pending-wake flag, then poll the top future until it completes;
2. drive the supervisor once (§2.12);
3. **return only when the top future has completed, the supervisor is empty
   and the bridge join count is zero** — so a finite program's detached
   strands drain before exit, and no blocking worker is still reading the
   caller's tree (§2.21);
4. evaluate the `OneShot` backstop and the deadlock detector (§8);
5. turn the reactor.

The task waker sets the pending-wake flag and wakes the bridge eventfd. The flag
keeps the deadlock detector from misreading a top future that was woken — for
example by a permit release during the supervisor drive — but not yet
re-polled.

Drop order is load-bearing: the supervisor and the strands it owns borrow the
`HostCtx` and pool, so they drop before those locals.

### 2.5 The await boundary — `EffectPoll`

`EffectPoll` is the only leaf future. `Bind`, `Pure` and continuation calls run
synchronously between awaits.

- **State.** An `IO_TAG_EFFECT_POLL` node's field 0 is a backend-built state
  closure: `code_ptr` is the poll-fn, `drop_glue` tears down the baked
  arguments, and the environment starts at closure offset 32. **The first
  environment slot is the result slot; the i64 arguments follow in declaration
  order, then leaf scratch.** The poll-fn writes its single i64 result — a
  scalar or a heap base pointer — to the result slot before returning `Ready`.
  This layout is part of the ABI governed by `ABI_VERSION`.
- **Establishment** (`await_poll_node`) reads only field 0. It takes the
  keep-alive reference (§2.20), mints a registrant id and constructs the future.
  It reads no scheduling state (§7.5).
- **Each poll** emits `EffectDispatched` (first poll) or `EffectResumed`,
  projects the waker, brackets the poll-fn call with the registrant id,
  and clears the bracket through a drop guard so a panicking poll-fn cannot
  leave a stale id behind.
- **On `Ready`** it reads the result slot, releases the keep-alive reference
  and eagerly releases every permit the effect holds (§2.9), then returns the
  value. **On `Pending`** it emits `EffectSuspended`.
- **Drop is the cancellation path.** Two fields' drop glue releases the
  effect's permits, deregisters its reactor interest (§2.16) and releases the
  keep-alive reference (§2.20). **There is no hand-written `Drop for
  EffectPoll`; adding one double-releases.**

### 2.6 The async `Par` arm — two-pool join

1. Read the branches in binding order.
2. **Partition by root tag**: `IO_TAG_EFFECT_POLL`-rooted branches go to the
   reactor partition; every other branch goes to the rayon partition.
3. **Rayon partition.** Each branch reads its `(token, capacity)` from its
   root `Effect` node, acquires a permit on the reactor thread, starts a bridge
   lease (§2.21) and `rayon::spawn`s the synchronous stepper. Completion
   returns through a `oneshot` woken via the executor waker. The permit is held
   across the bridge. If a runtime error or dispatch fault is already set when a
   parked branch is admitted, the branch returns without spawning; this
   preserves left-to-right semantics for a failed capacity-1 sibling.
4. **Reactor partition.** Each branch runs the async trampoline under a fresh
   child strand; poll leaves inside it acquire through the `ctx` vtable (§7).
5. Join both partitions concurrently on the reactor thread and merge the
   results by binding index into the one results buffer the continuation
   consumes.

- **Never block the reactor on rayon.** `block_on(rayon_join)` on the reactor
  thread starves every poll leaf; the wakeable bridge is the only rayon→reactor
  handoff.
- **The worker→join error ferry.** A worker's runtime error is taken from the
  worker's slot and re-raised on the reactor thread. The first branch to
  complete wins, not the first in source order, except for same-token
  capacity-1 branches, which run serially in order.
- **Two sites implement the ferry:** `run_blocking_branch` (async) and the
  synchronous `dispatch_par_branches_with_trace`. A change to ferry semantics
  touches both. Extract a shared helper only when a third caller appears.
- **Nested `Par` on a worker** uses the synchronous dispatcher, which still
  groups branches by token and runs each non-zero-token group serially.
- **Blocking I/O is uncapped by design.** A slow but completing blocking branch
  holds the `OneShot` backstop off (§8.2).

### 2.7 Test fixture leaves

`async_read_pollfn` (a non-blocking `recv` that registers readable interest)
and `timer_write_pollfn` (a timer-driven feeder) are `#[cfg(test)]` fixtures.
They prove the reactor, waker projection, `EffectPoll` and poll-leaf overlap
without the macro, backend or loader path. End-to-end poll leaves come from
`declare_platform!` DLLs and the runtime `sleep` leaf (§2.18).

### 2.8 The token permit pool

A host-owned permit map bounds how many effects on one token are in flight.
It lives beside the reactor for the same `--link` reason (§1).

| Carrier | Behaviour |
|---|---|
| token `0` | no acquire; full overlap |
| token *T*, capacity 1 | strictly serial; admission is FIFO |
| token *T*, capacity *N* ≥ 2 | at most *N* in flight; later acquirers park FIFO |

- **Sizing.** A token's slot is created on its first acquire, sized
  `min(max(capacity, 1), degree)`, and never resized. **First writer wins.** A
  later disagreeing capacity is a platform defect: it never raises the ceiling
  and never aborts.
- **Two acquire paths, one map.** Rayon-partition branches and the global
  budget use the `AcquirePermit` future and RAII `Permit`. Poll leaves use the
  vtable `acquire` against the same map through the held ledger (§7.2).
- **Single-threaded by construction.** Every acquire, park, release and
  cancellation runs on the reactor thread, so the map is a plain `RefCell` with
  no atomics and no lock. A release detaches its waker under the borrow and
  wakes after dropping it.
- **Ordering.** A permit gives exclusion, not order. Same-resource order comes
  from the inference (§7.7). Capacity 1 admits FIFO. Capacity *N* ≥ 2 promises
  no order, and callers may not rely on the FIFO queue there.

### 2.9 Permit release for a poll leaf

The permit wraps the leaf's whole establish→`Pending`→…→`Ready` arc. The
platform poll-fn acquires it (§7.2); the host releases it.

- **Eager on `Ready`.** A `join_all` holds a completed leaf until the whole
  join finishes, so release on drop would starve same-token waiters behind the
  slowest sibling.
- **On drop.** A leaf that never reached `Ready` releases through its guard.
- **Exactly once.** The first release removes the ledger entry, so the second
  is a no-op.
- **No self-deadlock.** A parked leaf holds its slot but not the thread. A
  poll-fn's acquire is idempotent per effect and cannot re-enter admission on a
  token it already holds.

### 2.10 Evidence

Module evidence lives in `reactor/tests.rs` and `io/tests.rs`: waker projection
and poll-leaf overlap; the pool's sizing, parking, FIFO and first-writer-wins
behaviour; the degree throttle; release on `Ready` and on drop, with no double
release; stale-waiter removal and permit forwarding on a cancelled parked
acquire; reactor-interest deregistration on drop; the `sleep` deadline;
supervisor panic and runtime-error capture; the trampoline-frame guard; the
keep-alive; the bridge-join ordering observer and its planted early-release
detection proof; and the liveness predicates
`reactor_is_armed` and `oneshot_backstop_action`.

End-to-end cells are in `tests/concurrency_*.rs`. The evidence plan and
acceptance belong to `qa` (`tests/plan/`).

### 2.11 Launch-and-continue

An `IO_TAG_LAUNCH` node detaches its field-0 sub-tree as a supervised strand
that nothing joins. The backend's independence analysis bakes the node
(`io-trampoline.md` §15). The runtime arm:

1. acquires a global-budget permit (§2.13). An exhausted budget parks the
   launching strand, which is how an accept loop feels backpressure;
2. mints a child strand and emits `StrandLaunched { strand, parent }`;
3. **moves the sub-tree out**: it reads field 0 and writes the `0` sentinel, so
   the node's null-guarded drop glue does not free it (`io-trampoline.md` §15.5).
   It also reads the result disposer from field 1;
4. spawns the supervised strand, which owns the sub-tree, the disposer, the
   global permit and a cloned `ReactorEnv`;
5. yields `Unit` at once.

| | `Par` (§2.6) | Launch (§2.11) |
|---|---|---|
| Join | all branches before the continuation | none |
| Result | merged by binding index | discarded; the node yields `Unit` |
| Runtime error | re-raised into the parent | handled by the supervisor (§2.12) |
| Lifetime | the expression's | as built, the supervisor's; the spec requires its cancellation context's (§2.19) |
| Bound | per-token permits | the global budget |

### 2.12 The supervisor

The supervisor is the single-threaded equivalent of a `JoinSet`: a
`FuturesUnordered` of supervised strand futures, built in the drive (§2.4) and
reached through `ReactorEnv`.

Each supervised strand:

- runs the sub-tree under `catch_unwind`, so a Rust panic never unwinds into
  the executor;
- takes the runtime-error slot **synchronously at its completion boundary**,
  with no await between completion and capture;
- on success disposes the result through its disposer and emits
  `StrandCompleted`; on a runtime error or panic applies the policy;
- consumes its detached sub-tree exactly once, then drops its global permit.

**Policy.** The only policy is `LogAndDrop`: emit `StrandFailed { strand,
message }` and drop the strand. It never re-raises and never aborts the drive.
Mapping a failure to a client response is the application's job.

Supervision decides where a fault goes. It does not decide when a strand is
cancelled; that is its cancellation context's (§2.19), and a cancelled strand is
not routed to the policy.

**Drive.** The supervisor's set is borrowed only for each synchronous
`poll_next`. A non-empty supervisor counts as armed for the deadlock detector,
but does not hold off the `OneShot` backstop (§8.2).

### 2.13 Admission budget and degree

Both are parameterisations of the §2.8 pool, not new machinery.

- **Degree** is the program's in-flight throttle. It clamps every token slot to
  `min(capacity, degree)`. It is read from `CRANELISP_DEGREE` at drive
  construction; unset, unparsable or zero means no throttle.
- **Global budget.** The reserved token `u64::MAX` is sized to the degree. Every
  launch acquires one global permit before spawning, and the strand holds it for
  its lifetime. Its events are `GlobalBudgetParked`/`Acquired`/`Released`.
- The CPU spark budget shares only the permit-counter shape, realised
  separately on rayon. Over budget, I/O parks while CPU work folds inline.

### 2.14 Strand drop releases its resources

A supervised strand ends by completion, caught failure or a `clear()` of the
supervisor. Each path drops the strand future, and with it any in-flight
`EffectPoll` (permits, interest, keep-alive), any parked `AcquirePermit`
(§2.17), the trampoline frame (§2.15.1) and the global permit. No release path
is specific to supervision.

### 2.15 `race`/`select` — cancellation is drop

`race` and `select` lower to one node, `IO_TAG_SELECT`, whose field 0 owns a
`Vec (IO a)` of branches and whose field 1 is the branch-result disposer
(`io-trampoline.md` §16). `race a b` is a two-element vector.

The runtime arm:

1. reads the branch pointers from the vector **without RC**. The node owns the
   vector for the tree's lifetime, and `consume_io_tree` later reclaims every
   branch, winner and losers alike. Nothing is moved out;
2. raises the empty-select runtime error when there are no branches (§9);
3. builds one async-trampoline future per branch under a fresh child strand;
4. races them with `select_all`, which re-polls every pending branch on each
   turn;
5. emits `StrandCancelled { reason: RaceLost }` for each loser, then drops the
   losers. **The drop is the cancellation.**
6. returns the winner's value to the surrounding `Bind`.

A dropped branch releases through whichever point it was suspended at:

- a parked acquire removes its own waiter or forwards a permit it was already
  given (§2.17);
- an in-flight `EffectPoll` releases its permits, deregisters its interest and
  releases its keep-alive (§2.9, §2.16, §2.20);
- an admitted blocking branch marks its bridge cancelled and releases its
  permit (§2.21);
- the trampoline frame releases the fresh nodes it holds (§2.15.1).

There is no cancellation-specific teardown checklist: ownership determines the
release order.

#### 2.15.1 The trampoline-frame guard

The async trampoline's in-flight `current` node and continuation stack are
manual-RC words, so dropping the future would leak them. A frame guard owns
them while the walk runs.

- On drop while armed, it consumes the frame's reference to a **fresh**
  (trampoline-produced) current node and to each un-popped fresh continuation.
- A non-fresh node belongs to its owning tree and is left for that tree's
  teardown. Branch roots of a `Select` are always non-fresh.
- Every normal return disarms the guard, so a completed walk releases nothing
  twice. The synchronous stepper uses the same guard; a cancelled return
  leaves it armed.

### 2.16 Reactor-interest deregistration on drop

Without active deregistration, a cancelled leaf's fd waiter and `mio`
registration persist until the fd readies, which may be never. That leak is
unbounded under repeated cancellation in a long-running server.

- Every fd and timer entry carries its registrant id (§2.1).
- On drop, `EffectPoll`'s interest guard releases the effect's permits
  (§7.3), then removes every fd entry with its id (with a `mio` deregister) and
  every timer waiter with its id. The removal scans live waiters; cancellation
  is rarer than steady state.
- **No eager deregistration on `Ready`.** A fired fd entry was already removed
  by `turn`, and a leftover timer tombstones. Unlike the permit, interest
  causes no `join_all` starvation.

### 2.17 Cancelling a parked acquire

An `AcquirePermit` dropped while parked would otherwise leave its waker queued.
A later release would wake the dead waker, strand the freed permit and starve
the next live waiter.

- Each parked waiter carries an id. On drop, a still-queued waiter
  `retain`-removes only its own entry. That preserves FIFO order and with it
  capacity-1 admission order.
- **Woken-then-cancelled forwarding.** If the waiter was already popped and
  woken — a permit freed for it — but is dropped before re-polling, it wakes
  the next front waiter. Otherwise that waiter strands under an executor that
  re-polls only woken futures, such as the supervisor.
- Rejected alternatives: *pop-until-live* (a `Waker` carries no liveness
  signal) and *wake-all* (a thundering herd that destroys capacity-1 order).

### 2.18 `sleep` and `timeout`

- **`sleep`** is a runtime-provided, tokenless poll leaf: `runtime/sleep_pollfn`,
  exported under that name for `--link` and listed in the catalog. The
  backend's `sleep` lowering bakes it as a poll node's `code_ptr` rather than
  loading it from a platform GOT slot. Its first poll computes the deadline and
  registers a timer; it returns `Ready(Unit)` once the deadline passes and
  never re-arms.
- **`timeout`** is stdlib `.cl` (`stdlib/core/io.cl`): a `race` of
  `(map-io Some io)` against `sleep` mapped to `None`. The losing arm is
  cancelled by the §2.15 drop, so `timeout` adds no runtime mechanism.

### 2.19 Cancel-on-disconnect, graceful shutdown and cancellation ownership — open

`spec/10-io.md` §10.12.10 requires both patterns, and both are `race`
compositions. The cancellation-ownership rule they rest on is
`spec/10-io.md` §10.12.9 and `effect-concurrency.md` §9.

- **Cancel-on-disconnect** is `race handler (await-disconnect conn)`. The
  runtime half is §2.15. **No platform ships a disconnect-detection leaf.**
- **Graceful shutdown** is the `race` of the server's work against the
  platform's shutdown-signal effect. **No platform ships that leaf.** It needs
  no runtime trigger, no supervisor-clearing control node and no
  program-visible cancel surface. `CancelReason::Shutdown` has no producer;
  `Supervisor::clear` runs only when the backstop or the deadlock detector
  terminates the drive.
- **As-built narrower than the spec: a launched strand is not owned by its
  cancellation context.** Launch (§2.11) spawns into the one per-drive
  supervisor with no link to the `race`/`select` branch it executes in. The
  §2.15 drop therefore cancels a loser's inline and worker effects and leaves
  the strands it launched running to completion, contrary to §10.12.7 item 5.
  Widens when per-context ownership of launched strands is designed here; no
  mechanism is chosen yet.
- **Drain on normal completion** (§10.12.7 item 6) is §2.4 step 3.

### 2.20 State-closure keep-alive across suspension

This realises bounded-context invariant 15. A launched strand's sub-tree can be
torn down while its last poll effect is still parked. That teardown runs the
state closure's drop glue and would free the baked arguments under the pending
poll-fn.

- **Establishment takes one extra reference** on the state closure (`rc_inc`)
  and hands it to the `EffectPoll`. Field 0 is left untouched, so the node's
  own teardown still releases the node's reference.
- The `EffectPoll` releases the extra reference exactly once: after reading
  the result slot on `Ready`, or on drop. The closure is freed at the later of
  node release and effect resolution.
- **Rejected: move-out with a sentinel.** It frees every poll closure eagerly
  on `Ready`, including an `accept` closure that captures the listener, and so
  wedges the accept loop.
- The backend's state-closure layout and drop-glue obligation are unchanged.
  Keep-alive is runtime-owned.

### 2.21 The rayon→reactor bridge join

The worker, not the awaiting future, acknowledges a blocking branch's lifetime.
A cancelled `Select` loser drops its future while the worker may still be
walking the caller's tree.

- **The owner already exists.** The caller-tree reference held across
  `cranelisp_run_io` → `drive_io` → `block_on_reactor` stays live until every
  bridge child has acknowledged exit. The join adds no branch increment, no
  move-out and no side table of heap owners.
- One join state per drive holds an atomic live count and a clone of the bridge
  waker.
- Each spawn creates one ticket. **The worker's lease is the ticket's only
  strong owner.** The reactor-side cancellation guard holds a weak reference
  and the permit, so it can request cancellation but never retain a worker.
- Normal receipt disarms the guard and releases the permit. Dropping the guard
  while armed marks the ticket cancelled (`Release`) and releases the permit at
  once, without touching the lease. Cancellation before admission has no ticket
  and uses §2.17.
- Dropping the lease decrements the count (`AcqRel`), treats an underflow as a
  located invariant failure, and wakes the reactor, so a worker unwind cannot
  strand the count. The executor reads the count with `Acquire`. If accounting
  disagrees, retain rather than tear down.
- The synchronous stepper checks the borrowed cancellation probe before each
  node and before each continuation call, and threads the same probe through
  nested synchronous `Par`. A call already entered runs to completion. A value
  produced on a cancelled path is disposed through the branch's result
  authority
  ([trampoline ownership transitions](ownership-and-disposal.md#7-trampoline-ownership-transitions)),
  and its runtime error is suppressed: cancellation is not a fault.

**Order:** cancel the loser → mark cancelled → release reactor resources → the
worker stops at its next boundary → its result is disposed and its error
suppressed → the lease drops and wakes → the executor observes zero → caller-tree
teardown. The same count drives armedness, the backstop hold-off and the return
gate (§2.4). The worker→reactor release/acquire edge also orders a worker's
last read of a branch node before root teardown discharges that node
([`ownership-and-disposal.md`](ownership-and-disposal.md) §6.1–§6.2). A
blocking foreign call is not pre-emptible, so the guarantee is structural, not
a time bound.

---

## 3. The strand observability sink

`StrandId` (`ROOT = 0`; `next_strand` mints from 1) correlates every dispatch,
suspension, launch and cancellation. Events go to a process-global buffer.
While not recording, `emit_strand_event` costs one lock and an `is_none` check.
`start_strand_recording` and `drain_strand_events` are the reader interface.

| Event | Emitted by |
|---|---|
| `EffectDispatched` / `EffectSuspended` / `EffectResumed` | `EffectPoll` (§2.5) |
| `TokenAcquired` / `TokenParked` / `TokenReleased` / `TokenCapacityMismatch` | the `AcquirePermit`/`Permit` path only — rayon-partition branches (§2.8) |
| `GlobalBudgetParked` / `GlobalBudgetAcquired` / `GlobalBudgetReleased` | the global budget (§2.13) |
| `StrandLaunched` | the launch arm (§2.11) |
| `StrandCompleted` / `StrandFailed` | supervised strands (§2.12) |
| `StrandCancelled { RaceLost }` | `select` losers (§2.15) |

As built:

- Poll-leaf acquires through the vtable emit no `Token*` or mismatch events.
- `SparkCreated`/`SparkForced` and `CancelReason::Shutdown` have no producer.
- The only readers are in-crate tests; there is no `/strand` dump in the binary.

The buffer is process-global and single-recording; tests rely on nextest's
process-per-test isolation.

## 4. IO node dispatch

| Tag | Async trampoline (reactor thread) | Synchronous stepper (rayon worker) |
|---|---|---|
| `Pure`, `Bind` | interpreted inline | interpreted inline |
| `Effect` (blocking thunk) | forced synchronously | forced synchronously |
| `EffectPoll` | awaited (§2.5) | not interpreted |
| `Par` | two-pool join (§2.6) | token-grouped rayon dispatch |
| `Launch` | detached (§2.11) | not interpreted |
| `Select` | raced (§2.15) | not interpreted |

After each arm, the async trampoline checks the runtime-error and
dispatch-fault slots and stops before feeding a continuation. **The synchronous
stepper panics on an unknown tag**, so a poll, launch or select node reached
inside a rayon-partition branch — a `Bind`-rooted branch whose chain later
produces one — is not handled (§5).

## 5. Known limits and potential extensions

- **Nested launch.** A launch from inside a supervised strand re-enters the
  supervisor's borrow during `drive` and panics. Launches are reached only from
  the top-level accept loop. *Trigger:* a program that launches from a launched
  strand or from a `race` branch; the design opens with `arch`.
- **Mixed-shape `Par` branches.** Routing is by root tag. A poll-rooted branch
  forces its nested blocking effects synchronously on the reactor thread, and a
  rayon-routed branch cannot interpret poll, launch or select nodes (§4).
  *Trigger:* lowering that produces such a branch; `qa` intake decides whether
  it is reachable today.
- **Per-strand runtime-error attribution.** Detached strands share the reactor
  thread's error slot. Capture at each strand's completion boundary covers the
  common case, but an error ferried from a sibling's blocking branch could be
  attributed to the strand that completes first. *Trigger:* an observed
  misattribution; the fix is a per-strand error channel.
- **Supervisor policy per effect kind.** Only `LogAndDrop` exists, and nothing
  configures it. *Trigger:* a platform needing a different failure mapping.
- **Drive-mode selection.** `Server` mode is chosen only by
  `CRANELISP_DRIVE_MODE=server`; no run-context signal selects it (§8.2).
  *Trigger:* a server entry point that must not depend on the environment
  variable.
- **Lazy reactor construction.** Construct no `mio::Poll` until the first
  `Pending`. Every `Pending` source must force construction before it parks:
  fd and timer registration, the `Par` blocking bridge, and the capacity park,
  whose permit-release wake also travels through the bridge waker.
  *Trigger:* a measured per-drive construction cost that matters to a delivered
  workload (`effect-concurrency.md` §6).
- **The deadlock detector panics** (§8.2), unlike the backstop's clean exit.
  *Trigger:* a production report where the panic's abort path costs time, as
  the backstop's did.

## 6. Single construction site

The reactor, `HostCtx`, waker, pool, supervisor and bridge join are built once,
in `block_on_reactor`, reached through `cranelisp_run_io` in every mode. The
binary and `cranelisp-exe-bundle` must never grow a parallel builder.

The platform-DLL `HostCallbacks` value is a separate, hand-mirrored surface.
It carries only `alloc` and `alloc_with_tag` and does not widen
(bounded-context §4b). A poll-fn receives `HostCtx` and a waker at poll time,
so the reactor adds no host callback.

Principles: 7 (single source of truth), 3 (dependency flows toward stability),
8 (no mode divergence).

## 7. The host `ctx`-vtable handle model

`effect-concurrency.md` §4.1.1 is the model; `poll-leaf-authoring.md` is the
platform half; `io-trampoline.md` §17 is the emitted half.

### 7.1 The model

A resource handle is an opaque ADT carrying the platform's own id. **The host
never introspects it.** The platform poll-fn projects a token from its handle,
calls `ctx.acquire` itself, performs its non-blocking syscall, and on
`WouldBlock` registers interest and returns `Pending`. The host owns the permit
map, a per-effect held-permit ledger and release. No scheduling state rides on
an IO node or a value header.

### 7.2 `acquire` and `retire`

`acquire(host, token, capacity, waker) → Acquired | Parked`:

- token `0` is `Acquired` without touching the map or the ledger;
- **idempotent per effect** — a token the effect already holds is `Acquired`
  without a second permit, so a re-poll may re-acquire freely;
- a free slot is decremented and recorded in the ledger under the effect's
  registrant id;
- a full slot enqueues an id-tagged clone of the waker and returns `Parked`.
  The host never blocks inside `acquire`;
- a fixture reactor with no pool resolves `Acquired`.

`retire(host, token)` removes the token's slot and wakes its parked waiters so
they re-poll and observe the closed resource through their own syscall. It is
idempotent and needs no drain barrier. A full-duplex handle retires each token
the platform projected for it.

**There is no `release` entry**, and `PollFn` has no scheduling out-parameter.

### 7.3 Release keyed by effect identity

- **On `Ready`,** `EffectPoll` releases every permit in the effect's ledger
  entry, incrementing each slot and waking its front waiter, before returning
  the value (§2.9).
- **On drop,** the interest guard releases the same ledger entry and then
  deregisters the effect's interest (§2.16). **Cancellation never re-enters the
  poll-fn.**
- Removing the ledger entry makes the second release a no-op.

### 7.4 Why release is host-owned

A cancelled effect is a dropped future, so its poll-fn never runs again. A
platform-side release could not fire on cancellation. The host already keys
permits and interest by effect identity, so a platform release entry would
duplicate that state.

### 7.5 Scheduling-blind establishment; roles are manifest facts

`await_poll_node` reads field 0 and nothing else from the node. The produce,
consume, retire and none leaf roles are compile-time manifest facts for the
inference and for platform authors. The host has no runtime role branch. The
handle reaches the poll-fn as `arg(0)`, the second environment slot; the
platform, not the trampoline, reads the id from it.

### 7.6 Singleton `read-line`

`read-line` acquires a fixed non-zero stdin token with capacity 1
(`poll-leaf-authoring.md` §3). The permit map then admits at most one
in-flight read, with no host special case.

### 7.7 Within-token source ordering

The trampoline never sees tokens, so it cannot restore order.

- **Same explicit handle:** the inference refuses to disjoin the effects, so
  they stay a serial `Bind` in source order.
- **Shared singletons** such as stdout: the inference never detaches them.
- **Capacity-*N* pools:** order is not promised beyond exclusion.

`effect-concurrency.md` §8.2 is authoritative; do not re-derive the inference
here. Effects from different provenances aliased onto one token get exclusion
but no ordering. An ordered form would be a separate, explicit API.

## 8. Liveness — no-progress detection, not a wall-clock cap

### 8.1 The problem

A healthy idle server parked on its listener fd and a stuck reactor both make
no progress for arbitrarily long, so a wall-clock cap cannot separate them.
**Armedness** can.

### 8.2 The deadlock detector and the drive modes

**Deadlock detector (both modes).** After a top-future `Pending`, if the
pending-wake flag is clear and nothing is armed, the drive clears the
supervisor and panics with a located message. The reactor is armed when any of
these holds:

- a live fd waiter or a live **timer waiter** — not a `timer_heap` entry, which
  may be a tombstone and would read falsely armed;
- a live bridge;
- a non-empty supervisor;
- a parked permit waiter.

**`OneShot`** (the default, for `--run`, `--link` and REPL evaluation) adds a
no-progress wall-clock backstop that catches an armed leaf that never readies:

- Its default is 30 s. `CRANELISP_REACTOR_BACKSTOP_MS` overrides it.
- **Only a live bridge holds it off,** because blocking I/O is uncapped to match
  sequential execution. A non-empty supervisor does not: an armed-but-hung
  handler must still hit the backstop. The predicate `oneshot_backstop_action`
  takes no supervisor input.
- The per-turn block is capped at the remaining backstop window, so the
  backstop fires on time.
- A fired backstop clears the supervisor, prints the diagnostic and **exits
  with status 70** (`EX_SOFTWARE`), not a panic. A panic would cross the
  `cannot_unwind` program boundary and core-dump. The unit-test seam
  (`block_on_reactor_capped`) panics instead, so tests can observe the trip.

**`Server`** (`CRANELISP_DRIVE_MODE=server`) has no wall-clock cap. An
idle-but-armed server runs indefinitely; its deadlines come from `timeout` and
cancel-on-disconnect. Both modes re-check every 5 s at most.

**Rejected: a per-leaf "may block indefinitely" descriptor flag.** It would add
ABI surface for a fact that armedness already supplies, and every new leaf would
have to declare it correctly. If a case ever needs per-leaf hang detection,
propose the flag to `arch`.

### 8.3 Evidence obligations

- **Module tier:** detector trips on a `Pending` future with nothing armed;
  detector silent when an fd is armed; backstop predicate ignores the
  supervisor and holds off only on a bridge; capped drive panics on the test
  seam.
- **End-to-end** (`qa`): a server idling past 30 s in `Server` mode is then
  served; a stuck one-shot aborts promptly; an armed-but-hung one-shot exits 70
  without a core dump.

## 9. Empty `select`

`(select [])` raises the recoverable runtime error
`select over empty collection` through the standard runtime-error slot
(`spec/10-io.md` §10.12.8; `spec/12-runtime.md` §12.4.4 and §12.7.2). The arm
returns before constructing the race; the trampoline's post-arm slot check
stops before any continuation sees a value. A `catch-runtime-error` boundary
recovers it; otherwise it is fatal to the evaluation.

## 10. Cross-references

- `design/arch/effect-concurrency.md` — the concurrency model; Appendix B is
  the implementation status.
- `design/arch/bounded-contexts.md` §4b (intrinsics hosting, invariant 15), §5
  (the platform C-ABI async leaf), §6 (the host-client binary).
- `design/arch/platform-interface.md` §6.8 — `HostCtx`, `Waker`, `PollFn`,
  `Poll` and `Acquire` layouts, and `ABI_VERSION`.
- `design/backend/io-trampoline.md` §12 (poll node), §15 (launch node), §16
  (select node), §17 (the uniform poll node under the vtable model).
- `design/platform/poll-leaf-authoring.md` — the poll-fn skeleton, the roles,
  the stdin token and resource handles.
- [`ownership-and-disposal.md`](ownership-and-disposal.md) — heap ownership, IO
  node teardown, result disposal and the node lifetime the bridge join orders.
- `design/int/io-integration.md` — the host-client side.
- `design/arch/sequences/concurrency-scheduler.mmd` — the reactor participant.
