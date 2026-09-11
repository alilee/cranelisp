# Observability — the int-owned trace sinks

**Status:** DESIGN — refreshed S122 Phase 5 against HEAD source. Supersedes the
S61 Slice-0 authoring, which described two proposed logs and a `/backend`
co-owner that no longer exists.
**Master:** `int.md` (§11 is the four-sink one-glance summary; this doc is the
canonical carrier for activator semantics, placement constraints and dump
mechanics).
**Owner surface:** int. Code homes: `src/observability.rs` (+ `src/observability/tests.rs`),
`src/io_trace.rs`, `src/got_trace.rs`, `src/sched_dump.rs`.

> **Section numbers are load-bearing.** `src/main.rs`, `src/worker.rs`,
> `src/session_v4/nice_worker.rs`, `src/observability/tests.rs`,
> `tests/facade_pif_rows.rs` and `tests/spec_10_io.rs` anchor `// spec:` and
> rationale comments on §3.1, §4, §7 and §7.1. Renumber only with the test
> owner.

## 1. Purpose

The int surface carries five standing inspection instruments: three event-ring
traces, one per-key introspection store, and one signal-triggered live-state
snapshot. They are permanent infrastructure, not sprint scaffolding — a race or
hang investigation reaches for them first rather than starting from ad hoc
`eprintln!`.

Structured rings rather than `eprintln!` because the compiler runs a persistent
worker pool: events from several threads interleave in stderr, cannot be
reconstructed into a causal sequence, and stderr contention distorts the timing
the investigation depends on. Every ring therefore records on a shared monotonic
timebase (§6) and merges at dump time (§7).

## 2. Activators — the int-owned inventory

| Activator | Sink | Observes | Code home |
|---|---|---|---|
| `CRANELISP_SCHEDULER_TRACE=1\|*\|<module>[,<module>…]` | scheduler ring | scheduler/worker pool transitions, dependency registration, `is_typechecked` hit/miss, REPL reload, symbol-table ensure | `src/observability.rs` |
| `CRANELISP_IO_TRACE=1\|*` | IO ring | IO trampoline transitions, platform effects, continuation push/pop, `Par` spark/join | `src/io_trace.rs` |
| `CRANELISP_GOT_TRACE=1\|*` | GOT ring | GOT-slot writes: `JitWrite`, `LinkerWrite`, `Redefinition`, plus int's `SlotFreeze` / `TrapPatch` | `src/got_trace.rs` |
| `CRANELISP_SCHED_DUMP_ON_SIGUSR1` (any value) | scheduler-state snapshot | live pool / `blocked_on` / waiter / queue state on `SIGUSR1` | `src/sched_dump.rs` (§8) |
| *(none — `RunMode::Repl`)* | introspection store | per-symbol metadata (§10; shape in `int.md` §4.3) | `SharedState.introspection` |

There is no repository-wide environment-variable inventory. `tests/CLAUDE.md`
§"Diagnostic env vars & assertions" lists the *other* surfaces' trace variables
for test authors and does not cover the int sinks. This table is canonical for
the int-owned activators only; it does not claim to be the project's whole
diagnostic surface.

## 3. The three ring sinks

Event taxonomies are enumerated in source (`SchedulerTraceTag`,
`cranelisp_intrinsics::io_observer::IoEventTag`,
`cranelisp_backend::got_observer::GotEventTag` + int's `StoredTag`). This doc
does not mirror them — a hand-copied tag list is a second authority that decays
silently.

### 3.1 `CRANELISP_SCHEDULER_TRACE`

Filter values, in the order the parser tries them:

- `1` or `*` — record every event.
- a comma-separated module-name list — record only events whose module payload
  matches one entry exactly. Bulk events, which name no module, always pass.
- unset, empty, whitespace-only, or a list that reduces to nothing — off.

A malformed value never panics; it degrades to off. The scheduler sink is the
only one with a payload filter, because it is the only one whose event volume is
dominated by a single dimension (the module) an investigator already knows.

**Cross-crate emission.** `cranelisp-typecheck` cannot depend on the binary
crate, so its symbol-table-ensure observation arrives through an installed
function pointer (`cranelisp_typecheck::install_symbol_table_ensure_hook`,
installed once from `main`). The uninstalled cost is a relaxed load plus a null
check. This is the same consumer-side shape as §3.2/§3.3, expressed as a hook
rather than an observer struct because typecheck emits exactly one event class.

### 3.2 `CRANELISP_IO_TRACE`

Values `1` or `*`; anything else is off. The taxonomy is owned by
`cranelisp-intrinsics` (`io_observer`) — the trampoline it observes is
backend-emitted runtime library, not an int concern (`design/intrinsics/reactor.md`;
int is a host-client only). int registers `record` as the observer and maps each
`IoEventTag`/`IoEvent` 1:1 onto its own ring representation.

### 3.3 `CRANELISP_GOT_TRACE`

Values `1` or `*`; anything else is off. Backend emits `JitWrite` and
`LinkerWrite`; int's own redefinition machinery adds two tags backend has no
name for — `SlotFreeze` (an ABI-changing redefinition froze the old slot and
allocated a fresh one) and `TrapPatch` (a BROKEN symbol's slot was patched to a
trap stub), per `session-transaction.md` §9.3.

## 4. Placement and hard constraints (MANDATORY)

| Sink | Emits from | Ring lives in |
|---|---|---|
| Scheduler | `src/scheduler.rs`, `src/worker.rs`, `src/process_form/`, `src/session_v4/`, and typecheck via the installed hook | `src/observability.rs` |
| IO | `cranelisp-intrinsics` (the trampoline) through `register_io_observer` | `src/io_trace.rs` |
| GOT | `cranelisp-backend` through `register_got_observer`, plus int's own redefinition sites | `src/got_trace.rs` |

**The emitting crate owns the taxonomy and publishes a registration function;
int owns every ring buffer, formatter and dump.** That split is the whole
pattern — learn one sink and the other two are mechanically the same. It keeps
the event shape free to evolve with the scheduler and the runtime instead of
with any published cross-crate surface.

Four constraints hold across all three:

1. **No event type appears in a boundary type.** Not in `cranelisp-types`, not
   on `SymbolTable<C, L>` / `ModuleEntry` / any cross-crate struct. *Grade:
   measured* — `src/observability/tests.rs::harvest_trace_event_types_absent_from_boundary_crate_sources`
   scans the boundary crates' sources, and `tests/facade_pif_rows.rs` +
   `tests/spec_10_io.rs` assert the observer-registration homes against the
   `public-api.txt` baselines.
2. **No event type is ever serialized.** Not in `.meta.json`, cache entries,
   on-disk artifacts or module bundles. Events are in-memory, process-lifetime
   only; no `Serialize`/`Deserialize` derive exists to skip. *Grade: structural*
   — the types carry no serde derive, so a serialized field would not compile.
3. **No ring allocates on the Cranelisp heap.** Host allocator only. A trace
   that allocated through `cranelisp_alloc` while RC tracing observes
   allocations would observe its own allocations; the recursion is unbounded.
4. **Events are `Send`.** Recording is thread-local and the dump-time merge
   *moves* events, so no `&Event` crosses a thread and no site requires `Sync`.
   *Grade: structural, all three sinks* — each sink's published-buffer registry
   is a `static OnceLock<Mutex<Vec<Vec<Event>>>>`, which compiles only when the
   event type is `Send`; a non-`Send` field fails at the registry line. The
   scheduler and IO modules additionally carry a `const _` `assert_send_sync`:
   redundant for `Send`, and naming a `Sync` nothing uses. The GOT module
   carries none, and none is owed.

## 5. Parse-once activation

Each sink parses its variable **once**, into its own `OnceLock`, on first touch.
Per-event `std::env::var` is forbidden: it is O(events) work on the hot path and
takes the process environment lock.

There is no startup hook to prime the parse — the first instrumented call site
initializes it, and a direct `filter()`/dump call does the same. The off-path
cost is one relaxed load, a null check and a well-predicted branch (§9).

## 6. Event shape

Each ring owns its own event type — there is no shared event type in
`cranelisp-types` (§4, constraint 1). All three carry the same four-field
skeleton:

- **`timestamp`** — monotonic nanoseconds elapsed since a single process-wide
  anchor, `cranelisp_intrinsics::trace_anchor()`. **One anchor for all three
  sinks** is what makes a scheduler dump and an IO dump interleavable; a
  per-sink anchor would silently destroy that. Monotonic rather than wall-clock
  because the merge must be stable and wall-clock can skew.
- **`thread_id: ThreadId`** — for display.
- **`thread_ord_id: u64`** — a process-monotonic ordinal assigned on the
  thread's first event. This, not `ThreadId`, is the merge tie-breaker:
  `ThreadId` has no stable order, so sorting on it would make dump ordering
  irreproducible across runs. Each sink numbers threads independently, since
  each merges independently.
- **`tag` + `payload`** — the taxonomy discriminant and its tag-dependent data,
  plain owned data only (no references, locks or JIT handles), which is what
  makes `Send + Sync` derivable.

## 7. Dump

Recording is per-thread: a bounded `VecDeque` ring with FIFO overflow — at
capacity the oldest event is dropped so a long run cannot grow unbounded.
Capacities are `65_536` (scheduler), `65_536` (IO) and `16_384` (GOT).

All three **buffer and flush at teardown**; none streams. At flush the thread
drains every published buffer plus its own live buffer, sorts by
`(timestamp, thread_ord_id)` and writes one line per event to stderr:

```text
[SCH|IO|GOT] ts=<ns> thr=<ThreadId>/<ord> <Tag>\t<payload>
```

The scheduler dump is preceded by the marker line
`=== CRANELISP_SCHEDULER_TRACE DUMP ===` so its section is unambiguous in
interleaved test output. The IO and GOT dumps carry no marker — their `[IO]` /
`[GOT]` line prefix already identifies them, and a marker would be a second
thing to keep in step with the format. A flush with an empty merge writes
nothing at all, so an unset activator produces byte-identical output to a build
without the instrument.

**Worker publication.** A thread's ring dies with the thread, so a thread that
emits and then exits must publish its buffer into a process-wide registry first;
the flushing thread merges the registry with its own live buffer. Without this a
dump shows only main-thread events. The scheduler and GOT sinks publish from
both worker pools. The IO sink exposes the same primitive with no caller — see
§10.

### 7.1 Process-exit and panic wiring

`flush_to_stderr` is not self-triggering. `main` therefore holds, per ring:

1. **An RAII flush guard** at the top of `main`, whose `Drop` flushes on normal
   return.
2. **An idempotent panic hook** chaining the flush *in front of* the previously
   registered hook — the default unwinder terminates the thread and drops its
   thread-local rings, so the drain must happen first. Idempotence is required
   because tests and defensive entry points install repeatedly.

`main` also calls `install_if_enabled` for the two observer-backed sinks, which
registers the observer with its owning crate only when the activator is on.

`std::process::exit` bypasses `Drop`, so every exit site calls the explicit
`flush_traces()` first.

| Path | Mechanism |
|---|---|
| `main` returns normally (REPL, `--link`) | guard `Drop` |
| Panic reaches the top-level hook | chained panic hook |
| `--run` exit-code escape (spec §12.6) | explicit `flush_traces()` before `process::exit` |
| `run()` returned `Err(_)` → exit 1 | explicit `flush_traces()` before `process::exit` |

Deliberately **not** covered: argv-parse `process::exit` paths (they fire before
any event can be emitted, so the flush would be a no-op and an unconditional
`exit` reads more clearly); `std::process::abort()`; and SIGKILL/SIGABRT, which
are kernel-terminated with no user-space flush possible. A subprocess that
aborts before flush produces no dump — that is the failure mode §8 exists for.

## 8. SIGUSR1 scheduler-state snapshot

`CRANELISP_SCHED_DUMP_ON_SIGUSR1` arms a different instrument: not a ring of
past events but a snapshot of *live* coordination state — every module's pool,
its `blocked_on` edge, its waiter list, and the queue contents. It answers the
question a ring cannot when a child hangs with every compute thread parked on a
futex and nothing queued: which module is stranded, and on what.

**Async-signal safety is the shape constraint.** Taking the scheduler mutex
inside a signal handler is unsound — the handler can interrupt a thread that
already holds it. So the handler does the one async-signal-safe thing, an atomic
store, and a dedicated watchdog thread performs the lock-and-dump on a normal
stack. The handler never locks, allocates or performs IO.

Unset (including the whole test suite) installs no handler and spawns no
watchdog; SIGUSR1 keeps its default disposition. Armed, handler and watchdog
install once per process and each session registers a `Weak` reference, so one
dump covers every live scheduler and a dropped session is not kept alive.

## 9. Off-path cost

The standing budget is that an unset activator is indistinguishable from the
instrument's absence in wall-clock terms.

The authoritative measurement is the criterion microbench
`benches/io_trace_off_path.rs` (`cargo bench --features bench --bench io_trace_off_path`),
which measures filter-off `record_event` at nanosecond resolution — a fixed
~0.29 ns guard. A suite-wall-clock or subprocess ceiling cannot reach that
resolution (process spawn and IO jitter swamp the signal) and is not used.

## 10. Mode discrimination, and known limitations

**The introspection store is REPL-only, gated on `RunMode`.** The store is
`Some(map)` under `RunMode::Repl` and `None` under `--run`/`--link`, decided
once at session construction through `RunMode::populates_introspection()`. The
env-var `CRANELISP_CODEGEN_TRACE` does **not** enable it.

This closes the S63 scoping obligation that asked this doc to adopt Decision
38's `shared.introspection.is_some()` mode discriminator: that proxy was
retired. `design/arch/d1-introspection-repl-only.md` §4 replaced it with the
explicit `RunMode` carrier precisely because a store's presence is not a
readable statement of intent. The three ring sinks share no discriminator with
it — they are env-var-activated in every mode, including `--link`.

Three limitations, all confirmed against source. None is a compiler defect and
none traces to a spec requirement; the first two carry work, the third this
design accepts.

**IO activation and IO recording use different predicates.**
`io_trace::install_if_enabled` registers the observer whenever
`CRANELISP_IO_TRACE` is *present*; `record_event` and the dump accept only `1`
or `*`. `CRANELISP_IO_TRACE=0` therefore registers an observer that records
nothing: an indirect call and an early return per trampoline transition, and
output byte-identical to unset. The intended rule is §3.2's one predicate —
Principle 07, single source of truth — which `got_trace::install_if_enabled`
already realizes by routing registration through `filter_enabled()`. Routing IO
registration the same way leaves no second decision point to observe; the
`src/io_trace.rs` module rustdoc ("## Activation") documents the present-check
and moves with it. Nothing beyond that constructive repair is owed: the
intrinsics observer slot is private, so no external observation distinguishes
the two predicates, and §9's off-path budget is measured with the variable
unset, which the mismatch does not touch.

**IO events recorded on rayon workers never reach the dump.** The scheduler and
GOT sinks publish from both int-owned worker loops at exit.
`io_trace::publish_thread_buffer` exists with no caller and there is no
int-owned loop to call it from: `Par` branches run on rayon's global pool — no
`ThreadPoolBuilder` or exit handler is configured anywhere — whose threads live
to process end. `ParSpark`, `ParSerialGroupEnter` and `ParJoin` are emitted on
the dispatching thread, before the `into_par_iter()` and after the join, and
survive. What is lost is the branch's own work: the branch trampoline's
`TrampolineEnter`/`TrampolineExit` bookends and every interior event it records
sit in the worker's thread-local ring, stranded in a live thread the flushing
thread cannot reach. This is reachable for every `Par` whose branches are
dispatched — the ordinary case. "Dropped at thread teardown" is the wrong
picture; nothing has to exit for the events to be unreachable.

§2 promises trampoline transitions without qualifying them to the dispatching
thread, and §1 gives cross-thread investigation as the reason these sinks
exist. That promise stands and the realization is short of it. **The scope
ruling is open and is not narrowed here.** Three candidate shapes, in no order:

- a branch-completion signal from `cranelisp-intrinsics` that lets int publish
  the worker's buffer — crosses the crate boundary, so `arch` rules it and the
  inter-crate public-API gate applies;
- registering each thread's ring in the process-wide registry at first touch
  rather than publishing its contents at thread exit, so a live thread's events
  are reachable — int-interior, but it replaces §7's publication story for all
  three sinks;
- recording the narrower promise: `Par` branch interiors are not observable,
  with §2, §7 and `int.md` §11 amended to say so.

Owner: `design` (int), with `arch` for the first shape. Trigger: the first
investigation that needs a `Par` branch's interior, or a decision to close the
gap on its own merits. Nothing is owed until it is ruled — the only IO-trace
e2e (`tests/spec_10_io.rs::io_trace_snapshot_pre_post_relocation_byte_equivalent`)
runs a `print`-only program and structurally cannot observe the loss. If branch
interiors are affirmed, the discriminating observation is a multi-branch `Par`
under `CRANELISP_IO_TRACE=1` in `--run`: N `ParSpark` lines — the control
proving the branches were dispatched — against one `TrampolineEnter` line
today, and 1+N once branch events are reachable.

**Ring overflow is silent** — accepted, with its improvement recorded. All
three rings drop the oldest event at capacity and keep no drop counter, so
a truncated dump reads like a short one and an investigator can reason from a
head that was never recorded. This is §7's designed FIFO behaviour, pinned by
`ring_buffer_wraps_at_capacity` in `src/io_trace.rs` and
`src/observability/tests.rs`. No investigation has been misled at the current
capacities; a per-thread drop count reported at dump time is the cheap
improvement if one ever is.

## 11. References

- `int.md` §11 — the master's four-sink summary; §4.3 the introspection store.
- `design/arch/d1-introspection-repl-only.md` §4 — the `RunMode` ruling.
- `design/intrinsics/reactor.md` — the IO runtime int is a host-client of; §0 is
  the seam.
- `design/int/session-transaction.md` §9.3 — the two int-owned GOT tags.
- `design/int/concurrency-architecture.md`, `design/int/signature-body-prepass.md`
  — the scheduler topology whose transitions the scheduler ring observes.
- `design/int/heisenbug-race-closure.md` — the race investigation these
  instruments were built for; retained as reference lineage.
- `design/backend/archive/io-trampoline-trace.md` — the archived S61
  `/backend`-side IO taxonomy record. Historical: the taxonomy now lives in
  `cranelisp-intrinsics`.
