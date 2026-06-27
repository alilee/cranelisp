# Effect concurrency — throughput is free, control is explicit

**Status: ratified target architecture (S92 design), pre-implementation.** This
document states the target *language-level* concurrency architecture for Cranelisp.
It is a confident statement of the destination, not a narrative of how it was
reached — the supersession of the earlier hand-rolled-fiber framing is recorded once,
terse, in Appendix A. The honest as-built ↔ target gap lives in Appendix B
(implementation status).

**Sequencing.** This is scheduled as its **own track**, **after** the agentic-REPL
track and **before** Phase H (the `--release` efficiency tier). The
concurrency → `--release` edge is a **dependency**, not a priority ordering: Phase H's
non-atomic RC, escape→stack/region, Perceus reuse and RC-fusion are sound only against
a *settled* concurrency model — it determines which values cross threads (atomic RC
exists *because* of lenient/`Par` parallelism). The "after agentic-repl" edge is a
priority choice; the two are independent.

**Scope — which concurrency.** Cranelisp has two concurrency axes that share almost
no mechanism. This document is the **language-level** axis: how a *program* gets
concurrency over its effects. The **compiler-internal** axis (how the compiler
schedules its own typecheck/codegen work — scheduler, worker pool, `SharedState`) is
a different subject, inventoried in `design/int/concurrency-architecture.md` and
debt-tracked by FIXME 0425. Do not conflate them.

---

## 1. Thesis — throughput is free; control is explicit

The concurrency model has two complementary halves. They are peers, not
primary-plus-footnote: one is the steady-state engine, the other is what makes the
engine survive contact with reality.

- **Inferred half (throughput).** ALL concurrency that follows from dataflow
  independence + platform-declared resource metadata is extracted **automatically** —
  steady-state parallelism written by nobody, with results **provably identical to
  sequential execution** (observational equivalence, spec §12.4.3). The programmer
  writes ordinary direct-style pure code with **zero concurrency primitives**.

- **Control half (timing).** Everything that branches on completion *timing* —
  cancellation, deadlines, races, supervision — is a first-class **in-language control
  layer interpreted by the trampoline**. This half is irreducible. Dataflow can say
  *"B's value depends on A's value"*; it can **never** say *"B's existence depends on A
  finishing first."* No amount of dependency analysis encodes "cancel the loser" or
  "give up after 200ms."

The control layer is **the vocabulary for an uncooperative environment at the I/O
boundary**: work that takes too long, callers that vanish, effects that fail, load
that floods. The inferred half computes the right answer *assuming a cooperative
world*; control handles **reality refusing to follow the dataflow.** The more
real-time and stateful the workload, the more central control becomes — for a web
service it is production-hardening; for a data pipeline it is backpressure; for a game
it is the whole architecture.

Underneath both halves is one structural commitment: **all state-mutation funnels
through a single serializing interpreter** (§2). Concurrency is permitted only over the
state-free part, or across provably-disjoint pieces of state. State is exactly "a thing
whose observed value depends on *when* you look," so confining it to one interpreter is
what makes the inferred half's equivalence promise hold by construction.

## 2. The trampoline — the single serializing interpreter

`IO a` is morally `World → (a, World)`; `bind!` threads `World` sequentially. **The
trampoline (the scheduler-trampoline) is that single interpreter** — it folds effects
into one coherent world-state in a defined order. It is the middle layer between the
pure world (values, continuations) and the platform world (effect implementations),
and it is the *only* place that orchestrates the two. Both halves of §1 are properties
of how this one interpreter runs the effect tree:

- the inferred half = the trampoline dispatching independent effects concurrently and
  joining their results back into the fold;
- the control half = the trampoline interpreting in-language combinator nodes
  (`race`/`select`/…) that branch on *when* sub-computations complete.

This is the algebraic-effects / effect-handler shape: direct-style code; concurrency
as a property of how the interpreter runs the effects, not as primitives sprinkled
through user source.

## 3. The objective and its standard

**The objective, in one sentence:** *the programmer writes ordinary direct-style pure
code with zero concurrency primitives; the trampoline extracts the maximum SAFE
concurrency from dataflow + resource metadata, with the result provably identical to
sequential execution.*

Two distinct axes the trampoline fills:

- **Parallelism** — fill CPU cores with independent pure compute (the rayon spark
  path; lenient-eval over pure values).
- **Concurrency** — keep many blocking effects in flight, each consuming **no core
  while it waits** (the reactor; thousands of pending I/O futures).

**"Maximum concurrency" is a direction, not a spec.** The standard is **per-workload
acceptance benchmarks**, with a universal floor beneath all of them: **never slower
than sequential** (overhead-bounded — the inferred machinery must not cost more than it
saves on workloads with no exploitable parallelism).

- **Web is the reference / lead workload.** The model is a natural fit (independent
  requests, per-connection tokens, I/O-bound). The §10 server example is the worked
  case, and the web acceptance benchmark is the one the architecture is tuned against
  first.
- **Data processing** sets a different bar: granularity (work per stage vs scheduling
  overhead), inter-stage **backpressure**, and an in-place-reuse dependency on the
  Phase-H memory model (RC-fusion / Perceus reuse) for competitive throughput.
- **Games** are frame-deadline-bound: an excellent fit for the **intra-frame job
  graph** (independent systems within a frame, extracted automatically), but hostile to
  the stateful, deadline-bound hot loop — possibly out of scope. They are named here to
  set expectations, not as a target the floor must clear.

## 4. The inferred half — how concurrency is extracted

The pure program emits effects ordered **only by data dependencies**. The trampoline
extracts concurrency from three compile-time facts — **unchanged from today's
extraction analysis**; the async substrate (§6) changes *execution*, not *extraction*:

1. **Dataflow independence** — two effects with no shared free variable may run
   concurrently (the auto-IO independence analysis, spec §10.12.1).
2. **Token disjointness** — effects on different resource tokens run concurrently;
   effects sharing a token serialize (the `ResourceSerial` mechanism, spec §10.12.4).
   An accept loop yields a stream of *distinct* connection tokens, so different
   requests are concurrent **by construction**, with no annotation in the handler.
3. **Pool cardinality** — a resource exposes N tokens; the (N+1)th effect parks until
   one frees. **A connection-pool bound is simply the token count** — there is no pool
   code in the platform.

Two consequences make the classic server fall out with **no `spawn`**:

- **Launch-and-continue is inferable.** In `(do (handle-conn conn) (serve listener))`,
  `handle-conn` returns `IO Unit` — its *result is unused* and its tokens are disjoint
  from the continuation. An effect whose result is discarded and whose tokens do not
  conflict with what follows may be launched and **not joined**. The accept loop fans
  out automatically; the recursion is TCO'd (spec §12.5).
- **Backpressure is a scheduler policy, not a language feature.** "Saturate but do not
  oversaturate under load" depends on dynamic resource availability — exactly the state
  the pure world correctly refuses to hold. The trampoline *is* the scheduler and holds
  that state: it does not dispatch the next `accept` until a worker / token / budget
  slot is free, parameterized by the platform-declared concurrency descriptors (§5).
  The pure loop emits `accept` eagerly and unboundedly; the scheduler throttles
  execution.

**Core saturation with responses *and* DB calls.** Blocking effects (the DB call) run
on the reactor — many in flight, consuming no core while waiting — while pure rendering
fills the CPU cores via rayon sparks. The blocking-vs-CPU split is itself inferable
(effects are potentially-blocking; pure values are CPU). Balancing the two pools to
fill the cores is the scheduler's job (§7), given the metadata — and none of it touches
the pure source.

## 5. The concurrency descriptor

The platform declares, per effect, a **concurrency descriptor** — a finite, declarative
generalization of today's scheduling classes (`Sequential` / `Commutative` /
`ResourceSerial`):

| Field | Meaning | Async substrate mapping |
|---|---|---|
| **token** | what the effect conflicts on (0 = unrestricted) | which `Semaphore` |
| **cardinality** | how many tokens exist = safe parallelism / pool size (new) | number of permits |
| **global budget** | optional cap on total in-flight effects of this kind = the backpressure threshold (new) | bounded channel / `Semaphore` |
| **blocking?** | does it block, or yield on `WouldBlock`? — selects the worker pool (inferable) | CPU pool (rayon) vs reactor routing |

This is the platform's entire concurrency contract: declarative, finite, evolutionary
from the auto-IO machinery — not a new subsystem. It is also a **trust boundary**,
continuous with the existing one: the compiler does not verify that a `Commutative`
effect truly has no shared state, exactly as it does not verify a `ResourceSerial`
token is correct. The platform author asserts safety; the language takes it on faith
(the platform's `unsafe`).

## 6. Execution substrate — async/await over a host-owned async runtime

The load-bearing enabler is a property the language already has: **IO is reified as
data.** An `IO a` is a continuation tree — a value, not a suspended native frame.
Cranelisp code is therefore ALWAYS synchronous pure compute *between* effects: the
native stack **unwinds to the trampoline at every effect**, the continuation is a heap
value, and `call_continuation` resumes it. There is never a cranelisp native stack
frame suspended across an I/O wait.

This is what lets the substrate be plain async/await with **no hand-rolled fibers, no
stackful coroutines, no JIT stack-switching**:

> Because the continuation is a value, the trampoline can simply BE an `async fn` that
> interprets the IO tree. All awaiting lives in Rust.

The combinators and the inferred dispatch map directly onto host-runtime primitives:

| Concept | Host-runtime primitive |
|---|---|
| `timeout d io` | runtime timeout |
| `race` / `select` | `select!` |
| `Par` (inferred fork-join) | `join!` |
| cancellation | drop the future |
| launch-and-continue | spawn the handler future, don't await; `JoinSet` for supervision |
| token-cardinality pool | `Semaphore(N)` per token |
| backpressure | bounded channel / `Semaphore` |
| blocking/CPU split | reactor (I/O effects) + rayon (CPU sparks) |
| supervisor | `JoinSet` + catch the spawned handler's outcome |

So the work is not "build a fiber runtime"; it is **use the async runtime, provide the
inference (§4), and map the descriptors (§5) onto runtime primitives.**

**Runtime naming and feature-gating.** The host runtime is tokio-or-equivalent, and it
is **feature-gated**: pure / non-concurrent `--link` binaries must not pull in the
reactor. This respects the "empty prelude works" principle (nothing in the runtime is
required for the language to work) and Phase-H binary size — a program that performs no
concurrent effects links no executor.

## 7. The two-pool model — rayon for CPU, async runtime for I/O

The two pools are the correct realization of §5's blocking/CPU split, **not accidental
complexity. They are not unifiable:**

- **rayon** = work-stealing fork-join for CPU-bound, run-to-completion sparks
  (lenient-eval; the Pillar-B apply-arg sparking).
- **the async runtime** = executor + reactor for many concurrent, mostly-waiting I/O
  futures.

Why they cannot merge:

- Putting CPU sparks on the async executor **starves the reactor** — a non-yielding CPU
  future occupies a worker thread. `spawn_blocking` is a park-on-syscall pool, wrong
  for fine-grained fork-join.
- rayon-alone has **no reactor** — nowhere for thousands of pending I/O waits to live
  without burning threads.
- thread-per-core runtimes (glommio/monoio) *do* unify, but impose a **sharded** model
  at odds with "infer + work-steal freely."

**Contention is low in the typical case.** The two pools compete for cores only under
*simultaneous* CPU+IO saturation. In the typical I/O-bound server the reactor threads
mostly park in epoll (consuming no core) while rayon computes, so real contention is
rare; balancing the two is a scheduler **policy** (§4's inherent two-pool problem), not
a structural flaw. Keep cross-pool handoffs **coarse** (at the effect→render boundary);
fine-grained CPU recursion stays inside rayon.

**De-risking — the CPU-spark path is independent of the I/O-runtime work.** Today rayon
does BOTH pure sparks and I/O `Par` (the limitation: blocking I/O ties up CPU threads).
The async split **moves I/O onto the reactor and leaves the pure-spark path on rayon
UNCHANGED.** So CPU-spark widening (pure-value sparks, apply-arg sparking — FIXME 0424)
is a rayon-side increment that can land independently of the I/O-runtime work.

## 8. The resource-token model under async — preserved and generalized

The extraction facts of §4 stand verbatim. Under the async substrate they map cleanly,
and **no concurrency is lost** — the available parallelism widens:

| Compile-time fact | Async execution |
|---|---|
| token-disjoint effects (independent) | separate concurrent futures — scales from ~hundreds of rayon threads to **thousands of pending futures** |
| same-token, cardinality 1 (`ResourceSerial`) | `Semaphore(1)` / a sequential `await` chain |
| same-token, cardinality N (new) | `Semaphore(N)` — the bounded pool you could not express before |
| global budget | bounded channel / `Semaphore` |
| blocking? | CPU-vs-reactor pool routing (the one **new** decision the descriptor drives) |

The bespoke "group-by-token, groups-parallel, within-group-serial" dispatcher
(`dispatch_par_branches_with_trace`) **dissolves into** "every effect acquires its
token's permit." That is a net mechanism simplification.

**One invariant to carry deliberately: within-token source ordering.** A bare semaphore
gives *exclusion* but not *order*, and order is observable for same-resource effects
(e.g. log appends to one file must land in source order). So a same-token group is
modelled as a **sequential async block**, mirroring today's `SerialGroup` — exclusion
*and* order. This must be carried into the async lowering on purpose; it does not fall
out of permits alone.

The worked example: concurrent HTTP GETs draw **distinct** connection tokens → run
concurrently; serial file block reads share **one** file token → serialize in source
order. Both behaviors are preserved exactly; only the mechanism underneath simplifies.

## 9. The control half — the combinators

The control layer is a small set of **ordinary typed functions that construct
trampoline-interpreted IO-ADT nodes** — the same mechanism class as the existing `Par`
node. They are emphatically:

- **NOT special forms.** An `IO a` is already a lazy description, so no special
  evaluation rule is needed. `bind!`/`do` remain macros that desugar to the `Bind`
  constructor; the combinators sit at the same layer as the IO constructors.
- **NOT platform effects.** They are not GOT-dispatched to a DLL. The entire control
  vocabulary lives in the runtime; **platforms never see it** — this is what keeps the
  thin-platform thesis intact even for the explicit surface.

**Minimize the irreducible primitive set.** The trampoline needs to interpret only
**`race`/`select` + structured cancellation**. Everything else is derived:

- `timeout d io = race io (sleep d)` — derivable in stdlib.
- `cancel` is **not** a standalone user combinator — it is the *consequence* of losing a
  race or exiting a scope (drop the future).

Indicative signatures:

```
race    : IO a -> IO a -> IO a
timeout : Duration -> IO a -> IO (Option a)
select  : List (IO a) -> IO a
```

These map directly onto the host runtime (§6): `race`/`select` → `select!`, `timeout` →
runtime timeout, cancellation → drop.

This layer is **separable but committed.** Separable is an architectural property, not a
delivery one: the combinator layer is purely additive — the inferred half does not
depend on it, and it can land without disturbing the inferred half (it depends only on
launch-and-continue being present). That separability is a correctness claim and stands.
But separable ≠ optional: the combinator layer is **in scope for this track and a
committed deliverable.** The timing-control behaviors it provides — per-request timeout,
cancel-on-disconnect, graceful shutdown — are not luxuries deferred until some SLO
workload demands them; they are what makes a server survive an *uncooperative,
open-internet environment* at all. This layer is exactly how the §1 control vocabulary
("the vocabulary for an uncooperative environment at the I/O boundary") is spoken. The
explicit control half is a **committed peer** of the inferred half — that is the whole
"throughput is free; control is explicit" thesis (§1).

## 10. Supervisor semantics — co-requisite of launch-and-continue

Launch-and-continue creates an un-joined effect: a fire-and-forget handler that panics
has **no join point** for its error to ferry to. Supervisor semantics is the policy for
where that error goes — and it must land **with** launch-and-continue, not after it.

**The ferry substrate already exists** (Appendix B): the fork-join error-slot ferry is
implemented (`ivar.rs` / `io.rs`: worker-side `take_runtime_error()` → IVar error-field
stash → join-side `set_runtime_error()` re-raise). That is the *substrate* — how a
captured error is carried.

**Supervisor semantics is the *policy*** — where a captured error GOES when a
fire-and-forget effect has no join point. The per-effect-kind default: **500 + log +
drop-that-request** — NOT a silent strand, NOT a whole-server abort. It maps to
`JoinSet` + catching the spawned handler's outcome. It is a scheduler-/platform-declared
default, so it stays out of the pure language.

**One honest caveat.** The `Par` path's "first error" among simultaneously-panicking
branches is **non-deterministic** (HashMap grouping order), not strict source-order; the
IVar path *is* source-ordered. This asymmetry is named, not papered over.

## 11. Observability — instrumenting concurrency written by nobody

Observability is a **ratified, first-class commitment of this track**, not an optional
add-on. For *this* model it is load-bearing in a way it is not for an explicit-concurrency
system, for three independent reasons:

1. **The concurrency is invisible in the source.** The thesis is *concurrency written by
   nobody* (§1) — there is no `spawn`, no explicit task graph, nothing in the user's code
   to inspect. The parallelism, suspensions, token-parks, and cancellations never appear
   in the source. **You cannot debug what you did not write** unless the runtime surfaces
   it — an implicit-concurrency system without instrumentation is strictly *harder* to
   debug than an explicit one. The trampoline (§2) is the single point all
   effects/sparks/suspends/resumes/token-acquires/cancels flow through — the only place
   this is observable — so it must emit a structured event stream **by design**.
   Retrofitting cannot recover events that were never recorded.
2. **Supervisor drops vanish without it.** Launch-and-continue + the supervisor policy
   (§10: 500 + log + drop-the-request) *intentionally* swallows a failed strand so one
   bad request does not kill the server. Without an observability sink those failures
   leave **no trace at all.** Supervisor semantics and the observability sink are
   coupled — designing one without the other makes errors disappear by construction.
3. **You cannot measure against the performance standard without it.** Core saturation,
   pool starvation, and backpressure stalls (§3, §7) are runtime-scheduler phenomena
   invisible in source; measuring them against the §3 per-workload acceptance benchmarks
   *is* observability.

**What it is — build on what exists, do not invent from scratch.** A **structured,
strand-correlated event stream emitted from the trampoline**, extending the existing
observability machinery rather than starting fresh:

- `trace` (spec §4.12) — the execution-trace keyword-node;
- `io_trace` / `IoObserver` — the IO ring-buffer + callback registration API, hosted in
  `cranelisp-intrinsics`;
- the S90 **log↔trace `turn` correlation** — the two-sink log/trace pair joined by a
  correlation id.

The single **indispensable primitive is strand identity**: a correlation id (the `turn`
id is the precedent) threaded through every suspension, spawn, and cancellation, so a
debugging user can reconstruct *"this request fanned out into these effects; this one was
cancelled by a race; that one panicked and the supervisor dropped it."* Strand-id
plumbing threads through the continuation/spawn machinery and is **expensive to
retrofit** — so it is **groundwork**: it lands *with* the async substrate, not after.

**Events the stream carries** (accrue per capability as the track lands them):

- effect **dispatched** (effect, token, blocking?/CPU, pool);
- effect **suspended** (parked on fd/reactor) and **resumed** (woken);
- spark **created** / **forced**;
- token **acquired** / **released** (pool contention);
- backpressure **admission park**;
- launch-and-continue **strand spawned** (with strand id);
- supervisor **action** (strand panicked → 500 + log + drop);
- **cancellation** (race loser / timeout fired → what was cancelled).

**Scope guard — do not gold-plate.** Build the *plumbing* (trampoline event hooks +
strand id) early, because that is the expensive-to-retrofit part. Keep the *sinks*
minimal and dev-facing (REPL-visible, like `trace`). Reuse the agentic-repl track's
**feature-gated / byte-identical-when-off** discipline so observability costs **nothing**
in `--link` / `--release`. No OpenTelemetry, no exporters in-track. Richer tooling (a
dev-facing strand inspector) is a later, optional consolidation, not in scope here.

## 12. Platform ABI — binary decoupling preserved via C-ABI-async (the A2 model)

The DLL/rlib boundary is preserved, upgraded from a blocking C-ABI to a **poll-based
async C-ABI (ABI v4)**. This is the second headline of the architecture. Frame it
correctly:

**Why the binary boundary exists.** The DLL/rlib exists for **deployment decoupling** —
a cranelisp user consumes a prebuilt third-party platform binary **without a Rust
toolchain and without rebuilding it.** It is **not** for language independence
(platforms are intended to be Rust). A cranelisp user needs no Rust.

**The deployment model is unchanged.** A platform ships as a directory on the platform
search path containing the binary (cdylib for REPL/`--run`, rlib for `--link`) +
bundled `.cl` modules (types, effect signatures, docstrings) + the existing exports.
The loader still: find dir → dlopen/link → read manifest → build SymbolTable → load
`.cl` types. Bundling cranelisp modules with the platform is preserved. (The
three-exports / GOT / manifest / schema+layout-hash model of `platform-interface.md`
carries forward; §13.)

**The boundary stays C-ABI.** C-ABI is the only contract stable across separate
compilation — Rust has no stable ABI. Async does **not** force a Rust-ABI boundary,
because async at the bottom IS a C-ABI-able poll protocol (cf. the `async-ffi`
pattern). We upgrade the *shape* of the C-ABI from a blocking `extern "C" fn` to a
**poll-based async** one.

**A2 model (chosen): host owns the reactor; platforms are C-ABI async *leaves*.**

- The platform does the non-blocking syscall — it owns the *what* (its domain, its
  protocol).
- On `WouldBlock` it registers interest via a **host-provided C-ABI callback**: a
  `HostCtx` vtable carrying `register_readable` / `register_writable` / `register_timer`
  + a **C-ABI waker** (the C-ABI projection of `std::task::Context`). The host's single
  reactor (epoll / io_uring / kqueue) owns the *when* and re-polls.
- The platform carries **NO runtime, NO tokio** — just libc + the host callbacks.
- **Cancellation** = the host stops polling + calls a `drop_state` export. This resolves
  the "cancel a blocking effect" problem cleanly: **we never truly block**, so nothing
  is ever stuck inside a syscall.

The platform author writes "try the syscall; if it'd block, tell the host to wake me" —
**thinner than today's blocking platform, and never learns an async concept.**
Platforms own the *what*; the host owns the *when*.

**This is an evolution of the existing ABI, not a new mechanism.** Call it **ABI v4**:

- the poll-fn lives in the **GOT** (same indirect dispatch as today);
- the manifest additionally declares each effect's concurrency descriptor (§5) and its
  poll-shape;
- sync / non-blocking effects just return `Ready` immediately — **blocking-style and
  poll-style coexist**;
- schema + layout-hash unchanged;
- the **versioned C-ABI contract IS the decoupling**: any v4 host loads any v4 platform.

**The one genuinely new designed artifact: the host-reactor C-ABI** — the `HostCtx`
vtable + the C-ABI waker. It is small, stable, and Unix-reactor-shaped. **This is the
load-bearing design surface this whole direction introduces** — everything else is
mapping existing facts onto an async substrate; this is the part that must be designed
from scratch.

**Optional fallback tier (B):** a blocking C-ABI + host `spawn_blocking`. It preserves
decoupling but gives **no real cancellation** and is thread-per-call. Acceptable only
for low-concurrency platforms; not the primary path.

## 13. Cascade-pending — `platform-interface.md` ABI-v4 rewrite

The current `platform-interface.md` documents the **ABI v3** three-exports model
(blocking `extern "C"` effect fns, GOT + manifest + schema+layout-hash). §12 here
supersedes the *effect-call shape* without disturbing the three-exports deployment
model. When this track moves to implementation, `platform-interface.md` needs an
**ABI-v4 cascade**:

- poll-shape effect fns dispatched through the GOT (the GOT mechanism is unchanged; the
  signature shape changes);
- the per-effect **concurrency descriptor** (§5) added to the manifest;
- the **host-reactor C-ABI** (`HostCtx` vtable + C-ABI waker) as a new exported/imported
  contract;
- `ABI_VERSION` 3 → 4.

This is **flagged, not executed** — the rewrite belongs to the implementation track
(after agentic-repl, before Phase H), not to this pre-implementation statement. No FIXME
is filed: per the project's manifestation-site discipline, the cascade is recorded here
at its natural home and actioned when the track opens (the trigger — implementation — is
unmet, so an open FIXME would merely idle across sprints).

## 14. Build sequencing (the implied roadmap, lightly)

The dependency order the architecture implies:

1. **descriptor (design)** — §5, the declarative contract.
2. **token-cardinality pool** — `Semaphore` per token (§8).
3. **backpressure** — bounded channel / global budget (§5).
4. **launch-and-continue + supervisor** — **co-landed**, gated on backpressure so
   fan-out is bounded (§4, §10).
5. **blocking/CPU two-pool routing** — the `blocking?` descriptor drives reactor-vs-rayon
   (§7).
6. **the cancellation/choice combinator layer** — §9. A **committed slice**, separable
   and additive (it depends only on launch-and-continue being present, not on the slices
   between), but delivered, not a deferred tail. Its position in the dependency order is
   late only because it has the fewest predecessors, not because it is optional (§9).

**Observability is groundwork, not a sequencing step.** The observability *framework*
(§11 — trampoline event hooks + strand id) is delivered **with the async-substrate slice**
(slice #2 in the `sprints/ROADMAP.md` delivery sequence), because the strand-id plumbing
is expensive to retrofit and must thread through the continuation/spawn machinery from the
start. Each subsequent slice above then **emits its new event types** into the existing
stream (token acquire/release with the pool slice, supervisor action with slice #4,
cancellation with the combinator slice). It is not its own dependency-order entry — it is
the substrate the entries instrument.

This states the **dependency order** the architecture implies, not the sprint-by-sprint
delivery sequence — the latter lives in `sprints/ROADMAP.md`.

Independent of all of the above: **pure-value spark widening** (apply-arg sparking,
FIXME 0424) is a rayon-side increment (§7 de-risking) and can land anytime.

## 15. Manifestation sites when implemented

This is a target; nothing in the canonical set changes yet. When built, the substance
manifests at:

- **`bounded-contexts.md` §3 (backend)** — the trampoline-as-async-scheduler;
  launch-and-continue codegen; two-pool routing; **the async trampoline emits the
  strand-correlated observability event stream and threads the strand id** (§11).
- **`bounded-contexts.md` §4b (intrinsics)** — the `IoObserver` / `trace` surface
  **extended to the new observability event kinds** (§11); strand id carried alongside
  the existing `turn` correlation id.
- **`bounded-contexts.md` §5 (platform)** — the concurrency descriptor (§5); the A2
  C-ABI-async-leaf model + the host-reactor callback contract (§12); "platforms own the
  *what*, the host owns the *when*."
- **`bounded-contexts.md` §6 (int)** — the scheduler policy: backpressure, supervisor
  semantics, pool sizing; the host reactor + the runtime feature-gating; **the dev-facing
  observability sink + its feature-gating** (§11).
- **spec cascade** (file `target: /spec` when actioned) — §10.12 (descriptor
  generalization; launch-and-continue semantics) and §12 (supervisor model; the eventual
  combinator layer); **plus a §4.12 / §12 note IF the strand-id / observable-event surface
  becomes user-visible** (the trace/event surface is `/spec`-owned — flag as cascade,
  `target: /spec`, do not author).
- **`platform-interface.md`** — the ABI-v4 cascade of §13.
- **A candidate new principle** — *"confine mutable-state concurrency to the
  interpreter; platforms are thin stateless effect vocabularies"* — file per
  `design/arch/principles/CLAUDE.md` if/when ratified as binding.

A **concurrency-scheduler sequence diagram** under `design/arch/sequences/` is warranted
when this moves from target to design — flagged sequence-diagram-pending; not drawn
while pre-implementation. The same diagram is the natural **annotation site for the
observability event stream** (§11) — where each suspend/resume/spawn/cancel arrow emits
its event.

## 16. Code sketch — the pure side of a web/DB API

Indicative cranelisp; the point is the **dataflow shape and where concurrency emerges**,
not exact record sugar. The programmer writes **zero concurrency primitives**. Every
comment marked `⟂` notes a place the trampoline extracts concurrency on its own.

```clojure
;; ── Thin platforms (declared, not shown) ───────────────────────────────────
;; web : listen, accept, read-request, respond
;;   accept  — ResourceSerial on the listener token; yields a FRESH conn token
;;   respond — ResourceSerial on the *connection* token
;; sql : query, execute
;;   both    — ResourceSerial on a connection-pool token of cardinality N
;;             (pool size IS the token count; the platform has no pool code)
;; Neither platform knows anything about concurrency. The descriptors above
;; (§5) are all the metadata the scheduler needs.

(deftype Method [GET POST PUT DELETE])
(deftype Req  [Req Method String String])   ; (Req method path body)
(deftype Resp [Resp Int String])            ; (Resp status body)

;; ── Per-request handler: data in, effects-described out ─────────────────────
(defn handle [req]
  (match req
    (Req GET  path _)    (handle-get path)
    (Req POST _    body) (handle-post body)
    _                    (pure (Resp 405 "method not allowed"))))

(defn handle-get [path]
  (let [id (path-param path "id")]
    ;; ⟂ `user` and `orders` are data-independent and draw two DIFFERENT pool
    ;;   tokens (cardinality N ≥ 2) → the two queries run concurrently.
    ;;   No annotation; the scheduler reads it off the dataflow + tokens.
    (bind! [user   (query "SELECT * FROM users  WHERE id = ?" id)
            orders (query "SELECT * FROM orders WHERE user-id = ?" id)]
      ;; ⟂ pure CPU render → eligible for lenient sparks, fills cores.
      (pure (render-user-page user orders)))))

(defn handle-post [body]
  (match (parse-user body)                     ; pure validation → Result
    (Err msg) (pure (Resp 400 msg))
    (Ok  u)   (bind! [_ (execute "INSERT INTO users (name) VALUES (?)"
                                 (user-name u))]
                (pure (Resp 201 "created")))))

;; ── Accept loop: TCO self-recursion; the trampoline fans out ────────────────
(defn handle-conn [conn]
  (bind! [req  (read-request conn)
          resp (handle req)]
    (respond conn resp)))                       ; ResourceSerial on conn token

(defn serve [listener]
  (bind! [conn (accept listener)]               ; one accept at a time (serial)
    ;; ⟂ (handle-conn conn) returns IO Unit, result unused, tokens disjoint from
    ;;   the next accept → LAUNCH-AND-CONTINUE. The loop keeps accepting; the
    ;;   scheduler throttles in-flight handlers by free-token / free-worker /
    ;;   budget availability (backpressure). No `spawn`.
    (do (handle-conn conn)
        (serve listener))))                     ; tail call → next accept

(defn main []
  (bind! [listener (listen 8080)]
    (serve listener)))
```

What the programmer expressed: a straight-line request/response and an accept loop. What
the runtime does for free, from dataflow + the platforms' concurrency descriptors: runs
the two queries concurrently, sparks the pure render across cores, overlaps many requests
as concurrent futures, bounds the DB pool at N, and applies backpressure on accept under
load. The robustness path (a per-request timeout, cancel-on-disconnect) is the *only*
thing that requires the explicit `timeout`/`race` combinator layer (§9) — and even that
is an in-language IO node the trampoline interprets, never a platform capability.

---

## Appendix A — Supersession note (terse)

This target **supersedes the hand-rolled-fiber framing** of the earlier
effect-concurrency write-up. That framing cast the trampoline as a bespoke fiber/task
runtime suspending stackful pure continuations, and treated the explicit control layer
as a small deferred remainder of an otherwise-inferred whole. Two corrections:

1. **Substrate.** Because IO is reified as data, no stackful machinery is needed — the
   trampoline is an `async fn` over a host-owned async runtime and all awaiting lives in
   Rust (§6). "Build a fiber runtime" becomes "use the async runtime + map descriptors
   onto its primitives."
2. **Framing.** Throughput (inferred) and control (explicit) are **complementary peers**
   (§1), not primary-plus-footnote. The control layer is irreducible and grows in
   importance with workload statefulness.

The thin-platforms thesis, the dataflow-extraction facts (§4), the resource-token model
(§8), the concurrency descriptor (§5), and the rejection of the Roc/"Model B"
platform-owned-loop degeneration all carry forward unchanged.

## Appendix B — Implementation status (as-built ↔ target)

**Exists today** (the building blocks):

- auto-IO independence analysis + `Par` nodes (spec §10.12);
- resource tokens (spec §10.12.4);
- IVars / completion cells (`crates/cranelisp-runtime/src/ivar.rs`);
- a rayon worker pool + `Par` dispatch (`crates/cranelisp-intrinsics/src/io.rs`,
  `dispatch_par_branches_with_trace`, with `SerialGroup` within-token ordering);
- `bind!`-compiled continuations (`call_continuation`, `io.rs`);
- lenient sparks over pure values (`ivar_spark` → `rayon::spawn`, `ivar.rs`; spec
  §12.4.3);
- **the fork-join error-slot ferry — IMPLEMENTED.** Worker-side
  `take_runtime_error()` → IVar error-field stash → join-side `set_runtime_error()`
  re-raise, on **both** the IVar path (`ivar.rs`) and the `Par` path (`io.rs`). This is
  the *substrate* §10 builds the supervisor *policy* on — not a pending defect.

**Needed for the target** (not built — re-cast from "build it" to "use the async runtime
+ provide the inference + map descriptors onto runtime primitives," per §6):

- a **feature-gated host async runtime** (tokio-or-equivalent) the trampoline runs as an
  `async fn`;
- the **concurrency descriptor** (§5) as a manifest-declared per-effect contract;
- the **token-cardinality pool** (`Semaphore(N)`) and **backpressure** (bounded channel
  / budget) — today cardinality is implicitly 1 per token value;
- unstructured **launch-and-continue** (today's `Par` is strictly lexical fork-join) +
  **supervisor policy** (§10), co-landed;
- the **blocking/CPU two-pool routing** driven by the `blocking?` descriptor (§7);
- the **host-reactor C-ABI** + **ABI v4** poll-shape platform boundary (§12) — the one
  genuinely new designed artifact;
- the **cancellation/choice combinator layer** (§9) — committed; separable/additive but
  delivered, not deferred;
- the **observability event stream** (§11) — strand-correlated trampoline instrumentation;
  the plumbing (event hooks + strand id) is expensive-to-retrofit groundwork that lands
  with the async substrate.

Independent of the above: **pure-value spark widening** (apply-arg sparking, FIXME 0424)
is a rayon-side increment that needs none of the I/O-runtime work (§7 de-risking).
</content>
</invoke>
