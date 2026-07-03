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
a different subject, inventoried in `design/int/concurrency-architecture.md`. (Its
highest-leverage item — the dependency-service single-writer race + the D0030
mutual-import deadlock — was resolved structurally by the S93 signature/body
pre-pass and the resolving FIXMEs 0425 item 1 + 0426 deleted; the residual
lower-value structure debt of 0425 items 2–4 — `SharedState` per-field ownership,
`cached_modules` dual-store, priority/nice worker unification — remains as
inventory in that doc, untracked by a FIXME.) Do not conflate them.

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
acceptance benchmarks**, with a floor beneath all of them: **never *dramatically* slower
than sequential, modulo the shared memory substrate.** Two costs the floor bounds: the
inferred machinery must not cost more than it saves on workloads with no exploitable
parallelism, AND sparking must not drive shared-substrate contention (the global
allocator lock + atomic RC, Decision 13) past the point where the contention cost exceeds
the parallel-compute gain. The floor holds **unconditionally for compute-bound sparks**
(allocation-light, RC-light branches); it is **contention-bounded — not yet guaranteed —
for allocation-/RC-heavy sparks** until **Phase H** (the S99 ablation confirmed no
pre-Phase-H substrate cure restores it — §3.1). The earlier unqualified "never slower than
sequential" wording over-stated the guarantee; see §3.1 for the scope correction and the
measured settlement.

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

### 3.1 Floor scope — contention is the boundary, not compute (S94 /port finding)

**The finding.** /port measured the floor *violated* for allocation-/RC-heavy parallel
workloads (Sprint 94, Phase 6). The ladder, parallel-vs-serial wall-clock:

| Workload | Parallel | Serial | Floor |
|---|---|---|---|
| pure compute (examples/30) | 1.3s | 0.9s | holds |
| int-Vec copy divide-and-conquer | 3.1s | 2.85s | holds, thin |
| ADT-Vec copy D&C | 6.9s | 5.0s | violated |
| Sudoku (copy-per-guess 81-elem Vec of RC'd `Cell` ADTs) | ~20s | ~1.9s | **~10× violated** |

The penalty scales with **heap allocation + atomic-RC traffic**, not compute. The parallel
branches *are* genuinely data-independent (the inference is correct), but each spawned
branch hammers two shared, *serializing* resources — the **global allocator lock** and
**atomic-RC cache lines bouncing across workers** (Decision 13). The Sudoku case is worst
because copy-per-guess allocates a fresh 81-element Vec of RC-managed `Cell` ADTs per
branch: allocation-dominated, RC-dominated, compute-trivial. **Independent dataflow does
not imply independent memory traffic** — and the inference sees only the former.

**The verdict (BOTH — scope the claim AND specify the gate).** The "never slower than
sequential" floor was over-stated as a universal guarantee, and the spark-budget
create-gate meant to secure it (`design/backend/lenient-eval.md` §3.6.3) is incomplete:

- **Scope correction (honesty, now).** The floor is scoped in §3 above: unconditional for
  compute-bound sparks, contention-bounded for allocation-/RC-heavy sparks. The create-gate
  bounds spark **count** — so the *spark-machinery* overhead (IVar/thunk allocation) is
  `O(cap)`, the `fib` explosion it was built for. It does **not** bound the **per-branch
  user-level** allocation + atomic-RC traffic each of the (bounded) `cap` live branches
  generates concurrently. Count is the wrong signal for contention.

- **Gap correction (the path back, in-track, without Phase H).** The create-gate is the
  right *locus* but needs a **contention-aware signal**. The floor is restorable
  *conservatively*: an allocation-/RC-dominated branch should simply **not spark** — it
  takes the sequential arm, which is exactly "never slower than serial" for that branch.
  This is a refinement of the existing sparkability cost heuristic + create-gate, not a new
  subsystem.

**Where the gate lives + what it gates on.** Backend (`design/backend/lenient-eval.md` —
the sparkability cost heuristic §2.2 + the create-gate §3.6.2), with this section as its
arch-thesis scope authority. Two layers, cheap-first:

1. **Static (first).** Extend the cost heuristic from a *compute-cost* axis to also carry
   an **allocation/RC-density** axis: a branch dominated by constructors / Vec copies / RC
   traffic on captured shared structure is declined for sparking even when its compute cost
   clears the "expensive Apply" bar. "Expensive *and* allocation-light" sparks; "expensive
   *but* allocation-dominated" stays sequential.
2. **Dynamic (later, only if static is insufficient).** Gate the runtime create-gate on a
   shared-substrate contention signal (allocator / atomic-RC hotness) *in addition to*
   in-flight spark count — back off when the substrate is hot. Same family as the
   unified-budget / backpressure work (`lenient-eval.md` §3.6.4, FIXME 0442); it belongs
   *with* that, not ahead of it.

**Relationship to atomic RC (Decision 13) and Phase H — this REINFORCES the sequencing.**
Atomic RC exists *because* of parallelism (it is the cost of values crossing spark
threads); the /port finding is the empirical confirmation that atomic-RC contention is
*the* parallel bottleneck for stateful workloads. Phase H's memory work —
non-atomic-RC-where-thread-local, escape→stack/region, Perceus reuse + RC-fusion — attacks
this contention **at its source**: thread-local values drop the atomic, non-escaping values
leave the allocator entirely, and in-place reuse removes the copy-per-guess alloc/free
churn (the Sudoku pattern is exactly the in-place-reuse case §3's data-processing bar
already flags as Phase-H-dependent). But Phase H stays **after** the concurrency track, and
this finding **reinforces that edge rather than pulling memory work forward**:

- Non-atomic-where-thread-local is *defined by* which values cross threads — exactly what
  the concurrency model determines and has not yet settled (§Sequencing, top of doc).
  Pulling the RC opt forward would implement it against a moving target — a Principle-8
  interim-implementation defect. The dependency is real, not a priority preference.
- So the three layers compose cleanly: **(a)** scope the claim now (honesty); **(b)** the
  in-track contention-aware gate restores the floor *conservatively* by declining to spark
  contention-heavy branches (serial fallback = floor met); **(c)** Phase H later *widens*
  the profitably-parallel set by removing the contention at its source, so the gate's
  conservative declines become admits. The interim gate is shaped-to-be-subsumed
  (Principle 8): the same cost-heuristic + create-gate it refines is what Phase H's
  escape/thread-locality analysis later feeds a sharper signal into.

**Sequencing — who owns the fix.** The conservative **static contention heuristic** is a
**rayon-side CPU-spark increment** (§7 de-risking: the CPU-spark path is independent of the
I/O-runtime work), so it can land in the concurrency track without waiting on the reactor
slices — placed as a **create-gate refinement in the backpressure-family slice** (slice
3/4, alongside the §3.6.4 / FIXME-0442 budget work it shares a locus with), or pulled
earlier as a standalone perf increment if a user-facing workload (the Sudoku exemplar,
FIXME 0408) forces it. The **dynamic** substrate-contention signal rides with the
unified-budget / backpressure slice (FIXME 0442). The **structural cure** is **Phase H**
(after the track), unchanged in sequence. The backend-side correction to
`design/backend/lenient-eval.md` §2.6.2 / §3.6.3 (the floor claim those sections state is
scoped to *spark-machinery* overhead, not per-branch user contention) is filed as FIXME
`target: /backend` (0459).

**S99 settlement — the four-spike ablation resolved the pre-Phase-H hypothesis: the floor
is NOT restorable in-track for alloc/RC-heavy parallel workloads.** The Sprint-99 close-out
ran a falsification-first ablation (fixtures F1 machinery / F2 clean contention / F3 inverted
search / F4 real Sudoku; `tests/plan/s99-measurement.md` §1–§10, on the **release** backend)
to decide whether the two contention terms (a) allocator-lock + (b) atomic-RC cache-line
bouncing could be cured before Phase H. The S94 framing above (contention splits (a)/(b); the
(b) in-track cure is capture-by-borrow across structured fork-join) was a *hypothesis*; the
ablation **measured** it and settled the question against an in-track cure. Four results are
now on record:

- **The R1 prior was inverted — measure contention on release, not debug.** R1 read the /port
  ladder's **debug** sys-dominance as a prior toward **(a) allocator-lock** as the larger term.
  On **release** the sys-dominance did **not survive**: contention is (b)-dominated — F2's
  N-worker contention delta is **99% user / 1% sys**, F4's **~70% user / ~30% sys**
  (`s99-measurement.md` §4 isolation 3). The user/sys *method* was right; the debug *numbers*
  misled the attribution. **Durable lesson: attribute contention on the release tier — a
  debug build's allocator-syscall (sys) overhead masks the atomic-RC (user) cache-line
  bouncing that dominates optimised code.**

- **No pre-Phase-H substrate lever restores the floor.** Three independent in-track cures were
  each built behind a toggle and re-benchmarked; each moves the dominant (b) term only
  single-digit percent on the clean F2 probe (`s99-measurement.md` §8–§10):
  - **capture-by-borrow (`CRANELISP_CAPTURE_BORROW`): ~0%.** The mechanism is correct (with it
    on, parallel `rc_inc` drops to *exactly* the serial count) but wrong-scoped: the incs it
    elides are the fork-join spark captures — **hundreds** (create-gate caps spark count far
    below leaf count; capture-arity ~1), not the millions. The dominant (b) traffic is the
    **in-leaf vec-COW leaf-refcount volume** (~81 atomic bumps per 81-cell grid COW-copy ×
    copies × leaves ≈ 170M), *inside* the computation, which no capture rule touches.
  - **saturation gate (`CRANELISP_SATURATION_GATE`): ~9%.** Caps concurrent sparks
    `4×threads → threads`, confining only *overflow* subtrees to one thread; the top ~`threads`
    branches still COW-copy + bump shared ancestor cells. Real, tight-spread, but marginal.
  - **mimalloc (`--features thread-caching-alloc`): user-neutral-to-worse** on the clean probe.
  After the best combined stack (mimalloc + saturation gate) F2 parallel is still **2.3× slower**
  than serial and F4 **6–15× slower** (`s99-measurement.md` §10.3). The removable term is the
  vec-COW leaf-refcount volume, curable only by **owned-copy mutate-in-place / last-use /
  Perceus reuse / non-atomic thread-local RC — all Phase-H memory-model work** (backend-doc
  contract: `design/backend/ring2-rc.md` §5.5.2.7). This is a §5.5 last-use *extension*, NOT a
  widening of the §5.5.2 spark-capture borrow.

- **(a) and (b) are COUPLED — an allocator cure alone can be net-negative.** Removing the
  allocator kernel-lock (sys↓) lets threads run concurrently and bounce the shared-cell
  atomic-RC cache lines **more** (user↑): on fixed-work F2 mimalloc's user-side alloc-throughput
  win dominates (net user↓), but on the deep/varied-alloc F4 the freed concurrency feeds (b)
  and user **worsens** (`s99-measurement.md` §10.1). The two contention terms are not
  independent, so **the RC/memory work and any allocator work must be co-designed for Phase H,
  not independently optimised** — an (a)-only cure trades allocator-lock sys for extra (b)
  user-bouncing.

- **Phase-H sequencing is now empirically confirmed, not merely conjectured (Principle 8
  vindicated by measurement).** The S94 floor-scope ruling said Phase H is the structural cure
  and the sequencing edge is "reinforced, not pulled forward." S99 upgrades that: the in-track
  path back was **attempted and measured insufficient** — the (b) cure is *confirmed* Phase-H,
  not conjectured. Principle 8 refused to fund an interim contention cure against the unsettled
  Phase-H memory model, and the ablation proved the interim cures cannot clear the bar without
  the structural work. The three cures land as **correct, byte-identical-off, Phase-H-durable
  opt-in substrate** (the borrowed/owned classification and the saturation gate both survive
  Phase H and feed sharper signals into it); none flips default-on for a performance reason.
  The ablation report §8–§10 is the durable record of *why* three in-track cures were tried
  and set aside.

**S100 — the (b)-cure now has a designed home: `design/arch/ownership-inference.md` (the
memory-model spine).** Phase H opened at S100 with the design phase this section's settlement
demanded: **interprocedural ownership inference computed at typecheck, consumed by the backend,
no annotations** — one flow/lifetime analysis answering five queries (borrow, escape,
confinement, uniqueness, duplication strategy), each driving a distinct codegen mechanism on the
**shared** Cranelift lowering. The vec-COW leaf-refcount volume named above is attacked from
three directions there: borrow-through-projection makes the read path rc-free (spine §4.4),
uniqueness-driven in-place reuse serves the write path (spine §4.3, increment II — the §5.5.2.7
last-use extension, generalised), and Copy value-flattening plausibly removes the leaf refcounts
outright (spine §6.3). The (a)/(b) **coupling** finding is honoured as a carried constraint
(storage+RC co-designed, spine §0), and the contention-aware gate (`0459`) is composed-not-blocked:
its missing allocation/RC-density axis becomes derivable from the analysis outputs (spine §8.3),
so the gate's conservative declines convert to admits as the memory model lands — exactly layer
(c) above.

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
3. **Pool capacity** — a resource (one token) sustains at most N concurrent ops; the
   (N+1)th effect parks until one frees. **A connection-pool bound is the token's
   capacity** — `query`/`execute`/`begin` over one pool share *one* token of capacity N
   (sum in-flight ≤ N), and there is no pool code in the platform. Capacity attaches to
   the **resource (token), not the effect** — distinct tokens have independent capacity
   (the per-effect special case); a shared token is a shared pool (the DB case). One
   mechanism (§8).

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

### 4.1 The inferred-launch eligibility predicate (the sound local check)

Launch-and-continue is **inferred** (§10.12.7 step 2 requires the tokens be disjoint
from the continuation; no annotation appears in source), so the eligibility test must
be **sound, conservative, and computable without following into a user fn**. This
subsection pins the exact predicate the local bind-chain analysis applies
(`src/bind_chain_analysis.rs`, the `LaunchContinue` arm). A step OR a discarded
**bind sub-tree** ahead of a continuation is launch-eligible iff ALL of:

- **(E1) Result-discarded.** The launched binder's name is unused in the continuation
  (`!free_vars(continuation).contains(binder)`). Sufficient on its own for the
  "no one awaits the result" half (§10.12.7 step 1): if the value is never referenced,
  the value the program computes is unchanged whether the effect runs detached or
  inline. **Local; sufficient.**

- **(E2) Value-locality (the disjointness *witness*).** Every effect in the launched
  sub-tree acts on a resource token carried by a value bound **within** the sub-tree —
  transitively from the launched step's own binder (the fresh `conn` produced by
  `accept`) — and the sub-tree shares **no free variable** with the continuation. This
  is the load-bearing move: token disjointness is a **runtime** fact (runtime tokens
  are dynamic, platform-supplied at the effect site, §5/§8.1 — the compile-time
  analysis sees only scheduling *classes*, never token *values*), so it cannot be
  proven by comparing token values. It is instead **derived from value provenance**: a
  resource reachable only from a freshly-bound, non-shared value yields a fresh,
  disjoint token by construction (the accept loop's "stream of distinct connection
  tokens", §4 fact 2 — a platform trust-boundary assertion, §5). This also discharges
  the **cross-iteration / sibling** hazard: each loop iteration binds a fresh `conn`, so
  two in-flight detached handlers ride distinct tokens and cannot alias. A
  module-global resource handle (a shared DB pool) is **not** locally-bound-per-launch
  and so fails (E2) — correctly, because successive detached handlers would share its
  token; the pool's legitimate concurrency comes from the capacity-N **inferred** pool
  (§8.1) inside a joined structure, never from detachment.

- **(E3) No shared-singleton-token effect — the token-0 *refusal*.** The sub-tree must
  touch **no `Commutative` (token-0, unrestricted) effect and no `Sequential` (the
  global token-1) effect** — only `ResourceSerial`/capacity-N effects on per-value-minted
  tokens. token-0 and token-1 are **shared singletons**, not per-value-minted, so (E2)'s
  value-provenance argument cannot witness their disjointness: two strands on token 0
  (e.g. a shared-`stdout` `print`) interleave **observably**, and the trampoline's
  per-token semaphore gives **exclusion but not source-order across the detach boundary**
  (§8.2) — so a wrongly-detached shared-token sub-tree *reorders* same-token effects
  relative to sequential. A `Commutative` tag asserts order-independence of the computed
  **value**, not of the observable **side-effect stream**; for an *inferred* (un-annotated)
  detachment we take no such latitude. **The disposition is REFUSE** (decline to detach
  is always sound, §10.12.7). An **opaque user-fn call** anywhere in the sub-tree's effect
  positions is an unknown footprint and is likewise refused — which is exactly why the
  sub-tree must be **inlined down to platform leaves** for the launch to fire, and exactly
  why the check stays **local** (no interprocedural token-provenance walk).

  **Timer-leaf refinement (S96 C-fanout, FIXME 0470).** A **resource-free `sleep`
  timer** is the one non-`ResourceSerial` leaf permitted as a sub-tree effect
  *member*. A timer carries **no resource token** and produces **no observable
  side-effect stream** (unlike a token-0 shared-`stdout` `print`), so detaching it
  *as a member of a larger launched sub-tree* reorders nothing observable — the E3
  hazard (reordering a shared-token stream across the detach boundary) does not
  apply. This is what lets the inlined connection handler legally carry a `(sleep d)`
  delay step (`read → sleep → send`) and still launch as one strand. The timer is
  admitted **only as a sub-tree member, never as the single-step launch root**: a
  lone detached `sleep` is pointless, and detaching a `sleep` the continuation's
  effect depends on would run the continuation *before* the delay — so the
  single-step arm keeps refusing it (`src/bind_chain_analysis.rs::is_sleep_timer_leaf`).
  This refines E3 without widening it to opaque user fns: `sleep` is a known,
  resource-free primitive leaf, resolved through the import chain — not an
  interprocedural footprint walk.

**Conservative default.** Any step that fails E1–E3 lowers as an ordinary `Bind`
(serial) — never wrongly detached. (E1–E3 *tighten* the pre-S96 single-step arm, whose
`class != Sequential && result-discarded` test is necessary but **not** sufficient: it
omits E2/E3 and so could wrongly detach a discarded `Commutative` effect. Folding E2/E3
into the arm is a co-landing correctness improvement.)

**Par vs launch vs Bind — the three-way disposition.** result-discarded is the **first**
discriminator. A discarded + disjoint step/sub-tree (E1–E3) is a **detached launch** and
MUST be excluded from `Par` grouping: `Par` *joins* (the continuation awaits every
branch), so folding a discarded effect into a `Par` would needlessly serialize the
continuation behind work no one awaits — defeating the fan-out. A step whose result **is**
used downstream can never launch (you must await a value you use) and is a `Par` candidate
(≥2 independent non-`Sequential` steps that join) or a `Bind`. So the grouping decision is:
(1) discarded + disjoint ⇒ `LaunchContinue` (detached, never grouped); (2) result-used +
independent + non-`Sequential` ⇒ `Par` (joined); (3) else ⇒ `Bind`. For the inlined
server sub-tree this falls out trivially: the outer step's `io_expr` is a bind *sub-tree*,
which classifies `Sequential` (its head is `bind`, not a platform effect), so it never
enters Par competition and is decided entirely in the `Sequential` arm's extended
launch-eligibility check.

### 4.1.1 Scheduling state never rides on values — the `ctx` vtable handle model (ABI v9, S97, supersedes FIXME 0482)

> **Supersedes the descriptor-representation-overhead cut.** A prior S97 ruling
> (FIXME 0482 + the Phase-2 value-header descriptor model) treated `(token, capacity)`
> as trampoline-owned representation overhead carried on the *value* (a fixed-offset
> heap-header slot, a `desc_out` out-param on `PollFn`, a `ResourceDesc` type, a
> `ResourceRole`-on-the-value notion). **That model is RETIRED** (user-ratified
> 2026-06-30, after the Wave-2 DLL-mint blocker: an opaque zero-field `Connection`
> minted in the DLL as a 24-byte object had no room for a 16-byte header slot stamped
> at `value+24`, and reserving that slot at the DLL-mint→host-alloc boundary was an
> undesigned cross-crate interface). The replacement is **simpler and dissolves the
> blocker**: scheduling state never touches the value at all — there is **no header
> slot, no `desc_out`, no `ResourceDesc`, no `AsRawFd`-style trait**.

**Scheduling state never rides on user values. It flows through a trampoline-owned
`ctx` vtable that the platform's poll-fns call** — the existing host-owned-reactor waker
(§12, the A2 model) **generalized** from "register interest" to "register interest +
acquire/release a token permit + retire a token." The model:

- **Handles are tramp-opaque, NOT user-opaque.** A resource handle (`Connection`, …) is
  an **ordinary ADT** carrying genuine program data (the fd, a peer address, say). "Opaque"
  here means **opaque to the trampoline / runtime** — *not* opaque to the user program.
  The two readers are distinct:
  - **The trampoline never introspects the handle.** This is the architectural invariant
    that lets all scheduling live in the `ctx` vtable: there is no per-ADT "token is
    field N" knowledge anywhere in the host, no resource-handle layout marking, no
    reserved slot. The trampoline passes the handle straight back to the platform's
    poll-fn; only the **platform** reads `r` out of it (the platform built the handle, so
    it knows which field is `r`).
  - **The user CAN read the handle.** It is *their* connection — its fd and peer address
    are genuine program data, and the user reads them by ordinary destructuring /
    `match` exactly as for any ADT (`(match c [(Connection fd) fd])` typechecks and yields
    the real fd). There is **no special "no user destructuring path" mechanism**, and the
    field is **not** hidden behind opacity-marking. A resource handle is `std::net::TcpStream`
    with `as_raw_fd()` *available*, not a sealed newtype — the program owns its own resource
    and may inspect it. (The earlier "opaque ADT — the type does not export a user
    destructuring path" framing conflated the two readers and is wrong; the handle is
    tramp-opaque and user-readable.)
- **The `ctx` vtable** (the generalized `HostCtx`, §12) carries, alongside the existing
  `register_readable`/`register_writable`/`register_timer` + the C-ABI waker:
  - `acquire(token, capacity, waker) -> Acquired | Parked` — ask for a permit on
    `token`'s capacity-`N` pool. `Acquired` ⇒ a permit is held; `Parked` ⇒ no permit
    free, the `waker` has been enqueued on the token's permit-wait queue and will fire
    when one releases.
  - `retire(token)` — the resource's scheduling identity is gone (its `close` ran);
    drop the token's permit pool and wake any permit-waiters to observe the gone
    resource.
  - (the three `register_*` + waker — unchanged, the A2 reactor primitives.)
- **Release is trampoline-owned, NOT a vtable call.** The platform never releases. The
  host releases a held permit automatically when the poll completes (`Ready`) **or** is
  cancelled (the future drops) — and **cancel never re-enters the poll-fn**. The
  platform expresses *intent* (`acquire`); the host owns *lifecycle* (release). This is
  why `release` is absent from the vtable: the platform could not soundly release on a
  cancel it never sees.
- **The token is a derived scheduling projection of the handle, recomputed not
  remembered.** The platform computes it in the poll-fn from the handle it holds
  (default per-resource: `token == r`; **split per-direction** — `read`/`write` project
  distinct tokens off one full-duplex handle so they do not serialize against each
  other; `token == 0` ⇒ commutative / no acquire). Because the platform recomputes the
  token each poll, **there is no separate scoreboard** mapping handle→token: the host's
  only scheduling state is the semaphore-per-token permit map (§8.1) and the reactor's
  interest table — both inherent, neither a value-side or handle-side store.

**Handle fabrication is a platform-IO concern, never a host-soundness one (ruling).**
Because the handle is user-readable (above), the obvious next question is whether the user
may *construct* one — `(Connection 999)` with an arbitrary or unowned fd — and hand it to
`read-conn`. **Ruling: this is out of scope as a language/host soundness or capability
concern; the trust boundary is the platform's syscall (the OS), and a bad/unowned fd
errors safely.** Rationale:

- **No host UB is reachable.** The trampoline never introspects the handle, so a
  fabricated handle cannot corrupt any host scheduling state by being *read* — the host
  touches no field of it. The only host scheduling state is the permit map + reactor
  interest table, and both are populated solely as a *consequence* of an `acquire` /
  `register_*` call the **platform's** poll-fn makes after projecting a token. A
  fabricated handle therefore reaches the host only through a normal `acquire(token, …)` /
  syscall path — the same path a genuine handle takes.
- **The OS is the capability checkpoint.** fds are OS capabilities; a fabricated fd is
  just an integer. The platform's `syscall(fd, NONBLOCK)` on a bad/unowned fd returns
  `EBADF` (or operates on whatever fd is actually open at that number) — the platform
  surfaces that as an ordinary `IO` error, recoverable at `catch-runtime-error`. There is
  no UB, no crash, no hang.
- **There is no intra-program privilege boundary to violate.** A single Cranelisp program
  is not a sandbox; code that already holds the program's fds (and could call a raw-fd
  leaf or FFI directly) gains *nothing* from fabricating a handle that it could not
  already do. Restricting the **constructor** would be security theatre — and would
  directly contradict the just-established user-readability of the handle. So the answer
  is **not** "restrict the constructor" (option b); it is "the syscall is the check"
  (option c), backed by "a bad fd errors safely" (option a).
- **Worst case is a scheduling nuisance, never memory unsafety.** If a fabricated token
  collides with a live resource's token, the two merely share that token's permit pool
  (exactly as full-duplex per-direction tokens and the singleton stdin token already share
  pools by design) — at most spurious backpressure or over-admission on that one pool, a
  liveness/throughput annoyance, never corruption.

**Surviving invariant (pinned):** *the handle carries no scheduling state and the host
never introspects it; all safety of fd use is enforced at the platform↔OS syscall boundary,
not by restricting handle construction or reading.* Consequently a fabricated handle can
produce a recoverable platform IO error but never host-level UB or scheduling-state
corruption.

**Uniform poll-fn skeleton.** Every poll-shape leaf has the same shape:

```
poll(state, ctx, waker):
    token = project_token(state.handle)          # platform computes from its handle
    if token != 0:
        if ctx.acquire(token, capacity, waker) == Parked:
            return Pending                        # backpressure: never start an op without a permit
    r = state.syscall(NONBLOCK)                   # the platform's `what`
    if would_block(r):
        ctx.register_<interest>(state.fd, waker)  # the host's `when`
        return Pending
    set_result(state, value_from(r))
    return Ready
```

- A **commutative** leaf (token 0) omits `acquire` entirely (no permit; the token
  never appears).
- A **one-shot** leaf (`sleep`) is the degenerate case: no handle, no token, no
  acquire — just `register_timer(deadline, waker) → Pending → Ready`.
- `acquire` returning **`Parked`** returns `Pending` **before** the syscall — an op is
  never started without a permit (this is the backpressure / pool-bound, §8). `acquire`
  is **idempotent per in-flight effect**: a re-poll (woken because the fd became ready,
  or a permit freed) calls `acquire` again, and the host — keying held permits by the
  effect's identity (the waker's data pointer) — returns `Acquired` without consuming a
  second permit. So the skeleton needs no "have I already acquired?" flag on `state`;
  the host's per-effect permit accounting makes acquire safe to re-call.

**The four leaf roles** (a static, per-effect *manifest* fact — see the layering split
below; the trampoline does **not** branch on role at runtime):

| Role | Examples | Shape |
|---|---|---|
| **Produce** | `open` / `accept` / `connect` | Acquires/registers on the **establishment** resource (the listener fd for `accept`, a fresh socket fd for `connect`); at `Ready` mints the handle ADT carrying the new `r` and returns it. During establishment there is no program handle yet, so the platform drives `acquire`/`register` on the fresh `r` it minted — the handle materializes only at `Ready`. |
| **Consume** | `read` / `write` | `state.handle` **is** the platform's own handle (it reads `r` from it); projects the (per-direction) token, acquires, does the I/O syscall. |
| **Retire** | `close` | `close(r)` syscall + `ctx.retire(r)`. Ends the resource's scheduling identity. |
| **None** | a commutative GET, `sleep` | No token (or token 0); no acquire. |

**A full open / read / write / close trace** (generic; web is the worked instance,
`r == fd`):

```
program                 trampoline (host)                 platform poll-fn
───────                 ─────────────────                 ────────────────
(open …)        ──►  drive Produce leaf  ──►  acquire(establish_tok, waker)? Acquired
                                              connect(NONBLOCK) → WouldBlock
                ◄──  Pending                ◄  register_writable(fd, waker); Pending
   … reactor wakes on writable …
                ──►  re-poll Produce      ──►  acquire(…)=Acquired (idempotent); connect done
                ◄──  Ready(Conn{r=fd})     ◄  mint Conn carrying r=fd; set_result; Ready
                     RELEASE establish permit (tramp-owned, on Ready)
(read conn)     ──►  drive Consume leaf   ──►  tok=read_tok(r);  acquire(tok,1,waker)=Acquired
                                              recv(fd,NONBLOCK) → WouldBlock
                ◄──  Pending                ◄  register_readable(fd, waker); Pending
   … reactor wakes on readable …
                ──►  re-poll Consume      ──►  acquire(tok,…)=Acquired (idempotent); recv ok
                ◄──  Ready(Request)        ◄  set_result; Ready
                     RELEASE read permit (on Ready)
(write conn r)  ──►  drive Consume leaf   ──►  tok=write_tok(r); acquire(tok,1,waker)=Acquired
                                              send(fd,NONBLOCK) ok
                ◄──  Ready(Int)            ◄  set_result; Ready
                     RELEASE write permit (on Ready)
(close conn)    ──►  drive Retire leaf    ──►  tok=read_tok(r); acquire(tok,1,waker)=Acquired
                                              close(fd); ctx.retire(read_tok); ctx.retire(write_tok)
                ◄──  Ready(Unit)           ◄  set_result; Ready
                     RELEASE close permit (on Ready)
```

If the `(read conn)` future is **cancelled** while Pending (race loser / timeout /
scope exit), the host drops it: it deregisters the fd-waiter from the interest table
and releases the read permit it holds — **without ever re-entering the poll-fn**.
Because the held permit and the registration are both host-tracked (keyed by the
effect's identity), cancel cleanup needs nothing from the handle and nothing from the
leaf.

**The layering split — manifest vs `ctx`.** The **manifest** carries *compile-time
facts*: is-poll-shape? (the `blocking` flag), the leaf's **role** (Produce/Consume/
Retire/None), its **capacity default**, its **serialization class** (Sequential/
Commutative/ResourceSerial) — exactly what inference E1–E3 and codegen need. The **`ctx`
vtable** carries **ALL runtime scheduling** — acquire/register/retire + waker. This is
unix/rust-stdlib-aligned: a handle is an fd; `accept` returns `(stream, addr)`; `Drop`/
`close` retires. The split is clean because no runtime scheduling datum ever needs to
live on a value: the platform recomputes it from the handle, and the host tracks permits
and registrations by effect identity.

**This strengthens E2 (§4.1) without changing it.** E2's value-locality witness — "a
resource reachable only from a freshly-bound, non-shared value yields a fresh, disjoint
token by construction" — holds because the **platform** mints `r` fresh at the Produce
leaf's `Ready` edge and projects the token from it. The disjointness proof is unchanged;
its grounding is that the conn's `r` is born fresh at `accept`. **FIXME 0478** (the
single-step launch arm admits a discarded `ResourceSerial` step without the E2
value-locality check the sub-tree arm runs) is a **compile-time inference soundness**
fix that is sound under **any** representation — it co-lands with the /int work but is
**not gated** on this model.

**Singleton resources carry a manifest-static token** (resolves FIXME 0471
structurally). A resource not minted per value (stdin) has no handle to project from; it
declares a **manifest-static** serial token — `read-line`: `{token != 0, capacity 1,
role Consume}` — and its poll-fn calls `acquire(STDIN_TOKEN, 1, waker)` on that constant.
Single-in-flight stdin is then enforced by construction (the second concurrent
`read-line` parks), with no value, no header, no special case.

**Cross-resource co-serialization is still expressible (point e — confirmed).** Two
*different* resources can be deliberately co-serialized by having both leaves' poll-fns
project the **same** token — the permit then serializes access across them. This is the
*exclusion* form of the 0482-deferred "explicit token" knob, and it remains expressible
with no ABI change (the platform controls the projection). Its *ordered* form
(source-order across two different-provenance resources) is **not** expressible via a
shared token alone — see §8.2 — and, consistent with 0482's deferral, belongs to a
separate advanced API (an explicit ordering combinator, or a threaded handle that
creates a real data dependency the inference respects) if ever wanted.

**Discrete vtable functions, not a bundled `schedule(intent)` (confirmed).** `acquire` /
`register_*` / `retire` stay **discrete** fn-pointer entries rather than one
`schedule(intent: Intent)` data object. The operations have genuinely different return
types (`acquire` → `Acquired | Parked`; the rest → unit) and different argument shapes
(fd vs deadline vs token+capacity); bundling them behind one struct-carrying call buys
nothing and adds a struct ABI (Principle 2 narrow interfaces, Principle 6 budget). The
three `register_*` are themselves the generalized `register(source, interest, waker)`
specialized by source-kind (readable-fd / writable-fd / timer) — kept discrete for the
same reason (a unified `register` would need a tagged source union for one i32-vs-u64
argument difference).

## 5. The concurrency descriptor

The platform declares, per effect, a **concurrency descriptor** — a finite, declarative
generalization of today's scheduling classes (`Sequential` / `Commutative` /
`ResourceSerial`):

| Field | Meaning | Owner | Async substrate mapping | Slice |
|---|---|---|---|---|
| **token** | what the effect conflicts on = the resource identity (0 = unrestricted) | platform (dynamic) | which `Semaphore` | 3 |
| **capacity** | the resource's safe-concurrency *ceiling* — "this token correctly sustains ≤ N concurrent ops"; exceeding it is a correctness violation | platform (trust) | number of permits on the token's `Semaphore` | 3 |
| **degree** | the *program's* chosen in-flight throttle (memory / fairness / politeness), always ≤ capacity = the backpressure threshold | program (policy) | the **existing §8.1 token-permit map**, effective permits `= min(capacity, degree)` + one **global** admission `Semaphore` (reactor-thread) | **4 (S96)** |
| **blocking?** | does it block, or yield on `WouldBlock`? — selects the worker pool (inferable) | platform | CPU pool (rayon) vs reactor routing | 6 |

**capacity vs degree — two concepts the prior `cardinality`/`global-budget` framing
conflated, split by owner (user-ratified S95).** *capacity* is a **platform** attribute
of the **resource**: the ceiling the resource correctly sustains; the platform asserts
it (the trust boundary). *degree* is a **program** attribute: the application's chosen
throttle, for policy reasons, always ≤ capacity. **Effective limit = `min(capacity,
degree)`.** S95 slice 3 handles **capacity only**; *degree* is slice 4 (backpressure /
the former "global budget").

**FIXME 0442 resolution — TWO substrate-bound mechanisms, ONE shared *concept*, NOT one
unified abstraction (/arch, S96 Phase 2; the FIXME's trigger — slice-4 design — is now
MET).** The CPU spark budget and the I/O backpressure budget bound "in-flight work of a
kind," but they share **no runtime code path** and must not be fused:

- **Over-budget action diverges irreducibly.** A CPU spark over budget **folds inline**
  on the caller (a synchronous run-to-completion fallback the backend create-gate emits);
  an I/O effect over budget **admission-parks** (an async suspension until a permit
  frees). There is no common body — a "polymorphic over-budget strategy" would be a name
  over two disjoint operations (Principle 6).
- **The two substrates forbid a shared data structure.** The CPU counter lives on the
  **multi-threaded rayon** side, so it is *necessarily* a cross-thread `AtomicIsize`
  (slice-1 `ivar_spark`); the I/O admission lives on the **single reactor thread**, so it
  is *deliberately lock-free* (the `reactor.md` §2.8 `RefCell<HashMap<token, TokenSlot>>`
  reactor-thread permit map — a ruling that exists precisely to avoid atomics). Unifying them would regress one
  substrate: atomics forced onto the lock-free reactor pool, or unsoundness on rayon.
- **Neither is orphaned (Principle 8 honoured).** The slice-1 CPU counter stays exactly
  as built — a plain counter + cap + single decision site — and its *signal* (not its
  shape) is refined later by the contention-aware gate (FIXME 0459, S97 / Phase H), which
  is a **Parallelism-axis** owner, not slice 4's. The slice-4 I/O *degree* is **not new
  admission machinery**: it is a parameter on the **existing §8.1 token-permit map**
  (effective permits `= min(capacity, degree)`), plus one **global** reactor-thread
  admission `Semaphore` that bounds total in-flight detached strands (the
  launch-and-continue fan-out memory bound, §4/§10) — and that global gate reuses the same
  `AcquirePermit`/`TokenSlot` permit-counter the per-token pool already runs. What the two
  sides genuinely share is the **permit-counter shape**, realized once per substrate, not
  a forced common type. Slice-4 /design elaborates the `min`-threading + the global gate
  against this ruling; no `cranelisp-types` edge touch (degree/budget ride the already-
  reserved, `concurrency`-gated `ConcurrencyDescriptor.global_budget` + a reactor-
  construction knob — both off the frozen public-api edge).

**Capacity is per-RESOURCE (per-token), not per-effect — sharing is the central case,
not an edge.** The DB connection pool is canonical: `query`/`execute`/`begin` are
*distinct* effects that all draw from **one** pool of N connections (sum in-flight ≤ N).
Per-effect capacity cannot express it (it would yield N+N+N). So capacity attaches to
the **token** (the resource identity); effects *reference* the token. **Distinct token ⇒
independent capacity** (the per-effect special case); **shared token ⇒ shared pool** (the
DB case) — one mechanism, no special-casing. (This is why a per-symbol carrier such as a
`got_slot`-derived token is not merely inelegant but *incorrect*: per-symbol forecloses
sharing and so violates the pool bound. It is retired — §8.)

**Capacity rides WITH the token, platform-supplied dynamically at the effect site** —
not declared statically per-effect-kind. A connection pool's size is a *config* value
(`(connect-pool url :size 16)`), known only at runtime when the pool opens — exactly when
the per-connection token is minted. So capacity travels with the token, on the node
(§8). The descriptor's *static* `token`/`capacity` fields are **defaults + documentation
+ the v6 `from_scheduling_class` bridge** only; the **live** values are platform-supplied
at the effect site.

This is the platform's entire concurrency contract: declarative, finite, evolutionary
from the auto-IO machinery — not a new subsystem. It is also a **trust boundary**,
continuous with the existing one: the compiler does not verify that a `Commutative`
effect truly has no shared state, nor that an asserted *capacity* is the resource's true
ceiling, exactly as it does not verify a `ResourceSerial` token is correct. The platform
author asserts safety; the language takes it on faith (the platform's `unsafe`).

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
| token-capacity pool | `Semaphore(capacity)` keyed by token |
| backpressure | bounded channel / `Semaphore` |
| blocking/CPU split | reactor (I/O effects) + rayon (CPU sparks) |
| supervisor | `JoinSet` + catch the spawned handler's outcome |

So the work is not "build a fiber runtime"; it is **use the async runtime, provide the
inference (§4), and map the descriptors (§5) onto runtime primitives.**

**Runtime naming and gating — UPDATED (S96 SCOPE PIVOT EXTENDED, user-directed).**
The host runtime is a hand-written single-threaded executor over a `mio` reactor
(NOT tokio in the as-built; the App. B substrate). It is **NO LONGER feature-gated**:
the S96 full-streamline cutover (`platform-interface.md` §6.8.0 + §6.8.0a) retires
both the `concurrency` and `concurrency-runtime` features and collapses the former
two `#[cfg]`-selected trampolines (sync off-build + async on-build) into ONE async
trampoline — **the reactor IS the runtime.** The "pure / non-concurrent binaries
must not pay for the reactor" goal is preserved, but as a **RUNTIME property via lazy
reactor init**, not a `#[cfg]` split: the executor drives the top future on the
calling thread, and the mio `Poll` (epoll_create) + bridge waker (eventfd) are
constructed only on the first `Pending` (first poll-leaf fd/timer registration or
first `Par` blocking-bridge spawn). A program that performs no concurrent effects
(`(print "hello")`) drains synchronously through the one trampoline and constructs no
`Poll` — honouring the "empty prelude works" principle as a behaviour rather than a
build mode. `mio`/`futures`/`rayon` are unconditionally linked (accepted: no users,
no out-of-tree DLLs); Phase-H binary size is addressed by the lazy construction, not
by a link-time gate. The feature-off "byte-identical"/"reactor-free" invariant is
retired and replaced by the runtime assertion *"a pure-blocking program builds no
mio `Poll`."* See `platform-interface.md` §6.8.0a for the feasibility verdict +
sequencing; the `Reactor` lazy-singleton implementation detail is `/design` int's
(`design/intrinsics/reactor.md` — change specified there, not authored here).

**Level-2 (the state-machine transform) is DEFERRED — trigger named, not defaulted (S98,
FIXME 0486 closed).** The reified-IO-as-data choice above makes lifetime-across-suspension a
*runtime* discipline rather than a compile-time guarantee (a deferred effect's baked args are
held alive by the runtime `EffectPoll`, BC §4b invariant 15 — not by a backend-generated frame).
The alternative — have `/backend` co-generate a per-program Rust-async-style **state machine** that
holds each suspended effect's args across its suspend points by construction, moving the
lifetime half of the trampoline into codegen — was weighed and **deferred**. Its recurrence
trigger: *a second deferred-effect lifetime bug that the reified-data model cannot localize to
the runtime.* The S98 bug #2 (the launched-`send-conn` heap corruption) was **NOT** such a
recurrence: its actual cause was a plain `/backend` codegen traversal gap
(`find_var_type_in_expr` failing to reach the `conn` argument, starving the existing
consuming-inc — FIXME 0494, fixed `5ca6ef2`, hardened `0497`), fixed within the current model by
the runtime keep-alive (`75f286d`, net-zero-inc `StateClosure` at the `EffectPoll`/`reg` seam) +
the traversal repair — **not** a failure of the reified-data lifetime model. So the evidence
*reinforces* keeping reified-IO-as-data; Level-2 is not indicated. The executor half (the reactor
owning OS handles + DLL calls) is a runtime library under **any** split, so even if Level-2 were
taken, only the interpreter/lifetime half would move — not the whole trampoline.

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

**Verdict on `par-map`/`par-reduce` — no PRIMITIVE, but they ARE stdlib functions
(FIXME 0424(ii) / 0445, S93 /arch; user-ratified S93 Phase-3 review).** Two halves:

- **No explicit parallel-map/-reduce *primitive* / no new language surface.** A dedicated
  `par-map` *compiler primitive* or new syntax cuts directly against the ratified thesis
  (§1, §3): the programmer writes **zero concurrency primitives**, and parallelism is
  extracted from dataflow. Declined — and stays declined.

- **`par-map` / `par-reduce` / `par-map-reduce` ARE legitimate stdlib functions.** They are
  ordinary `.cl` library definitions that `/stdlib` writes and owns — **not** compiler
  primitives, adding **no language surface or syntax**. What makes them parallel is the
  **inferred apply-arg sparking substrate**, NOT any magic: a stdlib `par-map` is an
  ordinary `map`/`fmap` whose per-element applications spark because their apply-arguments
  are independent and individually expensive. 0424(i)'s generalization — spark independent
  apply-arguments fully — is the substrate these functions build on; once it lands, a plain
  `(map f xs)` over an expensive `f` already auto-parallelizes, and `par-map` is the
  intention-revealing, divide-and-conquer-shaped stdlib name for that behaviour (the D&C
  lifting recovers parallelism today even before the full generalization, by lifting each
  half into an independent `let`). They are **not magic primitives** — a reader can open
  the `.cl` source and see ordinary recursion + `let` independence.

The on-track inferred path is **0424(i)'s generalization** — 0424(i) (the divide-and-conquer
apply-arg shape) shipped S92, and its full-independence generalization is a rayon-side
increment. **0424 is now CLOSED (S94).** The substrate generalization that kept it open
shipped: apply-arg sparking (S92) + the dependent-binding spark (limit #2, S94 — a general
backend capability pinned by `tests/concurrency_spark.rs`) + the spark-budget create-gate;
`/stdlib` layered `par-map` / `par-reduce` / `par-map-reduce` as ordinary `.cl` functions
(`stdlib/collections/parallel.cl`, combine-in-body so they rely on §2.1 apply-arg
independence). The FIXME file was deleted; this paragraph is the historical record of the
arc.
The *(ii)-as-primitive* sub-question is **closed (declined)**. **0445 (the stdlib
divide-and-conquer interim-or-reserve question) is resolved the STDLIB-PROVIDES way:**
`/stdlib` provides `par-map`/`par-reduce`/`par-map-reduce` as ordinary `.cl` definitions
over the sparking substrate (superseding the earlier "names merely reserved / `/stdlib`
holds" disposition). `/stdlib` owns the implementation and its sprint placement.

## 8. The resource-token model under async — preserved and generalized

The extraction facts of §4 stand verbatim. Under the async substrate they map cleanly,
and **no concurrency is lost** — the available parallelism widens:

| Compile-time fact | Async execution |
|---|---|
| token-disjoint effects (independent) | separate concurrent futures — scales from ~hundreds of rayon threads to **thousands of pending futures** |
| same-token, capacity 1 (`ResourceSerial`) | `Semaphore(1)` / a sequential `await` chain |
| same-token, capacity N (new) | `Semaphore(N)` keyed by the token — the bounded pool you could not express before |
| degree (program throttle) | bounded channel / `Semaphore` — **slice 4** |
| blocking? | CPU-vs-reactor pool routing (the one **new** decision the descriptor drives) |

The bespoke "group-by-token, groups-parallel, within-group-serial" dispatcher
(`dispatch_par_branches_with_trace`) **dissolves into** "every effect acquires its
token's permit." That is a net mechanism simplification.

### 8.1 The slice-3 carrier — `(token, capacity)` dynamic on the node (the ratified seam)

> **v9 relocation (§4.1.1).** The carrier described below — `(token, capacity)` baked
> onto the IO node and read by the trampoline, which acquires the token's permit
> *around* the poll — is the v8 shape. Under the v9 ctx-vtable model the **leaf**
> computes the token (from its handle) and calls `ctx.acquire(token, capacity, waker)`
> itself; nothing is baked onto the node, and the trampoline does not acquire-around-poll
> or read any token off the node. The **permit mechanism below is unchanged** — a host
> `Semaphore(capacity)` keyed by token, `token == 0` ⇒ no acquire, the (capacity+1)th
> parks — only *who calls acquire* (the leaf, not the trampoline) and *where the token
> comes from* (the platform's projection, not a node field) move. Release stays
> trampoline-owned (on `Ready`/cancel). Read this section for the permit semantics; read
> §4.1.1 for the call-site relocation.

Capacity reaches the runtime the *same way the token already does* — **dynamically, on
the IO node, platform-supplied at the effect site** — not via a static `DefKind` field
or a synthesized per-symbol token. The mechanism is a one-field generalization of the
*existing* `ResourceSerial` carrier:

- **Today** the blocking constructor `CLIO::effect_on_resource(token, f)` bakes a dynamic
  `resource_token` onto the `IO_TAG_EFFECT` node (payload offset 16); the trampoline
  reads it (`read_resource_token`) and serializes same-token branches (`SerialGroup` =
  capacity 1).
- **Slice 3** generalizes this to carry a `(token, capacity)` **pair**: an additive
  sibling constructor `effect_on_resource_with_capacity(token, capacity, f)` appends
  `capacity` as a new node field (payload offset 32; the node widens 32 → 40 bytes,
  **append-only — no existing offset moves**, so the fn-name handle stays at offset 24).
  `effect_on_resource(token, f)` stays as `…_with_capacity(token, 1, f)` — today's
  serial-within-token. Symmetrically, an `IO_TAG_EFFECT_POLL` node reserves the same
  `(token, capacity)` slots (env or node — interior choice, §8.2), so both effect kinds
  feed one pool.
- **The trampoline keeps a `Semaphore(capacity)` keyed by token** (a host-owned
  `HashMap<token, Semaphore>`). An effect acquires its token's permit before dispatch and
  releases on completion; effects sharing a token share the semaphore; the (capacity+1)th
  **parks**. `token == 0` ⇒ no acquire (unrestricted). The slice-3 mechanism reduces to:
  *read `(token, capacity)` off the node; run a `Semaphore(capacity)` per token.*

**Consequences (the retirements this ratifies):** **no `DefKind.cardinality`/`capacity`
field, no loader lift of a static capacity, no `got_slot`-derived token, no two
token-notions.** The static descriptor `capacity`/`token` become documentation + the v6
default bridge (Sequential ⇒ token 1 / capacity 1; Commutative ⇒ token 0 / unbounded;
ResourceSerial ⇒ per-instance token / capacity 1); live values are platform-supplied.
This **removes the one `cranelisp-types` (`DefKind`) edge touch** the prior gate-(b)
verdict anticipated.

**Reconciliation rule (pinned): same token, different capacity ⇒ first-writer-wins
(the value that created the token's semaphore), and a dev-facing strand event records the
disagreement.** Rationale: capacity is a property of the *resource*, so all effects on
one token *should* assert the same N (the DB case reads N from one pool handle — they
agree by construction); a disagreement is a platform bug. An `assert`/abort is too harsh
for a trust-boundary violation that does not corrupt memory (it only mis-sizes a pool);
silently taking the max would *raise* the bound past a capacity the platform declared
unsafe. First-writer-wins is the conservative, deterministic choice (it never exceeds a
declared ceiling), and the recorded event surfaces the bug to the observability sink
(§11) rather than hiding it. (Later, the slice-4 *degree* throttle composes by
`min(capacity, degree)` regardless.)

### 8.2 Within-token source ordering — its home moves to the inference (v9 ctx-vtable consequence)

**One invariant to carry deliberately: within-token source ordering.** A bare semaphore
gives *exclusion* but not *order*, and order is observable for same-resource effects
(e.g. log appends to one file must land in source order).

**Under the v9 ctx-vtable model the trampoline no longer sees tokens** — the platform
computes the token in its poll-fn and the host never introspects the handle (§4.1.1). So
the v8 mechanism (trampoline reads the token off the node and groups same-token effects
into an ordered `SerialGroup` sequential async block) **dissolves with the rest of the
group-by-token dispatcher** (§8): the trampoline cannot group by a token it cannot see.
This relocates where the ordering guarantee lives — and it is sound, because the
guarantee was already the inference's:

- **Capacity-1 same-resource ordering is guaranteed by the inference, not the
  trampoline.** Two effects on the **same explicit handle** share that handle as a free
  variable, so E2 value-locality refuses to make them disjoint (§4.1) — they lower to a
  serial `Bind` in source order. The permit then provides *exclusion* (a same-token
  re-entrant `acquire` parks until release); *order* comes from the bind chain. So
  capacity-1 within-token source order holds **by the inference sequencing same-handle
  effects**, exactly the cases where order is promised.
- **Capacity-N pools are an unordered bag of N slots** — the inference parallelizes
  data-independent effects (Par), the permit bounds them at N, order is **not** promised
  (unchanged from §8.2's v8 statement; the DB pool case).
- **Shared singletons (Sequential token-1, stdout) are sequenced by the inference**
  (Sequential is never Par'd; E3 refuses detaching them), so their order holds without
  trampoline grouping. Their `acquire(token-1, 1)` never contends (only one in flight)
  and is a harmless redundant safety net.

**The one thing genuinely lost is the trampoline's order-restoring safety net for
*different-provenance* effects that alias to the same token** (two handles the platform
deliberately projects onto one shared token for *ordered* co-serialization). The permit
gives them exclusion but not source-order (the inference parallelizes them — distinct
handles — and the trampoline can no longer re-sequence them). This is the *ordered* half
of the cross-resource co-serialization knob, which 0482 already deferred (§4.1.1, point
e): the *exclusion* form survives via shared-token projection; the *ordered* form, if
ever wanted, is a separate advanced API — and arguably belongs there, since an ordering
constraint is more honestly expressed as a data dependency than a hidden shared token.

The worked example: concurrent HTTP GETs draw **distinct** connection tokens → run
concurrently; serial file block reads share **one** file token of capacity 1 → serialize
in source order; a DB pool's `query`/`execute` share **one** pool token of capacity N →
run up to N concurrently, the (N+1)th parks. All behaviors are preserved/extended exactly;
only the mechanism underneath simplifies.

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

### 12.1 The boundary is complete: poll-in / wake-out only — no closure-callback-into-cranelisp (S98 ruling)

**Exactly two functions cross the platform-effect boundary, and a cranelisp closure is
not one of them.** The shipped v9 ctx-vtable model (§4.1.1 — the A2 reactor, generalized)
has precisely:

- **poll-in** — the host calls the platform's `PollFn` (GOT-dispatched over a host-built
  state-closure), which returns `Ready(result)` or `Pending`. This is the *what*: the
  platform tries its non-blocking syscall.
- **wake-out** — the platform signals the host waker (the C-ABI projection of
  `std::task::Context`) through the `ctx` vtable (`register_readable`/`register_writable`/
  `register_timer` + `acquire`/`retire`). This is the *when*: the platform tells the host
  reactor to re-poll it later.

**Ruling (user, 2026-07-01): poll-in / wake-out is the COMPLETE platform-effect boundary.
There is NO closure-callback-into-cranelisp capability, by design.** A cranelisp closure
never crosses the boundary; a *continuation* is the trampoline's own suspended state
(§2, §4), held host-side — never a handle the platform holds and calls back. The platform
never re-enters cranelisp: it returns `Ready`/`Pending` and signals a waker, and the
trampoline (host-side) resumes the continuation. Three grounds:

1. **Thin, stateless platforms.** Poll-in/wake-out keeps every platform a C-ABI leaf that
   owns only its domain protocol and holds no cranelisp state. Admitting a host-mediated
   closure-call would push concurrency / state / RC / error-slot-ferry complexity into
   *every* platform — the Roc "cranelisp is a DSL on a platform written in a real language"
   platform-owned-loop degeneration this architecture rejects (§2, Appendix A). The reactor
   already rejects "Model B" (a platform owning its event loop and calling pure handlers)
   as a *concurrency mechanism*; this ruling closes the residual by rejecting it as a
   *capability*.

2. **The only residual — an un-invertible synchronous C dispatcher — is handled one layer
   lower.** A native library that *forces* nested synchronous re-entry within a single
   blocking call (a `qsort` comparator, an un-invertible GUI `run()` loop, a signal handler)
   is served by writing the callback **in the platform's own language (Rust)** and exposing
   only a poll-shaped effect to cranelisp. The re-entrant callback is a platform-interior
   concern; it never becomes a cranelisp-closure-across-the-C-ABI contract.

3. **The remaining sliver is economically void.** "A C library demanding a
   *cranelisp-authored* synchronous callback" forfeits the C library's speed the moment the
   comparator is cranelisp — which is the reason to reach for the C library at all. No real
   workload both needs the native library's performance and requires its inner callback to
   be cranelisp.

**Consequence.** The `HostCallbacks` table stays the two-pointer allocator surface
(`alloc` + `alloc_with_tag`); it is **not** widened with `invoke_closure` / `rc_inc` /
`rc_dec`. No `CLClosure` / `CLFn` wrapper type is introduced. The "escape hatch, build on
demand" disposition once parked against this gap is **retired**: the reactor (for
concurrency) plus Rust-side platform-interior callback wrapping (for synchronous
C-reentrancy) cover every real case. (This ruling retires the former FIXME 0407.)

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

**STATUS — SINGLE-ABI CUTOVER (S96, supersedes the v6/v7 coexistence below).**
User-directed 2026-06-29: there is now ONE platform ABI (v8). The dual-channel
"v7 reserved behind an off-by-default `concurrency` feature, byte-identical-off"
disposition described in this section is **HISTORICAL** — the ABI types
(`ConcurrencyDescriptor`/`Poll`/`PollFn`/`HostCtx`/`Waker`/`WakerVTable`) are now
**core/ungated**, `ConcurrentPlatformFn`/`ConcurrentPlatformManifest` merge into the
unified `PlatformFn`/`PlatformManifest`, the `concurrency` (layout-only) feature is
retired (the host **reactor** stays optional behind `concurrency-runtime`), and the
descriptor's `blocking` flag is the per-effect blocking-vs-poll discriminator in one
manifest. "byte-identical-off" becomes "**reactor-free-off**". Authoritative home:
`platform-interface.md` **§6.8.0**. The descriptor model (§5) and the A2 leaf model
(§12) below are unchanged — only the gating/coexistence packaging is superseded.

**PRIOR STATUS — ACTIONING (S93, effect-concurrency slice 2).** The track has opened; the
cascade is **being executed**, recorded at its natural home in
`platform-interface.md` **§6.8**. Two corrections to the pre-implementation text
above: (1) the numeric stamp steps **`ABI_VERSION` 6 → 7**, NOT "3 → 4" — the "3→4"
above was written when the live stamp was 3; the stamp is 6 at slice-2 open, so the
bump is 6→7 (sprint R5; "v4" is the doc-label for the async-leaf *model*, not the
numeric version). (2) The **layout contracts are landed this sprint** (S93), gated
behind an off-by-default `concurrency` feature (byte-identical-when-off): `Poll` /
`PollFn` / `ConcurrencyDescriptor` in `cranelisp-types`; `HostCtx` / `Waker` /
`WakerVTable` / `PollFn` / `ConcurrentPlatformFn` in `cranelisp-platform`. The
poll-shape effect fns + descriptor-in-manifest + host-reactor C-ABI are all reserved
in those types; the **wiring** (macro emit, host loader, host reactor) is the slice-2
reactor implementation. See `platform-interface.md` §6.8 for the per-crate change
list and the landed-and-dormant disposition.

**S94 R1 — the backend↔intrinsics poll-shape Effect-node seam, RATIFIED.** The S93
contracts cover the platform↔host seam (the ABI-v7 `ConcurrentPlatformFn` / `HostCtx`
/ `Waker` types) but left the *runtime representation of a poll-shape Effect node*
undefined. S94 ratifies it (the canonical /dev contract lives in Appendix B §"the
ratified backend↔intrinsics poll-shape Effect-node seam"; the ABI-field consequence
is recorded in `platform-interface.md` §6.8). The four decisions:

1. **Node representation — the closure-env model (chosen over a poll-descriptor).** A
   poll-shape effect is a new `IO_TAG_EFFECT_POLL` node whose field-0 points at a
   **host-built state-closure** reusing the existing heap-closure layout
   (`[header | code_ptr | drop_glue_ptr | env…]`): `code_ptr` = the GOT-loaded
   poll-fn, `drop_glue_ptr` = the state teardown, `env` = the marshaled args + a
   result slot + leaf scratch. Chosen because it inherits RC + drop for free (the
   trampoline's existing `consume_io_tree` drop walk releases the closure and runs
   its `drop_glue_ptr`), adds **no new platform-DLL type** for state/poll/drop (the
   closure layout is an in-process contract, not a DLL-ABI one), and honours
   Principles 7 (reuse) + 20 (a callable-with-state IS a closure). A
   `#[repr(C)] PollDescriptor` was rejected: it is a new DLL-crossing struct with
   hand-rolled RC/drop and more ABI churn.
2. **State construction / arg-marshaling — backend-built, host-internal (NO
   `make_state` export).** The backend's poll-construction arm loads the poll-fn from
   the GOT and **builds the state-closure directly**, marshaling the effect's i64
   args as closure captures — the established closure-construction codegen, pointed at
   a GOT-loaded `code_ptr`. This is structurally enabled because the poll-fn is a
   *named GOT export* (not an anonymous thunk like the blocking path's DLL-built
   node), so the host has everything it needs (poll-fn address + arg values) to
   construct the node itself. The poll-fn does first-poll setup (open fd, etc.) from
   the captured args. Consequence (R1 decision rule): state construction adds **no
   platform-DLL field** — nothing to reserve.
3. **Result extraction — generic offset read (NO per-effect `ResultReader`
   fn-pointer, NO platform-DLL field).** The poll-fn writes its single i64 result
   (scalar or heap base pointer) into a reserved result slot in the state-closure
   env; the generalized `EffectPoll` reads it generically once `Poll::Ready`. The
   result location is host-known (a baked node field or a fixed env offset — the
   carrier is /design backend+int's interior choice; the env layout is a v7
   host↔platform convention governed by `ABI_VERSION`). The S93 fixture's
   `ResultReader` fn-pointer collapses to this offset read.
4. **drop_state / cancellation — RESERVED NOW (the one platform-DLL field this seam
   adds).** Per the R1 reserve-now rule (the `global_budget` precedent), a
   `drop_state: Option<unsafe extern "C" fn(*mut c_void)>` field is appended to the
   dormant `ConcurrentPlatformFn` **this sprint, with no `ABI_VERSION` bump** (v7 is
   not yet frozen — no real cdylib has shipped against it), inert until the
   cancellation slice. The *primary* drop path is the host-side closure
   `drop_glue_ptr` (releases RC'd captured args); `drop_state` is the platform's
   optional hook the host bakes into that glue for **leaf-private heap** a host
   cannot know how to free — `None` when the inline env suffices (the S94 in-tree
   demo's case). Decisions (1)/(2)/(3) stay host-internal (no ABI field); (4) is the
   sole reserve, avoiding a future 7→8 bump.

## 14. Build sequencing (the implied roadmap, lightly)

The dependency order the architecture implies:

1. **descriptor (design)** — §5, the declarative contract.
2. **token-capacity pool** — `Semaphore(capacity)` keyed by token (§8); capacity is
   per-resource, platform-supplied dynamically on the node (§8.1).
3. **backpressure** — the program *degree* throttle; bounded channel / `Semaphore` (§5).
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

  **Disposition (S94 Phase-7 close, /arch) — DEFERRED, not added. A hand-off to
  next-sprint design, NOT a final resolution.** The candidate was carried from S93
  (arch R6) and is now *sharpened* by the S94 floor finding (§3.1 / FIXME 0459):
  atomic-RC + allocator contention is THE parallel bottleneck for stateful workloads,
  which is exactly the empirical case *for* confining mutable-state concurrency to the
  single-threaded interpreter (parallelism only over independent, allocation-/RC-light
  dataflow). The evidence now strongly supports the principle. It is **not added at
  this close** because its precise *boundary and wording* are coupled to design work
  that has not settled: (a) the **contention-aware-gate design** (FIXME 0459 — the
  static allocation/RC-density axis + the dynamic substrate-contention signal) decides
  operationally *what* counts as "mutable-state concurrency" the gate must keep on the
  interpreter; and (b) the **Phase-H structural cure** (thread-local RC / escape→stack
  / region / reuse) is *defined by* which values cross threads — which the concurrency
  model must settle first (Principle 8, the reinforced sequencing edge of §3.1).
  Pinning principle wording ahead of (a)/(b) would be reactive rule-making (the
  discipline the close-review guards against). **Hand-off: `/design` picks this up
  next sprint (S95) alongside the 0459 contention-aware-gate design; the principle is
  added/refined at THAT sprint's close once the boundary is concrete.** Recorded here,
  not in `design/arch/principles/`, precisely because it is not yet binding.

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
;;   both    — ResourceSerial on a connection-pool token of capacity N
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
    ;;   tokens (capacity N ≥ 2) → the two queries run concurrently.
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

**Slice 2 has opened (S93).** The async-substrate slice is in flight. As of S93 the
**ABI-v7 layout contracts are landed** (gated behind an off-by-default `concurrency`
feature — out of the default build and the `public-api.txt` edge until the reactor
wires them; see `platform-interface.md` §6.8):

- `cranelisp_types::{ConcurrencyDescriptor, Poll, PollFn}` — the descriptor (§5,
  incl. the inert-until-slice-4 `global_budget` field) + the poll-ABI primitives;
- `cranelisp_platform::{HostCtx, Waker, WakerVTable, PollFn, ConcurrentPlatformFn}` —
  the host-reactor C-ABI (§12, the one genuinely new designed artifact) + the v7
  poll-shape manifest entry; `ABI_VERSION` bumped 6 → 7;
- `cranelisp_intrinsics::{StrandId, StrandEvent}` — the strand-identity correlation
  newtype + the (slice-2-kinds-only) observability event enum (§11; the
  expensive-to-retrofit groundwork that lands *with* the substrate).

What remains in slice 2 (the reactor *implementation*, feature-gated /
byte-identical-when-off, cleanly spillable to S94): the feature-gated host async
runtime + the trampoline-as-`async fn`; the host reactor implementing the `HostCtx`
vtable; one async-leaf effect demonstrating two slow reads overlapping on the reactor
(no thread-per-read); and the trampoline emit-hooks feeding the strand-correlated
event stream. Slices ≥ 3 (token-capacity pool, backpressure, launch-and-continue +
supervisor, two-pool routing, the combinator layer) follow per §14.

### Slice-2 reactor — the implementable plan (decisions, S93 Phase-5 Wave-3, /arch)

DESIGN settled, implementation pending — this is the `/dev` brief. Five decisions,
the per-crate step list, the spill marker.

**Substrate — `mio` (reactor) + `futures` (executor), NOT tokio.** §6's
"tokio-or-equivalent" resolves to the *or-equivalent*: a thin host reactor over
`mio` (the cross-platform epoll/kqueue/IOCP abstraction) driven by a
`futures::executor::block_on` single-future executor. Rationale: (1) the landed
host-reactor C-ABI is **mio-shaped, not tokio-shaped** — `HostCtx` is "register a
raw fd + this `std::task::Waker` projection," which is exactly
`mio::Registry::register(SourceFd, Token, Interest)` + a waker; tokio hides its
reactor behind `AsyncFd` + its own task waker, so we would fight it to surface the
raw-fd/raw-waker registration the ABI already commits to. (2) Dependency weight —
`mio` + `futures` are two small single-purpose crates, trivially `dep:`-gated;
tokio is a large runtime. (3) `--link` — a smaller gated dep is a cleaner
byte-identical-off guarantee. (4) Extends cleanly — slices 3–8 need
`Semaphore`/bounded-channel/`select!`/`join!`, all in the `futures` ecosystem
without tokio; and the C-ABI **insulates platforms from the executor choice**, so a
later swap (even to tokio) is gate-local and ABI-invisible. (5) Principle 8 — not
throwaway: the mio reactor implementing `HostCtx` is the permanent host reactor;
`block_on` is the canonical std-adjacent executor, and the suspension mechanism is
genuine Rust `async`/`.await` (a compiler-generated state machine) — exactly what
"no hand-rolled fibers" requires (a hand-written *executor* loop that calls
`Future::poll` is not a fiber; a stackful coroutine with manual stack-switching is).

**Feature topology — two features; `--link` links neither.**

- `concurrency` (exists, KEEP) — the ABI-v7 **layout contracts only** (the v7 types
  in `cranelisp-types`/`cranelisp-platform`/`cranelisp-intrinsics`;
  `StrandId`/`StrandEvent`). ZERO runtime deps. This is the C-ABI surface a platform
  compiles against — a platform enabling it pulls in **no executor** (the A2
  "platforms carry no runtime" thesis preserved *structurally*).
- `concurrency-runtime` (NEW, in `cranelisp-intrinsics`):
  `concurrency-runtime = ["concurrency", "dep:mio", "dep:futures"]`. Gates the async
  trampoline + the `block_on` executor + the mio-backed `HostCtx` reactor + the
  strand sink. Forwarded by a root passthrough and (for the dev-sink surface)
  `src/`. NOT in default features; NOT enabled by the exe-bundle `--link` path.
- **`--link`-links-no-executor guarantee is structural**: `mio`/`futures` are
  `dep:`-gated optional dependencies, so with the feature off cargo never compiles
  or links them. The exe-bundle build path must never request `concurrency-runtime`;
  off ⇒ a linked binary is byte-identical and executor-free. **Backend needs no
  feature** for the minimal slice (see step list).

**Trampoline-async-fn restructure — ONE await boundary.** The sync
`run_io_trampoline_inner` (`crates/cranelisp-intrinsics/src/io.rs`) already unwinds
to itself at every effect (the continuation stack is explicit + heap-valued; IO is
reified as data), so the restructure is narrow:

- Add an async twin `async fn run_io_trampoline_inner_async(io_ptr, host: &HostCtx,
  sink, strand: StrandId) -> i64`. Its loop body is the sync body **verbatim except
  the Effect arm**. Factor the per-node step logic (tag read, `Bind` push, `Pure`
  unwrap, the `call_continuation` feed) into shared **sync** helpers so the sync and
  async loops differ ONLY at the Effect arm (no node-logic duplication — Principle 7).
- **The single await boundary is the Effect leaf.** The Effect arm `.await`s an
  `EffectPoll` future whose `Future::poll(cx)` builds a C-ABI `Waker` projecting
  `cx.waker()`, calls the platform poll-fn `poll(state, *HostCtx, *Waker) -> Poll`,
  and maps `Poll::Ready` → `Ready(value-from-state)`, `Poll::Pending` → `Pending`
  (the platform has registered its fd/timer with the reactor via `HostCtx`).
- `call_continuation`, `Bind`, `Pure` STAY synchronous (straight-line code between
  awaits). CPU sparks (`ivar_spark` → rayon) STAY on rayon — unchanged (the §7
  two-pool split: rayon = CPU, reactor = I/O).
- The C-ABI entry `cranelisp_run_io(io_ptr) -> i64` keeps its signature; it
  cfg-splits — runtime-on constructs the mio reactor + `HostCtx` and `block_on`s the
  async trampoline; runtime-off is today's sync `run_io_trampoline_inner`,
  **byte-identical**.
- **Overlap (the "two reads" acceptance) needs a SECOND async point: the `Par`
  arm.** For I/O-effect `Par` branches, runtime-on lowers the branches to
  `futures::future::join_all` of `run_io_trampoline_inner_async(branch, host, sink,
  fresh_strand)` on the executor (concurrent futures on the single reactor — NO
  thread-per-read), instead of the rayon `dispatch_par_branches_with_trace`. The
  rayon dispatcher STAYS as the feature-off path AND the CPU-spark path. Token
  grouping / `Semaphore`-per-token is DEFERRED to slice ≥ 3 — minimal Par-async =
  `join_all` over token-disjoint branches.

> **CLOSED in S94 — real poll-shape effect nodes now suspend on the reactor through
> `cranelisp_run_io`.** S93 landed only the spine (the `EffectPoll` `.await` boundary
> reachable only by the fixture demo leaf). S94 ratified the backend↔intrinsics node
> seam (next subsection) and wired it end-to-end: the real async Effect arm over
> `IO_TAG_EFFECT_POLL` + the backend poll-construction arm (keyed on
> `DefKind::PlatformEffect.poll_shape`) + the `ConcurrentPlatformManifest` /
> `cranelisp_concurrent_manifest` / dlsym-probe channel (FIXME 0457) + a real
> `declare_platform!`-emitted in-tree async leaf. The 5 reactor e2e rows
> (`tests/concurrency_reactor.rs`) are green: two **real** leaves overlap in ≈max(delay)
> on one reactor thread, the i64 result reads back, and the strand stream shows
> `Dispatched → Suspended → Resumed`. The S93 fixture-leaf demo remains as the substrate
> regression guard. **Caveat carried to slice ≥3 — the §7 two-pool routing is NOT yet
> wired:** under `concurrency-runtime`, *blocking* effects in a `Par` route through the
> single-threaded reactor `join_all` rather than rayon/`spawn_blocking`, so they no
> longer overlap (poll-shape leaves do). Feature-OFF (the production default) is
> unaffected — blocking-effect `Par` still parallelizes on rayon. This regresses
> feature-on blocking-`Par` throughput until two-pool routing lands; it surfaces as 3
> RED wall-clock witnesses in the `nt-reactor-e2e` lane
> (`resource_serial_diff_token_parallelizes`,
> `auto_io_independent_diff_token_parallelizes_e2e`,
> `auto_io_par_grouping_uniform_across_modes`) — a known slice-3 gap (§7 / §14 item 5),
> not a 0457 regression. See `design/intrinsics/reactor.md` §4 for the as-built reactor
> interior.

### The ratified backend↔intrinsics poll-shape Effect-node seam (S94, R1 — the /dev contract)

This is the canonical `/dev` brief for slice-2 completion — the concrete representation
/design backend + /design int + /qa build against. Four decisions (rationale in §13
"S94 R1"):

1. **Node = closure-env.** A new `IO_TAG_EFFECT_POLL` node (pinned `= 4` —
   `IO_TAG_PAR` is the current max `3`; homed in `cranelisp-platform/src/lib.rs`
   alongside the other `IO_TAG_*` constants, `#[cfg(feature = "concurrency")]` so it
   stays off the default `public-api.txt` edge); field-0 → a **host-built
   state-closure** in the existing layout `[header(16) | code_ptr@16 = poll-fn |
   drop_glue_ptr@24 = state teardown | env@32 = result-slot + i64 args + scratch]`.
   The blocking `IO_TAG_EFFECT` node is **untouched** (R3 byte-identical-off): it is
   only ever constructed for blocking effects, which is every real platform today; the
   poll node is only ever constructed for poll-shape (`blocking == 0`) effects, which
   only exist in a `concurrency`-built toolchain. The backend needs **no cargo
   feature** — its second arm is keyed on the effect's declared shape and is reached
   only by concurrency-gated poll effects.
2. **State = backend-built, host-internal.** The backend's poll-construction arm loads
   the poll-fn from `__cranelisp_got_platform_<name>` (GOT-indirect dispatch
   preserved — the load happens once at construction, baked as `code_ptr`) and builds
   the state-closure, marshaling the effect's i64 args as captures — the existing
   closure-construction codegen. **No `make_state` platform export**; no eager call to
   platform code at the effect site (unlike the blocking path, which calls the DLL fn
   to build its node). The trampoline (not the backend) supplies `HostCtx`/`Waker` —
   at poll time, in `EffectPoll::poll(state=env, host, waker)`.
3. **Result = generic offset read.** The poll-fn writes its i64 result into the env
   result slot; `EffectPoll` reads it at a host-known location (baked node field or
   fixed env offset — /design backend+int choose) on `Poll::Ready`. The fixture's
   `ResultReader` fn-pointer collapses to this.
4. **drop_state = reserved-but-inert** (`ConcurrentPlatformFn.drop_state`,
   `Option<unsafe extern "C" fn(*mut c_void)>`, landed S94, no `ABI_VERSION` bump).
   Primary drop = the closure `drop_glue_ptr` on `consume_io_tree`; `drop_state` is
   the platform's optional hook for leaf-private heap, `None` for the in-tree demo.

**The poll-discriminator channel (S94 R1, FIXME 0457) — how `poll_shape` reaches the
backend arm.** The backend keys decision (1) on `DefKind::PlatformEffect.poll_shape:
bool` (landed in `cranelisp-types`, `#[serde(default)]` = `false` = blocking). The
loader populates it: a v7 platform exports a separate `cranelisp_concurrent_manifest`
(a gated `ConcurrentPlatformManifest` carrying a `ConcurrentPlatformFn` array); the
concurrency-built host dlsym-probes it, lifts each entry's `concurrency:
ConcurrencyDescriptor`, and sets `poll_shape = (descriptor.blocking == 0)`. v6
platforms (no v7 export) ⇒ `poll_shape = false`, byte-identical. The full descriptor is
**not** stored on `DefKind` (it stays `concurrency`-gated, off the frozen edge);
`poll_shape` is the orthogonal dispatch axis beside the existing `scheduling_class`
conflict-domain axis. Full per-crate channel spec + sequencing:
`platform-interface.md` §6.8 "S94 R1 (FIXME 0457)" (0457 resolved + deleted S94 — the
channel is as-built; see `design/intrinsics/reactor.md` for the as-built reactor interior).

**Trampoline.** Both node kinds flow through `run_io_trampoline_inner_async`; the
Effect arm `.await`s an `EffectPoll` for `IO_TAG_EFFECT_POLL` and forces synchronously
(no await) for `IO_TAG_EFFECT`. The sync stepper (feature-off) only ever sees
`IO_TAG_EFFECT`. **What /qa can assert:** (a) feature-off: no `IO_TAG_EFFECT_POLL` is
ever constructed; the v6 blocking path is byte-identical; (b) feature-on: a real
`declare_platform!`-emitted in-tree poll leaf, driven through `cranelisp_run_io`,
suspends and resumes on the reactor (strand `Dispatched→Suspended→Resumed`); two such
leaves in a `Par` overlap in ≈max not sum on one reactor thread; (c) the leaf's i64
result is read back correctly via the generic offset read; (d) `--link` links no
executor.

**Demo leaf — `async-read` (poll-shape, fd + `register_readable`).** A
built-in/fixture poll-shape effect whose `state` holds a non-blocking raw fd + a
result buffer; `poll` does `recv(fd, …, NONBLOCK)` → on bytes, write the result +
`Ready`; on `EWOULDBLOCK`, `register_readable(host, fd, waker)` + `Pending`.
Acceptance: two `async-read`s over two socketpairs whose write side is fed after a
delay (driven by the host reactor's `register_timer`, so still single-reactor, NO
per-read OS thread) run as two `Par` branches → complete in ≈ **max**(delay) not
sum, on ONE reactor thread, and the `StrandEvent` stream shows
`EffectDispatched → EffectSuspended → EffectResumed` interleaved for the two
distinct strands. The poll-fn is HAND-WRITTEN (fixture/built-in) — the
`declare_platform!` macro poll-emission is a later slice (`platform-interface.md`
§6.8 deferred), so NO backend / platform-macro change is needed to demo the
mechanism.

**Strand observability hook — minimal, feature-gated sink.** A thread-safe
`StrandEvent` sink (sibling to `IoObserver`, hosted in
`crates/cranelisp-intrinsics/src/strand.rs` behind `concurrency-runtime`; a
registration fn like `io_observer`). The trampoline emits via `emit_strand_event(ev)`
that compiles to a no-op when off. Emit sites (minimal): `EffectDispatched{strand}`
in the Effect arm before the await; `EffectSuspended{strand}` in `EffectPoll::poll`
on `Poll::Pending`; `EffectResumed{strand}` in `EffectPoll::poll` on a re-poll.
Strand identity: the async `Par` arm mints a fresh `StrandId` per branch (a monotonic
`AtomicU64`, child of the current strand) so the demo's two reads are
distinguishable; the root is `StrandId::ROOT`. (`SparkCreated`/`SparkForced` on the
rayon path are present in the enum; their emit is slice ≥ 3, once spark strands
matter.)

**Reactor IMPLEMENTATION location — `cranelisp-intrinsics`, not `src/` (sharpens BC
§6 + the scheduler diagram).** For the *policy* (construction parameters, pool
sizing, backpressure, the dev sink, feature-gating) "the reactor is int's" holds. But
the reactor *implementation* (the mio loop + the `HostCtx` impl + the `block_on`
executor) MUST be hosted in `cranelisp-intrinsics`, because (1) the C-ABI entry
`cranelisp_run_io` / `cranelisp_run_program` that drives the trampoline lives in
intrinsics and cannot depend on int (`int` → intrinsics, never the inverse); and
decisively (2) **a `--link`'d program does not contain `src/` at runtime** — int is
the compiler binary, not linked into the output — so a reactor hosted in int could
never drive a linked program's effects. Hosting it in intrinsics
(runtime-feature-gated, linked into `--link` output) serves `--run`/REPL now AND is
the only placement that can serve `--link` concurrency later. This mirrors the
`io_observer` split (int owns the ring buffer/policy; the registration API is hosted
in intrinsics). The minimal slice targets `--run`/REPL; `--link` concurrency is a
later slice, but the placement makes it reachable without a relocation.

**Per-crate `/dev` step list (platform → backend → int; intrinsics carries the
substrate):**

| # | Crate | MINIMAL step | Seam | Unit-test hook | Deferred to slice ≥ 3 |
|---|---|---|---|---|---|
| 1 | `cranelisp-platform` | NONE for the mechanism — the C-ABI types are landed. A hand-written fixture poll-fn for the demo leaf (or `/qa` owns it). | `src/concurrency.rs` (landed) | fixture poll-fn returns Pending-then-Ready; assert `HostCtx::register_readable` called | `declare_platform!` emits poll-fns + `ConcurrencyDescriptor`; manifest `PlatformFn`→`ConcurrentPlatformFn` |
| 2 | `cranelisp-intrinsics` | **the substrate.** (a) `concurrency-runtime` feature + mio/futures deps; (b) the mio reactor + `HostCtx` impl (new `reactor.rs`); (c) `run_io_trampoline_inner_async` + `EffectPoll` (the one await boundary); (d) async `Par` `join_all` path; (e) `cranelisp_run_io` cfg-split `block_on`; (f) the `StrandEvent` sink + emit hooks + per-branch `StrandId`. | `io.rs`, new `reactor.rs`, `strand.rs` | `EffectPoll` suspend/resume on a fixture reactor; two-branch overlap completes in ≈ max; strand events emitted in order | `Semaphore`-per-token `Par` grouping; `SparkCreated`/`Forced` emit; launch-and-continue |
| 3 | `cranelisp-backend` | **(S94, was "NONE" for the S93 spine.)** A second, additive **poll-construction arm**, keyed on the effect's declared shape (no cargo feature): for a `blocking == 0` effect, load the poll-fn from the GOT and build an `IO_TAG_EFFECT_POLL` node over a host-built state-closure (`code_ptr` = poll-fn, captures = marshaled i64 args, reserved result slot). Blocking effects take the unchanged v6 arm (R3 byte-identical-off). | `compiler/` effect-site codegen; reuse closure-construction codegen | feature-off baseline stays byte-identical (no poll node constructed); a poll effect builds the `IO_TAG_EFFECT_POLL` node with the expected closure layout | `Semaphore`-per-token grouping; the `drop_state` glue contribution (cancellation slice) |
| 4 | `src/` (int) | feature passthrough (`concurrency-runtime` forward); ensure default + exe-bundle/`--link` never enable it; wire the dev-sink surface (a `/strand` dump is OPTIONAL/spillable). | Cargo features; exe-bundle build path | feature-off baseline tests stay byte-identical | backpressure/supervisor/pool-sizing policy; reactor construction parameterization; `--link` concurrency |

**Spill marker — the spillable stretch (what `/dev` drops FIRST if it runs long):**

1. FIRST to drop: the **`Par`-async overlap** (step 2d) + per-branch strand minting +
   the richer sink. Landing just the **single-leaf suspend/resume** (steps 2a–2c +
   2e + one `EffectDispatched/Suspended/Resumed` on `ROOT`) still proves the spine:
   async trampoline + mio reactor + the `HostCtx`/`Waker` C-ABI + one `StrandId`
   path. The "two reads overlap" acceptance then carries to S94.
2. SECOND to drop: the `/strand` REPL dump (step 4 sink surface) — the sink can land
   as a registration-API + in-memory buffer with a test-only reader, no REPL command.
3. The reactor itself (the load-bearing new artifact) is NOT spillable — it is the
   point of the slice.

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
- the **token-capacity pool** (`Semaphore(capacity)` keyed by token, capacity dynamic on
  the node — §8.1) and **backpressure** (the program *degree* throttle; bounded channel /
  `Semaphore`) — today capacity is implicitly 1 per non-zero token value;
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
