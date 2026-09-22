# Lenient Evaluation Design

Current contract for automatic parallel evaluation of independent pure
sub-expressions: which candidates spark, how a spark is emitted, joined and
bounded, and the IVar runtime cells it rides on. Owned by `design` (backend).

- **Normative behaviour** is `spec/12-runtime.md` §12.4.1 and §12.4.3. They
  require independent `let` bindings to be parallelised under a cost heuristic.
  They permit the same for independent arguments of a function application, and
  keep left-to-right order as the *observable* order, including first-error-wins.
- **Architectural thesis** is `design/arch/effect-concurrency.md` §3.1–§3.1.6,
  the utilization and contention axes. The CPU/IO budget split is its §5.
- **Open performance work** is held in `design/arch/backlog/performance.md`
  (0534, 0535, 0536). `design/backend/lenient-eval.md` §2.8.8 points there.
- **Delivery history and superseded designs** are in Git and
  `sprints/archive/`.

Section numbers are anchors cited from source, tests and other designs; §7 is
unused.

## 1. Purpose and invariants

Cranelisp binding values and arguments are pure: effects flow through `IO` and
`bind!`, never through raw evaluation. So evaluating independent, expensive
sub-expressions concurrently gives the same result as any sequential order. The
backend exploits that without changing any observable behaviour.

The design holds five invariants:

1. **Declining is always sound.** Spark versus inline is a scheduling choice.
   Every admission filter, gate and depth bound may decline freely (§8).
2. **Structured fork-join.** Every sparked IVar is forced at a barrier before
   the enclosing `let` body or call instruction runs (§4.2, §4.4). Ferry
   soundness (§5) and capture-by-borrow (§4.4.1) both rest on this.
3. **Budget before allocation.** The runtime budget decision precedes IVar and
   thunk allocation, so the over-budget path allocates nothing (§3.6).
4. **One analysis, two sites.** The `let` and apply sites share one admission
   core, one gate helper and one emission mechanism (§2.5.1).
5. **Byte-identical when off.** Every tuning and diagnostic knob below leaves
   emitted code unchanged when unset, except where its default is stated.

## 2. Sparkability analysis

Sparkability is a codegen-internal decision taken at IR generation, after
typechecking. It does not change the AST, the check result or any cross-crate
type. The decision pass is `control_flow/sparkability.rs`; the M-static
classifier is `control_flow/utilization.rs`.

Admission has three layers, applied at both spark sites:

| Layer | Question | Where |
|---|---|---|
| Per-candidate predicate | Is this candidate worth sparking? | M-static (default, §2.8.2) or the syntactic filter (§2.2) |
| Independence | May it run before its siblings are bound? | `let`: §2.1/§2.6; apply: always (§2.5.2) |
| Count | Are there at least two survivors? | Shared ≥2 gate |

`CRANELISP_SPARK_ADMIT=syntactic` selects the syntactic predicate. Any other
value, including unset, selects M-static. The independence rule and the ≥2 gate
compose identically with either predicate inside `find_sparkable_bindings_with`
and `find_sparkable_args_with`.

### 2.1 The `let`-path rule

Given `let` bindings `[(x0, e0) … (xN, eN)]`, scan left to right. Binding `i` is
admitted iff:

1. the per-candidate predicate holds for its RHS; and
2. every earlier-bound free variable of the RHS denotes a binder that was itself
   admitted (§2.6). An independent binding satisfies this vacuously.

The admitted set is kept only if it has **at least two members**. A single spark
pays IVar creation and pool submission for no concurrency.

Earlier-bound means earlier in the *same* binding vector. The question is asked
of a binder position, not a name, through the shared resolver
`sparkability::binder_before` (`binding-scope.md` §Binding environment). A
repeated name is two binders (`spec/04-expressions.md` §4.3), so a non-sparked
rebinding displaces the earlier binder's spark record by construction.

### 2.2 The syntactic cost heuristic (selectable)

Under `CRANELISP_SPARK_ADMIT=syntactic`, a candidate is worth sparking iff:

- it is an `Apply`;
- its callee is not one of the cheap builtins
  `+ - * / = < > <= >= not and or`;
- its callee is not a data constructor, compared by bare member name; and
- the density axis (§2.7) does not decline it.

A computed callee, such as `((get-fn) arg)`, counts as worth sparking because
its cost is unknown. Literals, variable references and unapplied lambdas are
never candidates.

This filter is purely syntactic. On recursion and speculative search it
over-sparks by orders of magnitude (§2.8), which is why M-static is the default.
It remains as the comparison row for measurement.

### 2.3 Trace-body exclusion

Inside a `(trace …)` body no site sparks, because interleaved traced execution
would make trace output non-deterministic. Both sites test `in_trace_body`
before admission.

### 2.4 Opt-out and suppression

Both sites skip admission entirely when any of these hold:

- **`CRANELISP_NO_LENIENT=1`** (read once per process into `LENIENT_DISABLED`).
  This is the debugging escape hatch and the sequential equivalence oracle.
- **`suppress_spark_gate`.** It is set while the direct arm of a create-gate is
  compiled (§3.6.2), so a statically nested chain of sites in one body compiles
  once per arm, not O(2^depth) times.
- **IO combinator callees (apply site only).** An apply whose resolved call is
  one of the inline IO combinators (`apply::IoCombinator`) never sparks its
  arguments (`s122-closure.md` §8).

### 2.5 Apply-argument sparkability

The arguments of `(f a₁ … aₙ)` are candidates under the same predicate and ≥2
gate. The callee itself is never sparked.

#### 2.5.1 One analysis, two call sites (Principle 7)

`find_sparkable_bindings[_with]` and `find_sparkable_args[_with]` are siblings
over one shared per-candidate predicate and one ≥2 gate. They are separate
functions because their inputs differ in shape and their independence rules
differ. Folding them together would need a union signature for no shared logic.
Duplicating the predicate or the gate into one site would be the
recurring-mirror defect that Principle 7 forbids.

#### 2.5.2 Argument independence

Evaluating an argument binds nothing into its siblings' scope, so the arguments
of one apply are **mutually independent by construction**. Apply admission is
therefore just the per-candidate predicate plus the ≥2 gate, with no dependency
check. There is no dependent-argument analogue of §2.6.

#### 2.5.3 Interaction with the callee and tail calls

The pre-pass runs at the top of `compile_apply`'s non-TCO arm. Both TCO
self-call fast paths `return` before it. So a tail self-jump, which would jump
to the loop header past the force barrier, can never reach a spark site. Trace
exclusion (§2.3) and the opt-out and suppression rules (§2.4) apply exactly as at
the `let` site. When at least two arguments are admitted, the site is wrapped in
the create-gate (§3.6.2).

### 2.6 Dependent-binding sparks (`let` path only)

A `let` binding whose RHS references an earlier **sparked** binding may itself
spark. Its thunk forces the dependency's IVar on demand. This is the substrate
for the stdlib `par-*` divide-and-conquer shapes. It is backend-internal, reuses
the IVar machinery (§3) and the create-gate (§3.6) unchanged, and has no
public-API effect.

#### 2.6.1 The admission rule

- An **independent** binding is admitted iff the predicate holds.
- A **dependent** binding is admitted iff the predicate holds **and** every
  earlier binder it references is already admitted. A dependency on a
  non-sparked binder excludes it: that binder is bound only as an ordinary
  `Value` in Phase 2 (§4.2), which a thunk created in Phase 1 cannot see.

Dependencies point only backward in a sequential `let`, so source order is a
valid topological order and one left-to-right pass suffices.

#### 2.6.2 What it extracts, and the floor's scope

When a binding depends *entirely and immediately* on one spark, as in
`(b (f a))`, its thunk blocks on `a` almost at once and gains little. The gain
comes from a **partially dependent** RHS: in `(b (g (f a) (h c)))`, the `(h c)`
work runs while `a` is still computing.

The create-gate (§3.6.3) still bounds spark-**machinery** cost: IVar and thunk
allocation stays `O(cap)`, and dependent thunks count toward the same batch. It
does **not** bound per-branch **user-level contention** (§3.6.3 scope). For
allocation- or RC-heavy parallel work, heap allocation and atomic-RC cache-line
traffic can make parallel slower than serial. That floor belongs to Phase H
(`effect-concurrency.md` §3.1; `ring2-rc.md` §5.5.2.7).

#### 2.6.3 Why the dependency is forced, not captured

Phase 1 creates and sparks every IVar before Phase 2 binds any value. When a
dependent thunk is built, its dependency is therefore an unforced IVar, not a
`Value` in scope. The thunk captures the **IVar pointer** and forces it inside
its body. Forcing from both the dependent thunk and Phase 2 is safe:
`ivar_force` (§3.5) is idempotent under its CAS state machine. Whoever claims
first computes, and every other reader gets the resolved value. §4.5 is the
emission.

### 2.7 The allocation/RC-density axis (B4) — dormant

B4 is a static contention proxy, reachable **only** through the syntactic
predicate (§2.2) and **disabled by default** (`SPARK_DENSITY_MAX_DEFAULT = 0`).
It is not part of default admission. The reason is recorded in §2.8.5.

**Score.** `spark_density` walks the candidate subtree and reads only the
per-site ownership facts pass 5 already annotated (`ownership-codegen.md`
§13.4). For each heap-result allocation site that is not `NoEscape`:

- **+1** on the heap-pressure axis; and
- **+1** on the surviving-RC axis, unless the site is `Confined` or a
  borrow-elided projection.

A `NoEscape` site scores 0, a scalar-result site is not scored, and a site with
no fact counts as dense.

**Activation.** The axis is **inert** when the subtree carries no ownership fact
(for example under `CRANELISP_NO_OWNERSHIP=1`). This polarity is deliberate: a
facts-absent build must not score everything dense and silently stop all
sparking. When engaged, a candidate whose score exceeds
`CRANELISP_SPARK_DENSITY_MAX=N` is declined. `0` disables the axis.
`CRANELISP_SPARK_DENSITY_TRACE=1` prints one codegen-time line per scored
candidate.

**Standing.** The concept remains valid for the alloc/RC-dense compute-bound
class. Its planned return is as the *input* to a density-aware depth allowance
(0535, §2.8.8), not as an admission-decline filter. Any non-zero threshold must
be set by measurement in the change-set that re-enables it.

### 2.8 The utilization model — spark for core occupancy

The goal is **core utilization, not fine-grained parallelism**. Dispatch a small
number of large, separable work items, roughly two per core, and let each run
its subtree sequentially.

Two independent levers deliver this:

- **M-static** (§2.8.2) decides *which* candidates spark, at compile time.
- **Depth decline** (§2.8.4) decides *how many*, at runtime.

The create-gate's concurrent cap (§3.6) bounds live memory; it is not the count
lever (§2.8.3).

**Measured outcome** (10-core host, default depth 3, single-shot per §2.8.7):

| Fixture | Serial | Parallel | Reading |
|---|---|---|---|
| F6: 16 balanced alloc-free leaves | 3.10 s | 0.82 s | 3.4× |
| F5: recursive `fib` fork | 0.67 s | 0.39 s | 1.7×; spawns ~619K → ~14 |
| F4-hard: Sudoku speculative search | 0.88 s | ~2.3 s | Over-sparking cured (~55 s before M-static); still above serial (§2.8.8) |
| F3: alloc-heavy imbalanced search | 0.53 s | ~3.7 s | Contention class; above serial (§2.8.8) |

#### 2.8.1 Actors and the functions between them

| Actor | Role | Where |
|---|---|---|
| Producer | Chooses spark or inline per candidate | `compile_let` (§4.1), `compile_apply` (§4.4), then the create-gate branch |
| Pool | The fixed rayon work-stealing pool: the shared resource | `ivar_spark` → `rayon::spawn` (§3.4) |
| Strand | One dispatched thunk running its subtree | the spawned closure in `ivar_spark` |
| Consumer | Joins the strand at the barrier | `ivar_force` at Phase 2 (§4.2, §4.4) |

The costs between them:

1. **Produce or inline** costs compile-time classification plus one runtime
   `try_reserve`.
2. **Dispatch** is IVar creation, spawn, wake and steal: about 13 µs measured.
   It pays only if the strand then runs a body far larger than that on an
   otherwise idle core.
3. **Sequential execution** is where the useful work happens.
4. **Force/join** takes one of three paths: the resolved fast path, a claimed
   inline compute, or a wait. A force almost immediately after dispatch means
   the dispatch bought nothing.

The model avoids two failure modes:

- **Over-production at the frontier.** Millions of tiny sparks are forced
  immediately; F4's `(cell-at g i)` accessor pairs produced 13.1M. M-static
  cures this.
- **Internal re-explosion.** Each coarse strand re-sparks all the way down a
  divide-and-conquer tree. Depth decline cures this.

#### 2.8.2 M-static — the quality axis

**Rule.** A candidate is admitted iff it is an `Apply` whose resolved callee is
in a **recursive strongly connected component** of the static call graph and the
apply is **not in tail position** (`utilization::mstatic_admits`). Non-tail
recursion is the structural "probably large" signal.

**Derivation, with no new interface** (`effect-concurrency.md` §3.1.2):

- The call graph is built backend-internally from the persisted
  `ModuleEntry::Def` `callees` edges (Decision 21). Tarjan SCC
  (`recursive_scc_members`) marks members of any SCC with more than one node, or
  with a self-edge.
- The set is built once and cached per `FnCompiler`
  (`mstatic_recursive_set`). An inner compiler rebuilds the identical set.
- The `callees` feed omits direct self-edges, because the recursion name is
  shadowed at check time. Direct self-recursion is therefore recovered per site
  through the shared `is_self_call` predicate, the same one TCO and the stack
  gate use (`backend.md` §2).
- Spark candidates are always compiled in non-tail position, so the tail
  conjunct is `false` at every current site. Tail self-calls are excluded
  earlier, by the TCO fast paths (`design/backend/lenient-eval.md` §2.5.3).

**Soundness is toward decline.** A candidate is declined, never guessed as
recursive, when it is not an `Apply`, its callee is computed or reached through
a closure or HOF, or its callee `Def` is not loaded. M-static deliberately does
not consult the cheap-builtin, constructor or density checks. A cheap builtin or
constructor is never in a recursive SCC.

**Discrimination:**

| Candidate | Recursive SCC? | Verdict |
|---|---|---|
| `(add-i64 (fib a) (fib b))` | yes (self) | spark |
| `reduce-tree` recursive fork | yes | spark |
| F4 coarse `(solve-range …)` | yes | spark |
| F4 fine `(cell-at g i)` accessor | no | decline |
| mutual recursion `a → b → a` | yes (SCC > 1) | spark |
| computed or unresolved callee | unknown | decline |

Measured on F4-hard, M-static alone took fine-accessor spawns from 13.1M to 182.

**M-static does not bound count.** A divide-and-conquer recursion is non-tail at
every level, so M-static re-admits sites all the way down. Grade F4 as an
interaction: neither lever clears it alone.

#### 2.8.3 The concurrent cap does not bound cumulative spawns

The create-gate (§3.6) counts **concurrent** in-flight sparks and **recycles
permits on completion**. A recursion therefore never latches the pool full: as
strands finish, deeper sites re-reserve. F5 stayed at about 1.5M spawns at every
cap value tested.

The cap bounds *simultaneity* and live IVar memory, not cumulative count. The
count collapse therefore has to be structural (§2.8.4).

`IN_FLIGHT_SPARKS` remains the single budget counter (the one-counter ruling,
`effect-concurrency.md` §3.1.3). The depth mechanism adds no counter, only a
per-thread nesting level.

#### 2.8.4 Hierarchical decline by logical depth, and force backoff

**Invariant.** Beyond a bounded fan-out, a dispatched strand runs its subtree
sequentially with no further sparking.

**Mechanism** (all module-private in `ivar.rs`; no export):

- A thread-local `SPARK_DEPTH` holds the logical spark-nesting depth of the
  thunk the thread is running. The top level is 0.
- `ivar_force`'s claim-compute arm, the single choke point where any thunk runs,
  raises depth by one around the thunk call. This applies on the main thread and
  on workers, and whether the IVar was spawned or claimed inline at a barrier.
- `ivar_spark` captures the sparking thread's depth. The spawned closure restores
  it as the base before forcing, so a stolen child runs at `parent + 1` on
  whichever worker steals it.
- `spark_budget_try_reserve` checks depth before the concurrent cap: at
  `SPARK_DEPTH ≥ MAX_DEPTH` it returns 0, so the site takes the direct arm.
- `MAX_DEPTH` defaults to `floor(log2(threads))`, clamped to ≥ 1; that is 3 on
  the 10-core host. `CRANELISP_SPARK_MAX_DEPTH=D` overrides it: `0` inlines
  everything and `1` inlines each dispatched strand's whole subtree.
  `CRANELISP_HIER_DECLINE=0|off` disables the depth check for ablation.
- Total spawns become about `2^MAX_DEPTH = O(threads)`, independent of tree
  size.

**Why a depth allowance, not a boolean.** A depth-1 cutoff bounds spawns but
collapses a balanced coarse tree to the few splits the main spine reaches (F6
≈1.9×, peak ~8). A deeper allowance lets a bounded tree fill the cores while a
deep recursion still collapses. The default keeps `2^D ≤ threads`, well under
the `2 × threads` cap, so the depth cutoff bites before budget pressure does
(§2.8.8, budget-inline ceiling).

**Force backoff.** A consumer that loses the claim CAS waits with an escalating
backoff: `spin_loop` for 128 iterations, then `yield_now` for 512, then 50 µs
sleeps. `CRANELISP_IVAR_SPIN=1` restores pure busy-spin. This is CPU hygiene,
not a wall-time lever: F3 CPU fell from 617% to 275% at neutral wall, because
F3's cost is contention (§2.8.8). The CAS protocol and the ferry are identical
on either path.

#### 2.8.5 B4 is off by default

At full cores on the recursion/search class, B4 is net-harmful. It declines the
coarse divide-and-conquer sparks, which score dense, while the fine accessor
sparks, which score 0, stay admitted. Measured on F4-hard: 112 s with B4 on,
24 s with admit-all, 0.9 s serial.

That "decline coarse, admit nested fine" state must never be a default. With
M-static owning selection and depth decline owning quantity, B4 has no role in
default admission. `CRANELISP_SPARK_DENSITY_MAX=N` (with
`CRANELISP_SPARK_ADMIT=syntactic`) remains the opt-in diagnostic row.

#### 2.8.6 Codegen seams and the unit-scenario space

No mechanism here touches a public edge. There is no backend or intrinsics
`public-api.txt` delta and no `cranelisp-types` edit.

| Mechanism | Seam |
|---|---|
| M-static | `utilization.rs` (`recursive_scc_members`, `mstatic_admits`, `FnCompiler::mstatic_admits_candidate`), consumed by both sites through the `_with` cores |
| Create-gate | `let_if.rs::emit_create_gate`, shared by both sites (§3.6.2) |
| Depth decline, force backoff | `ivar.rs`, module-private |
| Site recording | `record_spark_sites_{let,apply}`: M-static classification per admitted site under `CRANELISP_SPARK_STATS`; measurement only |

Scenario classes the unit tier must hold:

- **SCC classification:** self-recursive, mutually recursive, flat and
  unresolved callees, crossed with the per-site self-call recovery.
- **Composition:** M-static with the §2.6 carve-out and the ≥2 gate, through the
  `_with` cores.
- **Depth boundary:** spark below `MAX_DEPTH`, inline at or above it. A stolen
  child observes `parent + 1`. The main-thread claim arm increments depth.
- **Create-gate cap boundary:** `cap − 1` in flight sparks; `cap` inlines. The
  batch is all-or-nothing.
- **Backoff:** the wait resolves to the claimant's value and re-raises a ferried
  panic.
- **B4:** the facts-absent and threshold-0 inert cases, plus score arithmetic.

#### 2.8.7 Measurement rules

The utilization levers move results by orders of magnitude, so measure them
single-shot. A repetition, idle-guard or thread-sweep harness is the wrong
instrument here.

- **Time wall-clock with `CRANELISP_SPARK_STATS` off.** Under hierarchical
  decline the per-declined-site counter fires hundreds of millions of times.
  With stats on, F5 read 5.8 s against a real 0.7 s.
- **Take counts from a separate stats-on run.** Never read wall and counts from
  one process.
- **Check `load1` is near zero before a timed run.** An idle-guard inside a
  sweep defeats itself, because the sweep's own reps keep the machine busy.
- **Use the rigorous harness only for final acceptance.**
  `tests/perf/s104_utilization.py` is that harness; its plan is
  `tests/plan/s104-utilization-measurement.md`.

The F1–F6 fixtures each isolate one axis: F1 coarse-parallel, F3/F4
alloc/RC-dense, F5 deep-recursion count, F6 balanced alloc-free compute. The
finer attribution seams for the contention residual are specified in
`ownership-codegen.md` §13.2.2.

#### 2.8.8 Open obligations

Each obligation below has its canonical home in
`design/arch/backlog/performance.md`. They are listed here so a change to this
mechanism sees them.

- **0535 — density-aware depth allowance.** A single `MAX_DEPTH` cannot serve
  both regimes: F6 wants deep, F4/F3 want shallow. The intended cure makes
  depth a function of the strand's allocation/RC density (§2.7's signal): deep
  for alloc-free strands, shallow for alloc-heavy ones. Re-entry: `design`
  (backend) revises §2.7/§2.8 with `arch`'s `effect-concurrency.md` §3.1, and
  it is graded on the F1–F6 lanes.
- **0536 — budget-inline depth ceiling.** A create-gate declined for *budget*
  runs its direct arm at the same depth, because depth advances only inside
  `ivar_force`. A deep recursion inlined shallow then re-sparks when permits
  recycle. Usable depth is therefore capped near `log2(cap)`: F5 goes to about
  1.3M spawns at D=4, against 14 at D=3. The default sits under the ceiling.
  Raising it, as 0535 needs, first requires the direct arm to advance depth.
  When that lands, re-check the F6 peak: the depth-1 collapse of §2.8.4 is the
  regression it could reintroduce.
- **Contention floor (Phase H).** Alloc/RC-dense compute (F3, and the alloc-heavy
  part of F4) stays above serial. The cost is in-leaf vec copy-on-write and
  atomic-RC traffic, which no scheduling lever removes
  (`effect-concurrency.md` §3.1; `ring2-rc.md` §5.5.2.7).
- **F4-at-D3 trade (user-accepted 2026-07-07).** The D=3 default regresses
  F4-hard relative to D=1 to keep F6's 3.4×. 0535 is what dissolves the trade.

## 3. IVar runtime primitives

IVars are write-once synchronization cells. They are `extern "C"` exports of
`cranelisp-intrinsics` (`ivar.rs`), registered in the intrinsics catalog and
called by name from emitted code. This section is the contract the backend
emits against. All IVar atomics are SeqCst (Decision 13), including the spark
RC increment, which deliberately bypasses `rc::rc_inc`.

### 3.1 Heap layout

Base-pointer convention (Decision 10); 48 bytes, a 16-byte header plus a 32-byte
payload:

```
+0   alloc_size  i64   (= 48)
+8   rc          i64   atomic; 1 at creation
+16  state       i64   atomic: PENDING 0 / EVALUATING 1 / RESOLVED 2
+24  value       i64   valid once RESOLVED
+32  thunk       i64   zero-argument closure base pointer
+40  error       i64   ferried panic String, or 0 (§5)
```

`value` and `error` are published together by the single SeqCst store of
`RESOLVED`.

### 3.2 State machine

- `PENDING → EVALUATING`: CAS in `ivar_force`; exactly one thread wins.
- `EVALUATING → RESOLVED`: store by the winner after writing `value` and
  `error`.

No other transition exists.

### 3.3 `cranelisp_ivar_create(thunk) -> ivar`

Allocates the cell with `rc = 1`, `state = PENDING`, `value = 0`, `error = 0`,
and stores the thunk pointer. The IVar takes over the thunk's single reference.
The thunk uses the standard closure layout (Decision 11):
`[header | code_ptr@16 | drop_glue_ptr@24 | captures…]`, called as
`code_ptr(env) -> i64`.

### 3.4 `cranelisp_ivar_spark(ivar)`

**Always spawns.** The create-gate (§3.6) has already chosen the lenient arm
before the IVar existed. `ivar_spark`:

1. increments the cell's RC for the spark task;
2. captures the current `SPARK_DEPTH`; and
3. calls `rayon::spawn` with a closure that:
   - arms `InFlightGuard` first, so the permit is released last, including on
     unwind;
   - restores the parent depth and calls `ivar_force`;
   - clears the worker's own runtime-error slot (§5);
   - decrements the RC, and frees the cell through `dealloc_ivar` if it reached
     zero.

It returns 0.

### 3.5 `cranelisp_ivar_force(ivar) -> value`

- **Resolved fast path:** re-raise any ferried error, then return `value`.
- **Claim path (CAS won):**
  1. Save the caller's runtime-error slot.
  2. Raise `SPARK_DEPTH` and call the thunk.
  3. Take any runtime error into a fresh String in `error`.
  4. Restore the caller's saved first error.
  5. Store `value` and `error`, then publish `RESOLVED`.
  6. Re-raise any ferried error on this thread.
  7. Release the thunk: run its drop glue, then decrement and free it.
- **Wait path (CAS lost):** wait for `RESOLVED` with the §2.8.4 backoff, then
  re-raise and return `value`.

This is **work conservation**. A consumer that reaches the barrier before a
worker has started claims and computes the thunk itself. The worker later takes
the resolved fast path.

### 3.6 The in-flight-spark budget and the backend create-gate

**Why it is before allocation.** The static decision cannot see dynamic
recursion depth. An in-`ivar_spark` budget would come too late: every sparkable
position would already have allocated a thunk and a cell. That measured about
140× serial on naive `fib`, even at cap 0. The budget decision is therefore a
codegen concern, emitted before any allocation. It has two parts:

- a reservation counter and try-reserve primitive in `ivar.rs`; and
- a create-gate in the backend, shared by both sites.

#### 3.6.1 The reservation counter and try-reserve

`IN_FLIGHT_SPARKS` is a process-global `AtomicIsize`. It is signed so that a
stray over-decrement stays below the cap and keeps granting, rather than
wrapping and wedging the budget permanently to direct.

`cranelisp_spark_budget_try_reserve(n) -> {0,1}`:

1. **Depth check** (§2.8.4): return 0 if `SPARK_DEPTH ≥ MAX_DEPTH` and decline
   is on.
2. **Fast reject:** return 0 if a single load shows `cur + n > cap`. The
   over-budget path is load-only, with no read-modify-write.
3. **Commit:** a CAS loop adds all `n` permits at once, or returns 0.

The batch is **all-or-nothing**. One site reserves every one of its `n ≥ 2`
positions or none. A check-only query would leave a TOCTOU window between check
and allocation and make the cap a soft target.

**Cap** (`effective_spark_cap`, read once per process):

1. an explicit `CRANELISP_SPARK_BUDGET=N`;
2. else `threads` when `CRANELISP_SATURATION_GATE=1`;
3. else `k × threads`, with `k = CRANELISP_SPARK_CORE_MULT` (default **2**).

`N = 0` or `k = 0` rejects every reservation. Non-parsing values fall back to
the default. The saturation gate stays opt-in; it recovered only about 9% of
the contention term (`ring2-rc.md` §5.5.2.7).

**Release accounting.** One permit is released per completing spark, by the
`InFlightGuard` drop inside `ivar_spark`'s closure. Release is not callable from
emitted code. A granted batch always creates exactly `n` IVars, and creation
cannot fail short of process abort. So `reserve(n)` ↔ `n` spawns ↔ `n` guard
drops is balanced by construction, and the guard covers unwinds.

A leaked reservation is the dangerous direction: it silently degrades toward
permanent serial. Consumer claim-compute does not change accounting, because
the spawned task still runs and drops its guard.

#### 3.6.2 The create-gate (backend codegen)

`emit_create_gate(n, …)` wraps every admitted site:

```
granted = call cranelisp_spark_budget_try_reserve(iconst n)
brif granted, lenient_block, direct_block

lenient_block:   Phase 1 create+spark n IVars; barrier-force each; body/call  → jump join(v)
direct_block:    the unchanged sequential lowering, nested gates suppressed   → jump join(v)
join(result: i64)
```

- **One join, one block parameter.** Both arms produce the site's result as one
  `i64`, so downstream RC treatment is unchanged.
- **Identical values.** A forced spark is byte-identical to the same expression
  evaluated directly. Only the schedule differs.
- **The barrier stays inside the lenient arm.** No path reaches the body or call
  with an unforced IVar. The direct arm has no IVars.
- **The direct arm suppresses nested gates** (§2.4) for the rest of that arm
  within the same function body. A lambda body nested in the arm, like a callee
  body compiled elsewhere, is a separate compile and keeps its own gate,
  reached at runtime.
- **Per-arm naming.** Inner functions compiled on each arm carry an arm
  discriminator (`gate_arm_disc`), so the two copies do not collide.
- **Tail calls.** The TCO fast paths return above the gate (§2.5.3).
  `in_tail_position` is saved and restored per arm.
- **Cost without explosion.** One granted `try_reserve` per site.

**Ferry soundness — inline spark.** On a claim-compute by the consuming thread,
that thread's runtime-error slot may already hold the first error from an
earlier barrier-forced sibling. `ivar_force` saves the slot before the thunk and
restores it afterwards (§3.5 steps 1 and 4). So an inline panic cannot displace
an earlier first error. On a spawned worker the saved slot is empty and the
save/restore does nothing.

#### 3.6.3 Floor restoration, and its scope

For an over-sparking recursion, about `cap` sites near the root reserve and
spark. Deeper sites get 0 from one load and run the direct arm with no
allocation. Completions re-admit a bounded frontier, subject to the depth
decline of §2.8.4. Live IVar and thunk allocation is therefore `O(cap)`, not
`O(nodes)`.

Two residuals are intended:

1. one load-only `try_reserve` per sparkable site, which is the `ON < 1.3·OFF`
   tolerance; and
2. the granted frontier's spark overhead, which is the parallelism the feature
   exists to buy.

**Scope.** This restores the floor against spark-**machinery** cost only. It
cannot see per-branch user-level contention. For alloc/RC-heavy branches,
parallel can run slower than serial until the Phase H memory mechanisms land:
the S99 ablation measured F2 at 2.3–3× and F4 at 6–15× slower
(`tests/plan/s99-measurement.md` §8–§10; `effect-concurrency.md` §3.1).

**Two routes to serial.**

- `CRANELISP_NO_LENIENT=1` emits no gate, IVar or spark.
- A cap of 0 emits the gate, but every site takes the direct arm with no
  allocation. This is the runtime route for an already-compiled binary.

The two are observably equivalent.

**Both sites are gated.** The budget is global, and the `let` site has no other
budget, so an ungated wide `let` inside a recursion could re-explode.

#### 3.6.4 Boundary facts

- `cranelisp_spark_budget_try_reserve(n: i64) -> i64` is the one C-ABI symbol
  the create-gate adds. It is in the intrinsics catalog and the intrinsics
  `public-api.txt`, next to `cranelisp_ivar_{create,spark,force,dealloc}`.
  Counter, cap, guard and depth state are module-private.
- The CPU spark budget and the IO backpressure budget share a concept but no
  mechanism. Their over-budget actions differ (inline versus admission-park),
  and so do their substrates (cross-thread atomic versus reactor-thread state).
  Ruled in `effect-concurrency.md` §5 (FIXME 0442 resolution).

## 4. Codegen path

### 4.1 `compile_let` decision point

```
if !NO_LENIENT && !in_trace_body && !suppress_spark_gate {
    sparkable = find_sparkable_bindings_with(bindings, predicate)   // §2.1, §2.6
    if sparkable.len() >= 2 {
        return emit_create_gate(n,
            lenient = compile_let_lenient(…),                         // §4.2
            direct  = compile_let_sequential(…))
    }
}
compile_let_sequential(…)
```

### 4.2 `compile_let_lenient`

Per-binding-vector state is keyed by **binding position** (§2.1).

1. **Phase 1 — create and spark.** Handle admitted positions in ascending
   (source, topological) order:
   - Build the thunk:
     - an **independent** RHS becomes a synthetic zero-parameter `Lambda` of
       type `(Fn [] T)`, compiled through `compile_spark_thunk`;
     - a **dependent** RHS becomes a manual thunk (§4.5).
   - Call `cranelisp_ivar_create`, then `cranelisp_ivar_spark`.
   - Record the IVar against the position.
2. **Phase 2 — bind in order.** For each binding:
   - a sparked position is forced with `cranelisp_ivar_force`, then its
     reference is released with `emit_rc_dec_for_ivar` (IVar-aware dealloc);
   - any other position is compiled normally.

   Each value is bound with `bind_local`. This is the barrier: every IVar is
   forced before the body, in source order.
3. **Phase 3 — the body,** compiled normally with return protection and scope
   cleanup.

`compile_spark_thunk` raises two flags around the thunk compile and restores
them on every exit:

- the capture-borrow flag (§4.4.1), when enabled; and
- `in_spark_thunk`, which makes constructions relocated into the thunk decline
  stack placement (`ownership-codegen.md` §4.3, gate 5). A stack slot would
  dangle at the join.

### 4.3 Thunk closure layout

A thunk is an ordinary closure (Decision 11):

```
+0 alloc_size | +8 rc | +16 code_ptr | +24 drop_glue_ptr (0 if none) | +32… captures
```

Its captures are the RHS's free variables that are in scope in the enclosing
function. Its drop glue releases them, unless they are borrowed (§4.4.1).

### 4.4 Apply-argument emission

Section §2.5.3 places the pre-pass, and the create-gate (§3.6.2) wraps the site.
The lenient arm has three phases:

1. **Create and spark** each admitted argument, exactly as §4.2 Phase 1 does for
   an independent binding. The resulting map is installed as `sparked_args`,
   keyed by the argument-slice base pointer. A nested apply or constructor can
   then never consult it.
2. **Barrier.** The unchanged apply lowering builds the argument vector left to
   right. `maybe_force_sparked_arg` forces each sparked position and releases
   its reference; every other position is compiled in place. Every sparked
   argument is forced before any call instruction is emitted, which is what
   keeps the construct a structured fork-join.
3. **Dispatch** through the unchanged `dispatch_apply`: resolved call, variable
   apply, constructor, closure or direct call. The enclosing `sparked_args` is
   restored afterwards.

The direct arm calls `dispatch_apply` with no `sparked_args` installed. Sparked
and direct arms keep constructions on the heap.

**RC and the consuming convention.** A sparked argument is always a non-trivial
`Apply`, so its forced value is a fresh temporary at `rc = 1`. It transfers into
the callee as a sequentially compiled temporary would, and no consuming
increment is owed. Other positions keep their normal per-argument treatment.

#### 4.4.1 Capture-by-borrow on the spark thunk (opt-in)

With `CRANELISP_CAPTURE_BORROW=1` (off by default, byte-identical when off),
`compile_spark_thunk` sets `spark_capture_borrow`. The thunk's heap captures of
enclosing-scope bindings then become borrows. `lambda.rs` skips **both** the
capture-store increment and the matching drop-glue decrement, coarsely, for
every heap capture. It is sound because the joined parent frame outlives the
spark (invariant 2). The returned value is still the single transferred
reference.

- The RC contract, soundness argument, failure mode and test obligations are
  `ring2-rc.md` §5.5.2.
- The ablation measured about 0% on the contention term, so the flag stays
  opt-in (§5.5.2.7).
- The detached `LaunchContinue` path never sets the flag.
- `ParBind` sets it for its own joined branches.

**Carve-out.** The IVar-pointer captures of a dependent thunk (§4.5) are
**never** borrows. They are keepalives of a sibling spark's cell, not
parent-owned bindings. The dependent thunk is built by the manual path, which
never reads the flag.

### 4.5 Dependent-binding emission

For a dependent admitted binding, `compile_dependent_thunk`
(`control_flow/dependent_spark.rs`) builds the thunk's inner function manually,
in the `par_bind.rs` style, rather than through `compile_expr(Lambda)`. At
Phase 1 the dependency is not a variable in scope, so the generic capture path
cannot reach it.

- **Capture layout:** `[ordinary captures…, dependency IVar pointers…]`,
  dependencies sorted by name. Ordinary captures follow the standard closure
  rules.
- **Prologue:** for each dependency, load the captured IVar pointer, call
  `cranelisp_ivar_force`, and bind the dependency **name** to the forced value.
  The **unmodified** RHS is then compiled, so its `Var(dep)` resolves to that
  value.
- **No new `MonoExpr` shape and no boundary change.** A MonoExpr-level rewrite
  would need `arch` first.
- The inner compiler sets `in_spark_thunk` (gate 5) but never the borrow flag.

**The RC rule for captured IVar pointers** (load-bearing):

- Each dependency pointer is `emit_rc_inc`'d when stored into the thunk
  environment.
- The thunk's drop glue decrements it through the IVar-aware path. When the
  count reaches zero, `cranelisp_ivar_dealloc` frees any ferried error String,
  then the cell.

This increment keeps the dependency's cell alive after Phase 2 releases the
consumer's reference. The cell's references are then:

- one for the consumer;
- one for the spark task; and
- one per dependent capture.

The cell is freed exactly once, when the last of these goes. Phases 2 and 3 are
unchanged: a dependent binding is forced at the barrier like any other spark.

#### 4.5.1 Observational equivalence for the dependent case

- **Value.** The dependent thunk computes from the same resolved value that
  sequential evaluation of the dependency produces.
- **First error.** If the dependency panics, both the dependent thunk's force
  and the Phase 2 force observe the ferried error. Phase 2 forces in source
  order, so the dependency's error surfaces first, as in sequential evaluation.
- **Non-termination.** A diverging dependency hangs its dependent at the same
  point sequential evaluation would.

## 5. IVar disposal and the error ferry

**No IVar drop glue is needed.** Under the barrier, every IVar is forced before
its scope exits. Then the consumer's release and the spark task's release, plus
any dependent-capture releases, bring it to zero, and whichever release is last
frees it. An IVar is never dropped while `PENDING`. Per-use-site forcing, which
would allow an unforced drop, is out of scope; adopting it would require IVar
drop glue.

**The fork-join error-slot ferry** (`design/arch/test-discovery.md` §6)
conveys a spark's runtime panic to the joining thread:

1. **Worker-side stash.** The claimant takes its thread's runtime error after
   the thunk. A message becomes a fresh `rc = 1` String in `error`, published
   with `value` (sentinel 0) under the `RESOLVED` store.
2. **Join-side re-raise.** Every reader of a resolved cell calls
   `reraise_ferried_error`. That means the claimant, a waiter, and the fast
   path. The call decodes `error` without consuming it and sets the reader's
   slot first-error-wins. Every joiner therefore sees the same message.
3. **Worker-slot hygiene.** `ivar_spark`'s closure clears its throwaway worker
   slot after forcing, so later rayon work on that worker is not polluted.
4. **Inline claimant.** A consuming thread that claims inline preserves an
   already-set first error (§3.6.2).
5. **Cleanup.** Both dealloc routes free the String with the cell: the spark
   task's RC-to-zero and the backend's `emit_rc_dec_for_ivar` →
   `cranelisp_ivar_dealloc`. Both go through `dealloc_ivar`.

Soundness rests on the structured fork-join. Every spark joins inside the
dynamic extent of any enclosing `catch-runtime-error`, so the error is observed
where sequential evaluation would observe it. The apply site needs no separate
mechanism because its barrier precedes the call. **Any path that reached the
call or body with an unforced IVar would break the ferry.** Examples are
hoisting dispatch above a force, or a tail jump past the barrier.

## 6. RC lifecycle

1. The thunk is created at `rc = 1`. `ivar_create` stores it, and the cell
   (`rc = 1`) takes over that reference.
2. `ivar_spark` raises the cell to `rc = 2`.
3. Exactly one thread claims the thunk and runs it. The result (`rc = 1` if
   heap) goes to `value`. The claimant then runs the thunk's drop glue and
   releases the thunk. The thunk pointer is never read after the claim.
4. The consumer forces the IVar. It receives `value` without an RC change, and
   `value` becomes the binding's or argument's ordinary owned temporary.
5. The consumer's release and the spark task's release, plus any
   dependent-capture releases (§4.5), each decrement the cell. The last one
   frees it and its ferried error.

## 8. Observational equivalence and evaluation order

Sparking is observationally equivalent to sequential left-to-right evaluation,
which is what `spec/12-runtime.md` §12.4.3 requires:

- **Pure values.** Independent pure sub-expressions have no observable
  evaluation order.
- **First-error-wins.** The barrier forces in source or argument order, and the
  ferry (§5) re-raises at the join. The first sub-expression's error surfaces,
  and an enclosing `catch-runtime-error` observes it in both modes.
- **Non-termination.** A diverging spark hangs its barrier force exactly where
  sequential evaluation would hang.

The spec states left-to-right as the observable order (§12.4.1) and grants the
permission for both `let` bindings and application arguments (§12.4.3). The
permission is unobservable, so a fully sequential build also conforms. Detached
strands and cancelled effects are outside this guarantee (§12.4.3).

## 9. Evidence

The observations below hold these invariants. The traceability band itself is
`qa`'s (`tests/plan/`).

| Invariant | Held by |
|---|---|
| Admission (§2.1–§2.2, §2.5.2, §2.6, §2.7, §2.8.2) | `control_flow/sparkability_tests.rs`; `utilization.rs` unit tests |
| Positional binders (§2.1, §4.2) | `tests/same_form_rebinding.rs`; `sparkability_tests.rs` positional matrix |
| Gate shape (§3.6.2) | `compiler/apply/spark_gate_codegen_tests.rs` |
| Budget, depth, backoff, inline ferry (§2.8.4, §3.6.1, §3.6.2) | `cranelisp-intrinsics/src/ivar/tests.rs` (`spark_budget_*`, `mdynamic_*`, `hier_decline_*`, `ivar_force_backoff_*`, `ivar_inline_claim_dual_panic_first_error_wins`) |
| Equivalence, opt-out, apply-site ferry (§5, §8) | `tests/spec_12_runtime.rs` (lenient and `apply_arg_*` rows) |
| Dependent sparks (§4.5, §4.5.1) | `tests/concurrency_spark.rs` (`dependent_spark_*`) |
| Performance lanes (§2.8, §3.6.3) | `tests/perf/s104_utilization.py`; `tests/plan/s104-utilization-measurement.md` |

Parallel wall-clock is not a suite gate. The floor witnesses in the suite cover
alloc/RC-light work only (§3.6.3 scope).
