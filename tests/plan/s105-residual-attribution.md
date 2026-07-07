# S105 residual-attribution measurement plan (preparatory measurement-fidelity phase)

**Author:** `/qa` · **Date:** 2026-07-07 (Phase-3 design) ·
**Status:** DESIGN — Phase-3 deliverable. Specifies the upgraded instrument, the
decomposition discipline, the two new fixtures, and the decision gate for
attributing the **post-increment-II F3/F4 parallel residual** (~2.6× — F4-hard
~2.3s vs 0.88s serial) **by mechanism** before any lever is built. This is a
PLANNING document; the harness upgrade + fixtures are Phase-5 work.

**Governing authority / inputs consumed (where they disagree, the first governs):**
- `sprints/SPRINT.md` (S105) — the preparatory phase, the fidelity-additions
  table, the fixture additions, the decision gate, the build-phase lever table,
  the four Phase-2 arch revisions.
- `design/arch/effect-concurrency.md` **§3.1.6** (R1–R5, binding) — the
  attribution/decomposition model this plan encodes: the 2×2 factorial + `I`;
  the unidentifiable-interior-split ruling; the coarse-vs-fine oracle
  granularity; the escape→stack 0525 gate-5 parallel caveat; Principle-8
  cleanliness + the `STACK_SLOT_HITS` backend-side-read caveat. Plus §3.1–§3.1.5
  (the axes, the S104 outcome, the F4-at-D3 trade).
- `tests/plan/s104-utilization-measurement.md` — the F1–F6 instrument this plan
  UPGRADES: the core-count-controlled harness (`tests/perf/s104_utilization.py`),
  the single-shot spot harness (`tests/perf/s104_spot.py`), the `[SPARK_STATS]` /
  `[SPARK_SITE_STATS]` counters, and the measurement doctrine (§0, §8.7).
- `design/arch/ownership-inference.md` §2.2 (escape edges), §2.3 (confinement,
  op-wise), §3.5 (R2 wrapper), §3.6 (conditional `MutBorrowed` ABI ruling).
- `design/backend/ownership-codegen.md` §4 (as-built escape→stack:
  `emit_stack_alloc`, `IMMORTAL_RC` sentinel, `STACK_SLOT_HITS`, the five
  eligibility gates incl. gate 5 / `in_spark_thunk`, the h2-RED counter-surface
  seam), §5 (non-atomic RC re-gate, `RcAtomicity`, the `[RC_STATS]`
  `rc_nonatomic`/`rc_atomic` split).

**Load-bearing framing (why this phase exists).** S104's close *asserts* the F3/F4
residual is "the alloc/RC-contention class," but that attribution **predates
re-measuring the residual after increment I (borrow, S102) + increment II (reuse,
S103) landed** — and the RC term it names is exactly what those increments cured
(rc_inc → 0.019% of baseline). The dominant residual term is therefore
**unprofiled**, and the four candidate cures point at four different build levers.
Per the user's own doctrine (profiled attribution over asserted mechanism), S105
**measures before it builds**. This is a *decomposition* problem, not a
wall-precision problem: it wants **finer instruments** (attribution counters,
oracle-differentials, HW counters), NOT more reps.

---

## §0. Measurement doctrine — carried from S104, non-negotiable

Every doctrine lesson S104 hardened (`memory/feedback_measure_orders_of_magnitude_not_precision`,
`s104-utilization-measurement.md` §8.7) is a **harness requirement here**, encoded
so a run that violates it is INVALID, not silently reported:

1. **Wall is taken with ALL counters OFF.** `CRANELISP_RC_STATS`, `CRANELISP_SPARK_STATS`,
   `CRANELISP_OWNERSHIP_TRACE`, `CRANELISP_CODEGEN_TRACE` — every stats/trace gate — is
   **unset** for any graded wall. The stats atomics (RC tally, spawn/peak high-water) perturb
   the wall; a graded wall never carries stats. The harness asserts the env is clean before a
   timed region and marks any wall taken with a counter set as `[INVALID: stats-on]`.
2. **Counts come from a SEPARATE run.** Spawn/peak/alloc/RC counters and walls are collected
   on **distinct invocations** of the same `(fixture, config)` cell — never the same process.
   The attribution vector is assembled by joining the two runs on the cell key.
3. **Idleness confirmed OUT-OF-BAND; no self-defeating in-harness idle-guard.** The S104
   in-harness idle poll loaded the machine and skewed the very wall it gated. `/proc/loadavg`
   (or the `/proc/stat` instantaneous busy-cores probe, `s104_utilization.py §8` refinement) is
   read in the gap **before** the timed region while nothing of ours runs, **never inside** it.
   A mechanical idle assertion that cannot confirm idle full-cores marks the rep
   **INVALID (not benign)** — the direct encoding of the S102→S103 false-green — and excludes it
   from medians with a visible `[INVALID: busy_cores=X]` line; it does not silently pass.
4. **HW counters run EXTERNALLY / separately.** `perf stat` (HITM, cross-core line transfers,
   ctx-switches) and `strace -c` (`futex`/`sched_yield` vs `brk`/`mmap` share) wrap the binary
   from outside the Python harness, on the graded cells only (expensive; not per-rep), on their
   own runs — never composed with the counter-off wall run or the counts run.
5. **Perf-lane, not nextest.** F1–F8 are perf-lane fixtures under the 30s suite-cap discipline;
   their durable `cargo nextest` record is the committed parallel≡serial exit-match (correctness),
   walls + attribution vectors are FIXME/plan-tracked (the 0534 precedent). Any *behavioural* suite
   guard that lands is failing-not-ignored (§9).
6. **Order-of-magnitude for walls; per-mechanism counts are exact.** The residual is ~2.6×; a
   lever that recovers it is an order-of-magnitude-visible wall move. Walls are single-shot /
   few-rep order-of-magnitude (the rigorous `s104_utilization.py` T-sweep matrix is retained for
   FINAL rigorous re-measure only). The **counts** (spawns, allocs, RC-atomic-share) ARE read
   exactly — they are the decomposition substrate, and a counter either moved or it did not.

---

## §1. The upgraded instrument — the per-fixture attribution vector

The Phase-5 harness upgrade extends `s104_spot.py` (single-sourced against
`s104_utilization.py` for config-env, fixture-gen, and parsers — imported, not mirrored) into
**`tests/perf/s105_attribution.py`**. Its load-bearing output is, per fixture, an **attribution
vector**:

```
attribution[fixture] = {
    scheduler-spread:        oracle-bounded net-recovery estimate + park/syscall signature,
    (a)-allocation:          oracle-bounded net-recovery estimate + alloc count/bytes/branch,
    residual-atomic-RC:      oracle-bounded net-recovery estimate + atomic-share + HITM,
    unavailable-parallelism: core-count-sweep speedup ceiling proxy,
    I (a/b coupling):        the named joint interaction term (§2),
}
```

Each entry is an **oracle-bounded estimate of what its candidate mechanism would recover** —
read from that lever's **direct oracle net-recovery column** (§2 R2), never from a reconstructed
additive breakdown.

### §1.1 The six fidelity instruments (SPRINT fidelity table, one row each)

For each instrument: the exact metric, how it is collected, and which candidate lever its reading
selects.

| # | Instrument | Exact metric | Collection | Selects lever |
|---|---|---|---|---|
| **I1** | Syscall / CPU-state profile on the *post-cure* binary | `%CPU = (user+sys)/wall` (parked-vs-busy); `futex`+`sched_yield` share vs `brk`+`mmap` share; vol/invol ctx-switches | `/usr/bin/time -f '%P'` + `os.wait4` rusage for `%CPU` (counter-off wall run); `strace -c` on the graded cell (separate run, external); ctx-sw from rusage | **scheduler-spread** (0535 depth) vs **(a)-allocator-bound** — a high `brk`/`mmap` share with low `futex` ⇒ allocator; the inverse ⇒ scheduler |
| **I2** | Allocation attribution + allocator-swap oracle | per-run **alloc count** (present: `allocs`), **alloc bytes** (NEW), **allocs/branch** (NEW — spark-site-keyed); wall under mimalloc vs system build | counts from `[RC_STATS]` `allocs=`/`deallocs=` + NEW `alloc_bytes=` + NEW per-site alloc dump (separate counts run); wall from the mimalloc-featured build (`--features thread-caching-alloc`) vs default build, both counter-off | **(a)-allocation** wall contribution → **escape∧uniqueness stack allocation** |
| **I3** | RC split — atomic vs non-atomic + Crossing/Confined + residual-atomic *site* | aggregate `rc_nonatomic`/`rc_atomic` (present, B3.3); NEW per-**site** residual-atomic dump; NEW Crossing-vs-Confined cell tally | `[RC_STATS]` `rc_nonatomic=`/`rc_atomic=` (present) + NEW `[RC_SITE_STATS]` per-site dump (analogous to `[SPARK_SITE_STATS]`), counts run; apportioned by the **FINE** probes `CRANELISP_NONATOMIC_RC` + `CRANELISP_CAPTURE_BORROW`, **NOT** by `NO_OWNERSHIP` (R3) | **residual conservatively-atomic RC, and where** → **0526/0528 confinement precision** |
| **I4** | HW cache-contention counters | `perf stat` HITM (`mem_load_..._l3_miss.remote_hitm` or host equiv); cross-core line transfers; ctx-switches | `perf stat -e` wrapping the binary externally on the graded cell, separate run | **(b)-term residual** — cache-bouncing wall invisible to wall-clock |
| **I5** | Available-parallelism ceiling | core-count sweep `T ∈ {1,2,4,6,8,10}` speedup curve; critical-path / useful-yield proxy (`(serial−Tworker)×T ÷ (spawns×overhead)`) | `RAYON_NUM_THREADS` sweep, counter-off walls; `NO_OWNERSHIP` used here as the **COARSE all-memory-off ceiling oracle** (R3), NOT a (b) toggle | **is near-serial simply correct?** → **accept-done → `--release`** |
| **I6** | Oracle-differential decomposition | the allocator-swap × ownership-off **2×2 factorial** {baseline, ¬a, ¬b, ¬a∧¬b}; the interaction term `I = baseline − ¬a − ¬b + ¬a∧¬b` reported explicitly | four counter-off wall runs per fixture (§2), `I` computed and printed as a named joint term | **the residual breakdown + per-lever recovery — the selection itself** (reads each lever's direct-oracle net-recovery column, never a reconstructed additive breakdown) |

---

## §2. The 2×2 factorial decomposition (§3.1.6-R1, binding)

The (a) allocator-lock and (b) atomic-RC terms are **coupled** — S99 proved removing the
allocator lock (a↓) lets threads run concurrently and bounce shared RC cache lines *more* (b↑),
so an (a)-only cure can be net-negative. An attribution that estimates "(a) is worth X" and "(b)
is worth Y" independently and reports `X+Y` **double-counts the coupled region and over-promises.**

**Mandatory instrument: the full 2×2 factorial, never two independent toggles.** For each fixture,
measure four counter-off wall cells and compute `I` explicitly:

| Cell | Allocator axis (a) | Ownership axis (b) | Config |
|---|---|---|---|
| **baseline** | system allocator | ownership ON | default release build, no toggles |
| **¬a** | mimalloc | ownership ON | `--features thread-caching-alloc` build, no toggles |
| **¬b** | system allocator | ownership OFF | default build, ownership-off oracle |
| **¬a∧¬b** | mimalloc | ownership OFF | mimalloc build, ownership-off oracle |

```
I = baseline − ¬a − ¬b + ¬a∧¬b        (the interaction / coupling term)
```

**Reporting rules (binding):**
- `I` is carried in the attribution vector as a **named joint term owned by neither (a) nor (b)
  alone** — never silently folded into either. A large-magnitude `I` *is* the coupling.
- **Do NOT present additive main-effects `(baseline−¬a)` and `(baseline−¬b)` without `I`.** That
  is the specific misread R1 forbids.
- The allocator axis is a **two-build** factorial (the mimalloc feature is compile-time, OFF by
  default). One consistent snapshot per build; label each cell with its build id.

**Which ownership oracle each factorial cell uses (R3, see §3):**
- The **ceiling factorial** (I6) uses `CRANELISP_NO_OWNERSHIP=1` as the (b) axis — the COARSE
  all-memory-off switch. Its `I` bounds the **combined** (a)×(memory-model) coupling, and its
  `¬b` bounds how much of the residual is memory-model-addressable **at all**.
- The **per-term apportionment factorials** (one per fine mechanism) replace the (b) axis with a
  **fine probe** (`CRANELISP_NONATOMIC_RC`, `CRANELISP_CAPTURE_BORROW`, or the stack-off oracle),
  each computing its **own** `I` against the allocator swap. Each row of the attribution table
  states which oracle it used.

---

## §3. Oracle granularity discipline (§3.1.6-R3)

The oracle set is sufficient, but its members operate at **different granularities and must not be
conflated.**

| Oracle | Granularity | What its on/off delta bounds | Toggle |
|---|---|---|---|
| `CRANELISP_NO_OWNERSHIP=1` | **COARSE — all-memory-model-off ceiling** | borrow + stack + non-atomic-RC + reuse **together** — the *combined* memory-model contribution, **NOT (b) alone** | present env; byte-identical-off (`ownership-inference.md §2`) |
| stack-off oracle | **FINE — (a)-via-stack** | net wall the stack path removes with (b) held at its coupled state | `STACK_ALLOC_ESCAPE_FACT_SOUND` const (as-built) — **needs an env gate, see §9 scope gap** |
| `CRANELISP_NONATOMIC_RC` | **FINE — (b)-via-RC** | net wall of forcing non-atomic RC (measurement ceiling for confinement precision) | present env |
| `CRANELISP_CAPTURE_BORROW` | **FINE — (b)-via-borrow** | borrow-elision on joined-spark captures | present env |
| allocator swap (mimalloc) | **FINE — (a)-allocator-lock** | net wall of removing allocator-lock contention | `--features thread-caching-alloc` build |

**Discipline (binding):** use the COARSE switch to establish the **ceiling** ("how much of the
residual is memory-model-addressable at all"), and the FINE probes to **apportion within it**.
**Treating `NO_OWNERSHIP` as a (b) toggle over-attributes (b) by the whole stack/borrow
contribution** — it is the specific error R3 forbids. Every attribution-table row names the oracle
it used; a row apportioning residual-atomic-RC that cites `NO_OWNERSHIP` instead of
`CRANELISP_NONATOMIC_RC`/`CRANELISP_CAPTURE_BORROW` is a plan violation.

---

## §4. Lever selection reads direct-oracle net-recovery (§3.1.6-R2)

The coupled (a)/(b) **interior split is unidentifiable by construction** — the interaction is a
real physical term, not a measurement artifact — **and it is decision-irrelevant.** The gate does
not need the split: it needs "which *lever* recovers the most," and **each candidate lever has its
own direct oracle measured against the coupled baseline**, so net recovery is measured directly,
never derived from an additive decomposition.

| Candidate lever | Direct oracle (net recovery vs the coupled baseline) | Selects when |
|---|---|---|
| **escape∧uniqueness stack allocation** (Q2 escape→stack ∧ Q4 uniqueness) | the stack-off oracle (`STACK_ALLOC_ESCAPE_FACT_SOUND` toggle) on the **parallel** stack-witness fixture (F8, §5.2) — measures the wall the stack path removes with (b) at its coupled state, **not** the (a)-isolated alloc-count delta | (a)-allocation dominates AND the stack path fires on the residual's paths (gate-5 caveat, §4.1) |
| **0528 uniqueness-preservation / 0526 confinement-gated projection elision** | `CRANELISP_NONATOMIC_RC` + `CRANELISP_CAPTURE_BORROW` net-recovery + the I3 residual-atomic *site* dump + I4 HITM/cross-core counters | residual-atomic-RC dominates |
| **0535 density-aware depth allowance** (+ 0536 depth-leak) | `CRANELISP_SPARK_BUDGET=0` (serial) + the depth sweep `CRANELISP_SPARK_MAX_DEPTH`; identified by the 0534 spawn-count × wall linearity (`wall ≈ serial + spawns × ~const`) — a **park/syscall signature** (99.9% scheduler: `futex`/`sched_yield`), physically orthogonal to memory traffic | scheduler-spread dominates (park signature, memory oracles flat) |
| **accept-done → pivot to `--release`** | core-count sweep 1..nproc speedup curve + critical-path/useful-yield proxy (I5); `NO_OWNERSHIP` coarse ceiling shows little memory-model-addressable residual | near-serial is *correct* (unavailable-parallelism) |

Because every lever is measured by its own toggle, the non-identifiable (a)/(b) interior split is
**decision-irrelevant** — the selection reads the direct net-recovery column.

### §4.1 The escape→stack 0525 gate-5 caveat (§3.1.6-R4, load-bearing)

The as-built escape→stack (`ownership-codegen.md §4`) **declines stack-alloc for any construction
the backend relocates into a spark thunk** (gate 5, `FnCompiler::in_spark_thunk`) — the thunk frame
pops at the join, so the slot would dangle. **Consequence:** escape∧uniqueness stack allocation
directly serves the **serial / near-serial** working-grid path but, in increment I, **does NOT fire
on the sparked parallel-search branches** — exactly the F4-hard residual. So the stack-witness
oracle **MUST measure the parallel (sparked) branch**, not only the serial in-frame case — an
(a)-isolated *serial* fixture over-states parallel recovery precisely where gate 5 blocks it. The
lever selects "build escape→stack" **only if** the residual is (a)-allocation on paths gate 5 does
*not* decline; if the (a) sits behind gate 5, selecting this lever requires the build scope to also
fund a **spark-frame-aware stack path** (a scope increase beyond the increment-I decline) — the gate
must surface that as an explicit sub-verdict (§6).

---

## §5. The two new fixtures

Both **free-standing** — zero `stdlib/` dependency, helpers defined inline via primitives/special
forms (`tests/`/`examples/` rule; root `CLAUDE.md §Stdlib separation`) — same `S99-KNOB` markers so
`scale_synth` applies, committed under `tests/fixtures/s99/`, each with a parallel≡serial exit-match
correctness guard.

### §5.1 F7 — the (a)-isolating fixture (`tests/fixtures/s99/f7_alloc.cl`)

**Purpose:** put the allocator term on its **own axis** — alloc-heavy, RC-light, scheduler-light —
so I2's allocator-swap oracle and the 2×2 (a)-axis read the allocator contribution un-confounded.

**Shape:** a coarse `reduce-tree` D&C (mirroring F1/F5/F6, so M-static admits the coarse forks) whose
leaf **allocates many short-lived heap aggregates** (fresh fixed-size ADTs/Vecs constructed and
immediately consumed) with:
- **RC-light** — leaves do not share cells across strands, do not retain, do not COW; each aggregate
  is born and dropped within the leaf so residual atomic-RC traffic is minimal (I3 confirms
  `rc_atomic` low). This isolates (a) from (b).
- **Scheduler-light** — a *shallow* coarse tree (few strands, well above spawn cost, well below the
  fib-explosion) so the spawn-count × wall linearity (scheduler term) is negligible (I1 confirms low
  `futex` share). This isolates (a) from scheduler-spread.
- Pure/commutative combine ⇒ deterministic exit-code checksum for the parallel≡serial guard.

**Required property:** under the allocator swap (mimalloc vs system), F7's wall must move
**measurably** while its `rc_atomic` and `futex` share stay flat — that separation is what makes it
the (a)-isolator. If mimalloc does *not* move F7's wall, (a)-allocator-lock is not a live term and
the stack-alloc lever's premise weakens (surfaced at the gate).

### §5.2 F8 — the parallel stack-allocation witness (`tests/fixtures/s99/f8_stack_witness.cl`)

**Purpose:** a **measurable upper bound on the stack-allocation win before building it** — AND, per
§4.1 / SPRINT Rev-3 / §3.1.6-R4, it **MUST exercise the parallel (sparked) branch**, so the harness
measures whether the (a)-allocation on the parallel path is reachable by stack-alloc or is stuck
behind the 0525 gate-5 decline.

**Shape:** a unique, non-escaping aggregate constructed and mutated **in-frame**, in TWO structurally
matched arms:
- **Serial in-frame arm** — the aggregate is built and mutated in the enclosing frame (no spark). The
  escape fact is `NoEscape`; gate 5 does not apply; `STACK_ALLOC_ESCAPE_FACT_SOUND` ON ⇒ the
  construction stack-allocates (`STACK_SLOT_HITS` moves; §8) and wall drops.
- **Parallel (sparked) arm** — the *same* construction escapes into a spark thunk (the copy-per-guess
  Sudoku pattern in miniature: a per-branch grid built/copied inside a sparked recursion). Gate 5
  **declines** stack-alloc here even with the toggle ON — the slot would dangle at the join.

**REQUIRED property (call it out):** F8 must demonstrate the **serial-vs-parallel divergence** — the
serial arm's construction stack-allocates (hits > 0), the parallel arm's does not (hits stay 0 with
the toggle ON), proving the (a)-allocation on the parallel path is behind gate 5. **A serial-only
witness over-states parallel recovery** and is INVALID for this measurement — the whole point is the
parallel branch. The harness reads `STACK_SLOT_HITS` **backend-side** (§8) separately for the two
arms and reports the divergence as the load-bearing sub-verdict feeding §6.

**Oracle read:** the stack-off toggle net-recovery on F8's **parallel** arm is the escape∧uniqueness
stack-alloc lever's direct oracle (§4). If the net recovery is ~0 on the parallel arm but large on
the serial arm, the verdict is "the residual (a) is behind gate 5 → build scope must include a
spark-frame-aware stack path, or the lever does not recover the parallel residual."

---

## §6. The decision gate

The preparatory phase's output is a **per-fixture attribution vector** (§1) plus a **per-fixture
verdict** in this exact format:

```
[S105-GATE fixture=F4-hard]
  residual (parallel wall − serial):        2.30s − 0.88s = 1.42s (~2.6×)
  attribution vector (oracle-bounded net-recovery, direct-oracle columns):
    scheduler-spread     : <Δwall> via SPARK_BUDGET/depth sweep   [park sig: futex=X%]
    (a)-allocation       : <Δwall> via mimalloc swap (2x2 ¬a)     [allocs=N bytes=B /branch=k]
    residual-atomic-RC   : <Δwall> via NONATOMIC_RC + CAPTURE_BORROW [rc_atomic=A share=s%, HITM=h]
    unavailable-parallel : speedup ceiling <c>× at T=nproc         [I5 curve]
    I (a/b coupling)     : baseline − ¬a − ¬b + ¬a∧¬b = <joint>    [NAMED, not folded]
  stack-witness (F8) sub-verdict: serial-arm hits=H_s, parallel-arm hits=H_p (gate-5)
  DOMINANT TERM: <term>  →  BUILD LEVER: <lever>   [+ gate-5 scope note if stack∧parallel-behind-gate5]
```

**Mapping attribution vector → build lever** (matching the SPRINT build-phase table):

| Dominant term | Build lever | Gate-5 rider |
|---|---|---|
| **(a)-allocation** | **Escape ∧ uniqueness stack allocation** (compose Q2 escape→stack with Q4 uniqueness into RC-free stack locals passed by reference; sidesteps the allocator — no lock to co-design; arch-separable for the statically-sized class) | **If F8 shows the (a) is on the sparked branch (H_p≈0), the build scope MUST include evidence the (a) is on gate-5-clear paths OR fund a spark-frame-aware stack path (scope increase beyond increment I).** If `MutBorrowed` callee-mutation-through-reference is needed, it is the arch-ruled conditional ABI mode (`ownership-inference.md §3.6`), whose `cranelisp-types` carrier is authored at the implementing sprint, not S105. |
| **residual conservatively-atomic RC** | **0528 uniqueness-preservation** (the live `chaining_toggle_off` RED) and/or **0526 confinement-gated projection elision** | — |
| **scheduler-spread** | **0535 density-aware depth allowance** (depth modulated by static alloc/RC density) + **0536** depth-leak enabler | — |
| **unavailable-parallelism** | **accept-done** — declare the parallel story settled for the low-exploitable class; **pivot to `--release`** (LLVM tier, where the composed end-state parallel gate lives) | — |

### §6.1 The honest accept-done branch (measurable criterion)

The gate **must** be able to conclude "little to win" without forcing a build (evidence-gated carry,
`memory/feedback_no_defer_for_size_decompose_evidence_gated`). The measurable criterion is the
**core-count-sweep speedup-ceiling proxy** (I5):

- Sweep `RAYON_NUM_THREADS ∈ {1,2,4,6,8,10}`, counter-off walls, on the residual fixture.
- Fit the speedup curve `serial / wall(T)`. The **ceiling** is `max_T speedup(T)`.
- Cross-check with the **coarse `NO_OWNERSHIP` ceiling** (I5/R3): if `NO_OWNERSHIP` (all
  memory-model off) recovers little of the residual, the residual is **not memory-model-addressable**
  — no memory lever (stack, RC) can beat it.
- **Accept-done fires when:** the speedup ceiling is ≤ ~1.2× at any `T` (near-serial is the ceiling
  the *shape* permits) AND the `NO_OWNERSHIP` coarse recovery is small — i.e. the workload has no
  exploitable parallelism to recover and no memory-model term to cure. Then near-serial **is correct**
  (S104's own north-star for the low-exploitable class), the sprint closes on the attribution + a
  scoped recommendation, and the roadmap mainline (`--release`) is the pivot.

Mechanism selection may trigger a **mid-sprint re-scope with user sign-off** — the build target is
evidence-gated, not pre-committed.

---

## §7. Doctrine guards encoded as harness requirements

Restated as explicit, checkable harness obligations (the §0 doctrine, made mechanical):

- **G-wall-off:** the harness asserts `CRANELISP_RC_STATS`, `CRANELISP_SPARK_STATS`,
  `CRANELISP_OWNERSHIP_TRACE`, `CRANELISP_CODEGEN_TRACE` are **unset** before every timed region;
  a wall with any set is dropped `[INVALID: stats-on]`.
- **G-separate-counts:** counts and walls come from **distinct process invocations**; the harness
  never parses a `[RC_STATS]`/`[SPARK_STATS]` line off a run it also timed.
- **G-idle-oob:** idleness is confirmed out-of-band (instantaneous `/proc/stat` busy-cores probe in
  the pre-rep gap), **never** by an in-harness poll inside the timed region; a rep that cannot
  confirm idle full-cores is `[INVALID: busy_cores=X]` (not benign) and excluded from medians.
- **G-hw-external:** `perf stat` / `strace -c` run **externally**, on graded cells only, on their own
  runs — never composed with the counter-off wall or the counts run.
- **G-two-build:** the allocator factorial uses two release builds (default vs
  `--features thread-caching-alloc`), each cell labelled with its build id; walls across builds are
  only compared within the factorial, never mixed into a single median.

---

## §8. The `STACK_SLOT_HITS` backend-side-read caveat (arch item 5 / §3.1.6-R5)

`STACK_SLOT_HITS` is a backend **codegen-time** counter (`heap::stack_slot_hits()`,
`ownership-codegen.md §4`). `cranelisp-intrinsics` does **not** depend on `cranelisp-backend`, so the
counter **cannot reach the intrinsics runtime print surface** (`print_rc_stats`) without a
reverse/cyclic dependency — the standing **h2-RED** coordination question. (The `[RC_STATS]` line
carries a `stack_slot=` field, but its runtime-reachability is exactly the RED seam; do not rely on
it as the source of truth for F8.)

**This plan reads `STACK_SLOT_HITS` backend-side** — via `CRANELISP_CODEGEN_TRACE` (or a backend-side
print / the `heap::stack_slot_hits()` accessor surfaced through a codegen-trace line) — as the record
of whether the stack path fired, per-arm for F8 (§5.2). **The plan MUST NOT force-resolve the
counter-surface cross-crate seam under measurement pressure** — WHERE per-mechanism counters live and
how they reach the runtime print surface is a separate design question (an `/arch` +
`cranelisp-intrinsics` touch), out of measurement scope. The measurement reads the counter where it
already lives (backend-side); it does not build the bridge.

---

## §9. Perf-lane behavioural guards + the NEW gated instrumentation list

### §9.1 Behavioural guards (failing-not-ignored, the 0534 precedent)

The graded walls/attribution vectors are perf-lane, plan-tracked, NOT `cargo nextest` guards (§0.5).
Two *behavioural* suite guards are proposed, landing **failing-not-ignored** until the selected build
lever makes them green (per `memory/feedback_failing_not_ignored.md`), decided at the gate against the
delivered counters — the exact bars are set when the lever is selected, not pre-committed:

1. **F8 parallel-arm stack-alloc guard** — an e2e that runs F8 with the stack toggle ON and asserts,
   via `CRANELISP_CODEGEN_TRACE` (backend-side), that the **serial arm stack-allocates** (`STACK_SLOT_HITS`
   moves) while the **parallel arm does not** (gate-5 decline holds). This pins the 0525 gate-5
   behaviour as a regression guard AND is the durable record of the parallel-residual reachability
   finding — RED until (if the lever is selected) a spark-frame-aware stack path lands, GREEN-and-pinning
   the decline until then. Committed with the F8 fixture regardless of lever selection (partial
   reductions join the suite for eternity, root `CLAUDE.md`).
2. **Residual-fixture spawn/attribution guard** (if the gate selects a memory lever) — an e2e asserting
   the residual fixture's dominant-term counter (`rc_atomic` share, or `allocs/branch`, or spawn count)
   moves under the built lever, failing-not-ignored until it does.

The committed **parallel≡serial exit-match** for F7 and F8 is their durable `cargo nextest` correctness
record independent of the perf verdict.

### §9.2 NEW gated instrumentation `/dev(cranelisp-backend)` must commit

Precise NEW-vs-already-present split. **Already present** (no new backend work): the aggregate
`rc_nonatomic`/`rc_atomic` RC split (B3.3, `[RC_STATS]`); per-run `allocs`/`deallocs` count
(`[RC_STATS]`); `STACK_SLOT_HITS` codegen-time counter + `heap::stack_slot_hits()` accessor; the
`STACK_ALLOC_ESCAPE_FACT_SOUND` const as the coarse-via-`NO_OWNERSHIP` stack oracle; `SPARK_STATS` /
`SPARK_SITE_STATS`; the mimalloc `thread-caching-alloc` feature; the fine probes `CRANELISP_NONATOMIC_RC`,
`CRANELISP_CAPTURE_BORROW`, `CRANELISP_NO_OWNERSHIP`, `CRANELISP_NO_LENIENT`; the depth/budget/thread knobs.

**NEW gated instrumentation (all `CRANELISP_RC_STATS`-gated, zero-cost-off, intrinsics-internal per
R5 — no `cranelisp-types` edit, no new C-ABI symbol):**

| # | NEW item | Extends | Why needed |
|---|---|---|---|
| **N1** | **Per-run alloc BYTES counter** (`alloc_bytes=` in `[RC_STATS]`) | `alloc_count`/`ALLOC_COUNT` (bytes not tracked) | I2 — alloc *volume*, not just count, to weight the (a) term |
| **N2** | **Per-site / per-branch alloc attribution** (`[ALLOC_SITE_STATS]` dump, spark-site-keyed allocs — analogous to `[SPARK_SITE_STATS]`) | none (aggregate only today) | I2 — allocs/branch, to attribute the (a) term to the *parallel* branch (the gate-5-relevant question) |
| **N3** | **Per-SITE residual-atomic-RC dump + Crossing/Confined cell tally** (`[RC_SITE_STATS]`: per-site `(site-id, atomic-count, confinement-class)`) | aggregate `rc_nonatomic`/`rc_atomic` (B3.3) | I3 — *where* the residual atomic ops are, so 0526/0528 target the right sites; apportioned by the FINE probes (R3) |
| **N4** | **A dedicated env gate for the FINE stack oracle** (e.g. `CRANELISP_NO_STACK_ALLOC=1` flipping `STACK_ALLOC_ESCAPE_FACT_SOUND` at runtime-read, sibling of `CRANELISP_NONATOMIC_RC`) | `STACK_ALLOC_ESCAPE_FACT_SOUND` const (compile-time only) | §3/§4 — the FINE stack oracle: stack off with borrow/RC/reuse still ON. Today the only OFF paths are the const (rebuild) or `NO_OWNERSHIP` (COARSE — conflates). Without N4 the stack lever's direct oracle can only be read by a two-build (const true/false) fallback (§9.3). |

**The parallel-witness fixtures (F7/F8) themselves need NO new backend work** for the stack-oracle
behaviour — the `STACK_ALLOC_ESCAPE_FACT_SOUND` toggle + gate-5 `in_spark_thunk` decline already exist;
F8 exercises them. The new backend work is the **attribution counters** (N1–N3) and the **fine-oracle
ergonomics** (N4), not the mechanism under test.

### §9.3 Scope gaps for `/sprint` to route

1. **N4 (fine stack oracle env gate) is a real gap, not optional polish.** §3.1.6-R2 names "the
   existing `STACK_ALLOC_ESCAPE_FACT_SOUND` toggle" as the stack lever's direct oracle, but as-built it
   is a **compile-time const**, and the only runtime OFF path is the **COARSE** `NO_OWNERSHIP` (which R3
   explicitly forbids using as a fine (b)/stack apportioner). Route to `/dev(cranelisp-backend)` as N4,
   OR accept the **two-build fallback** (const true vs const false release builds, analogous to the
   mimalloc two-build factorial). Recommend N4 (cleaner, one binary, matches the env-toggle doctrine);
   flag the two-build fallback as the no-new-code alternative. **`/sprint` decides N4-vs-two-build at
   the Phase-4 wave gate** — it changes whether `/dev(cranelisp-backend)` has an instrumentation commit
   or whether the harness carries a second build config.
2. **N2 (per-branch alloc attribution) may be heavier than N1/N3.** Attributing allocs to the spark
   branch that caused them needs either a spark-site-keyed alloc tally (a thread-local alloc counter
   sampled at spark boundaries) or codegen-time site tagging. If N2 proves expensive, the fallback is
   the **coarser** read: I1's `brk`/`mmap` syscall share as the (a)-on-parallel-path proxy, plus F7's
   allocator-swap delta as the (a)-magnitude bound. State to `/sprint`: N2 is desirable but the
   attribution can degrade gracefully to I1+F7 if N2 is descoped.
3. **HW HITM counter availability is host-dependent.** `perf stat` HITM events (I4) may not be exposed
   on the VM host (`perf` permissions / PMU virtualization). If unavailable, the (b)-cache-bouncing term
   falls back to the `CRANELISP_NONATOMIC_RC` net-recovery (I3) as the sole (b) witness — flag to
   `/sprint` that the I4 HW-counter row may be `UNAVAILABLE — host PMU` and the (b) attribution then
   rests on I3 alone.
4. **The h2-RED counter-surface seam is explicitly NOT resolved here** (§8) — if `/sprint` wants the
   `stack_slot`/`rc_site` counters on the *runtime* print surface (not just backend-side codegen-trace),
   that is a separate `/arch` + `cranelisp-intrinsics` design question, out of S105 measurement scope.

---

## §10. Phase-5 deliverable checklist (Phase-4 wave input)

1. **`/dev(cranelisp-backend)`** — commit the NEW gated instrumentation N1–N3 (+ N4 or the two-build
   fallback per the §9.3 wave-gate decision); all `CRANELISP_RC_STATS`-gated, zero-cost-off verified
   (byte-identical-off, the U-G6 precedent); no `cranelisp-types` edit, no new C-ABI symbol (R5).
2. **`/qa`** — `tests/perf/s105_attribution.py` (single-sourced against `s104_spot.py` /
   `s104_utilization.py`): the six fidelity instruments (§1.1), the 2×2 factorial + `I` computation
   (§2), the granularity-disciplined oracle reads (§3), the direct-oracle net-recovery lever columns
   (§4), the per-fixture attribution vector + gate verdict format (§6), the §7 doctrine guards
   encoded as INVALID-marking preconditions.
3. **`/qa`** — author F7 (`f7_alloc.cl`, §5.1) and F8 (`f8_stack_witness.cl`, §5.2), free-standing,
   with parallel≡serial exit-match guards; F8 MUST carry the serial-vs-parallel gate-5 divergence
   property.
4. **`/qa`** — the two failing-not-ignored behavioural guards (§9.1), bars set at the gate.
5. **Gate output** — the per-fixture attribution vector + verdict + build-lever selection, as the
   input to the evidence-gated build-phase re-scope (user sign-off).

## Next skills

- `/dev(cranelisp-backend)` — commit N1–N4 gated instrumentation (§9.2), the Phase-5 backend input.
- `/sprint` — route the four §9.3 scope gaps (N4-vs-two-build at the wave gate; N2 graceful-degrade;
  I4 HW-counter availability; the h2-RED seam deferral); organize Phase-4 waves; the gate verdict is
  the build-phase selection point.
- `/design` (`lenient-eval.md` / the selected lever's doc) — consumes the attribution gate to design
  the selected build lever, if the gate selects a build (not accept-done).
- `/arch` (`effect-concurrency.md §3.1.6`) — consulted if the gate surfaces a stack∧parallel-behind-gate5
  scope increase (spark-frame-aware stack path) or the `MutBorrowed` ABI half.
