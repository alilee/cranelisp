---
number: 0534
target: /design
filed_by: /qa
filed_at: 2026-07-06
sprint_filed: 103
refers_to: tests/plan/s100-ownership-verification.md §2.3 (II-G3), design/arch/effect-concurrency.md §3.1, design/backend/lenient-eval.md §2.7 (B4 density-admission axis), design/backend/ownership-codegen.md §13.4
status: open
diagnosed_by: /dev(backend)
diagnosed_at: 2026-07-06
sprint_diagnosed: 103
retarget_note: >
  Re-pointed /backend → /design after the /dev(backend) ablation below REFUTED
  the filed hypothesis. This is NOT a bounded backend density-gate tune: the fix
  is a contention-model design question (lenient-eval.md §2.7 + effect-concurrency.md
  §3.1) with a real cross-fixture trade (f3), not a B4 recalibration.
---

## /dev(backend) PROFILING ATTRIBUTION — S103, 2026-07-06 (the ~110s PROVEN; it is NOT "just contention")

**Mandate (user):** the prior diagnosis asserted "§3.1 contention" without proving
where the wall goes. Spending ~110s CPU on work that completes in ~1s serially is
~100×; "contention" is implausible at that magnitude. This section PROVES it with
CPU%, a syscall profile, spark-instance counts, and a spawn-count sweep.

**Verdict:** the ~110s is **rayon task-scheduling overhead (futex wake/park +
sched_yield) paid ~13 µs per spark × 9.45 M ultra-fine score-0 sparks whose real
body is ~20 ns.** It is **NOT** allocator-lock contention, **NOT** atomic-RC
cache-bouncing, **NOT** redundant recomputation, and **NOT** a livelock. The user's
instinct is correct — it is not cache contention; it is **over-sparking of
near-trivial work overwhelming the work-stealing scheduler**, which is a more
addressable class than the §3.1 "allocator lock + atomic RC" story implies. The
§3.1 attribution is **partially misattributed**: on F4-hard the dominant term is
scheduler churn, not the substrate.

### Evidence (release binary, 10 cores, idle, `f4_hard.cl` HARD puzzle, exit 154)

**(A) CPU utilization discriminates spin vs park — it is PARKING.**
| Config | wall | %CPU | vol ctx-sw | invol ctx-sw |
|---|---|---|---|---|
| serial (`NO_LENIENT`) | 0.94s | 93% | 14 | 9 |
| OFF (`NO_OWNERSHIP`) | 17.5s | 415% | 1,023,376 | 1,936,765 |
| ON default (B4 active) | 116s | **240%** | **6,313,619** | 7,513,735 |

240% CPU on 10 cores ⇒ ~7.6 cores idle at any instant ⇒ **not a pegged spin-loop**
(that would be ~1000%). 6.3 M voluntary ctx-switches ⇒ threads repeatedly parking.
`/proc/<tid>/wchan` sampling: nearly every worker in **`futex_do_wait`**.

**(B) syscall profile (strace -c, F4-hard ON default) — 99.9% is scheduler, ~0% allocator.**
```
 50.53%  sched_yield   365,181 calls    ← rayon workers idle-searching for work
 49.33%  futex         165,837 calls (52,766 EAGAIN)  ← park/unpark
  0.07%  brk           0.04% madvise  0.00% mmap        ← allocator barely hits kernel
```
The allocator-lock hypothesis is REFUTED at the syscall layer (glibc malloc stays
in userspace here). Atomic-RC bouncing would show as stalled-BUSY cycles (high CPU),
not futex parking — also refuted by (A)'s low CPU.

**(C) spark-instance + ivar_force outcome counts (instrumented, `CRANELISP_SPARK_STATS=1`).**
ON default:
```
spawns=9,448,736   force_claim_wins=9,448,736 (= spawns ⇒ each spark evaluated EXACTLY once)
force_fastpath_resolved=9,198,663   force_spin_waits=250,073 (2.6%)   force_spin_iters=896,424,350
```
- `claim_wins == spawns` ⇒ **no redundant recomputation** (corroborated: `rc_inc`
  is IDENTICAL serial-vs-ON at 31.7 M — the logical work is unchanged; only 19 M
  extra allocs appear = the IVar/thunk spark machinery).
- The IVar spin-loop (`ivar.rs` line ~441, `std::hint::spin_loop()`, no park) burns
  ~896 M iters ⇒ **~4–9s of the 116s** — real but secondary, NOT the dominant term.

**(D) DECISIVE: wall is ~linear in spawn count (spawn-count sweep, all ownership-ON).**
| knob | wall | spawns | µs/spark |
|---|---|---|---|
| `SPARK_BUDGET=0` (no sparks) | **1.18s** | 0 | — |
| `SPARK_BUDGET=4` | **3.34s** | 65,026 | ~33 |
| `SATURATION_GATE=1` (cap=10) | **72.8s** | 3,040,754 | ~24 |
| default (cap=40) | **116s** | 9,448,736 | ~13 |

wall ≈ serial + spawns × (per-spark scheduling cost). Halving spawns ~halves the wall.
This is the signature of **fixed per-task scheduling overhead × task count**, not of
data-dependent cache contention. 13–33 µs/spark = futex-wakeup scale; the actual body
(a couple of `vec-get`s) is tens of ns ⇒ **~600× per-task overhead ratio**.

**Root mechanism (the "why 100×"):** F4's admitted sparks are the **104 score-0 fine
accessor/projection pairs** in the per-cell hot loops (e.g. `(let [c1 (cell-at g1 i)
c2 (cell-at g2 i)] …)`), and the consumer forces each IVar almost immediately (a
near-immediate data dependency). So there is **almost no exploitable parallelism**,
yet every spark still pays a full spawn→wake-a-worker→run-20ns→park round-trip that a
serial inline call would skip entirely. 9.45 M × ~13 µs ≈ 123s. The create-gate
(`SPARK_BUDGET`) bounds *concurrent* in-flight sparks (memory = O(cap)) but does
**not** bound the *total spawn rate* — the steady-state firehose each pays full
scheduling cost.

**(E) delta profile — why B4-declines-coarse (default) is WORSE than admit-all (MAX=0).**
| Config | wall (uninstr.) | %CPU | spawns |
|---|---|---|---|
| ON default (B4 declines coarse) | 116s | **240%** (parked) | 9.45 M |
| ON `SPARK_DENSITY_MAX=0` (admit coarse) | ~24s | **565%** (busy) | 15.3 M |

MAX=0 admits MORE sparks (15.3 M) yet is 5× FASTER, because the coarse `solve-range`
D&C sparks give genuine coarse-grain parallelism that keeps workers BUSY (565% CPU)
and hides the per-spark wake/park latency. Default declines the coarse sparks →
outer search runs serial → the fine sparks **strand** with no coarse structure to
ride on → workers park constantly (240%) → each fine spark is a naked wake/park
round-trip. This PROVES the FIXME §(2) "declined-coarse + admitted-fine = worst"
claim with the CPU%/spawn-count mechanism, not just wall.

### Disposition — real, attributable, addressable pre-Phase-H (NOT a fundamental floor)
- The dominant cost is **scheduler overhead from over-sparking near-trivial work**,
  not the §3.1 substrate (allocator lock / atomic RC). This is the FIXME's own
  recommended-shape **option (b): a spark-overhead axis** — decline sparks whose body
  cost-to-run < cost-to-spawn (the score-0 accessor/projection pairs) — or **option
  (1a) hierarchical decline** (a declined coarse subtree suppresses nested fine
  sparks, removing the strand). Either kills F4's over-spark firehose.
- **NOT landed this sprint** and NOT a blind backend tune: the "no local signal
  distinguishes F4's harmful score-0 fine sparks from F1's beneficial `fib`/`reduce-tree`
  score-0 compute sparks" problem (FIXME §"Why it is NOT a bounded fix") is real — a
  static cost model / body-size heuristic is a **/design** deliverable (lenient-eval.md
  §2.7). `SPARK_BUDGET=4` reaches 3.34s here but would starve F1's genuine parallelism,
  so a global budget cut is the wrong lever. The correct lever is a per-spark
  cost/overhead axis distinct from the density (contention) axis.
- **§3.1 correction for /arch:** on F4-hard the measured dominant term is rayon
  scheduling churn (sched_yield 50% + futex 49% of syscall time), NOT the allocator
  lock + atomic RC named in §3.1. The floor-violation is real but its *cause* here is
  spawn-overhead-per-trivial-task; Phase-H thread-local RC / reuse would NOT fix it
  (it is not RC-bound). The in-track cure is the spark-overhead gate, available now.

**Reproduction:** `ivar.rs` carries uncommitted gated instrumentation (env
`CRANELISP_SPARK_STATS=1`, zero-cost when off) that prints the `[SPARK_STATS]` line
above; counters: `SPARK_SPAWNS` in `ivar_spark`, `FORCE_*` in `ivar_force`. Sweep via
`CRANELISP_SPARK_BUDGET={0,4}` / `CRANELISP_SATURATION_GATE=1` / `CRANELISP_SPARK_DENSITY_MAX=0`
over `f4_hard.cl` (HARD puzzle substituted per `tests/perf/s99_measure.py`).

---

## /dev(backend) ABLATION DIAGNOSIS — S103, 2026-07-06 (hypothesis REFUTED; carry to S104 as a design item)

**Summary:** The filed "increment-II density reduction defeats B4's decline →
over-sparking" hypothesis is **REFUTED by ablation**. The regression is **not
increment-II-introduced** and **not a spark-count/density-gate problem**. It is a
**pre-existing, core-count-scaled contention pathology** that the S102 increment-I
acceptance measured under **reduced effective parallelism** (residual load ≈ 2-6
cores) and so recorded as benign; the S103 FIXME measured the *same code* at truly
idle full 10 cores. No bounded backend change reaches II-G3. Evidence below.

### Measurement basis
Release binary; this machine `nproc=10`; F4-hard fixture (`f4_sudoku.cl` +
`s99_measure.py` HARD puzzle, unchanged since `c09c0a2`); `--run`; wall via
`date +%s.%N`; every config exits **154** (identical grid checksum ⇒ correctness /
differential-oracle intact throughout). Serial (`CRANELISP_NO_LENIENT=1`) = **0.90s**,
so the II-G3 bar (≤2× serial) = **1.80s**.

### (1) The density distribution is IDENTICAL at increment-I and increment-II HEAD — B4 still declines solve-range
`CRANELISP_SPARK_DENSITY_TRACE=1` over F4-hard, both at S102 close (`25ffe12`, increment-I)
and at S103 HEAD (increment-II):

```
104 [SPARK_DENSITY] engaged=true score=Some(0) max=1 decision=admit
  4 [SPARK_DENSITY] engaged=true score=Some(2) max=1 decision=decline
  6 [SPARK_DENSITY] engaged=true score=Some(4) max=1 decision=decline
```

Byte-identical between the two commits. F4's speculative `(solve-range …)` sparks
**still score 2/4 and are still DECLINED** — increment II did **not** reduce their
density. The hypothesis's core claim (ON admits substantially MORE dense sparks than
before) is false. What is admitted is **104 score-0 fine-grained sparks** (cheap
projection/accessor pairs — e.g. `(let [c1 (cell-at g1 i) c2 (cell-at g2 i)] …)` in
per-cell hot loops), unchanged across the two commits.

### (2) Core ablation at full 10 cores (HEAD) — B4 is NET-HARMFUL, the opposite of intent
| Config | F4-hard N-worker wall | vs serial |
|---|---|---|
| serial (`CRANELISP_NO_LENIENT=1`, no sparks) | **0.90s** | 1× |
| OFF (`CRANELISP_NO_OWNERSHIP=1`, axis inert ⇒ admits ALL incl. solve-range) | **15.9s** | 17.7× |
| ON `CRANELISP_SPARK_DENSITY_MAX=0` (B4 disabled, admits ALL) | **24.0s** | 26.7× |
| ON default `MAX=1` (**B4 declines** the 10 dense solve-range sparks) | **111.8 / 114.9s** | ~124× |

**Disabling B4 (`MAX=0`) takes ON from ~112s → 24s** — B4's coarse-spark decline,
while leaving the 104 fine score-0 sparks admitted, produces the **worst** sparking
outcome (declined-coarse + admitted-fine = fine sparks strand on a serialized outer
search tree, thrashing the pool with no coarse-parallel amortization). At full cores
B4 moves F4-hard **~4.6× AWAY from serial**, not toward it. B4's S102 "moves toward
serial" acceptance was an artifact of reduced-core measurement (see (4)).

### (3) NOT increment-II-introduced — increment-I HEAD reproduces it identically
At `25ffe12` (S102 close, increment-I), same F4-hard, 10 cores:
`ON default = 107.4s`, `ON MAX=0 = 12.2s`, `OFF = 3.5s`. Same 104/4/6 distribution,
same ~110s catastrophe at full cores. The S103 change-sets (R5 flattening, reuse
tokens, Wave-3c) did **not** cause this.

### (4) The "8-33s → 108s regression" is core-count/effective-parallelism sensitivity, not a code change
Thread-count sweep of ON-default (B4 active), HEAD:
```
RAYON_NUM_THREADS=2 → 7.6s    =4 → 16.5s    =6 → 27.8s    =10(default) → ~112s
```
Super-linear in worker count (contention thrash). The S102 increment-I record
`on=[8.38, 9.81, 14.54, 30.28, 33.0]` (`s100-ownership-verification.md §2.2.1`) lands
exactly in the **2-6-thread** band — i.e. that "settled load" run had only ~2-6
*effective* cores (residual background load), while the S103 FIXME's tight
`108.4/108.8/111.3` was at truly-idle full 10 cores. **Same pathology, different
effective parallelism** — a textbook `memory/feedback_verify_fix_not_symptom_absence.md`
measurement-condition false read, not a regression.

### Why it is NOT a bounded fix (evidence the goal is unreachable this way)
- **No spark-admission tuning reaches II-G3 (≤2× serial = 1.80s).** Best parallel =
  OFF 15.9s (17.7×); best ownership-on = MAX=0 24s (26.7×). Only **not sparking**
  (serial 0.90s) meets the bar. F4-hard's parallelism is pure overhead at this scale.
- **The density axis is working as designed** — it correctly scores solve-range dense
  (2/4). The harmful sparks are the 104 **score-0** cheap accessor pairs, which the
  density axis (a *contention* proxy: alloc/RC) cannot see as costly and the compute
  axis (§2.2) admits because they are non-cheap-named `Apply`s. There is **no local
  signal** distinguishing F4's net-harmful fine speculative-search sparks from F1's
  beneficial `fib`/`reduce-tree` compute sparks — both score 0. Declining all score-0
  would kill the F1 compute win (I-G4). Tuning to F4 alone is exactly the
  "tune to one fixture blindly" the S103 mandate forbids, and trades against the
  S102-accepted f3 benefit (−82% N-worker).
- This is the **`effect-concurrency.md §3.1` contention class** (Sudoku copy-per-guess
  violating the never-slower-than-sequential floor), whose structural cure is **Phase H**
  (thread-local RC / escape→stack-region / reuse) and whose acceptance is the **III-G2
  composed-end-state gate**, *not* an increment-II deliverable. `ownership-inference.md`
  §7 already stages F4-at-north-star as III-G2.

### Recommended S104 shape (design-level, not a /dev-backend tune)
1. **/design (lenient-eval.md §2.7):** the real defect surfaced here is that **B4's
   coarse-spark decline is incoherent when the declined subtree still sparks fine
   candidates** — declining the outer while admitting the inner is strictly worse than
   either extreme (112s vs 24s admit-all vs 0.90s spark-nothing). Options to weigh:
   (a) hierarchical decline — a declined (serialized) subtree suppresses sparks nested
   within it; (b) a **spark-overhead axis** distinct from the density (contention) axis
   — decline near-trivial accessor/projection sparks (cost-to-spark > cost-to-run) that
   currently pass the §2.2 compute gate; (c) recognise F4-class speculative search as a
   workload where *any* sparking is net-negative pre-Phase-H and gate it off.
2. **/arch (effect-concurrency.md §3.1):** confirm the floor-scope ruling covers this
   (it does — contention-bounded, not unconditional) and that the contention-aware gate
   was only ever "static alloc/RC-density axis *first*", with F4-hard's residual
   overhead an explicit Phase-H item. B4 being *net-harmful* at full cores (not just
   neutral) is new information for the gate model.
3. **/qa:** re-scope II-G3 — either (a) grade it against the Phase-H composed end-state
   (III-G2) per §7 staging and mark the increment-II cell a documented `§5-limit` like
   II-G4, or (b) keep it as a standing perf-regression tripwire but at a realistic bar
   (≤ OFF, i.e. "ownership-on must not be worse than the conservative lowering" —
   currently VIOLATED: ON 112s vs OFF 15.9s, which *is* the real actionable signal here).
4. **Interim actionable (bounded, if the user/design wants a stopgap this sprint):**
   B4 as-built is net-harmful on F4-hard at full cores. A minimal, reversible stopgap is
   to make the density decline **not fire when it would strand nested fine sparks**
   (option 1a) OR to gate B4's decline behind measured net-benefit; but both carry the
   f3 trade and belong to /design's call, not a blind backend edit. **Not landed this
   sprint** pending that decision.

---

# F4-hard N-worker regresses ~20× under analysis-ON (II-G3 fails 121×; increment-II-introduced)

## Issue

The increment-II acceptance gate **II-G3** (F4-hard median N-worker wall ≤ 2×
serial) FAILS catastrophically, and the cause is an increment-II-introduced
parallel regression that the analysis-off differential isolates cleanly.

**Measured (release binary, S103 HEAD, settled load, 2026-07-06):**

| Config | analysis-ON | analysis-OFF (`CRANELISP_NO_OWNERSHIP=1`) |
|---|---|---|
| F4-hard **serial** | 0.91s | ~0.90s |
| F4-hard **N-worker** | **108.8s** (median; 3 reps 108.4 / 108.8 / 111.3 — tight) | **5.46s** (median; 5.1 / 5.46 / 17.18) |

- II-G3: N-worker/serial = 108.8 / 0.91 = **121×** (bar ≤ 2×).
- The ON-vs-OFF differential on the SAME binary, same fixture, settled load,
  is the attribution: **analysis-ON N-worker is ~20× slower than analysis-OFF**
  (108.8s vs 5.46s), while serial is unaffected (ON ≈ OFF ≈ 0.9s). The
  slowdown is parallel-only and analysis-on-only.
- **This is a regression vs increment I.** At S102 close the I-G4/F4 report
  recorded F4-hard N-worker ON=[8.38, 9.81, 14.54, 30.28, 33.0] vs
  OFF=[6.6, 12.16, 15.15, 15.6, 19.18] — ON ≈ OFF, max ~33s
  (`tests/plan/s100-ownership-verification.md` §2.2.1). Increment II opened a
  ~20× ON-vs-OFF divergence that did not exist at increment I.
- `f4_sudoku.cl` is unchanged since S102 Wave A (`c09c0a2`); the regression is
  purely compiler-side (the S103 Wave 3a/3b/3c increment-II change-sets:
  R5 value-flattening + reuse tokens + Wave-3c function registration).

## Probable mechanism

This is the known contention class (`effect-concurrency.md` §3.1 — the
Sudoku copy-per-guess workload that violates the "never slower than sequential"
floor for allocation-/RC-heavy parallel work; former FIXME 0459). The
hypothesis, for `/backend` to confirm:

- Increment II's borrow-elision + reuse-token check-elision **reduce the
  measured static allocation/RC density** that the **B4 density-admission axis**
  (`ownership-codegen.md` §13.4) reads to decide whether to spark a
  heap-returning branch or decline it to the serial arm.
- With the density reduced, B4 now **under-declines** on F4-hard: sparks it
  previously kept serial (the whole point of B4 — kill the over-sparking
  contention) are now admitted, re-exposing the parallel over-sparking
  thrashing. Net: 108s of redundant speculative work where OFF stays at 5.5s.

I.e. increment II's density reduction defeats B4's density-based decline on this
workload. The fix likely lives in the B4 admission heuristic (it must not
mistake ownership-reduced RC/alloc density for genuine low contention), not in
R5 or the reuse tokens themselves (both are correct — output is byte-identical
under the differential oracle; only the wall regressed).

## Repro

```
SYS_BIN=target/release/cranelisp python3 tests/perf/ig_gates.py --gates iig3 --reps 7
```
or the direct ON-vs-OFF differential in `tests/perf/s99_measure.py` (F4-hard,
Nworker, toggle both polarities). The `ig_gates.py` II-G runner (S103 /qa
extension) grades II-G3 and prints the distribution.

## Operational implication / Context

- Perf-lane finding (not canonical nextest); this FIXME is the durable
  record + trigger (per `memory/feedback_no_fixme_with_failing_test.md` — a
  perf-gate result is a script, not a suite guard, so the FIXME is the
  appropriate durable trigger).
- II-G1's parallel-must-pay half is a **separate, benign** non-pass (R5 made
  F2v serial 0.12s and F2v N-worker 10× faster than OFF; parallelism can't beat
  the now-super-cheap serial — not a regression). II-G4's wall is the documented
  §5-limit-1 F2-not-cured case (F2 N-worker ON ≈ OFF; system-allocator
  contention, cured only at the III-G composed end-state). **0534 is the one
  gate failure that is a genuine regression**, not a designed limit.
- Does not block correctness: the differential oracle is byte-identical-off
  throughout; the suite is green modulo the intentional 0528 RED.
