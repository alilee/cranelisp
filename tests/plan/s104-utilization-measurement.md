# S104 utilization-thesis measurement plan + acceptance instrument (Stage 0)

**Author:** `/qa` · **Date:** 2026-07-06 (design); 2026-07-07 (Wave-0 RESULTS, §8) ·
**Status:** EXECUTED — Wave 0 (Stage 0) complete. The measurement instrument
(`tests/perf/s104_utilization.py`), the config matrix, the discrimination experiment, and
the fixture-adequacy verdict are DELIVERED; the Stage 2–4 acceptance gates (§6) stand for
Waves 1–3. **§8 carries the Wave-0 results: discrimination = PASS (Wave-0→1 gate
cleared); anchor reproduced; F1 inadequate → F5 authored.** The instrumentation commit was
`/dev(cranelisp-backend)` `4924c26`; the harness + F5 + these results are `/qa`.

**Governing authority / inputs consumed:**
- `sprints/SPRINT.md` (S104) — the thesis, the two mechanisms (M-static / M-dynamic), the
  five stages, the north star, the Phase-2 arch review. Where this plan and the SPRINT
  scope disagree, SPRINT governs.
- `design/arch/fixmes/0534-f4-hard-parallel-regression-analysis-on.md` — **the
  measurement basis.** Its methodology (CPU% via `/usr/bin/time`; syscall profile via
  `strace -c`; spawn-count sweep via `CRANELISP_SPARK_BUDGET` /
  `CRANELISP_SATURATION_GATE` / `CRANELISP_SPARK_DENSITY_MAX`; `/proc/<tid>/wchan`
  sampling; `CRANELISP_SPARK_STATS=1` counters) is reused verbatim and extended.
- `tests/plan/s100-ownership-verification.md` §0 (metrics discipline), §2.3/§2.3.1 (the
  II-G3 gate + its S103 re-scope record — this plan is the utilization-model re-scope it
  called for).
- `tests/plan/s99-measurement.md` (F1–F4 shapes, baselines, the median-of-N + F4-as-
  distribution discipline).
- `tests/perf/{s99_measure.py,ig_gates.py,l_d1_turn_latency.py}` — the perf lane this
  harness extends (READ for design; not run this phase).

**Load-bearing framing (the S102→S103 false-green).** S102 accepted F4 as benign because
it was measured under **2–6 effective cores** (residual background load); the truly-idle
10-core run showed **112s** (`s100` §2.3.1 (4)). Every number in S104 is invalid unless
it is taken at a **known, controlled effective core count on a confirmed-idle machine**,
and F4 is **always** read as a *distribution* across a *thread-count sweep*, never a
single point. This plan encodes that as an explicit harness precondition (§1), not a
convention to remember.

---

## §0. Metrics discipline (carried from S99/S100, extended for utilization)

1. **Release-tier binary only** for graded numbers (`target/release/cranelisp`); a debug
   binary is protocol/plumbing check only (the `ig_gates.py` WARNING precedent).
2. **Wall / user / sys collected separately.** Wall via `time.perf_counter`; user+sys via
   `os.wait4` rusage (the `hires_*` helpers already in `s99_measure.py`). `%CPU` derived
   as `(user+sys)/wall` — this is the parked-vs-busy discriminant (0534 (A): 240% parked
   vs 565% busy on 10 cores). `/usr/bin/time -f '%P'` is the cross-check.
3. **Counter-gated attribution** (`memory/feedback_verify_fix_not_symptom_absence.md`): no
   wall delta is attributed to a mechanism unless the mechanism's own `CRANELISP_SPARK_STATS`
   counter moved. This is the whole reason Stage 0 must commit the instrumentation *first*.
4. **Distribution, not point, for the search fixtures.** F4 (and any speculative-search
   fixture) reports the full 11-rep ordered distribution (min / median / max) at **every**
   thread count, never a single median pair (the 0534 "23×" / S102 "8–33s" cherry-pick
   lesson).
5. **Perf lanes are scripts, not canonical nextest** (30s suite cap discipline). Results
   are FIXME-tracked (the 0534 precedent), not `cargo nextest` guards. Any suite guard
   that does land is failing-not-ignored per `memory/feedback_failing_not_ignored.md`.

---

## §1. The core-count-controlled harness (the load-bearing requirement)

A new perf-lane driver — proposed `tests/perf/s104_utilization.py`, importing
`s99_measure` for `gen_fixtures` / `hires_*` / `env_for` machinery, extended with a
`CRANELISP_SPARK_STATS` parser and a per-config env-matrix builder. The controls below are
**preconditions of a valid run**, encoded as guards that *invalidate* a run rather than
silently reporting it.

### 1.1 Effective-core-count control

- **Pin `RAYON_NUM_THREADS`** for every measured config to a swept value; never rely on
  the ambient default. The **thread-count sweep is a first-class axis**, not a single
  point: `T ∈ {1, 2, 4, 6, 8, 10}` (extend to `nproc` on the host — this machine
  `nproc=10`). The report is the full `T`-sweep; the headline core-utilization claims are
  read at **`T = nproc` (full idle cores)**, which is exactly the condition S102 failed to
  measure.
- **Assert the machine is idle before each rep** (the false-green guard, made mechanical):
  read the 1-minute load average (`os.getloadavg()[0]`) immediately before each rep;
  **require `load1 < IDLE_MAX`** where `IDLE_MAX = 0.5 × (nproc − RAYON_NUM_THREADS)`
  headroom — concretely, before a `T = nproc` rep the machine's *non-benchmark* load must
  be `< ~0.5`. A rep that cannot confirm idle full-cores is marked **INVALID (not
  benign)** and excluded from medians with a visible `[INVALID: load1=X]` line; if > 20%
  of a cell's reps are INVALID the whole cell is reported `UNMEASURED — machine not idle`,
  never as a pass. (This is the direct encoding of `s100` §2.3.1 (4): "benign under 2–6
  effective cores" must be structurally impossible to record as a result.)
- **Warm-exclude the first rep** (JIT/page-cache) and take **median-of-11** with
  min/med/max for F4-class; median-of-7 for the fixed-work F1–F3.

### 1.2 What a "point" in the sweep is

Each measured cell is the tuple `(fixture, mechanism-config, T, spawn-config)` →
`{wall[min/med/max], user, sys, %CPU, spawns, serial-continues, peak-concurrent-executing,
vol-ctx-sw, invol-ctx-sw}`. `%CPU` and `spawns` travel with **every** wall number so a
"kept cores busy but slower" cell (F4 admit-all: 565% CPU, 24s) is never confused with a
"genuinely faster" cell (F1: cores busy AND wall → serial/T).

### 1.3 Spawn-count sweep (retained from 0534 (D))

Orthogonal to the mechanism-config axis, a spawn-count sweep via
`CRANELISP_SPARK_BUDGET ∈ {0, 4, …}` / `CRANELISP_SATURATION_GATE=1` /
`CRANELISP_SPARK_DENSITY_MAX` is retained as the **mechanism-independent** demonstration
that `wall ≈ serial + spawns × per-spark-overhead` (0534's decisive linear signature). It
is the falsifier: if a mechanism cuts wall *without* cutting spawns, the linear model is
wrong and attribution halts for re-diagnosis.

---

## §2. The independent-attribution config matrix (the Stages 2–4 acceptance instrument)

The mechanism-config axis. Six primary configs × the `T`-sweep (§1.1), each a differential
against `OFF`:

| Config | Env | What it isolates |
|---|---|---|
| **OFF (no spark)** | `CRANELISP_NO_LENIENT=1` | the serial floor — the correctness oracle and the wall the win must approach |
| **current-syntactic** | default *as-shipped today* (`is_worth_sparking` = non-cheap Apply) | the falsified model — the 9.45M-spawn baseline to beat |
| **M-static-only** | M-static ON, M-dynamic OFF, **`SPARK_DENSITY_MAX=0`** | quality axis alone: coarse selected, fine rejected — but no ~2/core cap |
| **M-dynamic-only** | M-static OFF, M-dynamic ON, **`SPARK_DENSITY_MAX=0`** | utilization axis alone: ~2/core cap on the *syntactic* spark set |
| **M-static + M-dynamic** | both ON, **`SPARK_DENSITY_MAX=0`** | the composed target (the north-star config) |
| **admit-all** | `SPARK_DENSITY_MAX=0`, no static/dynamic filter (`NO_OWNERSHIP`-style) | the "cores busy on coarse D&C" ceiling (0534: F4 24s @ 565%) |

**Pin `SPARK_DENSITY_MAX=0` (B4 OFF) on the M-static / M-dynamic / both rows** so B4's
measured net-harm (0534 (E): 112s default-on vs 24s off) does not contaminate the
attribution. **Carry B4-on as its own diagnostic row** — `M-static+M-dynamic +
SPARK_DENSITY_MAX=1` — reported, not part of the primary attribution, so the B4
default-flip decision (SPRINT Stage-0 named change-set: `SPARK_DENSITY_MAX_DEFAULT` 1→0)
has a measured basis on the utilization configs rather than the incoherent
decline-coarse-while-admitting-fine state.

**Attribution reads (the arch interaction ruling).** The matrix must let three things be
read *separately*:
- **M-static's effect** = `M-static-only` − `current-syntactic` (spawn quality: does the
  fine-accessor spawn count collapse while the coarse D&C survives?).
- **M-dynamic's effect** = `M-dynamic-only` − `current-syntactic` (spawn quantity: does
  the total spawn count collapse toward O(cores)?).
- **The interaction** = `both` − (the larger single-mechanism effect). **Per the arch
  ruling, F4's collapse is an M-static × M-dynamic *interaction*, not a sum** — a
  divide-and-conquer recursion is non-tail-recursive at every level, so M-static re-selects
  spark sites all the way down (the `fib`-explosion), and the ~2/core collapse is
  *entirely* M-dynamic's. **Design the reporting so a weak/partial single-mechanism row is
  NOT read as failure.** The runner prints, for every fixture, an explicit
  `interaction = both − max(static-only, dynamic-only)` line and a
  `SINGLE-MECHANISM ROWS ARE DIAGNOSTIC, NOT PASS/FAIL — grade the composed row` banner on
  F4. Only the `both` (north-star) config is graded against the north-star bars (§6);
  the single-mechanism rows are attribution diagnostics.

---

## §3. Metrics (precise definitions + counter sources)

The instrumentation is the S103-uncommitted gated block in `ivar.rs`
(`CRANELISP_SPARK_STATS=1`, zero-cost when off). **Stage-0 implementation obligation
(`/dev(cranelisp-backend)`): commit + gate it, and emit the counters below.** This plan
specifies WHAT it must emit; the emission is the backend's.

| Metric | Definition | Counter(s) |
|---|---|---|
| **spawn-vs-serial(continue-inline) ratio** | spawned sparks ÷ (spawned + inlined-because-busy-or-declined). The core "did we stop over-sparking" number. | `SPARK_SPAWNS` (in `ivar_spark`) + a **new `SPARK_SERIAL_CONTINUES`** counter (inline-instead-of-spawn outcomes — M-dynamic's busy-pool inlines + M-static's rejects). Ratio → 0 as sparking becomes selective. |
| **peak concurrent busy-cores / executing-sparks** | max simultaneously-*executing* (not merely reserved) sparks — the utilization signal. Distinct from `IN_FLIGHT_SPARKS` (reserved/created). | **new `SPARK_PEAK_EXECUTING`** high-water (inc on spark body entry, dec on exit, sample max). Cross-checked against `%CPU` (§0.2). This is the number that must move parked→busy. |
| **useful-spark yield** | realized parallel work ÷ (spawns × per-spark-overhead) — the "was the spawning worth it" ratio. Realized parallel work ≈ (serial-wall − Nworker-wall) × T; per-spark-overhead ≈ the 0534-measured ~13µs (or re-measured per host via the `SPARK_BUDGET` sweep slope). Yield ≫ 1 = spawns paid off; yield ≪ 1 = the F4 firehose. | derived: `SPARK_SPAWNS` × overhead-slope vs the wall differential. |
| **per-spark-site recursion-SCC + tail classification** | for each *static* spark site: `{callee-in-recursive-SCC?, apply-in-tail-position?}` → the M-static admit/decline verdict, plus the *dynamic* spawn count attributable to that site. The discrimination-experiment substrate (§4). | **new `SPARK_SITE_STATS`**: per-site `(site-id, scc?, tail?, spawns, serial-continues)` dumped at exit. Site-id = the codegen spark-site identity (callee FQ name + call-site span suffices). |

**Force-path outcomes** (0534 (C)) retained: `force_claim_wins`, `force_fastpath_resolved`,
`force_spin_waits`, `force_spin_iters` — the "no redundant recompute" + spin-secondary-cost
witnesses. **Syscall/park evidence** retained as the parked-vs-busy corroborant: `strace -c`
(sched_yield + futex share) and `/proc/<tid>/wchan` sampling (0534 (A)/(B)), run on the
graded F4 cells only (expensive; not per-rep).

---

## §4. The discrimination experiment (the pivotal Stage-0 deliverable)

**Question:** does the M-static signal (`callee ∈ recursive-SCC ∧ apply ∉ tail-position`)
**cleanly separate** F1's beneficial sparks from F4's harmful accessor pairs **while
keeping F4's coarse `solve-range` D&C admitted**?

### 4.1 Procedure

1. **Enumerate every current spark site** in F1–F4 (+ any new fixture, §5). Source of
   truth = the `SPARK_SITE_STATS` per-site dump (§3) under `current-syntactic` at
   `T=nproc`, cross-checked by hand against the fixtures (done below — this plan already
   carries the manual classification so Stage-0 measurement *confirms* rather than
   discovers).
2. **Classify each site** `{recursive-SCC?, tail?}` from the Decision-21 `callees` call
   graph + `in_tail_position` (the exact inputs M-static will use — the classification is
   computed by the same machinery, so the experiment tests the *real* signal, not a proxy).
3. **Cross the classification with the harmful/beneficial label** derived from the spawn-
   count × wall-vs-serial data: a site is *beneficial* if the sparks it produces are on the
   coarse structure that keeps cores busy toward a wall win; *harmful* if its sparks are
   sub-overhead fine work that only adds spawn cost (0534: the 104 score-0 accessor pairs).

### 4.2 The manual classification this experiment must confirm

| Fixture | Site | callee | SCC? | tail? | M-static | Label | Must confirm |
|---|---|---|---|---|---|---|---|
| F1 | `reduce-tree` args to `add-i64` (l.54–55) | `reduce-tree` | **yes** | **no** (args of `add-i64`) | **ADMIT** | beneficial (coarse compute D&C) | KEEP |
| F1 | `read-work` inner `cell-value`/`vec-get` (l.44) | flat accessors | no | — | decline | cheap read | reject |
| F2 | `reduce-tree` args (l.59–60) | `reduce-tree` | yes | no | ADMIT | coarse (contention leaves — M-dynamic caps) | KEEP + cap |
| F3 | `search-tree` args to `first-success` (l.68–69) | `search-tree` | yes | no | ADMIT | coarse search overlap | KEEP |
| F4 | `solve-range` args to `first-success` (l.182–184) | `solve-range` | **yes** | **no** | **ADMIT** | coarse speculative D&C (the ~10 that keep cores busy) | **KEEP** |
| F4 | `grids-differ-helper` `(let [c1 (cell-at g1 i) c2 (cell-at g2 i)]…)` (l.131) | `cell-at` | **no** | — | **decline** | **harmful (the 104 fine accessor pairs)** | **REJECT** |
| F4 | other `cell-at`/`vec-get`/`cell-value` accessor applies | flat accessors | no | — | decline | harmful fine | reject |

### 4.3 Pass / fail (quantitative)

**"Cleanly separates" =** at `T=nproc`, under `M-static-only` (B4 off):
- **(a) Coarse survives:** the recursive-SCC∧non-tail sites (`reduce-tree`, `search-tree`,
  `solve-range`) remain **ADMIT** — their per-site spawn count is > 0 and the coarse D&C
  structure is intact (F4's `solve-range` still sparks; not driven to zero).
- **(b) Fine rejected:** the flat non-recursive accessor sites (`cell-at`,
  `cell-value`, inner `vec-get`) go to **serial-continue** — their per-site spawn count is
  **0**. Concretely, F4's spawn count drops by **≥ the 104 fine-accessor share** (0534:
  the 104 score-0 admits become the dominant spawn term once the coarse tree is capped) —
  the separation is clean iff **zero** fine-accessor-site spawns survive while **every**
  coarse-D&C-site remains non-zero.
- **(c) Structural, not tuned:** the same rule produces (a)+(b) on F1, F2, F3, F4 with **no
  fixture-specific threshold** — the verdict is a function of `{SCC?, tail?}` only. If any
  fixture needs a per-fixture constant to land on the right side, the signal is not clean.

**If it does NOT separate cleanly** (e.g. a flat accessor lands in a recursive SCC via an
incidental cycle, or a coarse D&C recursion reads as tail-position under some lowering),
the experiment **feeds back to Stage 1 before build**: `/design` must refine the M-static
signal (candidate refinements to weigh: SCC-size floor; exclude sites whose callee body is
below a static instruction-count/allocation floor; distinguish "recursive via the sparked
arg" from "recursive elsewhere"). The Stage-0 deliverable is the *verdict + the failing
sites*, so Stage 1 designs against evidence, not assertion. **This experiment is the gate
on proceeding to Stage 2.**

### 4.4 What it deliberately does NOT prove

Per the arch correction: M-static keeping `solve-range` admitted at *every* level means
F4's spawn count under `M-static-only` is still **large** (the fib-explosion), NOT ~10.
That is expected and **not a discrimination failure** — the ~2/core collapse is
M-dynamic's job (§2, §6). The experiment proves *quality* (fine rejected, coarse kept),
not *quantity*.

---

## §5. Fixture-adequacy check

The thesis is validatable/falsifiable only if F1–F4 represents **both** regimes:

- **Regime A — genuine coarse-parallel win available** (cores-busy SHOULD beat serial).
  **Candidate: F1** (compute-bound D&C over pure reads; north star asserts near-linear
  speedup) and **F3** (best-case equal-cost overlap upside).
- **Regime B — no exploitable parallelism** (near-serial is correct). **Covered: F4-hard**
  — admit-all's 24s is 26× serial's 0.9s; even coarse sparks are speculative-search
  overhead. The *correct* answer here is near-serial.
- **Contention regime (context): F2** (copy-per-guess; serial cheap, parallel loses) —
  present, useful as the "utilization can't rescue a memory-bound copy loop" witness.

### 5.1 The distinguisher the harness must encode

"Kept cores busy but did useless speculative work" (F4-hard admit-all: **565% CPU, 24s** —
busy yet 26× serial) vs "genuinely faster" (F1: busy AND wall → serial/T). The harness
distinguishes them with **two numbers together**, never `%CPU` alone:
- `%CPU` high (cores busy) is **necessary but not sufficient**.
- **`wall ≤ serial`** (approaching `serial/T` for Regime A; approaching `serial` for
  Regime B) is the **only** acceptance of "genuinely faster." A cell that is CPU-busy yet
  `wall > serial` is **speculative waste** and is reported as such
  (`BUSY-BUT-SLOWER — speculative waste`), even at 565% CPU. `useful-spark yield` (§3) is
  the scalar form: yield ≫ 1 = genuine; yield ≪ 1 = waste.

### 5.2 Adequacy verdict — MEASUREMENT-GATED, with a named fallback

**Regime B is adequately represented (F4-hard).** No new fixture needed there. F4-hard's
correct answer is explicitly *near-serial*; the north star's F4 bar (§6) is written to
accept near-serial as the win, not to demand a speedup.

**Regime A adequacy is provisional pending a Stage-0 measurement.** F1/F2/F3 are
deliberately *light* (serial ~0.7s at `LEAVES=8192, COPIES=256`), and F1's leaves are
trivial reads. The risk: under the ~2/core coarse-strand model, F1's coarse strands may
each carry too little sequential work for the win to be *decisively* measurable above
startup/JIT noise (S102 already had to move F1 timing to report-only <60ms). The Stage-0
gate:
- **IF** at `T=nproc`, `M-static+M-dynamic` on F1 shows `wall` decisively below serial
  (target `wall ≤ serial / (0.5 × nproc)` — i.e. at least half-linear speedup) with the
  `%CPU`/`peak-executing` corroborant and yield ≫ 1 → **Regime A is represented; no new
  fixture.**
- **ELSE** (F1's win is marginal / unresolvable / startup-dominated) → **add the minimal
  fixture F5** (below). The point of F5 is to make "populate the cores, each runs an
  efficient sequential path, and beat serial by ~`T`" *unambiguous and decoupled from
  allocation/contention* — the pure positive witness the thesis needs to be *validated*
  (F4 can only falsify the over-sparking side).

### 5.3 F5 — the minimal new fixture (author only if §5.2 ELSE fires)

**Shape:** a `T`-way (i.e. ~`nproc`-leaf) divide-and-conquer over **heavy pure compute**,
no heap allocation in the leaf, no shared-cell contention — the clean Regime-A witness.
Minimal design: `(reduce-tree lo hi)` identical D&C to F1, but the leaf is a **naive
recursive `fib(N)`** (or an integer-only numeric kernel) sized so each of ~`nproc` coarse
strands runs **tens of ms** of sequential compute — well above the ~13µs spawn cost, so a
handful of coarse strands each running forward serially must beat serial by ≈`T`.
Free-standing (bare primitives, no stdlib), same `S99-KNOB` markers so `scale_synth`
applies, committed under `tests/fixtures/s99/f5_compute.cl` with a parallel≡serial
correctness guard (pure branches → identical result). This fixture is the decisive
*positive* half: F5 must show the coarse-strand win, F4-hard must show the near-serial
correctness. Together they let the thesis be both validated (F5/F1) and falsified (F4).

---

## §6. Acceptance gates for Stages 2–4 (north-star bars, gradeable) + II-G3 re-scope

All gates read the `M-static+M-dynamic` (north-star) config, B4 off, at `T=nproc`, on a
confirmed-idle machine (§1), F4 as a distribution.

| Gate | Fixture / lane | Bar |
|---|---|---|
| **U-G1 (cores parked→busy)** | F4-hard, `both` vs `current-syntactic` | **spawns collapse from ~9.45M to O(cores)** (≈ `k × nproc`, `k`≈2 — the ~2/core target); `%CPU` moves off 240%-parked toward busy; **`wall ≤ admit-all's ~24s`, ideally → serial (~0.9s)**. Read as the 11-rep distribution; median AND max below `current-syntactic`. |
| **U-G2 (coarse win survives)** | F1 (and F5 if added), `both` vs OFF | F1 keeps its coarse-parallel speedup — `reduce-tree` stays admitted (per-site spawns > 0), `wall` decisively < serial (§5.2 target), yield ≫ 1. **M-static must not reject the beneficial D&C**; **M-dynamic must still populate the cores** (`peak-executing` ≈ `nproc`, not 1). |
| **U-G3 (no parallel regression)** | F2 / F3, `both` N-worker vs `current-syntactic`-toggle-off | N-worker `wall ≤ toggle-off` (≤ +5%, the `s100` I-G4 non-regression bar carried forward). Utilization must not *worsen* the contention/overlap fixtures. |
| **U-G4 (structural, not fixture-tuned)** | the §4 discrimination verdict | the separation holds by `{SCC?, tail?}` alone across F1–F5 — no per-fixture constant (§4.3 (c)). A gate that passes only with an F4-specific threshold FAILS this bar even if U-G1 passes. |
| **U-G5 (interaction honesty)** | the single-mechanism matrix rows | `M-static-only` and `M-dynamic-only` are **reported, not graded pass/fail** (arch ruling: expect partial/inconclusive). The *graded* claim is the `both` row. A weak single-mechanism row is recorded, never read as failure (§2). |
| **U-G6 (spark-stats zero-cost-off)** | the instrumentation | `CRANELISP_SPARK_STATS` unset → byte-identical codegen/wall vs pre-instrumentation HEAD (the differential twin; the 0534 "zero-cost when off" claim, verified). |

**Stage mapping:** Stage 2 (M-static built) grades U-G4 + the discrimination confirmation +
the `M-static-only` attribution row. Stage 3 (M-dynamic built) grades the `M-dynamic-only`
row + `peak-executing` movement. Stage 4 (combine/tune) grades U-G1/U-G2/U-G3 on `both`,
tunes the utilization cap to the ~2/core target *by measurement* (sweep the cap, pick the
knee where U-G1 spawns hit O(cores) without U-G2 losing the F1/F5 win), and records
acceptance.

### 6.1 II-G3 re-scope against the utilization model

`s100-ownership-verification.md` §2.3 (II-G3) was re-scoped **off increment II** at S103
close (0534 proved F4's wall is scheduler churn, not a write-path/RC cost) and pointed at
the composed **III-G2** end-state. **S104 re-homes it onto the utilization axis:** II-G3's
target (F4 parallel ≤ 2× serial) is now **U-G1's** responsibility — it is a *scheduler-
admission* property cured by the utilization gate (M-static × M-dynamic), NOT by Phase-H
RC/reuse and NOT by increment II. The re-scope:
- **The interim tripwire `s100` §2.3.1 recorded — "ownership-ON must not be worse than
  ownership-OFF" (currently VIOLATED: 112s vs 15.9s at full cores) — is the U-G1 floor
  S104 must clear first** (≤ OFF), with the full bar being `wall ≤ admit-all ~24s → serial`.
- **The failing number stays VISIBLE.** Per `feedback_verify_fix_not_symptom_absence.md`
  (the S102 I-G5 / S103 II-G3 precedent): the re-scope is a scope correction backed by the
  0534 profile, not a bar relaxation. The 121×-at-10-cores measurement remains on the page
  in `s100` §2.3.1; S104's U-G1 is where it is *graded and cured*.
- **Cross-ref, not relocation:** the substance lives here (§6 / U-G1); `s100` §2.3 gets a
  one-line pointer to this plan so the II-G3 trail is followable. The III-G2 composed-end-
  state gate is unchanged and still owns the *Phase-H contention* term (0534's (b) axis) —
  U-G1 owns the *utilization* term. Two axes, cured in two places (the arch §3.1.4 roadmap
  course-correction).

**Failing-not-ignored discipline for any suite guard.** Per §0.5, U-G1–U-G6 are perf-lane
script results (FIXME-tracked, the 0534 precedent), not `cargo nextest` guards. If any
utilization property warrants a *behavioural* suite guard (e.g. an e2e that asserts a
known coarse-D&C fixture spawns O(cores) not millions — expressible via
`CRANELISP_SPARK_STATS` + a subprocess assert), it lands failing-not-ignored until the
mechanism makes it green, per `memory/feedback_failing_not_ignored.md`. That decision is
made at Stage 4 against the delivered counters, not pre-committed here.

---

## §7. Stage-0 deliverable checklist (Phase-4 wave input)

1. **`/dev(cranelisp-backend)`** — commit + gate the `ivar.rs` `CRANELISP_SPARK_STATS`
   block; emit the §3 counters (add `SPARK_SERIAL_CONTINUES`, `SPARK_PEAK_EXECUTING`,
   `SPARK_SITE_STATS`); verify zero-cost-off (U-G6). Flip `SPARK_DENSITY_MAX_DEFAULT` 1→0
   (the SPRINT named change-set) — with the §2 B4-on/off diagnostic rows as its measured
   basis.
2. **`/qa`** — `tests/perf/s104_utilization.py`: the core-count-controlled driver (§1,
   idle-guard + `T`-sweep + INVALID-not-benign marking), the §2 config matrix with the
   independent-attribution reads + interaction banner, the §3 metric parsers, the §4
   discrimination-experiment procedure (auto-classify from `SPARK_SITE_STATS`, emit the
   §4.3 pass/fail verdict), the §5.1 busy-but-slower distinguisher, and the §6 U-G gate
   grader. Extends `s99_measure`/`ig_gates` idioms; standalone, outside `cargo nextest`.
3. **`/qa` + measurement** — run the §5.2 Regime-A adequacy gate on F1; author F5
   (`tests/fixtures/s99/f5_compute.cl`) **only if** F1's win is not decisively measurable.
4. **Discrimination verdict** — produce the §4 verdict (clean-separation pass/fail + the
   failing sites if any) as the **gate on Stage 1→2**; if not clean, hand the failing sites
   to `/design` for signal refinement before build.

---

## §8. Stage-0 RESULTS (Wave 0, 2026-07-07) — `/qa`

Harness: `tests/perf/s104_utilization.py` (built to §1–§4). Release binary
`target/release/cranelisp` at instrumentation commit `4924c26`. `nproc=10`,
confirmed idle (instantaneous `busy_cores≈0.00` at each cell).

**Idle-guard as-built refinement (recorded per §1.1).** §1.1 mandates
`os.getloadavg()[0] < IDLE_MAX`. The 1-minute load average is polluted by the
harness's OWN prior reps (self-heat decays over ~1 min), which would spuriously
UNMEASURE the harness's valid back-to-back heavy cells (e.g. after an 11-rep
F4-hard cell, `load1` sits at 3–6 for a minute). The *intent* — "no
NON-benchmark work is stealing cores" — is served more faithfully by an
**instantaneous non-idle-cores probe** from `/proc/stat`, sampled in the gap
before each rep while nothing of ours is running (self-heat, whose process has
exited, does not count). The harness gates on that `busy_cores` against
`idle_max = max(0.5, 0.5·(nproc−T))` and still records `load1` on every rep.
This **strengthens** the S102→S103 false-green guard — it still rejects the
"residual 4–8 background cores" case (that load does not decay) — without
false-UNMEASURING valid cells. **Vindicated in this run:** the adequacy pass
started at `load1=5.83` (decaying self-heat from the prior baseline run) yet
`busy_cores=0.00`; had the guard used `load1`, the entire pass would have been
wrongly UNMEASURED. Across the whole baseline+adequacy run exactly **1 rep**
(f1 admit-all T=10) was flagged INVALID — the guard is neither too loose nor too
tight.

### §8.1 The discrimination experiment — VERDICT: **PASS** (Wave-0→1 gate CLEARED)

`[SPARK_SITE_STATS]` over F1/F2/F3/F4/F5 at `T=nproc`, `current-syntactic`
(as-shipped default). Every current spark site classified `{scc?, tail?}` by the
committed M-static classifier (`utilization.rs`, measure-only in Wave 0):

| Fixture | coarse-D&C site(s) `admit=true` | flat accessor sites `admit=false` |
|---|---|---|
| f1_machinery | `reduce-tree` (×2, scc=T tail=F) | `copies`, `rem-i64` |
| f2_contention | `reduce-tree` (×2) | `copies`, `rem-i64` |
| f3_inverted_search | `search-tree` (×2) | `copies`, `rem-i64` |
| f4_easy | `solve-range` (×2) | `cell-at`, `box-of`, `col-of`, `row-of`, `div-i64`, `mul-i64` |
| f5_compute | `reduce-tree` (×2), `fib` (×2) | — |

- **(a) Coarse survives:** every recursive-non-tail D&C site
  (`reduce-tree`/`search-tree`/`solve-range`/`fib`) classifies `scc=true`,
  `admit=true`, `emits>0`. ✓
- **(b) Fine rejected:** every flat non-recursive accessor site (`cell-at`,
  `vec-get`, `rem-i64`, `mid-of`, `copies`, `box-of`/`col-of`/`row-of`,
  arithmetic prims) classifies `scc=false`, `admit=false`. ✓
- **(c) Structural, not fixture-tuned:** `admit == (scc && !tail)` holds at
  EVERY site — the verdict is a pure function of `{scc,tail}`, no per-fixture
  constant. Each callee's `scc` value is identical across every fixture it
  appears in (`reduce-tree` always T; `cell-at`/`rem-i64`/`copies` always F). ✓

**Correction recorded (so the next reader does not re-derive it):** an initial
expectation that `solve` (F4) is a coarse spark site was WRONG. `solve` is
mutually recursive with `solve-range` (both are in the recursive SCC) but is
NEVER a sparkable apply-arg — in `solve-range`'s leaf branch `(solve (set-cell
…))` it is the sole call, not one of two independent args. F4's only coarse
spark site is `solve-range`, and it admits while the 104-class fine `cell-at`
pairs decline — exactly the discrimination the syntactic filter could not make.

**No misclassified sites. Wave 1 (build M-static) may proceed** on the signal as
specified — no `/design` signal-refinement is required (§4.3 holds by
`{scc,tail}` alone).

### §8.2 Baseline matrix — the anchor + config differentiation

**F4-hard (the confounded reference; `f4-reps=3` on the expensive cells):**

| Config | T | wall min/med/max (s) | %CPU | spawns | peak-exec | note |
|---|---|---|---|---|---|---|
| serial (`NO_LENIENT`) | 1 | 0.898 / **0.914** / 0.940 | 94 | — | — | the serial floor / correctness oracle |
| off (`NO_OWNERSHIP`) | 10 | 2.879 / 6.151 / 10.681 | 541 (busy) | 16.77 M | 15 | admits all incl. coarse |
| **admit-all = new default** | 10 | 5.162 / **10.537** / 19.189 | 480 (busy) | 12.81 M | 15 | post-flip shipped default |
| **current-b4on = OLD default** | 2 | 8.343 / 8.478 / 8.705 | 180 | 6.71 M | 4 | 0534 (4): 7.6s |
| current-b4on | 4 | 17.30 / 17.43 / 22.87 | 201 | 7.03 M | 5 | 0534: 16.5s |
| current-b4on | 6 | 28.22 / 28.29 / 28.60 | 205 | 5.01 M | 5 | 0534: 27.8s |
| **current-b4on** | **10** | 115.4 / **118.3** / 122.1 | **241 (parked)** | **9.84 M** | 5 | **0534 headline: ~112s/240%/9.45M** |

- **ANCHOR REPRODUCED.** `current-b4on` (= the pre-flip default) at T=10 =
  **118.3s median @ 241% CPU parked, 9.84 M spawns** — matches 0534's
  ~112s/240%/9.45 M within measurement noise. The super-linear T-ramp
  (8.5 → 17.4 → 28.3 → 118 s) reproduces 0534 (D)/(4) (7.6/16.5/27.8/112).
- **The parked↔busy discriminant is sharp:** `current-b4on` sits at 241% CPU
  (~7.6 cores idle, futex-parked) while `admit-all`/`off` sit at 480–541% CPU
  (cores busy). `%CPU` + `spawns` travel with every wall exactly as §1.2 requires.
- **B4 default-flip has a measured basis (SPRINT named change-set):** the shipped
  default F4-hard T=10 moves from **118.3s parked (old, B4-on)** to **~10–15s busy
  (new, B4-off)** — an ~8–11× improvement from the flip alone, on the incoherent
  decline-coarse-while-admitting-fine state 0534 identified. The flip is
  net-beneficial at full cores as predicted.
- **`current-syntactic` (default) ≡ `admit-all` confirmed** (coordinator ask):
  post-flip `SPARK_DENSITY_MAX` unset is env-identical to `=0`. Measured directly
  — F4-hard `current-syntactic` T=10 (3 reps) = walls **8.67 / 15.48 / 21.48 s**,
  ~380–506% CPU (busy), **7.90 M spawns, peak=15** — the same busy regime as
  `admit-all` (5.2/10.5/19.2 s, 12.8 M, peak=15), not the parked `current-b4on`.
  The wide spread is F4-hard's inherent speculative-search variance (read as a
  distribution per §0.4), not a config difference.
- **Residual over-sparking is what the mechanisms must close.** Even at the new
  busy default, F4-hard still emits **~8–13 M spawns** (~9–17× serial's 0.9 s):
  B4-off unparks the cores but does NOT cut the spawn *count* — that is M-static
  (reject the fine `cell-at`/accessor firehose) × M-dynamic (~2/core cap on the
  coarse `solve-range` set) at Stages 2–4 (U-G1: spawns → O(cores), wall → serial).
- **Self-call classifier caveat (from `/review` of `4924c26`) — not tripped
  here.** The module-blind self-call check false-admits only when a *cross-module*
  callee shares the enclosing fn's bare name. All F1–F5 fixtures are single-file
  (single module); every coarse site is genuine same-module self-recursion
  (`reduce-tree`/`search-tree`/`solve-range`/`fib`), so no fixture site trips it.
  Queued for the Wave-1 `/dev` M-static build regardless.
- All configs exit **154** (identical grid checksum) — parallel≡serial
  correctness intact throughout.

**Light fixtures (T=10 highlights; full sweep in the harness output):**

| Fixture | serial (s) | best parallel (s) | T=10 parallel (s) | regime |
|---|---|---|---|---|
| f1_machinery | 0.033 | 0.027 (T=8) | 0.037 | too light — startup/noise-dominated |
| f2_contention | 0.53 | 0.53 (T=1) | 5.4 | contention (copy-per-guess) — parallel loses, super-linear in T |
| f3_inverted_search | 0.55 | 0.55 (T=1) | 5.3 | contention/overlap — copy work dominates; parallel loses |
| f5_compute | 0.71 | 0.59 (T=4) | 0.75 | pure compute — marginal 1.2×; over-sparks (see §8.3) |

`current-syntactic` (default) and `admit-all` are env-identical post-flip
(`SPARK_DENSITY_MAX` unset ≡ `=0`); their light-fixture numbers coincide as
expected — confirming the flip's equivalence.

### §8.3 Fixture adequacy (§5) — F1 INADEQUATE → F5 authored

- **F1 is INADEQUATE for Regime A.** F1 serial = 0.033 s; the §5.2 decisive-win
  target `wall ≤ serial/(0.5·nproc)` = **0.0067 s**; F1's best parallel = 0.027 s
  ≫ target. At 33 ms the coarse-parallel win is startup/JIT/noise-dominated and
  not decisively measurable (the S102 <60 ms report-only problem). ⇒ **F5
  authored** per §5.3: `tests/fixtures/s99/f5_compute.cl` — a ~nproc-leaf D&C over
  heavy pure `fib` compute, no alloc, no contention, free-standing.
- **F5 is the prepared positive witness; correctness holds.** F5 serial =
  **0.712 s** (substantial — a T× speedup would be decisively measurable);
  parallel≡serial exit = **73 in every config** (the committed correctness guard).
- **F5 shows NO decisive win under any Wave-0 config — as predicted, and it
  validates the thesis structure.** Best F5 parallel ≈ 0.59 s (T=4) vs 0.71 s
  serial = a marginal 1.2×, at 440–800% CPU busy but over-sparking (spawns
  0.28–1.4 M — the `fib`-explosion). Even the saturation-gate proto-cap
  (`SATURATION_GATE=1`) is busy-but-slower (0.63 s @ 677%). **Neither a syntactic
  filter nor a proto-cap alone dispatches the ~nproc coarse strands while letting
  the `fib` internals run forward serially** — precisely why M-static (spark
  coarse not fine) × M-dynamic (~2/core cap) must both be built. F5's decisive
  coarse-parallel win is the **U-G2 grade at Stage 4** under the `both` config,
  not a Wave-0 deliverable.

### §8.4 Wave-1 recommendation

**PROCEED to Wave 1 (build M-static).** The Stage-0→1 gate (§4 discrimination) is
CLEARED: the M-static `{scc,tail}` signal cleanly separates every beneficial
coarse-D&C site from every harmful fine accessor site, structurally, across
F1–F5 with no per-fixture constant. The measurement instrument is in place and
reproduces the 0534 anchor; the config matrix attributes parked-vs-busy by
`%CPU`+`spawns`; the acceptance bars (U-G1..U-G6) have their baselines. F5 is the
prepared Regime-A positive witness for the Stage-4 `both` grade. No `/design`
signal-refinement is owed before build.

## Next skills

- `/design` (`lenient-eval.md`) — Stage 1 design convergence, consuming the §4
  discrimination verdict + the §5 adequacy verdict; refines the M-static signal if §4.3
  does not separate cleanly.
- `/dev(cranelisp-backend)` — Stage-0 instrumentation commit (§7.1), then Stage 2/3 builds
  measured against this matrix.
- `/arch` (`effect-concurrency.md §3.1`) — the utilization-axis floor re-ruling + the B4
  net-harm record (Stage 1), which this plan's U-G1 grades against.
- `/sprint` — organize Phase-4 waves from §7; the §4 verdict is the Stage-1→2 gate.
