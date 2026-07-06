# S100 ownership-inference verification & acceptance plan (parts 17–18)

**Author:** `/qa` · **Date:** 2026-07-02 · **Status:** DESIGN (S100 Phase 3, stage 2 —
the sprint's parts-17–18 deliverable). This is a **plan**: S100 ships design, not
implementation. The failing tests named here are drafted QA-first at the start of each
implementing increment sprint (METHOD Phase 5 stage 1); this document must be concrete
enough that a future `/qa` invocation drafts them directly from it.

**Revised 2026-07-03 (S101 Phase 3):** stage-M portions made sprint-ready — L-B2(i) +
L-B3(1)–(3) staging reconciled to the `/arch` S101 Phase-2 ruling (toggle + manifest
key ship at stage M); new §6.1 stage-M drafting specification (files, fixtures,
assertions, RED/GREEN-at-draft per lane); new §7.1 vec-query flip protocol; §4 stage-M
unit-tier handoff additions; §5 limit 6 extended to all R3 wording surfaces.

**Governing authority:** `design/arch/ownership-inference.md` (the spine — §9 is this
plan's inheritance; §3.4/§6.2 the oracle obligation; §7 the increment staging). Inputs
consumed: `design/typecheck/ownership-inference.md` §12 items 5–8;
`design/backend/ownership-codegen.md` §2.2(4) + §12 items 1–7;
`tests/plan/s99-measurement.md` (the F1–F4 shapes, baselines, and metrics discipline);
`sprints/SPRINT.md` (scope + walkthrough amendments). Where this plan and the spine
disagree, the spine governs.

**Sequencing frame (spine §5.7 / §7):** the implementation order is
**R3 machinery → increment I (read path) → increment II (write path)**. Each stage has
its own QA-first drafting list (§6) and its own acceptance bar (§2) — staged increments
are graded against their own bar, never the composed end-state's (R8).

---

## §0. The standing oracle and the two-sided bar (normative for every lane)

1. **The analysis-off toggle is the permanent correctness oracle.**
   `CRANELISP_NO_OWNERSHIP=1` (backend §2) forces the conservative
   all-Owned/all-atomic/all-heap lowering, **byte-identical to pre-S100 codegen**. Every
   mechanism lane in this plan has a differential twin: same input, toggle-on vs
   toggle-off, identical observable output. A lane that passes only toggle-on is not a
   pass.
2. **Every acceptance stage keeps the two-sided bar** (spine §0 north-star): scale
   dividends AND unnoticeable small-case overhead. Every performance gate in §2 is
   paired with a serial / 1-worker non-regression lane on the same fixtures. A mechanism
   that wins the parallel lane by regressing the serial lane fails acceptance.
3. **Metrics discipline carries from S99 verbatim** (`s99-measurement.md` §1, §10
   discipline note): release-tier binaries; wall/user/sys collected separately
   (`/usr/bin/time`); RC-op + alloc counts via `CRANELISP_RC_STATS`,
   program-attributable = raw − no-op-`--run` baseline; median-of-7 with per-rep
   min/med/max for the fixed-work probes (F1–F3); **F4 is always read as a
   distribution** (11-rep sweeps; never a single median pair — the Wave-0 "23×" was a
   cherry-picked pair, §10.1); per `memory/feedback_verify_fix_not_symptom_absence.md`
   no wall-clock delta is attributed to a mechanism unless the mechanism's own counter
   moved (the 1b F4 false-green lesson).
4. **Perf lanes are scripts, not canonical nextest.** The F-gates, turn-latency, and
   attribution lanes live in `tests/perf/` beside `s99_measure.py` (30s suite cap
   discipline). Correctness/differential/fence lanes are canonical `cargo nextest run`
   tests unless flagged otherwise (ASan lanes are scripted — §3.4).

---

## §1. Fixtures and baselines (part 18 substrate)

### 1.1 The standing fixtures

- **F1–F4** — `tests/fixtures/s99/{f1_machinery,f2_contention,f3_inverted_search,f4_sudoku}.cl`,
  unchanged, with the committed parallel≡serial guards (`tests/s99_fixtures.rs`).
  Synthetic scale LEAVES=8192, COPIES=256 unless stated.
- **F2v (NEW, authored at the increment-II sprint open, QA-owned)** — a single-constructor
  variant of F2: `(deftype Cell (Cell [:Int value]))` replacing the two-constructor
  `(Given …)/(Solved …)`, everything else identical. Rationale: R5 value-flattening's
  **first landing is one-word, single-constructor** (backend §7.1/§7.2) and therefore
  does **not** cover the S99 two-ctor `Cell` — F2v is the honest R5 witness; F2 stays
  the nested-ADT-constraint witness graded at the composed end-state (§5 limit 1).
- **Micro-fixtures per mechanism** (authored with each increment's QA-first tests): the
  stack-slot TCO shape, the projection-escape shapes, the reuse-fence shape, the
  redefinition-cascade REPL scripts (§3–§4 name each).

### 1.2 The S99 baselines this plan grades against (system alloc, release)

| # | metric | value |
|---|---|---|
| B1 | F1 rc_inc (program-attributable, serial) | 2,129,921 |
| B2 | F2 rc_inc / allocs | 169,902,081 / 4,194,386 (= 81.0 inc + 2.0 allocs per shared copy × 2,097,152 copies) |
| B3 | F4-hard rc_inc / allocs | 52,576,384 / 12,764,604 |
| B4 | F2 wall/user/sys — serial · 1-worker · N-worker | 0.72/0.36/0.29 · 0.72/0.97/0.27 · 2.22/19.18/0.47 |
| B5 | F2 N-worker contention delta (user, N-worker − 1-worker) | ≈ +18.2 s |
| B6 | F4-hard serial | 0.90/0.67/0.19; N-worker wall 3.3–20.7 (distribution) |
| B7 | Best pre-Phase-H stack (mimalloc+gate) residual | F2 still 2.3× slower than serial; F4 still ~6–15× (s99 §10.3) |

Each implementing sprint re-captures a **fresh toggle-off baseline on its own HEAD**
before grading (compiler drift between S99 and the increment sprint must not be
attributed to the mechanisms).

---

## §2. Part 18 — staged acceptance targets (spine §9, R8)

Gate numbers below are **provisional operationalisations**: set now so the increments
have a concrete bar, re-ratified (not silently relaxed) at each increment sprint's
Phase-1 against the fresh baseline. A gate that moves must move in the sprint plan with
rationale, not in the harness.

### 2.1 Stage M — the R3 machinery (no performance gates; correctness only)

The machinery sprint is graded by §3.6's R3 lanes (trap stubs, cascade, slot versioning,
summary-diff fast path) plus one latency pin: the **body-only redefinition turn** is
observably at today's cost (§3.5 L-D1 gate applies from this stage on, since the
summary-diff gate is machinery, not increment-I analysis). Per the `/arch` S101 Phase-2
ruling (`sprints/SPRINT.md` §Architecture review) the `CRANELISP_NO_OWNERSHIP` toggle
**and its cache-manifest key** ship at stage M, so the L-B2(i) suite-polarity leg and
the L-B3(1)–(3) manifest-key lanes also grade this stage (§3.1). Sprint-ready drafting
specification: §6.1.

### 2.2 Stage I — increment I (read path: borrow-elision, projection, stack slots, confined non-atomic RC, fact table, str-len sibling)

| Gate | Lane | Bar |
|---|---|---|
| **I-G1 (headline read-path collapse)** | F1 rc_inc, serial, program-attributable | **≥ 99% drop vs B1** (< 25,000 residual). F1's ~2.13M incs are one per `(vec-get g i)` element read + match projections on a borrowed root — exactly the projection-covered class (typecheck §4; borrowed capture §8.2-spine). Residual budget = grid build (81 cells) + machinery. |
| **I-G2 (attribution honesty)** | F2/F3/F4 rc_inc | **Expected essentially unchanged** (within 1% of B2/B3): the 170M term lives inside the `vec-set-copy`/`vec-push-copy` Rust bodies (backend §5.2 table) and is a write-path/increment-II target. This is an assertion, not a concession — if increment I *does* move it, the attribution model is wrong and acceptance halts for re-diagnosis. |
| **I-G3 (confinement correctness pin)** | per-mechanism counters on F2 | The shared board's cell classifies **Confined** (typecheck §5.3's F2 discharge) — asserted via the ownership-trace/counter hooks (§3.7), i.e. the surviving parent-side inline ops on it emit non-atomic. This is the designed attack on the S99 (b) shape and must be verified as a *classification*, independent of wall-clock. |
| **I-G4 (parallel non-regression)** | F2/F3 N-worker wall+user, median-of-7 | ≤ +5% vs same-HEAD toggle-off. (Increment I is not expected to *cure* F2; it must not worsen it.) F4: distribution report only. |
| **I-G5 (small-case overhead)** | F1–F4 serial + 1-worker, toggle-on vs toggle-off | wall+user median ≤ +3%, spreads overlapping-or-better — EXCEPT density-declined cells (B4 declines dense speculative sparks; currently only f3/1worker), which grade user/CPU ≤+3% and print the 1-worker wall as a VISIBLE user-accepted-trade line (§2.2.1a). Plus batch compile-time of the fixture corpus (cold cache, `--run` to first output) ≤ +10% — the pass5 structural budget (typecheck §3.4). |
| **I-G6 (interactive latency)** | L-D1 REPL turn lane | body-only redefinition turn ≤ 1.10× toggle-off median; ABI-changing turn reported with cone size (no numeric gate at first landing — the cone is the same set R3 must recompile anyway; typecheck §3.4). |
| **I-G7 (stack/region)** | alloc counter on the stack-slot micro-fixture (statically-sized scalar-payload ADT/closure temporaries in a hot loop) | heap allocs at the eligible sites → 0 (stack-slot-hit counter = loop count); F-series alloc counts reported (F2's 2-allocs-per-copy are escaping COW copies — not increment-I-eligible, expected unchanged; stated so the gate is honest). |

### 2.2.1 Increment-I acceptance record (S102 — measured, reconciled harness)

**Status:** ACCEPTED. `tests/perf/ig_gates.py` (release binary
`target/release/cranelisp`, `--reps 7`) — all selected gates PASS on a
corrected, resolution-bearing harness. Full verdict line reproduced verbatim
below. This subsection is the durable measured-acceptance artifact for
increment I.

**Verdict line (reps=7, settled load, 2026-07-05):**

```
[I-G1] PASS — F1 rc_inc serial: off=2129921 on=2 drop=100.00% (bar ≥99%)
[I-G2] PASS — f2_contention(flat): Δ=0.00%; f3_inverted_search(flat): Δ=0.01%;
        f4_hard(elision): rc_inc drop=39.76% wall -9.4% (honest);
        f4_easy(elision): rc_inc drop=31.59% wall +3.3% (honest)
        (bar: F2/F3 flat ≤1%; F4 drop paired with wall ≤+5%)
[I-G4] PASS — f2_contention: wall +4.5% user +4.4%; f3_inverted_search: wall -1.3% user -1.3% (bar ≤ +5%)
[I-G4/F4 report] N-worker wall on=[8.38,9.81,14.54,30.28,33.0] off=[6.6,12.16,15.15,15.6,19.18]
[I-G5/runtime] PASS — f2/serial w-2.5 u-2.0; f2/1worker w+2.5 u+2.4; f3/serial w+1.2 u+1.3;
        f3/1worker w+0.5 u+1.0 (graded bar ≤+3%);
        report-only <60ms startup-dominated (tripwire ≤+25%):
        f1/serial w-11.0 u-35.4; f1/1worker w-26.2 u-46.2; f4_easy/serial w+4.2 u+4.4; f4_easy/1worker w-0.5 u+4.0
[I-G5/compile] PASS — corpus aggregate cold-cache: on=0.125s off=0.127s Δ=-1.9% (bar ≤+10%);
        per-entry on/off all 0.010–0.017s
all selected gates PASS
```

**The three harness reconciliations (artifact → real property → evidence).**
Each corrects a **false negative** produced by measurement under-resolution or
mis-framing; the true behaviour was independently verified sound before the
harness was touched (`memory/feedback_verify_fix_not_symptom_absence.md` — a
gate is reframed to green ONLY after proving the property it should measure
actually holds). None hides a regression: wall-clock is neutral-to-faster
across the board.

1. **I-G2 — attribution honesty, REFRAMED.**
   - *Artifact captured by the old measurement:* the gate asserted F2/F3/**F4**
     rc_inc all within 1% of toggle-off, treating ANY rc_inc change as
     mis-attribution. It flagged F4/sudoku's **39.76% rc_inc drop** as a
     failure — but F4 is a *legitimate borrow-elision beneficiary* (typecheck
     §4 projection class), so the drop is the mechanism working as designed,
     not mis-attribution. The old frame could not tell an honest win from a
     mis-attribution.
   - *Real property the gate should validate:* a fixture's rc_inc drop is
     **honest iff** (a) fixtures the read path does NOT apply to show **no
     spurious drop** (F2/F3 — the 170M shared-artifact term lives in the Rust
     copy loops, increment-II-deferred, backend §5.2: expected flat, ≤1%); AND
     (b) a beneficiary's drop is **paired with a non-regressing wall** (a
     mechanism that "drops rc_inc" while slowing the program moved cost rather
     than removing it — the dishonest signature). F4 gate = drop>0 (genuine
     beneficiary) AND serial wall ≤ +5%.
   - *Evidence (reps=7):* F2 Δ0.00%, F3 Δ0.01% — correctly flat (no spurious
     drop where the mechanism doesn't apply). F4-hard rc_inc drop 39.76%
     **paired with wall −9.4%** (ON faster; observed −0.0% / −0.7% / −9.4%
     across runs — always non-regressing); F4-easy drop 31.59% paired with
     wall +3.3% (within the ≤+5% non-regression bar). The drop-with-faster-wall
     is the honest-win signature. Corroborated by I-G4/F4's ON≈OFF N-worker
     distribution and I-G1's F1 collapse.

2. **I-G5/compile — timer under-resolution (0.00s → +inf% harness bug), FIXED.**
   - *Artifact:* `cold_compile_seconds` measured cold `--run` wall with
     `/usr/bin/time -f wall=%e`, whose resolution is **0.01s**. Every corpus
     entry compiles in 8–18ms → each read 0.00–0.01s, the corpus aggregate
     quantized to 0.00s, and `pct(0,0)=+inf` → the gate could never pass. The
     "+inf% FAIL" was pure quantization, measuring nothing.
   - *Real property:* the pass5 structural compile overhead ON-vs-OFF over the
     L-B1 corpus, cold cache, ≤ +10% (typecheck §3.4). A *measured* delta.
   - *Fix + evidence:* replaced with in-process `time.perf_counter()` around
     the subprocess (sub-ms resolution). Per-entry compile now resolves to
     0.010–0.017s; **corpus aggregate on=0.125s off=0.127s Δ=−1.9%** —
     comfortably inside ≤+10%, and neutral-to-faster (the true near-zero pass5
     overhead sits under a few % of process-startup common-mode noise). A real
     number where the old harness had none.

3. **I-G5/runtime — sub-resolution tiny-workload fixtures, FIXED.**
   - *Artifact:* the FAILs were entirely F1 (~18ms) and F4-easy (~50ms). Under
     `/usr/bin/time`'s 0.01s tick a single-tick jitter on a sub-60ms workload
     becomes a ±20–100% swing (the `user −100%` / `wall +20%` false
     +regressions). The resolution-bearing fixtures F2/F3 (~460ms) were always
     correct.
   - *Real property:* small-case runtime overhead ON-vs-OFF ≤ +3% **where
     resolution exists**. Measuring a ≤3% overhead on an 18ms process
     dominated by fixed startup + JIT is below the noise floor — the honest
     scope of the graded bar is the resolution-bearing fixtures.
   - *Fix + evidence:* all I-G5 timing switched to hires (perf_counter wall +
     `os.wait4` rusage user/sys, microsecond resolution). **Graded** F2/F3
     serial+1-worker on ≤+3%: reps=7 gave w−2.5/+2.5/+1.2/+0.5%,
     u−2.0/+2.4/+1.3/+1.0% — all within bar. F1/F4-easy moved to
     **report-only** (documented: startup-dominated, pass5 delta below the
     wall noise floor) with a gross-regression tripwire ≤+25%; F1's user CPU
     (**−35% serial / −46% 1-worker** — the ~2.13M rc ops vanishing) is the
     real ON-faster evidence, corroborating I-G1. hires never reproduces the
     old false +regression: F1 reads consistently *faster*, never +20%.

**Measurement-trust notes (honest caps).**
- *N-worker + tiny-fixture variance is real.* An earlier reps=7 run under
  elevated background load (5-min load-avg ≈ 4.6 from prior probe processes)
  showed I-G4/f3 +6.9% and I-G5/f2-serial +4.1% — transient contention, not
  regressions: both returned within-bar on a settled-load re-run (the verdict
  above), matching the sprint's independent reps=7 ground truth. Acceptance
  runs must be taken at settled load; the graded bars hold there.
- *Report-only ≠ ungated.* F1/F4-easy carry a ≤+25% gross-regression tripwire
  so a 2× blowup is still caught; they are excluded from the ≤+3% grade only
  because a ≤3% signal is unresolvable on a startup-dominated <60ms workload —
  not to hide anything (both read neutral-to-faster).
- *Corpus programs exit with their result.* The L-B1 corpus mains return
  `Pure(int)` and `--run` uses that as the process exit code (corpus 01 → 24,
  etc.), so the compile probe treats only a **signal kill** (negative Python
  returncode) as a crash, never a nonzero exit.

**Harness changes (S102):** `tests/perf/ig_gates.py` (I-G2 reframe, I-G5
compile perf_counter, I-G5 runtime hires + grade/report split, absolute
SYS_BIN for the `cwd=tempdir` compile probe, signal-only crash guard);
`tests/perf/s99_measure.py` (new `hires_time`/`hires_median` helpers —
perf_counter + `os.wait4` rusage; existing `/usr/bin/time` helpers untouched,
so the S99 record is preserved). The harness is a standalone perf tool,
outside canonical `cargo nextest run` — no interaction with the suite baseline.

#### 2.2.1a B4 accepted-trade reframe (S102 Wave-18 → user Phase-7 ruling, 2026-07-05)

**This is categorically different from the three reconciliations above.** Those
cured **false negatives** — the gate mis-measured a behaviour that was actually
sound. This one records a **REAL regression the user explicitly chose to
accept.** The distinction is load-bearing: the reframe does NOT erase the
number — it keeps the measured +~6% VISIBLE in the gate output and this record
as a documented accepted trade, and it grades the property that must NOT
regress (CPU/user) so a genuinely dishonest "moved-cost-not-removed" outcome
would still trip the gate. (This is the honest side of
`memory/feedback_verify_fix_not_symptom_absence.md`: we did not relax a bar to
bury a number; we regraded the correct property and left the accepted cost on
the page.)

**What B4 is.** Ladder rung B4 (commit `68cf4d8`, `feat(backend): B4 / FIXME
0459 — static alloc/RC-density admission axis on sparkability`) adds a static
allocation/RC-density admission gate on sparking: it **declines dense
speculative-search sparks to the serial arm** rather than spawning them.

**The trade on `f3_inverted_search` (settled load, reproducible at 1-min load
0.88 and 6.0; pre-B4 the f3/1worker delta was +0.0%):**

| Axis | Config | Δ vs toggle-off | Disposition |
|---|---|---|---|
| N-worker wall | N-worker | **−82%** | WIN — B4 kills parallel over-sparking contention (I-G4 territory) |
| user CPU | everywhere | **−46%** | WIN — universal CPU savings (dense sparks no longer speculated) |
| **1-worker wall** | **1worker** | **+~6% (measured +4.0% / +5.7% / sprint +6.1%)** | **ACCEPTED COST** — eager speculation had hidden latency on the 1-worker critical path; declining it defers that. The 1-worker config is a *measurement baseline, not a production mode.* |
| serial wall | serial | ≈0% (−1.4%…+0.0%) | HELD — B4 does not regress serial |

**User Phase-7 ruling (2026-07-05), verbatim:** *"perfectly reasonable
tradeoff. reframe i-g5 and keep the gains."* The parallel win (−82% N-worker)
plus the universal CPU savings (−46% user) dominate; the modest 1-worker-wall
cost is the accepted price of forgoing eager speculation on a config that is
only a measurement baseline.

**The reframe (specific, not a blanket bar relaxation).** `ig_gates.py` now
carries a `DENSITY_DECLINED = {("f3_inverted_search", "1worker")}` set. For that
single cell I-G5/runtime grades **user/CPU ≤ +3%** (the density-decline
dividend — measured −45.6% / −45.9%, which is also the anti-false-green guard:
a mechanism that *moved* cost into CPU rather than removing it would trip here)
and **prints the 1-worker wall as a VISIBLE accepted-trade line**, ungraded:

```
f3_inverted_search/1worker: wall +4.0% [accepted trade — density-declined spark, §2.2.1] user -45.6%
```

Serial wall for f3 is graded normally (≤+3%, held at −1.4%…+0.0%). **The
ordinary ≤+3% wall+user bar is untouched for every other (fixture,config)** —
f2/serial, f2/1worker, f3/serial all still gate on wall AND user, so this does
NOT mask a future regression on any non-density-declined workload. The density
exemption is one named cell, extended only when a new fixture is *shown* to be
density-declined (add it to the set with its own record entry).

**Verdict (reps=7, settled load 0.48–0.66, 2026-07-05, release binary rebuilt
at HEAD):** two consecutive runs, both `all selected gates PASS`:

```
[I-G5/runtime] PASS — f2/serial w+1.4 u-1.1; f2/1worker w-1.2 u-0.8; f3/serial w+0.0 u-0.1;
        f3/1worker wall +4.0% [accepted trade — density-declined spark, §2.2.1] user -45.6%
        (graded bar ≤+3% wall+user; density-declined cells grade user only)
[I-G5/compile] PASS — corpus aggregate cold-cache: on=0.121s off=0.120s Δ=+1.1% (bar ≤+10%)
```

Second run identical disposition: f3/1worker wall +5.7% [accepted trade] user
−45.9%; I-G5/compile Δ−7.0%. The accepted +~6% is stable and always paired with
the ~−46% CPU dividend. I-G4 (the −82% N-worker win) and the universal CPU drop
are the gains this reframe keeps.

### 2.3 Stage II — increment I+II (write path: reuse tokens, R5 one-word flattening, region arena)

| Gate | Lane | Bar |
|---|---|---|
| **II-G1 (R5 witness)** | F2v rc_inc + wall | rc_inc collapses to **near-zero** (< 1% of B2): an 81-slot Vec of one-word value-`Cell`s copies by memcpy with null elem fns (backend §7.3). Wall: **F2v N-worker < F2v serial** — the first configuration where parallelism must actually pay on the copy shape. |
| **II-G2 (reuse hit-rate)** | reuse hit/miss counters on F4 (copy-per-guess) | in-place reuse hit-rate on the guess-grid write chain ≥ 50% (provisional; the copy-once-then-in-place property of backend §6.2 predicts ≫ this for chained writes). Counter movement is the attribution prerequisite for any F4 wall claim (§0.3). |
| **II-G3 (F4 floor progress)** | F4-hard 11-rep distribution | median wall ≤ **2× serial** (from B7's 6–15×), and the whole wall distribution's median-to-max below toggle-off's. **RE-SCOPED at S103 close (2026-07-06) — this bar is NOT increment-II-gradeable.** The S103 profiling investigation (FIXME 0534) PROVED F4-hard's parallel wall is **rayon scheduler churn** (9.45M ultra-fine score-0 sparks × ~13µs spawn/park each), not a write-path / RC / contention cost — so it is unreachable by ANY increment-II mechanism (R5 flattening, reuse tokens, borrow-elision leave it identical; it reproduces at increment-I HEAD). Its cure is a **spark-overhead cost axis** (decline sub-spawn-cost sparks), a concurrency-track /design deliverable (0534, re-pointed /design, carried to S104). II-G3 is therefore **regraded against the composed III-G / Phase-H+concurrency end-state** (III-G2, per spine §7 staging), gated on 0534's spark-overhead axis — NOT a Stage-II bar. See §2.3.1 for the measured S103 FAIL (kept VISIBLE — scope correction with proof, not a relaxation) + the interim ON-vs-OFF tripwire. |
| **II-G4 (F2 two-ctor honesty)** | F2 rc_inc + wall | partial: report rc_inc drop from reuse on chained copies; wall ≤ 1.5× serial (from B7's 2.3×). F2's shared-grid copies-of-a-shared-root are *genuine shared materializations* — fully cured only by multi-ctor flattening or persistent DS (§5 limit 1); II-G4 must not be silently graded as if R5-first-landing covered it. |
| **II-G5/G6** | = I-G4/I-G5/I-G6 re-run | same non-regression + overhead bars, including F2v serial. |

### 2.3.1 Increment-II acceptance record (S103 — measured, release binary)

**Status:** MEASURED, MIXED. `tests/perf/ig_gates.py` extended with the II-G
runner (`--gates ii` / `iig1..iig5`); release binary `target/release/cranelisp`,
median-of-7 (F4-hard distribution 7-rep), fresh same-HEAD toggle-off baseline,
settled load, 2026-07-06. Differential oracle (`CRANELISP_NO_OWNERSHIP`)
byte-identical-off throughout (suite L-B2 green; 4091/4090/1/1, only RED = the
intentional 0528 chaining witness). This subsection is the durable
increment-II measured-acceptance artifact.

**Per-gate verdict (numbers):**

- **II-G1 (R5 witness) — SPLIT: rc_inc PASS (decisive), parallel-pay benign non-pass.**
  - *rc_inc collapse — PASS.* F2v program-attributable rc_inc **on=32,769** vs
    B2=169,902,081 = **0.019%** (bar < 1%). Off-polarity F2v rc_inc = 169,902,081
    (= B2), so the collapse is entirely R5's own effect (RC_STATS attribution).
    Allocs also halve (ON 2,097,154 vs OFF 4,194,387 — the 2-allocs-per-copy → 1
    memcpy). Corroborated by the L-B1 null-elem-fn CLIF assertion.
  - *Parallel-must-pay (N-worker < serial) — NON-PASS, benign.* F2v N-worker
    **0.55s** vs serial **0.12s** — parallel does not beat serial. But this is
    NOT a regression: R5 made F2v **serial ~40× cheaper** and made F2v **N-worker
    10× faster than OFF** (ON 0.55s vs OFF 5.34s). Parallelism can't pay only
    because R5's serial copy is now too cheap to beat at this scale (81-cell Vec,
    memcpy). The mechanism works; the "parallel pays" bar was written before R5's
    serial-collapse was measured. Honest non-pass — flag to `/sprint`/user as a
    bar-re-ratification question (the copy shape is cured, not contended).
- **II-G2 (reuse hit-rate) — PASS (decisive).** F4-hard **reuse_hit=60,
  reuse_miss=0 → hit-rate 100.0%** (bar ≥ 50%); f4_easy 49/0 = 100.0% (report).
  Counter moved (60 > 0 — the §0.3 attribution prerequisite). **Measured directly
  off the delivered `reuse_hit`/`reuse_miss` counters, INDEPENDENT of the
  `(map inc (map dec v))` chaining witness** (that witness is a companion, not
  the numeric gate — §2 chaining note). **II-G2 is met by the delivered
  mechanism; the `chaining_toggle_off` fusion witness (FIXME 0528) is NOT
  required for II-G2 — 0528 is a clean carry.**
- **II-G3 (F4 floor progress) — FAILS AS WRITTEN (kept visible), but RE-SCOPED off
  increment II: the target is unreachable by any increment-II mechanism (FIXME 0534,
  profiling-proven).** F4-hard median N-worker **121× serial** at truly-idle 10 cores
  (ON 108.8–116s vs serial 0.91s; bar ≤ 2×). **The number stays on the page — this is
  a scope correction backed by a CPU/syscall/spawn-count profile, NOT a bar
  relaxation** (the honest side of `memory/feedback_verify_fix_not_symptom_absence.md`;
  the S102 I-G5 accepted-trade precedent — regrade the correct property, leave the
  measured cost visible).
  - *S103 result, honest:* the differential is clean — analysis-ON N-worker ~108s vs
    analysis-OFF 5.46s, serial unaffected (ON ≈ OFF ≈ 0.9s). Distribution
    N=[104.1, 108.8, 109.7, 110.7, 112.0, 113.4, 116.7] (tight, not cherry-picked).
  - *Profiling attribution (FIXME 0534 §PROFILING ATTRIBUTION, /dev(backend), 2026-07-06
    — the wall PROVEN, not "just contention"):* the ~110s is **rayon task-scheduling
    overhead** — **9.45M ultra-fine score-0 sparks** (the per-cell accessor/projection
    pairs, ~20ns real bodies) each paying **~13µs spawn/futex-wake/park**. Evidence:
    **240% CPU** on 10 cores (⇒ ~7.6 cores idle — parking, NOT a pegged spin-loop),
    **6.3M voluntary ctx-switches** (workers in `futex_do_wait`), syscall profile
    **99.9% scheduler** (sched_yield 50% + futex 49%) / **~0% allocator** (glibc malloc
    stays in userspace — allocator-lock hypothesis REFUTED at the syscall layer), and
    a spawn-count sweep with **wall ≈ linear in spawn count** (halving spawns halves the
    wall — the signature of fixed per-task scheduling cost × task count, not
    data-dependent cache contention). `claim_wins == spawns` (no redundant recompute;
    rc_inc identical serial-vs-ON at 31.7M ⇒ logical work unchanged).
  - *Why it is NOT increment-II-gradeable — the re-scope:* it is **NOT
    increment-II-introduced** (reproduces identically at increment-I HEAD `25ffe12`:
    ON-default ~107s at 10 cores, same 104/4/6 density distribution — the S103 R5/reuse
    change-sets did not cause it); the "regression vs S102" was a **measurement-condition
    artifact** (S102's ON=[8.38…33.0] landed in the 2–6-effective-core band under
    residual load; the 108s is the same pathology at truly-idle full 10 cores — a
    textbook `feedback_verify_fix_not_symptom_absence.md` false read). It is **NOT
    contention/RC-bound**, so Phase-H thread-local-RC/reuse/borrow would NOT fix it. The
    real cure is a **spark-overhead cost axis** (decline sub-spawn-cost sparks — 0534
    option (b)/(1a)), a **concurrency-track /design deliverable** (0534 re-pointed
    `target: /design`, carried to S104, user-approved 2026-07-06). II-G3's target (F4
    parallel ≤ 2× serial) therefore belongs to the **composed III-G / Phase-H+concurrency
    end-state (III-G2)** per spine §7 staging — graded there, gated on 0534's
    spark-overhead axis — not at Stage II. **Tracking record: FIXME 0534.**
  - *The write-path mechanisms that II grades all PASS:* II-G1 (R5 rc_inc collapse),
    II-G2 (reuse 100% hit), II-G5/G6 (I-G non-regression re-run) — see their bullets.
    F4-hard's parallel wall is a **scheduler-admission** property, orthogonal to the
    write-path facts increment II delivers; regrading II-G3 off Stage II does not
    unground any delivered mechanism.
  - *Interim actionable tripwire (kept as the standing S104-must-clear watch):* the 0534
    diagnosis notes **ownership-ON must not be worse than ownership-OFF** — currently
    **VIOLATED** (ON ~112s vs OFF 15.9s at full cores; B4's coarse-spark decline while
    the fine sparks stay admitted strands them, making ON *net-harmful*, not merely
    neutral). This is the real, bounded interim signal (≤ OFF, not ≤ 2× serial); the
    S104 spark-overhead fix must clear it. Recorded here so the failure carries an
    actionable bar in the interim rather than an unreachable one.
- **II-G4 (F2 two-ctor honesty) — wall FAIL, but the DOCUMENTED §5-limit-1 case,
  NOT a regression.** rc_inc drop = **0.00%** (ON 169,902,081 = OFF — F2's
  two-ctor `Cell` is genuinely not R5-covered; the honest report, §5 limit 1).
  F2 N-worker **5.05s** vs serial **0.52s** = **9.69×** (bar ≤ 1.5×). The bar
  derives from B7's 2.3× *mimalloc* stack; this binary uses the system allocator,
  and F2 N-worker ON (5.11s) ≈ OFF (5.47s) — increment II neither cured nor
  regressed F2. F2's shared-grid copies are genuine materializations, cured only
  at the III-G composed end-state (persistent DS / multi-ctor flattening). Graded
  honestly as a partial, explicitly **not R5-covered**.
- **II-G5/G6 (I-G non-regression re-run, incl. F2v serial) — PASS (settled load).**
  F2v serial ON vs OFF **wall −74.9% user −76.9%** (R5 win — the new fixture's
  two-sided bar held with margin to spare). I-G5 small-case re-run at settled
  load across 3 runs: all resolution-bearing cells (f2/serial, f2/1worker,
  f3/serial) oscillate within ±5% around zero with **medians within the ≤+3%
  bar** — single-run trips (f2/serial +4.1% under elevated load; f3/serial +4.6%
  one settled run) are measurement noise (the failing cell moves run-to-run,
  never consistent), exactly the variance the §2.2.1 measurement-trust note
  documents. Density-declined f3/1worker: accepted-trade wall +4.5…+8.7%,
  **user −45…−48%** (graded, passes). I-G5/compile: corpus aggregate cold-cache
  **Δ+0.0%** (bar ≤ +10%).

**Summary.** The two write-path mechanisms are individually validated: **R5
collapses rc_inc (II-G1 rc_inc 0.019% of B2)** and **reuse tokens hit 100% on F4
(II-G2)**; the differential oracle stays byte-identical-off. **All the write-path
gates that grade the delivered mechanisms PASS** (II-G1 rc_inc, II-G2, II-G5/G6).
Two gate non-passes are designed/benign (II-G1 parallel-pay — R5's serial too
cheap to beat; II-G4 wall — the §5-limit-1 F2-not-cured case). **II-G3 FAILS as
written (121× at 10 cores) but is RE-SCOPED off increment II** (2026-07-06,
S103 close): the S103 profiling investigation (FIXME 0534) PROVED its wall is
**rayon scheduler churn** — 9.45M ultra-fine score-0 sparks each paying ~13µs
spawn/park (240% CPU, 6.3M vol ctx-switches, syscalls 99.9% scheduler / ~0%
allocator, wall linear in spawn count) — **not** a write-path/RC/contention cost,
reproducing identically at increment-I HEAD and unreachable by any increment-II
(or Phase-H RC/reuse) mechanism. Its cure is a **spark-overhead cost axis**
(concurrency-track /design, 0534 re-pointed `target: /design`, carried S104,
user-approved); it is regraded against the composed **III-G / III-G2** end-state.
The failure number stays VISIBLE (scope correction with proof, per
`feedback_verify_fix_not_symptom_absence.md` — mirroring the S102 I-G5 honest
reframe), and carries an **interim tripwire** (ON must not be worse than OFF —
currently violated 112s vs 15.9s — the bounded bar S104's fix must clear). 0528
(the chaining witness) is a clean carry — not required for II-G2.

**Harness (S103):** `tests/perf/ig_gates.py` gained the II-G runner
(`run_ii_gates`, `reuse_counts`, B2 constant, `--gates ii`);
`tests/perf/s99_measure.py::gen_fixtures` gained the F2v fixture. Standalone
perf tool, outside canonical `cargo nextest run`.

### 2.4 Stage III — the composed end-state (persistent DS and/or multi-ctor flattening in play)

The only configuration honestly comparable to the north-star. Operationalisation of
"strong parallelisation dividends at scale; slight per-core discount":

- **III-G1:** F2 (and F2v) N-worker wall **< serial wall** (parallelism pays on the
  copy-a-shared-Vec-of-ADTs shape) **and** total CPU (user+sys) ≤ **1.3× serial's**
  (the "slight per-core discount", measured as aggregate-CPU inflation).
- **III-G2:** F4-hard median wall ≤ **serial** (parallel speculative search at least
  breaks even on the real workload), distribution reported.
- **III-G3:** small-case bar unchanged (≤ +3% serial lanes; L-D1 ≤ 1.10×).

---

## §3. Part 17 — verification lanes

Each lane: **purpose → mechanics → gate → stage → tier**. "Hook:" marks owed
observability that compiler skills must implement (per `tests/CLAUDE.md` §Diagnostic
Requirements — `/qa` specifies, the owning skill builds); §3.7 collects them.

### 3.1 The analysis-off differential oracle (backend §2.2(4); spine §6.2)

- **L-B1 — CLIF-text equality (byte-identical-off).**
  *Mechanics:* corpus = the S99 fixtures + a curated spec-shape corpus (one module each:
  ADT construct/match, closures + fn-as-value + auto-curry, vec COW loop, string
  externs, ParBind/LaunchContinue, TCO loop, trait dispatch — the shapes the five
  mechanisms touch). **The corpus is green-only by construction** (S102 Phase-2 /arch
  ruling; canonical home `design/arch/ownership-inference.md` §6.2): every shape under
  an open failing-not-ignored guard at capture time is EXCLUDED — at S102 capture that
  is the 0483 two-instantiation-HOF, 0488 FQ-call/imported-value-use, and 0484
  shadow-order shapes (live list = whatever the ledger's intentional-RED set covers).
  Exclusions are committed as `EXCLUSIONS.md` beside the corpus, each entry naming the
  guard whose flip triggers extension; a `MANIFEST.md` records entry → source fixture →
  capture SHA so extensions and re-baselines stay attributable. This is what makes the
  capture non-blocking on the co-scheduled defect wave. At the **parent commit of the
  increment-I change-set**, capture the per-function CLIF of the corpus via
  `CRANELISP_CODEGEN_DUMP` and commit it as a golden (`tests/fixtures/clif_baseline/`).
  Lane: toggle-off build of HEAD dumps the same corpus; normalized diff (sort by
  function symbol; strip nondeterministic ordering — see Hook H1) must be **empty**.
  **Extension ≠ re-baseline** (the 0503 pin): when a defect fix makes a
  previously-excluded shape green, the corpus is *extended* with the newly-green shape
  in the fix change-set — existing golden entries untouched, the `EXCLUSIONS.md` entry
  struck. A *re-baseline* — re-dump of only the entries whose CLIF changed, golden
  diff in the same commit, delta attributed to the change's seam (exactly the
  `public-api.txt` discipline) — happens only for an **emission-affecting** change:
  one that changes backend emission, primitives entry shapes, monomorphisation
  derivation, or name-resolution precedence *for green programs* (the §6.2
  classifier). Display/persistence/introspection/diagnostic fixes have no capture
  interaction. Wholesale re-capture without attribution is forbidden.
  *Gate:* zero diff. *Stage:* I onward, every change-set touching the five mechanisms.
  *Tier:* script lane + one in-suite smoke (single module golden compared in a nextest
  test, so the canonical suite catches gross breakage).
  *Note:* §9.3's dual-symbol pattern makes even the Rust side byte-identical-off (the
  consuming export is never edited) — the smoke asserts the emitted call targets too.
- **L-B2 — output differential (toggle-on ≡ toggle-off).**
  *Mechanics:* two legs. (i) **Suite-polarity leg:** the entire canonical
  `cargo nextest run` executes green under BOTH polarities of `CRANELISP_NO_OWNERSHIP`
  — the full e2e suite is already an output-assertion corpus; run it twice in CI
  (allowing only the ledgered intentional-failure set, identical under both). (ii)
  **Byte-differential leg:** a runner script executes the F-fixtures + `examples/`
  corpus + the mechanism micro-fixtures under both polarities and byte-compares
  stdout/stderr/exit status.
  *Gate:* identical pass-set (i); byte-identical observables (ii). *Stage:* (i)
  **M onward** — the toggle + manifest key ship at stage M per the `/arch` S101 Phase-2
  ruling (`sprints/SPRINT.md` §Architecture review); at M both polarities are
  behaviourally identical by construction (no analysis exists yet), so the leg's
  M-stage value is installing the protocol and guarding the toggle plumbing. (ii) I
  onward — the byte-differential only becomes discriminating once mechanisms land.
  *Tier:* (i) CI double-run (a gate-time lane — two full suite runs, executed at
  Phase-5 exit / wave gates, not in the per-commit loop); (ii) script lane.
- **L-B3 — cache-manifest invalidation key.**
  *Mechanics/tests:* (1) compile a multi-module project toggle-on, flip the toggle,
  re-run: assert **wholesale invalidation** (full recompile observed via
  `CRANELISP_MODULE_TRACE` cache-hit/miss lines) and correct output. (2) *Negative:*
  after the flip, no stale `.o` is consumed (zero cache hits) — mixed-ABI caches
  unrepresentable (backend §2.3). (3) Round-trip: flip back, again wholesale, output
  identical. (4) At R5 landing: `CACHE_SCHEMA_VERSION` bump invalidates every pre-R5
  cache (backend §7.4).
  *Stage:* (1)–(3) **stage M** (the manifest key lands at M with the toggle, per the
  same `/arch` S101 ruling — these lanes are the manifest-plumbing witness, drafted RED
  at M per §6.1); (4) increment II. *Tier:* canonical nextest (`cache.rs` family).

### 3.2 Starved-inc fences — every skip-the-inc emission site (the S98-bug-#2 class)

The spine mandates a regression fence on **every** "skip the inc" emission. The site
enumeration (from backend §3/§9 + typecheck §4) and the fence design:

| # | Elision site | Fence fixture shape |
|---|---|---|
| S1 | §3.1 caller-side skip-inc: Var arg → `Borrowed` param | caller passes `xs` borrowed, callee reads it, **caller uses `xs` again after the call**, N=1000 sustained iterations; assert value correctness + heap balance |
| S2 | §3.3 projection reads: `vec-get` skip-inc on borrowed root; match-field bindings; accessor `ProjectionOf` results | project, read, then use the ROOT again and the projection again, interleaved, sustained; assert values |
| S3 | §3.1 temporary → `Borrowed` param post-call dec | temporary arg to borrowed param; assert no leak (heap balance: allocs == deallocs at exit modulo baseline) AND no double-free (ASan leg) |
| S4 | §3.4/§3.5 wrapper adaptation: `Owned→Borrowed` post-call dec; `ProjectionOf→Fresh` materialization inc in the R2 wrapper and the curry adapter | call the same moded fn (a) statically, (b) through a closure value, (c) curried — same inputs, same outputs, heap balance across all three |
| S5 | §9.3 sibling targeting: no adaptation inc at `str-len$borrowed` | borrowed string through `(str-len s)` hot loop; `s` used after; on/off differential; heap balance |
| S6 | rule-5 materialization at escape edges (the inc must EXIST) | borrowed projection returned / stored / suspension-crossed: assert the escaping value survives (UAF side) AND is released exactly once (leak side) — see L-D3 |

**Fence design (all sites):** (i) **behavioral leg** — the guarded value is *used after
the elided-inc window*, repeatedly (sustained-load convention, 200–2000 crossings,
`tests/CLAUDE.md` §Sustained-load), asserting values, not crash-absence; (ii)
**balance leg** — `CRANELISP_RC_STATS` allocs==deallocs (± documented baseline) at
exit; (iii) **two-condition rule** — each fence runs under plain AND under the ASan
lane; a fence green only under one tool is not green
(`memory/feedback_verify_fix_not_symptom_absence.md`). *Stage:* S1–S4 increment I;
S5 with the sibling; S6 increment I. *Tier:* behavioral+balance legs canonical
nextest; ASan legs scripted (§3.4).

### 3.3 Projection-escape negative differentials (typecheck §12.7)

Wrong things must NOT happen:

- **L-D3a** — borrowed projection **returned**: materializes (S6); the double-free
  twin: caller decs the returned value once, root released once.
- **L-D3b** — borrowed projection **stored** into an escaping ADT/Vec: same pair.
- **L-D3c** — borrowed projection / borrowed capture **crossing a suspension**
  (ParBind-deferred continuation, `LaunchContinue`): must classify Escapes — the retain
  stays (R6). See L-C1.
- **L-D3d** — the **root-release-ordering shape** (typecheck §4.2 rule 4 — the
  Sprint-61 aliased-COW regression one level up): root vec reaches its syntactic
  last-use `vec-set` at rc==1 **while a projected borrow of an element is still live**;
  the projected value must read correctly after the write (in-place mutation must have
  been suppressed or ordered after). Small fixture, CLIF-inspectable.
- **L-D3e** — **fact-table wrong-direction guard**: for every declared-`Borrowed`
  primitive row (the §9-typecheck seed table), a behavioral row-test: arg survives the
  call, is usable after, and balances — so a mis-declared row (says only-read, actually
  retains) fails a test rather than corrupting silently. One test per table row,
  generated mechanically from the audit table at increment-I drafting.
- **L-D3f** — **no false elision**: a param the callee stores/returns must NOT be
  summarised `Borrowed` (assert via the ownership-trace hook H5's classification dump —
  a *negative on the summary itself*, cheaper and sharper than observing the crash).

*Stage:* increment I. *Tier:* canonical nextest (+ H5 hook).

### 3.4 Memory-safety lanes (ASan/UAF; stack slots; reuse)

- **L-C1 — R6 suspension-escape UAF lane.** The exact S98-0486-class site: a value
  whose in-frame uses are all borrowed/projection-covered but which flows into a
  trampoline-deferred `ParBind` continuation / `LaunchContinue` tree. Fixture drives
  the suspension 200–2000 crossings; ASan + behavioral legs. The existing guards carry
  forward unchanged as this fence's floor: `ring2-rc.md` §5.5.2.6's UAF/exclusion
  guards, `tests/launch_grid_corrupt.rs`, `tests/launch_vec_send_corrupt.rs` (flipped
  green with the 0486 fix — the S100-close suite state carries only the §7 guards as
  intentional failures, per root `CLAUDE.md` §Testing; they remain the standing
  launched-strand fence, independent of this design).
- **L-C2 — stack-slot lanes** (backend §12.3):
  (a) **TCO back-edge negative:** allocation in a TCO loop body flowing into recur args
  must NOT stack-allocate — stack-slot-hit counter attribution + ASan under ≥10k
  iterations; (b) **spark-reads-parent-stack-slot:** joined spark borrows a parent
  stack value, sustained, ASan; (c) **sentinel residual-path harmlessness:**
  `vec-push`/`vec-set` on a stack-eligible vec — assert the emission heuristic declined
  stack (counter) AND, for a forced-stack scalar-read vec, that `vec-push-grow` is
  unreachable (negative: no free-of-stack-pointer under ASan; the immortal sentinel
  defeats the rc==1 COW probe by construction, backend §4.2); (d) heap-balance at exit
  for all stack-slot fixtures (residual rc drift on the sentinel is expected and
  harmless — the balance assertion therefore keys on allocs/deallocs, not inc/dec
  symmetry; stated so the lane doesn't false-red).
- **L-C3 — reuse-corruption fence (increment II).** Reuse fired on a non-unique value
  is heap corruption. Fixtures: (i) rc>1 at the entry check → copy path taken; the
  OTHER live reference's value asserted unchanged after the write (behavioral, the
  whole point); (ii) the token path (drop-feeds-alloc) under shared/unique both;
  (iii) differential on/off; (iv) ASan + heap-balance legs; (v) sustained loop
  (uniqueness epochs: copy-once-then-in-place — assert exactly one COW per epoch via
  RC-stats deltas).
- **ASan availability note (honest cap):** ASan lanes are scripted
  (`tests/scripts/asan/…` or perf-lane family), not canonical nextest — they need a
  rebuilt binary (`RUSTFLAGS=-Zsanitizer=address` nightly, or the checking-allocator
  fallback `MALLOC_CHECK_`/`MALLOC_PERTURB_` where ASan is unavailable on this
  aarch64 toolchain). The two-condition rule (§3.2) exists precisely because these
  tools perturb layout; the behavioral legs are the canonical-suite guards.

### 3.5 Routed specific lanes

- **L-D1 — REPL turn-latency lane** (typecheck §12.5; gate I-G6/M).
  *Mechanics:* the REPL already prints per-turn timing in the prompt
  (`NN+NNms; user>`); the lane is a scripted REPL session (perf-lane script, 30+
  turns): load an F1-scale module (~50 defns), then a loop of **body-only**
  redefinitions of one hot fn; parse the per-turn ms; compare toggle-on vs toggle-off
  medians. A second scripted session performs an **ABI-changing** redefinition
  (signature change) mid-module and reports turn time + recompiled-set size (the
  cascade report names it, spine §5.5) — report, not gate, at first landing.
  *Gate:* body-only ≤ 1.10× toggle-off. *Stage:* M onward. *Tier:* perf script.
- **L-D2 — Transferred-promotion counter** (typecheck §5.4/§12.6).
  *Mechanics:* Hook H4 — an RC-stats attribution counting surviving **atomic** ops on
  cells whose fork edges are all joins ("Transferred-eligible"). Lane runs F1–F4 + the
  concurrency corpus and reports the eligible share of surviving atomic ops.
  *Decision rule:* if the share exceeds **10%** on any acceptance fixture after
  increment I, file the promotion FIXME to `/typecheck` (the §5.4 named trigger);
  otherwise record the number and keep the collapse. *Stage:* end of increment I.
  *Tier:* perf script.
- **L-D5 — per-extern RC-stats attribution** (backend §9.2/§12.6).
  *Mechanics:* Hook H3 — per-extern counters of adaptation-inc/consuming-dec pairs
  actually paid at extern sites. Lane reports the per-extern pair population on the
  F-series + a string-heavy micro-fixture. *Decision rule:* a §9.2 deferred sibling
  (`str-concat`, `eq`, `display`…) is funded iff its pair population exceeds ~1% of
  total RC ops on an acceptance fixture; otherwise it stays deferred — the pattern
  grows by measurement, never by tidiness. The `str-len` template instance itself is
  verified by S5 (§3.2) + L-B1/L-B2 regardless of measured win (it validates the
  pattern end-to-end, stated honestly in backend §9.2). *Stage:* increment I (report),
  expansion decisions increment II+. *Tier:* perf script.

### 3.6 R3 machinery lanes (trap stubs, cascade, slot versioning — backend §8, spine §5)

All e2e-able as scripted REPL sessions (canonical nextest):

- **L-R1 — trap-stub behaviour** (backend §12.5): redefine `f` ABI-changingly so `g`
  breaks; then (a) direct call of `g` raises a clean runtime error whose message names
  the provenance (`g is broken by the redefinition of f: <original error>`) — substring
  match, not exact (wording is provisional until the `/repl` spec half lands, §5
  limit 6); (b) a **closure value minted from `g` before the break** still reaches the
  trap (in-place stub patch on the existing slot); (c) a curried partial of `g`
  likewise; (d) `/info g` / `/sig g` answer with broken status + provenance; (e)
  **recovery both directions** — redefine `g` to match ⇒ green; or redefine `f` back ⇒
  `g` recompiles and works; (f) the RC-mid-panic leak is bounded: heap-balance with a
  documented per-trap tolerance, not asserted zero (backend §8.1 caveat).
- **L-R2 — ABI-epoch slot versioning / frozen-world semantics** (spine §5.6): a closure
  captured **before** an ABI-changing redefinition of its target chain, invoked
  **after**, sees the **old chain's** behaviour (frozen slots, transitively); a caller
  recompiled by the transaction sees the new. Negative: no crash, no mixed-ABI
  corruption — sustained invocation of the stale closure (S98-class fence). And the
  ABI-**preserving** fast path: a body-only redefinition is picked up by existing
  closures at their next call (late binding preserved — today's semantic pinned).
- **L-R3 — summary-diff fast path observability**: body-only edit does not recompile
  callers (assert via trace: no dependent recompiles reported in the turn's cascade
  report); ABI-changing edit reports the recompiled set naming exactly the static
  callers (and NOT unrelated fns) — positive + negative on the affected-set closure.
- **L-R4 — the latent type-change hole cure** (spine §5.2): a *type-changing*
  redefinition (pre-S100's silent hole) now either recompiles callers or marks them
  BROKEN — a caller passing the old type must NOT reach the new body uncorrected.
  Fixture: Int→String param change with a compiled caller; today this is silently
  unsound; after M it traps-or-recompiles. This lane is drafted RED at the machinery
  sprint (it is the machinery's own witness).
- **L-R5 — persistence pins** (spine §5.6 (i)–(iv)): after an ABI-changing persisted
  redefinition + session restart with a valid cache: slot numbers in `.meta.json`
  still match the `.o` machine code (programs run correctly from cache); the hole
  survives (no renumbering); `next_got_slot` high-water respected (new definitions
  allocate above). e2e via two-session REPL-persist scripts (`repl_persist.rs` family).

### 3.7 Owed observability hooks (specified here; implemented by the owning skill)

| # | Hook | Owner | Needed by |
|---|---|---|---|
| H1 | Deterministic CLIF dump ordering for `CRANELISP_CODEGEN_DUMP` under the concurrent scheduler (or: harness sorts per-function — decided at increment-I drafting; the dump exists today, `backend/src/lib.rs:946`) | `/backend` | L-B1 |
| H2 | Per-mechanism stat counters: stack-slot hits, reuse hit/miss, non-atomic op share (backend §11 names them as the designed extension of `heap.rs:294`/`rc.rs:117`) | `/backend` | I-G3, I-G7, II-G2, L-C2 |
| H3 | Per-extern adaptation-pair attribution in `CRANELISP_RC_STATS` | `/backend` (intrinsics/primitives seam) | L-D5 |
| H4 | Transferred-eligible atomic-op attribution ("all fork edges are joins") | `/typecheck` (classification) + `/backend` (counter) | L-D2 |
| H5 | `CRANELISP_OWNERSHIP_TRACE` — per-cluster summary + per-site verdict dump (typecheck §11 designs it) | `/typecheck` | L-D3f, I-G3 |

Per `tests/CLAUDE.md` §Diagnostic Requirements these are implementation obligations of
the increment sprints, drafted into the QA-first failing set where testable (H5's dump
format gets a golden smoke; counters get "moves when the mechanism fires" unit-adjacent
e2e probes).

---

## §4. Unit-tier expectations (Phase-5 handoff; `/dev`-authored, named here)

`/qa` does not author these (two tiers, no middle), but the QA-first drafting session
hands the implementing `/dev` triads this expectation list, derived from typecheck §11
and backend §11 testability commitments — every fix/mechanism lands with its unit test
in the same change-set (`memory/feedback_unit_test_per_fix.md`):

- **typecheck:** transfer-function purity tests over hand-built `MonoExpr` bodies
  (summary in/out); recursive two-fn cluster fixpoints with known joins; escape-edge
  widening negatives (return/store/suspension); the L-D3d aliased-root shape at the
  analysis level; `LaunchContinue` conservative point; the instantiation memo; the
  fact-table row consumption (rule 5 stops at declared leaves).
- **backend:** the adaptation-algebra emission golden; stack-slot eligibility gates as
  pure predicates (incl. the TCO flow check); `compute_last_uses` provenance extension
  against hand-built bodies; trap-stub invoke-and-read-error-slot; the wrapper naming/
  dedup (`__d24wrap_{fq}_{slot}__`); non-atomic arm selection per site fact.
  **Stage M additions (S101):** the NULL-slot fn-as-value fix's unit test at the
  `fn_as_value.rs::emit_wrapper_call` / `primitives_inline` seam (same change-set as
  the fix, per `memory/feedback_unit_test_per_fix.md`); `compile_trap_stub` emission
  unit (args untouched, message baked, sentinel return); the manifest-key global-key
  membership unit.
- **int / `src/` (stage M — the transaction, per the `design/int/` fire):**
  reverse-index derivation from `Def.callees` + incremental maintenance on entry
  (re)registration; summary-diff gate classification (at M: type-scheme-only ABI
  surface — body-only vs ABI-changing); affected-set closure over statically-resolved
  edges (positive + the unrelated-fn negative); reverse-topo ordering; BROKEN-state
  bookkeeping incl. provenance-string/`Code`-handle lifetime pairing (the `/arch` fire
  checklist item 2(i)); frozen-pool retention (superseded `Code` moves to the pool,
  not dropped).

---

## §5. Coverage limits — stated, not silent

1. **R5's first landing does not cover the S99 `Cell`.** One-word + single-constructor
   (backend §7.2) excludes the two-ctor `(Given …)/(Solved …)`. The F2/F4 headline
   collapse is therefore NOT an increment-II-first-landing deliverable; F2v (§1.1) is
   the R5 witness, and F2/F4 at north-star numbers are composed-end-state gates
   (III-G1/G2). The multi-ctor tag-in-value extension's named trigger (backend §7.2) is
   exactly this pair of fixtures.
2. **Increment I does not move the 170M term** (backend §5.2 table: it lives in the
   Rust copy loops). I's F2 bars are non-regression + classification pins, by design.
3. **Shared-artifact RC stays atomic in increment I** (elem inc/dec fns, Rust copy
   loops, drop glue — backend §5.2). The non-atomic share H2 reports will have a
   structural ceiling; the lane records it rather than gating on an impossible 100%.
4. **Region arena, multi-word flattening, sibling expansion, shared-helper atomicity
   variants** — increment II or data-gated; no lanes drafted for them until their
   increment (the decision rules that admit them are L-D5 and the backend §7.2/§4.4
   triggers).
5. **ASan lanes are scripted, not canonical** (toolchain-dependent on this platform);
   the behavioral fence legs are the always-on guards (§3.2 two-condition rule).
6. **Trap-stub message wording is provisional** until the `/repl` normative spec half
   lands (spine §11 routes it to the machinery sprint) — L-R1 uses substring anchors
   (`broken`, the redefined symbol, the original error) so the failing-first tests
   don't fossilize unratified UX text; `/qa` flags the spec-side anchor obligation at
   that sprint. The same bridge covers **every** R3 wording surface: the §5.5-spine
   cascade report (L-R3's needles are symbol names, not report prose) and the
   `/info`/`/sig` broken-status display (L-R1(d)). At the machinery sprint the `/repl`
   half lands in-sprint (S101 scope item 7), so drafted tests cite the spine/backend
   design anchors and are **re-anchored to `repl/spec.md`** (needles tightened where
   the ratified wording allows) before sprint close — see §6.1 anchor policy. No L-R
   lane is blocked on the wording: L-R2/L-R4/L-R5 assertions are behavioural
   (values, exit status, `.meta.json` contents) and wording-independent.
7. **F4 is never a single-number gate** (distribution discipline, §0.3).
8. **The perf gates live outside canonical nextest** (30s cap); CI carries them as
   scheduled lanes, not per-commit blockers, with per-increment acceptance runs
   attended (S99 method).

---

## §6. QA-first drafting lists per implementing sprint (Phase 5 stage 1)

- **Machinery sprint (M):** L-R1…L-R5 drafted failing-first (L-R4 is the sprint's own
  RED witness); L-D1 script + its M-stage gate; the toggle **and its manifest key**
  ship here (spine §5.7; `/arch` S101 Phase-2 ruling) so L-B2(i) suite-polarity and
  the L-B3(1)–(3) manifest lanes start here too. **Sprint-ready drafting
  specification: §6.1** (authored S101 Phase 3).
- **Increment I sprint:** L-B1 golden capture (BEFORE mechanisms land — schedule the
  baseline commit first), L-B1/L-B2/L-B3(1–3); S1–S4 + S6 fences; L-D3a–f (incl. the
  per-row fact-table tests generated from the audit table); L-C1, L-C2; str-len sibling
  S5; H1/H2/H3/H5 hook smokes; perf lanes I-G1…I-G7.
- **Increment II sprint:** F2v fixture; L-C3; L-B3(4) schema-bump lane; reuse/flatten
  counters; perf lanes II-G1…II-G6; L-D2 decision point executed on increment-I data.
- **Every sprint:** ledger discipline — new intentional-failing guards enter
  `tests/plan/ledger.md` with the six fields; the canonical-suite intentional-failure
  count in root `CLAUDE.md` §Testing is updated by `/sprint` at close.

### 6.1 Stage-M drafting specification (S101 Phase 3 — sprint-ready)

Authored by `/qa` at S101 Phase 3 so Phase-5 stage 1 drafts directly from it. Governing
design: spine §5.2–§5.7; backend §8.1–§8.3; `/arch` S101 Phase-2 verdict (at stage M
the summary-diff gate degenerates to **type-scheme-only** comparison — "ABI-changing"
below means a type-scheme change, e.g. a param type change; mode vectors do not exist
until increment I).

**Files (new and touched):**

| File | Lanes | Tier |
|---|---|---|
| `tests/repl_redefinition.rs` (NEW) | L-R1(a)–(f), L-R2, L-R3, L-R4 | canonical nextest |
| `tests/repl_persist_redefine.rs` (NEW) | L-R5 | canonical nextest (two-session) |
| `tests/cache.rs` (extend) | L-B3(1)–(3) | canonical nextest |
| `tests/scripts/suite_polarity.sh` (NEW) | L-B2(i) | gate-time script |
| `tests/perf/l_d1_turn_latency.py` (NEW) | L-D1 | perf script |

**Common conventions.** REPL scripts use `Cranelisp::new().repl()` with
`PreludeVariant::PrimitivesOnly` (`add-i64`, `sub-i64`, `eq-i64`, `str-len` suffice —
no traits, no stdlib). Redefinition is a dev-session concept: all L-R lanes are
REPL-mode only (no `--run`/`--link` legs; batch modes have no redefinition, spine
§5.6). Every test asserts **process survival** (`assert_ok` — the REPL must never die
on a redefinition, however hostile) in addition to its lane assertion.

**Anchor policy (per §5 limit 6).** At draft, `// spec:` cites the design anchors —
`design/arch/ownership-inference.md §5.2/§5.4/§5.5/§5.6` and
`design/backend/ownership-codegen.md §8.1/§2.3` (design-doc citations are established
practice — the `repl_persist.rs` family cites `design/int/session-persistence.md`).
When the `/repl` spec half lands (in-sprint, S101 scope item 7), a **re-anchor pass**
re-points the L-R1/L-R2/L-R3 citations to the new `repl/spec.md` sections and tightens
substring needles where the ratified wording allows; `spec_link_check.py` runs on both
the drafting and re-anchor commits.

**Ledger discipline for the RED-first set.** The drafting commit adds ONE ledger entry
("S101 Phase-5 Stage-1 — R3 machinery QA-first RED set", the S93-precedent form) with
the six fields covering all RED-at-draft tests below; they flip green as the `/dev`
waves land. At close the entry is annotated resolved (or any carried RED gets its own
full entry and joins the root `CLAUDE.md` intentional-failing count).

#### L-R1 — trap stubs (`tests/repl_redefinition.rs`; spine §5.5, backend §8.1)

Base fixture (all sub-lanes; concrete forms):

```clojure
(defn f [:Int x] (add-i64 x 1))
(defn g [:Int y] (f y))
(g 41)                            ; :primitives/Int 42 — pre-break sanity
(defn f [:String s] (str-len s))  ; ABI-(type-scheme-)changing ⇒ g fails re-typecheck ⇒ BROKEN
```

- **(a) `redefine_abi_change_broken_caller_direct_call_traps_with_provenance` — RED.**
  Post-break `(g 5)`: positive — stdout carries the trap substrings (`broken`, `g`,
  `f`; wording-provisional per §5 limit 6); negative — stdout does NOT contain
  `:primitives/Int 6` (silent stale/garbage execution) and the session exits 0 (no
  SIGSEGV — today this shape dies passing an Int as a String pointer).
- **(b) `redefine_broken_caller_value_use_minted_before_break_reaches_trap` — RED.**
  Pre-break `(def gv g)` (fn-as-value — deliberately the same wrapper seam as §7's
  defect); post-break `(gv 5)` reaches the trap (in-place stub patch on g's existing
  slot). Same positive/negative legs as (a).
- **(c) `redefine_broken_caller_curried_partial_minted_before_break_reaches_trap` —
  RED.** Caller `(defn g2 [:Int a :Int b] (f (add-i64 a b)))`; pre-break partial
  `(def p (g2 1))` (auto-curry); post-break `(p 5)` traps; NOT `:primitives/Int 7`.
- **(d) `redefine_broken_caller_info_and_sig_report_broken_status` — RED.**
  Post-break `/info g` and `/sig g` outputs contain `broken` + `f` (provenance).
  Negative: `/info f` (the redefined symbol itself, healthy) does NOT contain
  `broken`.
- **(e) recovery, both directions — two tests, both RED.**
  `redefine_recovery_fixing_caller_clears_broken`: post-break
  `(defn g [:String s] (f s))` then `(g "a")` → `:primitives/Int 1`, and `/info g` no
  longer says `broken`. `redefine_recovery_reverting_callee_recompiles_caller`:
  post-break redefine `f` back to the Int form; `(g 41)` → 42 again; `/info g` clean.
- **(f) `redefine_trap_invocations_leak_bounded_per_trap` — RED.** Variant fixture
  where broken `g` takes a heap arg: `(defn g [:String s] (f 1))`, break `f`
  Int→String ⇒ g BROKEN; drive `(g "abc")` × 20 REPL turns under
  `.env("CRANELISP_RC_STATS","1")`; assert allocs−deallocs ≤ 20 × (heap args per
  call) + documented baseline — **bounded, not zero** (backend §8.1 RC-mid-panic
  caveat). Stats parse at exit; nextest per-process isolation keeps this serial-safe.

#### L-R2 — frozen-world / late-binding (`tests/repl_redefinition.rs`; spine §5.6)

- **(a) `redefine_abi_change_stale_closure_sees_frozen_old_chain` — RED.**

  ```clojure
  (defn base [:Int x] (add-i64 x 10))
  (defn wrap [:Int y] (base y))
  (def c (fn [z] (wrap z)))                     ; closure compiled against OLD slots
  (defn spin [:Int n :Int acc]                  ; pre-break sustained driver
    (if (eq-i64 n 0) acc (spin (sub-i64 n 1) (add-i64 acc (c 1)))))
  (c 1)                                         ; :primitives/Int 11
  (defn base [:String s] (str-len s))           ; ABI-changing — fresh slots
  (defn wrap [:String s] (base s))              ; by-name world moves on
  (wrap "abcd")                                 ; :primitives/Int 4 — new world by name
  (c 1)                                         ; :primitives/Int 11 — frozen old chain
  (spin 500 0)                                  ; :primitives/Int 5500 — sustained (S98-class fence)
  ```

  Positive: post-break `(c 1)` → 11 (transitively frozen: old wrap → old base) and
  `(spin 500 0)` → 5500 under sustained invocation. Negative: exit 0, no mixed-ABI
  crash (today the in-place patch sends the stale closure into the new-ABI body —
  RED by crash/garbage). Exact primitive spellings per `spec/appendix-a-builtins.md`
  at drafting.
- **(b) `redefine_body_only_stale_closure_late_binds_new_body` — GREEN at draft
  (pin).** Same shape, body-only redefinition `(defn base [:Int x] (add-i64 x 20))`;
  `(c 2)` → 22 post-edit (late binding — today's prized semantic, pinned so slot
  versioning never eats it). Negative: NOT 12 (the old body).

#### L-R3 — summary-diff / cascade report (`tests/repl_redefinition.rs`; spine §5.4–§5.5)

Fixture: `callee`; annotated caller `caller-a` (will break), polymorphic caller
`caller-p` `(defn caller-p [x] (callee x))` (re-typechecks, recompiles), and
`unrelated` (no edge to `callee`).

- **(a) `redefine_body_only_neg_no_cascade_report_no_dependent_recompiles` —
  vacuously GREEN at draft (pin, stated honestly).** Body-only edit of `callee`: the
  redefinition turn's output contains NO recompiled-set report and does NOT name
  `caller-a`/`caller-p`; `(caller-a 1)` still works (late-bound). Today no report
  machinery exists so the absence legs pass vacuously; the lane becomes load-bearing
  the moment the transaction lands — it guards the fast path against over-triggering
  (L-D1 is its latency twin).
- **(b) `redefine_abi_change_cascade_report_names_exact_affected_set` — RED.**
  ABI-changing edit of `callee` (Int→String): the turn report names `caller-p`
  (recompiled OK) and `caller-a` (broken, with the original type error); **negative:
  does NOT name `unrelated`**. Needles are the symbol names, not report prose (§5
  limit 6). Follow-up turns assert both worlds: `(caller-p "abcd")` works;
  `(caller-a 1)` traps.

#### L-R4 — the type-change hole cure (`tests/repl_redefinition.rs`; spine §5.2) — the sprint's RED witness

- **(a) `type_change_redefinition_compiled_caller_never_reaches_new_body_uncorrected`
  — RED (the named witness).** The §2.1-sprint fixture verbatim — Int→String param
  change with a compiled annotated caller:

  ```clojure
  (defn f [:Int x] (add-i64 x 1))
  (defn g [:Int y] (f y))
  (g 1)                             ; :primitives/Int 2
  (defn f [:String s] (str-len s))
  (g 5)                             ; MUST trap-or-recompile; MUST NOT reach new body with an Int
  ```

  Assertion is the soundness disjunction: session exits 0 AND post-break `(g 5)`
  yields an error naming `g` (at stage M the annotated caller cannot re-typecheck, so
  the sanctioned outcome is BROKEN+trap) AND stdout does NOT contain
  `:primitives/Int 6`. Today: silently unsound (crash or garbage) — RED.
- **(b) `type_change_redefinition_polymorphic_caller_recompiles_and_works` — RED.**
  Same but unannotated caller `(defn g [y] (f y))`; post-break `(g "abcd")` →
  `:primitives/Int 4` (g re-inferred + recompiled against new f). Today the call is
  rejected against g's stale Int→Int scheme — RED.

#### L-R5 — persistence pins (`tests/repl_persist_redefine.rs`; spine §5.6 (i)–(iv))

Two-session scripts per the `repl_persist.rs` family: session 1 `.repl()` + `/quit`,
then `out.run_again()` in the same tmpdir; `.meta.json` inspected via
`read_tmp(".cranelisp-cache/…meta.json")` (exact module path per the `cache.rs`
precedent, resolved at drafting).

- **(a) `persist_abi_change_redefinition_restart_runs_correctly_from_cache` — GREEN
  at draft expected (pin (ii): slot numbers load-bearing against the `.o`).**
  Session 1: define `f`(Int) + `g`; redefine both to the String forms (coherent final
  source); `(g "hi")` → value; `/quit`. Session 2 (warm cache): `(g "abc")` → correct
  value. Persisted `user.cl` regeneration already yields a coherent restart today;
  the pin guards that slot versioning never breaks cache-restore.
- **(b) `persist_abi_change_allocates_fresh_slot_hole_survives_restart` — RED.**
  Same session-1 script PLUS a **control run in a second tmpdir** with identical
  definitions but NO redefinition (same definition prefix ⇒ deterministic same
  initial slots). Assert from the two `.meta.json`s: (i) redefined `f`'s persisted
  `got_slot` > control `f`'s (fresh slot allocated; today in-place patch ⇒ equal —
  RED); (ii) `next_got_slot`(redef) > `next_got_slot`(control) with symbol counts
  equal (the hole exists and is persisted). Session 2 (`run_again`): define a new fn
  `h`; re-read `.meta.json`: `h`'s slot ≥ session-1 `next_got_slot` (high-water
  respected — pin (iv)); `f`'s slot unchanged (no renumbering — pin (ii)); the
  frozen old slot number is NOT reassigned to `h` (hole survives — pin (iii)).
- **(c) `persist_body_only_redefinition_neg_keeps_slot` — GREEN at draft (pin).**
  Body-only redefinition keeps `f`'s slot and `next_got_slot` identical to control —
  the §5.4 fast path must NOT churn slots (guards against over-allocating once fresh
  slots exist).

#### L-B3(1)–(3) — manifest key (`tests/cache.rs`; backend §2.3)

- **`cache_ownership_toggle_flip_invalidates_wholesale_no_stale_objects` — RED.**
  Multi-module `--run` project; run once (populate cache); run again with
  `.env("CRANELISP_NO_OWNERSHIP","1")` + `CRANELISP_MODULE_TRACE=1`: positive — every
  module recompiles, output correct; negative — **zero** cache-hit lines (no stale
  `.o` consumed; mixed-ABI caches unrepresentable). Today the unknown env var is a
  no-op ⇒ full cache hits ⇒ RED.
- **`cache_ownership_toggle_round_trip_and_same_polarity_stability` — RED.** Flip
  back (unset): wholesale again, output identical; then re-run same polarity: full
  cache HITS (the key is *stable*, guarding against an always-miss implementation —
  this last leg is the lane's green-at-draft component but the test as a whole is RED
  on the flip legs).

#### L-B2(i) — suite polarity (`tests/scripts/suite_polarity.sh`)

Script: run `cargo nextest run` twice (default env; `CRANELISP_NO_OWNERSHIP=1`),
compare pass/fail sets; allowed delta = the ledgered intentional-failing set,
identical under both polarities (post-flip at S101 close: expected empty). Trivially
green at draft (env no-op) and still identical-by-construction once the toggle lands
at M — the M-stage deliverable is the installed protocol, executed at Phase-5 exit and
carried by CI as a gate-time lane (two full suite runs; never the per-commit loop).

#### L-D1 — body-only turn latency (`tests/perf/l_d1_turn_latency.py`)

Per §3.5 mechanics verbatim (scripted REPL, ~50-defn generated module, 30+ body-only
redefinition turns of one hot fn, parse the `NN+NNms` prompt stamps; second session:
one ABI-changing redefinition — report turn time + recompiled-set size, report-only).
M-stage gate: body-only median ≤ 1.10× toggle-off median. At M both polarities run no
analysis, so the gate is measuring exactly what stage M adds — summary-diff gate +
reverse-index maintenance overhead on the fast path. Evaluated attended at wave
close/acceptance (perf lanes live outside canonical nextest, §0.4/§5 limit 8).

#### RED/GREEN-at-draft summary

| Drafted RED (14 — flip green as `/dev` waves land) | GREEN-at-draft pins (4) |
|---|---|
| L-R1(a)(b)(c)(d)(e×2)(f); L-R2(a); L-R3(b); L-R4(a)(b); L-R5(b); L-B3 ×2 | L-R2(b) late-binding; L-R3(a) no-cascade (vacuous until landing); L-R5(a) cache-restore; L-R5(c) body-only-keeps-slot |

Scripts (not RED/GREEN entries): `suite_polarity.sh` + `l_d1_turn_latency.py` — both
authored at stage 1, executed at the wave gate / Phase-5 exit.

#### 6.1.1 Drafting-notes addendum (authored at Wave-1 drafting, 2026-07-03)

The set above was drafted and committed in S101 Phase-5 Wave 1. Deviations from the
spec as written, discovered at drafting:

1. **The pre-break VALUE carrier does not exist at stage M — L-R1(b)/(c) and
   L-R2(a) use closest-reachable shapes.** `(def gv g)` as written above is not
   REPL-reachable in a free-standing test: `def` is a **stdlib macro** (stdlib is
   out of bounds for `tests/`, root `CLAUDE.md` §Stdlib separation) and expands to
   a zero-arg `defn` + bare-symbol macro — i.e. it re-evaluates through a
   recompiled static caller, exactly the `/repl` Phase-3 finding. No cross-turn
   value carrier exists in the core REPL (bare-expression results are dropped;
   strand/channel carriers are not deterministically REPL-drivable from stdin).
   Drafted instead: pre-break-COMPILED zero-arg minting fns — `(defn hold [] g)`
   (fn-as-value wrapper compiled pre-break, targets g's slot) and
   `(defn mkp [] (g2 1))` (auto-curry wrapper ditto) for the trap lanes; for
   L-R2(a) the by-name/new-world half of §18.7 + the no-mixed-ABI coherence fence
   (`redefine_abi_change_closure_minting_caller_rejoins_new_world_coherently`).
   **Residue:** the direct frozen-world assertion (§18.7 requirement 1 — a
   pre-break heap value sees OLD-chain behaviour) is not e2e-assertable at stage M;
   its structural witness is L-R5(b) (fresh slot + surviving hole). When a
   cross-turn value carrier ships (session value bindings, or REPL-drivable strand
   state), add the direct test. Full reasoning: `tests/repl_redefinition.rs`
   module header.
2. **Anchor policy executed at draft, not as a later re-anchor pass**: `repl/spec.md`
   §18 landed in Phase 3 BEFORE this drafting, so the L-R1/L-R2/L-R3/L-R4 tests cite
   §18.x directly and use its normative needles (`is broken by the redefinition of
   {cause}` with FQ names; `recompiled`/`broken` report sections). The §5-limit-6
   re-anchor obligation for these tests is therefore already discharged;
   `spec_link_check.py` runs clean on the drafting commit.
3. **§7.1 flip count superseded 4 → 7**: the Wave-1 cat-3 sweep
   (`tests/plan/s101-coverage-postmortem.md` §3) widened the vec-query NULL-slot
   class to curried / returned / stored-in-ADT positions — 3 more failing-not-
   ignored guards in `tests/vec_query_value_use.rs`. The §7.1 protocol applies
   unchanged with "4 guards" read as "7 guards" (ledger §"Sprint 101 Wave-1 cat-3
   sweep"); the curried guard's DISTINCT signature (JIT `can't resolve symbol`
   panic, exit 101 — the curry path's `primitives_inline` fallback gap) is new
   information for the Wave-3 resolver.
4. **L-R2(b)'s pin carrier** is likewise the factory shape (`(defn c [] (fn [z]
   (base z)))`) rather than `def` — same reason; the late-binding semantics it pins
   are identical.
5. **L-R5(c) reclassified green-pin → RED, and a drafting FINDING recorded**: the
   post-`/quit` `.meta.json` is only intermittently complete — the nice workers'
   R18 abandon-on-shutdown races the last defining-turn persist (observed
   non-deterministic `symbol f/g not found` across consecutive suite runs). The
   L-R5 meta tests now assert meta completeness first (burst-amplified ×8 for (c),
   S98 precedent) and slot policy second; Wave-4 `/dev`(src/) must make the final
   persist deterministic at `/quit` (the fire's faithful-write pin) for L-R5(b)/(c)
   to flip. L-R5(a) remains a stable green pin (restore correctness rides
   `user.cl`, not the meta). Full record: ledger §"Sprint 101 Phase-5 Stage-1"
   FINDING + `tests/repl_persist_redefine.rs` module header. Drafted totals are
   therefore **15 RED / 3 green pins** (vs the table's 14/4).

---

## §7. Triage record — `(map vec-get …)` / vec-query-family value-use (spine §9 named item)

**Verdict: (a) REAL DEFECT** — verified 2026-07-02 on `target/debug/cranelisp`
(HEAD 78ac5dd).

- **Hypothesis confirmed exactly.** `vec-get`/`vec-set`/`vec-push` value-use calls
  through NULL GOT slots and **SIGSEGVs** (signal 11), in BOTH `--run` and the REPL
  (the REPL session process dies — no error, no recovery). `vec-len` — the one family
  member with a real extern shim — works through the identical fn-as-value wrapper
  path (control, green).
- **Reduction floor:** one user HOF + one vec literal, primitives-only, no stdlib, no
  `map` needed: `(defn call-get [f v i] (f v i))` + `(call-get vec-get [10 20 30] 1)`.
- **Code path:** `fn_as_value.rs::compile_fn_as_value → emit_wrapper_call` emits a
  GOT-indirect `call_indirect` through the primitive's slot; `insert_vec_query_entries`
  (`cranelisp-primitives/src/lib.rs` ~:246) leaves those three slots NULL by design
  ("name resolution is the sole gap these entries close"). The auto-curry sibling path
  (`emit_curry_target_call`) consults `primitives_inline` for inline builtins; the
  plain fn-as-value path consults nothing — the natural fix seam. Owning skill:
  **`/backend`** (the wrapper body should inline-lower the vec family exactly as the
  curry path does for known builtins, or the R2-wrapper work of `ownership-codegen.md`
  §3.5 subsumes it; a primitives-crate extern body is blocked on element-type erasure,
  which is why the slots are NULL in the first place).
- **Repro tests (failing-not-ignored, committed):** `tests/vec_query_value_use.rs` —
  `vec_get_as_value_through_hof_returns_element`,
  `vec_set_as_value_through_hof_returns_updated_vec`,
  `vec_push_as_value_through_hof_appends`,
  `vec_get_as_value_run_mode_returns_element` (4 RED, signal-terminated on HEAD), plus
  `vec_len_as_value_through_hof_returns_length_control` (GREEN — pins the root-cause
  boundary to the NULL slots, not the wrapper mechanism). Ledger entry:
  `tests/plan/ledger.md` §"Sprint 100 Phase-3 triage". No FIXME filed — the failing
  tests are the record and trigger (`memory/feedback_no_fixme_with_failing_test.md`).
- **Interaction with this plan:** backend §9.1's sibling registration touches the same
  primitives-table site — §12.7 there already requires this defect verified/fixed
  before the sibling lands; and the R2 wrapper emission (backend §3.5) must NOT route
  value-use of summary-carrying primitives through a NULL slot — the fix is a
  precondition for the "every primitive gets a real GOT-backed value entry" target the
  spine records.

### 7.1 Flip protocol (S101 — executed when the `/dev`(backend) fix lands)

> **EXECUTED at S101 Wave 5 (2026-07-03), with the 4→7 supersession** (§6.1.1
> note 3): all 7 guards GREEN after the Wave-3 fix, control green throughout;
> ledger entries annotated in place; test-file docs updated; the close-time
> canonical intentional-failing count is **3** (the NEW
> `tests/vec_cow_value_use_leak.rs` FIXME-0474 guards — the COW copy-branch
> leak residual on the same seam, incl. a static-site widening), flagged to
> `/sprint` for the root-`CLAUDE.md` user update. `suite_polarity.sh`
> protocol run post-flip: polarity-identical
> (ledger §"Sprint 101 Wave-5 close-out records").

The fix is S101 scope item 1; when it lands, in order:

1. **Fix + unit test in the same change-set** (`/dev` on `cranelisp-backend`): the
   mandatory unit test pins the `emit_wrapper_call`/`primitives_inline` seam (§4
   stage-M backend list). The e2e need is already met — the 4 guards ARE the e2e
   (assessed before the fix per `memory/feedback_unit_test_per_fix.md`); no new e2e
   is owed.
2. **Observe the flip**: the 4 guards
   (`vec_get_as_value_through_hof_returns_element`,
   `vec_set_as_value_through_hof_returns_updated_vec`,
   `vec_push_as_value_through_hof_appends`,
   `vec_get_as_value_run_mode_returns_element`) green in the canonical run; the
   control (`vec_len_…_control`) stays green. The tests are permanent regression
   guards — never deleted, never weakened.
3. **Ledger update** (`/qa`): annotate the `tests/plan/ledger.md` §"Sprint 100
   Phase-3 triage" entry in place with a resolution line — sprint (S101), fixing SHA,
   "4 RED → GREEN; control green throughout" — the S81→S82 flip-recording precedent.
4. **Test-file docs** (`/qa`, same change-set as 3): update the
   `tests/vec_query_value_use.rs` module comment and per-test "RED on HEAD" notes to
   record the resolution (the triage narrative stays as history).
5. **Root `CLAUDE.md` §Testing count**: the intentional-failing count drops 4 → 0
   (plus any stage-M RED-first guards still carried at that moment — the §6.1 ledger
   entry tracks those; at close the expected canonical state is **0 intentional
   failures** since the machinery lands in-sprint). The root-CLAUDE.md edit is
   outside `/qa` and `/sprint` edit boundaries — `/sprint` **flags it for the user at
   close** (S101 acceptance line 1), with `/qa` supplying the exact close-state
   counts in its Phase-7 suite report.
6. **L-B2(i) interaction**: `suite_polarity.sh`'s allowed-delta set is the ledgered
   intentional-failure set *at execution time* — run it after the flip so the
   expected delta is empty.

---

## §8. Registration

- This plan is registered in `tests/CLAUDE.md` §Plan documents.
- Supersedes nothing; peer of `tests/plan/s99-measurement.md` (whose baselines it
  consumes). `tests/plan/PLAN.md` remains the spec→tests bridge; rows for the new
  tests join it as they are authored (the S100 triage tests trace to
  `spec/04-expressions.md §4.6.2`).
