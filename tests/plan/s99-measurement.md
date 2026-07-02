# Sprint 99 Wave 0.3 — parallel-contention measurement report

**Author:** `/qa` · **Date:** 2026-07-02 · **Status:** Wave-0 payload deliverable
(the funding decision the mechanism waves depend on).

Decomposes the observed "lenient/speculative-parallel Sudoku ~10× slower than
serial" into its real terms, on the **release** backend, using the Wave-0.1/0.2
knobs. Built falsification-first: to be able to prove the hypothesis wrong.

**Hypothesis under test (arch/scope):** `10× = serial-luck × speculative-waste ×
contention`; only contention is substrate-fixable; contention ≈1.4× and splits
into **(a) allocator-lock (sys)** vs **(b) atomic-RC cache-line bouncing (user)**;
arch prior R1: sys-dominance ⇒ **(a) the larger term**.

**Verdict (one line):** the hypothesis is **partly FALSIFIED and partly
CONFIRMED**. The 10× is **essentially ALL contention** — serial-luck and
speculative-waste **cancel** (the serial baseline is itself speculative) and
machinery is negligible. Contention is **larger than 1.4×** (3× on a clean
fixed-size probe, up to **23× on the real Sudoku**) and is a **MIX with (b)
atomic-RC dominant**, not (a): (b) is 70–99% of the contention; (a) allocator-lock
is a real but secondary term that appears only with varied/deep allocation and is
cheaply cured by the allocator swap. **Fund BOTH cures, sequenced: allocator swap
first (cheap, kills (a)), then capture-by-borrow (the larger prize, kills (b)).**
This is **not** the refutation/"stop" branch.

---

## 1. Method

- **Fixtures** (`tests/fixtures/s99/`, free-standing, zero-stdlib, nested-ADT — a
  `Vec` of heap-allocated `Cell` ADTs; NO bitmask dodge):
  - **F1 `f1_machinery`** — D&C reduce, trivial leaf (reads shared cells, no copy)
    → pure spark/IVar/pool machinery tax.
  - **F2 `f2_contention`** — IDENTICAL D&C reduce tree, but each leaf does K
    `vec-set` copies of the **shared** grid (COW copy of the N-cell Vec + fresh
    `Cell` + refcount bump on every retained cell). All results consumed (reduce,
    no speculative waste). Clean contention probe. `(F2 − F1)` = contention.
  - **F3 `f3_inverted_search`** — same heavy copy work, `first-success` combiner,
    winner is the LAST leaf → best-case parallel-upside probe.
  - **F4 `f4_sudoku`** — real backtracking 9×9 Sudoku on the nested-ADT grid
    (free-standing port of `exemplar/{grid,solver}.cl`), the confounded reference.
- **Harness** `tests/perf/s99_measure.py` (NOT in canonical nextest). Sweeps each
  fixture × {serial `CRANELISP_NO_LENIENT=1` / 1-worker `RAYON_NUM_THREADS=1` /
  N-worker} × {system / mimalloc `--features thread-caching-alloc`} × {atomic /
  non-atomic `CRANELISP_NONATOMIC_RC=1` (1-worker only, indicative)}, collecting
  wall/user/sys (`/usr/bin/time`) median-of-3, plus `CRANELISP_RC_STATS` counts.
- **Synthetic scale** LEAVES=8192, COPIES=256 (serial ≈0.7s, N-worker ≈2.2s).
- **Alloc/RC counts are process-wide** — there is **no `reset_counts()` seam on
  the `--run` path** (confirmed: `src/main.rs` `Action::Run` calls `trampoline`
  with no pre-main reset; `cranelisp_intrinsics::alloc::reset_counts()` is public
  but unreferenced on that path). Program-attributable counts = raw − a
  no-op `--run` baseline (baseline: rc_inc=0 rc_dec=1 allocs=1 deallocs=1).
- **Machine:** 10 cores (`nproc=10`), release binaries.

---

## 2. Timing matrix (median wall / user / sys, seconds)

Clean, deterministic fixtures (F1/F2/F3). F4-hard N-worker is intentionally shown
as a range — heavy contention makes its timing chaotic (see §3).

| fixture | alloc | serial (wall/user/sys) | 1-worker | N-worker |
|---|---|---|---|---|
| F1 machinery | system | 0.02 / 0.01 / 0.00 | 0.02 / 0.02 / 0.00 | 0.02 / 0.06 / 0.00 |
| F2 contention | system | 0.72 / 0.36 / 0.29 | 0.72 / 0.97 / 0.27 | **2.22 / 19.18 / 0.47** |
| F2 contention | mimalloc | 0.64 / 0.30 / 0.28 | 0.66 / 0.83 / 0.28 | 1.85 / 15.54 / 0.71 |
| F3 inv-search | system | 0.73 / 0.37 / 0.30 | 0.73 / 0.96 / 0.30 | 2.26 / 19.46 / 0.50 |
| F3 inv-search | mimalloc | 0.66 / 0.29 / 0.30 | 0.66 / 0.84 / 0.30 | 1.77 / 14.82 / 0.65 |
| F4 hard | system | 0.90 / 0.67 / 0.19 | 1.34 / 2.12 / 0.25 | **wall 3.3–20.7, user 20–54, sys 2.7–27** |
| F4 hard | mimalloc | 0.92 / 0.64 / 0.23 | 1.14 / 1.86 / 0.20 | wall 5–33, user 42–194, sys 1.7–25 |

Cleanest single F4-hard N-worker pair (least-contended scheduling): **system
20.97 / 53.74 / 27.30** vs **mimalloc 4.37 / 37.67 / 1.20** — mimalloc collapses
**sys 27.3→1.2 (23×)** and **wall 21→4.4 (4.8×)**.

## 3. RC-op + alloc counts (system, serial; program-attributable)

| fixture | rc_inc | rc_dec | allocs | deallocs |
|---|---|---|---|---|
| F1 machinery | 2,129,921 | 81 | 82 | 81 |
| F2 contention | **169,902,081** | 81 | **4,194,386** | 0 |
| F3 inv-search | 169,934,847 | 81 | 4,202,578 | 0 |
| F4 hard | 52,576,384 | 1,662 | 12,764,604 | 301,694 |

**Volume claim confirmed to the digit.** F2 does 8192×256 = 2,097,152 shared
copies → rc_inc / copies = **81.0 rc_inc per copy** (= grid size N; every retained
cell's refcount is bumped) and allocs / copies = **2.0 allocs per copy** (new Vec
buffer + new `Cell`). This is exactly the "~81 RC bumps + fresh cells per copy per
node" claim. F4-hard: 52.5M rc_inc + 12.7M allocs from copy-per-guess.

> Note (side finding, not central): F2/F3 show rc_dec=81, deallocs=0 — the
> per-leaf temporaries are not decremented/freed promptly (they accumulate to
> ~4.2M live allocs until exit). rc_inc/allocs are the reliable contention-volume
> signal; the dec/dealloc asymmetry is a deferred-free/tally-path observation
> worth a backend glance but does not change the contention conclusion.

---

## 4. The six isolations

**1. Machinery tax `(1-worker − serial)`, zero cross-core contention.**
F1: +0.01s user, wall unchanged — the pure spark/IVar/rayon-pool machinery is
**negligible** at this granularity. F2: +0.61s user (0.36→0.97), wall unchanged —
this is the atomic-RC *instruction* + thunk cost on 170M single-threaded RC ops,
NOT contention (no cross-core bouncing with one worker). **Machinery is not a
term in the 10×.**

**2. Contention `(N-worker − 1-worker)` on F2.**
wall +1.50s (0.72→**2.22**, i.e. parallel is **3× SLOWER**, not faster);
**user +18.2s** (0.97→19.18); sys +0.20s. On a reduce where serial and parallel do
identical total work, N-workers burn **18× the CPU** and run **3× slower** —
contention is real, large, and dominates. (F3 identical: +18.5s user.)

**3. user-vs-sys split of the N-worker contention delta = (a) vs (b).**
- F2 (fixed-size alloc): user +18.2 vs **sys +0.20 → ≈99% (b) atomic-RC (user)**,
  ≈1% (a) allocator (sys).
- F4-hard (serial→N-worker): user +≈41 vs sys +≈17 → **≈70% (b), ≈30% (a)**.
- **(b) atomic-RC bouncing is the dominant, universal term.** (a) allocator-lock
  is a real but secondary term that only appears with varied-size / deep-recursion
  allocation (the real Sudoku), absent in the fixed-size probe. **This corrects
  arch prior R1** (which expected (a) dominant from the sys-heavy *debug* ladder):
  on release, contention is user/(b)-dominated.

**4. mimalloc vs system on N-worker = how much the allocator swap alone recovers.**
- F2: 2.22→1.85 wall (17%), user 19.18→15.54 — **small**, because F2's (a) is ≈0.
- F4-hard: best run **sys 27.3→1.2 (23×), wall 21→4.4 (4.8×)** — the allocator swap
  recovers the **bulk of (a)** in the real Sudoku. Residual after mimalloc is
  user-dominated (b) and still ≈5× slower than serial. **mimalloc is a large,
  near-free partial cure for the real workload and a no-op where (a) is absent.**

**5. non-atomic vs atomic @ 1-worker = the atomic *instruction* cost.**
F2 user 0.95→0.83 (−13%); F4-hard 2.12→2.05 (−3%). The atomic instruction itself
is **cheap uncontended**. The expensive (b) is the **contended cache-line
bouncing** (isolation 2's +18s), which capture-by-borrow removes by **not emitting
the RC ops at all** on structurally-joined shared-parent captures — so its
recoverable win is the ≈18s contended term, far above this −13% instruction cost.

**6. RC/alloc counts** — §3: **81 rc_inc + 2 allocs per shared copy**, confirmed
exactly; F4-hard 52.5M rc_inc / 12.7M allocs. The copy-per-node volume is the
direct driver of both (a) and (b).

---

## 5. Reconciliation: F4 vs F1/F3 — is the 10× contention, or waste/luck?

**The 10× is ALL contention.** Three legs:

1. **Machinery (F1) ≈ 0** — not a term.
2. **serial-luck and speculative-waste CANCEL.** The "serial" the sprint measured
   against is `CRANELISP_NO_LENIENT=1` on the *same speculative code*. Cranelisp's
   lenient eval **forces both args of `first-success` before the call — there is
   NO early exit** (proven: F3-serial does the same work as F2-serial, and F3
   evaluates all branches even though only the last wins; and NO_LENIENT still
   evaluates every branch). So a real early-exit backtracker's "serial luck" is
   **unavailable in this model**, and speculative-waste is **paid equally by both
   the serial and parallel baselines** → both cancel in the lenient-vs-serial
   ratio. **They are NOT terms in the measured 10×.** (They are real costs of the
   speculative *approach* vs a hypothetical optimal early-exit solver — but that
   is a different comparison than the one the sprint set out to explain.)
3. **Contention IS the whole ratio, and it reaches/exceeds 10×:** F4-hard
   N-worker/serial = **up to 23×** (system), ≈5× after mimalloc; F2 (pure (b),
   fixed-size) = 3×. The magnitude gap F2(3×) → F4(23×) is exactly the added (a)
   allocator-lock (varied/deep allocation) plus deeper recursion (more shared-cell
   bouncing).

**Corollary — the 10× is a debug artifact in *magnitude* but not in *structure*.**
The original 10× was a debug number; on release the real Sudoku is still **5–23×
slower parallel**. A Phase-H release backend alone does **not** fix it — the
substrate contention cures are needed.

**Honest "slight-discount-per-core" witness (F2):** today N-worker is **3× slower**
per the reduce, NOT a slight discount. The target performance model (near-serial
per core) is **not met** until contention is cured. Projection: removing the
81-per-copy shared-cell RC bumps (capture-by-borrow) collapses F2's 18s user
contention; the allocator swap collapses F4's sys term; only then is a real
per-core discount achievable, and only then does the saturation gate (0459)
convert the now-cheap branches into speedup.

---

## 6. Decision table — verdict

| Measurement outcome | Funds | This measurement? |
|---|---|---|
| (a) allocator-lock dominant | allocator swap ± arena | Partial — (a) is real & cheaply cured, but SECONDARY |
| (b) atomic-RC bouncing dominant | capture-by-borrow | **YES — (b) is the dominant/universal term** |
| contention small, waste/luck dominant | mostly 0459 | **NO — waste/luck cancel; contention is large** |
| contention dominant even at saturation | STOP → Phase H | **NO — both cheap pre-Phase-H cures apply** |

**Verdict: a MIX, fund both, sequenced (matches arch R2/R3):**

- **FUND FIRST — thread-caching global-allocator swap (a-cure).** Kills the
  allocator-lock (sys) term that dominates the real Sudoku's excess (best run:
  sys 23×↓, wall 4.8×↓). Near-free, byte-identical-off, survives Phase H
  (region allocator subsumes it). **Per R2, try this before any per-worker arena**
  — the swap already recovers the bulk of (a); an arena stays contingent-on-
  contingent. In F2 it is correctly a no-op (no (a) present), so it is precisely
  targeted at allocator-lock.
- **FUND — capture-by-borrow across structured fork-join (b-cure).** The DOMINANT
  contention term is atomic-RC cache-line bouncing on shared-parent-cell
  refcounts (F2: 99% of contention; F4: 70%; the residual after mimalloc, ≈5×).
  The atomic *instruction* is cheap (isolation 5) — the cost is contended
  bouncing, which the coarse borrowed-Var generalization eliminates by not
  emitting the ops on structurally-joined captures. Higher implementation risk
  (bug-#2 class per arch ruling 2) → **coarse version only**, within the FIXME
  0461 boundary (structural-join gate; return-value-only retain; no per-capture
  escape analysis; excludes `LaunchContinue`).
- **COMPLEMENTARY — saturation gate (0459).** Contention intensity scales with the
  number of branches concurrently copying/bouncing. A saturation-shaped gate
  (spark iff spare capacity, inline-when-saturated) directly throttles (b)'s
  cross-core bouncing AND converts the now-cheap branches into real speedup. It is
  scheduling, not memory — survives Phase H.
- **NOT the "stop" branch.** Contention is not intractable-only-in-Phase-H: the two
  cheap cures are complementary (allocator kills (a); capture-by-borrow kills (b))
  and together should restore the near-serial-per-core floor. Refutation branch
  obligations still met regardless (per R5): the F1–F4 fixtures land as committed
  guards (`tests/s99_fixtures.rs`, parallel≡serial), and the doc-scope/floor
  corrections land independently.

---

## 7. Artifacts

- `tests/fixtures/s99/{f1_machinery,f2_contention,f3_inverted_search,f4_sudoku}.cl`
  — free-standing fixtures (committed).
- `tests/s99_fixtures.rs` — committed **parallel≡serial correctness guards**
  (4 tests, all green; F4 uses a solved grid to stay fast under the debug binary;
  F2/F3 carry the spark/search-path guard). Canonical suite: **1802 pass / 1 skip
  / 0 fail** (1798 baseline + 4).
- `tests/perf/s99_measure.py` — the measurement harness (NOT in canonical nextest).
  `SYS_BIN=… MI_BIN=… python3 tests/perf/s99_measure.py [--reps N] [--quick]`;
  builds/points at the two allocator-variant release binaries.

---

## 8. Wave 1b — capture-by-borrow ablation result (the deliverable)

**Author:** `/dev`(backend) · **Date:** 2026-07-02 · **Status:** Wave-1b ablation
payload — the A/B that decides whether the `CRANELISP_CAPTURE_BORROW` toggle
flips default-on at sprint close.

**Setup.** Release build, **system allocator** (the cure is allocator-independent).
Capture-by-borrow across structured fork-join (FIXME 0461; `ring2-rc.md` §5.5.2,
`lenient-eval.md` §4.4.1) implemented behind `CRANELISP_CAPTURE_BORROW=1`
(byte-identical-off; canonical suite unaffected — **1807 pass / 1 skip / 0 fail**).
Median of 5 reps, `/usr/bin/time`, `LEAVES=8192 COPIES=256`, 10 procs, N-worker =
rayon default. rc_inc via `CRANELISP_RC_STATS`.

### Numbers (N-worker, off → on)

| fixture | wall off→on | user off→on | sys off→on | rc_inc off→on (drop) |
|---|---|---|---|---|
| F1 machinery | 0.02→0.01 | 0.04→0.04 | 0.00→0.00 | 2,130,924→2,129,921 (**−1,003**) |
| **F2 contention** (clean probe) | 2.06→2.10 | 17.86→18.16 | 0.42→0.44 | 169,902,978→169,902,081 (**−897**) |
| F3 inverted search | 2.11→2.11 | 18.18→18.29 | 0.44→0.44 | 169,935,424→169,934,847 (**−577**) |
| F4-hard sudoku | 13.75→7.25 † | 41.47→29.58 † | 17.38→7.55 † | 52,599,528→52,576,384 (**−23,144**) |

### Verdict — capture-by-borrow **alone recovers ~0% of the (b) contention** on F1–F4.

1. **The mechanism is correct but the volume is negligible.** The toggle does elide
   exactly the structurally-joined spark-capture incs — with it on, the parallel
   `rc_inc` drops to **== the serial `rc_inc`** (F2: 169,902,081 both), confirming
   the borrow removes precisely the spark-capture incs and nothing else. But that
   drop is **897 of 170M (0.0005%)** on F2, **−577/−1,003/−23,144** on F3/F1/F4 —
   three-to-five orders of magnitude below the contention it was funded to remove.
2. **Why: the §5.5.2.6 volume prediction was wrong.** The prediction was
   `rc_inc drops ≈ captures-per-spark × spark-count ≈ leaf-count × capture-arity`.
   In reality (a) the **create-gate budget caps spark count far below leaf count**
   (bounded `O(cap)`, §3.6), and (b) capture-arity is ~1 (the shared grid `g`). So
   the elided incs number in the **hundreds**, not the millions. The **dominant (b)
   atomic-RC traffic is the LEAF copy-work** — each `(vec-set g …)` COW-copies the
   81-cell Vec and **bumps every retained `Cell`'s refcount** (~81 incs × 256 copies
   × thousands of leaves ≈ the 170M) — and those bumps are **inside the computation,
   not spark captures**, so capture-by-borrow does not touch them.
3. **F2 (the clean, low-variance probe) is the honest headline: user-time is FLAT**
   (17.86→18.16, within noise; sys flat; wall flat/slightly up). Capture-by-borrow
   removes **none** of F2's measured contention.
4. **† The F4-hard wall "1.9×" is a FALSE GREEN — search-path variance, not the
   borrow.** F4-hard N-worker wall is dominated by speculative-backtracking
   scheduling: verified across single reps, **OFF spans 4.99–16.66 s and ON spans
   3.38–18.41 s** — fully overlapping. The 5-rep median simply caught an OFF-high /
   ON-low draw. With `rc_inc` moving only 0.04%, the wall delta **cannot** be
   attributed to capture-by-borrow (per `memory/feedback_verify_fix_not_symptom_absence.md`).

### Implication for the close-time default-on decision

On this evidence **do NOT flip `CRANELISP_CAPTURE_BORROW` default-on for a
performance reason** — it recovers no measurable (b) contention on F1–F4. The
implementation is sound (byte-identical-off, parallel≡serial, the mandatory
`LaunchContinue`-exclusion + heap-balance + inc-drop guards all green) and the
borrowed/owned classification is *permanent* and Phase-H-durable (§5.5.2.5), so it
can land as a correct, zero-cost-off substrate; but the **(b) prize is elsewhere**:
the vec-COW leaf refcount traffic. Candidate real (b)-cures on this evidence:
(i) owned-copy mutate-in-place / last-use on the freshly-COW'd grid so the per-copy
cell-refcount bumps are avoided (a §5.5 last-use extension, not a capture rule);
(ii) the saturation gate (FIXME 0459) to throttle the *number* of branches
concurrently bouncing those cell cache-lines. This finding is filed to `/design` +
`/sprint` (the §5.5.2.6 volume prediction needs correction; the b-cure funding
should re-point at the leaf-copy RC term). Raw ablation: 5-rep medians above,
`scratchpad/ablation.py` methodology (mirrors `s99_measure.py` + a CAPTURE_BORROW axis).

---

## 9. Wave 1c — saturation-gate ablation result (the deliverable)

**Author:** `/dev`(backend) · **Date:** 2026-07-02 · **Status:** Wave-1c
measurement spike — does a saturation-shaped spark gate cut the (b) atomic-RC
cache-line bouncing by confining saturated subtrees to one thread?

### Mechanism (minimal, reuses the existing correct inline path)

The create-gate (`lenient-eval.md` §3.6) *already* emits the spark-vs-inline
choice: `cranelisp_spark_budget_try_reserve(n)` → **granted ⇒ lenient arm
(spark)**, **rejected ⇒ direct arm (the existing fully-sequential inline
lowering)**. The saturation gate is therefore **not** new eval logic — it is a
one-line **cap-policy** change on the *same* reservation. `CRANELISP_SATURATION_GATE=1`
(`ivar.rs`, byte-identical-off) tightens the in-flight-spark cap from the default
`4 × threads` static budget to **exactly `threads`**: a batch is granted only
while a worker is free right now (`in_flight < threads`); once the pool is
saturated the reservation is rejected and the branch runs **inline on the current
thread** via the unchanged direct arm. Because the inline path is the pre-existing
sequential lowering and both arms produce byte-identical values, correctness holds
on/off by construction (no soundness/UAF surface — unlike 1b). The gate does **not**
change the RC-op *count* (F2 rc_inc 169.90M both, F4 52.60M both); it can only
change *where* the ops run (thread-local vs bouncing).

### Numbers (N-worker, system alloc, 7 reps, per-rep spread shown)

| fixture | config | wall (min/med/max) | user (min/med/max) |
|---|---|---|---|
| **F2** (clean probe) | 1-worker | 0.72 / 0.72 / 0.73 | 0.93 / 0.94 / 0.95 |
| F2 | N-worker gate **OFF** | 1.98 / 2.10 / 2.24 | 17.11 / **18.13** / 19.46 |
| F2 | N-worker gate **ON** | 1.91 / 1.95 / 2.01 | 16.27 / **16.52** / 17.22 |
| F2 | N-worker ON+borrow | 1.91 / 1.98 / 2.01 | 16.35 / 16.76 / 17.14 |
| **F4-hard** | 1-worker | 1.17 / 1.28 / 1.42 | 1.91 / 2.03 / 2.18 |
| F4-hard | N-worker gate **OFF** | 3.72 / **6.05** / 17.81 | 21.96 / **28.17** / 43.78 |
| F4-hard | N-worker gate **ON** | 3.31 / **15.83** / 21.25 | 16.74 / **32.43** / 37.89 |
| F4-hard | N-worker ON+borrow | 2.78 / 15.58 / 26.02 | 15.92 / 34.72 / 43.27 |

- **F2 (the honest, low-variance headline):** user-time contention delta
  `(Nworker_OFF − 1worker) = 17.19s`; gate recovers `18.13 − 16.52 = 1.61s`
  = **≈9% of the (b) contention**; wall 2.10→1.95 (**≈7%**). The per-rep spread is
  **tight and consistently ordered** — ON's *max* user (17.22) sits **below** OFF's
  *median* (18.13), and every ON rep beats the OFF median. This is a **real,
  reproducible effect, not a false green** — but small.
- **F4-hard: inconclusive — variance swamps the signal.** Median user swings the
  *wrong* way (−4.26s, −16%), but the per-rep spread is enormous and fully
  overlapping (wall OFF 3.72–17.81 vs ON 3.31–21.25; ON's *min* wall 3.31 actually
  beats OFF's min 3.72). This is exactly the 1b F4 false-green trap: F4-hard
  N-worker wall/user is dominated by speculative-backtracking scheduling, so the
  medians are draws, **not** a gate effect. **Do not read F4-hard as either help or
  harm.** (rc_inc unchanged ⇒ nothing algorithmic moved.)
- **Gate × capture-borrow (1b) interaction:** ON+borrow ≈ ON on F2 (16.76 vs 16.52,
  within noise) — no additive win, consistent with 1b recovering ~0% and the gate's
  small win being orthogonal to the (already-negligible) spark-capture incs.

### Verdict — the gate is a **real but marginal** (b) mitigation, NOT a cure; NOT a false-green.

1. **Directionally correct and honest.** On the clean F2 probe the gate removes a
   small, consistent slice (~9% user / ~7% wall) of the (b) cache-line bouncing by
   confining the *overflow* (11th–40th) subtrees to their own thread. rc_inc is
   unchanged, confirming the win is pure locality, exactly the hypothesised
   mechanism — just small.
2. **Why only ~9%.** Bounding concurrency from `4×threads` (40) to `threads` (10)
   inlines only the *deep overflow* sparks; the **top ~10 concurrent branches still
   run in parallel and still COW-copy + refcount-bump shared ancestor cells** — and
   that steady-state cross-core sharing over 10 cores is the bulk of the 170M-bump
   bouncing. Capping at N (vs 4N) barely changes it because the cores are saturated
   either way. The gate throttles the *number* of bouncers at the margin; it cannot
   touch the leaf-copy RC *volume* (which is what actually drives (b), per §8's
   re-diagnosis).
3. **This reinforces the FIXME-0462 conclusion → the dominant (b) is genuinely
   Phase-H.** Neither in-scope scheduling/borrow cure moves the F2 (b) term more
   than single-digit percent: 1b ≈0%, 1c ≈9%. The real lever is the **vec-COW
   leaf-refcount volume itself** — owned-copy mutate-in-place / last-use / Perceus
   reuse on the freshly-COW'd grid — which is Phase-H memory-model work, not
   scheduling. The gate is worth keeping as a cheap, sound, Phase-H-durable
   *complement* (it is honest scheduling hygiene and restores the never-much-slower
   floor), but it is **not** a standalone (b) fix and does not clear the
   near-serial-per-core bar on its own.

### Disposition
- Implementation: `CRANELISP_SATURATION_GATE=1` in `ivar.rs` (cap = worker-count),
  OFF by default, byte-identical-off. Canonical `cargo nextest run`: **1811 pass /
  1 skip / 0 fail** (pre-1c 1804 + 3 unit + 4 e2e = +7; no regressions).
- Tests: unit — `ivar/tests.rs::{saturation_gate_effective_cap_policy,
  saturation_gate_budget_grants_iff_spare_capacity,
  saturation_gate_env_caps_spark_budget_at_worker_count}` (pure cap/grant policy +
  env wiring); e2e — `s99_fixtures.rs::s99_f{1..4}_saturation_gate_parallel_equals_serial`
  (result-equivalence + no-signal heap guard, toggle ON).
- **Do NOT flip default-on for a performance reason** on this evidence (F2 ~9% is
  small; F4 inconclusive). It is sound and cheap, so it may land opt-in; a
  default-on decision is `/design`+`/review`'s at close, and would rest on the
  floor-restoration/honesty argument, not the (b)-cure magnitude.
- Raw ablation: 7-rep min/med/max above; `scratchpad/ablation_1c.py` (mirrors
  `s99_measure.py` + a `CRANELISP_SATURATION_GATE` axis + per-rep spread).

---

## 10. Wave 1d — mimalloc (a)-cure benchmark + combined shippable stack (the deliverable)

**Author:** `/qa` · **Date:** 2026-07-02 · **Status:** Wave-1d measurement — benchmark
the already-built mimalloc `#[global_allocator]` (Wave 0.2, `--features
thread-caching-alloc`) PROPERLY (Wave 0's "F4 sys 27→1s" was one cherry-picked
best run) and recommend adoption posture. **Benchmark-only — no production source
change.** Two release binaries: system (`cargo build --release`) vs mimalloc
(`… --features thread-caching-alloc`); the saturation gate composes with either
(runtime env, byte-identical-off, compiled into both). Canonical `cargo nextest
run` re-verified **1811 pass / 1 skip / 0 fail** (unchanged — 1d adds only a
non-compiled harness `tests/perf/s99_measure_1d.py`). `LEAVES=8192 COPIES=256`,
10 procs, `/usr/bin/time`. **F1–F3 fixed-work: 7 reps. F4-hard variable-work:
7 reps in the matrix + a dedicated 11-rep per-rep sweep (below) because F4's
speculative-backtracking search path makes even sys-time work-variable.**

> **Discipline note (`memory/feedback_verify_fix_not_symptom_absence`):** F4-hard
> wall/user/sys are ALL search-path-variable (each run backtracks a different
> amount → different total work), so *no* F4 metric is variance-immune — the
> report's "lead with sys" holds only for the **fixed-work** probes (F1–F3).
> Accordingly this section leads with **F2 (clean, fixed-work)** and treats every
> F4 number as a **distribution**, never a single median. The Wave-0 "27→1s (23×)"
> is confirmed to have been a **cherry-picked best-run pair** — see §10.1.

### 10.1 The clean (a) recovery — system vs mimalloc, N-worker

**F1–F3 (fixed-work, 7-rep min/med/max):**

| fixture | metric | system N-worker | mimalloc N-worker | mimalloc effect |
|---|---|---|---|---|
| F1 machinery | wall/user/sys | 0.02 / 0.04 / 0.00 | 0.02 / 0.04 / 0.00 | none (no alloc volume) |
| **F2 contention** (clean probe) | wall | 2.05 / **2.11** / 2.20 | 1.69 / **1.76** / 1.81 | **−17%** |
| F2 | user | 17.62 / **18.16** / 19.00 | 14.18 / **14.81** / 15.31 | **−18% (non-overlapping)** |
| F2 | **sys** | 0.45 / **0.46** / 0.50 | 0.57 / **0.59** / 0.65 | **+28% (WORSE)** |
| F3 inv-search | wall/user/sys | 2.13 / 18.41 / 0.46 | 1.66 / 13.90 / 0.59 | −22% wall / −24% user / +sys |

**The clean-probe headline overturns the Wave-0 framing.** On F2 (identical total
work serial vs parallel, fixed-size allocation) mimalloc's entire win is
**user-time** (−18%, tight and non-overlapping) — and it **slightly WORSENS sys**
(+28%). **There is no (a) allocator-lock *sys* term on the fixed-work probe at all**
(F2 sys is ~0.5s of an 18s-user / 2.1s-wall run either way). mimalloc helps F2 by
making the *user-mode* alloc path cheaper (thread-local caches cut alloc CPU) — a
per-thread-throughput win any modern allocator gives, **not** a lock-contention
(sys) collapse. This is a materially different mechanism than "collapse sys" — and
it is modest (~18%).

**F4-hard (variable-work) — dedicated 11-rep per-rep sweep, N-worker:**

| metric | system (med / min / max) | mimalloc (med / min / max) | median ratio |
|---|---|---|---|
| wall | **13.94** / 3.83 / 23.98 | **5.40** / 3.34 / 16.22 | 2.6× faster |
| user | **40.81** / 22.03 / 57.84 | **43.27** / 26.35 / **98.92** | 0.94× (mimalloc WORSE) |
| **sys** | **17.72** / 3.17 / 32.30 | **2.64** / 1.10 / **12.26** | **6.7× lower** |
| total CPU (user+sys) | 58.9 | 45.4 | 1.30× lower |

**F4 findings (all read as distributions):**

1. **The (a) sys term is REAL and large on F4, and mimalloc addresses it — but
   ~6.7× at the median, not 23×.** mimalloc's *entire* sys distribution
   (1.10–12.26) sits below system's *median* (17.72); the reduction is the most
   directionally-reliable F4 signal. **The Wave-0 "sys 27.3→1.2 (23×)" is confirmed
   a cherry-picked best-run pair** — the honest robust (a) sys recovery is **~6.7×
   median**, with single-rep pairs able to *look* like ~20× (system 23.01 vs
   mimalloc 1.10) only by matching a system-unlucky rep to a mimalloc-lucky one.
2. **mimalloc does NOT help user-time on F4 — it makes it WORSE (median 40.8→43.3,
   tail 57.8→98.9).** Combined with F2's user-*win*, this exposes a **coupling
   between (a) and (b): removing the allocator serialization (sys↓) lets threads
   run concurrently and bounce the shared-cell atomic-RC cache lines MORE (user↑).**
   mimalloc trades (a) kernel-lock sys for extra (b) user cache-bouncing. On the
   fixed-work F2 the alloc pattern is uniform so the user-side alloc-throughput win
   dominates (net user↓); on the deep/varied-alloc F4 the freed-up concurrency
   feeds (b) (net user↑). This coupling is why F4 *wall* improves far less than the
   6.7× sys reduction implies.
3. **Net F4 median: wall 2.6× faster, total-CPU 1.30× lower — a real but
   variance-obscured win** (wall spreads overlap: system min 3.83 < mimalloc median
   5.40). "mimalloc collapses F4" is an overstatement; "mimalloc cuts F4 kernel-lock
   sys ~6.7× and nets a ~2.6× median wall improvement, while shifting some cost into
   (b) user-bouncing" is the honest claim.

**Answer to "sys-only or also user?"** Allocator-dependent: on fixed-work (F2)
mimalloc's win is **user-only** (and sys slightly worse); on varied/deep-alloc (F4)
it is **sys-only** (6.7× down) while user gets **worse** via the (a)/(b) coupling.
There is no regime where mimalloc helps both.

### 10.2 The combined shippable stack — mimalloc + saturation gate (0459)

Baseline (system alloc, default create-gate) vs **mimalloc + `CRANELISP_SATURATION_GATE=1`**, N-worker, 7-rep min/med/max:

| fixture | stack | wall | user | sys |
|---|---|---|---|---|
| **F2** | system, no-gate | 2.05 / **2.11** / 2.20 | 17.62 / **18.16** / 19.00 | 0.45 / 0.46 / 0.50 |
| F2 | **mimalloc + gate** | 1.61 / **1.68** / 1.71 | 13.49 / **14.01** / 14.20 | 0.58 / 0.61 / 0.65 |
| **F4-hard** | system, no-gate | 6.20 / 9.70 / 20.12 | 27.55 / 34.57 / 52.23 | 6.96 / 11.83 / 26.38 |
| F4-hard | mimalloc + gate | 4.87 / 12.80 / 23.52 | 34.28 / 48.53 / 69.03 | 4.36 / 13.90 / 27.55 |

- **F2 (honest combined recovery):** mimalloc+gate cuts wall **2.11→1.68 (−20%)**
  and user **18.16→14.01 (−23%)**. Decomposed: mimalloc ≈ −18% user, saturation
  gate ≈ −5% more on top (consistent with 1c's ~9% standalone, partly subsumed once
  mimalloc has sped the alloc path). **The honest "how much can we recover
  pre-Phase-H" number on the clean probe is ~20–23%.**
- **F4 combined-cell: variance too high to read** (this 7-rep cell drew hard: wall
  9.70→12.80, sys 11.83→13.90 both worse; the dedicated 11-rep sweep §10.1 shows the
  real mimalloc F4 direction is favourable at the median). **Per the discipline, do
  NOT read the F4 combined medians as a result** — the reliable F4 (a) signal is the
  isolated 11-rep sys distribution (6.7× median), not this variance-swamped cell.

### 10.3 Where the floor lands — combined stack vs serial

| fixture | serial (wall/user/sys med) | combined mimalloc+gate (med) | wall slowdown vs serial |
|---|---|---|---|
| **F2** (clean) | 0.74 / 0.36 / 0.31 | 1.68 / 14.01 / 0.61 | **2.3× SLOWER** |
| F4-hard | 0.88 / 0.64 / 0.19 | 5.40–12.80 / 43–49 / 2.6–14 | **~6–15× SLOWER** |

**The "never dramatically slower than serial" floor is NOT restored by the combined
stack.** After mimalloc + saturation gate, F2 parallel is still **2.3× slower** than
serial (was ~2.9× pre-cure) and F4 remains **6–15× slower**. The residual is exactly
the **Phase-H (b) vec-COW leaf-refcount term** — the ~81-RC-bumps-per-copy in-leaf
traffic (§3, §8) that neither in-scope cure touches: capture-by-borrow ≈0% (§8),
saturation gate ≈9% (§9), mimalloc user-neutral-to-worse on the clean probe (§10.1).
Three independent pre-Phase-H levers each move the dominant (b) term single-digit
percent → **the (b) driver is confirmed genuinely Phase-H (Perceus / owned-copy
mutate-in-place / non-atomic RC), consistent with FIXME 0462.** The floor-scoping
doc correction (0459 doc half) stands: "near-serial per core" is a post-Phase-H
target, not a pre-Phase-H one.

### 10.4 Recommendation

**mimalloc adoption posture — KEEP OPT-IN (`--features thread-caching-alloc`); do
NOT flip default-on this sprint.** Rationale:

1. **The honest win is modest and regime-dependent.** Clean fixed-work probe: ~18–23%
   user/wall (user-side alloc throughput, not lock-collapse). Varied-work F4: a real
   ~6.7×-median sys reduction, but **variance-obscured and partly given back as (b)
   user-bouncing** via the (a)/(b) coupling (§10.1.2) — net median wall 2.6× with
   fully-overlapping spreads.
2. **It does not clear the floor.** The dominant residual is Phase-H (b) (§10.3);
   mimalloc is a partial (a) cure for a term that is *secondary* on the clean probe
   and coupled-to-(b) on the real workload.
3. **Default-on carries a real cost:** a **vendored-C mimalloc build dependency
   (via `cc`) on EVERY build**, plus cross-platform build-surface risk — paid by all
   users to buy a modest, workload-dependent, Phase-H-subordinate win.
4. **Posture:** land/keep it behind the feature flag, documented as the recommended
   toggle for **allocation-heavy parallel** workloads (where the F4 sys term bites).
   **Revisit default-on once Phase-H lands the (b) cure** — with (b) removed, the (a)
   sys term becomes the visible bottleneck and mimalloc's value rises; the C-build-dep
   trade then flips favourable. Byte-identical-off means the opt-in costs nothing to
   carry until then.

**Native alternatives (Ferroc / rimalloc) — NOT worth chasing this sprint;
Phase-H-adjacent follow-on.** The *measured* (a) win does not justify pursuing a
dependency-free rust-native allocator now: (i) on the clean probe there is no (a) sys
term to cure (the win is user-side, which the system allocator nearly matches); (ii)
on F4 the (a) sys win is real but variance-obscured, partly clawed back by (b), and
subordinate to the Phase-H (b) residual that actually gates the floor; (iii) a native
allocator's whole selling point over mimalloc is *dropping the C dep* — worth it only
if we commit to default-on, which (per above) we should not until Phase-H. **Evaluate
Ferroc/rimalloc alongside the Phase-H region-allocator work**, when (a) becomes the
visible bottleneck and a default-on dep-free allocator earns its keep — not against
today's modest, (b)-dominated numbers.

### 10.5 Artifacts
- `tests/perf/s99_measure_1d.py` — the 1d harness (NOT in canonical nextest): system
  vs mimalloc × {serial, N-worker} + the mimalloc+gate combined stack + floor table,
  per-rep min/med/max. `SYS_BIN=… MI_BIN=… python3 tests/perf/s99_measure_1d.py [reps]`.
- Raw: §10.1/§10.2 7-rep matrix + the F4-hard 11-rep per-rep sys/user/wall sweep above.
- Canonical suite re-verified **1811 pass / 1 skip / 0 fail** (1d adds no compiled test).
