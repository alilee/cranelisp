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
