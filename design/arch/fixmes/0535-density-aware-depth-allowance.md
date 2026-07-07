---
number: 0535
target: /design
filed_by: /qa
filed_at: 2026-07-07
sprint_filed: 104
refers_to: design/backend/lenient-eval.md §2.8, design/arch/effect-concurrency.md §3.1, tests/plan/s104-utilization-measurement.md §8.7 (U-G1 regrade)
status: open
---

# Density-aware depth allowance — gate the depth budget on alloc/RC density (the S105 focus)

## Issue

S104 shipped a uniform depth cap `CRANELISP_SPARK_MAX_DEPTH = floor(log2(nproc))`
(= 3 on the 10-core host) with worker-origin depth decline + backoff. Graded
single-shot at the D3 default (§8.7):

- **F6** (heavy balanced pure compute): 3.10s → **0.82s (3.4×)**, peak ≈ 12 — the
  Regime-A win. The thesis is proven **here**.
- **F5** (fib D&C): 0.67s → **0.39s (1.7×)**, spawns 619K → ~14 — compute-parallel win.
- **F4-hard** (alloc-contended search): 0.88s serial → **~2.27s at D=3**; the
  ≈24× over-sparking pathology is cured (13.1M → ~16 spawns), but F4 stays
  **above serial** and is a mild floor regression vs D=1.
- **F3** (alloc-contended search): 0.53s → **~3.7s** — same class.

A **single uniform depth** cannot satisfy both regimes at once. The value that
lets alloc-free strands go deep enough to win (F6-class wants deep) is the same
value that lets alloc-heavy strands recurse into contention (F4/F3-class wants
shallow). D=3 is the compromise that buys F6 (accepted per user trade) at the
cost of a mild F4/F3 floor slip. This is the **U-G1 second half** — F4 not at
≤ serial — regraded out of S104's utilization scope and into this synthesis.

The residual F4/F3 wall is NOT scheduling overhead (0534 proved the pathology
term was rayon park/wake per over-spark, now cured by the cap). It is the
**alloc/RC-density contention class** — per-branch heap allocation + atomic-RC
cache-bouncing (`effect-concurrency.md` §3.1; Decision 13) — which the depth cap
bounds spark *count* but does not attack per-branch.

## Proposed resolution

**Gate the depth allowance on the static alloc/RC-density signal**, so the depth
budget is a *function of the strand's density*, not a machine-wide constant:

- **Alloc-free / RC-quiet strands** (F6's `spin` tail-loop, F5's pure `fib`) —
  allow deep recursion up to (or beyond) `floor(log2(nproc))`: no contention to
  create, so more depth = more fill = more win.
- **Alloc-heavy / RC-loud strands** (F4/F3's copy-per-guess + fine accessor
  traffic) — hold the depth allowance shallow (toward D=1), so parallel does not
  drive the copy/atomic-RC firehose into contention. Near-serial is the correct
  answer for this class.

This is the **S104-utilization × §3.1-contention synthesis** the sprint work-list
names as the S105 focus (user-directed 2026-07-07). The density signal is the
same static allocation/RC-density axis `effect-concurrency.md` §3.1 already calls
for as the "contention-aware gate, static layer first" (the FIXME-0459 line), and
`lenient-eval.md` §2.8 is where the utilization depth mechanism lives — the two
must be joined: §2.8's depth allowance consults the §3.1 density classifier.

## Operational implication / Context

- The measurement basis is `tests/plan/s104-utilization-measurement.md` §8 (F1–F6
  single-shot walls) + §8.7 (the final acceptance + U-G1 regrade). F4/F3 are the
  witnesses for the shallow arm; F6/F5 for the deep arm — the fixtures already
  discriminate the two regimes by shape (U-G4 held), so they are the acceptance
  instrument for a density-aware depth.
- The trade F4 pays at D=3 (mild floor slip vs D=1) is accepted for S104 to keep
  the F6 win; the density-aware depth is the path that recovers F4 *without*
  surrendering F6 — the goal S105 grades.
- Scope note: this is the *static* density layer (backend cost-heuristic feeding
  the depth allowance). The structural cures (thread-local RC / escape→stack/region
  / reuse) remain Phase-H per Principle 8 and are NOT pulled forward — this FIXME
  is the in-track density-gate path, not the Phase-H cure.
- `/design` (or `/arch` — owner's call which holds the §2.8 × §3.1 join) actions
  by editing `lenient-eval.md` §2.8 + `effect-concurrency.md` §3.1; the resulting
  `/dev(cranelisp-backend)` implementation is graded against the §8 F1–F6 lanes.
