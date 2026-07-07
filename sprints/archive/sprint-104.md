# Sprint 104: Lenient Eval — the Utilization Thesis

**Status**: PHASE 5 → 7 — mechanisms built + measured + reviewed + consolidated; authoring Outcome

**Wave-2 progression (the measurement-driven convergence):** 2 (M-dynamic cap `6dbed5a`) → *finding: cap doesn't bound spawn count (permits recycle)* → 2b (structural hierarchical decline `af358ad`) → *finding: both-paths form harmful (peak 2)* → 2c (worker-only decline `b2c6122`) → *finding: F3 7.5× slower* → 2d (IVar-force backoff `45e58fc`) → *finding: F3 is contention, not spin; backoff halves CPU, wall-neutral* → 2e (depth-allowed decline, D=`floor(log2 nproc)`=3 `e3644ca`) → **F6 3.4×, F5 1.7×, pathology cured**. `/review` of the net machinery: CLEAN (SPARK_DEPTH cross-spawn + backoff both CORRECT; no Blocker/Important). Consolidation: `/arch` §3.1.5, `/qa` §8.7 + FIXMEs 0535/0536, `/design` §2.8 as-built + §2.8.7 measurement-strategy + §2.8.8 open-problems.

**Measurement doctrine (user direction 2026-07-07):** chasing order-of-magnitude wins ⇒ precision is premature. Per-wave attribution = **single-shot runs** (T=10, 1 rep, wall + `spawns=`), ~90s total — NOT the reps/distribution/idle-guard/thread-sweep harness (which spent ~1h measuring a 2-min runtime; its idle-guard is self-defeating during a sweep). The rigorous harness is **deferred to final acceptance** only.

**Goal**: Replace the falsified "spark every non-cheap Apply" model with a **core-utilization** model — dispatch a small number (~2/core) of distinct, probably-large work items that separate onto different cores and then run forward on a high-efficiency sequential path — and prove it by measurement, building both admission mechanisms (static + dynamic) with independently-attributed effect.

## Thesis (the reframe, user-directed 2026-07-06)

**The goal is keeping all cores doing useful work, NOT fine-grained parallelism.** The target behaviour: a *small* number of distinct, substantial work items — on the order of **~2 per core** — that **separate** from each other onto different cores, each then running forward on an **efficient sequential path**. Populate the cores, then get out of the way.

The current model does the opposite: a purely *syntactic* filter (`is_worth_sparking` = "a non-cheap `Apply`") emits **millions of tiny sparks clustered at the work frontier** that never separate and never amortize their ~13µs spawn/park cost against a ~20ns body. FIXME 0534 profiled this precisely on F4-hard: 9.45M sparks, wall ≈ serial + `spawns × per-spark-overhead`, ~600× overhead-to-work ratio, cores parked in futex (240% CPU on 10 cores) rather than computing.

**The design hole:** the language has a *create-gate* (bounds concurrent IVar count → memory) but no *utilization gate* (are cores already busy? is this piece big enough to be worth separating?). It estimates neither the benefit nor the cost of a spark. The evidence says the win is narrow and coarse: on F4-hard, admit-all runs 24s at 565% CPU (cores **busy**) entirely on ~10 coarse divide-and-conquer sparks, while the 104 fine accessor sparks are pure overhead. Utilization, not parallelism, is the lever.

## The two mechanisms (both built this sprint; effects measured independently)

**Their division of labour, corrected by the Phase-2 arch review:** M-static governs spark **quality** (spark coarse, not fine); M-dynamic governs **quantity** and owns the ~2/core collapse. **Neither alone clears F4** — M-static does *not* deliver hierarchical decline structurally (a divide-and-conquer recursion is non-tail-recursive at *every* level, so M-static re-selects spark sites all the way down — the `fib`-explosion shape). The ~2/core collapse is **entirely M-dynamic's**. Grade F4 as an M-static × M-dynamic *interaction*, not a sum (§Stage 4).

- **M-static — spark only probably-large work (quality axis).** Replace the syntactic non-cheap-Apply filter with a structural "large work" signal: **non-tail recursion** (callee in a recursive SCC ∧ apply not in tail position). This selects the divide-and-conquer / recursive forks (F1 `fib`/`reduce-tree`, F4 coarse `solve-range`) and rejects flat non-recursive accessor pairs (F4's 104 `(cell-at g i)` sparks). Uses the existing Decision-21 `callees` call graph + `in_tail_position` — **backend-internal, no new cross-crate interface, no runtime, no ABI change** (arch-confirmed).
- **M-dynamic — bail out of sparking when cores are already busy (utilization axis; owns ~2/core).** A cheap runtime *utilization* signal that inlines a spark site when cores are already busy. **Arch ruling: this rides the EXISTING `IN_FLIGHT_SPARKS` counter + `cranelisp_spark_budget_try_reserve` (a lower/utilization-tuned cap), NOT a new "executing-sparks" counter** — "inline when busy" is a re-parameterization of the create-gate's existing decision, and standing up a competing counter violates Principle 8 / the FIXME-0442 one-counter ruling. **No new C-ABI symbol expected**; `/design` Stage 1 must *justify* one if the reserved-vs-executing gap proves to matter — the only pre-approved shape then is `cranelisp_spark_executing_count() -> i64` (riding the Stage-3 cascade the budget symbol did). The saturation-gate's prior ~9% result is *not* counter-evidence: it was measured with B4 still declining the coarse sparks, so the pool never latched busy; with M-static feeding coarse strands, the same mechanism latches.
- **Hierarchical decline (the connective invariant).** Once a strand is dispatched it runs its sequential path — no further sparking *inside* a serialized subtree (0534's core finding: declined-coarse + admitted-fine is strictly the *worst* outcome). **M-dynamic delivers this at runtime** (busy pool → inline). If Stage 0 shows a structural form is wanted, the cheapest is a thread-local "inside a spark body" flag (an M-dynamic refinement, not a fourth mechanism) — NOT M-static.

## North star (acceptance we are homing in on)

Measured under the core-count-controlled harness at full idle cores, across the F1–F4 family (extended if needed — see Stage 0):

- **Cores busy, not parked.** F4-hard: spawns collapse from 9.45M to O(cores); CPU moves from 240% (parked) toward busy; wall drops from ~112s to at least ≤ admit-all's ~24s, ideally toward serial (F4-hard has little exploitable parallelism — near-serial *is* the win, and the model must recognize that rather than keep cores busy with speculative search).
- **The genuine coarse-parallel win survives.** F1 (compute-bound divide-and-conquer) keeps its near-linear speedup — M-static must keep `fib`/`reduce-tree` admitted; M-dynamic must still populate the cores.
- **No parallel regression.** F2/F3 N-worker ≤ toggle-off.
- **Principled, not fixture-tuned.** M-static's recursion signal must separate beneficial from harmful *structurally* (F1 admitted, F4 accessors declined) — verified by the Stage-0 classification, not by an F4-specific threshold.

## Scope — five stages

### Stage 0 — Measurement instrument + the discrimination experiment (the prerequisite)
Everything downstream is graded, not asserted. Owners: `/qa` (harness, metrics, baselines, experiment) + `/dev`(cranelisp-backend) (commit + gate the instrumentation).
- Commit the S103 uncommitted gated spark-stats instrumentation in `ivar.rs` (`CRANELISP_SPARK_STATS=1` → spawns, serial-continues, peak concurrent executing-sparks, force outcomes) — zero-cost when off.
- A perf-lane harness (`tests/perf/`) that **controls for effective core count** (pins `RAYON_NUM_THREADS`, asserts idle, reports the full thread-count × spawn-count sweep, not a point) — encodes the S102→S103 false-green lesson (F4 read benign under 2–6 effective cores) as an explicit guard.
- **Metrics:** spawn-vs-serial ratio; peak concurrent busy-cores; useful-spark yield (realized parallel work ÷ spawns×overhead); per-spark-site recursion-SCC / tail classification.
- **The discrimination experiment (the sprint's pivotal Stage-0 deliverable):** classify every current spark site in F1–F4 by {recursive-SCC?, tail?} and confirm the M-static signal cleanly separates F1's beneficial sparks from F4's harmful accessor pairs while keeping F4's coarse D&C. If it does not separate cleanly, the design (Stage 1) must adapt before build.
- **Fixture adequacy:** confirm the F1–F4 set represents both a *genuine coarse-parallel* case (utilization win available) and a *no-exploitable-parallelism* case (near-serial is correct); add a minimal fixture if a regime is unrepresented — otherwise the thesis can be neither validated nor falsified.
- **Baseline config matrix** (so M-static and M-dynamic effects are attributable independently): `{OFF (no spark), current-syntactic, M-static-only, M-dynamic-only, M-static+M-dynamic, admit-all}` × thread-count sweep. **Pin `SPARK_DENSITY_MAX=0` (B4 off) on the M-static/M-dynamic rows** so B4's net-harm does not contaminate attribution; carry **B4-on as its own diagnostic row**. This matrix is the acceptance instrument for Stages 2–4.
- **B4 default-flip (named change-set):** the arch review DEMOTED the §2.7 density axis — flip `SPARK_DENSITY_MAX_DEFAULT` from `1` to `0` (B4 off by default) this sprint, since it is *net-harmful* at full cores (112s default-on vs 24s off vs 0.9s serial). B4 stays a valid concept for the S99 alloc/RC-dense compute class (may return Phase-H-composed) but must never default-fire in the incoherent decline-coarse-while-admitting-nested-fine state. Owner: `/design`+`/dev`(cranelisp-backend).

### Stage 1 — Design convergence (work through the design issues)
Actors + functions explicit before mechanism (`memory/feedback_actors_functions_before_synthesis.md`); options as prose with an open verdict for user arbitration (`memory/feedback_design_rulings_prose_review.md`).
- `/arch` (`effect-concurrency.md §3.1`): re-rule the floor model as a **utilization axis** distinct from the RC/allocator contention substrate — 0534 proved F4's wall is scheduler churn, not contention, so the memory-model work is orthogonal and the floor for this class needs the utilization gate, not Phase-H. Record that B4 (density axis) is *net-harmful* at full cores (new information).
- `/design` (`lenient-eval.md` — a new utilization-model section, superseding the §2.7 density-axis framing for this workload class): the actors (spark producer at the codegen site; the rayon pool / cores; a dispatched strand; the consumer/forcer), the functions between them (produce-or-inline decision, dispatch cost, sequential execution, force/join), and the mechanism: M-static's recursion signal + M-dynamic's busy-core signal + the hierarchical-decline invariant. Name the concrete cheap signals (executing-sparks atomic; recursive-SCC ∧ non-tail). Weigh the two mechanisms' interaction and the f3 trade openly.

### Stage 2 — Build M-static (measured independently)
`/dev`(cranelisp-backend), serial. Implement the non-tail-recursion admission filter behind the instrument; run the config matrix M-static-only vs current vs OFF; attribute its effect.

### Stage 3 — Build M-dynamic (measured independently)
`/dev`(cranelisp-backend), serial. Implement the busy-core bail-out as a **re-parameterization of the existing `IN_FLIGHT_SPARKS` + `try_reserve` create-gate** toward a ~2/core utilization cap — NOT a new counter (arch ruling §4). If Stage-1 design proves a non-consuming per-site read is genuinely needed, add only the pre-approved `cranelisp_spark_executing_count() -> i64` with the full intrinsics cascade + `/arch` sign-off. Run the matrix M-dynamic-only; attribute its effect independently of M-static.

### Stage 4 — Combine, tune, accept
Run M-static+M-dynamic; **grade F4's collapse as an M-static × M-dynamic *interaction*** (arch ruling — expect partial/inconclusive independent rows; do not read a weak single-mechanism row as failure); verify hierarchical decline holds (busy-pool → inline); grade against the north-star bars; `/qa` records the acceptance and re-scopes the II-G3 tripwire against the utilization model. Tune the utilization cap by measurement (~2/core target), not assertion.

## Explicitly set aside (per user direction 2026-07-06)

**All memory / ownership optimisations are distractions to this question and are OUT of this sprint.** 0534 proved F4's floor is scheduler-bound, not RC-bound, so borrow / mutable-borrow / reuse-token / projection-elision work cannot be part of the lenient-eval viability story. Deferred until we have a validated utilization thesis:

| Item | Rationale | Target |
|---|---|---|
| 0528 (uniqueness-preservation), 0526 / II-B3 (projection elision), region arena | Orthogonal to the parallelism problem (0534). Set aside as distractions until the utilization thesis is validated. | post-S104 |
| `--release` efficiency tier | Gated on the memory/increment-II track, itself now paused behind this question. | post-S104 |
| Concurrency combinator layer (`race`/`select`), 0442 unified budget | effect-concurrency slice-2/4; independent of the utilization gate. | concurrency track |
| Release-polish (0050, 0052, 0365) | Phase-H aspirational; unrelated. | Phase H |

**T1-cure residue (0529–0533, 0505):** decoupled dev-session reload doc/correctness holes from S103. **Deferred to S105** (user direction 2026-07-06 — keep S104 a clean single-theme investigation). Low-risk, non-rotting; carried intact.

## FIXME debt

| FIXME | Target | Status | Disposition this sprint |
|---|---|---|---|
| 0534 | /design (+/arch,/qa) | open | **Spine.** The utilization model is its resolution. |
| 0528, 0526 | /typecheck, /design | open | **Set aside** (memory; orthogonal per 0534). |
| 0529, 0530, 0533 | /design (int) | open | T1 residue — **deferred to S105** (keep spine focused). |
| 0531, 0505 | /repl | open | T1 residue — **deferred to S105**. |
| 0532 | /int (src) | open | T1 residue — **deferred to S105**. |
| 0506, 0507 | /design | open | Assess in Stage 1 if they touch the spark path; else carry. |

Backlog not proposed (feature-/concurrency-/Phase-H-gated): 0408, 0416, 0463, 0466, 0050, 0052, 0365, 0496, 0498, 0499, 0510, 0521. Reassess at wave gate.

## Architecture review (Phase 2)

**Verdict: APPROVE-WITH-REVISIONS** (`/arch`, 2026-07-06). The utilization model is architecturally sound; M-static + M-dynamic + hierarchical-decline are coherent. Five revisions applied to the scope above.

**Substantive correction to the thesis:** M-static does NOT deliver hierarchical decline structurally — a D&C recursion is non-tail-recursive at every level, so M-static re-selects spark sites all the way down. The ~2/core collapse is **entirely M-dynamic's**; M-static is purely a *quality* axis (spark coarse, not fine). Neither alone clears F4 — grade as an M-static × M-dynamic interaction.

**Three-axis ruling (edited into `effect-concurrency.md` §3.1.1–3.1.4):**
- **Large-work axis (M-static)** — primary *selection*; non-tail recursion; replaces the syntactic §2.2 filter for this class.
- **Utilization axis (M-dynamic)** — primary *throttle*; the existing `IN_FLIGHT_SPARKS` + saturation-gate re-parameterized toward ~2/core, default-on. **One counter, no third throttle** (Principle 8 / FIXME-0442 one-counter ruling).
- **Contention axis (B4 / §2.7)** — **DEMOTED**. Default-flip `SPARK_DENSITY_MAX_DEFAULT` 1→0 this sprint; net-harmful at full cores. Concept retained for the S99 alloc/RC-dense class (may return Phase-H-composed).

**Public-API:** no new C-ABI symbol expected (M-dynamic rides the existing budget primitive); if justified, only `cranelisp_spark_executing_count() -> i64`. M-static needs no cross-crate interface (Decision-21 `callees` + `in_tail_position` suffice). **No `cranelisp-types` edit this sprint.**

**Orthogonality confirmed:** setting aside all memory/ownership work is correct (0534: F4 is scheduler-bound — reproduces at increment-I HEAD; `rc_inc` identical serial-vs-ON; allocator 0.1% of syscall). **Roadmap course-correction owed at close (`/sprint` → `sprints/ROADMAP.md`):** Phase-H cures the (b) contention term but does NOT restore the F4 *utilization* floor — that is a separate axis cured now by the utilization gate. (Recorded in `effect-concurrency.md` §3.1.4.)

_Full review returned by the Phase-2 `/arch` agent; the six scope adjustments are reflected in the Mechanisms and Stage 0/3/4 sections above._

## Skill plans (Phase 3)

**Exit gate: PASS.** Interface set complete (no new C-ABI symbol, no `cranelisp-types` edit — arch-ruled, `/design`-confirmed); `/qa` has enough to build the Stage-0 instrument; both touched docs current + cross-referenced to `effect-concurrency.md §3.1.1`.

### /design (cranelisp-backend) — `design/backend/lenient-eval.md`
- **Delivered §2.8 "The utilization model"** — actors+functions first (Producer / Pool-cores / Strand / Consumer-forcer; produce-or-inline, dispatch ~13µs, sequential-must-dominate, force/join); M-static (recursive-SCC ∧ non-tail, from Decision-21 `callees`); M-dynamic (re-parameterize `IN_FLIGHT_SPARKS`+`try_reserve` toward ~2/core, default-on, owns the collapse); hierarchical decline (emergent via busy-pool; optional thread-local flag); B4 default-flip 1→0 (§2.7 demoted-not-deleted, §2.2 pointer).
- **Codegen seams (§2.8.6) for Phase 5:** M-static → `sparkability.rs` consumed at `compile_let §4.1`/`compile_apply §4.4`; M-dynamic → `§3.6.2` create-gate emission (cap value + default polarity only); hierarchical flag → `ivar_spark` closure; B4 flip → density-axis constant. Unit-scenario space: {recursive,non-recursive}×{tail,non-tail}, cap boundary, hierarchical decline, B4-off byte-identity.

### /qa — `tests/plan/s104-utilization-measurement.md`
- **Delivered the Stage-0 plan** — core-count-controlled harness (`RAYON_NUM_THREADS ∈ {1,2,4,6,8,10}` pinned; mechanical idle guard → INVALID-not-benign; F4 read as 11-rep distribution; %CPU+spawns travel with every wall). Config matrix (6 configs × T-sweep, B4 pinned off on M rows + B4-on diagnostic; `interaction = both − max(single)`; single-mechanism rows diagnostic-not-graded). 3 new counters to emit: `SPARK_SERIAL_CONTINUES`, `SPARK_PEAK_EXECUTING`, `SPARK_SITE_STATS`.
- **Discrimination experiment = the Stage-1→2 gate:** clean-separation defined (every coarse-D&C site spawns>0; zero fine-accessor spawns; verdict a function of {scc?,tail?} only, no per-fixture constant). Pre-classified F1–F4 sites confirmed against fixtures.
- **Fixture adequacy:** F4-hard adequate for regime B (near-serial-correct; "busy-but-slower — speculative waste" detector encoded). Regime A (coarse-parallel win) **measurement-gated → author minimal F5** (`f5_compute.cl`, heavy pure-compute D&C) if F1's win isn't decisively measurable at `T=nproc`. F5 is the positive witness that lets the thesis be *validated*, not just the pathology avoided.
- **Gates U-G1..U-G6**; II-G3 re-homed onto U-G1 (interim "ON ≤ OFF" tripwire, currently violated 112s vs 15.9s); perf-lane FIXME-tracked (0534 precedent), behavioural guards failing-not-ignored.

### Open design gates (measurement-resolved; defaults set; see Notes for the user-steer batch)
G1 M-dynamic cap `k` (default **2** = the ~2/core thesis), G2 reserved-vs-executing (default no-symbol), G3 hierarchical emergent-vs-structural (default emergent), G4 f3/B4-off trade (tracked), F5 fixture (author if F1 too light). All resolve inside the Stage 0–4 measurement; none block wave org.

## Waves (Phase 4)

Stages are inherently sequential (each builds on the prior's measurement); backend is the only crate touched, so the build is a serial single-crate D/D/R across Stages 2–4 (honours "one source-touching agent at a time"). `/qa` measures after each; `/review` reviews each change-set.

### Wave 0 — Stage 0: instrument + baselines + the discrimination gate
| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | cranelisp-backend | Commit+gate the spark-stats instrumentation (3 new counters, zero-cost off) + B4 default-flip `SPARK_DENSITY_MAX_DEFAULT` 1→0. Unit tests for the {scc?,tail?} classification. | **done** `4924c26` — 12 unit tests green; suite 4119/1(0528)/1; SCC classifier measure-only; callees self-edge finding (per-site self-call check). No public-API change. |
| /qa | — | Build `tests/perf/s104_utilization.py` (harness + matrix + metrics); run baselines; **run the discrimination experiment**; fixture-adequacy (author F5 if F1 too light). | **done** `1360d62` — discrimination **PASS** (gate cleared; `{scc,tail}` separates coarse/fine across F1–F5, no misclass, no fixture constant); F1 inadequate → **F5 authored** (Regime-A witness for Stage 4); anchor reproduced (b4on 118s/parked/9.84M = 0534). |

**Wave-0 gate: PASS → build M-static.** Standout finding: the **B4 default-flip alone** moves F4-hard T=10 from **118s parked (241% CPU)** → **~10–15s busy (480% CPU)** — arch's B4 demotion empirically vindicated. Residual **~8–13M spawns (~9–17× serial)** is the over-sparking M-static (cut count) × M-dynamic (cap ~2/core) must close (U-G1). F2/F3 parallel 7–10× *slower* than serial = the set-aside contention class; correct answer is near-serial (M-dynamic's job). Results in `tests/plan/s104-utilization-measurement.md §8`.
| /review | cranelisp-backend | Review the instrumentation + B4-flip change-set (`4924c26`). | **done** — SCC classifier CORRECT/trustworthy for W1. 1 Important (module-blind self-call check → **W0→W1 gate item**, fold into W1 /dev before admission goes live); zero-cost-off/B4-flip/no-API-leak/dup all cleared; 2 minor Suggestions carry. No hard blocker to landing W0. |

**Wave-0 gate (Stage-1→2):** the discrimination experiment must show M-static's {scc?,tail?} signal cleanly separates (coarse-D&C admitted, fine accessors declined, verdict fixture-independent). PASS → build M-static. FAIL → back to `/design` before any build.

### Wave 1 — Stage 2: build M-static (quality axis), measured alone
| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | cranelisp-backend | **Task 0:** fix the module-blind self-call check (`utilization.rs:509`). **Task 1:** wire M-static admission — the spark decision now USES `admit?=(scc∧¬tail)` per §2.8.2, replacing the syntactic non-cheap-Apply filter for this class; add an env toggle (syntactic vs M-static) so the matrix can measure M-static-only. Unit tests per §2.8.6. | **done** `3804e42` — module-blind fix + M-static wired (independence+≥2 preserved; computed callees decline = toward-decline default); toggle `CRANELISP_SPARK_ADMIT=mstatic\|syntactic`. Backend 403/403, workspace 4124/1(0528)/1, no lenient_* flip, no API change. |
| /qa | — | ~~M-static-only matrix row~~ → **single-shot attribution (doctrine change)**: F4-hard `syntactic 54.9s/13.1M → mstatic 2.4s/182` (accessor firehose gone, 72,000× fewer spawns); F5 `syntactic 12.4s/1.89M → mstatic 11.7s/1.28M` (fib-explosion remains → M-dynamic's job). Recording §8.5 + lightweight spot instrument. | **done (measured)** — recording+commit in progress |
| /review | cranelisp-backend | Review the M-static change-set (`3804e42`): composition correctness, SCC cache, the toward-decline divergence, the 4 syntactic-pinned par_codegen_tests (legit or masking?). | **done — CLEAN** (no Blocker/Important; Wave 2 unblocked). Composition correct (independence+≥2 preserved, §2.6.3 guarded); toward-decline sound+right (pins don't mask a gap); SCC cache mono-invariant. 2 minor Suggestions carry (stats-path graph rebuild; /qa module-precision neg test). |

> **Wave-2 finding (single-shot, 2026-07-07): the concurrent-cap M-dynamic is INSUFFICIENT — hierarchical decline (G3) promoted from optional to MANDATORY.** F5(fib) stays ~40s/1.5M spawns at every cap (k=1 tightest gave MORE spawns, 5.4M) because the create-gate bounds *concurrent* sparks (memory) but permits recycle → total spawn *count* stays O(nodes). The user-thesis "~2/core strands then run a high-efficiency sequential path" REQUIRES the structural thread-local "inside-a-spark-body → inline nested" flag (§2.8.4 G3), not the emergent cap. Clean runtime-only fix in `ivar.rs` (thread-local set around the `ivar_force` thunk call; `try_reserve` returns 0 inside a spark body). Wave 2 continues as **2b** to build it. Design-doc update owed: §2.8.3/§2.8.4 must reframe G3 as mandatory (route to /design at close).

### Wave 2 — Stage 3: build M-dynamic (utilization axis), measured alone
| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | cranelisp-backend | Re-parameterize `IN_FLIGHT_SPARKS`+`try_reserve` toward the ~2/core cap (k=2 default), default-on (§2.8.3) — no new counter/symbol. Unit tests (cap boundary, hierarchical decline). | pending |
| /qa | — | Run the M-dynamic-only matrix row; attribute spawn-*quantity* effect. | pending |
| /review | cranelisp-backend | Review the M-dynamic change-set (confirm no third throttle / no new export). | pending |

### Wave 3 — Stage 4: combine, tune, accept
| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | cranelisp-backend | M-static+M-dynamic combined; tune the cap `k` by measurement (G1). | pending |
| /qa | — | Full matrix; grade U-G1..U-G6 (F4 as M-static×M-dynamic interaction); record acceptance; re-scope II-G3 onto U-G1; resolve gates G1–G4/F5 with the measured evidence. | pending |
| /review | cranelisp-backend | Final change-set review; confirm hierarchical-decline invariant holds. | pending |

## Notes

- Phase 1 scope authored 2026-07-06. Thesis reframed by user across two exchanges: (1) set aside all memory optimisations as orthogonal; (2) the goal is core utilization (~2/core distinct large strands separating then running serial), not fine-grained parallelism — pursued via a static "probably-large / non-tail-recursion" filter (M-static) + a dynamic "cores already busy" bail-out (M-dynamic), measured independently, both built this sprint.
- Central inputs: FIXME 0534 (profiled attribution — scheduler churn, B4 net-harmful, the 24s-busy vs 112s-parked vs 0.9s-serial rows), S103 close Findings (★ roadmap correction), `lenient-eval.md §2.2/§2.7/§3.6`, `effect-concurrency.md §3.1`.
- Measurement discipline is load-bearing: the config matrix must attribute M-static and M-dynamic effects *independently*, and the harness must control for effective core count (the S102→S103 false-green).
- **W0→W1 gate item (from `/review` of `4924c26`):** `classify_spark_callee`'s self-call check (`utilization.rs:509`) is module-blind — a cross-module call sharing the enclosing fn's bare name false-admits as recursive. Over-classify-only, inert while measurement-only; MUST be fixed (fq.module==current_module ∧ symbol match, ~3 lines) before Wave-1 M-static drives admission. Routed to Wave-1 `/dev` as task 0.

## Outcome (Phase 7)

**S104 DELIVERED — the utilization model for lenient eval: the 0534 over-sparking pathology cured and a real compute-parallel speedup demonstrated, via measurement-driven convergence. Awaiting user close sign-off.**

### Delivered — the utilization model (thesis validated)
The goal was reframed (user) from fine-grained parallelism to **core utilization**: dispatch a few distinct large strands that separate onto cores then run a high-efficiency sequential path. Built entirely in `cranelisp-intrinsics`/backend — **no public-API change, no `cranelisp-types` edit**:
- **M-static** (`3804e42`) — spark only non-tail recursion (`admit? = scc∧¬tail`, from Decision-21 `callees`); kills the fine-accessor firehose (F4 spawns 13.1M→182). Discrimination gate PASSED (structural `{scc,tail}` separation, no fixture tuning).
- **~2/core cap** (M-dynamic, `6dbed5a`) — `SPARK_BUDGET` default `4×→2×threads`.
- **Worker-origin depth-D hierarchical decline** (`af358ad`→`b2c6122`→`e3644ca`) — a strand re-sparks until nesting depth ≥ `floor(log2 nproc)` (=3 on 10 cores), then inlines; cross-spawn base propagation. This is the mechanism that bounds spawn *count* (the cap alone does not — permits recycle).
- **IVar-force backoff** (`45e58fc`) — `spin→yield→sleep`; halves CPU on decline-heavy shapes at neutral wall.
- **B4 density axis demoted** (`4924c26`) — default off (was net-harmful at full cores).

### Delivered — the results (clean single-shot, stats-off, T=10)
- **Pathology cured:** F4-hard **55s → ~2.3s**; spawns collapsed **~6 orders of magnitude** (13.1M→~16).
- **Compute-parallel speedup demonstrated (thesis positive claim):** **F6** (heavy balanced) 3.10s → **0.82s (3.4×)**; **F5** (fib) 0.67s → **0.39s (1.7×)**.
- **Floor held** on light work (F5 was ≈serial pre-tuning).

### Delivered — instrument + docs
- Measurement instrument: `tests/perf/s104_utilization.py` + `s104_spot.py` + fixtures **F5** (`f5_compute.cl`) and **F6** (`f6_parwin.cl`, the Regime-A positive witness) + the discrimination experiment.
- Design docs as-built: `lenient-eval.md §2.8` (mechanism) + **§2.8.7 Measurement strategy** + **§2.8.8 Remaining problems**; `effect-concurrency.md §3.1.5` (validated outcome + Phase-2 correction + S105 focus); `s100`/`s104` plan §8.7 acceptance (U-G2/G4/G5 PASS; U-G1 partial).

### Deferred (with rationale)
| Item | Rationale | Target |
|---|---|---|
| **All memory/ownership work** (0528, 0526, region arena, `--release`) | Set aside as orthogonal — 0534 proved F4's floor is scheduler-bound, not RC-bound (reproduces at inc-I HEAD). User direction. | post-S104 |
| **Density-aware depth allowance (FIXME 0535)** | **The S105 focus.** The depth knob can't distinguish alloc-free compute fan-out (F6, wins) from alloc-heavy contended fan-out (F4/F3, loses) — needs the alloc/RC-density signal to modulate depth. The clean synthesis of the S104 utilization axis + the §3.1 contention axis. | S105 |
| Budget-inline depth-leak hook (FIXME 0536) | D≤~log2(cap) without a backend hook on the create-gate inline arm; D=3 safely under. | /design(backend) |
| Alloc/RC-contention floor (F3, F4-hard above serial) | The contention class; cured by the density signal + Phase-H memory work, not the scheduler. F4-at-D3 is a mild floor trade vs D=1, accepted for the F6 win (user 2026-07-07). | S105 / Phase H |
| T1-cure residue (0529–0533, 0505) | Decoupled dev-session reload holes; kept S104 single-theme. | S105 |

### Findings
- **★ Measurement-driven convergence was the method, and it worked.** The pre-implementation design got four mechanism rulings wrong, each corrected by *measurement not assertion*: (1) the concurrent cap does NOT bound spawn count (permits recycle); (2) both-paths hierarchical decline is harmful (collapses to peak 2); (3) F3's cost is contention, not spin (backoff wall-neutral); (4) a depth allowance is needed for balanced coarse trees. Every correction was profiled.
- **The boundary is exactly where we drew it.** The residual above-serial cases (F3, F4-hard) are the deliberately-set-aside alloc/RC-contention class — and the sprint *precisely characterized* the missing input (alloc/RC density) as the S105 focus, re-motivating the memory work as a density-aware depth allowance rather than a distraction.
- **Measurement methodology lessons** (saved to memory `feedback_measure_orders_of_magnitude_not_precision`): single-shot for order-of-magnitude work (not rigorous rep/idle-guard harnesses — the idle-guard self-defeats mid-sweep); measure wall with stats OFF (the stats atomic inflated F5 to 5.8s vs the real 0.7s); counts from a separate run. Two false-reads were caught this way.

### Suite
**4137 run / 4136 passed / 1 failed / 1 skipped** — the sole RED is `chaining_toggle_off_allocates_intermediate` (the known FIXME-0528 carry, re-homed to /typecheck). No regressions across all Wave-2 concurrency change-sets.

## Next skills
- `/sprint` — open **S105**: FIXME **0535** density-aware depth allowance (the utilization × contention synthesis — the memory work now re-motivated with a precise job), + 0536 budget-inline hook, + the T1-residue drain (0529–0533, 0505).
- `/design`(backend) — 0535/0536 pick-up.
