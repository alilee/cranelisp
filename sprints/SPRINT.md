# Sprint 105: Lenient Eval — Attributing the Parallel Residual (measure-first)

**Status**: PHASE 5 LANGUAGE (ACTIVE) — Wave 0 (build the instrument)

**Goal**: Increase measurement fidelity to **attribute the post-increment-II parallel residual** (F3/F4 above serial) *by mechanism* — scheduler-spread vs (a)-allocation vs residual-atomic-RC vs unavailable-parallelism — then build the lever the evidence selects. Lead hypothesis for the (a)-allocation case: **escape ∧ uniqueness stack allocation** (unique, non-escaping values as true RC-free stack locals, passed by mutable/immutable reference).

## Scope

The parallel-performance story has been disentangled and largely cured across four sprints, leaving a **small, unattributed residual**:

- **Scheduler churn** — CURED S104 (utilization model; F4 55s→2.3s, F6 3.4×, F5 1.7×).
- **(b) atomic-RC contention** — CURED S102 (borrow / increment I; rc_inc 100% drop) + S103 (reuse / increment II; rc_inc → 0.019% of baseline).
- **(a) allocator-lock contention** — NOT built (region arena deferred; backend §4.4 verdict DEFER, blocked on allocator co-design).

What remains is F4-hard ~2.3s vs 0.88s serial (~2.6×) and F3 similar. **S104's close *asserts* this is "the alloc/RC-contention class," but that attribution predates re-measuring the residual after inc I + inc II landed** — the RC term it names is exactly what those increments cured. The dominant residual term is therefore **unprofiled**, and the four candidate cures point at four different levers. Per the user's own doctrine (profiled attribution over asserted mechanism), S105 measures before it builds.

**This is a regime shift from S104's doctrine.** S104 used single-shot / order-of-magnitude measurement because it chased a 100× pathology. Attributing a ~2.6× residual is a **decomposition** problem, not a wall-precision problem — it calls for *finer instruments* (attribution counters, oracle-differentials, HW counters), not more reps.

### Preparatory phase (the sprint opener) — increase fidelity + attribute

Owners: **/qa** (harness, attribution, fixtures) + **/dev(cranelisp-backend)** (gated instrumentation), **/arch** consulted on the decomposition model (the (a)/(b) coupling makes additive attribution ambiguous — S99 proved the terms interact).

**Fidelity additions** (each disambiguates one candidate cause):

| Instrument | Disambiguates | Candidate lever |
|---|---|---|
| Syscall/CPU-state profile on the *post-cure* binary (%CPU busy-vs-parked; `sched_yield`/`futex` vs `brk`/`mmap` share; ctx-switches) | scheduler-spread vs allocator-bound | 0535 depth vs stack/region |
| Allocation attribution (per-run alloc count + bytes + allocs/branch) + mimalloc-vs-system allocator-swap oracle (S99 toggle) | (a)-allocation wall contribution | escape∧uniqueness **stack allocation** |
| RC split — atomic vs non-atomic rc-ops + Crossing-vs-Confined cell tally, with the *site* of each residual atomic op (extends H2 `RC_STATS`) — apportioned by the FINE probes (`CRANELISP_NONATOMIC_RC`, capture-borrow), **not** by `NO_OWNERSHIP` (Rev-2, §3.1.6-R3) | residual conservatively-atomic RC, and where | 0526/0528 confinement precision |
| HW cache-contention counters (`perf stat` HITM / cross-core line transfers) | (b) cache-bouncing wall invisible to wall-clock | (b)-term residual |
| Available-parallelism ceiling: core-count sweep (1..nproc) speedup curve + critical-path/useful-yield proxy; `NO_OWNERSHIP` is the **coarse all-memory-model-off** ceiling oracle here (Rev-2), not a (b) toggle | is near-serial simply *correct*? | accept-done → `--release` |
| Oracle-differential decomposition — the allocator-swap × ownership-off pair runs as a **full 2×2 factorial** {baseline, ¬a, ¬b, ¬a∧¬b}, reporting the **interaction term `I = baseline − ¬a − ¬b + ¬a∧¬b` explicitly** as a named joint term owned by neither axis (Rev-1, §3.1.6-R1); the coupled (a)/(b) *interior* split is unidentifiable-by-construction and decision-irrelevant — the gate reads each lever's direct-oracle net-recovery column, never a reconstructed additive breakdown (§3.1.6-R2) | the residual breakdown + per-lever recovery | the selection itself |

**Fixture additions** (so the residual is structurally attributable, not confounded):
- an **(a)-isolating fixture** — alloc-heavy, RC-light, scheduler-light — the allocator term on its own axis;
- a **stack-allocation witness** — a unique non-escaping aggregate mutated in-frame vs. escaping to a spark — giving a **measurable upper bound on the stack-allocation win before building it** (toggle the existing immortal-sentinel stack path as a crude oracle). **The witness MUST exercise the *parallel* (sparked) branch, not only the serial in-frame case (Rev-3, §3.1.6-R4):** the increment-I stack path is declined inside spark thunks by the 0525 gate-5 spark-frame decline, so an (a)-isolated *serial* fixture over-states parallel recovery precisely where gate 5 blocks it. If the gate attributes the residual to (a)-via-stack on the parallel path, the build branch scope must include evidence the (a) is on paths gate 5 does not decline, OR an explicit spark-frame-aware stack path (a scope increase beyond increment I — see build-phase caveat).

**Doctrine guards carried from S104** (`memory/feedback_measure_orders_of_magnitude_not_precision`): wall runs with all counters OFF (atomics perturb the wall); counts from a separate run; mechanical idle assertion as INVALID-not-benign (no self-defeating idle-guard mid-sweep); HW counters run externally/separately.

**Preparatory-phase output — the decision gate:** a per-fixture **attribution vector** decomposing the F3/F4 residual into {scheduler-spread, (a)-allocation, residual-atomic-RC, unavailable-parallelism}, each with an **oracle-bounded estimate of what its candidate mechanism would recover.**

### Build phase — the lever the evidence selects (scoped at the gate)

The attribution gate selects one:

| If the residual is dominated by… | Build |
|---|---|
| (a)-allocation | **Escape ∧ uniqueness stack allocation** — compose Q2 (escape→stack) with Q4 (uniqueness) into true RC-free stack locals passed by mutable/immutable reference; sidesteps the allocator (no lock to co-design). **Arch-ruled separable for the statically-sized class** (incl. heap-typed fields via a backend-local frame-exit release, and fixed-size inline Vec/ADT buffers — the §4.4 DEFER is blocked only on *extern-reached* allocations, which a backend-inline slot is not); **dynamic-size / extern-reached stays Phase-H** (§3.1.6-R4). **Governing caveat: the 0525 gate-5 spark-frame decline blocks stack-alloc inside spark thunks — so in increment I this serves the near-serial working grid but does NOT fire on the sparked parallel-search branches**; firing there is a scope increase (spark-frame-aware stack path). Mutable-borrow-across-call = the arch-ruled conditional `MutBorrowed` ABI mode (`ownership-inference.md §3.6`): admissible monotone-soundable extension of `Borrowed`, uniqueness stays off-ABI, needs a `cranelisp-types` carrier for the ABI half (authored at the implementing sprint). |
| residual conservatively-atomic RC | **0528 uniqueness-preservation** (unique-in⇒unique-out advisory summary bit; the live `chaining_toggle_off` RED) and/or **0526 confinement-gated projection elision** |
| scheduler-spread | **0535 density-aware depth allowance** (depth modulated by static alloc/RC density) + **0536** depth-leak enabler |
| unavailable-parallelism | **Declare the parallel story settled** — near-serial is correct for the low-exploitable class (S104's own north-star); pivot to the roadmap mainline (`--release` LLVM tier, where the composed end-state parallel gate lives) |

Mechanism selection may trigger a **mid-sprint re-scope with user sign-off** (the build target is evidence-gated, not pre-committed). If the gate says "little to win," the sprint closes on the attribution + a scoped recommendation rather than forcing a build (evidence-gated carry, `memory/feedback_no_defer_for_size_decompose_evidence_gated`).

### T1-cure residue track (parallel, separate commits — user-directed 2026-07-07)

The T1-cure residue — dev-session reload doc/correctness holes decoupled from S103 (0529, 0530, 0533 → /design(int); 0531, 0505 → /repl; 0532 → /int(src)) — rides S105 as a **parallel, non-lenient-eval track**, with its fixes **committed separately** from the lenient-eval measurement/build commits (clean two-theme history). It touches different surfaces from the backend/intrinsics spine, so the doc-only design work (0529/0530/0533) can proceed in parallel; the source-touching work (0532 /int, 0531/0505 /repl) serializes with the measurement-phase `/dev(backend)` instrumentation commits per "one source-touching agent at a time." Sequenced in wave org (Phase 4) to avoid tree contention.

**Out of scope / deferred:** Phase-H structural cures beyond the selected lever; `--release` tier (unless the gate selects "accept-done"); concurrency combinator layer; release-polish (0050/0052/0365).

## FIXME debt

| FIXME | Target skill | Status | Notes |
|---|---|---|---|
| 0535 | /design (+/arch,/qa) | open | Candidate lever (scheduler-spread outcome): density-aware depth. |
| 0536 | /design(backend) → /dev | open | Enabler for 0535's deep arm (depth-leak). |
| 0528 | /design(int/typecheck) | open | Candidate lever (residual-atomic-RC outcome); the live `chaining_toggle_off` RED. |
| 0526 | /arch | open | Candidate lever (confinement-gated projection elision, inc-II half). |
| 0408 | /port | open | Sudoku parallel-search — the real-world witness for whichever lever lands. |
| 0529, 0530, 0533 | /design(int) | open | T1-residue track (parallel; separate commits). |
| 0531, 0505 | /repl | open | T1-residue track (parallel; separate commits). |
| 0532 | /arch → /int(src) | open | T1-residue track (parallel; separate commits). **0532 needs a small in-sprint `/arch` seam ruling** (explicit reload-instantiation vs implicit `__expr`-wrapper coupling; within-crate, no interface impact) before `/int(src)` actions it (Rev-4). |
| 0506, 0507 | /design | open | Assess in Phase 3 if they touch the spark/depth path; else carry. |
| 0416, 0463, 0466, 0496, 0498, 0499, 0510, 0521, 0050, 0052, 0365 | various | open | Feature-/Phase-H-gated backlog; reassess at wave gate. |

## Architecture review (Phase 2)

**Verdict: APPROVE-WITH-REVISIONS** (`/arch`, 2026-07-07). Measure-first is the correct application of the profiled-attribution doctrine; the S104-close residual attribution genuinely predates re-measuring after inc I+II, so the dominant term is unprofiled. Preparatory phase = measurement + gated instrumentation only → Principle-8-clean. Two rulings recorded durably:

- **`effect-concurrency.md §3.1.6` (new) — the attribution/decomposition model.** (R1) The four terms are NOT additive; the (a)/(b) pair runs as a **2×2 factorial** reporting the interaction term `I` explicitly. (R2) The coupled (a)/(b) *interior* split is unidentifiable-by-construction and decision-irrelevant — the gate reads each lever's **direct-oracle net-recovery**, not a reconstructed breakdown. (R3) `NO_OWNERSHIP` is the coarse all-memory-off ceiling oracle, not a (b) toggle; apportion with the fine probes. (R4) escape→stack is arch-separable for the statically-sized class (routes around the §4.4 extern-reached blocker) but the **0525 gate-5 spark-frame decline blocks it inside spark thunks** — so increment-I stack-alloc serves the near-serial grid, not the sparked branches; the stack witness must be the *parallel* fixture.
- **`ownership-inference.md §3.6` (new) — conditional `MutBorrowed` ABI ruling.** Admissible as a monotone-soundable extension of `Borrowed` (uniqueness precondition stays OFF the ABI per R4; fallback = today's `Owned`+dynamic reuse token). §5.6 fresh-slot handles the `Owned↔MutBorrowed` flip (one more compared value, no new machinery). The ABI half needs a `cranelisp-types` `Mode::MutBorrowed` carrier — authored at the implementing sprint, not landed speculatively in S105.

**Public-API:** confirmed — no `cranelisp-types` edit, no new C-ABI symbol for the preparatory phase (RC split extends H2 `RC_STATS`; alloc counters + stack-oracle intrinsics-internal). Caveat: `STACK_SLOT_HITS` is read **backend-side** — do not force-resolve the counter-surface seam under measurement pressure (standing h2-RED). **T1 track:** no cross-crate concern; **FIXME 0532 carries `target: /arch`** but is a within-crate seam-ownership ruling (no interface/ABI/facade), actionable as a small in-sprint `/arch` ruling in Phase 3.

Four revisions folded into the Scope above (Rev-1 2×2 factorial + `I`; Rev-2 granularity note on `NO_OWNERSHIP`/RC-split; Rev-3 parallel stack-witness fixture; Rev-4 the 0532 in-sprint `/arch` seam ruling).

## Skill plans (Phase 3)

Phase-3 design runs **serially** (one source/doc-touching agent at a time — shared-tree rule). Order: `/qa` (done) → `/design(cranelisp-backend)` → T1 track (`/design(int)` + `/repl`, + the 0532 `/arch` seam ruling).

### /qa — `tests/plan/s105-residual-attribution.md` — **DONE (`7a6728f`)**
- Delivered the attribution plan: upgraded instrument `s105_attribution.py` (single-sourced against the S104 harnesses) → per-fixture attribution vector {scheduler-spread, (a)-allocation, residual-atomic-RC, unavailable-parallelism}; the **2×2 factorial** (allocator-swap × ownership-off, `I` reported); coarse-vs-fine oracle discipline; **direct-oracle net-recovery** lever selection; two new fixtures **F7** ((a)-isolating) + **F8** (parallel stack-alloc witness with the REQUIRED serial-vs-parallel gate-5 divergence property); the decision gate + accept-done→`--release` branch (core-sweep ≤~1.2× ceiling); S104 doctrine guards as INVALID-marking preconditions; the `STACK_SLOT_HITS` backend-side-read caveat; 2 failing-not-ignored perf-lane guards.
- **NEW gated instrumentation for `/dev(cranelisp-backend)`** (all `CRANELISP_RC_STATS`-gated, zero-cost-off, intrinsics-internal, **no `cranelisp-types` edit / no new C-ABI symbol**): **N1** per-run alloc-bytes counter; **N2** per-branch/per-site alloc attribution (`[ALLOC_SITE_STATS]`); **N3** per-site residual-atomic-RC dump + Crossing/Confined tally (`[RC_SITE_STATS]`); **N4** a dedicated FINE stack-oracle env gate (`CRANELISP_NO_STACK_ALLOC=1`) flipping `STACK_ALLOC_ESCAPE_FACT_SOUND` at runtime-read.

### /design(cranelisp-backend) — instrumentation seams — **DONE (`9b343c4`)**
- `ownership-codegen.md §13.2.2` (new) specifies all four seams against the as-built, each zero-cost-off + interface-clean (no `cranelisp-types` edit, no `public-api.txt` regen, no C-ABI symbol, no cache-schema bump; `lenient-eval.md §2.8.7` cross-refs it):
  - **N1** — trivial: `alloc_with_rc` already tallies `BYTES_ALLOCATED`; N1 = an appended `alloc_bytes=` field in `rc_stats_line()`.
  - **N2** — the heavy one (compile→run channel on the hot alloc path); **descoped-safe** to I1 syscall-share + F7 allocator-swap (the gate-5 sub-verdict rides F8's `STACK_SLOT_HITS`, not N2). Minimal-viable = a coarse in-spark-vs-parent two-bucket if wanted.
  - **N3** — light, codegen-time; site + Confined/Crossing identity both in hand at `heap::use_nonatomic_arm`; backend-side `atexit` dump (does not re-open the h2-RED seam).
  - **N4** — **ADOPTED (recommendation over two-build):** relocate `STACK_ALLOC_ESCAPE_FACT_SOUND` (const at `fn_compiler.rs:807`) to a `OnceLock` env read — exact sibling of `nonatomic_rc_codegen_enabled()`; codegen-time, byte-identical when unset; keeps the stack oracle on ONE binary + the same env-toggle doctrine as the other fine probes (two-build reserved for the allocator swap per the 2×2 discipline).
- `STACK_SLOT_HITS` stays read backend-side; the h2-RED backend→intrinsics counter-surface seam is NOT force-resolved (standing design boundary).

### T1 track (parallel; separate commits) — _issued after the spine Phase-3_
- `/design(int)` — 0529/0530/0533 dev-session reload design; `/repl` — 0531/0505; **`/arch`** — the small 0532 within-crate seam ruling (no interface impact) before `/int(src)` actions it.

## Waves (Phase 4)

The spine is **inherently serial** — the instrument must be built before it can measure, and the build lever is selected only *after* the attribution. The T1 track runs parallel with separate commits, its source-touching work interleaved to honour "one source-touching agent at a time."

### Wave 0 — build the instrument (Phase-5 Stage 0)
| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | cranelisp-backend | Commit N1 (`alloc_bytes`) + N3 (`[RC_SITE_STATS]`) + N4 (`CRANELISP_NO_STACK_ALLOC` const→`OnceLock`) gated instrumentation; zero-cost-off unit tests; N2 only if the coarse two-bucket is cheap. | **done `3e923dc`** — N1/N3/N4 in, N2 skipped (hot-path cost; gate-5 rides F8 `STACK_SLOT_HITS`); seam×scenario unit tests; suite 4146/1(0528)/1, zero new REDs; nothing regenerates. |
| /qa | — | Build `tests/perf/s105_attribution.py` (single-sourced on the S104 harnesses) + fixtures **F7** ((a)-isolating) + **F8** (parallel stack-alloc witness, serial-vs-parallel gate-5 divergence); the 2 failing-not-ignored perf-lane guards. | **in-progress** |

### Wave 1 — run the attribution → the decision gate (Phase-5 Stage 1)
| Skill | Crate | Task | Status |
|---|---|---|---|
| /qa | — | Run the full attribution: the 2×2 allocator-swap × ownership-off factorial (+ `I`), the fine-probe apportionment, the core-count speedup-ceiling sweep, F8's gate-5 sub-verdict. Emit the per-fixture attribution vector + the decision-gate verdict. | pending |

**Wave-1 gate = `/sprint` + user** — read the attribution, select the build lever (mid-sprint re-scope with user sign-off). This is the pivotal decision the whole preparatory phase exists to inform; it can legitimately say **accept-done → pivot to `--release`** (no build).

### Wave 2 — build the evidence-selected lever (Phase-5 Stage 2; CONDITIONAL, scoped at the Wave-1 gate)
| If the gate selects… | Skill | Crate | Task |
|---|---|---|---|
| (a)-allocation | /design→/dev | cranelisp-backend (+types if `MutBorrowed`) | escape∧uniqueness stack allocation (mind the 0525 gate-5 spark-frame scope caveat) |
| residual-atomic-RC | /design→/dev | typecheck (+backend) | 0528 uniqueness-preservation / 0526 confinement-gated projection elision |
| scheduler-spread | /design→/dev | cranelisp-backend | 0535 density-aware depth + 0536 depth-leak |
| unavailable-parallelism | — | — | **no build** — record the settled verdict; pivot to `--release` mainline |

### Wave T1 — dev-session reload residue (parallel; separate commits)
| Skill | Crate | Task | Status |
|---|---|---|---|
| /arch | — | The small 0532 within-crate seam ruling (explicit reload-instantiation vs implicit `__expr`-wrapper coupling; no interface impact). | pending |
| /design → /dev | src/ (int) | 0529/0530/0533 dev-session reload design + fix; 0532 after the ruling. | pending |
| /repl | repl/ | 0531/0505. | pending |

Source-touching agents (Wave-0 /dev-backend, Wave-2 build, Wave-T1 /dev-int + /repl) run **serially** — never two editing the shared tree at once. Doc-only design + /qa harness authoring may overlap read-only work but commit disjoint files.

## Notes

- Phase 1 scope authored 2026-07-07. Reframed across a user dialogue: (1) step back from committing to 0535 — the memory optimizations (borrow inc I / borrow-mut inc II) are already delivered, so the S105 premise (residual = alloc/RC contention) is *asserted, not measured*; (2) the user proposes escape ∧ uniqueness stack allocation (RC-free stack locals passed by reference) as the (a)-term lever; (3) **the user directs a preparatory measurement-fidelity phase to attribute the residual before building** — this scope.
- **Key insight the phase must confirm/refute:** after inc I + inc II, is the F3/F4 residual (a)-allocation (→ stack allocation), conservatively-atomic RC (→ 0528/0526), scheduler-spread (→ 0535), or simply unavailable-parallelism (→ accept-done, near-serial is correct)?
- **The build is evidence-gated**, not pre-committed. The preparatory phase can legitimately conclude "little to win, pivot to `--release`."
- **Bundling gate RESOLVED (user, 2026-07-07):** S105 bundles the T1-cure residue as a parallel track, committed separately from the lenient-eval work.
- **Phase-3 scope gaps — RESOLVED at the Phase-3→4 gate** (`/design(backend)` `9b343c4`): **N4 = adopt the runtime-read fine gate** (`CRANELISP_NO_STACK_ALLOC`, ~10-line const→`OnceLock` relocation, one binary). **N2 = descope-safe** to I1 + F7 (gate-5 sub-verdict rides F8 `STACK_SLOT_HITS`); build only if cheap coarse two-bucket. Still open/environmental: **I4** HW HITM counters are host-PMU-dependent — may read `UNAVAILABLE` on the VM, (b) attribution then rests on I3 alone (accept). The **h2-RED counter-surface seam** (backend `STACK_SLOT_HITS` → intrinsics print) stays a separate `/arch`+`cranelisp-intrinsics` question, OUT of S105 scope.

## Outcome (Phase 7)

_Pending._
