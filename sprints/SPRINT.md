# Sprint 99: Parallelism/memory-contention — measure-first, decompose the 10×

**Status**: PHASE 5 — CLOSE-OUT WAVE (ACTIVE). **Ablation complete** (1a–1d committed): no pre-Phase-H substrate cure restores the floor; the dominant (b) contention (vec-COW leaf-refcount volume) is empirically confirmed **genuinely Phase-H** (Perceus/mutate-in-place). **User direction 2026-07-02 (post-1d):** keep all three cures **opt-in** (correct, byte-identical-off, durable substrate; none default-on), **accept the Phase-H re-sequence** of the (b) cure, **run the close-out wave** (record the knowledge + honesty doc corrections + cheap housekeeping) → Phase 7. Close-out: `/design`(backend) closes 0461 + actions 0462 + lands 0459 floor-scoping; `/arch` records the empirical Phase-H justification in `effect-concurrency.md §3.1`; `/design`(platform) stale-macro sweep; `/examples` network example. Then Phase-7 outcome for user approval.

_Prior status (ablation): Wave 0 complete; ran the three cures as an ablation (each toggle-gated, re-benchmarked); re-sequenced capture-by-borrow → gate → allocator-last; cancellation/short-circuit DEFERRED (keeps the deterministic benchmark). See the Wave-1 table + `tests/plan/s99-measurement.md` §8–§10._

**Goal**: Decompose the Sudoku parallel-search "~10× slower than serial" into its real terms — serial luck × speculative waste × contention — via a falsification-oriented **measurement pre-wave**, then fund only the substrate/RC cures the measurement justifies, so a *reasonable, idiomatic* nested-ADT workload runs near-serial-per-core up to core saturation — with cheap, durable changes that survive (not get thrown away by) the Phase-H stack/region/Perceus memory model.

## Why this sprint, why now

The roadmap's next-scheduled increment (post-S98 close) is the parallelism/memory-contention knot: FIXME `0459` (contention-aware spark gate) + FIXME `0408`'s perf half (Sudoku copy-per-guess). Before opening it, the user asked a pre-flight question — **are the user docs, examples, exemplar, and platforms actually updated for the new (v9 ctx-vtable handle model) concurrency approach?** — and then reframed the perf problem itself.

### Pre-flight audit — the base is sound (2026-07-02)

An independent read-only audit (Explore agent, not a re-read of the S98 record) checked all four surfaces against the live v9 model and re-ran the `exemplar_web` E2E tests:

1. **`user/` docs** — `concurrency.md` + `writing-platforms.md` describe the v9 model (poll-in/wake-out only, ctx-vtable, opaque handles); no stale token/descriptor-on-value language leaks to users. **CURRENT.**
2. **`examples/`** — `32-concurrency-combinators.cl` teaches `race`/`select`/`timeout`, cross-linked from the guide. **CURRENT**, one soft gap: no network/platform-authoring example in the teaching sequence.
3. **`exemplar/`** — `platforms/web/src/lib.rs` genuinely uses v9 (`HostCtx`, `reactor.acquire`), touched post-pivot; `exemplar_web` E2E **passes** (independently re-run). **CURRENT.**
4. **`cranelisp-platform` + `stdio`** — v9-shaped; `declare_concurrent_platform!` gone from live code. **CURRENT**, one soft gap: stale macro wording in `design/platform/{platform,poll-support}.md`.

**Verdict:** S98's self-report holds up. Nothing blocks opening the knot; the two soft gaps fold in as cheap housekeeping.

### The reframe (design conversation, user-led 2026-07-02)

The user set the frame that governs scope:

- **This is Phase-H memory-layout territory, entered deliberately.** The question is *not* "optimise the RC model" but "**are there cheap changes worth doing *before* the stack-allocated model — ones that survive it, not that Phase H throws away?**" Every candidate is filtered on: (1) survives Phase H, (2) the win lives in the substrate/stdlib, not in exemplar hand-tuning ("the showcase can't be passable only when hand-optimised").
- **Keep nested ADTs.** No bitmask/`0416` dodge — a `Vec` of heap-allocated ADTs is a genuinely common case worth optimising *for*. We commit to making "copy a `Vec` of shared heap ADTs under speculative parallelism" fast, not to sidestepping it.
- **Target performance model:** spark until cores saturate, then each core runs at a *slight discount to serial* — provided contention is handled well. Mechanically: a saturation-shaped gate (spark iff spare capacity, inline-when-saturated) **plus** contention driven to near-zero.
- **We are only *probabilistically* better than serial** — speculative search does more total work than serial (losing branches). So "always beats serial" is the wrong target; "near-serial per-core throughput + real speedup on parallel-friendly instances + never dramatically slower" is the right one. This means the observed "10×" is **confounded** and must be decomposed before any mechanism is funded.

## Scope

**Arch revisions R1–R6 folded (binding; full text in the Phase-2 section).** They sharpen — do not change — the candidate framing. The two that alter Wave-0 *behaviour*: (R2) the **thread-caching global-allocator swap is the first-line (a) cure**, not merely a probe — it lives at the binary/`int` surface (`#[global_allocator]`, feature-gated, byte-identical-off), tried before any per-worker arena (which drops to contingent-on-contingent and must be Phase-H-region-subsumable if funded); (R4) the **non-atomic-RC probe is a backend codegen switch** (`heap.rs` + `intrinsics/rc.rs`, env-gated, byte-identical-off), **documented unsound above 1 worker and excluded from the canonical `cargo nextest run`**. (R1) read the (a)/(b) split off **user-vs-sys time** and hold the "≈1.4×" guess loosely (sys-dominance ⇒ prior toward (a)). (R5) the refutation "stop" branch still lands the F1–F4 fixtures + doc-scope corrections. (R6) allocator-swap and arena stay distinct work-items.

### Wave 0 — Measurement pre-wave (COMMITTED; gates everything downstream)

Build a falsification-oriented measurement harness that decomposes the "10×" and produces a **funding decision** for the mechanism waves. Not illustrative — built to be able to tell us the hypothesis is wrong.

**Falsifiable hypothesis:** the "10×" = *serial luck × speculative waste × contention*; only contention is a substrate/RC problem; contention is small (order ~1.4×, to confirm) and splits into **(a) allocator-lock** and **(b) atomic-RC cache-line bouncing**. Refutation (contention dominant even at saturation) ⇒ **stop and re-sequence into Phase H.**

**Fixtures** (rebuild the S94 ladder cleanly so each isolates one term):
- **F1 naked-singles** (branching factor 1, no guessing) → pure **machinery tax**, no waste, no real parallelism.
- **F2 needed-reduce over ADT-copy** (all results consumed, no speculation) → **clean contention**; the honest witness for "slight discount per core". Also settles whether the S94 D&C row was a reduce or a search.
- **F3 inverted search** (answer in the last serial-tried branch) → **best-case upside**.
- **F4 real Sudoku instance(s)** → the confounded reference, kept only to reconcile.

**Configs / knobs:**
- Pool size: serial (`CRANELISP_NO_LENIENT=1`) / 1-thread-pool (lenient on, single worker) / N-thread-pool. *(First confirm the pool-size knob — likely the rayon thread-count env — so the key isolation is near-free.)*
- Allocator probe: system vs thread-caching (mimalloc/jemalloc) via feature-gated `#[global_allocator]`. Collapse of sys-time ⇒ confirms (a) **and** yields a near-free partial cure.
- RC-atomicity probe: atomic vs non-atomic RC (sound only at 1-thread-pool). `1-thread × non-atomic` vs `1-thread × atomic` isolates the atomic-*instruction* cost; gap to `N-thread × atomic` isolates the **bouncing**.

**Metrics:** wall + **user and sys separately** (contention is CPU-burn before it is wall-time when cores are spare — also run F2 under saturating background load); instrumented **RC-op count** + **alloc count** (confirm the copy-per-node volume directly).

**Decision table (the deliverable):**

| Measurement outcome | Funds |
|---|---|
| (a) allocator-lock dominant | thread-caching allocator swap and/or per-worker arena |
| (b) atomic-RC bouncing dominant | capture-by-borrow across structured fork-join |
| contention small, waste/luck dominant | mostly `0459` (saturation gate + cancellation); RC/arena shrinks/defers |
| contention dominant even at saturation | **stop — Phase-H memory work; re-sequence** |

### Wave 1+ — Mechanism waves (CONTINGENT on Wave 0; candidates, not commitments)

Candidate cures, each pre-vetted against the survives-Phase-H + substrate-not-exemplar filter. Which get funded, and how hard, is decided by Wave 0:

- **(a) Thread-local allocation arena / thread-caching allocator** — kills allocator-lock contention; RC-orthogonal; a stepping-stone toward the Phase-H region allocator, not throwaway.
- **(b) Capture-by-borrow across structured fork-join** — the interesting one: a sparked branch's capture of its enclosing scope is a **borrow**, not a retain, because structured join proves the parent outlives the spark → eliminates the per-copy atomic-RC traffic on shared parent cells *without* Phase-H non-atomic RC. Takes the **coarse** version (retain only what escapes via the branch's return value, via the existing consuming convention); stops short of full escape analysis (which is Phase H).
- **Saturation-shaped gate (`0459`)** — spark iff spare capacity, inline-when-saturated; restores the floor (safety net) and converts the now-cheap branches into real speedup. Survives Phase H (scheduling, not memory); threshold self-recalibrates as allocation gets cheaper.
- **Floor-claim scoping** (`0459` doc half, `lenient-eval.md` §2.6.2/§3.6.3) — scope "never slower than serial" to spark-machinery overhead vs per-branch user contention. Cheap, lands regardless.
- **Exemplar as witness** (`0408` perf half) — the Sudoku exemplar adopts the substrate wins and *demonstrates* a real speedup on an **idiomatic** (not hand-tuned) grid; re-include `solver/test-hard-puzzle` once it solves in fast-test time. Must remain nested-ADT (no bitmask).

### B. Opportunistic housekeeping (surfaced by the audit, cheap)

- **`/examples`** — add one network/platform-authoring example (poll-shape server accept/read leaf).
- **`/design`(platform)** — sweep `design/platform/{platform,poll-support}.md` for stale `declare_concurrent_platform!` references.

### Out of scope

- **Phase H itself** (release/Tier-2 backend; full escape analysis, region alloc, Perceus reuse, non-atomic RC) — unchanged sequencing. This sprint's cures are the *pre-Phase-H, survives-Phase-H* subset only.
- **`0416` bitwise intrinsics** — parked; explicitly *not* the lever (keep nested ADTs). Independently nice; revisit later.
- **`0430`, `0050`/`0052`/`0365`, `0460`** — unchanged parked/opportunistic status.

## FIXME debt

| FIXME | Target skill | Status | Notes |
|---|---|---|---|
| 0459 | /backend | **substance delivered → defer remainder to Phase-H** | Contention-gate ask delivered as the opt-in **saturation gate** (1c); floor-claim **scoped** (lenient-eval §2.6.2/§3.6.3, `9fe0955`). Remainder (default-on + a gate that actually *restores* the floor) = the Phase-H (b)-cure (ring2-rc §5.5.2.7). `/backend` to set `status: deferred → Phase-H` (only the target skill may). |
| 0461 | /design | **RESOLVED + deleted** (`02f519b`) | Capture-by-borrow contract satisfied; outcome + ParBind soundness caveat recorded in ring2-rc §5.5.2. |
| 0462 | /design | **RESOLVED + deleted** (`02f519b`) | Volume prediction refuted; re-diagnosis → ring2-rc §5.5.2.6 + the Phase-H (b)-cure forward item §5.5.2.7. |
| 0408 | /port | open (narrowed) | Exemplar-as-witness (perf half); nested-ADT, idiomatic |
| 0416 | /arch | parked | NOT the lever — keep nested ADTs |
| 0430 | /design | deferred | off-track (docstring regen), unchanged |
| 0460 | /qa | opportunistic | drain if slack |
| 0050/0052/0365 | /int·/repl·/spec | parked (Phase H) | unchanged |

## Architecture review (Phase 2)

**Reviewer:** `/arch` · **Date:** 2026-07-02 · **Verdict:** **SIGN-OFF WITH REVISIONS** (all revisions are additive scoping/guardrails; none re-open the scope). Proceed to Phase 3.

Docs consulted: `effect-concurrency.md` §3/§3.1/§6/§8.1/§12.4.3, `lenient-eval.md` §2.5/§2.6/§3.6/§4.4, `ring2-rc.md` §5.5/§5.6/§6 (Decision 24), `bounded-contexts.md` §3/§4b, Principles 8/18/21, FIXMEs 0459/0408/0494. Source verified: RC inc/dec are emitted **inline by the backend** as Cranelift `atomic_rmw` (`crates/cranelisp-backend/src/heap.rs:178/208/302`), *not* via an intrinsic — this determines ruling 4. No `#[global_allocator]` is set anywhere today.

### 1. Technical coherence of the reframe — SOUND

The decomposition "10× = serial luck × speculative waste × contention; only contention is substrate-fixable; contention = (a) allocator-lock + (b) atomic-RC bouncing" is architecturally sound and matches the two serializing resources already named in `effect-concurrency.md` §3.1. The F1–F4 fixture ladder isolates the terms cleanly: F1 machinery-tax (spark/IVar/pool overhead — this is where rayon scheduling/granularity cost is accounted, *separately* from contention, so it is not a missing term), F2 clean contention (the honest per-core-discount witness), F3 upside, F4 confounded reference. No term is missing or mis-attributed.

**One refinement (fold into Wave 0 reading, not a scope change):** the user/sys split is itself the (a)-vs-(b) discriminator. Allocator-lock (a) burns **sys** time (mmap/munmap/futex); atomic-RC bouncing (b) burns **user** time + IPC stall. The 0408 ladder is **sys-dominated** (~21s sys vs ~43s user on the Sudoku row) — a prior toward **(a) allocator-lock as the larger term**, which is the *best* case for Principle 8 because (a)'s cure (allocator swap) is the most survives-Phase-H and near-free. Corollary: the hypothesis's pre-labelled "contention ≈1.4×" is a guess in tension with the 10× sys-dominated raw number; hold it loosely — Wave 0 exists to correct it, and it plausibly lands well above 1.4× with (a) dominant. (Recorded in `effect-concurrency.md` §3.1, S99 correction.)

### 2. Capture-by-borrow across structured fork-join (cure b) — SOUND, with a hard soundness boundary (pinned)

This is the load-bearing novel idea and it holds up — **provided** it is built as a *generalisation of the existing `borrowed_vars` discipline* (`ring2-rc.md` §5.5), not as a new escape analysis. Assessment:

- **Sound against Decision 24 / borrowed-Var discipline.** §5.5 already establishes "a binding that reads a field from a still-live owner skips both inc and dec — the owner still owns it." A structurally-joined spark's capture is the *same shape*: the parent frame is the still-live owner; the spark borrows. This is a new *binding-introduction site* (spark-capture) for an existing rule, not a new rule. It is **safer** than the §5.5 match-arm case: Cranelisp values are immutable, so there is no Vec-COW-mutate-through-borrow hazard (the very hazard §5.5 gates last-use against). The borrow is rc-invisible, which *preserves* the parent's COW-last-use rc reasoning — it may even improve COW hit-rate, since today's inc-on-capture inflates rc during the spark's life and defeats parent-side mutate-in-place.

- **The structured-join lifetime guarantee does justify the elision — but only for the joined subset.** For rayon fork-join / `Par` / the apply-arg create-gate, the expression does not return until every branch joins (spec §12.4.3), and the parent's scope-cleanup dec runs *after* the join → the captured cell is live across the whole spark. **Structural, not analytical.** **BOUNDARY (load-bearing): this MUST NOT apply to a detached launch (`LaunchContinue`, §8.1)** — a fire-and-forget effect has no join inside the parent's dynamic extent, so its captures MUST retain. The joined-vs-detached grouping discriminator (`effect-concurrency.md` §, the `Par`/`LaunchContinue` decision) already carries the signal; the gate reads it — no new analysis.

- **The coarse/full boundary is a clean, defensible Principle-8 line — IF held exactly here:** *structural join ⇒ borrow; anything needing value-flow analysis to prove non-escape ⇒ Phase H.* The **only** retain is on the spark's **return value**, and it MUST flow through the already-audited machinery — the consuming convention (Decision 24) at the join + the §5.6 capture-return-inc rule — with **no per-capture escape decision**. This leans on exactly the path S98 hardened (FIXME 0497), not new machinery. The slippery slope is real and named: the temptation to widen "borrow" from "captures of joined sparks" to "captures analysis says don't escape" IS Phase-H escape analysis and is out of scope.

- **Failure mode if we get borrow/retain wrong = another UAF like bug #2.** This is a "skip the inc" optimisation, the exact class of S98 bug #2 (FIXME 0494: `find_var_type_in_expr` starved a consuming-inc → heap corruption). Mitigation is structural: because the coarse version borrows *all* captures and retains *only* the return value via existing audited paths, there is no new traversal/classification with bug-#2-style blind spots. **The moment a bespoke "does this capture escape?" traversal is introduced, the bug-#2 risk returns** — which is why the boundary forbids it.

- **Manifestation.** Arch scope authority recorded in `effect-concurrency.md` §3.1 (S99 correction — the (b) in-track cure, previously routed only to Phase H). Backend-doc contract (ring2-rc §5.5 generalisation + lenient-eval §4.4) pinned for `/design`/backend via **FIXME 0461**, contingent on Wave-0 funding. The soundness boundary stands as the record whether funded now or deferred.

### 3. Survives-Phase-H filter — per candidate

| Candidate | Survives Phase H? | Ruling |
|---|---|---|
| Thread-caching **global-allocator swap** | **Yes, unambiguously** | Memory-model-orthogonal drop-in; Phase-H region allocator subsumes it. Also the cleanest Wave-0 probe + a near-free partial (a) cure. FUND-READY. |
| Per-worker **bump/region arena** | **Borderline — Phase-H-adjacent** | A bespoke per-worker region is close to Phase-H region allocation and risks being redone. **REVISION:** do not fund the arena unless Wave 0 proves the allocator swap alone is insufficient; if funded, shape it as a pool/cache Phase H's region allocator subsumes, not a bespoke arena. Allocator swap should be tried first and likely absorbs most of (a). |
| **Capture-by-borrow** | **Yes** | Borrowed/owned classification is permanent; Phase H feeds a sharper escape signal into the same axis (widen-not-replace). Clean — see ruling 2. |
| **Saturation-shaped spark gate (0459)** | **Yes** | Scheduling, not memory. Already framed in 0459/§3.1 as a create-gate refinement, rayon-side, reactor-independent. The static allocation/RC-density axis is exactly 0459's ask. |
| **Floor-claim scoping** | **Yes (trivially)** | Honesty, not mechanism; lands regardless of Wave 0. Half already in §3.1; 0459 is the backend-doc half. |
| **Exemplar-as-witness (0408)** | **Yes** | A demonstration, not a substrate change; adopts substrate wins, no hand-tuning (per the substrate-not-exemplar filter). |

**Phase-H-in-disguise flags:** (i) the per-worker arena (above); (ii) capture-by-borrow *if* built as an escape analysis rather than the coarse borrowed-Var generalisation (ruling 2). Both are guarded by revisions/boundaries, not blocks.

### 4. Public-API / cross-crate interface impact — NONE to `cranelisp-types`; all probes are internal or binary-surface

No candidate or knob touches `crates/cranelisp-types/`, any crate's `public-api.txt`, or a bounded-context edge type. Specifically:

- **Pool-size knob** — rayon thread-count env (`RAYON_NUM_THREADS`) + existing `CRANELISP_NO_LENIENT` / `CRANELISP_SPARK_BUDGET`. Env only, no type. *(First confirm the rayon knob is respected by the spark pool — likely free.)*
- **Allocator swap** — `#[global_allocator]` **must** live in the **binary surface** (`src/` / `cranelisp-exe-bundle`, the `/int` surface — Rust requires the global allocator in the root artefact), behind a Cargo feature `default = []` with a dev-dependency on mimalloc/jemalloc. **Byte-identical-off by construction:** with the feature off, no allocator static is emitted → the default system allocator, unchanged. It is **not** a `cranelisp-platform`/`-primitives`/`-intrinsics` concern (ruling 6). No public-API surface (a `#[global_allocator]` static is not public API).
- **Non-atomic-RC probe** — since RC is **backend-inline `atomic_rmw`** (verified above), this is a **backend codegen switch** (emit plain `iadd` / non-atomic load-store instead of `atomic_rmw`), gated by an env var read at codegen time (e.g. `CRANELISP_NONATOMIC_RC=1`), same family as `CRANELISP_NO_LENIENT`. **Byte-identical-off** (env unset → same `atomic_rmw` path). It spans **two loci** — the backend inline emission (`heap.rs`) *and* the intrinsic-side dec paths (`cranelisp-intrinsics/src/rc.rs`, `drop.rs`) — both owned by `/dev`(backend) (intrinsics is backend-paired, BC §4b), so no ownership tangle. It is an **unsound build above 1 worker** (as the scope states): it MUST be documented unsound, off by default, **excluded from the canonical `cargo nextest run`**, and never shipped. No cross-crate type, no `public-api.txt` change (an internal codegen branch / feature-gated fn body is not a surface change).

**No `cranelisp-types` edit is required this sprint.** If Wave 0 funds capture-by-borrow, the implementation is internal to backend RC emission (the `borrowed_vars` set + apply-arg emission) — still no boundary type.

### 5. The refutation branch as a Principle-8 gate — CONFIRMED (it is a legitimate successful outcome)

"Measurement says contention dominates even at core saturation ⇒ stop and re-sequence into Phase H" is a **legitimate, successful sprint outcome**, and Wave 0 is the right interim-architecture guard. This is Principle 8 operating *before* code exists: it refuses to fund an interim contention cure against a moving target (the unsettled Phase-H memory model) when measurement shows the interim cure cannot clear the bar without the structural work. It also honours Principle 21 (measure/model before mechanism). A sprint that outputs the decomposition + funding table + a defensible re-sequence decision has produced durable architectural knowledge and is not a failed sprint.

**REVISION (make the refutation branch always-productive):** even on the "stop" outcome, Wave 0 MUST still land (a) the **F1–F4 fixtures as committed, failing-not-ignored regression guards** per project discipline ("reproduced defects join the test suite permanently"; "keep reductions as small as possible"), and (b) the **doc-scope corrections** (floor-scoping — 0459 + §3.1) which are honesty-not-mechanism and land regardless. The "stop" branch re-sequences *mechanism* funding into Phase H; it does not discard the measurement harness or the honesty corrections.

### 6. Wave/ownership shape — mostly clean; one conflation to avoid

- **Wave 0 knobs** — backend codegen switch (non-atomic-RC) + `cranelisp-intrinsics` (RC dec paths) = `/dev`(backend); allocator swap = **binary/`int` surface** (see below); pool-size = env; F1–F4 fixtures + RC-op/alloc-count instrumentation = `/qa`. Metrics harness = `/qa`.
- **The allocator is NOT a runtime-library concern.** `#[global_allocator]` binds at the **binary root** (`/int` — `src/` / `cranelisp-exe-bundle`), not `cranelisp-platform`/`-primitives`/`-intrinsics`. **Do not conflate** the *allocator swap* (binary/int surface) with a *per-worker arena* (backend/intrinsics spark substrate) — they are different loci with different owners and different Phase-H survivability (ruling 3). Name them as two separate work-items if both are funded.
- **Spark gate (0459)** — backend (sparkability cost heuristic §2.2 + create-gate §3.6.2) = `/dev`(backend). Clean.
- **Capture-by-borrow** — backend RC emission (`borrowed_vars` + apply-arg emission) = `/dev`(backend). Clean.
- **Exemplar witness (0408)** — `/port`. Housekeeping: `/examples` (network example), `/design`(platform) (stale-macro sweep). Clean.

No ownership tangle beyond the allocator-vs-arena conflation flagged above.

### Verdict — SIGN-OFF WITH REVISIONS

Scope is technically coherent; the reframe is sound; the novel idea (capture-by-borrow) is sound within a pinned boundary; nothing touches `cranelisp-types` or a public-API baseline; the refutation branch is a legitimate Principle-8 outcome. **Proceed to Phase 3.** Revisions for `/sprint` to fold into the scope (none re-open scope):

- **R1** — Wave 0 reading: use the user/sys split as the (a)-vs-(b) discriminator; hold "contention ≈1.4×" loosely (sys-dominance is a prior toward (a) dominant). *(Recorded in §3.1.)*
- **R2** — Allocator: fund the **thread-caching global-allocator swap first** (binary/`int` surface, feature-gated, byte-identical-off); fund a **per-worker arena only if** Wave 0 shows the swap is insufficient, and if so shape it to be Phase-H-region-subsumable (not a bespoke arena).
- **R3** — Capture-by-borrow: build **only** as the coarse borrowed-Var generalisation within the FIXME 0461 boundary (structural-join gate; return-value-only retain via existing consuming convention + §5.6; no per-capture escape analysis; excludes `LaunchContinue`). Any bespoke escape traversal is out of scope (bug-#2 class risk).
- **R4** — Non-atomic-RC probe is a **backend codegen switch** (not a library feature) spanning `heap.rs` + `intrinsics/rc.rs`; env-gated, byte-identical-off, documented unsound above 1 worker, **excluded from the canonical nextest run**.
- **R5** — Refutation ("stop") branch still lands the F1–F4 fixtures as committed failing-not-ignored guards + the doc-scope corrections (0459 + §3.1); it re-sequences mechanism funding, not the harness/honesty.
- **R6** — Keep the allocator-swap (binary/int) and per-worker-arena (backend/intrinsics) as **distinct** work-items with distinct owners; do not file them under one "allocator" concern.

Cross-crate interface work this sprint: **none** (no `cranelisp-types` edit). Manifestations landed by `/arch`: `effect-concurrency.md` §3.1 (S99 correction — the two-term contention cure split + capture-by-borrow candidate + soundness boundary); FIXME 0461 (`target: /design` — capture-by-borrow backend-doc contract, Wave-0-gated).

## Skill plans (Phase 3)

### Wave 1 — ablation study (user-directed 2026-07-02)

**Method:** each of the three cures built **behind its own toggle** (env/feature), re-benchmarked via `tests/perf/s99_measure.py` after it lands, marginal delta recorded in `tests/plan/s99-measurement.md`. Sound cures flip default-on at sprint close. **Serial pipeline** (shared-tree; one source-touching agent at a time). Ordered by (b)-dominance + "allocator last".

| Step | Cure | Skill(s) | Toggle | Notes |
|---|---|---|---|---|
| 1a | **Capture-by-borrow** design | /design (backend) | — | Pin the FIXME-0461 contract: coarse borrowed-Var generalisation, structural-join gate, return-value-only retain via existing consuming convention + ring2-rc §5.6, **excludes `LaunchContinue`**, no per-capture escape traversal (R3). Design-only. | **DONE** (`cbef1ed`) — contract in ring2-rc §5.5.2 + lenient-eval §4.4.1. Seam: `FnCompiler.spark_capture_borrow` flag set only around the 3 joined emission sites (`apply.rs:129`, `let_if.rs`, `par_bind.rs`); inc (`lambda.rs:156`) + drop-glue dec (`lambda.rs:183`) skip symmetrically; `LaunchContinue` never sets it. **Carve-out:** §4.5 dependent-`let` synthetic IVar keepalive captures stay retained. FIXME 0461 open, close at wave gate. |
| 1b | **Capture-by-borrow** impl | /dev (backend) → /review + /qa | `CRANELISP_CAPTURE_BORROW` | **DONE — NEGATIVE RESULT** (uncommitted at report time). Mechanism CORRECT + within-boundary (elides *exactly* the spark-capture incs; parallel `rc_inc` drops to the serial count; UAF exclusion guard green; 1807/1/0 byte-identical-off). **But recovers ~0% of (b):** spark-capture incs are only **hundreds** (F2 −897 of 170M; budget-bounded spark count × capture-arity ~1), while the dominant (b) traffic is the **in-leaf vec-COW cell-refcount bumps** (~81/copy × leaves ≈ 170M) — *inside* the computation, not fork-join captures, so borrow (correctly, by scope) never touches them. F4 wall "1.9×" = **false green** (search-path variance, verified). **Re-diagnosis → FIXME 0462.** ParBind-continuation borrow site has an **unverified lifetime-across-suspension concern** (captures live in a returned IO tree run later by the trampoline — parent may not outlive it; S98-0486 class) → **do NOT flip default-on**; land opt-in only. |
| 1c | **Saturation gate** (0459) | /dev (backend) measurement spike | `CRANELISP_SATURATION_GATE` | **DONE** (`961945a`) — caps spark budget at `current_num_threads()`; overflow inline (existing sequential lowering, no soundness surface); 1811/1/0 byte-identical-off. **Result: real but MARGINAL** — recovers **~9% user / ~7% wall** of F2 (b) (tight-spread, not false-green); F4 inconclusive (variance). Confines only *overflow* subtrees thread-local; top ~N branches still COW-bump shared cells; rc_inc unchanged. **Combined with 1b (~0%): neither in-scope cure moves the dominant (b) > single digits → the (b) driver is vec-COW leaf-refcount VOLUME = Phase-H (Perceus/mutate-in-place).** |
| 1d | **Allocator swap** — the (a) cure | /qa (benchmark; mimalloc already built 0.2) | `--features thread-caching-alloc` | **DONE** (`615307e`) — §10. F2 (clean) has **NO (a)/sys term** — mimalloc's F2 win is user-side alloc paths (−18%). F4 median **sys 6.7×↓** (not Wave-0's cherry-picked 23×), but median **user worsens**. **Coupling finding:** removing the allocator lock lets threads bounce shared-cell RC lines *more* — (a) traded for (b). Combined mimalloc+gate F2 wall −20%/user −23%. **Floor NOT restored** (F2 still 2.3× slower, F4 6–15×). **Recommend mimalloc OPT-IN, not default-on** (not worth a vendored-C dep until Phase-H removes (b)); Ferroc/rimalloc = Phase-H-adjacent follow-on. |
| — | Floor-claim scoping (0459 doc half) | /design (backend) | — | Lands regardless (honesty-not-mechanism). |

**Deferred out of Wave 1 (user):** cancellation / short-circuit search (`first-success` early-exit) — a scheduling/algorithmic speedup that recovers exhaustive-search waste, but would destroy the deterministic linear-speedup benchmark the ablation depends on. Follow-on once runtime cures settle.

## Waves (Phase 4)

_Mechanism-wave structure is written after Wave 0 reports (sized by the decision table). Wave 0 itself runs as a short serial pipeline (shared-tree constraint: one source-touching agent at a time):_

| Step | Skill | Crate/surface | Task | Status |
|---|---|---|---|---|
| 0.1 | /dev | cranelisp-backend (+intrinsics) | Confirm the pool-size knob (does the spark pool respect `RAYON_NUM_THREADS`?); implement the env-gated **non-atomic-RC codegen switch** (`heap.rs` + `intrinsics/rc.rs`, byte-identical-off, unsound>1-worker, excluded from canonical nextest); add **RC-op + alloc-count instrumentation** (env-gated counters). | **DONE** (`e63c4ca`) — pool knob free (`RAYON_NUM_THREADS`); `CRANELISP_NONATOMIC_RC` + `CRANELISP_RC_STATS`; 1798/1/0 byte-identical-off. Harness caveat: call `alloc::reset_counts()` before `main` (alloc counts are process-wide). |
| 0.2 | /dev | src/ (binary/`int`) + exe-bundle | Feature-gated **thread-caching `#[global_allocator]`** (mimalloc/jemalloc, `default=[]`, byte-identical-off). Doubles as the first-line (a) cure per R2. | **DONE** (`262bd07`) — mimalloc behind `--features thread-caching-alloc`; byte-identical-off 1798/1/0; exe-bundle (staticlib) untouched, harness measures `--run` in-process. |
| 0.3 | /qa | tests/ (+ harness) | Build **F1 naked-singles / F2 needed-reduce-ADT-copy / F3 inverted-search / F4 real-Sudoku** fixtures (free-standing, committed guards per R5); the measurement harness (each fixture × pool-size × allocator × RC-atomicity, collecting wall/user/sys + RC-op/alloc counts); run it; **report the decomposition + fill the decision table.** | **DONE** (`c9f4c0d`) — 4 fixtures + 4 correctness guards + harness + `tests/plan/s99-measurement.md`; 1802/1/0. Verdict below. |

### Wave 0 findings — the funding decision (2026-07-02, `/qa`)

Full report: `tests/plan/s99-measurement.md`. Headline: the hypothesis is **partly falsified, partly confirmed**, and it is **NOT the "stop→Phase-H" branch**.

- **The "10×" is essentially ALL contention.** Machinery tax is negligible (F1 +0.01s). Serial-luck and speculative-waste **cancel** — because `first-success` is **strict** (both apply-args are forced even under `CRANELISP_NO_LENIENT`, so the serial baseline pays the same "waste" as parallel). So the ratio is pure contention, not the confounded product we assumed. *(Side-finding: a **short-circuiting** serial search would be a different, harder bar — and cancellation, killing losing siblings once a winner is found, is the lever that recovers that waste for BOTH baselines. Scheduling-domain, 0459-adjacent.)*
- **Contention is far above the pencilled ≈1.4×:** F2 (clean, fixed-size) **3× slower parallel**; F4 (real Sudoku) up to **23× debug / ~5× release** post-mimalloc. So the "slight-discount-per-core" target is **not met today** (3× *slower* per core), and a Phase-H release backend alone does **not** fix it — the substrate cures are needed.
- **The (a)/(b) split CORRECTS arch prior R1.** The debug ladder's sys-dominance (which pointed at (a) allocator-lock) **did not survive to release**: on release it is **(b) atomic-RC bouncing that dominates** — F2 contention delta is **99% user / 1% sys**, F4 **~70% user / ~30% sys**. The user/sys *method* was right; the debug *numbers* misled the prior. **(b) capture-by-borrow is now the MAIN prize, not the secondary** — which raises the stakes on R3's soundness boundary.
- **RC/alloc counts confirmed exactly:** F2 = 81.0 rc_inc + 2.0 allocs per shared 81-cell copy (169.9M rc_inc / 2.1M copies). The "81 bumps + fresh cells per copy" claim is exact.
- **non-atomic vs atomic @1w:** the atomic *instruction* is cheap (F2 −13%); the expensive (b) is the **contended cache-line bouncing** (+18s user @Nw), which capture-by-borrow removes by **not emitting the ops at all** on joined captures — the right shape of cure.

**Decision-table verdict → MIX; fund both, sequenced:**

| Row | Fires? | Action |
|---|---|---|
| (a) allocator-lock dominant | partial (F4 only, ~30%) | **Fund allocator swap FIRST** — already built (0.2 mimalloc); the cure is *adopting* it (recovers F4 sys 23×↓, wall 4.8×↓); near-free, survives Phase H. Per R2, try before any arena. |
| (b) atomic-RC bouncing dominant | **YES (dominant)** | **Fund capture-by-borrow** — the F2 99% / F4 70% term; coarse borrowed-Var generalisation only, within the FIXME 0461 boundary (R3; bug-#2-class risk — now the main event). |
| contention small, waste/luck dominant | no | — (but the **gate 0459** stays a complement: throttles concurrent RC bouncing + converts cheap branches to speedup) |
| contention dominant even at saturation → stop | **no** | both cheap pre-Phase-H cures apply and are complementary. |

## Notes

- **Design conversation (user-led, 2026-07-02)** produced the reframe above: measure-first/decompose-the-10× before funding any mechanism; keep nested ADTs (no bitmask dodge); the survives-Phase-H + substrate-not-exemplar filter; the saturation-shaped-gate + contention-to-near-zero performance model; the probabilistic-better-than-serial framing that makes the raw "10×" a confounded number. The two candidate substrate cures (thread-local arena; capture-by-borrow across structured fork-join) are recorded as candidates gated on Wave 0, not commitments — per Principle 21 (actors + functions before synthesising a mechanism) and the measure-first discipline.
- **Pre-flight audit performed before Phase 1 scope** — verifying the previous sprint's Phase-6 self-report independently before trusting the roadmap's "next" pointer. Worth repeating whenever a sprint's close record is the sole basis for judging a prerequisite sound (generalises `memory/feedback_verify_fix_not_symptom_absence.md`'s "confirm behaviorally end-to-end").

## Outcome (Phase 7)

_Pending._
