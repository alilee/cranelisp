# Performance / parallel-execution backlog

**Owner:** `/arch`. **Status:** parked track — captured, not scheduled.

This document is the single owned home for the suspended performance / parallel-execution /
memory-model design arc closed at S105 (accept-done, user sign-off 2026-07-08). It replaces a
scatter of open FIXMEs so those items stop appearing in every Phase-1 and wave-gate scan while
their pinned analysis + provenance survive as pre-assembled scope input for when the perf track
is re-entered.

**Consolidating this arc is NOT re-entering it.** No perf implementation or design-argument
resolution happens by virtue of an item living here. Re-entry is a future sprint's decision,
gated on a measured trigger (Principle 8: the Phase-H structural cures — thread-local RC,
escape→stack/region, reuse tokens, value-layout flattening — remain the sequencing edge; none of
these items pulls that edge forward).

## Provenance discipline (required per entry)

Every migrated entry MUST carry, verbatim enough to act on without re-deriving:

1. **Origin line** — `FIXME NNNN · filed_by /skill · original target · sprint filed` (and
   `narrowed/diagnosed` sprints where the file recorded them).
2. **`refers_to` anchors** — the exact doc §sections + source paths the FIXME pinned.
3. **Pinned analysis** — the root cause / mechanism / measurement the FIXME had already
   isolated (this is the payload the arc paid for; losing it forces re-isolation).
4. **Re-entry trigger** — the measured condition under which the item becomes actionable
   (e.g. "measured GOT slab growth from redefinition churn", "an index-specific `ResultMode`
   consumer goes live", "II-B3 uniqueness machinery lands").
5. **Reversibility note** — whether the residual is monotone-sound-if-ignored (most are: they
   widen toward the conservative Owned/protect side).

## Structure (Phase 5 authoring target)

Group the 11 items + the /qa matrix note by their coupling, not by filing order:

- **§1 Ownership-lattice precision residuals** — 0521 (ResultMode ⊤ element), 0528
  (`result_unique` preservation), 0510 (`neq-string` has no `DefKind::Primitive` carrier),
  0526 (producer-side projection elision parallel-unsound → promoted to increment II).
  Common trigger: the increment-II uniqueness / index-specific-consumer machinery going live.
- **§2 Create-gate / lenient contention + density** — 0534 (F4 hard-parallel regression),
  0535 (density-aware depth allowance), 0536 (budget-inline depth leak), 0408 (Sudoku
  copy-per-guess allocator/atomic-RC contention — the floor-violation exemplar). Common
  trigger: contention-aware gate design OR the Phase-H RC/allocation cures.
- **§3 Regen / capture spec holes** — 0506 (§13.1 capture normalization spec), 0507 (T1
  trigger route + 0491 exclusion design holes). Trigger: the memory-model implementation
  sprint that reactivates these design surfaces.
- **§4 GOT slot-hole reclamation** — 0466. Trigger: measured GOT slab growth from redefinition
  churn.
- **§5 /qa verification-matrix growth** — 0499 / L-M1 (reference×referent×instantiation e2e
  matrix; growth driven by the parked backend `fn_as_value` seam). Recorded here so it
  re-enters with the perf track; the 0499 file itself closes under S106 WS-G once L-S1 lands.

## Deletion ownership (S106 WS-J) — Phase-2 ruling 2

`/arch` authors this doc (migrating each item's substance). Each owning skill then deletes ITS
OWN FIXME file once it confirms the substance is captured here — filing-skill-deletes, per the
cross-skill protocol. **A file is deleted ONLY after its §-entry below is filled — never before.**
The §-entries are now filled (AUTHORED S106 WS-J); `/arch` has deleted its own (0521, 0526). The
other owners delete on their next close-out step.

| FIXME(s) | Deletes its file | § home | Status |
|---|---|---|---|
| 0521, 0526 | `/arch` (own) | §1 | **DELETED S106 WS-J** (substance in §1) |
| 0528, 0510 | `/design` (narrow per crate) | §1 | captured — owner deletes |
| 0534, 0535, 0536 | `/design` (narrow per crate) | §2 | captured — owner deletes |
| 0408 | `/port` | §2 | captured — owner deletes |
| 0506, 0507 | `/design` (narrow per crate) | §3 | captured — owner deletes |
| 0466 | `/design` (narrow per crate) | §4 | captured — owner deletes |
| 0499 / L-M1 | `/qa` (L-M1 note migrates here; the 0499 *file* closes under WS-G at S106 close once L-S1 lands — not deleted from here) | §5 | L-M1 captured — file closes under WS-G |

Count check: **11 FIXME files** (0521, 0526, 0528, 0510, 0534, 0535, 0536, 0408, 0506, 0507, 0466)
+ the **0499/L-M1 note** = the full WS-J set. `/design` deletions are narrow-per-crate: the owning
crate's `/design` slot deletes only the FIXMEs whose substance sits in a section it has confirmed.

---

## Item sections — the pre-assembled re-entry scope (Phase 5, AUTHORED S106 WS-J)

Each `###` entry carries the five-field provenance contract (Origin line · `refers_to` anchors ·
Pinned analysis · Re-entry trigger · Reversibility note), migrated verbatim-enough-to-act-on from
its FIXME file. Once an entry is filled, the corresponding FIXME file is deleted by its owner
(deletion table above). `/arch` deleted its own (0521, 0526) at authoring; the rest are captured
here for their owning skills to delete cleanly.

### §1 — Ownership-lattice precision residuals
Common re-entry trigger: increment-II uniqueness / index-specific-consumer machinery going live.

#### 0521 — `ResultMode` needs a ⊤ element ("may alias MULTIPLE distinct params")
- **Origin** — FIXME 0521 · filed_by `/dev` · target `/arch` · sprint 102.
- **`refers_to`** — `crates/cranelisp-types/src/ownership.rs` (`ResultMode`);
  `design/typecheck/ownership-inference.md` §13.6(c); `design/arch/ownership-inference.md` §3.3.
- **Pinned analysis** — the 3-element lattice `{Fresh, ProjectionOf(usize), AliasOf(usize)}` (FIXME
  0520, landed S102 in `cranelisp-typecheck`, fixed the pass5 join so a partial-control-flow param
  return no longer collapses to `Fresh`) is **complete for the single-param case** but cannot
  express "may alias param 0 OR param 1" — the multi-distinct-param `(if c v w)` shape (`v`,`w`
  DIFFERENT params both reaching the result). 0520 chose the sound conservative representative
  **`AliasOf(lowest reaching index)`**: sound for the live binary `result == Fresh` gate consumer
  (`return_is_fresh_by_summary`, `cranelisp-backend/src/compiler/fn_compiler.rs` — any not-`Fresh`
  keeps the return protect), strictly more sound than pre-0520 `Fresh` (which elided protect on a
  possibly-returned param — a latent UAF), but imprecise for a hypothetical index-specific consumer.
  `walk_apply` composition (`transfer.rs`) maps `AliasOf(k) → arg_origins[k]`; a callee summarised
  `AliasOf(0)` under-reports on `(pick fresh p)` (caller passes fresh at 0, param at 1: caller
  composes `Fresh`, and a direct-`Apply` body would elide its own protect). No index-specific
  composition consumer is live at increment I (only the binary gate; a multi-param body is an
  `if`/`match`, never a direct `Apply`), so it is a **latent precision/soundness residual, not a
  live defect**. Cure: add a distinct ⊤ element (`MayAliasParam`/`AliasOfAny`, index-free) that the
  join maps the multi-distinct/mixed-kind case to and `walk_apply` treats as unconditionally
  not-`Fresh` (never resolving to a single arg) — closes the `(pick fresh p)` hole. A
  `cranelisp-types` carrier change (new variant + `#[serde(default)]` `Fresh`) + a
  `CACHE_SCHEMA_VERSION` bump in the same change-set.
- **Re-entry trigger** — co-land with the **first backend consumer that reads the `AliasOf` INDEX**
  (rather than the binary `Fresh` test): part 12/16 borrow-elision keyed off the specific param
  (`design/backend/ownership-codegen.md`).
- **Reversibility** — only ever widens a value away from `Fresh` ⇒ monotone-sound, additive to
  reverse. Until the index-specific consumer exists the 0520 lowest-index representative is sound for
  every live consumer.

#### 0528 — `result_unique` does not model uniqueness-PRESERVATION (unique-in ⇒ unique-out)
- **Origin** — FIXME 0528 · filed_by `/dev` · target `/design` · sprint 103.
- **`refers_to`** — `design/typecheck/ownership-inference.md` §7.2 (`result_unique` chaining);
  `design/backend/ownership-codegen.md` §6.4/§14.3 (II-G2 chaining metric).
- **Pinned analysis** — the increment-II backend half (II-B2 reuse tokens, `cranelisp-backend`) is
  landed and consumes write-path facts correctly (`reuse_hit`/`reuse_miss` runtime tallies at the COW
  arms `vec_codegen.rs`; `unique_static` check-elision off the fresh-producing Vec node
  `node_unique_static` elides the dynamic `rc==1` probe — verified `(vec-set [10 20 30] 0 99)` takes
  the proof-elided in-place arm, `reuse_hit=1`). Three of four II-B2 flips are GREEN; the fourth
  `tests/ownership_reuse.rs::chaining_toggle_off_allocates_intermediate` stays **RED**, cause entirely
  typecheck-side. Empirical root cause (`CHAIN_SRC` fixture — fused `(mapf inc (mapf dec v))` with an
  in-place `map-go`): the only `unique_static = Some(true)` fact is on the `[]` empty-vec literal in
  `(build [] 0 64)` (a fresh literal that already transfers, changes no alloc); `mapf`/`map-go` get
  **`result_unique = false`** so the inner `(mapf dec v)` is not `is_direct_fresh`, gets no
  `unique_static`, and the chaining proof never propagates; the two `map-go` first-iteration
  `vec-set`s each COW-**copy** (the `(vec-len v)` arg forces a Decision-24 consuming inc so `v` is
  rc==2 in `map-go`) IDENTICALLY on/off ⇒ `allocs=6`, `reuse_hit=190 reuse_miss=2` on both polarities
  ⇒ the test's `on < off` never holds. `result_unique` is computed intraprocedurally from the return
  SHAPE (`uniqueness.rs::is_fresh_unique_value`): a returned bound `Var` counts only if in
  `fresh_bindings`; a **param** returned unchanged (`map-go` base `(if (eq-i64 i n) v …)`) is never
  fresh ⇒ `result_unique = false`. But `map-go` is uniqueness-**PRESERVING** (given unique `v` it
  returns `v` unchanged or the in-place-mutated `v` — always the same unique root), the exact property
  the `(map f (map g v))` fusion (the design's own II-G2 witness §6.4/§14.3) rests on. Cure: extend
  the CS-3 uniqueness stratum so `result_unique` proves via **param-uniqueness preservation** (a
  "unique-in ⇒ unique-out" summary bit / a param-index the result aliases + the caller minting
  `unique_static` when it passes a proven-unique arg), landing `unique_static` on the `vec-set`
  consuming-use sites so the already-landed backend check-elision fires there (currently only fires
  for fresh-node Vec args per the §6.4 HARD requirement).
- **Re-entry trigger** — the II-B2 uniqueness / reuse-token machinery live **and** the
  `chaining_toggle_off_allocates_intermediate` flip required (a joint `/backend` + `/typecheck`
  B1/B2 deliverable; the backend half is complete, the `result_unique` chaining is the missing
  precondition).
- **Reversibility** — no spec change; an analysis-precision extension, monotone-sound — absent the new
  proof everything degrades to the dynamic `rc==1` token, exactly as today.

#### 0510 — `neq-string` has no `DefKind::Primitive` entry to carry declared facts
- **Origin** — FIXME 0510 · filed_by `/dev` (cranelisp-primitives) · target `/design`
  (cranelisp-backend) · sprint 102.
- **`refers_to`** — `design/typecheck/ownership-inference.md` §13.4 (the `neq-string` bullet + the
  coverage verdict); `design/backend/ring2-rc.md` §3.3 (the `neq-string` audit row, FIXME 0504).
- **Pinned analysis** — §13.4 lists `neq-string` as a covered leaf, but as-built `neq-string` has
  **no `ModuleEntry` in `cranelisp-primitives`**: it is shim-only (`extern_shims()` harvests its fn
  ptr for GOT population; reached exclusively through the `Eq.!=` trait-dispatch path,
  `cranelisp-typecheck/src/traits/dispatch.rs:177` maps `("Eq","!=","String") → "neq-string"`),
  registered in neither `ring0/ring1/ring3_primitives()` nor the vec-query family. So CS-B has no
  `DefKind::Primitive { mode_summary }` leaf for pass5 to read via `ModuleEntry::mode_summary()`;
  pass5's `Apply` classification of `(!= s1 s2)` (String) chain-follows to a missing entry ⇒ the
  Decision-24 conservative `Owned` default ⇒ `s1`/`s2` widen to `Owned`. **Asymmetric** with `str-eq`
  (`==`), a registered `ring1` entry that DOES get the declared `Borrowed` facts. Precision loss only
  (monotone-sound), not a correctness defect. CS-B populated every entry that exists, **transcribed
  the `neq-string` 0504 audit row into the classifier anyway** (`ownership_facts::declared_mode_summary`
  lists it in the only-read `Borrowed` set — unit-tested `neq_string_transcribes_the_0504_borrowed_row`
  — so IF an entry is ever registered it gets correct facts by construction), but did NOT register a
  new entry (a table change that would perturb name-resolution + the golden corpus / harvest
  invariant). Cure options: **(a)** register `neq-string` as a `ring1` `PrimitiveDef` entry symmetric
  with `str-eq` (assess vs Q1/`extern_shims` invariants; a pure table-registration change, no
  `ownership_facts` edit since the classifier already encodes the facts); **(b)** accept the
  conservative `Owned` default for the entry-less `neq-*` family (matching `neq-i64/f64/bool`, also
  shim-only trait-dispatch targets) and amend the §13.4 verdict to name `neq-string` as a
  trait-dispatch leaf outside the declared-fact table (like `sconcat`'s `PrimitiveExtern` scope cut)
  — a doc amendment, no code.
- **Re-entry trigger** — a memory-model implementation sprint electing to close the `==`/`!=`
  precision asymmetry for String args (or the broader `neq-*` family declared-fact coverage).
  Non-blocking for CS-B / CS-1..4 / the L-D3e per-row guards.
- **Reversibility** — precision loss only, monotone-sound; option (a) is a pure table registration,
  option (b) a doc amendment — both additive/reversible.

#### 0526 — §3.3 producer-side projection elision is parallel-unsound (promoted to increment II)
- **Origin** — FIXME 0526 · filed_by `/dev` (cranelisp-backend, S102 Wave 14) · target `/arch`
  (retargeted by `/sprint` 2026-07-05 from `/design`: no `/design` skill exists and the
  producer-side-vs-consumer-side memory-model soundness + increment-II framing is a cross-boundary
  `/arch` ruling; the `ownership-codegen.md` content edits remain `/backend`'s on `/arch`'s ruling) ·
  sprint 102. §3.3 re-frame authored S103 Phase 3 by `/design`(backend).
- **`refers_to`** — `design/backend/ownership-codegen.md` §3.3 (Result modes and provenance — the
  `compute_last_uses` extension; the §3.3 AS-BUILT box + the S103 RE-FRAME box + the §14.2 II-B3
  ladder).
- **Pinned analysis** — §3.3 specified **producer-side** in-frame projection elision (elide the
  `vec-get` element inc unconditionally at the read when the ownership pass set a `provenance` fact,
  materialize/lend at every consumer, keep the root live across the frame via the `compute_last_uses`
  extension; + `ResultMode::ProjectionOf` propagation across the function-return boundary).
  Implementation (S102 Wave 14) proved it **parallel-unsound** and reverted it. Root cause: a borrowed
  view that **escapes the producing function** (returned — `get0 [v] (vec-get v 0)` — stored into a
  Vec/ADT, or passed to an `Owned` position) carries no protective reference; under lenient parallel
  eval a sibling strand's COW/free of the root races the borrowed read. Reproduced as **f4_sudoku
  same-seed non-determinism** under `MALLOC_PERTURB_` (release false-greened; debug + same-seed
  repetition exposed it — `memory/feedback_verify_fix_not_symptom_absence.md`). `compute_last_uses`
  orders *in-frame* liveness but cannot order across the backend's spark-frame restructuring (the
  FIXME-0525 lesson). What landed instead (I-G1 100%, F1 `rc_inc` 1.54%→100%): a **consumer-driven**
  elision — a direct `vec-get` projection passed DIRECTLY into a `Borrowed` parameter collapses its
  inc+dec pair (the sole shape where the borrow provably never escapes the enclosing expression and
  never outlives the root's fork-join-guaranteed liveness). Captures the entire F1 machinery-tax class
  but NOT the return-boundary `ProjectionOf`/`AliasOf` propagation, the `Let`-binding `borrowed_vars`
  join, or the `compute_last_uses` extension. **S103 re-frame** (per the `/arch` Phase-2 direction 3 +
  gating from direction 1): consumer-driven is the increment-I **terminal** state (settled, I-G1 100%,
  no further backend work owed at increment I); the producer-side / escaping-projection model
  **promotes to increment II**, gated by the **Q4 uniqueness/confinement proof** (a projection may be
  lent past the consumer seam only when its root is proved `Confined` OR uniquely owned across the
  escape — coupled to the reuse-token / static-uniqueness machinery §6.4 + the confinement axis §5),
  staged as the **II-B3 deferred rider** in the §14.2 ladder (past the close-short seam; serves no
  II-G gate — I-G1 is already 100% on the consumer-driven seam). Confinement is *necessary* but the
  escape/return boundary is the sharper discriminant (F1's `vec-get` is classified Crossing yet the
  consumer-driven elision is safe there because the borrow does not escape).
- **Re-entry trigger** — **II-B3** (the increment-II uniqueness/confinement machinery) landing: the
  escaping-projection producer-side elision reactivates only when a `Confined`/unique proof across the
  escape is available.
- **Reversibility** — byte-identical-off holds (the whole seam sits behind the moded summary check);
  no `cranelisp-types` or typecheck change is implied — the `provenance`/`ProjectionOf` site facts are
  still sound and still emitted, the backend consumes a strict subset at increment I and a wider
  subset when II-B3 lands. Monotone.

### §2 — Create-gate / lenient contention + density
Common re-entry trigger: contention-aware gate design OR the Phase-H RC/allocation cures.

#### 0534 — F4-hard N-worker regresses ~100× under lenient eval (II-G3 fails)
- **Origin** — FIXME 0534 · filed_by `/qa` · target `/design` (re-pointed from `/backend` after the
  `/dev`(backend) ablation REFUTED the filed hypothesis) · sprint 103; diagnosed_by `/dev`(backend)
  2026-07-06 sprint 103.
- **`refers_to`** — `tests/plan/s100-ownership-verification.md` §2.3 (II-G3);
  `design/arch/effect-concurrency.md` §3.1; `design/backend/lenient-eval.md` §2.7 (B4
  density-admission axis); `design/backend/ownership-codegen.md` §13.4.
- **Pinned analysis** — II-G3 (F4-hard median N-worker ≤ 2× serial) fails catastrophically (**121×**
  — 108.8s vs 0.91s serial). **PROFILING ATTRIBUTION (the ~110s PROVEN, not "just contention"):** the
  wall is **rayon task-scheduling overhead (futex wake/park + `sched_yield`) paid ~13 µs per spark ×
  9.45 M ultra-fine score-0 sparks whose real body is ~20 ns**. It is NOT allocator-lock contention,
  NOT atomic-RC bouncing, NOT redundant recomputation, NOT livelock. Evidence: **(A)** 240% CPU on 10
  cores ⇒ ~7.6 cores idle ⇒ parking not spinning; `wchan` = `futex_do_wait`. **(B)** strace: 50.53%
  `sched_yield` + 49.33% `futex`, 0.07% `brk`/`madvise`/`mmap` ⇒ allocator refuted at the syscall
  layer (glibc malloc stays in userspace). **(C)** `spawns = 9.45M`, `claim_wins == spawns` ⇒ no
  redundant recomputation (`rc_inc` identical serial-vs-ON at 31.7M); the IVar spin-loop (`ivar.rs`
  ~:441) burns ~896M iters ≈ 4–9s (secondary, not dominant). **(D) DECISIVE:** wall ~linear in spawn
  count (`SPARK_BUDGET=0`→1.18s/0 spawns; `=4`→3.34s/65K; `SATURATION_GATE` cap10→72.8s/3.04M;
  default cap40→116s/9.45M) ⇒ fixed per-task scheduling cost × task count, ~600× overhead ratio
  (13 µs vs 20 ns body). Root mechanism: F4's admitted sparks are the **104 score-0 fine
  accessor/projection pairs** in per-cell hot loops (`(let [c1 (cell-at g1 i) c2 (cell-at g2 i)] …)`),
  the consumer forces each IVar almost immediately ⇒ almost no exploitable parallelism yet every spark
  pays a full spawn→wake→run-20ns→park round-trip. The create-gate (`SPARK_BUDGET`) bounds *concurrent*
  in-flight sparks (memory O(cap)) but NOT the total spawn rate. **(E)** the B4-declines-coarse default
  (116s, 240% parked) is WORSE than admit-all `MAX=0` (~24s, 565% busy, 15.3M spawns): declining the
  coarse `solve-range` sparks while admitting the fine ones **strands** the fine sparks with no coarse
  structure to ride ⇒ naked wake/park round-trips. **ABLATION also REFUTED the filed
  increment-II-density hypothesis:** the density distribution is byte-identical at increment-I
  (`25ffe12`) and II HEAD (104 score-0 admit / 4 score-2 decline / 6 score-4 decline); it is NOT
  increment-II-introduced (increment-I HEAD reproduces the ~110s); the "8-33s → 108s regression" is
  **core-count/effective-parallelism sensitivity** (`RAYON_NUM_THREADS` 2→7.6s, 4→16.5s, 6→27.8s,
  10→112s; the S102 accept record `on=[8.38…33.0]` landed in the 2–6-effective-core band under residual
  load, the FIXME measured truly-idle 10 cores) — a measurement-condition false read, not a code
  regression. **§3.1 correction for `/arch`:** on F4-hard the dominant term is scheduler churn
  (`sched_yield` 50% + `futex` 49% of syscall time), NOT the allocator lock + atomic RC named in §3.1;
  Phase-H thread-local RC / reuse would NOT fix it (it is not RC-bound). The in-track cure is a
  **spark-overhead gate available now** — decline sparks whose body cost-to-run < cost-to-spawn (the
  score-0 accessor pairs) OR **hierarchical decline** (a declined coarse subtree suppresses nested
  fine sparks) — either kills F4's over-spark firehose. NOT a bounded backend tune: "no local signal
  distinguishes F4's harmful score-0 fine sparks from F1's beneficial `fib`/`reduce-tree` score-0
  compute sparks" — a static cost-model / body-size heuristic is a `/design` deliverable
  (`lenient-eval.md` §2.7), and tuning to F4 alone trades against the S102-accepted f3 benefit
  (−82% N-worker).
- **Re-entry trigger** — the contention-aware / spark-overhead gate design (the §2.7 static
  cost-model / hierarchical-decline lever). The successor FIXME 0535 (density-aware depth) is the S105
  continuation of this arc.
- **Reversibility** — the differential oracle is byte-identical-off throughout (correctness intact,
  every config exits 154); a perf-lane finding, no suite guard. II-G3 recommended re-scope: grade
  against the Phase-H composed end-state (III-G2 per §7 staging) OR keep it a tripwire at a realistic
  bar (≤ OFF: ownership-on must not be worse than the conservative lowering — currently VIOLATED ON
  112s vs OFF 15.9s, the real actionable signal).

#### 0535 — density-aware depth allowance (the S105 focus)
- **Origin** — FIXME 0535 · filed_by `/qa` · target `/design` · sprint 104.
- **`refers_to`** — `design/backend/lenient-eval.md` §2.8; `design/arch/effect-concurrency.md` §3.1;
  `tests/plan/s104-utilization-measurement.md` §8.7 (U-G1 regrade).
- **Pinned analysis** — S104 shipped a uniform depth cap `CRANELISP_SPARK_MAX_DEPTH =
  floor(log2(nproc))` (= 3 on the 10-core host) with worker-origin depth decline + backoff.
  Single-shot at D3 (§8.7): **F6** (heavy balanced pure compute) 3.10s → 0.82s (3.4×, peak ≈ 12) — the
  Regime-A win, thesis proven here; **F5** (fib D&C) 0.67s → 0.39s (1.7×, spawns 619K → ~14);
  **F4-hard** (alloc-contended search) 0.88s serial → ~2.27s at D=3 (the ~24× over-sparking pathology
  cured 13.1M → ~16 spawns, but F4 stays **above serial** — a mild floor regression vs D=1); **F3**
  0.53s → ~3.7s, same class. A **single uniform depth cannot satisfy both regimes**: the value that
  lets alloc-free strands go deep enough to win (F6 wants deep) is the same value that lets alloc-heavy
  strands recurse into contention (F4/F3 want shallow). D=3 is the compromise buying F6 (accepted per
  user trade) at a mild F4/F3 floor slip — the **U-G1 second half** regraded out of S104's utilization
  scope into this synthesis. The residual F4/F3 wall is NOT scheduling overhead (0534 proved that term
  was rayon park/wake per over-spark, now cured by the cap); it is the **alloc/RC-density contention
  class** — per-branch heap allocation + atomic-RC cache-bouncing (`effect-concurrency.md` §3.1,
  Decision 13) — which the depth cap bounds spark *count* but does not attack per-branch. Cure: **gate
  the depth allowance on the static alloc/RC-density signal** so the depth budget is a *function of the
  strand's density*, not a machine-wide constant — alloc-free/RC-quiet strands (F6 `spin` tail-loop,
  F5 pure `fib`) allowed deep (up to/beyond `floor(log2(nproc))`); alloc-heavy/RC-loud strands (F4/F3
  copy-per-guess + fine accessor traffic) held shallow (toward D=1). This is the **S104-utilization ×
  §3.1-contention synthesis** named as the S105 focus (user-directed 2026-07-07): the density signal
  is the same static alloc/RC-density axis §3.1 already calls for (the FIXME-0459 "contention-aware
  gate, static layer first" line), and §2.8 (the utilization depth mechanism) must consult the §3.1
  density classifier.
- **Re-entry trigger** — the S105 utilization × contention synthesis actioning: `/design` edits
  `lenient-eval.md` §2.8 + `effect-concurrency.md` §3.1, `/dev`(backend) implements, graded against
  the §8 F1–F6 lanes. (Static density layer only; the structural cures — thread-local RC /
  escape→stack/region / reuse — remain Phase-H per Principle 8, NOT pulled forward.)
- **Reversibility** — the in-track density-gate path, not the Phase-H cure. The F4 D=3 trade (mild
  floor slip vs D=1) is accepted for S104 to keep the F6 win; a density-aware depth recovers F4
  *without* surrendering F6. The fixtures already discriminate the two regimes by shape (U-G4 held) so
  F4/F3 (shallow arm) + F6/F5 (deep arm) are the acceptance instrument. Monotone.

#### 0536 — budget-inline depth leak (the create-gate inline arm advances no `SPARK_DEPTH`)
- **Origin** — FIXME 0536 · filed_by `/qa` · target `/design` (retarget to `/dev` directly if
  `/design` judges the §3.6 contract already covers it and only the code hook is missing) · sprint
  104.
- **`refers_to`** — `crates/cranelisp-intrinsics/src/ivar.rs` (the create-gate);
  `design/backend/lenient-eval.md` §3.6; `tests/plan/s104-utilization-measurement.md` §8.7.
- **Pinned analysis** — the create-gate (`lenient-eval.md` §3.6.2; `ivar.rs`) has two arms —
  budget-granted (allocates IVars/thunks + sparks) and over-budget **inline** (sequential arg
  codegen). The depth cap decides sparking by comparing the current `SPARK_DEPTH` against the cap. The
  **inline arm advances no `SPARK_DEPTH`**: a budget-inlined child executes at the SAME depth as its
  parent, so its own sparkable sub-args re-test the cap against an unincremented depth and **re-spark
  at the same level** ⇒ the intended depth ceiling is not enforced past the point where inlining kicks
  in. Consequence: **D cannot exceed ~log2(cap) without a backend hook on the inline arm**. At D=3 the
  fixtures are safely under the leak (F5 collapses 619K → ~14 spawns) but raising the cap re-exposes it
  — **F5 re-explodes to ~1.3M spawns at D=4** (the inline arm's un-advanced depth lets the
  fib-explosion re-populate). Load-bearing only when the depth budget wants to scale — exactly what
  0535's density-aware-depth deep arm asks for. Cure: **advance `SPARK_DEPTH` on the create-gate inline
  arm** (a budget-inlined child is one more level of nesting; its `SPARK_DEPTH` must increment just as
  a sparked child's would, so its sub-args test the cap against the correct deeper depth). The hook is
  on the inline arm of the create-gate in `ivar.rs` (and any parallel inline fallback in the backend
  emit) — a backend/intrinsics change, not design-only.
- **Re-entry trigger** — the depth-aware work (0535) wanting alloc-free strands *deeper* than D=3;
  this leak is the reason D cannot scale past ~log2(cap) until the inline arm advances depth. Dormant
  at the shipped D=3 default (no fixture crosses the leak there) — not an S104 defect, but it **caps
  the depth-aware work**.
- **Reversibility** — dormant/benign at D=3; a backend follow-on that unblocks depth scaling. Repro
  signal when actioned: F5 spawn count as a function of `CRANELISP_SPARK_MAX_DEPTH` (~14 at D=3, ~1.3M
  at D=4 today; after the fix D=4 must stay O(cores × depth)). Perf-lane (§8 F5 lane), not a nextest
  guard.

#### 0408 — Sudoku exemplar copy-per-guess allocator/atomic-RC contention (the floor-violation exemplar)
- **Origin** — FIXME 0408 · filed_by `/sprint` · target `/port` · sprint 86; narrowed 2026-06-27
  sprint 92 (the parallel-search EXPRESSION half is DONE S92; this tracks the PERF half only).
- **`refers_to`** — `exemplar/solver.cl`, `exemplar/grid.cl`, `exemplar/plan-exemplar.md` §"Wave 4
  Parallelism Opportunities Assessment", `exemplar/CLAUDE.md` §"Known Issues", `exemplar/tests.cl`;
  cross-note `design/backend/lenient-eval.md` §3.6.3 (the never-slower-than-serial floor).
- **Pinned analysis** — the S92 reshape parallelises the backtracking search **structurally**
  (divide-and-conquer over candidate digits via `first-success` + `solve-range`; slice-1 lenient eval
  auto-sparks the two independent recursive solves, zero `spark`/`par` in source), validated 40/40
  green under both default-parallel and `NO_LENIENT`-serial (`solver/test-solve-parallel-equiv`, full
  solution pinned). But parallel is **~10× SLOWER than serial** — a never-slower-than-serial **floor
  VIOLATION** (S94: ~20s parallel vs ~1.9s serial, **sys-time dominated** ~21s sys parallel vs ~0.05s
  serial; user ~43s = many cores spinning). Shape-independent (the S92 `solve-range` apply-arg shape
  and the S94 stdlib `par-map-reduce` shape measure identically ~19.5s/~1.7s). Mechanism (S94,
  free-standing repro ladder): the **immutable copy-per-edit grid** dominates —
  `eliminate`/`set-cell`/`assoc` copy the full 81-cell Vec on every modification (quadratic), the Vec
  holds heap-allocated RC-managed `Cell` ADTs so each copy atomically bumps 81 element RCs and each
  guess allocates fresh `Cell`s; under the spark substrate this generates **allocator-lock +
  atomic-RC contention** across workers — that contention (not the create-gate's spark *count*, which
  it does bound) blows up `sys` time and breaks the floor. The repro ladder confirms the penalty
  scales with allocation/RC not compute: pure compute 1.3s/0.9s (sys 0.04) → int-Vec copy 3.1s/2.85s
  (sys 0.87) → ADT-Vec copy 6.9s/5.0s (sys 2.3) → Sudoku ~20s/~1.9s (sys ~21). Two compounding causes:
  copy-per-guess representation (the dominant, fixable one — allocator/atomic-RC contention under
  parallelism, which is *why* parallel is actively slower) + unoptimized debug backend (no
  release/Tier-2 until Phase H). Cross-skill note (`/backend`): the create-gate's floor
  (`lenient-eval.md` §3.6.3) holds for compute-bound sparks but is violated by allocation-bound sparks
  (the gate bounds spark count, not the per-branch global-allocator / shared-value-atomic-RC
  contention). Proposed resolution (perf half): (1) fix the copy-per-guess representation
  (persistent/structural-share Vec or an in-place candidate-mask scheme); (2) Phase-H benchmark under a
  release/Tier-2 backend; (3) re-include `test-hard-puzzle` once a hard puzzle solves in fast-test time
  + refresh the `/repl` `sudoku.demo` showcase to a *measured* parallel speedup.
- **Re-entry trigger** — a non-copying grid representation (the actionable trigger now — the dominant
  fixable cause) + the Phase-H release/Tier-2 backend (for the headline numbers). Demo/showcase-quality
  perf, deliberately carried.
- **Reversibility** — the equivalence guard (`test-solve-parallel-equiv`) + the 40/40 two-mode green
  run protect the reshape while the perf carry is open; genuinely-hard puzzles still run minutes so
  `solver/test-hard-puzzle` stays excluded from the runner. This is the **§3.1 floor-violation
  EXEMPLAR** — the concrete workload behind the `effect-concurrency.md` §3.1 contention-bounded floor
  scoping (former FIXME 0459).

### §3 — Regen / capture spec holes
Re-entry trigger: the memory-model implementation sprint that reactivates these design surfaces.

#### 0506 — §13.1 capture spec: normative dedup/scope pin missing; duplicate-frame mechanism mischaracterized
- **Origin** — FIXME 0506 · filed_by `/sprint` · target `/design` (cranelisp-backend) · sprint 102
  (+ post-Wave-3R addendum, same drain).
- **`refers_to`** — `design/backend/ownership-codegen.md` §13.1 (normalization contract items 1–4,
  the blockquote ~:1030, the claim ~:980).
- **Pinned analysis** — the Wave-3 B0-be review (S102) confirmed the golden-oracle first-occurrence
  dedup pin is SOUND but the spec does not state it and the recorded mechanism is wrong. **(1)
  Normative gap:** §13.1's normalization contract (items 1–4) is silent on frame dedup; the
  first-occurrence policy lives only in a narrative blockquote + script comments. **(2)
  Mischaracterization:** the blockquote says duplicate frames come from "recompilation passes re-derive
  the JIT symbol set"; empirically they are the **nice-worker `.o` cache-write emission pass**
  (`src/session_v4/nice_worker.rs::emit_object` ~:314 → `compile_to_module::<ObjectModule>`;
  `dump_this` at `crates/cranelisp-backend/src/lib.rs:989` ignores the worker's `capture_clif: false`)
  — proof: `--no-cache` yields exactly one frame per symbol, cache-enabled yields two. **(3) Scope pin
  unstated:** the oracle sees JIT-pass emission only; object-pass divergence (the
  `jit-object-convergence.md` class) is permanently outside L-B1, guarded by the mode-equivalence
  lanes; a future module-type-gated ownership mechanism's object-side delta is invisible to this
  oracle. **(4) Stale claim (~:980):** "cache hits do not re-codegen and dump nothing" — observed
  warm-cache single-file `--run` still compiles + dumps 2× per symbol (whether that recompile is
  intended is an `/int` classification question — flag only). **(5) Reproducibility:** the object
  pass's funcref declaration order is scheduler-timing-dependent so `.o` bytes are non-reproducible
  run-to-run (benign now — relocations resolve by name, cache keys on source hashes — but a Phase-H
  reproducible-builds concern; cheap fix = sorted funcref declaration in `compile_to_module`).
  **Post-Wave-3R addendum:** Wave 3R landed the harness side (`b82ebf1`) — capture runs `--no-cache`,
  the dedup logic is deleted, a duplicate frame is a hard error, a non-empty guard + the full pin set
  are enforced. Cure: edit §13.1 to (a) document the `--no-cache` pin + duplicate=hard-error (the
  as-built branch), (b) state the JIT-pass-only scope pin + the mode-equivalence-lane guard for the
  object side, (c) correct/remove the ~:980 claim, (d) fold the reproducibility sentence; also add to
  §13.1's pin list two emission-affecting vars named nowhere in the spec: `CRANELISP_RC_DEC_CHECK`
  (backend `heap.rs:270`, guarded-dec emission) and `CRANELISP_NO_IO_SCHEDULE` (`src/process_form.rs:377`,
  the pre-typecheck bind-chain transform shaping ParBind CLIF).
- **Re-entry trigger** — the memory-model implementation sprint that reactivates the golden-CLIF
  capture / re-baseline surface (the doc must land with or before the first B3.x scoped re-baseline so
  delta-attribution reasoning starts from the correct mechanism model). Coordinate (a) with the state
  of `tests/scripts/clif_golden.sh` at drain time.
- **Reversibility** — a pure spec-correction (design-doc §13.1 edits), no code; the as-built harness
  (`--no-cache`, duplicate=hard-error) already enforces the corrected contract, so this only closes the
  doc/as-built gap.

#### 0507 — T1 trigger route + 0491 exclusion — design-argument holes (nine items)
- **Origin** — FIXME 0507 · filed_by `/sprint` · target `/design` (src/) · sprint 102 (+ Wave-5 and
  Wave-5-review addenda, same drain).
- **`refers_to`** — `design/int/session-transaction.md` §9.1.1; `design/int/s102-defect-wave.md`
  §1/§7.1; `repl/spec.md` §18.1.1.
- **Pinned analysis** — nine design-argument holes surfaced by the Wave-4/Wave-5 reviews (the fixes
  conform to their designs; the holes are in the *arguments*). **Issue 1 (F2 — T1 over-fires for
  slotted→slotted late-binding targets):** `is_t1_downgrade()` (`prior_was_def && !per_symbol &&
  !gate_exempt`) reads no slot info; for a slotted prior replaced by a slotted staged entry outside
  per-symbol precision (reachable: `deftype` re-entry, ctors are slotted `DefKind::Constructor` Defs)
  the commit reuses the prior slot + patches code in place — compiled callers dispatch through the GOT
  slot and DO pick up the new definition at next call, yet `stale_callers` names them, violating
  §18.1.1's negative MUST. The "route not diff" ruling was argued only from templates/mints. Proposed:
  trigger additionally requires `o.new_slot.is_none() || o.old_slot.is_none()`. **Issue 2 (F3 — 0491's
  frozen-world argument over-generalized):** the safety argument ("a stale wrapper is never re-invoked;
  each expression turn redefines it before invoking") is true of `__expr` only, but `ReverseIndex::build`
  excludes every `is_gate_exempt_internal` name as caller — a compiled macro clause
  (`__macro_{name}_clause_{idx}`) persists and IS re-invoked; if a clause body references a cross-module
  user fn, an AbiChanging redefinition neither re-typechecks nor traps the clause and is invisible in
  `stale:` — a silently-stale expansion path. Proposed: one reachability confirmation; if reachable
  narrow the exclusion to `__expr*` (or add clause edges with a distinct grain); related Wave-7
  pre-check — `/refs`' textual-scan leg must cover macro-clause references the index leg now hides.
  **Issue 3 (F5a rider):** defmacro turns return early (`eval.rs:329`) before
  `apply_redefinition_outcomes` so macro-target outcomes are dropped (moot today — macro heads have no
  reverse edges — but the S103 module-grain cure should note the T1 route cannot fire for macro targets
  today). **Wave-5 addenda:** (4) startup-load exception pin — `recover_startup_failure` (CS-0489)
  drains `pending_cascade_reports`; a load is not a user redefinition turn so `stale:`/cascade sections
  are suppressed (record in `session-transaction.md` §9.1.1). (5) §5.2 correction in
  `s102-defect-wave.md` — "today `error_modules` gates nothing" is wrong; the §14.4 gate WAS wired in
  `process_commands`, the actual Wave-5 change was the §18.8 definition carve-out
  (`is_repair_definition_turn`, watcher-path included). **Wave-5 review addenda:** (6) I-1 repair
  carve-out taxonomy — `is_repair_definition_turn` allowlists only special-form heads so macro-mediated
  definitions (stdlib `def`/`mdef`) + `:Type`-annotated definitions are REFUSED as repair turns (a
  stdlib-def user with a broken backing file is expression-locked), and `defined_symbol_of_form`
  recognizes only special-form heads so macro-mediated failed forms are symbol-less/unclearable; rule
  the carve-out taxonomy (pre-expansion recognition vs expand-then-classify). (7) I-3 binder-position
  class ruling — the Wave-5 defmacro name shield is a spot-patch on "bare zero-arg macro symbols expand
  in ANY position"; the expansion walk has no binder-position concept; rule where binder positions live
  in the walk. (8) I-4 cross-section single-authority — regen dedup + source-first emission are
  section-8-local (`generate_fns_and_macros`); sections 5–7 (traits/types/impls) keep render-only
  emission + no cross-section dedup — the D1 poison class could recur; extend the invariant or pin why
  5–7 are exempt. (9) M-3 always-append acknowledgment — failed forms are always appended at regen not
  re-emitted in seq position (design §5.3); benign for reload, acknowledge the cut or require position
  preservation.
- **Re-entry trigger** — the S103 module-grain redefinition cure / memory-model implementation sprint
  that reactivates the session-transaction + repl §18.1.1 surfaces. Issues 1–2 gate the §18.1.1
  `[Tested+Neg]` annotation (a small `/design`(src/) disposition then `/qa` cells + a possible one-line
  `/dev` predicate change).
- **Reversibility** — design-argument dispositions (mostly doc); the one code touch is a one-line
  trigger-predicate refinement (issue 1) that only narrows the `stale_callers` over-report — monotone
  (removes a spurious name, never adds a missing one). Not blocking Waves 5–8.

### §4 — GOT slot-hole reclamation
Re-entry trigger: measured GOT slab growth from redefinition churn.

#### 0466 — GOT frozen-slot reuse at session load (deferred indefinitely)
- **Origin** — FIXME 0466 · filed_by `/sprint` · target `/design` · sprint 100; status **deferred
  indefinitely** by user direction (S100 design discussion 2026-07-02).
- **`refers_to`** — `design/arch/ownership-inference.md` §5.6; `crates/cranelisp-types/src/module.rs`
  (`allocate_got_slot`, `next_got_slot` serde); `design/int/` (the session load path).
- **Pinned analysis** — under the R3 ABI-epoch slot-versioning model (`ownership-inference.md` §5.6)
  an ABI-changing REPL redefinition allocates a fresh GOT slot + freezes the old one. Because REPL
  definitions persist (regenerated backing file + `.o`/`.meta.json` via the nice-worker path) and the
  `.meta.json` must record slot numbers **faithfully** — slot indices are baked into the `.o` machine
  code (`load(slab_base + slot*8)`), so `.meta`/`.o` renumbering desync is impossible by construction —
  the superseded slot survives restart as a **permanent hole**: `next_got_slot` is a serialized
  monotone high-water mark (`module.rs:135`, allocator `:609`) with no free list, and a valid cache
  reloads its holes indefinitely (compaction only ever rides the cache-invalid full-recompile path).
  Reuse at the session boundary would be **SOUND**: after restart no referent survives (heap gone, old
  body absent from the rewritten `.o`, cross-module stale `.o`s conservatively invalidated by the
  backing-file source-hash change per §5.1). The optimisation would be **load-time reclamation**: scan
  loaded entries' slots against the high-water mark, rebuild a free list, enforce reuse-only-at-load
  (never in-session while a freeze is live). **Do NOT implement now** — cost is 8 bytes of GOT slab per
  ABI-changing *persisted* redefinition (body-only edits take the §5.4 summary-diff fast path and keep
  their slot); a pathological session wastes a few KB, recovered on any genuine recompile. The
  reclamation invariant would be a new correctness obligation on the redefinition subsystem — the
  hottest new machinery in the memory-model design — for negligible return.
- **Re-entry trigger** — measured GOT slab growth from redefinition churn actually mattering
  (long-lived dev sessions with thousands of ABI-changing redefinitions, or a future
  GOT-size-sensitive deployment mode). If actioned: load-time free-list reconstruction in the session
  cache-load path (the `/int` half of the R3 machinery), invariant = in-session allocation never reuses
  a frozen slot.
- **Reversibility** — a standing design pin (spine §5.6): holes persist across restarts by design; the
  persisted `next_got_slot` high-water mark is the freeze boundary (new sessions allocate strictly
  above anything any cache could reference). Deferred indefinitely; a purely additive optimisation with
  no correctness dependency.

### §5 — /qa verification-matrix growth
Recorded here so it re-enters with the perf track.

#### 0499 / L-M1 — reference × referent × instantiation-count e2e matrix (perf-parked half)
- **Origin** — the **L-M1 note** within FIXME 0499 · filed_by `/sprint` · target `/qa` · sprint 101.
  **The 0499 *file* closes under S106 WS-G once L-S1 lands — it is NOT deleted from this doc; only the
  L-M1 note migrates here.**
- **`refers_to`** — `tests/plan/coverage-audit-s101.md` §2.4 (lanes) + §2.5 (drafting rules);
  `tests/CLAUDE.md` §Plan documents; `tests/plan/s103-test-plan.md` §1.7 (L-M1 growth); backend §13.3
  (the `fn_as_value` seam).
- **Pinned analysis** — L-M1 is the **reference-shape × referent × instantiation-count** e2e matrix,
  one of the 7 named lanes from the S101 coverage audit. It **grows with the `fn_as_value` seam
  rework** (backend §13.3): the 0483/0474 guards flipped GREEN in S102, so growth = corpus **EXTENSION**
  with the newly-green shapes + the new value-use × ≥2-instantiation cells the reuse-token/R5 seam
  introduces. Its growth is paced by (blocked on) the **parked backend `fn_as_value` seam**, so it
  re-enters WITH the perf/memory-model track rather than on 0499's own S106 close schedule. The other
  six lanes (L-U1/L-S2/L-S3/L-N1/L-N2/L-S1) exist or close under 0499's own WS-G schedule and are NOT
  perf-parked — only this L-M1 growth axis is captured here.
- **Re-entry trigger** — the parked backend `fn_as_value` seam (backend §13.3) reactivating: the
  reference×referent×instantiation cells grow as the value-use × ≥2-instantiation shapes the
  reuse-token/R5 seam introduces come back into scope.
- **Reversibility** — pure test-authorship growth (corpus extension, no compiler change); the guards
  it extends are already green. Additive.

---

**AUTHORED S106 WS-J.** Every entry above carries its five-field provenance migrated from the FIXME
file. `/arch` deleted its own FIXME files (0521, 0526) once their §1 entries were confirmed complete;
each remaining owner deletes ITS file once it confirms the substance is captured here (deletion table
above). Consolidating the arc is NOT re-entering it — re-entry is a future sprint's measured-trigger
decision (Principle 8).
