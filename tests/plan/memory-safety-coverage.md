# Memory-safety coverage strategy — standing (`/qa`, S111)

Status: **standing strategy**, not a per-sprint plan. Owner: `/qa` (this doc);
builds route to `/testing`; per-crate fixes to `/dev` per attribution.
Ratified from the S111 user directive: `/qa` owns and actively manages the
systemic memory-safety coverage risk as a standing concern, not
incident-by-incident.

Companion authority: the parallel `/arch` foundational-invariants assessment
(S111 Phase-7 track) states the *principle* — safety-relevant optimizations
must be **differentially checkable** against a conservative lowering
(`design/arch/ownership-inference.md` §2.1 monotone-soundness, §3.4/§6.2 the
R7 oracle). **This document operationalizes that principle as enforced
coverage**; it does not restate the design argument.

---

## §0. The problem, grounded in S111 evidence

Every memory-safety defect below was found **incidentally** — by adversarial
review of an adjacent fix, or by exercising the language a new way — never by
the suite going RED:

| Defect | How found | Class |
|---|---|---|
| 0633 drop-glue under-key (2 layers, SIGBUS all modes) | `/review` Important on CS-1 (a FALSE guard had canonized the bug as correct) | `drop-glue-underkey` |
| 0640 mangle non-injectivity (`A-B`/`A_B` → one glue, SIGBUS) | `/review` Blocker on the 0633 *fix* | `drop-glue-underkey` |
| Multi-arity §5.1.2 wrong-accepts — B-1 vectors 1–3 (String heap ptr read as Int) | `/review` adversarial refute-hunts, 3 successive vectors | `wrong-accept` |
| 0641 false-`Fresh` family — B-1 container-element laundering, B-2 producer seam, I-1 capture, I-2 element-store (UAF; `--link` SIGABRT) | `/review` adversarial hunt on CS-5 | `uaf` (false-Fresh elision) |
| 0638 macro-expansion interior-alias double-free | `/stdlib` exercising derive macros | `uaf` |
| 0637 `borrowed_sibling_slot` cache-load validation gap | `/review` Suggestion on CS-2 | forward UB obligation |
| R2 leak — four successive re-attributions (0633 → §3.7 → vec-element-drop) | still RED, attribution churn | `rc-miscount` |
| L-B1 golden-lane rot — 3 sprints of un-re-baselined emission drift, invisible | CS-0.5 gate stop | process |
| 0604 index-feed write race | load-dependent, still unlocated | `shared-state-write-race` |

Three structural gaps compound, and each has a distinct cure in this strategy:

1. **The default test mode is blind to the failure mode** (→ §1). A leak is
   invisible without RC accounting; a UAF frequently returns plausible garbage
   in `--run`/REPL and is only a deterministic signal under `--link` (glibc
   heap-corruption SIGABRT), `CRANELISP_RC_DEC_CHECK` (stale-dec trap), or the
   conservative-oracle diff. The suite is overwhelmingly "run → assert
   output"; a safety defect that does not perturb output PASSES. The exposing
   signals all exist **but are run by hand during certification** (the CS-0.5
   and CS-5 emission certs were manual `/qa` runs) — exactly the shell-lane
   disease that let L-B1 rot for three sprints.
2. **Tests share the implementation's mental model** (→ §3). The 0623 matrix
   was hand-enumerated by the same reasoning that wrote the CS-5 fix, so it
   was blind to precisely the axes the model missed (container-element,
   capture, injectivity, leaf-body). What worked in S111 was the adversarial
   reviews — instructed to *refute*, not confirm.
3. **The failure space is combinatorial** (→ §2). How a heap value flows —
   container × capture × match × ADT field × projection × callee × mode — is
   an open-ended composition space; a curated example list cannot enumerate
   it. Only generation covers composition.

§4 adds the fourth leg: a standing audit category for the *profile* that
recurs (a safety operation elided by a static analysis, verified by example),
because the same shape appears outside the ownership analysis proper.

---

## §1. The differential-oracle CI gate (highest leverage)

### 1.1 What the oracle is

`CRANELISP_NO_OWNERSHIP=1` (`cranelisp_types::ownership_analysis_off()`)
selects the conservative all-Owned/all-atomic/all-heap lowering — byte-identical
to pre-ownership codegen, **permanently sound by the monotone-soundness
property** (`design/arch/ownership-inference.md` §2.1: widening toward Owned
preserves correctness, only performance degrades). Therefore:

> **The optimized lowering is unsound EXACTLY when it observably diverges
> from the conservative oracle.** A divergence needs no one to have thought
> of the case — the whole false-`Fresh` class (0641 B-1/I-1/I-2, the §3.7
> COW family, any future elision bug) fails this check mechanically.

The `--link` SIGABRT face and the RC-accounting signals are the oracle's
teeth for defects whose divergence is "garbage that happens to print the
same": a UAF that luckily reproduces the value under `--run` still corrupts
the allocator heap (deterministic `--link` abort) or fires the stale-dec trap.

### 1.2 The gate — four signals, one combinator

For a program P under the gate, assert ALL of:

1. **Behavioral equivalence** — stdout + exit code identical between
   ownership-on and `CRANELISP_NO_OWNERSHIP=1`, per mode. (The ruled
   tolerance: the oracle direction may *leak more* — conservative
   leak-tolerance is the sound direction — so RC-count equality between
   toggle states is NOT asserted; behavior is.)
2. **RC balance on the optimized lowering** — `CRANELISP_RC_STATS=1`:
   `allocs == deallocs` at exit (the leak face; this is what R2-class leaks
   trip even when output is byte-identical).
3. **Stale-dec zero** — `CRANELISP_RC_DEC_CHECK=1`: no dec on an untracked/
   freed pointer (the UAF face, firing AT the bad dec with the pointer —
   deterministic where the crash itself is layout-luck).
4. **A `--link` face** — link-then-RUN exits clean (glibc hardening turns
   heap corruption into a deterministic SIGABRT that JIT modes miss).

### 1.3 Wiring — an enforced nextest gate, not a manual cert

The precedent is the CS-0.5 lesson made flesh: the golden lane rotted three
sprints because it was shell-only; folding it into nextest
(`clif_golden_lane_no_drift`) made drift RED mechanically. Same move here:

- **`/testing` adds a harness combinator** to `tests/helpers/e2e.rs` — working
  name `assert_safety_matrix(program, prelude)` (and a builder face
  `.safety_matrix()`): runs P through `--run` + REPL + `--link` × toggle
  {on, off} with `RC_STATS` + `RC_DEC_CHECK` set, asserts §1.2's four signals.
  It composes the existing pieces (`run_through_all_modes`, `.env`, the
  `env_remove` polarity hygiene already in `ownership_fences.rs`) — no new
  binary machinery. RC-signal runs stay serial per the standing rule.
- **A dedicated oracle lane** — `tests/safety_oracle_lane.rs` — sweeps a
  fixture corpus (`tests/fixtures/safety_corpus/*.cl`) through the
  combinator. Adding a program to the corpus directory IS adding it to the
  gate; no per-program test authorship. Seed corpus: the 0641 B-1/B-2/I-1/I-2
  repro programs, the §3.7 COW family shapes, the 0633/0640 collision pairs,
  the 0638 repro (from the FIXME body), the multi-arity B-2 heap-read shapes,
  the tco/vec-query/vec-cow repro programs.
- **Plan-row discipline**: from S112 on, every plan row `/qa` marks
  **`[oracle]`** — any row whose subject is ownership/RC-affected (touches
  what a heap value's inc/dec/protect/drop schedule depends on) — MUST be
  authored through the combinator or land a corpus program. `/qa` verifies at
  the Phase-5 QA-first check; a bare output-assert on an `[oracle]` row is a
  plan-conformance finding.
- **Batching caveat (0633 lesson)**: collision scope differs by batch
  cardinality, so the lane runs corpus programs BOTH batched (shared process,
  cheap) and per-program for the modes where scope differs — the combinator
  owns this so authors cannot get it wrong.

> **As-built record (S115 instrumentation matrix, /qa 2026-07-20).** The
> combinator + lane landed S113 W1 and ARE the enforced nextest gate
> (`tests/helpers/e2e.rs::SafetyMatrix`/`assert_safety_matrix`;
> `tests/safety_oracle_lane.rs`). Three deviations from this section's letter
> are ACCEPTED as the settled shape: (1) there is no
> `tests/fixtures/safety_corpus/` directory sweep — lane programs are named
> per-cell tests calling the combinator, which names failures better and
> enforces identically; growth = add a cell, not a file-drop. (2) The
> `CRANELISP_SAFETY_FULL` split is unbuilt — moot until the lane approaches
> its wall budget; revisit when the §2 harness lands. (3) The batching caveat
> is handled per-cell, not combinator-owned. Standing rule from the same
> matrix: new `RC_DEC_CHECK` positives ride the lane/combinator (face 4),
> never scattered per-file `.env` sites; the `env_remove` sites are polarity
> hygiene, not assertion sites.

### 1.4 Cost envelope

Wrapping multiplies subprocess runs ×~6 (3 modes × 2 toggle states) for
wrapped tests only. Scope of the always-on gate: the existing ownership/RC
corpus (~10 files, ≈60–80 tests) + the seed corpus (~25–40 programs), NOT the
full 1,963-test e2e tier. Estimated added wall: ~30–60s serialized RC lanes —
acceptable against the ~60s suite; if it grows past that, the lane splits a
fast always-on core from a `CRANELISP_SAFETY_FULL=1` sweep, with the core
REQUIRED to contain every cell that has ever failed.

### 1.5 The 0641 gate (user directive — sequencing is binding)

**The oracle gate GATES the 0641 instance-fix.** The false-`Fresh` class must
not be fixed instance-by-instance ahead of the class-closing gate: the fix
increment (FIXME 0641, `/design`(typecheck) container-element provenance axis
→ `/dev`) lands AFTER (or in the same change-set as) the oracle lane, so that
(a) the committed B-1/B-2/I-1/I-2 repros flip under the gate, proving the gate
sees the class, and (b) the fix's own blind spots — the next laundering
mechanism nobody enumerated — are caught by the same lane, not by the next
adversarial review. An instance-fix that lands first merely moves the class
back into the "found incidentally" regime this strategy exists to end.

---

## §2. Generative / property harness (the combinatorial cure)

### 2.1 Shape

A **deterministic enumerator** of well-typed programs threading heap values
through the flow-space, each run under the §1 combinator. Not random
property testing: deterministic exhaustive enumeration of a bounded space
gives stable, nameable failures (the no-flaky rule) and reproducible CI.

Well-typedness by **construction, not synthesis**: a small algebra of
type-preserving flow operators over a heap value `v`, composed to bounded
depth. v1 dimensions:

- **Heap value kinds** (~5): `Str`, `(Vec Int)`, `(Vec Str)`, ADT with a heap
  field (`(Pair Int Str)`), closure capturing a heap value.
- **Flow operators** (~10): return directly; return via `let` alias; store
  into a Vec literal (`[v]`); `vec-push`; `vec-set` (COW); ADT-ctor field
  store; project out (`vec-get` / field accessor / `match` ctor-pattern
  bind); `match` var-pattern bind; pass to a callee (identity fn — exercises
  the summary at the boundary); capture in a returned closure (direct and
  via `let`).
- **Consumption** (~3): result printed; result dropped at scope exit;
  closure invoked after the constructor returns.
- **Faces**: the §1 combinator's modes × toggle × RC signals.

Depth-2 composition (operator ∘ operator over one value kind, all
consumptions) ≈ low hundreds of programs — exactly the space where 0641
lived: `return ∘ project ∘ store` IS B-1; `capture ∘ let-alias` IS I-1;
`return ∘ store ∘ vec-set` IS I-2. **The generator would have emitted all
three without anyone thinking of them.**

### 2.2 Realistic v1 scope

- `/testing` authors a generator module under `tests/` (e.g.
  `tests/gen_ownership_flows.rs`): Rust code that enumerates the templates,
  writes each program to the per-test tmpdir, runs the §1 combinator.
- **Always-on core**: depth-2, one representative value kind per operator
  pair, batched where scope-equivalent — budget ≤60s serialized. **Full
  sweep**: all value kinds × depth-2 (later depth-3) behind
  `CRANELISP_SAFETY_FULL=1`, run at sprint certification (Phase 5 close /
  Phase 7) — but unlike the old by-hand certs, the *sweep itself is a
  nextest test*, just env-gated; the core is never gated.
- **Failure protocol**: a generated failure is reduced by `/testing` to a
  named committed repro (the generator names the cell: kind × ops ×
  consumption × face), joins the §1 seed corpus permanently, and the cell is
  pinned into the always-on core.
- **Deferred to v2**: spark/concurrency flows (ParBind/IVar suspension-escape
  edges — coordinate with the R6 classification), macro-expansion flows (the
  0638 family — Sexp interior aliases across the JIT boundary), platform
  marshalling flows, `--link`-with-ASan lane (add when the toolchain lane is
  provisioned; `--link` + glibc + DEC_CHECK carry v1).

---

## §3. Adversarial / model-independent authorship (standing practice)

S111's productive pattern — CS-4.1's "hunt a THIRD vector" found B-2; CS-5's
adversarial review found the entire false-`Fresh` residual — is
institutionalized:

1. **Safety surfaces get refute-instructed review, always.** Any change-set
   touching a safety surface (ownership analysis/summaries, RC emission,
   protect/drop scheduling, drop glue & its keying, mangles, cache load of
   safety-bearing facts, spark admission) is dispatched to `/review` with an
   explicit adversarial brief: *find the next vector, or prove exhaustion
   structurally*. "The matrix passes" is not an exhaustion argument;
   "the check verdicts the clause's param types directly, so every body shape
   is subsumed" (CS-4.2's root-cause form) is.
2. **Matrix axes derive from spec + design model, never from the diff.**
   `/qa` authors safety plan rows from `spec/` MUSTs and the design doc's
   own invariant statements (e.g. §3.7's reservation clause), not from the
   implementation's enumeration of what it handles — the 0623 lesson. Where
   the design names an invariant, the plan row tests its *negation space*.
3. **An adversarial-review Blocker on a safety surface is a QA-first miss**
   (standing lesson, S108): each one feeds back as (a) a new axis in the
   relevant matrix, (b) a generator operator if it names a flow mechanism,
   (c) a §4 audit surface if it names an elision profile.
4. **The generator IS model-independent authorship.** Enumeration does not
   share the implementer's blind spot; the refute-hunt is the human interim
   lane for any axis the generator does not yet cover, and each hunt's
   finding shrinks that gap (the goal state: the hunt comes back empty
   because the lane already covers the space).

---

## §4. Standing audit category — "safety operation elided by a static analysis, verified by example"

**The recurring profile**: a runtime safety operation (an RC inc/dec, a
protect, a drop, a rebuild, a validation check) is *elided or deduplicated*
because a static claim says it is unnecessary — and the claim was verified by
the examples at hand rather than by a structural or differential argument.
0641 (protect elided on a false `Fresh`), 0633/0640 (glue rebuild elided on
an under-determined identity key), and 0637 (cache-load validation covering
`callable_got_slot` but not `borrowed_sibling_slot`) are the same profile at
three different seams.

`/qa` audits this as a **rolling per-sprint category** (peer of the
"coverage by definition variants" lens). The audit question per surface:

> *What is the structural or differential argument that this elision is
> sound — and is that argument enforced by a standing gate, or only
> witnessed by examples?*

### Candidate surfaces (the rolling sweep list; extend as mechanisms land)

| Surface | Elided operation | Static claim | Standing gate today? |
|---|---|---|---|
| RC/borrow elision (backend B3.x: caller-inc/callee-dec elision, projection elision, capture-borrow, confined non-atomic RC, return-protect elision `fn_compiler.rs` §B3.2) | inc/dec/protect | mode summary / escape / confinement | §1 oracle lane (this strategy) — partial until landed |
| Drop-glue / dealloc identity (`adt_instantiation_mangle` consumers, `build_elem_dec_fn`, `poll_state_drop_glue`) | glue rebuild (dedup) | key determines body | 0633-R3 battery + 0640 injectivity round-trip decoder — GREEN; keep under §1 lane |
| Keyed-identity resolution (Principle 24 carriers/sidecars) | re-resolution | carrier value = storage key | P24 battery (PLAN §F) — a wrong-key read is an elided resolution "verified" by whichever example hit the right key |
| Cache (de)serialization boundaries (GOT slots, ownership `ModeSummary` round-trip — schema 20 makes summaries SAFETY-BEARING: a stale summary elides protects) | re-validation / recompile | schema + validation cover what consumers read | 0637 is the open counterexample: validation enumerated by *current* consumers, not by *persisted* fields. Audit rule: every persisted safety-bearing field gets a load-validation row WHEN WRITTEN, not when its first consumer appears |
| Spark admission (S104 M-static flip: spark-leg deletion at non-recursive sites; R6 suspension-escape edges) | spark leg + its RC symmetry | static recursion/escape classification | CS-0.5 cert was by-hand; fold representative shapes into §1 corpus |
| Macro-expansion marshalling (Sexp interior aliases across the JIT boundary — 0638) | copy/protect on expansion values | expansion value ownership assumptions | none — 0638 is open; v2 generator axis |
| Extern-primitive declared fact tables (§3.1(a) hand-declared per-param facts) | inference at the leaves | the hand-written table is truthful | CS-5 swept the table once by hand; audit = table vs implementation per sprint a primitive changes; oracle lane catches downstream divergence |

Findings route per normal attribution; a surface with NO structural/
differential argument (example-verified only) is an audit finding even with
zero known defects — that is the whole point of the category.

### 4.1 Diagnostic-mode capability fences — lifecycle ruling (S114, standing)

Escalated from the S114 cleanup batch (`adb8d3fb`): the `m1_quarantine`
e2e capability fence was retired when its planted fault — the last live
free-class double-free (0638) — was fixed, and a re-plant proved
empirically impossible (MS-P7 is reuse-corruption and runs clean under
quarantine). The standing question: do MS-P6 e2e capability fences exist
only opportunistically-while-a-live-fault-exists, or must retirement be
replaced by unit-only coverage?

**Ruling — neither pole; three prongs, all required:**

1. **Unit-tier synthetic self-test per diagnostic mode: MANDATORY and
   durable.** The fault is planted at the intrinsics allocator seam —
   below the language, where a plant is ALWAYS constructible regardless of
   compiler health — and the test asserts the mode detects it
   (fail-on-revert of the detection logic). This is the durable capability
   record; it never depends on a live compiler defect.
2. **E2e capability fences are opportunistic BY NATURE, not by policy
   laxity.** An e2e plant requires a source-level program that commits the
   fault, which exists only while a live compiler defect of the class
   exists. While one does, the fence is mandatory (free teeth — the MS-P6
   self-test discipline). When the last live fault of the class drains,
   the fence RETIRES **with a tombstone** naming (a) the drained fault
   set, (b) the unit-tier successor (prong 1 — a retirement without one
   is a coverage regression), and (c) the sibling faces still fencing the
   env wiring.
3. **Env-wiring e2e coverage is a per-MODE property, not per-fault.** At
   least one e2e fence per diagnostic mode keeps exercising the env-var
   wiring end-to-end (a sibling planted-fault face or a clean-run
   capability cell) — unit tests are structurally blind to the subprocess
   env plumbing (§5's unit-tier row).

The m1_quarantine retirement is compliant on all three prongs (intrinsics
unit seam carries the verification; sibling quarantine faces fence the
wiring; tombstone recorded in the retiring change-set). The W7 MS-P6 COW
capability re-plant (s114-test-plan §8 rider; landed `7c2d5168` as
`safety_lane_detects_falsified_clean_expectation_capability_green`) is the
worked example of the compliant alternative: re-plant on a SYNTHETIC fault
when one is constructible at the e2e tier. A retirement claiming prong-2
impossibility must state WHY a synthetic e2e plant is not constructible
(as the m1 tombstone does: quarantine's detected class cannot be committed
from source once the compiler is fixed).

**Face-1 narrowing (S114 W7-review Minor, recorded here as the standing
coverage statement):** the synthetic re-plant exercises the **Face-1
value-equivalence guard only** (a falsified clean expectation tripping the
§1.2 signal-1 comparison). The gate's **differential faces — signal 1
ON-vs-OFF behavioral divergence from a REAL elision bug, signal 2
rc-balance (`allocs != deallocs`), and signal 4 abort-on-corruption —
currently have NO e2e capability plant**: constructing them synthetically
requires a source-committable fault of each class, which per prong 2
exists only opportunistically. The **unit-tier prong (prong 1) is the
durable capability layer for those faces** — the intrinsics-allocator-seam
self-tests are what durably prove each detection mechanism fires. An e2e
differential plant is authored opportunistically per prong 2 whenever a
live (or synthetically constructible) fault of the matching class exists —
e.g. the S114→S115 chained-MayAliasOf pins double as live signal-4 plants
while they stay RED; when that family drains, the capability question
returns to prong 1 + this note.

**Prong-2 amendment — a live-defect plant is SELF-EXPIRING (S115, standing).**
Twice now the same e2e fence has inverted to RED because its planted fault was
fixed: `ms_p6_mode_self_tests::m3_parity_catches_planted_leak` went stale at
S114 (FIXME 0690 — the W4 F-R1 fix balanced the entry-`main` plant) and again
at S115 W3 (FIXME 0746 — the item-26 generalisation balanced the non-`main`
plant), the second time exactly as the test's own FLIP-HAZARD comment
predicted. The lesson is not "re-plant harder": a plant drawn from a defect
class **under active repair** has a half-life measured in waves, and each
expiry costs a triage cycle plus an unattributed RED carried toward
certification.

Standing rule, binding on every new or re-planted capability fence:

- **Prefer a SYNTHETIC plant** — a test-only fault injected at the seam the
  mode instruments (e.g. an env-gated imbalance hook at the intrinsics
  allocator), so the fence is fail-on-revert of **the MODE**, not of some
  unrelated fix. Any such hook lands in the same change-set as its
  byte-identical-off fence (`diagnostics/tests.rs::all_gates_default_off`).
- **Draw from a live defect only when a synthetic plant is not
  constructible**, and then say so on the test: name the defect, its owner,
  and the expectation that the fence expires when it drains.
- **Never plant on a live defect that already has an owner and a fix path**
  — the fence becomes collateral of someone else's wave.
- When a plant expires, the compliant dispositions are (i) synthetic
  re-plant or (ii) retirement with the §4.1 tombstone; a fence must not
  linger RED into a certification run while the choice is pending.

---

## §5. Current exposure — quantified (S111, post-CS-5)

Suite ≈ 4,630 tests: **≈1,960 e2e** test fns across 90 files + **≈2,670
unit** tests. Signal reach today:

| Signal | Reach | Share |
|---|---|---|
| Differential oracle (`CRANELISP_NO_OWNERSHIP` both-polarity runs) | 8 e2e files, ≈30 tests | **≈1.5% of e2e, ≈0.6% of suite** |
| RC accounting (`CRANELISP_RC_STATS`) | 9 files, 24 sites | ≈1–2% of e2e |
| RC trace (`CRANELISP_RC_TRACE`) | 9 files, 25 sites | ≈1–2% of e2e |
| Stale-dec trap (`CRANELISP_RC_DEC_CHECK`) | **2 sites, both `env_remove` hygiene — ZERO standing positive assertions** | **0%** |
| `--link` face (72 direct `.link*` sites + 62 `run_through_all_modes` sites) | 25/90 files, ≈130 tests | ≈7% of e2e, ≈3% of suite |
| Unit tier | executes no JIT code — **structurally blind to every runtime memory-safety signal** | 0% of ≈2,670 |

Read: **≈97% of the suite cannot see a UAF that does not perturb output, and
>98% cannot see a leak at all.** The strongest deterministic UAF signal in the
tree (`RC_DEC_CHECK`) is asserted nowhere. The oracle — the one signal that
fails the false-`Fresh` class mechanically — protects 0.6% of the suite, and
its certification uses are manual. This is the quantified version of "these
defects are only found incidentally": the suite's safety-signal surface is
roughly two orders of magnitude thinner than its output-assert surface.

Target after the first increment (§6): every ownership/RC-affected row and the
seed corpus under all four signals (≈100–150 programs), `RC_DEC_CHECK` asserted
suite-wide within the lane, and the generator core adding composition coverage
no curated list reaches.

---

## §6. First increment (what to wire first) + sequencing

1. **`/testing` — the combinator + lane** (one change-set, est. 1 `/testing`
   dispatch): `assert_safety_matrix` in `tests/helpers/e2e.rs` +
   `tests/safety_oracle_lane.rs` + `tests/fixtures/safety_corpus/` seeded per
   §1.3. Acceptance: the 0641 B-1 program goes RED under the lane on all four
   signals' union TODAY (it is the live counterexample); the §3.7 fixed
   family is GREEN; lane wall ≤60s.
2. **Then the 0641 fix increment** (`/design`(typecheck) per FIXME 0641 →
   `/dev`) — gated per §1.5; the lane repros flip green and STAY in the lane.
3. **Retro-wrap the existing ownership/RC corpus** (~10 files) through the
   combinator (`/testing`, mechanical, may ride change-set 1 or follow).
4. **Generator v1 core** (`/testing`, est. 1 dispatch after the lane exists —
   the lane is its output surface): §2.2 always-on core + env-gated full
   sweep.
5. **`/qa` standing hooks** (no dispatch — process): `[oracle]` row marking
   from S112 Phase 3 on; the §4 audit joins the rolling per-sprint sweep
   beside the definition-variants lens; Phase-7 suite report gains a
   safety-signal-reach line (the §5 table's deltas).

Items 1 and 4 are the only new build cost: **two `/testing` dispatches**.
Everything else is sequencing discipline over work already owed.

---

## §7. Cross-references

- `design/arch/ownership-inference.md` §2.1 / §3.4 / §6.2 — the
  monotone-soundness property and the R7 oracle this operationalizes.
- The parallel `/arch` foundational-invariants assessment (S111 Phase-7) —
  the differential-checkability principle; this doc is its enforcement arm.
- `design/arch/fixmes/0641-…md` — the gated instance-fix (§1.5).
- `design/arch/fixmes/0637-…md`, `0638-…md` — open instances of the §4
  profile at non-ownership seams.
- `tests/plan/PLAN.md` §"Sprint 111 … I. In-sprint additions" — the
  committed S111 safety matrices this strategy generalizes.
- `tests/plan/risks.md` — standing risk entry pointing here.
- `tests/CLAUDE.md` §"Diagnostic env vars", §"Defect-repro notation" — the
  signal inventory and the `class=` vocabulary the lane's failures feed.
