# S100 ownership-inference verification & acceptance plan (parts 17–18)

**Author:** `/qa` · **Date:** 2026-07-02 · **Status:** DESIGN (S100 Phase 3, stage 2 —
the sprint's parts-17–18 deliverable). This is a **plan**: S100 ships design, not
implementation. The failing tests named here are drafted QA-first at the start of each
implementing increment sprint (METHOD Phase 5 stage 1); this document must be concrete
enough that a future `/qa` invocation drafts them directly from it.

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

The machinery sprint is graded by §4's R3 lanes (trap stubs, cascade, slot versioning,
summary-diff fast path) plus one latency pin: the **body-only redefinition turn** is
observably at today's cost (§3.5 L-D1 gate applies from this stage on, since the
summary-diff gate is machinery, not increment-I analysis).

### 2.2 Stage I — increment I (read path: borrow-elision, projection, stack slots, confined non-atomic RC, fact table, str-len sibling)

| Gate | Lane | Bar |
|---|---|---|
| **I-G1 (headline read-path collapse)** | F1 rc_inc, serial, program-attributable | **≥ 99% drop vs B1** (< 25,000 residual). F1's ~2.13M incs are one per `(vec-get g i)` element read + match projections on a borrowed root — exactly the projection-covered class (typecheck §4; borrowed capture §8.2-spine). Residual budget = grid build (81 cells) + machinery. |
| **I-G2 (attribution honesty)** | F2/F3/F4 rc_inc | **Expected essentially unchanged** (within 1% of B2/B3): the 170M term lives inside the `vec-set-copy`/`vec-push-copy` Rust bodies (backend §5.2 table) and is a write-path/increment-II target. This is an assertion, not a concession — if increment I *does* move it, the attribution model is wrong and acceptance halts for re-diagnosis. |
| **I-G3 (confinement correctness pin)** | per-mechanism counters on F2 | The shared board's cell classifies **Confined** (typecheck §5.3's F2 discharge) — asserted via the ownership-trace/counter hooks (§3.7), i.e. the surviving parent-side inline ops on it emit non-atomic. This is the designed attack on the S99 (b) shape and must be verified as a *classification*, independent of wall-clock. |
| **I-G4 (parallel non-regression)** | F2/F3 N-worker wall+user, median-of-7 | ≤ +5% vs same-HEAD toggle-off. (Increment I is not expected to *cure* F2; it must not worsen it.) F4: distribution report only. |
| **I-G5 (small-case overhead)** | F1–F4 serial + 1-worker, toggle-on vs toggle-off | wall+user median ≤ +3%, spreads overlapping-or-better. Plus batch compile-time of the fixture corpus (cold cache, `--run` to first output) ≤ +10% — the pass5 structural budget (typecheck §3.4). |
| **I-G6 (interactive latency)** | L-D1 REPL turn lane | body-only redefinition turn ≤ 1.10× toggle-off median; ABI-changing turn reported with cone size (no numeric gate at first landing — the cone is the same set R3 must recompile anyway; typecheck §3.4). |
| **I-G7 (stack/region)** | alloc counter on the stack-slot micro-fixture (statically-sized scalar-payload ADT/closure temporaries in a hot loop) | heap allocs at the eligible sites → 0 (stack-slot-hit counter = loop count); F-series alloc counts reported (F2's 2-allocs-per-copy are escaping COW copies — not increment-I-eligible, expected unchanged; stated so the gate is honest). |

### 2.3 Stage II — increment I+II (write path: reuse tokens, R5 one-word flattening, region arena)

| Gate | Lane | Bar |
|---|---|---|
| **II-G1 (R5 witness)** | F2v rc_inc + wall | rc_inc collapses to **near-zero** (< 1% of B2): an 81-slot Vec of one-word value-`Cell`s copies by memcpy with null elem fns (backend §7.3). Wall: **F2v N-worker < F2v serial** — the first configuration where parallelism must actually pay on the copy shape. |
| **II-G2 (reuse hit-rate)** | reuse hit/miss counters on F4 (copy-per-guess) | in-place reuse hit-rate on the guess-grid write chain ≥ 50% (provisional; the copy-once-then-in-place property of backend §6.2 predicts ≫ this for chained writes). Counter movement is the attribution prerequisite for any F4 wall claim (§0.3). |
| **II-G3 (F4 floor progress)** | F4-hard 11-rep distribution | median wall ≤ **2× serial** (from B7's 6–15×), and the whole wall distribution's median-to-max below toggle-off's. |
| **II-G4 (F2 two-ctor honesty)** | F2 rc_inc + wall | partial: report rc_inc drop from reuse on chained copies; wall ≤ 1.5× serial (from B7's 2.3×). F2's shared-grid copies-of-a-shared-root are *genuine shared materializations* — fully cured only by multi-ctor flattening or persistent DS (§5 limit 1); II-G4 must not be silently graded as if R5-first-landing covered it. |
| **II-G5/G6** | = I-G4/I-G5/I-G6 re-run | same non-regression + overhead bars, including F2v serial. |

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
  mechanisms touch). At the **parent commit of the increment-I change-set**, capture the
  per-function CLIF of the corpus via `CRANELISP_CODEGEN_DUMP` and commit it as a golden
  (`tests/fixtures/clif_baseline/`). Lane: toggle-off build of HEAD dumps the same
  corpus; normalized diff (sort by function symbol; strip nondeterministic ordering —
  see Hook H1) must be **empty**. The golden is re-captured ONLY with an explicit
  change-set rationale (a compiler change that legitimately reshapes CLIF re-baselines
  in its own commit, exactly the `public-api.txt` discipline).
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
  *Gate:* identical pass-set (i); byte-identical observables (ii). *Stage:* I onward.
  *Tier:* (i) CI double-run; (ii) script lane.
- **L-B3 — cache-manifest invalidation key.**
  *Mechanics/tests:* (1) compile a multi-module project toggle-on, flip the toggle,
  re-run: assert **wholesale invalidation** (full recompile observed via
  `CRANELISP_MODULE_TRACE` cache-hit/miss lines) and correct output. (2) *Negative:*
  after the flip, no stale `.o` is consumed (zero cache hits) — mixed-ABI caches
  unrepresentable (backend §2.3). (3) Round-trip: flip back, again wholesale, output
  identical. (4) At R5 landing: `CACHE_SCHEMA_VERSION` bump invalidates every pre-R5
  cache (backend §7.4).
  *Stage:* (1)–(3) increment I; (4) increment II. *Tier:* canonical nextest (`cache.rs`
  family).

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
  guards, `tests/launch_grid_corrupt.rs`, `tests/launch_vec_send_corrupt.rs` (both
  currently RED for 0486 — they remain the launched-strand fence and flip green on the
  0486 fix, independent of this design).
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
   that sprint.
7. **F4 is never a single-number gate** (distribution discipline, §0.3).
8. **The perf gates live outside canonical nextest** (30s cap); CI carries them as
   scheduled lanes, not per-commit blockers, with per-increment acceptance runs
   attended (S99 method).

---

## §6. QA-first drafting lists per implementing sprint (Phase 5 stage 1)

- **Machinery sprint (M):** L-R1…L-R5 drafted failing-first (L-R4 is the sprint's own
  RED witness); L-D1 script + its M-stage gate; the toggle ships here (spine §5.7) so
  L-B2(i) suite-polarity starts here too.
- **Increment I sprint:** L-B1 golden capture (BEFORE mechanisms land — schedule the
  baseline commit first), L-B1/L-B2/L-B3(1–3); S1–S4 + S6 fences; L-D3a–f (incl. the
  per-row fact-table tests generated from the audit table); L-C1, L-C2; str-len sibling
  S5; H1/H2/H3/H5 hook smokes; perf lanes I-G1…I-G7.
- **Increment II sprint:** F2v fixture; L-C3; L-B3(4) schema-bump lane; reuse/flatten
  counters; perf lanes II-G1…II-G6; L-D2 decision point executed on increment-I data.
- **Every sprint:** ledger discipline — new intentional-failing guards enter
  `tests/plan/ledger.md` with the six fields; the canonical-suite intentional-failure
  count in root `CLAUDE.md` §Testing is updated by `/sprint` at close.

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

---

## §8. Registration

- This plan is registered in `tests/CLAUDE.md` §Plan documents.
- Supersedes nothing; peer of `tests/plan/s99-measurement.md` (whose baselines it
  consumes). `tests/plan/PLAN.md` remains the spec→tests bridge; rows for the new
  tests join it as they are authored (the S100 triage tests trace to
  `spec/04-expressions.md §4.6.2`).
