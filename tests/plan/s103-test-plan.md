# S103 test plan — increment II write-path evidence (reuse tokens, R5 flattening, T1 cure)

> **Retained dated record (S122 consolidation).** Only the sections that current
> test sources, the backend ownership design and the performance backlog cite
> remain, with their original numbering: §1.1, §1.2, §1.4, §1.6, §2 with §2.1,
> and §4. They are the 2026-07-05 Phase-3 allocation and the 2026-07-06 measured
> gate results, not current status: RED/GREEN-at-draft colours, sizes and
> specification or design section numbers are as drafted, and the named test
> files are the current record of what landed. Metrics discipline is
> [ownership verification](s100-ownership-verification.md) §0. The removed
> inputs list, §1.3 (h3 flip), §1.5 (coupled-work coverage), the 0499
> lane-refactor plan (§3), §5–§9 (coverage summary, guard-flip bookkeeping,
> harness gaps, registration and Stage-1 authoring status) are recoverable with
> `git show 57253cf2:tests/plan/s103-test-plan.md`.

## §1 The increment-II QA-first drafting set (cited lanes)

### 1.1 Block B — the two write-path mechanisms (the centrepiece; each mapped to its gate)

| Lane / test group | File(s) | Mechanism → gate | RED/GREEN at draft |
|---|---|---|---|
| **F2v single-ctor witness fixture + parallel≡serial guard** | NEW `tests/fixtures/s99/f2v_single_ctor.cl` + row in `tests/s99_fixtures.rs` | R5 → **II-G1** (the F2v witness; §1.1-plan) | correctness guard GREEN at draft (parallel≡serial holds off-mechanism); the gate itself is a perf lane (§2) |
| **L-C3 reuse-corruption fence** (5 legs: (i) rc>1 copy-path other-ref-unchanged, (ii) token drop-feeds-alloc shared∧unique, (iii) on/off differential, (iv) ASan + heap-balance, (v) sustained epoch loop — exactly one COW per epoch via RC-stats deltas) | NEW `tests/ownership_reuse.rs` (behavioral+balance canonical; ASan scripted) | reuse tokens → **II-G2/G3/G4** (correctness precondition — a reuse fired on a non-unique value is heap corruption, backend §6.3) | behavioral+balance GREEN at draft (conservative codegen has no token path); **load-bearing when reuse tokens land** — the fence must stay green through the mechanism |
| **Reuse hit/miss counter smoke** (`reuse_hit`/`reuse_miss` move when the mechanism fires; zero when off) | `tests/ownership_reuse.rs` | H2 `reuse_hit`/`reuse_miss` (**LANDED S102**) → attribution prerequisite for **II-G2/G4** | GREEN at draft against the landed H2 grammar (counters exist, read 0 pre-mechanism); asserts non-zero once reuse fires |
| **R5 value-flatten witness (rc_inc collapse + null-elem-fn emission)** | `tests/ownership_reuse.rs` (rc_inc via RC_STATS) + L-B1 corpus extension (CLIF null elem fns) | R5 → **II-G1** attribution | rc_inc-collapse assertion RED-until-mechanism (F2v copies still inc pre-R5); CLIF assertion rides the corpus extension |
| **R5 soundness-couple negative fence** (a Copy-eligible-*looking* but NOT-flattened shape — >1 word per §7.2, or multi-ctor per §7.1 — must NOT be moded/treated `Copy`; sustained-use + ASan + heap-balance, no missing-inc UAF) | `tests/ownership_reuse.rs` (behavioral+balance) | `value_layout` single-source predicate soundness (spine §6.3 / backend §7.1) — the negative half | GREEN at draft (nothing flattens yet), **load-bearing when R5 lands** — the guard that a `Copy`-moded-but-unflattened param cannot slip through |

### 1.2 Block B — the differential oracle extended to the write path (§4 detail)

| Lane / test group | File(s) | Purpose | RED/GREEN at draft |
|---|---|---|---|
| **L-B1 corpus EXTENSION** (add the reuse-token shape + the one-word value-`Cell` shape as newly-green corpus entries in the mechanism change-sets; `MANIFEST.md`/`EXCLUSIONS.md` bookkeeping per the 0503 pins) | `tests/fixtures/clif_baseline/` + capture/diff script | byte-identical-off for the write-path mechanisms (ownership spine, its section 6.2) | extension lands WITH each mechanism (extension ≠ re-baseline) |
| **L-B2 byte-differential (ii)** on F2v + reuse fixtures under both `CRANELISP_NO_OWNERSHIP` polarities | scripted runner | toggle-on ≡ toggle-off observable output for reuse + R5 | discriminating once mechanisms land |
| **L-B3(4) `CACHE_SCHEMA_VERSION` 12→13 bump lane** | `tests/cache.rs` (extend) | R5's representation change wholesale-invalidates every pre-R5 `.o` (backend §7.4) | RED at draft (schema still 12); flips when R5 lands with the bump |

### 1.4 Block C — the T1 full cure acceptance (L-U1 negative-MUST protection)

- **`repl_redefinition::t1_downgrade_report_names_stale_compiled_callers_exactly`** — the
  S102 L-U1 RED (ledger item 1) that pins `repl/spec.md §18.1.1`'s `stale:` section (exact
  header line `; stale: compiled callers keep the previous definition of {cause}` + exact
  caller set). It flips GREEN when the T1 **interim print** lands (that was S102 Wave-4
  scope; carried). **For the S103 full cure** (end-of-turn-sequenced module reload,
  `design/int/session-transaction.md` §10 T1): author the cure-acceptance sibling pair:
  1. **`t1_full_cure_recompiles_stale_callers_stale_section_empty` (RED at draft).** After a
     downgrading (unannotated, generalizing) redefinition, the callers the interim report
     named as `stale:` are now RECOMPILED by the end-of-turn transaction, so the `stale:`
     section is **omitted entirely** (§18.1.1: "omitted when nothing is stale") AND the
     previously-stale caller called after the turn observes the NEW definition (positive:
     new behaviour; negative: NOT the old value). This is the Principle-8 shape the arch
     review pinned — the cure keeps the same report section, rendered empty.
  2. **`t1_full_cure_body_only_edit_still_no_report_no_recompile` (GREEN pin).** A body-only
     edit still prints only the §1.3 confirmation (the fast path must not over-trigger a
     reload) — guards the cure against recompiling the world on every turn.
- **L-U1 sibling reconciliation:** the S102 coherent-stale pins
  (`redefine_concrete_to_polymorphic_caller_survives_coherent_stale`,
  `redefine_concrete_to_overloaded_caller_survives_coherent_stale`, and the Wave-5
  Overloaded-T1 sibling) carry **flip notes** naming the full-cure acceptance. Under the
  cure their coherent-stale residue is superseded — either they flip (caller now recompiled)
  or their flip note is updated to record the cure's disposition. **None deleted or
  weakened**; `/qa` reconciles the notes in the same change-set as the cure lands (the
  "permanently-RED test for designed behaviour is wrong" ledger ruling — the flip note makes
  each test fail loudly exactly when the cure lands, which is the intended signal).

### 1.6 FIXME 0499 remainder — L-S1 lands, L-M1 grows with B3

Per FIXME 0499's per-lane status (5 of 7 lanes EXISTED at S102 close; remainder blocking
deletion = **L-S1** + **L-M1's B3-wave growth**):

- **L-S1 session-history preambles** (deferred in-sprint at S102, capacity-gated tail):
  author this sprint. Extend `repl_introspection.rs` + `repl_redefinition.rs` with the
  preamble-grid helper (prepends {∅, bare lookup, expression turn, prior failed turn,
  `/reset`} to stdin). Marginal value = generalization to the surfaces 6a did NOT burn
  (the 0486/0491/0484 cells already have guards). ~10–15 tests. If capacity forces deferral
  again, defer to S104 with rationale at the gate (0499 partial-resolution protocol).
- **L-M1 reference-shape × referent-kind × instantiation-count matrix** (rides B3): grows
  with the `fn_as_value` seam rework (backend §13.3). The **0474/0483 guards already flipped
  GREEN in S102** (SPRINT.md FIXME table: both STALE-cured, 17/17 green) — so L-M1's S103
  growth is the corpus EXTENSION with the newly-green shapes + the new value-use × ≥2-
  instantiation cells that the B3 reuse-token/R5 seam introduces (one exemplar per artifact-
  minting kind per axis; crashing→guards, passing→one-line controls). ~8–12 new cells.
- **0499 disposition at S103 close:** if L-S1 lands and L-M1's B3 growth is in, all 7 lanes
  exist → 0499 is DELETABLE by `/qa` (delete with a commit naming the resolution). Else
  annotate per-lane status and carry.

## §2 Gate plan — II-G1…II-G4 fixtures, measurement lanes, and the h3 flip

Gates are **perf lanes** (scripts beside `s99_measure.py`, outside canonical nextest, 30s
cap discipline), graded attended at the wave gate / acceptance run, on the **release** binary
with a **fresh toggle-off baseline re-captured on S103 HEAD** before grading (§1.2 discipline).
Each gate maps to exactly one mechanism per the Phase-2 verdict: **II-G1 ← R5**;
**II-G2/G3/G4 ← reuse tokens**.

| Gate | Fixture | Measurement lane | Bar | Attribution counter (must move) |
|---|---|---|---|---|
| **II-G1 (R5 witness)** | **F2v single-ctor** (`(deftype Cell (Cell [:Int value]))`, else identical to F2) — the honest R5 witness ratified at S100 close, since R5's first landing is one-word single-constructor (backend §7.1/§7.2) and does NOT cover F2's two-ctor `Cell` | `ig_gates.py` extension: F2v rc_inc + wall, on-vs-off, median-of-7 | rc_inc collapses to **< 1% of B2** (81-slot `Vec Cell` copies by `memcpy` with null elem fns) **AND F2v N-worker wall < F2v serial wall** — the **first parallel-must-pay gate** | rc_inc → near-zero (RC_STATS) — the mechanism's own effect; corroborated by the L-B1 null-elem-fn CLIF assertion (see §7 gap G-1) |
| **II-G2 (reuse hit-rate)** | F4 (copy-per-guess grid) | `ig_gates.py`: `reuse_hit`/`reuse_miss` on the guess-grid write chain | in-place reuse hit-rate **≥ 50%** (provisional; copy-once-then-in-place predicts ≫ this for chained writes) | `reuse_hit` (LANDED S102) — counter movement is the attribution prerequisite for any F4 wall claim (§0.3) |
| **II-G3 (F4 floor progress)** | F4-hard | `ig_gates.py` 11-rep **distribution** (never a single median pair) | median wall **≤ 2× serial** (from B7's 6–15×); whole median-to-max below toggle-off's | `reuse_hit` moved (II-G2 prerequisite) |
| **II-G4 (F2 two-ctor honesty)** | F2 (two-ctor `Cell` — the nested-ADT-constraint witness, NOT R5-first-landing-covered per §5 limit 1) | `ig_gates.py`: F2 rc_inc drop from reuse on chained copies + wall | partial: report rc_inc drop; wall **≤ 1.5× serial** (from B7's 2.3×). MUST NOT be silently graded as if R5 covered it (F2's shared-grid copies are genuine shared materializations, cured fully only by multi-ctor flattening or persistent DS — a composed-end-state III-G gate) | `reuse_hit` |
| **II-G5/G6** | = I-G4/I-G5/I-G6 re-run, **including F2v serial** | existing `ig_gates.py` I-G lanes | same non-regression + small-case overhead bars (≤+3% serial; ≤1.10× L-D1 turn) — the two-sided bar holds | I-G counters |

**Chaining witness (II-G2 companion, not a numeric gate):** the fused
`(map inc (map dec v))` pipeline as **two in-place passes, zero intermediate allocation**
(typecheck §7.2 success metric = proof chaining, not per-site elision). Reads `reuse_hit` +
RC_STATS alloc delta; differential twin (toggle-off ⇒ 2 allocs) confirms attribution.

**The h3 flip criterion** (restated for the gate context — h3 is report-grade, gates nothing):
per-extern adaptation-pair attribution (Hook H3 / L-D5) emits into RC_STATS; the L-D5 decision
rule then funds a deferred §9.2 sibling (`str-concat`, `eq`, `display`…) iff its pair
population exceeds ~1% of total RC ops on an acceptance fixture — the pattern grows by
measurement, never by tidiness. `str-len$borrowed` (the one template instance) is verified by
the S5 fence + L-B1/L-B2 regardless of measured win.

**Close-short seam (after B3):** if the sprint closes short, II-G5/II-G6 still run at the
seam (the two-sided small-case bar is live the moment a mechanism runs); II-G1–G4 defer with
the second mechanism per the SPRINT.md seam ruling. The `ig_gates.py` II-G runner therefore
lands in stage 1, not with B3.

### §2.1 Measured results (2026-07-06, release binary, median-of-7, settled load)

II-G runner landed in `ig_gates.py` (`--gates ii`); F2v added to
`s99_measure.gen_fixtures`. Full durable record: `s100-ownership-verification.md`
§2.3.1. Verdicts:

| Gate | Result | Numbers |
|---|---|---|
| **II-G1** | rc_inc **PASS**; parallel-pay benign non-pass | F2v rc_inc on=32,769 = 0.019% of B2 (bar <1%); allocs halved (2.10M vs 4.19M). N-worker 0.55s ≮ serial 0.12s — but N-worker is 10× faster than OFF (5.34s); R5 made serial too cheap to beat, not a regression |
| **II-G2** | **PASS** (decisive) | F4-hard reuse_hit=60 reuse_miss=0 = **100%** (bar ≥50%); f4_easy 49/0=100%. Counter moved. **Independent of the chaining witness** |
| **II-G3** | **FAIL — genuine regression** | F4-hard N-worker 108.8s vs serial 0.91s = **121×** (bar ≤2×). ON 108.8s vs OFF 5.46s (~20× parallel slowdown, analysis-on). New vs increment-I. → **FIXME 0534 (/backend)** |
| **II-G4** | wall FAIL = §5-limit-1 (not a regression) | F2 rc_inc drop 0.00% (honest — not R5-covered); N-worker 5.05s vs serial 0.52s = 9.69× (bar ≤1.5× from B7 mimalloc; ON≈OFF, system-alloc contention, III-G cure) |
| **II-G5/G6** | **PASS** (settled load) | F2v serial ON vs OFF wall −74.9% user −76.9% (R5); I-G5 small-case medians within ≤+3% (single-run trips = noise); compile Δ+0.0% |

**Task-3 verdict (0528 decision input):** II-G2 **IS met** by the delivered
mechanism (F4-hard reuse hit-rate 100% ≥ 50%, measured off the landed
`reuse_hit`/`reuse_miss` counters); the `chaining_toggle_off` `(map inc (map dec
v))` fusion witness **is NOT required** for II-G2 (it is a companion optimization
needing the typecheck uniqueness-preservation analysis, FIXME 0528). **0528 is a
clean carry.**

**Task-2 (FIXME 0527):** `cache_pre_r5_schema_object_invalidated_wholesale`
re-pointed to patch the manifest's `cache_format_version` global key (the actual
`check_manifest` invalidation gate) instead of the per-module `.meta.json`
`schema_version` (a later secondary guard) — flips GREEN. 0527 deleted.

## §4 Differential oracle — the write-path polarity extension

`CRANELISP_NO_OWNERSHIP=1` is the permanent correctness oracle (byte-identical to pre-S100
codegen). The byte-identical-off expectation **extends to the write-path mechanisms**:

- **Reuse tokens are off-ABI, function-local** (spine §3.5): toggle-off forces the
  conservative dealloc+alloc path — byte-identical to pre-reuse codegen. The oracle needs no
  new machinery here; L-B1 (CLIF byte-equality) + L-B2 (output byte-equality) cover it.
- **R5 flattening is representation-internal, toggle-gated:** toggle-off forces all-heap
  (no `Value` arm) — byte-identical to pre-R5. But R5 also bumps `CACHE_SCHEMA_VERSION`
  12→13, so the manifest global key must invalidate wholesale on a polarity flip (L-B3) AND
  on the schema bump (L-B3(4)).

**The named polarity lane:** **L-B2 (i) suite-polarity** (the entire canonical
`cargo nextest run` executes green under BOTH polarities — allowed delta = the ledgered
intentional-failing set, identical under both) + **L-B2 (ii) byte-differential** on the F2v +
reuse fixtures + the mechanism micro-fixtures. Run L-B2(i) at Phase-5 exit / wave gates
(gate-time, two full suite runs, never per-commit). The allowed-delta set at execution time
is `{h3}` until h3 flips, then empty — run `suite_polarity.sh` after the h3 flip so the
expected delta is empty.
