# S103 test plan — increment II (the write path): reuse tokens + R5 flattening, T1 full cure, typecheck-drain foundation

**Author:** `/qa` · **Date:** 2026-07-05 · **Status:** Phase 3 (design) deliverable —
planning only; test authoring is Phase 5 stage 1. Consumed by `/sprint` for wave
planning (`sprints/SPRINT.md` §"Skill plans (Phase 3) → /qa").

**Inputs:** `sprints/SPRINT.md` (Blocks A/B/C, the Phase-2 arch review PASS-with-revisions,
the FIXME table, the close-short seam after B3); `tests/plan/s100-ownership-verification.md`
§2.3 (Stage-II gates II-G1–G4), §3.1 (differential oracle L-B1/L-B2/L-B3), §3.4 (L-C3
reuse-corruption fence), §3.5 (L-D5 per-extern attribution / Hook H3), §5 (coverage limits
1–4), §6 (increment-II QA-first drafting list), §1.1 (F2v fixture);
`tests/plan/coverage-audit-s101.md` §2.4 (7-lane model) / §2.5 (4 standing drafting rules);
FIXME 0499 (e2e-lane refactor, target /qa — the QA-first stage head);
`design/arch/ownership-inference.md` §6.3/§7 (R5 mechanism, staging), §5.6 (slot versioning),
§10 items 5/10/11/14; `design/backend/ownership-codegen.md` §6 (reuse tokens), §6.3/§7 (R5
flattening), §7.2 (one-word bound), §7.6 (compatibility checklist), §9.2 (str-len sibling /
L-D5), §13.3 (fn_as_value seam rework); `design/typecheck/ownership-inference.md` §7 (write
path, `result_unique` chaining, eligibility-vs-permission); `repl/spec.md` §18.1.1 (the
downgrade-report `stale:` section — the T1-cure negative-MUST); `tests/plan/ledger.md`
(guard inventory; the sole carried intentional RED = `h3_rc_stats_reports_per_extern_adaptation_pairs`).

Where this plan and the spine disagree, the spine governs. Metrics discipline is
`s100-ownership-verification.md` §0 verbatim (two-sided bar; median-of-7; F4 as a
distribution; no wall attributed unless the mechanism's own counter moved).

---

## §1 The increment-II QA-first drafting set (Phase 5 stage 1), by lane

All new tests carry `// spec:` anchors (`spec_link_check.py` on every drafting commit) and
ledger rows. RED-first drafting gets ONE ledger entry per the S101 §6.1 precedent
("S103 Phase-5 Stage-1 increment-II QA-first RED set", six fields); carried REDs at close
get full entries and join the root-`CLAUDE.md` intentional-failing count. The 4 standing
drafting rules (audit §2.5) govern every item: value-use × instantiation-count rows key on
artifact-minting; shape-pinning MUSTs get exact assertions; new session-visible state kinds
get restart + preamble rows at drafting; designed floors get flagged to user-proxies in-phase.

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
| **L-B1 corpus EXTENSION** (add the reuse-token shape + the one-word value-`Cell` shape as newly-green corpus entries in the mechanism change-sets; `MANIFEST.md`/`EXCLUSIONS.md` bookkeeping per the 0503 pins) | `tests/fixtures/clif_baseline/` + capture/diff script | byte-identical-off for the write-path mechanisms (spine §6.2) | extension lands WITH each mechanism (extension ≠ re-baseline) |
| **L-B2 byte-differential (ii)** on F2v + reuse fixtures under both `CRANELISP_NO_OWNERSHIP` polarities | scripted runner | toggle-on ≡ toggle-off observable output for reuse + R5 | discriminating once mechanisms land |
| **L-B3(4) `CACHE_SCHEMA_VERSION` 12→13 bump lane** | `tests/cache.rs` (extend) | R5's representation change wholesale-invalidates every pre-R5 `.o` (backend §7.4) | RED at draft (schema still 12); flips when R5 lands with the bump |

### 1.3 Block B5 — the h3 owed-signal flip (the sole carried intentional RED)

- **`ownership_fences::h3_rc_stats_reports_per_extern_adaptation_pairs`** — already in the
  suite, RED, targeting increment II (ledger §"Sprint 102 Phase-5 Stage-1" item 22). **Flip
  criterion:** the per-extern adaptation-pair attribution lands — a runtime, name-keyed tally
  map of adaptation-inc/consuming-dec pairs paid at each extern site, emitted into
  `CRANELISP_RC_STATS` as a per-extern sibling family (Hook H3, backend §9.2/§13.2.1 grammar
  extension, owner `/dev` for `/backend`, intrinsics/primitives seam). This rides the **L-D5
  sibling-expansion decision** — the `str-len$borrowed` dual-symbol convention (spine §10
  item 14; backend §9.2) — which is itself increment-II work. When H3 emits the per-extern
  pairs, the test's assertion (RC_STATS output contains the per-extern pair population) flips
  GREEN. `/qa` observes the flip, annotates the ledger row in place with sprint + SHA, updates
  the test-file note; the test is never deleted or weakened.

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

### 1.5 Block B1 / Block C — coupled-work coverage (typecheck-drain quartet + write-path queries)

- **The drain quartet 0509/0510/0511/0513 is primarily unit-tier** (`/dev` for
  `/typecheck` — every fix lands with its unit test in the same change-set). `/qa`'s e2e
  obligation is only where the fix is observable end-to-end:
  - **0510** (`neq`/string has no primitive entry to carry declared facts): the new
    declared-`Borrowed` primitive rows extend the **L-D3e fact-table per-row behavioral
    guards** (`ownership_fences.rs`, one test per declared-fact row — arg survives the call,
    usable after, balances). A write-path fact row that mis-declares fails a row-test rather
    than corrupting silently. RED-until-the-row-exists.
  - **0509/0511/0513** (generalization-ordering resettle, pass5 session-memo threaded field,
    qualified-lookup phantom-child gap): internal typecheck plumbing — **no new e2e owed**;
    the existing redefinition/qualified-lookup e2e surface (`repl_redefinition.rs`,
    `spec_08_modules.rs`, `repl_mod_devloop.rs`) is the regression envelope. If a quartet fix
    changes an observable resolution outcome, the affected existing test is the guard; flag a
    row only if a currently-untested observable behaviour appears.
- **The write-path queries (spine §7 Q4):** the static-uniqueness proof subset
  (`result_unique` chains, typecheck §7.2) + the dynamic rc==1 discriminator. `result_unique`
  is advisory (false is always sound); II starts emitting `true`. The **observable
  acceptance witness is proof CHAINING** (typecheck §7.2/§7.3): the fused
  `(map inc (map dec v))`-class pipeline measured as **two in-place passes, zero intermediate
  allocation** — attributed via the `reuse_hit` counter + RC_STATS alloc delta. Draft
  `reuse_chaining_map_inc_map_dec_two_in_place_passes` (RED-until-mechanism) as the II-G2
  chaining witness, plus its differential twin (toggle-off ⇒ two allocations).

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

---

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

---

## §3 FIXME 0499 lane-refactor plan (the QA-first stage head)

0499 is the /qa half of the S101 audit's action set (the /dev unit-tier half is
0495/0496/0498, Block C). It lands **incrementally, riding the sprints whose scope touches
each surface** — not a monolithic refactor. S103 disposition:

- **Lands this sprint:** **L-S1** (the deferred capacity-gated tail — §1.6) and **L-M1's
  B3-wave growth** (§1.6). These are the two remainder lanes blocking deletion.
- **Standing drafting rules (§2.5) — binding on every S103 drafted test** (restated in §1
  head): (1) value-use × instantiation-count rows key on artifact-minting — exercised by
  L-M1's ≥2-instantiation cells on the B3 reuse/R5 seam; (2) shape-pinning MUSTs get exact
  assertions — exercised by the §18.1.1 `stale:` exact-header T1-cure acceptance and the R5
  rc_inc witness; (3) new session-visible state kinds get restart + preamble rows at drafting
  — the write-path introduces no new *session-visible* state kind (reuse tokens are off-ABI
  function-local, R5 is representation-internal), so this rule is satisfied vacuously this
  sprint EXCEPT the T1 full cure, whose recompiled-caller state gets an L-S1 preamble row;
  (4) designed floors flagged to user-proxies in-phase — the II-G4 "F2 not fully cured" honesty
  and the R5 one-word-bound limit are flagged to `/port`/`/examples` at the Phase-6 gate.
- **Deletion condition:** all 7 lanes exist (or explicitly retired) AND the drafting rules
  are in the qa working docs (DONE). If L-S1 + L-M1-growth both land, `/qa` deletes 0499 at
  close with a commit naming the resolution; else the per-lane status table is annotated and
  the FIXME carries with rationale at the wave gate.

---

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

---

## §5 Coupled-work coverage summary (mapping every task item to a guard)

| Coupled item | Coverage | Tier |
|---|---|---|
| Typecheck-drain quartet 0509/0510/0511/0513 | 0510 → L-D3e fact-row guards (e2e); 0509/0511/0513 → existing resolution/redefinition e2e envelope (no new owed) + unit-tier (/dev typecheck) | mostly unit; e2e where observable |
| Write-path queries (static-uniqueness + dynamic rc==1) | II-G2 chaining witness + L-C3 reuse fence + `reuse_hit` attribution | e2e + perf |
| T1 full cure | §18.1.1 `stale:`-section-empty cure-acceptance pair + coherent-stale flip-note reconciliation | e2e (`repl_redefinition.rs`) |
| repl §18.1.1 negative-MUST | exact-header `stale:` section, exact caller set both ways, section-omitted-when-clean — the "split world is never silent" protection | e2e, exact assertion (drafting rule 2) |
| R5 `value_layout` soundness-coupling | §1.1 negative fence (Copy-eligible-but-unflattened must not be moded Copy — no missing-inc UAF) + the single-source predicate is drift-proof by construction (one predicate in `cranelisp-types`; /dev(types) unit-pins `value_layout(ty)` per FIXME 0498) | e2e negative fence + unit-tier (types) |

---

## §6 Guard-flip bookkeeping

**Carried intentional RED into S103 (1):** `h3_rc_stats_reports_per_extern_adaptation_pairs`
— flips with L-D5 / Hook H3 (§1.3). (0474×3 + 0483×3 flipped GREEN in S102 per the SPRINT.md
FIXME table — both STALE-cured, 17/17 green; their deletions route to `/backend` at a wave
gate.)

**New transient REDs this sprint (QA-first drafting, expected to flip in-sprint as the
mechanisms land):** the L-B3(4) schema-bump lane; the R5 rc_inc-collapse witness; the II-G2
chaining witness; the T1 full-cure `stale:`-empty acceptance; the L-D3e write-path fact rows;
the reuse hit/miss non-zero assertions. ONE drafting-batch ledger entry; any carried at close
get full entries and join the intentional count.

**Flip protocol per set** (the §7.1 precedent): fix + unit test in the same change-set
(`/dev`); `/qa` observes the flip (controls stay green), annotates the ledger row in place
with sprint + SHA, updates the test-file "RED on HEAD" note. Tests never deleted or weakened.

**Root-`CLAUDE.md` §Testing count at close** (noted, not edited here): `/qa` supplies exact
close-state counts in its Phase-7 suite report; `/sprint` flags the user edit. Full-sprint
outcome → h3 flips + the transient REDs flip → expected **0 intentional failures**. Close-short
after B3 → h3 may carry if L-D5 defers with the second mechanism (count = 1 + any carried
drafting REDs). Two consecutive `--no-fail-fast` runs with identical fail sets remain the
close-verification standard.

---

## §7 Harness readiness + gaps needed from /design and /arch

**Exists and ready:** `CRANELISP_RC_STATS` incl. the H2 per-mechanism family
(`reuse_hit`/`reuse_miss`/`stack_slot`/`rc_nonatomic`/`rc_atomic` — LANDED S102); F1–F4
fixtures + `s99_fixtures.rs` parallel≡serial guards; `ig_gates.py` (the I-G runner, extend for
II-G); `s99_measure.py` (measurement discipline); `suite_polarity.sh` (L-B2(i));
`CRANELISP_CODEGEN_DUMP` + `tests/fixtures/clif_baseline/` (L-B1 substrate); the `h3` RED
(owed-signal, awaiting L-D5).

**Gaps (named, with owners) — I have enough to draft the Phase-5 failing tests, but these
must land in their named change-sets for the gates to be gradeable:**

| # | Gap | Needed by | Owner / when | Blocks drafting? |
|---|---|---|---|---|
| G-1 | **R5 flatten-fired attribution** — whether II-G1 needs a `value_flatten` H2 counter, or whether rc_inc-collapse (RC_STATS) + a null-elem-fn CLIF assertion (L-B1) suffices to attribute the win to R5 (vs borrow-elision) on F2v. Backend §7.3 says "zero new runtime code" for flattening, so there may be no runtime counter — the CLIF/rc_inc pair is the witness. **Confirm with /design-backend.** | II-G1 attribution (§0.3 discipline) | /design-backend — ruling at B3 design | No — I draft the rc_inc + CLIF witness now; a counter would only strengthen it |
| G-2 | **F2v fixture ratification** — the `(Cell [:Int value])` single-ctor shape + whether the exemplar/F2 refactor to a scalar-payload wrapper is in scope, or F2v stays a standalone synthetic. §1.1-plan ratifies F2v as QA-owned standalone; confirm no exemplar coupling is expected for II-G1. | II-G1 fixture | /qa authors; **confirm scope with /sprint** (no /design dependency) | No |
| G-3 | **`result_unique = true` emission point** — typecheck §7.2 says II starts emitting `true`; confirm the chaining witness (`(map inc (map dec v))` two-in-place-passes) is the intended acceptance surface and that `reuse_hit` distinguishes token-reuse from inline-COW mutate-in-place. **Confirm with /design-typecheck.** | II-G2 chaining witness | /design-typecheck — B1/B2 design | No — drafted RED-until-mechanism; the counter granularity affects the assertion, not the shape |
| G-4 | **T1 full-cure report shape under the cure** — confirm `session-transaction.md §10` renders the §18.1.1 `stale:` section EMPTY (Principle-8 same-section shape) rather than suppressing the whole report; and confirm which S102 coherent-stale pins flip vs get flip-note-superseded. **Confirm with /design-src (int).** | T1 cure-acceptance pair + pin reconciliation | /design-src (int) — Block C1 T1 design | No — §18.1.1 is normative; I draft to it; the pin-flip mapping is reconciled when the cure lands |
| G-5 | **`value_layout` predicate + `VALUE_LAYOUT_MAX_WORDS` + schema 12→13** landing in the B3 change-set (the /arch-authored `cranelisp-types` carrier). Needed for the L-B3(4) schema-bump lane and the soundness-couple negative fence to be gradeable. Already named as the one new cross-crate edge in the Phase-2 review. | L-B3(4), R5 negative fence | /arch (predicate) + /design-backend/typecheck (consumers) — B3 | No — drafted RED-until-landing |

**Exit-gate readiness — READY for Phase 5.** The II-G gate bars, fixtures (F2v ratified),
measurement lanes, the differential-oracle write-path extension, the h3 flip criterion, the
T1 negative-MUST, and the coupled-work coverage are all concrete enough to draft the failing
tests directly from this document. The five gaps above are landing dependencies on named
owners in named change-sets, not planning holes — none blocks Phase-5 drafting (every
dependent test drafts RED-until-its-mechanism-lands, which is the QA-first discipline). No
new FIXME filed: the h3 RED is the record+trigger for L-D5 (`memory/feedback_no_fixme_with_failing_test.md`),
and G-1/G-3/G-4 are Phase-3 co-resolution questions to the per-crate /design plans, not
cross-skill change requests.

---

## §8 Registration

- Registered in `tests/CLAUDE.md` §Plan documents (this pass).
- Peer of `tests/plan/s100-ownership-verification.md` (whose §2.3 gates + §6 drafting list it
  executes for increment II) and `tests/plan/s102-test-plan.md` (the increment-I predecessor).
- Ledger rows for all new tests land with the drafting commits (Phase 5), not this plan.

---

## §9 Phase-5 Stage-1 authoring status (2026-07-05, /qa)

Written this pass. Full suite after the batch: **3972 run / 3960 passed / 12 failed /
1 skipped** (51.9s) — 12 reds = the carried h3 + 11 new QA-first reds. No pre-existing
green regressed. Ledger: `tests/plan/ledger.md` §"Sprint 103 Phase-5 Stage-1
increment-II QA-first RED set".

| Plan item | File(s) | Status |
|---|---|---|
| §1.1 F2v single-ctor fixture + parallel≡serial + capture-borrow guards | `tests/fixtures/s99/f2v_single_ctor.cl`, `tests/s99_fixtures.rs` | **written — GREEN** (correctness guards) |
| §1.1 L-C3 reuse-corruption fence (5 legs) | `tests/ownership_reuse.rs` | **written** — legs i/iii/iv/v GREEN; leg ii RED (reuse_hit); + discovered-defect RED (pure SSA alias) |
| §1.1 reuse hit/miss counter smoke (landed H2 grammar) | `tests/ownership_reuse.rs` | **written** — family-present GREEN; nonzero-when-fires RED |
| §1.1 R5 value-flatten witness (rc_inc collapse) | `tests/ownership_reuse.rs` | **written — RED** (F2v≈F2 pre-R5) |
| §1.1 R5 soundness-couple negative fence | `tests/ownership_reuse.rs` | **written — GREEN** |
| §1.2 L-B2(ii) byte-differential on F2v/F2 under NO_OWNERSHIP | `tests/s99_fixtures.rs` | **written — GREEN** (oracle) |
| §1.2 L-B3(4) `CACHE_SCHEMA_VERSION` 14→15 invalidation lane | `tests/cache.rs` | **written — RED ×2** (schema still 14) |
| §1.4 T1 full-cure acceptance pair | `tests/repl_redefinition.rs` | **written** — recompile+empty-stale RED; body-only over-trigger GREEN |
| §1.4 coherent-stale flip-note reconciliation | `tests/repl_redefinition.rs` | **written** — 4 pins' flip notes updated in place (none weakened) |
| §1.3 h3 flip-shape confirmation | `tests/ownership_fences.rs` | **confirmed** — left RED, correctly shaped to flip at L-D5/H3 |
| §1.5 0510 L-D3e `neq-string` fact rows (e2e) | `tests/ownership_fences.rs` | **written — RED ×2** (`neq-string` undefined until 0510 registers it) |
| §1.5 chaining witness `(map inc (map dec v))` two-in-place + differential twin | `tests/ownership_reuse.rs` | **written** — value-correct GREEN; two-in-place + twin RED |
| §1.6 L-S1 preamble-grid helper + tests | `tests/repl_introspection.rs`, `tests/repl_redefinition.rs` | **written — GREEN ×7** (robustness generalization) |
| §1.6 L-M1 B3-wave value-use × ≥2-instantiation cells | `tests/vec_query_value_use.rs` | **written — GREEN ×3** (write-op/pipeline/constructor controls) |
| §4 L-B2(i) suite-polarity allowed-delta note | `tests/scripts/suite_polarity.sh` | **updated** — expected shared set = `{h3}` + the transient S103 reds until they flip |

**Pending a mechanism (all the reds above)** — each flips green in its named change-set;
`/qa` observes the flip, annotates the ledger row + test-file note, never deletes/weakens.

**FIXME 0499 disposition:** L-S1 landed + L-M1 B3-growth landed (both this pass). Per §3
deletion condition, 0499's remainder lanes now exist → deletable by `/qa` at close if the
per-lane audit confirms all 7 lanes present; else annotate + carry. Not deleted this pass
(defer the deletion decision to the wave/close gate).
