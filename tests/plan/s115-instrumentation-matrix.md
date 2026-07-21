# S115 instrumentation-completeness verification matrix (Phase 3, 2026-07-20, /qa)

**Mandate**: SPRINT.md Track B early wave — every recommendation row from
`design/arch/safety-invariants.md` §4 (R1–R14, as re-audited by /arch at S115
Phase 2), `tests/plan/memory-safety-coverage.md` (§1 oracle gate, §2
generative harness, §3 adversarial practice, §4/§4.1 audit category +
fence-lifecycle ruling), the S113 risk-assessment tiers (Tier-5 diagnostic
modes, Tier-3 seam-assertion density, standing `RC_DEC_CHECK` positives), and
the 0604 observability rider (MODULE_TRACE + closure predicate) → its named
mechanism → **VERIFIED-IN-PLACE** (file:line + the test that exercises it) or
**OWED** (owner + change-set shape, this sprint) or **DEFERRED/PARKED** (with
the sanctioning record).

**Method**: every VERIFIED verdict below was checked against SOURCE at HEAD
(`5ba28de8` + the S115 planning tree), not against records — the S108-R-4
lesson (a multi-part acceptance silently half-executed) is the audit lens. No
row closes on "it was scheduled". Live suite evidence: ONE full
`cargo nextest run --no-fail-fast` this session — **5164 run / 5153 passed /
11 failed / 1 skipped**; the 11 REDs are exactly the S114 attributed-carry
set (enumerated in `s115-test-plan.md` §1), and neither named flap
manifested in this run. Per the standing counting convention this is one
observation, not a certification (that needs ≥2/≥3 identical runs).

## Verdict summary

- **VERIFIED-IN-PLACE: 14 rows** (R1 mechanism, R2, R3, R5, R8, R9, R10,
  R11, R14 instrumentation-half, §1 gate, §3 practice, §4 category, §4.1
  lifecycle incl. per-mode self-tests, RC_DEC_CHECK positive set, MODULE_TRACE
  current seams — see table).
- **OWED this sprint: 5 items** — (O1) R7/0604 wave (predicate correction +
  census row + MODULE_TRACE at the staging-commit seam + NEW synthesized
  trigger — the existing unit test cannot guard the corrected predicate, see
  R7 row); (O2) R6 persisted-index validation seam; (O3) R4 mangle-family
  census + witnesses; (O4) §2 generative harness v1 (recommendation: OWED,
  bounded — see row); (O5) §1.3 strategy-doc as-built amendment (done in this
  change-set, /qa-owned).
- **DEFERRED/PARKED with sanction: 3 rows** — R13 (user, S115 Phase 1), R12
  (session-transaction sprint, by design), 0637/R5-sibling (parked to first
  consumer, re-affirmed S113 W5).
- **REGISTERED-FUTURE (not S115, correctly so): 1** — R3's P7 single-sourcing
  evaluation (§6 cascade task 2; register carries no sprint tag — recorded so
  it cannot masquerade as scheduled).

## The register rows (R1–R14)

| Row | Mechanism named | Verdict + evidence |
|---|---|---|
| R1 ownership-summary truth | §3a lattice + §3b producer split + §3c rule table | **VERIFIED-IN-PLACE (mechanism).** `Origin::{Fresh, Unconditional, Conditional}` is walk-internal at `crates/cranelisp-typecheck/src/ownership/transfer.rs:150` (enum; rustdoc states no serde/no schema impact); hard-claim publish arms in `origin_to_result_mode` match ONLY `Unconditional` (`transfer.rs:263–283` — Conditional publishes `MayAliasOf`, never `AliasOf`/`ProjectionOf`). Rule table lives at `design/typecheck/ownership-inference.md` §16. Exercised by: the ownership unit tiers + the tier-4 lane (R9). **Open INSTANCE (not an instrumentation gap): the chained-`MayAliasOf` family** — live REDs `safety_oracle_lane::safety_lane_chained_{nested,let_bound}_cow_projection_returns_set_value_abort_free_red` (verified RED this run). Fix constraints are Track A rows (plan §1.1): family grain, §16.2 rule-table rows, never a 5th consumer arm, 0693 fence before/with. |
| R2 elision-consumer safe default | P18 exhaustiveness; no `#[non_exhaustive]` | **VERIFIED-IN-PLACE.** `crates/cranelisp-types/src/ownership.rs:35–45` — module rustdoc pins the no-`#[non_exhaustive]` exception and its rationale; no `#[non_exhaustive]` attribute present in the file. Maintenance = /review's `_ =>`/`== Fresh` grep per landing (process, in force). |
| R3 declared-fact truthfulness | whole-table sweep, matrix-tested | **VERIFIED-per-register** (matrix-tested; CW-F3a/Fence-3 pins; /arch spot-verified unchanged S115 P2). The owed item on this row — P7 single-sourcing of the emission convention across `ownership_facts`/`vec_codegen` — is §6 cascade task 2, **NOT scheduled S115**; recorded here as REGISTERED-FUTURE so the register's "evaluate" verb is not mistaken for done or for in-flight. |
| R4 keyed-identity injectivity | census: witness-or-disambiguator per mangle family | **OWED (O3, scheduled S115, SPRINT §B).** In place today: the drop-glue tier-2 model only — `escape_symbol` prefix-free escaping at `crates/cranelisp-backend/src/compiler/resolution.rs:134–182` with round-trip tests in `resolution/tests.rs`. All other mint families (impl$FQType$FQTrait method keys, inner-fn span discriminators, GOT data symbols, platform export names, `LinkerSymbol` mangles) are UNAUDITED. Change-set shape: /design(backend) census table (durable artifact) → per-family witness-or-disambiguator; every family the census keeps gets a unit-test row per METHOD §2.2 (plan §6.2 reserves them). |
| R5 GOT index in range | always-on asserts + fallible allocate + cache-seam diagnosed error | **VERIFIED-IN-PLACE.** Always-on `assert!(slot < GOT_TABLE_SIZE)` in BOTH `store_slot` and `load_slot` (`crates/cranelisp-types/src/got.rs:135–159`, with the S111-R7 rationale rustdoc). Cache-seam validation of `callable_got_slot` at `crates/cranelisp-backend/src/cache/serialize.rs:295` (+ `cache/mod.rs:590`). 0637 sibling-slot validation: **PARKED to first consumer** (R5 ruling re-affirmed S113 W5; the P8 co-landing rule IS the mechanism) — sanctioned, not owed. |
| R6 persisted-index trust boundary | ONE validation seam in `deserialise_meta_with_build_id`, `CacheStale` class per family | **OWED (O2, scheduled S115, /dev(backend, cache)).** Verified partial as registered: the seam exists (`cache/serialize.rs:248` `deserialise_meta_with_build_id`) and validates `callable_got_slot` only (`:295`). Un-validated persisted indices confirmed by absence: sibling slot, `callees` FQs, summary param indices (an out-of-range `MayAliasOf(k)` from corrupt bytes indexes `arg_origins[k]`), span keys. Change-set shape per /arch revision 3: ONE validation seam, one `CacheStale` class per family, census table lands in the cache-submodule rustdoc, /review verifies census completeness. Unit + e2e rows: plan §6.1. |
| R7 prelude export closure | declared-export-closure predicate at the ONE chokepoint, unconditional diagnosed error, MODULE_TRACE at the seam, synthesized-trigger unit test | **OWED (O1 — the 0604 early wave). Current state verified `asserted`-but-BLIND, exactly as /arch found:** (a) both landed predicates are provider-existence-shaped — `prelude_write_is_closure_valid` (`src/imports.rs:245–264`, `.is_public()` on the source) and `write_is_closure_valid` (`src/imports.rs:357–367`, `.is_some()`); `bit-and` IS a bundled public primitive (`crates/cranelisp-primitives/src/lib.rs:412`), so the live phantom (undeclared-PUBLIC entry whose source genuinely provides the name) passes BOTH by construction. (b) `commit_staging_to_live` (`src/worker.rs:439`; `live.insert` `:513`) routes through NO gate and emits NO trace — grep-verified. (c) The falsified premise comment survives at `src/imports.rs:251–252` ("bit-and is homed in num.bits, absent from primitives" — FALSE) and in the unit-test narrative (`src/imports/tests.rs:904–942`). (d) **Critical finding for the wave: the existing chokepoint unit test (`imports/tests.rs:942` `check_terminal_closure_rejects_out_of_closure_public_write`) injects a source that LACKS the name — a trigger that both the current AND the corrected predicate reject. It cannot fail on a revert of the correction.** The 0604 synthesized trigger must be the discriminating shape: source PROVIDES the name, entry OUTSIDE the declared export closure (the live phantom's shape). Full test design: plan §3. |
| R8 RC balance | tier-5 modes M1/M2/M3 + per-mode self-tests + A1–A4 seam checks | **VERIFIED-IN-PLACE, fully.** (a) Modes hooked on the single-sourced funnels: `crates/cranelisp-intrinsics/src/diagnostics.rs` (env gates incl. `CRANELISP_RC_DEC_CHECK` at `:92`). (b) **Per-mode unit-tier synthetic self-tests (the §4.1 prong-1 mandate): `diagnostics/tests.rs` — quarantine ×2 (`:12`, `:35`), scrub ×2 (`:64`, `:81`), parity ×4 (`:100`, `:108`, `:116`, `:124`), + `all_gates_default_off` (`:134`, the byte-identical-off fence)** — matches /arch's count exactly. (c) Tier-3 A1–A4 codegen-time gates release-gated on `CRANELISP_RC_DEC_CHECK`: `crates/cranelisp-backend/src/heap.rs:352` + `crates/cranelisp-backend/src/compiler/vec_codegen.rs` (grep-verified both files gate on the var). (d) **Per-mode e2e env-plumbing fences (prong 3): every mode has one** — `tests/ms_p6_mode_self_tests.rs`: M3 planted-teardown-leak abort (`:55`) + M3/M1/M2 clean-run wiring cells (`:71`, `:79`, `:87`); plus M1 quarantine planted face (`tests/macro_expansion_interior_alias_double_free.rs:201`) and M3 parity positives (`tests/ms_p8_conj_leak.rs:91`, `:108`). No mode lacks a wiring fence. M2 (scrub) has clean-run wiring only, no planted e2e fault — compliant per §4.1 prong 2 (opportunistic by nature; the unit tier carries detection durability). |
| R9 differential-oracle equivalence | standing nextest-visible lane + combinator | **VERIFIED-IN-PLACE — and the §1.3 question is answered: it IS an enforced nextest gate today, not a manual cert.** `SafetyMatrix` + `assert_safety_matrix` in `tests/helpers/e2e.rs:1561–1721` assert all four §1.2 signals — face 4 (RC_DEC_CHECK zero) at `:1700–1710`. `tests/safety_oracle_lane.rs` (8 test cells) drives it; RED-under-lane proven live this run (the two chained MS-P7 cells). Three as-built deviations from §1.3's letter, all ACCEPTED (O5 amendment records them in the strategy doc): no `tests/fixtures/safety_corpus/` directory sweep (as built: named per-cell tests through the combinator — better failure naming, same enforcement); no `CRANELISP_SAFETY_FULL` split (moot until the lane approaches its wall budget); batching caveat handled per-cell rather than by a combinator-owned dual run. The `[oracle]` plan-row discipline is in force (S113/S114 plans). |
| R10 resolve-once keyed reads hard-fail | hard-error arms + negatives | **VERIFIED-IN-PLACE, with live behavioral evidence**: the loud keyed-consumer miss is firing as designed in two of today's REDs (`fn_as_value_carrier_loss`, `shadowing_scope_lookup::…auto_curry…` — the consumer hard-fails instead of soft-falling-back; the PRODUCER gap is the defect, per the carrier-loss class definition). /arch spot-verified the arms unchanged. Citation note: the register's "KC-N1..N6" test names did not resolve to current test fns by grep — the battery has been renamed/absorbed since S110; /qa will re-anchor the register row's test citation at the next annotation pass (cosmetic; the mechanism is source- and behavior-verified). |
| R11 concreteness at codegen | P20 slot ⟺ `is_concrete()` + backstop asserts | **VERIFIED-per-register** (unconstructable; /arch re-audit unchanged; the S84 structural shape is the mechanism — no sprint-scheduled residue). |
| R12 published-pointer retention / slot freeze | slot-freeze assert WITH the R3 machinery | **PARKED by design** — pinned to the session-transaction sprint; not S115 scope. Note: the S115 impl-redefinition fix (plan §1.6) uses the EXISTING GOT-patch path and does not widen redefinition exposure (/arch §5), so it does not trigger this row. |
| R13 fork-join error-slot ferry | tier-3 ferry at both boundaries | **DEFERRED — user-sanctioned S115 Phase 1** (parked on the test-discovery implementation wave). Recorded; no S115 action. |
| R14 COW count-truth | escape gate + tier-4 lane + R8 lanes | **VERIFIED (instrumentation half)**: checks = the R9 lane + R8 DEC_CHECK, both verified above; the two open chained-face pins are RED **inside the lane** — i.e. the family's live faults are already under the strongest available signal (and double as the §4.1 face-1-note's live signal-4 plants while RED). Open residue = the R1 fix instance (Track A). |

## Strategy-doc + tier rows

| Row | Verdict + evidence |
|---|---|
| §1.2/§1.3 oracle gate wiring | **VERIFIED** — see R9. The gate is enforced (nextest-visible, fails the suite); the CS-0.5 "manual cert" disease is structurally closed for lane-covered programs. |
| §1.5 0641 gate-before-fix sequencing | **DISCHARGED (historical)** — the lane landed S113 W1 with 0641 B-1 RED-under-lane as acceptance, before the fix wave; nothing owed. |
| **§2 generative harness v1** | **NOT BUILT — verified by absence**: no `tests/gen_ownership_flows.rs`, no generator module anywhere under `tests/`, no `CRANELISP_SAFETY_FULL` consumer in code (the string exists only in the strategy doc). The S113 W5 frame said "generative harness deferred S114"; S114 did not build it; the deferral has no user sanction on record for S115. **Recommendation (decision for /sprint → user at Phase 4): OWED S115, bounded** — ONE /testing dispatch, v1 CORE ONLY (§2.2: depth-2, one representative value kind per operator pair, ≤60s serialized, always-on; the env-gated full sweep may land trivially with it), scheduled AFTER the Track-A chained-family fix wave (so generated failures are not dominated by the known REDs, and the harness immediately audits the fix's blind spots — the §1.5 argument applied to the S115 fix). Grounds: this sprint's charter is precisely "recommendations actually in place"; the chained-`MayAliasOf` family is a composition-space defect the §2.1 operator algebra enumerates mechanically (the depth-2 space contains B-1/I-1/I-2 verbatim, and set∘set∘project — this sprint's face — at depth 3/2); the combinator (its only build dependency) is landed and proven. **Fallback if Phase-4 capacity fails: explicit user-sanctioned deferral to S116** with rationale recorded on this row (lane + named cells carry S115's fix verification; the harness is additive coverage, not the fix gate) — a silent third slip is the S108-R-4 shape and is not an option. |
| §3 adversarial / model-independent authorship | **VERIFIED (process, in force)** — refute-instructed review briefs are standard in safety-surface dispatches (S114 W-review chain); matrix axes derive from spec/design (M1–M3 standing matrices). Continues as practice; no mechanism owed. |
| §4 standing audit category | **VERIFIED (process)** — this matrix IS the S115 execution of the category; the §4 sweep-list surfaces with no structural argument remain: macro-expansion marshalling (0638 family — fixed S114; generator-v2 axis stands) and spark admission (corpus growth). No new elision surface arrived unregistered this sprint (maintenance rule holds). |
| §4.1 capability-fence lifecycle | **VERIFIED — all three prongs, per mode**: prong 1 (unit self-tests) and prong 3 (per-mode e2e wiring) cited under R8; prong 2 compliance: the m1_quarantine retirement tombstone stands; the S114 re-plant (`safety_lane_detects_falsified_clean_expectation_capability_green`, `7c2d5168`) is the worked synthetic-plant example; the two chained pins are the current live differential/signal-4 plants — when the family drains, the capability question returns to prong 1 per the face-1 note (already recorded in §4.1). |
| Tier-3 seam-assertion density (S113 tiers) | **VERIFIED** — A1–A4 seam checks release-gated on `CRANELISP_RC_DEC_CHECK` at the two intrinsics funnels (`diagnostics.rs:92` gate) + backend codegen-time gates (`heap.rs:352`, `compiler/vec_codegen.rs`); R5/R10 always-on asserts cited above. The R7 chokepoint's tier-3 sub-form (diagnosed error, self-identifying as an internal R7 breach) is part of O1. |
| **Standing `RC_DEC_CHECK` positive-assertion set** | **VERIFIED — the 4-file set is the DESIGNED set, not residue.** Designed composition: (1) **the systemic carrier** — `SafetyMatrix` face 4 (`tests/helpers/e2e.rs:1700–1710`): every lane/matrix cell runs a DEC_CHECK-positive leg, which is how positive coverage scales (corpus growth, not per-file scatter); (2) **direct positives ×2** — `tests/safety_oracle_lane.rs:366–380` (collision must-not-trip cell) and `tests/macro_expansion_interior_alias_double_free.rs:172–178` (M1-OFF explicit DEC_CHECK face); (3) **polarity hygiene ×2** — `tests/ownership_fences.rs:802` and `tests/golden_clif_w0b.rs:96` are `env_remove` sites, BY DESIGN (§1.3 names the env_remove hygiene explicitly; they prevent env bleed, they are not assertion sites). Standing rule derived: new DEC_CHECK positives land via the lane/combinator, not as scattered per-file `.env` sites; a per-file positive outside a repro's own mode-face is a plan-conformance finding. |
| **MODULE_TRACE seam coverage** | **VERIFIED (current) + OWED (the 0604 addition).** Emitting today: `src/imports.rs:229` (prelude-closure debug seam) + `:336` (terminal-closure chokepoint breach); `src/session_v4/index_worker.rs:1008`, `:1051` (index feed); `src/process_form/cache_restore.rs:122` (discovery/cache-hit); `src/save.rs:864` (regen section-completeness breach). **Not emitting: the staging→live commit seam** (`src/worker.rs::commit_staging_to_live`) — the 0604-wave addition (O1) and the seam the re-attribution evidence names as the suspected writer. |

## Owed-item → change-set map (Phase-4 input)

| # | Item | Owner | Change-set shape | Test rows |
|---|---|---|---|---|
| O1 | R7/0604 wave: declared-export-closure predicate (closure PRECOMPUTED — no map read under the DashMap `get_mut` guard) as unconditional diagnosed error self-identifying as an R7 breach; `commit_staging_to_live` census row (route-or-legal-skip); MODULE_TRACE at that seam; `src/imports.rs:251` falsified-comment fix (arch revision 2) | /dev(src), early wave | one change-set; /design(int) §2.2 correction rides | plan §3 (synthesized trigger — NEW discriminating shape; false-fire fence; existing test retained as sibling with comment corrected by /testing) |
| O2 | R6 validation seam: census every persisted index → ONE seam in `deserialise_meta_with_build_id`, per-family `CacheStale`; census table in cache-submodule rustdoc; /review completeness check | /dev(backend, cache) | one change-set | plan §6.1 |
| O3 | R4 mangle census: every symbol-mint site → witness or disambiguator | /design(backend) census → /dev per family | census artifact + per-family fixes as needed | plan §6.2 |
| O4 | §2 generative harness v1 core (recommendation OWED; Phase-4 fallback = explicit user deferral to S116) | /testing | one dispatch, after the Track-A fix wave | plan §6.4 |
| O5 | §1.3 as-built amendment (corpus-dir/per-cell shape, SAFETY_FULL status, batching note) | /qa | done this change-set (`memory-safety-coverage.md` §1.3 note) | — |

Exit check for SPRINT Track B: with O1–O4 landed (or O4 explicitly
user-deferred), every row above is VERIFIED-IN-PLACE or carries an explicit
user-sanctioned deferral; no row rests on a scheduling claim.

## O-row delivery status (updated post-W3, 2026-07-21, /qa)

Source-checked against the wave commits, not against the wave reports.
Disposition detail: `s115-test-plan.md` §8.6.

| # | Status | Evidence / what actually landed | Residual |
|---|---|---|---|
| **O1** — R7/0604 wave | **DELIVERED (W2, `d9f2caea` + review `c9d1585e`)** | Destination-keyed declared-export-closure predicate replacing provider-existence; `commit_staging_to_live` ROUTED with `D(M)` precomputed before the `get_mut` guard (deadlock hazard honored); `SharedState.declared_exports`; **MODULE_TRACE now emits at the staging→live commit seam** (the one seam the matrix listed as not-emitting — that row is now closed); unconditional diagnosed error self-identifying as an R7 breach; falsified `imports.rs:251` comment corrected. The §3.1 binding trigger shape was authored as specified (provides-name-but-outside-declared-exports) and **RED-on-revert was demonstrated** — the matrix's binding wave finding held. | The 0604 FIXME does not retire on O1 alone: /review FIXME 0740 shows the census **closure claim** is still materially false (`src/bootstrap.rs:446`, `src/platform.rs:407` undispositioned). /design(int), W6. R7's register row moves `asserted`-but-BLIND → **asserted-and-discriminating**, but the closure-completeness half is open. |
| **O2** — R6 persisted-index validation seam | **DELIVERED (W3, `4ea5c758`)** | The ONE existing loop in `deserialise_meta_with_build_id` extended: 4 validation arms + 4 distinct `CacheStale` classes + the census table in the cache-submodule rustdoc **with an honest scope note**; 6 cells incl. a false-fire fence. Change-set shape matches /arch revision 3 exactly. | public-api +15 lines (the `CacheStale` variants) — **/arch sign-off owed** per the baseline-diff discipline. /review verifies census completeness at its pass. |
| **O3** — R4 mangle-family census + witnesses | **BLOCKED — census landed, injectivity fix re-routed cross-crate (W3)** | /design(backend)'s census named `got_data_symbol_name` as backend's owed witness (`.`→`_` flatten, constructible collision). /dev found the function **DUPLICATED, with the `cranelisp-types` copy as the definer's** — a backend-only change broke 40+ cross-module calls. Landed instead: backend body reduced to a one-line forward to the types copy (P7) + a corpus-equality fence. **Injectivity belongs at the types home → FIXME 0748 (`/arch`).** LinkerSymbol / method-mangle `$`-join / platform export names were already routed cross-crate by the census. | **O3 CANNOT close as VERIFIED in S115.** Its honest exit state: census artifact + P7 de-duplication + corpus fence landed; the injectivity witness-or-disambiguator is OWED at `cranelisp-types` and gated on 0748's /arch disposition. This is a Track-B row that ends the sprint **OWED with a named owner** — recorded here so it cannot masquerade as delivered at Phase 7. |
| **O4** — §2 generative harness v1 core | **PENDING — W7, per the accepted OWED recommendation** | Unbuilt at W3 (verified by absence at Phase 3; nothing since has touched `tests/`). The dependency it waited on is now MET: the Track-A fix waves that would have dominated generated failures with known REDs are W3-complete on the backend side. What it needs at W7: ONE `/testing` dispatch, v1 CORE ONLY per `memory-safety-coverage.md` §2.2 (depth-2, one representative value kind per operator pair, ≤60s serialized, always-on; the env-gated full sweep may ride free); it consumes the landed `SafetyMatrix`/`assert_safety_matrix` combinator, its only build dependency. **Sequencing caveat added post-W3:** the entry-payload leak does NOT flip this sprint (`s115-test-plan.md` §8.1 — re-attributed to int), so a depth-2 flow whose result is a heap value reaching the program boundary will trip signal 2 for THAT reason; the dispatch must either exclude program-result-heap shapes from v1's generation space or pre-register that face as a known attributed RED, so the harness's first run is not read as noise. | Fallback unchanged: explicit user-sanctioned deferral to S116 recorded on this row — a silent third slip is the S108-R-4 shape and is not an option. |
| **O5** — §1.3 as-built amendment | **DONE (Phase 3)** | `memory-safety-coverage.md` §1.3 note. | — |

**Amended Track-B exit check:** O1 and O2 are VERIFIED-IN-PLACE. O3 exits
**OWED-with-owner** (0748 → `/arch`, `cranelisp-types` home) — the Phase-7
statement must say this in those words rather than counting O3 as landed.
O4 is a W7 gate. R7's matrix row and the 0604 FIXME retire together, at the
W6 census disposition, not at O1's landing.

---

# W7 RE-AUDIT AGAINST THE STRONGER BAR (FIXME 0767, 2026-07-21, /qa)

**The bar changed mid-sprint and this section re-runs every row against it.**
Per FIXME 0767 (`target: /qa`, now discharged here) and METHOD §2.2, a row is
**VERIFIED** only when it cites, alongside the mechanism's file:line, the
**capability test that plants the fault the instrument claims to catch and
observes detection**. Two things that are NOT that bar, and each of which
carried rows in the Phase-3 pass:

- "the mechanism exists at file:line" — proves the code is present, not that it
  fires;
- "a test exercises it" — proves the code runs, not that it discriminates.

The S115 lane taught this the hard way: the RC face asserted
`imbalance(ON) == imbalance(OFF)` over two configurations of ONE codepath, five
real leaks lived in the shared non-gated part, and every cell compared
`0 == 0`. Tests exercised the lane constantly. In `/testing`'s words, *the
lane's pass was not weak evidence, it was NO evidence*.

**MOVEMENT IS THE FINDING, NOT A REGRESSION.** Nothing below got worse this
sprint; the instruments are the same or better than at Phase 3. What changed is
that the register now reports what it can prove instead of what it can point
at. A row moving from VERIFIED to `asserted-but-unproven` is the audit working.

## Verdict movement summary

**Eight rows move. Seven demote (in whole or in part); one is conditional.**

| Row | Phase-3 verdict | W7 verdict | Why it moved |
|---|---|---|---|
| R1 producer-split half | VERIFIED-IN-PLACE | **partially proven** | join half now has a real plant (below); the `origin_to_result_mode` hard-claim arms have none |
| R3 declared-fact truthfulness | VERIFIED-per-register | **asserted-but-unproven** | "matrix-tested; CW-F3a/Fence-3 pins" is exercise, not detection — no cell plants a false declared fact and observes the sweep catching it |
| R5 GOT index in range | VERIFIED-IN-PLACE | **asserted-but-unproven** | always-on `assert!` at `got.rs:135–159`, but nothing constructs an out-of-range slot and observes the abort |
| R9 differential-oracle equivalence | VERIFIED-IN-PLACE | **asserted-but-PARTIALLY-proven** | the S114 re-plant proves the combinator notices a falsified *expectation*; nothing plants the **differential-blindness** class (a leak in the shared, non-ownership-gated part, where ON and OFF agree) that 0767 was written about |
| R14 COW count-truth (instr. half) | VERIFIED | **partially proven** | its checks ARE R9 + R8; inherits R9's gap |
| §1.2/§1.3 oracle gate wiring | VERIFIED | **partially proven** | same mechanism as R9 |
| Standing `RC_DEC_CHECK` positive set | VERIFIED | **partially proven** | the two direct positives + M1/M3 planted faces are proven (R8); the *systemic carrier* — `SafetyMatrix` face 4, the leg the design says is how positive coverage SCALES — inherits R9's blindness |
| R10 resolve-once keyed hard-fail | VERIFIED-IN-PLACE | **VERIFIED, transient proof** | its only detection evidence is two LIVE REDs firing as designed. Per §4.1 ("synthetic, never a live defect") that proof **dies with the fix** — the m1/m3 lesson, third occurrence |

**The demotions are not eight independent findings. They are ONE.** R9, §1.2/§1.3,
R14 and the `RC_DEC_CHECK` systemic carrier are the same instrument counted four
times: a single unproven differential propagated an unearned VERIFIED to three
dependent rows. That is 0767's thesis, now measured rather than argued — *the
proofs of the parts do not compose into a proof of the composition*, and the
inverse is worse: an unproven composition silently certifies its consumers.

### Rows the bar does NOT apply to (re-labelled, NOT demoted)

Recording these explicitly so a future reader does not "fix" them:

- **Tier-1 unconstructable — R2, R11.** The detection proof is the Rust compiler.
  Reverting R2's mechanism (adding `#[non_exhaustive]` to the mode enums) breaks
  every downstream exhaustive match; reverting R11's is a type error. A build
  that fails IS the fault being planted and detected. **VERIFIED, bar satisfied
  by tier.**
- **Process rows — §3 adversarial authorship, §4 standing audit category.**
  These are practices, not instruments; there is no fault to plant. **In force
  (process).** Do not carry them in the instrument count.
- **Observability — MODULE_TRACE seam coverage.** Trace emission is a
  diagnostic aid, not a fault detector. The safety claim at that seam is the
  0604 predicate, and *that* is proven (below). **Bar N/A.**

## Rows that now MEET the bar, with their proofs

New proofs landed this sprint. Each cites a planted fault and observed
detection:

| Row | Detection proof (the plant + the observation) |
|---|---|
| **R7 prelude export closure** | **The 0604 gate's fail-on-revert trigger.** The synthesized trigger is the discriminating shape (source PROVIDES the name, entry OUTSIDE the declared export closure) and **RED-on-revert was demonstrated** — reverting the predicate correction reddens it. Second, independent proof at the same wave: `bootstrap_seeds_pass_the_terminal_closure_gate` sweeps every seeded entry under the STRICTEST closure `D(M) = {}` so an unknown-`D` permit cannot mask, and detection was demonstrated by flipping the `macros` seeds to Public → RED, revert → GREEN. This row's Phase-3 finding (that the *pre-existing* chokepoint test could not fail on a revert of the correction) is exactly what the bar exists to catch, and it was caught prospectively. |
| **R6 persisted-index trust boundary** | **Per-variant RED-then-GREEN + a false-fire fence.** Each of the four validation arms was demonstrated RED before its `CacheStale` class landed and GREEN after; the false-fire fence pins that a *valid* persisted index is not rejected. Both polarities, per family. |
| **R8 RC balance** | Unchanged and still the strongest row: per-mode synthetic self-tests (quarantine ×2, scrub ×2, parity ×4) plant faults at the unit tier, and `ms_p6_mode_self_tests:55` plants a **teardown leak** e2e and observes the M3 abort. Planted, synthetic, per mode. |
| **R1 join half** | **The `Origin`-lattice property cells** (`ownership/transfer.rs` → `transfer/tests.rs::join_lattice_*`): **3 of 4 are RED on revert, and each names the mechanism it protects.** These are seam-level algebraic-property cells over the lattice with no program involved — structurally capable of failing on an order asymmetry, which the pre-existing program-SHAPE cells were not. The 4th cell's non-reddening is honest residue, recorded not hidden. |
| **Backend RC/ownership gates** | **The structural fence `rc_ownership_fence_tests`** — reverting any gate names the offending file:line. A fence that reports *where* on revert is stronger than one that merely reddens. |
| **Dead-lookup enrolment** | **The `force_enroll` predicate**, extracted as a testable predicate with a measured detection proof, plus a **false-fire measurement**: zero spurious fires across 5333 tests, release-mode byte-for-byte identical to HEAD. The false-fire half is the leg most instruments skip. |
| **§4.1 capability-fence lifecycle** | Prongs 1 and 3 proven per mode under R8; prong 2's worked example is the S114 re-plant. The mandate itself is met **at the mode grain** — 0767's generalisation of §4.1 from "mode" to "instrument, including a composed one" is what the R9 demotion above records as not yet met. |

## O3 and O4 — the two owed items, honestly

**O4 — §2 generative harness v1: CLOSED, and it is more than a coverage item.**
`tests/gen_ownership_flows.rs` landed at W7 (5 owning types × 9 positions × 2
toggles × 2 iteration counts = 45 cells / 180 runs / 1.59s), carrying **4
synthetic capability fences — planted constant leak, planted over-release,
planted per-iteration scaling leak, planted unmeasured run — each fail-on-revert
proven, plus an anti-vacuity guard** that measures a real clean cell as clean.
Exclusions are pre-registered and structural (no suppressed assertions; the
0745 program-result-heap face has no template in the generator at all, and the
0760 capture exclusion carries its measured rates so removing it is the
post-fix acceptance check).

Two things follow, and the second matters more than the first:

1. The matrix item closes. O4 is **VERIFIED with detection proof** — the only
   owed row that landed already meeting the new bar, because the bar was known
   when it was specified.
2. **The harness is the structural answer to the R9 demotion.** Its instrument
   is an *absolute* balance (`allocs == deallocs` exactly, both polarities, with
   a scaling rate), not a differential between two configurations — so the
   `0 == 0` blindness that made the lane's pass no evidence **cannot arise by
   construction**. The four plants prove it detects the classes the lane could
   not. The lane keeps its job (differential equivalence across the ownership
   toggle, which the harness does not replace); the harness supplies the
   detection floor underneath it. On its FIRST run it found a reaching context
   nobody had enumerated (0796, curried partial application stranding at the
   identical rate as an explicit capture) — the return on a generative
   instrument arriving inside one wave.

**O3 — R4 mangle-family injectivity: NOT DELIVERED. It exits the sprint
OWED-with-owner and must not read as delivered.** What landed: the
/design(backend) census artifact, the P7 de-duplication of
`got_data_symbol_name` (backend body reduced to a one-line forward to the
`cranelisp-types` definer), and a corpus-equality fence. What did NOT land: the
injectivity witness-or-disambiguator, because the fix belongs at the
`cranelisp-types` home and a backend-only change broke 40+ cross-module calls.
**Routed to `/arch` as FIXME 0748.** LinkerSymbol, the method-mangle `$`-join,
and platform export names were already routed cross-crate by the census and are
equally open. Phase-7 wording is binding: *O3 is owed, its owner is `/arch`, and
its instrument is 0748* — one census plus one de-duplication is not an
injectivity proof, and this row has no detection proof of any kind (nothing
plants a colliding mint and observes a diagnostic).

## S116 obligations this re-audit creates

Ordered by what a failure would cost, not by effort:

1. **Plant the differential-blindness class** (closes R9 → §1.2/§1.3 → R14 →
   `RC_DEC_CHECK` carrier, all four, with one fence). The plant: a leak in the
   shared, non-ownership-gated codepath, where `imbalance(ON) == imbalance(OFF)`
   and both are wrong. Synthetic, per §4.1 — never planted on a live defect.
   The harness's `gen_flows_capability_detects_planted_constant_leak` is the
   template; the work is porting that discipline into the combinator.
2. **Replace R10's transient proof before the carrier-loss family drains.** Its
   detection evidence is currently two live REDs. When they flip, the row silently
   becomes unproven and nobody will notice — this is the m1/m3 lesson for the
   third time. A synthetic keyed-consumer miss, planted at the unit tier, lands
   BEFORE the fix.
3. **R5 and R3 are cheap** — one `#[should_panic]` cell constructing an
   out-of-range GOT slot; one cell planting a false declared fact and observing
   the whole-table sweep reject it. Both are afternoon work and both close a row.
4. **O3 / 0748** — `/arch` disposition on the `cranelisp-types` injectivity home.

## Amended verdict summary (supersedes the Phase-3 counts)

- **VERIFIED with detection proof: 7** — R6, R7, R8, R1 (join half), §4.1
  (mode grain), O4 harness, backend structural fence + dead-lookup predicate.
- **VERIFIED by tier (unconstructable; bar N/A): 2** — R2, R11.
- **VERIFIED, transient proof (expires at the fix): 1** — R10.
- **Partially proven: 4** — R1 (producer-split half), R9, R14, §1.2/§1.3,
  `RC_DEC_CHECK` systemic carrier *(one mechanism, four rows)*.
- **asserted-but-unproven: 2** — R3, R5.
- **Process / observability (bar N/A): 3** — §3, §4, MODULE_TRACE.
- **OWED-with-owner: 1** — O3 (→ `/arch`, FIXME 0748).
- **DEFERRED/PARKED with sanction: 3** — R13 (user, S115 Phase 1), R12
  (session-transaction sprint), 0637/R5-sibling (parked to first consumer).

FIXME 0767 is **discharged by this section**: the criterion is upgraded, the
`asserted-but-unproven` status exists and is populated, the re-audit ran, and
the movement is recorded as a finding. The §4.1 generalisation from "diagnostic
mode" to "instrument, including a composed one" is adopted — item 1 above is its
first bill.
