# Sprint 118 QA plan — instrumented ownership closure

**Status:** Phase 3 plan of record
**Authority:** `/qa`; `/testing` authors e2e sources; narrow `/dev` owners author
unit tiers beside their seams
**Baseline evidence:** full-run 2026-07-25 (5,514 run / 5,486 passed / 28
failed / 1 skipped), reconciled name-for-name against live test sources below
**Binding architecture inputs:** `sprints/SPRINT.md` §Architecture review
rulings 1–13; `design/intrinsics/diagnostic-modes.md` §6–§9;
`design/backend/transitive-drop-glue.md`; `design/int/result-owner.md`

## 1. Certification split and detector-arming discipline (ruling 3, structural)

Two independent certification verdicts, as in S116, with one **structural**
change ruled by `/arch`:

1. **Deterministic suite — UNARMED.** The full `cargo nextest run
   --no-fail-fast` suite runs with **no detector environment variable exported
   at suite scope, ever**. Detector arming (`CRANELISP_QUARANTINE_FREED`,
   `CRANELISP_SCRUB_FREED`, `CRANELISP_ALLOC_PARITY`, `CRANELISP_RC_DEC_CHECK`,
   `CRANELISP_TEST_FAULTS`/`CRANELISP_TEST_FAULT`) is legal **only** as a
   per-subprocess `.env(…)` on a spawned child, or inside a fault-plant child
   built per §7.1 of `diagnostic-modes.md` (`env_clear` + explicit allow-list).
   A globally-armed M3 would abort every still-red leak guard and destroy the
   baseline arithmetic. Structural enforcement:
   - no test file may read a detector variable from its own process env or
     export one via `std::env::set_var`;
   - `/testing`'s W1 static gate greps for suite-scope arming and any
     `set_var` of a `CRANELISP_*` detector variable — a hit is a W1 FAIL;
   - `/review` rejects any change-set that arms a detector outside a child
     `.env`/`env_clear` construction.
   Existing per-child armed legs (e.g. `ms_p8_conj_leak`'s
   `CRANELISP_ALLOC_PARITY` leg, the M3 subprocess pair) are compliant and
   unchanged.
2. **Load-dependent — separate.** `launch_grid_corrupt::…` is certified
   separately per §5; it is never folded into the deterministic scalar.

**Exit contract (deterministic):** two consecutive complete captured runs with
identical failure sets, and that set is **empty** except for explicitly
user-approved carries recorded at close (candidates pre-authorized by the
Phase-1 cut order: 0869 implementation, 0868, Track C's three-run loaded
certification — in that order; 0863 is renegotiated with the user, never
silently dropped). Any RED outside §2's enumeration plus this sprint's named
intended-RED additions (§2.3) is a regression and blocks close.

**Schema fence (ruling 1):** exactly one `CACHE_SCHEMA_VERSION` delta (23→24)
is authorized this sprint, in the 0869 carrier window, only if the 0869
implementation ships. A schema delta in any other change-set is a `/review`
REJECT and a close blocker.

## 2. The 28-RED baseline contract

### 2.1 Enumeration (from live sources, 2026-07-25)

Every name below carries a live `// defect:` attribution; zero unattributed.
The **flips** column names the wave whose change-set must turn the cell GREEN.

| # | Test | Defect | Flips at |
|---:|---|---|---|
| 1 | `match_owned_temporary_scrutinee_0810::inline_call_wrapper_scrutinee_does_not_leak` | 0810 | B (backend) |
| 2 | `match_owned_temporary_scrutinee_0810::inline_call_wrapper_scrutinee_does_not_leak_linked` | 0810 | B (backend) |
| 3 | `match_owned_temporary_scrutinee_0810::inline_constructor_scrutinee_does_not_leak` | 0810 | B (backend) |
| 4 | `match_owned_temporary_scrutinee_0810::inline_scrutinee_with_heap_payload_does_not_leak_box_or_field` | 0810 | B (backend) |
| 5 | `match_owned_temporary_scrutinee_0810::wrapper_from_call_superseding_loop_param_does_not_leak` | 0810 | B (backend) |
| 6 | `match_owned_temporary_scrutinee_0810::let_bound_scrutinee_payload_outlives_the_match` | 0810 | B (backend) |
| 7 | `match_owned_temporary_scrutinee_0810::let_bound_scrutinee_payload_outlives_the_match_linked` | 0810 | B (backend) |
| 8 | `match_owned_temporary_scrutinee_0810::let_bound_scrutinee_loop_result_still_matches_its_own_tag` | 0810 | B (backend) |
| 9 | `match_owned_temporary_scrutinee_0810::let_bound_scrutinee_loop_result_still_matches_its_own_tag_linked` | 0810 | B (backend) |
| 10 | `match_owned_temporary_scrutinee_0810::var_pattern_arm_consuming_owned_temporary_releases_it_once_linked` | 0782 | B (backend) |
| 11 | `capture_drop_glue_strands_nested_heap_0760::closure_capturing_vec_of_strings_does_not_leak` | 0760 | B (backend) |
| 12 | `capture_drop_glue_strands_nested_heap_0760::closure_capturing_adt_with_string_field_does_not_leak` | 0760/0796 | B (backend) |
| 13 | `capture_drop_glue_strands_nested_heap_0760::nested_adt_chain_past_glue_depth_limit_does_not_leak` | 0760 depth cliff | B (backend) |
| 14 | `transitive_drop_glue_s116::finite_recursive_values_zero_one_many_terminate_and_balance` | recursive-glue termination | B (backend) |
| 15 | `adt_drop_glue_underkey::entry_main_ioresult_heap_payload_toggle_off_leak_r2` | 0745 | B (int/exe-bundle) |
| 16 | `program_result_owner_s116::run_nested_pure_payload_observed_then_released_both_toggles` | 0745 | B (int/exe-bundle) |
| 17 | `program_result_owner_s116::linked_nested_pure_payload_converts_then_releases` | 0745 | B (int/exe-bundle) |
| 18 | `program_result_owner_s116::repl_nested_heap_value_displays_before_exact_release` | 0745 | B (int/exe-bundle) |
| 19 | `ms_p8_conj_leak::conj_loop_does_not_leak` | 0688 TCO supersede | B (backend), verified consequent |
| 20 | `ms_p8_conj_leak::conj_loop_parity_no_abort` | 0688 TCO supersede | B (backend), verified consequent |
| 21 | `exemplar_ownership_residue_s116::sudoku_warm_serial_solve_residue_at_most_1400` | 0840 composite | B, verified consequent (§4.4) |
| 22 | `intrinsics_m3_detection_s116::m3_parity_catches_injected_imbalance` | 0848 | A (intrinsics) |
| 23 | `intrinsics_m3_detection_s116::m3_parity_clean_child_exits_normally_control` | 0848 (+ possible 0745 coupling, §2.2) | A, possibly A+B |
| 24 | `launch_grid_corrupt::launched_strand_grid_get_assoc_does_not_corrupt_heap_neg` | 0694 family (load-dependent) | C (separate certification, §5) |
| 25 | `spec_11_stdlib::def_definition_echo_names_user_binding_not_internal_thunk` | 0863 DF-1 | D (src) |
| 26 | `spec_11_stdlib::def_info_and_sig_describe_bound_value_not_macro` | 0863 DF-2 | D (src) |
| 27 | `cache::cache_restored_parent_enrols_private_test_child` | 0868 | D (src) |
| 28 | `cache::cache_restores_sibling_written_trait_impls_for_dispatch` | 0869 | D conditional (ruling 1) |

### 2.2 W1 reconciliation obligations (two low-confidence cells)

Static inspection cannot fully color two cells; `/testing`'s W1 baseline
reconciliation resolves both **from the captured 2026-07-25 run log** (or, if
the log is not retained, one targeted per-binary run — never a full-suite
rerun for this purpose):

1. **`ms_p8_conj_leak` third member.** The file holds three tests; the S117
   contaminated gate counted 3 failures there, the family gloss says the two
   `conj_*` guards. Confirm whether `int_loop_control_balances_green` (whose
   second leg runs the child under `CRANELISP_ALLOC_PARITY=1`) is in the 28.
   If it is, the enumeration above trades one cell (most plausibly by the M3
   clean control at #23 being GREEN) and the table is corrected name-for-name
   in this file — arithmetic must land exactly on the verified 28.
2. **The M3 clean control (#23) coupling.** With parity armed, the clean
   child aborts on ANY exit imbalance — including the ambient 0745
   program-result leak if its child program's result were heap-typed (it is
   `Int`, so the expected coupling is via compiler-side allocation only).
   Determine from the failure output whether #23's RED is 0848-only (flips at
   W2) or leak-coupled (flips only after W4). Record the answer here; the
   exit reconciliation depends on it.

### 2.3 Intended-RED additions this sprint

New failing-not-ignored cells authored in W1 are recorded as a separate named
set and do not alter the 28-baseline arithmetic (S116 W1 precedent):

- the ruling-10 structural fence (§4.3) — RED until Track B W3;
- the 0726 mixed-arm exact-balance tripwire cells (§4.2) — the ctor-path cell
  is expected RED (leak-safe residue) until Track B W3;
- the 0830 eliminator-axis harness rows (§4.2) — RED until Track B W3;
- the 0867 polymorphic-accessor repro (§6.2) — RED until its `/dev`
  attribution and fix (this sprint fixes it only if capacity allows; it is
  not in the pre-authorized carry list, so an unfixed 0867 repro at close
  needs an explicit user-approved carry).

Every addition carries `// spec:` and (for defect repros) one `// defect:`
line; no `#[ignore]`; no baseline name renamed or deleted.

### 2.4 Exit reconciliation

Phase 7 reports name-for-name: each of the 28 either GREEN (with the flipping
change-set named), or an explicit user-approved carry (pre-authorized
candidates in §1). A cell that goes green **without** its owning fix landing
is treated with suspicion, not celebration — S98 rule: perturbation reshapes
layout; the flip must trace to the mechanism change-set, and the Track-B
fixes must be demonstrated with detectors armed in their acceptance legs
(§4.1), not by symptom absence.

## 3. Track A — detection proofs (the sprint's foundation)

### 3.1 Eight detector rows × plant triplets (0848)

Per `diagnostic-modes.md` §7.3, each row is a fresh-subprocess triplet:
**positive** (plant + detector → named observation + expected failure mode),
**clean control** (detector, no plant → normal exit, no report), **negative
control** (plant, detector off → observation absent, no UB executed).

| Row | Plant | Required positive observation |
|---|---|---|
| M1 quarantine | dealloc, re-request same layout, stale-RC-op quarantined base | address never re-handed; lifecycle check names the planted base |
| M2 scrub | dealloc (retained via M1), read payload via `heap_access` | exact `POISON_WORD`, then stale-RC rejection |
| M3 leak | suppress exactly one discharge | atexit leak report + non-zero abort |
| M3 over-free | one ledger over-free event, no UB | atexit double-free polarity + non-zero abort |
| A1 zero-RC inc | zero planted allocation's RC, `rc_inc` | rejection before resurrection |
| A2 interior ptr | interior/non-base address to dec validation | address/range rejection before mutation |
| A3 freed ptr | dec a logically-freed (M1-retained) base | lifecycle rejection before mutation |
| A4 malformed header | corrupt planted header size, `dealloc` | header/size rejection before layout/disposal |

Acceptance per row (all four required; asserted-but-unproven is worth zero):

1. the triplet exists at the production funnel (`alloc_with_rc`/`dealloc`/
   `rc_inc`/`consume_shallow`/`atomic_dec_rc`) — a test that bypasses the
   funnel or instantiates `Quarantine`/internal state directly does not count;
2. **fail-on-revert demonstrated and recorded**: disabling/reverting the
   detector makes the committed positive FAIL (the `/dev` change-set records
   the revert demonstration per row; `/review` verifies the record);
3. subprocess isolation per §7.1: `env_clear`, exact arm
   `s116-detection-proof-v1`, exactly one closed `FaultPlant` spelling, fresh
   tempdir, `--no-cache`, no inherited `CRANELISP_*`;
4. unarmed byte-inertness: with the arm variable absent there is no state
   construction, counter adjustment, or new failure (unit-pinned).

The M3 **e2e pair is already committed** (`intrinsics_m3_detection_s116`,
cells #22/#23) and flips here; e2e proves composition
(counter→atexit→report→abort through the production compiler binary), the
unit children own both polarities. No new e2e detector cells are owed unless
a public diagnostic mode can express a plant without internal APIs — `/dev`
proposes, `/qa` disposes; default is unit-tier.

### 3.2 0850 convergence — what pins behavior-invariance

`drop.rs` deletes its private `read_i64` and copied Vec offsets, delegating
to `heap_access`/`vec_runtime` (ruling 6). Pins:

- unit: the `heap_access`/`vec_runtime` matrix rows of `diagnostic-modes.md`
  §10 (round-trip, largest field offset, typed Vec readers; M2 reads through
  the shared accessor; **no local reader/offset copy** — grep-zero in
  `drop.rs`);
- behavior-invariance evidence: zero e2e delta — every currently-GREEN
  drop/Vec/ADT cell stays green AND every currently-RED cell in §2.1 stays
  RED with byte-identical failure signature in the same run. A RED that flips
  in the 0850 change-set is *mis-attributed evidence*, not a win — it reopens
  attribution;
- zero public-API delta for the convergence itself (the subtractive delta
  below is ruling 7's, riding the same change-set but separately accounted).

### 3.3 Ruling-7 subtractive API change — baseline regeneration check

`reset_counts()` and `bytes_peak()` removed from `cranelisp-intrinsics`; the
remaining counters are monotonic process-lifetime evidence (M3's monotonicity
cannot be invalidated by a public reset). Cells:

- `crates/cranelisp-intrinsics/public-api.txt` regenerated in the SAME
  change-set, subtractive-only diff;
- grep-zero `reset_counts`/`bytes_peak` across the crate's src + rustdoc;
- `tests/facade_compliance.rs` + `tests/public_api_relocations.rs` green;
- the catalog guard `name_set_is_exactly_expected` remains the only numeric
  authority (no count-bearing prose reintroduced).

### 3.4 0857 regrade — sequencing and inputs (mine)

The regrade of R8/detector-mode grades runs **after**: (a) W2's triplets land
with recorded fail-on-revert evidence, and (b) `/arch` actions FIXME 0768
(register status vocabulary) — ruling 12 pairs the two in one window so the
regrade lands into the amended vocabulary. Inputs: the per-row revert records,
the M3 e2e pair's color, and the dead-citation repair
(`s115-instrumentation-matrix.md` line-55 tombstone reference). Output: each
mode graded at its actually-proven tier — proven, or explicitly downgraded;
no "asserted" grade survives without a matching triplet. Grades land in
`tests/plan/memory-safety-coverage.md` + the instrumentation matrix, and the
`/arch` register row consumes them.

### 3.5 0859 ProjectionOf witness — CONDITIONAL cell (ruling 2)

**Not a suite cell yet.** The instrument is the **existing** env-gated
detector surface (M1/M2/M3 + RC/parity counters) used as an oracle over
isolated-declaration-mutation experiments (`ownership_facts.rs`:
`ProjectionOf(0) → Fresh`, applied singly, restored after each experiment) in
fresh subprocesses over production consumer shapes **beyond** the bounded
S117 set. The §7 fault-plant protocol is NOT the instrument (plants prove
detectors; they cannot witness declarations). Gates:

1. **May only begin after §3.1's proofs land** (0768 rule: an unproven
   detector cannot serve as an oracle);
2. if a shape is found where the mutation changes armed-detector observations
   (parity imbalance, quarantine/scrub firing) while the truthful declaration
   stays clean → `/testing` commits the ordinary-source witness with the
   mutation record appended to the S117 §4.1 acceptance record, and R-2
   closes (disposition 1);
3. if every surveyed production shape remains emission-inert under armed
   detectors → that is **disposition 2, returned to the user** via the FIXME
   (is typecheck transfer evidence + direct body guards sufficient, or is a
   designed observable requirement wanted?). It is not overridden with
   test-only facts, and no new seam/carrier/hook is proposed without `/arch`
   review and user approval.

## 4. Track B — consumer migration acceptance (the RED clearance payload)

### 4.1 Carried S116 matrix — reconciliation, not re-derivation

The S116 §3 acceptance matrix stands unchanged as the contract (depths
1/2/4/5/>5; recursive 0/1/many termination; eliminator faces; ownership
displacement; typed-context exits; both analysis toggles; REPL/`--run`/
`--link`). Reconciliation of what already exists vs. what is owed:

| Axis | State | Owed in S118 |
|---|---|---|
| Depth 1/2/4 shallow control, 5/>5 cliff (both toggles), recursive 0/1/many | landed S116 W1 (static gate §8 verified) — cells #13/#14 + green controls | nothing to author; cells flip at W3 |
| Match eliminator (ctor/var × inline/let-bound × payload) | committed cells #1–#10 + 4 green controls | nothing to author; flip at W3 |
| Capture/curry teardown | cells #11–#12 + green capture controls | `/dev` unit matrix per `transitive-drop-glue.md` §7 (capture/environment glue row) |
| TCO displacement predicate | cells #5/#8/#9, #19–#20, `adt_wrapped_supersede_leak_0720` greens | `/dev` unit cells for the §6 predicate table (transfer vs replacement polarity, borrowed-alias rejection) |
| Typed-context exits (run/REPL/link; scalar/heap/nested/`Pure`) | cells #15–#18 + `program_result_owner_s116::scalar_pure_result_exit_conversion_control_green` | `/dev`(int/exe-bundle) unit matrix per `result-owner.md` §6; no new e2e owed |
| Eliminator axis in the generative harness | MISSING (FIXME 0830) | §4.2 — W1 |
| Mixed-arm whole-match approximation tripwire | MISSING (FIXME 0726) | §4.2 — W1 |

**Armed acceptance legs (new, detectors-first dividend):** the Track-B fix
waves must additionally demonstrate their flips under armed detectors —
`/dev`'s acceptance run for each fix wave re-runs the flipped cells' programs
in child processes with M1+M2+M3 armed (subprocess-scoped, per §1) and shows
clean exits. This is the "every fix proven by a detector proven to detect"
sprint goal made operational. It is an acceptance-run obligation, not a new
committed-cell family (the committed cells stay unarmed/deterministic;
`ms_p8_conj_leak`'s armed leg is the committed pattern where one exists).

### 4.2 New W1 cells (0726 + 0830 ride Track B)

- **0726 tripwire** (mixed ctor+var match whose var-default arm forwards the
  scrutinee): {ctor-path selected, var-path selected} × {toggle-on,
  toggle-off}, asserting absolute `allocs == deallocs`, plus one `--link`
  face. The ctor-path cells are expected RED today (the whole-match
  suppression leaks the consumed temp); `transitive-drop-glue.md` §5's
  per-arm release plan flips them at W3. These graduate the parked
  approximation boundary from "no fence" to Track-B acceptance cells.
- **0830 eliminator axis**: two new `Position` rows in
  `tests/gen_ownership_flows.rs` — `matched_in_place`
  (`(match <mk> [pat …])`) and `let_bound_then_matched`
  (`(let [v <mk>] (match v …))`) — the minimum change that would have caught
  0810/0782. Instrument caveat is binding: the rows assert **exact balance**
  (never differential — the 0761 blindness) and either route through the
  `--link` face or carry an explicit note that they cover the 0810 leak
  polarity only (the 0782 double-free is `--link`-visible only).

### 4.3 Ruling-10 structural fence (atomic legacy-emitter deletion)

Track B item 1 closes the Principle-8 bridge: consumers migrate AND
`MAX_DROP_GLUE_DEPTH` + the inline recursive emitter delete **atomically in
the same wave**. `/testing` authors one structural fence cell in W1
(precedent: `tests/mode_gating_guard.rs`):

- grep-zero `MAX_DROP_GLUE_DEPTH` and `drop_glue_depth` in
  `crates/cranelisp-backend/src/`;
- the inline recursive drop-glue emission path in `rc_emission.rs` is absent
  (assert on its named seam, not a line number);
- RED today by construction; flips exactly at the W3 migration change-set. A
  wave that flips the behavior cells while this fence stays RED is the
  partial-migration state ruling 10 declares a `/review` REJECT.

### 4.4 Verified consequents (no separate patch permitted)

Cells #19–#21 (`conj` ×2, exemplar residue) are expected consequents of the
0810 + TCO-predicate migration. They are **verified, not patched**: if any
stays RED after the W3 wave, that is a NEW attribution question routed to
`/qa` — not a threshold adjustment (the exemplar bound stays at ≤1400), not a
per-seam patch, and not grounds to re-open the migrated seams without a
reduction.

## 5. Track C — load-dependent characterization and certification

### 5.1 Certification design

- **Deterministic:** two identical complete captured runs (§1 exit
  contract). Runs are `tee`'d — the S115 lost-output lesson is binding
  hygiene.
- **Loaded:** the corruption member (#24) reports separately. Closure
  requires: controlled reproduction under load; reduction to a mechanism
  (named violated invariant + owning seam); a permanent reduced repro; the
  fix; fail-on-revert evidence; the targeted loaded repetition the reduction
  prescribes; and **at least three consecutive captured complete runs green
  after the fix**. Symptom absence, M1 perturbation, or folding into a
  scalar is not closure. If capacity cuts the three-run loaded certification
  (third in the cut order), the characterization evidence is still required
  and the member carries with an explicit user-approved carry.

### 5.2 Characterization protocol (0694 — with proven detectors)

Executes the FIXME's D1→D2→D3 design, now with Track-A-proven instruments;
armed lanes are subprocess/lane-scoped per §1. **D1 gates D2/D3.**

1. **D1 — falsify the shared premise cheaply.** The member binary in
   isolation ~200× under equal non-cranelisp host CPU load. Reproduces →
   intra-subprocess fault, premise holds. Does not reproduce while the full
   suite does → inter-process shared state (cache dir, `CRANELISP_LIB`,
   tmpdir, cwd) — re-design before running D2/D3.
2. **D2 — per-class seam observation.** Class I (heap-invariant violation):
   re-run under M1+M2+M3 + `CRANELISP_RC_DEC_CHECK=1` (armed children), and
   again single-threaded (rayon=1, spark budget 0) under identical load —
   elimination names intra-subprocess concurrency; survival names a latent
   deterministic overrun (S98: absence under perturbation is not a fix).
   With detectors proven, an armed-lane firing is now evidence-grade: the
   faulting op names its seam. Class II (publication ordering — the nullary/
   multi-sig faces, if they resurface): under load with
   `CRANELISP_MODULE_TRACE=1` tee'd; a trace showing read-before-publication
   demonstrates the class and names `/dev`(src).
3. **D3 — anti-vacuity control.** Env-gated dev-only delay at the
   publication seam must reproduce the Class-II signature deterministically;
   the plant then becomes the standing regression guard. A mechanism that
   cannot be planted is not attributed.

Evidence closes 0694 only by demonstrated mechanism + fix + fail-on-revert +
the ≥3-green-run condition. If S118 produces characterization but no
mechanism fix, what returns to the user is the evidence record and a
scheduling decision — never a "flap" disposition (banned vocabulary).

### 5.3 0604 / 0818 discriminator

- **0604**: retirement is already mechanical on `/design`(int)'s census rows
  (check 1; code half done, check 2 discharged). `/qa` owes no new analysis;
  the plan records only that Track C's load work must not reopen it without
  a named-seam firing from the landed MODULE_TRACE.
- **0818 (mine, cheap-first)**: run the contamination experiment — seed a
  contaminated working directory (persisted `user.cl` touching
  `bit-and`/`num.bits`), run 0604's recipe; and its pristine control.
  Confirmation gives the three-sprint heisenbug a deterministic trigger and
  re-attributes it to session persistence re-entering the live table;
  falsification is recorded in the FIXME and removes the last plausible
  non-scheduling hypothesis. Either outcome is progress; both are recorded
  in 0818 before any further 0694-family scheduling.

## 6. Track D — forward-flow cells

### 6.1 0863 (DF-1/DF-2 + transaction negatives) — late wave, after 0745

Serialized after the W4 int wave (ruling 11: same `src/` publication/
result-owner seams; must not interleave). Cells:

- flips: #25/#26 (committed DF guards) through echo, `/info`, `/sig`, and
  bare lookup;
- new negatives (authored in the W6 window, expressible e2e through the
  public binary): induced preparation/backend failure mid-macro-turn leaves
  **no partial state** — no emitted symbol callable, no introspection row,
  no reserved GOT cell observable, next turn fully functional (the TX-family
  pattern from S117 reused for the prepared-transaction boundary);
- controls: ordinary direct `defmacro` unchanged; private emitted subjects
  not presented; zero/one/multiple public emitted subjects each present the
  right subject set;
- structural: no parallel presentation store (projection lives only in
  canonical introspection — `/review` checks against the rejected S117
  shape).

### 6.2 0867 — repro lands in W1

`polymorphic_product_mints_canonical_and_unique_bare_accessors`: the
polymorphic `(deftype (Pair a b) (MkPair [:a fst :b snd]))` case paired with
the existing concrete control
(`spec_field_accessor::bare_alias_resolves_when_field_unique`), asserting
both `Pair.fst` and bare `fst`; duplicate-field ambiguity family retained as
the negative boundary. After the RED lands, `/qa` finalizes the narrow `/dev`
attribution (registration/publication seam) — fix is capacity-dependent.

### 6.3 0868 — cache-hit lifecycle parity

Flip of #27. Acceptance beyond the flip: fresh/cache equivalence for public
AND private declared children; child resolution relative to the declaring
parent; parent-before-child readiness; idempotence under multiple dependency
edges. Owner unit test pins the cache-hit registration→child-enrollment
transition. Schema-free and ruling-free — survives a 0869 cut independently
(ruling 8).

### 6.4 0869 — CONDITIONAL (ruling 1)

The carrier **ruling** is the S118 deliverable regardless. Implementation
cells apply only if it ships:

- flip of #28; qualified and imported-bare variants both;
- schema 23→24 in its own window: stale-cache rejection cell (a pre-24
  sidecar invalidates cleanly rather than half-restoring);
- idempotent re-enrollment (multiple restore paths, one discovery shell);
- malformed/conflicting cached records rejected loudly (no silent row
  choice);
- owner units: writer-side metadata projection, restore-time enrollment,
  replay idempotence, rejection polarity.

If cut: #28 carries to S119 with the settled ruling as a user-approved carry
(pre-authorized first cut).

## 7. Track E — platform slice checks

- **0874 fixture consolidation — preservation check (the QA cell).** Sharing
  the raw heap-ADT fixture across the three integration crates must not
  weaken assertions: before/after inventory of test fns + assertions in the
  affected crates' tiers; zero assertion deletions/weakenings; schema
  isolation (per-crate schemas) demonstrably retained; sustained-repetition
  marshal guards untouched. `/review` executes against this checklist; `/qa`
  audits at Phase 6.
- **0870 (facade/ABI-v9 doc repair)**: documentation-only — acceptance is
  zero semantic API delta (`public-api.txt` byte-identical) + doc-accuracy
  review. No test cells.
- **0873 (marker-binding ergonomics design)**: design-only; any public
  `cranelisp-platform` surface contact returns to `/arch` (ruling 5). No
  test cells this sprint; the design's verification ideas are future rows,
  not present obligations (the S117 byte-backed-text precedent).

## 8. 0875 — attribution before fix (mine)

The exemplar standalone-`--link` failure (unresolved Rust symbols in the
platform archive) gets a **minimal repro before any fix dispatch**: smallest
program + platform-archive combination that fails the standalone link, with
the exact unresolved-symbol set captured and mapped to its defining crate
(exe-bundle force-link set vs platform staticlib build vs archive
production). Scheduling recommendation: the symbol-inventory attribution is
cheap and read-only — run it in the W5 window **after** the 0745 linked-
startup work lands (same link path; 0745's changes may shift or even cure
the symptom, so attributing before W4 wastes the reduction). Fix ships S118
only if the repro proves it trivially adjacent to the 0745 change-set;
otherwise S119 with the repro as the durable handoff.

## 9. Re-eligible instrumented-matrix FIXMEs — triage (mine)

| FIXME | Disposition | Rationale |
|---|---|---|
| 0726 | **RIDES Track B (W1 cells)** | The per-arm release plan is exactly what Track B implements; the tripwire cells become Track-B acceptance (§4.2). FIXME stays open until the cells land; disposition appended to the file. |
| 0830 | **RIDES Track B (W1 rows + PLAN rows now)** | The eliminator axis is the v1-vs-its-own-design gap that let 0810 ship; adding it while the fix lands makes the harness the standing fence (§4.2). PLAN rows for the 0810/0782 pin batch land in `PLAN.md` this phase. Stays open until the harness rows land. |
| 0831 | **ACTIONED NOW → delete** | The ask is a `/qa`-owned risk-register row (eliminator/consumer axis). Landed in `risks.md` S118 read as a standing register entry; FIXME deleted per protocol. |
| 0778 | **ACTIONED NOW → delete** | PLAN rows for the six 0772-family lane cells land in `PLAN.md`; the arm-order/order-symmetry twin obligation for join-shaped seams lands as a standing lens in `risks.md`. The `/dev` property cells (`join_lattice_*`) already exist. Nothing residual. |
| 0761 | **DEFER standing lane to S119; requirement rides now** | Every Track-B acceptance cell already asserts absolute `allocs == deallocs` (the committed REDs) and the new §4.2 rows are exact-balance by specification. Building the full owning-type × position exact-balance LANE while 21 cells are RED adds no discrimination and competes with W1's detection-proof capacity; it is the right S119 follow-on once the cells are green and can seed the lane. Deferral recorded in the FIXME. |
| 0779 | **DECIDED; residual deferred to S119** | `/qa` decision recorded: adopt candidate (1) — a seam-level polarity cell driving `resolve_auto_curry` over a seeded `pending_auto_curry` (the `join_lattice_*` template), `/dev`(typecheck)-owned, S119 (no typecheck wave exists in S118); the four recheck-scoped seams are recorded as "`Final` by construction, not by test" per the FIXME's own honest-disposition clause. Recorded in the FIXME; stays open as the S119 trigger. |

## 10. Close gate

1. Deterministic: two consecutive complete captured (`tee`'d) runs, identical
   failure sets, empty except user-approved carries (§1). Name-for-name
   reconciliation of §2.1 per §2.4.
2. Load-dependent member per §5.1 — or explicit carry with characterization
   evidence attached.
3. All eight detector rows have positive + clean + fail-on-revert evidence;
   0857 regrade landed into the amended (0768) vocabulary; no
   asserted-but-unproven grade survives.
4. Ruling-10 fence GREEN (legacy emitter + depth constant gone) in the same
   wave as the consumer flips; ruling-7 subtractive baseline landed; zero
   schema deltas outside the 0869 window.
5. 0859 dispositioned: closed with a committed witness, or returned to the
   user as disposition 2 — never silently carried.
6. No new ignores; every new cell carries `// spec:` (+ `// defect:` where a
   repro); `plan/spec_link_check.py` + `plan/spec_coverage_reconcile.py`
   clean over the changed set.
7. Track E preservation check clean (§7); 0875 repro produced before any fix
   dispatch (§8).

## Next skills

- `/testing` — W1: baseline reconciliation (§2.2), the §2.3 intended-RED
  additions (fence, 0726 cells, 0830 rows, 0867 repro), static arming-
  discipline gate (§1).
- `/design`(intrinsics) → `/dev`(intrinsics) — Track A per §3; the triplet
  revert records are `/qa`'s regrade input.
- `/design`/`/dev`(backend) — Track B per §4 + `transitive-drop-glue.md`;
  atomic deletion with the fence.
- `/design`/`/dev`(int, exe-bundle) — 0745 per `result-owner.md`; then 0863
  serialized after.
- `/arch` — 0869 carrier ruling; 0768 vocabulary amendment in the 0857
  regrade window.
- `/sprint` — sequence waves with the W1 static gate before Track A, and the
  armed-acceptance obligation (§4.1) in each fix wave's dispatch brief.
