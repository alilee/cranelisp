# Sprint 116 QA plan: zero-baseline-RED safety and conformance

**Status:** Phase 3 plan of record
**Authority:** `/qa`; `/testing` authors e2e sources; narrow `/dev` owners author unit tests
**Exit:** every named baseline cell below is green, and the load-dependent member has mechanism-level closure evidence

## 1. Risk verdict and certification split

This is a release-blocking safety sprint. Transitive discharge, ownership displacement, and typed-context exit are Blocker risk because a correct scalar result can coexist with leak, double-free, or allocator corruption. Constructor/default/annotation work is Important conformance risk because the failure modes are silent acceptance, wrong rejection, and divergent parser paths.

Certification has two independent verdicts:

1. **Deterministic:** one name-for-name run of the complete suite followed by a second identical run. All 28 deterministic baseline cells below must be green; zero unattributed REDs; no new ignore. Exact alloc/dealloc cells run serially and assert absolute parity, not merely ownership-toggle equivalence.
2. **Load-dependent:** `macro_clause_interior_alias_double_free_run` is reported separately. Closure requires the 0694 D1/D2/D3 discriminators, a permanent reduced repro, a named violated invariant and owner, fail-on-revert evidence, and at least three consecutive captured full-suite runs plus the targeted loaded repetition prescribed by the reduction. Symptom absence, M1 perturbation, or inclusion in a scalar is not closure.

Any newly discovered RED remains failing-not-ignored and blocks close unless the user explicitly adjusts scope.

## 2. Exact S115 baseline reconciliation (28 + 1 = 29)

The 28 deterministic cells are the five stable REDs at S115 close plus 23 S115 Phase-7 intended-RED pins accepted into S116. The separately observed load-dependent corruption member is the 29th certification failure.

### 2.1 Deterministic 28

| # | Test name | Group / acceptance |
|---:|---|---|
| 1 | `match_owned_temporary_scrutinee_0810::inline_call_wrapper_scrutinee_does_not_leak` | 0810; exact parity, both toggles |
| 2 | `match_owned_temporary_scrutinee_0810::inline_call_wrapper_scrutinee_does_not_leak_linked` | 0810; linked parity |
| 3 | `match_owned_temporary_scrutinee_0810::inline_constructor_scrutinee_does_not_leak` | 0810; in-place constructor |
| 4 | `match_owned_temporary_scrutinee_0810::inline_scrutinee_with_heap_payload_does_not_leak_box_or_field` | 0810; box and field discharge |
| 5 | `match_owned_temporary_scrutinee_0810::wrapper_from_call_superseding_loop_param_does_not_leak` | 0810; match + displacement composition |
| 6 | `match_owned_temporary_scrutinee_0810::let_bound_scrutinee_payload_outlives_the_match` | 0810; no premature release |
| 7 | `match_owned_temporary_scrutinee_0810::let_bound_scrutinee_payload_outlives_the_match_linked` | 0810; linked no-UAF |
| 8 | `match_owned_temporary_scrutinee_0810::let_bound_scrutinee_loop_result_still_matches_its_own_tag` | 0810; correct tag/lifetime |
| 9 | `match_owned_temporary_scrutinee_0810::let_bound_scrutinee_loop_result_still_matches_its_own_tag_linked` | 0810; linked tag/lifetime |
| 10 | `match_owned_temporary_scrutinee_0810::var_pattern_arm_consuming_owned_temporary_releases_it_once_linked` | 0810/0782; exact-once var eliminator |
| 11 | `capture_drop_glue_strands_nested_heap_0760::closure_capturing_vec_of_strings_does_not_leak` | 0760; nested container fields |
| 12 | `capture_drop_glue_strands_nested_heap_0760::closure_capturing_adt_with_string_field_does_not_leak` | 0760; ADT heap field |
| 13 | `capture_drop_glue_strands_nested_heap_0760::nested_adt_chain_past_glue_depth_limit_does_not_leak` | 0760; depth cliff removed |
| 14 | `adt_drop_glue_underkey::entry_main_ioresult_heap_payload_toggle_off_leak_r2` | 0688/0745; result owner, conservative toggle |
| 15 | `adt_wrapped_supersede_leak_0720::adt_wrapped_supersede_loop_does_not_leak` | 0688; ADT-wrapped TCO replacement |
| 16 | `adt_wrapped_supersede_leak_0720::adt_wrapped_supersede_residue_does_not_scale_with_n` | 0688; non-scaling exact parity |
| 17 | `annotation_fold_macro_arg_0708::annotation_folds_in_macro_argument_position` | 0708; structural fold |
| 18 | `deftype_duplicate_constructor::deftype_duplicate_nullary_constructor_rejected_neg` | duplicate constructor; second occurrence located |
| 19 | `deftype_duplicate_constructor::deftype_duplicate_enum_constructor_rejected_neg` | duplicate enum constructor |
| 20 | `deftype_duplicate_constructor::deftype_duplicate_fielded_constructor_rejected_neg` | duplicate fielded constructor |
| 21 | `deftype_constructor_form_rulings_s116::deftype_content_free_paren_constructor_rejected_neg` | content-free paren rejects |
| 22 | `deftype_constructor_form_rulings_s116::deftype_content_free_paren_among_bare_nullaries_rejected_neg` | mixed-arm mirror rejects |
| 23 | `deftype_constructor_form_rulings_s116::deftype_content_free_paren_in_polymorphic_type_rejected_neg` | polymorphic mirror rejects |
| 24 | `deftype_constructor_form_rulings_s116::deftype_nullary_constructor_sharing_type_name_rejected_neg` | forbidden nullary/type-name sharing |
| 25 | `deftype_constructor_form_rulings_s116::deftype_empty_field_list_arm_rejected_neg` | empty field-list arm rejects |
| 26 | `deftype_constructor_form_rulings_s116::deftype_empty_field_list_arm_name_differs_rejected_neg` | differently named empty arm rejects |
| 27 | `deftype_constructor_form_rulings_s116::deftype_documented_nullary_sharing_type_name_rejected_neg` | documented spelling obeys same rule |
| 28 | `deftype_constructor_form_rulings_s116::match_nullary_constructor_empty_parens_pattern_rejected_neg` | pattern mirror rejects |

### 2.2 Load-dependent 29th member

| Test name | Required closure evidence |
|---|---|
| `macro_expansion_interior_alias_double_free::macro_clause_interior_alias_double_free_run` | 0694 controlled-load reproduction/reduction; allocator/RC seam observation; permanent repro; mechanism fix; fail-on-revert; targeted loaded repetition; ≥3 captured full-suite runs. `_repl`, `_link`, M1-on, and M1-off siblings remain mode/perturbation controls, not substitutes. |

## 3. Transitive-discharge acceptance matrix

Every owning shape is tested at value depths **1, 2, 4, 5, and >5**. Depth 4 is the retired cutoff boundary; 5 and >5 prove no raised constant. Recursive definitions additionally construct finite runtime chains of 0, 1, and many nodes and must terminate compilation and release without compiler unrolling or runtime recursion failure.

| Axis | Required cells / oracle |
|---|---|
| Owning shape | Vec-of-scalars control; Vec-of-heap; ADT-with-heap-field; closure capture; closure-capturing-closure; ADT→Vec→ADT; recursive ADT. Absolute allocs = deallocs. |
| Publication/eliminator | lexical expiry; returned through 0/1/2 lets; closure capture; constructor-pattern match; var-pattern match; payload surviving match; compiler-synthesised capture. Exact-once release and value correctness. |
| Ownership displacement | TCO bare Vec; ADT-wrapped param; wrapper payload; same-binding carry-forward; cross-position in-place COW; toggle-off copy path. Superseded owner releases once; transferred owner never releases early. |
| Typed-context exit | JIT `--run`, REPL display, linked startup/exit conversion; scalar control, heap payload, nested heap payload, `Pure` result. Observe/convert first, then exact-once release through the same per-type glue identity. |
| Modes/toggles | Language-semantics representatives across REPL/`--run`/`--link`; all exact-balance ownership cases with analysis on/off; RC diagnostics on/off where perturbation could mask corruption. |
| Scale | N=1 and work-scaling N; residue must be zero, not merely constant. Sudoku warm-cache composition guard from 0840 must meet its numeric bound. |

`/testing` adds the missing depth and recursive-termination e2e cells before backend implementation. `/dev(backend)` adds unit matrices for glue identity/caching, recursive-definition compile termination, type-directed field traversal, displacement predicate polarity, and no fixed-depth fallback. `/dev(int/exe-bundle)` adds unit coverage for result-owner sequencing and exact-once selection at all three exits.

## 4. Track C: positive detection proof

All fault seams are inert in production and reachable only in test configuration. A positive proof must (a) plant one named fault through the production funnel, (b) assert the expected detector and failure mode, (c) retain a clean control, and (d) be demonstrated fail-on-revert. Passing without the detector is a failed test design.

| Detector | Plant | Required observation |
|---|---|---|
| M1 quarantine | free then exercise a planted stale access/double release through `alloc_with_rc`/`dealloc` | quarantine/assertion identifies the planted allocation; clean control passes |
| M2 scrub | free, scrub, then planted read through the production heap-access seam | poison is observed deterministically; disabling scrub makes the proof fail |
| M3 parity | leak one production allocation | counters disagree; atexit report occurs; subprocess aborts non-zero; clean subprocess exits normally |
| A1 zero RC | decrement a planted zero-RC allocation | `CRANELISP_RC_DEC_CHECK` rejects at the production decrement funnel |
| A2 non-allocation/interior pointer | decrement planted invalid/interior address | address/range validation rejects before mutation |
| A3 freed/quarantined pointer | decrement a planted released allocation | lifecycle validation rejects |
| A4 malformed header/size | corrupt the planted header invariant | header/size validation rejects |

M3 requires both intrinsics unit proof and one e2e counter→atexit→abort cell. M1/M2/A1–A4 require production-funnel unit proofs; add e2e only where the public diagnostic mode can express the plant without internal APIs. `tests/plan/s115-instrumentation-matrix.md` and `memory-safety-coverage.md` remain **asserted-but-unproven** until these cells and their revert demonstrations land; then `/qa` regrades R8/0857 by mode.

## 5. Syntax and carrier coverage

| Surface | Required acceptance |
|---|---|
| §7.1 method signature/default | typed signature; conforming default body; implementing-type occurrence in argument and return positions; deleted three-element spelling rejects; default-body annotation twin; re-impl/default dispatch cells 0826/0832/0833; run/REPL/link equivalence where executable. |
| Constructor arms | All 15 cells named by 0847 remain represented: bare/documented nullary, content-free paren, fielded, enum, product and zero-field product, positive and negative. Duplicate constructor and duplicate field errors locate the second occurrence. Pattern/value/definition mirrors agree. |
| Annotation fold | top-level, paren application, macro argument, nested expression, and qualified type; malformed/dangling annotation negatives; `Sexp::Annotated` round-trip and schema 22→23 stale-cache rejection; no macro-specific pairing path. |

The 15 constructor rows belong in `PLAN.md` and the §5.2 annotation band upgrades only after implementation and traceability audit. FIXME 0847 remains open until that durable update; Phase 3 records the required rows here so `/testing` is unblocked.

## 6. Narrow owner acceptance criteria

- **`/design` + `/dev(backend)`:** one named/per-concrete glue contract, finite compiler construction for recursive types, no `MAX_DROP_GLUE_DEPTH` fallback, all depth/0810/0760/TCO cells green, unit matrices above, absolute parity in both toggles and linked/run representatives.
- **`/design` + `/dev(int, exe-bundle)`:** one observe-then-release result protocol across REPL/run/link, using the backend glue identity; scalar/heap/nested payload cells and 0745 green; no JIT-only or IO-only releaser.
- **`/design` + `/dev(intrinsics)`:** inert injection seam; all M1/M2/M3/A1–A4 positive and clean controls; revert discrimination recorded; M3 e2e wiring green; raw heap reads converged; counter APIs removed with baseline; citation/count records corrected.
- **`/design` + `/dev(frontend/typecheck)`:** one §7.1 production and one constructor-registration rule; complete accept/reject occurrence and arm-spelling matrices; errors located at the offending trailing form or second duplicate.
- **`/design` + `/dev(types/frontend/int)`:** only `Sexp::Annotated`; coordinated schema-23 window and public baseline; corpus repair precedes reader flip; macro fold plus round-trip/stale-cache cells green.
- **`/testing`:** author missing matrix cells RED-first, preserve every defect repro, maintain `// spec:` and `// defect:` annotations, and provide the name-for-name close report.
- **`/review`:** reject shallow seam patches, fixed-depth recursion, private release mechanisms, differential-only parity, or detector tests that bypass production funnels.

## 7. Close gate

1. The 28 deterministic names in §2.1 are green in two consecutive complete captured runs with an identical failure set (which must contain none of these names).
2. The 29th member meets §2.2 independently; at least three consecutive captured complete runs are green after its mechanism fix.
3. Every remaining RED, if any, is newly discovered, attributed by name, and blocks close absent explicit user-approved carry.
4. M1/M2/M3/A1–A4 have positive, clean-control, and fail-on-revert evidence; R8 grades match evidence.
5. No new ignores; all new tests carry `// spec:` and PLAN rows; public API/schema changes have reviewed baselines.

## 8. Wave 1 static gate audit (2026-07-22)

**Verdict: PASS for static authoring; runtime verification remains required.**

- Mechanical reconciliation found all 28 deterministic baseline names and the
  separately listed 29th load-dependent name unchanged in source. New intended
  REDs are recorded separately and do not alter baseline arithmetic.
- Depths 1/2/4 are present in the shallow control; 5/>5 are present in the live
  cliff cell, both toggles; recursive 0/1/many is newly present. Typed run,
  link, and REPL exits, scalar control, trait/default matrices, duplicate-field
  polarity, structural annotation positives/negatives, and the exemplar
  composition bound are present.
- Every new Wave-1 test has a live `// spec:` citation. Intended REDs carry a
  `// defect:` class, locus, found sprint, and `/dev` owner. No new `#[ignore]`
  was added. Existing baseline names were neither renamed nor removed.
- FIXME 0798 (module alias as qualifier) and 0799 (autocurry free-type-variable
  matrix) are honestly deferred outside Tracks A--C and do not conceal a
  baseline S116 RED.
- The repaired `intrinsics_m3_detection_s116` child now satisfies the exact
  §7.1--§7.3 closed contract: fresh tempdir, `env_clear`, absolute compiler
  path, restored `CRANELISP_LIB` and `CRANELISP_PLATFORM_PATH`, `--no-cache`, a
  valid imported-`Pure` `IO` entry returning exit 0, exact arm
  `s116-detection-proof-v1`, and closed plant `M3Leak`. The positive requires
  abnormal status plus a plant-named alloc/dealloc parity report; the otherwise
  identical clean child requires success and absence of both plant and
  imbalance text. The polarity is statically discriminating.
- The restored 0741 guard is complete: its function name contains no frozen
  target numeral; extraction is bounded to the `SharedState` body; the public
  field count is asserted exactly at 17; and direct body-local absence checks
  exclude both retired fields, `module_sexps` and `suspend_states`.
- Tests were not executed: `cargo-nextest` is unavailable and dependency-index
  resolution is environment-blocked. This prevents runtime gate certification,
  but not the static matrix findings above.

Wave 1's static authoring gate is complete and implementation may proceed.
Runtime color remains a mandatory later gate and final certification cannot
use this static verdict as execution evidence.

## Next skills

- `/arch`, then `/review` — land and verify the Wave-2 shared carriers and the single schema-23 window.
- `/dev`(backend), then `/review` — implement and verify the common transitive-discharge foundation in Wave 3.
- `/design`(int/exe-bundle), then narrow `/dev` — specify and implement program-result ownership.
- `/design`(intrinsics), then `/dev`(intrinsics) — specify and implement production-funnel detector proofs.
- `/spec` — scribe the duplicate-field ruling and settled syntax; `/qa` then updates the durable annotation band.
- `/sprint` — sequence Phase 4 waves with Track A safety gates before dependent ownership work.
