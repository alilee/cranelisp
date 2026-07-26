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
| 10 | `ms_p8_conj_leak::int_loop_control_balances_green` | ambient prelude-load residue (§2.5) | W2b, branch H only (§2.5) |
| 11 | `capture_drop_glue_strands_nested_heap_0760::closure_capturing_vec_of_strings_does_not_leak` | 0760 | B (backend) |
| 12 | `capture_drop_glue_strands_nested_heap_0760::closure_capturing_adt_with_string_field_does_not_leak` | 0760/0796 | B (backend) |
| 13 | `capture_drop_glue_strands_nested_heap_0760::nested_adt_chain_past_glue_depth_limit_does_not_leak` | 0760 depth cliff | B (backend) |
| 14 | `transitive_drop_glue_s116::finite_recursive_values_zero_one_many_terminate_and_balance` | recursive-glue termination | B (backend) |
| 15 | `adt_drop_glue_underkey::entry_main_ioresult_heap_payload_toggle_off_leak_r2` | 0745 | B (int/exe-bundle) |
| 16 | `program_result_owner_s116::run_nested_pure_payload_observed_then_released_both_toggles` | 0745 | B (int/exe-bundle) |
| 17 | `program_result_owner_s116::linked_nested_pure_payload_converts_then_releases` | 0745 | B (int/exe-bundle) |
| 18 | `program_result_owner_s116::repl_nested_heap_value_displays_before_exact_release` | 0745 | B (int/exe-bundle) |
| 19 | `ms_p8_conj_leak::conj_loop_does_not_leak` | ambient prelude-load residue (§2.5); 0688 signature ABSENT at HEAD (§2.2.1) | W2b, branch H only (§2.5) |
| 20 | `ms_p8_conj_leak::conj_loop_parity_no_abort` | ambient prelude-load residue (§2.5); 0688 signature ABSENT at HEAD (§2.2.1) | W2b, branch H only (§2.5) |
| 21 | `exemplar_ownership_residue_s116::sudoku_warm_serial_solve_residue_at_most_1400` | 0840 composite + ambient term (§2.5) | W2b + B, verified consequent (§4.4, §2.5) |
| 22 | `intrinsics_m3_detection_s116::m3_parity_catches_injected_imbalance` | 0848 | A (intrinsics) |
| 23 | `intrinsics_m3_detection_s116::m3_parity_clean_child_exits_normally_control` | ambient prelude-load residue (§2.5) — NOT 0848, NOT 0745 (§2.2.2) | W2b, branch H only (§2.5) |
| 24 | `launch_grid_corrupt::launched_strand_grid_get_assoc_does_not_corrupt_heap_neg` | 0694 family (load-dependent) | C (separate certification, §5) |
| 25 | `spec_11_stdlib::def_definition_echo_names_user_binding_not_internal_thunk` | 0863 DF-1 | D (src) |
| 26 | `spec_11_stdlib::def_info_and_sig_describe_bound_value_not_macro` | 0863 DF-2 | D (src) |
| 27 | `cache::cache_restored_parent_enrols_private_test_child` | 0868 | D (src) |
| 28 | `cache::cache_restores_sibling_written_trait_impls_for_dispatch` | 0869 | D conditional (ruling 1) |

### 2.2 W1 reconciliation obligations — RESOLVED (W1 measurement 2026-07-25; `/qa` promotion 2026-07-25)

Both low-confidence cells are colored; the §2.1 table above is corrected
name-for-name and the arithmetic lands exactly on the verified 28
(150 run / 122 passed / 28 failed across the eleven baseline binaries).

1. **`ms_p8_conj_leak` is THREE members, not two** — all three cells RED,
   including the control twin `int_loop_control_balances_green`. The trade is
   NOT against #23 (also RED): it is against
   `match_owned_temporary_scrutinee_0810::var_pattern_arm_consuming_owned_temporary_releases_it_once_linked`
   (the former #10, defect 0782), **GREEN at HEAD with no fix landed** —
   dispositioned under the S98 rule in §2.6 below. Additionally the 0688
   TCO-supersede signature the `conj` cells were enumerated under is **absent
   at HEAD**: the conj loop's marginal residue over the int control is ZERO
   (1219−1198 = 21 allocs vs 76−55 = 21 deallocs over 20 iterations — no
   per-iteration term). All three REDs measure only the program-independent
   ambient prelude-load residue (§2.5). Whether 0688 was cured by an
   S116/S117 change-set or its cell shape stopped reaching the seam is an
   open suspicious-green question of the same S98 kind as §2.6; it is owed a
   trace-to-mechanism before the family is called closed (recorded as a §2.4
   exit-reconciliation obligation — the flip of #19/#20 does NOT retire
   0688's attribution question).
2. **The M3 clean control (#23) is NEITHER 0848-only nor 0745-coupled.** The
   detector is present and WORKING: the child aborts on a genuine exit
   imbalance of exactly 1143 (`ALLOC_COUNT=1199 DEALLOC_COUNT=56`), which is
   the ambient prelude-load residue (§2.5), not this child's `Int` result
   (0745's mechanism) and not a detection gap (0848's). No W2a
   detection-proof work and no W4 result-owner work can flip it.

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
  needs an explicit user-approved carry);
- the 0835 repros A + B (§4.5) — failing-not-ignored with **process-abort
  guards** (the failure is a SIGABRT; a bare value assertion takes the
  harness down). RED until the runtime-library fix (attribution ruled §4.5;
  the fix is NOT a Track-B backend flip).

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

### 2.5 Ambient prelude-load residue — ATTRIBUTION RULING (`/qa`, 2026-07-25)

**Ruling: the program-independent 1143-allocation residual that every
stdlib-prelude `--run` child carries is macro-expansion-execution residue on
the SList/Sexp marshal path — the same runtime-pair seam FIXME 0835 owns.
It is NOT compiler-side allocation in general, NOT definition/trait/impl
compilation, NOT `defmacro` compilation, and NOT 0745/0848/Track-B glue.**

The user's directed lead (2026-07-25: the only code that *executes* during
prelude load is macro expansion) is **confirmed** by discriminating probes
(fresh tempdir + `env_clear`-equivalent env per session, `--run --no-cache`,
`CRANELISP_RC_STATS=1`, trivial `Int`-returning child, debug binary at HEAD):

| probe | prelude contents | residual (`allocs − deallocs`) |
|---|---|---:|
| P0 | empty prelude | 0 |
| P1 | macro-free subset: 8 real stdlib modules verbatim (compare.eq/ord, num.num, text.display, fn.option/result, testing.assertions + 7 test children) — traits, impls, deftypes, defns, ADT re-exports | 0 |
| P2 | P1 + a module DEFINING one `defmacro`, never invoked | 0 |
| P3 | P2 + ONE macro invocation in a loaded module body | **+2** |
| P3b | two invocations of the same macro | **+4** |
| P3c | one invocation with a larger argument sexp | **+23** |
| P4 | full stdlib (`CRANELISP_LIB=stdlib/`) | **1143** |

The discrimination is total: compiling the entire macro-free surface leaks
nothing; compiling a macro definition leaks nothing; the first residual
appears with the first macro *expansion*, is **linear in expansion count**
(+2 per invocation) and **linear in the size of the marshalled sexp** (+2 →
+23 at constant invocation count). That is exactly 0835's confirmed
signature — per-call and per-|structure| growth at constant type depth — on
the same data path (`marshal` Sexp↔SList construction with undischargeable
interior +1s vs `consume_slist` tree-ownership teardown). The full-stdlib
1143 is the sum over the prelude closure's macro invocations
(`control`/`defs`/`str`/`vec`/`list`/threading/io.monad expansions).

**Disposition: no new FIXME.** The prelude-load face is appended to FIXME
0835 as a scope note (the probes indicate the 0835 mechanism; a second
number for the same seam would split the record). Probe harness retained at
the session scratchpad `probe/` tree; the P3 shape (two tiny modules, one
invocation, +2) is the minimal deterministic repro if a committed cell is
ever needed for a divergent attribution.

**Testable prediction (binding on W2b acceptance):** the W2b runtime-pair
fix for 0835's consume-owner contract collapses the ambient residual to 0.
W2b's acceptance MUST re-run the P4 probe shape (trivial `Int` child, full
stdlib, RC_STATS): residual 0 confirms; a surviving residual is a NEW
attribution routed to `/qa` (never a silent re-scope). `/testing` is
directed (W2b change-set rider, not W1) to land ONE prelude-face cell —
trivial program + macro-invoking mini-prelude fixture, exact balance — as
the standing fence for this face.

**Flip-accounting amendment (cells #10/#19/#20/#21/#23), both branches:**

- **Branch H — the 0835-collapse prediction HOLDS.** #10 (int control), #19,
  #20, #23 flip at **W2b** (their REDs are entirely the ambient term). #21
  (exemplar ≤1400) loses the 1143 ambient term at W2b and its remaining 0840
  composite residue is verified as a consequent of W3 per §4.4 — flip
  expected only after **W2b + W3**, and a residual RED after both is a NEW
  attribution. None of these five flips at W2a, W3-alone (for
  #10/#19/#20/#23), or W4 — a flip in any other change-set is the S98
  perturbation flag, and re-opens attribution.
- **Branch F — the prediction FAILS (residual survives W2b).** The prelude
  face is a distinct defect no current track owns: #10/#19/#20/#21/#23
  **cannot flip from any currently-scoped track** and the sprint owes the
  user a scope decision (new fix window vs explicit user-approved carries —
  they are NOT in the §1 pre-authorized carry list). The surviving-residual
  measurement itself becomes the new FIXME's evidence base, and the P3 probe
  shape is the reduction `/testing` commits with it.

**Branch F EXECUTED — attribution complete (`/qa` probe, 2026-07-26, HEAD
`34aac8ff` post-W2b; user-directed "probe only, then decide").** The W2b
P-ladder was byte-identical pre/post (P3 +2, P3b +4, P3c +23, P4 1143 —
reproduced), so Branch F fired. Discriminating probes WITHIN the
macro-expansion turn attribute the whole residual to the **int-side
macro-turn marshal boundary** — `src/marshal.rs` (args leaked by design +
FIXME-0638 deep protection) and `src/expander.rs::invoke_clause` (the
expansion-result tree never consumed after `runtime_to_sexp`) — NOT the
`quote_sexp`/`quote_slist` path and NOT the 0835/RE runtime-pair class:

| discriminator | shape | predicted (leak-boundary model) | measured |
|---|---|---:|---:|
| (d) no quote forms, nullary | body `(SexpInt 2)` | +1 (result cell) | **+1** |
| (d)+(b) no quote forms, list result | ctor-built 8-cell tree | +8 | **+8** |
| (a) quote-built IDENTICAL result | `` `(add-i64 1 2) `` | +8 (quote path balanced) | **+8** |
| (c) two invocations | P3b | +4 | **+4** |
| arg-size axis | P3c | +23 (22 arg cells + 1 spine; result aliases arg) | **+23** |

Armed `CRANELISP_ALLOC_PARITY=1` fingerprints: P3 survivors are exactly the
args-spine `SCons` (size=40 tag 0x1) + marshalled `SexpInt` (size=32 tag
0x0); the nullary shape's lone survivor is the JIT-built result cell;
full-stdlib `delta=1143` with all 64 dumped samples Sexp-family cells (26
SCons / 11 SexpList / 7 SexpSym / 5 SexpInt / 3 SexpStr / 2 SexpBool / 2
SexpBracket / 1 SexpAnnotated / 7 HeapStrings). Record + fix-shape
estimates (instrument-truthfulness = hours vs macro-turn ownership protocol
= a wave, `/design`(int) first): **FIXME 0888** (`target: /sprint` — the
fix-vs-carry decision is the user's). Cells #10/#19/#20/#23 measure ONLY
this leak; #21 carries it as its ambient term. The residue is a documented
compile-time leak (bounded per session), not a runtime RC violation —
P1/P2 = 0 stands; its cost is instrument poisoning of every
stdlib-prelude exact-balance cell.

### 2.6 Cell trade-out — the 0782 linked cell's suspicious green (S98 rule, executed 2026-07-25)

`match_owned_temporary_scrutinee_0810::var_pattern_arm_consuming_owned_temporary_releases_it_once_linked`
left the 28 (GREEN at HEAD) with **no fix landed**. Per §2.4 that is
suspicion, not closure. The S98 step is executed: the original defect
signature is **reproduced another way, at the IR level** — `/clif f` over
0782's exact repro (`(defn f [] (match [7 8 9] [xs (vec-get xs 1)]))`,
empty prelude, HEAD debug binary) shows the double release verbatim:

```
block5:  v24 = iadd_imm.i64 v4, 8
         v26 = atomic_rmw.i64 sub v24, v25   ; arm-exit scope cleanup
         brif v27, block8, …                 ; → fn2(v4) conditional free
block2:  v33 = iadd_imm.i64 v4, 8
         v35 = atomic_rmw.i64 sub v33, v34   ; merge-block consume dec
         brif v36, block10, …                ; → fn4(v4) conditional free
```

Both subs target the SAME scrutinee `v4` (RC field +8) — exactly 0782's
mechanism (`compile_var_pattern_arm` scope registration +
`dec_temporary_scrutinee` both firing), unfalsified by the FIXME's own
falsifiability clause. **Disposition: the defect is LIVE and deterministic
in the emitted IR; only the e2e symptom (the `--link` allocator abort) is
layout-latent at HEAD.** The cell:

- does NOT join the 0694 load/interleaving family — nothing here is
  interleaving-dependent; the mechanism is byte-visible in every compile;
- stays attributed to 0782, stays in the suite as the regression guard, and
  is OUT of the 28 as measured (baseline honesty);
- exit reconciliation (§2.4) must NOT count its green as 0782 closure: 0782
  closes only when its fix change-set lands (Track B match_codegen seam) and
  the acceptance evidence shows ONE release in this CLIF shape (the `/clif`
  probe above is the check; `/dev`'s unit tier pins the count at the seam).
  A tightened e2e cell (CLIF-trace-asserting sibling) is `/testing`'s option
  in the fixing change-set, not a W1 obligation.

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

Two sequencing/shape notes from the refreshed design
(`diagnostic-modes.md` §7.5–§7.7): the **§7.5 precheck hoist gates the
triplets** — as built, gated seam checks run after their mutation (and after
always-on `debug_assert!` twins), so a positive proof attempted before the
hoist lands fails against a *working* detector; such a failure is a
sequencing artifact, not detector evidence, and the hoist's own revert is
itself a detected regression (design §7.7 row 2). And the §7.6 harness shape
— plant children as ordinary non-ignored tests that no-op unarmed — makes
byte-inertness continuously executed and is compliant with §1's arming
discipline (arming happens only inside the child `Command` construction).

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
| Capture/curry teardown | cells #11–#12 + green capture controls | `/dev` unit matrix per `transitive-drop-glue.md` §7 (capture/environment glue row); **W3: 0796 exclusion removal** — `/testing` removes the `curried_partial_application` entry from `tests/gen_ownership_flows.rs::balance_exclusion` IN the S4 flipping change-set, and the harness must then run clean over that position for every owning type under both toggles. The removal IS the 0796 acceptance (`transitive-drop-glue.md` §7.4): a fix that flips #11–#13 while the exclusion stays is incomplete |
| TCO displacement predicate | cells #5/#8/#9, #19–#20, `adt_wrapped_supersede_leak_0720` greens | `/dev` unit cells for the §6 predicate table (transfer vs replacement polarity, borrowed-alias rejection) |
| Typed-context exits (run/REPL/link; scalar/heap/nested/`Pure`) | cells #15–#18 + `program_result_owner_s116::scalar_pure_result_exit_conversion_control_green` | `/dev`(int/exe-bundle) unit matrix per `result-owner.md` §6 **including the §5 error-path negative rows** (`/qa` verifies at Phase 6, with the §9.2 armed legs); no new e2e owed. **Flip rider (`result-owner.md` §9.1):** cell #15's `// defect:` line still reads `locus=…rc_emission.rs::protect_return_value` (`tests/adt_drop_glue_underkey.rs:258`) — both mechanisms at that locus are falsified; `/testing` re-locuses it onto the int result-value lifetime seam IN the flipping change-set (I3), or the `locus=` hotspot analysis keeps mis-attributing this defect to backend |
| Eliminator axis in the generative harness | MISSING (FIXME 0830) | §4.2 — W1 |
| Mixed-arm whole-match approximation tripwire | MISSING (FIXME 0726) | §4.2 — W1 |

**Behaviour-neutral slice invariance (S0/S1):** the §3.2 invariance pin
extends to backend slices S0 (registry reshape) and S1 (glue-call emitter
swap), which are behaviour-neutral by design (`transitive-drop-glue.md`
§7.0–§7.1, §9): every baseline RED stays byte-identically RED through them —
a RED that flips during S0/S1 re-opens attribution rather than counting as a
win — and the 0753 controls (`moded_arg_rc_tests`) stay green at S1.

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

  **W1 OUTCOME (2026-07-25) — the two planned rows are INSUFFICIENT; the
  landed third row is the operative one.** Measured at HEAD `e15ff20f`, both
  proposed rows balance exactly for every owning type including the ADT
  ctor-pattern arm — 0830's "minimum that would have caught 0810" claim is
  falsified. The discriminating ingredient is not "a match over an owned
  temporary": it is the match **as a tail-recursive loop body**, where the
  missing release is at the tail jump and the loop and the match must share
  a frame. The two proposed rows put `cell` in its own frame under the
  repeater, so the seam is never reached — the same shape of miss 0830 itself
  diagnosed in v1 (a borrowing reader), one level in. `/testing` landed all
  THREE rows (`matched_in_tail_loop` added; position axis 9 → 12);
  `matched_in_tail_loop` is RED for `adt_with_heap_field` (7/3), GREEN for
  var-pattern types — the expected 0810-Face-A split. Named residual: 0810
  Face B (payload outlives the match as the loop parameter) needs a wrapper
  ADT the generator lacks; pinned cell-by-cell in
  `match_owned_temporary_scrutinee_0810.rs`, v2 widening here. FIXME 0830 is
  actioned and deleted with this record (the tail-loop lesson also lands in
  the `risks.md` standing eliminator-axis entry: an eliminator row that does
  not share the loop frame does not test the tail-jump seam).

### 4.3 Ruling-10 structural fence (atomic legacy-emitter deletion)

Track B item 1 closes the Principle-8 bridge: consumers migrate AND
`MAX_DROP_GLUE_DEPTH` + the inline recursive emitter delete **atomically in
the same wave**. `/testing` authors one structural fence cell in W1
(precedent: `tests/mode_gating_guard.rs`):

- grep-zero `MAX_DROP_GLUE_DEPTH` and `drop_glue_depth` in
  `crates/cranelisp-backend/src/`;
- the inline recursive drop-glue emission path in `rc_emission.rs` is absent
  (assert on its named seam, not a line number);
- **grep-zero the second glue-identity home** (FIXME 0878 — resolved by this
  extension; aligns the structural fence with `transitive-drop-glue.md` §8's
  deletion enumeration): `build_adt_drop_glue_fn`, `build_elem_dec_fn`, and
  `adt_drop_glue_name` in `crates/cranelisp-backend/src/`. Without this the
  fence would pass while `vec_codegen` still mints named per-instantiation
  ADT glue under the backend-local `adt_instantiation_mangle` key — two
  type-directed glue mechanisms and two identity schemes alive, the exact
  state ruling 10 exists to prevent. (`adt_instantiation_mangle` itself is
  expected to delete with the pair — verified at HEAD `4c1aa80b` to have no
  non-glue production consumer, only `adt_drop_glue_name` and
  `build_elem_dec_fn` reach it — but it stays OUT of the grep-zero cell
  because §8 conditions its deletion on that check holding at migration
  time; a surviving consumer-less mangle is a `/review` dead-code catch, not
  a fence FAIL.);
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

### 4.5 0835 attribution ruling (FIXME 0877 — RULED 2026-07-25, /qa)

**Ruling: 0835's mechanism is runtime-library-owned (the S116 ruling-2
inventory's second row — known runtime protocol trees → their intrinsics
`consume_*` owner), not backend. Track-B slice S2 is removed from the backend
wave; the backend migration proceeds S0 → S1 → S3 → S4 → S5 → S6 without
waiting. Arch ruling 1(d)'s "0835 first" ordered the transitive-discharge
class, which 0835 does not join.**

Evidence (probe run 2026-07-25, HEAD `4c1aa80b`, debug binary, fresh tempdir
per session, `CRANELISP_RC_STATS=1`, 0835 repro B shape):

| sconcat calls | `\|ys\|` | residual (`allocs - deallocs`) delta vs control |
|---:|---:|---:|
| 0 (control) | — | 0 |
| 1 | 2 | +3 |
| 2 | 2 | +7 (+4 for the second call) |
| 1 | 4 | +6 |

The residual grows with each `sconcat` call and doubles when `|ys|` doubles,
at **constant** type nesting depth (`SList<Sexp>` in every session) — the
recipe's confirmation arm. The transitive-discharge hypothesis (residual
proportional to type depth, or vanishing when backend consumers migrate) is
falsified: backend emission contributes only the unchanged call-site
consuming-arg protocol here. Code seams: `marshal::deep_rc_inc_slist`
(`crates/cranelisp-primitives/src/marshal.rs:160-171`, called by `sconcat`
at `:195-217`) adds +1 to every interior `SCons` node and every element —
references no structural owner corresponds to — while
`consume_slist` (`crates/cranelisp-intrinsics/src/drop.rs:134-155`)
correctly implements tree-ownership drop glue (dec the head; descend only on
last ref), so the interior +1s are undischargeable: a per-call leak
proportional to `|ys|`.

Dispositions:

1. **W1 (`/testing`):** land 0835 repros A + B as failing-not-ignored cells
   with process-abort guards (§2.3). This also satisfies FIXME 0765's
   no-fix-without-repro precondition for the runtime fix.
2. **Fix routing:** `/design`(intrinsics) rules the consume-owner contract
   first — whether embedding a list as a shared tail takes a head-only inc
   (making `deep_rc_inc_slist`'s deep walk the defect, fix in primitives
   `marshal.rs`) or `consume_*` becomes deep (wrong for genuinely shared
   tails) — then `/dev` on the runtime pair. `/sprint` slots this in the
   intrinsics/runtime windows; it does not gate, and is not gated by, the
   backend W3 wave.
3. **Honesty caveat:** the probe confirms the LEAK face; 0835's abort face
   (glibc corruption at ~6 cells) is characterized by the committed repro's
   reduction. No backend mechanism is implicated at this seam; if the abort
   face survives the runtime fix, that is a NEW attribution question routed
   to `/qa` (§4.4 discipline), never a silent re-opening of the migrated
   backend seams.
4. FIXME 0877 is fully disposed and deleted; FIXME 0835 stays open,
   retargeted to `/design`(intrinsics) with this ruling appended.

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

### 6.2 0867 — repro landed W1; ATTRIBUTION FINALIZED (`/qa`, 2026-07-25)

The W1 reduction (`tests/spec_field_accessor.rs` §"THE CONSTRUCTOR-ARM
AXIS") falsified 0867's polymorphism framing: two polymorphic forms mint
both accessors, and a CONCRETE distinct-name constructor arm mints neither.
**The axis is where the field list lives**: accessors are synthesised only
from the deftype-LEVEL field list (and the same-name single-constructor
spelling that reduces to it); a field list in a named constructor arm whose
name differs from the type's contributes NO accessor — every sum type,
every distinct-name product.

**Finalized attribution — `/dev`(typecheck), single-crate.** The seam is
`crates/cranelisp-typecheck/src/adt.rs`: `synthesise_field_accessors` is
called only under `if is_product` and only over `ctor_infos[0]`, with an
explicit (wrong) comment "Sum/enum fields have no total accessor". Spec
§5.2.6 is already normative against it — it REQUIRES sum-type accessors and
specifies their semantics ("**Sum type accessors** are partial — they
succeed on the matching variant and panic on mismatched variants", with
`Option.unwrap` worked). No `/spec` question is open: the fix synthesises
accessors over EVERY constructor arm's field list (partial semantics for
multi-arm types per §5.2.6), preserving the §8.6.5 bare-alias contest
classification unchanged — the retained duplicate-field negative family is
the boundary fence. The panic face of a partial accessor needs its own
positive + negative cells when the fix lands (`(Option.unwrap None)` →
runtime panic — currently untestable, nothing mints).

**`class=` re-label ruling: `class=enumeration-miss` STANDS.** The
controlled-vocabulary definition ("a reachable-set enumeration omits …a
symbol source") fits exactly: the accessor-source enumeration omits the
constructor-arm field lists. No vocabulary addition; no test edit needed.
Invisibility cause confirmed as the coverage-by-definition-variants lens
(every prior guard spelled the ONE variant that works); the landed matrix is
the variant × polarity grid that lens requires. Fix remains
capacity-dependent (not in the pre-authorized carry list — an unfixed 0867
at close needs an explicit user-approved carry). FIXME 0867 is retargeted
`/testing` → `/dev` (typecheck) with this attribution appended.

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
4. Ruling-10 fence GREEN (legacy emitter + depth constant + the second
   glue-identity home — §4.3 extended cell — all gone) in the same wave as
   the consumer flips; the 0796 balance-exclusion removal landed with S4
   (§4.1); cell #15's `// defect:` re-locus landed with its flip (§4.1);
   ruling-7 subtractive baseline landed; zero schema deltas outside the
   0869 window.
5. 0859 dispositioned: closed with a committed witness, or returned to the
   user as disposition 2 — never silently carried.
6. No new ignores; every new cell carries `// spec:` (+ `// defect:` where a
   repro); `plan/spec_link_check.py` + `plan/spec_coverage_reconcile.py`
   clean over the changed set.
7. Track E preservation check clean (§7); 0875 repro produced before any fix
   dispatch (§8).

## 11. Pre-gate pass (`/qa`, 2026-07-26, HEAD `49a20269`) — attribution + exit reconciliation

Evidence: one focused run over all eleven baseline binaries + every §2.3
intended-RED binary + the Bind-family binaries + both golden lanes
(1,059 tests: 1,042 passed / 17 failed; log tee'd to the session scratchpad),
plus `cargo nextest run -p cranelisp-backend` (**527/527**) and the
`spec_*`-corpus count (**8 failed** = Bind ×3 + 0863 ×2 + 0867 ×3), which
together discharge the waived standalone review's evidence claim for
`5a906eca` (0904/0905 resolution).

### 11.1 The Bind family — ATTRIBUTED (FIXME 0907, `/design` backend)

`constructor 'Bind' disagrees on declared parameter identity for
'primitives/IO'` is **7 cells, not ~9**: `spec_10_io` ×3
(`io_internal_ctors_stay_excluded_from_exhaustiveness_neg`,
`match_arms_all_io_pure`, `pure_pattern_accepted`), `ctor_as_value` ×2,
`examples` ×1 (programs 21-hello-io + 23-io-sequence), `stdlib_conformance`
×1 (`core.io/when-io`, taking `core` + `core.io` down). The W4-review guess
that `spec_11_stdlib` ×2 belong to this family is **falsified by signature**:
both fail on their own 0863 DF-1/DF-2 mechanisms (the `n-def` thunk leak is
verbatim in their output), not on Bind.

Minimal repro (one line, PrimitivesOnly):
`(match (Pure 5) [(Pure x) x (Effect e) 0])`. Mechanism: every release of a
concrete `IO T` routes through `DropGlueRegistry::ctor_shapes`, whose
shared-substitution identity precondition is structurally unsatisfiable for
IO — the seeded `Bind` ctor (`src/bootstrap.rs:767`) deliberately mints fresh
existential vars; and even per-ctor substitution leaves `Var(b)` free in
Bind's field types, so per-concrete IO glue cannot be derived from ctor
shapes at all. **W3-surfaced** (registry had zero consumers before W3;
proven not-W4's by stash/pop), so these 7 are NOT in the sprint-open 28 —
they are W3's newly-visible face of a pre-existing modelling gap (the legacy
emitter silently shallow-released the same values). **Connection to the 0903
census confirmed**: third face of the same class (signature/existential
types not determined by the release key), loud where 0903's two families are
silent; the S119 0903 ruling should co-rule it. Runtime already owns dynamic
IO teardown (`free_io_branches`) — the natural ruling direction is recorded
in 0907.

### 11.2 The two 0903 leak families — DECISION: plan rows now, guards at S119 W1

The censused families (synthetic accessors of generic/undeclared-field
products; generic trait-method instances — both shallow-release and leak
today, pre-existing) get **PLAN rows now** (landed, `PLAN.md` §S118 track
rows) and **failing-not-ignored marginal-balance guards authored by
`/testing` at S119 W1**, QA-first, BEFORE the 0903 ruling's implementing
wave. Not now, because: (1) the W8 gate's name-for-name accounting is
already fixed — injecting new intended REDs mid-gate churns the exact
arithmetic the gate exists to verify, for zero added detection (no fix can
land before the S119 ruling); (2) FIXME 0765's no-fix-without-repro
precondition is satisfied so long as the repros precede the fix dispatch —
S119 W1 does; (3) the leak polarity needs the marginal harness (subject vs
control differing in exactly the accessor call / trait-instance invocation),
which is the S119-W1-shaped authoring the harness was built for. Interim
visibility is not zero: cell #21 already carries the class at application
scale (§11.3), and the 0903 file + `emit_heap_binding_decs` rustdoc census
are the durable record.

### 11.3 Cell #21 / FIXME 0890 — marginal re-derivation EXECUTED; 0890 disposed

Probe (HEAD `49a20269`, exemplar tree copied per the cell, same env, cold
then warm; controls: trivial `(Pure 0)` main, same prelude/env, warmed the
same way; second control adds `(import [solver [solve]])` so the exemplar
modules' own compilation is present):

| child | cold residual | warm residual |
|---|---:|---:|
| control (trivial main) | 1143 | **0** (allocs=1/deallocs=1) |
| control (same-imports) | 1143 | **0** |
| subject (warm serial solve) | 13,574 | **12,431** |

Findings, and they invert 0890's premise:

1. **A successful warm cache-hit run carries NO ambient 0889 term** — the
   macro-turn leak is compile-time only and cache-hit skips expansion; two
   independent warm controls measure exactly 0. (The Branch-F 1143 appears
   in COLD/`--no-cache` children only; 0890's "~87% ambient" read the cold
   arithmetic into the warm cell.)
2. So the warm cell's 12,431 is **pure runtime retention** — the absolute
   and marginal measurements coincide for this cell; the threshold's meaning
   is NOT corrupted by 0889, and fixing 0889 will not move this cell.
3. The §4.4 verified-consequent prediction failed honestly: ~12.4k blocks of
   genuine solve-work retention survive W2b+W3. **New attribution lead
   (recorded, not ruled): the 0903 families are live on the solve path** —
   `grid/Grid.cells` is a synthetic accessor of a GENERIC product
   (`Grid$(Vec Cell)` instantiations visible in RC_SITE_STATS), and the
   backtracking solver calls accessors per cell per pass; generic instances
   over `SolveResult$Grid$…` are likewise live. The cell's residue is
   plausibly 0903-dominated and is expected to move only when the S119 0903
   ruling lands.

**Dispositions:** FIXME 0890 actioned and deleted (this section is the
record). Cell #21 keeps its threshold FORM and its ≤1400 bound unchanged (a
composite application guard measuring a real class; loosening it would
absorb the leak, converting it to exact-balance is unreal until 0903
closes). `/testing` owes two riders in an ordinary change-set (no urgency,
may ride the golden rebaseline): (a) re-point the cell's `// defect:` line
from the completed 0810/0840 attribution to the 0903 families + this
section; (b) add a warm-control guard leg (same-env trivial main, warmed
identically, asserting residual exactly 0) so the "warm ⇒ ambient-free"
premise that makes the absolute bound meaningful is continuously executed —
the marginal-harness principle adapted to the cold/warm axis 0890 flagged.

### 11.4 Golden CLIF lanes — pure expected drift; rebaseline ROUTED (FIXME 0908)

Two RED cells: `clif_golden_lane::clif_golden_lane_no_drift` (**11 frames**:
01,02,03,04,05,07,08,f1,f2,f3,f4) and
`golden_clif_w0b::golden_clif_w0b_synth_accessor`. Verified drift shape in
every inspected hunk: inline guarded-dec sequences (rmw/icmp/brif/fence +
dealloc or embedded-ptr call, inline 1024 nullary guards) replaced by ONE
colocated canonical-glue call with void signature — the W3 §8 reshape and
nothing else; renumbering deltas are consequences. Behaviour corroboration:
backend 527/527, consumer guards green, armed legs balanced, three-round W3
review PASS. `/testing` re-captures BOTH lanes scoped + attributed citing
`2df95c41..966d298e` (never blind), **before the W8 full-suite run**.

### 11.5 Result-owner error-path negatives — COVERAGE CONFIRMED

The §5/§6 rows the design owes are landed and discriminating
(`src/result_owner.rs` unit tier + `src/pipeline.rs` + `src/exe.rs`):

- **All four fresh-JIT polarities**: `fresh_jit_absent_key_is_a_hard_error_naming_the_expected_symbol`,
  `fresh_jit_missing_address_is_a_hard_error`,
  `fresh_jit_zero_address_is_a_hard_error` (the new null-address row — and it
  discriminates the adapter's located error, not the `debug_assert`, per the
  §6 requirement; verified again by the W4 closing review),
  `fresh_jit_symbol_key_mismatch_names_both_spellings`; plus
  `armed_owner_survives_a_pair_atomic_row_replacement`.
- **Error outcomes release nothing**:
  `resolver_failure_propagates_and_releases_nothing`;
  `drop_backstop_releases_once_and_never_doubles` +
  `observation_completes_before_the_single_glue_call` (exact-once);
  `io_type_is_rejected_and_never_selects_io_glue`;
  `non_concrete_type_is_a_hard_error_naming_module_and_type`;
  `startup_non_concrete_inner_type_is_a_located_link_error` +
  `scalar_result_startup_stub_omits_the_release_call_entirely` +
  `exit_conversion_and_release_are_independent_axes` (link arm). The
  trap/dispatch-fault row is tier-1 unconstructable (an owner exists only on
  the clean arms; `program_outcome_to_result_runtime_error_*` +
  `…_dispatch_fault_is_err` pin the arms' classification) — accepted.
- **Honest residuals** (recorded, not gaps in the owed set): the cache-hit
  adapter's miss/null rejections are code-present with located diagnostics
  but have no constructed-`Linker` unit row, and the adapter itself is
  production-unreached (W4 as-built note; `/design`(int) call recorded W4+).

### 11.6 Exit reconciliation — name-for-name (input to W8/Phase 7)

**The 28-name baseline: 22 GREEN / 6 RED, verified in this pass, exactly as
committed.** Flip attribution: #22 → W2a; #10/#19/#20/#23 → W2b+ (marginal
instrument, real measurements); #1–#9, #11–#14 → W3 (S3/S4 slices; S0/S1
invariance held); #15–#18 → W4 (I3/I4/I5). The 6 remaining, all explicit
carries: **#21** (re-attributed §11.3, S119/0903), **#24** (0694, Track C →
S119), **#25/#26** (0863, Track D → S119; still failing on their OWN
mechanisms — §11.1), **#27** (0868, S119), **#28** (0869 implementation
deferred, carrier ruling in force). §2.2.1's 0688 trace-to-mechanism
question stays open (absence proven, cure-vs-unreached unruled) and carries
with the 0688 attribution question to S119; §2.6's 0782 stays "mechanism
live in CLIF, cell green-by-latency" — closes only with fix + one-release
IR evidence.

**Intended-RED additions (§2.3), disposition:** arming gate, ruling-10 fence
(extended), 0726 tripwires, 0830 rows (incl. `matched_in_tail_loop`), 0835
repros A+B, 0889 exact-value pins, marginal-harness capability fence — **all
GREEN** (flipped by their named waves; fence flipped atomically with W3's
twelve-symbol deletion). Still RED: **0867 repro ×3**
(`spec_field_accessor`) — not in the pre-authorized carry list; needs an
explicit user-approved carry at close (fix retargeted `/dev`(typecheck),
S119).

**REDs at HEAD outside both sets** (all attributed this pass): Bind family
×7 (§11.1, FIXME 0907, W3-surfaced) and golden lanes ×2 (§11.4, FIXME 0908,
rebaseline owed). **Expected W8 full-suite failure set: 18 named cells** = 6
carries + 3 (0867) + 7 (Bind) + 2 (golden; 0 if the rebaseline lands
first). Any other RED in W8's run is a genuine regression. (This pass's
universe covered the eleven baseline binaries + §2.3 binaries + Bind/golden
binaries; the W2/W3 fence binaries and the wider corpus ride W8's full run.)

**S118 FIXME ledger at the gate.** Filed-and-resolved this sprint: 0876,
0877, 0878, 0879, 0880, 0881, 0882, 0883, 0884, 0885, 0886, 0887, 0888,
0892, 0893, 0894, 0895, 0896, 0897, 0899, 0901, 0904, 0905, plus 0890 +
0726 actioned/deleted in this pass. **Open S118-filed set going into close:**
0889 (S119, user-required recovery), 0891 (deferred S119 on 0903), 0898
(`/arch`), 0900 (`/testing`, locus-form suggestion), 0902 (`/arch`), 0903
(`/design` backend, S119 ruling), 0906 (backend nit), 0907 + 0908 (this
pass). Pre-S118 carries with recorded S118 dispositions: 0761/0779 (S119
triggers), 0694/0604/0818 (Track C → S119), 0863/0867/0868/0869 (Track D →
S119), 0870/0871/0872/0874/0875 (Track E / S119). **0835 is a candidate
close for its owner**: all committed repros (A, B1–B3) are GREEN after
W2b+W3 and the prelude face is carved off as 0889 — `/design`(intrinsics)
confirms and deletes.

## Next skills

- `/testing` — W1: baseline reconciliation (§2.2), the §2.3 intended-RED
  additions (extended fence, 0726 cells, 0830 rows, 0867 repro, 0835
  repros A+B with process-abort guards), static arming-discipline gate
  (§1); later, riding their flipping change-sets: the 0796
  balance-exclusion removal (§4.1) and the cell-#15 `// defect:` re-locus
  (§4.1).
- `/design`(intrinsics) → `/dev`(runtime pair) — 0835 per the §4.5 ruling:
  consume-owner contract first, fix after the W1 repros land; decoupled
  from the backend W3 wave.
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
