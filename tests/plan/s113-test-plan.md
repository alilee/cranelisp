# Sprint 113 — sprint-wide test plan (Phase-3, 2026-07-19, /qa)

Companion to `s113-risk-assessment.md` (the W0 gate artifact — read it first;
its verdict shapes this plan's depth). Scope: SPRINT.md chunks A–F. Rows here
are `/testing`'s authoring contract (W1 QA-first + per-wave flips); `/qa`
verifies the drafted set against this plan at Phase 5.

Conventions: row IDs are `F-` (W1 fences, ungated), `MS-P` (memory-safety
probe slice, **detachable, gated on the W0 user decision**), `MC-` (W2
mono/carrier), `BD-` (W3 binder), `PS-` (W4 persistence/shadowing), `RG-`
(registers/batteries). `[oracle]` marks ownership/RC-affected rows — under
the strategy's §1.3 discipline these MUST be authored through the safety
combinator **once the lane exists**; until the W0 gate rules, they run on
established observables (`RC_STATS`, `RC_DEC_CHECK`, `--link` face) only.
**Twin-row-per-axis is binding on every matrix in this plan** (the S112
calibration, §6 below): each family names its equivalence twin explicitly.

## 1. W1 fences — ungated (author before W2 opens)

### 1.1 D2-as-ruled — spec §7.11.2 (method-import dispatch), incl. the fence-inversion sweep

The ruling is scribed: `spec/07-traits.md` §7.11.2 cells (a)–(e). The fix
lands in W2 (accept-side, existing `MethodResolutions` carrier — arch Q4).
Fences first; the inversion sweep (arch seam flag ii / revision 5) flips OLD
pins **in W1**, not when W2 trips over them.

| Row | Cell | Test / directive | Expected at W1 close |
|---|---|---|---|
| F-D2-1 | §7.11.2(e) nullary must-accept-and-compile | RE-POINT `tests/nullary_return_dispatch_method_only_import.rs::nullary_return_dispatch_method_only_import_no_codegen_leak` — the ruling-agnostic two-arm pin tightens to the ruled arm: **exit 42**, ×3 modes (`run_through_all_modes` or mode triplet). `// spec:` → §7.11.2(e); `// defect:` framing updated (ruling landed; owner /dev(typecheck), W2) | RED (flips at W2) |
| F-D2-2 | **FENCE INVERSION** — unary method-only-import | `…::unary_arg_dispatch_method_only_import_clean_typecheck_error_green_fence` currently pins the OLD "no impl" reject as the *correct* shape. §7.11.2(e) final sentence inverts it: the unary case must **accept** and dispatch on the argument's concrete type. Flip to must-accept (exit/output identical to the trait-imported twin); rename to drop the `_green_fence` framing | RED (flips at W2) |
| F-D2-3 | Sweep completion | Sweep for OTHER old-behavior pins: grep `tests/*.rs` (`spec_07_traits.rs`, `trait_imports.rs`, `cache.rs`, `repl_*.rs`, `examples.rs`) for method-only-import cells asserting a "no impl"/trait-not-in-scope reject. Every hit flips or gets an explicit not-affected note in the change-set (the S112 UW preserved-facet discipline: negative facets — no-panic, no `undefined function` leak — are RETAINED through the flip, never dropped) | sweep table in W1 report |
| F-D2-4 | Trait-imported control | `…::nullary_return_dispatch_trait_imported_runs_green_fence` stays GREEN untouched | GREEN |
| F-D2-5 | **TWIN row** (the relations axis) | Method-only vs trait-imported: same program modulo the import line, SAME observable (exit 42) — one test asserting both runs agree. This is the invariant the ruling states ("reaching the method reaches everything dispatch needs") | RED (flips at W2) |
| F-D2-6 | §7.11.2(b) conflict-not-shadow | Import same-named method `m` from two modules → §8.6.4 duplicate-bare-name conflict, located, at compile time; neg twin: importing only ONE of them dispatches fine (the import IS the disambiguator) | RED or GREEN per current behavior — author both polarities; any RED attributes to W2 |
| F-D2-7 | §7.11.2(c) diagnostic names the trait | Method-only import, dispatch type with NO impl → clean typecheck-family error that **names the owning trait** though the trait was never imported | RED (flips at W2) |
| F-D2-8 | §7.11.2(d) declaration still gated — **over-inversion fence** | `(impl T Type …)` with only a method of `T` imported → still REJECTED (declaration reaches the trait; dispatch reaches the method). Guards W2 against overshooting the inversion | GREEN expected (current reject stands); must STAY GREEN through W2 |
| F-D2-9 | Mode uniformity (AG-2 class) | The new accept class and the (c)-diagnostic class each get one extract-and-compare mode-uniformity guard, REPL/`--run`/`--link` | rides the W2 flip change-set |
| F-D2-10 | **NULLARY no-impl reject cell (was FIXME 0672, P6b — the missing variant sibling of F-D2-7)**: a return-type-dispatched method whose pinned return type has NO impl is accepted by typecheck and leaks `undefined function` at codegen — REPL + `--run`, **import-independent** (reproduces fully inline; NOT a D2 import edge — the general return-dispatch no-impl gate). The unary sibling rejects cleanly (F-D2-7 pins it). **Attribution: /dev(typecheck), `class=check-gate-leak`** — the nullary resolution path's no-impl case never reaches the reject author the unary path uses; it must reject at typecheck naming the owning trait (§7.11.2(c)), uniform with unary, never emitting a call to the un-monomorphised method symbol. **THIRD check-gate-leak instance this sprint** (D2 original accept-side; 0655 face 3; this) — noted as 0653 prong-3 evidence. /testing (close-out): F-D2-7's nullary sibling in `nullary_return_dispatch_method_only_import.rs` + an inline-trait variant ×3 modes (F-D2-9 discipline), RED, `// spec:` §7.11.2(c) + §3.11; repros verbatim in the FIXME (delete it in the pin change-set) | RED until the /dev fix |

`Default` prelude promotion (P6, /stdlib) consumes F-D2-1/5 as its fences —
no separate rows here; the stdlib side is covered by the 0605 gate (§1.4).

### 1.2 Binder-generalization matrix (per-surface-form × route × polarity)

Spec: §5 intro (binder principle, scribed S112; generalization stood
un-vetoed → now in scope). ONE frontend seam (`reject_qualified_binder_head`,
arch Q3); the matrix exists precisely to pressure that one seam — a form
whose cell fails differently has grown its own path. Existing pins:
`spec_05_definitions.rs::defn_qualified_head_rejected_binder_neg`,
`spec_07_traits.rs::deftrait_qualified_bare_head_rejected_binder_neg`,
`…::deftrait_qualified_parenthesized_head_rejected_binder_neg` (all RED,
`class=silent-accept`). TB-26/27 from the S112 batch fold in here.

| Row | Cells | Notes |
|---|---|---|
| BD-M1 | **Native forms × {qualified-head reject, bare-head accept}**: `defn` (pinned), `defn-`, `deftype`, `deftype-`, `deftrait` bare + parenthesized head (pinned ×2), `deftrait` METHOD-name position, `defmacro`, `defmacro-` | one reject row + one bare-head positive twin per form; reject must be LOCATED (span assertion per the S112 F1 precedent — `assert_err_span_at`) |
| BD-M2 | **Macro route** (distinct path to the same seam): an inline `defmacro` whose expansion emits `defn`/`defn-`/`defmacro` with a qualified head → reject; **span lands on the user's WRITTEN form**, not the synthesized `defn` (arch Q3 rider b — its own cell) | tests are stdlib-free: use an inline macro, NOT stdlib `def`. Provenance-through-expansion is the load-bearing assertion |
| BD-M3 | **Stdlib-route conformance row** (single row, sanctioned exception): `def`/`const` (stdlib/defs.cl macros) with a qualified head, behind `use_workspace_stdlib_for_stdlib_conformance_only()` — the real user-facing route | one row, both a reject cell and a bare-head positive; /testing may fold into the 0605 gate file |
| BD-M4 | **con_var qualification** (S112 F3): `(deftrait (Functor prim/x) …)` — slash-bearing con_var rejects (spec: bare lowercase identifier) | rides the same seam family |
| BD-M5 | 0589 family: qualified-lowercase annotation mints a type var (pin exists RED, `spec_03_types.rs` F2/0589 rows) — W3 drains it; verify the pinned rows flip and the four mirror mint sites converge (0590 map) | existing pins are the rows; no new authoring unless W3 evidence names new cells |

### 1.3 Qualified-head corpus sweep (GATES W3 — arch seam flag iii / revision 6)

Turning 8 forms' silent-accepts into rejects can break fixtures that
accidentally use qualified heads. /testing sweeps `tests/` (incl.
`tests/fixtures/`), `examples/`, `repl/demos/` (+ archive), `exemplar/` for
qualified heads in ANY binder form, native or macro-route. **Seed evidence
(/qa grep, 2026-07-19): single-line pattern hits only the deliberate binder
pins themselves (`spec_05_definitions.rs`, `spec_07_traits.rs`) — corpus
likely clean**; the /testing sweep must be stronger (multi-line forms,
macro-route `def`/`const` in stdlib-adjacent fixtures, `.demo` files). Result
table lands in the W1 report; any fixture fixes ship **atomically with W3**
(reject + fixes in one change-set). W3 does not open until this table exists.

### 1.4 0605 — stdlib compile smoke gate (FIXME 0605, target /testing)

Per the FIXME's settled design: e2e family behind
`use_workspace_stdlib_for_stdlib_conformance_only()` that `--run`s an import
of **every top-level stdlib module** — enumerated from `stdlib/` at test
time (skip `prelude.cl` + `.test` submodules), never hand-listed; the failing
MODULE must be named (per-module tests or per-module failure report —
/testing's call). Tier 2 (self-test execution via `discover-tests`) is sized
separately, NOT this sprint's blocker. /testing deletes 0605 when the gate
lands.

### 1.5 0638 repro capture (ungated — deterministic defect pin, NOT a probe)

From FIXME 0638's preserved verbatim files (`dthelp.cl`/`mac.cl`/`usemac.cl`):
narrow failing-not-ignored repro, all three modes.
`// defect: class=uaf locus=src macro-clause invoke/marshal seam (src/expander.rs + src/marshal.rs; intrinsics alloc adjacent) found=S111 owner=/dev`.
Attribution is ALREADY CONFIRMED (PLAN §I.4, re-checked at HEAD post-CS-5:
distinct defect — not §3.7, not 0633) — the pin cites it; no attribution work
rides the capture. Once committed, the failing test is the record + trigger
and FIXME 0638 deletes (the FIXME's remaining function is repro-source
preservation). `[oracle]` — graduate into the lane when it exists; until
then `--run` exit-code + `RC_TRACE` garbage-header face per the FIXME.
**W5a addendum**: pin family gains the M1 mode-axis twin per §2.2 R-1
(M1-ON ⇒ M3-parity-leak face; M1-OFF ⇒ double-free-assert face; both
RED-until-fixed).

### 1.6 Small ungated riders

| Row | Item |
|---|---|
| F-R1 | Entry-`main` IO-teardown leak: land the 2-line narrow guard (`(defn main [] (let [s "hi"] (Pure 9)))` → allocs==frees under `RC_STATS`) and re-annotate DG-R2's `// defect:` → `class=rc-miscount locus=entry-main IO-teardown seam` per PLAN §I.4 (directed S111, not yet executed — `adt_drop_glue_underkey.rs:136` still carries the superseded class). `[oracle]` |
| F-R2 | Framing strips still outstanding from the S112 §11 list: verify the R2 `owner=` update + mode-uniformity instruction landed in `multi_sig_base_mono_carrier_loss.rs` (W6 report says maintenance done — confirm, else do) |

## 2. Memory-safety probe slice — DETACHABLE (gated on the W0 user decision)

> **GATE OUTCOME (user, W1)**: the W0 depth recommendation was APPROVED
> AS-IS (tiers 4+5+3+1–2; generative harness → S114). This slice was
> **ungated into W1** and landed with the fences; MS-P6 rides W5. The
> detachability provision is spent — retained below as the record.

Dispatch W1 with this slice separable; if the user gates depth down, §1
lands unchanged. Contents (strategy §1.3/§6 made rows):

| Row | Item |
|---|---|
| MS-P1 | `assert_safety_matrix` combinator in `tests/helpers/e2e.rs` (+ `.safety_matrix()` builder face): modes × toggle {on, off} × {behavioral equivalence, `RC_STATS` balance, `RC_DEC_CHECK` zero, `--link` face}; batched + per-program duality (the 0633 batch-cardinality lesson); RC runs serial |
| MS-P2 | `tests/safety_oracle_lane.rs` + `tests/fixtures/safety_corpus/` seeded per strategy §1.3 (0641 B-1/B-2/I-1/I-2, §3.7 COW family, 0633/0640 collision pairs, 0638 repro, multi-arity B-2 heap-read shapes, tco/vec-query/vec-cow repros). **Acceptance: the 0641 B-1 program goes RED under the lane on day one; §3.7 fixed family GREEN; lane wall ≤60s** |
| MS-P3 | Retro-wrap the existing ownership/RC corpus (~10 files) through the combinator (mechanical; may ride MS-P1 or follow) |
| MS-P4 | **0633 module-axis cell RE-AUTHORED** `[oracle]`: DG-R2's observable was re-attributed (PLAN §I.4) — the module-axis drop-glue collision (two bare-same-name ADTs from different modules in one compiling batch) currently has NO effective guard. Re-author on a corruption face (`RC_DEC_CHECK` / DEC-on-wrong-slot / `--link` SIGABRT), not the leak face. Include the REPL-vs-`--run` divergence face from the reachability record (`s111-0633-adt-drop-glue-underkey.md` §Collision scope: per-turn Jit batches vs whole-module ObjectModule) |
| MS-P5 | Standing `RC_DEC_CHECK` positive assertions (today: zero suite-wide) — join the lane's signal set |
| MS-P6 | W5 acceptance rows ride the build change-sets per the depth ruling: diagnostic-mode lanes (quarantine/scrub/counters) get one deliberate-violation self-test each (the mode catches a planted fault); the §3 rule-table increment lands with the 0641 flips UNDER the lane (strategy §1.5 sequencing); 0633 re-key (R4) flips DG-R1a/b/c + MS-P4 |

| MS-P7 | **NEW lane-caught defect (W1 day one)** `[oracle]`: direct COW-set→project shape — `(vec-get (vec-set v 0 9) 0)` (incl. let-bound variant) returns correctly under `--run` but **deterministically aborts under `--link`** ("corrupted double-linked list"). Pinned RED: `tests/safety_oracle_lane.rs::safety_lane_cow_set_read_link_corruption_red`, `class=uaf found=S113 owner=/dev`. **Attribution (provisional, /qa 2026-07-19)**: the vec-set-RESULT consume/provenance family — 0641-adjacent, a THIRD reaching-context of the seam PLAN §S111 I.4 already attributed for B-2/I-2 ({match var-binding, vec-literal element store} + now {projection-out}); /testing confirms the §3.7 `MayAliasOf` fix does not cover it. **Discriminator recorded, not yet run**: the lane's toggle-off face decides the half — abort ALSO under `CRANELISP_NO_OWNERSHIP=1` ⇒ ownership-independent backend consume defect (the B-2/I-2 factor); oracle-off clean ⇒ the elision/provenance half (§3c rule-table projection row). /testing reports which signals fired per toggle at W5 dispatch — no /qa test run (one-agent-one-test-run; W2a active). **Flip trigger: the W5 0641/§3 increment** (it spans both halves — typecheck rule-table + the paired backend consume fix), verified UNDER the lane; if the pin survives that change-set it is a DISTINCT backend vec-set-result defect and re-attributes then (the MC-E1 protocol: a non-flip is evidence, not a failed fix) |

Generative harness v1: **deferred to S114** per the risk assessment §3 —
stretch only.

### 2.1 Suite-stewardship note — lane-induced load sensitivity (W1, not a lane defect)

The link-heavy safety lane raises parallel subprocess load enough to surface
**pre-existing concurrency-timing races**: `lenient_vec_map_reduce_parallelizes`
and rotating peers fail under full-suite load, **all pass in isolation**
(W1 report: 1 isolation-clean load-sensitive RED in the run). Disposition per
standing practice: NOT "flaky" (forbidden disposition), NOT attributed to the
lane — these are timing-threshold assertions in the effect-concurrency family
(same profile as the `concurrency_capacity` ~151–156ms-vs-150ms threshold
defect recorded at 0604 §S110-disposition, owner /qa triage,
effect-concurrency track). Stewardship: (a) the failing set is recorded
per-run in the wave reports (rotation is expected — load, not seed, selects
the victim); (b) they count as attributed carries under this note, never as
lane regressions; (c) the durable cure is the effect-concurrency-track
timing-threshold review (S114 candidate — thresholds asserted against wall
time under uncontrolled parallel load are the defect class, per
`feedback_measure_orders_of_magnitude_not_precision`); (d) if any member
fails IN ISOLATION, this note no longer covers it — isolate fresh, own
attribution.

### 2.2 W5a attribution-re-run reconciliation (/qa, 2026-07-19 — three deviations ruled; /testing directives land inside the W5b batch)

| # | Deviation | Ruling |
|---|---|---|
| R-1 | **0638 face flip under M1**: quarantine neutralizes the double-free into a leak — M3 parity abort (delta +10), not the double-free assert (physics sound: a quarantined block cannot be re-freed-into-reuse) | **Map updated**: the double-free class's mode-face is **M3-leak with M1 ON; double-free-assert only with M1 OFF**. **YES — the 0638 pin family gains a mode-axis cell**: one cell M1-ON (expects the M3 parity abort face) + one cell M1-OFF (expects the double-free assert face), BOTH RED-until-fixed, both flip on the /dev fix. Grounds: a defect's observability must not depend on lane config — without the OFF cell, enabling quarantine by default would silently reclassify the defect's face and a partial fix could green one face while the other still fires. **/testing (W5b): add the M1-OFF twin beside the existing pins** |
| R-2 | **MS-P7 flips GREEN under modes** — the `_red` guard's detection-shaped assertion passes once corruption is deterministic | **Re-shape — mode-conditional green is NOT acceptable for a defect pin.** A pin whose color depends on lane config cannot serve as the flip trigger (the failing-not-ignored discipline: RED while the defect EXISTS, green when FIXED — never green when *detection improves*). **/testing (W5b): re-shape `safety_lane_cow_set_read_link_corruption_red` to assert the SPEC-CORRECT contract** — `(vec-get (vec-set v 0 9) 0)` returns the set value, abort-free, across modes — **RED under ALL mode combinations** until /dev fixes it. The detection capability is separately valuable: keep it as a SEPARATE GREEN lane-capability fence ("the lane detects this planted-class fault" — the MS-P6 self-test discipline), beside, not instead of, the pin |
| R-3 | **`ownership_reuse` +6 parity aborts** (deltas 1–2; one standalone-binary ALLOC=3/DEALLOC=1; clean programs balance — program-attributable) | **Split attribution, discriminator-directed**: (a) the standalone-binary ALLOC=3/DEALLOC=1 case matches the **entry-`main` IO-teardown family** (PLAN §S111 I.4 DG-R2 re-attribution: the chronologically-LAST IO/result allocation leaks; F-R1's record) — joins that row, owner /dev (backend main-epilogue / int IO-trampoline result-dec seam), flip trigger = the teardown fix. (b) The delta-1 cases: **/testing (W5b) runs the characterization discriminator per test** — teardown-residual signature = the leak is the final IO/result allocation only and the delta is INVARIANT under program scaling; real-leak signature = delta scales with values/iterations (M2/trace names the leaked block). Teardown-residuals get the shared characterization note under F-R1 (so W5b runs do NOT read them as regressions); any real leak gets its own row + pin + owner per evidence. No test attributed by guess |

**Folded strengthenings**: (i) **DG battery**: modes fire the drop-glue
collision on **7 axes deterministic vs the 3 mapped** — recorded as
strengthened coverage on the DG/MS-P4 row set; all 7 axes join the CS-1.1
re-key acceptance set (the flip must green all seven, not the mapped three).
(ii) **A2–A4 release-variant scope** (for the R8 register row — flagged to
/arch for its next `safety-invariants.md` touch; /qa cannot edit that file):
release builds carry the **RC-field/size invariant asserts only**;
`LIVE_ALLOCS` full alloc-tracking is **debug-bound** — R8's
"production unasserted by design" carve-out is now partially retired and
should read "production: RC-field/size asserted (A2–A4); full
alloc-tracking debug/lane-only". The register row stays truthful only with
that split stated.

**Named-member extension (W2a, 2026-07-19)**:
`nullary_return_dispatch_method_only_import_no_codegen_leak` (F-D2-1, GREEN
since the W2a D2 fix) is explicitly under this note's cover — /dev observed
intermittent failure under parallel subprocess load, isolation-clean 8/8.
Same conditions apply: counted as a load-sensitivity carry when it fails in a
parallel run, never re-attributed to the D2 fix without an isolation failure;
an isolation failure exits the cover and re-opens D2 evidence fresh.

**Run log**: W2-close run (4863/34/1) — ZERO §2.1 fires (clean run recorded;
the note's members are load-selected, so a clean run is expected variance,
not retirement evidence).

**Agent-lane family — explicitly covered**: the FIXME-0615-documented
binary-provenance race (`agent_flag_errors_on_non_agent_build` and any
agent-flag sibling asserting feature-off behavior against
`target/debug/cranelisp` by path) is under this note on the SAME terms — a
parallel-run or bare-run failure attributes to 0615's provenance mechanism
(deterministic in binary provenance, per S112 §11 ruling 6 — never "flaky");
the cure remains 0615's `CARGO_TARGET_DIR=target/agent` lane isolation
(owner /testing); an isolation failure under verified single-lane provenance
exits the cover — isolate fresh.

## 3. W2 — mono/carrier family (flips + the owed S112 rows)

### 3.1 The four owed PLAN rows (S112 Phase-6b debt) — precise attributions

These are the plan-of-record rows for the pinned family; committed pins
cited; attribution is final unless W2 evidence contradicts.

| Row | Defect | Pin | Attribution + fix shape |
|---|---|---|---|
| MC-D1 | **D1 — multi-sig variant display drops inferred constraints** (`/sig h` shows `(Fn [a a] a)` not `(Fn [:Num a :Num a] a)`; bound IS enforced — display-only) | `tests/multi_sig_variant_display_constraint_drop.rs` (RED), `class=display-envelope-mirror` | Owner /dev(typecheck), W2. The single-sig and multi-sig variant renders diverge for the same inferred scheme — fix at the ONE variant scheme→display seam, reading the RECORDED constraint-carrying scheme (P26). **Arch revision 9 check item: the fix stays inside W2's typecheck deployment; NO int-side echo patch** (the eval.rs `impl_echo_type_name` precedent — re-deriving at the echo is the named defect shape). Row asserts /sig AND the definition echo agree. **W2-close status: per the W2 record; the no-int-side-echo-patch note STANDS into W4 (echo agreement verified there)** |
| MC-D2 | **D2 — nullary method-only-import codegen leak** (now: must-accept per §7.11.2(e)) | `tests/nullary_return_dispatch_method_only_import.rs` (RED; re-pointed per F-D2-1) | Owner /dev(typecheck), W2. Accept-side close (arch Q4): trait-method resolution roots at the method's chain-followed home (bounded keyed chain, P24) instead of requiring trait-in-scope; populate the existing `MethodResolutions`/`ResolvedCall::TraitMethod` carrier for the nullary return-type-dispatch cell; codegen's keyed read then links. NO new resolution machinery; expected types diff none; any carrier shape change = FIXME `target: /arch` before landing. The unary reject INVERTS (F-D2-2); declaration gate does NOT (F-D2-8) |
| MC-D3 | **D3 — poly callee in a cross-arity-reached clause never monomorphised** (codegen `undefined function`; concrete clause; primitive-free-standing — prelude NOT load-bearing) | `tests/multi_sig_poly_callee_cross_arity_mono.rs` (RED), `class=carrier-loss` | Owner /dev(typecheck), **typecheck-only** (arch Q2/revision 3): producer failure, P26-shaped, same family as R2 — the poly callee reached only through a cross-arity clause's mono recheck is never enqueued/instantiated. Backend is a pure keyed consumer (BC §3 inv. 10); the ONLY admissible backend delta is diagnostic hardening (raw Cranelift `undefined function` → located P24 hard-fail). **/design(typecheck) produces call-chain evidence (where the mono request is dropped) BEFORE the fix**; expected shape = §11.3.4 settled-state direction, landing with R1/R2 in one producer change-set |
| MC-R1v | **R1 prelude-`+` variant** (cross-arity poly-clause self-call via the trait-method `+` dispatch path) | `tests/multi_arity_clause_param_51_2.rs:611` area (RED), `class=wrong-reject` | Owner /dev(typecheck), W2; fix direction §11.3.4 (widen the inline self-call match to the base's post-drain-settled overload clauses — P26 shape). **Entangled — see MC-E1** |

### 3.2 Pin-4 entanglement row (sequencing constraint on W2)

| Row | Content |
|---|---|
| MC-E1 | **The trait-`+` STANDALONE TWIN itself hits carrier-loss** (S112 P6b finding, documented in-pin: `user/user/fb$Int+Int` — note the DOUBLED module prefix — R2-family evidence). Consequence: the prelude-`+` R1 variant likely needs BOTH the R1 inline-gate widening AND the carrier-loss fix to flip. **Binding sequencing note for W2**: land/verify the carrier family (R2/D3) before judging R1-variant flips; a non-flip of MC-R1v after the R1 fix is NOT a failed fix — check the carrier face (does the twin now run?) first, and only then re-attribute. The doubled `user/user/` prefix is its own evidence cell: if it survives the carrier fix, it is a distinct mangle/keying defect — pin separately then (R4 register row candidate), do not fold silently. **NOTE CLOSED W2 (2026-07-19): ruled BENIGN/distinct — the doubled prefix is home-qualified storage-KEY rendering, not a mis-mint; the backend keyed read hits it correctly. No pin owed** |

### 3.3 Remaining W2 rows

| Row | Content |
|---|---|
| MC-R1 | R1 primitive variant (`multi_arity_clause_param_51_2.rs:536` area) flips; the standalone twin fence (already in-file) must stay GREEN |
| MC-R2 | R2 carrier-loss flips (`multi_sig_base_mono_carrier_loss.rs`); the fixing change-set MUST extend the flip with the mode-uniformity assertion (S112 §11 ruling 1 — the REPL/`--run` gate-order divergence is a FACE; if any divergence survives the carrier fix it earns its own row + attribution then) |
| MC-TB24 | TB-24 poly-applied impl target wrong-reject flips (`spec_07_traits.rs:1943` area — both forms) |
| MC-X1 | **Carrier × reaching-context sweep — TRIGGERED.** The S112 §11 ruling-1 condition ("if leg (c) confirms a second producer miss") is met by R2 + D3 = two producer misses in one family. Scoped to the carriers W2 touches: {`resolved_target`, `MethodResolutions.resolved_calls`, `multi_sig_mangled_names`, mono-instance requests} × reaching context {direct call, call inside minted mono body, cross-arity-reached clause, return-type-dispatch site} — pos cell + **standalone-twin row per context** (the instrument that caught every S112 topology cell). Author the cells not already pinned; expected mostly GREEN — the value is the enumerated fence against the family's NEXT cell |
| MC-N1 | **Inversion fences** (the S112-1 wrong-accept-inversion hazard applied to W2's flips): what must STILL reject after the accepts land — genuinely-no-impl dispatch still errors (naming the trait, F-D2-7); §5.1.1 same-arity-unifiable still rejects; §8.6.4 method-import conflict still rejects (F-D2-6). Each accept-flip change-set runs these as its must-hold set |
| MC-S1 | **No schema bump expected in W2** (arch revision 4). Contingent row only: if any W2 carrier shape change escalates to /arch and lands, an AG-1-class stale-cache wholesale-refusal row rides the same change-set. Otherwise no row |

### 3.4 W2a-close addenda (/qa, 2026-07-19 — review findings actioned; /testing lands rows next dispatch)

| Row | Content |
|---|---|
| MC-X2 | **NEW DEFECT (review finding 8, verified live) — imported multi-sig base fails on the DIRECT path**: `(import [mlib [h]]) … (h 1)` → `undefined function: h`. **Attribution (/qa)**: owner **/dev(typecheck)**, `class=carrier-loss` — a module-locality cell of the same producer family as R2/D3: the multi-sig dispatch machinery (overload gate → carrier writes → mangled-entry registration) derives its keys for LOCALLY-defined bases; an imported base's call site never gets a consumable carrier/mangled entry, and the backend's keyed read misses loudly (correct consumer behavior — the producer is the owner). Pre-existing: **no green cross-module multi-sig cell has ever existed** (coverage-matrix axis miss: module-locality × multi-sig — see §6 calibration). **Fix-time interaction, recorded**: the W2a scoped-drain carrier writes `state.current_module`, which is WRONG for imported bases — the fix must key by the base's HOME module (storage identity, the 0621 `storage_fq()` lesson; P24). **Cross-note**: the MC-E1 doubled `user/user/fb$Int+Int` prefix is plausibly the same module-prefix mishandling one layer down — the fixer checks both faces. /testing lands the failing pin next dispatch (direct call + a dispatch-requiring twin, ×modes); fix rides W2b if capacity, else attributed carry. Matrix consequence: MC-X1 gains the **base-locality axis** {local, imported} per reaching-context, with the local cell as the GREEN twin. **CLOSED W2 (2026-07-19): FLIPPED — all faces incl. the qualified face (Fix A), ×3 pins green; home-module keying landed** |
| MC-TB24b | Constrained applied form `(Box :Disp a)` as an impl target — design names it equally-valid to the bare poly-applied form; NO test exists. Positive cell + its reject twin (`(Box :NoSuchTrait a)`) ride the TB-24 family. **CLOSED W2: both twins landed GREEN** |
| MC-G1 | The W2a review/fix-cycle repros become PERMANENT e2e cells (GREEN fences post-fix — each caught a real hole once, so each guards a revert): (a) template-select inside a mono body; (b) D3-harvested orphan-pendings; (c) method-only-import wrapper hop through `verify_constraints`; (d) foreign-sig-type `(sh 5)` with no `Int` in the importing module's scope | 
| MC-A1 | **F-D2 family gains a named MATRIX AXIS: import-shape × sig-mentions-foreign-type.** The review found every landed F-D2 cell imported `Int` into the calling module — a systematic hole: the cells never exercised dispatch/constraint checking when the signature mentions types NOT in the importing module's scope (exactly where the wrapper-hop and foreign-sig holes lived). /testing re-sweeps the F-D2 rows: each accept cell gets a foreign-sig-type variant (type reachable via the method's home but not imported at the call site) |
| MC-X3 | **FIXME 0655 attribution (W2-close, /qa)** — qualified own-module self-reference (`user/qloop` written inside module `user`) behaves THREE ways: batch `--run` circular-dependency reject / REPL-fresh "no member" reject / REPL-redefine **typechecks then hard codegen error** (`undefined function: user/qloop`). **Attribution**: owner **/dev(typecheck)**, producer-side — `record_reference_target`'s qualified leg: the `if let Some(resolved)` SILENTLY DROPS a recording failure the typing path tolerated, so typecheck accepts a form it wrote no carrier for (a P25 check-gate violation and a falsifier of the backend §2.7 "unreachable for well-typed programs" annotation — that hard-miss row's premise is now conditionally false until this closes). Class: `check-gate-leak` under EITHER ruling (the accept+no-carrier is wrong regardless); the pos/neg polarity of the other two modes awaits the user ruling (framed to /sprint at W2 close — see 0655). **Ruling-agnostic pin directive (/testing, next dispatch, D2 precedent)**: (i) the REPL-redefine cell must NOT reach codegen-error — either it evaluates or it is a clean located typecheck-family error; (ii) mode-uniformity — all three modes produce the SAME disposition (AG-2 extract-and-compare). Post-ruling: the matrix completes qualified-self-ref × {batch, REPL-fresh, REPL-redefine} × {pos,neg} at the shared seam, ONE diagnostic if illegal / carriers recorded if legal (and if legal, FIXME 0654's gate-3 shared-predicate obligation becomes ACUTE — the fixer reads 0654 first). Adjacency note: §5 binder work (heads) is DISTINCT — this is a reference, not a binder |
| PS-C1 | **5(a) disposition — stale-cache-over-changed-source (review incidental): ruled SUSPECTED DEFECT of the R6 cache-trust family, repro-gated** (not attributed by guess — the ruling-7 precedent). Observation: a REPL session in a dir with stale `.cranelisp-cache` + persisted `user.cl` served the PREVIOUS program's compiled module for CHANGED piped-stdin source (returned the old answer). The discriminator /testing lands next dispatch: session 1 defines `(defn f [] 1)` and exits; session 2 in the same dir pipes `(defn f [] 2)\n(f)` → MUST print 2 (redefinition wins — entered forms are evaluated; on-disk `user.cl` authority extends to *restoration*, never to overriding just-entered source). Pre-registered branches: prints 1 (or the old program's answer) ⇒ **DEFECT**, pin RED, owner /dev(src or backend cache seam), `class=` cache-trust (R6: re-validation elided at load — a stale compiled artifact served despite a source change), sibling of AG-1; prints 2 ⇒ the incidental was authority-model semantics ⇒ downgrade to **usability finding**, /qa files FIXME `target: /repl` (+/docs note) documenting the persistence/cache authority sharp edge, no pin. Either branch closes the item. **CLOSED (W2, 2026-07-19): discriminator printed 2 — redefinition wins, as-designed; usability branch taken → FIXME 0657 filed (`target: /repl`, /docs rider). No pin owed** |

### 3.5 MC-X3 dual-path audit (USER-DIRECTED, 2026-07-19 — call-chain evidence; ruling (a) LEGAL received)

**User ruling**: qualified own-module self-reference is **LEGAL** (TB-25
resolved-identity — `user/qloop` in module `user` is another spelling of the
local binding). **User directive**: audit whether the three-mode divergence
means duplicate typechecker paths. Read-only audit, no test runs.

**Verdict: ONE resolver — the divergence is NOT three resolvers.** Both the
typing leg and the carrier-recording leg of a qualified reference route
through the single sanctioned chain: `checker.rs::lookup` qualified leg
(~:1400) → `resolve_qualified` (:2066) → `scope_resolve` →
`cranelisp_types::ResolutionScope::resolve` (resolve.rs:125) →
`resolve_one` (:461) → `resolve_qualified` (:694); and
`record_reference_target` (:1508) → `resolve_ref_target` (:1577) →
`def_resolved` (:1604) → the SAME `scope_resolve`. But the one resolver's
**qualified leg has a structural blind spot**, and three consumers surface
it mode-dependently:

**The root seam**: `cranelisp_types::resolve.rs::resolve_qualified` (:694)
resolves via `resolve_terminal_entry_home_and_key(symbol_tables, …)` — the
**COMMITTED live tables only**. The unqualified path (`resolve_one` :481)
resolves through the caller's **first-hop VIEW (staging ∪ live)**, and even
its chain-follow carries the S109 AN-5 same-module staging arm
(`chain_follow_committed`, :765 doc). The qualified leg never got that fix:
a current-module-qualified reference cannot see staging, the in-flight
cluster, or the checker's env-held recursion local. Additionally,
**self-identity recognition is written-bare-name-keyed at two seams**:
`check_defn_body` binds the recursion local under the BARE name (so
`env.lookup("user/qloop")` and `is_recursion_self_ref("user/qloop")`
both miss — checker.rs:1515/:1546), and the backend's shared `is_self_call`
predicate compares written names — the register §3 written-name-identity
class, at the self axis.

**The three faces, mapped**:
1. **Batch** — mid-compile module's table not committed ⇒ `:694` yields
   `QualifiedModuleUnknown`/not-found ⇒ gap `SymbolTypechecked{module:
   qself}` (checker.rs:2094–2110) ⇒ int `gap_target_module`
   (dependency.rs:436) → `drive_module_dep` (:356) — **no `dep == module`
   guard** — `fq_module_is_loaded(qself)` false mid-compile (registered but
   not `is_typechecked`, :294) → register + `block_dep` (:341) → acyclicity
   check → "circular dependency detected: qself -> qself"
   (scheduler.rs:928/:1729).
2. **REPL-fresh** — SAME gap; module `user` IS loaded (`was_ever_terminal`)
   ⇒ `drive_module_dep` early-returns ⇒ retry makes no progress ⇒ the honest
   "module 'user' has no member 'qloop'" author (process_form.rs:588).
   Faces 1 vs 2 = ONE consumer chain reacting to loaded-vs-mid-compile
   state — not a second resolver.
3. **REPL-redefine** — committed table holds the OLD `qloop` ⇒ `:694`
   resolves against the STALE committed identity ⇒ typing succeeds; the new
   body's compile then misses (the bare-name-keyed self-call machinery
   never engages for the qualified spelling; the old entry is superseded
   mid-redefinition) ⇒ `undefined function: user/qloop` at the §2.7 keyed
   seam. ONE probe left for /dev at fix time: dump
   `resolved_targets[28..38]` on the repro — carrier recorded-but-stale vs
   silently-dropped (0655's hypothesis) distinguishes nothing about the fix
   shape, only the diagnostic wording.

**Duplicate-implementation census** (question (a)): resolution itself is
single-chain (clean). Remaining duplicate *interpreters* of the spelling,
now sweep rows: (i) the child-vs-absolute candidate-order policy exists
TWICE — `lookup`'s leg (~:1400) and `resolve_ref_target`'s hand-rolled
mirror (:1583–:1596, "mirroring lookup") — P7 twins that can drift; (ii)
the 0590 four type-position mirror resolvers (traits/type_resolve.rs ×3 +
form.rs) — same family, S114; (iii) self-identity recognition ×2 (env
recursion binding; backend `is_self_call`) — written-name-identity class.
Frontend (symbol kept whole) and int (consumes structured gaps, never
parses spellings) are clean.

**Recommended fix shape (single-seam, per ruling (a))** — for
/design(typecheck) → /dev(typecheck):
- **Primary — spelling normalization at the ONE Var entry** (`infer_var` /
  `lookup` entry): when the qualifier (after §8.6.6 alias substitution)
  names the CURRENT module, the reference IS the bare name — normalize
  before the env consult, so recursion-local / shadow gates / staging /
  `record_reference_target` / backend self-call predicates all see the
  bare shape. All three faces collapse to the bare twin's behavior by
  construction; batch/fresh gaps for own-module refs become unmintable.
- **Supporting (types crate, /arch approval)** — apply the AN-5 staging-arm
  cure to `resolve_qualified` :694: when the alias-substituted module part
  == `current_module`, resolve through the first-hop VIEW like the
  unqualified path (defense-in-depth for non-checker consumers of the
  scope).
- **Deletions, never per-mode patches**: int gains NO `dep == module`
  special case (the gap must simply never exist for the current module); a
  tier-3 `debug_assert!(dep != current_module)` at `drive_module_dep` is
  the legitimate seam-naming residue. While in the file, collapse the
  candidate-order twin (i) onto one helper (P7).

**Post-ruling matrix rows** (/testing, with the fix change-set — all
UNIFORM-accept per ruling (a)):

| Row | Cells |
|---|---|
| MC-X3a | qualified own-module reference × {batch, REPL-fresh, REPL-redefine} × pos — **TWIN ROW per mode**: qualified spelling behaves IDENTICALLY to the bare twin (same value, same exit); includes the fresh self-recursive cell (`user/qloop` inside `qloop`'s initial definition = legal recursion, ≡ bare) |
| MC-X3b | neg twin: qualified reference to a genuinely-ABSENT own-module member ⇒ "module 'user' has no member" — IDENTICAL diagnostic in all three modes (mode-uniformity, AG-2 extract-and-compare); never a circular-dependency reject, never a codegen leak |
| MC-X3c | guard cells: submodule-child precedence unregressed (`util/x` in `main` with a `main.util` submodule still prefers the child — the :1403 candidate order); alias-spelled current module (`(mod …)` alias resolving to self) behaves as own-module |
| MC-X3d | the existing MC-X3 ruling-agnostic pins flip to the accept arm; §2.7 backend annotation ("carrier-absent = unreachable for well-typed") becomes TRUE again — /design(backend) note rides the fix |

**Fed into sweep records**: register §3 gains rows (i)/(iii) as
`written-name-identity` / P7-twin sweep entries; 0653's S114 sweep cites
this audit as instance evidence; 0590's convergence increment now has a
fifth mirror-family member (the candidate-order twin).

### 3.6 Phase-6a attribution batch (/qa, 2026-07-19 — proxy findings; /testing pins in ONE 6b-window dispatch)

| Row | Content |
|---|---|
| MC-X4 | **NEW defect (/port) — consumer-of-multi-sig-return residual**: a poly Vec callee (`count`) consuming a multi-sig fn's bare `(Vec Int)` return ⇒ codegen `undefined function: count`; mode-uniform (run+link); two-function control GREEN (§5.1.2 equivalence divergence — the standalone-twin instrument again); concrete caller (≠ R2); consuming-the-RETURN (≠ D3); ADT-wrapped return dodges. **Attribution**: owner **/dev(typecheck)**, `class=carrier-loss`, **P26-temporal mechanism**: the multi-sig call's RESULT type settles post-drain, but the consumer's mono harvest keys its instance request pre-settlement ⇒ the request carries a residual Var ⇒ no ground `count` instance minted ⇒ loud keyed miss (correct consumer). Fix shape: the consumer harvest keys on the SETTLED ground result (derive-at-settlement, §11.3.2 single-sourcing reference). Pins from the preserved repros (`probe/min.cl` RED + `minctl.cl` control-twin GREEN fence, ×run+link) + the ADT-wrapped boundary GREEN fence — **CORRECTED (P6b): ADT-wrapping dodges only when the field is merely MATCHED; see MC-X4b**. **Matrix**: MC-X1's reaching-context axis gains **{poly-consumer-of-multi-sig-return}** — the family's fifth context. Flip trigger: the /dev(typecheck) fix; rides the same deployment as MC-X5 (below) but is a DISTINCT mechanism row |
| MC-X4b | **MC-X4 face 2 — the TYPE-AMBIGUITY face (P6b, /port)**: the multi-sig return flowing through an **UNTYPED ADT field**, then CONSUMED (not merely matched) by a downstream poly user ⇒ `ambiguous type … residual unbound type variable`. **Same root, same owner** (/dev typecheck, the pre-settlement residual Var — here it lodges in the untyped field and surfaces as ambiguity instead of a keyed miss; two faces, one mechanism, one fix). Pin directive (/testing close-out, free-standing re-author from the `probe/rep.cl` pair): typed-field GREEN twin + untyped-field-consumed RED; both flip/hold with the MC-X4 fix. The face pair itself is the fence against a partial fix (grounding the direct-call path but not the field-flow path) |
| MC-X5 | **infer_apply raw-name overload gates** (/dev's flagged 0655-fix residual): the gates at `infer.rs:658/:678` read RAW AST names, so a multi-sig SELF-QUALIFIED self-call (`user/msig` inside `msig`) is not normalized at the gate — the written-name-identity class (register §3 row 7's sibling) at the overload-gate seam. **SEPARATE from MC-X4, connected at the family level** — verdict below. Pin: qualified-spelled self-call to a multi-sig base ≡ bare twin (accept + same dispatch), per the MC-X3 normalization contract. Owner /dev(typecheck) |
| MC-V1 | **Connection verdict (item-1 question)**: MC-X4 does NOT sit on the raw-name seam. Evidence: (i) the MC-X4 repro has no qualified spelling anywhere — the raw-name residual concerns spelling normalization; (ii) the control divergence keys on RESULT-TYPE groundedness (two-function twin green ⇒ the multi-sig drain's settlement timing is load-bearing), not on name classification; (iii) the raw-name hazard's face is wrong gate classification (wrong dispatch/wrong-reject), not a missing consumer instance. **Two mechanisms, two rows — do not fold.** Connection: both are cells of the ONE multi-sig call seam in `infer_apply`; the SAME /design(typecheck) evidence pass covers both in one narrow deployment (call-chain evidence per row BEFORE fixes, standing rule) |
| MS-P8 | **ALLOC_PARITY conj/assoc leak (/port)** `[oracle]`: 1 Vec leaked per conj/assoc iteration (25,461 surviving in the solver; int-loop control balanced; QUARANTINE+SCRUB clean ⇒ **no UAF** — bounded, non-corrupting leak). The never-freed face of the 0408 copy-per-guess carry — but a LEAK is not copy-cost: the superseded/temporary Vec is never dec'd to zero. **Attribution**: owner **/dev(backend/intrinsics)**, `class=rc-miscount` (leak polarity), vec persistent-op (conj/assoc) RC path. Pin: minimal conj loop under `RC_STATS`/ALLOC_PARITY (allocs==deallocs), int-loop control twin — effectively /port's measurement as a lane cell. Scheduling: S114 candidate unless the Track-A window absorbs it (leak polarity = the S110-8/S111-2 inversion lesson: the pin must fence BOTH polarities — the fix must not convert to under-count). **P6b characterization datum (no independent row — the §2.2 R-3 discipline: constant delta invariant under scaling = residual class)**: the is-solved multi-sig collapse adds a deterministic ONE-TIME +1 to the exemplar's parity delta (single retained block, not per-call; ALLOC identical) — Track-A parity runs against the exemplar expect delta = per-iteration-leak + 1 until both faces close |
| PS-D1 | **0671 impl-confirmation display stamps the ASKING module, not the canonical home** (`impl user/Display for user/Int` when the canonical homes differ; `format.rs:497-501/:707-710`; live in 05-traits.demo). **Attribution**: owner **/dev(src)**, `class=display-envelope-mirror` — the P24 resolve-home class's display face and the eval.rs `impl_echo_type_name` precedent repeated: the confirmation line COMPOSES FQ names from the asking context instead of reading the RESOLVED identities (trait home, type home) the registry already carries. Fix reads recorded resolved state (P26); never a display-side re-derivation. /testing pins per 0671's brief (FQ-correct confirmation for a cross-module impl; asking-module ≠ home cell) |

**Risk-assessment fold** (recorded here; `s113-risk-assessment.md` §3a
stands): the ALLOC_PARITY finding is a RANKING DATUM in both directions —
(a) the W5a modes DETECTED a real latent leak in a real program on first
contact with the exemplar (detection win: the §3a "unknown member found
mechanically" pattern, second instance); (b) the leak itself is
**bounded and non-corrupting** (quarantine+scrub clean — no UAF face), so it
does not move the family-1 ranking; it joins the rc-miscount evidence list as
the leak-polarity exemplar. MC-X4 extends the mono/carrier family (family 2)
with a fifth reaching-context — the family's matrix (MC-X1) was built for
exactly this arrival.

**6b-window /testing dispatch readiness (item 4) — CONFIRMED, one batch**:
MC-X3a–d (accept-assert cells, §3.5) + MC-X5 (self-qualified gate cell) +
MC-X4 pins (min.cl RED + control + ADT-boundary fence) + MS-P8 (parity pin +
control) + PS-D1 (0671 cells) + the 0669 family e2e pins per that FIXME's
brief (cells A/E born-green + the still-RED family faces). All rows carry
owner + flip trigger; none is gated.

## 4. W3 — binder family execution

BD-M1..M5 flip (authored in W1). Plus:

| Row | Content |
|---|---|
| BD-X1 | 0613 verify: S111 record says the quasiquote fold landed — /dev(W3) closes 0613 or names the residual; /qa row = the QQ negatives (QQ-I1/I2/I5, committed S111) stay GREEN and any residual gets its own pin before 0613 closes |
| BD-X2 | W3 ships rejects + corpus fixes atomically (consumes §1.3's sweep table); examples/repl gates stay green in the same change-set |

### 4.1 Frontend-audit finding-1 addenda (pre-W5, /qa 2026-07-19 — `audits/frontend-s113.md` §2.2/§2.8; /testing pins next batch)

**Attribution (all rows): owner /dev(frontend), `ast_builder.rs`.** One
family, one cure shape: the crate's OWN invariant ("route every operand
position through `build_one_expr_at` — a raw `build_expr` silently drops
annotation support") enforced at N of M positions, because the
operand-position × {bare, ascribed, trailing-junk} matrix was never drawn —
each parser grew its own subset (the S108 mechanism verbatim). Fix = route
the four positions through the ONE seam + mirror `parse_defn`'s trailing
rejection at the two sibling sites; never per-site re-implementations (P7).

| Row | Content |
|---|---|
| BD-A1 | **`:Type`-ascription wrong-rejects ×4** (spec §2.3.8 MUST: "an annotation MAY appear in EVERY expression position"): `let` BODY (`build_let:1425` — `(let [x 1] :Int x)` errors), impl-method body (`build_impl_method:1204`), trait default-method body (`build_method_sig:1007`), `trace` operand (`build_trace:1377`). Four failing-not-ignored pins, `class=wrong-reject`, `// spec:` §2.3.8; each with its bare-body GREEN twin in-file. Ascribed-position cells for the ALREADY-routed positions (defn body, fn body, if, match, let *values*, apply, vec, top-level) are the positive fence set — spot-pin any not already covered |
| BD-A2 | **Trailing-form silent-drop siblings ×2**: `build_impl_method:1199` (`(defn name [p] body junk)` inside impl silently drops `junk`; contrast `parse_defn:467` which rejects) and `build_method_sig:1003` (`(show [x] Str body junk)`). Two neg pins, `class=silent-accept` (the pinned ctor sibling `deftype_ctor_trailing_form_after_field_bracket_rejected_neg` is the family's existing RED — cite it; the sweep the audit names is now this row set) |
| BD-A3 | **`build_type_head` case-hole — repro-gated classification cell**: the list arm (`:606`) skips the uppercase check the bare arm has (`:599`), so `(deftype (point a) …)` parses with a lowercase head; downstream behavior UNVERIFIED (audit ran no suite). /testing probes first, then pins per outcome: silent-accept ⇒ `class=silent-accept` neg pin at the parse seam (deftrait's `parse_trait_head_shape` checks BOTH arms — the P7 mirror is the fix shape); late incidental error ⇒ located-diagnostic row. Type-params any-case cell rides the same probe. NOTE 0660 adjacency (deftype ctor/field binder cells) — same enumeration, coordinate rows |
| BD-A4 | **`mod` binder row — missing from the BD matrix** (audit §2.8.2): §5.8's "simple symbol (not qualified, not dotted)" MUST is enforced NOWHERE (`module_extract.rs` has no such check, contra the design doc's claim) and tested nowhere. Add the qualified/dotted-`mod`-name reject cell + bare positive twin to BD-M1's family. The design-doc premise corrections (§2.8.1/§2.8.2 false claims in `binder-head-reject.md`) are /design(frontend)'s — routed by /sprint, not this plan |

## 5. W4 — persistence + shadowing (src/)

| Row | Content |
|---|---|
| PS-RT4 | RT-4 ×2 flip (`repl_persist.rs:1221/:1260` — impls dropped from regenerated `user.cl`; `class=enumeration-miss`, owner /dev(src), data-loss class). **The fix's acceptance is a persisted-content ENUMERATION MATRIX**, not the two pins alone: every persisted kind (`defn`/`deftype`/`deftrait`/`impl` conventional/`impl` HKT/`defmacro`) × {survives regen, survives schema-bump-or-no-cache restore} — rooted in the D45-as-amended storage model (shell at trait home + `impl_module` pointer, method `Def`s at writer's module; arch seam flag iv): every source of the kind contributes rows or a legal skip. Twin: conventional-impl vs HKT-impl regen twin. **AXIS ADDED (W4 close, was FIXME 0665 — deleted, this row is the durable record): trait-PROVENANCE {trait local, trait imported (file module), trait imported (prelude)} × {conventional, HKT} × {survives regen, survives no-cache restore}** — both original RT-4 pins sat in the local-trait cell only, and the W4 fix passed them while the imported-trait cell still dropped (0664, fix now landed + verified e2e). /testing lands the imported-trait e2e cell **born-green next batch** (recipe in the 0664 record — it is 0664's regression guard) + the prelude-trait cell (`impl Display MyType` in a full-prelude REPL — the highest-value real-usage variant). The D45 model SPLITS on this axis (shell at the trait's home), which is exactly why the variant grew its own missing codepath — the S108 category's textbook instance |
| PS-SH1 | Shadowing hang flips (`shadowing_scope_lookup.rs:54` — assert `:primitives/Int 5`, bounded timeout); shadowing overload-gate sibling flips (`:131`). The §12 matrix completes: {let-shadowed} × {single-sig defn, multi-sig base} × {call, value-ref} — the value-ref cells author now if missing. **CLOSED EARLY (W2, 2026-07-19): both shadowing pins FLIPPED incl. the hang — landed in the W2 window ahead of W4; matrix value-ref completion stands as the residual /testing item** |
| PS-R7 | **0604 rider consumption** (arch revision 7): W4 lands `debug_assert!` + `MODULE_TRACE` emit at EVERY live-table insertion seam (prelude-export-closure invariant, R7). /qa's diagnosis plan post-rider: (a) the assert converts any future firing into a named seam — that is the deliverable, NOT a fix; (b) a bounded recipe re-sweep runs ONLY in an environment with prior fires (the S109-era one, if still accessible) — ~320 cumulative no-fires say quiet-environment sweeps are spent evidence; (c) IR-1 lane + the two GREEN twins (`spec_08_prelude_outer_scope.rs`) stay must-hold; (d) unit test at the assert seam per METHOD §2.2 rides the rider change-set. FIXME 0604 stays open (updated 2026-07-19) — the sanctioned no-stable-RED exception; it retires when a firing names the seam and the fix + fail-on-revert sweep land |
| PS-0646/47 | 0646 (primer `Show` collision) / 0647 (empty `; impl:` drawer) riders — one display row each at the touched seam; 0647's fix un-blocks the held `; impl:` spec pin (/repl noted S112) |

## 6. Standing-category upkeep (S112 calibration folded in)

**Coverage by definition variants** (rolling category, user directive S108;
canonical statement `tests/CLAUDE.md`) gains the S112 calibration as
checklist items, applied throughout this plan:

1. **Axes are RELATIONS, not just forms.** Every S112 blocker sat in a
   relational cell (call topology, pairing slot, scope shadowing,
   carrier × reaching-context) that no form-variant matrix enumerated. Phase-3
   matrices must name their relational axes explicitly — this plan's:
   import-shape × dispatch (D2), route × seam (binder macro-route),
   carrier × reaching-context (MC-X1), shadowing × callee-kind (PS-SH1),
   storage-model × persisted-kind (PS-RT4).
2. **Twin-row-per-axis.** The standalone-twin/equivalence discipline caught
   what the matrices missed (B1, I1, R1, Pin-4); every matrix above names at
   least one twin row (F-D2-5, BD-M1 bare-head twins, MC-X1 per-context
   twins, PS-RT4 conventional/HKT twin).

3. **…and import shapes are an axis** (W2a calibration, 2026-07-19). Two
   fresh data points: (a) the F-D2 matrix lacked the
   import-shape × sig-mentions-foreign-type axis — every landed cell
   imported `Int` into the calling module, a systematic hole the review
   walked straight through (MC-A1 cures it); (b) finding 8 sat in the
   module-locality × multi-sig cell — no green cross-module multi-sig cell
   ever existed (MC-X2). Where a mechanism resolves *through* module
   structure (dispatch, carriers, mangles, constraint verification), the
   matrix carries {local, imported, foreign-sig-type} as a first-class axis
   with the local cell as the twin.
4. **The unit tier shares the implementer's blind spot too** (W2a review
   finding 1 — a QA-first miss, recorded): /dev's R2 unit test was SHAPED
   AROUND its own gap — it pinned the return with `add-i64`, exactly
   avoiding the un-unified-ret cell the defect lived in. This is the
   strategy doc's §3 pathology ("tests share the implementation's mental
   model") surfacing at the unit tier: a unit test authored by the fixer,
   from the fix, validates the fix's model of itself. Mitigation joins the
   category: for strategy-bearing fixes, the /qa plan row (or the /review
   brief) names the NEGATIVE-SPACE cells the unit tier must pin —
   derived from the design's claim, not the diff — before the fix lands
   (the S108 review-caught-defects-are-a-testing-miss lesson, now with a
   unit-tier instance).

**Recurring-class record (W2a)**: "**resolve once then throw the home
away**" — a resolution correctly chain-follows to an identity, then discards
the resolved HOME and re-derives it (or substitutes the current module)
downstream — hit **3 instances in W2a alone** (D2 dispatch rooting,
`verify_constraints`, dispatch-type resolution), meeting the escalate-on-3rd
threshold. **FIXME 0653 filed → /arch** (P24 corollary + helper-classification
sweep, S114). The S114 sweep's plan row MUST cite 0653 and the three W2a
instances as its seed register; MC-X2's `current_module` interaction note is
the same shape's fourth face (carrier keyed by caller-module instead of the
resolved home) — cite it there too.

(The one-sentence calibration for the `tests/CLAUDE.md` §"Coverage by
definition variants" text itself is flagged to /testing in the W1 brief —
that file is /testing-owned; the normative record is this section + the S112
plan §12.)

**"Safety operation elided by a static analysis, verified by example"** (the
§4 rolling audit): this sprint's sweep surfaces = the W5 landings (each
diagnostic mode's self-test proves the lane sees a planted fault; the R4
mint census + R6 trust census rows land as register updates, not tests) +
the 0637 row discipline (validation co-lands with the first consumer — do
not audit it green by absence).

## 7. Batteries and registers (FIXME dispositions actioned here)

| Item | Disposition |
|---|---|
| RG-P24 (was FIXME **0632**) | Fully actioned → **deleted 2026-07-19**. All three asks live in `tests/plan/s111-principle24-register.md`: §1 transcribes the criterion VERBATIM from `principles/24-resolve-once.md` (acid test, both carve-outs, enforcement clause); §2.1 cites the backend-DONE leg from `audits/cranelisp-backend-s110.md` §2.1 (not redone) + closes primitives/intrinsics/platform on the zero-hit grep + records the pre-seeded `jit.rs:117` row (last-write-wins platform registration; /qa lean recorded: structural tie-error). OPEN legs remain register-tracked: leg 3 (frontend) is carried by **this sprint's /audit rotation** (dispatching W3-parallel — its findings append to the register per §2.3); legs 1–2 (typecheck, int) stay open register work, S114 scheduling candidate. The P26 carrier→pass→window classification sweep (SPRINT chunk F) is /design's; its findings also append here |
| RG-DG (was FIXME **0633**) | Fully actioned → **deleted 2026-07-19**. Reachability record: `s111-0633-adt-drop-glue-underkey.md` (REACHABLE, both axes). Committed battery: `tests/adt_drop_glue_underkey.rs` DG-R1a/b/c (RED, the durable triggers). False guard CORRECTED (S111 — `resolution/tests.rs:128` now states the predecessor's false assertion in past tense). Residuals routed: module-axis cell re-author = MS-P4; re-key fix = W5 R4 register row (/dev backend); the canonized-claim design correction = the W5 `/design`(backend) §6-task-2 census re-verifies `audit-drain-s111.md` §4's keying statements. Per the no-FIXME-with-failing-test rule the REDs are the record + trigger |
| FIXME **0638** | **DELETED (W1, 2026-07-19)** — the §1.5 condition met: /testing landed `tests/macro_expansion_interior_alias_double_free.rs` (RED ×3 modes, `class=uaf owner=/dev`, src marshal/invoke seam). The failing pins are the record + trigger; attribution stands per PLAN §S111 I.4 |
| FIXME **0604** | Kept open, updated: W4 rider (PS-R7) is the plan of record; /qa consumes the named seam when it fires |
| FIXMEs **0637/0641** | Not /qa-targeted; ride W5 per the gate (0641 flips under the lane, strategy §1.5; 0637 co-lands with its first consumer) |

## 8. Traceability

- `spec/07-traits.md` §7.11.2 `[S113]` markers (+ §7.3.5:250 declaration-side
  line): flip to `[Tested …]`/`[Tested+Neg …]` at W2 close (F-D2 rows).
- `spec/05-definitions.md` §5 binder-principle bands: flip at W3 (BD rows).
- `repl/spec.md` §15.4 persisted-content rows: flip at W4 (PS-RT4 matrix).
- Run `plan/spec_link_check.py` + `plan/spec_coverage_reconcile.py` before
  landing any annotation flip; re-run at Phase 6.
- Suite-delta expectation for Phase-6/7 audit: W1 adds intended REDs (F-D2-1
  re-point stays RED, F-D2-2 inversion goes RED, F-D2-5/7 RED, binder-matrix
  new cells RED, 0638 RED) and the W2/W3/W4 waves flip the 14 S112-pinned
  REDs family-by-family; the 11 pre-S112 durable carries (memory-safety
  family + ownership_reuse + deftype silent-accept) flip only via W5 per the
  gate. Zero unattributed REDs at every wave close.

## Next skills

- `/testing` (W1): author §1 in full + the detachable §2 slice per the W0
  user ruling; sweep tables (F-D2-3, §1.3) in the W1 report; delete 0605 on
  gate landing; delete 0638 on §1.5 landing.
- `/design`(typecheck): MC-D3 call-chain evidence BEFORE the fix; the W5 §3
  frame per the depth ruling.
- `/dev`(typecheck, W2): flips per §3; MC-E1 sequencing note is binding.
- `/sprint`: the W0 gate presentation (`s113-risk-assessment.md` §2–§3 is
  the artifact); MC-X1 confirms the carrier-sweep trigger fired.
