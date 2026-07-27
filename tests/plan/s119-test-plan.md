# Sprint 119 QA plan — the non-concrete release contract, and the typed consume funnel

**Status:** Phase 3 plan of record
**Authority:** `/qa`; `/testing` authors e2e sources (Phase 5 stage 1, QA-first,
to these rows); narrow `/dev` owners author unit tiers beside their seams
**Baseline evidence:** full run 2026-07-26 at `5520186d`, clean tree —
5,660 run / 5,639 passed / 21 failed / 1 skipped; every RED attributed, zero
untraced (`sprints/SPRINT.md` §Baseline)
**Binding architecture inputs:** `sprints/SPRINT.md` §Architecture review
(the G1–G6 gate table, the two spines, the must-not-interleave list);
`design/arch/ownership-stratum-options.md` (as amended `3232a061`); FIXMEs
0903 (incl. the acceptance addendum), 0907, 0913, 0916, 0917, 0889;
`tests/plan/s118-test-plan.md` §11 (the P6/W8 dispositions this plan inherits)

**The plan's one binding property (dispatch directive): every gate G1–G6 has a
named cell or a named measurement.** §2 is the gate→instrument map; a gate row
with an empty instrument column is a Phase-3 exit blocker.

## 1. Certification split and the 21-RED baseline contract

### 1.1 Certification split (unchanged in meaning — see §5.5)

Two independent verdicts, exactly as S116/S118 established:

1. **Deterministic suite — UNARMED.** Full `cargo nextest run --no-fail-fast`
   with no detector variable at suite scope, ever; arming is per-subprocess
   `.env(…)`/`env_clear` only (`s118-test-plan.md` §1's structural enforcement
   stands: the static arming gate, the `/review` reject, the
   `detector_arming_discipline_guard`). Exit contract: two consecutive complete
   captured (`tee`'d) runs with identical failure sets, empty except explicitly
   user-approved carries recorded at close.
2. **Load-dependent — separate.** `launch_grid_corrupt::…` certifies separately
   (S118 §5.1 criteria); never folded into the deterministic scalar. The named
   flap set reports beside the exact count, **both polarities** (should-be-GREEN
   failing under load AND should-be-RED passing under interleaving — the 0694
   S118 roster rule). Intended-RED colors are verified **per binary**, never
   from an interleaved multi-binary run.

### 1.2 Baseline enumeration and flip attribution

The 21 REDs at open are **20 stable certified carries + 1 named-flap-set
member observed in the opening run** (the counting convention keeps the flap
member out of the exact scalar; it is listed here because it was RED in the
one run that defines the baseline).

| # | Cells | Defect | Flips at |
|---:|---|---|---|
| 1–3 | `spec_10_io::{io_internal_ctors_stay_excluded_from_exhaustiveness_neg, match_arms_all_io_pure, pure_pattern_accepted}` | 0907 | Spine-1 implementing wave (IO face) |
| 4–5 | `ctor_as_value::{bare_ctor_as_map_io_function_run_and_link, bare_ctor_through_race_map_io_run_and_link}` | 0907 | Spine-1 implementing wave |
| 6 | `examples::every_example_runs_with_documented_exit` (21-hello-io, 23-io-sequence) | 0907 | Spine-1 implementing wave |
| 7 | `stdlib_conformance::stdlib_all_public_modules_compile_and_run` (`core.io/when-io`) | 0907 | Spine-1 implementing wave |
| 8–9 | `nullary_arm_beside_boxed_arm_0917::{…_frees_its_loop_under_run, …_under_link}` | 0917 | Spine-1 window, distinct axis (provenance classification) |
| 10 | `exemplar_ownership_residue_s116::sudoku_warm_serial_solve_residue_at_most_1400` | 0917 (re-attributed S118 §11.8.1) | Spine-1 window (0917 fix); then re-derived per §5.3 |
| 11 | `trait_scrutinee_scalar_payload_0916::trait_method_instance_does_not_rc_a_scalar_payload_as_a_pointer` | 0916 | Spine-1 implementing wave (family-2 unsafety) |
| 12 | `residual_type_param_result_leak_0913::unannotated_result_turn_releases_like_its_annotated_twin` | 0913 | **Rider 3** (implementation) — NOT the contract face |
| 13–15 | `spec_field_accessor::{concrete_constructor_arm_product…, polymorphic_product…, sum_type_variant_field…}_mints_canonical_and_unique_bare_accessors` | 0867 | Rider 1 — only after the accessor-family disposition |
| 16–17 | `spec_11_stdlib::{def_definition_echo_names_user_binding_not_internal_thunk, def_info_and_sig_describe_bound_value_not_macro}` | 0863 | Rider 7, conditional (§Open items ①); else S120 carry |
| 18 | `cache::cache_restored_parent_enrols_private_test_child` | 0868 | Rider 2 |
| 19 | `cache::cache_restores_sibling_written_trait_impls_for_dispatch` | 0869 | Rider 2 (schema 23→24 window) |
| 20 | `launch_grid_corrupt::launched_strand_grid_get_assoc_does_not_corrupt_heap_neg` | 0694 family, load-dependent | carried; Track C bounded obligation only |
| 21 | `nullary_return_dispatch_method_only_import::…_no_codegen_leak` | 0694 named flap member (Class II) | flap set — not in the exact scalar; Track C §8 |

Floor (spines only): 20 stable → **9 stable** (+ launch_grid) — matching
SPRINT's 21→10 with the flap convention applied. Ceiling (all riders): → **1
stable** (launch_grid) + the flap set.

### 1.3 Exit reconciliation discipline (S98 rule, binding)

Phase 7 reports name-for-name: each cell GREEN with its flipping change-set
named, or an explicit user-approved carry. A cell that goes green **without**
its owning fix landing is suspicion, not closure — the flip must trace to the
mechanism change-set. Two standing instances inherited open from S118:
0688's cure-vs-unreached question, and 0782's "mechanism live in CLIF,
cell green-by-latency" record (closes only with fix + one-release IR
evidence). A RED that flips during a byte-identical-by-design wave
(tranche-A churn, S0/S1-style slices) re-opens attribution.

## 2. The gate→instrument map (the plan's spine)

| Gate | Named cells / named measurements | Where specified |
|---|---|---|
| **G1 — release-contract totality** | (a) the **16-program corpus manifest** asserted per §3.2 (enumerated names, per-wave focused-run record, `/review` reject); (b) baseline flips #1–7 (0907), #8–10 (0917), #11 (0916); (c) the **family-1 accessor marginal guard** + the **IO-Bind balancing marginal guard** (§3.3, stage-1 authored, RED); (d) the `f4_sudoku.clif::user::Grid.cells` scoped attributed re-baseline **in the implementing change-set** (0903 addendum); (e) the 0891 three negatives re-land RED→GREEN (§3.5); (f) producer face: the fabricated-`ConcreteType::Int` prohibition pinned per §3.4; (g) **the R11 negative set (§3.7, the user's negative-coverage finding)**: the universal slot-gate sweep NC-1 (I-CONC, four-fn form per FIXME 0930; groups 2–3 pre-declared S120 carries) + the I-ABI roster pin NC-R + the 0926 P-1 unit gate cell, the fabrication census NC-2 (families A + B), the accessor 1023/1024 boundary repro NC-4 (stage-1, RED), and the declaration-channel sweep NC-5 (the CtorMeta channel NC-1 cannot see) | §3, §3.7 |
| **G2 — mechanism count stays one** | (a) `drop_glue_legacy_emitter_fence` stays GREEN through every wave; (b) the new **emission-licence census cell** (§3.6): admission-variant set, `Rejected` call-site count, and `protect_return_value` call-site count pinned to the ruling's numbers — a new licence arm cannot land without touching the census in the same change-set; (c) `/review` reject criterion (arch ruling) | §3.6 |
| **G3 — raw-handle representability** | (a) before/after counts recorded in the tranche-A change-set: `consume_*` raw-`i64` signatures 36→0; non-extern `i64`-heap-handle declarations 136 → 136 − (exact tranche-A slice, enumerated); (b) structural census cell: zero `consume_*` fn taking raw `i64` (§4.2); (c) 83 extern shims byte-identical: `public-api.txt` diff (extern lines unchanged) + `facade_compliance` + `public_api_relocations` GREEN | §4.2 |
| **G4 — prose-contract elimination** | (a) shim-fact single-sourcing **unit row**: every shim's `Owned`/`Borrowed` signature derived from (and conflict-checked against) the declaration table — one derivation (§4.3); (b) per-tranche **drop-bomb detection proof**: positive plant (undischarged `Owned` → debug bomb fires, located) + clean control + recorded fail-on-revert (0768 rule) — one triplet per tranche (A, B-int) (§4.3) | §4.3 |
| **G5 — instrument truthfulness** | (a) unit-tier marginal helper + its own detection proof (§5.2); (b) the lens rule normative in §5.1 (and folded to `PLAN.md` at Phase 6/7); (c) 0890 re-derivation record §5.3–§5.4: warmed-pair harness mode + its capability cells + cell #21 threshold retirement post-0917; (d) the option-2 measurement recorded with its method (§7) | §5, §7 |
| **G6 — 0889** | the **0889 exact-value pins** (`macro_turn_marshal_leak_0889.rs`): re-derived to **zero** in tranche B-int's implementing change-set — or, if B-int is cut, an explicit recorded carry with the pins standing at their documented values (they are GREEN either way; the branch is recorded, never silent) | §4.4 |

Cross-cutting acceptance for both spines: **the S118 instrument set re-runs
byte-identically across churn** — enumerated as: the marginal capability fence,
the 0889 pins (pre-B values), the armed-lane detector rows, the RE-1 fences,
and every baseline RED's failure signature. This is the acceptance criterion
for churn masking behaviour change, not a nicety (SPRINT §Spine-2 acceptance).

## 3. Spine 1 rows — the non-concrete release contract

### 3.1 The five faces, and what checks each

| Face | Contract disposition (design's to rule) | The check that makes it real |
|---|---|---|
| Ctor templates | ruled (§4.1/I-CT) — sound | 0903's §10-row-4 positive/edge cells (landed S118, stay GREEN); the re-landed negatives (§3.5) |
| Synthetic accessors (generic / undeclared-field products) | one of the four legal outcomes | family-1 marginal guard (§3.3); `Grid.cells` static re-baseline; corpus manifest §3.2 |
| Generic trait-method instances | must close the **wild-write** face, not only the leak (0903 addendum) | 0916 cell #11 flips; its two GREEN boundary controls (n=1023, plain-defn 400k) stay GREEN; family-2 leak polarity via the 0916 file's balance assertions + cell #10 |
| IO existential `Bind` | one of three directions on file; **admission exclusion restores the silent leak and is weighed as such** | 0907 cells #1–7 flip; the IO-Bind **balancing** marginal guard (§3.3) stays the fence against refusal→silent-leak |
| Lenient-view result root (0913) | producer prohibition: no fabricated concreteness | §3.4; cell #12 flips at rider 3, not at the contract |

0917 rides the same window as a **distinct named axis** (concrete types;
provenance classification — nullary `ConstrADT` joins Fresh). Its fix must not
add a licence arm: the §3.6 census must stay green through it.

### 3.2 The G1 corpus gate — asserted, not assumed (the plan's highest-value row)

The S118 §4.1 ruling bound before measurement and was falsified by 16 corpus
refusals (FIXME 0903). The assertion form for S119, in three layers:

1. **The manifest is enumerated by name.** The 16-program corpus is exactly the
   16 tests FIXME 0903 lists, all GREEN at baseline:
   `spec_03_types::{applied_annotation_bare_var_corefers_param,
   applied_annotation_bare_var_pins_through_ctor,
   defn_param_free_var_nested_in_applied_type,
   defn_param_multi_var_applied_annotation, rank2_argument_applied_at_two_types_neg,
   single_poly_instance_used_at_two_types_value_restriction_neg,
   unknown_uppercase_type_annotation_nested_still_errors_neg}`;
   `spec_07_traits::{hkt_functor_impl_on_option_dispatches_via_match,
   hkt_impl_on_user_well_kinded_adt_dispatches,
   hkt_impl_pairing_head_qualified_resolves_to_slot1_trait_accepts_and_dispatches,
   hkt_impl_targets_bare_type_constructor_not_applied_form,
   qualified_hkt_impl_trait_reference_resolves_canonical_home_and_dispatches}`;
   `spec_field_accessor::{control_polymorphic_deftype_level_product_mints_both_accessors_green,
   control_same_name_constructor_arm_mints_both_accessors_green}`;
   `spec_04_expressions::fn_lambda_param_free_var_annotation`;
   `spec_05_definitions::deftype_product_shortcut_field_names`.
2. **Measure-before-binding (design window).** The co-ruling does not bind until
   the corpus run — the 16 above, plus the full `spec_*` corpus as the wider
   screen — is executed against the candidate gate *inside* the design window
   and its per-program result table (compiles/refuses, before/after) is recorded
   in the ruling document. A ruling without that table is not a ruling
   (SPRINT §Sequencing 1). This applies **identically to each severed piece**
   if the fallback order fires.
3. **Standing assertion (implementation waves).** Every Spine-1 implementing
   change-set's acceptance includes a focused run of the manifest —
   `cargo nextest run --no-fail-fast -E 'binary(spec_03_types) + binary(spec_07_traits) + binary(spec_field_accessor) + binary(spec_04_expressions) + binary(spec_05_definitions)'`
   — with the 16 names GREEN, recorded (tee'd) in the change-set. A missing
   record is a `/review` REJECT. At Phase 7, the full-suite run re-verifies
   (the 16 are ordinary committed cells; a refusal regression is an untraced
   RED and blocks close by the standing rule).
4. **Corpus extension after rider 1.** 0867's fix mints accessors for every sum
   type and distinct-name product — it *widens family 1's surface* (the reason
   it is gated behind the disposition). When rider 1 lands, the three
   `spec_field_accessor` 0867 cells join the manifest and the focused run is
   repeated for any Spine-1-adjacent change-set landing after them.

### 3.3 Stage-1 authored guards (`/testing`, QA-first, before the implementing wave)

All marginal-pair form (§5.1), failing-not-ignored, `// spec:` +
`// defect:` per convention:

- **Family-1 accessor leak guard** (owed since S118 §11.2): subject invokes a
  synthetic accessor of a generic product (`(deftype (Box a) [:a v])` shape)
  and of an undeclared-field product (`(deftype Pair [first second])` shape) in
  a loop; control differs only in reading the field by `match` destructure.
  Expected RED (silent shallow release leaks today). Flips at the Spine-1
  implementing wave. `--run` + `--link` faces.
- **IO-Bind balancing guard** (the refusal→leak fence): subject runs a bind
  chain over heap payloads (once 0907's fix makes it compilable); control
  differs only in the bind. Authored stage 1 **against the ruled direction**
  once the design window closes — if the ruling takes admission-exclusion, this
  guard is the cell that would go RED on the restored silent leak, which is
  exactly why it exists. Until the fix lands the subject program is refused;
  the cell asserts the refusal is GONE **and** the balance holds, so it is RED
  today on the refusal and stays RED on a leaking "fix".
- **0915 frame guard** (deferred from S118 §11.8.4): the §5.5
  error-frame-presentation guard, authored **in the fix window** against
  whatever codegen-refusal trigger remains after 0907 (or a constructed one) —
  `[S119]` row, not a stage-1 cell, because every current trigger dies with
  0907's fix.
- **The accessor boundary repro NC-4** (§3.7) — stage-1, RED today
  (SIGSEGV 139 on the subject). The cheapest memory-safety cell in the
  non-concrete class; it was reproducible from S84 and is unguarded at
  baseline.

### 3.4 The producer face (0913 contract half)

The contract binds producers: no fabricated concreteness. Checks:

- The typecheck co-ruling (Round 2) names the seam
  (`MonoExpr::lenient_from_expr` / the lenient view) and the prohibition.
- `/dev`(typecheck) unit row at implementation: the lenient view never
  fabricates `ConcreteType::Int` for a residual-parameter result — a
  constructed lenient-view instance over an unannotated `(Err x)`-shaped
  result asserts the non-concrete classification reaches the release seam
  (polarity: the pre-fix behaviour is the RED).
- The e2e flip is cell #12 (rider 3). **Closure by pinning annotations in
  tests or docs is prohibited** (SPRINT): the cell's subject/control differ
  ONLY in the annotation, so an annotation-pinning "fix" cannot flip it —
  this is the structural reason the cell has the shape it has; `/review`
  verifies no test-side annotation edit rides the fixing change-set.

### 3.5 0891 paste + 0906 riders

- The 0891 re-land is a paste after the ruling: the implemented gate + the
  three held-back negatives from FIXME 0903 (§"The three negative cells") land
  RED→GREEN in the implementing change-set, re-specified only as far as the
  ruled disposition table differs from the S118 frame key.
- 0906 (nullary-skip guard fold): **scoped golden re-baseline, not
  byte-identical** — block-creation order swaps CLIF numbering. `/testing`
  re-captures scoped + attributed, citing the implementing commit range (the
  0908 discipline), never blind. Any teardown-level loss in the diff is a
  finding, not drift (the S118 `Grid.cells` lesson).

### 3.6 The G2 emission-licence census cell (mechanical form)

`/testing` authors one structural cell in the Spine-1 implementing wave
(precedents: `mode_gating_guard`, `drop_glue_legacy_emitter_fence`, 0903's
negative #3), pinned to the landed ruling's numbers:

- the admission enum's variant set is exactly the ruled set (named variants,
  count pinned);
- `emit_heap_binding_decs(&to_dec, …Rejected)` call-site count pinned;
- `protect_return_value` call-site count pinned (4 at baseline:
  `match_codegen.rs` ×2, `control_flow/lambda.rs`, `control_flow/launch.rs` —
  per SPRINT §Verify-against-source, corrected locus `rc_emission.rs:156`);
- the legacy-emitter grep-zero set stays absent.

Any new emission licence arm must touch this cell in its own change-set —
which is the visibility G2 demands. The 0917 fix is the first client: a
provenance *classification* correction leaves every census count unchanged.

### 3.7 The R11/R17/R18 negative set (user finding, Phase-5 amendment)

**Provenance.** User finding 2026-07-27: R11 sat graded `unconstructable` from
S84 to S119 with zero negative coverage, and the whole suite is green on all
four live fabrication sites because every cell asserts what should happen and
none asserts what must not. This section is the executable answer. Source
verification for this amendment (mine, at HEAD): the fabrication set is
**four** sites, not five — `fn_compiler.rs:1287` (`.is_err()` →
threshold-guessing branch), `ownership/fixpoint.rs:221`
(`unwrap_or(ConcreteType::String)` — carries an inline "never mis-classified
as Copy" soundness claim, unproven), `mono_expr.rs:836-841`
(`unwrap_or(ConcreteType::Int)`, the 0913 lenient view),
`drop_glue.rs:398` (`unwrap_or(ConcreteType::Int)` for a missing Vec elem
arg). Two sites are the CORRECT refusal pattern and are the models:
`program/support.rs:321` (explicit `NotConcrete` match) and
`types/heap.rs:310-334` (`ctor_field_concrete_types` — one `NotConcrete`
refuses the whole ctor via `Option` collect). `fixpoint.rs:221` and
`drop_glue.rs:398` appear in NEITHER design census nor R18's instance list —
register completeness routed to `/arch` as FIXME 0929. (Disposition
`f5d30808`: asks 1–3 discharged — R18 row extended to all five sites with
grades and owners, model sites named, census-as-enforcement accepted with
the residual graded asserted-with-a-named-falsifier once NC-2 lands; 0929
re-targeted `/design`(backend) as the CtorMeta carrier-ruling anchor.)

**Second finding (coordinator follow-up, verified at source): the
declaration channel, and Type-side laundering.** The backend has two type
sources. The body-AST path is `Var`-free by construction (`MonoExpr`, every
node `ConcreteType`); the OTHER channel is `signature_heap_category(ty:
&Type)` (`rc_emission.rs:478`, ~25 live call sites across `vec_codegen`,
`apply`, `match_codegen`, `lambda`, `par_bind`, `dependent_spark`,
`fn_compiler`), whose `Err(_) ⇒ Mixed` arm is R17's registered violating
seam. One of its feeders is structural, not incidental:
`context.rs:265-284` (`extract_constructor`) materialises
`CtorMeta`/`CtorField` from the ctor **declaration's** scheme, so a
polymorphic product's field type is `Type::Var(a)` **permanently** — a
declaration is polymorphic by nature; monomorphisation substitutes at uses,
and nothing substitutes here. Consequences: (a) **NC-1 is structurally blind
to this channel** — it asserts over slotted entries' schemes, and even after
P-1 lands, `CtorMeta` is still built from the declaration, so NC-1 would be
GREEN while the wild-write channel stayed live — hence NC-5; (b) **R17's
end state depends on this seam**: the arm flip is gated on the census
reading zero, and the declaration channel generates permanent traffic for
every polymorphic-ctor field categorisation until it is closed. There is
also a **Type-side fabrication family** the NC-2 `from_type` pattern is
structurally blind to, because the fabrication happens BEFORE the boundary
and then *passes* `from_type` — laundered concreteness:
`context.rs:280` (`unwrap_or(Type::Int)` when `field_count` exceeds the
scheme's params), `fn_compiler.rs:1214` (defensive dead arm — the preceding
filter guarantees `Some`; unreachable by local construction, still the
wrong spelling), and the int-layer result/display defaults
`src/eval.rs:586`, `src/repl/commands.rs:632`, `src/pipeline.rs:133` (the
fabricated `Int` flows toward the result-release protocol — severity
ungraded). All routed into NC-2 family B + FIXME 0929's extension.

- **NC-1 — the universal slot-gate sweep** (`/dev`(typecheck) unit row,
  authored with CS-1; predicate re-ruled **target-universal** per
  `design/arch/total-concreteness.md` §2, invariant **I-CONC**; FIXME 0930).
  For EVERY symbol-table entry: `callable_got_slot().is_some() ⇒
  scheme.ty.is_concrete()` — whole-table, kind-free. Authored as ONE walk
  asserted through FOUR test fns, so each violating population flips with
  its own fix (the failing-not-ignored convention, per-defect signal):
  1. `…_hand_mints` — the two `UserFn` hand-mints (synthetic accessors,
     residual trait-impl methods) — **RED, flips with CS-1/P-1 this
     sprint**; still the population that would have been RED from S84.
  2. `…_ctor_templates` — every generic-ADT ctor template: user `deftype`
     generics + the bootstrap seeds (`Option.Some`, `Result.Ok/Err`,
     `Pair.MkPair`, `SList.SNil/SCons`, `IO.Pure/Effect`) + `IO.Bind` —
     **RED against FIXME 0931** (S120 ctor-monomorphisation tranche;
     pre-declared close carry, see §11.8). The S119 face-1/I-CT′ work
     proceeds unchanged and does NOT flip this group — `Constructor` slots
     are mandatory fields today, ungated by P-1.
  3. `…_vec_len` — the ONE slotted polymorphic primitive in the system —
     **RED against FIXME 0932** (S120 de-slot; pre-declared close carry).
  4. `…_no_unattributed_violations` — **GREEN**: any violation OUTSIDE the
     three named populations fails here, immediately. This fn is the
     durable universal sweep — as groups 1–3 flip, it alone carries
     I-CONC.

  Fixture: the full bootstrap table + a user polymorphic product with
  synthetic accessor + a generic trait impl + concrete controls. In-fixture
  negative controls proving the sweep does NOT fire on slot-less
  polymorphism: `vec-get`/`vec-set`/`vec-push` (`PrimitiveBody::Inline`,
  slot-less by construction) and the four NC-R roster externs. The reverse
  direction (concrete determined `UserFn` ⇒ slot) stays behaviourally
  enforced by the missing-slot hard failure and is NOT asserted here. The
  FIXME-0926 gate cell is the site-naming sibling for group 1. **Row
  history, kept deliberately:** between 2026-07-27 and 2026-07-28 this row
  carried a kind-partitioned licence table (`f5d30808`) built on the claim
  that `bind` and `catch-runtime-error` are polymorphic slotted primitives.
  The claim was **false at source** — both are slot-less
  `DefKind::PrimitiveExtern`, `callable_got_slot() → None` structurally
  (`src/bootstrap.rs:884-905`, `:1129-1160`;
  `crates/cranelisp-types/src/module.rs:1446-1471`) — and it propagated
  unverified through three hands before `total-concreteness.md` verified
  it. The lesson is root `CLAUDE.md` §Assurance applied to our own
  artefacts: a slot-status claim is a claim about source, checked at source
  before any row is amended over it. The partition table is superseded; do
  not resurrect it. **Known blind spot, by construction:** NC-1 quantifies
  over slotted entries' schemes and cannot see the backend's
  declaration-materialised `CtorMeta` channel — that is NC-5's job; the two
  are a pair, not alternatives.
- **NC-R — the I-ABI roster pin** (NC-1's partner cell; unit row,
  `/dev`(src) beside `src/bootstrap.rs`, stage-1, GREEN at author time).
  The slot-less polymorphic by-name callable roster is a **closed set**
  (invariant I-ABI, `total-concreteness.md` §3.3): the primitives-table
  entries with `DefKind::PrimitiveExtern` and a non-concrete scheme are
  exactly {`bind`, `race`, `select`, `catch-runtime-error`}. A fifth member
  REDs the cell until declared — in the cell AND the roster doc, with its
  representation dependencies recorded. That roster is the re-visit list
  when `--release` layouts specialise, which is why it is a cell and not a
  comment: a silent fifth member is precisely the class of quiet exception
  that kept R11 false for thirty-five sprints. Authored NOW, not with 0932
  — the silent-addition hazard exists today; if 0932 chooses spelling (b),
  `vec-len` joins the pin in that change-set (the §3.6 census mechanics).
  Detection proof per 0768: a planted fifth member REDs, recorded,
  reverted.
- **NC-2 — the fabrication census** (`/testing` structural cell, Spine-1
  implementing wave, §3.6 mechanics; precedent
  `drop_glue_legacy_emitter_fence`). Grep-shaped over non-test source: every
  discard-and-substitute of `ConcreteType::from_type` (`unwrap_or…` /
  `.ok()`-then-default / `.is_err()`-branch-to-guess) must be on the pinned
  allow-list, each entry carrying its open-defect citation:
  `fn_compiler.rs:1287` (R18), `fixpoint.rs:221` (0929),
  `mono_expr.rs:836-841` (0913/R18), `drop_glue.rs:398` (0929). The two
  refusal-pattern model sites are named in the cell's rustdoc as the correct
  spelling. A NEW discard site REDs the cell in its own change-set; each fix
  shrinks the pin in the fixing change-set. Detection proof per 0768 in the
  authoring change-set: a temporarily planted discard site REDs the cell,
  recorded, reverted. **Family B (Type-side laundering, same cell, second
  pattern):** `unwrap_or(Type::…)` / `unwrap_or_else(|| Type::…)` in
  non-test source — fabrications that never meet `from_type` as an `Err`
  because they fabricate BEFORE the boundary and pass it after. Pinned
  allow-list at author time, every entry citing 0929:
  `crates/cranelisp-backend/src/compiler/context.rs:280`,
  `crates/cranelisp-backend/src/compiler/fn_compiler.rs:1214` (dead arm —
  filter-guaranteed `Some`; correct spelling is `expect`/`filter_map`),
  `src/eval.rs:586`, `src/repl/commands.rs:632`, `src/pipeline.rs:133`
  (int-layer result/display defaults; severity ungraded — 0929).
  `infer.rs:1290`'s `Type::Var(0)` fallback is out of this family's scope
  (it fabricates a *variable*, not concreteness) and is not pinned.
- **NC-3 — per-site fail-on-revert unit rows** (one per fabrication, riding
  each fix — the enumerated-deferral discipline, so unit-test-per-fix has
  named targets): (a) `fn_compiler.rs:1287` — covered by R17's census + arm
  flip (release contract §5.1); its unit row asserts the located error, never
  the guess branch; (b) `fixpoint.rs:221` — pending the 0929 grading: either
  the arm gains its Principle-25 check (unit row: a residual-typed param
  never seeds below the graded conservative point) or is registered
  legitimate-with-proof and moves to NC-2's model list; (c) `mono_expr.rs` —
  already §3.4's row, unchanged; (d) `drop_glue.rs:398` — unit row: a Vec
  glue request with missing/residual elem arg refuses with a located error,
  never mints Int-elem glue.
- **NC-4 — the accessor boundary repro** (`/testing` e2e, stage-1, RED
  today). The release contract's §2.4 four-line program, `PrimitivesOnly`,
  `--run` + `--link` faces:
  `(deftype (Bx a) [:a v])` / `(defn get [b] (v b))` /
  `(defn main [] (Pure (get (Bx 1024))))`. Subject: payload **1024** exits 0
  with NO signal — RED today (SIGSEGV 139, the `NULLARY_TAG_THRESHOLD`
  boundary). Controls, both GREEN today and staying GREEN: payload **1023**
  exits 255; payload `"hi"` exits 0 — the String control documents WHY the
  suite stayed green for 35 sprints (every heap-typed instantiation passes;
  only scalar payloads ≥ 1024 take the wild write). `// spec:` +
  `// defect: class=scalar-as-pointer
  locus=crates/cranelisp-typecheck/src/adt.rs::synthetic-accessor-mint
  found=S119 owner=/dev(typecheck)`; traces to FIXME 0924 / R11. Joins the
  §1.2 accounting as a stage-1 authored guard; flips at the Spine-1
  implementing wave. Its sum-arm sibling —
  `(deftype (Mb a) Nn (Jj [:a v]))`, payload A/B at the same boundary — is
  the 0926 §1 shape: authored RED-then-GREEN **inside 0867's change-set**
  (rider 1), because 0867 is what makes that surface reachable.
- **NC-5 — the declaration-channel sweep** (`/dev`(backend) unit row,
  RED-first, Spine-1 window). The invariant at the seam, stated
  design-neutrally: **no heap-category decision is made off a residual
  field type materialised from a declaration.** Cell: build a symbol table
  containing a polymorphic product `(Bx a)` (and a concrete control); call
  `ctor_meta_at`; assert every materialised `CtorField.ty` satisfies
  `ConcreteType::from_type(..).is_ok()` OR the materialisation refuses /
  demands an instantiation (however the ruling spells the legal path) —
  RED today (`field_types[0]` is `Type::Var(a)`, permanently). Second
  polarity, the fabrication arm: a ctor whose `field_count` exceeds its
  scheme's params must refuse with a located error, never mint
  `Type::Int` (`context.rs:280`). Routing under the `f5d30808` split: the
  **derivation seam is RULED** — ctor field-type materialisation for
  category/glue purposes delegates to the types-owned refusing projection
  (`heap.rs::ctor_field_concrete_types`) or an instantiation-substituting
  sibling landed beside it in `heap.rs`, never `context.rs`'s hand-rolled
  `scheme.ty` walk — so NC-5's flip criterion gains a structural leg: the
  fixing change-set retires the hand-rolled walk (grep-shaped pin: zero
  field-type derivation from `scheme.ty` in `context.rs`), and the
  behavioural leg (concrete-or-refuse at `ctor_meta_at`) goes GREEN through
  the delegation. The **carrier shape** (`CtorField { ty: ConcreteType }`
  vs instantiation-keyed materialisation — backend-interior, `pub(crate)`)
  remains `/design`(backend)'s to rule inside the release-contract window
  (FIXME 0929, re-targeted `/design` as the anchor); this cell asserts the
  invariant whichever carrier is chosen. R17 sequencing under the
  `total-concreteness.md` re-ruling: **the arm flip becomes reachable at
  the S120 ctor tranche** (FIXME 0931 — non-concrete templates stop
  compiling, so the census can finally read zero on the polymorphic-ctor
  families); NC-5 is the seam guard that holds the derivation honest until
  and through that tranche.

**Structural-closure note (for the record).** `ConcreteType`'s variants are
`pub`, so `from_type`'s "ONLY way" rustdoc claim is true of conversion but
unenforced against direct literal construction — and every live fabrication
IS a direct literal in `unwrap_or` position, which NC-2's pattern covers.
Full structural closure (sealed variants) would break legitimate exhaustive
matching across the backend; the recommendation to `/arch` in FIXME 0929 is
census-as-enforcement with the residual graded
asserted-with-a-named-falsifier, not a sealing change.

## 4. Spine 2 rows — the typed consume funnel

### 4.1 Instrument invariance (the tranche acceptance frame)

Spine-1 backend implementation and tranche-A signature churn never share a
wave (arch must-not-interleave). Each tranche's acceptance re-runs the §2
byte-identical set; the tranche is behaviour-neutral by design, so **any**
delta — a RED flipping, a marginal moving, a pin drifting — re-opens
attribution rather than counting as a win.

### 4.2 Tranche A (G3)

- Before/after counts recorded in the change-set: 36 `consume_*` call sites →
  0 raw-`i64`; the exact internal-declaration slice enumerated (which of the
  136 flip in A; the remainder are C's, named as pending).
- `/dev` structural census (unit tier, in-crate): zero `consume_*` signatures
  take raw `i64`; `Owned` is `#[must_use]`, not `Copy`/`Clone`; `Borrowed` is
  `Copy` with `.to_owned()` the single `rc_inc` home (grep-shaped pins at the
  seam, the 0903-negative-3 pattern).
- ABI byte-identity: extern names and signatures unchanged —
  `crates/cranelisp-{intrinsics,primitives}/public-api.txt` regenerated in the
  same change-set with the extern surface byte-identical; `facade_compliance` +
  `public_api_relocations` GREEN. The approved public delta is confined to the
  `Owned`/`Borrowed` vocabulary + changed `consume_*` signatures (arch §Risk).

### 4.3 Tranche A (G4)

- **Shim-fact single-sourcing unit row** (part of tranche A's design, not a
  follow-on): one derivation from the primitives declaration-table ownership
  facts to the shim annotations, conflict-checked — a unit test walks the
  table and asserts every shim signature matches its declared fact; a false
  edit to either side REDs it. This is the §2.2 false-confidence mitigation;
  the trusted base narrows to this row plus the newtype impl.
- **Drop-bomb detection proof (per tranche, 0768 rule).** Triplet at the
  production funnel: positive (a deliberately leaked-on-the-floor `Owned` in
  debug profile → bomb fires naming the frame), clean control (discharged →
  no fire), fail-on-revert recorded (disabling the bomb makes the positive
  FAIL). An instrument is unverified until proven to detect; a typed layer
  landing with zero executing consumers is the S118 named hazard — the bomb
  proof plus the 36 flipped call sites are the executing consumers.

### 4.4 Tranche B-int (G6) and the 0889 pins

- `/design`(int) rules the macro-turn ownership protocol **before any `/dev`
  dispatch** (0889's own precondition). No `cranelisp-types` delta.
- **G6 named cells:** the 0889 exact-value pins in
  `tests/macro_turn_marshal_leak_0889.rs`. Branch A (B-int lands): the pins
  re-derive to **zero** in the implementing change-set — the same-change-set
  re-derivation IS the acceptance; the marginal instrument stays valid
  unchanged (the common term goes to zero). Branch B (B-int cut — the first
  structural drop if capacity binds, §Open items ②): the pins stand at their
  documented values, GREEN, and the carry is recorded explicitly at close.
- The 0638 interior-alias history is the standing caution: the tranche's
  thesis is that the danger *is* the miscounting typed handles remove; the
  acceptance evidence is the pins at zero **plus** no new double-free face
  under the armed lanes (M1/M2 armed acceptance legs in the fixing wave, the
  S118 §4.1 armed-acceptance pattern).
- 0863 never interleaves with B-int (same `src/` macro-turn seams).

### 4.5 R8's standing lane (FIXME 0761 — the trigger has fired)

The Track-B cells the S118 deferral waited on are GREEN. The standing
owning-type × position exact-balance lane lands this sprint in the §5.1
normative form:

- **Vehicle:** `tests/gen_ownership_flows.rs` — already the owning-type ×
  position harness (12 positions incl. the S118 eliminator rows). `/testing`
  reconciles its matrix against 0761's axes (let-bound local; borrowed
  argument temporary; returned through N ∈ {0,1,2} lets; TCO loop-carried
  param; closure-env capture; the matched positions) and fills gaps; both
  toggles; a `--link` face for the leak-vs-double-free polarity split.
- **Form:** absolute exact balance is legal here per §5.1(b) — the children
  are free-standing/PrimitivesOnly, macro-free — PROVIDED the binary carries
  one ambient-zero control (a trivial program through the same fixture,
  asserting absolute 0). Remaining `balance_exclusion` entries each carry an
  open-defect citation or are removed.
- 0761 is then actioned: the lane row folds into `PLAN.md` (§S119) and the
  FIXME deletes when the lane lands. Disposition appended to the FIXME this
  phase.
- 0779's decided candidate (1) — the `resolve_auto_curry` seam-polarity unit
  cell, `/dev`(typecheck)-owned — rides the S119 typecheck window (rider 1/3);
  row: `[S119]`, flip = the cell exists and is GREEN with fail-on-revert.

## 5. Option 3 — the normative-form proposal (paper §7 decision 5) and its riders

### 5.1 The proposal (mine to make; lane mechanics are plan-owned)

**N1 — e2e balance lanes.** Any e2e cell asserting allocator balance MUST take
one of exactly two forms:

- **(a) the marginal pair** (`helpers::marginal::MarginalPair`) — control and
  subject differing in **one named axis**, `env_clear` + enumerated allow-list,
  same drive for both halves, asserted quantity = the marginal residual
  (`assert_balanced` / `assert_residual(n)` with a documented closed form).
  Required whenever the child's ambient residual cannot be proven zero: any
  stdlib or macro-invoking prelude, any cold-cache compile-bearing child, any
  REPL session with a prelude.
- **(b) the degenerate absolute** — absolute `allocs == deallocs` over an
  ambient-free child, legal ONLY when the ambient-zero premise is
  **continuously executed** by a named GREEN control in the same binary (a
  trivial program through the identical fixture/env asserting absolute 0 — the
  warm-control pattern of `exemplar_ownership_residue_s116::warm_cache_hit_control_carries_no_ambient_residual`).
  A bare absolute cell with an unexecuted "the prelude is macro-free" premise
  is non-compliant.

**Thresholds are banned outright** for this class (already the
`tests/CLAUDE.md` rule; this proposal makes it the required form's negative
space). §5.3 executes the retirement of the last standing threshold cell.

**N2 — the unit-tier lens rule.** A unit row asserting balance **at one
sampled point** is the named anti-pattern (the decision24 blindness: the
sampled point is chosen by the same understanding that wrote the code). A
unit-tier balance row must assert one of:

- a **rate** — the residual is independent of a size axis (measure at ≥2
  values of `|input|`, assert the delta);
- a **tally** — the op count equals a closed form (`incs == |xs| + 1`, pinned
  against the rejected variant, per 0885);
- a **marginal** — delta-vs-control over the in-process RC/alloc counters
  around a closure pair built from ONE parameterised constructor differing in
  one named axis (the §5.2 helper).

Or it names the variant axes it samples and covers them as a matrix. `/review`
treats a new single-point balance row as an Important finding.

**Scope of the normative form:** all balance lanes — `tests/plan/` rows, the
R8 standing lane (§4.5), and every future leak/balance cell. `/arch` owns only
the register linkage (R8's row in `safety-invariants.md` §4 pointing at the
lane); I do not edit that file — the linkage request rides `/arch`'s rider-5
window (0918/0919) and needs no FIXME beyond this named handoff.

**One-axis discipline survives generalization** by construction, not review:
at e2e the harness constructs both children identically except the declared
axis; at unit tier the helper's constructor takes the shared setup once and
the axis as a parameter — hand-built control/subject closure pairs are the
non-compliant spelling.

### 5.2 The unit-tier helper (spec for `/dev`, per crate; first instance beside the intrinsics counters)

Small in-crate helper: `marginal_over(counters, |axis| …)` — snapshot the
RC/alloc counters, run control(axis₀) and subject(axis₁) closures built from
one constructor, return the marginal. **Its own detection proof is mandatory
before any cell trusts it** (0768): a planted single-op imbalance in the
subject closure must read exactly ±1; identical closures must read exactly 0.
The helper preserves N2's one-axis discipline in its signature.

### 5.3 Threshold-cell retirement (the census, and the worked instance)

Census at baseline: **exactly one threshold cell stands** —
`exemplar_ownership_residue_s116::sudoku_warm_serial_solve_residue_at_most_1400`
(grep over `tests/` finds no other `at_most`/`<= N` balance form). S118 §11.3
kept its threshold form deliberately while its residue was 0917-attributed;
0917 closes in the Spine-1 window, so the retirement executes this sprint:

- **After 0917's fix flips it**, `/testing` re-derives the cell in the fixing
  change-set's rider: warm absolute exact balance (`residual == 0`), with the
  already-landed warm-control leg as the executed ambient-free premise
  (§5.1(b)) — the S118 measurement showed warm absolute and marginal coincide
  (warm carries no 0889 term). The ≤1400 bound retires with the flip.
- If 0917's fix leaves a nonzero residue, that is a NEW attribution routed to
  `/qa` (the §4.4-S118 discipline) — never a re-derived threshold.

### 5.4 (moved to §6 — the cold/warm axis is 0890's record)

### 5.5 Does the proposal change the certification split's meaning? **No.**

Stated plainly, per the arbitration boundary: the split remains
deterministic-unarmed vs load-dependent, with the same exit contracts, the
same two-run identical-failure-set verdict, and the same named-flap-set
convention. Marginal pairs are ordinary deterministic cells (both children
spawned per-subprocess with per-child arming — already compliant with §1.1's
arming discipline); they fold into the deterministic scalar as named cells
exactly as absolute cells did. The proposal constrains the **form** of
balance cells inside the deterministic verdict; it does not create a third
verdict, move any cell between verdicts, or alter what "certified" asserts.
**Therefore no user arbitration is required for decision 5.** (If a future
generalization ever proposed certifying on aggregate marginal statistics
rather than named cells, THAT would change the split's meaning and would go
to the user; this proposal does not.)

## 6. FIXME 0890 — the cold/warm cache axis (record + S119 residue)

**Record.** The 0890 re-derivation was EXECUTED at S118 pre-gate
(`s118-test-plan.md` §11.3) and **inverted the FIXME's premise**: a successful
warm cache-hit child carries NO ambient 0889 term (two independent warm
controls measured exactly 0); the "~87% ambient" figure read cold arithmetic
into the warm cell. The FIXME file was actioned and deleted in that pass; the
`sprints/SPRINT.md` FIXME-table row listing 0890 as open is **stale** —
reported to `/sprint` in this phase's handoff (I do not edit SPRINT.md).

**S119 residue (what G5's "0890 re-derived" still owes):**

1. **Warmed-pair harness mode** (`/testing`, extending `helpers::marginal`):
   a per-child warm drive — populate the child's private cache with an
   identical priming run, then measure the cache-hit run — applied to BOTH
   halves identically (cold-then-warm, no `--no-cache` on the measured run;
   the private tempdir isolates the cache per child, the `link_then_run`
   precedent). This makes cache-restoration-path balance measurable
   marginally — the instrument the rider-2 window (0868/0869) wants.
2. **Capability cells for the mode** (0768 — the mode is unverified until
   proven): (a) warm identical children read marginal exactly 0; (b) the M3
   single-suppressed-dealloc plant is detected at one-block resolution in a
   WARM subject (the plant is runtime-side, cache-independent, so it
   discriminates); (c) the warm ambient-zero premise is pinned (warm
   full-stdlib control absolute 0 — the harness-level sibling of the landed
   exemplar warm-control cell).
3. **Cell #21's re-derivation** — §5.3 (the worked threshold retirement).
4. **Acceptance arithmetic, stated:** warm cells assert exact 0 marginal;
   cold cells carry the 0889 common term (which cancels in the pair) until
   tranche B-int lands, after which it is zero everywhere — no cell needs
   re-deriving at that flip (the marginal's standing property).

## 7. The option-2 measurement gate (report-only; the number, not the adoption)

**Sequencing:** after Spine-1 implementation lands; never sharing a wave with
tranche churn. A measurement against emission we are about to change is not
decision-grade for S120. Executed by `/testing` under this method; recorded as
`tests/plan/s119-option2-measurement.md` (mine to hold).

**Axis and its honest gap.** Subject = the conservative all-Owned lowering
(the R7 differential-oracle toggle, the permanently-reachable reference
semantics); control = current dev-tier emission. Same binary, same HEAD, same
tree, per-child env only. **Binding on decision-grade status:**
`/design`(backend) enumerates, in the report, the gap between toggle-off and
true option-2 uniform emission (emission special cases the toggle does NOT
govern — TCO carry-forward, scrutinee release gates, protect licences, as
post-Spine-1 built). Because toggle-off restores analysis-licensed ops while
keeping structural elisions, the measured cost is a **lower bound** on
uniform emission's cost; the report says so on its face. If the gap cannot be
enumerated cheaply, the report states that and S120 prices a prototype
uniform-emission flag before adoption.

**Workloads and quantities** (each: median of ≥5 repetitions, spread reported,
tee'd, HEAD + machine recorded):

1. **Exemplar warm serial solve**, driver loop N ∈ {1, 8, 64} (the `/port`
   S118 shape): wall time + RC_STATS op counts (allocs / incs / decs) —
   control vs subject. The op-count multiplier is reported beside the time:
   it is the S94-flagged term.
2. **Parallel/contention face:** the sanctioned on-demand contention benchmark
   (`tests/concurrency_spark.rs:823`, the suite's 1 skip) run explicitly under
   both emissions — the S94 ~10× floor-violation shape is exactly what the
   adoption decision must price.
3. **Suite face:** one full `cargo nextest run --no-fail-fast` with the toggle
   exported (it is not a detector variable; the arming ban does not apply),
   wall time vs a same-HEAD baseline run, **and the failure-set delta by
   name** — toggle-sensitive cells are data for the adoption decision, not
   noise. Run in a window `/sprint` allocates (one-agent-one-test-run).

**Deliverable:** the number(s) + method + gap enumeration + failure-set delta.
No adoption action this sprint under any capacity outcome (arch ruling).

## 8. Track C — the bounded obligation (0694 D1), the datum, and 0859

### 8.1 The D1 discriminating experiment (the only 0604/0818-family work this sprint)

Scope: FIXME 0694's D1 exactly, on the **nullary flap member** (the member
with fresh S119 evidence — baseline cell #21 of §1.2):

- Run the single test binary (`nullary_return_dispatch_method_only_import`)
  in isolation ~200× while the host carries equal CPU load from a
  **non-cranelisp** source (`stress`/`yes` on N−1 cores). Tee everything.
- **Reproduces** → host contention alone suffices; the fault is
  intra-subprocess interleaving; the shared premise holds; S120 proceeds to
  D2 Class-II (the MODULE_TRACE lane at the publication seam) with the rig
  validated. The captured failure output either matches the S115 signature
  (`undefined function: z`) — confirming Class II — or names a new face.
- **Does not reproduce** (while full-suite runs do) → the premise is
  **falsified**: other cranelisp subprocesses matter, pointing at
  inter-process shared state (cache dir, `CRANELISP_LIB`, tmpdir, cwd). D2/D3
  are re-designed, not run; the S118 inverse-polarity member
  (`cache::…written_trait_impls…` passing under interleaving) becomes the
  leading corroboration, and the rider-2 cache window gains a hazard note
  (its fixes touch exactly the suspected shared substrate).
- Either outcome is recorded in FIXME 0694 before any further 0694-family
  scheduling. Execution: `/testing`, in a `/sprint`-allocated run window
  (D1 is run-heavy; it must not contend with a fix wave's build slot).

### 8.2 The opening flap datum — recorded re-measurement

The member's reappearance at `5520186d` (unprompted, first S119 run, not in
S118's certified 20) is logged in 0694's roster this phase. The re-measurement
obligation: (a) isolation color at current HEAD (expected GREEN n/n — 
confirming the load-flap signature rather than a new deterministic
regression; a deterministic RED in isolation would be a NEW attribution, not a
flap datum); (b) per-run color captured across every full-suite run this
sprint (Phase 5/7 runs are all tee'd), appended to the roster. The flap set
reports at close beside the exact scalar, both polarities.

### 8.3 FIXME 0859 — disposition returned (its own §Future resolution, option 2)

The S118 close-gate item 5 ("dispositioned … or returned to the user — never
silently carried") went undischarged; discharged now, analytically:

**Disposition 2 is returned to the user, with a recommendation.** The S117
survey was competent and bounded-complete: every attempted production shape
(direct return, wrapper return, retained root, return adaptation, two-function
compositions) left `ProjectionOf(0) → Fresh` emission-inert, for the
structural reason recorded — materialisation makes every escaping heap element
an owned reference either way at the current language boundary. No S118/S119
surface changes that: Spine 1 rules the *release* of non-concrete values, not
projection provenance emission.

**Recommendation:** accept R-2 on the existing evidence (typecheck transfer
units distinguishing Projection provenance + the direct inline-body guards +
the nine production witnesses), **with a named revival trigger**: the moment
projection provenance becomes emission-live — ownership-inference increment
II's uniqueness/reuse tokens, or option-2 adoption re-staging elision into
`--release` under the differential lane — the declaration-sensitive witness
obligation revives automatically and is a plan row of that sprint. Until a
consumer exists, a witness cannot exist; manufacturing an observation surface
for it was already ruled out by the FIXME itself. Second-order support:
option-1's typed handles independently narrow the same risk class the
declaration table carries (the facts become representational at the pair's
seams). Disposition appended to the FIXME; it deletes when the user answers
(accept ⇒ delete with the trigger recorded in `PLAN.md`; designed-observable
wanted ⇒ re-target `/arch` for the seam design). Routed via `/sprint` with the
Phase-3 exit gate.

## 9. Rider rows (drop order; deepest last)

| Rider | Rows / checks |
|---|---|
| **1 — 0867** (`/dev` typecheck; **gated on the accessor disposition** — landing first manufactures unruled family-1 members) | flips #13–15; new positive+negative cells for the partial-accessor panic face (`(Option.unwrap None)` → runtime panic — untestable until minted); the duplicate-field negative family stays the §8.6.5 boundary fence; the `/stdlib` blast-radius rider: a cross-module `head`/`rest` contest cell over the 26-symbol surface — per FIXME 0926 §3 the cell's shape is ONE consumer module `[*]`-importing BOTH `collections.list` and `seq.lazy` (neither contest is intra-module, so §8.6.5 cannot fire and per-module `stdlib_conformance` structurally cannot see it); corpus-manifest extension per §3.2(4) **with the 0926 §1 sum-arm boundary sibling** (`(Mb a) Nn (Jj [:a v])` at 1023/1024, §3.7 NC-4) authored RED-then-GREEN inside this change-set |
| **2 — 0869 + 0868** (`/dev` src + types; the ONE schema window 23→24) | flips #18–19 (qualified + imported-bare variants for 0869); stale-cache rejection cell (pre-24 sidecar invalidates wholesale, no half-restore); idempotent re-enrollment (multiple restore paths, one shell); malformed/conflicting cached record → loud rejection; owner units (writer projection, restore enrollment, replay idempotence, rejection polarity); **0898/0748 riding**: the two hand-rolled `impl$` mint sites (`traits/dispatch.rs:143`, `traits/impl_check.rs:421`) re-pointed onto `trait_impl_key` — grep-zero hand-rolled `impl$` format strings; warmed-pair mode (§6) is this window's instrument |
| **3 — 0913 implementation** (after its contract face is ruled) | flips #12 under the §3.4 no-annotation-pinning discipline; the `/dev`(typecheck) unit row §3.4 |
| **4 — 0914** (`/design` int) | `/mem`'s counter window moves past `release_program_result()`; check: a REPL cell where `/mem`'s delta reflects the result release (row `[S119]`, cell shape settled by the design; the 0913 cell's instrument choice — exit counters, never `/mem` — stays until this lands) |
| **5 — 0918/0919** (`/arch`) | facade-truth pass: `facade_compliance` + `public_api_relocations` GREEN over the types delta; R4 compaction drops first; the §5.1 R8-linkage request rides here |
| **6 — platform/testing riders** | 0870: doc-only, `public-api.txt` byte-identical; 0874: the S118 §7 preservation checklist (zero assertion deletions/weakenings, per-crate schemas retained, sustained-repetition guards untouched); 0873: design-only, any public surface contact returns to `/arch`; 0871: doc canon collapse, no cells; 0900: locus seam-form edit (ordinary `/testing` change); 0798: module-alias-as-qualifier repro cell lands (deferred ×2 — lands or is explicitly re-deferred with user visibility at close); 0799: the autocurry free-type-var matrix column + repro (same rule) |
| **7 — 0863** (conditional, §Open items ①; never interleaved with B-int) | if executed: flips #16–17 through echo/`/info`/`/sig`/bare lookup; the S118 §6.1 transaction negatives (induced mid-turn failure leaves NO partial state) + controls + the no-parallel-presentation-store structural check; else: S120's first item, carry recorded |

## 10. Risk read (what shapes depth this sprint)

1. **Ruling-with-zero-consumers (the S118 D1-drift class).** Mitigated
   structurally: measure-before-binding (§3.2.2); the eleven acceptance REDs
   are the contract's executing consumers; the drop-bomb proofs are the typed
   layer's. Deepest coverage goes to Spine 1's corpus gate and the family
   guards — the two places a wrong ruling fails silently.
2. **Churn masking behaviour change.** The §4.1 byte-identical re-run set;
   must-not-interleave is a `/review` reject, not advice.
3. **The 0867 widening hazard.** Sequencing gate (§9 rider 1); the corpus
   manifest extension is the fence.
4. **Refusal→silent-leak escape hatch on the IO face.** The balancing guard
   (§3.3) exists precisely for the admission-exclusion direction.
5. **Flap-polarity arithmetic.** Per-binary intended-RED verification; the
   flap set stays outside the scalar; D1 may re-point the whole family at
   shared cache substrate — which rider 2 touches, so its window carries the
   hazard note.
6. **Schema discipline.** Exactly one window (23→24, rider 2); a schema delta
   in any other change-set is a `/review` REJECT and a close blocker.

## 11. Close gate

1. Deterministic: two consecutive complete tee'd runs, identical failure
   sets, empty except user-approved carries; name-for-name reconciliation of
   §1.2 per §1.3 (flip traced to mechanism change-set; suspicious greens
   investigated, not celebrated).
2. G1–G6 each verified against §2's named instruments; a gate asserted in
   prose with its instrument missing fails the gate.
3. Load-dependent member per §1.1(2); the flap-set roster (both polarities)
   reported; D1's outcome recorded in 0694 whichever way it fell.
4. The option-2 number recorded with method + gap enumeration + failure-set
   delta (§7) — or an explicit record that the run window did not open, with
   the S120 consequence stated (adoption cannot be decided without it).
5. 0859's disposition-2 return delivered to the user (§8.3) — never silently
   carried a second time.
6. No new ignores; every new cell carries `// spec:` (+ `// defect:` for
   repros); `plan/spec_link_check.py` + `plan/spec_coverage_reconcile.py`
   clean over the changed set; threshold census (§5.3) reads zero at close or
   names the explicit carry.
7. Durable fold-back: §5.1's normative form and the R8 lane row land in
   `PLAN.md`; 0761 deleted with the lane; the annotation band updated for
   newly covered spec rows.
8. **Negative-coverage accounting (the S119 user finding):** the §3.7 set
   reconciled name-for-name — NC-1 group 1 + the 0926 gate cell GREEN with
   P-1's change-set named; **NC-1 groups 2–3 are pre-declared S120
   carries**, attributed at authoring time (group 2 → FIXME 0931, group 3
   → FIXME 0932) and entering close as named carry candidates under §1.1's
   user-approval contract — planned instruments, never surprises; NC-1
   group 4 + NC-R stay GREEN throughout; NC-2 (both families) standing
   GREEN with its detection proof recorded; NC-4 flipped by the Spine-1
   wave; NC-5 flipped by the ctor-materialisation ruling's change-set (or
   an explicit user-approved carry);
   the close report states the annotation-band ratio
   (`[Tested]`-only vs `[Tested+Neg]`, `negative-coverage.md` §S119) beside
   the suite scalar. A close that certifies the release contract with NC-4
   still unguarded-and-unlanded repeats the R11 failure and is blocked.

## Next skills

- `/testing` — Phase 5 stage 1: the §3.3 guards (family-1 pair, IO-Bind
  balancing guard, the §3.7 NC-4 accessor boundary repro), the §3.6 census
  cell and the §3.7 NC-2 fabrication census (in the implementing wave), the §4.5
  lane reconciliation, the §6 warmed-pair mode + capability cells, riders'
  cells per §9; later, riding fixes: cell #21 re-derivation (§5.3), 0889 pin
  re-derivation (§4.4), the 0915 frame guard in the fix window; Track C D1
  execution (§8.1) in the allocated run window.
- `/design`(backend) — the co-ruling with §3.2's assertion form binding
  (record the corpus table in the ruling); the §7 gap enumeration when the
  measurement window opens.
- `/design`(typecheck) — Round 2 producer face (§3.4) against the landed
  contract.
- `/dev` (per crate, Phase 5) — unit tiers named in §3.4, §3.7 (NC-1
  typecheck, NC-R src, NC-5 backend, NC-3 per site), §4.2, §4.3, §5.2, §9;
  the census-pinned numbers come from the landed ruling.
- `/arch` — Phase-3 exit gate (intrinsics `public-api.txt` diff, tranche-A
  shim-fact design); the R8 register-linkage request (§5.1) in the rider-5
  window.
- `/sprint` — carry to the user: the 0859 disposition-2 return (§8.3); note
  the stale SPRINT.md 0890 row (§6); allocate the D1 and option-2 run windows
  under one-agent-one-test-run; wave sequencing per the must-not-interleave
  list.
