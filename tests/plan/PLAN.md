# Test plan

Owner: QA. This is the current assurance and coverage navigation for Cranelisp,
established by [test ownership](../CLAUDE.md). Requirements remain in the
[language specification](../../spec/CLAUDE.md) and
[REPL specification](../../repl/spec.md); mechanisms remain in their owning
designs. This plan allocates evidence, not language semantics or implementation.

## Strategy — two tiers, no middle

- Public behavior is observed through the compiler process: REPL, run or a
  linked executable, with isolated input files and captured output/exit state.
  Test owns solution tests and helpers; QA owns allocation and adequacy.
- Dev owns module evidence beside the implementation. It covers internal
  representation, lifecycle and failure states that a legal public program
  cannot construct or discriminate. Do not construct compiler internals in a
  public-process test to bridge an observation gap.
- The process harness pipes all three standard streams and reads them after
  exit. It therefore cannot observe the interactive-terminal line editor and
  history, colour-on rendering (a non-terminal forces colour off and
  [terminal styling](../../repl/spec/10-terminal-styling.md) defines no force
  flag), or whether output arrived incrementally. Those observations are module
  evidence or a stated manual check; the process tier pins the non-terminal
  byte-identical path and the rendered result.
- Assign the cheapest observation that separates the required result from a
  plausible wrong result. Add another layer only for a distinct residual risk.
  Shared [QA responsibilities](../../.agents/skills/qa/SKILL.md) and
  [quality standards](../../.agents/skills/quality-standards/SKILL.md) govern
  allocation, attribution and evidence limitations.

### Repository gates — maintenance checks, never compiler authority

[Document wiring](../citation_drift.rs) invokes the shared document checker and
project declaration without a suppression baseline. [Role wiring](../role_wiring.rs)
checks local host/package declarations. These are repository-maintenance
observations, not compiler-behavior acceptance. A finding invalidates the
record or wiring claim it measures; it does not reopen an unrelated compiler
correction. The [D7 integration disposition](s122-evidence-delta.md#d7-integrated-project-gate--adequacy-and-remaining-conformance)
separates delivered wiring from unresolved document conformance.

## Traceability and authoring

- Derive the expected result from the current requirement before choosing the
  fixture. Concrete tests carry their specification and defect provenance;
  the navigation rows below identify the owning behavior families.
- Record acceptance, safety, diagnostic and maintenance evidence separately.
  A correct value does not establish balanced ownership; a clean diagnostic
  does not establish rollback; source structure is not executing evidence.
- Preserve intended RED/control and corrected GREEN provenance when allocated.
  A failing process must fail for the intended reason, and a passing absence
  assertion needs a positive operational signal where silence could be vacuous.
- Under [root coverage annotations](../../CLAUDE.md#requirementstest-traceability),
  positive-only `[Tested]` remains a coverage gap until the required negative
  behavior is evidenced; do not label it `[Tested+Neg]`. QA chooses the
  proportionate observation under the shared risk/cost rule, without weakening
  that coverage distinction.
- When MUST or MUST NOT prose is annotated `[Tested]` without a negative, name
  the missing negative observation at annotation time in the unclassified-leads
  list below; the specification band and that list are the only registers
  (S119 standing practice — no separate negative-coverage register is kept).
- The sprint close report states the `[Tested]`-only and `[Tested+Neg]`
  counts and their delta beside the suite result. A ratio that moves only when
  a defect forces it is the dormancy signal the S119 R11 finding exposed. A
  [safety-register](../../design/arch/safety-invariants.md) row touched in
  scope carries its own cited detection proof under that register's
  requirement; this plan does not duplicate it.
- A suite-state count at a gate states the stable failing set exactly and
  lists any run-dependent guard separately by name. A run-dependent guard is
  a defect signal to attribute under the
  [failing-test discipline](../CLAUDE.md#failing-test-discipline-migrated-from-the-retired-ledger),
  never a member of the exact count;
  [suite-count provenance 0694](../../design/arch/fixmes/0694-qa-suite-count-nonreproducible-two-interleaving-dependent-guards.md)
  is the open record of the last such guard.
- A leak attribution separates a program-independent residual from the leak
  by scaling the workload: a delta invariant under N is residual, a delta
  that scales with N is the leak. Measure it as a marginal pair under
  [allocator balance](../CLAUDE.md#allocator-balance-is-measured-marginally-never-absolutely),
  never against a threshold.
- A wall-clock witness asserts a structural inequality between regimes that
  are wide apart (overlapped, waved, serial), never a tuned threshold. Repeat
  only the leg that machine contention can falsify: contention slows a run and
  never speeds it, so an upper bound takes the minimum of several attempts
  while a lower bound stays single-shot. A CPU-bound speedup witness needs a
  qualifying attempt among several, and its no-speedup control a majority.
  Widen the separation between regimes before loosening a margin; assert
  value equality on every attempt. [Failing-test discipline](../CLAUDE.md#failing-test-discipline-migrated-from-the-retired-ledger)
  bans the "timing-sensitive" disposition these rules exist to avoid.
- Four drafting rules come from the S101 escape analysis and are stated once,
  in the [S101 coverage audit](coverage-audit-s101.md#25-standing-rules-fed-back-into-qa-practice-supersede-post-mortem-33):
  value-use rows key on per-consumer artifact minting and include a second
  instantiation; a MUST that pins display shape gets an exact assertion while
  error matching stays substring; each new session-visible state kind gets a
  restart row and a session-history preamble row; and a designed floor that QA
  pins is flagged to the user-facing roles in the same phase. Its
  [named lanes](coverage-audit-s101.md#24-proposed-lanes-named-durable--s102-qa-work-unless-noted)
  are the vocabulary test sources use for those observations.
- In-scope failures remain visible. Unknown attribution stays provisional;
  neither an old issue label nor a terminal error identifies the corrective
  owner. Use the [test-side notation and harness rules](../CLAUDE.md).
- An explicit module deferral names the cases, observing seam, owner and what
  remains unproved publicly. “Unit-pinned” alone is insufficient. Reuse adequate
  existing evidence; do not manufacture public invalid-language triggers for
  internal failures.

## Standing coverage audit — definition variants

When one invariant spans definition forms, resolution sites, provenance or
output kinds, enumerate the affected family from current source. Compare its
positive behavior, applicable refusals and existing observations. Distinguish
an unknown cell from a demonstrated gap, and record structural equivalence
where a shared mechanism makes another observation redundant. No Cartesian
matrix is required merely because axes can be named.

- Axes are relations as well as forms. Name the relational axis a mechanism
  resolves over — for example call topology, carrier × reaching context,
  shadowing × callee kind, storage model × persisted kind — and give each
  axis one equivalence twin: the same invariant satisfied two ways under one
  assertion, so a variant that grows its own codepath diverges the pair and
  the failing twin names the site.
- Where a mechanism resolves through module structure (dispatch, carriers,
  mangling, constraint verification), carry {local, imported, foreign
  signature type} as an axis with the local cell as the twin. A cell whose
  fixture imports every type the signature mentions into the calling module
  never asks the foreign-type question.
- For a strategy-bearing fix, name the negative-space module cells from the
  design's claim before the fix lands; a unit test authored from the diff
  validates the fix's model of itself.
- The frontend operand-position × {bare, ascribed, trailing}, head-parser
  × {arm, case} and binder-position × {qualified, dotted} matrices are drawn
  in [enforcement matrices](../../design/frontend/enforcement-matrices.md)
  and [binder-head reject](../../design/frontend/binder-head-reject.md);
  re-audit them when a new expression-position or head parser appears.

The standing lens is the S108 direction reconciled in S122. Filing0944's
universal absence claim was disproved by existing variant matrices; its current
procedure/discoverability repair is complete. [Detailed reconciliation](s122-evidence-delta.md#standing-category-reconciliation-for-filing0944)
preserves that closure, without claiming every current family is covered.

### Prelude and explicit-import parity

Use equivalent public re-export and explicit-import fixtures at the affected
resolution or publication boundary. A private prelude name is not a legal
substitute for the public-import control. Check terminal binding home and
visibility as well as the observed value; imports and locally authored
bindings may have different conflict obligations. The owning
[convergence contract](../../design/arch/prelude-import-convergence.md)
defines those semantics; the old S108 site count is not a current census.

## Coverage preservation and evidence navigation

Before retiring an assertion, identify equivalent coverage or the authority
that makes it obsolete. Compare context, modes, defect lineage and each
material assertion. Keep unresolved obligations independently of a deleted
working plan. The S64/S82 quarantine harvest is complete; its initial GAP
counts are not current findings. [The S82 outcome](../../sprints/archive/sprint-82.md)
and Git preserve the migration result and original per-test dispositions.

The ring-era plans, the four-layer strategy and the S61 audits that lived
in the legacy-plan collection (`git show 7f834bf6:tests/plan/legacy/`)
were deleted in S122 after verification against source; the checkpoint retains the set. The Sprint-64 harvest audits of the deleted test
quarantine (the wave-3.5, wave-5.5, wave-5.6 and wave-6 records), the S21
line-coverage snapshot, the S16 negative-coverage register and the
failure-ledger stub followed (`git show b602708e:tests/plan/`): every
sampled carry-forward those audits demanded exists in the current suite or
was dispositioned by the S82 harvest gate, and no register held a rule
without a current home — the FFI-marshalling detection gaps are
[Risk 11](risks.md), the failure-ledger retirement is stated in
[test conventions](../CLAUDE.md), and the S119 negative-coverage practice
is in §Traceability above. Their surviving rules live where a reader needs them: the
tier strategy above, the per-test temporary-directory rule in
[test conventions](../CLAUDE.md#fresh-temp-directory-per-test) with its
harness enforcement in [helpers design constraints](helpers.md#design-constraints),
and the S61 negative-coverage promotions in the specification annotations
themselves.

The eleven Sprint-84 to Sprint-97 working plans (monomorphisation and
auto-IO, the agent rungs, `/search`, the race gate and the effect-concurrency
slices) were deleted in S122 (`git show 7e56a81c:tests/plan/`). Their closed
[sprint records](../../sprints/archive/) hold each increment's disposition and
the tests they named are in the suite; a plan row is not evidence that its test
landed, so rows that never did are carried below as unclassified leads. The
lane, feature-gate and descriptor models those plans describe were retired by
the S96 single-lane cutover and the S97 handle model.

The Sprint-69, Sprint-75, Sprint-92 and Sprint-94 working plans were deleted in
S122 (`git show cdd1f9ea:tests/plan/`); their closed
[sprint records](../../sprints/archive/) hold each disposition. The S69 and S75
plans scheduled facade-conformance re-anchoring whose subject is retired:
[public-API enforcement](../CLAUDE.md#public-api-enforcement) names the
executing guard, and the constructor-as-value cell S75 carried forward is
observed by [constructor values](../ctor_as_value.rs). Every solution test the
S92 apply-argument and spark-budget plan and the S94 effect-await,
dependent-binding and docstring-regeneration plan named is in
[runtime behavior](../spec_12_runtime.rs), [reactor await](../concurrency_reactor.rs),
[spark substrate](../concurrency_spark.rs) and [agent behavior](../agent.rs)
under its planned name. Their module rows are owned beside the implementation
and landed under successor names (the spark-budget reservation units, the
`render_decl` docstring units) or were superseded with the v7 ABI and the
feature-gated lanes that the S96 single-lane cutover retired.

The Sprint-78 int-restructure plan was deleted in S122
(`sprint78-restructure` under `git show cdd1f9ea:tests/plan/`). Every test it owed
is in the suite: the H5 replay gate and the regrounded observable-outcome
guards in [persistence races](../repl_persist_race.rs), the two-node
cycle-before-wait refusal in [module conformance](../spec_08_modules.rs) and
the parking-map guard in [regression](../regression.rs). The two
guard-mechanism probes it scheduled for retirement are gone. The invariants
those tests evidence are stated in [int orchestration](../../design/int/int.md)
§6.2, and the replay gate's own comment carries its limit: fifty zero-tolerance
iterations are a reopening tripwire, not statistical proof. The plan's
prelude rows asserted that an explicit import silently shadows the prelude;
the [convergence contract](../../design/arch/prelude-import-convergence.md)
reversed that, and [prelude scope](../spec_08_prelude_outer_scope.rs) now
observes the poisoning outcome. Its one
withheld observation, the §8.10.1 run-mode exit, is now asserted by
`defn_before_import_resumes_correctly_after_dep_load` in module conformance.

Six Sprint-106 to Sprint-120 working records were deleted in S122
(`git show 48d6e713:tests/plan/`): the S106 burn-down and S107 rendering plans,
the S110 gate attribution, the two Sprint-116 baseline and changed-test
reconciliations and the S120 0917 provenance delta. No current source, test,
design or filing cited them. Every filing the S106, S107 and S110 records
planned against is closed, the agent-lane provenance race they attributed is
stated in [test conventions](../CLAUDE.md#the-agent-lane---features-agent--isolated-target-dir),
the delivered 0917 contract lives in
`design/backend/non-concrete-release-contract.md` §6, and the harness limits
S106 and S107 named are in the [current strategy](#strategy--two-tiers-no-middle). The Sprint-116 changed-test audit listed module
tests without `// spec:` comments; that list was not re-measured here and is
not a current finding.

### Mode canonicalisation — REPL is the canonical surface for language conformance

Use REPL for bulk language conformance and the relevant public entry for
mode-specific behavior. Representative equivalent programs exercise fresh and
cached REPL, run and linked execution; preserve each outcome so one cached
failure cannot hide behind fresh success. The [mode-equivalence helper](helpers-api.md#mode-equivalence-helper--run_through_all_modes)
and [harness design](helpers.md) define the observation mechanics. Int-return,
stdout and error observations serve different properties; do not force an
encoding that obscures the requirement. Correct results alone do not prove
parallel execution or actual warm-object reuse.

## Current coverage navigation

Rows identify current requirement/evidence homes, not blanket certification or
an exhaustive test census. Inspect concrete assertions and their recorded run
before reusing an observation. Specification annotations and source tests carry
the fine-grained forward/back trace; this plan does not duplicate every name.

| Requirement family | Concrete evidence navigation | Material distinction |
|---|---|---|
| Types, inference, annotations and polymorphism | [Type conformance](../spec_03_types.rs), [expression conformance](../spec_04_expressions.rs), [S121 result-context allocation](s121-test-plan.md) | Written/unwritten variables, quantified/value positions, result-only inference and refusal are distinct. Old rigid-variable proposals are not current semantics. |
| Definitions, patterns and traits | [Definition conformance](../spec_05_definitions.rs), [pattern conformance](../spec_06_pattern_matching.rs), [trait conformance](../spec_07_traits.rs) | Constructor/binder/reference roles, sibling clauses and scrutinee-directed resolution need their own applicable polarity. |
| Module identity, loading and visibility | [Module conformance](../spec_08_modules.rs), [name conflicts](../spec_08_name_shadowing.rs), [prelude scope](../spec_08_prelude_outer_scope.rs) | Explicit/prelude provenance, terminal home, poison, private names, missing modules and persisted declarations are not interchangeable. |
| Macros, quotation and standard-library composition | [Macro conformance](../spec_09_macros.rs), [standard-library conformance](../stdlib_conformance.rs), [stdlib REPL behavior](../spec_11_stdlib.rs) | Ordinary value success does not establish macro ownership, annotated-child cleanup or aggregate IO safety. |
| IO, scheduling and ownership | [IO behavior](../spec_10_io.rs), [runtime behavior](../spec_12_runtime.rs), [memory-safety coverage](memory-safety-coverage.md), [ownership-flow generator](../gen_ownership_flows.rs) | Value/order, cancellation, liveness, exact balance and scaling are separate observations; generator coverage is limited by its actual types, positions and modes. |
| Local binding identity and lifetime | [Same-form rebinding](../same_form_rebinding.rs), [shadowed-parameter reach](../shadowed_param_reach_stale_rc_dec.rs), [binding-scope design](../../design/backend/binding-scope.md) | Distinguish displaced binder cleanup, inner shadow scope, capture membership and continuation capture types. |
| REPL state, diagnostics and presentation | [Introspection](../repl_introspection.rs), [negative paths](../repl_negative.rs), [lifecycle](../repl_lifecycle.rs), [search](../search.rs) | Prompt/update text alone does not prove publication; diagnostic rendering alone does not prove state preservation. |
| Replacement, persistence and watching | [Redefinition](../repl_redefinition.rs), [watching](../repl_watch.rs), [persistence](../repl_persist.rs) | Prior realization, same-family replacement, rejection atomicity, provenance and dependency ordering are distinct. |
| Cache and executable behavior | [Cache behavior](../cache.rs), [link behavior](../link.rs), [build confidence](../build_confidence.rs) | Demonstrate real reuse where reuse matters; schema rejection/rebuild and fresh/cached value parity prove different facts. |
| Platform boundary | [Public ADT crossing](../spec_platforms_adt.rs), [platform module fixtures](../../crates/cranelisp-platform/tests/), [surface guards](../facade_pif_rows.rs) | Source ABI-version, exported surface, physical layout and an actual DLL crossing are different claims. |
| REPL agent | [Agent behavior](../agent.rs), [agent testing strategy](agent-testing-strategy.md), [active eval policy](s122-evidence-delta.md#runnable-eval-corpus-and-policy) | Deterministic routing/transport checks do not certify live-model quality. Live configuration and budget remain a separate gate. |

## Active allocation and unresolved evidence

[S122 evidence](s122-evidence-delta.md) owns the current per-stream allocation,
executing checkpoints, bounded closures and remaining gates; its
[acceptance reconciliation](s122-evidence-delta.md#phase-5-acceptance-reconciliation-2026-09-27)
is the current gate disposition. The [active sprint](../../sprints/SPRINT.md)
owns sequencing and user decisions. Neither a historical RED nor deletion of
its old matrix changes current acceptance. Retained [S121 evidence](s121-test-plan.md)
and [S118 evidence](s118-test-plan.md) supply specific prior witnesses when the
active allocation cites them; they are not fresh source censuses.

- The exact-RC generator's linked nested-data/closure-capture remainder is
  tracked by [filing0761](../../design/arch/fixmes/0761-qa-exact-rc-balance-lane-owning-type-by-position-matrix.md)
  and the S122 allocation. Do not widen this into a full mode matrix.
- [Suite-count provenance0694](../../design/arch/fixmes/0694-qa-suite-count-nonreproducible-two-interleaving-dependent-guards.md)
  remains an independent record; a later green suite does not reconstruct its
  missing historical attribution.
- The 0859 `ProjectionOf` production-witness obligation is retired unexecuted
  under the 2026-09-01 user disposition recorded at the
  [primitives R-2 evidence boundary](../../design/primitives/primitives.md#r-2-evidence-boundary--accepted-with-a-revival-trigger),
  which names this plan as the trigger's home. The exact revival trigger is
  the [accepted future-triggered action row](s121-test-plan.md#510-accepted-future-triggered-actions):
  it fires only when projection provenance becomes emission-live, and then
  returns as a plan row of that sprint. Nothing is allocated now; the
  [S118 conditional cell](s118-test-plan.md#35-0859-projectionof-witness--conditional-cell-ruling-2)
  is a dated record of the retired experiment, not a live observer plan.
- Other open compiler findings retain their own records in the
  [sprint inventory](../../sprints/s122-candidate-inventory.md) and active
  allocation. This rewrite closes none of them.
- Annotation in macro-argument position (0708, resolved in S122): the user's
  Reading A-structural ruling is scribed. The acceptance evidence is
  `annotation_fold_macro_arg_0708::annotation_folds_in_macro_argument_position`
  and its unannotated control, both GREEN in the S122 CD-1 final suite. The
  witness asserts the folded `:primitives/Int 5` result, which a malformed-sexp
  failure cannot produce, so it supersedes the former polarity-safe
  `returned malformed sexp` pin; no pin is allocated. `test` owes only the
  witness's notation upkeep: `fixed=` and past-tense framing on its open
  `// defect:` line and header. The int annotation-mirror tail is in
  [`int.md` §16.0](../../design/int/int.md#160-open-binaryint-obligations-verified-against-source-2026-09-21);
  the spaced `: Int` spelling stays with its owner.
- The exemplar warm-solve cell asserts exact warm balance:
  `exemplar_ownership_residue_s116::sudoku_warm_serial_solve_retains_nothing`,
  with `warm_cache_hit_control_carries_no_ambient_residual` in the same binary
  as the executed ambient-free premise. No allocator-balance threshold cell
  remains.
  - The cell is RED, with a residual of 51 against a premise of 0 (2026-09-30).
    It is carried as intake under
    [ACT-1018](../../sprints/actions/ACT-1018-exemplar-warm-solve-residual-intake.md).
  - A nonzero residual is intake to `qa`, never a threshold.
  - Provenance: S119 §5.3, `git show a07823d8:tests/plan/s119-test-plan.md`.
- **L-B1 corpus extension: QA disposition pending.** The retired S102
  exclusions promised capture after six shapes were fixed, but the corpus was
  not extended. Their existing regression guards pass in the S122 cache-work
  log; that does not establish corpus completeness. QA must decide whether
  the current 14 entries are adequate or allocate additional captures to
  `test`. The shapes are: two-instantiation Vec-operation HOF value use
  (0483), single-instantiation Vec-operation value use (0474), qualified
  generic call (0488a), imported generic value use (0488b), composition over
  a fold-bodied imported generic (0488c), and definition-over-import shadow
  order (0484, a rejected-program case whose capture suitability needs review).
  Provenance: `git show a07823d8:tests/fixtures/clif_baseline/EXCLUSIONS.md`.
- Option-2 (uniform emission) dev-tier cost remains unmeasured. The
  [ownership-stratum options](../../design/arch/ownership-stratum-options.md)
  paper defers option-2 adoption until that cost is measured, and no sprint
  schedules the measurement. The S119 method (§7 at the revision above) is the
  starting point:
  - subject: the all-Owned lowering toggle; control: current emission; same
    binary and tree, with only the per-child environment differing;
  - the toggle leaves structural elisions in place, so the result is a lower
    bound on uniform emission's cost unless `design`(backend) enumerates the
    gap;
  - measure the exemplar warm solve's wall time and RC op counts, the
    contention benchmark, and the full suite's wall time and failures by name.

  Nothing is allocated until the option is scheduled.
- Historical unfiled limits remain explicitly unclassified. Each keeps its
  exact provenance so its substance is recoverable without re-derivation:
  - the S108 all-green multi-form display note — the
    [historical S108 E7 allocation](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/tests/plan/PLAN.md#e7--multi-form-line-swallows-per-form-errors-no-agent-path)
    and the control's own comment in [REPL negative paths](../repl_negative.rs)
    (`multi_form_all_green_line_evaluates_without_error`);
  - the S115 impl-rejection expected/got wording — the
    [historical S115 re-impl cells](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/tests/plan/PLAN.md#b-impl-redefinition-hot-reload--testsimpl_redefinition_dispatchrs),
    observed on [impl redefinition dispatch](../impl_redefinition_dispatch.rs)
    (`reimpl_neg_type_changing_body_rejected_and_prior_impl_keeps_dispatching`);
  - the S115 frontend dotted-reference mutation rider — item 4 of the
    [retired 0787 disposition](s115-test-plan.md#102-fixme-0787--dotted-reference-over-reach-cells-retired),
    over [dotted reference-column controls](../dotted_binder_reject_0702.rs);
  - the S121 capture-veto optimization/observer proposals — the
    [historical S121 same-form rebinding rows](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/tests/plan/PLAN.md#sprint-121-same-form-rebinding-rows-design-designbackendbinding-scopemd)
    and the observation limit in
    [binding-scope state and assurance](../../design/backend/binding-scope.md#state-and-assurance);
  - the S61 inline-ADT-argument equivalence property — `(f (Ctor [v]))`
    observationally equivalent to `(let [x (Ctor [v])] (f x))` in value and
    exact allocation balance, for a callee that takes the constructed value
    by ownership and matches it, over scalar and heap field types and across
    a module boundary. The S61 plan rows that reserved it were never authored
    (retired ring plans, `git show 7f834bf6:tests/plan/legacy/` — `ring1.md`
    §"Inline-ADT-arg class"). Today's observations are the single-type,
    value-only repro in [regression](../regression.rs)
    (`t_s2_2_inline_adt_arg_wrapping_vec_preserves_len`) and the
    [ownership-flow generator](../gen_ownership_flows.rs), whose argument
    positions hand inline-constructed owning types to a borrowed reader in
    one module rather than to an owning matcher across modules;
  - the S108 §1.5 Vec and List value-display rows in
    [display format](../../repl/spec/01-display-format.md), downgraded to
    positive-only when their original negatives were deleted. The named
    missing observations are a no-raw-pointer / no-truncation negative for
    Vec and a no-raw-pointer / no-forced-tail negative for List; the bare-`[]`
    case is now evidenced by [introspection](../repl_introspection.rs)
    (`display_empty_vec_value`), and the exact-line display cells partially
    subsume both by whole-line equality;
  - the S85 REPL-entered auto-IO parallelisation witness. The S85 plan row
    `auto_io_repl_eval_path_parallelizes` was never authored; the
    [S85 record](../../sprints/archive/sprint-85.md) left it on a doubt that
    REPL output gives a reliable wall-clock window and proposed a
    `Par`-emission introspection witness instead. Today
    `auto_io_par_grouping_uniform_across_modes` in [IO behavior](../spec_10_io.rs)
    observes run and linked execution only, and
    [bind-chain analysis](../../design/int/bind-chain-analysis.md) §5.1 rests
    the REPL case on all modes sharing one `process_cluster_once` seam;
  - the S87 wall-clock witness sweep. S87 allocated a QA pass over every timing
    assertion whose contention-falsifiable leg is single-shot; its findings
    file holds no result (S87 findings at Git revision `66a4d41e`). Later
    witnesses follow the timing rule in §Traceability; earlier ones were not
    re-inspected against it;
  - the S88 module-preamble read. The `/doc <module>` read and its no-preamble
    refusal are rows of the [agent testing strategy](agent-testing-strategy.md#35-preamble-edit--round-trip-rungs-0-and-6);
    the command is implemented in the REPL command handler, the requirement
    headings in [modules](../../spec/08-modules.md) §8.16.4 and the
    [embedded agent experience](../../repl/spec/17-embedded-agent.md) §17.5.1
    still carry `[S88]`, and no solution test traces to either section;
  - the S92 lenient-evaluation annotation band. The S92 plan scheduled
    band updates against its landed apply-argument tests. The §12.4.3 heading
    now names two landed cells, but the
    observable-order paragraph of [runtime](../../spec/12-runtime.md) §12.4.1,
    the two permission paragraphs of §12.4.3 and the closing note of
    [expressions](../../spec/04-expressions.md) §4.11 still carry `[S92]`,
    while `apply_arg_pair_equiv_run`, `apply_arg_dc_map_reduce_equiv_run` and
    the ferry cells in [runtime behavior](../spec_12_runtime.rs) trace to those
    sections. This is a band reconciliation, not a missing test: the next
    observation is whether each cell still validates its paragraph as now
    written, including the negative direction, before any tag changes;
  - the [session-persistence authority rows](../../repl/spec/15-session-persistence.md)
    §15.2.1 (restoration governs, redefinition wins, piped input is session
    input) and §15.2.2 (startup restore notice) carry `[S113]` with no
    traced solution test. The S113 discriminator that settled §15.2.1 —
    session 1 defines `(defn f [] 1)` and exits; session 2 in the same
    directory pipes `(defn f [] 2)` then `(f)` and must print `2` — was run
    once and never committed, and the S114 notice cell (present on restore,
    absent in a fresh directory) is not evidenced by name in
    [persistence](../repl_persist.rs). The §15.2.3 startup-recovery and
    retention rows are allocated, not leads:
    [S122 evidence](s122-evidence-delta.md#startup-recovery-and-failed-source-retention--evidence-delta-2026-09-22);
  - the S117 module matrices allocated to `dev` and never verified
    ([S117 plan at `7b1220c7`](https://github.com/alilee/cranelisp/blob/7b1220c7/tests/plan/s117-test-plan.md) §5). A bounded name
    search on 2026-09-22 located the transaction-state cell
    (`src/worker/tests.rs::ordinary_replacement_compile_failure_restores_prior_instance_and_session_state`,
    now owned by the S122 Q2/D1 allocation) and the `/info` view cells
    (the impls_for_type_in_view test family in `src/repl/format_type.rs`), and found no module
    matrix by name for typecheck trait-reference resolution
    ({bare imported, FQ same trait, FQ same-spelled foreign, nonexistent
    module} × {method mint, default synthesis, forced re-impl enrollment}),
    for the macro-expanded top-level registrar sequence, or for type-render
    variants. The e2e twins in [trait conformance](../spec_07_traits.rs),
    [macro conformance](../spec_09_macros.rs) and
    [introspection](../repl_introspection.rs) are the acceptance evidence at
    those seams; a module matrix is owed only if `dev` names a private branch
    they cannot reach. The R-2 matrices that row also named are retired with
    0859 above;
  - the S111 Principle-24 register's unfinished legs. S111 set out to classify
    every unindexed iteration whose result can become a compile-necessary
    identity as an enumeration or an identity scan, under the carve-outs in
    [Principle 24](../../design/arch/principles/24-resolve-once.md). The backend
    and the primitives, intrinsics and platform crates were classified. Three
    legs were not: the typecheck producer surface, which
    [typecheck](../../design/typecheck/typecheck.md) §9.7 names as open; the
    integration layer's `symbol_tables.iter()` sites
    (`git grep -n 'symbol_tables.iter()' -- src`), which carry only unverified
    leans; and the frontend, delegated to an audit rotation that recorded no
    verdicts. One backend row was never decided:
    [`register_platform_effect_symbols`](../../crates/cranelisp-backend/src/jit.rs)
    registers each platform effect under its table key, without a module
    qualifier, into the JIT's one flat namespace, and checks for no collision.
    Two same-keyed effects in different platform modules would resolve by
    table iteration order. S111 judged the keys unique by convention only and
    left the choice between a structural tie error and an asserted uniqueness
    invariant open ([retired register](https://github.com/alilee/cranelisp/blob/fc49541f/tests/plan/s111-principle24-register.md)
    §2);
  - the S104 U-G6 gate. S104 defined `CRANELISP_SPARK_STATS` unset as
    byte-identical codegen and wall against the uninstrumented build, and its
    final acceptance graded U-G1 to U-G5 only. The zero-cost-off claim stands
    asserted in the counters' rustdoc in the `ivar` and `utilization` modules;
    the byte-identical-when-off invariant (§1 item 5) in
    [lenient evaluation](../../design/backend/lenient-eval.md) has no row in
    that design's evidence table
    ([retired S104 record](https://github.com/alilee/cranelisp/blob/fc49541f/tests/plan/s104-utilization-measurement.md)
    §6, §8.7);
  - the S109 capacity-window observation.
    `concurrency_capacity::same_token_capacity_n_blocking_admits_n_concurrent_nplus1_parks`
    was seen to pass, fail and pass in isolation during S109. It was listed as
    an unverified candidate member of the 0604 index-feed family, and 0604
    closed structurally in S122 without that verification. The test's
    two-sided wall-clock window is a contention-falsifiable timing assertion
    ([closed S109 record](../../sprints/archive/sprint-109.md)).

  They are not newly allocated defects. Before relying on any, compare current
  specification and evidence; no new test, API or optimization is authorized
  by retaining the lead.
- The S112 MS-6 and other enumerated module obligations/user-choice cells remain
  in [their retained allocation](s112-0628-ic-wave.md). Removing PLAN's duplicate
  does not settle an unresolved choice. Later ownership obligations remain in
  the cited live filing/evidence homes.

## Evidence currency and retention

Record the source/build configuration, inputs, intended failure/control,
observed output and material limits needed to assess a claim. Counts are dated
measurements, not acceptance constants. Reuse a proven witness when the change
has not invalidated it; a new snapshot, plant, matrix or suite run needs a
specific unresolved risk. [METHOD retention](../../sprints/METHOD.md#31-where-things-live)
keeps completed planning detail in Git by default. Irreplaceable evidence gets
an explicit retained carrier; [the exact legacy checker reconciliation](s122-document-checker-reconciliation/README.md)
is such a carrier and is never a suppression baseline.

Four S99–S101 records are retained because current design, test sources and
harnesses cite them by section, so those section numbers stay stable. Each
opens with what in it is standing and what is dated:

- [S99 contention measurement](s99-measurement.md) — the measured basis of the
  contention rulings in the effect-concurrency and reference-counting designs,
  and the F1–F4 baselines.
- [Ownership verification](s100-ownership-verification.md) — the analysis-off
  oracle, lane definitions, hooks and coverage limits that ownership tests,
  scripts and gate harnesses cite, with the S102 and S103 measured acceptance
  records and the user's accepted trade.
- [S101 coverage post-mortem](s101-coverage-postmortem.md) — the `callees`
  completeness contract cited by the typecheck and save unit tiers.
- [S101 coverage audit](coverage-audit-s101.md) — the named lanes and the
  drafting rules in §Traceability above.

The S102–S121 records below are retained for the same reason: current source,
tests, designs, the specification band or open filings cite them by section or
row identifier. Each is a dated allocation, attribution or measurement, never
current status; compare a RED, carry or count in one with current source before
reuse. Retirement needs the citing owners to move their citations first.

- Measurement: the [S105 attribution results](s105-attribution-results.md) — the
  graded walls and accept-done verdict that the S105 behavioural guards and the
  CLIF-verification demo cite.
- Cut in S122 to their cited sections, original numbering kept and the removed
  remainder named in each header: [S102](s102-test-plan.md),
  [S103](s103-test-plan.md), [S112](s112-0628-ic-wave.md),
  [S115](s115-test-plan.md), [S118](s118-test-plan.md),
  [S119](s119-test-plan.md) and [S121](s121-test-plan.md). The S117 record
  retired with ACT-0958 on 2026-09-30. Its §3.3 failed-turn rows are carried by
  the S122 Q2/D1 allocation. Its §5 module-matrix allocation is dispositioned in
  the unclassified leads above. The text is at the
  [last revision](https://github.com/alilee/cranelisp/blob/7b1220c7/tests/plan/s117-test-plan.md).
- Kept whole, because citations reach most sections: [S116](s116-test-plan.md).
- The S115 instrumentation matrix is retired to Git
  ([last revision](https://github.com/alilee/cranelisp/blob/a07823d8/tests/plan/s115-instrumentation-matrix.md)). Its row
  verdicts were a dated S115 snapshot; some were later falsified. The current
  grade and evidence for each row are in the
  [safety-invariant register](../../design/arch/safety-invariants.md). Its
  standing lesson, that a row is verified only with a cited detection proof, is
  in [memory-safety coverage](memory-safety-coverage.md) §4.1. The R8 regrade it
  fed stays open in filing 0857.
- The Sprint-113 and Sprint-114 working plans and the S113 global risk
  assessment were deleted in S122
  (`git show 7b1220c7:tests/plan/`). Every row they allocated is a committed
  test under its planned family, a design that now states the mechanism
  ([binding-indirection consume](../../design/backend/binding-indirection-consume.md),
  [expansion qualification](../../design/int/expansion-qualification-scope.md),
  [the export-closure gate](../../design/int/int.md#67-public-candidate-exposure--the-export-closure-gate),
  [enforcement matrices](../../design/frontend/enforcement-matrices.md)), or
  a filing carrying its own subject (0694, 0811 and 0857 open; 0708 and 0745
  resolved in S122).
  Their standing rules are in §Standing coverage audit and §Traceability;
  their unlanded observation is the §15.2 persistence rows in §Active
  allocation. Their attributions, wave rulings and counts
  are dated S113/S114 and do not describe current status; the 0720 exemplar
  attribution in the S114 plan was later falsified by re-measurement
  ([0811](../../design/arch/fixmes/0811-attribution-closed-on-the-repro-never-re-measured-at-source.md)),
  while its reduced repro stands in
  [ADT-wrapped supersede](../adt_wrapped_supersede_leak_0720.rs). The S113
  assessment's ranking and depth recommendation were consumed by the
  user-ruled W5 frame and tier grades in the
  [safety-invariant register](../../design/arch/safety-invariants.md); the
  [risk register](risks.md) keeps only its standing classes.
- The S120 shared-role evidence delta and the S80 link-prerequisite e2e
  architecture plan are retired to Git (the
  [last S120 revision](https://github.com/alilee/cranelisp/blob/57253cf2/tests/plan/s120-evidence-delta.md)
  and the
  [last architecture-plan revision](https://github.com/alilee/cranelisp/blob/57253cf2/tests/plan/e2e-architecture.md)).
  The architecture plan's standing rules are the link-prerequisite and
  fresh-tmpdir rules in the [tests memory](../CLAUDE.md). The S120 delta measured the
  citation instrument that the shared document checker replaced, its last
  standing consumer was the retired S120 audit report, and its two package
  advisories are delivered in the shared package; the
  [repository gates](#repository-gates--maintenance-checks-never-compiler-authority)
  state the current conditions.
- The S104 utilization plan, the S105 attribution plan, the S109 index-feed
  attribution, the S111 drop-glue under-key record and the S111 Principle-24
  register are retired to Git (`git show fc49541f:tests/plan/`). Their standing
  content has current homes: the utilization mechanism, measured outcome,
  measurement rules and open depth obligations in
  [lenient evaluation](../../design/backend/lenient-eval.md) §2.8 and the
  [performance backlog](../../design/arch/backlog/performance.md) (0535, 0536);
  the attribution model in [effect concurrency](../../design/arch/effect-concurrency.md)
  §3.1.6 and its measurement seams in
  [ownership codegen](../../design/backend/ownership-codegen.md) §13.2.2; the
  structural cure for the phantom write in
  [integration](../../design/int/int.md#67-public-candidate-exposure--the-export-closure-gate)
  §6.7, with its firing record in the [closed S109 record](../../sprints/archive/sprint-109.md#findings-record-in-fixmes-if-not-already);
  canonical glue identity in [transitive drop glue](../../design/backend/transitive-drop-glue.md)
  §3.1; the classification criteria in [Principle 24](../../design/arch/principles/24-resolve-once.md)
  and its imported-base tripwire in
  [monomorphisation](../../design/typecheck/monomorphisation.md) §11.8.9. Their
  unresolved residuals are the S104, S109 and S111 leads above.

The following compact closure records remain because other current records
point to their specific evidence, which must not be lost during consolidation.
They are dated evidence, not a second active sprint timeline.

## S122 — W3c traceability reconciliation (0766 / 0771)

2026-09-10, QA record-only closure. Current source assertions below were checked
against the executing stocktake at compiler `dc78ddbe`; each named case is PASS
in `/tmp/cranelisp-s122-stocktake-nextest.log`. No new test run or stronger
acceptance claim is implied. These current rows supersede historical S116 RED /
non-scaling descriptions for the named cells only. Run/link axes remain exactly
those selected by each source fixture; both-toggle equality is not by itself a
separate negative-test or mutation proof.

| Requirement / observed obligation | Test | Executing evidence |
|---|---|---|
| §12.3.1 exact allocation/deallocation balance; both ownership toggles | `tests/rc_escape_release_0763::curried_local_closure_applied_immediately_balances` | PASS in S122 stocktake |
| §12.3.1 exact allocation/deallocation balance; both ownership toggles | `tests/rc_escape_release_0763::curried_local_closure_let_bound_in_same_frame_balances` | PASS in S122 stocktake |
| §12.3.1 exact allocation/deallocation balance; both ownership toggles | `tests/rc_escape_release_0763::curried_local_closure_escaping_its_frame_balances` | PASS in S122 stocktake |
| §12.3.1 exact allocation/deallocation balance; both ownership toggles | `tests/rc_escape_release_0763::curried_escaping_closure_with_string_capture_balances` | PASS in S122 stocktake |
| §12.3.1 exact allocation/deallocation balance; both ownership toggles | `tests/rc_escape_release_0763::lambda_returned_through_nested_lets_balances` | PASS in S122 stocktake |
| §12.3.1 exact allocation/deallocation balance; both ownership toggles | `tests/rc_escape_release_0763::vec_literal_returned_through_let_balances` | PASS in S122 stocktake |
| §12.3.1 exact allocation/deallocation balance; both ownership toggles | `tests/rc_escape_release_0763::lambda_capturing_a_closure_balances` | PASS in S122 stocktake |
| §12.3.1 exact allocation/deallocation balance; both ownership toggles | `tests/rc_escape_release_0763::adt_wrapped_vec_argument_balances_both_toggles` | PASS in S122 stocktake |
| §12.3.1 exact allocation/deallocation balance; both ownership toggles | `tests/rc_escape_release_0763::adt_wrapped_string_argument_balances_both_toggles` | PASS in S122 stocktake |
| §4.6.3 local non-trait auto-curry resolution | `tests/shadowing_scope_lookup::local_closure_auto_curry_non_trait_control_resolves_to_local` | PASS in S122 stocktake |
| §12.3.1 exact superseded-value balance; both toggles | `tests/adt_wrapped_supersede_leak_0720::adt_wrapped_supersede_loop_does_not_leak` | PASS in S122 stocktake |
| §12.3.1 exact superseded-value balance; both toggles | `tests/adt_wrapped_supersede_leak_0720::adt_wrapped_supersede_residue_does_not_scale_with_n` | PASS in S122 stocktake |
| §12.3.1 exact superseded-value balance; both toggles | `tests/adt_wrapped_supersede_leak_0720::bare_vec_supersede_loop_balances_green` | PASS in S122 stocktake |
| §12.3.1 exact transitive capture/field balance; both toggles | `tests/capture_drop_glue_strands_nested_heap_0760::closure_capturing_vec_of_strings_does_not_leak` | PASS in S122 stocktake |
| §12.3.1 exact transitive capture/field balance; both toggles | `tests/capture_drop_glue_strands_nested_heap_0760::closure_capturing_adt_with_string_field_does_not_leak` | PASS in S122 stocktake |
| §12.3.1 exact transitive capture/field balance; both toggles | `tests/capture_drop_glue_strands_nested_heap_0760::nested_adt_chain_past_glue_depth_limit_does_not_leak` | PASS in S122 stocktake |
| §12.3.1 exact transitive capture/field balance; both toggles | `tests/capture_drop_glue_strands_nested_heap_0760::closure_capture_controls_balance_green` | PASS in S122 stocktake |
| §12.3.1 exact transitive capture/field balance; both toggles | `tests/capture_drop_glue_strands_nested_heap_0760::borrowed_argument_twins_of_k_and_l_balance_green` | PASS in S122 stocktake |
| §12.3.1 exact transitive capture/field balance; both toggles | `tests/capture_drop_glue_strands_nested_heap_0760::adt_wrapping_vec_of_adts_balances_green` | PASS in S122 stocktake |
| §12.3.1 exact transitive capture/field balance; both toggles | `tests/capture_drop_glue_strands_nested_heap_0760::nested_adt_chain_up_to_glue_depth_limit_balances_green` | PASS in S122 stocktake |

The two ADT supersede cells jointly cover N = 1, 2, 200, 400 with exact
`allocs == deallocs`, not a non-scaling residue bound. The depth cells cover
1–4 and 5–6; the historical depth cutoff is not current implementation policy.
The retired `ms_p6_mode_self_tests::m3_parity_catches_planted_leak` remains a
source tombstone, not an active test or an owed new check; the existing clean
control remains separate. No PLAN row currently names that retired function
as live coverage.

0771 is superseded: the current S101 historical postmortem §2.1 contains
neither of its alleged `program::tests::` citations, and its S109 citation
freeze explicitly preserves dated source coordinates. Current unit homes are
`crates/cranelisp-typecheck/src/program/callees/tests.rs` and
`crates/cranelisp-typecheck/src/program/mono_collect/tests.rs` (the latter holds
`cross_module_imported_constrained_fn_monomorphises_in_defining_scope`). Do not
rewrite the frozen historical analysis or restore the retired test-path alias.


## S122 — 0779 drain-polarity evidence closure

The [S122 attribution and completion record](s122-evidence-delta.md#phase-5-attribution-observations)
retains the Deferrable/Final observation, intended polarity-plant failure,
restored GREEN and closed review. This is the filing's resolved evidence
pointer; no new observer or public test is allocated.


## S122 — 0936 production realization-roster closure

`src/bootstrap.rs::bootstrap_generic_uniform_body_roster_is_closed` runs real
`mount_synthetic_modules` over fresh tables and enumerates generic hand-written
bodies using current HostPromised/UniformRust carriers. The observed closed set
is primitives bind, race, select and catch-runtime-error, each HostPromised and
slot-less. This is the current production measurement, not an assumption that
the historical four-member list remains correct or that the proposed inline
trajectory has occurred. The cell labels the backend realization contract; it
asserts exact equality so an extra member fails. The existing catch scheme/slot
control passes alongside it:2/2, run `cf467c35-ac84-4087-8017-f9336e3f5eb6`,
`/tmp/s122-int-bootstrap-roster-result-dc78ddbe.log`. Representation dependencies
remain the existing uniform-word/IO/closure/result-layout contract; the roster
is a revisit list for changes to those representations, not a polymorphic
typecheck licence. No new plant or public matrix is required to relabel and
establish this production projection.

0936's plan/rustdoc and evidence obligations are satisfied and its QA filing is
resolved/deleted. This section is its durable closure carrier. 0932's linked
roster obligation is also satisfied; its design owner may retire that filing
with the already delivered vec-len inline/no-slot/no-shim disposition.
