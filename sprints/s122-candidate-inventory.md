# S122 candidate inventory — scope discussion

Owner: sprint. Checkpoint: `dc78ddbe`, 2026-09-09. Purpose: let the user choose
next-sprint outcomes across compiler quality, language function and user experience.
LLVM is excluded by user direction. REPL-agent evals are an explicit candidate.

This is the Phase-1 assessment snapshot. [SPRINT.md](SPRINT.md) is the live
scope, allocation and approval record; it carries the completed plan and the
next checkpoint. Candidate recommendations here do not override that plan.
Links for filings subsequently closed point to their current closure evidence;
the original assessment and 88-row inventory remain unchanged.

**Snapshot status: candidate-level QA triage complete for all 88 then-live filing paths.**
Source observations and existing executing evidence classify each filing below.
Unresolved mechanisms, intermittent behavior and incomplete evidence remain
explicit; this is not a fresh whole-context audit or a release judgment. No filing is closed, deferred,
re-targeted or authorized for implementation by this document. No sprint phase
has advanced. The user's request authorizes inventory and triage only.

The user authorized Codex-equivalent role allocation for this work, naming
Sol at high effort and Astra at medium effort. Independent QA triage completed
as the named native Codex `qa` agent on Astra at medium effort. The earlier
external Claude dispatch was rejected before launch; it is not retried.
QA's classifications are integrated below. Their priority is a recommendation
for scope discussion, not authority to implement or close the item.

## Current executing evidence

The default stocktake ran 5,909 tests: 5,889 passed, 20 failed, one skipped,
in 123.603 seconds. Fourteen environmental failures (11 socket permission
denials and three reactor timeouts) were rechecked outside the sandbox with a
sibling: 15/15 passed in 8.194 seconds. These are separate runs, not an aggregate
all-green result. No test was rerun for this inventory.

- Default run ID: `b5d19d16-6bf5-4265-bc02-18fb1f773fde`.
- Local log: `/tmp/cranelisp-s122-stocktake-nextest.log`.
- Local recheck: `/tmp/cranelisp-s122-stocktake-network-recheck.log`.
- Six remaining REDs are the three generic-redefinition witnesses and two
  failed-turn witnesses in [spec_11_stdlib](../tests/spec_11_stdlib.rs), and
  `stdlib_core_io_public_scalar_driver_across_modes` in
  [stdlib_conformance](../tests/stdlib_conformance.rs).
- Monomorphic replacement and explicit-bind composition controls pass.
- The default run does not establish feature-enabled agent health, live-model
  quality, every diagnostic lane, performance, or absence of untested defects.

The [S121 close](archive/sprint-121.md#outcome-phase-7) is the authority for the accepted
carry and its limits. Failing tests are not six proven independent root causes.

## Proposed discussion order

| Candidate outcome | Compiler quality | Language function | User experience | Current footing and next decision |
|---|---|---|---|---|
| Correct generic redefinition | Stale compiled behavior and signal termination are observed | Replacement must execute the new definition under the existing contract | Reliable interactive iteration | First priority already directed at S121 close. QA attributes scalar/vector observations separately; fix follows a seam-level RED. |
| Meaningful failed-turn recovery coverage | Four historical witnesses do not establish that their trigger failed | Preserve existing publication/recovery semantics | Recovery and diagnostics remain trustworthy after an error | ACT-0958; two current REDs, two potentially false-green witnesses. QA must allocate an armed failure/control. |
| Working sequence-IO composition | Runtime RC abort observed | Public IO composition across REPL/run/link | Ordinary stdlib programs complete | Public RED and explicit-bind GREEN control exist. Internal attribution remains unassigned; no assumption that this shares the older IO defects. |
| Reconcile reload realization | Unused public foundation and retained old mechanism | Effect on current reload promise must be determined | Avoid stale interactive results | 0553 + src audit F-1. Source confirms the mismatch; it does not prove a cause for the generic REDs. |
| Source-verified closure of older correctness claims | Memory, identity, cache and publication records may name residuals or already-fixed behavior | Includes macro, import, constructor and trait claims | Crashes, rejected programs and confusing output if still live | All nine filing groups below need owner verification; do not schedule one fix per historical title. |
| Repeatable REPL-agent evals | Exercises the delivered compiler as an outside consumer | Check generated programs against task outcomes | Measure whether assistance succeeds, and where it struggles | New user candidate. Existing deterministic tests, traces, scenario stamps and tuning plan are inputs; QA defines a small real-task baseline and graders. Provider/model, budget and task corpus require decisions before live runs. |
| Better discovery and learning | No existing compiler defect is inferred from a future feature | Full semantic search; tutorial contract | Search consistency, readable collections, guided learning | ACT-0952, ACT-0951/0052, 0050, 0463 and 0821/0823 (closed S122: examples-local library ruling established). Feature/policy decisions, not automatic bug-clearance obligations. |
| Truthful and economical maintenance records | Reduce stale guidance and review noise | Usually indirect | Mainly contributor experience | Audit disposition trails, platform records, API-baseline formatting, citation roots, shared-role residuals and root-file cleanup. Preserve user-owned notes pending decision. |

This order recommends discussing observable failures before optional expansion.
It neither assigns severity to unverified historical claims nor silently defers
any item. A green historical repro is closure evidence only for what it tests;
its owning role must verify the filing's complete remaining obligation.

## Local verification already available

| Claim checked | Source opened / observation | Limit |
|---|---|---|
| Reload mismatch | `src/redefine.rs` retains `capture_instantiation_drivers`; `src/session_v4/lifecycle.rs` appends `extra_forms`; `crates/cranelisp-typecheck/src/form.rs` defines `instantiate_demands`; source search has no production call under `src/` | Confirms src audit F-1, not a runtime cause or required implementation. |
| Contradictory source map | `src/lib.rs` declares `repl` and immediately says the module was deleted | Confirms src audit F-2; small owner correction candidate. |
| 0944's absence claim | `tests/CLAUDE.md` has a standing “Coverage by definition variants” section | The claim that the lens is nowhere recorded is stale; full disposition belongs to QA. |
| 0917 | Existing permanent run/link repros in `tests/nullary_arm_beside_boxed_arm_0917.rs` pass in the stocktake; S120/S121 records report accepted repair; final notation cleanup committed at eac3c1be and filing retired | Stale-status candidate; do not count as an observed current leak. |
| Failed-turn trigger | `tests/spec_11_stdlib.rs` still uses `vec-flatten`, with no positive initial-failure assertion in the four witnesses | Matches ACT-0958's evidence issue; no replacement failure is invented. |
| Search narrowing | `src/session_v4/index_worker.rs` removes direct macro forms in its isolated source feed | ACT-0952 is a stronger semantic-search proposal, not proof of violation of the narrowed contract. |
| API baseline formatting | `tests/public_api_relocations.rs` omits auto-derived impls but retains auto-trait impls | ACT-0955 remains a format-change candidate; no API change authorized. |
| Agent eval substrate | `tests/agent.rs`, `tests/scripts/run-agent-lane.sh`, `src/agent/log.rs`, `tests/plan/agent-context-tuning.md` | Instrumentation and scenario guidance exist; no dedicated model-quality runner found in the searched test/script surfaces. No live evaluation was run. |
| Backend S110 R7 | `crates/cranelisp-types/src/module.rs` now returns `GotExhausted` when slot allocation has no free slot; the stocktake passes the typecheck error-mapping test | The old unchecked-allocation claim is superseded; a complete audit disposition still needs its owner's review. |
| Types S118 R3 | `crates/cranelisp-types/src/module.rs` now escapes dots and underscores distinctly in `got_data_symbol_name` | The original collision claim is superseded. Its current rustdoc names a separate platform-namespace carve-out residual, referred to QA for classification. |

## Live FIXME inventory

All 78 paths are included once, grouped by subject. Assessments and next owners
are QA recommendations. **Defect** denotes current executing evidence or a
source-observable order violation; **claim** retains an unestablished hypothesis;
**evidence** denotes a discrimination gap; **maintenance** covers records,
tooling and bounded convergence; **choice** denotes optional stronger behavior;
**stale** means the central historical claim is refuted or completed, with any
remaining tail retained. No stale row is automatic closure authority.

Priorities: **P1** correctness/recovery first; **P2** verify or complete beside or
after P1; **P3** bounded maintenance; **C** user scope choice. Axes: **Q** compiler
quality, **L** language function, **U** user experience. Across all 88 filings,
QA assigned six P1, 29 P2, 46 P3 and seven C rows. Thirty-eight rows have a stale
central claim, including mixed evidence/maintenance tails. These counts exclude
the public defects retained directly in tests and do not count independent roots.

### Redefinition, reload and publication

| ID | QA assessment and source observation | Priority; axes | Owner / next step |
|---|---|---|---|
| [0553](../design/arch/fixmes/0553-instantiate-symbol-at-types-entry-point.md) | **maintenance / claim; implementation in progress** — The opening replay helpers are now absent from `src/redefine.rs` and `src/session_v4/lifecycle.rs`. Reload-demand convergence is in the active Binary/int stream; required evidence and filing closure remain pending. | P1; Q,U | arch then design(src) |
| [0604](../design/arch/bounded-contexts.md) | **closed: structural obligation** — BC §6 preserves QA’s existing no-flip retirement ruling, current publication/census contract and corrected regression-sweep scope. Historical firing attribution remains explicitly unconfirmed. | P2; Q | QA plus design(src) |
| [0740](../design/arch/bounded-contexts.md) | **closed: census** — Current isolation design and source commentary account for all three session-init seams and candidate-before-publication routes; the owned record obligation is discharged. | P3; Q | design(src) |
| [0793](../design/arch/bounded-contexts.md) | **closed: census** — The PRIMITIVES_TABLE whole-table initialization has its explicit disposition in the current design and source census; no new initialization mechanism was needed. | P3; Q | design(src) |
| [0818](../design/arch/bounded-contexts.md) | **closed: preserved attribution limit** — The contaminated-probe signature remains an unconfirmed explanatory lead for the historical firings. BC §6 and the retained test state that limit; structural closure does not depend on reconstructing unavailable provenance. | P2; Q | QA |
| [0863](../design/arch/fixmes/0863-cluster-wide-prepared-macro-presentation-transaction.md) | **stale / evidence** — Current macro-turn design explicitly supersedes temporary prepared publication with immediate one-module checkpoints. Current spec_11 echo/introspection tests consume that behavior. Reconcile old transaction wording; do not implement the superseded prepared world. | P2; Q,U | QA/design(src) |
| [0868](../design/arch/fixmes/0868-cache-restored-parent-does-not-enrol-private-child.md) | **stale** — Exact `tests/cache.rs::cache_restored_parent_enrols_private_test_child` passes in stocktake. Source/cache orchestration has moved since filing; retire based on current guard, not the old open status. | P3; L,U | QA/src |
| [0869](../design/typecheck/CLAUDE.md#redirections) | **stale** — `SymbolTable.written_trait_impls` exists; cache schema documents carrier validation; exact `cache_restores_sibling_written_trait_impls_for_dispatch` passes. Carrier loss is fixed on the represented path. | P3; Q,L | QA/typecheck/src |

### Runtime ownership and result lifetime

| ID | QA assessment and source observation | Priority; axes | Owner / next step |
|---|---|---|---|
| [0745](../design/arch/fixmes/0745-entry-payload-leak-misattributed-to-protect-return-value.md) | **stale** — `src/result_owner.rs` owns result release; stocktake program-result ownership rows pass. S121 source-verification record classifies central attribution superseded. Preserve original-aggregate limits rather than equating a reduced fix with all exemplar leaks. | P3; Q,U | QA/design(src) |
| [0747](../design/arch/fixmes/0747-wb5-collapse-acceptance-is-self-contradictory.md) | **claim / maintenance** — `design/backend/s115-carrier-and-rc-sweep.md` and filing describe a contradictory historical byte-identical acceptance constraint. Current fn_compiler has evolved; settle remaining skip/provenance obligation before scheduling a refactor, not a new defect assertion. | P2; Q | design(backend) |
| 0781 (retired S122) | **stale / evidence** — Current `match_scrutinee_yielded_borrow_0781` controls and owned/borrowed expression cases pass. Central fix and attribution are delivered; guards remain in `tests/match_scrutinee_yielded_borrow_0781.rs`. | P3; Q | QA/test |
| 0782 (retired S122) | **stale** — S121 source-verification record marks the central double-release fixed; current match/scope regression surface passes in stocktake. Do not infer a live double free from its open title. Pinned by `scrutinee_ownership_tests.rs::consuming_arm_releases_the_owned_scrutinee_exactly_once`. | P3; Q | backend/QA |
| 0835 (retired S122) | **stale** — Current `slist_sconcat_ownership_0835` direct A/B/control tests all pass. The source marshal/consume surface has changed. Do not conflate closure of this runtime embedding defect with macro-turn 0889 or untested derive ceilings [0815](../design/arch/fixmes/0815-derive-ord-macro-expansion-panics-then-hangs.md). | P3; Q,L | QA/runtime owners |
| [0889](../design/arch/fixmes/0889-recover-the-macro-turn-marshal-leak.md) | **defect; integration in progress** — `src/marshal.rs` and `src/expander.rs` now transfer typed owners and consume successful results. The strengthened public pair now balances in both cases after the backend return-ownership correction (`0ce70208`). Scoped review and the matched aggregate comparison are complete; remaining residue is 46 and unclassified. Generated runtime API confirmation is pending; see the live evidence delta. | P1; Q,U | design(src), QA; runtime prerequisites |
| 0898 (retired S122) | **maintenance; implementation delivered** — `src/result_owner.rs` and `crates/cranelisp-backend/src/lib.rs` now use `ConcreteType::result_root`. The duplicate rule is removed; `ConcreteType::result_root` is canonical. No new leak is inferred from this convergence. | P2; Q | src then backend owners |
| [0906](../design/arch/fixmes/0906-vec-element-inc-adapter-hand-rolls-the-nullary-skip-guard.md) | **maintenance; implementation delivered** — `crates/cranelisp-backend/src/compiler/vec_codegen.rs` now uses the shared guard at all five selected sites. Module evidence and review pass; actual solution-golden selection and owner filing closure remain pending. | P2; Q | backend |
| [0907](../design/arch/fixmes/0907-io-bind-existential-ctor-defeats-canonical-glue-derivation.md) | **stale / evidence** — Runtime now has tag-directed IO disposal and ABI-10 Pure payload handling. “Every concrete IO release refuses” is false against current successful IO controls. Sequence-IO remains independently RED; do not automatically attribute it here. | P2; Q,L | QA/backend/intrinsics |
| [0913](../design/typecheck/CLAUDE.md#redirections) | **stale** — Exact `residual_type_param_result_leak_0913::unannotated_result_turn_releases_like_its_annotated_twin` passes in stocktake; it checks marginal allocator balance. Retire old displayed-residual leak claim against that evidence. | P3; Q,U | QA/typecheck/src |
| 0916 (folded into [0903](../design/arch/fixmes/0903-s4-1-frame-key-excludes-two-measured-escapee-families.md)) | **stale** — `tests/trait_scrutinee_scalar_payload_0916.rs` explicitly falsifies TCO-loss attribution and pins scalar threshold behavior. Stocktake has no failures there. Reconcile under concrete-instance work, not a tail-call implementation package. | P3; Q,L | QA/typecheck/backend |
| 0917 (retired S122) | **resolved** — S120 provenance correction and passing run/link/exemplar witnesses verified; final notation cleanup committed at eac3c1be. The independent residue-threshold retirement remains allocated in QA PLAN. | P3; Q | QA/backend |
| 0921 (retired S122) | **resolved** — `crates/cranelisp-intrinsics/src/handle.rs` provides typed `Owned` transfer; typed `consume_slist`/`consume_sexp` are consumed by `src/marshal.rs`. Canonical contract: `design/runtime/s119-typed-consume-funnel.md`. | P2; Q | arch/intrinsics/src |
| [0927](../design/int/macro-turn-ownership.md) | **resolved** — Rule-0 enforcement is absorbed: clause preparation clears the inferred ownership summary and the named unit fence exists. The design owner verified source during the S122 consolidation; the filing is retired. Macro leak recovery is a separate obligation. | P2; Q | design(src) |
| 0928 (retired S122) | **rulings recorded** — The typed handle and consume funnels are delivered; settled boundary rulings live in `design/runtime/s119-typed-consume-funnel.md`. Its §9 retains the missing debug-only Drop rustdoc obligation. | P2; Q | dev(intrinsics) |
| [0934](../design/arch/fixmes/0934-bind-payload-glue-word-dissolves-the-face4-residual.md) | **stale / evidence** — Intrinsics PurePayloadState and atomic claim/discharge logic exist; platform documents ABI v10 payload-glue append; backend Pure-stamp tests pass. Central layout mechanism landed. Reconcile unrun-Bind and cancellation acceptance; ACT-0956 is a distinct evidence tail. | P2; Q,L | QA/runtime/backend/platform |

### Concrete instances, identity and cache contracts

| ID | QA assessment and source observation | Priority; axes | Owner / next step |
|---|---|---|---|
| 0637 | **resolved and deleted 2026-09-24** — `crates/cranelisp-backend/src/cache/serialize.rs` validates ExternShim borrowed-sibling slots and has `SiblingSlotOutOfRange`; its exact corrupt/highest-legal-slot test passes in stocktake. Backend design verified the validation arm and existing planted-cell pass before disposal. | P3; Q | Complete |
| [0762](../design/typecheck/CLAUDE.md#redirections) | **stale** — `crates/cranelisp-typecheck/src/ownership/transfer.rs` ProjectionOf now reads `arg_origins.get(k)` with conservative unknown-origin fallback, not raw `args[k]`; cache summary-index validation exists. Old raw-index claim refuted. | P3; Q | typecheck/QA |
| [0891](../design/arch/fixmes/0891-d2-entry-check-escapee-generic-ctor-template-param.md) | **stale** — Central old template admission was superseded by non-concrete release and lifecycle migration; current S121 record explicitly marks central claim resolved. Verify remaining exact negatives with 0924/0931 rather than reinstalling sanctioned shallow RC. | P3; Q | QA/backend |
| [0903](../design/arch/fixmes/0903-s4-1-frame-key-excludes-two-measured-escapee-families.md) | **stale / evidence** — Current 0916/0917 and residual-result tests pass; old “one frame class” premise was explicitly replaced. Verify the original corpus/CLIF residual obligations together with 0924, not a new TCO or general IO exclusion. | P2; Q,L | QA/backend/typecheck |
| [0924](../design/typecheck/CLAUDE.md#redirections) | **stale / evidence** — Current lifecycle concreteness and passing accessor/trait threshold/result guards contradict broad non-concrete-frame failure claim. Verify the named instance families and original corpus before final closure; no new broad migration justified by historical source coordinates. | P2; Q,L | QA/typecheck |
| [0929](../design/arch/fixmes/0929-r18-instance-census-incomplete-two-ungraded-fabrication-arms.md) | **evidence / maintenance** — `design/arch/safety-invariants.md` R17/R18 now explicitly enumerate fabrication arms and census residual grade. `crates/cranelisp-typecheck/src/ownership/fixpoint.rs` now uses fallible from_type mapping. Old “two absent census arms” is stale in part; verify remaining named falsifiers/allow-list rather than inventing sealing. | P2; Q | QA/arch; per-site owners |
| [0931](../design/arch/fixmes/0931-ctor-monomorphisation-and-template-slot-retirement.md) | **stale / evidence** — `lifecycle.rs` carries distinct template/concrete states and rejects non-concrete slot claims; current collector uses MonoDemand/canonical identity. Template-slot retirement has landed materially. Final constructor family/corpus reconciliation remains owner work. | P2; Q,L | QA/types/typecheck/backend |
| [0932](../tests/plan/PLAN.md#s122--0936-production-realization-roster-closure) | **closed: implementation and evidence** — `vec-len` is inline, slot-less and absent from shim harvest; the linked current production-roster obligation is discharged by 0936 evidence. Architecture retired the filing without new lowering work. | P3; Q,L | QA/primitives/src |
| [0933](../design/arch/fixmes/0933-platform-sig-residual-type-var-must-refuse-at-mint.md) | **stale / evidence** — `src/platform.rs` goes through fallible table.install_platform; types lifecycle has NonConcreteSlot refusal. Old unchecked direct insertion is gone. Verify located lowercase-manifest negative and specific diagnostic before closure. | P2; Q,L | QA/src/types |
| [0935](../design/typecheck/CLAUDE.md#redirections) | **stale** — Current mono_collect passes `resolved.canonical` to mono_demand_from_spans; old resolved.fq.symbol remains only in stale comment in that inspected arm. Reconcile alias/accessor dedup witnesses; do not implement written-to-canonical migration again. | P3; Q,L | QA/typecheck |
| [0936](../tests/plan/PLAN.md#s122--0936-production-realization-roster-closure) | **closed: production evidence** — Real bootstrap roster and existing catch control pass (2/2, `cf467c35`). QA reconciled the current four slot-less HostPromised entries and their representation dependencies; the expected set comes from current bootstrap, not the historical I-ABI list. | P3; Q | QA/test |

### Language forms and name resolution

| ID | QA assessment and source observation | Priority; axes | Owner / next step |
|---|---|---|---|
| [0708](../design/arch/fixmes/0708-annotation-not-folded-in-macro-argument-position.md) | **stale** — Reader `read_colon_prefix` constructs Annotated universally, including macro arguments; `annotation_fold_macro_arg_0708::annotation_folds_in_macro_argument_position` passes. No repeat reader implementation. | P3; L,U | QA/spec reconcile tail |
| [0785](../design/arch/fixmes/0785-return-position-annotation-syntax-unenforced-corpus-colonised.md) | **stale / evidence** — Reader rejects dangling annotation introducers; current trait fixtures explicitly use repaired syntax. Only verify the requested exact solution-level negative and trace, not another grammar change. | P3; L | QA |
| [0789](../design/arch/fixmes/0789-export-reader-quote-predicates-from-frontend.md) | **maintenance** — `crates/cranelisp-types/src/sexp.rs::quote_head` exists and frontend consumes it, but `src/expander.rs` still defines local QuoteHead/quote_head and macro_resolution calls that bridge. Concrete remaining duplicate; no new frontend API needed. | P2; Q | design/dev(src) |
| [0794](../design/typecheck/CLAUDE.md#redirections) | **stale** — `crates/cranelisp-typecheck/src/traits/impl_check.rs` mints with `fq_trait_name.name`; stocktake qualified conventional/HKT impl positive and negative witnesses pass. The as-written qualifier defect is fixed. | P3; L,U | QA/typecheck |
| [0798](../design/arch/fixmes/0798-testing-module-alias-not-usable-as-qualifier.md) | **stale / evidence** — `src/imports.rs` registers scoped `<owner>.<alias>` and restores aliases from cache. “Never registered” is refuted. Verify full alias-only/value/type/constructor behavior against current witnesses before final closure; no new missing-feature implementation justified by old title. | P2; L,U | QA/src |
| [0799](../design/typecheck/CLAUDE.md#redirections) | **claim** — Current spec_04 auto-curry tests cover ordinary/constrained cases, but the searched surface did not establish the sharpened supplied-free-variable/curry-then-apply case. Retain wrong-reject claim for a minimal current repro. The residual-free-variable normative question is separate. | P1; L,U | QA then test/typecheck |
| [0800](../design/arch/fixmes/0800-def-macro-expansion-leaks-internal-thunk-name-and-blocks-call.md) | **claim / evidence** — `stdlib/defs.cl` and current spec_11 multi-definition echo witnesses reflect the new checkpoint world. Old thunk-only presentation cannot define scope; verify the separately retained function-valued application tail. Overlaps 0863; avoid reintroducing PreparedMacroTurn. | P2; U,L | QA then src/stdlib |
| [0815](../design/arch/fixmes/0815-derive-ord-macro-expansion-panics-then-hangs.md) | **claim / evidence** — `stdlib/derive/helpers.cl` still records multi-field/three-constructor ceilings; `stdlib/derive/test.cl` deliberately excludes them. 0835 direct repros pass, so old heap attribution is insufficient. Revalidate the actual omitted derive cases before a fix or closure. | P1; L,U,Q | QA then test, attributed owner later |
| [0841](../design/arch/fixmes/0841-qa-when-unless-have-no-spec-home-and-9-10-cites-them.md) | **stale** — `spec/09-macros.md` now explicitly documents when/unless, Some/None results, unconditional wrapping and nested Option behavior. The claimed missing semantic home is refuted. | P3; L,U | QA/spec |

### Evidence adequacy and diagnostic instruments

| ID | QA assessment and source observation | Priority; axes | Owner / next step |
|---|---|---|---|
| [0694](../design/arch/fixmes/0694-qa-suite-count-nonreproducible-two-interleaving-dependent-guards.md) | **claim / evidence** — `tests/nullary_return_dispatch_method_only_import.rs` named witness passes in stocktake, as do relevant macro tests; one green run cannot retire historical load-dependent publication claims. Require current mechanism evidence before a race fix or new detector. | P2; Q,U | QA |
| [0761](../design/arch/fixmes/0761-qa-exact-rc-balance-lane-owning-type-by-position-matrix.md) | **evidence** — `tests/helpers/e2e.rs` SafetyMatrix RC face remains differential and skips comparison if counters are absent. Existing exact-balance tests and S121 supersession record mean this is not “no absolute evidence anywhere.” Reconcile promised standing lane and exclusions; identify residual before adding another lane. | P2; Q | QA |
| [0766](../tests/plan/s122-evidence-delta.md#evidence-owned-filing-disposition-allocation) | **evidence** — Named `rc_escape_release_0763`, `adt_wrapped_supersede_leak_0720` and `shadowing_scope_lookup` tests are present in the current test surface. This is plan/spec-side trace reconciliation; test presence does not establish every requested annotation has been folded. | P3; Q | QA |
| [0771](../tests/plan/s122-evidence-delta.md#evidence-owned-filing-disposition-allocation) | **stale** — Opened `tests/plan/s101-coverage-postmortem.md` §2.1; the complained-of `program::tests::callees_*` citation is absent from current text. Retire or narrow the exact historical path claim. | P3; Q | QA |
| [0779](../tests/plan/s122-evidence-delta.md#evidence-owned-filing-disposition-allocation) | **evidence** — `crates/cranelisp-typecheck/src/program/mono_collect/tests.rs` has single- and multi-clause auto-curry witnesses. Filing's later ruling says four Final seams are construction-discharged and one discriminating cell remains; do not re-run the obsolete six-identical-tests proposal. Verify that remaining seam witness. | P2; Q,L | QA then dev(typecheck) |
| [0811](../design/arch/fixmes/0811-attribution-closed-on-the-repro-never-re-measured-at-source.md) | **maintenance** — Shared QA contract now explicitly requires original-aggregate remeasurement; historical s114 attribution still needs exact owner reconciliation. A reduced repro and a coincidental total are not interchangeable acceptance evidence. | P3; Q | QA |
| [0848](../design/arch/fixmes/0848-intrinsics-diagnostic-modes-need-detection-proofs.md) | **stale / evidence** — Current diagnostics test surface and S121 reconciliation report production detection work delivered. `tests/ms_p6_mode_self_tests.rs` still has retired-plant tombstones; final evidence must point at live replacements, not claim this old file itself arms every mode. | P2; Q | QA/intrinsics |
| [0857](../design/arch/fixmes/0857-regrade-r8-modes-against-live-detection-proof.md) | **evidence** — the retired S115 instrumentation matrix (last revision a07823d8) claimed a live e2e plant at line 55, while current `tests/ms_p6_mode_self_tests.rs` has tombstone prose there and only clean wiring tests. Repair the grading/citations against actual replacement detection proofs. | P2; Q | QA |
| [0859](../design/primitives/primitives.md#r-2-evidence-boundary--accepted-with-a-revival-trigger) | **closed: accepted evidence boundary** — Architecture verified the S121 user approval, existing nine production witnesses and PLAN revival trigger. The typed runtime migration adds no emission-live projection consumer; no additional observer is owed under that disposition. | P2; Q | QA |
| [0900](../design/arch/fixmes/0900-cell-15-locus-token-could-be-a-seam-form.md) | **maintenance** — `tests/adt_drop_glue_underkey.rs` is the referenced cell carrier; filing itself establishes crate-grain locus is valid. Optional finer diagnostic token, no correctness blocker. | P3; Q | test |
| [0944](../tests/plan/PLAN.md#standing-coverage-audit--definition-variants) | **stale / maintenance** — `tests/plan/memory-safety-coverage.md` and PLAN explicitly contain standing coverage-by-definition-variants lens/matrices. “Not recorded anywhere” is false. Reconcile visibility/currency tail, not a new category. | P3; Q | QA |

### Diagnostics and introspection

| ID | QA assessment and source observation | Priority; axes | Owner / next step |
|---|---|---|---|
| [0914](../design/arch/fixmes/0914-mem-delta-window-excludes-the-result-release.md) | **evidence acceptance** — `handle_mem` now releases the result before sampling; Q6 has RED→GREEN evidence. QA acceptance, the unit pin and stale spec/demo wording remain in the filing. | P1; U,Q | QA |
| [0915](../design/arch/fixmes/0915-codegen-diagnostic-exposes-mangled-doubled-internal-subjects.md) | **claim / evidence** — Backend CodegenFailed Display still nests module/symbol/cause; that alone does not prove public doubled/mangled output because a presentation adapter may repair it. ACT-0958's diagnostic trigger is unarmed. Establish a legitimate public failing case before changing diagnostics. | P2; U | QA then design(backend/src) |

### Learning and display

| ID | QA assessment and source observation | Priority; axes | Owner / next step |
|---|---|---|---|
| [0050](../design/arch/fixmes/0050-promote-list-seq-pretty-printer-aspirational.md) | **choice** — `repl/spec/01-display-format.md` still makes natural List/Seq rendering aspirational; no Collection implementation found. `design/arch/CLAUDE.md` records a settled S106 mechanism design and user forks, so “no design exists” is stale; implementation and normative promotion remain separate. | C; U | design(src), spec |
| 0052 (merged into [ACT-0951](actions/ACT-0951-specify-learn-feature.md)) | **choice** — The former user documentation plan is retired; ACT-0951 and current REPL authority supersede the old Ring-0 request. No complete tutorial contract may be inferred from historical prose. | C; U | spec; merge disposition with ACT-0951 |
| [0463](../design/arch/fixmes/0463-examples-network-poll-shape-example.md) | **choice** — `tests/examples.rs` and `examples/32-concurrency-combinators.cl` carry the plain example/combinator route; the filing's network leaf/client harness requirement is additional infrastructure, not a compiler failure. Revalidate enabling assets before estimating. | C; U,L | training with platform/test prerequisite |

### Platform usability and records

| ID | QA assessment and source observation | Priority; axes | Owner / next step |
|---|---|---|---|
| 0870 (retired S122) | **maintenance complete** — Platform facade documentation and the remaining HostCallbacks test comments match the current ABI. The contract lives in crate rustdoc; the finding is retained in Git history. | P3; U,Q | dev(platform) |
| 0871 (retired S122) | **resolved** — The platform design canon is established through `design/platform/CLAUDE.md`; obsolete platform design records are retired. | P3; Q,U | design(platform) |
| 0873 (retired S122) | **stale** — `crates/cranelisp-platform/src/declare.rs` exports schema_declares_type, supports adts:, and has declaration/missing/comment tests; `platforms/shapes` uses adts:. Selection and implementation exist. Canonical home: `design/platform/adt-marker-binding.md`; source and tests discharge the filing. | P3; U,Q | QA/platform/arch |
| 0874 (retired S122) | **stale** — `crates/cranelisp-platform/tests/common/mod.rs` now exists alongside separate product/sum/worked-example integration binaries. All three import common allocation helpers; central shared-fixture request is delivered. | P3; Q | platform/test |

### Design and delivery record quality

| ID | QA assessment and source observation | Priority; axes | Owner / next step |
|---|---|---|---|
| [0764](SPRINT.md#repro-before-fix-guidance-closure) | **maintenance** — Root CLAUDE and METHOD mandate repro-before-fix; the former local review command is a retired home. Reconcile wording with current shared review contract instead of editing deleted local commands. | P3; Q | shared review contract owner |
| [0765](SPRINT.md#repro-before-fix-guidance-closure) | **maintenance** — Current `.agents/skills/dev/SKILL.md` requires a spec-traced failing reproduction; root/METHOD also bind. Old local command target is obsolete; verify exact residual before adding duplicate policy. | P3; Q | shared dev contract owner |
| [0776](../design/arch/fixmes/0776-arch-settlement-seam-multiplicity-register-row.md) | **maintenance** — `crates/cranelisp-typecheck/src/program/mono_collect.rs` and its tests still carry explicit settlement/drain distinctions. The filing is a proposed invariant taxonomy, not a separate failure. Reconcile with present R17/R18/variant coverage before another register layer. | P3; Q | arch |
| [0777](../design/typecheck/CLAUDE.md#redirections) | **stale** — `design/typecheck/ownership-inference.md` now explicitly corrects face-3 row-4 insufficiency and explains the composition repair. The request to correct that premise is already reflected. | P3; Q | design(typecheck) |
| [0783](../design/arch/fixmes/0783-arch-shape-test-standing-in-for-a-derived-answer-register-row.md) | **maintenance** — Opened `design/arch/safety-invariants.md`: category-before-operation and fabrication rows now exist. Determine whether the proposed syntactic-proxy class adds anything beyond them; this is register disposition, not four new defects. | P3; Q | arch |
| [0795](../design/int/session-transaction.md#25-trait-implementation-redefinition) | **resolved** — `design/int/session-transaction.md` now states trait-prefix enrollment, explains why impl_.methods is insufficient, and names omitted-default witness. Exact requested documentary repair exists. | P3; Q | design(src) |
| [0938](../design/arch/fixmes/0938-arch-principle-wording-states-intent.md) | **maintenance** — Opened principle-authoring guidance: this asks for intent-authoring procedure, not a runtime correction. Reconcile package/current guidance and preserve user-arbitrated principle meaning; avoid deriving new policy from current code. | P3; Q | arch |
| [0939](../design/arch/fixmes/0939-arch-principle-11-early-branch-duplication-acid-test.md) | **maintenance** — Principle 11 currently states shared pipeline and origin but lacks the requested explicit early-branch audit question. Small wording candidate; no new audit or broad extraction implied. | P3; Q | arch |
| [0940](SPRINT.md#evidence-and-delivery-record-dispositions) | **maintenance** — METHOD still prohibits broken-build handoff generally; retired .claude/commands target cannot own migration exception. Reconcile intentional within-wave producer→consumer breakage and endpoint gates in current homes. | P3; Q | arch/shared dev owner |
| [0941](SPRINT.md#evidence-and-delivery-record-dispositions) | **maintenance** — METHOD gate has suite obligations, but original command target is retired. Fold with 0940, distinguishing an intermediate cascade build from completed product evidence; not a separate implementation stream. | P3; Q | arch/QA/shared owner |
| [0942](../design/arch/fixmes/0942-arch-design-doc-structure-convention.md) | **maintenance** — `design/CLAUDE.md` names content homes but does not carry the requested full document ordering. Current maintain-documents support may supersede generic procedure; reconcile before adding another template. | P3; Q,U | standing-document owner |
| [0943](../design/arch/fixmes/0943-arch-proposal-discipline-checklist.md) | **maintenance** — Principle 21 states actor/function modeling; shared quality standards already require cohesion, constructive controls and minimum cost. Decide any real receiver/data-ownership residual instead of duplicating generic procedure. | P3; Q | arch/shared owner |

## Live action inventory

All ten actions are included, using the same QA classification and priority key.
These are mixed requests, not ten compiler bugs. Each linked action retains its
completion criteria and source references.

| ID | QA assessment and source observation | Priority; axes | Owner / next step |
|---|---|---|---|
| [ACT-0947](SPRINT.md#runtime-before-state-and-scratch-cleanup) | **maintenance / choice** — Opened all six current paths: NOTES idea list, intrinsics scratch diff and four project/test fixtures remain. No removal authorized; verify references/purpose before deletion. User-owned NOTES is a separate decision. This does not block compiler correctness. | P3; Q,U | sprint; user for NOTES |
| ACT-0950 (retired: shared checker delivered) | **choice / maintenance** — At the opening checkpoint, the former citation script intentionally excluded general doc→doc roots; the old 214 count was not remeasured. The delivered shared checker and current scope are recorded in [the active sprint](SPRINT.md). Decide widened authority and repair economics; a maintenance guard must not become unrelated product acceptance. | C; Q,U | QA then owner repairs |
| [ACT-0951](actions/ACT-0951-specify-learn-feature.md) | **choice** — Current action explicitly removed provisional /learn contract and lists unresolved state/trigger/persistence semantics. 0052 is duplicate provenance. Specification package first if chosen. | C; U | spec, user then QA |
| [ACT-0952](actions/ACT-0952-complete-semantic-search-indexing.md) | **choice** — Action/current REPL interim contract exclude macro declarations from search and require future complete isolated compilation. Stronger semantics/background macro execution are pending choices; not a regression against interim promise. | C; U,L | spec/user then design(src) |
| [ACT-0953](actions/ACT-0953-decouple-live-slot-abi-from-ownership-inference.md) | **choice** — Existing redefinition tests explicitly reject ownership-ABI-changing same-type edits and pass. Removing restriction is a stronger contract, separate from the three currently failing generic replacements. | C; L,U | spec/user then arch |
| [ACT-0954](SPRINT.md#evidence-and-delivery-record-dispositions) | **choice / claim** — At `dc78ddbe`, the public wrapper in `src/session_v4.rs` queued work and returned; the lifecycle watcher path waited. The wrapper has since been removed; see the linked disposition. Public asynchronous contract deserves review, but no production wrapper consumer/race established. Prefer settling intended surface before coordination machinery. | P2; Q | arch then user |
| [ACT-0955](actions/ACT-0955-omit-auto-traits-from-public-api-baselines.md) | **maintenance** — `tests/public_api_relocations.rs` omits auto-derived impls but does not yet omit auto-trait impls. Coordinated baseline migration is concrete; assess required Send/Sync contracts and obtain exact resulting baseline approval. | P3; Q,U | arch/QA |
| [ACT-0956](SPRINT.md#select-ready-loser-evidence-closure) | **evidence** — io/tests has Select winner disposer transfer and other disposal rows; requested blocking-ready-loser oneshot barrier is a distinct missing discrimination. No new runtime mechanism follows from this evidence request. | P2; Q,L | QA then test |
| [ACT-0957](../tests/plan/s122-evidence-delta.md#act0957-residual-outcomes--qa-closure-disposition) | **maintenance** — Consume existing shared-role audit §9 residuals, not every original recommendation. Codex allocation authorization solves this dispatch's provider gap; it does not itself migrate the durable package/adapters or approve publication. | P3; Q,U | sprint/shared owner |
| [ACT-0958](actions/ACT-0958-rearm-failed-turn-recovery-coverage.md) | **evidence** — `tests/spec_11_stdlib.rs` four old failed-codegen witnesses use now-successful vec-flatten and omit trigger arming/process success. Two REDs/two potentially false GREENs. Replace evidence honestly; no permission to manufacture invalid compiler behavior. | P1; Q,U | QA then test; generic owner by attribution |


## Audit findings and deduplication

The latest located whole-context reports are indexed below. Earlier reports are
history inputs through each report's prior-assessment reconciliation; their
recommendations are not automatically additional live backlog. A missing filing
or empty disposition trail does not prove either completion or an outstanding
implementation defect. Older recommendation claims need current source checks.

| Assessment | Recommendations in the report | Recorded trail / candidate treatment |
|---|---|---|
| [Backend S110](https://github.com/alilee/cranelisp/blob/57253cf2/audits/cranelisp-backend-s110.md) | R1 disposition; R2 hard-miss negatives; R3 keying drift; R4 shims/ISA/front-door hygiene; R5 large funnels; R6 drop-glue convergence; R7 GOT exhaustion; R8 design currency | §4 contains a placeholder rather than a completed trail. Reconcile against later delivery, especially GOT/exhaustion and RC work, before reviving any finding. R1 includes earlier S107 dispositions. |
| [Frontend S113](https://github.com/alilee/cranelisp/blob/57253cf2/audits/frontend-s113.md) | R1 enforcement matrices; R2 qualified-name splitter; R3 head classifier; R4 synthetic S-expression kit; R5 docs; R6 hygiene; R7 reader/annotation cases | All accepted in S114, mapped to 0676–0682, which are absent from the live filing set. Verify closure through history/source; 0708 is a related live annotation carrier, not automatically a duplicate. |
| [Typecheck S114](https://github.com/alilee/cranelisp/blob/57253cf2/audits/cranelisp-typecheck-s114.md) | R1 stale 0590 disposition and riders; R2 master design; R3 test/module structure; R4 crate guidance | S115 trail accepts all four; R1 executed, others mapped to 0721–0724, absent from live filings. Reconcile rather than create duplicate work. |
| [Intrinsics S115](https://github.com/alilee/cranelisp/blob/57253cf2/audits/cranelisp-intrinsics-s115.md) | R1 detection proofs; R2 catalog count; R3 read helpers; R4 counters; R5 citations; R6 typed-context boundary; R7 record integrity | Accepted as 0848–0857; live carriers 0848 and 0857 remain. Related result-lifetime work has separate filings. Do not reopen all seven from historical prose. |
| [Primitives S116](https://github.com/alilee/cranelisp/blob/57253cf2/audits/cranelisp-primitives-s116.md) | R1 complete registration; R2 production ownership witnesses; R3 layout ownership; R4 master design; R5 facade rustdoc | §4 still says pending S117 disposition. R2 has the accepted 0859 evidence boundary above. Establish the other four's later outcomes. |
| [Platform S117](https://github.com/alilee/cranelisp/blob/57253cf2/audits/cranelisp-platform-s117.md) | R1 source facade; R2 design canon; R3 bounded-context records; R4 marker ergonomics; R5 shared fixture | All accepted as 0870–0874; 0870 is retired after the final test-comment repair. The delivered 0871/0873/0874 records were retired after source and evidence reconciliation; no new audit additions. |
| [Types S118](https://github.com/alilee/cranelisp/blob/57253cf2/audits/cranelisp-types-s118.md) | R1 dead exports/append seam; R2 facade truth; R3 injective GOT data-symbol identity; R4 rustdoc history; R5 citation refresh | §4 remains a placeholder. R3 pointed to now-absent 0748. Reconcile later delivery and tests before counting a current identity bug. |
| [src S121](https://github.com/alilee/cranelisp/blob/57253cf2/audits/src-s121.md) | F-1 unused instantiation API/replay mismatch; F-2 contradictory module comment; F-3 oversized orchestration functions | All three recorded unresolved. F-1 overlaps 0553; F-2 independently source-confirmed. F-3 recommends a decision only when a planned change opens a named function, not a broad extraction campaign. |
| [Shared-role integration S120](https://github.com/alilee/cranelisp/blob/57253cf2/audits/shared-role-integration-s120.md) | R1–R8, with S121 reconciliation | R2 and R5 recorded met. R1/R3/R4/R6/R7/R8 carried by ACT-0957. Details below; no extra action count. |

The six ACT-0957 residuals are:

| Recommendation | Remaining recorded question | User-facing axis |
|---|---|---|
| R1 | Fresh-clone promise versus unpublished contribution window; current reproducibility | Compiler delivery quality, indirect product impact |
| R3 | Ownership of AGENTS.md, .codex and remaining Copilot guidance | Contributor experience |
| R4 | Adapter generation and Copilot keep/drop | Contributor experience and maintenance cost |
| R6 | Missing-contract refusal and actual SIGTERM test evidence | Delivery-tool correctness |
| R7 | Recoverable session/dispatch accounting parity | Evidence provenance |
| R8 | Retired role names and dead METHOD anchor | Contributor navigation |

S121 publication supersedes the audit's intermediate dirty-package checkpoint;
see the close record. It does not by itself establish the remaining
fresh-clone or historical-accounting claims.

## Questions for the next triage checkpoint

1. Select scope from QA's source-backed classifications, retaining existing
   REDs and controls and the uncertainties on derive, curry and intermittent
   behavior. Passing residual witnesses are not proof of defect closure.
2. Reconcile older audit trails with source and later outcomes; retain an
   explicit unknown wherever evidence cannot be recovered.
3. Present grouped fix/evidence/record/feature candidates with owners, actual
   dependencies and proposed priorities on the three user-selected axes.
4. For REPL-agent evals, settle the real task corpus, outcome checks, reproducible
   starting state and model/run budget. Keep model-quality results distinct
   from deterministic compiler conformance and delivery-tool evaluations.
5. Obtain individual decisions for stronger feature contracts or genuine carries.
   This inventory grants none of those approvals.

## Source streams and candidate execution order

**Efficiency assessment: the earlier A–E themes were outcome priorities, not
an efficient implementation partition.** Replacement, macro ownership, language
claims and convergence all potentially touch the binary crate; executing those
as successive closed waves would reopen the same surface. The source streams
below replace that ordering. Scope remains unapproved, and unknown defect owners
are not guessed to make the table appear settled.

### Confirmed overlaps

These are source locations opened during coordination, not inferred common
root causes:

| Outcomes that would otherwise cause repeat visits | Shared source surface | Coordination consequence |
|---|---|---|
| Macro leak recovery 0889, quote-classifier convergence 0789, possible derive/def tails 0815/0800 | `src/expander.rs`, `src/marshal.rs`, `src/process_form/macro_resolution.rs`; derive/def ownership still needs current reproduction | Give the confirmed macro changes one binary owner and one cohesive change/review bundle. Bring any attributed derive/def obligation into that reservation before it closes. |
| /mem accuracy 0914, result-root convergence 0898, any attributed result-lifetime correction | `src/repl/commands.rs`, `src/result_owner.rs`; 0898 also consumes backend work | Plan the binary result-handling changes together; distinguish diagnostic observations from runtime acceptance. |
| Generic replacement REDs, reload realization 0553 and audit F-1 | `src/redefine.rs`, `src/session_v4/lifecycle.rs`; actual RED owner remains provisional | Reconcile the reload decision before releasing this binary submodule. Do not implement 0553 as a guessed fix. |
| Result-root convergence 0898, Vec tag-guard convergence 0906, any attributed backend defect | `crates/cranelisp-backend/src/lib.rs`, `crates/cranelisp-backend/src/compiler/vec_codegen.rs` | One backend reservation/evidence delta; no later generic “convergence wave” reopening it. |
| Agent eval harness, any resulting agent instrumentation or context changes | Existing `tests/agent.rs` and `src/agent/` boundaries | Keep a harness-only eval stream independent. Route any selected production-agent change into the binary reservation; do not authorize tuning merely by choosing evals. |

### Proposed source ownership

One continuing owner per implementation surface. Paths below are candidate
reservations, not permission to edit everything in a crate. No new crate-shaped
architecture or public interface is decided here. Each design/dev/review dispatch
still names exactly one permitted surface.

| Stream | Candidate reservation and combined work | Input needed before implementation | Closure obligation |
|---|---|---|---|
| Binary / integration | Selected paths under `src/`: replacement/reload, macro invocation and quote classifier, result ownership and /mem, confirmed def/derive integration tails, src audit comment repair; any selected `src/agent/` changes | Attributed failures; current reload ruling; approved runtime/typed-transfer contract; settled eval observation needs if they require production changes | Same owner through submodule bundles and dependency pauses. Close each bundle's source, module evidence, relevant solution evidence and records together; release the crate stream when its selected cross-surface obligations are complete. |
| Typecheck | Selected paths under `crates/cranelisp-typecheck/`: established curry/redefinition/derive producer defects and any verified instantiation-demand producer remainder | Current discriminating reproductions and approved semantics; do not rebuild already-delivered concrete-instance work | One typecheck evidence/design delta covering all selected incoming obligations; stale typecheck filings reconciled in this visit. |
| Backend | Selected paths under `crates/cranelisp-backend/`: 0898 consumer, 0906 adapter, and any backend-attributed current failures | Settled input/ownership contracts and attributed failures | One backend reservation. Convergence, implementation, regression evidence and backend record retirement travel together. |
| Intrinsics | Selected paths under `crates/cranelisp-intrinsics/`: macro-transfer prerequisite realization if retained by design, any attributed sequence-IO runtime correction, and selected disposal evidence | Reconcile already-landed IO work with still-absent typed-handle work; exact public API approval if needed | One runtime owner/evidence delta. Never infer that all IO observations share a mechanism. |
| Conditional producer/consumer surfaces | `crates/cranelisp-types/`, `crates/cranelisp-primitives/`, `crates/cranelisp-platform/`, or executable bundle only if an approved selected dependency actually requires them | Architecture names the necessary delta and affected consumers; source-confirmed completed work stays closed | Each necessary crate gets its own narrow role invocation and reservation. No blanket S121 migration replay or platform rewrite. |
| Independent solution evidence | Exact selected files under `tests/`, its fixtures and scripts, with one nominated owner per shared helper/file; QA owns the evidence plan | Current requirements, discriminating controls and the smallest settled evidence delta | Record REDs first; keep the reservation through green-up and trace reconciliation. Do not rewrite a common helper for each compiler stream or leave evidence debt for an end sweep. |
| Agent eval harness | A bounded eval runner/task corpus/report surface selected during design; use existing REPL/process/log interfaces where sufficient | Real tasks, observable graders, configuration/provenance and model budget; identify any production seam need early | Baseline plus comparable results and explicit known failures. Harness work can progress beside compiler work; selected production changes belong to the binary owner. |
| Language-facing artifacts | Selected `stdlib/`, `examples/`, `user/`, `repl/` and exemplar records, with separate owning-role invocations and path allocations | Accumulated delivered behavior and any explicit UX selection; derive reproduction happens earlier, not here | Apply the known consequences once per owned artifact; do not repeat full docs/training assessments after each compiler ticket. |
| Coordination / maintenance | Sprint records, audit disposition trail and selected shared-tooling choices | Source-backed owner outcomes; individual policy/cleanup choices | One nominated edit owner per shared register. Source comments and crate-local docs stay with their source stream, not a later cleanup campaign. |

### Candidate scheduling shape

1. **Resolve routing and gather the evidence delta.** Preserve known REDs and
   establish the outstanding derive/curry/def controls early. Reconcile reload
   and macro-transfer requirements in their approved phases. Identify the
   actual writable overlaps before implementations begin. Independent read-only
   work may run in parallel; an unrelated unresolved item does not become a
   new gate on already-settled work.
2. **Deliver approved producers and their consumers.** Architecture/design
   determine the dependency order. Collect every selected obligation reaching
   a crate into its single stream. An owner can pause for a dependency and
   resume without relinquishing the reservation or repeating whole-surface
   discovery, design and review. This may require ordered cross-crate slices;
   “one visit” does not mean an artificial all-at-once commit.
3. **Finish consumers and user-facing consequences.** The binary stream
   consumes settled contracts and completes its selected submodule bundles.
   Harness-only eval work may run alongside it and produce an early baseline;
   it need not wait for zero compiler defects. Apply accumulated documentation,
   examples and stdlib consequences in their owned surfaces.
4. **Verify the composition and accept.** Each stream arrives with its relevant
   tests, review and records already complete. Fresh integrated acceptance
   checks composition. Only new executing evidence that falsifies a completed
   outcome reopens the affected stream; rerun the affected checks, not every
   role and gate.

These are scheduling constraints and candidate streams, not a promised fixed
wave count. Formal Phase-4 waves follow scope, architecture and design approvals.
Before presenting them, sprint checks that each writable path has one owner,
every selected filing has one closure owner, producer/consumer dependencies are
settled, and planned reopenings have been merged or explicitly justified.
Existing artifacts carry this allocation; no new telemetry/control system is
needed to enforce the planning check.

Optional search, display or tutorial work must be selected before the relevant
source reservation closes if it is to join this sprint. Unselected feature
expansion does not delay defect closure. LLVM remains excluded. Codex-equivalent
allocation remains authorized; it does not authorize later phase transitions.

## Verification and dispatch provenance

The register was generated from the current directory entries: 78 FIXME files,
ten action files, each linked once in its inventory table. QA's 88-row report
was checked for exact set equality and integrated into those same rows. Links
are checked locally; source observations, known executing results and unresolved
claims are explicitly distinguished. No formal disposition follows from triage. Nine latest assessment
reports are indexed with their recorded trails. The 88 records, nine reports,
six RED tests and eval candidate are overlapping sets and must not be added
into a single issue count.

QA dispatch attempt: configured Claude `fable`, `high` effort, through
`.agents/tools/claude_role.py`; approval review rejected process creation.
That rejected attempt has no provider session or QA report. The brief remains local at
`/tmp/cranelisp-s122-triage/qa-brief.md`. No disclosure, package adoption,
implementation, filing mutation, commit or publication occurred.

Subsequent user-authorized allocation override: native Codex `qa`,
`gpt-6-astra`, medium effort, agent identity `/root/qa`; read-only source-backed
classification of all 88 filings, completed and integrated above. Original
report: `/tmp/cranelisp-s122-triage/qa-report.md`. No additional tests were run. Bounded delivery work may use
`gpt-5.6-sol` at high effort under the same user instruction. Shared package
contracts and checked-in adapters were unchanged at scope completion. Phase 2
subsequently adopted the upstream Codex allocation and synchronized consumer
wiring; see [the live plan](SPRINT.md) for the pinned revision and evidence.
