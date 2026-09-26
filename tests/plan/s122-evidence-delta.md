# S122 evidence allocation

Owner: QA. Purpose: give design and test/dev the conditions needed to deliver the approved known-issue closure and REPL-agent eval outcome. Authority: [scope](../../sprints/SPRINT.md), [architecture review](../../sprints/s122-architecture-review.md), existing requirements cited below. Status: **Phase 3 reviewed; Phase 4 authorized on 2026-09-10; Phase 5 authorized on 2026-09-10.** Implementation follows sprint reservations; live-model execution still requires D6.

## Open conditions

| Condition | Required resolution | Owner |
|---|---|---|
| D1 — failed-turn observability | Approved by the user on 2026-09-10: root src unit evidence at the existing prepare→compile→publish seam with an int-private failing compile operation, plus public successful-turn controls. Implementation and executing evidence remain pending. No stable legitimate public trigger is established; this substitution does not prove public codegen-failure reachability. No new public flag, API or faulty language behavior. A type error is not the same lifecycle stage. | dev(src), test and QA under Phase-5 reservations and subsequent closure gates |
| D2 — defect attribution | Separate generic scalar/vector and sequence-IO symptoms using the existing public REDs and controls; establish a discriminating module seam before prescribing fixes. | QA/test, design of attributed context |
| D3 — runtime transfer contract | Consume the reconciled nine-funnel/callback/primitive/host contract and producer→consumer map. Establish how argument/result ownership, aliases, protected JIT traps and code-owner lifetimes satisfy macro-turn discharge. | arch, design(intrinsics/primitives/src) |
| D4 — current language claims | Reproduce omitted derive shapes, supplied-free-variable curry and function-valued def application. Return only genuinely ambiguous semantics; do not assume historical mechanisms remain true. | QA/test; design of attributed context, spec if needed |
| D5 — platform collision reachability | Distinguish a string-mint collision from an accepted two-module loaded/linkable program; establish current accepted names and coexistence before choosing refusal or reminting. | QA/test, arch |
| D6 — live eval execution | Select provider/model/endpoint, allowed fixture disclosure, autonomy/consent, repeat count and request/time/spend budget. This gates live calls, not harness implementation. | user through sprint |
| D8 — primitives construction/traversal/transfer | Approved by the user on 2026-09-10: the exact limited private trusted-base amendment in [the allocation packet](../../sprints/s122-primitives-allocation-proposal.md). Source implementation and executing evidence remain pending. The one bundle covers `adopt_produced_value` including the existing error sentinel, parent-lifetime `borrowed_field`, and exact ADT/Vec storage exits. Final primitives mapping is reviewed: 19 functions/20 adoption sites, six borrow projections, four storage exits. It expands private trusted sites with no new public API. | arch/design propagate the approved contract; dev/test realize under Phase-5 reservations and subsequent closure gates |
| D7 — shared document-checking pilot | Approved on 2026-09-10 under [SPRINT scope](../../sprints/SPRINT.md): replace the narrow four-root proposal with the shared mechanism pilot below. The shared checker is integrated as the project gate ([adequacy](#d7-integrated-project-gate--adequacy-and-remaining-conformance)); project document conformance remains RED pending owner repairs and any specifically approved exceptions. Magic cutover and upstream publication are not approved here. | sprint coordinates shared-tool/project owners under Phase-5 reservations and subsequent closure gates |

The existing `safe-dial` record supplies a task shape, not exact prompts, input data or expected answers. Bounded repository search found no full transcript. It is unavailable for replay and is not a prerequisite: the initial corpus below uses actual compiler-use cases, explicitly adapted into assistance prompts.

## Conditions by source stream

Classes: A acceptance evidence; S safety fence; D diagnostic observer; M maintenance check. Unit evidence is dev-owned; subprocess solution evidence is test-owned. Existing recorded RED→GREEN evidence is sufficient detection evidence for that correction; do not add post-green mutations merely to prove it twice. A new checker self-test protects the checker, not unrelated product behavior.

| ID / class | Required observable and plausible wrong outcome | Lowest discriminating evidence and allocation | Existing evidence / limit |
|---|---|---|---|
| Q1 A — generic replacement | Caller-free generic replacement publishes the new type/body, later calls return 42 and the child completes; stale value or signal termination is wrong. `repl/spec/18-redefinition.md` §18.1. | Test retains the three public scalar/vector witnesses and monomorphic control. Dev adds a failing unit at the attributed publication/realization seam, then fixes it. | `tests/spec_11_stdlib.rs` named generic-redefinition tests; existing stocktake REDs reused. No fourth broad matrix unless attribution exposes an uncovered axis. |
| Q2 A — failed-turn recovery | Intended failure occurs, failed unit publishes no partial state, later literal/definition/call succeeds, and diagnostic names the actual authored unit. | Under the approved D1 substitution, dev must pin actual rollback/publication/next-turn state and batch-identity diagnostics at the root-private compile seam. The injected operation must compile at least one real prepared target using the actual backend, prove its GOT cell changed while its local JIT owner remains live, then return Err before publication. Restoration must precede owner drop; compare live table, cells, retained/compiled owners, publication/introspection and warnings with the pre-turn snapshot, then prove the next turn succeeds. An immediate error with no changed state is insufficient. Test repairs/retires misleading public witnesses while retaining ordinary success controls; it may not label them public codegen-failure coverage. If a legitimate source trigger becomes available, retain independent failure/process/post-error observations there. | ACT-0958 and `tests/spec_11_stdlib.rs`; vec-flatten now succeeds. Two false-green candidates supply no failure evidence. Requirements remain; do not weaken to a convenient failure stage. |
| Q3 A — public IO | Public sequence-IO composition completes with ordered values and correct empty result across REPL/run/link. A stale RC abort or wrong order fails. `spec/10-io.md`, public core.io contract. | Reuse aggregate RED and explicit-bind control; test reduces to the smallest differing composition, retaining the public aggregate as acceptance. Dev owns the reduced internal seam witness. | `tests/stdlib_conformance.rs::stdlib_core_io_public_scalar_driver_across_modes`; scalar result does not imply scalar-only allocation. Do not infer old Pure teardown as cause. |
| Q4 A/S — macro discharge | A successful expansion retains no argument/result tree; aliasing does not double release; after argument transfer a trap causes no host double-cleanup, and executable owners remain live through invocation. The retained [macro-turn contract, Rule 3](../../design/int/macro-turn-ownership.md#rule-3--the-argument-tree-is-discharged-by-crossing-the-abi), reconciled by approved S122 architecture item 4, expressly permits forfeiture of the transferred argument tree on a failed expansion; zero-leak acceptance is not extended to that path. `spec/12-runtime.md` §12.3.1 and macro-turn design. | Test changes existing +1/+2 marginal residual witnesses to balanced expectations, first recording their intended pre-fix failure. Reuse interior-alias run/link/armed cases. Dev pins all-Owned clause production (no inferred mode summary plus the existing D0 CLIF check), argument transfer before protected invocation, successful result copy/consume once, and absence of host argument cleanup after transferred-call failure. Intrinsics handle misuse detection remains at its own unit seam after D3. | `tests/macro_turn_marshal_leak_0889.rs`, `tests/macro_expansion_interior_alias_double_free.rs`, marginal helper. A newtype alone proves neither correct JIT consumption nor trap cleanup. |
| Q5 D — original workload | Reconcile the claimed prelude/session residual on the same library/input/configuration before and after macro repair; distinguish changed fixed overhead from per-expansion slope. | QA allocates one paired original prelude/session measurement using current binary and corrected binary, recording actual residuals. Test retains existing marginal workload guards unchanged where common residue cancels. | S118 1143 is historical, not a current acceptance constant. Existing +1/+2 passing pins establish present marginal leak. No threshold around historical fixed overhead. |
| Q6 A — /mem | Report the expression observation after its returned owner is released, including heap values; no phantom retained result in delta. `repl/spec/03-slash-commands.md` §3.7 and `design/int/result-owner.md`. | Test extends current /mem process witness with a heap-result/control and separately verifies rendered value. Dev pins sampling order around owner lifetime. | `tests/repl_introspection.rs`; `src/repl/commands.rs::handle_mem` samples before formatting/drop. Use warmed/paired setup so macro/bootstrap work is not mislabeled result leakage. |
| Q7 A — reload demand recovery | Capture all required concrete instances, including complete result-context substitutions; settled reload remints them without replaying stale source expressions. Current session-transaction §10 contract. | Reuse typecheck instantiate_demands unit battery; dev(src) tests set capture and correct forwarding at its private consumer. Test extends existing reload e2e with two distinct realizations and an unrelated stale expression, observing correct post-reload calls. | `crates/cranelisp-typecheck/src/form/tests.rs`, `src/redefine.rs`, `tests/repl_persist_redefine.rs`. Do not duplicate every producer unit via subprocess. |
| Q8 A/M — ACT-0954 removal | Unsafe unused public wrapper is unavailable; synchronous watcher/reload followed by evaluation observes current module. | Remove obsolete row-45 source-presence assertion; use existing synchronous reload process evidence. Arch checks exact approved root-library removal and retained scheduler operation. | `tests/facade_pif_rows.rs`; no runtime test through a deleted API and no new publication clock. Seven generated baselines do not cover root library. |
| Q9 S/M — bounded convergence | Quote shields, IO result-root interpretation and Vec tag polarity retain their contract through shared derivation. | Dev retains/extents the existing shared-helper units and changed call-site unit only where a wrong argument/branch survives them. Test reuses quote/shield, result-owner and threshold public guards; no new e2e merely for code deduplication. | 0789,0898,0906; shared APIs already exist. CLIF golden change is a scoped diagnostic/maintenance consequence, not authority for semantics. |
| Q10 A — omitted language shapes | Valid multi-field derive and three-constructor Ord cases, supplied-free-variable curry-then-apply, and function-valued def application behave under their current spec. | Test authors minimal current public repro/control first; dev adds attributed unit before fixing. Keep generic ambiguity question separate from the already-ruled supplied-free-variable case. | 0815/0799/0800 current Q10 cases are now executing and pass; see clause-specific disposition below. `stdlib/derive/test.cl` still needs its owner to repair obsolete failure/omission prose. No direct-callable `def` semantics are inferred. |
| Q11 S — Select ready loser | Dropping a blocking loser after successful channel publication invokes its nonzero disposer exactly once; winner transfer remains caller-owned. `spec/10-io.md` §10.12.9. | Intrinsics dev owns the module seam barrier/channel test after QA allocation; test need not add e2e because public timing cannot reliably select this state. Reconcile ACT-0956's inherited owner with that allocation. | Existing `crates/cranelisp-intrinsics/src/io/tests.rs` winner/disposal helpers. Initially poll/admit the branch to spawn its worker and suspend on rx; after successful send is proven, cancel before polling the ready receiver. Scope the barrier to this test/branch and release/join on failure. One lifecycle case and winner control; no wall-clock-only oracle, no new runtime mechanism. |
| Q12 A/S — platform identity | Distinct accepted source identities cannot access the same wrong GOT slab. | Test establishes minimal valid load/coexist/link fixture and non-collision control; dev pins whichever naming/registration boundary is attributed. | `got_data_symbol_name` documented platform carve-out is only static overlap. D5; broad prefix rejection is unapproved and would overconstrain the language. |
| Q13 M — API baseline format | Omit generated auto-traits while continuing to detect real API additions and retain required concurrency contracts. | Existing `tests/public_api_relocations.rs` guard and its isolated public-addition self-check; arch inventory of required Send/Sync contracts, compile witnesses only where omission removes the sole fence. | ACT-0955 policy already approved. Generated all-seven contraction returns to user; separate mechanical and functional changes. |
| Q14 M/D — instruments and records | Claimed detection/traceability refers to live discriminating evidence; optional observers do not block unrelated acceptance. | QA reconciles exact evidence-owned filings below. Test updates only missing source-side traces/guard evidence; dev owns runtime instrument tests. | No blanket “one mutation per row” rule. Existing real pre-fix failures and recorded plants are reused. |
| E1 M — eval harness | Runner cannot confuse agent prose, wrong result, missing telemetry or terminated process with a verified task outcome. | Test implements subprocess runner and deterministic stub/synthetic artifact self-tests for its parser/classifier. Actual feature-enabled stub smoke uses same executable launch and grading path as live runs. | Existing `tests/agent.rs`, `src/agent/stub.rs`, `tests/scripts/run-agent-lane.sh`; harness confidence is not model competence. |
| E2 D — agent effectiveness | Report independently verified task completion, repairs/tools/steps and unavailable metrics without hiding compiler/provider failures. | Test implements corpus/grading/report below; QA reviews classification and comparisons. | No perfect-score gate, automatic tuning or provider adapter. |

D8 is approved; primitives construction/traversal/transfer implementation and evidence remain pending: adapt existing module observations for String value/one-owner balance, initialized `Some` and typed nullary `None`, empty/nonempty String Vec child transfer with existing unwind cleanup, and constructed macro trees with reused children retaining their distinct obligations. Intrinsics/test guard ownership follows the shared design: prove prohibited mint/out-of-set adoption, borrowed-field caller and raw-storage exit rejection with valid controls. Keep field views tied to the parent lifetime, retain reused children before storage, observe no premature child disposal while the parent lives and one discharge on parent release. Preserve the quote error slot plus its no-reference `0` sentinel; never grade the sentinel as successful Sexp output. `StoredField` separates scalar and owned fields; source review and existing module observations must cover destination readiness and no fallible gap after disarm, including the Vec caller boundary before its existing constructor takes ownership. This is syntactic containment evidence; permitted-site provenance still requires source review and module observations. No deliberate double-adoption UAF, blanket directory exception, or extra e2e layer is allocated.

## Evidence-owned filing disposition allocation

This list supplies closure criteria, not deletion authority. The sprint's source-stream inventory remains the single primary owner map; these are QA's contributing evidence obligations.

| Filings | Evidence disposition in the selected stream |
|---|---|
| ACT-0958 | Q2: replace unarmed witnesses; preserve Q1 separately. Remains open until intended failure and independent recovery/process observations are established. |
| 0694,0818 | Reconcile historical load-dependent/contaminated attribution against current Q1/Q7 publication evidence. One green stocktake does not prove a race impossible; identify a surviving exact condition or seek explicit residual disposition, not another speculative detector. |
| 0761 | Exact generated lane and capability/clean controls already pass; current product is 5 owning types × 12 positions × 2 toggles × 2 counts, run-only, with no balance exclusions. Narrow remaining link observation: reused nested-data capture and closure-capturing-closure cases, both toggles/exact balance, in retained runtime/test visit. Keep filing open for that evidence; no full link Cartesian expansion. |
| 0766,0771 | Closed 2026-09-10: PLAN S122 W3c rows and spec traces now enumerate current exact-balance/local-curry evidence using existing dc78ddbe PASS records; retired M3 remains a tombstone. 0771 cited paths are absent from the current frozen postmortem, so its moved-path claim is superseded. No new behavioral tests. |
| 0779 | Closed 2026-09-10: `program::mono_collect::tests::auto_curry_drain_polarities_handle_unresolved_trait_decl_carrier` directly checks both disciplines over one seeded unresolved carrier. Single polarity plant fails at deferred count0 versus1; restored production passes1/1. Function-level evidence only; settled-seam construction argument retained. Independent typecheck review reports no implementation defect. |
| 0781,0785,0794 | Reuse current green regression/negative guards; close any remaining locus, exact syntax-negative or downstream trace tail. No repeated fixes for stale central claims. |
| 0811 | Q5 and affected exemplar measurements distinguish reduced-repro correction from original aggregate attribution. Shared QA rule already exists; repair historical false conclusion only in its owning record. |
| 0848,0857 | Inspect current intrinsics production detection tests and recorded detection evidence; replace dead ms_p6 line-55 plant citation and grade at proven tier. Clean-run wiring is not a planted-fault witness. |
| 0859 | Consume the already-recorded user disposition and current production ownership witnesses; reconcile typed-funnel consequences with primitives design. Do not re-ask settled instrumentation choices. |
| 0900 | Optional finer locus token has no correctness effect; accept valid crate-grain token or improve it within test-side reconciliation. |
| 0916,0917,0924,0929,0931,0933,0934,0935 | Reconcile current threshold/concreteness/corpus/manifest/disposal witnesses with delivered source and exact design tails. TCO-loss and several template claims are superseded. Only demonstrated remaining conditions allocate new work. |
| 0936 | Replace historical I-ABI roster label/set with current realization contract and its actual witness, coordinated with primitives design. |
| 0944 | Resolved: existing explicit variant tables refute universal absence; PLAN standing-category section now makes the rolling procedure and current family statuses discoverable. No new tests/policy or shared-skill edit. |
| ACT-0950 | Retired 2026-09-21: its request — a ruling on document-to-document citation roots — is discharged by the delivered shared checker, whose `standing-documents.toml` roots include `design`, `spec`, `audits` and `user` and which resolves document targets, anchors and sections. Open conformance debt is carried by [D7](#d7-integrated-project-gate--adequacy-and-remaining-conformance) and the RED project gate, not by the action; no baseline migration or exception is accepted. |
| ACT-0955 | Q13; classify baseline as maintenance evidence and preserve actual required trait contracts. |
| ACT-0956 | Q11; module-level lifecycle observation is sufficient, and owner correction is explicit. |
| ACT-0957 R6 | Current package source/test search found no actual SIGTERM or missing-contract-named detection cases in the role wrapper test files. This is inspection, not executed proof of absence/coverage. Allocate to the package/test owner in Phase 5: remove a required role contract in an isolated fixture and prove refusal before fake-provider launch, paired with the valid-contract launch control; terminate a launched fake-provider subprocess with real SIGTERM and verify the existing wrapper interruption/exit and accounting semantics (no fabricated transcript signal). Extend existing wrapper tests, not a new framework. No package edits are authorized during Phase 3; bounded local evidence repairs remain included in S122, with upstream contribution separately approved at Phase 7. Retain the adopted package pin rather than fetching new contracts mid-increment. |

## Runnable eval corpus and policy

The first runner is a process client of the actual `--features agent` executable. Proposed artifacts: `tests/scripts/run-agent-evals.py`, `tests/fixtures/agent-evals/` task manifests/setup/prompt/probe files, and per-run output under a caller-selected scratch directory. These are test-owned implementation surfaces; this document is QA's policy. No production adapter or session-internal helper is required by default. Live evals intentionally exercise the delivered stdlib as product-client diagnostics; this does not authorize ordinary compiler tests to acquire a stdlib dependency. Reuse the existing explicit stdlib-conformance exception only for the cited public conformance witnesses; harness self-tests can use free-standing stub definitions.

Each manifest contains versioned task id, provenance source, setup/project fixture, exact prompt sequence, post-turn probes with expected typed results, permitted configuration, and timeout/turn limits supplied by the run configuration. Store hashes of each file. Initial prompts are **new fixed adaptations of observed compiler-use cases**, not claimed verbatim historical conversations.

| Task | Starting session and fixed prompt | Independent grader / provenance |
|---|---|---|
| generic-replacement | Workspace-stdlib configuration copied into a fresh project; enter `(defn redefinition-no-import [v] v)` and `(redefinition-no-import 7)` as setup. Prompt: `Replace redefinition-no-import in this session with a generic one-argument function that ignores its argument and always returns 42. Keep that exact name. Apply the definition.` | After the agent turn, call `(redefinition-no-import 0)` and `(redefinition-no-import 9)`; both must yield Int 42. `/info redefinition-no-import` must show the replacement generic Int-returning definition. Setup must have yielded Int 7. Source: existing spec_11 no-import generic replacement RED, `repl/spec/18-redefinition.md` §18.1. |
| ordered-sequence-io | Fresh workspace-stdlib project, same explicit core.io/List/primitives imports as the existing ordered-sequence witness. Prompt: `Define collect-three with no arguments. Use sequence-io to collect (Pure 1), (Pure 2), and (Pure 3) into a List in that order. Apply the definition so I can call it.` | Invoke `(collect-three)` through a harness-owned bind/match probe that verifies exactly three List elements, no surplus tail, and compares each element with its required value (`eq-i64` against 1, 2, 3 in position, as the source witness does); it returns Int 123 only when all three match. A value mismatch and each empty/wrong-shape case return distinct non-123 failure values, which are diagnostic only. A positional `100*a + 10*b + c` encoding must not decide the pass: `[1,1,13]` and `[0,12,3]` also encode 123. Source: `tests/stdlib_conformance.rs` ordered-sequence check. Record requested-API compliance separately from the executable result; a human checks the retained function source for an actual sequence-io call. Mere string occurrence is insufficient. The report may mark executable outcome pass with API compliance unreviewed, but cannot claim complete task success until both pass. |

The test author copies the exact primitive/import syntax from the source witnesses, validates the setup/probe with an independently supplied known-correct program, and records that execution before live runs. The grader observes returned values and exact list shape; matching `123` anywhere in prose is invalid. No extra curriculum scenarios are needed to pad this two-task baseline. A public failed-turn recovery eval task can join only when a legitimate stable public source trigger is established; the approved D1 private-seam witness cannot itself supply that REPL task; safe-dial can join when its exact task contract is recovered or explicitly supplied.

### Launch and observation

- Build/select `target/agent/debug/cranelisp` using the established isolated target convention. Do not overwrite the default-suite executable. Record absolute executable path and hash, repository revision plus dirty diff hash, feature set, platform/build/configuration hashes, copied stdlib/prelude fixture hash and cache policy.
- One fresh project, cache and process per task/repeat; use `--no-cache`, explicit no-color output and declared agent/autonomy flags. Do not copy user project state or provider credentials into task artifacts. Pass secrets only through the existing provider environment and omit their values from reports.
- Send setup forms, explicit `/ask` prompt, post-turn probes and EOF through ordinary REPL stdin. The prompt turn is synchronous. `--yes` may be used only when selected in the live-run consent policy; uncontrolled consent reads must not consume grader input. Otherwise the runner needs an explicitly scripted consent policy, not a guessed number of `y` lines.
- Frame each grader region with harness-issued fresh scalar sentinels and parse only exact ordinary typed result lines in that region, excluding agent-gutter prose. Require the expected number/order of result lines, successful process completion and completed grading region. Duplicate, malformed, absent or ambiguous regions are inconclusive/harness failure, never a pass. A stub that claims success without defining the function must fail grading.
- Record stdout/stderr and agent JSONL/trace at unique per-run paths; verify existence and parsing when those artifacts are used. Production logging can silently fail by design, so missing logs invalidate related metrics, not a separately observed language result. Do not add a production logging guarantee just for evals.
- Kill and reap the whole owned process group on timeout; preserve partial artifacts and mark the result incomplete. No automatic retries overwrite attempts. A provider request timeout is not a precise spending cap; the provider request cap is `AGENT_MAX_TOKENS` in `src/agent/provider.rs` and the approved live budget must account for it.

### Graders, classifications and reports

Use deterministic program-result graders first. No LLM judge or subjective prose-quality score is required. Keep **task result** (`pass`, `wrong_result`, `not_completed`, `ungradable`) separate from **attribution** (`model`, `compiler_confirmed`, `provider_transport`, `harness`, `unknown`). A crash is not automatically a compiler attribution: the compiler-only exact source/control must establish that mechanism. An invalid model-produced program is model failure unless a current requirement says it should be accepted.

The runner assigns only `harness` or `unknown`; a person assigns `model`, `compiler_confirmed` and `provider_transport` from retained evidence. A recorded `give_up` is retained with its cause and error class as evidence for a refusal reading, but does not establish `model`: both causes (`model_declined`, `step_budget`) arise only after a compiler rejection in `src/agent/pull.rs::validate_and_repair`, and `agent_complete_for_repair` also reports a failed provider call as `model_declined`. Lack of a definition alone only proves non-completion. A log with no `exchange` event is unavailable telemetry, not zero counts. Missing telemetry never becomes zero repairs/tokens. A known compiler failure remains visible in all-attempt results and can be separated into a compiler-blocked stratum only with linked current reproduction evidence. Report denominators explicitly; do not silently exclude inconvenient runs.

Each run report includes task/run/repeat ids, timestamp/duration/process status, fixture/prompt/probe/grader hashes, compiler/build/configuration provenance, provider/model/endpoint (credentials removed), autonomy and all limits, task result and attribution/evidence, grader observations, artifact paths/hashes, and available log metrics. Extract submits, repairs, pulls by tool, give-up cause, steps_at_submit/steps_at_give_up, primer_hash and harvest_len from existing fields. Tokens/cost stay `unknown` unless supplied by actual telemetry; do not estimate them from transcript length. First-submit metrics require identifiable symbol/turn association, otherwise report unavailable.

Runner accepts an explicit repeat count. One run/task is a smoke observation; the initial descriptive live comparison recommends three independent fresh repeats per task **only within the separately approved budget**. Report individual outcomes and counts/fractions, median elapsed time and spread, with no statistical significance claim from this tiny sample. Compare runs only within matching task/probe/grader/fixture/compiler/provider/configuration strata; when testing a compiler or primer change, name the changed dimension. Nondeterminism remains even with identical hashes. Never silently replay failed attempts until green.

### Harness evidence before live calls

Reuse the existing stub DSL/provider. Test the runner's shared launch/grader path with: a real applied correct definition, a wrong value, a success claim with absent definition, an explicit give-up, and a terminated/nonzero child. Parser-level fixtures cover malformed/missing log and ambiguous/missing grader framing. These cases target false-positive completion and misclassification, not another exhaustive agent-conformance suite. Require process exit, source/probe truth and report class to agree. The stub run is a deliverable harness check; it cannot satisfy the live-model baseline.

## Approved shared document-checking pilot — ACT-0950

The user approved the replacement D7 scope on 2026-09-10; [SPRINT.md](../../sprints/SPRINT.md) is the scope authority. One offline shared `.agents` tool consumes project declarations, independently discovers all project-owned nonignored Markdown, checks establishment to root `CLAUDE.md` or justified exemptions, and checks document references, anchors and sections while preserving Cranelisp source-citation checks. Validate the candidate against both repositories read-only, then adopt it in Cranelisp and repair findings. Magic edits and upstream publication need subsequent approval. There is no blanket residual baseline migration.

This supersedes the narrow four-target-root proposal; measurements taken with the retired citation script do not describe the delivered checker's corpus or findings. Delivery state is recorded under [D7 integrated project gate](#d7-integrated-project-gate--adequacy-and-remaining-conformance).

### D7 evidence allocation

The [shared checker design](../../design/arch/s122-shared-document-checker.md) is reviewed and adequate for Phase 4 organization. This is M-class evidence for the shared checker and document claims, not a new compiler acceptance layer. Shared-tool dev owns parser/discovery/graph/ratchet units; test owns the candidate CLI and project-adoption observations. Reuse existing source-checker fixtures where they already distinguish the required rule. One small temporary project fixture can carry the following independent wrong outcomes; do not build a language-by-project Cartesian matrix.

| Condition | Minimal discriminating evidence |
|---|---|
| Discovery is independent of declarations | Add one nonignored Markdown file outside all declared paths and observe it in discovery plus an unestablished finding; include a new untracked file. An ignored file and a recorded foreign gitlink/package boundary are excluded; discovery does not descend into gitlinks. A declaration omitting a project document must not hide it. |
| Establishment reaches the governing root | A valid governing-memory chain reaches root `CLAUDE.md`. An orphan and a disconnected cycle do not. An explicit justified establishment exemption retains its root-reaching governing memory and remains visible in the report; an absent or invalid justification cannot silently establish the file. A broken outgoing reference in a live establishment-exempt document must still fail unless it has its own justified rule-specific waiver. A bounded reasoned `historical-record` class remains discovered, owned and root-established; its outgoing references are excluded and counted. A live link into that archive still requires target resolution; use these paired observations to preserve dated records without hiding broken live navigation. Mere incidental prose linkage cannot replace the design's governing relation. |
| References resolve under the documented grammar | One valid target, heading anchor and section citation serve as controls; break each target independently and require the corresponding located diagnostic. Include one ambiguous shorthand/section target that must report ambiguity instead of choosing a convenient match. Reuse extracted Magic fixtures for supported bold/table section labels and comment/docstring citations. A code file selected through `references.comment_input_patterns` supplies reference inputs without acquiring standing-document establishment obligations; keep that control distinct from document `extra_suffixes`. Unsupported or ambiguous forms cannot be counted as verified resolution; proposed targets and absent optional-package targets remain separately classified, not verified. An established optional absent Gitlink control must not mask a missing file inside an initialized package. |
| Cranelisp source guards survive | Reuse the existing valid source citation plus missing path, out-of-bounds line and absent symbol witnesses. Verify the actual project entry point still executes all three guards; successful document-link checks cannot substitute for them. |
| Reporting and ratchet reject new debt | Repeat an unchanged fixture and compare stable finding identity. A new finding must fail the project gate; resolving it must clear that failure. An old baseline entry must not automatically enroll a different checker rule or newly discovered document. Invalid declarations or incomplete checks must be distinguishable from a clean corpus. Exercise the declared CLI statuses: 0 for no unsuppressed findings, 1 for findings, 2 for invalid configuration/invocation or inability to inspect. Use one overlapping-class or escaping-path declaration to discriminate invalid configuration; no broad schema permutation matrix. Any retained legacy baseline identity requires an explicit reviewed mapping. |

For Cranelisp adoption, record the candidate/tool and declaration revisions, repository checkpoint plus working-tree state, full discovery manifest, rule set, findings and exit result before repairs. `--list-docs` alone or any partial-corpus run cannot satisfy adoption. Compare retained source checks over the same source-citation input with the existing checker; explain differences by precise rule/corpus changes. Verify a representative newly discovered document reaches the real project gate, and use its resolved counterpart as the control. Repair findings through their owners, rerun the same declared candidate, and record remaining findings individually. Any specific residual exemption or baseline proposal returns for its required approval; no blanket migration. Retire duplicate local implementations only after the real entry point demonstrates shared invocation and retained source guards. Existing maintenance-gate tests receive the minimal migration updates rather than a second checker implementation.

For Magic, run the same candidate tool read-only with its proposed project declaration kept outside the repository. Record the tool identity, declaration, discovery manifest, rule enablement and findings; verify the repository state is unchanged by validation. No Magic repair, checked-in declaration, hook cutover or upstream publication is implied. Results validate candidate applicability only: differences in ignore rules, ownership boundaries, establishment declarations, source-language guards and reference grammar must be reported. Neither equal finding counts nor a clean Cranelisp run proves Magic coverage. The historical four-root measurement cannot serve as this new corpus baseline. No live measurement or implementation is performed in Phase 3.

## Phase-5 attribution observations

Q1 first focused run at unchanged compiler checkpoint `dc78ddbee3107043925505531798667dc61f7a03`: test reports one monomorphic GREEN and three generic REDs from the four existing redefinition cases in `tests/spec_11_stdlib.rs`. The no-import identity case realizes 7, publishes/introspects replacement `(Fn [a] Int)`, then returns stale 0 instead of 42; adding the Vec import does not change that result. The Vec-realized sibling produces its initial list then terminates with status 11 after replacement confirmation. Invocation: `CARGO_TERM_COLOR=never cargo nextest run --no-fail-fast --test spec_11_stdlib -E 'test(/redefinition/)'`; raw evidence `/tmp/s122-q1-focused-dc78ddbe.log`. These are test-owned executing observations, not a QA rerun.

Bounded corrective-owner lead: Binary/int replacement/instance lifecycle. `src/redefine.rs` excludes `__expr` from reverse caller indexing and `drive_t1_full_cure` returns when `stale_callers` is empty. `crates/cranelisp-typecheck/src/program/mono_collect.rs` dispatches directly to an existing concrete `demand.instance_key()` without reminting. Together these source facts explain a stale-instance route after caller-free template replacement; the consumer assumes its existing instance is current. The executing prior-realization discriminator now confirms the bounded attribution: `generic_redefinition_without_prior_realization_uses_replacement_control` omits the initial concrete call and returns 42 after replacement, while the paired existing no-import case retains the initial `(f 7)` and returns stale 0. Test ran the filter `test(/generic_redefinition_(without_vec_import|without_prior_realization)/)` at the same checkpoint: one pass/one fail, `/tmp/s122-q1-prior-realization-control-dc78ddbe.log`. Prior concrete realization distinguishes this stale-call face. Assign corrective design to Binary/int for replacement/instance lifecycle; the internal empty-caller path remains a source-backed inference rather than an instrumented branch observation. No additional public control is required before that design handoff. Do not infer a separate Vec RC/backend correction from status 11. Corrective design must preserve typed identity and existing caller-report exclusions; no fix mechanism is prescribed here.

Q1 ownership-ABI admission clarification: the exact authored base changes from `(Fn [a] a)` to `(Fn [a] Int)` with no blocking dependent. `repl/spec/18-redefinition.md` §18.1.2 already permits caller-free language-type changes through a fresh slot and coherent persisted-source reconstruction to change ownership mode. This does not authorize ACT-0953's stronger same-language-type replacement or a generated-instance blanket exemption. Validate authored admission first; module evidence must distinguish fresh-slot replacement/old-key retirement from patching an ABI-incompatible old slot, and prove failed reconstruction leaves the prior unit intact. Reuse same-language-type ABI-rejection and named-blocking-dependent type-change rejection controls. Current §18 forbids ordinary callable dependent recompilation; historical T1 cascade prose is not authority to waive that constraint. Designer owns the exact bounded reconstruction path before source continuation.

Q1 placement correction: `apply_redefinition_outcomes` runs after ordinary publication, so a post-publication T1 reload cannot establish §18's prior-base preservation on failure. Allocate the correction to the original ordinary prepared candidate; Q7 persisted-source reconstruction remains separate. The minimum dev evidence exercises that actual original-candidate entry path with a prior generic realization and observes the authored replacement plus all affected remints in one unpublished candidate before its first publication. An isolated remint helper unit alone does not prove turn atomicity. Reuse the approved D1 private failure operation where it traverses this path: perform real candidate compile work, fail before publication, and observe the old authored scheme/body, instance slot/code/GOT, introspection and backing source unchanged; the next ordinary call still uses the prior definition. Preserve the public prior-realization RED/control as acceptance of successful replacement. One same-module control has the replacement generic call an unrelated existing local helper: that helper must remain visible while affected old instance keys cannot satisfy dedup. Full-reload's empty current-module fallback is not evidence for this selectively masked ordinary candidate. No ordinary dependent cascade is allocated.

Q1 current failure-evidence assessment (2026-09-10, source inspection; dev executing results attributed): reported public 3/3 GREEN and the preparation unit establish rematerialization, preserved same-module helper lookup, a fresh realization slot and prior-slot retirement in the candidate. `src/worker/tests.rs::declined_prior_demand_retirement_is_unpublished_until_commit` drops an uncompiled `PreparedCommit` and compares the surviving instance binding/slot/GOT pointer and compiled-owner presence. Credit it only as preparation-discard isolation. It does not exercise a compile/publish failure or establish original-turn rollback, old authored base/introspection/backing preservation, or subsequent prior-definition usability. Q1 therefore remains incomplete on that failure obligation. Complete the approved D1 private compile-operation seam within the retained Binary/int visit, using one shared Q1/D1 original-candidate failure case with real backend mutation, live owner during mutation, restoration before owner drop, unchanged prior complete unit and next ordinary old-result call. Do not add a second failure framework or repeat successful public coverage solely for this assessment; rerun affected evidence after the new seam lands.

Q1/D1 follow-up source assessment (2026-09-10): the new `ordinary_replacement_compile_failure_restores_prior_instance_and_session_state` now traverses original preparation, real backend compilation and prepublication error; it observes changed prepared GOT state and compares prior base/instance/GOT, retained owners, introspection, backing source, publication outputs and the next old-definition call. The production error arm restores the slab before the local JIT owner leaves scope. This supersedes the earlier preparation-drop-only gap; final executing detection results remain dev-owned. Its injected message is built by the test from `prepared.targets` and returned unchanged, so matching it proves error pass-through and batch delivery, not production diagnostic attribution. Credit actual-target diagnostics only after a production attribution/formatting seam is observed; otherwise retain that narrow evidence limit.

Approved test delta under the existing allocation: keep the first two obsolete failed-codegen-labelled `spec_11_stdlib` cases as explicitly named successful Vec-flatten followed by literal / definition-call controls, asserting first result and process success. Delete the duplicate successful-replacement/partial-publication case and the unarmed diagnostic-name case; the Q1 siblings and approved private D1 failure cover their applicable claims. No public codegen-failure reachability is established. Remove the entire ACT-0954 row-45 wrapper-presence test. Strengthen the existing `repl_watch::watch_notification_appears_at_prompt_boundary_not_mid_result` with successful status and ordered initial42/postreload99 result observations while retaining notification placement. No new watcher harness or deleted-API test is allocated.

Q1 review blocker (2026-09-10): current `src/worker.rs::capture_affected_mono_demands` filters solely through `is_caller_free_language_type_change`. An admitted same-language-type generic edit consequently captures no prior realizations, contrary to `repl/spec/18-redefinition.md` §18.1. Assign the correction to retained Binary/int; this is an Important current correctness/contract-completion issue, not ACT-0953 expansion. Minimal public discriminator: define generic `f [_] 7`, realize `(f 0)` as 7, replace with same-type `f [_] 42`, and require `(f 0)` to return 42. An otherwise identical no-prior-realization session is the control. The existing original-candidate unit should also observe the same typed instance key included and its ABI-compatible slot preserved; retain complete-candidate rejection for incompatible same-type ownership ABI and no dependent recompilation. Extend §2's lower design carrier to distinguish same-type rematerialization from caller-free changed-type fresh-slot replacement. No broad new matrix is allocated.

D1 diagnostic follow-up: current private fixture now obtains a production typed `CompilationError::CodegenFailed` from an invalid `missing-local` body under the prepared batch's exact target after the real Q1 compilation/mutation. It checks target module/symbol separately from that incidental cause and the converted outer diagnostic. This closes the prior test-authored-message gap at the private attribution seam; it still supplies no public source-trigger reachability. Dev reports focused three-unit PASS evidence in `/tmp/s122-q1-d1-focused-dc78ddbe.log`. The compensation-removal detection observation remains pending and must join the same-type correction before release. Public success controls report 5/5 PASS, synchronous watcher initial42→updated→99 reports 1/1 PASS, and facade checks report 20/20 PASS; these do not discharge the new same-type blocker.

Q3 public reduction at the same checkpoint: `sequence-io` over two nested Bind actions aborts with a stale RC decrement in REPL/run/link. The same actions explicitly bound into the same exact ordered List, a one-nested-action sequence, and an empty sequence pass; the earlier two-Pure sequence control also passes. Test evidence: `/tmp/s122-q3-reduction-dc78ddbe.log`, focused `stdlib_conformance` filter `test(/stdlib_core_io_(ordered_two_action|one_nested_action|empty_sequence)/)`, three pass/one fail. This isolates nested-action aggregation, not an internal RC cause.

Q3 next attribution belongs to an intrinsics dev-owned module witness when its source reservation opens. Current `io.rs` transfers the fields of a fresh Bind and `drop.rs::dec_shallow_io` leaves a non-last-reference parent allocated; this creates a specific shared-parent ownership hypothesis. Reuse `io/tests.rs` Pure/Bind/identity-continuation fixtures and `alloc::is_live`: a continuation returns a counted reference to a Bind retained by another owner (RC2), paired with the unique-parent RC1 control. Observe value and child/continuation liveness while the retained parent lives, then balanced final teardown. A RED uses the allocation ledger rather than dereferencing or deliberately consuming known-dead children. Existing public observers may further localize the original trace; until that/module observation settles, no production correction is assigned from the abort label. Preserve the original public RED/control and all modes as eventual acceptance.

Q3 module attribution settled (2026-09-10): `crates/cranelisp-intrinsics/src/io/tests.rs::continuation_returned_shared_bind_preserves_retained_parent_fields` is intended RED and `continuation_returned_unique_bind_transfers_and_balances` PASS in run `34c74925-ba8e-4e74-bdab-f9d63b7c2d60`, `/tmp/s122-q3-intrinsics-attribution-red-control-dc78ddbe.log`. HEAD is `dc78ddbe` plus S122 working-tree changes; this attribution increment changed only the intrinsics test file, not production. QA inspected the helper, assertions and recorded result without building or executing. `make_return_node_closure` explicitly increments the returned parent in the counted branch, retaining the original reference; the unique branch transfers the sole reference. The shared case completes with73, then observes `parent_live=true, inner_live=false, cont_live=false`; the RC1 control frees the parent/children and balances. The failed liveness assertion precedes final parent consumption, so it detects the ownership violation without dereferencing or deliberately disposing already-dead children. The shared case's final-balance assertion remains an unexecuted obligation until correction makes those liveness assertions pass.

This is sufficient to attribute a current intrinsics defect: `crates/cranelisp-intrinsics/src/io.rs::run_io_trampoline_inner_async` marks a continuation result fresh, then treats a fresh Bind's child and continuation as consuming transfers. `crates/cranelisp-intrinsics/src/drop.rs::dec_shallow_io` leaves a non-last-reference parent allocated; its still-owned fields therefore cannot be consumed solely because the trampoline owns another reference to that parent. The module pair discriminates shared-parent ownership from unique-parent transfer. It does not directly correlate the public sequence reduction's exact parent identity with this fixture, so do not claim complete public-root-cause proof or assign a backend/stdlib correction from the abort label.

Next allocation is bounded intrinsics corrective design for preserving the live shared Bind's field ownership while retaining correct unique transfer and normal teardown. Design determines the mechanism under the existing runtime ownership contract; QA prescribes no new API or algorithm. Reuse this module RED/control and final exact-balance assertions, then rerun the existing public two-nested-Bind sequence reduction, aggregate and existing explicit-bind/one-action/empty controls across their already-allocated REPL/run/link modes. Public acceptance must complete with the exact ordered values and no stale-RC abort; if it remains RED, retain that public gap and reattribute rather than declaring Q3 fixed or expanding correction by guesswork. Scoped review covers the shared/unique ownership distinction and affected normal/cleanup paths; no extra matrix or independent failure framework is allocated. In the retained source visit, repair the module pair's trace to `spec/12-runtime.md` §12.3.1 normal lifetime requirements: its current `spec/10-io.md` §10.12.9 cancellation citation does not mean this fixture exercises cancellation.

Q12 next test handoff: the static collision `platform.hx` / ordinary `platform-x` at `__cranelisp_got_platform_hx` needs a loaded executable witness. Allocate one minimal proposed test-platform fixture named `hx` under `platforms/` (not yet created) to a separately reserved platform-fixture dev invocation, following existing platform fixture conventions; sprint coordinates necessary workspace registration/build wiring. Test owns temporary `platform-x.cl` via the existing harness and cases in `tests/spec_platforms_adt.rs` / `tests/link.rs`. The fixture and ordinary module return distinct values (for example 7 and 3); invoke both and encode their ordered results as 73, so mere load success or wrong dispatch cannot pass. Run the same pair through REPL, `--run`, and `--link` with actual execution of the linked binary. Record acceptance/load/link/execution separately, retaining the first failure diagnostic. One otherwise identical noncolliding ordinary-module rename is the initial control. If the collision pair refuses before coexistence, test the original ordinary name alone to distinguish name admissibility from collision. Reuse the existing dual-platform and run/link harness patterns; add no stdlib dependency or broad platform matrix. This allocation authorizes the already-scoped fixture under Phase-5 reservations, not a naming correction or a static-only defect attribution. No source/build activity occurred during this allocation.

0931 QA evidence disposition (2026-09-10, bounded read-only): the existing dc78ddbe stocktake passes `adt::tests::polymorphic_constructors_are_slotless_templates` (Some/None), `traits::monomorphise::tests::rechecked_bare_constructor_value_mints_and_carries_its_concrete_instance`, its imported-caller-module twin, and `module::tests::concrete_to_template_conserves_and_never_reissues_prior_slot`. Current source gives Template no callable slot; these are existing behavioral companions to that construction boundary. They are not a freshly executed universal bootstrap sweep or numeric R17 ctor-partition measurement. No such current full-bootstrap/partition observation was located in this scoped review. Hand the retained NC-1 ctor-population / R17 evidence tail to the typecheck/backend owners for reconciliation using existing bootstrap-table and corpus/CLIF facilities; identify a current witness or source-backed supersession before claiming closure. Do not recreate old kind-specific machinery simply to preserve an obsolete test label.

MEASURE-C1/C2's historical before/after commission applies to the superseded separate-constructor-state/wrapper migration. That comparison is not current executing evidence. In particular, the passing imported-constructor unit locates the instance in the caller module, so the old premise that all such instances accumulate in `primitives` is not the current placement contract. Retire the old measurement design as superseded; make no unmeasured claim of net-zero code size or negative slot pressure. Any present cost/capacity claim needs its own comparable current corpus observation within the existing owning visit. 0931 stays open for the narrow ctor-population/partition evidence disposition, with no new source defect attributed and no new framework allocated.

0761 current disposition (2026-09-10): `tests/gen_ownership_flows.rs` already implements absolute balance on every measurement, in addition to value, differential, scaling and missing-measurement checks. Its five owning types and twelve positions cover let/borrowed temporary/return through 0–2 lets/curried capture/TCO/match contexts; there is no balance-exclusion switch. Existing dc78ddbe stocktake reports all five generated lanes and five capability/clean tests PASS. The clean measured case supplies the executing zero-residue control for these macro-free children; arithmetic plants check verdict/measurement plumbing, not a newly planted production defect. `SafetyMatrix` remains intentionally differential and is not credited as the exact lane. The focused 0763/0760 corpus supplies closure-owning shapes not enumerated as generator types, as reconciled by the 0766 rows.

The outstanding 0761 observation is the limited linked-runtime boundary: generated cases are `--run` only; 0763 A/B/C/C2 already execute run/link, while nested-data capture and closure-capturing-closure remain run-only in the inspected dedicated files. In the retained runtime/test visit, reuse one existing nested-data captured-closure program and the existing F closure-capturing-closure program under `link_then_run`, both ownership toggles with exact balance/value assertions; retain the already executing linked clean control. This samples the distinct nested-data and closure destructor paths without multiplying the full generated product across modes. Report combined generated+focused coverage honestly, not full linked Cartesian coverage. Filing remains open for that bounded evidence; no source/test change or new execution was performed for this disposition.

Q10 clause-specific disposition (2026-09-10): evidence is `/tmp/s122-q10-current-shapes-dc78ddbe.log`, HEAD `dc78ddbe` with the logged partial Q1 working-tree changes; there were no Q10 production changes. Do not label it a pristine unchanged-compiler rerun. Supplied-free curry pair passes 2/2, derive cases 5/5, function-valued `def` contract case 1/1. The first Display failure was an incorrect comma expectation; actual `Point(1 2)` matches the current builder, and the corrected oracle passes. It is not a compiler fix.

| Filing / face | QA classification and exact remaining owner work |
|---|---|
| 0815 derive panic/hang | Historical failure not reproduced by current three-constructor Ord and adjacent/field controls. Current public regression coverage is present. QA record may retire this failure claim; stdlib owner repairs `stdlib/derive/test.cl`'s obsolete blocked-shape ceiling/omission commentary in its retained visit. No helper/runtime correction is attributed. |
| 0815 macro-body location request | Current `spec/09-macros.md` §9.3 call-site convention and §9.14 item5 explicitly limit error spans; `src/expander.rs` uses the invocation span for runtime error wrapping. A richer body-location diagnostic would be an enhancement to that contract, not a reproduced defect. Do not add a guessed new requirement or failure test to close the old symptom. |
| 0835 structural embedding | No blanket closure from derive GREEN. Its own residual B3+2 and JIT-inline abort claims are separately resolved by current `tests/slist_sconcat_ownership_0835.rs` exact B3 and both teardown cases; all seven direct tests PASS in the existing stocktake. Source records attribute B3 to the removed glue cutoff and abort to the corrected match-release seam. Branch F already moved to 0888 and remains Q4/Q5. Runtime dev/design owners reconcile those exact clauses and the structural-embedding record; the typed-consume migration preserves this evidence and does not reimplement the old fix. |
| 0799 supplied-free curry | Historical sharp wrong-reject no longer reproduces: then-apply returns3; incompatible scalar-use control exposes the residual Fn. Current §4.6.3 already settles residual-free inference/ambiguity, so its historical semantic-fork paragraph is stale. Test/design(typecheck) owners reconcile the filing and `design/typecheck/auto-curry.md`'s observation-first stale-defect wording against this pair and existing guards; 0779's separately allocated drain unit is now closed by its recorded polarity evidence. Do not infer all historical matrix cells ran from these two observations or add a new matrix solely for old labels. |
| 0800 faces1/2 | Ordered definition-result behavior already has stocktake PASS in `def_definition_echo_lists_every_emitted_definition_in_order`; introspection describes the actual macro binding as specified. Int/stdlib record owners replace stale singular-result defect wording, preserving the existing observer. |
| 0800 face3 | Bare k evaluates to a closure; `(k 1 2)` invokes its specified zero-argument macro and rejects arity; equivalent local closure yields13. Nondefect under `spec/05-definitions.md` §5.7 and `spec/09-macros.md` §§9.5/9.10.2 plus current `stdlib/defs.cl`. Direct callable-def behavior remains a stdlib API/user choice, not an inferred compiler requirement or automatically closed enhancement request. |

Q1 overload-family reorder review condition (2026-09-10): `CallableArmId::from_ordinal` is generation-local, while `capture_affected_mono_demands` carries the old `InstanceLink.template` into a replacement. A preserved signature set may reorder clauses under §18.3, so old ordinal identity is not established correspondence to the new arm. This is a new Important correctness/dispatch condition, not a repeat of the plain same-type test and not authority for a particular API change. Binary/int owns the generation-transition correction design, with typecheck/types consultation only if the actual seam requires it.

The first proposed partially typed same-arity shape was invalid: its signatures overlap at Int/Int and registration correctly rejects it before redefinition. Test substituted fully concrete String/Int and Int/String clauses; that permanent pair passes 2/2 in `/tmp/s122-q1-overload-family-reorder-dc78ddbe.log` (run `766b0652-ac71-4876-9a8c-c28ba3903b1f`). It establishes concrete-family reorder coverage only: it does not create the generic captured-demand property and cannot classify the original finding as a nondefect.

QA's revised legal generic witness was executed using the already-built CLI in isolated temporary sessions, without builds or source/test edits. Initial `(defn f ([:a x] 7) ([:a x :b y] 42))`; define `(defn call-one [] (f 0))` and `(defn call-two [] (f 0 0))`; call both; replace with `(defn f ([:a x :b y] 42) ([:a x] 7))`; call both existing callers again. `/tmp/s122-q1-generic-arity-reorder-probe.log` preserves exact input/output: initial confirmations are genuinely generic `(Fn [a] primitives/Int)` and `(Fn [a b] primitives/Int)`, and initial callers return7/42. The first failure is replacement rejection: `cannot rematerialize prior instance 'user/f__arm1$Int+Int' ... same-language-type replacement declined the prior realization`. The process exits0 and old callers still return7/42, so exit/value assertions alone would miss the defect. A fresh session defining the already-reordered generic family accepts and returns7/42. Provenance is the existing working-tree binary at HEAD `dc78ddbe`, with current Q1/typecheck changes, not a pristine historical binary.

Source attribution is bounded to Binary/int's cross-generation demand replay. `crates/cranelisp-typecheck/src/program/register/multi_sig.rs::resolve_variant_types` preserves authored enumeration and rejects overlap only between equal arities; `register_mangled_variants` preserves that order. `resolve_one_overload_call` selects an `OverloadArm` by variant ordinal and derives a typed demand for the generic clause. `owned_overload_template` and `crates/cranelisp-typecheck/src/program/mono_collect.rs::instantiate_demand_roots` resolve that ordinal against the current declaration. `src/worker.rs::capture_affected_mono_demands` retains the prior demand unchanged, and `instantiate_captured_demands` replays it in the replacement world. The emitted prior-instance name corroborates that this subject reaches the captured generic-realization path. This demonstrates a wrong rejection under §18.3, not an observed wrong-body call or memory fault; no specific mapping API or repair is prescribed.

Test's single revised delta is a distinct permanent generic subject/control using that executed shape. The subject must require two complete f confirmations, both generic signatures in each family confirmation, no error/stale/dependent-recompilation report, and original named-caller results7/42 before and after reorder. The fresh reordered control requires one complete generic-family confirmation and7/42. Keep the passing concrete pair as its separate control surface. The permanent subject now supplies the intended RED before correction (record below). Binary/int design/dev owns the admitted family's cross-generation instance correspondence; scoped next review checks that condition, same-slot/ownership-ABI compatibility, no subset publication and existing-caller preservation. It does not repeat unrelated Q1/D1 gates or introduce a new language/API decision.

Permanent generic-family evidence (2026-09-10): `tests/repl_redefinition.rs::generic_overload_family_reorder_preserves_realized_named_callers` is intended RED and `generic_overload_family_already_reordered_fresh_session_control` PASS in run `61a51698-402e-453e-ab3b-fb8fa8f32aa4`, recorded in `/tmp/s122-q1-generic-overload-reorder-red-control-dc78ddbe.log` (1 failed, 1 passed, 28 skipped). QA inspected the permanent assertions and recorded output. Both generic signatures and prior realizations are established before rejection; the no-Error and second-complete-family requirements detect the otherwise false success of exit0 and surviving old7/42. This run reports `f__arm0$Int` as the first declined realization; the earlier probe reported `f__arm1$Int+Int`. Neither ordinal is an oracle or a distinct defect: both expose the same replacement-preparation rejection. The permanent RED/control is adequate for the assigned public condition. Correction and finding-scoped review remain pending with Binary/int; passing prior Q1/D1 evidence does not discharge this independent family correspondence condition. No broader allocation or additional execution was performed in this record update.

0779 completion evidence: source checks both `Deferrable` and `Final` over the same unresolved trait-declaration item, forbids publication of that unslotted declaration carrier, and distinguishes deferred retention from final AutoCurry resolution. `/tmp/s122-0779-polarity-plant-red-dc78ddbe.log` records intended deferred-count failure (0 versus1); `/tmp/s122-0779-polarity-restored-green-dc78ddbe.log` records restored1/1 PASS. Independent typecheck review reports no implementation defect. This satisfies the adopted candidate-(1) closure; it is not per-caller-seam behavioral proof, and the construction rationale for settled Final seams remains unchanged. The QA filing is deleted; evidence lives here and in PLAN.


## Approved uniform executable identity — coordinated evidence delta

The user approved the uniform identity and exact public API packet on 2026-09-10;
[canonical packet](../../design/arch/s122-overload-reorder-publication.md) owns
scope. Any remaining awaiting-approval prose in that carrier is a propagation
repair, not another user gate. QA read current types, typecheck, integration and
cache evidence homes at `dc78ddbe` plus S122 working-tree changes. This is GO for
the bounded coordinated types → typecheck → Binary/int migration, with backend
label/cache consumers visited only for actual dependencies. It is not completed
implementation or release evidence. Q3 remains a separate runtime condition.

| Owner / risk | Economical required observation and reuse |
|---|---|
| Types — full signature identity and collision resistance | Extend existing key tests in `crates/cranelisp-types/src/module/tests.rs`. One compact set compares direct `concrete_callable_key`, Binding-link, OverloadArm-link and MonoDemand projections for the same owner/full signature; selector ordinal and diagnostic site do not change executable identity. Require literal approved rendering, including nullary/nested Fn syntax. Distinguish legal `a → Int` versus `(a,a) → Int` at the same `[Int]` substitutions; ordered argument reversal; result-only Int/String nested Fn choices; same short nominal name in different modules and differing nested nominal arguments; different authored owners. Reuse current nominal/home tests rather than adding a product matrix. Alpha-renamed scheme variables, repeated occurrences and unused quantified variables must project identically using the approved first-occurrence ordering. One higher-kinded-head substitution observation covers the explicitly reused `apply` behavior. |
| Types — error and installed-state authority | Focused cases for argument-count mismatch, residual nonconcrete signature, non-function signature and unsupported template must return the specified error variant, never an old-key fallback. Adapt `install_instance_derives_key_preserves_backlink_and_mints_slot` and `mismatched_instance_candidate_is_rejected_before_mutation`; require helper/install agreement from actual settled signature, preserved backlink/slot, and refusal of mismatched stored key/payload without table mutation. Reuse restored-state validation coverage with one mismatched persisted instance key; helper success alone is not installed/restored-state proof. |
| Typecheck — authoritative generation/schema and complete demand | Adapt `program/mono_collect/tests/result_context.rs` existing result-only closure, nested/container, selected-overload and imported-hop observers to the new context API. Assert actual installed signatures, distinct keys and caller references; expected identity must include an independently written full-signature/rendering expectation, not just call the helper twice. Add or extend one existing multi-sig unit with legal repeated-variable different-arity arms to prove two installed instances cannot collide despite equal substitution vectors. Preserve existing overlapping-signature rejection; do not turn invalid same-arity generic fixtures into acceptance tasks. |
| Binary/int — selector remap and atomic same-key replacement | Keep the permanent generic reorder intended RED/control unchanged as the public acceptance anchor. A focused original-preparation unit observes old arm → uniquely matched staged scheme before replay, unchanged concrete keys/slots for both realized signatures, updated backlinks to the staged selectors, and unchanged named caller references. Use alpha-renamed/reordered template schemes in this module observation to cover the packet's existing signature comparand; keep a constrained-scheme identity/rejection control at that same comparand if not already covered. Compile/publish through the ordinary path and observe current callable targets plus required prior-owner retention, not only successful key construction. Reuse complete-family rejection, same-type ownership-ABI refusal, changed-language-type fresh-slot/old retirement, unrelated local helper and original Q1/D1 rollback cases. Failed correspondence/derivation must leave the whole prior family, instances, slots/GOT and owners intact; never publish only a matched subset or recompile ordinary callers. |
| Backend + test — table/native/cache agreement | Reuse `tests/cache.rs::cache_result_only_returned_closure_specializations_agree_uncached_cold_and_warm` with its actual warm cache-hit assertion. Select existing ordinary, concrete overload and generic/self-call acceptance fixtures for JIT and object/link execution; record the named subset at handoff, adapting a fixture only if an actual label-consumer path is otherwise unobserved. Include one recursion/self-call subject that uses a generic instance key and an existing concrete-overload control; value/termination plus real object/cache load must agree. No wholesale native-label rename or three-class × mode matrix is allocated. |
| Backend + test — semantic cache retirement | Bump the approved coherent semantic cache version and its frozen assertion. Reuse the cache-version rejection harness: a prior-version sidecar/object pair with otherwise current compiler fingerprint must be refused for version mismatch, then rebuild/current warm reuse must work. Observe refusal before stale object/key installation; changing only the build fingerprint cannot satisfy this condition. One stale/current control pair suffices; no old binary farm or serialization-shape expansion. |

Deliberate arming stays proportional. The existing permanent generic reorder
RED already detects the ordinal-replay defect and must turn GREEN after the
migration. Types dev performs one temporary result-omission key mutation against
the result-only distinction observer, records its intended collision failure,
restores production and records GREEN. The explicit malformed-key install and
old-version cache cases are direct negative controls, not reasons for another
mutation per row. Reuse D1's already demonstrated compensation-removal RED and
restored GREEN; rerun the affected D1 case after migration without planting the
same fault again unless that compensation mechanism changes.

Retained reservations permit the approved producer-before-consumer compile gap;
no owner claims completed handoff from an uncompilable partial migration. Types
hands off the exact approved signatures, derivation/error evidence and install
validation; typecheck hands off grounded full-signature keys and keyed references;
Binary/int integrates generation correspondence and transaction observations;
backend resolves only dependent label/cache concerns. Test owns the preserved
public reorder pair and existing public/cache/link subset. Root coordinates
exclusive source/build ownership. Any new public delta beyond the exact packet
returns to its existing gate, not an inferred extension of this allocation.

Completion requires the focused module/public results above, finding-scoped
review of identity authority and generation/cache boundaries, then the existing
full-suite gate after the chain compiles coherently. Exact generated API changes
must match the approved two method replacements, function/error additions and
stated trait implementations; later generated-diff confirmation remains required
and separate from ACT0955 formatting contraction. Preserve original Q1/D1
acceptance and the explicit absence of public codegen-failure reachability proof.
No new tests, source implementation or builds were performed for this delta.

## Identity migration executing checkpoint

QA records the following owner execution evidence on 2026-09-10 against HEAD
`dc78ddbe` plus the evolving S122 working tree; it is not a pristine-checkpoint
rerun or a QA build. Current reservations/status are in
[SPRINT.md](../../sprints/SPRINT.md).

| Surface | Available evidence and bounded credit |
|---|---|
| Types uniform key producer | 283/283 PASS, run `8b8cd4cd-fdbc-4eae-b349-4748f0dec942`, `/tmp/s122-types-signature-key-nextest.log`. Existing `/tmp/s122-types-key-result-omission-red.log` records intended distinct-result collision failure in `executable_key_result_context_and_nominal_structure_are_lossless`; restored production is covered by the green types run. Independent review reports no findings for that delivered producer. |
| Typecheck context-bearing consumers | Full crate903/903 PASS, run `bc3f7d54-f41a-4d87-8910-92f8eaf717dd`, after repair of48 obsolete key-spelling test expectations. The remaining canonical negative assertion was separately corrected and passes1/1 in run `2b772a0a-a7a5-4111-aba6-5b9978408548`; root readback is complete. This is the reported producer/consumer completion, not an assertion that old-key expectation failures were48 production defects. |
| Binary/int integration | Combined18/18 PASS in `/tmp/s122-int-signature-key-focused-green-dc78ddbe.log`, including the original permanent generic reorder subject/control and original Q1/D1 transaction checks; agent compilation also passes. Later removed-arm correction/control batch8/8 passes and finding-scoped review is closed. Credit same-family generic reorder as corrected in that integrated batch; preserve its original RED provenance. |
| Remaining cross-class publication condition | A distinct permanent overload→ordinary regression remains RED at the types publication gate. Arch owns its private correction under existing REPL §18.1/§18.3; no new API or new QA test allocation is inferred. Its correction/evidence remains outstanding despite the above green batches. |
| Backend/cache and overall acceptance | Key/native-label, self-call/object/cache agreement and semantic cache invalidation observations remain pending. No overall identity-migration adequacy or sprint acceptance is claimed. Retain existing scoped review, generated API confirmation and fresh full-suite gates after coherent completion. |

D1 evidence is private, armed compilation/compensation and production diagnostic
attribution, not a public failure-trigger test. The deliberate compensation
removal produced its intended fresh-cell RED in
`/tmp/s122-d1-compensation-plant-red-dc78ddbe.log`; restored production passes in
`/tmp/s122-d1-compensation-restored-green-dc78ddbe.log`, and the later integrated
18/18 includes the D1 witness. This supersedes earlier pending compensation
wording in the chronological observations. PLAN now names the live private unit
and successful public sequential-turn controls instead of removed failed-codegen
cases. No legitimate public source-triggered backend failure is established;
none is requested to replace the approved private evidence.

## RP4 cached executable reconstruction intake

Current public evidence is `/tmp/s122-public-identity-cache-link-evidence-dc78ddbe.log`
(2026-09-10, HEAD `dc78ddbe` plus S122 working tree, production frozen during
test's reservation). Existing unchanged
`tests/multi_arity_clause_param_51_2.rs::rp4_unannotated_backflow_accepted_and_runs`
is the sufficient small repro: two unannotated clauses, the two-argument clause
calling its three-argument sibling, then `main` invokes `(rp4 3 4)`. Run
`08c3de7a-2009-4c3d-b980-cb7b111b4785` observes3 in fresh REPL/run/link and cached
REPL; cached run/link exit1 at rematerialization rejection. The diagnostic's1
is process failure, not a wrong language result. No native wrong-body execution
or memory fault is observed. Existing fresh/cached mode controls discriminate
the condition; no new matrix or smaller speculative fixture is required.

QA source reading localizes the rejection to
`src/worker.rs::plan_demand_publication`: its expected staged key plus
`Life::Concrete`/matching `minted_from` observation is absent. The emitting
condition does not itself identify why replay missed. A bounded source lead is
that `capture_mono_demands` captures concrete `minted_from` provenance, while
`crates/cranelisp-typecheck/src/program/mono_collect.rs::instantiate_demand_roots`
requires the selected current arm to be `Life::Template`. RP4's documented
back-flow settles its parameter types concrete. This is a hypothesis about the
producer/consumer lifecycle boundary, not proof that the fixture took that exact
branch or authority to skip a required realization.

Next owned investigation belongs to retained Binary/int entry preparation. For
the exact rejected two-argument key, compare cached prior binding/key/link and
prior/staged selected arm Life/scheme; capture replay warning/result and staged
key/link lookup, paired with the existing fresh source control. One original
preparation/module observer is sufficient if private instrumentation is needed
under that owner's later reservation. It must distinguish whether historical
provenance from an already concrete arm is being treated as a reusable generic
template demand, versus missing/misrestored producer state. Consult typecheck
only if the observed producer lifecycle is wrong, or backend only if the actual
restored metadata differs from what was written. Do not infer an object-label
fix, weaken rejection, drop provenance, or assign source correction from the
error text alone. Preserve all six existing outcomes as acceptance of any
attributed correction.

Other allocated observations now execute: ordinary all-mode control PASS
(`4be1039e-a366-4d8f-afea-a6eaf492025c`), final generic reorder2/2 PASS
(`99481035-058d-43e5-baba-c3253129bcb4`), and cache identity3/3 PASS
(`a7eb9cc5-4fa1-446e-b646-604f3564bb77`). The latter covers result-only closure
uncached/cold/actual warm agreement, generic self-call JIT/warm-object/link, and
prior schema28 rejection with current fingerprint, paired object rebuild and
current warm reuse. The initial schema fixture lacked an object and was repaired
to an existing object-producing fixture; that was a test setup failure, not a
compiler defect. Root reports types285/typecheck903/backend583 passing and their
identity reviews closed. These are credited bounded results, not overall
adequacy: RP4 cached executable reconstruction remains an open current defect.
No production/test edits, builds or extra execution were performed by QA here.

## Uniform identity slice — final bounded adequacy

QA judges the allocated uniform identity evidence **adequate for generated API
baseline confirmation** on 2026-09-10. This supersedes the open identity/RP4/cache
statuses in the chronological checkpoints above. It is not overall S122 or
Phase-5 acceptance: Q3/runtime, evals, shared document checker and the remaining
sprint closure gates stay open. No new broad review/test cycle is required by
this assessment.

| Completed boundary | Final evidence / finding disposition |
|---|---|
| Types key authority and cross-class publication | 285/285 PASS, `/tmp/s122-types-cross-class-green-dc78ddbe.log`, run `c6acbdfd` (prefix). Approved API and private overload↔ordinary publication correction independently reviewed without findings. Existing result-omission intended RED and restored-green evidence establish collision detection. |
| Typecheck consumers | 903/903 PASS, `/tmp/s122-typecheck-signature-oracles-green-dc78ddbe.log`, run `bc3f7d54-f41a-4d87-8910-92f8eaf717dd`; residual canonical negative corrected1/1 in run `2b772a0a-a7a5-4111-aba6-5b9978408548`, root verified. Identity review closed. |
| Backend consumers | 583/583 PASS, `/tmp/s122-backend-signature-key-full-green-dc78ddbe.log`, run `795667b5` (prefix); identity review closed without findings. Public object/cache evidence below closes the separate execution gap. |
| Binary/int generation/transaction | Existing18/18 plus agent compile and removed-arm8/8 remain credited; the removed-arm review finding is closed. Generic reorder public subject/control remain unchanged and pass2/2, run `99481035-058d-43e5-baba-c3253129bcb4`. Existing ordinary all-mode control passes, run `4be1039e-a366-4d8f-afea-a6eaf492025c`. |
| RP4 cached reconstruction | The unchanged six-mode public RP4 witness passes, `/tmp/s122-rp4-public-green-dc78ddbe.log`, run `9d5b51ba-f957-444a-bcc8-60e3d1253278`. Worker7/7 PASS, `/tmp/s122-rp4-worker-focused-green-dc78ddbe.log`, run `8799b247` (prefix), includes the back-flow concrete-arm preparation and existing D1/reorder controls. Use this7/7 log, not the misleading standalone filename containing an intermediate failure. No production review findings remain; the source comment now correctly records follow-on ownership completion and root verified it. |
| Real object reuse and cache retirement | Final3/3 PASS, `/tmp/s122-public-cache-object-review-correction-dc78ddbe.log`, run `e8b05c34-130f-4131-8dfb-6fbbd8aa9d40`. The original generic-only util fixture was deliberately armed and failed because util.o was absent, run `fb45ef08-e7c5-4baa-bde9-bf5dba3b8fdc`. A concrete exported wrapper causes the retained generic recursion to be emitted in util.o; cold/warm/link return5 and exact object bytes/mtime remain unchanged across warm/link. Result-only closure metadata reuse remains separately credited. Current-fingerprint schema28 refusal, object rebuild/schema29 restamp and subsequent warm reuse pass. The object-cache review finding is closed. |

The final cache correction supersedes the earlier claim that a generic-only
module metadata hit proved object reuse. The missing-object RED and unchanged
object GREEN make the final observer discriminating. Likewise, final RP4 public
and worker results supersede the earlier reconstruction intake without erasing
its failure provenance. No remaining identity finding is carried as hidden
follow-up work. The runtime Q3 classification is unaffected.

Arch regenerated all seven API baselines. QA read
`/tmp/s122-identity-public-api.diff`: types has exactly20 added and2 removed
lines for the approved context-bearing method replacements, shared helper and
non-exhaustive error surface (including generated standard/auto-trait entries).
Arch reports the other six baselines byte-identical; ACT0955 contraction is
untouched. This is the concrete generated delta ready for the existing user
confirmation, not QA approval to widen the API or contract other baselines.
Canonical Binary/int/typecheck design alignment and finding-scoped reviews are
reported complete. QA performed record/log/diff inspection only; no production
edits, compiler builds or fresh executing tests were performed here.

## Readiness and closure

This assessment reuses the existing stocktake and source observations; it creates no new executing compiler evidence. Design readiness is assessed per stream. D2/D4/D5 are ready for bounded Phase-5 reproduction/attribution, with an explicit stop before any ungrounded correction; they do not authorize guessed fix designs or test authoring in Phase 3. D1 private compile/publish failure evidence substitution was approved on 2026-09-10; implementation and executing evidence remain pending, with public success controls retained and no claim of public codegen-failure reachability. D3 producer and all selected consumer designs are reviewed and adequate. D8, the exact limited private construction/traversal/transfer amendment, was approved on 2026-09-10; arch, intrinsics/shared and primitives contract propagation is complete; source implementation and executing evidence remain pending under their allocated owners and later phase gates. D6 gates live execution, not Phase-5 harness authoring; D7 shared-pilot scope is approved; its implementation and evidence proceed under authorized Phase-5 reservations. Phase 4 organization was authorized on 2026-09-10; the [execution wave plan](../../sprints/s122-wave-plan.md) sequences the following evidence boundaries, with Phase 5 authorized on 2026-09-10 and implementation assigned through sprint reservations; live execution still requires D6. The approved METHOD producer→consumer continuation permits temporary compile failures within retained reservations; it is not a completed handoff and closes only with the allocated behavioral and full-suite evidence.

| Stream | Current readiness boundary |
|---|---|
| Eval runner/corpus/grader | Local stub harness (E1, maintenance check) delivered and adequate once test's attribution/empty-log correction lands; run `self-check` when the runner or fixtures change and before a live baseline, outside the default suite. E2 (diagnostic observer) has one live observation: `claude-haiku-4-5-20251001`, one attempt per task, both tasks complete success including reviewed sequence-io API compliance; four earlier attempts were pre-inference provider rejections. This is a smoke observation, not a reliability estimate; tokens and cost are unknown. The enabling request-cap correction in `src/agent/provider.rs` is established only by that live acceptance: its module unit is unexecuted because the agent-feature lib tests do not compile, which is open sprint intake for dev. Raw reports and QA assessments are retained locally under `.local/s122-agent-evals/haiku-baseline-20260919*/`. |
| Generic/IO and language/collision intake | Ready for bounded existing-witness reduction and attribution; stop before a correction without its owning design and intended RED. |
| Failed-turn replacement evidence | GO at the design-readiness boundary: D1 substitution approved on 2026-09-10. Implementation and executing evidence remain pending under Phase-5 reservations and subsequent closure gates; retain public success controls and the explicit absence of public codegen-failure reachability proof. |
| Macro/runtime transfer | Binary/int and intrinsics designs reviewed: normal success discharge, explicit trap forfeiture, nine consuming APIs and typed callbacks align. Intrinsics Q11 now specifies admission to Pending, successful-send publication, loser cancellation before ready-receiver repoll, exact once disposal, winner control and unwind-safe scoped barrier cleanup. The dependent launch fixture belongs to retained backend dev. Primitives design is reviewed against its complete declaration projection and exact construction/traversal/transfer mapping. GO at the design-readiness boundary: D8 was approved on 2026-09-10. Shared guard/contract design propagation is complete; source implementation and executing evidence remain pending under Phase-5 reservations and subsequent closure gates. D0 clause-convention observations precede host transfer; integrated evidence remains the completion gate. |
| Reload/result/convergence | Binary/int design reviewed against Q6–Q9: explicit demand staging into the same publisher, private replay retirement and canonical helper consumption align. Backend design also reviewed: canonical result-root call-site artifact observation, both Vec guard CFG polarities and scoped CLIF reconciliation are adequate. GO for these selected mechanisms; 0779 uses its existing typecheck design and dev-owned private unit. Attribution-driven behavior changes retain their separate stop. |
| Shared document-checking pilot | GO at the Phase-3 design/evidence-allocation boundary: D7 and host/adapter choices are approved, the shared checker contract and bounded evidence allocation are reviewed. Shared mechanism/project declaration work, read-only validation in both repositories, Cranelisp adoption and repairs remain pending under Phase-5 reservations and subsequent closure gates. Magic edits/upstream publication need subsequent approval; no blanket residual baseline migration. |
| Record retirements and baseline formatting | Ready for source/evidence reconciliation within owning streams; generated API contraction still returns for user confirmation. |

The reviewed design carriers are [Binary/int](../../design/int/s122-closure.md), [intrinsics](../../design/intrinsics/ownership-and-disposal.md), [primitives](../../design/primitives/primitives.md#24-typed-abi-boundary), [backend](../../design/backend/s122-closure.md), and the existing [auto-curry evidence design](../../design/typecheck/auto-curry.md). D1 and D8 are approved with implementation and executing evidence pending. D7 shared document-checking pilot scope, host ownership and checked-in adapter choices are approved; the shared checker design and evidence allocation are adequate. Phase 4 was authorized on 2026-09-10; Phase 5 was authorized on 2026-09-10, and subsequent Magic edits/upstream publication remain separately gated. D6 is a future live-evaluation configuration/budget gate and does not block runner design or implementation planning. No additional compiler contract decision is inferred from owner/copilot execution policy.

At stream closure, inspect the actual change, dev unit evidence, independent test evidence, review findings and exact API confirmation. At composition closure, run the fresh default suite and isolated agent lane in their required environments, then the authorized live eval baseline. Report known/environment/provider limits separately. Broaden testing only for a changed condition or unresolved composition risk. Update PLAN/spec traceability once actual evidence establishes coverage; this assessment does not confer Tested status.


## Generated identity baseline confirmation and runtime handoff

The user's subsequent explicit approval on 2026-09-10 confirms the generated
identity baseline: types +20/−2, other six unchanged, ACT0955 untouched. The
confirmation checkpoint described above is closed; it is not whole Phase-5
acceptance. No further identity-baseline permission is pending.

The next reserved test work is the existing Q4/Q5 macro before-state and Q6
`/mem` evidence, not another readiness cycle. Reusable exact artifacts are
`tests/macro_turn_marshal_leak_0889.rs`'s nullary and one-argument marginal
programs, existing interior-alias cases, and
`tests/repl_introspection.rs::mem_with_expr_emits_signed_delta_line` with its
`str-concat` heap result and rendered `"hi world"` check. The /mem case currently
checks signed-field presence, not result-release balance; use the already
allocated warmed heap/control refinement to establish the before-state.

For Q5, `tests/plan/s118-test-plan.md` §2.5 preserves the P4 historical setup:
fresh isolated session, debug binary, `--run --no-cache`,
`CRANELISP_RC_STATS=1`, full `CRANELISP_LIB=stdlib/` and trivial Int-returning
child. It is a setup/provenance lead, not a current golden or authoritative old
mechanism claim. Record the exact chosen input/library/configuration and current
counts before the grouped runtime migration, then repeat that identical setup
afterwards. No retained exact historical raw session was established by this
bounded readback; do not invent one or assert1143. Reuse the minimal current
macro marginal witnesses for slope and the one paired session measurement for
fixed overhead; do not rebuild the historical P-ladder or add a matrix.


## Q4/Q5/Q6 allocated before-state recorded

QA read `/tmp/s122-q4-q6-before-red-dc78ddbe.log`,
`/tmp/s122-q5-full-stdlib-before-dc78ddbe.log` and the exact two test diffs on
2026-09-10. These are test-owned executions against HEAD `dc78ddbe` plus the
recorded S122 working tree, not a QA rerun or a pristine historical binary.
The before-state adequately arms the existing allocation; implementation is
already authorized. No additional readiness gate or matrix is introduced.

| Allocation | Exact before-state and continuing obligation |
|---|---|
| Q4 macro discharge | Historical magnitude oracles first pass2/2 (`06be9166-8af8-4b8b-9fb2-b4259525f673`). Renamed permanent `tests/macro_turn_marshal_leak_0889.rs::{macro_turn_marshal_one_argument_expansion_is_balanced,macro_turn_marshal_nullary_expansion_is_balanced}` require balance and both fail as intended (`0ad9accd-129e-4cba-bf11-15d604b46ab2`). Each control allocates/frees1; one-argument subject3/1 gives marginal+2, nullary subject2/1 gives marginal+1; child exits0. Same minimal programs/configuration, changed acceptance oracle, not a production regression. Existing interior-alias run/link/assert/quarantine guards pass4/4 (`3bd8a1cb-2cf0-461f-b4ee-c5baea0cd045`); the REPL case was not in that filter, so do not report5/5. Retain these balance and alias observations after grouped migration alongside allocated module ABI/transfer/trap evidence. |
| Q6 memory observation | `tests/repl_introspection.rs::mem_with_expr_emits_signed_delta_line` retains its name and now warms `str-concat`, checks scalar `/mem 0`, then separately checks rendered heap `"hi world"` and heap delta. Prior field-only case passed1/1; strengthened case fails as intended (`a956c445-7255-46cd-b5d2-d3c7b264e278`). Scalar alloc/dealloc/bytes/live deltas are0; heap alloc+3/dealloc+2/bytes+32/live+1. This arms post-owner-release sampling, not a bootstrap/macro residue inference. Correct rendered value and balanced live delta remain separate acceptance observations. |
| Q5 original session | Exact isolated input is `(import [primitives [Pure]])` then `(defn main [] (Pure 0))`, retained at `/tmp/s122-q5-before.jHUHi6/user.cl`. Run with cleared environment, `CRANELISP_LIB=/home/alilee/cranelisp/stdlib`, `CRANELISP_RC_STATS=1`, debug binary and `--run user.cl --no-cache`; exit0. Current alloc1198/dealloc55 gives1143. The log retains input/binary hashes, clean library tree `f51a1bcdbe933e68d2ae86a52dea4984d4c59ef2` and exact command. Reuse that input/library/configuration/build mode/cache posture for the paired after observation;1143 is a measured current before-state, never a threshold or claimed necessary after value. Report fixed-session change separately from Q4 marginal balance. |

The original raw-session availability limit in the earlier handoff concerned
S118 provenance; a reproducible current Q5 session is now available at the
explicit path above. A bounded search found no old long Q4 function-name
references in current `tests/plan`, design, spec or sprint Markdown; QA uses the
new live names above. ACT0956's inherited owner is corrected to intrinsics dev
as already allocated by Q11. No new source, test or build work was performed
for this record update, and there is no material evidence concern requiring
interruption of the authorized runtime implementation.


## Intrinsics producer, Q3 module and Q11 evidence checkpoint

QA inspected the current module cases and owner logs on 2026-09-10 without
source/build activity. Focused8/8 PASS is recorded in
`/tmp/s122-intrinsics-handle-q3-q11-final-green-dc78ddbe.log`, run
`c302a849-f90c-4654-8b2c-6b7e16ae5d11`. It covers consumed-owner balance, debug
leak detection, unrelated-unwind handling, shared/unique returned Bind cases,
ready-loser/winner handoff and the current trusted-base guard. It does not prove
integrated public Q3 sequence behavior or macro consuming ABI/discharge.

Full intrinsics run `f9a7fbea` (prefix),
`/tmp/s122-intrinsics-full-sandbox-result-dc78ddbe.log`, reports346/349 PASS and
three socket/reactor timeouts. The three named reactor cases then pass3/3 in
the authorized environment, run `88059622-c822-4350-89c6-927605ad3ead`,
`/tmp/s122-intrinsics-reactor-authorized-green-dc78ddbe.log`. Record this split
environment evidence honestly, not a single full349-green run.

The handle-bomb plant disables expected leak detection and fails because no
expected panic occurs; the unwind plant produces the intended destructor
double-panic/SIGABRT. Exact logs are
`/tmp/s122-intrinsics-handle-bomb-plant-red-dc78ddbe.log` and
`/tmp/s122-intrinsics-handle-unwind-plant-red-dc78ddbe.log`; restored behavior is
covered by focused8/8. The trusted-base plant in
`/tmp/s122-intrinsics-trusted-base-plant-red-dc78ddbe.log` detects an added
immediate-file call changing a per-file count. Independent review found that
this guard still permits an unauthorized caller substituted at the same count
and misses nested-module sites. That Important coverage finding remains open
for the queued exact guard correction and one scoped re-review; do not credit
the plant as proving a recursive function-level allow-list. Current production
sites and Q3/Q11 have no review findings. Public API baseline generation and
confirmation remain with arch's existing gate.

**Q11 / ACT0956 evidence is complete at its allocated module boundary.**
`crates/cranelisp-intrinsics/src/io/tests.rs` contains
`ready_blocking_loser_disposes_successfully_published_result_once` and
`ready_blocking_winner_transfers_result_to_caller`. Each admits the branch to
Pending before releasing the worker. The test-only barrier in `io.rs` fires
only after successful oneshot publication. The loser drops its still-unpolled
ready receiver and the nonzero disposer observes exactly83 once; the winner
polls the same ready handoff, observes no disposal before ownership transfer,
and its caller disposes exactly89 once. The scoped barrier releases on unwind
and normal execution waits for the worker handoff to finish. This directly
satisfies ACT0956's deterministic ready-state, exact-value/once and winner
criteria; no additional public test or runtime mechanism is required. Root subsequently verified the source and resolved/deleted ACT0956; the durable
[closure record](../../sprints/SPRINT.md#select-ready-loser-evidence-closure)
retains its disposition independently of the unrelated guard finding.

Q3's shared-parent module RED now turns GREEN with its unique control and final
balance assertion. Retain the already allocated public reduction/aggregate
acceptance after grouped consumer migration; neither that public result nor
Q4/Q5 macro discharge is claimed by the producer's focused run. No new matrix
or readiness gate is introduced.


## Standing-category reconciliation for filing0944

QA read the original referred coverage-gap/negative-coverage artifacts and
current PLAN before disposition. Those two dated artifacts do not themselves
define the category, and the historical QA command path is retired. However,
PLAN already explicitly names the standing definition-variants lens and contains
variant/positive/negative matrices; the filing's universal absence claim is
false. Its remaining discoverability/currency concern is repaired by
[PLAN's standing audit section](PLAN.md#standing-coverage-audit--definition-variants),
which states the existing procedure, current scoped family status and limits
of historical matrices under current QA risk/cost rules. No complete fresh
variant census, new test matrix or implementation convergence is claimed.
The QA-targeted0944 filing is resolved/deleted; the linked PLAN section is the
durable closure carrier for the original sprint inventory row. No source/tests,
builds, shared skill or policy changes were made.


## Primitives evidence and guard review checkpoint

Primitives focused11/11 PASS is recorded in
`/tmp/s122-primitives-d8-focused-green-dc78ddbe.log`, run
`8e1f35eb-d874-4dbc-84fb-b9995a1dde72`; full102/102 PASS is recorded in
`/tmp/s122-primitives-full-green-dc78ddbe.log`. Credit the existing declaration
ABI/negative checks, parse controls, owned string/Vec handoff, identity borrowing
and quote/shared-tail balance observations at their module boundary. Independent
review reports no current production conversion/transfer defect, but final
acceptance is not established by these green runs.

Three deliberate prohibited-site plants each produce their intended exact-site
guard RED: `/tmp/s122-primitives-adoption-guard-plant-red-dc78ddbe.log` adds fresh
adoption in `_force_alloc_dep`;
`/tmp/s122-primitives-borrow-guard-plant-red-dc78ddbe.log` adds borrowing in
`make_sexp_sym`; `/tmp/s122-primitives-storage-guard-plant-red-dc78ddbe.log` adds
raw transfer in `_force_alloc_dep`. Restored production passes the focused and
full sets. These prove detection of those directly spelled prohibited sites,
not every equivalent call spelling. Review found crate-visible
`AbiHandle::{from_abi,into_abi}` admits out-of-wrapper trait-dispatch conversions
that the guard does not count. That blocking guard finding remains open for
the queued distinct primitives correction and one scoped re-review; it is not
covered by the three plants or waived by current production correctness.

The separate intrinsics guard finding is now closed by scoped re-review. Its
recursive exact enclosing-function/site inventory detects the same-count
unauthorized-helper move in
`/tmp/s122-intrinsics-handle-guard-same-count-move-red-dc78ddbe.log`, run
`f328523a` (prefix); restored1/1 PASS is in
`/tmp/s122-intrinsics-handle-guard-green-dc78ddbe.log`, run `e0a1f21b` (prefix).
This supersedes the earlier open immediate-file/count-only condition. Retain
its lexical-analysis limitation: this is the delivered source-site guard, not
a general semantic proof over arbitrary Rust spellings.

Public consumer integration and generated runtime API baseline confirmation
remain pending. Q11's separately closed action remains closed; no public Q3 or
macro closure is inferred. QA inspected logs and updated owned records only;
no new allocation, matrix, source edit, build or execution was performed.


## Primitives guard closure and backend runtime consumer checkpoint

The primitives trait-dispatch guard finding is **closed** after the one scoped
independent re-review. The out-of-wrapper trait-call plant in
`/tmp/s122-primitives-abi-trait-guard-plant-red-dc78ddbe.log` fails as intended
on forbidden `bool.rs`; restored1/1 PASS is recorded in
`/tmp/s122-primitives-abi-trait-guard-restored-green-dc78ddbe.log`, run
`b89e61a5` (prefix). The corrected guard covers qualified, UFCS and method
conversion calls, restricts `AbiHandle` use to approved files, and pins the
approved wrapper/helper sites. Preserve its lexical boundary; do not represent
it as semantic analysis of arbitrary equivalent Rust. This supersedes the
blocking status in the preceding historical checkpoint, without changing the
credit for the earlier three direct-site plants or the focused11/full102 runs.

Backend runtime-consumer review reports no material findings. Focused4/4 PASS
(run `4dbc0fbe`, prefix) and full586/586 PASS (run `cb4a87e5`, prefix) are
distinct from the earlier identity-only583 run. Compile/format checks pass;
clippy's recorded existing lint debt is not a clean-clippy result. Actual
solution-golden/public integration remains unexecuted pending the host build;
backend module success does not substitute for it. Intrinsics design/crosspair
records now reflect the closed guard and delivered primitives/backend consumers.

Binary/int host completion, public integration and exact generated runtime API
baseline confirmation remain pending under their existing allocations. No
additional gate, matrix, source change or compiler execution was introduced
by this records-only QA update.


## Q4 remaining alias residual after host migration

Host module52/52 PASS (`82cbd387-292a-4778-9826-5ecf3decac28`,
`/tmp/s122-int-runtime-module-focused-result-dc78ddbe.log`) does not close the
public macro discharge condition. Existing permanent pair run
`8054f1da-10b2-4cc0-8ff6-1c2ff51e98ef` is1 PASS/1 FAIL: nullary expansion
balances; one-argument alias retains marginal1 against control0. This improves
the earlier+2 but remains an acceptance failure, not a new permitted residual.

QA read `/tmp/s122-int-d0-clif-result-dc78ddbe.log` and current source without
builds. The successful identity-clause path increments the extracted returned
child once in its match block (`v8`) and again at the return join (`v2`), then
calls the argument-list consumer on `v1`. The constructor-result/nullary paths
do not have the same two-retain pattern. Current `src/expander.rs::invoke_clause`
transfers its argument and copies/consumes the successful returned owner once;
`src/process_form/macro_clause.rs::pin_macro_clause_ownership` clears the
summary as required. These observations support investigating generated alias
lowering, not declaring host modules sufficient or changing the consuming ABI.

The bounded next owner is backend: observe the exact prepared MacroClause
scheme, bound parameter type and ownership/provenance decisions responsible
for both emitted retain sites, using this existing identity clause and the
existing nonalias/nullary control.
At that checkpoint, the now-retired `defn_param_types` helper in
`crates/cranelisp-backend/src/compiler/fn_compiler.rs` queried `Binding::callable` by generated definition name, whereas the macro
body lives under its selected clause; this is a specific lookup lead, not proof
that a missing type causes the residual.
`crates/cranelisp-backend/src/compiler/match_codegen.rs` has a borrowed-return
upgrade and the function compiler also protects escaping values. Determine
whether the observed pair is duplicate protection or requires a balancing
release before prescribing a correction. One module/CLIF observation at that
seam under the backend reservation is sufficient; preserve the existing public
RED and avoid another matrix or guessed release. Binary/int retains its own
reservation and does not acquire backend source ownership through this record.
No new public test or source/build work was performed by QA.


## 0932/0936 current realization-roster evidence handoff

QA read both live filings, `design/arch/total-concreteness.md` §3.3, the
S119 NC-R row, current lifecycle and actual bootstrap source. The authoritative
ruling retains an executing closed production uniform-body roster observation
to expose an undeclared additional representation dependency. That obligation
is not discharged by synthetic `UniformRust` fixtures or a designer's witness
assertion. The historical four-member set and I-ABI rationale are superseded;
0932's vec-len inline/no-slot/no-shim obligation is already satisfied.

Current source requires a narrower, accurate projection: bootstrap mounts
`catch-runtime-error` through `insert_primitive`, and its existing
`src/bootstrap.rs::mounts_catch_runtime_error_primitive` checks a polymorphic
`Life::HostPromised` with no slot. `TemplateBody::UniformRust` is a supported
recipe, but its presence in a synthetic typecheck fixture is not a production
roster. A UniformRust-only empty census would miss the actual hand-written
polymorphic body and falsely discharge the contract. No new lifecycle or API
requirement is inferred from this mismatch.

One settled next handoff: in the later test reservation, coordinate the existing
root/bootstrap module owner to reuse `fresh_tables` and real
`mount_synthetic_modules`, then enumerate the actual mounted polymorphic
hand-written realization entries through current HostPromised/UniformRust
carriers. Establish the exact canonical owner/body set from that production
mount before fixing an oracle; include neither source/synth templates nor
inline operations merely because their scheme is generic. Pair the enumeration
with the existing catch-runtime-error no-slot/scheme observation and existing
Vec inline guards; record each real roster member's existing representation
dependencies. An explicit unexpected-member negative over that same projection
can demonstrate the closed-set refusal without new runtime machinery or a
public-mode matrix. The cell and plan must say backend uniform-realization
roster, not polymorphic typecheck licence. Existing tests alone do not establish
this closed production set, so0936 and0932's linked second deliverable remain
open for that one evidence task. Design/primitives should remove the unsupported
claim that a production UniformRust roster is already pinned; root has this
source-backed handoff.

## Public Q3 reduction and Q6 follow-through

The existing Q3 public reduction/control batch now passes4/4 across its
allocated modes, run `dddc845f-0d1c-49e2-bd3b-8a1666bcda12`,
`/tmp/s122-int-q3-sequence-result-dc78ddbe.log`: two nested-action sequence,
explicit-bind control, one-action control and empty sequence. This closes the
previous reduced public RED in conjunction with the module shared-parent
observation; the broader public aggregate and remaining runtime gates are
still pending. The strengthened heap/scalar `/mem` witness passes1/1, run
`c217a766-0769-4d77-800b-bd94b12a8986`,
`/tmp/s122-int-q6-mem-result-dc78ddbe.log`, following its recorded intended
heap-live1 RED. Credit Q6's allocated rendered-value/post-release process
observation; it does not prove macro balance or overall runtime completion.
No source edits, tests or builds were performed during this QA reconciliation.


## Q7 external overload reload carrier finding

Independent Binary/int review raised an Important foreign-template generation
condition; QA source readback confirms the carrier gap, without an executing
wrong-result claim. `src/worker.rs::capture_reload_instantiation_demands` keeps
the historical `OverloadArm` ordinal/type arguments. In
`extend_reload_demands`, a foreign owner is resolved from the current dependency
table using that same selector and its current scheme. Unlike local replacement
matching, this does not establish correspondence after dependency clause order
changes. The approved uniform identity packet requires the authoritative
template generation/schema and semantic matching before replay; no new API or
language rule is needed to identify the omission. The plain generic Q7 witness
and local-family reorder evidence do not cover this foreign path.

One minimal next Binary/int module observation is allocated under its next
reservation: use a real imported generic family with legal one/two-arity clauses
and consumer-owned prior concrete realizations; capture the consumer's reload
packet, reorder the dependency with the same signature set, then reload the
consumer. Inspect both prior concrete identities, staged selected-arm backlinks
and compiled bodies immediately after reload, before a later call can remint
a missing instance. Pair with the same consumer reload under an unchanged
dependency. Ensure the fixture reaches `extend_reload_demands`' foreign-owner
branch rather than the local authored-replacement matcher. Use the existing
legal generic shape and module reload facilities; no new public seam or mode
matrix. First record the intended failing carrier/result observation. Design
then determines the private correspondence correction, preserving atomic
publication/retirement and owner retention under the existing reload contract.
If legitimate setup cannot retain the claimed old-selector condition, report
that reachability limit before prescribing a fix. QA requested review's final
source/fixture detail; source observation above is the bounded handoff and does
not imply a completed independent review.

Queued record reconciliation remains separate: root reports real bootstrap
roster2/2 (`cf467c35`, prefix), with design-complete0604/0740/0793 and QA0818
awaiting their exact closure readbacks. This note credits the reported roster
execution only; it does not delete those filings or substitute for their
criteria. No tests/builds/source edits were performed during this QA intake.


Q7 reviewer follow-through adds a distinct demand-only omission to the same
retained Binary/int handoff. QA verified `check_cluster_to_staging` returns
None for empty ordinary parsed entries;
`prepare_cluster_commit_with_demands` then returns before
`extend_reload_demands`, and `src/scheduler.rs` clears the packet at terminal
typecheck completion. The delivered marker-bearing fixture does not observe
this path. This is source-confirmed control flow; executing loss remains to be
armed, not presumed from the review report.

Prioritize one import-only caller subject with an external plain generic and
prior transient Int/String realizations: persist/reload the caller's import-only
source, inspect recovered bodies before subsequent eval can remint. Its control
adds the unrelated marker used by the existing fixture. Keep dependency order
unchanged here so empty-work omission is discriminated independently. Reuse
that setup for the external-overload condition above with marker present to
ensure replay is reached, comparing unchanged/reordered dependency. Combine
helpers where economical, not the causal oracles: an early empty-work exit
cannot prove ordinal replay correctness. Both belong to the one queued Q7
owner visit, with no new public seam/matrix or inferred API. Review supplied
the exact paths; final integrated review remains pending.


## Queued filing reconciliation — delivered roster and census limits

0936 is resolved/deleted on the actual production roster2/2 and live cell
rustdoc, as recorded in [PLAN](PLAN.md#s122--0936-production-realization-roster-closure).
This supersedes the earlier unproven-roster handoff. The observed current set
is four HostPromised bodies, not the synthetic UniformRust fixture and not an
inferred single-member trajectory. 0932's vec-len and linked roster deliverables
are now both satisfied; its design owner receives that exact closure handoff.

0604's explicit no-flip retirement ruling already discharged executing guard
evidence; its remaining design census rows and the imports mirror now exist,
including all three session-init seams and the Private/intra-module corrections.
The canonical home is `design/int/int.md` §6.7.
0740/0793's design obligations are satisfied. The one remaining retirement rider
is test-owned commentary in `tests/index_race_foreground_0604.rs`: replace the
UNLOCATED/future-fix/scheduling-attribution banner and assertion prose with the
landed structural-gate/no-regression disposition, retaining the existing sweep
and defect provenance. This is a mechanical source-comment repair in the next
solution-evidence reservation, not another historical race experiment or a new
acceptance run. Do not retire the group with that rider silently outstanding.

0818 records a disclosed contaminated-probe signature and pristine control,
not attribution of the old firing environments. No retained seeded/pristine
reproduction or corroborating historical directory state was established in
this readback. The truthful disposition is an unconfirmed historical explanatory
lead; the structural0604 closure does not depend on proving it, and no further
experiment is allocated solely to recreate unavailable provenance. Preserve
this limit in the final closure carrier rather than claiming the race was
proved to be contamination or that quiet sweeps established absence. Root
retains group retirement until the commentary rider and this attribution limit
are reflected in its closing records.

Reviewer also identifies one bounded marshal evidence omission for the next
Binary/int visit: extend the existing recursive single-owner completeness helper
and cell to visit `Sexp::Annotated` and both children produced by
`alloc_sexp_pair`. Current production construction is structurally correct;
this is an incomplete allocated producer observer, separate from both Q7
behavior findings. No new matrix, production fix or public case is implied.


## Q7 public watcher integration — new stale-body observation

The permanent
`tests/repl_watch.rs::watch_reload_recovers_two_generic_demands_without_replaying_stale_expression`
fails in run `1a306cbc-72d0-4780-9c35-0077a6295706`,
`/tmp/s122-runtime-q7-public-watcher-red-dc78ddbe.log`. The dependency is reached
through a prelude re-export. Named Int/String callers return7/7 before the
external generic file changes to42; after `[updated: generic_value.cl]` they
still return7/7. Process exits0 and sentinel31337 appears once. The final oracle
splits at the update boundary and rejects missing post-update42/42, so neither
notification nor retained old results falsely prove recovery. This is a new
public integration failure, not reopening the closed module carrier findings.

Current `src/session_v4/lifecycle.rs::dependent_modules` scans recorded direct
imports once; `poll_and_reload` consumes that selection. The corrected module
witness in `src/session_v4/persistent_worker_tests.rs` explicitly reloads the
consumer after its dependency and therefore does not exercise automatic watcher
selection through this prelude provenance. Source supports investigating that
orchestration boundary, but does not establish which dependent was admitted
in this public run.

Allocate one explicit-import twin to the same existing public shape: user
imports `generic_value/value-for` directly, with the generic re-export removed
from its prelude if needed, keeping callers, types, sentinel and changed file
identical. Keep the prelude subject intact. This distinguishes selection by
import provenance from downstream rematerialization without a mode matrix.
The next Binary/int observation records selected dependent modules and whether
the consumer reaches reload preparation before prescribing correction; if both
provenances fail, inspect the admitted consumer's captured/reminted bodies.
No scheduling-only attribution, new API, backend correction or notification-as-
publication claim follows from this intake. QA performed source/log reading
and owned-record updates only while test retained its source/build reservation.


Q7 watcher attribution settled by the executing provenance pair: run
`d18e302d-2720-4a89-9b7a-ded21001b079`,
`/tmp/s122-runtime-q7-public-watcher-pair-dc78ddbe.log`, is1 PASS/1 FAIL.
`watch_reload_direct_import_recovers_two_generic_demands_control` produces
post-update42/42; the unchanged transitive prelude-export subject produces7/7.
Both succeed as processes, report the dependency update and print the sentinel
once. Source plus this pair attributes the defect to Binary/int watcher
dependent selection/provenance: `dependent_modules` matches only each table's
recorded direct imports against the original changed set, and `poll_and_reload`
uses that one result without establishing affected consumers through implicit
prelude/re-export dependencies. The successful direct-import twin shows that
the corrected downstream reload/rematerialization can deliver both bodies when
the consumer is reached. This does not claim every internal dependency edge
has been independently traced.

The existing watcher §14.2 contract requires dependent recompilation in
topological order. The next retained Binary/int correction/design must make
this affected consumer reachable through the actual prelude/re-export
dependency relationship while preserving that ordering and existing path
admission/once-only semantics. Do not weaken the public oracle, replay prompt
expressions, or reopen the already-corrected demand/ownership path by guess.
The existing executing public pair and inspected selection source suffice for
this handoff; no additional private attribution observer is required. Dev may
use its ordinary focused selection unit to protect the correction's actual
branch, but QA allocates no second framework/matrix. Acceptance reuses the pair
with both42/42, sentinel once and successful process after the update; preserve
previous module replay/rejection/ownership evidence. One scoped review of the
changed selection path follows, under the existing gate, not a new role cycle.
No source/build activity was performed by QA.


## Runtime evidence checkpoint — matched residual and golden limit

The final matched Q5 measurement in
`/tmp/s122-runtime-q5-final-after-dc78ddbe.log` is alloc1198/dealloc1152,
residual46, versus original1198/55=1143 and intermediate1198/1025=173. Exact
input hash, clean library tree, cleared environment, debug build and no-cache
posture match the before-state. This demonstrates1097 more deallocations and
a fixed-session residual reduction of1097; the final stage reduces the
intermediate residual by127. It is an adequate paired measurement under Q5,
not proof of zero residual, a threshold, or attribution of every surviving cell.
The RC summary alone does not distinguish remaining macro allocations, retained
session/runtime owners or another allocation class. Keep46 explicitly
unclassified in closure accounting; do not label it harmless overhead or a
newly proved leak without liveness/provenance evidence. No automatic extra
experiment or correction is allocated solely because this diagnostic is
nonzero. If a broader zero-session-residue claim is proposed, its missing
provenance must be resolved or the claim narrowed; current Q5 promises the
matched comparison, not that broader claim.

Raw public Q4 balance pair is now2/2 PASS (`0ce70208`, prefix), with backend
Q4 scoped review closed; credit successful argument-alias and nullary-result
discharge for those cases. Binary/int affected13/13 PASS (`236d2b5d`, prefix)
and its scoped review are closed, preserving both Q7 module pairs, Q1
replacement/rollback controls and Annotated completeness. These facts do not
discharge the separate public watcher transitive-provenance RED; its executing
pair is reviewed sound and its correction is in the current int reservation.

The reported14 solution-golden results are **not credited**. Independent test
review found both extractors use `CLIF(\S+)`-style name matching, omitting the
whitespace-bearing canonical executable frames. Earlier selection/diff claims
therefore cannot establish complete affected golden coverage. The queued test
correction must demonstrate extraction of those frames, then recapture/review
the allocated actual golden changes; this is repair of an existing evidence
instrument, not a new matrix or another ownership test cycle. Keep original
raw Q4, module and Q5 observations separate from the invalid extractor claim.

The runtime API checkpoint remains pending: delivered producer/consumer module
evidence and closed scoped implementation findings are credited, but corrected
golden/public watcher integration and exact generated runtime baseline
confirmation have not completed. No whole Phase-5 or S122 acceptance is given.
Root/arch have now retired0604/0740/0793/0818 with the historical-attribution
limits in bounded-contexts §6 and preserved inventory links; this supersedes
their earlier queued retirement status without claiming a proven historical
race cause. QA performed log/record assessment only, no source edits/builds.


## Watcher complete-graph ordering review basket

The provenance-selection correction's public pair2/2 and watcher14/14 remain
credited for their actual paths. New independent review identifies two
source-confirmed ordering gaps in `src/session_v4/lifecycle.rs`; executing
wrong-generation behavior is not yet established. When no node is ready,
`dependent_modules` alphabetically emits every blocked node, although that set
can contain both a dependency cycle and acyclic consumers downstream of it.
A lexically early consumer can therefore precede its dependency component.
Separately, `poll_and_reload` appends dependent selection after changed roots
in incoming order, while `dependent_modules` treats all changed roots as
already available. `src/watch.rs::poll_changes` collects changed paths through
a HashSet, so two related changed roots are not ordered by dependency.
Watcher §14.2's topological cascade is the existing authority; no API/schema
or language-cycle admission change is inferred.

One retained Binary/int correction handoff covers the complete admitted reload
graph, including changed roots. Minimal module evidence has two discriminating
shapes using the production plan assembled for execution: (1) a dependency
component with two mutually reachable nodes and a lexically earlier acyclic
consumer downstream, requiring the entire component before that consumer;
(2) two simultaneously changed roots with a dependency edge, supplied in both
orders, requiring dependency before consumer in both cases. Keep an unrelated
node outside the selected closure and assert selected nodes occur once. Reuse
current graph/selection fixtures; do not build a public cycle fixture that
violates language admission merely to reach the fallback. The component case
is an ordering-boundary observation over the admitted graph, not proof that
source cycles have gained new semantics.

Record intended order REDs before correction. The simultaneous-root case must
exercise the same complete-plan entry used by `poll_and_reload`, not only
`dependent_modules` with roots already removed; otherwise it would repeat the
blind spot. A focused executable generation observation is needed only if the
plan consumed by the reload loop cannot be directly established by that module
case. The current source makes the missing order visible, so no new timed
watcher matrix is allocated. Design owns the ordering/component mechanism
under current dependency/provenance/path admission; QA prescribes neither a
new graph API nor an implementation algorithm. Reuse the existing public
provenance pair after correction, followed by one scoped ordering review.
Previously closed Q7 remap/empty-entry/Annotated and ownership conditions stay
closed. No source/tests/builds were changed by QA during test's reservation.


## Runtime generated-baseline readiness — 2026-09-11

QA judges the delivered runtime checkpoint **adequate to present the exact
generated baseline for user confirmation**. This supersedes the earlier open
watcher-order and incomplete-CLIF-extraction statuses. It is not whole Phase-5
or S122 acceptance and does not close other sprint streams.

Watcher complete-plan ordering has intended RED (`beacb3e6`, prefix) followed
by2/2 GREEN (`a58ef193`, prefix), with the scoped independent re-review closed
without remainder. The cases exercise the production consumed plan across
SCC/downstream boundaries and both orders of related simultaneous roots. They
do not simulate OS simultaneous delivery or execute real cyclic source modules;
review accepts their composition with the public watcher evidence. The public
provenance pair passes2/2 (`be88574b`, prefix); full watcher14/14 passes
(`977c5ba4`, prefix). Existing corrected Q7 carrier/ownership evidence remains
credited, not re-opened or rerun solely for owner changes.

CLIF capture's scoped re-review is closed. Corrected extraction accounts for
all14 entries, including whitespace-bearing canonical identities:23 identity
renames, zero frames added/removed and zero instruction changes. Parser/smoke
passes2/2 (`e4a4ed06`, prefix); selftest/diff covers14/14. The complete raw
capture is `/tmp/s122-runtime-clif-complete-capture-dc78ddbe.log`. These final
results supersede the invalid original extractor claims, not merely their
filenames. No additional recapture or broadened matrix is required.

The already recorded raw Q4 balance2/2, module corrections/reviews and Q5
matched1143→46 comparison remain adequate at their allocated boundaries;46
remains unclassified, not a threshold or zero-leak assertion. Current sprint
execution additionally records Q3 aggregate scalar driver PASS (`86114587`,
prefix), alongside the recorded reduction4/4, strengthened /mem1/1, public
lifecycle/RP4 7/7 (`d8ae6fb8`, prefix) and macro alias5/5 (`41871783`, prefix).
This supersedes earlier pending aggregate/alias-filter status for those runs.

QA read `/tmp/s122-runtime-public-api.diff` and its generated summary. The
exact default-feature/default-profile generation uses the established
`--omit auto-derived-impls` format: intrinsics +38/−9, replacing nine raw-i64
consuming signatures with Owned (including `fn(Owned)` callback) and adding
the approved handle surface. The other six generated baselines are byte-identical,
including the already confirmed types baseline. The diff matches the approved
packet; ACT0955 auto-trait contraction remains untouched. This is a
source-breaking Rust signature migration, not a changed raw C/GOT/heap/platform
ABI or schema.

No further runtime evidence repair is identified before presenting this
generated diff. The user explicitly confirmed that exact generated baseline on 2026-09-11:
intrinsics +38/−9, other six unchanged. This runtime checkpoint is closed. Existing sprint-wide full-suite/other-stream obligations
remain with their allocations; lexical guard and split-environment reactor
limits remain disclosed. QA performed records/log/diff assessment only, no
source edits, builds, tests or expanded review cycle.


Runtime baseline confirmation (2026-09-11): the user's explicit yes confirms
the reviewed intrinsics +38/−9 generated delta with the other six baselines
unchanged. Earlier readiness/awaiting-confirmation paragraphs are historical
observations, not a remaining permission gate. Whole Phase5 remains pending;
ACT0955 format contraction is separate and untouched. No new assessment,
review, tests, builds or source edits accompanied this confirmation update.


## ACT0957 residual outcomes — QA closure disposition

QA read the action and its referred audit §9, METHOD §3.1 and package
CONSUMING guidance before assessing the current evidence on 2026-09-11.
All six allocated residual outcomes now have adequate completed or approved
alternative dispositions; root has closed/deleted ACT0957. This is local tooling/record
closure, not package publication or whole Phase5 acceptance.

| Residual | Completed disposition and limit |
|---|---|
| R1 | CONSUMING now limits fresh recursive-clone reproducibility to a published package revision and explicitly distinguishes unpublished local contributions. Independent package review accepts that wording. The held98436c9 revision plus authorized local changes is not proof those unpublished changes can be freshly cloned; publication/consumer-pin movement retains separate authorization. No new remote verification is claimed. |
| R3 | User-approved ownership is recorded in METHOD: sprint owns AGENTS/Codex/Copilot host guidance; technical content retains its existing owners. |
| R4 | User-approved alternative retains eleven checked-in Copilot adapters and the consistency check, without a generator. This satisfies the advisory decision, not the original proposed implementation. |
| R6 | Package transport103/103 PASS in `/tmp/s122-act0957-r6-transport-result-98436c9.log`. Both transports exercise missing-contract refusal before launch plus restored launch, and actual SIGTERM producing abandoned/exit143. Established accounting repairs remain; independent review closes R6. This is fake-provider transport execution, not live model quality or provider production testing. |
| R7 | Recoverable records preserve327 parseable telemetry rows and review sessions `375fe048-959d-4da1-ad76-4d7344cecb3d` and `db287613-bf3d-42a2-91e5-a97e002b03e6` (Claude / `claude-fable-5` / high, both exit 0); no exact historical session-to-phase join is available. That unknown is explicitly retained rather than invented. Current native S122 dispatch attribution is separate. |
| R8 | Current design guidance assigns stdlib source to dev and uses METHOD §1.2; the remaining test-guidance `/testing` mention is dated S118 authorship, not a live assignment. Owning-role review accepts the repair/disposition. |

No residual requires another test matrix, source change or historical-attribution
invention to close this action. R2/R5 stay complete. The action's stale
independent-inspection-pending text can be replaced by the reported closed
package review during root's closure recording. The exact closure carrier is
this section; root performed the sprint-owned action closure.

D7 is independent: its candidate retains five review findings and pending
project observations. Neither ACT0957 transport success nor this disposition
accepts the shared checker candidate. QA made owned-record updates only; no
source/tests, build, review repeat or publication occurred.


## D7 first project observations — instrument limits

The bounded current handoff is `/tmp/s122-d7-first-observation-handoff.md`,
covering candidate package98436c9 plus local changes, Cranelisp dc78ddbe and
Magic1dc2b246 plus their observed dirty trees. The independent permanent CLI
set reports6 PASS/8 intended RED in
`/tmp/s122-d7-candidate-cli-observed-red-v3.log`; the earlier5/5 result covers
only the original narrower fixtures. The observed failures and five independent
review findings form one current correction basket, already with dev.

Full corpus discovery observes820 Cranelisp and748 Magic documents; both
validation runs exit1. Reference-finding counts are instrument-invalid as debt
measurements: ordinary code/currency spans such as `self.impl_registry` and
`$5.25` are falsely classified as paths, alongside incompatible supported
section/shorthand interpretation. Mixed establishment counts also await a
corrected run: architecture confirms exact products/memories require their
exact establishing reference, not repetition of declared purpose; named classes
require name and purpose. The candidate's blanket purpose requirement
overconstrains exact products. Do not assign all raw establishment findings as
owner repair debt or adopt their counts as a baseline.

The permanent REDs additionally cover optional-package unverified reporting and
missing Gitlink structure, normalized finding identity, Python docstring
extraction, complete grouped text reporting and unreadable-input failure. The
real missing-link and named-target section-association controls remain
discriminating. These are corrections within the approved contract, not new
design or a new matrix. Old/new source identity mapping remains deferred until
parsing is sound; raw overlap numbers cannot authorize baseline migration.

No project adoption, reference/baseline exception, gate cutover, Magic write or
whole Phase5 acceptance follows from these observations. Detailed owner batches
and raw counts stay in the handoff rather than duplicated here. ACT0957 is
closed separately with its existing QA closure carrier; its transport evidence
does not accept D7. QA made records-only changes, with no new tests, source
edits, builds or gate.


## D7 corrected candidate — non-Markdown section boundary

Current candidate SHA256
`5d2306a26aeb3339255ca35d21395ceedbe5fc5b921a2b760b19984e45793a7a`
reports units12/12 and independent CLI19/19 PASS; prior observed/review defects
have recorded RED→GREEN. The owner-merged Cranelisp run now observes819
documents and6425 findings, exit1. These are current observations, not adoption
or baseline-exception approval; final605 mapping remains test-owned. Personal
notes and additional historical proposals are still pending.

QA examined the actual executable-path misassociation and the correction in
`check_documents.py`: only `.md` code-span targets now participate in implicit
`§` association. This prevents the reported nontext executable path from being
opened as section content, but is narrower than the published generic contract.
CONSUMING permits explicit non-Markdown document products and configured extra
suffixes, and applies section checks to live reference inputs without a
Markdown-only target restriction. Magic's actual declaration includes `.mmd`
and `.cairn`; this is not a request to recognize arbitrary binaries or invent
a new document language. No actual bad selector in those products is claimed.
Explicit Markdown-link fragment checks still use the general resolver; the
omission is specifically code-span/§ association for configured document targets.

One bounded missing acceptance observation is justified: a configured non-
Markdown text document using the already supported heading grammar, with a
valid section control and missing-section negative; retain the existing
nontext executable existence-only control. This distinguishes configured
document eligibility from arbitrary file existence without a new parser
framework/matrix. Root receives the material test need for coordination; QA
does not write/run it during test's reservation. Preserve the executable fix
and assess the exact declared-document boundary; no broad review cycle or
automatic invalidation of unrelated source-identity mapping follows.

ACT0957 remains closed at its existing closure carrier. This D7 assessment
does not accept the candidate, adopt a project declaration, enroll debt or
close Phase5. No source/tests/builds were changed by QA.


## D7 final mapping and bounded correction disposition

QA read `/tmp/s122-d7-final-parity-and-mapping-handoff.md` against current
CONSUMING. Exact605-entry reconciliation is complete:507 entries map to506
current normalized identities,69 are demonstrated repairs and29 have explained
old-only differences; zero entries are unexplained. Same-input670-document
comparison maps945 of991 legacy unique findings, with46 explained differences.
The646 candidate-only source identities remain unsuppressed new discovery.
These figures establish traceable parity/mapping, not permission to enroll
any debt; normalization merges are explicit. Mapping need not restart merely
because independent section/establishment conditions remain open.

The final observation has819 Cranelisp documents/6379 grouped findings and748
Magic documents/2346 grouped findings, both exit1, with exact artifacts and
comparability limits in the handoff. Cranelisp's280 establishment observations
include271 undeclared products and nine known relative-establishment false
findings; they are not280 accepted owner defects. No adoption/exception has
occurred. Personal NOTES and additional historical proposals remain pending.

The settled correction basket has two instrument defects and one authority-
alignment repair. Non-Markdown section checking remains the already-allocated
defect. Directory-bearing relative establishment links must resolve beside
the governing memory consistently with reference resolution; the existing
observed fixture suffices. Neither requires a new project-specific exception.

The ACT-NNNN filename-template case is not yet supported generic-placeholder
authority: CONSUMING promises explicitly classified proposed/future references
and excludes fenced examples, but does not infer template status from `NNNN`
or a project-specific naming pattern. Root CLAUDE's prose describes the
*current* naming convention, so labelling that convention future/proposed would
misstate it. The smallest truthful repair is for its sprint owner to present
the filename pattern as an explicitly labelled fenced example, using the
existing generic exclusion. Test should align that fixture to the supported
example grammar and retain its neighboring real missing-link control. Do not
add an ACT-specific exception/regex or silently generalize placeholder syntax.
This narrows the handoff's blanket classification of all three REDs as checker
defects; the current21-case18-PASS/3-RED result is preserved as observation.

Root received this single settled basket for dev/test/owner coordination.
The completed mapping is adequate for explicit later migration decisions,
subject to these disclosed instrument limits; it does not authorize blanket
baseline migration, project adoption or Phase5 acceptance. No source/test edits,
builds or broad review cycle were performed by QA.


## D7 attributed parity correction evidence

Candidate30692e8a delivers the two attributed fixes. Package units14/14 PASS
after the two intended REDs are recorded in
`/tmp/s122-d7-package-units-parity-result-98436c9.log`; unchanged independent
non-Markdown-section and relative-establishment CLI cases pass2/2 in
`/tmp/s122-d7-candidate-cli-parity-focused-result-dc78ddbe.log`. QA read the
results and bounded source changes: section association admits configured or
discovered document targets while retaining the executable exclusion; relative
establishment uses the context of the governing memory. No additional
independent review cycle is allocated. The final focused handoff follows.

The completed605 mapping remains credited as traceable reconciliation, with
zero unexplained old-only identities; none of its entries or the646 new source
identities is automatically approved as debt. Owner document work, adoption
and pending historical decisions remain separate. No broad
corpus repeat, new matrix or source/build work was performed by QA.


Independent CLI evidence is now **21/21 PASS** against candidate SHA256
`30692e8ae59a87ee876a9e3b1092d9184f4086e3e5aa023fb0c70c443e037c45`
in
`/tmp/s122-d7-candidate-cli-final-green-30692e8a.log`.
The filename fixture now represents the root's explicitly labelled fenced
example and retains a real missing-link negative control; this was an
authoring/fixture alignment, not a new generic placeholder exception.

The affected owner-merged observation covered 819 documents and reported
6,369 findings, including 272 establishment findings
(exit 1, 44.36s). Of the nine previously grouped relative-establishment
observations, eight disappeared through the contextual-resolution correction;
one was an actual owner navigation defect. The test owner repaired
`repl/CLAUDE.md` to link directly to `repl/demos/CLAUDE.md` using a
relative link. Its targeted candidate
classification now reports the direct token present and zero relevant findings
in `/tmp/s122-d7-repl-demos-establishment-green-30692e8a.log`. This settles all
nine allocated observations without claiming that all nine were parser defects.
The affected full observation predates that final owner-link repair and is not
silently reduced or presented as a subsequent clean run.

**Focused adequacy:** the attributed checker corrections, filename-example
alignment and affected establishment observations are adequately evidenced.
The 605-entry mapping retains its stated 507 mapped entries (506 identities),
69 repairs, 29 explained old-only entries and zero unexplained disposition;
646 newly discovered source identities remain unsuppressed. These bounded
conclusions permit continued owner-debt repair and explicit migration/adoption
work, not adoption itself, baseline exceptions, resolution of pending
historical proposals, or whole-Phase5 acceptance. No further
review cycle, repeated mapping/Magic/compiler/transport run or new matrix is
required by this correction basket.


User decision on 2026-09-11 supersedes the earlier pending personal-notes proposal:
retain `NOTES.md` locally, ignored and removed from the Git index; do not check
it in or delete it yet. Root preserves the exact bytes (SHA256
`8f458edc7f522285b06a2ea2987aa40590c771b86cd1f56a1915d39e2ac2ced8`).
This is local ignored retention, not a standing-document exemption. Earlier
candidate observations above remain historical; additional historical-class
proposals remain pending. This records the user decision without an evidence
rerun.


## D7 project gate cutover allocation

The user's current direction is implementation/integration first, exceptions
second. The shared candidate and completed mapping are adequate to proceed with
project wiring. Preserve raw findings and nonzero failure; no clean-corpus
expectation, baseline suppression or exception approval follows.

The test owner replaces the legacy invocation in `tests/citation_drift.rs` with
shared CLI/project configuration wiring and retires the old executable. Reuse
the 21 passing independent CLI cases for parser semantics. The smallest changed
wiring allocation is:

- Exercise the actual new invocation helper on a temporary valid project and
  the same project with one planted stale source symbol; require clean exit 0
  versus exit 1 with that finding, not merely any process error. Missing tool,
  interpreter or invalid configuration must fail loudly rather than skip.
- Verify project discovery includes scheduling/host/standing-review surfaces,
  records the foreign package boundary, and classifies dated review records by
  the approved history policy. Reuse existing corpus membership assertions;
  historical discovery is no longer equivalent to excluding the file entirely.
- Run the actual project gate with its checked-in configuration and no baseline.
  Preserve its raw findings and exit status. Current debt means this gate may
  remain RED; do not rewrite its oracle to accept arbitrary exit 1 as cleanliness.

Do not port the obsolete baseline-regeneration/header preservation test or
legacy lifecycle exemption as current policy. Shared CLI fixtures already cover
rule semantics; project class decisions remain in the approved declaration.
No second parser matrix or broad review loop is allocated.

[Reconciliation evidence](s122-document-checker-reconciliation/README.md)
preserves the exact legacy baseline bytes and all 605 mapping entries in order.
QA verified that each mapping entry matches its original baseline entry. These
are historical data, never shared-tool suppression inputs. The test owner may
retire the old active baseline path with the executable once this carrier is
present. Remaining owner repairs and any specifically proposed exceptions are
subsequent work; pending historical proposals and whole Phase5 remain open.

## D7 integrated project gate — adequacy and remaining conformance

Delivered wiring meets the bounded cutover allocation. The project test invokes
shared CLI plus `standing-documents.toml` without a baseline. Final focused
nextest evidence is two passing controls (sound/planted source symbol through
the actual invocation helper; discovery/package boundary), plus the actual
project conformance gate RED, exit 1. The gate rejects invocation failure and
requires exit 0; known debt is not normalized into success. Evidence:
`/tmp/s122-d7-project-integration-final-nextest.log` (SHA256 prefix `fa00098c`).

The observation reports 820 documents, 6,022 unsuppressed findings at 7,714
locations, historical182/proposed348/unverified0. Required scheduling,
Claude/Copilot, standing and dated review, configuration and reconciliation
paths are present; no foreign package documents are traversed. This is a specific
integration observation, not a clean corpus or a repair comparison against prior
runs with different inputs. Candidate SHA256 is unchanged:
`30692e8ae59a87ee876a9e3b1092d9184f4086e3e5aa023fb0c70c443e037c45`.

QA read the invocation and declaration. Existing sprint/review/architecture
history policies are retained; deferred historical exclusions are not silently
granted. Other classes named historical remain live by default. Local ignored
notes have no standing-document exemption. Review class establishment remains
visible for its owner to repair. The old executable and active baseline are
retired; exact legacy bytes and all 605 ordered mapping entries remain in the
reconciliation carrier and are never passed to the shared checker.

**Disposition:** integration and allocated wiring evidence are adequate;
project document conformance is explicitly RED. Continue owner repairs and
specific exception decisions in the user's requested order. No new parser
matrix, review cycle or whole-Phase5 acceptance follows. QA ran no builds/tests.


## Final integration failures — classification and allocation

QA read, and did not re-execute, the default-suite logs (5,963 pass / 6 fail
at classification; 5,968 pass / 1 fail / 1 skip after the corrections below,
the sole failure being document conformance), the agent feature-lane logs
(81/81; agent module tier with its imports and prelude consumers 175/175), the
agent fixture review, the harvest correction review and the agent lookup
correction review. Uncommitted product changes are confined to `src/agent/`
and `src/repl/commands.rs` and cannot reach CLIF emission.

| Failure | Class and attribution | Owner and bounded delta |
|---|---|---|
| `golden_clif_w0b_{ctor_def,synth_accessor,multisig_variant,expr_disposition3}` | Maintenance check: stale instrument and stale golden; no compiler defect. Actual output differs from each golden only by whole missing constructor-instance frames. `tests/golden_clif_w0b.rs` extracts frame names with `\S+`, which cannot match the canonical whitespace-bearing instance names; this third extraction site was not among the two corrected earlier in S122. Control: `tests/fixtures/clif_baseline/golden/f1_machinery.clif`, captured by a corrected extractor, holds the `IO.Pure` Int instance under its canonical name with an instruction body identical to the w0b golden's `primitives/IO.Pure$Int` frame. | `test`: adopt the line-anchored extraction already used by `tests/ownership_fences.rs` and `tests/scripts/clif_golden.sh`, retaining the duplicate-frame and zero-frame errors; then re-baseline 01–04 scoped to the canonical rename (frame header, end marker, `function %` line and sort position). Any instruction, signature or frame-count delta in 01–04 refutes this attribution: stop and return to `qa`. Bring MANIFEST focus-frame names, line counts and the attributed re-baseline entry current. |
| `golden_clif_w0b_macro_clause` | As above, plus one attributed emission change. The dropped frames are the `IO.Pure` and `SList.SCons` instances. `twice$macro-clause$0` additionally gains one `call fn5(v1)` (`colocated u0:40`, void `(i64)`) before `return`, with its `sig8`, `fn5` and two alias lines: the clause parameter release of the delivered Q4 all-Owned clause convention ([macro-turn ownership](../../design/int/macro-turn-ownership.md)). `u0:40` is the glue the golden's `SCons` frame already calls on its `Sexp` field. | `test`, same change: re-baseline 05 with the delta attributed to the Q4 clause-preparation seam. Admissible delta is the canonical renames plus exactly that release-family addition in the clause frame, with `user::main` unchanged. Anything else returns to `qa`. |
| `citation_drift::project_documents_conform_to_the_checked_in_declaration` | Maintenance check: known unsuppressed debt; no new finding. The log's 2,519 finding identities equal the last recorded stable-tree report exactly (none added, none removed; 3,088 locations; 182 historical). One document was added and carries no finding. | Remains RED. Acceptance depends on the user's specific disposition of the remaining debt at the S122 acceptance gate: owner repair or a named exception. No baseline or blanket exception is implied. |
| `agent::set_doc_non_function_target_e2e_refused_not_recorded_neg` (feature lane) | Corrected; evidence adequate (see the lookup-correction adequacy below). Product defect, `src/agent/pull.rs::apply_docstring_edit`; the fixture conforms. `repl/spec` §17.15.4 face 2 names an ADT constructor as a locally resolving non-function whose refusal must make clear that only a function's docstring is recorded; face 1 (`no such definition`) is reserved for a name with no local definition. With the bare-constructor fixture the run reaches the refusal and prints `no such definition: Red`. No success line appears and `/doc Red` shows no docstring, so the honesty half holds and only the stated reason is wrong. Mechanism, read at its seam and not executed: a sum constructor is stored under `member_key` (`Color.Red`, `adt_build.rs`), its bare spelling is a name candidate only, and the edit looks the target up with the binding-only `SymbolTable::get`. Executed control: the module unit `set_doc_non_userfn_refused_not_recorded` installs a bare-keyed extern and receives the face-2 message (134/134). Refuter: a current-module product constructor or type name, both bare-keyed, also answering `no such definition`. Coverage attribution: the unit's only non-function variant was bare-keyed, and the e2e could not execute from S115 until this fixture repair in a lane outside the default suite. | `dev` (`src/`): a target whose spelling has a current-module terminal candidate that is not a plain function body takes the face-2 refusal; an import-only or undefined name keeps face 1 (`set_doc_missing_target_e2e_refused_no_false_recorded_neg` is the standing negative control). The existing e2e is the observed-RED reproduction. The correction carries one module unit installing a sum constructor through the ADT funnel, observed RED before the fix, asserting the face-2 message and an unset docstring. No further e2e and no public-API change is expected; `name_candidates` is already public. `test`: add the `// defect:` line (`class=resolver-mirror locus=src/agent/pull.rs::apply_docstring_edit found=S122 owner=/dev`). |
| `agent::harvest_in_scope_shows_name_sig_docstring`, `agent::harvest_budget_degrades_grain_not_truncates_neg` (feature lane) | Corrected; evidence adequate. The seam observation separated the rivals (names and prelude-owned control passed, the re-export leg failed), the feeder-3 correction resolves each name through its public candidate to the defining module, and the discriminating unit went RED to GREEN for that reason. Both e2e pass and observe the primitive classification and docstring, which require the resolved home. Independent review: no blocking finding. | `dev`: formatting and the one-line rustdoc repair (review F2); mechanical, no re-review. Review A1–A3 are not required: the home-module half of the fix is observed by the e2e, and no detector is warranted for an unknown ambiguous prelude name. |

Residual intake, classified. None gates the corrected harvest seam.

| Intake | Class | Allocation |
|---|---|---|
| Explicit-import in-scope feeder reads `all_symbols()` (bindings only) | Observed and corrected; evidence adequate (see the lookup-correction adequacy below). At intake: suspected defect, unobserved. §17.18.1 requires explicitly imported symbols in the block; the mechanism matches the one observed in feeder 3; the harvest e2e covers own definitions and the implicit prelude only, so the provenance twin is missing. | `test`: one explicit-import twin of `harvest_in_scope_shows_name_sig_docstring` with the same assertions. RED is the reproduction and goes to `dev` (`src/`) with a module unit on the same candidate path; GREEN refutes the intake and the twin stays as coverage. |
| Context exports arm uses `public_symbols()` while `/exports` resolves candidates and filters internals | Same consumer family; advisory model context; no requirement fixes the grain and no wrong outcome is reproduced. | No observation now. `design/int/agent.md` §5.2 records the divergence as an open design question. `design` (int) decides convergence on the `/exports` producer; if adopted, one twin cell (context export names equal `/exports`) accompanies it. |
| Pin narrower than "full current-module source" (types, traits, impls, file-loaded definitions absent) | Authority and realization disagree; not a defect until the owner chooses which moves. | `design/int/agent.md` §5.2 now states the delivered admission rule and records the narrower pin as an open design question; `repl/spec/17-embedded-agent.md` §17.8.1 describes disclosure of the full current-module source. The decision remains `design` (int)'s, with `spec` if the disclosure wording moves, raised through `sprint`; `qa` allocates after it. |
| `prelude_implicit_names` holds the prelude table guard across a second `symbol_tables` read | Latent safety residual in a shape FIXME 0666 already retired in harvest; present before this change and not widened; reached by `/imports` and every context dump. | `dev` (`src/`): collect-then-resolve, the constructive repair. No detector or stress cell. Delivered for this function; review found it correct. |
| `src/CLAUDE.md` and `format.rs` said `/doc` follows the import chain through the identity helper `resolve_entry_for_display`, since removed (final section); stale `defined_symbols()` mentions in `design/int/agent.md` and `harvest.rs` comments | Stale records. `/doc` on a re-exported primitive and on a constructor is observed working. | The `src/CLAUDE.md` and `format.rs` `/doc` claims are repaired with the `/imports` guard correction, and review confirmed the new text against source. The `defined_symbols()` mentions are gone: a search of `design/int/agent.md` and `src/agent/` finds none. No evidence. |

- Review A1 and A2 are mechanical comment repairs with root. A3 is accepted:
  the cap unit guards the Haiku ceiling only and is not a general budget guard;
  ACT-0960 stays deferred.
- Review R1: pin admission of `Overloaded` and `Macro` affects advisory context
  only and has no reproduced wrong outcome. No observation is allocated.
  `design/int/agent.md` §5.2 block 1 now states the admission rule as callables,
  overload groups and macros that are not internal listing entries. Read at its
  seam, `harvest.rs::push_module_full_source` admits exactly those declaration
  kinds with the same internal-listing filter, so the restatement excludes no
  class the pin admits and no observation is reconsidered.
- The agent feature lane is outside the default suite, so default-suite green
  does not cover it. S122 agent acceptance needs the lane green, or each RED
  traced to an owned filing. The set-doc and harvest defects both entered as
  unmigrated binding-only reads in `src/agent/` and stayed unseen because
  nothing executed the lane; running it at each Phase-5 checkpoint is the
  control, not a per-site detector.

### Agent lookup corrections — adequacy

The bounded agent corrections are adequate against the allocation above.

- **Set-doc refusal.** The sum-constructor unit, installed through the ADT
  funnel, failed before the fix with `no such definition: Red` in place of the
  function-only reason; the e2e failed at the same assertion. Both pass after.
  The bare-keyed, import-only and undefined-name controls passed on both sides.
- **Explicit-import feeder.** The twin passed its import-resolution setup
  assertion and failed at the first `add-i64` assertion with an empty block
  line; the module unit failed on the absent defining-module entry. Both pass
  after. The implicit-prelude original passed on both sides, which separates
  this feeder from feeder 3.
- **Review.** Fresh `review` (`src/`), static: no blocking finding; the three
  corrections match their rows. QA did not see an independent re-run; the logs
  are root's.
- **Limit.** The import-only set-doc control detects a cross-table resolve and
  any write to the imported function. It does not detect a candidate pick that
  ignores the source module, which still answers face 1. No requirement rests
  on that distinction, so no cell is added.

Review findings, classified. None gates the agent lane.

| Finding | Class | Allocation |
|---|---|---|
| R1: the explicit-import twin is a reproduction without a `// defect:` line | Maintenance check (defect-corpus notation). Class token `enumeration-miss`: the in-scope enumeration omitted the explicit-import candidate source. It is not `resolver-mirror`; no name was resolved on a divergent path. | Root, mechanical, no test run or re-review: `// defect: class=enumeration-miss locus=src/agent/harvest.rs::push_in_scope_block found=S122 owner=/dev`, directly above the twin's `#[cfg(feature = "agent")]`. |
| A1: a plain function under a second same-module spelling | No producer found; recording on the canonical function satisfies the honesty contract. | None. Refusing on a spelling mismatch would have a lower carrier strengthen §17.15.4. |
| A2: `handle_imports` holds the current-module table guard across `resolve_to_definition` and `prelude_implicit_names()` | Corrected; evidence adequate (see the `/imports` guard adequacy below). At intake: latent safety residual, same family as the `prelude_implicit_names` row; no failure reproduced; slash-command path only. | Delivered by `dev` (`src/`): collect-then-resolve. No detector, stress cell or action. |
| A3: the units report overstates the import-only control | Report wording; the test is unchanged. | Root integrates the wording QA supplied with this judgment; the limit is stated above. |
| A4: one spelling with two foreign sources renders once | Advisory model context; no requirement fixes the grain. | None. |
| A5: the resolve, internal-listing and special-form filter sequence repeats at four sites | Corrected with A2. The resolve and internal-listing pair has one site, `listable_definition`, with three consumers; special-form exclusion stays with the two callers that apply it, because `/imports` categories never did. | Delivered with A2. |
| A6: `design/int/agent.md` §23.1 feeder list contradicted the delivered feeder 2 | Stale record under the stale-records row. Repaired: §23.1 feeder 2 now states name candidates from another source module, resolved with `resolve_to_definition` and filtered as feeder 1, which matches `explicit_import_sources` and `listable_definition` as read. | Closed by `design` (int). No evidence. |
| A7: typographic apostrophe in the `push_in_scope_block` rustdoc | Nit. | Root, mechanical. |

### `/imports` guard correction — adequacy

The A2 and A5 correction is adequate against its allocation.

- **Guard lifetime.** Read at its seam: `explicit_import_sources` returns owned
  pairs and releases its table guard; `handle_imports` holds no guard at any
  `listable_definition` call; the root-table guard closes before
  `prelude_implicit_names()`. The property is constructive at these sites.
  Nothing executes the lock-order hazard and none was reproduced, so no
  red-to-green exists or is owed.
- **Behaviour preservation.** Root's logs: the twelve `/imports` e2e pass
  (12/12), the agent lane passes with both `harvest_in_scope_*` cells (81/81),
  and the module tier passes with the new own-definition exclusion unit
  (176/176, one more than the prior 175). QA read the logs and did not re-run
  them; no format or lint log was supplied.
- **Review.** Fresh `review` (`src/`), static: no blocking or required finding.
  ADV-1 (`resolve_entry_for_display` was an identity step with live call sites
  and stale "chain" narration in `src/eval.rs`, `src/repl/format_type.rs` and
  `src/session_v4.rs`) is delivered and judged in the final section.
  ADV-2 (the unit's positive leg is loose) needs no change: the filtered-view
  and negative assertions discriminate the rule the helper single-sources.
- **Limit.** The family is not closed by construction: a new caller can still
  hold a table guard across `listable_definition`. The rustdoc states the
  obligation.
- **`/exports` (ADV-3) — delivered, adequate.** `handle_exports` collects the
  public candidates as owned `(spelling, source)` pairs in one statement, so
  the table guard drops before the loop calls `resolve_to_definition`. The
  loop order and the internal filter, keyed on the exposed spelling, are
  unchanged. The property is constructive at this site, read and not executed.
  The five allocated preservation cells pass in root's default-suite run:
  `exports_lists_public_symbols_after_defn`,
  `exports_neg_nonexistent_module_not_found`, `exports_no_arg_shows_usage`,
  `exports_show_ctor_once_canonical` and
  `layout_cross_command_list_exports_byte_identical`. No separate review was
  requested: the hunk is the allocated shape and carries no new material risk.
  Folding into `listable_definition` still waits on `design` (int) choosing
  the filter key. ADV-1 is delivered; the final section judges it, and it gates
  nothing here.
- **Format and lint.** Root's clippy run exits 0, and its warnings and the
  `cargo fmt --check` differences all sit on lines this basket did not touch.

The Haiku 2/2 observation stands and ACT-0960 stays deferred. Document
conformance remains RED at 2,519 findings over 3,088 locations with 182
historical exclusions, the counts recorded above; QA compared counts, not
identities, for this run. Whole Phase-5 acceptance remains open.

## Identity-helper removal and the qualified-display lead

### `resolve_entry_for_display` removal (ADV-1) — delivered, adequate

Class: maintenance of a private surface; no condition is added, changed or
retired. At `HEAD` the helper returned `(entry.clone(), current_module.clone())`,
so each caller already held the tuple it now uses. `arch` and `design` (int)
confirm that no guarantee rests on it.

- **Plausible wrong outcome.** A caller substitutes the wrong variable for the
  forwarded tuple, so a declaration prints under the wrong home or with the
  wrong entry. A type mismatch cannot compile; a same-typed swap can.
- **Diff, read by QA.** The helper and its seven call sites are gone; a search
  under `src/`, `crates/`, `tests/` and `design/arch/` is empty. Each site
  binds the pair its unchanged producer returns: `eval.rs` renames the tuple
  slot to `fq_module`; `handle_sig`, `handle_doc` and `handle_info` destructure
  `resolve_entry_arg`; the two `format.rs` sites and `search.rs` take
  `lookup_with_prelude_fallback*` directly. No hunk changes which lookup a
  caller uses, its arguments or its precedence. The remaining removal hunks
  are comments, plus two assertion-message strings in
  `tests/repl_introspection.rs` that assert nothing new.
- **Executed evidence, root's logs.** Every source and test edit predates the
  rebuilt binary and the logs. All nine allocated e2e cells
  (`repl_introspection` ×5, `repl_mod_devloop` ×2, `search` ×2) and the four
  `bare_primitive_value_path_tests` units pass in the full run: 5,970 run,
  5,969 pass, 1 skip, and the single RED is the document-conformance gate
  already recorded above. The targeted lane passes 267/267. No test was added:
  an output-preserving deletion has no red to observe.
- **Format and lint.** Clippy exits 0 and none of its warnings sits on a line
  the removal touched. `cargo fmt --check` reports the locations known before
  the change; `src/repl/mod.rs` moves from 1015 to 1010 by line shift only.
- **Documents.** Root's checker comparison: 710 documents, 2,284 findings,
  160 removed and none introduced against the cohort baseline. QA took the
  counts from root and did not re-derive identities.
- **Independent review: not triggered.** The three waiver conditions hold:
  the search is empty, every non-comment source hunk is a tuple pass-through,
  and the cells pass.
- **Limits.** The rewritten comments and `src/CLAUDE.md` sentences are read,
  not executed; the checker validates their references only. The stale
  `Import`-edge narration `dev` listed elsewhere in `src/` and other crates is
  outside this change and stays with those surfaces' next `dev` pass. This
  judgment covers the helper removal only; whole Phase-5 acceptance remains
  open.

### Qualified re-export spelling at the prompt — defect, corrected

Class: acceptance evidence for `repl/spec/03-slash-commands.md` §3.8,
`spec/08-modules.md` §8.4.6 and `repl/spec/17-embedded-agent.md` §17.1, which
`spec` reads as settling the case without a ruling. It is independent of the
helper removal above.

- **Defect.** With the project prelude `(export [primitives [*]])`, the prompt
  line `prelude/add-i64` printed
  `:(Fn [primitives/Int primitives/Int] primitives/Int) <closure>` while
  `/sig prelude/add-i64` printed the `primitives/add-i64 ; primitive - Add`
  line. Binary surface, `owner=/dev`, class `resolver-mirror`.
- **Cell.**
  `repl_introspection::qualified_reexport_bare_display_parity_with_sig_neg_not_closure`:
  the two primary lines are equal, name `primitives/add-i64`, and the first is
  not `<closure>`. In-cell control: `primitives/add-i64` against its `/sig`
  form. The bare control is
  `bare_primitive_parallel_paths_converge_on_same_attribution`.
- **Observed.** RED at the `<closure>` assertion with the control leg passing
  (`.local/s122-display-red-followup.log`), so qualified introspection was not
  broken generally; GREEN after the correction
  (`.local/s122-display-final-green.log`).
- **Mechanism.** Not observed at its seam. The control localises the fault to
  the re-exporting qualifier; `design` (int) reads it as the same cause as the
  listing defects below — several resolvers for one displayed identity — and
  one correction closed both. The cell carries the shared seam tag.
- **Unallocated.** A re-exporting qualifier that still exposes several
  terminals; see the listing rule's "Not allocated".

### In-scope candidate display — listing rule

Class: acceptance evidence for the user ruling recorded in
[SPRINT](../../sprints/SPRINT.md) §"In-scope introspection — current ruling",
as `spec` records it in `repl/spec/04-self-documentation.md` §4.1.11 and
`repl/spec/03-slash-commands.md` §3.8. Delivered and observed; the listing
rule's requirement rows carry the cells below as their bands.

**Rule as evidence reads it.** A bare spelling lists every in-scope canonical
candidate, whatever the candidates' types, with no warning or error at import
or at lookup. A use of the spelling resolves under `spec/08-modules.md`
§8.6.5 exactly as before, so a use the candidate set cannot decide is still
the existing use-site ambiguity error. Display compares no types; no equality
policy and no generic-equality cell exists for it. Conflicting imports stay
legal; the user defers that language question.

**Defect intake.** Root's corrected probe
(`.local/s122-b2-collision-observation.json`): with a prelude `foo` on `Int`
and a local `foo` on `Bool`, bare `foo` and `/sig foo` print only the local
declaration, while `(foo 1)` selects the prelude's. Under the ruling that omission is a
defect of the binary surface (`owner=/dev`, class `resolver-mirror`). Observed
once outside the suite and again in it; CD-1 is its permanent record. `design`
reads the cause as a tier-first single-answer lookup; not observed at its seam.

**Conditions.** Each cell is one isolated REPL session over monomorphic
primitive types, asserts by substring, and compares bare and `/sig` output as
unordered line sets. CD-4 and CD-7 are retired with the type-equality policy.

| Id | Condition | Plausible wrong outcome | Fixture and observation | Observed before the fix; all GREEN after |
|---|---|---|---|---|
| CD-1 | Local and implicit-prelude candidates both list, at bare lookup and `/sig` | One candidate shown by tier; the other omitted | Prelude `foo` on one primitive type, local `foo` on another; bare `foo` and `/sig foo` each carry a primary line for the prelude's `foo` and one for the local `foo`, each fully qualified and with its own type, and neither `unbound` nor `ambiguous`. In-cell control: a call whose argument selects the prelude candidate still evaluates | RED observed: listing, 1 of 2 lines, `prelude/foo` dropped. Control, parity and no-rejection legs passed |
| CD-2 | The same for two explicit imports — provenance twin of CD-1 | Two imports fall through to another tier or to `unbound` | `a/f` and `b/f` on different primitive types, both imported; same assertion over `a/f` and `b/f` | RED observed at the no-rejection leg: bare `f` answers the use-site `ambiguous bare name` error. Control passed; the `/sig` face was never reached |
| CD-3 | Identically typed candidates list the same way; only a use is ambiguous | The import line or the lookup warns or errors early; one candidate hidden; or listing relaxes the use and a call silently picks one | `a/f` and `b/f` both `(Fn [Int] Int)`. Lookup session: the import line, bare `f` and `/sig f` produce both primary lines and no `ambiguous`. Use session, same fixture plus `(f 1)`: the existing use-site ambiguity diagnostic, which also shows the fixture collides | RED observed at the no-rejection leg, bare session: the import turns are silent and bare `f` answers the use-site ambiguity error. The `/sig` session was never reached. Use session GREEN observed |
| CD-5 | One terminal reached by two import paths is one candidate: one line | Exposures listed instead of terminals, so a declaration prints twice | Import `a/f` directly and through a re-exporting module; bare `f` prints exactly one `a/f` line | GREEN observed, both legs; negative control for CD-2 |
| CD-6 | `/info` and `/doc` list every candidate too | A command keeps its own single-answer lookup | Over the CD-1 and CD-3 fixtures, `/info` and `/doc` of the bare name each name both canonical declarations and print no `ambiguous`. §4.1.11 adds no per-command format, so nothing else is asserted | RED observed, one cell per command and fixture. CD-1 fixture: `/info` names only the local declaration and `/doc` prints only the local docstring. CD-3 fixture: `/info` and `/doc` each answer `unknown symbol 'f'` |
| CD-8 | A candidate set holding a result-only-polymorphic nullary constructor still lists in full at bare lookup | The prompt gate describes only when every member describes, so one value-path member sends the whole turn to evaluation: the §8.6.5 use-site `ambiguous` error, or one candidate picked | `a/Empty`, a nullary constructor of a parameterised `a/Box`, and `b/Empty : (Fn [Int] Int)`, both imported; bare `Empty` names `a/Box` and `b/Empty` and prints neither `ambiguous` nor `unbound`. The constructor line's form (§1.5.1 or §4.1.2) is not asserted. Control, reused: `prelude_option_none_value_display_neg_definition_metadata` keeps the single-candidate §1.5.1 form | RED observed at the no-rejection leg: bare `Empty` answers the use-site `ambiguous bare name` error naming `a/Box.Empty` and `b/Empty`; the import turns registered, so the fixture is sound. The reused control passed in the same run |

**Observed.** Red-to-green per cell; no planted fault is added.

| Run | Log | Result |
|---|---|---|
| First eight cells | `.local/s122-display-red.log` | 2 pass, 6 fail; reused guards 142 pass (`.local/s122-display-controls-before.log`) |
| Ten cells, lead control first, one cell per command | `.local/s122-display-red-followup.log` | 2 pass (CD-5, CD-3 use), 8 fail, each for its allocated reason |
| CD-8 and its control | `.local/s122-display-edge-red.log` | 1 fail for the allocated reason, control pass |
| After the correction: module tier, [introspection](../repl_introspection.rs), facade rows, `spec_08_*` | `.local/s122-display-final-green.log` | 1131 of 1131; all eleven cells, the reused control and the `dev` seam units pass |
| Full suite | `.local/s122-display-final-default.log` | 5983 of 5984; the one RED is the document gate below |
| Agent lane, isolated target | `.local/s122-display-final-agent.log` | 81 of 81 |

- Every RED was a §4.1.11 or §3.8 violation on a fixture its control proves
  sound; none was a fixture or harness failure. All faces fell inside the one
  binary-surface pass `design` (int) records; no import-policy change
  followed.
- Faces, by provenance and surface: prelude-plus-local **omitted** a candidate
  (CD-1, CD-6 over that fixture); two distinct imported terminals made bare
  lookup **fall through to evaluation**, which correctly raised the §8.6.5
  use-site error, and made `/info` and `/doc` answer `unknown symbol` (CD-2,
  CD-3, CD-6, CD-8).
- Controls that discriminate: CD-5 leg A differs from CD-2 only in reaching
  one terminal instead of two, and listed; each red fixture's use still
  resolved the full candidate set. The introspection surfaces and use-site
  resolution answered one spelling differently — the `resolver-mirror` class,
  observed as behaviour. Which reader answered was `design`'s code reading;
  no cell names a function as the mechanism.
- The nine red cells, the lead included, carry
  `// defect: class=resolver-mirror locus=binary-introspection-lookup found=S122 owner=/dev`.
  The locus is the seam name and stays. `test` appends `fixed=S122/<sha>` and
  puts CD-8's comment in the past tense in one pass once the commit exists.
- Limits. The pre-fix `/sig` faces of CD-2 and CD-3 were never reached; the
  post-fix listing assertions force both line sets non-empty, so their parity
  now discriminates. Cells compare canonical names and unordered line sets,
  not order, wording or the constructor line's form.
- The full suite's one RED is
  `citation_drift::project_documents_conform_to_the_checked_in_declaration`:
  2,282 corpus findings under the D7 no-baseline adoption, none on a line this
  change touches. It is a maintenance check; its debt is D7's and it does not
  gate this acceptance.

**Reused, unchanged guards — no new cell.**

- Import registration and use-site selection: the §8.6.4–§8.6.5 matrix in
  [name shadowing](../spec_08_name_shadowing.rs), including
  `def_over_import_repl_rejected`, the `def_over_prelude_*` trio,
  `mode_parity_def_over_import_same_rejection_all_modes` and
  `reuse_by_reexport_same_terminal_dedups`. These must stay green; a change in
  any of them is a regression, because the ruling changes no language
  resolution.
- In [introspection](../repl_introspection.rs): single-candidate display
  (`sig_shows_type_signature`,
  `bare_primitive_parallel_paths_converge_on_same_attribution`), one
  declaration's overload arms (`display_overloaded_fn_shows_all_variants`),
  private qualified members (`private_fq_member_errors_not_displays_mode_uniform_neg`)
  and lookup leaving definition display intact
  (`bare_lookup_does_not_corrupt_info_and_source_definition_display`).

**Not allocated.**

- The lookup-shape × surface product is not enumerated e2e. The delivered
  interior is one candidate query that the prompt, `/sig`, `/info` and `/doc`
  consume (`design/int/int.md` §3.3), so the bare/`/sig` twins and CD-6
  pressure that single path. Per-surface resolution returning there reopens
  this allocation.
- Candidate classes other than functions get no cell of their own: each
  candidate prints by its existing class rule, which the reused guards cover
  one candidate at a time.
- Display order and exact wording: cells compare unordered line sets and
  canonical names only.
- A candidate set holding a zero-argument macro: a bare zero-argument macro
  reference is an expansion, a use that precedes lookup (REPL §4.1.6 and
  bare-symbol expansion, `spec/09-macros.md` §9.5). Use-site selection governs
  that turn; the listing rule does not. The
  prompt gate yielding that turn conforms. Which declaration the use then
  selects is `cranelisp_types::resolve_macro_head`'s language behaviour in
  every mode, outside the display surface; unobserved.
- Private qualified members at `/sig`, `/info` and `/doc`: refusal is required
  by `spec/08-modules.md` §8.7.3, and `/sig` prints what bare lookup prints
  (`repl/spec/03-slash-commands.md` §3.8). The commands
  and the prompt share one candidate query, so
  `private_fq_member_errors_not_displays_mode_uniform_neg` pressures that
  path; no command twin.
- `describe_symbol` had no requirement, design condition or production
  caller. `dev` deleted the chain with its two `collect_related` unit cells,
  and `test` dropped the name from
  `facade_pif_rows::row_42_read_side_accessor_methods_exist_on_compiler_session`,
  a source-presence maintenance check. No replacement cell.
  `rev3_describe_symbol_resolves_primitive_via_facade_method` observes `/info`
  behaviour and stays.
- A qualified spelling whose re-exporter exposes several terminals, the other
  name-taking commands, `/search` and the agent's in-scope checks are outside
  the bare-name rule as ruled; no cell until `spec` text or sprint scope
  covers them.
- Accepted residual, as `design/int/int.md` §3.3 records it: the legacy
  tier-first helper still answers three membership readers and two display
  readers — `/search`'s exact in-scope hit and the sole-candidate
  nullary-constructor value display — so single provenance holds of the
  listing, `/sig`, `/info` and `/doc` only. Asserted with a named falsifier
  (`/search foo` over the CD-1 fixture), not executed; no cell.
- Import conflict policy is deferred to ACT-0961; nothing here observes it.

**Module evidence (`dev`, binary surface).** Unit cases at the candidate-query
seam: none, one and several candidates; identically typed candidates both
returned; a lookup result is not a defining turn; the qualified re-export
spelling resolves through the same query as its `/sig` form; and
`eval::tests::polymorphic_nullary_ctor_lists_among_several_candidates`, which
runs the sole-candidate and several-candidate dispositions over one fixture.
The terminal-deduplication unit pins int's reliance on the table's canonical
keying only; CD-5 carries the distinct-path evidence.

**Adequacy.** The class stands: nine acceptance cells red-to-green for the
stated reason, two controls green on both sides, reused guards green, and an
independent finding-scoped review with no surviving blocking or required
finding (R1–R3, A1–A4 closed). Format shows no drift in changed hunks.
The remaining lanes are observed, not assumed: the agent lane through its
launcher, because `src/agent/harvest.rs` reads the same lookup, 81 of 81
(`.local/s122-display-final-agent.log`); clippy on the binary surface with no
error, no dead-code or unused lint after the deletion and no lint inside a
changed hunk (`.local/s122-display-final-clippy.log`; no pre-change count was
recorded, so the comparison is by location); and the `public-api.txt` set
unchanged, its drift guard green in the full run. Evidence is adequate for the
listing rule and the qualified lead.

## Reuse of an IO value — defect allocation

Authority: the user's ruling of 2026-09-21, recorded at the
[reuse checkpoint](../../sprints/SPRINT.md) and scribed in `spec/10-io.md`
§10.8.1: IO values are reusable descriptions of work; every forcing is
interpreted as the first is; refusing a reused `Pure` is a compiler defect;
memory safety is preserved while ownership is corrected, and removing the guard
alone is not a fix. The proposed correction is `arch`'s retain-on-force rule in
`design/arch/total-concreteness.md` §3.4 — a published `Pure` node is never
written, a force of an `Owned(glue)` payload mints the consumer's reference, and
node teardown discharges the node's own reference under both dispositions.
`design` (intrinsics) owns its interior. This section allocates evidence for the
`Pure` correction only. That correction is private to intrinsics; the only user
gate in this area is a public-API proposal, which it does not make.

This section supersedes the expected-error observable of cell 1 in the
[S121 shared-`Pure` allocation](s121-test-plan.md#31-r1--shared-pure-double-force).

**Observed.** Root's single `--run` observations
(`.local/s122-r1-root-observation-result.md`) and the authored pair, red and
green for the allocated reason (`.local/s122-io-reuse-test-log.txt`):

| Source | Differs from control by | Observed |
|---|---|---|
| `(let [p (Pure 7)] (bind p (fn [a] (Pure a))))` — control | — | exit 7 |
| `(let [p (Pure 7)] (bind p (fn [a] p)))` — reuse | the continuation returns `p` | exit 1, `runtime panic: Pure node forced more than once` |

The control discriminates the mechanism: a second force of one node. The
message has one emission site, `io.rs::force_pure_node`. The defect entered at
the S121 once-only force ruling, which no requirement carried; the claim
realizes that ruling as designed. Class `wrong-reject`.

**Not observed, and not inferred from the above.** Concurrent reuse (the two
`race` probes returned 7 and do not show a second lane forced the node); reuse
of a `Launch` or `EffectPoll` node. `Effect` reuse is observed and is separate
intake — see [the probes](#effect-and-launch-probes--diagnostic-separate-from-the-pure-defect).

### Conditions

| ID | Class | Condition | Plausible wrong outcome | Layer, owner | State |
|---|---|---|---|---|---|
| IOR-1 | acceptance | One `Pure` value forced twice in sequence yields its value each time: the reuse source exits 7. | refusal (today); a second force yielding a stale or zero value | e2e `--run`, `test`: `tests/spec_10_io.rs::run_mode_reused_pure_yields_its_value_on_each_force` | green since the retain-on-force correction; observed RED on the refusal first |
| IOR-C | acceptance control | The control source exits 7 before and after. | a harness, import or exit-path fault posing as the defect or its fix | `tests/spec_10_io.rs::run_mode_fresh_pure_per_force_yields_its_value_control` | green |
| IOR-2 | safety fence | The reuse shape with a `String` payload: both forced values contribute to the exit code, and the marginal allocation balance against the fresh-node twin is exact, with `CRANELISP_RC_DEC_CHECK` armed. | a force that still moves the payload on some path — the claim deleted without the retain, or a move kept for a fresh or uniquely-held node — so the payload is released twice or read after release. IOR-1 stays green under all of these: a scalar has no second owner | e2e, `test`, the `platform_pure_string_*` marginal-pair harness in `tests/spec_10_io.rs`; subject and control differ only in `p` versus a second fresh `Pure` | `tests/spec_10_io.rs::platform_pure_string_reused_node_yields_payload_to_each_force_and_balances`: green, exits 17 and 17, marginal 0, seam checks armed. The balance leg read −2 until the [IOR-5](#scope-result-bind-leak--intake) correction and flipped with it unchanged, as predicted: no second cause |
| IOR-3 | — | One heap `Pure` forced on two completing `par` lanes. | two lanes both take one payload | not written — see below | discharged by construction, conditionally |
| IOR-4 | acceptance | A reused `Effect` value performs its effect on each use, in order (§10.8.1 covers every IO value). | the effect runs once; the second force faults or reads released memory | e2e `--run`, `test`: `tests/spec_10_io.rs::run_mode_reused_effect_performs_its_effect_on_each_force`, control `run_mode_fresh_effect_per_force_performs_its_effect_control` — [cell](#ior-4--permanent-regression-cell) | green with the approved `Effect` correction; observed RED on the dispatch fault first |
| IOR-5 | safety fence | A `bind` node returned from a scope that owns a heap binding is released with its tree: the `let`-bound forced platform `Pure` balances against its inline twin. | the scope's result keeps one reference nothing releases, stranding the whole IO tree | e2e marginal pair, `test` — [intake below](#scope-result-bind-leak--intake); correction evidence [here](#ior-5-correction--evidence-delta) | both cells green at marginal 0 on the corrected build; observed RED first at +4 (trigger) and +3 (mechanism control) |
| IOR-6 | safety fence | An `Effect` node discarded unforced releases its thunk and the thunk's captures. | the node-owned thunk is never destroyed, or is destroyed by a force and again at teardown | e2e marginal pair, `test` — [fence below](#effect-correction--lifetime-and-reuse-fence) | green at marginal 0 on the corrected build; proven to detect by the one-off `Effect`-row mutant (+1) — [IOR-6 sentinel](#ior-6--capture-release-sentinel) |

**Why IOR-2 is an e2e cell and not only `dev`'s unit.** The retain is a source
property, not a structural one: a force that omits `rc_inc`, or keeps the move
behind a freshness or count test, compiles and passes IOR-1 and every
single-force program. `dev`'s unit sees it at the seam, but is written from the
implementer's own model of which forces alias; IOR-2 reaches the seam through
the compiler's real aliasing of a `let`-bound IO value. It costs one cell and its
twin on an existing harness. Its detection does not rest on its own pre-fix red
(that red is the refusal): it rests on the marginal harness's capability fence
(`tests/marginal_harness_capability.rs`, one-block resolution) for the leak
direction and the proven A1 stale-inc/dec seam checks for the double release.

**Why IOR-3 is not written.** Under retain-on-force no word of a published
`Pure` node is written, so lane contention on the witness has no code path. What
two lanes share is the payload's count, moved only by the atomic `rc_inc` and
release every heap value already uses and the `concurrency_*` corpus already
exercises. This prevention is structural only if the as-built change deletes
`swap_pure_payload_to_claimed` and the `Claimed` decode, and adds no
post-publication write and no count- or freshness-directed move. `review`
confirms those four facts at source; if any fails, IOR-3 returns to `qa`. A
two-lane e2e cell would also be a weak instrument: scheduling decides whether
both lanes force, as the `race` probes showed. S121 cells 2 and 3 stay credited
to their existing equivalents.

No e2e cell covers a reused `Bind`: it has no force-time write and reaches the
same leaves; the shared-parent fresh-`Bind` module pair already carries its
ownership.

### Retired with the claim

Retain-on-force removed the one transfer that A6 and the claim observers
refereed, so they retired in the correcting change-set. Their obligations moved:

| Obligation | Carried by |
|---|---|
| a payload leaving through the shallow last-reference release has exactly one owner | teardown discharging `Owned(glue)` under both dispositions — `dev` units T1–T2 — and IOR-2 |
| a second successful transfer of one node is reported | no transfer remains; a double release is caught by the A1 seam checks and marginal balance |
| the claimed state is visible before any later release | nothing is written after construction |

Unchanged and required green: the Q3 public aggregate and its controls, the
shared- and unique-parent fresh-`Bind` pair, the `Select`-loser release unit,
the `platform_pure_string_*` cells and the healthy `concurrency_*` corpus.
Error-abort, `Select`-loser and cancelled-frame paths need no new cell: the
consumer holds the same one reference it held before (minted now, moved then),
and the only new obligation — the node's own reference — is T1–T2's.

### `dev` module evidence (intrinsics force and teardown seams)

Red first against the current seam, on the existing intrinsics `io` and `drop`
test-module fixtures and the `alloc` ledger:

- T1 — an `Owned(glue)` `Pure` released through the shallow last-ref path after
  one force: payload released exactly once, balanced. Replaces A6's planted leg.
- T2 — the same node never forced, and forced once then released structurally:
  balanced each way.
- T3 — one `Owned(glue)` node with a second owner forced twice: each force
  returns a live value the consumer releases; the payload stays live for the
  node; final teardown balances. Scalar witness once.
- T4 — `Owned(glue)` over a bare nullary-tag payload: no count is touched.
- One further unit per payload category for which `design`'s source analysis
  finds `rc_inc` is not the exact inverse of `drop<T>` (`arch` names `IVar` as
  the candidate); none if the analysis finds none. No category matrix.

T1–T4 and a scalar T3 twin are landed in
`crates/cranelisp-intrinsics/src/io/tests.rs`, where the private force seam is
reachable; each was observed RED on the seam without the retain
(`.local/s122-io-reuse-dev-red-log.txt`).

Completion: IOR-1 flips and IOR-2's exit legs pass in the change-set carrying
the correction; IOR-C and the unchanged set stay green; the retirements above
land in that change-set; the full `cargo nextest run --no-fail-fast` shows no
RED that does not trace to an open defect. IOR-2's balance leg completed with
IOR-5. If the correction touches codegen or the result root, IOR-1 is also entered
once at the REPL; otherwise one mode suffices and `--link` is a stated limit. No
test may pin `Pure node forced more than once` as an outcome of a legal program.
The cost measurement `arch` asks for is `design`'s, order of magnitude only, and
is not acceptance evidence.

#### Reserved witness — review R1 allocation

`1` has no producer: the claim swap that wrote it is deleted, the backend stamp
cell pins that no emitter writes it, and no artifact carries it. A witness-`1`
node therefore reaches teardown only through a future emitter or a corrupted
word. What is worth evidence is the decode, because `glue => Owned(glue)` is a
catch-all: dropping the `1` arm compiles, keeps every current test green, and
turns the word into a call to address 1. The gated report is a new instrument,
so its detection proof belongs to the introducing change-set (root `CLAUDE.md`
§Assurance).

Conditional on `design` (intrinsics) retaining `Reserved`. If `design` retires
the variant instead, the arm, the "never a call target" sentence and both cells
go together and nothing replaces them: `1` is then no more special than any
other corrupt word, and that narrowing is truthful.

| ID | Class | Condition | Plausible wrong outcome | Layer, owner |
|---|---|---|---|---|
| R1-a | safety fence | Ungated structural teardown of a `Pure` node with witness `1`, whose field 0 holds a live string the node does not own, deallocates exactly the node and leaves the string live. | `1` decodes as `Owned` and is called (the process faults); or field 0 is discharged as if owned | `dev` (intrinsics) unit in `drop/tests.rs`, on the scalar-node fixture pattern beside it |
| R1-b | maintenance check | The same node torn down with `CRANELISP_RC_DEC_CHECK` armed hard-fails with the seam banner and `reserved Pure payload witness`. | the report never fires, or fires for another reason | `dev` (intrinsics): one more leg and child arm on `drop::tests::unknown_tags_hard_fail_under_the_diagnostic_gate` |

- R1-a is also R1-b's silent leg and the decode's witness; no separate `decode`
  unit, no second disposition (one dispatcher, one arm) and no force cell.
  Force never calls the witness; a `1` misread there retains a payload once —
  a leak, not a wild call — and R1-a already fails on that misdecode.
- R1-a's red is observed once by deleting the `1` arm locally; R1-b's by
  observing the child pass ungated. Record both; no standing mutation run.
- Force staying silent on `Reserved` needs no evidence: a forced node still
  reaches teardown, which reports. If `design` rules that force must report,
  the condition returns to `qa`.
- The four IOR-3 source facts get no standing guard: a reintroduced
  post-publication write needs a deliberate new `AtomicI64` or `write` site in a
  reviewed crate, and IOR-2 plus T1–T3 fail on its ownership consequences.

**Advisories, resolved in the same source visit as E-T1–E-T3.** A1: `// defect:`
marks a repro born from a defect, which here is IOR-1 and IOR-2 under `tests/`;
T1–T4 and the scalar twin are module evidence of the correction and name a locus
that is now cured, so `dev` removes those lines and keeps the `// spec:` cites.
The notation is not extended to the module tier. A2 (commentary weight, inline
`force_once`) and A3 (rename `PurePayloadState` / `PURE_STATE_OFFSET` to witness
vocabulary) change no condition and need no evidence beyond the crate gate. One
finding-scoped re-review covers R1-a and R1-b only.

### `Effect` and `Launch` probes — diagnostic, separate from the `Pure` defect

Class: diagnostic observer. The probes decide whether `Effect` or `Launch` reuse
enters scope as new defect intake. They do not gate the `Pure` correction, and
no protective claim or other fix is allocated on their account before a result
and its approval. `test` runs them sequentially against the HEAD debug binary in
its own scratch directory (`sprints/METHOD.md` probe hygiene), uncommitted, one
run per source, ten-second timeout, recording exit status or signal, stdout and
stderr verbatim.

| Probe | Subject | Control — differs only by | Conforming observation |
|---|---|---|---|
| P-E | one platform effect value bound by `let` and forced twice in sequence (`bind e (fn [_] e)`), using the effect the neighbouring `spec_10_io` effect cells use | the continuation constructs the effect afresh | the effect's output twice, in order; same exit as the control |
| P-L | an existing `concurrency_*` launch-and-continue source whose launching IO value is `let`-bound and forced twice | the second force builds the value afresh | the control's output and exit |

P-L runs only if such a source is a one-token change to an existing cell;
otherwise `test` reports it not constructed. A clean-looking P-E does not clear
the hazard `arch` reads at source — a second `Box::from_raw` can pass unobserved
— so a conforming result is reported as inconclusive for memory safety, not as
green. Results return to `qa`. A non-conforming subject becomes a permanent
failing, unignored, spec-traced repro with its control (IOR-4 for `Effect`), and
`arch` scopes the correction, including any public-API proposal to the user.
`EffectPoll` stays unprobed until `arch` asks.

**Results** (`.local/s122-io-reuse-test-heap-probes.txt`, HEAD `48d6e713` plus
the working tree, one run each). P-L was not constructed: no `concurrency_*`
source `let`-binds its launching value.

| P-E source (`main` body) | Exit | stdout | stderr |
|---|---|---|---|
| control `(let [e (print "p-e")] (bind e (fn [_] (print "p-e"))))` | 0 | `p-e` twice | — |
| subject `(let [e (print "p-e")] (bind e (fn [_] e)))` | 1 | `p-e` once | ``platform fn `platform.stdio/print` dispatch failed: segmentation fault`` |

#### `Effect` reuse — intake

- **Accepted as a defect**, separate from the `Pure` refusal: §10.8.1 makes the
  subject legal; it lost one effect and took a hardware fault. The `Pure`
  defect is a deliberate guard refusing; this one has no guard.
- **Confirmed by the control:** the fault follows the second force of one
  `Effect` node. A parse, import, platform-load or `print` fault is excluded.
- **Mechanism.** At the defect's source
  `cranelisp-platform::call_effect_thunk` rebuilt and consumed
  `Box<Box<dyn FnOnce>>` from node field 0, and
  `io.rs::force_effect_node` neither wrote that field nor refused a second
  force, so a second force re-boxed a released thunk. The named refuter — the
  fault persisting with a re-callable thunk — did not occur: IOR-4 flipped on
  the borrowing `call_effect_thunk`, so the attribution stands.
- **Entered** at the consume-once thunk contract (`call_effect_thunk` rustdoc,
  `total-concreteness.md` §3.4), which the 2026-09-21 ruling now contradicts.
  The contract is `cranelisp-platform` public API and ABI; the user approved
  `arch`'s exact `Effect` delta on 2026-09-21 (`total-concreteness.md` §3.4).
  The `Pure` correction does not cure it.
- The guard turned the fault into exit 1; without the `sigsetjmp` recovery the
  same program is a process crash. One run: determinism is unmeasured.

#### IOR-4 — permanent regression cell

In `tests/spec_10_io.rs` beside IOR-1/IOR-C, on the `sequential_class_program`
spawn shape.

- Subject `run_mode_reused_effect_performs_its_effect_on_each_force` and control
  `run_mode_fresh_effect_per_force_performs_its_effect_control`: the two P-E
  sources unchanged, `--run --no-cache`.
- Both assert exit 0 and stdout exactly `p-e` twice. Neither matches the fault
  text or the signal: the fault is one face of undefined behaviour, not the
  condition.
- `// spec: spec/10-io.md §10.8.1`; subject carries
  `// defect: class=uaf locus=crates/cranelisp-platform/src/lib.rs::call_effect_thunk found=S122 owner=/dev`,
  closed with its `fixed=` stamp under
  [integration state](#io-correction--adequacy-and-integration-state).
- No balance assertion: the subject's literal is last owned by the DLL capture,
  which the ledger cannot see
  ([instrument limit](#ior-6--capture-release-sentinel)). Forced-node
  destruction rests on E-T2 and E-T3.
- Its lifetime fence is [below](#effect-correction--lifetime-and-reuse-fence).

#### Abort-path leak — source-only intake, unconfirmed

`design` (intrinsics) reads `io.rs`'s runtime-error / dispatch-fault return as
disarming the frame without releasing a fresh `current` or the un-popped fresh
continuations
([trampoline ownership transitions](../../design/intrinsics/ownership-and-disposal.md#7-trampoline-ownership-transitions)).
`qa` opened the site: it
disarms and returns; `TrampolineFrame`'s own rustdoc calls that exit "already
balanced", so the two source readings disagree. No leak is measured and no
repro exists; it is a hypothesis, independent of node kind and of the `Pure`
correction, which changes only what a leaked forced `Pure` holds. No cell, fix
or fence is allocated. Confirming it takes one marginal pair differing only in
whether a fresh node is in flight at an abort; `qa` allocates that when `sprint`
schedules the intake.

#### `Effect` correction — lifetime and reuse fence

Authority: the approved delta — `Fn() -> CL + Send + Sync + 'static`
constructors, a borrowing `call_effect_thunk`, `drop_effect_thunk` called once
by node teardown under both dispositions, ABI 11. One owner, one discharge.

| Condition | Plausible wrong outcome | Layer, owner |
|---|---|---|
| IOR-4: reuse performs the effect on each force | second force faults or is lost | e2e, `test` — flips RED→GREEN in the correcting change-set |
| IOR-6: an unforced, discarded `Effect` releases its thunk and captures | teardown row missing under one disposition, so thunk and captured `CLOwned` strand | e2e marginal pair, `test` — subject and control in [IOR-6 sentinel](#ior-6--capture-release-sentinel) |
| E-T1: node released unforced destroys the thunk once | as IOR-6, at the seam | `dev` (intrinsics) unit, drop-counting capture; RED first on the current empty `Effect` field row |
| E-T2: node with a second owner forced twice, then released: two calls, one destruction, after the last call | force still frees the box; destruction doubled; destruction before a later call | `dev` (intrinsics) unit on the new seam. Not run against the current seam — it is undefined behaviour in-process; its pre-fix red is IOR-4's |
| E-T3: shallow last-reference release after a force destroys the thunk once | the `SpineTransferred` disposition omits the row | `dev` (intrinsics) unit |
| E-P1: a capture whose destructor panics does not unwind out of `drop_effect_thunk` | unwind across the `extern` boundary aborts the host | `dev` (platform) unit |

- `Send + Sync` is structural: a violating closure does not compile. Its
  evidence is the workspace build of every in-tree platform DLL plus the
  generated `public-api.txt` lines, which the executing baseline guard then pins
  against removal. No compile-fail test and no two-lane e2e cell: scheduling
  decides whether both lanes force, as for IOR-3.
- The two `ABI_VERSION` literal pins in `tests/concurrency_poll_edge_guards.rs`
  and the adjacent-pair message in
  `tests/platform_errors.rs::platform_abi_version_mismatch_e2e` read 11
  (maintenance check).
- **Trampoline-driven discharge gets no further cell** (intrinsics review
  advisory). `feed_continuation` releases a fresh `current` through one
  tag-blind `dec_shallow_io` call. E-T3 observes that function discharging an
  `Effect` once, and every green e2e balance cell that forces a fresh node
  observes the call being made. A counting trampoline cell fails only where
  one of those already fails.
- The host-side thunk box is outside the allocation ledger; e2e sees its
  destruction only through a captured counted value.

##### IOR-6 — capture-release sentinel

- **Instrument limit.** `RcStats` and `AllocParity` read the host allocator's
  counters in `cranelisp-intrinsics`. A platform DLL's last release —
  `CLOwned` drop → `CLHeap::dec_rc` — frees with `std::alloc::dealloc` and
  reaches neither. A counted block whose last owner is a DLL capture reads +1
  whether the DLL frees it or strands it.
- **Consequence.** The first subject, `(let [_ (print "p-e")] (Pure 0))`, made
  the thunk the literal's only owner. It measured +1 before and after the
  teardown correction; the traced run counts the `Effect` and `Pure` node frees
  and no free of the string. That +1 is not evidence of a product leak, and
  production is not changed to satisfy it. That the DLL-side free happens is a
  source argument, not a measurement.
- **Fixture property.** The captured value has a second, host-held owner that
  outlives the discard, so the host performs the last release:
  control `(let [s "p-e" n 0] (Pure (add-i64 n (str-len s))))`, subject the same
  with `n (let [_ (print s)] 0)`. Exits equal and non-zero, stdout empty,
  `pair.allocs() > 0`, `CRANELISP_RC_DEC_CHECK` armed, `assert_balanced`.
  `test` may respell with free-standing primitives; the property is what binds.
- **Discrimination.** A stranded capture pins the string's count at 1 after the
  host's release: +1. A doubled destruction releases it early, so the later
  `str-len` and host release meet a freed block under the armed seam check.
- **Detection — proven.** `dev`(intrinsics) retargeted the `Effect` field row
  at the empty field set once and restored it byte-exactly. Under the mutant:
  control 2/2, subject 3/2, marginal +1, failing at `assert_balanced`, both
  exits still 3. Restored: subject 3/3, marginal 0. No standing mutation run.
- **Classification.** Safety fence on the composed path (real DLL constructor,
  real teardown, `CLOwned` capture). E-T1–E-T3 remain the seam evidence. The
  `// defect:` tag on the first subject is withdrawn, not retagged: its red was
  the instrument's.
- A non-zero marginal on the corrected build returns to `qa`; `test` does not
  adapt the subject to reach zero.
- **Limit carried.** Any program whose DLL capture is a block's last owner —
  for example a forced `(print "literal")` — reads as a leak under both
  instruments. Diagnostic-observer limit; no ledger or allocator change is
  allocated, and none is authorized by the approved `Effect` delta.

##### Discharge-panic containment (platform review R1)

- **Grade.** Asserted with a named falsifier. E-P1 measures the catch in
  process; nothing measures it across a real `cdylib` boundary.
- **Falsifier.** A DLL-built `Effect` whose capture's destructor panics, torn
  down by the host, aborts the process instead of completing.
- **Decision: bounded residual, no fixture now.** In-tree captures are `i64`
  and `CLOwned`; neither destructor can panic. The uncontained outcome is an
  abort, not corruption. The containment is lost if the holder moves out of
  the generic constructor; that compiles and keeps E-P1 green, which is why
  the grade is asserted and not structural.
- **Trigger.** The first in-tree capture with a fallible destructor, or a
  change to where the holder is constructed, allocates one extern on the
  existing `platforms/boom` fixture plus one `tests/platform_errors.rs` cell.
  A new `cdylib` is not warranted.

#### Scope-result `bind` leak — intake

Accepted as a defect: a legal program strands its IO tree. Measured by `dev`
(`.local/s122-io-reuse-dev-scratch/`, one `--run` each, allocation counts from
`CRANELISP_RC_STATS`), all on the `platform_pure_program` preamble:

| `main` body | allocs / deallocs |
|---|---|
| `(bind (pure-string) (fn [s] (Pure …)))` | 6 / 6 |
| `(let [p (pure-string)] (bind p (fn [s] (Pure …))))` | 6 / 2 |
| `(let [p (pure-int)] (bind p (fn [_] (Pure 17))))` | 4 / 1 |
| `(bind (Pure 0) (fn [_] (bind (pure-string) (fn [s] (Pure …)))))` | 9 / 9 |
| IOR-2 control | 11 / 3 |
| IOR-2 subject | 9 / 3 |

- **Confirmed by control:** the leak follows `let`-binding the operand (rows 1
  and 2 differ in that alone) and does not need a heap payload (row 3).
- **Mechanism — observed at its seam ([C0](#ior-5-correction--evidence-delta)).**
  Not the binding's own release: that strands `p` and its payload only, and rows 2 and 3 strand the
  `bind` node and its closure as well. One reading fits all six counts: a
  `bind` node that is the result of a scope owning a heap binding takes the
  protective retain in
  `crates/cranelisp-backend/src/compiler/rc_emission.rs::protect_return_value`
  (a builtin call is not an independent result there), and no release balances
  it. Row 4's closure parameter is an `Int`, so no retain; IOR-2's continuation
  parameter is a `String`, so the inner `bind` strands four nodes in the control
  and two in the subject — the −2. The pre-fix CLIF of `let1` carries an
  `atomic_rmw add` on the new Bind node's RC word and `sib` carries none; the
  corrected build's CLIF differs by exactly those three lines.
- **Unmeasured:** a build without the `Pure` correction; balance under `--link`
  and the REPL (value only: the IOR-1 subject returned 7 in all three modes); a
  non-IO heap binding; a `select`, `race` or `sleep` result publicly.
- **Coverage attribution:** every IO balance cell either ends its scope in a
  fresh `Pure` or holds no heap binding beside its `bind`, and IOR-2 assumed two
  healthy children without a cell establishing it.
- The `Pure` correction is intrinsics-only and changes what a stranded forced
  node holds, not whether it is stranded; the backend correction is
  [below](#ior-5-correction--evidence-delta).

Landed by `test` in `tests/spec_10_io.rs` beside the `platform_pure_string_*`
cells, `MarginalPair` over `platform_pure_program`, each observed once:

| Cell | Control allocs/deallocs | Subject | Residual |
|---|---|---|---|
| `platform_pure_let_bound_bind_operand_balances` — rows 1 and 2 above | 6/6 | 6/2 | +4 |
| `platform_pure_unused_heap_binding_beside_bind_balances` — control `(bind (pure-int) (fn [_] (Pure 17)))`, subject the same inside `(let [q (pure-int)] …)` | 4/4 | 5/2 | +3 |

- The table records the pre-fix observation; both read 0 on the corrected
  build. Both exit 17 on both children. The +3 fits node, inner node and
  closure; that breakdown was not traced.
- Both cells and IOR-2 carry
  `// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/rc_emission.rs::protect_return_value found=S122 owner=/dev`;
  C0 confirmed the locus; all three are closed with `fixed=S122/57253cf2`. The
  requirement they fence is `spec/12-runtime.md` §12.3.1, which the IOR-5 cells
  now cite; IOR-2 cites `spec/10-io.md` §10.8.1 for its value legs and the runtime release requirement
  for its balance leg. The cancellation coverage band claims nothing from
  them.
- Do not re-axis IOR-2 or any sibling to avoid the shape.

#### IOR-5 correction — evidence delta

Authority: `design/backend/s122-closure.md` §8 — a closed backend-private
classification of the four IO-combinator `BuiltinFn` carriers (`bind`, `select`,
`race`, `sleep`), read by the spark exclusion, the interceptors and the `Apply`
arm of `value_provenance_with_calls`, which maps each to `Fresh`. No public-API,
ABI or schema change. `design` confirmed the structure at source
(`call_returns_owned_reference` answers `Some(_) => false`, so the result was
`OwnedTemporary` and took the protect); C0 observed the emitted retain.

| # | Condition | Plausible wrong outcome | Layer, owner |
|---|---|---|---|
| C0 | Before any edit, the pre-fix CLIF of `let1.cl`'s `main` shows an `atomic_rmw add` on the new Bind node's RC word that no release balances; `sib.cl`'s shows none. | the counts fit a different mechanism and the correction cures nothing or something else | `dev` (backend), one `CRANELISP_CODEGEN_DUMP` run per source from `.local/s122-io-reuse-dev-scratch/`, stderr kept. No such retain: stop, return to `qa`. This observation retires "provisional" on the locus |
| C1 | Each of the four carriers, as a scope result, classifies `Fresh`; the IOR-5 shape's CLIF carries no retain on the Bind node's RC word. | one carrier omitted; the classification lands but a second reader still names the spelling | module, `dev`: `compiler/apply/io_combinator_freshness_tests.rs`, pure tier and CLIF tier, both observed RED before the fix |
| C2 | Narrowing holds: `(let [p io] (if c (bind p k) p))` stays `NotOwnedHere`; a `vec-get` builtin stays `OwnedTemporary`; a `bind`-spelled `Apply` without the carrier is not `Fresh`. | `Fresh` granted to a join, to every builtin, or by spelling — the binding arm's node is freed at scope exit and then forced | module, `dev`, same file, pure tier. Green before and after; this is the control that makes C1's red discriminating |
| C3 | The two IOR-5 cells and IOR-2's balance leg read zero on the corrected build; `sib`, `nested` and every IO balance cell stay green; no `CRANELISP_RC_DEC_CHECK` trip, double release or exit change. | the elision fires on the module fixture and not on the public shape; or it over-releases | existing e2e cells, unchanged. IOR-2 is a prediction: if it stays RED after the IOR-5 cells flip, its −2 has a second cause and returns to `qa` as new intake |

**The suggested public borrowed-result negative is not allocated.** Its wrong
outcome is C2's. The join is `ValueProvenance::join`, a `max` this correction
does not touch, already pinned for a `Fresh` arm beside a binding arm
(`fn_compiler.rs::one_non_fresh_arm_makes_the_join_non_fresh_neg`); the only
new fact is which `Apply` nodes are `Fresh`, and C2 observes that and the
verdict at its own seam. An e2e twin would be green before and after and could
fail only where C2 already fails.

**C2 carries no CLIF leg of its own** (backend review R1). Emission reads the
verdict through one gate, `body_has_independent_result`, over the same walk C2
calls. Both sides of that gate are already pinned in CLIF: a borrowed join
keeps the protect
(`rc_emission/return_ownership_tests.rs::mixed_callable_and_scope_binding_return_keeps_protection`)
and C1's `Fresh` result loses it. The only fact this correction adds to the
join is its verdict, which C2 observes. A CLIF twin would fail only where one
of those three fails.

**Modes.** Shared codegen changes, so every mode takes the elision. The final
full `cargo nextest run --no-fail-fast` already carries the REPL and `--link`
`bind` cells and is the standing mode evidence. Added once, uncommitted, by
`dev` on the corrected build: the IOR-1 subject — itself a heap-binding scope
returning `bind`, needing no platform preamble — entered at the REPL and built
with `--link`, seam checks armed where the mode honours them. Expected 7 each.
Diagnostic observer; a wrong value, fault or check trip is a refuter and returns
to `qa`. No per-mode balance cell: nothing in the correction is mode-conditional.

**CLIF goldens** (maintenance check). A golden may change only where a
heap-binding scope returns one of the four carriers, and only by losing the
protect retain. `dev` re-baselines those with that attribution; any other golden
difference is a refuter.

Completion: met. C0 recorded before the edit; C1 red then green; C2 green on
both builds; C3 zero on the full run; the three mode entries returned 7; no
golden changed.

**Residual intake — not accepted semantics, nothing allocated.**

- *Joined fresh arm.* A join with a fresh-combinator arm and a binding arm keeps
  the protect, so it still leaks when the fresh arm is taken. Read at source by
  `design`; unmeasured. The leak is a defect, not a sanctioned cost of the
  conservative join; per-arm protection needs its own design.
- *Unmeasured neighbours.* An extern string primitive
  (`(let [a (int-to-string 1)] (int-to-string 2))`) or a platform call
  (`(let [q (pure-int)] (pure-int))`) returned from a heap-binding scope may
  share the class. Neither is confirmed, and each needs its owner's result
  contract before a probe means anything. No probe is run on their account now.

`qa` allocates a marginal pair for either when `sprint` schedules the intake.

**Limits.** One observation per source and one binary; public cells run under
`--run` only. Concurrent reuse is argued from construction, not measured.
`Launch` and `EffectPoll` reuse are unobserved, as is reuse of a `Bind`, `Par`
or `Select` node as such; the §10.8.1 band names `Pure` and `Effect` and no
more.

#### IO correction — adequacy and integration state

- **Evidence: adequate** for the approved reusable-`Pure`, `Effect` ABI-11 and
  IOR-5 corrections. One full `cargo nextest run --no-fail-fast` on the
  integrated tree: 6011 run, 6010 passed, 1 failed, 1 skipped. The failure is
  `citation_drift::project_documents_conform_to_the_checked_in_declaration`, a
  maintenance check on project documents that gates no IO condition; the skip
  is the `#[ignore]`d contention benchmark in `tests/concurrency_spark.rs`.
- **User gate, closed (2026-09-21).** The generated
  `crates/cranelisp-platform/public-api.txt` diff matches the approved delta
  under independent review. The user confirmed that exact generated diff.
- **Integration, complete.** The corrections are in checkpoint `57253cf2`.
  The `// defect:` tags on IOR-1, IOR-2, IOR-4 and both IOR-5 cells carry
  `fixed=S122/57253cf2`, and no "Attribution provisional" line remains. A RED
  on any of those cells is a regression and returns to `qa`. The ABI guard is
  `tests/concurrency_poll_edge_guards.rs::poll_capacity_rides_node_convention_and_abi_is_v11`.
  The stamp and rename pass changed no assertion and is itself uncommitted.
- **IOR-6 trace, confirmed.** The cell cites `spec/12-runtime.md` §12.3.1 for
  the release and `spec/10-io.md` §10.8 for the unforced effect performing
  nothing, which it observes as empty stdout. Both match what the cell
  observes; no owner correction is needed.
- **Residuals carried to close:** the ledger's blindness to DLL-side frees
  ([limit](#ior-6--capture-release-sentinel)); asserted discharge-panic
  containment ([grade](#discharge-panic-containment-platform-review-r1)); and
  the open intakes — the severed join and cross-lane no-overlap that
  `design/intrinsics` grades asserted, the
  [abort-path leak](#abort-path-leak--source-only-intake-unconfirmed), the
  joined fresh arm and the unmeasured neighbours above. Each stays an
  unconfirmed or uncorrected defect hypothesis, not accepted semantics.

## Retired-audit evidence reads — frontend S113 R1/R7, backend S110 R2

Source read only; nothing executed. Green state rests on the integrated run
recorded [above](#io-correction--adequacy-and-integration-state). The
assessments are in Git at `57253cf2`: the frontend S113 and backend S110
reports.

- **Frontend R1 — discharged.** The class is closed by construction and by
  cells, not only at the originally pinned sites.
  - *Ascribed axis, structural:* the reader folds `:Type form` into one
    `Sexp::Annotated` node and `build_expr` builds it, so no expression
    position can drop an ascription by calling `build_expr` directly.
  - *Trailing axis:* `build_let`, `build_impl_method` and `build_trace` route
    through `build_body_to_end`; `build_method_sig` rejects anything after its
    one trailing form. Cells in
    `crates/cranelisp-frontend/src/ast_builder/tests.rs::track_d_wd1`:
    `let_body_ascription_builds`, `let_body_trailing_form_rejected`,
    `trace_operand_ascription_builds`, `trace_trailing_form_rejected`,
    `impl_method_body_ascription_and_trailing`,
    `trait_default_body_ascription_and_trailing`,
    `deftype_ctor_trailing_form_after_field_bracket_rejected`. Each carries its
    bare or accepting twin.
  - *Head parser × {case, arm}:* both `build_type_head` arms enforce the
    uppercase rule and parameters enforce lowercase. Limit: the bare arm's
    lowercase reject (`(deftype point …)`) is a match guard whose only
    fallthrough is an error arm, and no cell names it; the audit's hole was the
    list arm. One negative assertion closes it and rides ACT-0968 as an
    advisory rider, not a dispatch of its own. Cells:
    `deftype_parenthesized_head_lowercase_rejected_uppercase_twin_accepts`,
    `deftype_uppercase_type_param_rejected` (unit);
    `tests/w3_enforcement_fences.rs::deftype_lowercase_parenthesized_head_rejected_neg`
    and the four cells of `tests/type_param_case_m2_0676.rs` (e2e, `deftype`
    and `deftrait`, each with an accepting twin).
- **Frontend R7 — discharged.** The user ruled 2026-07-20 that `: Int` ≡ `:Int`
  is tolerated and dangling qualifiers error; `tests/ra_annotation_qualifier_0682.rs`
  pins both space-tolerance positives, the `:foo/`, `:a.b/`, `foo/`, `/bar` and
  non-type-bound-form rejects, and the bare-`/` division fence.
  `consume_dotted_module_path` exists once in `reader.rs` with the symbol and
  annotation paths as its two callers.
- **Backend R2 — two of three seam classes discharged; the pattern seam is
  not.** KC-N1/N2 (call) and KC-N3–N5 with the KC-N6 fence (value) assert their
  message families. No test in the backend unit tier or `tests/` asserts either
  `compile_constructor_pattern` miss arm (`match_codegen.rs`: carrier-`None`
  "no resolved_ctor carrier"; entry-miss "has no Def"). The KC-N family never
  enumerated this seam, so the arms have not been observed to fire.
  - *Surviving wrong outcome:* with the resolver family deleted a fallback
    cannot re-resolve, but a lenient arm (skip the pattern, default the tag)
    would still compile and mis-match silently; positive pattern suites stay
    green under it.
  - *Allocation (safety fence, `dev` backend module tier):* two cells beside
    the existing `match_codegen.rs` fixture that populates `pattern_ctors` —
    one omitting the carrier, one keying it to an FQ absent from the tables —
    each asserting a `CodegenError` naming the constructor and its family. No
    e2e: a well-formed program cannot reach either arm. Fixture reachability is
    unexecuted; if the harness refuses earlier, `dev` reports the seam that
    fired. Carried by ACT-0968.

## Startup recovery and failed-source retention — evidence delta (2026-09-22)

Authority: [session persistence](../../repl/spec/15-session-persistence.md)
§15.2.3 (restored by user ruling), §15.1's retention exception and the
[redefinition](../../repl/spec/18-redefinition.md) §18.8 exception clause;
their bands are restored below. The `dev`-owned unit cells that trace to
§15.2.3 (`src/session_v4/lifecycle.rs::append_failed_forms_reemits_verbatim_and_is_noop_when_empty`,
`src/session_v4/persistent_worker_tests.rs::reload_success_drops_failed_forms_and_error_block`
and `…::reset_command_retains_failed_forms_and_their_error_block`) neither
drive a real startup nor read the regenerated file back. Three `test`-owned
solution cells sit at the end of `tests/repl_persist.rs`
(executed evidence below): fresh tmpdir, `PreludeVariant::PrimitivesOnly`,
backing file seeded with `.user(…)` before the REPL starts. Refusal and report
are asserted by substring (neither text is spec-pinned) and every value by its
exact envelope.

| Condition / class | Plausible wrong outcome | Lowest discriminating observation |
|---|---|---|
| R1 A — a persisted file with one good definition and one definition referencing an undefined name reaches a `user>` prompt and reports the load error. §15.2.3 requires that a report exists; it prescribes neither the report's format nor that it names the file or symbol. | Exit before the prompt (the closed 0489 lockout), or a silent load with no report. | Cell A, session 1: seeded broken file, `assert_ok`, prompt present, report present. Detect the report by the substring the implementation emits today (`[errors: user.cl]`, `src/session_v4/lifecycle.rs::render_startup_error_report`) and mark that substring implementation-specific in the cell: a format change updates the cell, it is not a spec violation. |
| R2 A+Neg — while blocked, an ordinary expression is refused; the good definition's value is not produced for that turn. | The expression evaluates; the block is decorative. | Cell A: `(good 1)` before repair yields a refusal line and no `:primitives/Int` envelope for that turn. |
| R3 A — a definition turn redefining the broken name is accepted and clears the block; the repaired name and the good name then evaluate. | The definition is refused, or the block outlives the repair. | Cell A, same session: `(defn broken [] 2)`, then `(broken)` → `:primitives/Int 2`, `(good 1)` → its value, no further refusal. |
| R4 A+Neg — after a broken-file restart, a successful definition of a *different* name regenerates the backing file with the broken form's text still present verbatim. | The user's example: the broken definition disappears on the next save. | Cell B, session 1: `(defn other [] 3)` then EOF; `read_tmp("user.cl")` contains the seeded broken form text exactly once and `defn other`. |
| R5 A (control for R4) — a successful same-name definition replaces the broken text. | Retention never releases; both texts persist, or the file holds the old text. | Cell B, session 2 in the same directory: `(defn broken [] 2)` then EOF; the file holds the new body once and the broken text not at all; a session 3 `(broken)` → `2` without any error report. |

Existing evidence to extend: `persist_defn_survives_restart_via_user_cl`
(restart shape), `persist_failed_import_not_written_to_backing_neg` (the §15.1
never-written rule for interactive failures, unchanged). Module evidence stays
dev-owned and is not re-allocated: `src/repl/mod.rs::definition_and_structural_turns_pass_the_carve_out`
(carve-out decision), the append_failed_forms tests in `src/session_v4/lifecycle.rs`
(verbatim re-emission) and `persistent_worker_tests::reload_success_drops_failed_forms_and_error_block`
(§14.6 reload authority, mixed with §15.2.3). The no-silent-drop and
repair-direction traces already cite §15.2.3 (`lifecycle.rs:1428, 2955`,
`persistent_worker_tests.rs:694`, `main.rs:310`, `eval.rs:205`). Distinct from
the requirement, and kept `dev`-owned as implementation-specific module risk
with no spec trace: the load report's exact layout and symbol naming
(`render_startup_error_report_names_symbols_and_errors`), which form heads
yield a repairable symbol (`defined_symbol_of_form_*`), and retained-form
ordering (`append_failed_forms_multiple_forms_each_own_block_in_order`). Those
three cells and the `defined_symbol_of_form_*` cells still cite the retired
`repl/spec.md §18.8` path; `dev` retargets them to the internal invariant, not
to §15.2.3, in its next `src/` visit.

### Executed evidence, intake and correction (2026-09-22)

Provenance. Discovery binary: HEAD `7b1220c7` plus a working tree whose `src/`
and `crates/` edits were comment-only citation retargets (diff inspected line
by line), so its production logic was HEAD's. Focused run `7da18da1` — 3 run,
2 passed, 1 failed (`.local/s122-persistence-run1.log`); both persistence
binaries — 43 run (`repl_persist` 37 = 34 pre-existing + 3 new;
`repl_persist_redefine` 6), 42 passed, 1 failed
(`.local/s122-persistence-run2.log`). Corrected binary: the same tree plus the
two-file Binary/int change in `src/repl/mod.rs` (`Reset` arm) and
`src/session_v4/persistent_worker_tests.rs`; `.local/s122-reset-dev-result.md`.
No full-suite run in either state; the full run belongs to the integration
gate. The independent fresh-context review of the change
(`.local/s122-reset-review-result.md`) reports no blocking or required
finding against the correction; its two required items are the `test`
comment handoff and a citation repair made in this record.

| Cell (`tests/repl_persist.rs`) | Conditions | Result | Class and detection |
|---|---|---|---|
| A `persist_startup_load_failure_reaches_prompt_blocks_then_repairs` | R1, R2, R3 | GREEN on first execution; GREEN after the correction | Acceptance. Discriminates by construction: ≥5 prompt-split segments, refusal and no `:primitives/Int` envelope on turn 1, exact envelopes on turns 3–4, no refusal on turns 2–4. No RED leg exists — the behaviour predates the cell (S102 CS-0489) — and none is fabricated; detection of each wrong outcome is argued from the assertion, not observed. |
| B `persist_startup_failed_source_retained_until_same_name_repair_neg` | R4, R5 | GREEN on first execution; GREEN after the correction | Acceptance. The R4 assertion form (`matches(STARTUP_BROKEN).count() == 1` over the same seed) is **observed** to detect dropped failed source: cell C fired it on the discovery binary (`left: 0, right: 1`). R5's release, no-duplicate and clean-restart assertions have no observed RED leg. |
| C `persist_startup_failed_source_survives_reset_then_other_definition` | §15.2.3 "every later regeneration", across `/reset` | **RED → GREEN**: RED on the discovery binary (runs above), GREEN unchanged on the corrected binary (`.local/s122-reset-dev-green-e2e.log`, 43/43) | Acceptance of the retention clause and the repro of the defect below. Observed failure, not setup: exit 0, file regenerated (`defn other` present), seeded broken text absent. The cell was not edited between the two runs. |

Cell C defect, attribution and correction. Trigger confirmed by control: cell
B session 1 has the same seed, prelude, defining turn and EOF without the
`/reset` turn and retains the text once. Mechanism observed at its own seam:
the pre-correction unit (replaced in place by
`reset_command_retains_failed_forms_and_their_error_block`) executed
`dispatch_command(ReplCommand::Reset)` and asserted `failed_forms` empty
afterwards (`self.failed_forms.clear()` in the `Reset` arm);
`regenerate_backing_file` appends retained text only from that map
(`src/session_v4/lifecycle.rs:1435–1436`), and the failed forms never enter the
live table, so nothing else carries them. The refuter — a correction leaving
`failed_forms` intact across `Reset` with cell C still RED — did not fire: the
correction removes only that clear and narrows `error_modules.clear()` to
`retain(|m| failed_forms.contains_key(m))`, and cell C flipped GREEN with no
edit. Owner Binary/int (`dev`, `src/`). Module evidence: the replacement unit
`reset_command_retains_failed_forms_and_their_error_block` observed RED for the
intended reason on the pre-correction arm (`left: []`, `right:
["(defn broken [] nope)"]`, `.local/s122-reset-dev-red.log`) and GREEN after
(`.local/s122-reset-dev-green-unit.log`, 7/7 with the reload/carve-out/append
siblings). Regression observation: `repl_watch`, `repl_redefinition`,
`repl_introspection`, `cache` 285/285 and the `repl::`/`persistent_worker`/
`lifecycle` units 107/107 (`.local/s122-reset-dev-regression.log`,
`…-unit-modules.log`). Detection credit for cell C rests on this recorded
RED→GREEN pair; no post-green mutation is allocated.

Authority. Cell C is a defect under existing authority, and no ruling was
made: §15.2.3 binds every later regeneration until a successful definition
replaces the failed one, `/reset` is not a definition and has no clause in
`repl/spec/03-slash-commands.md` or elsewhere, and the user's retention ruling
carries no `/reset` exception. `/help`'s "Clear all state and reload prelude"
and [reset design](../../design/int/repl-lifecycle.md#2-reset-command) describe an unimplemented full reset and
are not requirement authority. The coupled face — the same arm lifting the
error block without the repair named by [startup recovery](../../repl/spec/15-session-persistence.md) — is now retained for modules
holding failed source and is pinned by the replacement unit only, and that
unit's membership assertion has no observed RED leg (its `failed_forms`
assertion fires first on the old arm) — reasoning-graded, recorded as such.
No e2e cell asserts it and none is allocated: the unit observes the exact
seam, and the public consequence is the retained text cell C already reads
back. One cheap strengthening is allocated to `test` with the comment
re-word: cell C asserts on its turn-1 segment that the `/reset` turn was
dispatched (the implementation's reply substring, marked
implementation-specific like the report/refusal substrings), so the guard
cannot go vacuous and pass on cell B's strength if `/reset` ever stops
dispatching.

`// defect:` class. `release-path-bypass` is added to the controlled
vocabulary in `tests/CLAUDE.md`: retained state whose release the spec ties to
one named condition, discarded by an unrelated lifecycle action. The exact
test-side line for cell C is in `.local/s122-reset-qa-close-result.md`;
`test` applies it and re-words the cell's comment to past tense.

Limits and dispositions:

- `tests/repl_persist_redefine.rs::rejected_change_does_not_write_an_incoherent_backing_file`
  validates a *coherent* restart (session 1's redefinition is rejected, so the
  file never breaks); its FIXME 0489 banner is retired and its trace points to
  §15.6 and §15.2. Its `does_not_contain("has errors")` is a real negative
  (the live refusal line). It is not §15.2.3 evidence and must not be cited as
  such.
- The implementation refuses expressions for every module while any module is
  blocked; §15.2.3 speaks of the affected module. All cells use one module,
  so they do not decide that scope. Naming the broken symbol in the report and
  retained-form ordering are unspecified and are not asserted beyond R1's
  file-naming report line. Cells run in non-TTY piped mode only. Cell C does
  not exercise `/reset` followed by a same-name repair.
- §15.1's last paragraph: no cell enters a compile-failing *definition* at the
  prompt and reads the file back; its band cites the failed-structural-form
  negative (`persist_failed_import_not_written_to_backing_neg`), the
  expression-only control and cell B, with that limit stated in the tag. One
  cell in the next `test` persistence visit closes it; not dispatched here.
- Leads from `dev`, unverified and not attributed as defects: (1) `/reset`
  still clears §14.4 watcher-driven error-set members that hold no failed
  source, while §14.4 item 4 and §14.6 name a successful recompile as the
  exit — the `release-path-bypass` sibling face, on a carrier no cell reads;
  (2) `/reset` still runs `watcher.clear_all()`, so after `/reset` an external
  edit that would repair a watched file may go undetected and the §14.6 exit
  works only at the prompt — and the authorities disagree
  (`design/int/repl-lifecycle.md` says the watcher continues across reset;
  `src/watch.rs` justifies `clear_all` by an arch item), so this one is a
  design inconsistency before it is a product defect; (3) a command that
  replies "not yet available"
  mutates state. Each needs a discriminating public observation before
  attribution; none is a condition of this correction, and none authorizes a
  full `/reset` feature. They route to `qa` intake with `design`/`spec` as
  the eventual owners.
- Annotation bands restored by QA (2026-09-22): §15.1 heading (prior cover
  re-judged valid for the unchanged clauses), §15.1 last paragraph, §15.2.3
  heading and retention paragraph, §18.8 exception clause — all `[Tested+Neg …]`
  citing cells A/B/C as applicable; no paired `[S122 — … RED …]` tag is
  needed because cell C is GREEN.

## CLI and IO exit-code evidence — executed (2026-09-22)

Provenance. Baseline `a7ec1f7d`; the working tree adds test-only lines to
`src/main.rs` (`#[cfg_attr(test, derive(Debug, PartialEq))]` on `ParsedFlags`,
a `flags_of` helper and three units) and cells in `tests/spec_10_io.rs` and
`tests/link.rs`. The diff was read line by line: no production parser, runtime
or harness line changed. Authorities: [CLI](../../repl/spec/00-cli-invocation.md)
§0.2, §0.2.1.1, §0.3, §0.5, §0.5.3; [IO](../../spec/10-io.md) §10.6.1;
[runtime](../../spec/12-runtime.md) §12.6. The independent review of this
delta (`.local/s122-cli-review-result.md`) passed it with no blocking finding.
Its advisories: the stale link-cell name is already current below; the `--run`
half of `main_returning_io_bool_exits_zero_run_and_linked` duplicates
`spec_12_runtime::main_returning_non_int_produces_zero_exit_code` — accepted
redundancy, the allocation asked for the paired mode observation in one cell;
the `link_then_run` harness residual is allocated in its own section below.

Executed runs (logs under `.local/`). Binary units:
`cargo nextest run -p cranelisp --bin cranelisp` 14 run, 14 passed
(`s122-cli-unit-dev-nextest.log`). Detection proof: the same command with two
faults planted in `parse_arg_flags` — the `"-o" | "--output"` arm split so
`--output` no longer sets the override, and the positional captured only at
`argv[1]` — 11 passed and the three new units failed on their intended
assertions (`s122-cli-unit-dev-mutation.log`); both faults were reverted
before the green run. Public cells: focused filter over `spec_10_io` and
`link` 12 run, 12 passed (`s122-cli-public-test-nextest.log`); both binaries
92 run, 92 passed (`s122-cli-public-test-binaries.log`). No full-suite run;
it belongs to the integration gate. Every public cell was GREEN on first
execution against the unchanged product: they are acceptance cells with no
RED leg, and none is claimed.

| Condition | Cell | Result | Class and detection |
|---|---|---|---|
| Non-`Int` inner result exits 0 with empty stdout, `--run` and linked (§10.6.1, §0.2, §12.6) | `tests/spec_10_io.rs::main_returning_io_string_exits_zero_run_and_linked`, `…::main_returning_io_bool_exits_zero_run_and_linked` | GREEN first run | Acceptance. `(Pure "s")` discriminates by construction an exit status narrowed from the result word (the string pointer's low bits); asserts `(Some(0), "")` for `--run` and for the linked executable spawned directly. Detection argued from the assertion, not observed. |
| `Pure 0` main with prelude-supplied `Pure` links and exits 0 (§10.6.1) | `tests/link.rs::link_main_returning_io_pure_zero_with_prelude_exits_zero` (renamed from `…_exits_zero_or_errors_clearly`) | GREEN | Acceptance. The either/or arm is retired; strict `assert_exit(0)`. |
| `--output <path>` writes the artifact there, default `<stem>` absent, the executable runs (§0.2.1.1) | `tests/link.rs::link_output_long_form_writes_named_path_not_default` | GREEN first run | Acceptance +Neg. Exit 23 from `main` proves the file at `out/custom` is the compiled program; `hello` absent is the negative. The short form is discharged by the single parser arm: unit `src/main.rs::tests::output_long_form_equals_short_form_in_any_position`, RED observed under the split-arm fault. |
| Output path without `--link` rejected: exit 1, `error` and `usage:` on stderr, no artifact (§0.2.1.1, §0.3) | `tests/link.rs::run_with_output_path_is_rejected_with_usage_and_no_artifact` | GREEN first run | Acceptance +Neg. Exit 1 rather than `main`'s 23 shows the program did not run; neither `x` nor `hello` is written. `--run` only; the gate is the single `!action_link` predicate in `parse_args`. |
| Target before or after the mode flag is equivalent (§0.5.3) | unit `src/main.rs::tests::target_before_or_after_mode_flag_parses_identically`; process twin `tests/spec_10_io.rs::run_mode_main_returns_pure_exit_code` (`--run user.cl`, exit 42) | 14/14; GREEN | Unit RED observed under the `argv[1]`-only fault. The twin observes the options-first order only: every harness spawn is `<mode> <target> <flags…>` (`tests/helpers/e2e.rs::materialise`), so no committed process cell exercises `<target> --run`. |
| Target between options; an option value stays adjacent (§0.5) | unit `src/main.rs::tests::target_between_options_keeps_option_values_adjacent` | 14/14 | Unit RED observed under the `argv[1]`-only fault (`--priority-workers 3 t --run` ≡ `--run t --priority-workers 3`). Unit-only. |

Limits, explicit:

- REPL-mode rejection of an output path is not observed; the link-only cell
  runs `--run`. Accepted on the single-predicate argument; a REPL cell joins
  the next `test` CLI visit only if the gate gains a second predicate.
- Target-first and between-option orders have parser-unit evidence only. The
  residual — a stage after `parse_arg_flags` that depends on argument order —
  has no carrier: `parse_args` consumes the order-free `ParsedFlags`.
  Reasoning-graded, stated in the §0.5 and §0.5.3 tags.
- §0.3: the link-only cell is the only committed cell asserting `usage:` for
  a CLI argument error; unknown flags, `--run` with `--link`, and the hint's
  positional-target content have no committed evidence. The §0.3 tag states
  this.
- §0.2's missing-`main`, missing-source-file and warnings-to-stderr clauses
  have no committed cell: `spec_05_definitions::multi_arity_call_from_main_batch_no_main_neg`
  asserts the *absence* of the no-`main` error when `main` is defined, not the
  missing-`main` path. Pre-existing gap, not opened by this delta; the §0.2
  tag names it.
- Observation, not a defect: the `USAGE` string and the link-only error name
  only `-o <path>`. No requirement pins the alias in the hint, and
  `user/cli-reference.md` documents both spellings. No filing.
- Pre-existing and outside this delta: the `// spec:` at `tests/spec_10_io.rs`
  for the IO-reuse cells cites a plan anchor that is not a `spec/10-io.md`
  heading (`spec_link_check` MIS-CITED). `test` owns the retarget.

Annotation bands restored by QA (2026-09-22): §10.6.1 and §0.2
`[Tested+Neg …]` naming the `String` and `Bool` linked cells, the `Int` exit
cells and the rejection cell (§0.2 retains the former run-mode parity cite and
names its uncovered clauses); §12.6 extended with the `String` cell; §0.2.1.1
alias and link-only paragraphs `[Tested+Neg …]`; §0.5.3 and §0.3 `[Tested …]`
with limits; §0.5's ordering sentence cites its unit. After restoration
`spec_coverage_reconcile --mode check` reports no cleared CLI/IO row and 0 dead
citations. References outside the QA surface were scanned for the renamed link
cell and the restored tags: none require a change.

## `link_then_run` harness observation — maintenance-check allocation (2026-09-22)

Source of the observation: `.local/s122-cli-review-result.md` advisory 3.
Read against `tests/helpers/e2e.rs::materialise` and
`tests/helpers/e2e.rs::spawn_and_capture`, the 104 `link_then_run` call sites
across 43 test files, [CLI](../../repl/spec/00-cli-invocation.md) §0.2.1.1 and
`src/session_v4/lifecycle.rs::derive_link_output_path`. No build or run.

Finding. `spawn_and_capture` executes the produced executable only when the
compiler exited 0 **and** the path the harness derived exists; otherwise it
returns the compiler's own `CrOutput` (exit 0, `; Linking: …` on stderr,
`linked_execution_elapsed == None`) without error. The harness derives the
path as `<tempdir>/<file stem>`; §0.2.1.1 and the compiler place the artifact
**beside the source**. The two coincide only because every current caller
passes a root-level file. This is not a compiler defect: artifact placement is
GREEN under `tests/link.rs::link_default_output_is_entry_stem_no_extension`
(a nested source and its executable in the same directory) and
`…::link_output_long_form_writes_named_path_not_default`. It is a gap in the
instrument's honesty: a `link_then_run` cell that asserts exit 0 cannot tell
"the program ran and returned 0" from "nothing ran". Nine committed cells sit
in that position (`concurrency_spark::dependent_spark_dependency_panic_ferried_caught_link`,
`link::link_main_returning_zero_exits_zero`,
`link::link_main_returning_io_pure_zero_with_prelude_exits_zero`,
`link::link_repeated_platform_adt_marshal_does_not_corrupt_heap`,
`spec_08_name_shadowing` and `spec_03_types` link twins,
`stdlib_trait_impls::stdlib_link_mode_against_intrinsics_archive`,
`spec_12_runtime::catch_runtime_error_err_arm_link`,
`spec_12_runtime::apply_arg_panic_ferried_caught_link`); the 42 cells asserting
a non-zero exit, the stdout-comparing mode-equivalence permutations and the
safety-matrix link face with a non-zero expectation discriminate already.
Class: **maintenance check** — governs the `link_then_run` instrument, not
product acceptance; a failure blocks claims resting on that instrument only.

Conditions (harness; owner `test`, `tests/helpers/e2e.rs` and cells):

| Condition | Plausible wrong outcome | Cell (existing APIs, synthetic files, no planted fault) | RED reason today |
|---|---|---|---|
| H1 — `link_then_run` derives the artifact where §0.2.1.1 places it (stem beside the source), so a target in a subdirectory runs | Compiler writes `sub/hello`; harness looks for `hello`; compiler status returned | `.file("sub/hello.cl", "(import [primitives [Pure]])\n(defn main [] (Pure 23))").link_then_run("sub/hello.cl").output()`; assert `tmp_exists("sub/hello")` (compiler control), exit `23`, `linked_execution_elapsed.is_some()` | exit `Some(0)`, `linked_execution_elapsed == None`, while `sub/hello` exists — the miss is the harness's, not the compiler's |
| H2 — compiler exit 0 with the derived artifact absent is a `CrError`, never a `CrOutput` | Vacuous green on every exit-0 link cell | `.file("hello.cl", same program).link_then_run("hello.cl").cli_flag("--output").cli_flag("out/custom").try_output()` must be `Err` | returns `Ok` with exit 0 and no execution |
| H2 control — compiler failure through `link_then_run` still yields the compiler's `CrOutput` | Compile-failure assertions turned into harness errors | existing `link::link_module_referencing_discover_tests_extern_fails_with_friendly_message` stays GREEN unchanged | — |

Discrimination: exit 23 versus the compiler's 0 is the same construction as
the `--output` cell; the `tmp_exists` control attributes the miss to the harness
seam, and `linked_execution_elapsed` observes the mechanism directly rather
than inferring it from the status.

Acceptance evidence, minimal: H1 and H2 observed RED for the stated reasons
before the harness change and GREEN after, in one log; the H2 control and the
focused `--test link` binary GREEN; one further `link_then_run` binary from the
nine-cell list GREEN. Root-level callers are unaffected by construction
(`Path::new("user.cl").parent()` is empty), and a derivation mistake fails
every caller loudly, so the integration gate's full run is the backstop, not a
prerequisite. The correction is a `test` dispatch inside this increment; no
action, no `dev` or `spec` work, no compiler defect intake.

### Closure (2026-09-24)

Delivered by `test` at checkpoint `2fee9bb2` plus working tree, no commit
(`.local/s122-harness-artifact-test-result.md`): `tests/helpers/e2e.rs`
derives the artifact as `tmpdir.join(file).with_file_name(stem + EXE_SUFFIX)`,
returns the new `CrError::LinkedExecutableMissing(PathBuf)` on compiler
success with that path absent, and still returns the compiler's `CrOutput` on
compiler failure; `tests/link.rs` §2 carries H1
(`link_then_run_executes_artifact_beside_nested_source`) and H2
(`link_then_run_without_expected_artifact_is_a_harness_error`), both
`// spec:`-anchored to `helpers-api.md` and to the
[CLI artifact-placement rule](../../repl/spec/00-cli-invocation.md). H2 adds `out/.keep` so
the compiler's `--output out/custom` succeeds, the same shape as the existing
`--output` cell, and recognises the error by its `Display` text. QA read the
diff and the three logs; no build or run by QA.

| Leg | Command | Observed | Reads as |
|---|---|---|---|
| RED, cells present, helper unchanged | `cargo nextest run --no-fail-fast --test link -E 'test(…nested_source) \| test(…harness_error)'` — `.local/s122-harness-artifact-before.log` | 2 run, 0 passed, 2 failed. H1: `tmp_exists("sub/hello")` passed, then `tests/link.rs:172` `left: Some(0) right: Some(23)`, stderr only `; Linking: cc -o hello …`. H2: `got Ok: exit Some(0), linked_execution_elapsed None` | Both RED for the stated reasons: the compiler wrote the artifact, the harness looked at `<tmpdir>/hello` and handed back the compiler's status; nothing ran |
| GREEN, helper changed, cells unedited | `cargo nextest run --no-fail-fast --test link` — `.local/s122-harness-artifact-after.log` | 25 run, 25 passed: H1, H2, the H2 control `link_module_referencing_discover_tests_extern_fails_with_friendly_message`, and the nine-cell members `link_main_returning_zero_exits_zero`, `…_io_pure_zero_with_prelude_exits_zero`, `…_repeated_platform_adt_marshal_does_not_corrupt_heap` | Detection proven at the harness seam; compile-failure `CrOutput` preserved; root-level callers in this binary unchanged |
| Further nine-cell binary | `cargo nextest run --no-fail-fast --test spec_12_runtime` — `.local/s122-harness-artifact-spec12.log` | 98 run, 98 passed, including `catch_runtime_error_err_arm_link` and `apply_arg_panic_ferried_caught_link` | Those two exit-0 cells now certify an executed program |

Adequacy: sufficient for this maintenance check. The pre-fix RED is observed,
not inferred; the H2 control discriminates fail-closed from fail-everywhere;
the detection cells were not edited between legs. Five of the nine exit-0
cells have executed GREEN under the fail-closed harness. `helpers-api.md`
§Errors, the `link_then_run` doc line, the `linked_execution_elapsed` field
and the artifact-path paragraph now state the delivered contract; `helpers.md`
§Output already reads `Some` only when the executable was launched and needs
no change. No spec requirement changed, so no `Tested` band moves; no defect
intake, action or `dev`/`spec` work arises.

Limits, explicit:

- No full-suite run. The other 41 `link_then_run` binaries — including the
  remaining four exit-0 cells (`concurrency_spark`, `spec_08_name_shadowing`,
  `spec_03_types`, `stdlib_trait_impls`) — have not executed against the new
  helper. Root-level callers derive the identical path by construction
  (`EXE_SUFFIX` is empty on Linux), and `test`'s grep found no caller passing
  `-o`/`--output` through `link_then_run`; the integration gate's full run is
  the backstop. A RED there of the form `link succeeded but the expected linked
  executable … was not produced` is the instrument working, not a regression:
  it names a cell whose green was vacuous.
- The `EXE_SUFFIX` leg of the derivation is Linux-observed only; parity with
  `derive_link_output_path` on a suffixed platform is by reading, not by run.
- Stdout-only `link_then_run` cells were not individually classified; they
  already discriminated by construction and are unchanged.
- QA's advisory record (`.local/s122-harness-artifact-qa-result.md`) placed
  `; Linking:` on stdout; the log shows stderr. Corrected above; no assertion
  depended on it.

## Backend cleanup QA triage — cache-seam lifecycle discard and R4 sanitize (2026-09-24)

Source: the two inspection-only intake questions in the S115 backend design
consolidation (`.local/s122-s115-backend-design-result.md`). Read-only source
triage; no build, run or test edit. A scratch-directory probe with the built
binary was attempted and refused by the sandbox, so neither lead carries an
executed observation here — every claim below is source-derived and says so.

### C-A — cache lifecycle-validation hardening (deferred by user)

User ruling, 2026-09-24: the compiler is the cache writer; handling deliberate
or negligent cache corruption does not currently justify added complexity.
The proposed `LifecycleInvalid` API change and tampered-cache test allocation
are withdrawn from active S122 work. Existing checks remain unchanged.

Known limitation retained: the backend decoder propagates only
`LifecycleError::InstanceKeyMismatch` from `validate_lifecycle`; other refusals
are discarded and the integration restore path adds no later validation.
No failing reproduction or downstream wrong-code outcome has been executed.
The earlier risk argument concerned invalid cached tables, not evidence that
the compiler produces them during normal operation. C-A is accepted residual
risk for now, not a delivery gate or a request awaiting approval.

The existing design record is `design/int/int.md` §7.5. Revisit
prioritization if evidence implicates compiler-written caches or the user
chooses to expand corruption handling; do not reopen solely because a
hand-edited cache can violate an invariant.

### C-B — sanitized inner names across instances of one template (asserted → constructible falsifier, repro allocated)

Source facts, verified 2026-09-24:

- A mono instance's symbol is its storage key,
  `crates/cranelisp-types/src/lifecycle.rs::concrete_callable_key`, rendered
  `(owner [params] result)` with qualified type names — for example
  `(user/f [user/A-B] primitives/Int)`.
- `crates/cranelisp-backend/src/compiler/resolution.rs::inner_fn_discriminator_for`
  maps every non-`[A-Za-z0-9_]` char of that name to `_`. The reader admits
  `_`, `-`, `?` and `!` as symbol constituents
  (`crates/cranelisp-frontend/src/reader.rs::is_symbol_char`), so type names
  `A-B` and `A_B` (or `A?B`) produce byte-identical discriminators.
- The lambda body name is `__lambda_{discriminator}{start}_{end}__`
  (`crates/cranelisp-backend/src/compiler/control_flow/lambda.rs::compile_lambda`);
  instances of one template share the span; `define_function` is not
  idempotent. The body is defined before the capture glue is built
  (`compile_lambda_body` precedes `build_closure_drop_glue`), so in one batch
  the collision surfaces as a loud `Duplicate definition of identifier`
  codegen error, and the silent `emit_capture_dec_glue` reuse is unreachable
  there.
- The only unit witness,
  `crates/cranelisp-backend/src/compiler/resolution/tests.rs::inner_fn_discriminator_uniquifies_per_mono_instance`,
  compares names that differ in alphanumerics; nothing exercises two names
  differing only in collapsed characters.

Classification: a source-derived prediction of a `wrong-reject` on a
spec-valid program (two product types whose names differ only in `-`/`_`,
one generic function containing a `fn`, instantiated at both), not an
observed defect. Reachability is not disputed by anything in source; it is
unobserved. The mechanism is the 0640 class (`A-B`/`A_B` collapsing to one
symbol) at a sibling seam, which makes it material: the fix is a
backend-internal injective escape with no public surface.

| Condition / class | Required observable | Lowest discriminating evidence | Control | Limit |
|---|---|---|---|---|
| C-B unit, A (mechanism) | `inner_fn_discriminator_for` yields distinct strings for two instance names differing only in collapsed characters | `dev`(backend) cell beside the existing discriminator test: `(user/f [user/A-B] primitives/Int)` versus `(user/f [user/A_B] primitives/Int)` must differ | The existing alphanumeric-difference cell | RED today by construction; it names the seam, not the symptom |
| C-B e2e, A (acceptance) | A program defining `(deftype A-B [x :Int])`, `(deftype A_B [x :Int])`, a generic `(defn f [v] (let [g (fn [] v)] (g)))` and a `main` applying `f` to one value of each type runs and returns the expected value in REPL, `--run` and `--link` | `test` authors the minimal repro through `run_through_all_modes`, `PreludeVariant::None`, tracing to `spec/01-lexical.md` §1.4.1 and `spec/04-expressions.md` §4.5.1; the capture makes the glue name collide as well as the body name | The same program with `A-C` in place of `A_B` (names distinct after sanitizing) must pass | Predicted RED in every mode with the duplicate-definition message; if GREEN, the prediction is refuted and the pair becomes R4's cross-instance witness, which the register lacks either way. If REPL accepts across two turns while `--run` refuses, record `mode-divergence` as a second face |

`// defect:` on the e2e cell, if RED: `class=wrong-reject
locus=crates/cranelisp-backend/src/compiler/resolution.rs::inner_fn_discriminator_for
found=S122 owner=/dev`. The R4 register row is `arch`'s to regrade after the
observation; `design`(backend) already carries the asserted claim with this
falsifier in `design/backend/s115-carrier-and-rc-sweep.md` §4.

### C-B closure — prediction reconciled to executed evidence (2026-09-24)

QA inspected the recorded runs; no QA rerun, build or source edit.

Executed evidence at `6c1fe761` plus the S122 working tree:

- **e2e RED before correction.** `tests/inner_fn_sanitized_name_collision.rs::generic_capturing_lambda_at_hyphen_and_underscore_type_names_runs_in_all_modes`
  fails in all six permutations (run `a7297f9b`, `.local/s122-cb-test-run-final.log`;
  untruncated output `.local/s122-cb-diag.log`). `--run`/`--link`, fresh and
  cached, exit 1 with `Duplicate definition of identifier:
  __lambda__user_f__user_A_B__user_A_B___114_123__`. REPL, fresh and cached,
  exits 0: the `main` turn is rejected with the same identifier at span
  `20..29`, then `(main)` reports `undefined variable: main`; no value is
  observed. Control `…names_distinct_after_sanitizing…` (`A-C`) is GREEN, 7 in
  all six.
- **Unit RED before correction.** `compiler::resolution::tests::inner_fn_discriminator_separates_names_differing_only_in_escaped_chars`
  fails on the QA pair with both sides `_user_f__user_A_B__primitives_Int___`
  (run `3edaea23`, `.local/s122-cb-dev-red.log`); the existing alphanumeric
  cell and four sibling naming cells pass in the same run.
- **GREEN after correction.** Focused resolution units 6/6 (run `5f687fb4`);
  both e2e cells across six permutations 2/2 (run `bbc8b20b`);
  `-p cranelisp-backend` 594/594; `regression` + `ownership_fences` +
  `drop_glue_legacy_emitter_fence` 133/133.

Reconciliation:

- The prediction holds in symptom, mode set and message. Class `wrong-reject`
  and locus `inner_fn_discriminator_for` are confirmed, not inferred: the unit
  RED observes the collapse at that seam, and the e2e control differs from the
  repro only in the collapsed character.
- Not `mode-divergence`: every mode rejects. The REPL face is a rejected turn
  at exit 0, so the e2e cell discriminates by observed value, not exit code.
- Two immaterial deviations from the allocated row: the failing key is
  `(user/f [user/A_B] user/A_B)` (result type is the ADT, not `Int` as the
  example spelled), and the repro uses `[:primitives/Int p]` because the row's
  `[x :Int]` field syntax was invalid. Neither touches the mechanism; the unit
  pair keeps `primitives/Int` and differs only in the parameter segment.
- Detection is established at both layers by the recorded RED-for-the-intended-
  reason → GREEN sequence; no planted fault or mutation run is owed.

Adequacy: the C-B unit and e2e conditions are discharged. The cross-instance
property of span-derived inner names now has acceptance evidence at both
layers, and the e2e guard is a GREEN regression guard. Public API unchanged.

Limits:

- Not a full-suite claim. Exposure of the unrun remainder to the new spelling
  is bounded by inspection only: no test or fixture matches an inner-fn name by
  exact spelling (`tests/regression.rs` mentions are comments), and the names
  are not persisted in `SymbolTable`. `BUILD_ID` cache invalidation is dev's
  source claim; the cached permutations ran in fresh tempdirs and observe no
  stale cross-build cache.
- The unit composes through `closure_drop_glue_name` only; lambda-body
  composition is covered by the e2e. Adequate, since the property lives in the
  prefix.
- The `__curry_{target}_…` `target` component was not re-examined for
  injectivity (dev's report). It is an existing R4-census codepoint, recorded
  as a residual for `arch`'s regrade, not a new allocation.
- Independent review had not reported when this record was written; a review
  finding routes through `sprint` and may reopen this closure.

Handoffs, none of them QA edits here: `arch` regrades R4's inner-name families
against these witnesses and carries the curry-target residual; `design`(backend)
supersedes the `s115-carrier-and-rc-sweep.md` §4 asserted note (falsifier
observed; map now injective); `test` on commit moves the guard's `// Open:`
framing to past tense and adds `fixed=S122/<sha>`. QA's own pending band edit,
outside this invocation's writable set: add the repro as one more `[Tested …]`
citation on `spec/04-expressions.md` §4.5.1 only — no `+Neg` promotion, and the
lexical chapter's simple-symbol row is not promoted from one cell. C-A is
deferred by the user; its current disposition is recorded above.

### 0637 tracking closure (QA surfaces)

`memory-safety-coverage.md` §4 table row and §7 cross-reference now state the
sibling-slot arm as landed and the filing as resolved, and route the open
cache-seam residual to C-A. The S115 instrumentation matrix carried a dated
closure addendum; the matrix is now retired to Git (revision `a07823d8`). No
other QA-owned surface names 0637.

## S68 obsolete-instrument retirement (2026-09-24)

ACT-0984 is resolved. The obsolete link-mode trace rejection cell and its
header references were deleted (77 lines); its filing and Decision 0040's
superseded citation record are retired. The verbatim fixture probe exited 1
with only the non-IO-main diagnostic: `primitives/Trace` was the return type.
The cell's lowercase "trace" match came solely from its filename. There was
no linker or trace-runtime failure. Existing positive linked-trace tests and
the wrong-main-type negative cover the current requirements; no replacement
or spec coverage promotion is needed.

The same binary exposed a second obsolete instrument: a primitive-entry
source grep that had matched only a comment since S117 (`d1c34699`), then
failed when `7134cb28` removed the comment. Its 60 lines were deleted without
replacement: the live-table unit
`crates/cranelisp-primitives/src/tests.rs::every_entry_is_def_kind_primitive`
already checks origin and lifecycle shape, which is the governing rule
(`design/primitives/primitives.md` invariant 6). Its negative leg — no
`Code::Primitive` in primitives code — is structurally discharged: primitives'
manifest names no backend crate, and
`s68_code_enum_has_no_primitive_marker_variant` fences the variant at its
owner. This was an instrument failure, not a compiler regression.

Final evidence: `cargo nextest run --no-fail-fast --test s68_primitives_uniform`
passes 8/8. The earlier `cargo check --tests` passed with only the known nix
future-incompatibility warning; no imports changed afterward. No full-suite
claim. Logs: `.local/s122-act0984-probe.log`, `.local/s122-act0984-check.log`,
and `.local/s122-s68-source-test-run.log`; source checkpoint `f84a6d69` plus
the deletions. QA's allocated conditions are satisfied.

Retained observations: the remaining source-grep assertions are comment-blind;
the non-IO-main diagnostic uses an empty span (`codegen error at 0..0`). These
are recorded limitations/intake, not newly allocated gates. C-A remains
user-deferred.

## Cache documentation leads — QA intake (2026-09-24)

Source: the three cache observations the Binary/int design result carried into
[`int.md` §16.0](../../design/int/int.md#160-open-binaryint-obligations-verified-against-source-2026-09-21).
Read-only intake at `bad445da` plus the documentation working tree. No build,
run or test edit: every claim below comes from reading source and records no
executed observation.

The user's C-A ruling covers deliberate or negligent corruption of
compiler-written caches. It does not cover a cache that goes stale because an
input the compiler does not control changed. Examples are an edited dependency
source and a platform DLL that is missing or refused. The cache design treats
those as ordinary invalidation:
[module caching §1 goals 1–2, §3, §6 and §10](../../design/backend/module-caching.md#3-cache-key-design).
It requires that stale caches are never served and that a cached module
matches a fresh compile.

| ID / class | Required observable and plausible wrong outcome | Lowest discriminating evidence and allocation | Existing evidence / limit |
|---|---|---|---|
| CD-1 A — dependency-hash validity (priority: required) | A program with a cached importer behaves exactly as it does under `--no-cache` after one of that importer's dependencies changes. Two wrong outcomes are plausible. (a) Signature leg: the importer `a` restores against its stale typecheck, so a program that is ill-typed under fresh compilation runs, or runs through a mismatched ABI. (b) Layout leg: the dependency `b` changes compatibly by inserting a concrete `defn` before the called one, and cached `a` calls through a slot index that now names a different function. | `test` writes one minimal repro in `tests/cache.rs` with the shape `main → a → b`, run twice in one project, so that `a` itself is cached and unchanged. The signature leg changes `b`'s exported parameter type. With `--no-cache` this is a type error at `a`'s call site; the cached run must match it. The layout leg inserts a new concrete `defn` ahead of the called one; the value must match `--no-cache`. For each leg, the control is the same second run under `--no-cache`, which differs only in cache use. Cover `--run` and `--link`: link reuses cached objects. Tag it `// defect:` only after a RED is observed, with the class chosen by the observed face. `dev`(src) owns the attributed unit at the writer/restore seam when a fix is scheduled. | Source: `cache_restore.rs::cache_validity_check` passes an empty dependency map, and `nice_worker.rs` records `HashMap::new()` ("future enhancement"). Backend `check_manifest` therefore never runs its dependency loop. Every existing dependency-change cell makes the fresh CLI target the importer, which is never cache-restored (`cache_multi_module_invalidation_dependency_change`, `cache_invalidation_on_dep_change_e2e`, `cache_invalidation_transitive_pipeline`, `cache_prelude_change_invalidates_user_module`), so none can discriminate this case. That is the coverage attribution. Both legs were observed RED and are GREEN under the correction; see [delivered adequacy](#delivered-adequacy-2026-09-24). |
| CD-2 A — platform-miss fall-through (priority: advisory) | When a cached module's recorded platform DLL is absent or refused at restore, the run ends with the same platform-load diagnostic as `--no-cache`. It must not crash, report a conflicting-state error, or complete against the decoded table. A second importer of that module must not accept the abandoned table as satisfied. | This is a bounded later handoff to `test`, sequenced after CD-1. Extend the existing two-run platform cache round-trip in `tests/spec_platforms_adt.rs`. Leg 1 makes the DLL unavailable on the second run, with a single importer. Leg 2 is the same with two importers. The control for each leg is the same second run under `--no-cache`, whose diagnostic is the expected oracle, plus the existing DLL-present cache hit. Any fix belongs to the `dev`(src) restore path. | Source: `try_cache_hit_load` calls `install_cached_table` before `reresolve_cached_platforms` and returns `Ok(false)` with the table installed. Its `contains_key` guard returns `Ok(true)` for any later importer. No test takes this branch. If the DLL is absent, the fresh path also fails, which bounds the impact to crash or misattribution. A DLL that is refused and then accepted on the fresh path could let a second importer compile against the stale table; this is unobserved. |

**CD-3 — cached-object load diagnostic: observation only, no allocation.** The
misattributed "orchestrator-sequencing bug — clause not in memory" message
needs a cached object that fails to load after its metadata validated. A
missing `.o` is already a miss, so this means a malformed or incomplete
compiler-written object, which falls under C-A. The failure is not lost:
`worker.rs::handle_cached_codegen` marks the module failed. Revisit if CD-1,
CD-2 or another observation shows such a load failure in normal operation.

Open handoffs from this intake are listed under
[outstanding risk and next allocation](#outstanding-risk-and-next-allocation).

### CD-1 reconciliation — observed defect (2026-09-24)

QA read the committed cells and the recorded runs (`5b1a843b`,
`.local/s122-cd1-cache-repro-result.md`); no QA build, run or test edit.

Observed, in two consecutive targeted runs: the four cells in the
`tests/cache.rs` section "Dependency change under an unchanged,
cache-restored intermediate importer" are RED — signature and layout legs,
each under `--run` and `--link`. The signature leg runs an ill-typed program (exit 107 where
the uncached oracle rejects with a `String` mismatch). The layout leg calls
`e` instead of `f` (99 where the oracle gives 11).

Evidence adequacy — adequate as the defect record and as the fix's e2e
acceptance evidence for direct imports:

- The arming step (nothing changed, trace shows `cache hit (.meta valid) for
  a`) proves the subject restores `a`; the cell cannot pass through the fresh
  path. It stays valid after a fix, and it discharges the intake's "unchanged
  dependencies keep the importer cached" leg in the three-level shape.
- The `--run` control differs from the subject only in cache use, and
  `a.o` is byte-identical afterwards. The `--link` control is a fresh project
  because `--link` refuses `--no-cache`; each control is also pinned to an
  independent oracle, so equivalence does not rest on the control alone.
- The gate asserts behavioural equivalence, not a cache miss. That is correct:
  the design may permit a hit that re-resolves against the new `b`.
- Recorded RED for the intended reason satisfies the pre-fix detection proof;
  the fix owes GREEN on the same cells with the arming step still GREEN.

Attribution:

- **Symptom and cache-use dependence: confirmed** by the controls above.
- **Locus `src/process_form/cache_restore.rs::cache_validity_check`:
  confirmed by source, mechanism provisional.** Backend `check_manifest`
  iterates only the caller-supplied current map, so the restore seam's empty
  map makes the comparison vacuous whatever the writer recorded. The
  writer's empty record (`session_v4/nice_worker.rs`) alone would cause
  misses, not stale service; it is a co-requisite for keeping importers
  cached, not the stale-serve mechanism. The existing backend unit
  `check_manifest_transitive_dependency_change_invalidates` shows the
  comparison discriminates when given a map (not re-run here).
- **Refuter:** with the restore seam supplying the importer's current
  dependency hashes and the writer recording them, any of the four cells
  stays RED, or the arming step turns RED.
- **Class: one mechanism, one class across all four cells.** The face tokens
  (`wrong-accept`, `enumeration-miss`) are superseded. The key under which the
  cached module is validated omits a determinant of its content, the class
  `drop-glue-underkey` anticipated generalizing when a non-glue sibling
  appeared. The class becomes `artifact-underkey`; the vocabulary in `tests/CLAUDE.md` and the affected test tags now use
  that class under QA's vocabulary authority.

#### Correction evidence — transitive dependency record ([`int.md` §7.6](../../design/int/int.md#76-dependency-record-and-validity))

The correction is int-private: each manifest entry records the source hash of
every module in its transitive closure, and validity is driven by the recorded
keys. That shift changes which failure is silent. As built, the vacuous
comparison served stale. After the correction, an **under-recorded** map (a
missed edge kind, an empty or partial stand-in, a restored member contributing
only itself) serves stale silently. An over-recorded or unsettled member only
causes a miss, which the arming steps and existing hit cells observe. The
delta therefore weights evidence toward under-recording.

| Condition | Plausible wrong outcome | Lowest discriminating evidence | Owner |
|---|---|---|---|
| CL-A — direct dependency (unchanged condition) | Cached importer served against a changed direct dependency | The four `cache_dep_*` cells, recorded RED, turn GREEN with their arming steps GREEN | `dev` turns GREEN; no new `test` work |
| CL-B — change reaching an importer only through an unchanged intermediate (added) | A direct-imports record: `c` records only `{a}`, `a` is unchanged, so `c` restores stale | New `--run` cell, shape `main → c → a → b`. `a` only re-exports `(export [b [f]])`; `c` imports `[a [f]]` and calls `(f 5)`. Signature leg as in CD-1. Arming: with nothing changed, both `a` and `c` restore from cache. Oracle and control: `--run --no-cache` on the edited sources | `test`, RED before the fix |
| CL-C — importer rebuilt over a restored intermediate (added) | Session cache state does not keep a restored member's validated record, or the builder treats a missing record as empty, so rebuilt `c` records `{a}` alone | Same fixture as CL-B. After the cold run, edit only `c`, adding a comment line so its source hash changes. Arming: `a` restores and `c` rebuilds. Then edit `b` and compare with `--run --no-cache` | `test`, RED before the fix |
| CL-D — record builder (added) | An edge kind is omitted, an unsettled member is recorded as empty or partial, or a synthetic module is keyed | Module units: see `dev` completion below | `dev` |
| CL-E — validity query (changed) | A recorded member's current hash is not compared, or an unresolvable member hits | Seam unit at `cache_restore.rs::cache_validity_check`: see `dev` completion below | `dev`, RED before the fix |
| CL-F — no over-invalidation (retained fence) | Unsettled-at-write timing or a wrong prelude lookup leaves modules missing on every run | Existing hit-asserting cells in `tests/cache.rs`; the three `tests/search.rs` pins, including `search_index_to_import_is_meta_cache_hit`; the prelude and submodule cache cells; the CL-B and CL-C arming steps | Existing; `dev` keeps GREEN |

Why these layers:

- **CL-B discriminates the closure from a direct-imports record** only through
  the shape's construction: under direct imports, `c`'s record holds `a` alone,
  and `a`'s source never changes. Its RED as built proves only that it detects
  stale service. No legitimate build records direct imports only, so that RED
  is not observable. The seam observation is the CL-D chain row. Falsifier:
  with the correction in place, CL-B is GREEN while that chain row is absent
  or RED.
- **Why `a` re-exports only.** Its sole edge to `b` is then a re-export target,
  and its entry comes from the no-object writer. So CL-B also discriminates a
  missing re-export edge, and CL-C discriminates a no-object writer that
  bypasses the builder. Contingency: if a re-export-only `a` does not restore
  from cache as built, `test` reports this, gives `a` a concrete `defn` called
  by `c`, and the no-object writer then relies on the structural criterion
  below.
- **`--run` alone suffices for CL-B and CL-C.** The builder and the validity
  query are shared by all modes. The CD-1 `--link` cells already show that
  link restores through this seam.
- **CL-C covers what the builder units cannot.** Those units use a constructed
  session state. CL-C is the only observation that the real restore path
  stores the validated record that the builder reads.

#### Delivered adequacy (2026-09-24)

QA read the working-tree correction (`src/cache/dependency_record.rs`, its
unit module, the retry in `src/session_v4/lifecycle.rs::wait_object_complete`), the `dev` and
`review` results and the recorded logs. No QA build or run.

**Verdict: adequate for CL-A to CL-F; the correction may land.** It protects
dependencies reached through imports, re-exports, declared children and the
prelude. It does not close CD-1 as a class: while F1 below is unresolved, the
§7.6 opening sentence must not be recorded as satisfied.

| Condition | Executed evidence | Judgment |
|---|---|---|
| CL-A | The four `cache_dep_*` cells, recorded RED under `--run` and `--link`, are GREEN with their arming steps in the targeted and final full runs | Adequate |
| CL-B, CL-C | `test` observed both RED for the intended reason: arming, `c.o` identity and control legs passed, and the cached run exited 107 where the uncached run rejects with the `String` mismatch. Both are GREEN after the fix. The re-export-only `a` restored, so they also discriminate a missing re-export edge and a no-object writer that bypasses the builder | Adequate |
| CL-D | Builder units: fresh chain, restored member without a table walk, the six-row edge matrix, prelude absent when the bit is clear, compiler-owned and self exclusion, the three representable unsettled cases. Restored-without-record is unrepresentable because `LoadedSource::Restored` carries its record | Adequate; the chain row discharges CL-B's falsifier |
| CL-E | Five seam units: 4 RED with the unchanged case passing, then 5 GREEN. Limit: the RED ran the surviving `validate` signature with as-built empty-map semantics, not the removed `is_cache_valid`; the recorded e2e REDs cover the original | Adequate |
| CL-F | `tests/cache.rs` 52/52 and `tests/search.rs` 42/42, including `search_index_to_import_is_meta_cache_hit`. The fence fired: the first full run failed both `exemplar_ownership_residue_s116` warm cells because declared children importing `super` lost their entries (review F2). The correction defers an unsettled entry and retries it before the only manifest flush. `a_child_written_before_its_parent_settles_is_recorded_once_it_has` was RED under a no-op retry; it and both warm cells are now GREEN | Adequate; F2 is resolved |
| Structural | `review` confirmed one edge definition, one builder behind every writer, validity only through a current-hash source and no empty-map record. `manifest_globals_current` passes an empty map only as a global-key probe | Adequate |

The final full suite ran 6049 tests: 6048 passed, 1 failed, 1 skipped. The
failure is the maintenance check
`citation_drift::project_documents_conform_to_the_checked_in_declaration`. It
reports document-checker findings over the integrating documentation tree and
names no changed symbol. It blocks document claims, not CD-1 acceptance; root
disposes of it at integration.

#### Outstanding risk and next allocation

Neither required item is a user-accepted residual. Both come before any claim
that CD-1 is closed.

| ID / priority | Risk | State | Smallest next evidence |
|---|---|---|---|
| F1 — FQ-reference dependency (required) | A module whose only use of `b` is a qualified reference has no edge to `b`, which §8.5.4 admits without an import. An ordinary edit to `b` then restores it stale (`artifact-underkey`), or nothing loads `b` for the restored object (`enumeration-miss`). This is a source edit, not cache corruption, so C-A does not cover it | Qualified **callable** references: corrected by [callee-module edges](../../design/int/int.md#761-callee-module-edges) and adequate as a bounded correction ([F1 acceptance](#f1-acceptance-and-qr-classification-2026-09-25)). Every other qualified-reference kind: the measured QR REDs below | FN-1 fence, armed ([alias-only correction](#alias-only-import-registration-fixme-0798--correction-adequacy-2026-09-25)); QR disposition by `arch` and the user |
| DV3 — fresh module over a restored module (required intake) | A spec-valid program failed on a warm run. A freshly re-typechecked declared test child reported `'assert-true' not found in module 'testing.assertions'` while that module restored (first full run, both `exemplar_ownership_residue_s116` warm cells). Deferral removed this trigger, not the mechanism. Editing only such a child reaches the same shape | Observed once; mechanism unknown; no minimal repro | `test`, one stdlib-free `tests/cache.rs` cell. `grp.cl` declares `(mod asserts)`, and `grp/asserts.cl` defines `one`. `lib.cl` declares `(mod- test)`, and `lib/test.cl` imports `[grp.asserts [one]]` and calls it. `main` imports `lib`. Run cold, then warm with nothing changed (arming: `grp.asserts` and `lib.test` hit). Append a comment to `lib/test.cl` only and compare with `--run --no-cache`. If GREEN, add one variant whose child also imports `super` (the exemplar shape) and report. If RED, add the sibling that differs only in `asserts` being a top-level module, to control the declared-child cause |

Advisory and unallocated; each awaits its owner:

- **F3 — record conflicts and write-time reads.** A walked member's loaded
  hash overrides a restored member's recorded hash, and the builder reads the
  stash at write time. After an in-session change, both under-record. The
  unit `hashes_are_the_versions_this_session_loaded` pins the current rule,
  which §7.6 does not state. `design`(int) rules: make a conflict `Unsettled`,
  or record both paths under *Unprotected* with falsifiers. No repro is
  allocated, because a deterministic e2e face needs nice-worker ordering
  control.
- **F4 — a prelude that was absent.** The builder drops the prelude edge when
  no prelude loaded, so adding a `prelude.cl` later is undetected. The face is
  a wrong-accept of a bare name that the new prelude makes ambiguous. It needs
  a project that had no prelude. `design`(int) records or protects it.
- **Index-writer entries.** An index-written entry whose member this session
  never loaded stays unsettled and is dropped at session end. This is
  source-read and causes misses only. `design`(int) records it with `dev`'s
  observations on index edges and empty index `.meta` structural fields,
  which bear on ACT-0952.
- **F5 and F6.** `dev` removes the uncalled
  `introduce_module`/`try_load_cached_for_introduction` install path, which
  skips `validate`, and resolves the duplications at its next visit.
- **Reactor panic, `dev` observation 6.**
  `spec_10_io::resource_serial_diff_token_parallelizes` panicked once in the
  first full run with `reactor suspended with no armed interest`. It passed
  alone and in the final run. No cache is involved: each run uses a fresh
  tempdir. It joins the unattributed run-dependent members of
  [0694](../../design/arch/fixmes/0694-qa-suite-count-nonreproducible-two-interleaving-dependent-guards.md);
  QA's filing edit is outside this dispatch's write scope.
- Unchanged: the `startup_latency` before/after run, if restore-time closure
  hashing is questioned, and the trait-home reverse-dependency question, which
  `design`(int) establishes from source before QA allocates.

Unprotected paths recorded by design in `int.md` §7.6, not allocated:

- a platform DLL signature change made without a `.cl` edit;
- a same-session disk edit to a loaded dependency before an importer restores;
- corrupt cache content.

Only the last has a user decision: the user deferred C-A hardening, and that
deferral still binds. The first two are design records, not user-accepted
residuals.

Limits:

- Every `process_form` restore caller reaches validity through
  `try_cache_hit_load`, so no per-caller or REPL cell is allocated.
- The signature leg's body ignores its argument, so the memory-safety
  consequence of the mismatched ABI was never probed.
- The `--link` signature cells compare compiler stdout from two failing links
  in different projects.

Retained observation, not CD-1: a dependency's diagnostic location. Under
`--link`, and under `--run` for the four-module shape, the uncached signature
diagnostic renders at `main.cl:1:1 … 0..0`. In the three-module `--run` cell,
`a.cl`'s span `69..74` renders as `main.cl:3:24`, which is byte 69 of the
entry file. This is a candidate wrong-file span and a candidate
`mode-divergence`. It stays unallocated until `spec` confirms whether a
dependency-failure location is normative.

Pending, in order:

1. `test` confirms the commit that carries the CD-1 correction (its F1 record
   names `94486f24`), then adds `fixed=S122/<sha>` and past-tense framing to
   the six CD-1 cells.
2. The F1 items under [F1 acceptance](#f1-acceptance-and-qr-classification-2026-09-25).
3. `arch` and the user dispose of the five measured QR kinds. QA records no
   acceptance on the user's behalf.

The `design`(backend) remaps B1–B5 are documents and comments only, and are
not evidence-bearing.

### Unverified evidence leads — candidates, not defects (2026-09-24)

Neither lead has an executed observation. Neither gates S122.

- **Panic-sentinel consumers** (`design/backend/backend.md` §7). Graded there
  as asserted with a named falsifier: a panic site's sentinel `0` reaching a
  heap dereference before the invocation returns. Plausible wrong outcome:
  a heap-typed callee panics and its caller dereferences the `0`, so the
  process faults instead of reporting and, in the REPL, surviving
  (`spec/12-runtime.md` §12.7.2). Proportionate next evidence, advisory and
  scheduled by `sprint` when convenient: `test` first checks whether
  `tests/spec_12_runtime.rs` already has a heap-consuming caller of a
  panicking callee; if not, one `PreludeVariant::None` probe in `--run` and
  the REPL. A RED becomes defect intake; a GREEN lets `design`(backend) cite
  it as a witness, not a proof for every consumer shape.
- **M3 ledger and DLL-side frees** (`.local/s122-platform-capture-doc-result.md`
  finding 3). An instrument-capability question, not a product defect.
  Source supports the concern: `design/intrinsics/diagnostic-modes.md` §3
  names intrinsics `alloc::dealloc` as the only free funnel, but platform
  `CLHeap::dec_rc` frees through the DLL's own `std::alloc::dealloc`,
  bypassing the host counters. If so, M3 would report correct capturing code
  as leaking and cannot serve as the capture-RC falsifier that
  `platform-dlls.md` §4 names as a candidate. No allocation now: nothing
  relies on M3 over a DLL-freeing workload. Before anyone upgrades that grade
  through M3, `test` runs one marginal pair differing only in extra calls to
  a capturing extern; a non-zero residual on correct code confirms the
  limit. `design`(intrinsics) owns the "only free funnel" wording.

### Deferred-record provenance — D1 triage (2026-09-24)

QA refutes the ABI-changing-parent/BROKEN-child trigger in the finding-scoped
review: the live-dependent guard rejects that turn before publication or
persistence. The recorded cross-module refusal tests pass. The specific
`super`-child edge is not separately executed.

A distinct macro-redefinition trigger remains plausible: a deferred child's
record is rebuilt at flush after an allowed macro edit advances a dependency's
stashed hash. QA holds acceptance of the deferral correction on one armed
REPL-to-restart cell and its non-deferred sibling control. The authoritative
requirement is [macro restart semantics](../../repl/spec/18-redefinition.md)
§18.4; the implementation contract is [dependency record validity](../../design/int/int.md)
§7.6. This is source-supported intake, not an observed defect.

Allocated to test: main declares kid; kid imports super/helper and mac/k, and
compiles helper plus k. Arm the child's deferred-write trace at startup, verify
the type-changing helper turn refuses, then switch to mac and change k's
expansion from1 to100. After quit, compare cached and no-cache batch runs:
expected107, suspected stale8. The matched control removes only the super
dependency (uses literal7), must not defer, and should give107 on both paths.
An unarmed run is not GREEN evidence. Tag a defect only after RED. If the
control also serves stale, reattribute rather than blaming deferral.

Execution update (2026-09-25): D1 is UNARMED, neither confirmed nor refuted.
In the legal observable shape, the parent deferred, not the child (12/12).
The super-import dependent correctly blocks the type-changing turn. Three
macro-edit probes showed the new expansion live but saved the old macro body;
the no-cache restart therefore also returns the old value. This extends
[ACT-0970](../../sprints/actions/ACT-0970-macro-redefinition-persistence-intake.md). The requested function control is
still owed. No permanent D1 test was added; the acceptance hold remains open.

### F1 and DV3 execution update (2026-09-25)

Test's two F1 guards are RED in two complete cache-target runs (56run,
54PASS/2FAIL). With main also importing b, the qualified-only cached a
returns99 where no-cache returns11 after a compatible insertion in b. With
main's import removed, the unchanged warm run fails resolving b's GOT; its
cold run succeeds. The six earlier CD-1 guards remain GREEN. The `arch`
reassessment (`.local/s122-callee-cache-reassessment-result.md`) attributes
both faces to missing consumption of the persisted `callees`, not to missing
information, and withdraws the `int.md` §7.6.1 carrier. Cell 2's
`enumeration-miss` class is ratified under
[remaining qualified-reference kinds](#remaining-qualified-reference-kinds--evidence-allocation-2026-09-25).

Both allocated DV3 shapes are GREEN: an edited test child imports a restored
declared child successfully, with and without a super import. The original
exemplar assertion lookup failure remains unreproduced outside its first
full-run observation; these smaller shapes do not establish its mechanism.

### Remaining qualified-reference kinds — evidence allocation (2026-09-25)

**Authority.** The governing requirements are these:

- `spec/08-modules.md` §8.5.4 edge 1: auto-load covers every position and
  symbol kind.
- The opening rule of [`int.md` §7.6](../../design/int/int.md#76-dependency-record-and-validity):
  a cached module restores only if every source it was derived from is
  unchanged.
- [Module caching §1 goals 1–2](../../design/backend/module-caching.md).

§7.6's "no carrier records it" and §7.6.1 are stale; `design`(int) owns that
repair. No new mechanism or semantics is approved.

**Question.** After the callee-consumption correction, does any other
qualified-reference kind still let a cached module restore stale, or fail to
load? Is the missing fact one that nothing records?

**Source reading** (QA, at `94486f24`; no build or run):

- `checker.rs::record_reference_target` adds a callee only for `Plain` and
  `TraitMethod` callables.
- `Ctor` (with its positional `tag`) and accessor origins record nothing.
  Type names, macro heads and mono-instance rechecks also record nothing
  (typecheck `CLAUDE.md`).
- A re-exported name records only its terminal home.
- `drop_glue_symbol_name` mints glue under the demanding module, so an
  importer holds its own glue for a foreign type.

**Construction rules for every cell:**

- **Placement.** Every cell goes in the F1 section of `tests/cache.rs`.
  Cells are stdlib-free, run under `--run`, and use the legs of
  `edit_after_warm_restore`:
  - cold oracle;
  - warm arming: `a` restores, and the warm run behaves as the cold run;
  - a `--no-cache` control on the edited sources, which leaves the cache
    untouched;
  - the cached run, compared with the control by exit code and stdout.

  `--run` alone suffices, for the reason given at CL-B.
- **No callable path into the module under test.** `a` has no callable
  reference into that module. Consuming `callees` therefore cannot add the
  module to `a`'s record, and a RED as built predicts a RED after that
  correction.
- **Edge-supplied sibling.** This leg runs before the subject.
  - The module under test defines an unused `(defn anchor [] 0)` in both
    versions.
  - The sibling differs from the subject only in that `a` adds
    `(import [<module> [anchor]])`.
  - Expected: GREEN. That result rules out every stale mechanism except the
    absence of the module from `a`'s edges. Keep the sibling as a permanent
    leg.

| Cell | Dependency fact | Fixture: `before` → `after`, edit only the named module | Oracle; prediction as built |
|---|---|---|---|
| QR-1 first-hop re-export | `callees` holds the terminal home, not the module the spelling names | `main` imports `[a [g]]` and `[c [f]]` (`c` is loaded only by this import). `a`: `(defn g [] (r/f))`. `r`: `(export [c [f]])` → `(export [d [f]])`. `c` defines `f` = 11; `d` defines `f` = 99 | 99; predicted 11 (the record gains `c` after the correction; `c` is unchanged) |
| QR-2 constructor tag, value and pattern | Constructor references record nothing; the tag is positional | `b`: `(deftype T Lo Hi)` → `(deftype T Hi Lo)`, each with `(defn mk-hi [] Hi)` and `(defn code [t] (match t [Lo 1 Hi 2]))`. `a`: `(defn make [] b/Hi)` and `(defn classify [t] (match t [b/Lo 1 b/Hi 2]))`. `main` imports `[a [make classify]]` and `[b [mk-hi code]]` and returns `classify(mk-hi) + 10 × code(make)` | 22; the face tells which positions are stale: 11 (both), 12 (value only), 21 (pattern only) |
| QR-3 dotted accessor | Accessor and dotted-member references record nothing | `b`: `(deftype Box [:Int v :Int w])` with `(defn mk [] (Box 11 99))` → `(deftype Box [:Int w :Int v])` with `(defn mk [] (Box 99 11))`. `a`: `(defn g [bx] (b/Box.v bx))`. `main` imports `[a [g]]` and `[b [mk]]` and returns `(g (mk))` | 11; predicted 99 |
| QR-4 type-only | Type names record nothing; `a` mints its own glue for `b/T` | `b`: `(deftype T [:Int n])` with `(defn mk [] (T 7))` → `(deftype T [:String s])`, with `mk` building a heap-allocated `String`. `a`: `(deftype W [:b/T inner])` and `(defn g [:b/T t] :Int (match (W t) [(W _) 7]))`. `main` imports `[a [g]]` and `[b [mk]]` and returns `(g (mk))` | Exit 7 on both paths. The observable is the `[RC_STATS]` `allocs`/`deallocs` pair: predicted one fewer dealloc on the cached run |
| QR-5 qualified macro head | A macro use is not a callee, and a literal expansion names nothing in `b` | `b` defines a macro `m` whose expansion changes from 11 to 99 (shape of `s76_macro_availability::fq_macro_reference_expands_without_import`). `a`: `(defn g [] (b/m))`. `main` imports only `[a [g]]` | 99; predicted 11 |
| QR-6 constructor-only home, never loaded | Restore loads only edge targets | `d`: `(deftype K [:Int n])`. `a`: `(defn g [] (match (d/K 7) [(d/K n) n]))`. `main` imports only `[a [g]]`. The warm run is the observation and no edit is needed | Cold 7. Warm: unknown, and RED only if `a.o` binds something of `d` (the F1 cell 2 face). Run the sibling only if RED |

**Limits on individual legs:**

- **QR-2 and QR-3.** Use nullary constructors and scalar fields only. A stale
  tag or offset then produces a wrong value and never a payload read. Do not
  probe the memory-safety consequence: a wrong value already establishes the
  defect.
- **QR-4, edit direction.** Edit in the direction `Int` → `String` only. Stale
  glue then under-releases. The reverse direction would release an `Int` as a
  pointer.
- **QR-4, instrumentation.**
  - Set `CRANELISP_RC_STATS=1` on every run, cold included, so every object
    is compiled under the same codegen gate.
  - The assertion is a pair that differs only in cache use, which satisfies
    the marginal rule in `tests/CLAUDE.md`. Use no absolute balance and no
    threshold.
- **QR-4, arming.** Two more checks apply:
  - the warm unchanged counts equal the cold counts;
  - the edited control allocates more than the unedited program, which proves
    the `String` is a real allocation.
- **QR-4, credit limit.** A GREEN protects nothing unless `a` releases the
  value. QA credits no QR-4 GREEN as protection.
- **QR-5.** Invalidate through source-file edits only.
  [ACT-0970](../../sprints/actions/ACT-0970-macro-redefinition-persistence-intake.md)
  and the D1 hold remain separate.

**Leads held for `spec`; no cell until the user rules.** `sprint` routes each
question.

- **Mount-alias first hop.** Take `r.cc/f` written in a module that does not
  import `r`. §8.4.4 describes only downstream importers. §8.5.4 edge 2 and
  §8.6.6 step 2 do not settle whether an unloaded prefix module is
  auto-loaded.
- **Instance-mediated implementation dispatch.** This is `arch` falsifier 4.
  §5.11.1 makes an implementation visible through the import closure, and
  §8.5.4 edge 10 says auto-load is not an import. Neither says whether a
  qualified-only `d/K` brings `d`'s implementations into scope.
  - If the ruling is "no", the current acceptance becomes wrong-accept
    intake, not a cache observation.
  - If the ruling is "yes", QA allocates the cell.

**Classification after execution:**

- **RED with the sibling GREEN.**
  - Validity face: `class=artifact-underkey locus=src/cache/dependency_record.rs::ModuleEdges`.
  - Load face: `class=enumeration-miss locus=src/process_form/cache_restore.rs::try_cache_hit_load`.
    The restore walk is a reach-set enumeration that omits a module the
    restored object binds. That ratifies F1 cell 2's class.
  - Both take `found=S122 owner=/dev`.
- **RED with the sibling also RED.** The mechanism is unattributed. Tag the
  face class, add a comment that names the unknown, and return the case to QA.
- **GREEN with the arming legs passing.** Keep the cell as a guard without
  `// defect:` and report it as GREEN.
- **Cold failure or an unarmable fixture.** This is not a cache observation.
  A spec-valid program that fails fresh is §8.5.4 intake: keep the minimal
  shape and report it. Do not force a result.

Trace every cell with
`// spec: design/int/int.md §7.6 — Dependency record and validity (<kind>; spec/08-modules.md §8.5.4 edge 1)`.

### F1 acceptance and QR classification (2026-09-25)

QA read the `design`, `dev`, `review` and `test` F1 results, their logs, and
the changed restore and record source. QA ran no build or test and edited no
test.

**Verdict: F1 is adequate as a bounded correction for qualified callable
references.** It does not close CD-1 or the cache-dependency class. `int.md`
§7.6 *Known gaps* 1 (the QR kinds) and 2–7 stay open.

| Condition | Class | Executed evidence | Judgment |
|---|---|---|---|
| F1 cell 1: validity (`artifact-underkey`) | Acceptance | RED for the intended reason in two runs: cached 99, uncached 11, arming GREEN. GREEN on the delivered source in `dev`'s full run and `test`'s cache-target run, with no assertion changed | Adequate |
| F1 cell 2: restore load (`enumeration-miss`) | Acceptance | RED for the intended reason: cold 11, then the unchanged warm run failed with `unresolved symbol: __cranelisp_got_b`. GREEN in the same two runs | Adequate; the only measurement of the restore walk |
| Callee-module set and index edges | Acceptance (module) | Four units RED → GREEN: every callable kind in both lives, a closure member linked only by a callee, `Unsettled` for an unloaded callee module, and an index edge from a real typecheck. Two preservation units GREEN before and after | Adequate. Limit: the decoded-table unit was never observed RED; F1 cell 2 measures that read end to end |
| No regression | Safety fence | Full suite: 6067 run, 6058 PASS, 9 FAIL, which is the before-set of 11 minus the two F1 cells. The `cache_dep_*`, restored-chain, DV3 and QR-6 cells and the `redefine` blocking units are GREEN | Adequate |
| Private boundary | Maintenance | No change to `crates/*/src` or `public-api.txt` against `293534ee`; new visibility is `pub(crate)`. `cargo check` and `--tests` are zero-warning | Adequate. Limit: no new clippy lint is graded by inspection of the changed sites, because no count exists at `293534ee`. That bears on the `dev` release gate, not on F1 behaviour |

`dev`'s two cache-target runs predate its final `cache_restore.rs` edit and
the module rename. The delivered source therefore has two cache observations:
`dev`'s full run and `test`'s run. `test`'s run kept the fail set, panic sites
and face values, but not per-leg output, so per-leg results rest on `dev`'s
full run over the same source.

**Residual: `callees` completeness.** It now gates cache validity and restore,
so a callable reference that typecheck does not record is served stale.

- Covered: every callable kind and life at the unit tier, and a direct
  monomorphic qualified call end to end. The QR cells measure the kinds
  `callees` does not carry.
- Asserted only: a qualified trait-method callee and a qualified call inside a
  generic template. The template life records the call, and the closure is
  transitive through `a`. Falsifier: either shape in `a` whose cached importer
  differs from `--run --no-cache` after an edit to `b`. It is not allocated,
  because no source reading shows an omission and the cell would add little to
  the unit matrix. Instance-mediated dispatch stays held for `spec` (above).

**Review advisory 1.**

- **Null-import target that is also a callee.** §7.6.1 requires the module to
  load. Source satisfies it: the callee walk applies no import filter, and the
  validity record already counts null imports as edges, so the exposure is a
  loud warm-run load failure, not stale service. The shape is ordinary. An
  alias-only import (`spec/08-modules.md` §8.3.6, for qualified access) is an
  `ImportNames::None` spec, which both import walks skip, so only the callee
  walk restores its target. F1 cell 2 cannot detect a later change that
  applies the import skip to callee modules, because its `a` has no import
  spec. One cheap cell earns its cost: FN-1.
- **Callee cycle.** Not allocated. Mutual imports are a compile-time cycle
  error, and whether mutual qualified-only calls compile fresh is unestablished.
  Establishing that is §8.5.4 fresh-path intake outside F1. Restore
  termination rests on the installed-module check that every restore
  dependency step and declared-child enrolment share. Falsifier: a cold-valid
  pair, `a` calling `b/f` and `b` calling `a/g`, whose warm run fails to
  terminate or differs from the cold run.

| ID | Class | Evidence | Expected and limits |
|---|---|---|---|
| FN-1: an alias-only import target reached by a qualified call restores | Safety fence for the §7.6.1 null-import rule. **Armed** | `test`'s cell `cache_alias_only_import_target_reached_by_qualified_call_restores_and_matches_uncached_run` in the F1 section of `tests/cache.rs`. It is F1 cell 2 with `a` replaced by `(import [(b bb) []])` and `(defn g [] (bb/f))`. Legs as cell 2: cold 11; warm arming hits `a` (trace-asserted) and behaves as cold, which is the discriminating leg; the `--no-cache` control gives 11 after the edit; the cached run matches the control | GREEN on every leg since the alias-only correction, in `dev`'s focused run and in the full run (`.local/s122-io-notice-dev-full.log`). A warm `unresolved symbol: __cranelisp_got_b` is F1 defect intake and reopens this acceptance. No planted-fault proof is owed: the warm leg's detection is its asserted restore of `a` plus an exit comparison with the cold run, and F1 cell 2 observed exactly that failure face RED before the F1 fix. Limit: FN-1's own warm failure face is predicted, not observed |

FN-1 does not gate F1 acceptance. Source establishes present conformance, and
the fence protects later change.

**QR classification: measured.** QR-1 to QR-5 are RED with unchanged faces
under callee consumption in all four runs. Every panic is at the subject's
final cached-versus-uncached comparison (for QR-4, the `(allocs, deallocs)`
pair), so each edge-supplied sibling, arming leg and control passed. Each is therefore **RED with the sibling GREEN**, with a
validity face (`artifact-underkey`, `ModuleEdges`). QA's prediction stands
unrefuted.

- **Measured.** After `callees` is consumed, the module that a re-export first
  hop, constructor, accessor, type-only or macro-head reference depends on is
  still absent from the importer's dependency record, and restore serves the
  stale object. For QR-1 the absent member is the spelled re-exporter `r`; the
  terminal home `c` is now recorded.
- The approved carrier and its evidence are
  [qualified lookup dependencies](#qualified-lookup-dependencies--evidence-delta-2026-09-26).
- QR-4 remains a memory-safety exposure: the stale importer under-releases.
- QR-6 is GREEN: a constructor-only home that the object does not bind
  restores.
- Outside F1 and unchanged by it:
  `fq_type_only_reference_loads_its_module_on_a_fresh_compile` (a cold
  `wrong-reject`; [allocation](#fresh-fq-type-only-loading--evidence-delta-2026-09-25)).

**F1 items still open, none an evidence gate:**

1. The two F1 `fixed=S122` stamps are true only if they land with the `src/`
   correction. If that correction commits separately, `test` appends `/<sha>`.
2. `design`(int) marks F1 accepted in `int.md` §7.6.1 and §16.0 and in the
   `s122-closure.md` row.
3. `test` stamps the FN-1 cell `fixed=S122/bc675d86` and restates it as the
   armed fence ([alias-only correction](#alias-only-import-registration-fixme-0798--correction-adequacy-2026-09-25)).
4. The user accepts what ships at the Phase-5 checkpoint.

### Alias-only import registration (FIXME 0798) — correction adequacy (2026-09-25)

**Requirement** (unambiguous; no user ruling): `spec/08-modules.md` §8.3.6
registers the alias for qualified access; §8.6.6 step 1 resolves through it;
§8.5.4 loads the unloaded target. §8.3.7's no-loading rule governs only the
alias-less `[m []]`. Eager or lazy loading of the alias target is unspecified
and not pinned.

**Attribution: confirmed at the seam.** `handle_import`'s `ImportNames::None`
arm returned before the only fresh-path import-alias writer ran. `test`'s
executed controls refute the widened locus (an explicit-name alias resolves,
so 0798's S115 row 2 is not live) and exclude load order (the alias-only form
fails with `b` already loaded). `dev`'s Pass-0 module witness observed no alias
registered before the fix. Class `wrong-reject`; locus
`src/process_form/dependency.rs::handle_import`.

**Correction** (`bc675d86`, private to `src/`): one import-alias writer,
`imports.rs::install_import_alias`, serves the named, name-less and restore
routes; the name-less arm registers the alias and still loads nothing.

| Condition | Class | Evidence | Judgment |
|---|---|---|---|
| Alias-only alias resolves a qualified call, whether or not the target is loaded | Acceptance | `tests/spec_08_modules.rs::alias_only_import_alias_resolves_qualified_call` (explicit-name control first; two subjects). RED for the intended face before the fix, GREEN after | Adequate |
| Registration without loading | Acceptance (module) | `process_form::tests::alias_only_import_registers_alias_without_loading`, keyed by the public `module_alias_key`. RED before, GREEN after | Adequate |
| Plain null import registers nothing and loads nothing (§8.3.7) | Safety fence | `null_import_does_not_load_its_module` (named-import control over a broken `b`) and `null_import_registers_no_alias_and_loads_nothing`. GREEN before and after | Adequate; never RED because no fault existed |
| No blanket qualifier acceptance | Safety fence | `undeclared_alias_qualifier_is_not_resolved_neg`. GREEN before and after | Adequate |
| Restore path parity | Safety fence | FN-1 (above), GREEN on every leg | Adequate |
| No regression | Safety fence | Full run over the committed Rust sources (all mtimes precede the run's end): 6079 run, 6071 passed, 8 failed. The failures are the five QR cells, the two fresh type-only cells and the since-repaired `citation_drift` citations | Adequate |

Independent `review`(src) passed the source with no blocking or required
source finding (`.local/s122-alias-review-result.md`).

**Verdict: adequate.** Limits, none gating:

- REPL and `--link` are not observed. All modes reach the same
  `handle_import`, so mode parity is structural, not measured.
- No cell asserts that an alias-only import binds no bare name. The arm
  returns before any binding is written.
- The alias key is still minted by the private `alias_key` (`int.md` §16.0
  residue, owned by `design`(int)).

**0798 disposition** (for its target role): asks 1 and 3 and the repair are
delivered. Ask 2's matrix reduces to what the single writer does not make
structural: the type-annotation column `:u/T`, allocated with
[fresh FQ type-only loading](#fresh-fq-type-only-loading--evidence-delta-2026-09-25),
and the bare-submodule alias target (lead R-A3 below). Nothing else
remains for 0798 to carry.

#### Review leads — candidates, not defects

Source readings from the alias review, none executed, none introduced by the
correction and none gating. Each needs `sprint` scheduling with the user
before any cell is written; a RED becomes defect intake.

- **R-A1 — qualified reference into a private submodule** (§8.2.3: other
  modules "MUST NOT … reference names in a private submodule"). Neither the
  name-less arm nor `drive_module_dep` appears to check §8.2.3; a direct
  `p.priv/f` seems to take the same route, so the alias adds a spelling, not a
  capability. Smallest probe: `p` declares `(mod- priv)`; a peer calls
  `(p.priv/f)` and must be rejected; control: `p` itself calls it and runs.
- **R-A2 — duplicate import alias overwrites** (§8.6.4: two import aliases
  binding one local alias "remain compile-time errors"). The writer is a plain
  insert, as it was before. Probe: `(import [(b u) [f]])` then
  `(import [(c u) [g]])` must be rejected; control: distinct aliases run.
- **R-A3 — bare-submodule alias target** (§8.11.2.1). The alias target is
  recorded as written, while the named-import bindings resolve
  current-module-relative. Probe: in `main` with `main/util.cl`,
  `(import [(util u) [f]])` then `(u/f)`; a top-level `util.cl` with a
  different `f` turns a wrong target into a wrong value. Control: the full
  path `(main.util u)`.
- **Run-dependent dependency-failure wrapping.** The same fixture
  (`fq_type_only_reference_loads_its_module_on_a_fresh_compile`) reported
  either the chained form (`module 'main' failed: … dependency 'a' failed`) or
  the direct form (`module 'a' failed`, with `a.cl`'s span 28..52 rendered as
  `main.cl:1:29`) across three runs. Both name the failed module and its
  error, so §8.5.4 edge 5 holds as far as observed; the span joins the
  retained dependency-location observation held for `spec`. Not allocated.

### Fresh FQ type-only loading — evidence delta (2026-09-25)

**Authority.** `spec/08-modules.md` §8.5.4 edge 1: a fully-qualified type
name in an annotation participates in auto-load, and an unresolved FQ type is
a resolution-layer `Type` gap. Edge 2 applies registered aliases; edge 3
makes a missing file a located error. Design guard: the public
`ResolutionGap::Type` contract, which int already consumes
(`process_form::tests::gap_target_module_type_names_module`). The approved
correction is a private typecheck producer; no API or schema change
(`.local/s122-remaining-arch-result.md` A2).

**Attribution: the typecheck producer, `wrong-reject`.** `test`'s executed
controls show that loading `b` by an import or by any value reference makes
the same annotation resolve, and the face is the `QualifiedModuleUnknown`
display raised as a type error. `design`(typecheck) confirmed from source that
only the value path records the pending gap that `lift_error` promotes
(`.local/s122-fq-type-design-result.md`). The seam observation is unit row 1's
pre-fix RED. Falsifier: if that row shows the checker already returns the
`Type` gap, the loss is in int's lift or consumer and the locus moves to
`src/`.

**Coverage miss.** `spec_08_modules::fq_type_annotation_triggers_autoload`
claims the type trigger, but its body also references `shapes/Circle.r` and
`(shapes/Circle 9)` in value positions, which load `shapes` on their own. It
passed a non-conforming build. The one-module cell below isolates the type
trigger.

| ID | Condition; plausible wrong outcome | Class | Evidence | State |
|---|---|---|---|---|
| FT-1 | A `defn` parameter annotation `:b/T` alone loads `b` (exit 7); wrong: the "not loaded" type error | Acceptance | `spec_08_modules::fq_type_annotation_alone_loads_its_module`, named-import control first | RED before the fix (`test` log); GREEN in the integrated full run |
| FT-2 | In a dependency module, a `deftype` field and a parameter annotation each load `b`; wrong: one entry route still refuses | Acceptance | `cache::fq_type_only_reference_loads_its_module_on_a_fresh_compile` | As FT-1 |
| FT-3 | Through an alias-only import, `:bb/T` loads the alias target; wrong: the gap carries the spelled `bb` (`module 'bb' … not found`) | Acceptance | `spec_08_modules::fq_type_annotation_through_alias_only_import_loads_its_target`: control `(import [(b bb) [mk]])`, subject `(import [(b bb) []])`, each exit 7 | Subject RED before the fix, control GREEN; both GREEN in the integrated full run |
| FT-4 | An annotation in the entry module naming a module with no file is rejected at the reference site (§8.5.4 edge 3), naming the module, and terminates; wrong: silent acceptance of an unused function's annotation, a retry loop, or an unlocated (`at 0..0`) rejection | Safety fence | `spec_08_modules::fq_type_annotation_to_missing_module_errors_at_reference_site_neg`: `(defn h [:zz/T t] :Int 7)`, `:Int` control exit 7; subject non-zero, names `zz`, no `at 0..0`, within the default timeout | Location leg RED after the typecheck fix alone (`at 0..0`), as predicted; GREEN on every leg with the int reference-site repair, in the integrated full run |
| FT-U | The producer reports the gap only for an absent module, through the one projection | Acceptance (module) | `dev` unit rows below | Rows 1–3 and 6 RED before, all GREEN after; the negative legs failed under a planted record-every-failure fault. Observed in session, no log file |
| FT-L | The reference-site walk locates a gap under either spelling of its module: the written qualifier (a member-absent gap) and its alias substitution (an absent-module or `Type` gap); wrong: an alias-spelled member-absent reference reported `at 0..0` (review R1) | Acceptance (module) | `dev`(src) rows in `src/process_form/tests.rs`: `gap_reference_span_locates_alias_spelled_member_absent_value_gap` (the written leg), `gap_reference_span_resolves_alias_qualifier_for_type_and_value` (the substituted leg), and the two `…_neg_…` rows | R1 row RED before its fix (`left: ""`), GREEN after; planted faults detected by the impl-method-body, `Fn`-carrier and trait-reference rows. Logs in `.local/s122-fq-span-r1-dev-evidence/`; finding-scoped review passed |

**FT-4 location.** A `Type` gap reaches int with no span, so FT-4's location
depends on int's reference-site walk
([`int.md` §6.3.1](../../design/int/int.md#631-locating-a-gap-at-its-reference-site)),
which FT-L pins at the unit layer. FT-L has no e2e: the e2e shape for the
written leg reaches lead H1's load decision before any location is reported
([open leads](#open-leads-from-the-loading-group--candidates-not-defects)).
Revisit the e2e need when H1 is attributed.

**`dev` unit obligation** ([`typecheck.md` §7.3.1](../../design/typecheck/typecheck.md)),
beside `gap_on_missing_module_plain` in `form/tests.rs` unless noted. Rows 1–3
and 6 must be observed RED before the fix:

1. A `defn` parameter annotation `:some.mod/T`, with `some.mod` absent, returns
   `Gap(Type)` naming `some.mod` and `T`.
2. The same for a `deftype` field (the ADT route and its `&CheckState`
   threading).
3. Beside `gap_on_missing_module_via_alias`: `:r/T` with alias
   `r → real.target` and `real.target` absent; the gap names `real.target`.
4. Negative: `some.mod` present without `T` is a type error, not a gap.
5. `checker/tests.rs`, the projection: `QualifiedModuleUnknown` records
   `Type(module/name)`; `TypeNotFound`, `PrivateInaccessible` and `Ambiguous`
   record nothing; every returned error equals today's conversion.
6. An impl whose target type is `some.mod/T`, with `some.mod` absent, returns
   the same gap. The impl-target lookups return the same private failure, so
   this route is structural too; the row is its regression guard and the
   evidence that an impl head keeps its qualifier.

The projection is structural for every caller of the type-expression entries
and impl-target lookups: a bypassing `?` does not compile. A caller that
discards the type failure to try a trait reading is outside it; the two
annotation routes that do so now share one resolving step, evidenced
separately under
[annotation trait fallbacks](#annotation-trait-fallbacks-f-a-f-b--intake-and-allocation-2026-09-25).

**Completion criteria:**

- Pre-fix REDs are recorded for FT-1, FT-2, FT-3's subject, FT-4's location
  leg, unit rows 1–3 and 6 and the FT-L R1 row. Met.
- FT-1 to FT-4, FT-U, FT-L, every control and
  `fq_type_annotation_triggers_autoload` are GREEN. Met in the integrated
  full run.
- `cargo nextest run --no-fail-fast` fails only the five QR cells, and
  `public_api_relocations` passes with no `public-api.txt` changed. Met.
- The `dev` release gate is met for `cranelisp-typecheck` and `cranelisp`,
  and `review` of each touched surface reports no blocking finding. Met for
  both FT surfaces.
- After the commit: `test` appends `fixed=S122/<sha>` (handoffs below).

**`test` record handoffs.** Apply the tense corrections now; the stamps wait
for the commit (`<sha>` is that commit). Keep every `locus=` token as written.

- `tests/spec_08_modules.rs`, `fq_type_annotation_alone_loads_its_module`:
  - now: replace "The subject fails with the type error … nothing turns the
    unloaded type home into a load." with "Before the S122 correction the
    subject failed with the type error "module `b` referenced by `b/T` is not
    loaded", not the loader's module-not-found error: nothing turned the
    unloaded type home into a load."; delete "Which layer should is not
    attributed.";
  - after the commit: append ` fixed=S122/<sha>` to the `// defect:` line.
- `tests/spec_08_modules.rs`,
  `fq_type_annotation_through_alias_only_import_loads_its_target`:
  - now: "a gap that names the spelled `bb` instead of `b` fails as an unknown
    module `bb`" is a conditional wrong outcome and stays; "(§8.3.6)" is
    correct (alias-only import);
  - after the commit: append ` fixed=S122/<sha>`.
- `tests/cache.rs`, `fq_type_only_reference_loads_its_module_on_a_fresh_compile`:
  - now: "compiled fresh, the program is rejected with …" becomes "compiled
    fresh before the S122 correction, the program was rejected with …";
    "makes it compile" becomes "made it compile"; delete "The locus is
    provisional: which layer should turn the unloaded type home into a load
    is not yet attributed.";
  - after the commit: append ` fixed=S122/<sha>`.
- The FA-1 and FB-1 handoffs are with
  [their section](#annotation-trait-fallbacks-f-a-f-b--intake-and-allocation-2026-09-25).
- `tests/spec_08_modules.rs` null-import assertion messages in
  `null_import_module_resolves_all_names_via_explicit_imports` and
  `null_import_module_neg_unimported_name_is_undefined`: "spec §8.3.6" becomes
  "spec §8.3.7", matching their `// spec:` lines (the banner is already
  corrected).

**Owning record.** The REDs trace to this section and the user-approved S122
loading group. No action is needed while S122 carries the fix; a carry past
close needs one.

**Limits, not allocated:**

- REPL and `--link`: every mode reaches the same typecheck producer and int
  consumer. The agent validator and the generic worker translation render any
  gap as text (`worker.rs`), as they already do for value references.
- A type reference to a present but non-terminal module (spec §8.5.4 edges
  6–7; open item in `typecheck.md` §11). Not exercised by this correction.
- Warm restore of a type-only importer, reachable once it compiles fresh. Its
  object binds nothing of `b`, whose glue it mints itself, and QR-6's
  constructor-only analogue restores GREEN. Falsifier: an unchanged warm run
  of the FT-2 fixture that fails or differs from the cold run. Staleness after
  an edit to `b` is QR-4 under
  [qualified lookup dependencies](#qualified-lookup-dependencies--evidence-delta-2026-09-26).

#### Annotation trait fallbacks (F-a, F-b) — intake and allocation (2026-09-25)

**Authority; no normative question.** A single annotation name is a type if a
type candidate exists, otherwise a trait (§3.9.3). Qualified names resolve in
the named module, auto-loading it first (§8.6.1); an unknown module is a
compile-time error (§8.6.6 step 5), located at the reference when no file
exists (§8.5.4 edge 3). The obligation to load depends only on the module
being unloaded, not on the kind the name turns out to have, which can only be
known after loading. Both defects violate these rules under any reading of
edge 1's list of kinds, so no `spec` ruling is needed.

**Mechanism: confirmed.** Before the correction both trait fallbacks ran
after the type attempt failed and took `tref.module` as the trait home as
written, with no §8.6.6 resolution. The value route (`infer_annotate`) did so
directly; the parameter route did so after `register_defn_signature` gated
the fallback on the **bare** name resolving as a trait. The FA-1 and FB-1
controls discriminate it: adding a same-spelled bare `Tr` turns FB-1's
located unknown-module rejection into an acceptance. The correction is one
crate-private step, `checker.rs::resolve_annotation_trait`, that both routes
call, and it resolves the reference as written through `resolve_trait`
([`typecheck.md` §7.3.2](../../design/typecheck/typecheck.md#732-type-or-trait-annotations)).
No public API, `ResolutionGap` or schema changed.

| ID | Condition; plausible wrong outcome | Class | Evidence | State |
|---|---|---|---|---|
| FA-1 | A value annotation `:zz/T t`, with no `zz.cl`, is rejected, names `zz` and is located (§8.5.4 edges 1 and 3; §8.6.6 step 5); a value annotation `:b/Tr t` naming a trait in an unloaded, present `b` is accepted (§3.9.3). Wrong: the first is accepted (F-a); a fix rejects the second or forces the type reading | Acceptance; defect repro `class=wrong-accept locus=crates/cranelisp-typecheck/src/infer.rs::infer_annotate found=S122 owner=/dev` | `spec_08_modules::fq_value_annotation_neg_missing_module_rejected_unloaded_trait_accepted`: control `:Int`, exit 7; subject A `:zz/T`, non-zero, names `zz`, no `at 0..0`; subject B `:b/Tr` with `b` not imported, exit 7 | Subject A RED before the fix (accepted, exit 7), control and subject B GREEN (`.local/s122-annotation-fallback-test-run1.log`); every leg GREEN in the integrated full run. The location leg discriminates only once subject A is rejected |
| FB-1 | A parameter annotation's qualified trait resolves in the named module (§8.6.1, §3.9.3). Wrong: a same-spelled bare trait captures `:zz/Tr` so a missing module is accepted, or a trait reachable only by qualification is rejected | Acceptance; defect repro `class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/program/register.rs::register_defn_signature found=S122 owner=/dev` | `spec_08_modules::fq_param_trait_annotation_resolves_in_named_module_neg_not_captured_by_bare_trait`: subject 1 adds a local `Tr` to control 1 (`:zz/Tr`, no `zz.cl`), both rejected naming `zz`; subject 2 omits control 2's `(import [b [Tr]])` from `:b/Tr`, both exit 7 | Subject 1 RED (accepted) and subject 2 RED (``unknown type `Tr` (from module `b`)``) before the fix, both controls GREEN, as predicted (same log); every leg GREEN in the integrated full run |
| FU | The shared step takes the trait reading only when the reference resolves as a trait, at its canonical home; otherwise the type failure is the form's failure | Acceptance (module) | `dev` cells U1–U6 in `crates/cranelisp-typecheck/src/form/tests.rs` (`type_or_trait_*`; table in `typecheck.md` §7.3.2): absent module gaps on both routes (U1, U2), qualified and alias-spelled traits resolve at the target home (U3–U5), a present module without the member is a type error, neither a gap nor an acceptance (U6) | All six RED before the fix (`.local/s122-annotation-fallback-dev-prefix-units.log`), GREEN after (`…-postfix-units.log`). U6 was predicted GREEN; it was RED because the unresolved-home fallback also accepted `:b/X` for a present `b` without `X`. The same correction repairs it, and U6 is its discriminating cell |

- **Layer.** FA-1 and FB-1 are the permanent e2e guards, because the defects
  are observable end to end on the edge-1 contract FT-4 fences; FU pins the
  shared step. U6's face needs no e2e: with `b` loaded, no gap or int
  consumer is involved and the unit cell observes the whole failure. With `b`
  present but unloaded, the path is the load-and-retry FA-1 subject B
  exercises followed by U6's check; that composition is not observed end to
  end. REPL and `--link` stay unallocated for the reason given for FT-1 to
  FT-4.
- **Detection sequence.** An executed RED for the predicted reason, logged
  before the fix, establishes each cell; the test and the fix land in one
  change-set (root `CLAUDE.md` §Testing). A separate RED-only commit is not
  required.
- **Scope.** Trait-only positions, a renamed trait import and the other
  [open leads](#open-leads-from-the-loading-group--candidates-not-defects)
  are outside this correction.

**`test` record handoffs.** Apply once the change-set is committed (`<sha>`
is that commit); keep every `locus=` token as written. The FA-1 and FB-1
comments carry no present-tense failure, so nothing changes before then.

- `fq_value_annotation_neg_missing_module_rejected_unloaded_trait_accepted`
  and
  `fq_param_trait_annotation_resolves_in_named_module_neg_not_captured_by_bare_trait`:
  append ` fixed=S122/<sha>` to each `// defect:` line.

#### Open leads from the loading group — candidates, not defects

None is executed, allocated or accepted as a residual. Each becomes intake when
a failing cell of its shape exists; scheduling a cell is `sprint`'s.

- **H1 — member-absent load decision follows the written qualifier.** With
  alias `z → zz`, `zz` loaded and lacking `f`, `(z/f 1)` records
  `SymbolTypechecked(z/f)`; int then drives a module named `z` instead of
  reporting "module 'zz' has no member 'f'" (§8.5.4 edge 4; §8.6.6 step 1).
  Source-derived by `design`(int); candidate owners are the typecheck
  producer's member-absent arm and int's gap arm. FT-L's e2e waits on it.
- **Child-probe gap after a private absolute hit.** When the absolute probe
  returns `PrivateInaccessible`, `lookup` surfaces the child probe's gap for
  `<current>.<qualifier>`; neither spelling matches it, so the location is
  `SYNTHETIC`. Whether the reported error is edge 9's private-access error is
  unexecuted.
- **Qualified trait in an impl trait or constraint slot** naming an unloaded
  module. §8.6.1 requires the load for every kind of name. The impl
  constraint slot returns a located error with no gap. The stacked-bound
  position is a confirmed defect under
  [lookup leads](#source-read-lookup-leads--classification-2026-09-26). The as-written
  trait spelling is now composed in two places (`impl_check.rs` and
  `resolve_annotation_trait`), with `resolve_bound_param` a third reader
  ([`typecheck.md` §11](../../design/typecheck/typecheck.md#11-open-design-items)).
- **Trait through a renamed import** (`spec/08-modules.md` §8.3.5). Both
  type-or-trait routes and the bare arm of `resolve_bound_param` pair the
  resolved home with the spelled name, an identity that may not exist; recorded
  in the same `typecheck.md` open items.
- **A-1 — HKT impl heads drop the qualifier** in the primitive-name check and
  the arity kind-check (`traits/impl_check.rs`); wrong outcome: a kind check
  against a same-named local type, or none (`typecheck.md` §7.3.1).
- **A-3 — the two type resolvers name an intrinsic differently**; no
  divergence found (`typecheck.md` §7.3.1).
- **Module maintenance, not QA leads:** typecheck review A-2 and A-4, and
  the fallback review's A-1 (U6 asserts the `TypeError` variant, which
  discriminates, but not the location or member name its name promises), for
  `dev`(typecheck); int re-review A4 and A5 (two `src/process_form/tests.rs`
  comments that still state the substituted-only match rule) for the next
  `dev`(src) visit.

#### Adequacy (2026-09-25)

Evidence is judged on the uncommitted tree. The integrated full run
(`.local/s122-annotation-fallback-dev-full.log`, started after the last source
change) ran 6103 tests: 6098 passed and 5 failed, the five QR cells only.
`public_api_relocations` passed and no `public-api.txt` changed.

| Condition | Judgment |
|---|---|
| FT-1 to FT-4, FT-U, FT-L | Adequate. Pre-fix REDs are logged, every leg is GREEN in the full run, and the typecheck review and the int finding-scoped re-review report no blocking finding |
| FA-1, FB-1, FU | Adequate. Pre-fix REDs are logged, every leg is GREEN in the full run, and `review`(typecheck) passed the shared step with no blocking finding |
| No regression | Adequate: only the five QR cells fail |
| §8.5.4 edge 1 for annotations | Evidenced for parameter, `deftype`-field and value annotations, including alias-only spellings and qualified traits in the two type-or-trait routes. Not evidenced for trait-only positions (open lead) |

## REPL execution notice for `IO` expressions — evidence delta (2026-09-25)

**Authority.** [`repl/spec/01-display-format.md` §1.2.1](../../repl/spec/01-display-format.md#121-io-expression-results):
the REPL executes an `IO a` expression automatically. It prints the exact line
`Executing IO…`, then the action's platform output, then the payload under
`a`. A non-`IO` expression prints no notice. Batch output never contains it.
[`spec/10-io.md` §10.6.2](../../spec/10-io.md) and the `IO` row of
[`spec/12-runtime.md` §12.9.1](../../spec/12-runtime.md) defer to that REPL
requirement.
[`repl/spec/03-slash-commands.md` §3.7](../../repl/spec/03-slash-commands.md)
applies the same order to `/mem <expr>`. This requirement supersedes the
`IO` envelope display; its conditions and cells are retired.

**Design guard.** [`design/int/io-integration.md`](../../design/int/io-integration.md)
§1.1: one site in `pipeline::execute_compiled_expr`. From the same `is_io`
that selects forcing, the notice is written to process stdout and flushed
before `cranelisp_run_program`. `--run` and `--link` do not reach that site.
The "stdout" and "flushed" parts of the conditions below trace to this guard,
not to the spec.

| Id | Cell | Observable | Plausible wrong outcome discriminated | Class |
|---|---|---|---|---|
| IOT-1 | `tests/spec_10_io.rs::repl_pure_int_result_prints_io_notice_then_payload` | `(Pure 42)`: exactly one notice line, then `:primitives/Int 42`; neither `primitives/IO` nor `IO.Pure` | No notice; notice after the payload or on the payload line; ASCII `...`; envelope display | Acceptance |
| IOT-2 | `…::repl_pure_string_result_prints_io_notice_then_payload` | `(Pure "hello")`: notice, then `:primitives/String "hello"` | The heap payload path diverges | Acceptance |
| IOT-3 | `…::repl_bind_pure_lambda_result_prints_io_notice_then_payload_without_double_free` | `(bind (Pure 42) (fn [x] (Pure x)))`: notice, then `:primitives/Int 42` | Notice keyed on a literal `(Pure …)` form rather than the type; the S61 double free | Acceptance |
| IOT-4 | `…::repl_io_notice_precedes_effect_output_neg_not_on_pure_defn_or_lookup_turns` | One `PrimitivesOnly` session with the stdio platform: a pure call, a `defn` whose body prints, the bare name `print`, then `(print "iot-probe")`. Exactly one notice; `:primitives/Int 3` < notice < `iot-probe` < `:primitives/Int 0`; `iot-never` absent | Notice written after execution or unflushed; notice on a pure, definition or lookup turn; notice keyed on a displayed type that mentions `IO`; duplicated notice; no effect | Acceptance (positive and negative) |
| IOT-5 | `tests/repl_introspection.rs::mem_with_io_expr_prints_notice_then_payload_then_delta` | `/mem (Pure 42)`: one notice < `:primitives/Int 42` < the `; delta:` line | `/mem` bypasses the notice site; delta before the payload | Acceptance |
| IOT-B | `tests/output_equivalence.rs`, all cells | Unstripped `--run` and `--link` stdout equals the REPL effect stream | Notice leaks into batch output; an effect runs twice | Acceptance (batch negative); safety fence (effect once) |

**Maintenance check.** `tests/helpers/e2e.rs::strip_repl_chrome` drops a
line exactly equal to `REPL_IO_NOTICE` from the REPL leg only. Without it,
every `run_through_all_modes` REPL leg would fail on the notice. Only the
unstripped batch legs give IOT-B its authority.

**`dev` module evidence** (`src/pipeline.rs`, `src/repl/format.rs`):

- `write_io_execution_notice` writes exactly one notice line and flushes after
  the write when `is_io`.
- It writes zero bytes when `!is_io`.
- `io_execution_notice_line` is byte-identical to the spec text, with colour
  off and on.

**Adequacy (2026-09-25): adequate.**

- **Detection.** IOT-1 to IOT-5 were RED before the correction, each at its
  notice-count assertion (`.local/s122-io-notice-test-run1.log`: 278 run, 5
  failed). They are GREEN on the delivered source
  (`.local/s122-io-notice-dev-targets.log`: 278/278, including all 12
  `output_equivalence` cells).
- **Full suite.** `.local/s122-io-notice-dev-full.log`: 6079 run, 6071
  passed, 8 failed, 1 skipped. The three module tests pass.
  - Seven failures are defect guards outside this change: the five
    [QR cells](#f1-acceptance-and-qr-classification-2026-09-25) in
    `tests/cache.rs`, `fq_type_only_reference_loads_its_module_on_a_fresh_compile`
    and its one-module reduction
    `tests/spec_08_modules.rs::fq_type_annotation_alone_loads_its_module`.
    Each fails in a batch `--run` leg, which never reaches the notice site.
  - `citation_drift` failed on four citations of the retired cell names:
    three in §1.2.1 and one in this record. This record and the §1.2.1 band
    now repair them.
  - No failure is a notice-only expectation update, which matches the
    census's prediction of zero.
- **Review.** Independent `review`(src) accepted the delivered source with
  no blocking or required finding.

**Limits:**

- The negative legs of IOT-4 and the zero-bytes module test were never
  observed RED, because the product emitted no notice before the correction.
  Their detection rests on the count and position assertions, which the
  outside-product predicate replica rejected for a notice on the pure,
  definition and lookup turns.
- IOT-B's batch negative is observed only through `output_equiv_*`, whose
  `// spec:` lines cite §10.6.3, not §1.2.1.
- For a non-`IO` `/mem <expr>`, the order of result and delta line is not
  asserted. `mem_with_expr_emits_signed_delta_line` checks only that both are
  present.
- Evidence covers only a piped session. A terminal session uses the same
  stdout write and flush.
- Not allocated, each unobserved:
  - a trapping IO action;
  - an `IO`-typed compile error;
  - multi-form lines, which the spec leaves open;
  - agent submit;
  - the design-accepted degraded-startup residual.

## Qualified lookup dependencies — evidence delta (2026-09-26)

**Authority.**

- The user's approval of the exact API and schema, and of module-wide
  insert-only maintenance
  ([sprint record](../../sprints/SPRINT.md#lookup-dependency-implementation-approval--2026-09-26)).
- The boundary design, [interfaces §Qualified lookup dependencies](../../design/arch/interfaces.md#qualified-lookup-dependencies):
  the recorded modules are validity edges, not load edges.
- The opening rule of [`int.md` §7.6](../../design/int/int.md#76-dependency-record-and-validity).
- [Module caching §1](../../design/backend/module-caching.md) goals 1–2, and
  `repl/spec/14-file-watching.md` §14.7: unchanged modules keep their cached
  objects.

The producer census belongs to `design`(typecheck). `design`(int) settled the
rewritten-restored-module rule in
[`int.md` §7.6.2](../../design/int/int.md#762-lookup-dependencies): the
rewritten entry is deferred, then dropped, and the earlier entry remains.
Every condition below also holds under the rejected own-record alternative.

**Baseline.** In `.local/s122-annotation-fallback-dev-full.log`, 6103 tests
ran: 6098 passed, 1 was skipped, and 5 failed. The failures are QR-1 to QR-5.
Their pre-fix REDs are recorded under
[F1 acceptance](#f1-acceptance-and-qr-classification-2026-09-25).

| ID | Condition; plausible wrong outcome | Class | Lowest layer and owner | Before the fix (observed unless stated) |
|---|---|---|---|---|
| LD-1 | QR-1 to QR-5 pass on every leg. Wrong: any kind that stays unrecorded, or any recorded member that validation cannot read (the warm arming leg then misses `a`) | Acceptance | Existing `tests/cache.rs` cells, unchanged | RED, recorded |
| LD-2 | Re-export chain: `a` writes `r1/f`; `r1` re-exports `f` from `r2`; `r2` re-exports it from `c` (11), and the edit changes that to `d` (99). Only `r2` is edited. Wrong: the lookup member is kept as a leaf and its own edges are not walked, or only the terminal is recorded | Acceptance | New e2e cell (`test`) using the QR helper. The anchor sits in `r1`, so the sibling's `a` imports `[r1 [anchor]]` and has a declared edge | Subject RED: cached 11, uncached 99; the trace hits `a` and `c`. Sibling GREEN |
| LD-3 | A REPL rewrite of a restored module keeps its recorded dependencies, and the result is not a perpetual miss. Wrong: restore, the concrete conversion or REPL publication drops the restored set, and the rewritten entry then restores stale | Acceptance | New e2e cell (`test`) over the QR-1 fixture; legs below | Subject RED through the rewrite-written entry: cached 11, uncached 99. Sibling GREEN, and its unchanged run after the rewrite hits `a` |
| LD-4 | A warm run does not load a module that is a lookup dependency only. Wrong: the restore walk consumes the set, as the withdrawn proposal did | Safety fence | A warm-leg assertion added to QR-1 (`test`). The subject's warm run has no `cache hit (.meta valid) for r`; the sibling's warm run has one, which proves the observation fires. Assert it before the final comparison | GREEN on both legs: the sibling's warm run hits `r`; the subject's does not |
| LD-5 | Unchanged sources hit the warm cache for the spellings that no existing trace leg covers: a compiler-owned qualifier (`primitives/…`), the module's own qualifier, and a declared child reached as `child/f`. Wrong: a member that validation cannot resolve gives a perpetual miss, which no behavioural oracle can see | Safety fence | New cold→warm e2e cell (`test`). The warm run hits `a` and the child and behaves as the cold run | GREEN: exits 5 cold and warm; the warm run hits `a` and `a.util` |
| LD-6 | A macro head's module stays recorded when a later form gaps after expansion. Wrong: a continuation holder drops the attempt's set | Acceptance | QR-5 extended with a later reference to an unloaded `e` (`test`). Armed once by `dev`(src): with the resumed set seeded empty, QR-5 is RED and LD-7 GREEN | Subject cold and warm legs GREEN; edit leg RED: cached 11, uncached 99. Sibling GREEN. The carry itself has no pre-fix state; the arming control observes it |
| LD-7 | A qualified reference in a macro clause body keys the defining module. Wrong: the checkpoint publishes without `clause_staging`'s lookup dependencies | Acceptance | New e2e cell (`test`), with a re-export hop in the clause body; module row I7 | Subject warm leg hits `a`, so the cell is armable; edit leg RED: cached 11, uncached 99. Sibling GREEN |
| LD-8 | An expression turn and the `/quit` persist of a restored module keep a sound warm hit, and a later lookup edit is not served stale. Wrong: a perpetual miss, a retained entry that serves a broken rewritten artefact, or a rewrite that loses the restored set | Acceptance | New e2e cell (`test`); legs in §"LD-8 legs". Armed once post-fix by the session's `manifest entry for a deferred: r unsettled` trace line | Legs 1–3 GREEN, with `a.cl` byte-identical after the session; leg 4 RED: cached 11, uncached 99; leg 5 unreached |
| LD-T | Types carrier rows, listed below | Acceptance (module); T4 is a safety fence | `dev`(types) | T1–T5 GREEN; each planted fault turned one witness RED (`.local/s122-lookup-types-dev-faults.log`). The T5 fallback row went RED under the planted `lookup_module: None`, with the canonical module unchanged, and GREEN restored (`.local/s122-lookup-types-r1-fault.log`, `.local/s122-lookup-types-r1-green.log`) |
| LD-C | Typecheck producer rows, listed below | Acceptance (module) | `dev`(typecheck) | All 16 census rows recorded `[]` before the producer (`.local/s122-lookup-typecheck-dev-mid.log`); GREEN after (`.local/s122-lookup-typecheck-dev-unit.log`) |
| LD-I | Int consumer and macro-producer rows, listed below | Acceptance (module) | `dev`(src) | I1 (both rows), I2, I3, I4 (alias), I5 (unsettled), I6 and I7 RED before wiring; the bare-head, restored-member, I8 and I9 rows GREEN (`.local/s122-lookup-int-dev-red.log`) |
| LD-M | `CACHE_SCHEMA_VERSION` moves from 29 to 30, and the existing schema-refusal cells stay GREEN. `public_api_relocations` passes against the regenerated types baseline, whose diff is exactly the three approved lines | Maintenance | `dev`(backend) and `dev`(types). The user confirms the baseline under the existing gate | The bump turned `schema28_identity_cache_refused_rebuilt_and_reused_warm` RED on its epoch pin, not its refusal logic (`.local/s122-lookup-backend-dev-schema.log`). `test` now reads the stamped schema from the binary (`.local/s122-lookup-oracles-test.log`). The version gate already refuses a schema-29 sidecar, so no schema-29 leg is allocated |

**LD-3 legs.**

1. Cold `--run`.
2. A REPL session in the same directory. It imports `a`, and the trace shows
   that `a` restored. It then runs `/mod a`, defines an unrelated `h` and
   quits. `a.cl` now contains `h`.
3. Edit `r`. A `--no-cache` control, which leaves the cache untouched, gives
   99. The cached `--run` matches it.
4. An unchanged `--run` hits `a`.

The sibling adds `(import [r [anchor]])` to `a`. After leg 2 it runs an
unchanged `--run` that hits `a`, which proves that the rewrite wrote a
restorable entry. The subject must not run between legs 2 and 3.

The sibling arms the cell: its unchanged run after the rewrite hits `a`.
After the fix, the subject's defining turn defers and drops its entry.
The cached run on the edited sources rebuilds `a`, and the next unchanged
run hits it.

**LD-8 legs.**

1. Cold `--run` of the QR-1 fixture.
2. A REPL session restores `a`, runs `/mod a`, evaluates a pure expression
   and quits. Assert the trace hit and that `a.cl` remains byte-identical.
3. An unchanged `--run` exits 11 and hits `a`.
4. Edit `r`; the cache-preserving `--no-cache` control exits 99 and the cached
   run matches it.
5. An unchanged `--run` exits 99 and hits `a`.

The sibling supplies the import edge as in LD-3. Before the fix, legs 1–3
pass and the subject fails at leg 4 (cached 11, uncached 99). Post-fix arming
quotes the subject session's `manifest entry for a deferred: r unsettled`
trace once; it is not a permanent implementation-specific assertion.

**Module rows.**

- **`dev`(types).**
  - T1. The recorder ignores the table's own path, and duplicate records
    collapse.
  - T2. Both publish funnels union the staged set into the live set. A live
    member that is absent from staging survives.
  - T3. `into_concrete` and `Clone` carry the set. `new_with_params` starts
    it empty.
  - T4. A serde round trip preserves the set. A sidecar without
    `lookup_dependencies` fails to decode; an empty default would under-key.
  - T5. `Resolved.lookup_module` names:
    - the alias target, not the alias;
    - the spelled re-export hop, not the terminal home;
    - the child, for a child-relative spelling;
    - the absolute module after a child-probe miss, not the child candidate.

    - the ancestor, when a descendant qualifies the ancestor's private
      binding and resolution takes the direct-lookup fallback in
      `resolve.rs` (review R1). The canonical module is the ancestor too.

    It is `None` for a bare name, including a prelude fallback, and for a
    qualified spelling of the current module.
  - **Detection.** No pre-fix state exists. Observe T2 and T4 failing once,
    against a replace-on-publish variant and a defaulted-field variant
    respectively, and then revert. Observe the fallback row failing once with
    `lookup_module: None` planted at the fallback's `Resolved` literal, then
    revert.
  - The fallback row is a module extension of T5. It adds no `test` cell and
    no separate gate. `qa` consumes its planted-fault log at adequacy and does
    not request a re-review for it.
- **`dev`(typecheck).**
  - Each route in the design's census has one row. After a successful check,
    the cluster's staging holds the answering module. The plain row proves
    that the route reaches the one recording seam.
  - Alias substitution is single-sourced in the types resolver (T5, first
    bullet), so an alias row is required only for each distinct path by which
    a spelled qualifier reaches the seam: the value path, type resolution,
    step R, the stacked bound and the pattern walk. The value constructor and
    `b/T.C` share the value path. The `deftype` field shares type resolution.
    The impl target passes its spelling to the seam unchanged
    (`traits/type_resolve.rs::impl_target_head_spelling`).
  - A `(mod q)` declaration installs the alias `q → <current>.q`, so a
    declared child is reached through alias substitution. The child-relative
    rows observe the walk's own child candidate, which R-1 below classifies.
  - The dotted member core has no qualified reading and is not a family. A
    bare `T.C` resolves through an import, which is a declared edge.
  - Observe every row RED before the producer is wired.
  - The census is the falsifier's enumeration. A route missing from it is
    graded as asserted. Falsifier for a shared-path grade: a successful
    cluster whose aliased spelling of a census route leaves the staging set
    without the alias target while its plain spelling records it.
- **`dev`(src).** I1–I9 are the unit rows in
  [`int.md` §7.6.2](../../design/int/int.md#762-lookup-dependencies), in order:
  - I1: the union, including from a decoded table;
  - I2: the lookup-only closure;
  - I3: the index worker;
  - I4: alias-qualified and bare macro heads;
  - I5: an unloaded member is unsettled, and a restored member settles
    without loading its lookup members;
  - I6: the carry;
  - I7: the checkpoint;
  - I8: a failed check publishes nothing;
  - I9: `/expand`.

  Observe I1, I3, I4, I6 and I7 RED before wiring. I8 and I9 are safety
  rows with no pre-fix state. Forms and the set cross every continuation
  holder as one value. The restore walk has no unit tier; LD-4 measures it.
  Arm LD-6 once by seeding the resumed dependency set empty: QR-5 must fail
  while LD-7 stays GREEN, then revert the fault.

**Completion criteria.**

- `test` logs the pre-fix results before any consumer lands. Met:
  - LD-2 and the LD-3 subject are RED for the predicted reason, with their
    siblings GREEN, and LD-4 and LD-5 are GREEN
    (`.local/s122-lookup-test-cache-target.log`);
  - LD-6 and LD-7 subjects are RED with siblings GREEN, and LD-8 is RED at
    leg 4 only (`.local/s122-lookup-int-test-cache.log`).
- After implementation:
  - LD-1 to LD-8 pass on every leg;
  - the LD-6 arming control is observed and the LD-8 deferral trace quoted;
  - the module rows pass, with the REDs stated above logged;
  - `cargo nextest run --no-fail-fast` has zero failures;
  - LD-M holds.
- The `dev` release gate is met on each touched surface, and `review` of each
  surface reports no blocking finding.
- `test` then marks the QR-1 to QR-5, LD-2, LD-3, LD-7 and LD-8 `// defect:` lines as
  fixed (`artifact-underkey`, `ModuleEdges`, found in S122, owner `/dev`),
  using the commit's SHA.

**Limits, not allocated.**

- `--link` and the REPL for QR-1 to QR-5 are not observed separately. They
  use the same record builder and restore walk.
  - Fresh and warm `--link` link different objects; nothing binds a
    lookup-only module.
  - Falsifier: a warm `--link` that fails or differs where `--run` agrees.
- A watcher reload recompiles onto the existing table and unions into its
  set. A dependent re-check of a restored module with an unloaded lookup
  member defers and drops its entry. The earlier record holds the changed
  dependency's older hash, so the module misses. Neither path is observed
  separately.
  - Falsifier: a restored module rewritten by a dependent re-check, with an
    unloaded lookup member, restores stale in the next session after that
    member changes.
- A spurious member left by a redefinition or a failed turn costs a miss,
  never stale service. This follows from the approved insert-only rule.
- Instance-mediated dispatch stays held for `spec`.
- Selective reuse is deferred to
  [ACT-0992](../../sprints/actions/ACT-0992-optimisation-aware-cache-invalidation.md).
- No spec band changes here. The LD conditions trace to design; §14.7 is
  revisited at adequacy.

- The eval and redefinition retry loops carry the same continuation value
  as the pool worker, which LD-6 measures. They are not observed separately.
  Falsifier: a REPL turn expands an FQ macro head, gaps on an unloaded module,
  and the next session serves the old expansion after the head's macro changes.

#### Adequacy (2026-09-26)

**Verdict.** Every allocated LD condition and the LB/LP cells are met on the
uncommitted tree below. The evidence is adequate for the allocated
conditions. Every surface review reports no blocking finding; `review`(src)
reports no required finding either. This is not phase acceptance. The user confirmed the generated baseline on
2026-09-26; the change remains uncommitted.

**Tree.** The full run is `.local/s122-lookup-int-dev-full.log`
(sha256 `8f20d11a…6c72`): 6144 run, 6144 passed and 1 skipped, in 213.5 s. No
source file changed after it except comment corrections. The root then applied:

- the backend R-1 wording at the constant's rustdoc
  (`crates/cranelisp-backend/src/cache/mod.rs`), a doc-only diff against
  `HEAD` apart from the value 30 that the run tested;
- the P4 comment in `crates/cranelisp-typecheck/src/form/tests.rs`. Reversing
  that one comment restores the tested hash `09c7732b…`.

The LB-1 comment citation was subsequently repaired without changing executable code. Every other source file hashes to its dev and review record.

| Condition | Evidence |
|---|---|
| LD-1 to LD-8 | All `tests/cache.rs` cells GREEN in the full run. LD-4 is inside QR-1. The LD-6 arming control ran with the resumed set seeded empty: QR-5 was RED (cached 11, uncached 99), LD-7 GREEN and I6 RED. The fault was then reverted (`.local/s122-lookup-int-dev-ld6-fault.log`). The LD-8 subject session printed `manifest entry for a deferred: r unsettled`, and legs 3–5 exited 11, 99 and 99 (`.local/s122-lookup-int-dev-ld8-trace.log`) |
| LD-T | T1–T5 and the fallback row GREEN; the planted faults are recorded in the LD-T row |
| LD-C | Census and negative rows GREEN. The R-2 criterion is met |
| LD-I | I1–I9 GREEN. I7 asserts membership, because clause bodies also record the compiler-owned `macros`, which the consumer filters. It was `[]` before wiring, so it still discriminates |
| LD-M | Schema 30; tripwire at 30; the schema-refusal cells and `public_api_relocations` GREEN; types baseline +3/−0, matching the packet |
| LB-1, LB-2, LP-1 to LP-3 | GREEN. The LB-1 oracle repair landed before the typecheck fix |

**Remaining before delivery.**

- The user confirmed the types baseline diff on 2026-09-26; that gate is satisfied.
- `arch` confirmed review(src) A3 on 2026-09-26: the changed root-crate
  items have no inter-crate consumer and require no additional API gate.
- At commit, `test` adds `fixed=S122/<sha>` and past-tense framing to the
  QR-1 to QR-5, LD-2, LD-3, LD-7, LD-8 and five LB/LP `// defect:` lines.

**Evidence limits.**

- The `dev` clippy gate for `src/` compares by reading each site. No
  pre-change count was captured.
- `crates/cranelisp-exe-bundle` was not gated; it was not touched.
- The eval and redefinition continuation holders remain asserted, as the
  limit above states. The pool-worker holder is measured.
- The LD-6 fault run and the LD-8 deferral trace ran on source that preceded
  the last edits to `src/scheduler.rs`, `src/process_form.rs` and its tests,
  made between 10:51 and 10:52 (review(src) A1). The only lints `dev` reports
  fixing there are in a test helper and a parameter allow. The LD-6 planted
  site is unchanged. The full run on the final bytes passes QR-5, LD-7 and
  every LD-8 leg. Root subsequently re-observed the deferral on the final
  binary, with all LD-8 legs passing; `.local/s122-lookup-ld8-final-trace.log`
  records the binary hash, unchanged cache hit, edited re-export rebuild and
  subsequent warm hit. This resolves the trace timing limit.

**Baseline verification.** Root ran `cargo +nightly public-api -s --omit auto-derived-impls -p cranelisp-types` into a temporary file and confirmed byte-for-byte equality with the checked-in baseline using `cmp`. The generated diff contains exactly the three approved additions.

**Empty-publication lead (`dev`(src) §7 item 3): a confirmed source-read
lead, class `artifact-underkey`, mechanism a hypothesis.**

- Recording happens only at a staged publication. Two paths skip it:
  `worker.rs::check_cluster_to_staging` returns `None` when the expanded
  cluster has no checkable entry, and `prepare_cluster_commit_with_demands`
  then returns `Ok(None)`. So a cluster whose qualified macro head expands to
  nothing publishable records the head's module nowhere.
- review(src) A2 confirms this by source reading. It conforms to int.md
  §7.6.2's *record at publication*, but falls short of the approved fact in
  `interfaces.md`, which covers every macro head. It falsifies no allocated
  LD condition. The *macro heads recorded* grade holds only for attempts that
  publish.
- Reaching it needs a module whose whole checked cluster is empty after
  expansion. Whether such a module writes a cache entry at all is
  unobserved.
- Plausible wrong outcome: `a.cl` holds only `(b/m)`, and `m` expands to
  `(begin)`. `main` loads `a` without naming a member, for example through a
  glob import. After a cached run, `m` changes to expand to `(defn g [] 99)`
  and `main` starts calling `a/g`. The cached run then rejects or misbehaves
  where `--no-cache` exits 99.
- **Allocation LD-9 (`test`, e2e `--run`, stdlib-free, RED-first,
  `tests/cache.rs`, QR helper).** It runs on the first free `test` visit with
  DB-1 and R1-V.
  - Subject: the scenario above, cold then edited, compared with the
    cache-preserving `--no-cache` control.
  - Sibling: `a` also defines `(defn anchor [] 1)`. The cluster then
    publishes and records `b`, so the sibling is GREEN.
  - If the subject's cold run writes no cache entry for `a`, or it passes,
    `test` reports that. The lead then closes as unreachable and the design
    grade stands.
  - If RED, add
    `class=artifact-underkey locus=src/worker.rs::prepare_cluster_commit_with_demands found=S122 owner=/dev`.
    The locus is provisional, and `design`(int) settles the recording point.
- It is not an accepted residual. It does not gate the adequacy above,
  because it is outside the allocated conditions.

### Source-read lookup leads — classification (2026-09-26)

Source: [typecheck design §11](../../design/typecheck/typecheck.md#11-open-design-items)
and its §3.4 census. All five leads are **confirmed conformance defects**.
Each subject is RED for the predicted mechanism and its control GREEN
(`.local/s122-lookup-leads-test.log`, `tests/spec_08_modules.rs`). None is an
accepted residual. `design`(typecheck) is settling the correction.

**Effect on the lookup-dependency claim.** Neither route obstructs it, and no
LD condition changes.

- *Stacked bound.* `program/register.rs::resolve_bound_param` builds
  `FQTraitName(m, Tr)` from the spelled qualifier. Nothing in the defining
  module's check reads `m`'s table for it, and spec §7.12.1 rules out
  supertraits. The artifact is therefore a function of its own source, and a
  cache entry cannot go stale through this bound. The approved fact records
  only tables that answered, so it holds as written.
- *Pattern constructor.* The design's caller-side record names the module
  whose table answered for every accepted program. A rejected program writes
  no entry.
- The pattern cell in `dev`(typecheck)'s census holds for both the current
  route and a route converged onto the seam.
- Falsifier: a module-hash change to `m` makes a cached run differ from an
  uncached one, where `m` is reached only through a stacked bound or a
  qualified pattern.

**Requirement decision.** None. Spec §8.6.6 steps 1, 3 and 5, §8.6.1,
§8.5.4 edges 1, 3 and 9, §8.7.3 and §8.6.5 ("constructors use the same rule
in value and pattern positions") decide every cell. Accepting the
stacked-bound residual would retain a spec violation. Each is a Phase 5
defect under [METHOD §2.4](../../sprints/METHOD.md#24-deferral).

**Repro cells (`test`, e2e, stdlib-free).** Each subject differs from its
control only in the claimed cause. The `// defect:` lines carry
`class=resolver-mirror found=S122 owner=/dev` and the locus shown.

| ID | Subject; spec | Control | Observed before the fix | Locus; face |
|---|---|---|---|---|
| LB-1 | REPL, `PrimitivesOnly`: alias `(zz z)`, a trait `Tr` in `zz` and a local trait `Ts`, `(defn f [:Ts :z/Tr x] 7)`. The published scheme must constrain `a` by `Tr` in `zz` and by the local `Ts`; §8.6.6 step 1, §3.4.1 | Stack length 1, `[:z/Tr x]` | RED: displays `[:user/Ts :z/Tr a]`, an identity built from the alias. Control GREEN: `[:zz/Tr a]` | `register.rs::resolve_bound_param`; wrong constraint identity |
| LB-2 | `--run`: `[:Ts :nosuch/Tr x]`, with no file backing `nosuch`, must be a reference-site error; §8.5.4 edge 3, §8.6.6 step 5 | `[:nosuch/Tr x]` | RED: accepted, exits 7. Control GREEN: rejected, naming `nosuch` | same; `wrong-accept` |
| LP-1 | `--run`: alias `(shapes s)`, `(match c [(s/Circle r) r])` must match as `shapes/Circle`; §8.6.6 step 1 | The same program with the pattern spelled `shapes/Circle`; the value `(s/Circle 8)` is common to both | RED: "unknown constructor in pattern: s/Circle". Control GREEN: exits 8 | `checker.rs::resolve_constructor_entry`; `wrong-reject` |
| LP-2 | `--run`: `shapes` declares `(deftype- Secret (Hid [:Int v]))` and a public `mk`; `(match (shapes/mk) [(shapes/Hid v) v])` from `main` must be a compile-time error; §8.7.3 | The value twin `(shapes/Hid 8)` from `main` | RED: accepted, exits 8. Control GREEN: "module 'shapes' has no member 'Hid'" | same; `wrong-accept` |
| LP-3 | `--run`: the pattern in an uncalled `(defn radius [c] (match c [(shapes/Circle r) r]))` is the program's only reference to `shapes`; `main` is `(Pure 8)`; §8.5.4 edge 1 (pattern position) | `radius`'s parameter annotated `:shapes/Circle`, which loads through the type gap | RED: "unknown constructor in pattern: shapes/Circle". Control GREEN: exits 8 | same; `wrong-reject` |

- **LB-1 observes the published scheme, not a call.** A `--run` call cannot
  discriminate: a declared bound that the body does not use is not checked at
  the call site in any spelling (DB-1 below). The REPL scheme is the scheme
  every caller instantiates, so it carries the identity condition in every
  mode. Limit: call-site acceptance through the bound is unobserved until DB-1
  is repaired. No `--run` twin is allocated then, because the call-site check
  reads this scheme.
- **LB-1 oracle repair (`test`, before `dev`(typecheck) runs the fix).** The
  subject asserts `[:user/Ts :zz/Tr a]` exactly. §3.4.1 and
  [REPL display §1.4](../../repl/spec/01-display-format.md#14-type-display) fix neither the
  constraint order nor any other rule that order would follow. The assertion
  must accept both constraints in either order, on `f`'s scheme line, and
  must reject the alias spelling `:z/Tr`. The cell's comment states the
  unchecked bound as current behaviour. It should name DB-1 as an open
  defect instead, so that the comment does not outlive the repair.
- **LP-3 makes the pattern the only reference, not the first in form order.**
  Any later value reference in the same file, such as
  `(radius (shapes/Circle 8))` in `main`, loads `shapes` before `radius`'s
  pattern is checked. The cell as first allocated was GREEN on both legs for
  that reason.
- Each cell discriminates a distinct partial fix:
  - alias substitution added to the rooted route (LP-1 green, LP-2 red);
  - convergence without a gap (LP-3 red);
  - resolving the bound without alias substitution (LB-1 red), and resolving
    it without rejecting an unbacked module (LB-2 red).
- Child-relative and prelude-fallback spellings of the pattern route are not
  allocated. They share the one bypass, and a repair converged onto the seam
  covers them. Falsifier: after the repair, a `(mod q)`-declared child's `q/C`
  pattern resolves to an absolute `q`, or `m/C` resolves where `m` only
  imports `C`. An undeclared registered child is R-1's subject below.
- No `--link` or REPL parity legs are allocated for LB-2 or LP-1 to LP-3.
  Every mode reaches the same typecheck routes.

**Why coverage missed them.**

- `tests/spec_06_pattern_matching.rs::fq_ctor_pattern_position_autoloads`
  claims pattern-position auto-load. In it, the parameter annotation and the
  value reference load `shapes` before the pattern is checked. The pattern is
  never the only reference, so it cannot discriminate. LP-3 is the missing
  condition.
- The other qualified-pattern cells use only `user/`, where the rooted and
  qualified routes coincide.
- The FT and FA cells covered the two type-or-trait routes only. The
  trait-only positions were already a recorded open lead.
- No broader variant matrix is allocated.

**Correction and completion.**

- `design`(typecheck) settles the routes: the bound resolves through
  `resolve_trait`, and the pattern route converges onto the qualified seam,
  including the gap for an unloaded module. The quasiquote `macros/SCons`
  lowering stays GREEN.
- `dev`(typecheck) repairs with a module cell for each face, and adds the
  census cell `[:Eq :b/Tr x]` giving `{b}`.
- Converging the pattern route retires the caller-side record. `sprint`
  decides whether that repair precedes the record's implementation.
- Done when the five cells pass, the LB-1 oracle repair has landed first, and
  `test` has marked each `// defect:` line fixed with past-tense framing.
- State, 2026-09-26: the first two conditions are met; see the lookup
  adequacy above. The `fixed=` marking waits for the commit SHA. None of the
  five comments frames its own defect as open; LB-1's names DB-1, which is
  open. `qa` has therefore restored the
  §8.5.4 edge 1 pattern-position band with LP-3, and cited LB-2's refusal
  there. It also cited LB-1 and LP-1 at §8.6.6 step 1, LB-2 at step 5 and
  LP-2 at §8.7.3. These bands land in the same change-set as the fix.

#### Producer review R-1 and A-4 — classification (2026-09-26)

Source: `review`(typecheck) of the lookup-dependency producer. Neither
finding was introduced by that change-set, and neither gates LD, the cache
correction or LB/LP. Neither is an accepted residual.

**R-1: undeclared registered child — a confirmed source-read lead, class
`resolver-mirror`, mechanism a hypothesis.**

- Value position reads a qualified spelling twice:
  - the types resolver first, which applies alias substitution and then the
    absolute path, with no child reading;
  - then the typecheck walk, whose `qualified_candidate_modules` synthesises
    `<current>.<q>` before the absolute path. `resolve_ref_target` records
    through the walk; the pattern route reads only the walk.
- `(mod q)` registers the alias `q → <current>.q`
  (`src/process_form/dependency.rs::register_submodule_alias`; the
  cache-restore mirror is in `src/imports.rs`). A declared child therefore
  wins in both positions through the first reading, and the absolute module
  is never consulted.
- The two readings can diverge only for a registered `<current>.q` that the
  current module did not declare. The unit census world seeds exactly that
  shape. Reaching it in the product has not been observed.
- Spec reading: §8.11.2 item 1 defines the current module's submodule as one
  "registered via `(mod name)` in the current module". §8.5.4 item 2 confines
  child-of-current resolution to such submodules and to aliases, and
  §8.11.2.1 forbids a bare module name reaching the submodule in one
  position and the root module in another. For an undeclared `a.q`, §8.6.6
  step 3 does not apply, and the walk's synthesised candidate is the
  non-conforming reading. Its answer also depends on whether an unrelated
  module registered `a.q`, which is the face behind review's §3.4
  unrecorded-miss scenario.
- Refuter: `spec` reads §8.1.1's "a submodule of `foo`" into §8.6.6 step 3.
  The value leg below then expects the child; the pattern leg is unaffected.

**Allocation R1-V (`test`, e2e `--run`, stdlib-free, RED-first,
`tests/spec_08_modules.rs`), on the first free `test` visit after the cache
chain, with DB-1.**

- Construction: `a.cl` imports `[b [anchor]]`. `b.cl` imports from `a.q` and
  from the root `q`, so both are registered before `a` is checked. `a/q.cl`
  and `q.cl` each declare `(deftype T (C [:Int v]))` and `g`, returning 11
  and 99 respectively. `a` declares no `(mod q)`.

| Leg | `a`'s subject | Required | Predicted before the fix |
|---|---|---|---|
| Pattern | `(match (q/C 9) [(q/C v) v])` | Exits 9 under either reading (§8.6.5) | RED: a type mismatch between `q/T` and `a.q/T` |
| Value | `(q/g)` | Exits 99 (§8.11.2 item 1) | RED at 11 if the call follows the walk-recorded target; 99 means the divergence stops at the recorded identity, which `test` reports |
| Control | Both subjects, with `(mod q)` added to `a` | Exits 9 and 11 | GREEN |

- The control differs only in declaring the child.
- If the undeclared `a.q` cannot be registered before `a` is checked, `test`
  stops and reports that. R-1 is then product-unreachable, and the walk's
  synthesised candidate is a latent mirror that `design`(typecheck) settles.
- After the RED is observed, add
  `class=resolver-mirror locus=crates/cranelisp-typecheck/src/checker.rs::qualified_candidate_modules found=S122 owner=/dev`.
  The locus is provisional until `design`(typecheck) settles the route.
- The fix's module cell (`dev`(typecheck)) is P4's value twin in the census
  world. It asserts that value and pattern agree, and that the scheme and
  the recorded target name one declaration.
- No REPL or `--link` legs: every mode reaches the same typecheck routes.

**A-4: quasiquote `macros/…` capture — a candidate lead, not a defect of this
change.**

- Compiler-lowered quasiquote spellings (`macros/SCons`) resolve through the
  qualified seam in value position, and now in pattern position too, so a
  module alias or `(mod macros)` spelled `macros` redirects them.
- §9 promises that qualified `macros/…` access is available without an import.
  It does not say whether a user alias may shadow the compiler's own
  lowering; that is a hygiene question, and nothing observes it.
- No cell is allocated. Falsifier: a module that declares `(mod macros)` or
  imports an alias `macros`, and uses a quasiquote template or pattern,
  is rejected or matches the user's constructor.

#### Declared bound not checked at the call site — intake (2026-09-26)

**Observation.** `test` observed this in diagnostic cells while shaping
LB-1. Those cells have since been removed; no committed cell reproduces it
yet.

- `(deftrait Ts (ts [self] Int))`, `(impl Ts Int …)`, `(deftype U [:Int n])`,
  `(defn f [:Ts x] 7)` and `(defn main [] (Pure (f (U 1))))`: accepted,
  exits 7. `U` has no `Ts` impl.
- The same with body `(ts x)`: rejected with "no impl of trait main/Ts for
  type main/U".
- Qualification makes no difference: `[:z/Tr x]`, `[:zz/Tr x]`,
  `[:Ts :z/Tr x]` and `[:Ts :zz/Tr x]` with body `7` are all accepted at a
  type that lacks the `Tr` impl.

**Classification: a confirmed lead, face `wrong-accept`. The spec decides it,
and it is not a requirement ambiguity.**

- §3.9.2: a trait annotation restricts the parameter "to types that
  implement the named trait".
- §3.3.2: a constraint is "a claim the compiler checks", and "the caller
  relies on the constraint".
- §3.4 and §3.6.2: the constraint is part of the scheme, and instantiation
  copies it to the fresh variables. The REPL already publishes it: LB-1's
  scheme shows the unused `:user/Ts`.
- Two passages might appear to permit acceptance. Neither does:
  - §3.3.2 MUST (b)'s "a caller instantiating the variable at a concrete type
    MUST NOT be an error" is scoped to skolem escape ("The escape MUST arise
    only from the body").
  - §7.8.2's "identical results" compares an asserted constraint with the
    same constraint inferred. It does not exempt a constraint the body leaves
    unused.
- It is not a qualification defect. It belongs to neither the LB/LP routes
  nor the cache work, and it changes no LD condition.
  - A repaired check reads the trait home's impls at the call site. That is
    the instance-mediated limit already held for `spec` above, and it is not
    a new lookup-dependency case.

**Mechanism: a hypothesis, read from source and not observed at its seam.**

- `traits/monomorphise.rs::instantiate_constrained` carries the scheme's
  constraints onto the fresh variables as active constraints.
- The no-impl error is raised only where a trait method is dispatched
  (`traits/dispatch.rs`, and the monomorphisation resolution).
- Nothing appears to discharge an active constraint when its variable is
  pinned to a concrete type.
- The body-use control separates a declared-only constraint from a
  body-inferred one at the symptom. It does not observe the discharge seam.
- Refuter: a module test shows the caller's instantiation lacks the declared
  constraint, for example because the scheme used at instantiation differs
  from the displayed one. The locus then moves.

**Allocation DB-1 (`test`, e2e `--run`, stdlib-free, RED-first,
`tests/spec_03_types.rs`).** One cell, three legs:

| Leg | Program | Required | Before the fix |
|---|---|---|---|
| Subject | `(defn f [:Ts x] 7)`, called as `(f (U 1))` | Rejected, naming `Ts` and `U` | Predicted RED: accepted, exits 7 |
| Control | The body is `(ts x)`; the call is the same | Rejected, naming `Ts` and `U` | Predicted GREEN |
| Positive | `(defn f [:Ts x] 7)` with `impl Ts Int`, called as `(f 3)` | Exits 7 | Predicted GREEN |

- The control differs from the subject only in whether the body uses the
  constraint.
- The positive leg guards against an over-fix that rejects the definition or
  every call.
- Add the `// defect:` line only after the RED is observed:
  `class=wrong-accept locus=crates/cranelisp-typecheck/src/traits/monomorphise.rs::instantiate_constrained found=S122 owner=/dev`.
  The locus is provisional. If `design`(typecheck) places the discharge
  elsewhere, `test` updates the locus before the fix lands.
- If the control or the positive leg fails, `test` stops and reports it as a
  separate intake.
- No REPL or `--link` legs: the check lies in the typecheck judgment, and
  every mode reaches it.

**Disposition.**

- `sprint` schedules DB-1 on the next free `test` visit, together with the
  LB-1 oracle repair above.
- It does not gate the lookup-dependency work, the cache correction or LB/LP.
- Once DB-1 is RED, the lead is a Phase 5 defect under
  [METHOD §2.4](../../sprints/METHOD.md#24-deferral).
  - `design`(typecheck) settles where the declared constraint is discharged.
    `sprint` chooses whether that shares the current route design.
  - `dev`(typecheck) repairs with a module cell.
  - The full suite at that fix is the regression check for any program,
    fixture or example that calls through an unused declared constraint.
- The §3.9 `[Tested+Neg …]` band does not evidence §3.9.2's restriction. `qa`
  revises it when DB-1 exists.
- This subsection is the open record until DB-1 is committed. After that, the
  failing cell is the record.
