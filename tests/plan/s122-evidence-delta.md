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
| D7 — shared document-checking pilot | Approved on 2026-09-10 under [SPRINT scope](../../sprints/SPRINT.md): replace the narrow four-root proposal with the shared mechanism pilot below. Implementation and evidence remain pending; Phase 4 was authorized on 2026-09-10; Phase 5 was authorized on 2026-09-10. | sprint coordinates shared-tool/project owners under Phase-5 reservations and subsequent closure gates |

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
| Q6 A — /mem | Report the expression observation after its returned owner is released, including heap values; no phantom retained result in delta. `repl/spec.md` §3.7 and `design/int/result-owner.md`. | Test extends current /mem process witness with a heap-result/control and separately verifies rendered value. Dev pins sampling order around owner lifetime. | `tests/repl_introspection.rs`; `src/repl/commands.rs::handle_mem` samples before formatting/drop. Use warmed/paired setup so macro/bootstrap work is not mislabeled result leakage. |
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
| ACT-0950 | Approved shared mechanism pilot below supersedes the narrow four-root proposal; no blanket residual baseline migration or enrollment on historical counts. |
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

This supersedes the narrow four-target-root proposal and its old realization sequence. Phase 4 was authorized on 2026-09-10; Phase 5 was authorized on 2026-09-10; implementation and executing evidence remain pending within sprint reservations. Host-guidance ownership and retention of checked-in adapters without a generator were separately approved on 2026-09-10.

Historical measurement of the superseded four-root proposal only; it does not measure the approved pilot's corpus or findings: Read-only measurement used the existing checker module with only SOURCE_ROOTS extended in memory, on the final-design 493-document live corpus: current roots **744 raw findings**, proposed roots **944**, difference **200 PATH observations / 141 unique fingerprints**. Citing roots: design 166, tests 24, sprints 7, spec 2, crates 1. These are neither 200 implementation defects nor 141 authorized baseline entries. This refresh supersedes the earlier Phase-3 202-observation/142-fingerprint snapshot and the historical 214 count. Measurement JSON: `/tmp/cranelisp-s122-triage/citation-doc-roots.json`; checker SHA-256 `056d89675b23542bb67d5fa7f931d2351dfb04f33d791a602621665a484751a4`.

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

Next allocation is bounded intrinsics corrective design for preserving the live shared Bind's field ownership while retaining correct unique transfer and normal teardown. Design determines the mechanism under the existing runtime ownership contract; QA prescribes no new API or algorithm. Reuse this module RED/control and final exact-balance assertions, then rerun the existing public two-nested-Bind sequence reduction, aggregate and existing explicit-bind/one-action/empty controls across their already-allocated REPL/run/link modes. Public acceptance must complete with the exact ordered values and no stale-RC abort; if it remains RED, retain that public gap and reattribute rather than declaring Q3 fixed or expanding correction by guesswork. Scoped review covers the shared/unique ownership distinction and affected normal/cleanup paths; no extra matrix or independent failure framework is allocated. In the retained source visit, repair the module pair's trace to `spec/12-runtime.md` §12.3.1 normal lifetime requirements: its current §10.12.9 cancellation citation does not mean this fixture exercises cancellation.

Q12 next test handoff: the static collision `platform.hx` / ordinary `platform-x` at `__cranelisp_got_platform_hx` needs a loaded executable witness. Allocate one minimal `platforms/hx/` test-platform fixture to a separately reserved platform-fixture dev invocation, following existing platform fixture conventions; sprint coordinates necessary workspace registration/build wiring. Test owns temporary `platform-x.cl` via the existing harness and cases in `tests/spec_platforms_adt.rs` / `tests/link.rs`. The fixture and ordinary module return distinct values (for example 7 and 3); invoke both and encode their ordered results as 73, so mere load success or wrong dispatch cannot pass. Run the same pair through REPL, `--run`, and `--link` with actual execution of the linked binary. Record acceptance/load/link/execution separately, retaining the first failure diagnostic. One otherwise identical noncolliding ordinary-module rename is the initial control. If the collision pair refuses before coexistence, test the original ordinary name alone to distinguish name admissibility from collision. Reuse the existing dual-platform and run/link harness patterns; add no stdlib dependency or broad platform matrix. This allocation authorizes the already-scoped fixture under Phase-5 reservations, not a naming correction or a static-only defect attribution. No source/build activity occurred during this allocation.

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

The reviewed design carriers are [Binary/int](../../design/int/s122-closure.md), [intrinsics](../../design/intrinsics/s122-typed-consume-closure.md), [primitives](../../design/primitives/s122-typed-consume-consumers.md), [backend](../../design/backend/s122-closure.md), and the existing [auto-curry evidence design](../../design/typecheck/auto-curry.md). D1 and D8 are approved with implementation and executing evidence pending. D7 shared document-checking pilot scope, host ownership and checked-in adapter choices are approved; the shared checker design and evidence allocation are adequate. Phase 4 was authorized on 2026-09-10; Phase 5 was authorized on 2026-09-10, and subsequent Magic edits/upstream publication remain separately gated. D6 is a future live-evaluation configuration/budget gate and does not block runner design or implementation planning. No additional compiler contract decision is inferred from owner/copilot execution policy.

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

QA read both live filings, `design/arch/concreteness-types-first.md` §1.3, the
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
Canonical homes are `design/int/prelude-table-write-isolation.md` §§2.1,2.4,4.
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
| R7 | Recoverable records preserve327 parseable telemetry rows and the two audit-listed review identities; no exact historical session-to-phase join is available. That unknown is explicitly retained rather than invented. Current native S122 dispatch attribution is separate. |
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
| Context exports arm uses `public_symbols()` while `/exports` resolves candidates and filters internals | Same consumer family; advisory model context; no requirement fixes the grain and no wrong outcome is reproduced. | No observation now. `design` (int) decides convergence on the `/exports` producer; if adopted, one twin cell (context export names equal `/exports`) accompanies it. |
| Pin narrower than "full current-module source" (types, traits, impls, file-loaded definitions absent) | Authority and realization disagree; not a defect until the owner chooses which moves. | `design` (int) decision, raised through `sprint`; `qa` allocates after it. |
| `prelude_implicit_names` holds the prelude table guard across a second `symbol_tables` read | Latent safety residual in a shape FIXME 0666 already retired in harvest; present before this change and not widened; reached by `/imports` and every context dump. | `dev` (`src/`): collect-then-resolve, the constructive repair. No detector or stress cell. Delivered for this function; review found it correct. |
| `src/CLAUDE.md` and `format.rs` said `/doc` follows the import chain through the identity helper `resolve_entry_for_display`, since removed (final section); stale `defined_symbols()` mentions in `design/int/agent.md` and `harvest.rs` comments | Stale records. `/doc` on a re-exported primitive and on a constructor is observed working. | The `src/CLAUDE.md` and `format.rs` `/doc` claims are repaired with the `/imports` guard correction, and review confirmed the new text against source. The `design/int/agent.md` and `harvest.rs` mentions stay with their owners' next edit; no evidence. |

- Review A1 and A2 are mechanical comment repairs with root. A3 is accepted:
  the cap unit guards the Haiku ceiling only and is not a general budget guard;
  ACT-0960 stays deferred.
- Review R1: pin admission of `Overloaded` and `Macro` moves toward
  `design/int/agent.md` §5.2 #1 ("pinned in full"), affects advisory context
  only and has no reproduced wrong outcome. No observation is allocated.
  `design` (int) restates the §5.2 admission rule against the live symbol-table
  API; `qa` reconsiders an observation only if that restatement excludes a
  class the pin now admits.
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
| A6: `design/int/agent.md` §23.1 feeder list contradicts the delivered feeder 2 | Stale record under the stale-records row. | `design` (int), in progress. |
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
