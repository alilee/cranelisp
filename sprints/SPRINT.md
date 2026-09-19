# Sprint 122: Known-issue closure and REPL-agent evaluation

**Status:** PHASE 5 — Runtime implementation, evidence, reviews and generated API confirmation are complete. Shared document-checker adoption is implemented; the latest completed consolidation check reports 2,519 existing findings across 723 documents, with no new finding identities. The eleven S84–S97 QA plans are retired after source-backed retention assessment and reference integration. The local REPL-agent eval runner/corpus is delivered with 18/18 self-check outcomes; the bounded Haiku smoke baseline passed both tasks; agent verification passes all 81 end-to-end cases and 175 selected module/import cases. Default verification passes 5,968 tests with only document conformance RED. QA accepts the bounded agent corrections and the design reconciliation is complete; integrated acceptance remains pending. No phase transition or publication is authorized.

**Goal:** Resolve the known compiler and language defects, make the remaining
issue records truthful, and deliver a repeatable REPL-agent evaluation baseline.

**Starting source checkpoint:** `dc78ddbe`, 2026-09-09. Phase-5 source changes
are tracked in the live execution record; opening role-package and consumer
wiring changes remain in the shared working tree. The [candidate inventory](s122-candidate-inventory.md) carries the
88-row QA assessment, current evidence and audit reconciliation; this plan owns
scope, allocation, dependencies and checkpoints, not another copy of the findings.

**Audit:** `cranelisp-backend` selected in Phase 4; its latest located
whole-context assessment is S110, the oldest in the current rotation inventory.
Dispatch read-only in Phase 6a. The S121 src assessment receives its
proposed dispositions below rather than being audited again.

## Phase approvals

| Transition | Checkpoint | User authority | State |
|---|---|---|---|
| Start → Phase 1 | Inventory, QA triage, efficient grouping and completed scope plan | 2026-09-09: “let's inventory the defects, issues, actions and audit findings”; “ok complete the plan” | approved; scope planning complete |
| Phase 1 → Phase 2 | Scope, allocation, exclusions and architecture-review brief in this plan | 2026-09-09: “ok proceed” in response to the explicit transition request | approved; complete |
| Phase 2 → Phase 3 | Reviewed boundaries, ACT-0954 exact removal and per-surface design scope | 2026-09-09: “approved” to both checkpoint decisions | approved; complete |
| Phase 3 → Phase 4 | Settled designs, user rulings and QA evidence deltas | 2026-09-10: “yes” to the explicit transition request | approved; complete |
| Phase 4 → Phase 5 | Exact producer/consumer sequence, source reservations and wave exits | 2026-09-10: “yes” to the explicit implementation request | approved; in progress |
| Phase 5 → Phase 6a | Delivered compiler/eval capability and evidence | — | pending |
| Phase 6a → Phase 6b | User-facing assessment and action plan | — | pending |
| Phase 6b → Phase 7 | Accepted artifacts and exact close operations | — | pending |

“Complete the plan” authorizes this scope artifact, not later-phase technical
work. Proposed role handoffs and wave structure below are reviewable planning
inputs; they do not claim architecture or design approval has occurred.

## Scope

### Included outcomes

| Outcome | Completion evidence to be allocated by QA | Important limit |
|---|---|---|
| Correct generic replacement and public IO composition | Existing generic replacement REDs execute the replacement body without signal termination; sequence-IO and its explicit-bind control succeed across applicable modes; fixes have discriminating module evidence | Scalar, vector and IO symptoms are not presumed one root cause. The current language contract remains authoritative. |
| Trustworthy recovery and diagnostics | ACT-0958's failed-turn conditions are positively armed; process success and recovery observations are independent; /mem's observation matches its lifetime contract | A now-successful trigger cannot stand in for failure. Diagnostic observations do not silently gate unrelated runtime behavior. |
| Recover known macro-turn ownership residue | The current +1/+2 marginal residual witnesses become correct balance observations; QA allocates required original-workload remeasurement | The typed-transfer design is reconciled against current source before implementation; a new foundation needs a consumer in the same stream. |
| Resolve material language-function claims | Current minimal cases establish derive's omitted shapes, free-variable curry and the retained def-application tail; proven violations receive fixes and permanent evidence | Historical mechanisms are hypotheses. A semantic ambiguity returns to the user, not a guessed test expectation. |
| Finish selected existing convergence obligations | Reconcile reload demand consumption; complete the remaining quote-classifier, result-root and Vec guard obligations where current authority and risk justify them | No revival of delivered concrete-instance, cache or platform migrations merely to clear an old title. |
| Close the known-issue inventory truthfully | Every live filing and identified audit residual has an owning-role disposition: repaired, already satisfied, superseded, or individually approved carry/alternative | Thirty-eight stale central claims are candidates for retirement, not automatic deletion authority. No record-only closure of an unfixed defect. |
| Working REPL-agent eval baseline | A runnable, documented small corpus of real REPL tasks starts from reproducible sessions, checks observable outcomes, retains run provenance and yields a comparable baseline report | Initial model-quality scores are diagnostic. Harness correctness and recorded results are deliverables; a perfect model score is not the goal. |

Confirmed defects discovered while establishing these outcomes join their owning
stream. The default is resolution within the sprint. A genuinely unreachable
outcome or requested scope expansion returns with evidence and an explicit
choice; size alone is not a carry reason.

### REPL-agent eval scope

Build on the existing agent test launcher, logs/trace, scenario stamps and
[context-tuning plan](../tests/plan/agent-context-tuning.md). The recorded
`safe-dial` session is an initial task candidate; QA selects a small corpus
from actual use and current failure/recovery cases. Do not invent extra tasks
merely to increase volume.

The design package will specify replayable prompts and starting state, outcome
checks, compiler/configuration/model provenance, repeat policy and result
comparison. Collect existing repairs/tool-use/step/cost observations when
available. Any extra instrumentation must have an identified information need;
no general observability platform or automatic tuning system is implied.

A baseline may run while known compiler failures remain explicitly classified.
The user selected the latest Claude Haiku as the eval quality benchmark on
2026-09-19. Resolve the latest Haiku release when preparing a baseline and record
the exact model ID for comparisons. On that date, Anthropic's
[model reference](https://platform.claude.com/docs/en/models/haiku-4-5/overview)
identifies Haiku 4.5, `claude-haiku-4-5-20251001`. This selects the embedded
agent's reference benchmark; delivery-role allocation stays unchanged. No
numerical quality threshold is inferred from the model choice.

The user deferred project-TOML agent configuration, GPT/OpenAI integration and
combined multi-model comparison reports to future sprints on 2026-09-19.
[ACT-0960](actions/ACT-0960-agent-configuration-and-model-comparison.md) owns that
follow-on. The immediate outcome is a Haiku run using the existing harness.

The requested first live slice is the two existing tasks, one attempt each,
using Anthropic Haiku 4.5 (`claude-haiku-4-5-20251001`), fresh disposable
projects and `--yes`, with a 120-second process timeout per task and no retries.
Disclosed material is the fixed eval prompts, generated project source and
harvested repository stdlib context. The existing compiler caps agent turns and
repair iterations; the timeout is not a hard monetary cap. Preserve all attempt
artifacts and record actual available metrics. The user's direction to get to
the Haiku run authorizes this bounded task execution, not a wider campaign.

The user supplied a private credential file after the initial environment
preflight. The first live attempt below reached Anthropic but was refused for
missing workspace scope; no model response was produced.

### Explicit exclusions and proposed carries

These entries remain owned and receive a recorded scope disposition. Approving
scope accepts only the stated exclusion, not a historical deferral rationale
that has become false.

| Item | Proposed disposition / reason | Owner and return trigger |
|---|---|---|
| LLVM / --release backend | Excluded by explicit user instruction | Future user-directed scope only |
| Full semantic /search — ACT-0952 | Feature implementation excluded from the core closure/eval scope; stronger indexing semantics and background macro execution remain unruled | spec/user, then design(src); return when those choices are approved. Existing interim-contract defects remain in scope. |
| /learn — 0052 and ACT-0951 | Tutorial implementation excluded; no complete user-ruled contract exists. Consolidate the two records' disposition | spec/user; return on a separately selected specification package |
| Natural List/Seq display — 0050 | Optional UX addition proposed outside core scope. Its design already exists; “no design” is not a valid carry reason | user scope selection, then design(src); include now only if selected before binary reservation closure |
| Network teaching example — 0463 | Optional teaching capability outside core scope; verify prerequisites and retain one explicit owner instead of treating it as a compiler defect | training with platform/test; return when the network lesson and its assets are selected |
| Ownership-ABI-independent live replacement — ACT-0953 | Stronger contract excluded; fix current-contract violations without silently removing the interim restriction | spec/user then arch; return on approval of the stronger promise |
| Project-TOML agent configuration, GPT support, multi-model comparison reports | Deferred by the user to future sprints so the Haiku baseline can run now | ACT-0960; future sprint scope |
| Automatic primer tuning or an unbounded live comparison campaign | Outside this bounded Haiku run | Separate future scope and spend decision |

Repeated-deferral history is reviewed per filing before a final disposition.
The longest-standing optional items above require explicit scope approval;
this table does not reset their counters. No technical or maintenance filing
is silently deferred simply because it is old or assigned to another roadmap.

ACT-0947 root-file disposition, ACT-0950 citation policy, ACT-0954 asynchronous
public API, ACT-0955 baseline formatting and ACT-0957 tooling residuals are
**included decisions/work**, not automatic exclusions. The owning roles present
any needed policy/API changes before implementation. User-owned notes are not
deleted without the user's decision.

## Evidence authority and existing baseline

The inventory links the original default and environment-recheck logs. Default:
5,909 run, 5,889 passed, 20 failed, one skipped. Separate environment recheck:
15/15 passed, including the fourteen sandbox failures. Six default-suite REDs
remain attributable to the S121 handoff; passing +1/+2 macro residual pins add
a known defect beyond those REDs. These are separate runs, not an aggregate pass.
No new baseline run is needed merely to write this plan.

| Evidence | Class / scope | Planned handling |
|---|---|---|
| Public replacement, IO and language behavior | Acceptance evidence for current requirements | Preserve existing RED/control pairs; add the narrowest discriminating missing conditions |
| Ownership balance, release and cancellation protections | Acceptance evidence or safety fence, per QA's exact allocation | Prove the selected witness detects the wrong outcome and passes its control |
| Failed-turn publication/recovery | Acceptance evidence for that contract | Repair the unarmed trigger; escalate a genuine testability gap rather than manufacture faulty behavior |
| /mem, broad censuses and model-quality scores | Diagnostic observations; /mem output also has its own specified behavior | Repair claims/instruments within their authority; do not convert their surprises into unrelated acceptance gates |
| Citations, API baselines, role wiring, accounting and inventory coverage | Maintenance checks on their own artifacts | Check changed surfaces and preserve distinctions in final reporting |

Before acceptance, run the appropriate default `cargo nextest run --no-fail-fast`
and isolated agent lane where selected changes affect it. Use network-capable
execution for socket evidence and record configuration. Run required local
build/lint/API/reference checks for changed surfaces. QA determines any extra
runtime diagnostic or feature lanes; do not equate the default suite with all
possible configurations. Final acceptance uses a freshly built invocation and
fresh sessions from the delivered tree, with exact provenance and results.

## Source ownership and filing closure

The inventory's source-overlap analysis is the input. Each implementation path
has one continuing owner; each filing has one primary **closure lead** below.
A lead coordinates other role-owned obligations and is not a declaration of
root cause or permission to edit another role's files. QA retains attribution
and evidence authority. Records with several consumers produce handoffs within
these streams, not separate ticket-shaped waves.

| Closure stream | Filings allocated exactly once |
|---|---|
| Binary / integration | 0553, 0604, 0694, 0740, 0745, 0789, 0793, 0795, 0798, 0800, 0818, 0863, 0868, 0889, 0898, 0914, 0921, 0927, 0933, ACT-0958 |
| Frontend / annotation closure | 0708, 0785 |
| Typecheck | 0762, 0776, 0777, 0779, 0794, 0799, 0869, 0913, 0924, 0929, 0935 |
| Backend | 0637, 0747, 0781, 0782, 0891, 0900, 0903, 0906, 0907, 0915, 0916, 0917 |
| Types / public contracts | 0931, ACT-0954 |
| Intrinsics | 0835, 0848, 0857, 0928, 0934, ACT-0956 |
| Primitives | 0859, 0932, 0936 |
| Platform | 0870, 0871, 0873, 0874 |
| Language-facing closure | 0815, 0821, 0823, 0841 |
| Delivery / evidence records | 0761, 0764, 0765, 0766, 0771, 0783, 0811, 0938, 0939, 0940, 0941, 0942, 0943, 0944, ACT-0947, ACT-0950, ACT-0955, ACT-0957 |
| Explicit UX scope choices | 0050, 0052, 0463, ACT-0951, ACT-0952, ACT-0953 |

All 78 FIXMEs and ten actions are covered. The public generic and sequence-IO
REDs remain recorded in their permanent tests; sprint does not file duplicates.
Their implementation owner is filled after discrimination. Agent evals are a
new sprint outcome, not a fabricated pre-existing defect action.

For source reservations, use the inventory's exact candidate paths. The binary
stream combines selected reload/session, macro/quote, result-handling and agent
production changes. Backend combines its result-root/Vec work with attributed
fixes; runtime/typecheck consume all their selected obligations once. A frontend,
platform, primitives or types record may need only verification and documentation:
an allocated filing does not require reopening correct production code.

Each design/dev/review invocation names one crate-shaped surface. Intrinsics and
primitives receive separate invocations when both need work; the binary owner
coordinates the executable-bundle consumer where needed. Solution test files,
shared helpers, QA plans and shared registers each receive one nominated writer.
Read-only work can run concurrently; source edits are serial.

## Audit dispositions proposed at this scope gate

| Finding | Proposed disposition | Owner / completion |
|---|---|---|
| src S121 F-1 — reload realization mismatch | Include authority/evidence reconciliation with the binary stream | arch/design(src)/QA choose the current required outcome; implementation, retirement or explicit alternative follows that decision |
| src S121 F-2 — contradictory module comment | Include narrow correction with the binary source-map visit | dev(src); check the current map, no new behavioral test |
| src S121 F-3 — large orchestration functions | Evaluate only the functions opened by selected work; no broad extraction campaign | design(src) chooses cohesive decomposition or a truthful exception; dev acts on the approved cut |
| Shared-role S120 residuals | Include only ACT-0957's six surviving recommendations | sprint coordinates owning roles and user choices; R2/R5 are not reopened |
| Older context audits in the inventory | Reconcile missing trails with later delivery/source | Existing closure streams own any verified remainder. Missing historical paperwork alone does not create a fresh compiler defect. |
| Platform naming carve-out in current GOT symbol documentation | Include bounded current-risk review | arch/QA establish whether the documented collision route remains constructible and protected before any new fix or closure claim |

The formal audit trails are amended only after the user approves these
Phase-1 dispositions. Until then the inventory and this plan hold the proposal.

## Architecture review — Phase 2 outcome

The [architecture assessment](s122-architecture-review.md) records the completed
Phase-2 dependency review. The phase approval table and decision checkpoints
below retain the user's authority; active reservations are in Phase 5.

## Role handoffs — planned for Phase 3

Phase-3 architecture, context design and QA readiness handoffs are complete;
the dispatch log records their owners and outcomes. The
[wave plan](s122-wave-plan.md) carries their implementation sequence. Phase-6
user-facing work remains unapproved and is not dispatched by this cleanup.

## Execution waves — Phase 4

The [execution wave plan](s122-wave-plan.md) supersedes the scope-stage W1–W4
placeholders. It sequences evidence/attribution and early checker discovery,
necessary compiler producers, intrinsics → primitives → backend → Binary/int,
document adoption/live-eval preparation, and final composition. One continuing
owner retains each source reservation through its dependent evidence and review.
The original 88-filing closure allocation above remains authoritative.

## Execution allocation and operations

The shared package owns the current role allocation. On 2026-09-11 the user
authorized returning future dispatches to Claude while leaving running work
alone. The restored historical allocation is Fable/high for arch, QA, audit and
review; Opus/high for design, dev, test, docs, spec, training and ops. Sprint
remains in this primary context. Shared adapters, checked-in host adapters and
package guidance agree; the earlier Codex dispatch log remains historical.

The test reference repair completed on Sol/high under its launch allocation:
provider session `da3850c7-de1f-4a03-9fce-40104bdb4ac5`, supported Codex transport.
No session is interrupted or re-labelled. New Claude work uses the shared
Claude transport with its normal permissions. This delivery-role switch does
not choose the embedded REPL-agent provider, live-eval data or budget.
Deployment, package publication, commits and pushes remain unapproved.

Opening convergence fast-forwarded the clean shared package from `1172631`
to `98436c9`; hold this revision through closure. Consumer integration adds
the package declaration, synchronizes provider/model/effort, removes the
coordinator from subordinate adapters, and composes the shared wiring check
with the existing repository verifier. Native architecture review runs
read-only alongside the bounded test-owned checker integration. No optional
Rust context standard is adopted. Contribution/publication remains a separate
close operation.

## Dispatch log

| Work | Role / identity | Model | Effort | Harness / outcome |
|---|---|---|---|---|
| Candidate triage of 88 filings | QA `/root/qa` | gpt-6-astra | medium | Native Codex; complete, read-only; integrated into candidate inventory |
| Architecture and dependency review | arch `/root/arch` | gpt-6-astra | medium | Native Codex; complete, source read-only; retained in architecture assessment |
| Opening consumer-check integration | test `/root/test` | gpt-5.6-sol | high | Native Codex; complete; shared check plus local wiring gate and 2/2 focused tests pass |
| Phase 3 boundary propagation | arch `/root/arch` | gpt-6-astra | medium | Native Codex; complete; canonical contracts and REPL diagram/SVG synchronized, source read-only |
| Phase 3 evidence and eval design | QA `/root/qa` | gpt-6-astra | medium | Native Codex; complete; condition-scoped readiness and eval design, user gates retained |
| Phase 3 Binary/int design | design `/root/design` | gpt-5.6-sol | high | Native Codex; complete; Binary/int design ready; D1 approved 2026-09-10 |
| Phase 3 intrinsics design | design `/root/arch/design` | gpt-5.6-sol | high | Native Codex; complete; intrinsics/runtime design and QA evidence allocation adequate |
| Phase 3 backend design | design `/root/design` | gpt-5.6-sol | high | Native Codex; complete; backend design and QA evidence allocation adequate |
| Phase 3 primitives design | design `/root/arch/design` | gpt-5.6-sol | high | Native Codex; complete; primitives design ready; D8 approved 2026-09-10 |
| Phase 3 current role-reference repairs | design `/root/design`, test `/root/test` | gpt-5.6-sol | high | Native Codex; complete; current role names and METHOD anchor repaired |
| Phase 3 shared document-checker contract | arch `/root/arch` | gpt-6-astra | medium | Native Codex; complete; approved D7 shared mechanism boundary and migration contract |
| Phase 3 shared document-checker evidence | QA `/root/qa` | gpt-6-astra | medium | Native Codex; complete; bounded fixtures, Cranelisp migration checks and read-only Magic validation |
| Phase 4 wave organization | sprint `/root` | primary harness | inherited | Execution waves and retained source reservations prepared |
| Phase 4 evidence sequence check | QA `/root/qa` | gpt-6-astra | medium | Native Codex; complete; no sequencing blockers; two Q-label references corrected |
| Earlier external attempt | QA, no provider session | configured fable | high | Process creation rejected by approval review; no disclosure; superseded by user-authorized native allocation |

## Scope completion

Completed: live inventory and existing executing baseline, QA classification,
source-overlap correction, exact 88-record closure allocation, proposed prior-audit
dispositions, eval outcome, named exclusions, planned source streams and staged
wave structure. Link/reference and allocation checks validate the planning
artifacts; they do not certify compiler readiness.

## Phase 2 checkpoint

The architecture assessment keeps the existing contexts and combines changes
by continuing source owner. Macro ownership reserves intrinsics **and
primitives** before its Binary/int consumer; reload uses the existing approved
typecheck producer and complete substitutions. Backend result-root/Vec work
stays in one backend reservation. The eval runner remains test tooling over
the actual REPL. Generic replacement, sequence-IO and platform-name reachability
still need discriminating attribution; static resemblance does not fix their
owner or mechanism.

S121's recorded approvals already authorize the reload consumer, nine typed
consume funnels and baseline-format migration. Phase 3 reconciles their exact
current producer/consumer obligations; unchanged contracts need no renewed
approval. Added or changed public contracts and actual generated baseline
diffs retain their explicit gates. The already-delivered annotated-Sexp disposal
arm is verified and reconciled, not implemented again.

**New API decision, ACT-0954:** architecture recommends removing the unused
`cranelisp::session_v4::CompilerSession::re_register_module(&mut self, module:
&ModuleFullPath) -> Result<bool, CranelispError>` wrapper. It queues work before
returning; synchronous watcher reload remains. This breaks the root library's
public Rust surface even though no tracked generated baseline covers it.
The review's packet B presents the removal and synchronous-compatibility
alternative. The user explicitly approved this exact removal on 2026-09-09;
implementation remains scheduled in the Binary/int delivery stream.

**Approved Phase 3 target:** reconcile per-surface designs, previously approved
interfaces and QA evidence deltas for the approved closure/eval scope. Use
native arch/QA on Astra-medium and design on Sol-high; spec on Sol-medium only
for genuine semantic questions. Design, QA planning and local inspection are
included; compiler implementation, permanent test authoring, paid/live eval
calls and external publication remain in their later authorization windows.
Return at design readiness with exact remaining API proposals, required user
rulings and the proposed Phase 4 wave-organization checkpoint.

Live eval endpoint/model, fixture disclosure, autonomy and bounded budget remain
choices before live execution. They do not block design of the local harness.
No filing is closed by this review. No compiler fix is claimed.

**Opening-convergence evidence:** package consumer check passes for eleven
subordinate roles with checked-in adapters. The composed repository gate passes
with eleven Copilot adapters, 26 principles and four first-read roles. Focused
`cargo nextest run --no-fail-fast --test role_wiring` passes **2/2**, including
clean-fixture and planted-fault checks. Package-owned conditions now run first;
local conditions cover only repository obligations. Historical W1–W7 labels in
S120 evidence describe the earlier verifier; current shared/local allocation
is defined by the executing checker.

The final live citation check covers **487 documents / 8,539 citations**, with
**zero findings**; `git diff --check` passes. These are maintenance evidence,
not a new compiler baseline. Compiler source remains at the scope checkpoint;
its six classified REDs are not claimed repaired. No commit or push occurred.

## Phase 3 coordination

Design work starts with the approved cross-context contracts, Binary/int's
combined consumer design and QA's evidence/eval allocation. Intrinsics and
primitives receive separate producer/consumer design invocations against the
same reconciled contract. Backend and typecheck receive only their selected
current obligations and attributed work. Completed source is not reopened by
a stale filing alone. Unknown roots retain an explicit reproduction and
attribution step before the Phase-5 correction design.

### Delivery-record decisions prepared for the checkpoint

- **ACT-0947:** all six named files were opened and current code, test, script
  and user-document references searched. The matches for `default/test.cl` and
  `testing/runner/test.cl` describe their actual stdlib counterparts, not the
  root copies. Recommend retaining `NOTES.md` untouched as the user's personal
  idea list, and removing the five probe/diff artifacts during delivery once
  their owning source streams confirm any useful evidence is preserved. The
  scratch patch covers intrinsics drop/lib/panic/rc/strand, so that stream
  verifies its source-backed remainder before deletion. No root file is deleted
  by the design phase.
- **ACT-0957 ownership choice:** approved 2026-09-10. Sprint owns host-entry
  guidance (`AGENTS.md`, `.codex/`, Copilot instructions) alongside existing
  adapter/hook ownership. METHOD §3.1 records the assignment; referenced
  technical content and shared-package contracts retain their owners.
- **ACT-0957 adapter choice:** approved 2026-09-10: “yes, no generator.”
  Retain the eleven checked-in Copilot role adapters and existing entry points;
  use the composed wiring check to detect drift from the shared role package.
  No adapter generator is included.
- **ACT-0957 provenance:** the adopted package is clean at `98436c9`, equal to
  the fetched `origin/main`; current consumer changes are still uncommitted.
  This proves availability of the pinned package, not that an uncommitted
  consumer can be recreated by cloning. Exact publication remains a close
  operation; unrecoverable historical dispatch attribution is never invented.

The approved D7 shared-mechanism pilot below supersedes ACT-0950's narrow
root-expansion proposal. QA owns evidence allocation and residual-finding
assessment; any proposed exceptions return separately to the user. Repairing
stale document links is maintenance work, not compiler acceptance evidence.

### Architecture readiness

The architecture owner propagated existing approvals to
`design/arch/bounded-contexts.md` and baseline guidance, and repaired the
REPL sequence diagram with its rendered SVG. No additional public delta was
identified. Primitive bodies and generated shims are private, so their typed
adaptation has no primitive Rust-baseline delta. The existing nine-funnel
approval includes Vec's typed callback. The original typecheck Packet C
post-implementation confirmation remains a historical provenance limit: its
signature approval is explicit, but the inspected archive does not separately
record confirmation of that generated line. Do not infer another approval
from unrelated later types API confirmations.

QA's [evidence delta](../tests/plan/s122-evidence-delta.md) owns the current
condition-scoped readiness and eval task design. It includes two newly fixed
prompts adapted from actual compiler-use cases; these are not presented as
verbatim recovered conversations. The unavailable safe-dial transcript does
not block this initial corpus.

### Binary/int design ready for checkpoint

[Selected Binary/int closure](../design/int/s122-closure.md) and its natural
subsystem amendments combine reload-demand realization, approved wrapper
removal, macro/quote handling and result-owner/memory observation. QA refined
the proposed private codegen-failure witness: it must compile a real prepared
target, observe changed GOT state while the resulting code owner is live, then
fail before publication and demonstrate safe restoration and recovery. A
closure that returns an error before meaningful compile state exists is not
that witness. The user approved this private evidence substitution on
2026-09-10, retaining the explicit public-trigger limitation.

The Binary/int pass verifies 345 citations in nine changed documents with zero
findings. It changes no compiler source or public baseline and adds no new
interface proposal. Backend's subsequent design invocation is separate; the
same design identity retains the completed Binary/int handoff for any
later evidence-driven refinement.

### Producer and backend designs

[Intrinsics closure](../design/intrinsics/s122-typed-consume-closure.md) retains
the already-approved public vocabulary and updates current same-crate callers.
The backend closure fixture remains with the backend owner. ACT-0956 uses a
module-level post-send barrier with observed initial admission, cancellation
before receiver polling and cleanup on assertion failure; no timing-based e2e
or production control is added. The inspected scratch patch contains no
undelivered typed-funnel work; its Launch-drop behavior is already delivered.

[Backend closure](../design/backend/s122-closure.md) consumes existing
`result_root` and `emit_rc_inc_guarded` helpers without adding helper visibility
or a public API. Its source-backed 0747 disposition retires the old one-finder
proposal: exact cleanup slots, carrier-keyed COW names and wider alias provenance
are different facts in the current code. This is a no-source-change design
resolution, not an unapproved carry. Formal filing closure remains later.

QA finds both evidence designs adequate. The existing typecheck auto-curry
design already specifies 0779's needed private polarity unit; the retained
typecheck dev pass supplies it and repairs the unsupported coverage claim.
No new typecheck design or per-seam mutation battery is required.

### Primitives construction decision

The [primitives consumer design](../design/primitives/s122-typed-consume-consumers.md)
completes the source-backed construction/traversal/storage census, including
bool/float producers and the existing error-return sentinel. Architecture's
[exact proposed amendment](s122-primitives-allocation-proposal.md) covers one
private produced-value adopter, parent-lifetime borrowed-field projection and
explicit owned-child storage transfers at named sites. The proposed set is
19 functions / 20 adoption sites, six borrowed projections and four storage
exits. Scalar payloads remain distinct from owned fields; reused children
receive their own retained obligation. No new public operation, allocator,
API, ABI, layout, cache or baseline change is proposed.

The user approved this complete trusted-base amendment (QA D8) on 2026-09-10:
“let's make an action or a roadmap item for the alternative full redesign of
the public allocation API's (per your above) and proceed with the limited
version proposed.” Arch and design propagate it into the standing contracts;
implementation and generated-baseline confirmation remain later.
[ACT-0959](actions/ACT-0959-public-allocation-api-redesign.md) records the full
public allocation API alternative for future sprint scoping. It is outside the
original 88-record inventory and is not a prerequisite for S122 delivery.

## Phase 3 decision checkpoint and Phase 4 proposal

Prepared design package: Binary/int, intrinsics, primitives and backend current
deltas; canonical architecture propagation; corrected REPL sequence source and
SVG; compact QA evidence allocation and two-task eval policy. Typecheck's
existing private-drain design is reused. No compiler source, test source,
golden or public baseline was changed during Phase 3. The wiring/source-test
diffs remain the previously verified opening-convergence work.

**Decisions reviewed one at a time:**

| Decision | Recommended choice | Boundary |
|---|---|---|
| D8 — typed primitive ownership closure | Approved 2026-09-10: exact private construction/traversal/storage amendment linked above | Arch and the two runtime design owners fold the approved amendment into their canonical contract/guard allocation; no new public API |
| D1 — failed-codegen recovery evidence | Approved 2026-09-10: armed private compile/publish failure witness plus public recovery controls and explicit public-trigger limitation | Preserve real compile/GOT mutation and restoration-before-owner-drop; do not claim public backend-failure reachability |
| ACT-0950 / D7 — shared document mechanism | Approved 2026-09-10: replace the narrow root expansion with the shared-mechanism pilot below | Specific residual exceptions, upstream publication and Magic cutover remain separate; maintenance findings do not gate unrelated compiler behavior |
| ACT-0957 — host-guidance ownership | Approved 2026-09-10: assign AGENTS/Codex/Copilot entry guidance to sprint | Recorded in METHOD §3.1; referenced content and source/test tooling retain their owners |
| ACT-0957 — adapter maintenance | Approved 2026-09-10: retain checked-in Copilot adapters with measured parity; no generator | Existing consistency check detects drift from the shared package |

D1 approval: the user answered “yes” on 2026-09-10 to the recommended
real-compilation failure-before-publication witness, rollback and next-turn
checks, retained public recovery controls, and explicit public-trigger limit.
This settles the evidence choice; Phase 4 was subsequently authorized on
2026-09-10.

### Approved D7 shared document mechanism pilot

On 2026-09-10 the user approved replacing the four-root citation expansion
with a shared-mechanism pilot. This supersedes the earlier D7 proposal.

- Discover every project-owned, nonignored Markdown document independently of
  the declaration, including new files. Require establishment through governing
  memories to root `CLAUDE.md`, or an explicit justified exempt classification;
  references between live documents resolve.
- Build one offline shared tool in `.agents`, with project-specific declarations.
  Combine establishment and document reference/anchor/section checking while
  preserving Cranelisp's source line-bound and symbol-presence checks. Retire
  duplicate local implementations after validation.
- Validate the candidate against both repositories, adopt it in Cranelisp and
  repair Cranelisp findings with their owners. Magic remains read-only during
  the pilot. Review the working tool and migration evidence before upstream
  contribution or Magic cutover.
- Present specific proposed residual exceptions separately; no blanket
  exemption or automatic baseline migration is approved. The earlier root-only
  measurement is historical evidence, not the new tool's discovery result.

The [shared-checker contract](../design/arch/s122-shared-document-checker.md)
and [QA allocation](../tests/plan/s122-evidence-delta.md) own the technical
contract and evidence. Host-guidance ownership and checked-in adapters without
a generator were separately approved on 2026-09-10. The Phase-5 record below
carries implementation, migration and remaining document dispositions.

### Final Phase-3 readiness and verification

Completed on 2026-09-10: approved decisions propagated, D1/D8 accepted, shared
checker and QA designs ready. QA distinguished local harness readiness from
unattributed cases needing reproduction; D6 remains the live-model gate.
The final historical citation ratchet observed 495 documents, 8,645 citations
and zero findings; that retired instrument is not evidence that the current
shared checker passes. User authorization advanced to Phase 4 that day.

## Phase 4 completion and Phase 5 request

Completed on 2026-09-10: five waves, retained surface reservations and evidence
exits settled; QA found no sequencing blockers. All 88 original filings were
allocated once; ACT-0959 stayed a separate future action. The user authorized
Phase 5 implementation. Current operation limits and pending transitions live
in the approval table, execution allocation and Phase-5 record.

## Phase 5 live execution

Authorized 2026-09-10. The uniform callable identity slice is implemented and
QA finds its evidence adequate for generated-baseline confirmation. Types
285/285, typecheck 903/903 plus the corrected residual assertion, backend
583/583, the unchanged six-mode RP4 witness, affected lifecycle controls, and
the final three public cache cases pass. All identity production and evidence
review findings are closed; source comments and live design prose are aligned.
Arch generated all seven guarded API surfaces: the types baseline has exactly
20 added and 2 removed lines for the approved packet; the other six are
byte-identical. The [types baseline](../crates/cranelisp-types/public-api.txt)
contains this delta. The user confirmed this exact generated diff on 2026-09-10 ("approved").
The identity checkpoint is complete; ACT-0955 formatting is separate.
The runtime producer/consumer implementation and its review corrections are
complete. Public macro balance, IO composition, `/mem`, quote and watcher
checks pass. Complete CLIF capture is restored and reviewed: 23 identity
renames preserve frame cardinality and instruction bodies. The matched
allocation observation falls from 1,143 to 46; the residual is unclassified.

Arch generated all seven runtime API baselines on 2026-09-11. Intrinsics alone
changes by **+38/−9**, matching the approved handle and consuming-signature
packet. The other six match, including the confirmed types identity baseline.
The [intrinsics baseline](../crates/cranelisp-intrinsics/public-api.txt) is
updated; the user confirmed exact diff `/tmp/s122-runtime-public-api.diff` on
2026-09-11 ("yes" to the generated runtime baseline checkpoint). QA finds the
runtime evidence adequate; this checkpoint is complete. D7 source parity and legacy mapping are complete; Dev completed the checker corrections. Test completed project integration and
verified its controls; the unsuppressed project conformance gate remains RED. ACT-0957 is closed separately.
Runtime owner records reflect the confirmation; no runtime retesting is allocated.

This is the runtime API checkpoint, not overall S122 or Phase-5 acceptance.
Evals, the shared checker, ACT-0955, remaining issue-record obligations and the
final whole-increment checks remain open. No Phase-6 work is authorized.

### Current reservations and next handoffs

| Work | Role / identity | Model / effort | State |
|---|---|---|---|
| Runtime before-state Q4/Q5/Q6 | test `/root/test` | Sol / high | complete: Q4 balance assertions intended RED (+2/+1), alias controls 4/4 PASS; Q6 scalar live +0 / rendered heap live +1 intended RED; Q5 current residual 1,143 saved with exact configuration; released |
| Intrinsics typed runtime / Q3 / Q11 | dev `/root/dev` | Sol / high | implementation complete: focused 8/8 PASS; full sandbox 346/349, exact three socket failures separately PASS with required authority; production check PASS; scoped review and allocated public integration complete; generated API confirmed 2026-09-11 |
| Intrinsics independent review | review `/root/arch/review` | Sol / high | closed: exact-function/site recursive guard corrected; same-count unauthorized-helper plant detected (`f328523a`), restored guard 1/1 PASS (`e0a1f21b`); one scoped re-review found no remaining issue |
| Intrinsics live design alignment | design `/root/design` | Sol / high | complete: producer/internal consumers, corrected guard and evidence reflected; downstream/baseline obligations retained; 41 citations / 0 findings |
| Primitives typed consumers / D8 | dev `/root/dev` | Sol / high | implementation complete: focused 11/11 and full 102/102 PASS; three prohibited-site plants detected/restored; source frozen and released |
| Primitives independent review | review `/root/review` | Sol / high | closed: trait-dispatch guard corrected, out-of-wrapper call plant detected, restored 1/1 PASS (`b89e61a5`); one scoped re-review found no remainder within lexical guard boundary |
| Primitives live design alignment | design `/root/design` | Sol / high | complete: delivered private conversions/D8 and evidence reflected, integrated/baseline obligations retained; 25 citations / 0 findings |
| Backend runtime consumers | dev `/root/dev` | Sol / high | Q4 correction delivered: observer (`350403d5`) confirmed two retains; corrected module2/2 (`284ab0b1`), final raw public macro pair2/2 (`0ce70208`), focused lifetime controls19/19 (`7777a8dc`) PASS. Check/fmt/diff pass, existing14clippy warnings retained; frozen/released; earlier helper/result-root evidence retained; complete golden selection reviewed |
| Backend runtime review | review `/root/arch/review` | Sol / high | original helper/result-root review complete; new Q4 ownership handoff review complete with no material findings; complete golden/public evidence accepted within scope; existing lint limits retained |
| Backend live design alignment | design `/root/design` | Sol / high | complete: delivered helper consumers/evidence reflected, integration/golden obligations retained; 57 citations / 0 findings |
| Binary/int runtime consumers | dev `/root/dev` | Sol / high | complete and released: focused modules 52/52 PASS (`82cbd387`), quote module/public 8/8 and 2/2, bootstrap roster 2/2 (`cf467c35`), check with tests PASS; clippy completes with existing warnings; whole-tree fmt retains unrelated drift in `src/repl/format_type.rs`, `src/repl/mod.rs` and `tests/spec_04_expressions.rs`; public macro pair now 2/2 after reviewed backend correction (`0ce70208`) |
| Binary/int runtime review | review `/root/review` | Sol / high | complete: two high Q7 findings (foreign overload ordinal replay and empty-entry demand loss), one medium Annotated-cell guard gap; no other runtime finding. The correction is frozen and its one finding-scoped re-review closed all three findings |
| Runtime public checks during host integration | dev `/root/dev` | Sol / high | ordered IO reduction/control 4/4 PASS (`dddc845f`), aggregate scalar driver PASS (`86114587`), strengthened `/mem` PASS (`c217a766`), public lifecycle/RP4 7/7 (`d8ae6fb8`), macro alias controls 5/5 (`41871783`) ; allocated runtime evidence complete, checkpoint QA adequate for generated-baseline confirmation |
| Q5 paired allocation measurement | test `/root/test` | Sol / high | final matched ownership after-state: alloc1198/dealloc1152, residual46 (`/tmp/s122-runtime-q5-final-after-dc78ddbe.log`), versus before1143/intermediate173; exact input/library/env/debug/cache posture retained, no threshold or zero-leak claim |
| Q7 persisted reload demand | dev `/root/dev` | Sol / high | corrected: revised actual-source witness detects omitted demand capture (`a3688227`, stale body 7), restored carrier PASS (`ed4f6f4c`); checks both concrete bodies before a later expression can remint them; public watcher and scoped review now complete |
| Q7 review correction | dev `/root/dev` | Sol / high | frozen/released: affected13/13 PASS (`236d2b5d`), including both reload pairs, Q1 replacement/rollback controls and Annotated completeness. Before pairs remain `048bcf37` and `284517d5`; diff/fmt PASS, finding-scoped re-review closed with no surviving findings |
| Runtime solution evidence | test `/root/test` | Sol / high | complete/released: watcher pair (`d18e302d`) direct PASS42/42, transitive subject FAIL7/7;initial golden results invalidated by whitespace-truncating extraction; corrected capture retains all frames,23 canonical renames and0 additions/removals/instruction changes; re-review closed. FinalQ5 residue46 retained; watcher selection corrected: publicpair2/2 (`c073e7f0`), affectedwatcher14/14 (`55802f4f`), provenance review closed; watcher order corrected and scoped review closed, extractor correction reviewed/released |
| Watcher selection review | review `/root/review` | Sol / high | order basket confirmed by complete-plan REDs (`beacb3e6`,0/2): downstream precedes dependency SCC, and simultaneous roots preserve consumer-first input order. Complete-graph SCC correction frozen: module2/2 (`a58ef193`), publicpair2/2 (`be88574b`), watcher14/14 (`977c5ba4`) PASS; finding-scoped re-review closed with no remainder |
| Primitives QA records | QA `/root/qa` | Astra / medium | complete: trait-dispatch correction and scoped review credited with lexical limits; backend runtime evidence/review recorded separately from identity evidence ; allocated public integration complete, generated baseline confirmed 2026-09-11 |
| D7 independent CLI fixtures | test `/root/test` | Sol / high | complete: five compact CLI cases authored; preimplementation exit 2 records candidate absence only, no behavioral acceptance claimed; `/tmp/s122-d7-cli-fixture-handoff.md`; source reservation released |
| D7 shared candidate / ACT-0957 package residuals | dev `/root/dev` | Sol / high | candidate delivered: CLI5/5, units5/5, transport103/103 PASS; source released. Declared gaps: Python docstrings, Magic section matching, absent-package unverified reporting; review and project observations follow |
| D7 full-project observations / fixture materialization | test `/root/test` | Sol / high | complete: Cranelisp820 / Magic748 documents, full reports exit1; reference totals invalid as debt due parser defects. Same-input source comparison provisional. Original CLI5/5; expanded14cases6PASS/8intendedRED; `/tmp/s122-d7-first-observation-handoff.md`; Magic status unchanged; source released |
| D7 consolidated correction | dev `/root/dev` | Sol / high | complete: final candidate `14cdce3b` passes 10/10 units and 17/17 CLI cases; four actual Magic section observations clear; source reservation released |
| D7 candidate inspection | review `/root/review` | Sol / high | initial review and one scoped re-review complete; final parser remainders resolved with module RED/GREEN and independent CLI evidence. Empty deinitialized/initialized Gitlink controls pass; QA adequacy follows final parity |
| D7 source parity and final declarations | test `/root/test` | Sol / high | complete/released: all 605 entries classified (507 mapped, 69 repairs, 29 explained differences); Cranelisp819 / Magic748 documents; final CLI21/21 PASS; two checker corrections and filename fixture alignment complete; eight parser establishment findings cleared and one actual owner link repaired; `/tmp/s122-d7-final-parity-and-mapping-handoff.md` |
| Runtime generated API | arch `/root/arch` | Astra / medium | all seven generated; intrinsics +38/−9 matches approved packet, other six unchanged; exact diff confirmed by user 2026-09-11; source/build released |
| Q10 derive/curry/def-application repros | test `/root/test` | Sol / high | complete: focused 2/2, 5/5 and 1/1 PASS; reservation released |
| Overload-family reordering repro | test `/root/test` | Sol / high | complete: generic subject intended RED, fresh reordered control PASS; reservation released |
| Overload-family correction design | design `/root/design` | Sol / high | implementation and evidence complete; exact generated types baseline confirmed by user |
| Q3 runtime attribution witness | dev `/root/dev` | Sol / high | complete: unique control PASS, shared-parent witness intended RED; reservation released |
| Q3 corrective design | design `/root/design` | Sol / high | complete: private shared-parent field-lifetime correction, no new public API |
| Q1 typecheck completion design | design `/root/arch/design` | Sol / high | separate typecheck invocation complete; monomorphisation §3.8.6 |
| Q1 typecheck producer completion | dev `/root/dev` | Sol / high | test-only retained-oracle repair complete: 48 old-key failures corrected, full crate 903/903 PASS (`bc3f7d54-f41a-4d87-8910-92f8eaf717dd`); reservation released |
| Typecheck independent review | review `/root/arch/review` | Sol / high | scoped re-review residual corrected to canonical owner prefix; focused 1/1 PASS (`2b772a0a-a7a5-4111-aba6-5b9978408548`), root verified exact assertion/log; closed |
| Q1/D1 Binary/int correction | dev `/root/dev` | Sol / high | RP4 corrected; public six-mode witness PASS (`9d5b51ba-f957-444a-bcc8-60e3d1253278`), affected lifecycle 7/7 PASS (`8799b247-1bb8-4a89-80e8-8614f736eec9`); review no production findings, minor comment repaired; released |
| Q1/D1 independent review | review `/root/review` | Sol / high | removed-arm finding closed; affected controls 8/8 PASS; permanent overload→ordinary regression 1/1 PASS (`e3792517-64a4-4915-b19d-d52b4fa5f02c`) after private types correction |
| Backend identity/cache consumers | dev `/root/dev` | Sol / high | complete: scheme-bearing consumers, canonical SCC owner projection and schema 29; full backend 583/583 PASS (`795667b5-9c17-47f0-9eb5-78e01505e93f`); independent review no findings; actual object/warm evidence is complete in the public identity/cache row below |
| Public identity/cache/link evidence | test `/root/test` | Sol / high | final cache 3/3 PASS (`e8b05c34-130f-4131-8dfb-6fbbd8aa9d40`), actual object-reuse observer armed and reviewed; ordinary all-mode control and reorder pair pass; released |
| Evidence allocation and attribution | QA `/root/qa` | Astra / medium | uniform identity evidence adequate for generated-baseline confirmation; all identity findings closed; no overall sprint acceptance |
| Public contracts and architecture | arch `/root/arch` | Astra / medium | types 285/285 PASS and reviews closed; generated types API +20/-2 matches approved packet, other six unchanged; generated identity baseline confirmed by user on 2026-09-10; checkpoint complete |

The user-requested [uniform identity assessment](../design/arch/s122-overload-reorder-publication.md)
is complete. Arch and Binary/int design recommend authored owner plus full
concrete callable type for ordinary, overloaded and generic executables.
Authored names and declaration selectors stay separate. `PreserveAbiFrom` is
withdrawn as the recommendation; stable keys reuse existing `PreserveAbi` and
remove its special cross-key metadata repair. Prefer deriving keys from settled
signatures over duplicate persisted signature fields. The exact types API packet is now ready: shared `concrete_callable_key`,
scheme-bearing `InstanceLink::instance_key`/`MonoDemand::instance_key`, and
`InstanceKeyError`; constructors and stored fields stay unchanged. The user explicitly approved this exact packet after clarifying symbol-table
ownership on 2026-09-10; coordinated implementation is authorized. The later
generated-baseline confirmation was explicitly approved on 2026-09-10;
coherent semantic cache invalidation is included. The user clarified that
identity belongs to symbol tables/types and runtime calls consume GOT slots.
Arch verified this boundary and removed mandatory wholesale backend renaming;
backend work is limited to dependencies on changed instance-key spellings.
The user agreed the readable executable-identity spelling
`(symbol [ParamType*] ReturnType)`, with recursively nested `(Fn [Type*] Type)`
and the existing concrete type forms. Architecture owns its canonical syntax
record. This syntax agreement does not approve an exact Rust public-API delta.
No implementation or baseline generation was performed by the assessment.
The permanent generic RED/control remains the behavior witness. Q3's
implementation and module evidence are complete; public integration, the Q12
fixture, local eval and shared checker remain pending. The larger runtime consumer tail retains the
[wave plan](s122-wave-plan.md)'s dependency order and continuing owners.

### Q1/D1 correction and evidence

- Ordinary replacement prepares the admitted base and its prior realizations
  before their first publication. No post-publication reload or dependent
  cascade is part of the correction. Q7 persisted-source reload is separate.
  Abandoned scheduler packet transport is absent from the delivered slice.
- Initial public no-import prior-realization case confirmed the new type/body
  but called the old body; the vector sibling exited with status 11. The
  no-prior-realization control passed. Logs:
  `/tmp/s122-q1-focused-dc78ddbe.log` and
  `/tmp/s122-q1-prior-realization-control-dc78ddbe.log`.
- Before the review correction, type-changing replacement evidence passed:
  module 3/3, public replacement 5/5, admission controls 3/3. Logs:
  `/tmp/s122-q1-d1-focused-dc78ddbe.log`,
  `/tmp/s122-q1-public-green-dc78ddbe.log`, and
  `/tmp/s122-q1-guard-controls-dc78ddbe.log`. These are recorded milestones,
  not acceptance of the later partial correction or the full sprint.
- Independent review found that demand capture omitted same-language-type
  generic body edits. QA confirmed this violates existing REPL §18.1 and
  attributed it to Binary/int. Public permanent RED/control: after realizing
  `(defn f [_] 7)`, same-type replacement with 42 still returns 7; the no-prior
  twin returns 42. Run `e3587bc8-9d56-4515-b008-038da0c1b931`, 1 intended RED /
  1 GREEN; `/tmp/s122-q1-same-type-red-control-dc78ddbe.log`. The original-candidate
  module RED independently observed the stale body at the same instance key:
  `/tmp/s122-q1-same-type-module-red-dc78ddbe.log`.
- The corrected [Binary/int design](../design/int/s122-closure.md) §2 captures
  all admitted replaced generic bases/families. Compatible same-type instances
  preserve their slot; decline or ownership mismatch rejects the complete
  same-type candidate. The caller-free language-type-change fresh-slot exception
  remains bounded. ACT-0953 is not expanded.
- The initial same-type correction exposed a missing ownership summary
  (`None`, versus the prior `Copy/Fresh`) and correctly refused slot reuse.
  Arch and designer verified that the old producer stopped after its demand
  drain. The correction completes normal private ownership inference inside
  that existing entry point before return, as recorded in
  [BC §2](../design/arch/bounded-contexts.md). Preserve inference eligibility,
  toggle/refusal behavior and staging-only publication; `None` remains possible
  for a refused/ineligible body. No signature, error, schema, dependency or
  public-baseline change is needed. Never reuse the old summary or weaken the
  Binary/int ABI guard.
- D1 now compiles the actual ordinary candidate, observes its GOT mutation
  while the JIT is live, then returns a prepublication failure. A separate
  private malformed-body fixture exercises production `CodegenFailed`
  attribution for the exact prepared target and a distinct incidental cause.
  Assertions cover prior definition/instance/slot/owner, introspection, backing
  product/file, warnings, notification state and a succeeding old-definition call.
- The original old-slot-only rollback assertion did not observe the fresh
  candidate cell. Dev added that observation and executed the deliberate
  compensation-removal plant: intended RED at the still-populated fresh cell,
  then restored the exact production call and reran GREEN. Logs:
  `/tmp/s122-d1-compensation-plant-red-dc78ddbe.log` and
  `/tmp/s122-d1-compensation-restored-green-dc78ddbe.log`.
- Typecheck completion is implemented in four selected paths; producer live/
  staging and private polarity cells pass 3/3, affected demand/error/curry
  controls pass 8/8, and the initial consumer subset passes 6/6. Logs:
  `/tmp/s122-typecheck-demand-ownership-red-dc78ddbe.log`,
  `/tmp/s122-typecheck-focused-green-dc78ddbe.log`,
  `/tmp/s122-typecheck-affected-controls-green-dc78ddbe.log`, and
  `/tmp/s122-typecheck-q1-consumer-green-dc78ddbe.log`. Architecture verified
  no public signature, schema, dependency or baseline delta.
- Root's fresh integrated Q1/D1 check passes 14/14: four module cases, seven
  public replacement cases and three admission controls. Run
  `aa761c38-ee11-453a-aaf3-0493ceac1b84`; log
  `/tmp/s122-q1-d1-integrated-after-typecheck-dc78ddbe.log`.
  Typecheck independent review and the one Binary/int finding-scoped re-review
  are complete; the new generic-family condition and final QA adequacy remain open. D1 proves private failure recovery and attribution; no legitimate
  public source-triggered backend failure is claimed.

### Completed solution-test cleanup

Test retained two explicit successful `vec-flatten` sequential-turn controls,
removed the duplicate replacement and unarmed diagnostic cases, removed the
obsolete public-wrapper Row 45, and strengthened the existing watcher fixture.
The watcher initially failed because a private import made both calls undefined;
exporting the imported value repaired the fixture. It now asserts successful
child completion and ordered 42 → update notification → 99.

| Focused evidence | Result | Nextest run |
|---|---|---|
| spec11 success controls and replacement subset | 5/5 PASS | `f09f7532-4f09-4aa4-bbbd-a7b5a2488d81` |
| watcher reload/order/completion | 1/1 PASS after fixture repair | `1e8aaaa8-cfcc-47ac-be8d-f54e8fcd616c` |
| facade rows after wrapper-test removal | 20/20 PASS | `21ee4c42-c8a2-401d-9e01-a87667be1131` |

### Other established evidence and queued work

- Q10: permanent current-shape evidence passes: supplied-free-variable curry
  pair 2/2, omitted derive shapes/control 5/5, function-valued def semantics
  and local callable control 1/1. Log
  `/tmp/s122-q10-current-shapes-dc78ddbe.log`. The initial Display punctuation
  oracle was corrected to the actual `Point(1 2)` form; it was a test-oracle
  mistake, not a compiler defect. QA confirmed no new production defect and
  identified clause-specific owner record repairs in its evidence delta. Direct application
  of a function-valued def remains a language/API choice under the current
  zero-argument macro contract; no new behavior is inferred.
- Q3: two nested Bind actions under `sequence-io` fail in REPL/run/link at stale
  RC decrement; explicit-bind, one-nested-action and empty-sequence controls
  pass. Focused batch 3 PASS / 1 RED:
  `/tmp/s122-q3-reduction-dc78ddbe.log`. Plain two-Pure sequence also passes.
  Intrinsics module run `34c74925-ba8e-4e74-bdab-f9d63b7c2d60` confirms
  the allocated shared-parent lifetime defect: the RC2 parent remains live
  after value 73 while its inner and continuation are no longer live; the
  identical RC1 control passes with balanced teardown. Log
  `/tmp/s122-q3-intrinsics-attribution-red-control-dc78ddbe.log`. Only module
  tests changed. QA accepts the module attribution; intrinsics corrective design
  can proceed. The exact path from the public sequence abort to this shared
  parent remains an inference until the retained public cases pass after the fix.
- Q12: static candidate `platform.hx` / ordinary `platform-x` maps to the same
  GOT name. QA allocated a minimal `platforms/hx/` fixture to a separate dev
  invocation and public coexistence/load/link/control cases to test. No fixture
  source or executing collision evidence exists yet; no naming rewrite is assumed.
- ACT-0955: arch completed the required direct positive/negative concurrency
  fence inventory and canonical HostCallbacks correction. Typecheck's existing
  visit also repairs `new_with_staging`'s stale Sync prose while retaining the
  single-threaded staging usage restriction. Test replaces baseline-string
  fences only as allocated. Generated baseline contraction still requires its
  later exact confirmation.

### Evidence and delivery-record dispositions

- QA closed 0766 and 0771 using the recorded opening stocktake: twenty current
  trace rows and spec annotations now identify existing passing evidence.
  The historical postmortem was preserved; both satisfied filing files were
  deleted. These are record repairs, not new executions.
- Arch closed ACT-0954 against the exact approved wrapper removal, source diff,
  and attributed test/review evidence. Scheduler registration and synchronous
  lifecycle reload remain. No seven-baseline change applies to this root wrapper.
- Arch retired 0940/0941: current METHOD already carries the approved callee-first
  migration and complete behavioral verification rules. Their obsolete command
  targets do not require extra policy. Both filing files were deleted.
- 0938/0939 retain their explicitly scheduled Phase-7 wording work; 0942/0943
  have narrowed remaining guidance reconciliation recorded by arch.
- 0931's historical constructor migration is superseded by the delivered
  lifecycle. QA found existing constructor slot/mint evidence and superseded
  the obsolete cost-measurement premises without claiming measured savings.
  The filing retains the narrow constructor-population/partition observation
  for the owning typecheck/backend visit.
- 0761's exact-balance lane is already delivered and passing. QA retained only
  two reused linked-execution observations for the runtime/test visit; no
  Cartesian matrix expansion is allocated.
- The original 88-row inventory is unchanged. Links for retired filings point
  to current closure evidence. ACT-0959 remains the separate approved future
  public-allocation redesign assessment, outside that original inventory.

### Review outcomes and overload-family follow-up

- The one Binary/int re-review accepted plain same-type replacement and the
  executed rollback detector. It found a surviving overload-family condition:
  a prior `OverloadArm` target contains a generation-local arm ordinal, while
  existing REPL §18.3 permits signature-preserving clause reordering. Reusing
  that ordinal across generations may address a different new clause. QA
  confirmed a legal generic one-/two-argument family wrongly rejects its
  unchanged clause reorder; the fresh reordered control passes. Permanent
  subject/control run `61a51698-402e-453e-ab3b-fb8fa8f32aa4`: 1 intended RED,
  1 PASS. Log `/tmp/s122-q1-generic-overload-reorder-red-control-dc78ddbe.log`.
  Existing callers still return 7/42 after rejection, so the test also requires
  successful replacement confirmation. No wrong-body or memory fault is claimed.
  The earlier concrete-family pair covers monomorphic behavior only.
- Independent typecheck review found no implementation, staging/refusal, API
  or Sync-comment defect. Its evidence repairs are complete: three greppable
  `// spec:` prefixes, one actual function-level polarity reversal plant,
  restored GREEN, and truthful census-comment wording. Root verified that
  `mono_collect.rs` differs only in comments after restoring the branch. Logs:
  `/tmp/s122-0779-polarity-plant-red-dc78ddbe.log` and
  `/tmp/s122-0779-polarity-restored-green-dc78ddbe.log`. QA accepted this evidence and closed 0779; no six-seam mutation battery is claimed.
- Typecheck designer retired source/evidence-satisfied 0762, 0777, 0794, 0799,
  0869, 0913, 0924 and 0935. Their current dispositions are in the
  [typecheck master](../design/typecheck/typecheck.md#985-per-filing-disposition).
  0776 remains with arch; 0929 retains only non-typecheck census arms.
  The original 88-row snapshot retains all rows with repaired closure links.

QA closed and deleted 0779 after checking the unit, intended plant failure,
restored success and repaired trace/comment evidence. Its durable disposition
is in PLAN and the QA evidence delta. For overload reordering, QA allocates
existing named callers of both distinct generic signatures across the edit,
plus a fresh-session already-reordered control; setup must be unambiguous and
test must record the actual first failure stage before attribution.


### Runtime before-state and scratch cleanup

- Test recorded Q4/Q6 intended failures and passing alias/scalar controls in
  `/tmp/s122-q4-q6-before-red-dc78ddbe.log`. Q4's two permanent balance
  assertions replace the historical nonzero pins. The Q5 exact isolated
  full-stdlib run is in `/tmp/s122-q5-full-stdlib-before-dc78ddbe.log`:
  1,198 allocations minus 55 releases, residual 1,143. This current observation
  is the paired-before measurement, not an acceptance threshold.
- ACT-0947 is resolved under the user's approved five-file deletion, retaining
  `NOTES.md`. Sprint opened all five files and checked source/test/script
  references; test independently found no live fixture or manual dependency.
  Removed root-level `default/test.cl`, `foo/test.cl`, `test1/Cranelisp.toml`,
  `testing/runner/test.cl` and `scratch_other.diff`. The distinct live stdlib
  self-tests remain. No tracked root `testing/` content remains, removing that
  directory's naming collision. The resolved action is deleted; its original
  inventory row remains linked here for accounting.


### Select ready-loser evidence closure

- ACT-0956 is resolved. Sprint checked the current `run_blocking_branch`
  publication seam and both permanent IO module tests; independent intrinsics
  review found no Q11 issue, and QA accepted this action's module-only evidence.
  The loser is first polled to Pending, then cancelled after successful channel
  publication and before receiver repoll; its nonzero disposer observes the
  exact value once. The paired winner retains disposal authority until caller
  release. Both pass in focused run `c302a849-f90c-4654-8b2c-6b7e16ae5d11`.
- The action is deleted and its original inventory row links here. This closes
  the requested Select evidence gap independently of the open intrinsics
  trusted-base guard finding and integrated runtime migration.


### Repro-before-fix guidance closure

- 0764 and 0765 are resolved against current composed guidance. Sprint opened
  both filings and their current METHOD and shared-role destinations;
  independent review `/root/review` confirmed no remaining guidance gap.
  The retired local command files are not recreated.
- METHOD §2.2 binds each discovered defect to RED → design → GREEN. The shared
  dev contract requires failing evidence before correction, a failing module
  test for a self-discovered defect, and reporting of evidence gaps to QA.
  The review contract checks established obligations and discriminating
  evidence, with an unmet current gate classified as blocking. Current guidance
  separately requires fresh, nonauthor review.
- The old proposed serial prerequisite and attempted-reproduction exception
  do not override the current METHOD: QA investigation proceeds in parallel,
  owns independent evidence allocation, and reconciles before closure. No
  duplicate rule or shared-package change is needed. Both filings are deleted;
  the original inventory rows link here.

### Shared-role audit residual closure

ACT-0957 is closed on 2026-09-11. Sprint reopened the audit §9, METHOD §3.1
and package CONSUMING.md; shared-package dev completed the wording and transport
cases, independent review accepted them, and
[QA accepted all six residual outcomes](../tests/plan/s122-evidence-delta.md#act0957-residual-outcomes--qa-closure-disposition).
The 103/103 transport result includes missing-contract refusal/restoration and
actual SIGTERM in both transports. Host ownership and checked-in adapters retain
the user's approved dispositions; live role guidance is current.

The published-pin promise excludes unpublished local changes. The historical
session-to-phase join remains unknown; recovered identities are preserved, not
extended by inference. No publication, fresh remote verification or live-provider
run is claimed. The action is deleted and its original inventory row points to
QA's closure evidence. D7's five checker findings and adoption work remain open.

### D7 current evidence and owner handoff

- Shared checker candidate `30692e8a` passes 14/14 module tests and 21/21
  independent CLI cases. All nine establishment issues are resolved: eight
  parser corrections and one REPL navigation repair. No inferred placeholder
  grammar was adopted; fenced examples retain the existing exclusion.
- Same-input source parity accounts for all 991 legacy identities (945 mapped,
  46 explained differences). All 605 baseline entries are accounted for:
  507 entries map to 506 candidate identities, 69 repairs, 29 explained coverage
  differences. No unexplained disappearance remains. The canonical
  [reconciliation evidence](../tests/plan/s122-document-checker-reconciliation/README.md)
  preserves exact legacy bytes and mapping; it is not suppression input.
- Read-only Magic comparison completed: 748 documents, 2,346 grouped findings,
  unchanged working-tree status. This observation does not accept project debt.
  Final parity provenance: `/tmp/s122-d7-final-parity-and-mapping-handoff.md`.
- Source/test ownership is released. Integration below is complete; remaining
  documents follow the approved retention policy. Earlier candidate counts and
  temporary declaration batches are superseded by the integrated observations.
- `NOTES.md` remains local, ignored and unchanged under the user's explicit
  instruction. No document exemption replaces that disposition. LLVM remains
  an unratified future input, with no implementation scheduled.
- Package publication, live eval, Magic mutation and Phase-6 advancement remain
  outside this authorization. Cleanup does not accept unresolved findings or
  authorize new historical policies.

### D7 implemented project integration

- `standing-documents.toml` is the active project declaration; the root command
  and `tests/citation_drift.rs` invoke the shared checker directly with no
  baseline. The old local implementation and active baseline path are retired.
- Final affected nextest run: two wiring/discovery controls PASS; the actual
  project conformance gate remains RED with exit 1, 820 documents, 6,022
  unsuppressed findings and 7,714 locations (38.345 seconds). Existing historical
  exclusions count 182 documents; proposed references 348; unverified 0.
  `/tmp/s122-d7-project-integration-final-nextest.log` records the exact run.
- The gate requires exit 0; findings and inspection errors remain failures.
  No pending exception or historical proposal was applied. The inherited review
  archive policy still needs its named collection established by the owner.
- [Reconciliation evidence](../tests/plan/s122-document-checker-reconciliation/README.md)
  preserves the old baseline bytes and all 605 mapping entries as evidence,
  never suppression input. Ignored local NOTES remain outside discovery.
- Source/test ownership is released. Step two is owner repair and explicit
  exception disposition against this implemented checker. No publication,
  package-pin change, Magic mutation or whole-sprint acceptance is implied.

### D7 canonicalization rule — user decision, 2026-09-11

The user's retain/fold/delete rule is incorporated in
[METHOD §3.1](METHOD.md#retention-and-maintenance). Routine owner consolidation
and establishment are authorized. The earlier 18-record architecture exemption
proposal is withdrawn; NOTES remains the retained, ignored local file.

### D7 first canonicalization batch

All 37 assessed originals are removed after comparison with their canonical
homes. This is document consolidation, not closure of historical compiler
findings or acceptance of the remaining checker output.

| Assessed material | Disposition and canonical home |
|---|---|
| 18 architecture audit/review/planning records | Current boundary, lifecycle, platform and introspection contracts already contain the useful commitments; Git retains the dated findings and execution evidence. No extraction or exemption needed. |
| Nine loose sprint records | Consolidated S121 closure/publication evidence and the exact scope of its record-only spec approval into [its archive](archive/sprint-121.md); the remaining approval/intake content was already there. The concreteness cross-check survives in [its canonical design](../design/arch/concreteness-types-first.md); obsolete prototype strategy, cancelled v3 brief and old decay snapshot remain in Git. |
| Eight context implementation/migration records | Binary/int, intrinsics, platform (two), backend, typecheck, primitives and retired runtime owners verified useful content against their current canonical contracts before deletion. No new technical commitments were extracted. |
| Two QA implementation plans | At that checkpoint PLAN retained the S66 inventory and S76 dispositions; current [assurance navigation](../tests/plan/PLAN.md) preserves the useful platform structural/crossing distinction. |

The reusable [sprint template](SPRINT_TEMPLATE.md) remains canonical and is now
established directly by root guidance and the project declaration. Its obsolete
combined-context example and audit scheduling placeholder are corrected.
Owned incoming references and affected test comments now name the canonical
information or verified historical Git locations. Declaration membership and
class purposes reflect the removals. No new reference exception or baseline
entry is added. NOTES remains unchanged and ignored.

The consolidated shared-checker run completes with exit 1: 783 documents,
5,474 findings across 6,881 locations, versus the pre-batch 820 documents and
6,022 findings. Existing historical exclusions remain 182; matched baseline
and exceptions remain zero. The retained template has no establishment finding.
The exact deleted-path scan finds no remaining local Markdown citations outside
verified historical URLs. Scoped owner checks and the final diff check pass;
no compiler behavior or test assertions changed, so no compiler suite was rerun.

Report: `/tmp/s122-d7-canonicalization-full.json` (SHA-256
`549e07b5ba78a4f0a53dd528985a72f9da950ca27778f7d2bc4e971c960a491c`).
Checker remains `30692e8a`; declaration SHA-256 is
`6b899e03758ff748860876102d4824c2cacbaba83596796be98bada1880ca327`.
Remaining candidate documents require the same individual owner assessment;
the count reduction is not acceptance of their unresolved findings.

### D7 document map — agreed, 2026-09-11

The user approved the information homes and principles: “this looks right. we
do need to close out a lot of documents with accumulated cruft.” The standing
map and retention policy now live in [METHOD §3.1](METHOD.md#31-where-things-live);
the temporary proposal is retired. QA owns a representative `tests/plan/`
consolidation and arch a representative `design/arch/` consolidation. Each
compares actual content, preserves unresolved obligations and records useful
missing substance in its canonical home before deleting superseded originals.
This resumes authorized Phase-5 document cleanup; it does not advance phases
or accept unresolved checker findings.

| Document consolidation stream | Native session | Allocation | State |
|---|---|---|---|
| QA current assurance and completed plans | `/root/qa` | Codex gpt-6-astra / medium | complete; 11 S82 plans removed, PLAN reduced by 709 lines |
| Architecture completed API-planning cluster | `/root/arch` | Codex gpt-6-astra / medium | complete; 3 packets removed, lifecycle current contract condensed; cross-owner reference integration complete |

The representative core set removes 14 completed documents and 4,769 lines:
QA's 11 S82 plans plus the old PLAN migration block account for 1,610 lines;
architecture's three S121 API packets and canonical-contract consolidation
account for 3,159. PLAN is 3,936 lines and lifecycle is 332 lines. No replacement
archive is created. Exact API signatures remain beside their public items;
current contracts retain useful rules, rationale and representation limits.

The broader PLAN histories, remaining architecture inventories and context
visit records still need owner assessment under the same policy. These results
establish a useful reduction method, not completion of repository-wide cleanup.
Dispositions and before/after comparisons are working verification records in
`/tmp/s122-map-qa-dispositions.md` and `/tmp/s122-map-arch-dispositions.md`.

Reference integration used retained native design (Sol/high), sequentially per
context, and dev/test (Sol/high), sequentially for source comments. All owned
repairs are complete. The 14 retired paths have no remaining local Markdown or
Rust citations; dated approvals and migration instructions use verified Git
records, while current API claims use canonical contracts and rustdoc. No
compiler behavior, test assertion, new exception or baseline policy changed.
NOTES remains unchanged and ignored.

Final shared-checker observation: exit 1, 769 documents, 5,329 findings across
6,707 locations. Compared with the preceding 783-document observation, there
are 145 fewer findings and no new finding identities. Existing historical
exclusions remain 182; matched baselines and exceptions remain zero. Seven
introduced section-reference ambiguities were repaired with explicit targets
and descriptive link labels; no suppression was added. Diff checks pass.
No compiler suite was rerun for documentation and comment-only changes.
Report: `/tmp/s122-map-final-check.json`, SHA-256
`60c806d854208e79045a5aa7b1932c1cb0ce040bc03068254fea332f410ec502`.
Remaining checker findings and further document consolidation remain open.

### D7 continuing standing-document reduction

The user requested continued cleanup after the representative pass. QA retains
`tests/plan/` to consolidate PLAN's remaining accumulated histories; arch retains
its architecture memory to replace repeated technical inventories with current
navigation. Both use the approved METHOD retention rule, preserve unresolved
obligations and hand off exact reference repairs for integration. These runs used native `/root/qa` and `/root/arch` on Astra/medium before
the user restored Claude for future dispatches; their completed work remains
attributed to those launch models.

The continuing pass reduces PLAN from 3,936 to 245 lines before final retention
navigation repairs, and architecture memory from 12,032 to 1,431 words. Neither
creates a replacement standing report. Exact active closure evidence stays in
its existing PLAN/S122 homes; dated references move to verified Git records.

| Continuing reference integration | Provider/model at launch | Session | State |
|---|---|---|---|
| Test comments and test-owned guidance | Codex Sol/high | `da3850c7-de1f-4a03-9fce-40104bdb4ac5` | complete; all 65 mapped references repaired, comment-only snapshot comparison passes |
| Backend design citation integration | Claude Opus/high | `1db92e97-d3fc-4cc7-8c1e-8417a351c013` | complete; canonical decisions and dated attribution references repaired |
| QA retained-trigger navigation check | Claude Fable/high | `41bdcc3e-e585-40f9-9cee-94c51ca10148` | complete; 0859 trigger navigation and four unclassified leads preserved |

The supported Codex transport supplied the test role after the native harness
reported its agent-thread limit. Both new Claude dispatches follow the restored
shared allocation. The shared consumer check and repository wiring verifier
pass with eleven roles and zero local findings; no running session was stopped.

Final owner integration leaves PLAN at 269 lines; it retains 0859's existing
future-triggered obligation through canonical navigation and exact provenance
for four unclassified leads. Architecture memory remains 1,431 words. All 65
affected test references are repaired; an independent snapshot comparison of
28 Rust files finds only comment changes. Current S122 closure links remain
current rather than pointing to a pre-S122 Git version. PLAN is now declared
explicitly under QA and established by test guidance. No new exemption or
baseline was introduced. Pre-existing standalone decision and context-record
debt remains in scope for later owner consolidation, not silently closed.

Claude executions completed on reported `claude-opus-5` and
`claude-fable-5-1`; the prior Codex execution completed on Sol/high. Future
Claude handoff files use ignored `.local/` to fit its normal file-tool scope;
source and model permission defaults are unchanged.

### D7 exact-anchor matcher correction

Integrated cleanup exposed a shared-checker defect: a unique exact Markdown
heading anchor is reported ambiguous when an unrelated numeric table label is
a prefix. The minimal reproduction has one `1. Target` heading and one table
cell `1`; selector `#1-target` incorrectly reports two matches. Three current
links have exactly one verified GitHub heading target but trigger this defect.
Reproduction: `.local/s122-numeric-anchor-reproduction.json`.

This is an instrument correction within the authorized document-conformance
stream, not an exception for the affected documents. Test owns the bounded
regression evidence on Claude Opus/high, session
`c0e41e12-4220-44bd-a6a4-1914d54f2048`: baseline 14/14 PASS; expanded suite has
one intended failing test (two subtest failures) and fifteen passing tests.
Controls cover genuine ambiguity, missing fragments, table shorthand and
abbreviated links to annotated headings. Dev completed the matcher correction
on Claude Opus/high, session `7f7675e9-1821-4521-a4c8-cce4c12144aa`: 16/16 shared
unit tests and 21/21 CLI tests PASS. Exact fragments now take precedence;
fallback matching remains when no exact match exists. Source is released.
QA judged the correction adequate on Claude Fable/high, session
`0b34c718-0542-4418-8abf-864f8437cc31`; no further independent review is warranted
for this bounded maintenance correction. No compiler behavior or public API
changes are involved. Evidence: `.local/s122-anchor-test-result.md`,
`.local/s122-anchor-dev-result.md` and `.local/s122-anchor-qa-result.md`.

Final integrated observation: 769 documents, 5,111 findings across 6,462 locations
(exit 1), down 218 findings from the preceding 5,329-finding pass, with no new
finding identities. The matcher removes the three reproduced false positives
and one additional candidate-inventory citation: its exact sprint heading
`Evidence and delivery-record dispositions` previously collided with table
label `Evidence`. Root verified this fourth match at the same resolver seam;
it lies outside the roles' Markdown-link probes. No genuine ambiguity was
silently accepted. Historical exclusions remain 182; matched baselines and
exceptions remain zero. Shared consumer and local role wiring checks pass.
Report: `.local/s122-next-verified-check.json`, SHA-256
`312413db05d1ef5dcd4d63a5f0faa039f3b0876a00d54d1547a7cd50e9bb788e`.

QA retains a separate suspected instrument defect in numbered section citations:
numeric table labels may cause analogous ambiguity in the non-fragment matcher.
Before dispositioning that finding family as document exceptions, test must
establish a minimal reproduction and discriminating controls; attribution and
scope remain provisional. This is the next checker-triage dependency, not a
closure of those findings. Further document consolidation and Phase 5
acceptance remain open. NOTES remains unchanged and ignored; no commit or
publication occurred.


### D7 legacy records and section-citation triage

Continued cleanup is authorized within Phase 5. This pass retires five obsolete
documents: the three top-level architecture legacy files, the combined-runtime
record and the S51 backend cache migration design. Useful type-identity and
shared-table rules were extracted into existing canonical contracts; dependent
citations and collection declarations were repaired. ROADMAP falls from 27,180
to 1,408 words by linking closed outcomes and retaining current future conditions.
No replacement archive or permanent cleanup report was created.

The section matcher no longer emits empty normalized names. Its independently
established four-leg RED now passes: 18/18 shared units and 21/21 CLI tests.
QA judged it adequate and corrected the original numeric-row attribution.
Newly visible missing sections and basename ambiguities are instrument findings,
not automatic document exceptions. Numeric-row precedence and selector
capture remain separate policy/intake questions; no suppression was added.
Evidence: `.local/s122-section-test-result.md`,
`.local/s122-section-dev-result.md`, `.local/s122-section-qa-result.md`.

Observability now names current activation and mode behavior. QA retracted the
redundant GOT Send/Sync assertion proposal and classified FIFO ring overflow as
existing tested behavior. The IO activation mismatch and worker-thread trace
limitation remain explicitly distinguished from compiler defects; their final
design disposition is retained in the observability contract. Five Rust files changed only in
comments, verified against the owning streams' working-tree snapshots. No
compiler suite, compiler behavior change, commit or publication is claimed.
NOTES remains unchanged and ignored.

All dispatches use the restored shared Claude allocation at high effort.
The machine lifecycle record is `.local/subagents.jsonl`; results and snapshots
are retained under `.local/s122-*` for this in-flight pass.

| Role work | Reported model / launch alias | Session | State |
|---|---|---|---|
| test | claude-opus-5 | `5739abf7-b4a9-4758-b53d-0b1d57646631` | success |
| arch | claude-fable-5-1 | `ac5cd260-ecc9-4530-8cc1-e0f178f0d2e1` | success |
| design | claude-opus-5 | `21fc4a9f-7211-487c-bd67-8b0f3101ea2d` | success |
| design | claude-opus-5 | `33647e8a-7d9b-4249-b642-3247d4791803` | success |
| dev | claude-opus-5 | `2deb5fbe-d8d0-4ff0-92b1-3b77cf1aea16` | success |
| qa | claude-fable-5-1 | `a7754065-2a54-485b-aa40-df0a229c2beb` | success |
| design | claude-opus-5 | `c8993635-d2f4-40f6-9e8b-16e409a17df9` | success |
| arch | claude-fable-5-1 | `f37e5a9d-92d2-41d7-a28e-d8f52325fbb8` | success |
| design | claude-opus-5 | `f918bd97-4584-4b73-8bad-a6616cf07441` | success |
| dev | claude-opus-5 | `5f271fc7-1572-4cf6-a21d-b888c18532fd` | success |
| dev | claude-opus-5 | `9162114f-1c8b-4c7a-9d57-ddc09ea131d8` | success |
| qa | claude-fable-5-1 | `b240ab8c-3014-4e58-b881-6fb3fecd6791` | success |
| design | claude-opus-5 | `e6094ed9-9cc6-4606-9efa-750ec8a5204a` | success |
| design | claude-opus-5 | `26737d4f-4cca-4233-8301-bd6a3652fc81` | success |

All owner reservations are released. The backend master no longer duplicates
closed tracker rows; it preserves one newly exposed public-contract question:
`Linker::get_symbol` is implemented with `&str` while older design intent names
`&LinkerSymbol`. Arch must settle the design/API direction before any API
change; none is authorized by this cleanup. The observability guide retains
the IO activation mismatch and unmet worker-event visibility promise without
adding redundant assertions or counters. No compiler implementation follows
from those document observations in this pass.

Final comparison completed on an unchanged tree of 764 documents. With the
old matcher, document cleanup reduces the prior 5,111 findings to 4,893. The
corrected matcher reports 3,365 findings at 4,357 locations: it removes 1,878
false ambiguities and exposes 325 missing sections plus 25 basename ambiguities.
Two misbound architecture citations were repaired with explicit heading links;
no new document-edit finding survives the corrected matcher. Existing debt
still makes the checker exit 1. No baseline or exception was added.

Evidence: `.local/s122-cleanup-stable-summary.json` and the before/after reports;
after-report SHA-256 is
`cddef931311274dc00e5a96132fbe5b653f4201a239576c6accbee3e69252f71`.
Consumer and role-wiring checks pass (11 roles, 11 adapters, 26 principles,
four first-read documents, zero wiring findings). Both repository diff checks
pass. NOTES integrity and ignore status are unchanged. This evidence precedes
this ledger-only result entry; it does not imply sprint closure.

### Local checkpoint and continuing cleanup

The user authorized a local checkpoint and continued Phase-5 document cleanup.
The shared package is saved on its consumer branch `cranelisp-s122-checkpoint`
at `eda9132`; it is not published. The superproject retains the published
package revision `98436c9058241458317d4b96a78f04f52ace9476` as its Gitlink, per
the package contribution policy. Reproducing this in-flight checkpoint's shared
checker and Claude allocation requires that local package branch. NOTES remains
on disk, unchanged and ignored; the checkpoint removes its tracked copy.
This is a work-in-progress checkpoint, not sprint acceptance or closure.

Checkpoint `7f834bf6` is complete. The next document cohort reserves
the legacy-plan collection and its minimum QA-owned integration to `qa`; four old int
records (codegen convergence, pipeline convergence, persistence collapse and
race closure) and their minimum int-owned integration to `design`. The source
and shared checker remain unchanged. Dispatch results follow on completion.

| Cleanup owner | Provider/model | Effort | Session | State |
|---|---|---|---|---|
| qa — legacy assurance records | Claude/claude-fable-5-1 | high | `4046d1bc-c463-4053-970d-eaf4ac084eba` | complete |
| design — int migration and race records | Claude/claude-opus-5 | high | `cc87a0ac-f2d2-4616-921a-a3589c7d2ab6` | complete |

The candidate set starts at 15 documents, 8,709 lines and 80,905 words.
These counts describe the assessment scope, not a deletion target.

The owners retired all eleven legacy QA plans and three int migration records.
The race-lineage record retains its useful evidence, rationale and live cited
anchors in 283 lines, down from 3,214. The dependency queue-priority rule now
lives in the int master. QA preserved the never-authored S61 inline-ADT
equivalence matrix as an unclassified historical lead in current allocation.
Reports: `.local/s122-checkpoint-qa-result.md` and
`.local/s122-checkpoint-int-result.md`.

Remaining source-currentness leads: int master code-publication/lifetime
sections and concurrency publication terminology; QA's unannotated blank-line
case and missing CLI conflict test; design-based worker unit annotations. These
are not new implementation authorizations or claims of reproduced defects.

Citation-only handoffs completed through Claude Opus 5/high: test session
`b299b6fb-65dd-4a93-8bcd-0eeb4347c447` and dev (int) session
`53eae155-ee9f-4416-8eb8-0bd27ac9c42b`. Root integrates the owning reports'
mechanical design/QA citations, historical checkpoint links and declaration
removals. All four streams released their reservations. Ten changed Rust files
have identical non-comment content against the checkpoint; no compiler suite
was needed for this document/comment-only batch.

Final stable-tree check: 750 documents, 2,956 findings at 3,660 locations, down
from 3,365 findings. Exactly 409 identities removed and none added; no baseline
or exception added, historical exclusions unchanged at 182. Existing debt
keeps the checker at exit 1. Report: `.local/s122-checkpoint-final.json`, SHA-256
`b64fe85486c89a708c0c1d7f60517bc0c7c1417ef7f35322bec3ff63f6e5b49e`.
This check precedes this ledger-only completion entry. Consumer/wiring and diff
checks pass. NOTES integrity and ignore status remain unchanged.

The test-to-spec diagnostic improved by one malformed citation; its six
mis-cited and four malformed entries remain pre-existing intake. Its support
for the split REPL-spec pointer also corrects the earlier assumption that all
pointer-form citations require repair. No annotation-policy change follows.

Next consolidation candidates are the S64 harvest working audits and stale QA
registers, assessed against current evidence before retirement; int master
source reconciliation remains a separate owned pass. Further cleanup after
checkpoint `7f834bf6` is uncommitted. No publication or phase transition occurred.

### Harvest-record consolidation after checkpoint

The user authorized checkpoint and continuation; local commit `b602708e` saves
the preceding completed cohort. Shared package `eda9132` remains local and
unchanged; the published Gitlink is retained. QA owns the S64 harvest audit
cohort and three older QA registers, plus minimum QA-owned integration, as
one stream. Root handles cross-owner mechanical citations and declaration
changes. No source behavior, policy, publication or phase change is authorized
by this document cleanup.

QA dispatch: Claude Fable/high through shared transport, session
`0a4b6465-619b-4507-b5aa-087c85255898`, complete (reported Claude Fable 5.1). The candidate inventory is
`.local/s122-harvest-candidates.json`; the prior-tree reference inventory is
`.local/s122-harvest-crossrefs.json`. Both are temporary working inputs.

QA retired all seventeen candidates after source and historical-disposition
checks: fourteen harvest audits, the old coverage snapshot, negative-coverage
register and ledger stub. PLAN retains the Vec/List negative-coverage leads
and the existing S119 traceability practices; Risk 11 retains the marshalling
gaps. The S119 close-report band ratio was not practised in recent closes; its
application or deliberate retirement remains a Phase-7 coordination question.
No new evidence policy or tests were introduced here.

QA report: `.local/s122-harvest-qa-result.md`; all QA reservations released.
Test integration uses Claude Opus/high, session
`1677472e-98e9-42bc-80d6-cf8165f0c1be`, complete (reported Claude Opus 5). Root applied the exact
retired-ledger navigation handoffs in root guidance, design and audit records.
The shared checker/declaration is unchanged; none of the retired files had
a declaration to remove.

The QA tools' dormant harvest-crosswalk branch and stale linter-origin
docstring remain a separate tooling cleanup; no code changed in that tooling.
Dated QA plans remain candidates for further retention assessment.

Harvest integration is complete; both role reservations are released. Test
repaired 60 references across 28 files while preserving all test-side spec and
defect annotations. Root completed the three metadata/message references
outside the comment-only brief: the ignored benchmark's reason now names the
current design, and the suite-polarity comment/reminder names the open-filing
rule. Ignore status, test assertions and script control flow are unchanged.
The obsolete inline-FIXME migration sentences were superseded by root's
current filing protocol; their removal creates no new obligation.

Final stable-tree observation: 733 documents, 2,625 findings at 3,208 locations;
331 identities removed from the prior 2,956, none added. No baselines or
exceptions added; historical exclusions remain 182. The checker still exits 1
for existing debt. Report: `.local/s122-harvest-final.json`, SHA-256
`99a555176db331f5f33a34b4745a5e375af39e24f5361142dd4d9099d2739661`.
The snapshot precedes this ledger-only completion entry.

All 27 changed Rust files were compared against checkpoint content with only
comments and the one named ignore-reason citation allowed to differ. Script
syntax and unchanged control flow were checked; consumer/wiring and diff
checks pass. No compiler builds or runtime suites were run for this batch.
NOTES remains unchanged and ignored. The seventeen retirements remove about
97,000 net Markdown words across the changed surface. Changes after checkpoint
`b602708e` remain uncommitted; no push or phase transition occurred.

### Early QA-plan consolidation

The user authorized checkpoint and continuation; commit `7e56a81c` saves the
completed harvest cohort. QA now reserves the eleven S84–S97 plan candidates
and their minimum QA-owned integration. Test independently inspects incoming
reference contexts and waits for QA's disposition before editing its own
surface. Root integrates other mechanical references and verifies the result.
No compiler behavior, new control, publication or phase change is in scope.

| Owner | Provider/model | Effort | Session | State |
|---|---|---|---|---|
| qa — early plans | Claude/Fable | high | `0c9e3812-3f30-4412-b872-dde600d65283` | interrupted: provider limit |
| test — incoming references | Claude/Opus | high | `a38201b4-738f-4cc4-81a5-01d5bd7fa778` | interrupted: provider limit |

Both dispatches stopped with Claude API 429, terminal reason `api_error`,
before any candidate, source or test edits. The provider reports the session
limit resets at 20:10 Australia/Melbourne on 2026-09-11 (10:10 UTC). QA reported
Claude Fable 5.1; test reported Claude Opus 5. All eleven candidates are
byte-identical to checkpoint `7e56a81c`. No retention decision or partial
inspection is accepted as completed evidence. The last full checker result
remains 2,625 findings across 733 documents.

Resume this same reserved cohort through the required Claude allocation once
capacity returns. Briefs, candidate list, cross-reference inventory and provider
results are retained as `.local/s122-early-plans-*`; they are working inputs,
not new standing records. No model substitution, publication or phase
transition occurred. Only this coordination entry changed after the checkpoint;
NOTES remains unchanged and ignored.


On 2026-09-18 the user authorized resumption: finish this cohort with QA first,
then one settled test-reference handoff, verify and checkpoint, and reassess
current standing-document reconciliation and the outstanding local eval
deliverable. Fresh QA dispatch uses Claude Fable/high, session
`621de07c-1394-416a-850f-8b66648d18c0`; complete, reported Claude Fable 5.1.
QA retired all eleven plans, extracted existing timing-witness practice and the
mode-helper range limit, and retained three unclassified evidence leads in
PLAN. All QA reservations are released. Test integration uses Claude Opus/high,
session `6bcc2c1f-69ca-4309-b281-4dd2b2f9c83c`; complete, reported Claude Opus 5. Root removed the five
obsolete plan citations from platform comments, retaining their design references. The preceding provider-limit entries remain historical. Live eval
configuration and budget remain separately gated.


Both owners released their reservations. Reports are
`.local/s122-early-plans-qa-result.md` and
`.local/s122-early-plans-test-result.md`. QA retained three unclassified leads:
REPL auto-IO parallelisation evidence, the unfinished timing-witness sweep,
and module-preamble read/refusal coverage. Their current observations and
provenance are in PLAN; retirement does not close them or allocate new tests.
Test repaired 13 source files and replaced duplicated test-run timing guidance
with a reference to root authority. Root integrated three platform-source files.

The final stable-tree checker observes 722 documents, 2,522 findings at 3,091
locations: 103 identities removed, none added. It still exits 1 for existing
debt; no baseline or exception was added, and historical exclusions remain 182.
Report: `.local/s122-early-plans-final.json`, SHA-256
`ae69f10b1077863bc4fa6d65879c6baa111b9b522446a5efdc1cb291a0156e41`.
This observation precedes the ledger-only completion update. All 16 changed
Rust files preserve non-comment content; test counts, ignore status and spec
anchors are unchanged. Consumer/wiring and diff checks pass. No runtime suite
was run for comment/document edits. The batch removes about 64,000 net Markdown
words. NOTES is unchanged and ignored; the published package Gitlink is retained.

Reassessment: finish the local REPL-agent eval runner/corpus/grader already
allocated in the wave plan and QA delta before selecting another broad
historical cleanup cohort. No runner or task-fixture implementation was found
in the current test/script surfaces. Its two-task local stub validation can
proceed within Phase 5; live execution still requires D6. Reconcile current
integration-design publication/lifetime claims in an owned pass before relying
on them for acceptance. Test's report retains concurrency-comment debt, the
literal-token ordering question and the bare-alias list-coverage lead; none is
silently converted into a compiler defect or a new test obligation here.
The next checkpoint saves this completed cohort; no push or phase advance.


### Local REPL-agent eval implementation

After checkpoint `660f0920`, the user directed continuation of the already
approved local runner, two-task corpus and stub validation. Test owns the
combined implementation and serial build/test reservation, using the existing
QA readiness and evidence allocation. Claude Opus/high session
`414eaaf4-eb09-4330-95fa-584b6fc37b7c` completed (Claude Opus 5). Working brief and results are
`.local/s122-local-evals-test-*`. Independent review and QA adequacy follow the
working deliverable. Live calls remain gated by D6; no new production seam,
commit, publication or phase advance is included in this dispatch.


Test delivered the process runner, two task manifests, stub/parser self-checks
and usage guidance. The report at `.local/s122-local-evals-test-result.md`
records a fresh isolated agent build, 17/17 expected self-check outcomes,
2/2 generic normal-run outcomes and three effective grader-fault detections.
All source/build reservations are released. These observations validate the
local harness only; requested-API compliance remains a separate source review,
and no model-quality baseline is claimed. Independent review completed on
Claude Fable/high, session `c06c8d87-e6f0-4adb-a6e8-85a22f8b5fd5`.


QA sessions `2954b139-b344-4ad3-8286-dafd60c69ee9` and
`3257b79c-ec13-4b42-a31f-0b5f374ea874` (Claude Fable/high) settled the review
findings and the coordinator's list-encoding counterexample. Both completed
and released the evidence delta. Their reports are
`.local/s122-local-evals-qa-result.md` and
`.local/s122-local-evals-qa-probe-result.md`. The corrected allocation narrows
automatic attribution to supported observations and requires exact per-element
list comparison. Test now owns one L+D correction batch, including the
counterexample's executing before/after evidence and offline live-readiness
repairs: Claude Opus/high session `3123b785-4182-4528-919e-65e1b0faa308`.
QA accepts local E1 completion on the prescribed green evidence without another
review cycle. Live E2 evidence and user D6 configuration remain outstanding.


The L+D correction completed on Claude Opus 5, with the intended four RED
mismatches followed by 18/18 GREEN outcomes. Report:
`.local/s122-local-evals-test-correction-result.md`. The real counterexample
List 1,1,13 passed the old encoding and fails the exact-value probe; 1,2,3
remains green. Offline configuration refusals and report survival after a later
attempt failure also pass. No compiler source changed.

A source-backed endpoint follow-up resolved the reported registry-access gap:
this build uses Rig 0.39.0's Ollama `Client::new`, not its environment-reading
constructor. Test corrected the report to name the actual localhost endpoint
and label the override as ignored. Session
`e446ebe2-537a-4ecb-9ca7-8d7dd4ad1b8c` (Claude Opus/high) completed; report:
`.local/s122-local-evals-endpoint-result.md`. The final runner self-check is
18/18, exit 0; report `.local/s122-agent-evals/endpoint-green-self-check/report.json`,
SHA-256 `16a5b05956937bcfa61b486aea7a8de768cc1f5e5b3e04bfddfd90e88374a4a3`.
All source/build reservations are released. QA's stated local E1 completion
condition is met. Usage lives in test guidance; E2 remains unobserved.

The stable-tree document check before the final endpoint-only source repair
observed 722 documents and 2,519 findings at 3,088 locations: three identities
removed, none added, no suppression; historical exclusions remain 182. Report:
`.local/s122-local-evals-final.json`, SHA-256
`3876e5ba6923565bbf911f0cba75d212f5d7bb4d2c0a996c73029d623f061dde`.
The endpoint repair changed no Markdown; subsequent ledger edits receive scoped
reference/diff checks. Wiring checks pass; NOTES remains unchanged and ignored.
Changes are uncommitted; no live calls, push or phase advance occurred.

Remaining product observations for QA intake before any affected live use:
the provider guide claims an Ollama endpoint override the current constructor
ignores, and repair-provider errors can be logged as model decline. The local
runner reports these paths conservatively; it neither fixes nor attributes a
compiler defect from them. Live readiness still requires D6 and the committed
runner/fixtures specified by QA. These observations do not reopen local E1.


### First live Haiku attempt

Checkpoint `42b7af81` commits the verified harness and future-extension records.
The user supplied the requested private credential file. Sprint executed the
bounded two-task run against `claude-haiku-4-5-20251001`, one attempt each,
120-second process limit, no retries. Both processes completed in about 1.2s;
both Anthropic requests returned HTTP 400 before any model response: the key
is not workspace-scoped and requires a workspace-ID header or a workspace-scoped
replacement. The current client does not supply that header. No Haiku quality
score can be inferred.

Raw outcomes remain `not_completed/unknown` as emitted by the conservative
runner; the observed provider rejection establishes provider-configuration
attribution for this attempt. Raw report and separate assessment are retained
under `.local/s122-agent-evals/haiku-baseline-20260919/`. No retries or provider
changes were attempted. The next execution dependency is a workspace-scoped
credential in the same private file, or an explicitly selected header-support
change. Future comparison/configuration extensions remain deferred in ACT-0960.


### Haiku baseline after provider-request correction

The replacement workspace-scoped key was accepted. Both next requests were
rejected before inference because our request cap was 65,536 versus Haiku's
64,000 limit. Those attempts remain in
`.local/s122-agent-evals/haiku-baseline-20260919-workspace-key/`.
Dev narrowed the private cap to 64,000 and added a request-bound unit
(session `25d475ae-78ae-4e84-9899-094b24381154`, Claude Opus/high).
The isolated binary rebuilt successfully. The new unit could not execute:
agent-feature module tests have 23 compilation errors involving obsolete or
private types across four agent files, before and after this change. This is
current sprint evidence debt, not a passed unit test or an accepted carry.
Dev report: `.local/s122-haiku-token-limit-dev-result.md`.

The next bounded live invocation completed both tasks with executable passes:
generic replacement 4.327 seconds, one submit, zero repairs; ordered IO 15.282
seconds, one submit, one repair. Raw report and artifacts:
`.local/s122-agent-evals/haiku-baseline-20260919-token-fix/`.
The two earlier invocations contribute four preserved pre-inference rejections;
they are not model-quality failures. This is one completed attempt per task,
not a reliability estimate. Token usage and cost remain unavailable.
QA source-based API compliance and final evidence assessment completed in
session `45b73a9a-980d-4fc5-8c54-b7c27127f9f8` (Claude Fable/high).
No further live repetitions are scheduled. The provider correction is included
in the user-authorized agent verification checkpoint.


QA accepts the bounded Haiku smoke baseline: 2/2 complete task successes.
The retained IO body applies the imported sequence-io function to exactly the
three requested Pure values, so source-based API compliance passes. Its first
candidate was rejected and logged a give-up event before the model continued
to a successful submit; that event is not a final refusal. Raw reports remain
unchanged; the separate reviewed disposition is
`.local/s122-agent-evals/haiku-baseline-20260919-token-fix/assessment.json`.
QA report: `.local/s122-haiku-live-qa-result.md`. All reservations are released.

The fixture compilation and request-cap unit obligations are completed in the
agent integration verification below. The live baseline does not confer
whole-sprint acceptance. No further model calls or deferred extensions are
needed to report it.


### Agent integration verification

- Agent fixture migration and request-cap proof are complete: the cap unit
  fails at 65,536 and passes at 64,000; the mention-arm negative assertion
  detected a planted extra mention.
- Prelude context, explicit-import context and constructor docstring-refusal
  corrections are complete. The two latest defects each failed at their
  intended assertions in both module and end-to-end tests before correction.
  All controls remained green. The table guard is released before resolving
  implicit-prelude candidates.
- Final affected module/import tier: **175/175 passed**. Full agent end-to-end
  lane: **81/81 passed**. Logs:
  `.local/s122-agent-lookup-modules-green.log` and
  `.local/s122-agent-lookup-e2e-green.log`.
- Final default suite: **5,968 passed, 1 failed, 1 skipped**, 111.3 seconds.
  Sole failure: unsuppressed document conformance (2,519 findings). All finding
  identities match the preceding baseline. Log:
  `.local/s122-default-lookup-final.log`. The scoped golden repairs pass.
- Independent review found no blocking issue; its required defect annotation
  and mechanical wording repairs are applied. QA accepts the bounded agent
  corrections. Design reconciled the changed harvesting description.
  [QA's canonical allocation and adequacy](../tests/plan/s122-evidence-delta.md#final-integration-failures--classification-and-allocation)
  owns residual classification: the pre-existing slash-command guard lifetime
  goes to the next correction basket; pin/export decisions remain open.
- Changed Rust files pass formatting and diff checks. Repository-wide formatting
  still reports untouched `src/repl/format_type.rs`, `src/repl/mod.rs` and
  `tests/spec_04_expressions.rs`.
- All role reservations are released. NOTES.md is unchanged and untracked;
  the unpublished shared-package checkout is excluded from the checkpoint.
  The user authorized committing this verified checkpoint. No push, phase
  transition or further live call is authorized.
