# Sprint 122: Known-issue closure and REPL-agent evaluation

**Status:** PHASE 5. The compiler corrections, bounded Haiku eval and IO reuse
corrections have executing evidence; checkpoint `57253cf2` is committed.
Document consolidation continues: the last integrated check has 1,000 findings
across 593 documents. Historical audit reports are retired to Git with open
points preserved in actions and existing filings. Current reservations appear
at the end of this plan. No phase transition or publication is authorized.

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
  and user-document references searched. The matching `test.cl` names describe their actual stdlib counterparts,
  not the root probe copies. Recommend retaining `NOTES.md` untouched as the user's personal
  idea list, and removing the five probe/diff artifacts during delivery once
  their owning source streams confirm any useful evidence is preserved. The
  scratch patch covers intrinsics drop/lib/panic/rc/strand, so that stream
  verifies its source-backed remainder before deletion. No root file is deleted
  by the design phase.
- **ACT-0957 ownership choice:** approved 2026-09-10. Sprint owns host-entry
  guidance (`AGENTS.md`, `.codex/`, Copilot instructions) alongside existing
  adapter/hook ownership. The [information map](METHOD.md#31-where-things-live)
  records the assignment; referenced
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

[Intrinsics closure](../design/intrinsics/ownership-and-disposal.md) retains
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
  GOT name. QA allocated a minimal fixture named `hx` under `platforms/` to a separate dev
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
  [typecheck master](../design/typecheck/CLAUDE.md#redirections).
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
  Removed the `test.cl` probes under the former root-level directories
  named `default`, `foo` and `testing/runner`, the project TOML under `test1`,
  and `scratch_other.diff`. The distinct live stdlib
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

Completed owner comparisons retired superseded architecture, context, QA and
sprint records. Useful current content lives in its canonical designs, PLAN and
METHOD; closed delivery evidence lives in the relevant sprint archive or Git.
Deletion did not close compiler findings or accept document-checker debt.

### D7 document map — agreed, 2026-09-11

The user approved the information map and substantial standing-document
reduction. [METHOD §3.1](METHOD.md#31-where-things-live) owns that map and the
retention rule. Compare content with its canonical home; extract useful missing
substance and preserve open obligations before retiring originals.

### D7 continuing standing-document reduction

The representative passes and subsequent batches are complete. Current
assurance is in [PLAN](../tests/plan/PLAN.md); current context guidance is in
its governing memory. Completed dispatch tables, intermediate finding counts,
and per-batch transcripts are recoverable from Git checkpoint `57253cf2`.

### D7 exact-anchor matcher correction

The shared checker correction and its detection evidence were delivered.
The project consumes the published package pin; the local package checkout
must not be staged as an incidental part of document cleanup. No finding
baseline or new reference exemption was introduced.

### D7 legacy records and section-citation triage

Completed owner passes replaced stale live citations with canonical targets or
historical provenance, retaining source/test section anchors where still used.
The project check continues to expose unresolved references; its failures do
not become accepted debt through record retirement.

### Local checkpoint and continuing cleanup

The user repeatedly authorized checkpoints followed by continued cleanup.
Completed checkpoints and old provider-capacity interruptions are Git history;
current integration status and reservations are recorded below. NOTES remains
local and must not be committed or deleted.

### Harvest-record consolidation after checkpoint

The S64 harvest cohort and older QA registers were reconciled and retired.
Their current evidence obligations remain in PLAN; obsolete inventories and
unexecuted work orders do not remain as parallel standing authority.

### Early QA-plan consolidation

The eleven early plans were retired after QA retained the REPL auto-IO evidence
lead, unfinished timing-witness sweep and module-preamble coverage lead in
PLAN. Test/source citation integration completed without changing assertions.
Concurrency-comment debt, literal-token ordering and bare-alias list coverage
remain owner observations, not silently accepted defects or new test scope.
The allocated REPL-agent eval then proceeded as recorded below.

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

### Post-checkpoint Phase-5 continuation

The user approved proceeding after checkpoint `cdd1f9ea`. Dev owns the
remaining `/imports` guard-lifetime correction, with QA's existing A2/A5
allocation: Claude Opus/high session
`df7d38d4-c842-42c6-a4a0-3c53bf674ef8`. Design independently owns retention
assessment and consolidation of seven integration decomposition/migration
records, Claude Opus/high session `f2ad4ec3-aaf5-4ac3-95db-a3ce87798ccd`.
The retention rule in METHOD remains binding: extract useful missing content
into canonical homes, preserve unresolved obligations, and retire originals
when Git suffices. Cross-owner reference integration follows their exact
dispositions. Root owns the serial verification reservation after source
release. No phase transition, publication or additional eval is included.

The integration cohort retires seven delivered migration/decomposition records;
missing current guarantees are extracted into the integration master. QA also
retires the related S78 evidence plan while preserving its exit-result lead.
Root observed the exact fixture return 42 with empty stdout/stderr; test owns
the permanent assertion, Claude Opus/high session
`00bdfc47-5d11-498b-8d72-8608dfc34db3`. The `/imports` correction is QA-accepted:
176 module/import, 81 agent end-to-end and 12 public `/imports` cases pass.
The final related `/exports` guard is queued after test releases source.
Removing the display-identity helper requires a separate cohesive pass over
its retained architecture/design contracts and callers; it remains pending. Spec confirmed the existing S78 user ruling
for bare `/mod` and repaired its stale prose; both existing `/mod` cases pass.

### Integration cohort completion

- Eight obsolete documents are retired: seven delivered integration migration/
  decomposition records and the related S78 evidence plan. Missing current
  guarantees are extracted into `design/int/int.md`; unresolved display-lookup
  reach remains explicit there. Current source, test and architecture citations
  are integrated; the declaration no longer names the seven deleted designs.
  Dated sprint history and immutable reconciliation evidence remain historical.
- `/imports` and `/exports` release table guards before resolving candidates.
  QA accepts both corrections; exports preserves its spelling-based filter.
  The redundant display-identity helper remains for a cohesive source/contract
  pass, not an automatic future-sprint carry.
- The recovered S78 exit-result obligation now has its permanent exit-42
  assertion and passes. Bare `/mod` prose is corrected to the recorded S78
  user ruling, with the two existing passing cases traced by QA.
- Verification: 176/176 selected module/import cases; 81/81 isolated agent
  cases; 12/12 public imports cases; both `/mod` cases; restored exit witness.
  Final default suite: **5,969 passed, 1 failed, 1 skipped** in 113.2 seconds,
  including all five allocated exports cases. Sole failure is document
  conformance. Log: `.local/s122-cohort-default-final.log`.
- Feature-enabled Clippy lib/bin check exits 0 with warnings outside the
  changed executable lines. Formatting differences are the same pre-existing
  locations. Diff and role-wiring checks pass. NOTES remains unchanged.
- Final ownership: spec Opus/high `d6c7e8d3-6e68-4b8c-a251-becb261e26fd`
  reconciled the existing ruling; dev Opus/high
  `8b2d3011-701a-4091-abd9-10174b534cef` completed exports; QA Fable/high
  `4c7575c1-4df6-4aa8-9844-85052c9cc259` accepted the final bounded outcomes.
  All reservations are released. No commit, push or phase transition is
  included in this continuation.

Stable-tree document result: **715 documents, 2,444 findings**; exactly 75
identities removed and none added against the checkpoint snapshot. No baseline,
exception or historical-reference policy changed. Report:
`.local/s122-cohort-stable-final.json`. This observation precedes only this
ledger status update, which receives a scoped check. All eight retirements and
remaining obligations are accounted for in the canonical master and QA homes.

### Continuous cleanup batches

The user authorized continuing batches until a decision needs review. Batch 2
reserves lookup/display architecture contracts to arch Fable/high
`e93e6873-fa0f-4b53-aefb-feb9ebc9abbb`, the related integration design to
design Opus/high `3e3d6ec4-0e0d-4518-8ac0-13144e7ad051`, and eight older
QA-plan candidates to QA Fable/high `71f799af-b0b9-4fab-a4cd-4f7b12689d09`.
Establishment now follows the nearest owner memory for current language/REPL
specifications and user documentation, excluding historical candidates. Spec
Opus/high `fabfb0fa-aefb-45bc-8eb4-cfa1d32fea39` and docs Opus/high
`bd565e94-c652-4811-9826-336bdedf1d8e` repaired those entry points.

Arch retains three shortened current contracts; design retires the obsolete
bare-primitive chain-walk record, preserving display provenance in the
integration master. Dev Opus/high `852a82ab-9f44-43f5-9102-90adc163ae2f`
holds the sole source reservation for the behavior-preserving identity-helper
removal. Root owns tests after release.

Spec Opus/high `c18c49cf-0941-4ea2-b9b4-0215eb7e60aa` confirms one user
question remains: multi-candidate introspection. Root's isolated observation
shows local Bool `foo` alone in bare lookup and `/sig`, although `(foo 1)`
selects the prelude Int candidate. Listing all candidates versus reporting
ambiguity is presented to the user; no display rule changes before approval.
The separate qualified re-export observation shows a closure at bare lookup
and the defining primitive at `/sig`; existing authority settles agreement,
so it goes to QA for permanent reproduction, not a new semantics ruling.
Observation logs: `.local/s122-b2-collision-observation.json` and
`.local/s122-b2-display-observation.json`. Scratch directories were removed.

Batch-2 retention: QA deletes the completed S69/S75/S92/S94 working plans and
retains four cited S99–S101 evidence records with repaired references and explicit
standing-versus-dated scope. Their class is established in test guidance. The
S92 annotation-band lead remains in PLAN; retirement does not close it. Root
integrates owner-specified citation repairs. Remaining cross-owner currentness
items are enumerated in `.local/s122-b2-arch-result.md` and
`.local/s122-b2-docs-establishment-result.md`, including the stale integration
candidate/conflict prose and architecture interface inventories. They remain
queued for their owning batches, not accepted exceptions. QA Fable/high
`6d72a1ad-c8f2-4ee1-b81a-01e0d14a64e2` allocates helper-removal evidence and
records the qualified-display observation separately from the user decision.

Batch-2 verification is complete: 267/267 focused cases; default suite
5,969 passed, one document-conformance failure, one skipped (119.283 seconds).
Clippy all-targets exits 0 with existing warnings; formatting reports the same
known locations, shifted only by deleted lines. Wiring and diff checks pass.
The stable document report `.local/s122-b2-stable.json` has **710 documents,
2,284 findings: 160 removed, none introduced** versus the preceding cohort.
QA Fable/high `239636ff-ba86-4eb3-bab8-b2ab1ec7d407` accepts the helper
removal as adequate; all reservations are released. The qualified-display lead
remains pending a permanent reproduction within S122. No commit or phase transition occurred; NOTES and the published
shared-package gitlink remain unchanged.

The user challenged whether hiding is already defined and distinguished
`/search` discovery from imported scope. Root clarified the observed example:
local and implicit-prelude declarations are both already in module scope under
`spec/08-modules.md` §8.6.1; only lexical bindings shadow that whole set. The
proposal concerns only in-scope candidates. This exchange is a clarification,
not approval of any display change.

### In-scope introspection — current ruling

- The user supersedes the earlier display-only ambiguity policy: list all
  in-scope canonical candidates, including candidates with the same type,
  without ambiguity warnings. Ambiguous applications retain the existing
  language use-site error. No display-specific type-equality test is needed.
- The user considers conflicting imports a language-specification mistake but
  explicitly defers that correction. Current import registration and language
  resolution remain unchanged; a future spec action preserves the issue.
- Spec Opus/high `800937cb-dde0-48b4-b508-35d0ad857b79` updates the canonical
  REPL rule and records the deferred import question in ACT-0961. Both are
  complete. QA Fable/high `0979462b-7a3b-448a-b9b6-c503da467175` replaced the
  obsolete same-type-error allocation in the existing evidence delta; its
  `/sig`, `/info` and `/doc` conditions match the final spec. All reservations
  are released. Scoped reference checks introduce no findings; diff checks
  pass. The architecture note now identifies an implementation gap against
  the settled rule instead of an open semantics question. No implementation,
  test execution, commit or phase transition is part of this correction.
- The prior integration assessment found existing candidate-query interfaces
  adequate. Its display-verdict/type-comparison proposal is superseded; any
  subsequent implementation design must use the current listing rule.
- The separately settled qualified-re-export display lead remains pending
  permanent reproduction within S122. It is not deferred with import policy.

### Candidate-display implementation

User authorized continuation. Integration design and architecture alignment are
complete: display consumes the existing language candidate set, renders each
canonical declaration and remains non-defining. No public-API change is needed.
The source-before snapshot is `.local/s122-display-source-before.json` for a
focused review against the prior uncommitted cleanup.

The discriminating before-state is established: ten cases, eight display
failures and two passing controls (ambiguous application and terminal
deduplication). The canonical qualified-name control passes; its re-exported
spelling fails. Both `/doc` cases now run independently and show the allocated
omission/unknown-name defects. Existing language/import controls pass 142/142.
Evidence: `.local/s122-display-red-followup.log` and
`.local/s122-display-controls-before.log`. QA attributes the display failures
to the binary introspection seam; the test reservation is released.

Dev Opus/high `5c85dab5-ea0f-4d83-b5b5-a48c9194023a` released the Binary/int
implementation. Focused evidence passes 1,111/1,111; the default suite has
5,983 passing tests, one known document-conformance failure and one skipped
(117.444 seconds). Logs: `.local/s122-display-green.log` and
`.local/s122-display-default.log`. Root corrected only newly introduced
formatting and is running the isolated agent lane.

The isolated agent lane passes 81/81. Clippy exits 0 with no diagnostic on
this correction's lines. Independent review identified inaccurate residual
wording, the retained unused helper, and the mixed-candidate case. QA confirms
private-qualified command refusal conforms and allocates one additional
constructor/function listing cell. That reproduction fails for the predicted
ambiguity while the singleton constructor control passes
(`.local/s122-display-edge-red.log`).

The final correction is complete. Design records the constructor listing rule
and the truthful remaining legacy readers; the unused description helper,
collector chain and record are deleted, with only their obsolete facade-test
item retired. The constructor regression and its singleton control pass.

Final verification: **1,131/1,131 focused; 5,983 passing default tests, one known
document-conformance failure, one skipped (117.799 seconds); 81/81 isolated
agent tests**. Clippy exits 0 with no diagnostic on this correction's lines;
formatting reports only the known out-of-change locations. Wiring, diff and
public-API-baseline checks pass. Logs are the
`.local/s122-display-final-{green,default,agent,clippy,fmt,wiring}.log` files.

Fresh review Fable/high `725dbecd-e765-49f1-9f6a-f2df55e6ec47` closes R1–R3
and A1–A4 with no required finding. QA Fable/high
`e176f353-2f9f-44b4-a028-b5d04b8b1cae` accepts the evidence with no pending
condition and sets the REPL §4.1.11 traceability bands. All role reservations
are released. Root applied the owner-specified mechanical annotation, citation
and completed-implementation status repairs. The final typecheck design aside
and the obsolete integration toolbox member are also repaired.

The legacy helper's three membership readers and two display readers remain
scoped residual work in the integration design; this correction does not claim
they have converged. Nine defect tags await the eventual fixing commit SHA;
the post-commit notation pass also owns the noted past-tense comment cleanup.
One older unit-test history comment remains advisory. NOTES and the published
shared-package index pin are unchanged. No commit or phase transition occurred.

Import-policy work remains deferred in ACT-0961; no phase transition or commit
is authorized by this continuation.

Stable document measurement after this correction:
`.local/s122-display-final-documents.json` reports **711 documents and 2,280
findings — four identities removed, none introduced** versus the prior
710-document, 2,284-finding checkpoint. The additional document is the deferred
import-policy action. No suppression or discovery policy changed.

### Document retirement resumed; coverage work reserved for next increment

On 2026-09-20 the user approved recording coverage assurance and se-agentic
convergence for the next increment, then instructed continued documentation
cleanup. [ACT-0962](actions/ACT-0962-coverage-assurance-and-shared-standard.md)
owns that future work; S122 remains in Phase 5. No commit or phase transition
is included.

Current reservations: design owns the eight historical typecheck working
documents and their owned canonical destinations; audit owns the three older
backend, intrinsics and primitives audit reports selected for disposition.
Each batch verifies current homes and preserves unresolved obligations before
retirement. Root integrates mechanical cross-owner links and checker evidence.

| Role | Provider / model / effort | Session | Outcome |
|---|---|---|---|
| design, typecheck historical documents | Claude / Opus / high | `5422c515-637e-401f-b00c-0d516289468a` | complete; seven retired, one retained for live test contract |
| audit, three historical reports | Claude / Fable / high | `3ec11cc1-23ba-49a5-954f-641083c96562` | complete; three reports retired, successor obligations retained |

Audit retirement preserves the unresolved findings in the successor assessments:
[backend S110](https://github.com/alilee/cranelisp/blob/57253cf2/audits/cranelisp-backend-s110.md),
[intrinsics S115](https://github.com/alilee/cranelisp/blob/57253cf2/audits/cranelisp-intrinsics-s115.md) and
[primitives S116](https://github.com/alilee/cranelisp/blob/57253cf2/audits/cranelisp-primitives-s116.md). Follow-up disposition
work remains: S115 accepted recommendations name absent filings; S110 and S116
have incomplete disposition records. QA must also reconcile the named Vec
null-slot test (not found in the current test/source tree) and the historical
ferry-regression claim. No implementation defect or closure is inferred from
these record gaps. The bounded retirement evidence is
`.local/s122-audit-retirement-result.md`; Git retains the original reports and
the backend diagram companions.

Typecheck disposition removed seven historical plans (3,497 lines); the three
audit retirements removed 868 lines and their four backend diagram companions.
The guard-lifetime rule extracted from the old migration plan now lives in
[typecheck design](../design/typecheck/typecheck.md).
The rendering working record remains because three current types tests cite its
contract: arch must relocate that contract and its citations together before
retirement. Design records canonical destinations in the typecheck guidance;
`.local/s122-typecheck-document-retirement-result.md` carries the source checks.
Root applied the owner-provided mechanical inbound-reference repairs and removed
only the deleted files from the declared inventory. No checking exemption or
suppression was added.

Integrated verification: `.local/s122-doc-retirement-complete.json` reports
702 documents and **2,147 findings**, down from 712 documents / 2,280 findings
after ACT-0962 was added: **133 identities removed, none introduced**. The
checker remains nonzero for the existing backlog. `git diff --check` passes;
NOTES retains its prior SHA-256 and the shared-package index pin is unchanged.
The role's staged deletions were unstaged without restoring the files; all
changes remain uncommitted. No behavioral tests were rerun for these prose and
comment-only changes. Both reservations are released.

### Whole-context document consolidation

The user approved larger, cohesive batches on 2026-09-20. Backend and platform
design owners assess each complete document surface, with audit consolidating
the corresponding report succession. The target is fewer dependable standing
documents, with unique current content extracted before retirement and live
obligations preserved. No behavior changes, commit or phase advance. Coverage
assurance remains next-increment work in ACT-0962.

| Reservation | Provider / model / effort | Session | Status |
|---|---|---|---|
| Backend design documents and companions | Claude / Opus / high | `2765afdb-777d-4163-8dae-a6e2c4bd7a41` | complete; 35 documents reduced to 24 |
| Platform design documents and companions | Claude / Opus / high | `4a83f427-d52c-43e0-a29d-d0addb82d94a` | complete; 10 documents reduced to 5 |
| Backend/platform audit succession and companions | Claude / Fable / high | `a45dcb1d-95a0-4342-bb3d-d2d69329741e` | complete; six reports consolidated to two |

Root integrates inventory and mechanical incoming-reference repairs, then runs
one whole-repository checker followed only by any required correction checks.
Before-state: `.local/s122-wide-docs-before.json`; checker baseline:
`.local/s122-doc-retirement-complete.json` (702 documents / 2,147 findings).

Audit succession: four reports and four diagram companions retired; backend S110
and platform S117 retain the unresolved findings and provenance. The owner
verified current sources and added dated succession notes; no recommendation
was silently accepted or declined. `.local/s122-wide-audits-result.md` owns the
batch detail. Backend S110 R3 prompted the bounded assessment below; its two lookup leads
are not reproduced defects. The complete historical recommendation is not
disposed by document retirement. Platform filings 0870 and 0874 appear delivered
but require their owners' completion checks; audit did not close them.

Whole-context outcomes (relative to the before-state, excluding earlier batches):

| Surface | Markdown documents | Markdown lines |
|---|---|---|
| Backend design | 35 → 24 | 24,034 → 17,998 |
| Platform design | 10 → 5 | 4,808 → 1,283 |
| Audit corpus after the backend/platform succession fold | 30 → 26 | 9,912 → 8,541 |

Net: 20 Markdown documents and 10,932 lines removed, plus four audit diagram
companions. Current homes retain the extracted layout, handle-opacity, cache
symbol, panic-boundary and closure-lifetime contracts. Root applied the precise
owner-provided citation moves in neighboring prose, source comments and test
annotations; no behavior changed. The declaration follows the surviving
collections without new exclusions or suppressions.

The backend owner initially retained a drop-glue/GOT-routing claim in
[jit-object-convergence](../design/backend/jit-object-convergence.md) and
release-mode keying observations in the master design. The bounded assessment
below supersedes their classification: the glue claim contradicted current
authority, and the lookup leads do not establish reachable defects. Platform
filings 0870/0871/0873/0874 have owner-verified completion leads but still require
their filing owners' disposition. The remaining backend ownership staging
material requires deeper source verification before further retirement.

Batch records: `.local/s122-wide-backend-result.md`,
`.local/s122-wide-platform-result.md`, `.local/s122-wide-audits-result.md`. All
reservations are released.

Final integrated document check: `.local/s122-wide-final.json` reports
**682 documents / 1,878 findings**, versus 702 / 2,147 before this batch:
**269 finding identities removed, none introduced**. The checker remains red
for the existing backlog. Integration repaired the newly exposed section links
and restored the submodule declaration accidentally removed with an obsolete
collection; no checking policy changed. `git diff --check` passes. NOTES and
the published shared-package index pin are unchanged. All changes remain
uncommitted and unstaged; Phase 5 remains active.

### Backend obligations — bounded assessment

The user's continuation authorizes assessment of the two backend leads exposed
by consolidation. QA investigates current source, reachability and evidence;
arch independently checks governing contracts and executable-owner lifetime.
Neither raw function-address syntax nor a silent fallback alone establishes a
reproduced behavior defect. The outcome determines whether the next work is
document correction, a minimal reproduction, or a decision requiring review.

| Role | Provider / model / effort | Session | Status |
|---|---|---|---|
| QA, backend obligation classification | Claude / Fable / high | `9fc45d47-b6e7-498b-a145-1e536e705990` | complete; no independent reproduction allocated |
| Arch, contract and lifetime authority | Claude / Fable / high | `e1dc1c0f-8f0c-4569-8ff4-77f9ab94dd46` | complete; glue claim withdrawn, existing contracts govern |

No implementation, public-API change, commit or phase transition is implied.

QA and arch independently classify the glue-through-GOT obligation as an
unsupported, superseded claim: compilation-local glue and executable owner
retention govern its lifetime. Cross-load numerical address equality is not a
parity condition. The lookup misses are producer-invalid-state cases, with a
prior hard check on the pattern path and a debug detector for constructor
enumeration; no independent reproduction is allocated. No test was executed in
this assessment. Sprint selects the least-cost document correction, with no new
implementation work or filing for these leads. This is not a blanket proof of
all executable-lifetime paths; cache-hit displacement and future cross-turn
value carriers remain the stated limits of the source assessment.

The recent consolidation had dropped the old convergence text's owner-rooted
alternative and promoted a stale hypothesis to a current obligation. Backend
design repairs the two affected documents against current arch authority. Root
applies arch's explicit BC invariant wording correction. Integration design
repairs the stale AbiPreserving reclaim and retention-growth claims against
current publication paths.

| Repair | Provider / model / effort | Session | Status |
|---|---|---|---|
| Backend obligation documents | Claude / Opus / high | `132b2c0e-baeb-422e-a420-9859265ca439` | complete; valid parity contract retained, unsupported claims removed |
| Integration retention account | Claude / Opus / high | `6108f94b-8cf4-4d95-9f16-8e908483aaf8` | complete; pooling scope and growth bound corrected |

The document corrections are complete. Source and test edits in this correction
are limited to a historical citation comment; no executable behavior changed.
Root narrowed the backend risk sentence to QA's actual finding (legitimate
inputs do not construct the missing-entry state, rather than claiming arbitrary
corrupted metadata harmless), scoped the retention sentence to staged/compiled
publication, and repaired the test's old convergence-section citation.

The integration account now distinguishes retaining publication from cache-hit
replacement and pool-less contexts, and measures growth by pooled displacements.
Older pre-cure watcher/reload narration and the stale retention rustdoc census
remain next-touch document work, not evidence of a new runtime defect. The
current lifecycle contract and the assessment's named falsifier remain the
authority for any future reachable-lifetime investigation.

Evidence: `.local/s122-backend-obligations-{arch,qa}-result.md`,
`.local/s122-backend-obligation-doc-repair-result.md` and
`.local/s122-retention-record-repair-result.md`. All reservations released.

Final correction check: `.local/s122-obligation-repair-final-documents.json`
reports **1,878 findings, unchanged identities and no new findings**. The
correction changes the substance of misleading claims rather than the finding
count. `git diff --check` passes. No tests were run or new runtime claims made;
NOTES and the published shared-package index pin remain unchanged. Uncommitted,
unstaged, Phase 5.

### Checkpoint and continued document consolidation

The user authorized a checkpoint commit and continued cleanup until a decision
needs review. The checkpoint includes the accepted REPL candidate-display
correction, accumulated documentation consolidation and ACT-0961/ACT-0962.
NOTES and the unpublished shared-package HEAD are excluded; the index keeps the
published package pin. Diff checks and role wiring pass. Behavioral evidence
remains the previously recorded 5,983 default passes (known document gate red),
1,131 focused passes and 81 isolated agent passes; subsequent edits are prose
and citation corrections. Latest document check: 1,878 findings, no new
identities from the obligation correction. Phase 5 remains active.

Checkpoint committed as `48d6e713`. The nine accepted REPL defect records now
name that fixing commit; this post-checkpoint update changes comments only.

The next whole-surface batch reserves frontend design, intrinsics design and
retained S102–S121 QA plans independently. Root owns incoming citation repairs,
collection declarations and one integrated document check. Coverage assurance
extensions remain deferred in ACT-0962. No implementation or phase transition.

| Reservation | Provider / model / effort | Session | Status |
|---|---|---|---|
| `design/frontend/**` | Claude / Opus / high | `49da08df-ec23-4f74-9414-1c4df39b8a34` | complete; 15 products to 12, current interiors |
| `design/intrinsics/**` | Claude / Opus / high | `4118c29c-7a1d-4415-b25c-4d306972015e` | complete; ownership/disposal consolidated |
| S102–S121 `tests/plan/` records and PLAN.md | Claude / Fable / high | `0c11c7e8-0b52-43d2-8754-42f6def2295e` | complete; six retired plans, cited sections retained |

Batch baseline: `.local/s122-next-docs-before.json`; checker baseline:
`.local/s122-obligation-repair-final-documents.json` (682 documents,
1,878 findings). Role results are `.local/s122-next-{frontend,intrinsics,qa}-result.md`.

QA removed six completed records and trimmed seven plans to still-cited
sections. Root applied its incoming citation and collection-registration map.
Retained S117 module-matrix allocations remain dated, unverified evidence; no
new evidence claim or obligation is inferred. ACT-0950 was subsequently retired after shared-checker delivery; the S122
QA evidence delta carries the D7 disposition. Its older request is not new scope.

The released slot continues with the Binary/int standing surface, including
older compiler-concurrency and session narratives. Reservation: `design/int/**`;
Claude / Opus / high, session `98c00e36-3f1f-450a-909d-490322097ae4`, running.
Result: `.local/s122-next-int-result.md`. Other owners' citation edits wait for
that reservation to release.

Intrinsics consolidation produced the current ownership/disposal home and
retired three predecessor plans. Root applied the owner's relocation map
except Binary/int citations, which await its active reservation. Integration
corrected a stale open-runtime-acceptance sentence against QA's later explicit
closure and the user's 2026-09-11 baseline confirmation; no evidence rerun.

QA is classifying the separate A6 diagnostic detection-proof lead read-only:
Claude / Fable / high, session `a6020cb1-5b30-4232-a227-0204cd6bc4c2`, running;
result `.local/s122-a6-qa-result.md`. No new control or defect is inferred from
the design search alone.

Frontend consolidation and its source-comment relocation map are complete.
QA classifies A6 as an already allocated, undischarged intrinsics module proof,
not a compiler defect or a new control. Its bounded assessment is complete;
root applied the exact truthful evidence wording. One dev-owned debug-twin
unit and fail-on-revert observation discharge it without changing production
behavior or reopening runtime acceptance.

A6 dev reservation: `crates/cranelisp-intrinsics/src/drop/tests.rs`, plus a
temporary scoped `drop.rs` mutation restored after the detection observation;
Claude / Opus / high, session `d3774cee-0c66-4940-a659-389536da625c`, running.
Only the allocated two module units run; no production change is authorized.
Result: `.local/s122-a6-dev-result.md`.

QA read-only assessment of the retained trait-head echo question: Claude /
Fable / high, session `8047113b-c191-4bfd-90df-ded95012c66d`, running; result
`.local/s122-trait-echo-qa-result.md`. It compares the current spec, source and
existing evidence before treating the old frontend question as unresolved.
No concurrent tests or implementation are allocated.

A6 dev completed the allocated proof: planted and clean units pass 2/2;
removing the debug assertion fails only the planted unit with the intended
"did not panic" message; restoration passes 2/2. Production `drop.rs` is
byte-identical to HEAD (SHA256 `5e0562cf5d512747476f7d295657017a4fecc086cf4549b5b0e2256427469969`).
Only one unit was added; no production change or expanded evidence matrix.
Root updated the design evidence with its explicit debug-twin/scalar limits.

The trait-head QA assessment is complete: the supposed open question was
already settled and implemented in S112, with existing module and e2e guards.
Root corrected the retained false claim and the shape-only wording against
QA's exact source-backed disposition. No user question or new test is needed.

Final A6 QA verdict: adequate within the allocated debug-profile/module-seam
limits; no further test or review needed. Claude / Fable / high, session
`5bce35d7-23ae-477a-b486-8049d7562f01`, complete;
`.local/s122-a6-adequacy-result.md`. This closes the allocated proof.

Continued architecture document reservation: `design/arch/**` excluding
`fixmes/**`; source, specs and public baselines remain read-only. Claude / Fable /
high, session `ac6fb85c-ff9b-43eb-89c6-20bc7b743dc0`, running;
Result pending. No boundary/API/semantic change authorized.

Binary/int consolidation complete: 46→39 Markdown files and 26,614→21,047
lines, with six obsolete diagrams retired. Root applied the relocation map
and merged the misleading historical collection into its current/retained
carriers. This is ordinary declared-collection maintenance under the user's
approved retention policy, not a new permission gate or checker exception.
The architecture decision's old persistent-worker section citation waits for
the active architecture reservation. Remaining stale bodies require repair,
not an inferred banner-scoped exemption.

The completed four-surface batch reduces its Markdown burden by roughly
14,800 lines and 19 documents. Integrated check after mechanical repairs:
`.local/s122-next-repaired-documents.json` reported 1,597 findings; three new
identities were a pending local result link (removed until it exists) and an
ambiguous typecheck citation (qualified). Architecture edits were beginning
during that check; the next stable gate will supply the final count.

Specification navigation reservation: `spec/**`, `repl/spec/**`, `repl/spec.md`;
Claude / Opus / high, session `9b8ea257-e980-4137-9c15-5eb0b3ac64ad`, running.
Meaning, user rulings and coverage bands are unchanged by authorization.

QA is classifying the remaining R1 observer/public-evidence lead read-only,
without reopening Q3 or A6: Claude / Fable / high, session
`03a19781-a3cf-4352-9510-793be883f350`, running. Filename absence alone is not
credited as a gap; existing equivalent evidence and current authority govern.

R1 QA classification complete (read-only). The loser-force path and its
diagnostic observer lack their previously allocated observations; this is not
a reproduced product defect. QA separates module refusal evidence, observer
proof and language-level acceptance. The last depends on whether repeated
forcing of one IO value is specified to succeed, refuse, or remain unspecified.
Root is preparing a bounded public probe and spec-authority framing before
asking the user; Q3/runtime and A6 remain accepted.

Public R1 probe: `test`, Claude / Opus / high, session
`b3fd7c01-c685-451c-b24b-60d53aa304d1`, running; existing binary only, disposable
inputs, no permanent expected-behavior test before specification authority is
settled. Root narrowed the ownership/disposal evidence credit using QA's exact
disposition. The architecture register wording awaits its reserved owner.

Architecture consolidation complete: 54 tracked files retired; decision labels
resolve through their canonical homes. Root applied collection and incoming-link
repairs. The lifecycle/transaction facade approval basis is the archived S121
confirmation; no new public surface was approved by document status correction.
Spec navigation repair complete: one spent readiness record retired and stale
section/path references repaired without normative or coverage-band changes.

The test role could only observe typechecking under its Bash permission policy.
After its reservation released, root executed the exact prepared sources through
explicitly escalated/approved bounded invocations. Sequential reuse of one Pure
refuses with the named runtime error; the fresh-Pure sequential control returns
7. Both race probes return 7 in these single observations; the invalid-type
control rejects. No rebuild or production change. Recorded in
`.local/s122-r1-root-observation-result.md`; this is not an acceptance ruling.

Read-only specification-authority framing is running: Claude / Opus / high,
session `33e098a1-9d61-4508-a96c-1f3c6742c258`. The conformance sentence still
using the retired ring axis is a separate spec-reported question, held behind
the IO-reuse question for one-at-a-time review.

### Approved IO reuse — current correction status

- **Authority (user, 2026-09-21):** IO descriptions are reusable, recorded in
  `spec/10-io.md` §10.8.1. Once-only refusal is a defect, not language behavior.
- **Approved Effect API:** three `CLIO::effect*` constructors require
  `Fn() -> CL + Send + Sync + 'static`; `call_effect_thunk` borrows;
  add `pub unsafe fn drop_effect_thunk(i64)`; `ABI_VERSION` 10 → 11.
  [Architecture contract](../design/arch/total-concreteness.md#34-the-io-existential-bind-a-representation-question-and-it-dissolves)
  owns the exact delta. The generated platform baseline matches: three changed
  constructor lines and one added cleanup function. **User confirmed the exact
  generated diff on 2026-09-21.** No other public delta changed.
- **Implemented:** Pure retain-on-force and node-owned Effect thunk teardown;
  private backend IO-combinator freshness classification removes the observed
  unbalanced scope-result retain. Producer, consumer and backend reviews found
  no blocking implementation issue. QA accepted the existing mixed-join evidence:
  the new cell observes classification, while an existing test covers emitted
  protection.
- **Evidence:** Pure and Effect reuse, heap balance, both backend leak cases,
  and ABI-11 checks pass. Run, linked and REPL observations return 7. Module
  tests prove capture lifetime and both teardown dispositions; Reserved-word
  and capture-cleanup detection proofs fail under mutation and pass restored.
- **Final full suite:** `cargo nextest run --no-fail-fast` — **6,010 passed,
  one standing document-gate failure, one existing skip**; 114 seconds. No other
  RED. Raw evidence: `.local/s122-ior6-proof-dev-logs/ior6-full-suite.log`.
  Mutation restoration is byte-exact; no test expectation was weakened.
- **Document check:** 615 documents, **1,491 findings**; five prior identities
  removed against the 1,496-finding IO-review baseline, no new identity after
  the sprint reference repair. Role wiring and diff checks pass. The architecture
  once-only contract was replaced, removing 285 lines of superseded prose.
- **Final QA:** Claude / Fable / high, session
  `0b05ad08-de6a-49b9-8004-d241fb33c385`, finds implementation and evidence
  adequate for the approved correction. All reservations are complete.
  Test attribution stamps and runtime trace links now name the fixing commit
  and requirement; the ABI-11 test name is current. Any new test failure is a
  regression.
- **Residual limits:** host allocation counters cannot observe direct DLL frees;
  IOR-6 now keeps a host owner to make its final release visible and is proven
  to detect missing teardown. DLL-side capture-panic containment is asserted
  with a named falsifier; no new fixture is allocated for current captures.
  Launch/EffectPoll reuse, severed-join, abort-path and joined-fresh-arm/other
  result-ownership intakes remain separate, unmeasured work, not accepted
  semantics or newly approved scope.
- **Integration:** committed as `57253cf2`; Phase 5 remains active. Test
  fixed-commit stamps are complete in the current working tree. NOTES and the
  published shared-package index pin are preserved; no push or phase transition.

### Checkpoint and resumed document cleanup (2026-09-21)

Checkpoint `57253cf2` commits the accumulated document consolidation and approved
IO corrections: 224 files, 6,383 insertions and 27,289 deletions. NOTES and the
published shared-package pin were excluded; no push or phase transition.

Current reservations:
- `test` — Claude / Opus / high, session
  `fc053fc4-1c70-478b-b769-7ffaef400e8b`: complete; regression records name
  the fixing commit, runtime links are corrected, and the renamed ABI-11
  test passes. Assertions and fixtures are unchanged.
- `design` (typecheck) — Claude / Opus / high, session
  `6960113e-16a0-4c2e-9a6b-d5cf7dedcfd8`: complete; current master and
  annotation design replace spent plans, 1,741 context lines removed.
- `audit` — Claude / Fable / high, session
  `35dfcae9-f29d-494a-9fa0-f1c0695b6580`: complete; 26 reports reduced to
  nine, predecessor obligations reconciled, 24 obsolete diagrams removed.

Root applied incoming-link repairs and established the audit collection through
root guidance, with live reference checking retained pending user disposition.

QA follow-through: Claude / Fable / high, session
`d41025b3-827c-41ab-a805-327a0c6f6748`, complete: reconciled test records
and retired ACT-0950 after verifying shared-checker delivery. Open document debt
and external adoption decisions remain in their canonical carriers.

User ruling (2026-09-21): retain unaddressed audit points in their canonical
carriers; historical audit reports belong in Git history. No historical-reference
exemption. `audit` extracts remaining obligations before root retires reports.
Other audit disposition questions (host-extern wiring, tracked local settings,
and unwritten trails) remain recorded in the retained assessments. Typecheck
owner handoffs and the next ownership-inference consolidation are recorded in
`.local/s122-typecheck-doc-batch-result.md`; no behavior change is authorized
by those maintenance observations.

Integrated batch check: **1,491 → 1,321 findings** (171 old identities removed;
one new dated-audit line citation after the annotation-design contraction).
No suppression or historical-reference exemption was added. Role wiring and
diff checks pass. The post-checkpoint document and test-record batch remains
uncommitted at that checkpoint. NOTES hash and published
shared-package index pin remain unchanged.

Audit retirement reservation: Claude / Fable / high, session
`ca9279c9-5e9c-47ab-9402-c920f4f4824d`. Outcome: verify existing carriers and
prepare compact action content for uncarried points from all nine reports.
Root integrates the extracted points before deleting their historical carriers.

### Audit reports retired after point extraction (2026-09-21)

User ruling applied: historical audit reports live in Git, not in the standing
tree. Claude / Fable / high audit session
`ca9279c9-5e9c-47ab-9402-c920f4f4824d` mapped all recommendations and uncarried
predecessor points; no new audit or implementation approval was inferred.

- Existing filings 0553, 0848, 0857 and 0870/0871/0873/0874 remain their
  canonical carriers; 0848 now includes the previously report-only evidence
  detail. S122 QA evidence retains the two recovered review-session identities.
- ACT-0963 preserves accepted intrinsics work that lacked filings.
- ACT-0964–ACT-0967 preserve backend, integration, types and host-settings
  questions pending disposition, not approved implementation.
- ACT-0968 now carries the backend pattern-miss evidence gap after QA
  reconciled the frontend and call/value cases; ACT-0969 preserves
  observations for the next context audit without approving code changes.
- All nine remaining reports are retired; historical citations point to
  checkpoint `57253cf2`. No report archive or reference exemption was created.
- METHOD and audit guidance now keep new assessments only until their points
  are extracted and disposed. NOTES and the shared-package pin are preserved.

Audit retirement verification: **1,321 → 1,232 findings**, 89 old identities
removed and no new identities; 596 documents discovered. All historical audit
reports are absent from the standing tree; the seven new actions total 354
lines. Diff and role-wiring checks pass. The changes remain uncommitted; no
source implementation or assertion changed in this retirement pass.

### Current document consolidation reservations

Baseline: `.local/s122-audit-retired-documents.json`, 596 documents and 1,232
findings. All three reservations are documentation-only; no compiler or test
implementation change, new exception, commit, push or phase transition.

| Owner and surface | Provider / model / effort | Session | Status |
|---|---|---|---|
| design — typecheck ownership, monomorphisation and release obligations | Claude / Opus / high | `10544bf8-30ce-4165-ae26-b57e7ef54e05` | complete; three designs 6,871 → 1,740 lines |
| design — backend ownership/release contracts and spent visit records | Claude / Opus / high | `f54ef217-29c6-4b23-ac34-fef0c9ff0ad2` | complete; visit retired into current release contract |
| qa — dated evidence-record retention | Claude / Fable / high | `16bbb225-eeca-4d7f-9c2e-9e6abf4baeff` | complete; two records retired, cited sections retained |

Root integrates cross-owner citations and declarations, then runs the combined
document check. The current plan's completed D7 execution narrative has been
condensed; the canonical policy, open evidence leads and cited headings remain.

Evidence read: QA / Claude / Fable / high, session
`22ede80f-a4fa-43b4-b65c-1afce2ce7cf9`, complete. ACT-0968 is narrowed to the
remaining module evidence; no source implementation was dispatched in this
document batch. Arch / Claude / Fable / high, session
`d999c570-a9fb-4223-8656-0187ed2af4e7`, reconciles R10's per-variant grade
against that evidence. Root has established the QA support collection and
applied its scoped reference map; no historical exemption is adopted.

Backend integration caught a reintroduced once-only IO claim. The correction
ran as design / Claude / Opus / high, session
`cd81f403-4ee9-49d1-83ef-2e346e2aafbd`. Independent review / Claude / Fable /
high, session `989358ad-a8b1-404f-8ef1-729948785e1e`, confirmed reuse semantics
and required two wording corrections: Bind's shallow disposition transfers its
fields; Launch's non-zero guard belongs to runtime teardown. Root applied the
reviewer's exact ownership outcomes and mechanical references; no runtime
change or further review is allocated. R10's grade reconciliation is complete.

Combined ownership/QA batch verification: **1,232 → 1,000 findings**, 232 old
identities removed and none introduced; 593 documents. Diff and role-wiring
checks pass; backend source repoints change citation comments only. No runtime
assertion changed, so no broad suite rerun. NOTES and the shared-package index
pin remain unchanged. All role reservations are released; the batch remains
uncommitted. Next document concentrations are architecture boundary/ownership
contracts, Binary/int visit records, and specification references.
