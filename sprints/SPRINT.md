# Sprint 122: Known-issue closure and REPL-agent evaluation

**Status:** PHASE 5, final acceptance reconciliation: not yet ready for acceptance.
Latest consumer checkpoint: `bc675d86`; local shared-package checkpoint:
`c339fa7`. The compiler corrections,
bounded Haiku eval and IO reuse corrections have executing evidence. The
generated-inner-name collision fix is verified and committed.
Document consolidation continues: the last integrated check has zero findings
across 508 documents. Historical audit reports are retired to Git with
open points preserved. Current reservations appear at the end of this plan.
C-A cache-corruption hardening is user-deferred. The cache dependency direction
and exact API/schema are approved; implementation, independent review and QA
adequacy are complete. The full suite passed 6,144 tests with one skipped.
The user confirmed the generated three-line API addition; changes remain
uncommitted. DB-1, R1-V and LD-9 remain allocated for follow-up reproduction.
No phase transition or publication is authorized.

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
| Backend | 0747, 0781, 0782, 0891, 0900, 0903, 0906, 0907, 0915, 0916, 0917 |
| Types / public contracts | 0931, ACT-0954 |
| Intrinsics | 0835, 0848, 0857, 0934, ACT-0956; 0928 rustdoc remainder in `design/runtime/s119-typed-consume-funnel.md` §9 |
| Primitives | 0859, 0932, 0936 |
| Platform | 0870, 0871, 0873, 0874 |
| Language-facing closure | 0815, 0841 (0821/0823 closed: examples-local library ruling established) |
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

The [primitives consumer design](../design/primitives/primitives.md#24-typed-abi-boundary)
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

### Architecture and integration document continuation

Checkpoint `07f46769` records the completed consolidation and audit retirement.
Within Phase 5, `arch` reserves top-level `design/arch/*.md`; `design` (int)
reserves `design/int/*.md` for independent documentation-only consolidation.
Source, tests, NOTES and the shared-package checkout are outside these writes.
The integrated starting check is 1,000 findings across 593 documents.

| Role | Provider / model / effort | Session | State |
|---|---|---|---|
| arch | Claude / Fable / high | `56616baf-fe9b-4b64-b2eb-9e37c1a40e3a` | completed; architecture documents |
| design (int) | Claude / Opus / high | `b2ee8220-afb4-416a-a97a-a62a5a54d8d1` | completed; integration documents |

QA read `8917f705-8a26-4eea-9410-f0f8d3cc447d` (Claude Fable high, exit 0)
did not reproduce a generic-redefinition public failure. The named-caller
acceptance combination remains uncovered, and the reload seam remains
unobserved; keep both as pending Phase-5 evidence work, not a confirmed defect
or an accepted carry. The incidental macro-persistence suspicion is retained
in ACT-0970 for QA intake. No source behavior changed in this batch.

Review `523cb9dd-1872-4c0e-8f4f-bf65dea2ca33` (Claude Fable high) inspects
the rewritten boundary contract; design `011fbdcf-eedf-40da-a91e-8d691bfbd49b`
(Claude Opus high) owns the bounded integration wording correction.

**Integrated result:** 846 document findings, down from 1,000: 154 prior
finding identities removed, none introduced. Diff whitespace and role wiring
checks pass; all Rust changes are citation comments only. Review and the
bounded design correction completed successfully; reviewer-required label
restorations and comment repoints are applied. Their reservations are released.
The continuation remains uncommitted after checkpoint `07f46769`.

**Next cohesive work:** the architecture boundary-types guide and concrete
boundary contract still need consolidation. Before deciding whether to realise
or withdraw the approved publication-receipt rule, observe the generic
redefinition reload seam; design records the unrealised rule and its current
consumers in `design/int/int.md` §16.0. No withdrawal or implementation is
authorised by this documentation correction. Current CLI guidance exists at
`user/cli-reference.md`; the obsolete claim that `user/` is empty is retired.

### Boundary-guide and specification-citation continuation

Checkpoint `9c74e2eb` records the preceding verified batch. Phase5 continues:
`arch` reserves the boundary-types and concrete-boundary guides plus its index;
`qa` reserves only coverage annotation brackets in lexical, grammar and module
specifications. Starting check: 846 findings across 591 documents.

| Role | Provider / model / effort | Session | State |
|---|---|---|---|
| arch | Claude / Fable / high | `7f2ddc0c-0793-499d-aa6f-c89849f36b94` | completed; boundary-guide consolidation |
| qa | Claude / Fable / high | `293c6c3d-4919-4445-8e87-400bb53f785d` | completed; annotation-only edits |
| spec | Claude / Opus / high | `cfe4b422-bdf2-4f80-a49d-666b00126604` | completed; read-only authority assessment |

QA corrected unsupported coverage grades; pending evidence now appears in
`spec/01-lexical.md` §1.6 and `spec/08-modules.md` §8.1 and §8.11.3.
File-to-module mapping and DLL search tier2/order require discriminating
evidence. These are pending obligations, not scheduled implementation or
approved carries. Anonymous-function shorthand is specified but rejected by
the compiler; route its conformance gap to QA/test intake, not a unilateral
removal from the language.

**User decision pending, first:** `vec` is contradictory across the specification.
Grammar §2.3.9/§2.9 calls it core/reserved; macros §9.10.10 makes it a prelude
macro, as implemented. Recommendation: retain the library macro and bracket
literal as core, correct the conflicting grammar, then have QA reassess the
changed annotations. No normative edit before the ruling.

After that decision, the spec owner requests confirmation of unspaced rest
parameters: current lexical rules permit the spaced form, while source and
stdlib also use the unspaced form. A nameless rest marker is already invalid.
Present that separately; do not infer either answer from the cleanup approval.

Independent review `351f97bd-a009-4900-8027-6d1fa06a3ccc` (Claude Fable high,
exit0) found one required source-claim correction and two citation/status
repairs. Applied: the result-root consumers already share the derivation;
0898 remains an open filing requiring disposition. The signature fallback is
explicitly interim under safety-register R17. Review found no lost current
obligation and requires no re-review for these exact wording repairs.

All role reservations for this batch are released. API contraction candidates
are retained in ACT-0971; stale types-rustdoc leads join ACT-0966. Neither
action approves an API change. Follow-up architecture cleanup is the overlapping
total-concreteness and types-first reasoning records; 0789, 0798 and 0898 need
owner disposition against their source. The first user decision remains `vec`.

**Verified result:** 761 findings across 592 documents; 85 previous finding
identities removed and zero introduced. Specification edits are annotation-only
(byte-identical after stripping the coverage brackets). Rust edits are comment
citations only. Diff and role-wiring checks pass; no runtime test rerun was
needed. Continuation changes remain uncommitted after `9c74e2eb`.

### Approved vec specification correction

The user answered “agreed” after reviewing the consequences of retaining
`vec` as a library macro: bracket literals stay core; parenthesised `vec`
requires ordinary macro availability and is not reserved; neither form is a
first-class function. This explicitly approves removing the core `vec` grammar
alternative and reserved-word entry and identifying the library form accurately.
`spec` owns the bounded correction, then `qa` reassesses affected annotations.
The separate rest-parameter spelling decision remains unresolved.

**Vec ruling applied.** Spec sessions `b3ae55fb-d3a3-4057-950d-d100ce63652e`
and `7db12c7e-44bd-45c6-a5a5-0b4f248268c5` (Claude Opus high, exit0)
corrected grammar §2.3.6, §2.3.9 and §2.9. The final wording preserves ordinary
application to user-defined `vec` bindings as well as reference-macro invocation.
QA `43718f31-09d8-402c-998f-7e79cc8a371a` (Claude Fable high) reassessed
existing assertions: application is Tested+Neg; literal/reserved-word sections
and their rollup remain partial. Pending focused evidence: absent `vec` binding
rejects without a prelude; a user function named `vec` applies normally; the
reference macro cannot be captured as a function value. No runtime change or
new tests were part of this specification correction. These gaps remain open.

The first decision is resolved. The next user question asks whether spaced
and unspaced rest markers are both legal. No answer is inferred from the
`vec` approval; the rest-marker specification remains unchanged.

### Approved rest-marker spelling correction

User: “this would make & a reserved character that must be excluded from
symbols. allow both spellings.” Both spaced and unspaced rest-marker spellings
are approved; ampersand is reserved and excluded from ordinary symbol
characters. Nameless ampersand remains invalid. Spec records this ruling and
QA reassesses affected evidence; no unrelated syntax or implementation change
is implied.

Rest ruling: spec `f35388f9-c339-41d5-b174-1997c7f87fed` (Claude Opus high)
applied lexical/prose changes; QA `bf90a083-40a1-46d9-a5ab-1c98079262f3`
(Claude Fable high) verified spelling equivalence and nameless-marker evidence.
QA rejects the inference that the internal `Sexp::Symbol` carrier itself
violates lexical reservation. No confirmed defect or implementation change is
allocated on that basis. Identifier exclusion still lacks a committed negative
for `foo&bar`; spelling equivalence needs no duplicate e2e evidence.

One observable semantic question remains: quoted or macro-argument data
currently represents `&name`/`& name` as a single `SexpSym` marker carrying
`&name`. The lexical ruling does not decide this data representation. Ask
whether to retain it or expose separate marker/name elements before reader
changes. The spec owner’s inference of mandatory two-element representation
is not an approved ruling. Scope the lexical prose precisely when this question
is resolved; do not classify current behavior as a defect meanwhile.

### Rest-marker representation decision resolved

The user approved continuing with `SexpSym("&rest")` for now and requested
a future action. ACT-0972 owns the structural rest-marker proposal. Both
spellings remain one marker in quoted and macro-argument data; source
identifier reservation is unchanged. No implementation change is authorised.
Spec records the representation and scopes the identifier wording; QA updates
the affected coverage claim, preserving genuine untested boundaries.

Rest-marker closeout: spec `3874279a-c21b-4d14-ae36-c828b9e61bd5`
(Claude Opus high) and QA `609f4cd3-3169-4c86-9b10-8cdb581a772f`
(Claude Fable high) completed, exit0. Current carrier is explicitly documented;
ACT-0972 holds the future design. Existing reader tests support the approved
shape; identifier-exclusion and quote/macro transport coverage remain partial.
No defect is established by the current encoding. The separate macro rest-target
grammar and rest-position evidence questions remain pending assessment.
Final document check: 761 findings across 593 documents, zero introduced;
whitespace check passes. No compiler change or commit in this correction.

### Concreteness, lenient-eval and remaining spec citation batch

Phase5 continues from 761 findings. Arch reserves the two overlapping
concreteness records and their canonical arch destinations; design (backend)
reserves lenient-eval and its index; QA reserves coverage brackets in remaining
spec files. No implementation, API change, commit or phase transition is
authorised by this batch. The vec and rest-marker rulings stay settled.

| Role | Provider / model / effort | Session | Outcome |
|---|---|---|---|
| arch | Claude / Fable / high | `7bde1ab8-72fd-4125-a48b-d8fa2b3d24e7` | consolidation delivered; review correction below |
| design (backend) | Claude / Opus / high | `5bb43093-49e4-4b40-97b1-f23b04aab284` | lenient-eval consolidated |
| qa | Claude / Fable / high | `1ff2b61c-dc4c-4017-b1f2-4f2bb9e4bcc5` | annotation-only citation repair; five selected existing tests pass |
| review (backend) | Claude / Fable / high | `a4cbc24d-9182-4623-ad12-508326823c90` | no required finding; advisory wording corrections |
| review (arch) | Claude / Fable / high | `22944ca2-e446-4e7e-9c98-f59e137f51ef` | approval provenance and retained-prior claims require correction |
| arch | Claude / Fable / high | `17f9a886-1252-40d6-b45c-eaa168c7f5ef` | corrected; finding-scoped review below |
| dev (intrinsics) | Claude / Opus / high | `68d5c302-03d7-459c-8fed-d219b1bd4c39` | comments corrected; cargo check passes; no code change |

ACT-0973 retains the source-read platform-scope suspicion for QA reproduction.
QA's additional coverage limits remain explicit in the spec annotations: empty
select non-catchability and non-entry platform declarations. No new language
question is required for these unambiguous requirements.

| Role | Provider / model / effort | Session | Outcome |
|---|---|---|---|
| review (types architecture) | Claude / Fable / high | `d25e1f25-8a49-45e6-a1ea-2e33d1654e9d` | completed; remaining retirement wording corrected |
| qa | Claude / Fable / high | `0bde639b-0289-4c06-9193-686d64963a68` | completed; no call-target consumer found; no defect established |

Integrated document check: 704 findings across 593 documents; 57 finding
identities removed and none introduced against the 761-finding baseline.
The five consolidated architecture/backend documents fall from 63,569 to
15,850 words against checkpoint `9c74e2eb`, including retirement of the
superseded types-first commission. Open obligations remain in their canonical
contracts and filings. All Rust changes since that checkpoint are comments.
Whitespace check passes; NOTES.md is unchanged.

Intrinsics verification: `cargo check -p cranelisp-intrinsics` passes.
`cargo doc -p cranelisp-intrinsics --no-deps --document-private-items` succeeds
with 13 warnings elsewhere in the crate's existing rustdoc; this is not a
warning-free documentation build. Those references remain maintenance debt for
the intrinsics documentation pass. No runtime implementation change was made.

Concreteness approval provenance was checked against the checkpoint: the old
empty-vec-module contraction ruling was scoped to the de-slot change-set.
The module remains present; any removal still needs the repository's exact
public-API user gate. The retained-prior interpretation follows the user clarification below.

The finding-scoped review and QA census completed successfully. Review's
remaining clause correction includes ABI-changing tombstone retirement; this
is wording only and needs no further review. QA found no external prior reader
and no call emission, GOT access or callable publication through a provisional
scheme. The one-off source census discharges the requested investigation;
assurance grades remain unchanged. Cache-writer reachability was not traced,
and the retained-prior/non-concrete rebind branch has no dedicated test;
QA allocates no new independent acceptance condition for either observation.
The user's subsequent clarification is recorded below.

### Concrete-signature slots and retained callers

User: “only concrete signatures should have callable slots”, clarified by:
“the retained prior isn't callable by any new callers though - it is retained
to avoid stomping on existing callers, before we set up cascading recompiles.”
A retained index must not be equated with a callable slot assigned to the
unresolved replacement. The prior assessment inferred non-conformance from
physical storage and a missing signature payload; that inference is
withdrawn following the user's lifecycle clarification. No representation/API
change is allocated on that basis.

| Role | Provider / model / effort | Session | Outcome |
|---|---|---|---|
| arch | Claude / Fable / high | `7ab31477-d98c-481e-9d65-2791f89bc191` | initial assessment superseded by the user's retained-caller clarification |
| arch | Claude / Fable / high | `1fdc8ed1-b4a7-4f19-be06-e1b3f1afd01e` | completed; retained prior conforms; earlier non-conformance withdrawn |

The canonical contract and R11 now distinguish retention for existing concrete
callers from callability by new callers. No defect intake, representation
proposal, API packet, tombstone decision or additional census is required by
this clarification. Cascading-recompile implementation status was not assessed;
the wording correction makes no claim that it is delivered.

### Result/macro ownership and runtime documentation consolidation

Phase5 continues from 704 findings. Three independent design reservations
cover Binary/int result and macro ownership, intrinsics reactor and diagnostic
modes, and primitives current design plus completed visit records. Each owner
verifies current source, retains unresolved obligations, and retires spent
history. Root integrates cross-owner citation remaps and checks the combined
tree. No compiler implementation, API change or phase transition is allocated.

| Role | Provider / model / effort | Session | Outcome |
|---|---|---|---|
| design (int ownership) | Claude / Opus / high | `c120b207-3da2-4227-a436-06062f2b64d7` | complete; current ownership contracts consolidated; review below |
| design (intrinsics runtime) | Claude / Opus / high | `6cc56e2b-7704-4032-85cc-5cb819c732d1` | complete; runtime contracts consolidated; arch reconciliation below |
| design (primitives) | Claude / Opus / high | `06f57330-4f77-42bf-8b84-368a4954bd4a` | complete; two spent records retired into primitives master |

| Role | Provider / model / effort | Session | Outcome |
|---|---|---|---|
| dev (primitives documentation) | Claude / Opus / high | `ffa454fc-44d7-4aec-ac8b-1b218f482428` | complete; comments only; fmt and cargo check pass |

Primitives design consolidates 13,301 words into 3,036. Source comments,
shared runtime design and active evidence links are remapped to the canonical
typed ABI section. The source-read value-position String-wrapper concern is
retained as QA intake ACT-0974; it is not a confirmed or attributed defect.

| Role | Provider / model / effort | Session | Outcome |
|---|---|---|---|
| review (int ownership) | Claude / Fable / high | `efb40737-5c22-4171-bf5a-8267915c8ce5` | one required runtime-error residue wording correction; result ownership sound |

The int owner verified and absorbed 0927's Rule-0 enforcement: clause
preparation clears the inferred summary and the named unit fence exists.
The filing requested deletion when absorbed and is now retired. External
references to the completed result-owner slice/acceptance sections are repaired;
the S118 plan's own close-batch reference is made explicit. Other apparent
completed filings await their owning disposition; they are not silently closed.

| Role | Provider / model / effort | Session | Outcome |
|---|---|---|---|
| arch (reactor contract) | Claude / Fable / high | `4ff8608d-bdd8-4ef5-a400-31de1e9733c7` | complete; eager form already permitted; shutdown surface question routed to spec |
| design (int ownership correction) | Claude / Opus / high | `01c55402-0673-4b8e-a49e-4a68efb98d00` | complete; trap and runtime-error residue distinguished; ACT-0976 retains QA intake |
| dev (intrinsics documentation) | Claude / Opus / high | `81a7277a-8897-4cd3-8b7e-540ca6b6e9b8` | complete; comments only; fmt and cargo check pass |

ACT-0975 retains the synchronous Par-branch/poll reachability question as QA
intake. Neither source-read intake in this batch is a confirmed defect.
The int review preserves the prior distinction between source-delivered IO
reuse and pending integrated acceptance; consolidation does not grant acceptance.

| Role | Provider / model / effort | Session | Outcome |
|---|---|---|---|
| review (intrinsics runtime) | Claude / Fable / high | `5f1d3afd-ce13-43d5-861b-42afc15644b0` | completed; optional strand edge and overbroad diagnostic claims corrected |
| arch (platform record) | Claude / Fable / high | `0daf6379-0a45-48fa-9cd2-ab9d8cbc3833` | completed; eager state and optional lazy refinement recorded |
| spec (shutdown assessment) | Claude / Opus / high | `ab05d505-7315-44ee-b78b-51991d699be6` | completed; cancellation of launched strands is the user decision |

Arch found eager reactor construction already admitted by the governing
platform-interface record; lazy construction is a workload-triggered
refinement, not an unmet user requirement. Root applied the exact reactor
handoff and corresponding comment references. Cancellation and shutdown
requirements remain open. Spec assesses the missing program-visible shutdown
surface; the architecture report does not itself approve language changes.
Primitives source-backed origin/lifecycle terminology was corrected in its
master design using the dev handoff; no code or baseline changed.

The int correction follows the review's bounded wording repair: runtime errors
are distinct from trap/panic forfeits, and no unsupported residue bound remains.
ACT-0976 retains the risk/evidence intake. The correction changes no release
behavior, so the coordinator checks the wording and references without replaying
the review gate.

Connected runtime comment corrections compile and format successfully.
The combined private rustdoc build succeeds with 13 intrinsics warnings and
2 primitives warnings (existing broken/private links); it is not warning-free.
The global Rust diff still contains comments only, and NOTES.md remains unchanged.

Remaining connected documentation work retains explicit owners: arch's older
platform-interface coexistence narrative and stale public-API forecast need
consolidation; docs must reconcile the graceful-shutdown guide claim and assess
the undocumented drive-mode/backstop/degree settings; QA owns the two unfulfilled
shutdown/disconnect coverage rows. These are not closed by the runtime rewrite.

The intrinsics review's two required wording corrections are applied: the
crate-private strand sink is not an existing binary API edge, and the
single-reader/layout claims are scoped to the drop path actually guarded.
The bridge detection proof, retain-on-accounting-disagreement direction and
synchronous cancellation guard remain explicit. Source-comment advisories
about eager construction and the backstop's four readiness sources are
corrected from the review's source evidence. No further review is allocated
for these exact wording repairs.

The cancellation-scope decision is resolved by the user ruling below.
Architecture retains the spec's Vec select input and Int timeout duration.

| Role | Provider / model / effort | Session | Outcome |
|---|---|---|---|
| docs (concurrency guide) | Claude / Opus / high | `3c343088-2928-42a9-b9d9-38c92d34fdfa` | completed; both unavailable patterns clearly marked; no future behavior chosen |

This batch consolidates eight topic documents from 60,582 to 17,539 words,
retiring three spent design records; guidance and architecture corrections are
additional. The integrated checker has 630 findings across 592 documents:
74 baseline finding identities removed, none introduced. Whitespace and role
wiring checks pass. Source changes remain comments only. No commit or phase
transition occurred.

User ruling (2026-09-21): “ok agree - let's make coherent before adding more
capability.” Launched work inherits the cancellation context of enclosing effect
combinators such as race/timeout, not ordinary function-call lifetime or the
scheduler's placement choice. Normal program completion continues draining.
Reconcile spec, architecture, designs, guide and coverage claims before adding
capability. No task handles/groups, global cancel primitive, platform signal
leaf, drain-deadline shutdown policy or runtime implementation is allocated by
this coherence pass.

### Cancellation contract coherence

| Role | Provider / model / effort | Session | Outcome |
|---|---|---|---|
| spec | Claude / Opus / high | `731347f0-c576-419d-98b5-234c5dd595a5` | complete; affected requirements captured and coverage invalidated |
| qa | Claude / Fable / high | `434e5dcb-8036-42e8-bcbb-ebc7e1049752` | read-only assessment of cancellation/reference-pattern evidence |

Spec owns the first writable pass; downstream technical and user-document
alignment follows its canonical wording. QA's concurrent assessment changes
no spec text and separates test execution from what assertions discriminate.

| Role | Provider / model / effort | Session | Outcome |
|---|---|---|---|
| arch | Claude / Fable / high | `5fc6f9ea-8965-41c5-bf00-df66f9b62186` | align architecture and hand off runtime-design wording |
| docs | Claude / Opus / high | `221def51-8e09-4c07-965d-02ed6a177f8a` | align guide with settled semantics and current implementation limits |

Spec records cancellation contexts at effect execution, nested by explicit
combinators. Ordinary calls, returns and inferred launch placement do not
create or cancel contexts. Losing/timed-out contexts cancel their descendants;
winning branches do not themselves trigger cancellation. The existing normal
completion drain is preserved. This coherence work changes no runtime behavior.


| Role | Provider / model / effort | Session | Outcome |
|---|---|---|---|
| test | Claude / Opus / high | `e333e305-cd0b-4ed1-beb3-0dff14eccfd3` | corrected two test names/traces; retired vacuous SIGTERM test and unused helper; two focused tests pass |
| spec (appendix C) | Claude / Opus / high | `d52431d7-84e6-4769-9914-3a88db9f4366` | final summary alignment |

Architecture and guide alignment are complete. Sprint applied arch's exact
reactor wording handoff: the current supervisor lifetime is distinguished from
the specified cancellation ownership; fault supervision and normal draining
remain separate. No new runtime mechanism is chosen.

QA's assessment invalidates shutdown/disconnect claims. The web survivor test
now names server survival after an abandoned request; the direct-race test
names cancellation and permit reuse. The SIGTERM test proved only process death
and is retired. Partial direct-race observations have not been promoted into
coverage of whole requirements covering launched descendants or reference
patterns. Changed requirements remain uncovered.

[ACT-0977](actions/ACT-0977-scoped-launched-work-cancellation-evidence.md)
retains the next evidence and implementation work: a minimal launched-work
cancellation reproduction and controls, then intrinsics design and realization.
Normal-drain evidence needs an observable completion witness. Platform
shutdown/disconnect leaves remain separate missing capabilities. REPL execution
is unchanged; this pass introduces no cross-input background work contract.


Coherence pass verified: two selected nextest cases pass (17 not selected);
19/19 citations in the two changed test files resolve. Coverage reconciliation
finds 831 live test citations with no missing files or test names; three cleared
coverage markers remain uncovered following QA's assessment. Role wiring and
whitespace checks pass. The document checker retains 630 findings across 593
documents, with zero finding identities introduced or removed relative to the
preceding 630-finding checkpoint; the additional document is ACT-0977.
Appendix C now links the cancellation-context rule and includes launched work.
The concurrency teaching example contains no obsolete scope-exit claim.
Production behavior is unchanged. NOTES remains untouched, and neither it nor
.agents is staged. No commit, phase transition or capability implementation is
part of this pass.


### Integration subsystems and platform-contract consolidation (2026-09-22)

The user requested continued cleanup. Remain in Phase 5; cancellation capability
stays in ACT-0977. Two disjoint documentation reservations consolidate current
contracts and retire accumulated history against the canonical homes. No source,
test, API, schema or behavior changes are allocated.

| Role | Provider / model / effort | Session | Reservation and outcome |
|---|---|---|---|
| design (int) | Claude / Opus / high | `592f93c0-b976-4974-8495-8f4f7fce2f30` | complete: four current subsystem designs and local index updates |
| arch | Claude / Fable / high | `5fb048ba-09e4-416e-9ee6-9cf90f43d420` | complete: current boundary contract, preserved live section references |

Baseline: 630 document findings; the four integration documents contain 47,282
words and the platform-interface document 17,866. Root integrates external
mechanical handoffs and verifies the combined result. NOTES and the .agents
Gitlink remain excluded.


| Role | Provider / model / effort | Session | Outcome |
|---|---|---|---|
| spec | Claude / Opus / high | `7b345e8f-c2fb-4ada-bac2-4d6213a2da16` | assessed closure-callback conflict against S98 ruling; exact replacement supplied |
| qa | Claude / Fable / high | `2775f537-568e-413c-ad70-504650addb1c` | complete: corrected evidence guidance, closed stale feeder record, classified three source-read leads |

Five documents consolidated from 65,148 to 16,008 words. Current source facts
replace completed migration plans; useful section identities and unresolved
obligations remain. Sprint integrated the owners' mechanical cross-reference,
output-budget and source-comment handoffs. Platform test-trace observations
are retained in [ACT-0978](actions/ACT-0978-platform-test-trace-intake.md).

User ruling 2026-09-22: “State the boundary and require rejection”. Applied
spec's exact proposed replacement at `spec/10-io.md` §10.10.1: platform parameter
and result types must not contain function types, and implementations must
reject those declarations. The obsolete closure-invocation/RC callback promise
is removed. Coverage is invalidated, not inferred from the architecture ruling.
[ACT-0979](actions/ACT-0979-platform-function-type-rejection.md) retains QA
allocation and possible defect intake. Runtime behavior is unchanged.


Integrated outcome: 630 → 577 document findings (53 identities removed,
zero introduced), across 597 documents. The five consolidated designs contain
16,013 words after QA's primer wording correction, versus 65,148 before.
The added documents are unresolved intake actions, not retained historical
reports. Whitespace and role-wiring checks pass. All 831 spec-to-test citations
resolve to existing tests. No behavior test was run for this documentation-only
batch; Rust changes here are comments. Workspace formatting check reports
existing differences in untouched `src/repl/format_type.rs`, `src/repl/mod.rs`
and `tests/spec_04_expressions.rs`; no formatting sweep was applied.

QA closed the stale agent feeder-design record and corrected private probes,
form-count routing, the delivered membrane, request observation and Lane D's
actual rendering evidence. It did not allocate tests merely because direct
`free_vars_expr` coverage is absent; the existing binder-scoping risk and trigger
remain in the scheduling design.

New source-read leads remain unconfirmed:
[ACT-0980](actions/ACT-0980-cache-restored-declaration-persistence-intake.md)
prioritizes potential authored-source loss after warm-cache regeneration;
[ACT-0981](actions/ACT-0981-multi-signature-io-scheduling-intake.md) follows with
multi-signature automatic scheduling. Neither is closed or represented as a
reproduced defect.

Next coherent document batch: the agent architecture, REPL summaries and QA
strategy still contain older surrounding claims. Reconcile architecture's
unbuilt pull-to-harvest/seq-recency targets and echoed-read descriptions with
private-probe requirements; align the spec's older echoed-read summaries with
its explicit private-probe rule. Finish the QA strategy's S88 framing, stale
suite timing, missing memory/role/ledger references and unbuilt spec-grep claims.
Keep pin-admission versus disclosure as the already-open design/spec question.
The platform ABI spec's incomplete ADT type list also needs spec assessment;
it was not changed by the approved function-type rejection edit.

No commit or phase transition. NOTES hash remains unchanged and .agents is
unstaged. All four role dispatches in this batch completed successfully.


### Agent architecture, summaries and assurance coherence (2026-09-22)

User requested continuation in Phase 5. Three disjoint document reservations
complete the prior batch's identified agent-document handoffs. No capability,
source or test work is allocated; existing unresolved pin-admission/disclosure
and defect intake remain separate.

| Role | Provider / model / effort | Session | Reservation and status |
|---|---|---|---|
| arch | Claude / Fable / high | `712d0749-e3e9-4009-a8f3-26895b0fed66` | complete: current architecture, distinct optional targets, historical duplication retired |
| qa | Claude / Fable / high | `d5f36ec9-f57c-449e-b1e4-8325dd7cbf1d` | complete: current evidence authority and execution limits |
| spec | Claude / Opus / high | `ab1b73b8-c9b7-48ae-a2ed-e6146ce978ad` | complete: summaries aligned with existing probe rule |

Baseline: 577 findings, 597 documents. Sprint integrates mechanical external
handoffs and verifies the combined tree. No commit or phase transition.


| Role | Provider / model / effort | Session | Outcome |
|---|---|---|---|
| spec (follow-up) | Claude / Opus / high | `0d0d1698-7e60-4d0d-93d9-3dc207eeba6b` | complete: streaming/styling summaries and existing Document-edit echo sites aligned |

Architecture now distinguishes delivered boundary intent, optional targets and
unresolved questions. Pull results already return via the transcript, so arch
withdraws the unrealised pull-to-harvest interlock; recency remains optional
int-owned tuning. Existing pin/disclosure and ACT-0952 cache-write questions
remain. No new behavior, API or requirement is introduced.

Spec carried the existing private-probe rule into older summaries, worked
examples, prompt-site descriptions and streaming/styling text. Sprint applied
its mechanical language-awareness handoff for syntax/search pulls. Human
commands still display results. Probe membership retains its existing dev
discretion; neither that nor the shell-proposal prompt needs a new decision to
complete this alignment. The latter remains unspecified; this pass selects
no behavior for it.

QA's strategy retains the four evidence lanes and existing obligations, but
removes completed planning, duplicate shared procedure, outdated live-eval
instructions and false feature-off detection claims. Architecture and QA
strategy shrink from 17,269 to 7,080 words. The main spec gains clarity rather
than being shortened (10,579 → 10,692 words). Mechanical external references,
classifier comments, request-content commentary and local test guidance align.
[ACT-0982](actions/ACT-0982-agent-module-evidence-routing.md) retains the
feature-gated module-evidence execution question without adding a new gate.

Integrated check before adding that action: 577 → 566 findings, 11 removed
and none introduced. Whitespace and role wiring pass. No runtime tests were
needed or run: executable code and test assertions are unchanged. NOTES
hash is unchanged; .agents remains unstaged. No commit or phase transition.

Final verification including ACT-0982: 566 findings across 598 documents;
11 baseline identities removed, none introduced. All four dispatches closed.


### Decision records and typechecker topic designs (2026-09-22)

User requested continued Phase-5 documentation cleanup. Two independent
reservations consolidate current contracts and retire spent implementation
history; no source, test, API, schema or behavior changes are allocated.

| Role | Provider / model / effort | Session | Reservation and status |
|---|---|---|---|
| arch | Claude / Fable / high | `0dfbd0d5-5956-499a-b093-0f94fe15b56c` | complete: compact operative records with explicit retirement handoffs |
| design (typecheck) | Claude / Opus / high | `55417728-1ee9-4ced-bd78-a191dde9e101` | complete: current accessor and signature-matching designs |

Baseline: 566 findings, 598 documents; five target documents contain 21,209
words. Sprint owns integration of exact mechanical external handoffs and the
combined reference check. NOTES and .agents remain untouched.


| Role | Provider / model / effort | Session | Outcome |
|---|---|---|---|
| design (typecheck siblings) | Claude / Opus / high | `0530c4ed-2ce7-417e-87b4-6268e0cb90fb` | complete: ADT/trait summaries distinguish approved overlap from obsolete rejection |
| design (constructor finish) | Claude / Opus / high | `894c1780-312c-43fc-96c0-1c55ed9cfacf` | complete: constructor design consolidated onto canonical bindings and candidates |

Six topic documents reduce from 25,594 to 7,022 words. The original five
alone reduce from 21,209 to 5,003 words. Source-read corrections preserve
operative rulings, algorithms, useful rationale and live citation subjects;
completed inversion, rollout and facade-migration plans are retired into Git.
Sibling ADT/trait descriptions and the backend's primitive-startup hook name
are aligned. Source and test assertions are unchanged.

[ACT-0983](actions/ACT-0983-accessor-impl-collision-intake.md) retains the
obsolete accessor/impl rejection for QA reproduction; it is not closed by the
document edit. ACT-0984 (resolved; filing retired)
retains the trace-under-link rejection test's conflict with current authority.
Neither source-read lead is represented as an executed reproduction.

The three decision records remain compact citation anchors. Their Retirement
tables name each remaining repoint and extraction: the Approach-B rationale
belongs in interfaces, the primitive-construction rejections in bounded
contexts. Deletion awaits those moves, source/test repoints and the obsolete
trace-test disposition. Principle edits retain their existing sprint-close
boundary. No source citation has been broken merely to delete a record.

Remaining connected work: the non-concrete producer design still carries older
alias/poison wording and an unqualified collision preflight; typecheck source
comments also retain the old model. Constructor-pattern selection remains an
existing approved-design implementation obligation, explicit in the current
constructor design. Typecheck crate-root rustdoc's check_forms example has a
stale parameter/result shape; no API change is proposed.

Final integrated check: 566 → 522 findings across 600 documents, 44 baseline
identities removed and zero introduced. Whitespace and role wiring pass.
No builds or behavior tests were run for this prose-only batch. NOTES hash
is unchanged; .agents remains unstaged. All four dispatches completed.
No commit or phase transition.


### Typechecker guidance and producer obligations (2026-09-22)

User requested continued cleanup in Phase 5. Finish the connected typechecker
memory/source-comment alignment and producer-design consolidation. No code,
assertion, API, schema or behavior changes are allocated; ACT-0983 remains the
separate obsolete-rejection intake. Dev holds the sole source-edit reservation.

| Role | Provider / model / effort | Session | Reservation and status |
|---|---|---|---|
| dev (typecheck) | Claude / Opus / high | `fe20e805-d37d-437c-a34c-bb462dbed4d4` | complete: crate memory and source documentation; rustdoc follow-up below |
| design (typecheck) | Claude / Opus / high | `a4e9b379-2cf7-4e6f-895c-68f39f5d6897` | complete: corrected producer routes and explicit current residuals |

Baseline: 522 findings, 600 documents. The two Markdown targets contain 6,548
words; source documentation is additional. Root integrates external mechanical
handoffs and runs the document check. NOTES and .agents remain untouched.


| Role | Provider / model / effort | Session | Outcome |
|---|---|---|---|
| dev (typecheck rustdoc) | Claude / Opus / high | `0542de04-150c-4e06-a8c0-2f52fbcbd9e2` | complete: all 15 rustdoc warnings corrected against current source |

The main dev pass corrected obsolete Alias/Ambiguous/poison descriptions,
misleading test comments and the check_forms signature/return example. Root
confirmed zero non-comment source diff lines. The API itself is unchanged.
Root ran the scoped offline private-item rustdoc build successfully after the
role could not run it; 15 warnings prompted the bounded follow-up above.

The producer design corrected concrete-installation ownership, demand
derivation and release-contract citations. It grew modestly to retain explicit
residuals and distinguish required behavior from the obsolete as-built
accessor/impl rejection. Sprint applied the supplied mechanical R18 register
correction: strict-retry/refusal, not the retired typechecker census counter.
Backend's separate category-census obligation remains as its owning design
states it; no prior aggregate/Q3 acceptance is reopened.

Source-read lead checked by sprint: the misleadingly named
`tests/spec_08_name_shadowing.rs::def_over_import_repl_rejected` asserts
ambiguity at use time after both candidates register. Its name alone does not
establish a contradictory rejection assertion; no defect intake was created
from that naming observation. Actual accessor/impl rejection remains ACT-0983.


Final verification: 522 → 507 document findings across 600 documents;
15 baseline identities removed, none introduced. The two Markdown targets
shrink from 6,548 to 3,509 words (crate memory 4,234 → 1,097; producer design
2,314 → 2,412). Runtime behavior, APIs and assertions are unchanged: root's
final whole-crate source diff check again finds zero non-comment changes.

`cargo doc -p cranelisp-typecheck --no-deps --document-private-items --offline`
passes with zero warnings after the follow-up. Scoped formatting, whitespace
and role-wiring checks pass. No runtime tests were needed or run. NOTES hash
remains unchanged and .agents is unstaged. All three role dispatches closed;
no commit or phase transition.

Remaining typecheck documentation residue: plain-code ModuleEntry/DefKind
wording in unrelated comments, stale test names/assertion message wording, and
older program.rs/traits.rs paths in check-form-api, hkt and decomposition
designs. These are not hidden by the clean rustdoc build: plain code spans and
non-rustdoc comments are outside its link checks. ACT-0983 and the approved
pattern-selection implementation obligation remain unchanged.


### Typechecker design records, macro ownership and test discovery (2026-09-22)

User requested continued Phase-5 cleanup. Two independent documentation
reservations consolidate current designs and assess completed-record retirement,
with useful content extracted into canonical homes before deletion. No source,
test, spec, API, schema or behavior change is allocated.

| Role | Provider / model / effort | Session | Reservation and status |
|---|---|---|---|
| design (typecheck) | Claude / Opus / high | `511c3863-4a8b-4ac4-8288-7c24e9d964ac` | complete: extracted current contracts, retired both completed records, rewrote HKT |
| arch | Claude / Fable / high | `d96c6803-f6bb-41af-9b27-55ce03ad1d30` | complete: current contracts reconciled; source/spec handoffs retained below |

Baseline: 507 findings, 600 documents; five main targets contain 29,533 words.
Related topic extraction/navigation is reserved to the same owner. Sprint
integrates external mechanical remaps and verifies the resulting tree.
NOTES and .agents remain untouched.


Outcome: the check-form API and S87 traits-decomposition working records are
retired; their pass contracts, visibility/cohesion rules and monomorphisation
state channels live in the current typecheck master, traits and monomorphisation
designs. HKT now states current design and open questions. Macro ownership and
test discovery retain the adopted contracts rather than completed migration
narratives. Architecture boundary and interface prose now correctly places both
macro recognition calls and execution in the binary's expand loop.

Sprint integrated the owners' exact external citation remaps, removed the two
retired paths from collection membership, and disambiguated references with
explicit paths or Markdown anchors. Historical checker-reconciliation evidence
was left intact. Source integration touched 13 Rust files; comparison with the
pre-integration snapshot finds zero non-comment deltas. Test names, bodies and
assertions are unchanged.

Verification: **507 → 472 findings**, 35 prior identities removed and zero new
identities. The corpus remains 600 documents: two working records retired and
two QA intake actions added. The five main targets fall from 29,533 to 6,990
words; this is not the net extraction-inclusive measure. Including their four
canonical typechecker destination/memory documents, the measured design set
falls from **4,970 to 2,956 lines (41%)**. Small topic/navigation repairs in
other arch carriers and the new intake records sit outside that measure.
Whitespace and role wiring pass (11 dispatched roles, 26 principles, zero local
wiring findings). No runtime tests were needed or run for documentation/comment
changes. NOTES retains its recorded hash; nothing is staged and no commit or
phase transition was made. Both provider dispatches closed successfully.

New source-read intake, explicitly not executed defect evidence:

- **ACT-0985** routes declaration forward-reference/test tension, result-only
  higher-kinded constructor dispatch and primitive-spelling rejection to QA.
  The current typecheck and HKT designs retain the underlying questions.
- **ACT-0986** routes test-discovery eligibility differences, missing warning,
  IO-versus-pure signature, unauthored sugar and stale linked-mode description
  to QA and spec. It does not authorize changing a normative contract.

Remaining owner handoffs for the next documentation batch:

| Owner / surface | Outstanding work |
|---|---|
| dev, types | `crates/cranelisp-types/src/macro_expander.rs` still describes typecheck as callback consumer and cites a retired macro-recognition design. Arch supplies the replacement contract: implemented and called by the binary Pass-1 loop; recognition through `ResolutionScope::resolve_macro_head`; current authority is `design/arch/macro-expansion-ownership.md`. Public documentation only, no signature change. |
| dev, frontend | `crates/cranelisp-frontend/src/lib.rs` still assigns recognition, expansion fixpoint and gap surfacing to typecheck. Reconcile with the current binary-owned loop contract. |
| dev, int | `src/CLAUDE.md` test-discovery table and macro entry still use DefKind, the old session body location, and the incorrect shared-discovery-core claim. Source comments in bootstrap, exe and test_runner also retain the retired entry vocabulary. The corrected arch contract owns the replacement; preserve ACT-0986's as-built eligibility divergence. |
| dev, backend | `crates/cranelisp-backend/src/jit.rs` retains PrimitiveExtern wording; the current test-discovery design records host-promised RustPrimitive publication. |
| spec | `spec/08-modules.md` still describes mutual-import deadlock although bounded contexts records a diagnosed cycle. Assess and reconcile the implementation note without changing the governing prohibition on silent nontermination. Appendix A discovery discrepancies are ACT-0986. |
| design, typecheck | Retire `program-decomposition.md` after extraction; reconcile inference's retired pipeline account and traits' obsolete name-freedom gate/loci. ACT-0983 retains the separate real accessor/impl rejection question. |
| arch | `design/arch/macro-availability-model.md` still carries deliberation and superseded recognition ownership beyond its current ruling; this batch only repointed its incoming contract citations. |

Role disclosure: design initially ran read-only status/diff despite its brief's
no-git instruction, then stopped those operations. No Git mutation occurred.


### Test-discovery requirement assessment (2026-09-22)

Following the cleanup's ACT-0986 leads, a read-only spec pass checks existing
user/spec authority before presenting any new decision. This remains Phase 5.

| Role | Provider / model / effort | Session | Reservation and status |
|---|---|---|---|
| spec | Claude / Opus / high | `25b7b7c9-1981-41b9-94db-c9e27c94316e` | complete: existing rulings recovered; IO-versus-pure and empty-vector scope require user arbitration; no tracked edits |


| Role | Provider / model / effort | Session | Reservation and status |
|---|---|---|---|
| dev (types) | Claude / Opus / high | `97af6fa0-81e9-4a96-90fb-858b15231fc9` | complete: callback ownership, raw arguments, sequencing and error documentation corrected; comments only |


Spec assessment recovered a genuine unresolved return-type choice: S76 ruling
prose says a vector, while signature listings and the normative REPL spec say
IO. Present that decision first. Empty-vector module scope follows separately:
the implementation reads the session module whereas earlier sugar rationale
baked in the caller module. No normative text was changed.

The claimed missing sugar was disproved: `stdlib/testing/runner.cl` implements
`discover-here`. Sprint corrected arch's as-built paragraph and ACT-0986 from
the spec handoff after opening the macro. The primitive's advertised shorthand
examples remain a separate spec correction. Friendly linked-mode refusal and
mutual-import cycle diagnosis are already settled; their exact normative edits
still return under the local edit gate. Warning and eligibility observations
remain QA intake against settled requirements.

Types dev completed the macro callback rustdoc correction. Runtime items and
signatures are unchanged; the module now places invocation in the binary,
records unexpanded arguments and fresh result spans, and removes obsolete gap
sequencing. The scoped offline private-item rustdoc build passes. Root also
validated all 29 changed test-to-design annotations from this batch.

Retained source/contract mismatch from types dev: the binary maps a malformed
returned macro value to MacroInvokeError::Aborted, although the Malformed
variant documentation assigns malformed results to that variant; no matching
clause produces Malformed. No mapping change was made. Arch owns reconciliation
of that public error contract before any implementation change. Source-read
loci are `src/expander.rs` invoke_clause and macro_error_to_invoke_error; this
is not executed defect evidence. The dev report's suggestion of no observable
impact is not acceptance evidence: Display uses different variant messages.

The frontend and int macro-documentation handoffs above remain; only the types
row is now discharged. No independent code review or runtime test was added
for this comments-only repair. No API baseline changes, commit or phase advance.


Final integrated checker remains 472 findings (35 removed, zero introduced).
Both follow-up dispatches closed successfully; root independently confirms zero
non-comment changes in the callback diff. Rustdoc exits successfully and the
new callback links resolve, but it reports four warnings elsewhere in types:
`resolve.rs` names retired BindingBody::Alias; `concrete.rs` has one redundant
Type link; `mono_expr.rs` has two redundant Expr links. These remain a concrete
next types-documentation repair, not a zero-warning claim. No runtime evidence
is inferred from that build.


### Discovery as notionally constant introspection (2026-09-22)

User chose to treat introspection functions as notionally producing a constant
in response to the pure-vector versus IO-vector decision. The approved delta
is discovery's direct vector result, with no IO wrapper. This does not approve
an introspection platform, freeze live state, or decide empty-vector module
scope. Spec records the ruling; sprint integrates its mechanical design handoff.

| Role | Provider / model / effort | Session | Reservation and status |
|---|---|---|---|
| spec | Claude / Opus / high | `91f697b2-8b90-413e-8e55-1ff9de45cd82` | failed before edits: provider 529 overload; zero tool uses and provider tokens; retry follows |


| Role | Provider / model / effort | Session | Reservation and status |
|---|---|---|---|
| spec retry | Claude / Opus / high | `e92a3882-b331-4f69-9245-f887e344155f` | failed before edits: provider 529 overload on retry; no model substitution |


Both attempts to apply the settled ruling failed at the provider with HTTP 529
Overloaded before any role tool use or edits. The normative files and design
remain unchanged from the pre-dispatch snapshot. The approved user ruling is
retained here and ACT-0986 marks the return-type question settled; the exact
specification edit remains pending on the allocated Claude spec route. This is
a provider outage, not a request for more user approval. No alternative model
or coordinator-authored normative edit was substituted.


User requested another attempt after the provider failures.

| Role | Provider / model / effort | Session | Reservation and status |
|---|---|---|---|
| spec retry 2 | Claude / Opus / high | `bdca3624-8cfe-45d5-a90d-5d3053f63f82` | complete: direct-vector requirement and rationale recorded; coverage invalidated for QA |


The user-requested retry succeeded. REPL section 16.3 now requires the direct
vector result and records notionally constant introspection; all three result
type copies and the Appendix A function scheme drop IO. Existing freshness
requirements are unchanged. Coverage is marked Uncovered S122; Appendix A
preserves its former S77 provenance. ACT-0986 retains QA reassessment and the
separate scope, warning, eligibility and stale-example obligations. The design's
unresolved signature-divergence bullet now points to the settled normative home.
No runtime, test, public-API or unrelated normative change was made.

Verification: shared checker remains at 472 findings, with zero introduced
identities; whitespace check passes. The spec dispatch closed successfully.
NOTES retains its recorded hash. No runtime tests were needed for this prose
change, and coverage reassessment remains with QA under ACT-0986. No commit or
phase transition.


### Checkpoint and remaining pipeline/macro guidance (2026-09-22)

User authorized checkpoint and continuation. Commit `7134cb28` records the
completed cleanup and settled language rulings; NOTES and the .agents Gitlink
were excluded. Whitespace and role wiring passed before the commit. New work
continues within Phase 5, with a 472-finding baseline.

| Role | Provider / model / effort | Session | Reservation and status |
|---|---|---|---|
| design (typecheck) | Claude / Opus / high | `772de8bd-8e98-42f5-8b52-93ff7c889a39` | complete: plan retired; inference and traits current; canonical extraction and open findings retained |
| arch | Claude / Fable / high | `3f081cc3-4c2b-46e9-aa93-035a871836c9` | complete: current availability contract; obsolete deliberation retired; references integrated |

The separate discovery empty-vector module-scope question has been presented
to the user while these independent documentation passes proceed. No answer
is assumed and no dependent normative edit is authorized yet.


Outcome: program-decomposition is retired after extraction into the typecheck
master; inference and traits now describe the current state, registration,
resolution and pipeline. Macro availability retains the adopted source-order
checkpoint contract and concise rejected-alternative rationale, with ordinary
S76 deliberation left in Git. The measured six-document set, including canonical
typecheck extraction destinations, falls from 30,163 to 11,237 words (63%).
Unchanged monomorphisation is not counted in that reduction.

Sprint integrated the roles' external reference maps, removed retired collection
membership, and replaced ambiguous section shorthand with exact links. It also
applied the prior source-guidance handoffs: host-promised RustPrimitive naming,
the actual separate discovery scans, binary-owned macro expansion, the current
resolution-query spelling, and stale scaffold/test-header prose. Current callers
were read before updating the no-gap helper's comment: only REPL /type calls it.
All Rust deltas since the checkpoint are comments; no executable changes.

The sequence source and generated SVG now cite macro availability section 5.
The default Puppeteer browser was x86-only; snap Chromium could not access the
system-installed CLI HTML. Rendering succeeded using the installed CLI copied
into ignored target space with its existing dependencies and native Chromium;
no installation or repository tooling change. XML text comparison finds exactly
one label difference, the intended section reference.

Verification: 472 → 468 shared-document findings, four identities removed and
none introduced. Whitespace and role wiring pass. The scoped frontend/typecheck/
backend private-item rustdoc build succeeds. It reports one frontend warning in
ast_builder.rs and 17 backend warnings across apply, fn_as_value, utilization,
literals, context and fn_compiler; all are outside this batch's edited source
files. These unresolved rustdoc references are retained for the owning dev
passes, separately from the shared Markdown checker. Typecheck has no warning.
No runtime tests were needed or run. Both Claude dispatches closed successfully.

ACT-0987 routes the two newly retained typecheck source-read leads to QA: bare-name
primitive dispatch identity and impl-method constraint rigidity. No failure is
claimed executed. The dead default-body fallback's design disposition remains
in traits open items for a later narrow dev pass. Existing ACT-0983/0985 obligations
remain open. The discovery module-scope question is still awaiting user ruling;
sprint clarified that the older text concerned caller-module macro sugar, not
an explicit empty-vector primitive rule, and described explicit-empty semantics
as another option. No dependent spec or behavior change was made.

The checkpoint was already committed; subsequent work in this batch remains
uncommitted. NOTES and the .agents Gitlink remain excluded and unchanged by this
work. No phase transition.


### Discovery scope ruling and deferred uplift (2026-09-22)

The user approved retaining current empty-vector discovery: session current
module only, without expanding through imports. This settles the earlier
module-scope question. Broader project regression discovery is explicitly
deferred to a future sprint in
[ACT-0988](actions/ACT-0988-project-regression-discovery.md); no future scope or
API is selected. ACT-0986 retains evidence reassessment and its other unresolved
contract discrepancies.

Spec dispatched on Claude / Opus / high, session
`ef914af9-dd24-45e6-b0bc-2ee62a270ea7`, to record the approved scope in the
canonical requirements. No runtime change, commit, or phase transition.

Spec completed successfully. REPL section 16.3 and Appendix A now state the
approved session-module scope; sprint integrated the supplied mechanical
design wording. Existing Uncovered S122 annotations remain for QA reassessment.
Whitespace passes; the shared document checker remains at 468 findings with
zero introduced or removed identities. No runtime tests were needed for this
prose-only change. NOTES and the .agents Gitlink were not touched.


### Discovery primitive call shapes (2026-09-22)

The user explicitly approved correcting the primitive signature and runner
examples to vector arguments and documenting the library's optional
`discover-here` macro separately. No compiler or library behavior change.
Spec dispatched on Claude / Opus / high, session
`c8974fd3-244f-48d1-8cc9-67f32b966fe0`, within Phase 5. The remaining linked-mode
prose correction is separate from this approval.

Spec completed successfully; signature, discovery calls and optional macro
prose corrected in REPL section 16 and Appendix A. Sprint integrated the exact
design handoff and updated ACT-0986 with remaining example syntax/import and
parse-only test attribution leads. These are source-read findings, not executed
failures. Existing uncovered evidence status remains; runtime tests were not
run for this documentation-only change. Whitespace passes; shared checker
findings stay at 468 with zero introduced or removed identities. No commit,
phase transition, NOTES change or .agents Gitlink change.


### Normal execution capability parity and future test mode (2026-09-22)

The user confirmed that ordinary --run and release execution should expose the
same language capabilities; execution and optimization strategies may differ.
The proposed discovery --link prose correction is held. The direction toward
an explicit --test harness is retained in
[ACT-0988](actions/ACT-0988-project-regression-discovery.md) with the deferred
discovery uplift. REPL harness policy and the detailed test-mode contract remain
open. ACT-0986 now distinguishes this future direction from current behavior
and from the unapproved proposed wording. No normative spec or runtime change
in this step, and no claim that --test is implemented.


### Checkpoint and historical QA plan consolidation (2026-09-22)

User authorized checkpoint and continuation. Commit `7b1220c7` records the
completed documentation consolidation and discovery rulings (43 files). NOTES
and the .agents Gitlink were excluded. Whitespace and role wiring passed; Rust
diffs were verified comment-only. The document-check baseline is 468 findings.

QA on Claude / Fable / high, session
`fb16cf9b-28aa-4952-83f8-f2f68a38de1b`, is assessing the S113/S114 retained test
plans as one batch, preserving current obligations and reducing dated standing
material. No runtime changes, new testing campaign or phase transition.

A disjoint design (stdlib) pass on Claude / Opus / high, session
`fbccf05e-80b0-41ec-a8d4-f082ddc0f8bf`, assesses the S60 examples-run-path
remediation document against current authority and source. Its writable surface
is design/stdlib only; QA owns tests/plan. Both passes must preserve unresolved
obligations and supply cross-owner extraction/reference handoffs.

The stdlib design pass completed: the S60 examples-run-path record is retired
(3,639 words removed, no extraction needed). Its raw-primitive re-export policy
was superseded by the existing S86 curated-surface authority; current example
prelude exports and the subprocess regression harness carry the live facts.
Sprint integrated supplied reference repairs, removed the empty design
collection declaration, and aligned one stale prelude-export sentence with its
owning current policy. Source/config edits are comments only. Interim checker:
468 → 453 findings, 15 identities removed and none introduced.

QA completed the S113/S114 disposition and retired both plans. Current
assurance rules and unlanded annotation-diagnostic/persistence observations
were extracted into the existing QA plan; permanent tests and open filings
remain. The R8 build-variant question is explicitly retained in filing0857.
The disproved exemplar leak attribution remains recorded as such; filing0811
is not closed. No historical RED or source-read observation is presented as
a freshly executed result.

Sprint integrated the role's source-comment, design, filing and exemplar
reference map. The session-persistence spec edit changes only its historical
ruling citation, not normative behavior. Both provider dispatches closed
successfully. Across the seven measured carriers (the three retired documents
and all four QA extraction/reference destinations), 34,530 → 13,126 words:
21,404 removed, 62%. Other citation repairs add no replacement historical
document. Checker 468 → 429: 39 identities removed, zero introduced. Whitespace
and role wiring pass; all Rust and Cranelisp source deltas are comments.
No runtime tests were needed or run. NOTES hash is unchanged. The completed
batch after checkpoint 7b1220c7 is uncommitted; .agents remains excluded.
No phase transition.


### Risk records and user-documentation cleanup (2026-09-22)

User authorized continuation within Phase 5; baseline 429 checker findings.
Two disjoint document passes preserve the preceding uncommitted batch:

| Role | Provider / model / effort | Session | Scope |
|---|---|---|---|
| qa | Claude / Fable / high | `e5f773c3-0451-40d6-9d29-af34014ca5ea` | S113 risk assessment and accumulated risk register; existing QA extraction destinations |
| docs | Claude / Opus / high | `5afc0626-b018-485f-aa0c-3990c9b1c79a` | Completed S117 documentation plan and CLI-reference currentness |

Runtime behavior and normative language are unchanged by scope. The future
--test mode remains deferred under ACT-0988; current documentation must not
advertise it as delivered. NOTES and .agents remain protected.

A third disjoint pass reserves src/CLAUDE.md only to dev (binary),
Claude / Opus / high, session `b48ece35-aea0-4b3f-8283-aeebbd3695f8`. It repairs
current contributor guidance and stale references against source/design; no
source-code changes are authorized.

Docs completed the initial pass: retired the completed S117 plan after checking
canonical guide homes; repaired CLI references and source-confirmed claims.
Same-sprint spec follow-ups remain: CLI main-result table conflicts with the
IO-main requirement; target-last wording conflicts with any-position flags;
source accepts an undocumented --output alias. These are not silently ruled by
the guide repair. The linked discovery wording remains held under ACT-0988.

A bounded docs follow-up (Claude / Opus / high), session
`82842de8-740c-49e6-a569-c50ac01e7cb3`, repairs the accessor guide under the
already-settled product-only rule, assesses the 0868 discovery caveat's reader
home, and corrects one getting-started citation. No new semantics authorized.

Dev completed the binary-guidance pass: repaired stale helper/source and split
REPL-spec references, replaced the copied dependency inventory with canonical
authority pointers, and retained operational constraints. Root repaired one
checker misreading of a generic section-reference phrase. Remaining owner work:
arch verify/dispose quote-head filing0789; dev reconcile stale forced-enrollment
rustdoc; JIT naming examples and owner-scoped-key statement remain explicitly
unverified. These are source-read leads, not closed implementation issues.

Spec (Claude / Opus / high), session
`20c0acd5-b8ab-4ecd-88ed-73489356e6d0`, assesses the CLI contradictions and
startup-recovery citation read-only, to prepare the next exact user decision.
No normative changes are authorized by this assessment.

QA retired the S113 risk assessment and rewrote risks.md around four current
risk classes; dated rankings/counts and sprint gates remain in Git. Current
control homes and unmeasured residuals are retained. Root integrated the
filing0694 counting-convention citation and corrected the historical Git
reference syntax. No defect closures or new safety grades. Remaining QA work:
exposure re-grade when the strategy's measurement is next relied on; reconcile
the tests-memory per-crossing assert claim with the located dealloc-time check;
check DEF-6 guard comment currency at its next execution; preserve0857's
build-variant question. S117 plan section6 is the next historical candidate.

The docs follow-up corrected product-only accessor guidance and type-directed
bare accessor selection under existing S121 authority, and repaired the
getting-started link. Filing0868 remains open with its permanent cache guard;
no unevidenced workaround was added to the guide. A test-discovery reader guide
needs sequencing with ACT-0988's REPL policy. The accessor/impl test conflict
is already routed in ACT-0983, not a new language decision. Constructors-guide
candidate-selection prose needs the next docs pass.

Spec completed its read-only assessment. Next approval: CLI section0.2 must
require main of type (Fn [] (IO _)), replacing its obsolete pure-result rows
while retaining inner-Int exit-code handling and zero for other inner types.
The governing language sections10.6/12.6 and S80 enforcement ruling already
require IO-main; no runtime change is proposed. Subsequent questions, one at a
time: target position (target-last contradicts section0.5.3/0.6); whether to
formalize the delivered --output alias and synchronize the synopsis; restoring
the startup-recovery obligation lost in the S121 section18 rewrite; reconciling
section10.6.1's implementation-defined non-Int exit with section12.6's zero.
None is silently settled. Startup recovery's old test trace remains an evidence
handoff after its normative home is decided.

Final integrated verification for this batch: 429 → 401 document findings,
28 identities removed and none introduced. Across ten measured carriers
(including all QA extraction destinations and edited user/source guidance),
31,622 → 21,330 words, 10,292 removed. Whitespace and role wiring pass. All five
Claude dispatches closed successfully. Source inspection and existing test
assertions informed prose; no runtime tests were run or newly claimed.
Changes remain uncommitted; NOTES and .agents are untouched. Phase 5 continues.


### CLI IO-main correction (2026-09-22)

The user approved correcting CLI section0.2 to require main of type
(Fn [] (IO _)), rejecting pure results while retaining the existing inner-Int
exit-code rule and zero for other inner types. This changes prose only; the
compiler and existing rejection assertions already enforce the IO-main rule.
Spec dispatched on Claude / Opus / high, session
`8d25fb47-adea-4084-8d63-8d5263ad1c83`, limited to that approved delta.
Other CLI/startup questions and ACT-0988 remain separate.

Spec completed the approved CLI section0.2 correction. The old pure-result
rows are replaced by IO-main handling; compilation-error behavior and inner
result exit codes are unchanged. Coverage was invalidated for QA reassessment,
preserving the former citation. Existing Int/Bool rejection and IO execution
tests are candidate evidence; no new runtime run or coverage grade is claimed.
Whitespace passes; document findings remain 401 with zero introduced identities.
No commit or phase transition.


### CLI option ordering (2026-09-22)

The user approved retaining options before or after the target, with an
option's value immediately following that option, and showing options first
in documentation examples. Explicit equivalence examples may show both orders.
The mentioned -- separator/program-argument forwarding remains a separate
unapproved feature; it is not introduced here.

Spec on Claude / Opus / high, session
`5c51bf98-9d28-4ea3-875b-69dc9f604c94`, applies the approved target-order
correction and presentation changes. No runtime change or phase transition.

Spec completed: section0.5 now permits the target before, after or between
options and keeps option values adjacent. Ordinary spec/CLI-guide examples
show options first; explicit equivalence examples retain both orders. The
guide synopsis is identified as presentation rather than an exact USAGE quote.
QA needs to assess the newly explicit between-options and value-adjacency
claims; no runtime test result is claimed. Whitespace passes; checker findings
remain 401 with zero introduced identities. No source change, commit or
phase transition.


### CLI output alias (2026-09-22)

User approved documenting --output as the supported long form of -o, with
QA to verify equivalence. Spec on Claude / Opus / high, session
`fc30f4d6-c77c-438e-ba91-de8bffd6962d`, records this within CLI section0 and
supplies guide propagation. No compiler change. Other pending CLI/startup
questions remain separate.

Spec completed the alias correction: --output takes the same path argument
and inherits all -o requirements; the synopsis and user CLI reference show
both spellings. The parser uses one match arm and one output_override field
for both; this is source confirmation, not executed equivalence evidence.
The new claim remains S122 pending QA evidence allocation, batched with the
other CLI corrections. No source or test change.

Spec found another missing normative statement: the implementation rejects
-o/--output without --link, but the CLI spec does not explicitly require that
rejection. No new failure requirement was added under the alias approval; the
link-only/error-status question remains for the user. The short-form-only
USAGE/error strings are not changed by this documentation work.

Verification: whitespace passes; document findings remain 401 with zero
introduced identities. No runtime tests, commit or phase transition.


### Output options apply to artifact-producing modes (2026-09-22)

User approved the link-only restriction for current output flags, qualifying
that they are relevant to link and release. Source/spec confirm no --release
flag is delivered today. Spec (Claude / Opus / high), session
`1798a572-8f73-436d-9c5d-0ef31635bb79`, records current -o/--output rejection
without --link (error and usage on stderr, exit1). ROADMAP's release sequence
retains the approved future applicability to release artifacts. No release-mode
implementation or test-harness change is authorized by this correction.

Spec completed the link-only output-path requirement, tagged S122 pending
QA evidence. The alias inherits the same restriction. The CLI guide already
matches. Whitespace passes; document findings stay at 401, zero introduced.
No runtime change or test execution; no commit or phase transition.


### Startup recovery and constructor guidance (2026-09-22)

User approved restoring startup recovery: saved-source compile failure reports
the error and reaches a prompt; the affected module blocks ordinary expressions
while accepting definition repairs; successful repair clears that state.
Spec on Claude / Opus / high, session
`58e9aae8-2610-4211-8afa-aa9b4478b099`, restores the canonical persistence
requirement and supplies citation/evidence handoffs. Runtime behavior is not
changed by this approval. An independent docs pass corrects the constructor
guide's overbroad ambiguity claim under existing S121 authority.

Docs (Claude / Opus / high), session
`0a9984a8-41da-49d9-9d92-a1d8a3e13235`, owns the constructor-guide repair.
Sprint source-read found that the old startup18.8 trace now heads
rejected_change_does_not_write_an_incoherent_backing_file: its fixture rejects
an incompatible change before saving, then restarts coherent source. It is
not evidence for broken-source startup recovery; QA must assess separately
before any trace is repointed or coverage credited.

Both role dispatches completed successfully. Persistence section15.2.3 now
contains the approved startup recovery requirement, explicitly marked uncovered.
Sprint integrated the spec handoff's startup-only source/design citations;
current redefinition citations and claims beyond the ruling were left intact.
The constructor guide now describes selection at each use, including selection
of bare patterns by a known scrutinee type, under existing S121 authority.

Evidence handoffs remain open for QA/test: broken-source startup needs a
pre-seeded backing-file recovery journey; the old coherent-restart test must
be traced to its actual redefinition/persistence assertions. Constructor value
selection by context lacks identified solution evidence, and the old test
comment claiming value constructors always poison needs correction. No new
coverage is credited from source inspection or committed fixtures alone.

Spec also identified residual startup claims requiring authority reconciliation:
symbol naming in load reports, preservation of failed forms during regeneration,
cache poisoning, reset behavior and the watcher restart-clears-state wording.
These are not restored by implication. Check existing authored-source preservation
requirements before treating failed-form retention as a missing obligation.
The implementation's all-module expression gate is broader than the affected-module
wording; the ruling does not settle that scope.

Verification: document findings 401 → 397 (four removed, zero introduced);
whitespace and role wiring pass. Rust changes remain comment-only. NOTES hash
is unchanged. No runtime tests, commit or phase transition. Next queued normative
question is the non-integer IO exit result: IO section10.6.1 still permits
implementation-defined behavior whereas runtime section12.6 and CLI section0.2
require zero. Await the user's exact ruling before changing that clause.


### Non-integer IO exit status (2026-09-22)

User approved requiring zero for non-integer IO results consistently across
the IO, runtime and CLI specs. Spec (Claude / Opus / high), session
`625769d4-6492-40b8-aca1-4218e3b48a89`, owns the section10.6.1 correction
and coverage invalidation. The same pass assesses existing authority for
failed-form preservation after broken-source startup; additional normative
changes are not authorized. No runtime change or phase transition.

Spec completed successfully: non-Int IO normal completion now MUST exit zero;
IO Int behavior is unchanged. The former coverage set is retained in the
uncovered annotation pending QA reassessment, including the parent summary.
Runtime and CLI prose agree. No runtime tests were run.

The startup assessment found no current obligation specifically preserving
failed persisted forms across later regeneration. Section15.4 item7 is rationale,
and round-trip of live session state does not include forms that never loaded.
The next user question is retention of failed-form source until successful
replacement. The role's proposed original-position requirement is not included
in that question: the current implementation appends retained failed forms, so
ordering needs a separate assessment rather than being folded into retention.


### Failed saved-source preservation (2026-09-22)

User approved explicitly preserving the verbatim source of saved definitions
that fail at startup across later regeneration, until successfully replaced.
The explanatory example was a broken definition disappearing when another
successful definition triggers saving. Spec (Claude / Opus / high), session
`bcd46a3b-3642-4af2-b2b3-689144e6571b`, owns the persistence requirement
and its citation/evidence handoff. Ordering, diagnostic naming and cache policy
are not part of this ruling.

Both spec passes completed, including the consequential conformance pass
(Claude / Opus / high, session `0d8b7dd6-370f-4dd9-8b0f-e265d35d5038`).
Persistence section15.2.3 now explicitly retains failed definitions verbatim;
section15.1 and redefinition section18.8 account for that exception to successful
source. Changed coverage is marked uncovered with former covering sets retained.
Sprint integrated the precise no-silent-drop and repair-direction source
comment remaps; claims about diagnostic naming, ordering, cache and reset were
not assigned coverage by association.

QA/test handoff: assess a broken-file startup followed by an unrelated successful
definition and readback of retained source, plus same-name successful replacement.
Existing helper tests do not establish that complete persistence journey.
Also assess reset clearing failed_forms followed by regeneration against the
approved retention obligation; the absence of a reset-specific requirement
does not by itself establish compatibility with the new general obligation.
Docs should check the live-development guide's successful-definition wording
for any implication about failed backing-file source. These remain open.

Whitespace and role wiring pass; Rust changes are comment-only. NOTES remains
unchanged. No runtime tests, commit or phase transition.
Final document check: 397 → 397 findings; 0 removed, zero introduced.


### Learning-plan and QA consolidation batch (2026-09-22)

Continuing authorized Phase5 document cleanup, with disjoint owners:
- training, Claude / Opus / high, session
  `6d8ac738-ce80-4d98-b451-70157b5f2506`: examples plan and local guidance.
- qa, Claude / Fable / high, session
  `3f8cca5a-2b17-450d-92fb-f267a4fe464a`: remaining S117 plan consolidation
  and a cohesive allocation for recent persistence/CLI requirement evidence.
- docs, Claude / Opus / high, session
  `f38a5491-f9bb-417a-a4de-db5fd746b6a9`: live-development guide alignment
  with approved startup recovery and failed-source preservation.

The examples plan alone contains 16,099 words before this batch. Success means
useful teaching design and unresolved findings remain discoverable while dated
delivery narration and duplicated facts are retired, not merely relocated.
No runtime code change, test execution, commit or phase transition dispatched.

Training and docs completed. Examples plan/guidance: 16,469 → 3,476 words
(13,000 removed; 79%). The learning gaps, library candidates and prerequisite
checks remain current in the plan; exit expectations remain in tests/examples.rs.
Docs aligned saved-source recovery and retention, and sprint remapped four
obsolete impl-guide anchors. QA's first pass completed; its reset disposition
returned for finding-scoped reassessment against the general retention rule,
with report formatting kept separate from required load-error reporting.
QA follow-up (Claude / Fable / high), session
`c7d19784-f9c5-4e2a-a06d-f8f450a19e21`, owns that correction and the compact
remaining CLI option evidence handoff.

Arch (Claude / Fable / high), session
`267e1c7f-7beb-4dbc-8f23-8f74dd6d3675`, retired answered filing0821 and
supplied the exact still-unapplied root amendment from the approved S115
examples-local library ruling. Sprint applied that clause verbatim in substance
(link instead of a bare path), verified the filing's retirement condition,
and retired0823. Tests retain their existing helper-placement rule.
No new scope boundary was decided.

QA correction completed: /reset's public dispatch can clear failed-source
retention without replacement; classify as suspected failure pending a narrow
public reproduction, not as exempt because reset lacks its own specification.
Cell C joins startup/repair cells A/B. Only an observed RED requiring a policy
exception returns to the user. Required error reporting is distinguished from
implementation-specific report spelling. Current unit traces are acknowledged
without claiming end-to-end coverage. CLI ordering, output alias and link-only
rejection now have a compact allocation alongside the IO exit cells.

S117 historical plan reduced from 1,534 to 285 words, retaining only the four
failed-turn assertion rows cited by ACT-0958. Unlocated module matrices remain
a qualified lead in PLAN; no completion is inferred. New persistence and CLI
evidence allocations explain the growth in the current evidence delta. Sprint
retired the obsolete0489 banner over the coherent-restart test and remapped
the bare-expression persistence trace; test behavior is unchanged. Other
unit-risk trace corrections remain with dev.

All four initial role passes and QA correction are complete. Source/test edits
remain comments only; no runtime tests or new coverage claims. NOTES hash
is unchanged; whitespace and role wiring pass. No commit or phase transition.
Final integrated check: 397 → 382 findings, 15 removed and zero introduced.
Final examples plan/guidance total: 3,472 words (16,469 before; 79% reduction).


### Persistence evidence execution (2026-09-22)

User continued after the allocated evidence was presented. Test (Claude / Opus /
high), session `8d6ae0f0-8f2b-4cf2-83f2-3ec3e1f568cc`, owns the focused
public persistence cells A/B/C from the current QA delta and the only foreground
nextest run. No concurrent source writer or test runner. Existing dirty work
is preserved. Compiler corrections, reset exceptions, CLI tests and phase
advancement are not part of this dispatch. A reproduced defect remains a
minimal failing unignored test for QA attribution.

Test completed: the three allocated persistence cells ran 2 GREEN / 1 RED;
the focused two-binary regression run completed 42/43 PASS, with only the
new reset-retention cell failing. Logs: local s122-persistence-run1/run2.
Both normal recovery and unrelated-save retention/same-name replacement pass.
Reset then unrelated definition regenerates a file holding good and other
but no broken definition; the matched no-reset control retains it once.
The failing cell is retained unignored. Compiler source is unchanged.

QA (Claude / Fable / high), session
`251acdc9-d489-418f-8af2-8f722e3d4574`, assesses the executed evidence and
reset defect intake. No whole-retention coverage restoration while the
reset counterexample remains. The fmt discrepancy reported by test is
pre-existing outside this delta; no concurrent source writer was dispatched.

QA intake completed: A/B are adequate originally-green observations; C is a
confirmed Binary/int reset-induced authored-source loss with a matched control.
QA says policy input is needed only to change current authority (abandonment).
Sprint therefore proceeds under the user's existing retention ruling; no
exception is proposed, and no repeat approval is needed.
Dev (Claude / Opus / high), session
`23fcd2ed-44c8-435a-a7a1-e7db50c8a4cd`, owns the narrow Reset correction and
its coupled module guard, using the independent public RED unchanged. No new
reset feature or cross-crate API is authorized. QA's defect-class vocabulary
gap remains for disposition during final evidence assessment.

Dev completed the reset-retention correction. The failed_forms clear is removed;
error_modules retains modules carrying failed source. The existing watcher
clearing and response remain outside this correction. The replacement unit
failed before the fix then passed; the unchanged public C flips RED→GREEN.
Foreground checks: persistence43/43, related integration285/285, module107/107.
No full-suite claim; unrelated formatting discrepancies remain outside the delta.

Review (Claude / Fable / high), session
`0f95e6b7-7b08-48fa-8de5-9f537ba70c60`, independently inspects the Binary/int
change. QA (Claude / Fable / high), session
`7444c0dd-1407-488e-8e92-9fb9b78a63a0`, owns final evidence/annotation
reconciliation and defect taxonomy, with review judgment composed at integration.
Dev's watcher-only reset and lost-watch observations remain unverified leads,
not proved defects or a full-reset feature commitment.

Review completed with no required implementation findings; its two required
record repairs are covered by QA's closure and the test handoff. QA accepts
the narrow correction, restored appropriate coverage with evidence limits,
and ratified release-path-bypass for the defect taxonomy. No new reset policy
was decided and no repeated retention approval was sought.
Test (Claude / Opus / high), session
`25a64982-ecdc-4e5b-9ad2-84855cce6a00`, completes the single dispatch-witness
assertion and exact defect trace. Only that cell is rerun; the broader green
evidence stands. At checkpoint commit, add the actual fixing SHA to its
optional fixed= field; no commit has been requested yet.

Final test handoff completed: reset dispatch witness added, its focused cell
passes1/1. Defect trace and past-tense framing are now integrated; no other
assertions changed. Review's required record findings are closed. Watcher-only
reset leads and the uncovered interactive failing-definition persistence cell
remain in the current QA delta, with no invented policy or claimed coverage.
Final document check: 382 findings, no introduced identities; whitespace
and role wiring pass. NOTES unchanged. No commit or phase transition.


### Checkpoint and CLI evidence continuation (2026-09-22)

User requested checkpoint commit and continuation. Checkpoint `9d4f18f5`
contains document consolidation, approved CLI/persistence requirements, and
the independently reviewed reset-retention correction with its evidence.
85 files changed; NOTES and the independently dirty .agents Gitlink excluded.
The regression trace now records that actual fixing SHA. A small follow-up
commit carries this provenance, since a commit cannot contain its own hash.

Continue in Phase5 with the existing QA CLI allocation: first src parser
unit evidence, then the public CLI/IO exit and output-path cells. One source
writer and test runner at a time; no new CLI semantics or phase advancement.

Dev (Claude / Opus / high), session
`3400b7df-e8b7-494a-9db6-3716d9550059`, owns parser module evidence in
src/main.rs under the settled CLI requirements. This is evidence-only; a
failed observation is returned rather than silently changing parser behavior.

Parser evidence completed: 14/14 binary units pass, including three new
ordering/adjacency/alias cells. Dev reported two temporary parser fault plants
that made all three new units fail as intended, then restored the parser and
reran green. Final source diff is test-only derives/helper/cases, no production
parser change. Independent review will inspect the complete CLI evidence delta.
Test (Claude / Opus / high), session
`2dcab1c4-6161-4060-8f8d-60980244db46`, owns the subsequent public CLI/IO
exit/output-path cells and the sole test run; no concurrent source writer.

Public CLI evidence completed:12/12 focused cells and92/92 across both touched
binaries pass. Non-Int String/Bool IO results exit0 in run and linked execution;
the output override creates the requested artifact (default absent), and output
without link fails with status1/usage and no artifact. The legacy either/or
pure-zero cell is now strict. No product behavior changed.
Review (Claude / Fable / high), session
`3aa598ef-c061-48fd-bcb1-4b51dbe6e4b0`, owns the independent CLI evidence
inspection; QA (Claude / Fable / high), session
`713fbc31-853e-4ac2-8d20-10a1249887e2`, owns coverage reconciliation and
current evidence records. Originally-green public evidence is not described
as red-to-green defect evidence.

CLI evidence wave complete: independent review has no blocking/required finding;
QA deems allocated conditions adequate and restored their coverage annotations.
Production behavior unchanged.14/14 binary units and92/92 public tests pass;
temporary parser fault plants were reverted before final green. No full-suite
claim. Final document check remains382 with zero introduced identities.

Remaining observations retained for the next targeted intake: pre-existing
mis-cited spec trace in tests/spec_10_io.rs near line144; missing-main/file and
warnings-to-stderr CLI coverage, unknown-flag and conflicting-mode coverage;
Bool run-half duplicates an existing runtime-spec cell (accepted redundancy).
Review also identified a pre-existing harness lead: link_then_run returns the
compiler's success status if the derived executable path is absent, potentially
masking a missing-artifact failure in assert_exit(0) callers. The new direct
artifact cells discriminate existence; assess the helper separately before
claiming a defect or changing its semantics. These observations do not reopen
the accepted CLI conditions and are not a phase transition.

Checkpoint remains9d4f18f5 plus fixing-SHA trace commita7ec1f7d. The continued
CLI evidence/annotations are uncommitted. NOTES unchanged; .agents excluded.


### Checkpoint2fee9bb2 and rendering/typecheck cleanup (2026-09-22)

User requested checkpoint and continuation. Committed CLI evidence and
annotations as2fee9bb2 (8files); NOTES and .agents excluded. ContinuePhase5:
- qa, Claude/Fable/high, session `ac4588ca-84aa-4520-beef-70bc5d8a3a00`: bounded
  link_then_run missing-artifact risk and minimal evidence allocation.
- arch, Claude/Fable/high, session `3183cd27-736d-47ef-837a-2bb5fdb6b054`:
  historical type-rendering consolidation and display protocol/current homes.
- design, Claude/Opus/high, session `94919811-1a82-4ac1-97f9-b8d98d6b50d3`:
  typecheck checked-body-publication design/current master, disjoint from arch.
No source writer or runtime test run dispatched yet; docs ownership disjoint.
Retain unresolved findings, retire ordinary history, measure destination-inclusive
standing burden. No API/semantic change or phase transition authorized.

Design/arch passes completed. Checked-body design+master:8,730→5,976 words
(2,754 removed); rendering record+display protocol+interface destination:
9,918→5,521 (4,397 removed). Combined role-owned net reduction7,151 words,
before small integration remaps. The S87 record is retired; the rendering
byte table now lives in interfaces.md. Display protocol remains clearly
unimplemented, with its settled rulings and implementation obligation retained.
Body-ledger identity prose now matches source; default-method re-settlement
remains an open design concern, not a proved observable defect.

Sprint integrated three types-test anchors, the crate entry citation, four
body-design test anchors and the S121 QA-plan citation; removed the obsolete
historical collection and master row; updated0050's stale no-design defer
reason without scheduling implementation. Arch had staged the deletion despite
its no-Git brief; sprint unstaged that path, preserving the intended retirement.
The display spec's aspirational forcing/choice wording remains an unresolved
spec handoff; no unapproved normative edit was made.

QA allocated H1/H2 maintenance checks for link_then_run, including the concrete
nested-file artifact-path mismatch; compiler behavior is not implicated.
Test (Claude/Opus/high), session `03773f8f-4dd4-4250-a3c2-6c82ace7efa9`,
will reproduce both before correcting the harness. Source comments were
remapped before this sole source/test writer began. No phase transition.

Continuation recovered 2026-09-24: test completed both harness reproductions
RED before correction, then 25/25 link and 98/98 runtime-spec cells GREEN.
No compiler behavior changed. The final rendering/body document check is
382→363 findings, 19 removed and zero introduced identities; NOTES unchanged.
The interrupted QA/review dispatches (ec194691 / ead176df) left no reports.
Fresh Claude/Fable/high runs complete their outstanding scopes:
- QA `643b659e-5689-43e9-8826-5a3501951d65`: helper contract and evidence adequacy.
- Review `e11f651e-4fa1-46e6-b655-c7672f10ad35`: independent harness inspection.
- Arch `9c8c8b63-67c6-4abe-aa11-477b4ae5e998`: next cohesive documentation batch,
  backend-keyed-consumer and safety-invariants; source read-only, preserve open
  obligations and report canonical-home handoffs.
No new checkpoint or phase transition.

Harness independent review completed with no blocking or required finding.
Advisories retained: directory-project targets are not modelled by link_then_run
(they fail loudly; no current caller); H2 matches Display text rather than the
new error variant; the tuple's unused bool predates this correction. These do
not invalidate H1/H2 or justify broadening this instrument repair. QA's helper
contract follow-on is in progress.

QA closure completed: allocated instrument evidence adequate, helper reference
and current evidence delta updated. No coverage-band changes or full-suite
claim. QA checked documents before/after:363 findings, unchanged.
Spec (Claude/Opus/high), session `a7cbba46-6721-4538-b101-4f147926d77c`,
verifies dated authority for the stale aspirational display paragraph before
reconciliation; retain current generic ADT norm and unimplemented MAY status.

Display spec reconciled only its aspirational paragraph against the explicit
S106 user ruling (archive sprint-106, 2026-07-10; committed design52389dfa):
no forcing, compiler-internal recognition, no annotation surface. MAY status
and normative generic ADT display remain. Sprint removed the now-resolved
design handoff and refreshed0050's obsolete role/source/design-status prose;
implementation remains unscheduled, promotion remains subject to spec authority.

Backend identity/safety cleanup complete:17,277→6,779 words (10,498 removed),
no content shifted to another file; all21 safety-register rows retained. Current
carrier shapes and landed mechanisms verified against source; open obligations
remain in their rows. R12's grade is explicitly not re-established.
Arch's exact remap applied to two incoming citations that incorrectly bound
§10 to backend-keyed-consumer; the actual home is dotted-ctor-canonical-keys.
The Principle24 edit repairs that citation only under the approved document
integrity work; no principle statement or membership changed (Phase7 revisions
remain out of scope).
Remaining owner work:R12
grade and R18(8) severity (integration design); R11 I-EMIT scheduling; Principle25
register-range prose at close. Optional source-comment remaps and all safety
residuals remain recorded in the standing documents and arch's handoff. Next
cohesive cleanup candidate:typed-resolution-carrier and its incoming citations.

Final integrated document check:382→345 findings, 37 removed and zero
introduced identities. Diff whitespace clean; NOTES hash unchanged. Harness
25/25 +98/98 passes and independent review/QA remain the completed evidence.
Work since checkpoint2fee9bb2 is uncommitted; .agents remains excluded.

### Checkpoint777ed404 and carrier/backend continuation (2026-09-24)

User requested checkpoint and continuation. Committed25 files as777ed404;
NOTES and .agents excluded. Baseline345 document findings. Phase5 continues:
- arch, Claude/Fable/high, session `3e58160d-3f69-425d-8e6a-02c79a6e2521`: typed
  carrier migration retirement/consolidation, existing canonical homes and links.
- design, Claude/Opus/high, session `745810c9-5ce9-479e-9639-c79c3ecd034f`: S115
  backend plan consolidation and source-verified0637 disposition.
Disjoint document ownership; source read-only; no test run or phase transition.

Backend design completed:6,190→3,934 words destination-inclusive (2,256
removed). S115 retains unique measured discriminators and R4 census, with
current contracts linked.0637 resolved/deleted against cache-loader arm and
existing positive/negative corruption evidence; sprint inventory reconciled.
QA Claude/Fable/high session `0f1283a0-a737-4395-a8b5-b7cc1ba9914a` owns bounded
triage of two inspection-only leads (discarded cache lifecycle errors; sanitized
inner names across instances) and QA0637 tracking reconciliation. No defect
claimed from inspection and no new test allocated yet.

Arch retired the completed S114 carrier migration record, folding only unique
current obligations into interfaces and backend-keyed-consumer. Destination-
inclusive reduction1,658 words (including the new192-word ACT-0989 retaining
the orphaned helper-disposition obligation). All source/API behavior unchanged.
Sprint applied the exact typecheck-document and collection-pattern remaps.
Arch also repaired incoming links in its broader owned surface and types
guidance. Source-comment/diagnostic remaps remain its explicit handoff.

QA triage completed. C-A is an existing documented cache-restore residual:
only InstanceKeyMismatch propagates from validate_lifecycle; no later check
was found. Allocated duplicate-slot corruption unit + existing valid control;
CacheStale surface choice routes to arch before implementation/API approval.
C-B predicts wrong-reject for distinct legal types A-B/A_B through the generated
inner-name sanitizer; allocated unit inequality and all-modes repro/control.
Neither lead has executed failing evidence. QA's scratch probe was refused by
its sandbox; no application behavior was observed and no production correction
is authorized by that attempt. Both conditions remain active in the evidence
delta for the next backend evidence batch; no defect closed or deferred.
QA0637 tracking reconciled; dated measurement verdicts preserved with correction.
No runtime tests rerun for this documentation-only batch.

Final integrated check after QA:345→339 findings, six removed and zero
introduced identities. Diff whitespace clean; NOTES unchanged. All continuation
changes remain uncommitted after777ed404; .agents excluded.

### Checkpoint6c1fe761 and backend evidence (2026-09-24)

User requested commit and continuation. Committed23 files as6c1fe761; NOTES
and .agents excluded. Phase5, document baseline339.
- arch Claude/Fable/high `77691048-8fc2-4f0f-b5a3-4393288276b7`: bounded C-A
  error-mapping decision, source read-only; exact API proposal if necessary.
- test Claude/Opus/high `fedddb6b-8024-4048-9110-0e6e07321f0b`: C-B all-modes
  e2e repro/control, sole source writer and foreground test runner.
No public API change authorized by this dispatch. Observe before correction.

C-B independently reproduced: A-B/A_B fails duplicate-definition in all six
fresh/cached REPL/run/link permutations; A-B/A-C control returns7 in all six.
No mode-divergence claim (REPL rejects the turn with process exit0). New
unignored guard tests/inner_fn_sanitized_name_collision.rs retained.
Dev Claude/Opus/high `4443c0d0-7e6f-4c6b-bc22-47e064f92436` now owns backend
resolution unit RED→injective internal-name correction→focused GREEN. Test
dispatch complete before source ownership transferred. C-A remains read-only.

C-A arch proposal awaits user API gate: replace CacheStale::InstanceKeyMismatch
{path,symbol,expected} with LifecycleInvalid {path:PathBuf,error:LifecycleError};
reason lifecycle_invalid. Map every refusal after existing R6 per-field loop
to preserve specific error precedence. No cache format/schema/ABI change;
existing consumers handle Err generically. Backend baseline4 removed lines,
3 added; types unchanged. User approval requested while C-B continues.
No cache source or baseline modified before approval. Source-based consequence
(wrong-body dispatch) is a risk prediction, not an executed C-A observation.

C-B correction complete: discriminator escapes every non-alphanumeric UTF-8
byte (including underscore) with fixed-width hex, retaining a distinct terminator.
Unit RED before fix;6/6 focused units GREEN, both e2e cells GREEN across six
modes each;594/594 backend tests and133/133 related integration tests GREEN.
No API/schema change. Sprint applied dev's exact stale-rustdoc handoff in
fn_compiler.rs, comment-only.
Review Claude/Fable/high `3e7c0cbb-1a4b-4b01-b1d6-4d1026104690` owns independent
inspection; QA Claude/Fable/high `d3203bee-f7b0-4ed5-8a17-0ee0c6889b4e` owns
evidence closure. C-A approval remains pending; no cache code changed.

QA accepted C-B evidence and confirmed wrong-reject attribution from unit/e2e
RED and discriminating control. Sprint reconciled the test's Open comment and
the S115 asserted-note to the executed correction, linking QA's exact evidence
and retaining the separate curry-target limitation. No broad grade/coverage
promotion. The fixing SHA is still pending a future user-requested checkpoint.

C-B independent review passed; required rustdoc repair already applied. Reviewer
noted final rustfmt reflow postdated evidence, so sprint ran the six affected
resolution unit tests on the final file:6/6 GREEN (.local/s122-cb-final-unit.log).
No full-suite rerun warranted by formatting-only change; prior594backend and
133related integration results remain qualified evidence. Review's BUILD_ID
advisory retained: it includes HEAD and changes at commit, not each edit;
local object symbols stay self-consistent and no cache schema bump is required.
Final document check339→339, zero introduced identities; whitespace clean and
NOTES hash unchanged. C-B fix/regression uncommitted after6c1fe761.
C-A has no executed reproduction or cache correction; the user disposition
below supersedes the API-approval request.

### C-A disposition — user declines corruption hardening (2026-09-24)

User treats caches as compiler-written and declines added complexity to catch
self-poisoned/corrupt caches at this stage. Defer C-A as accepted residual risk;
withdraw the LifecycleInvalid proposal and tampered-cache test allocation from
active work. No pending API approval, source change or new assurance gate.
Existing checks unchanged. No evidence currently shows the compiler writing
the invalid state; predicted downstream damage was never reproduced. QA's
active allocation and coverage status reconciled mechanically to this ruling.
C-B is independent: ordinary valid source reproduced its failure and the
verified naming correction remains complete and uncommitted.

### Continued document cleanup after C-A deferral (2026-09-24)

User requested continuation. C-A deferred; C-B already verified, uncommitted.
- design Claude/Opus/high `b79dda1d-c8f3-4bef-935e-28d03f4de499`: typecheck
  carrier producer plan and its canonical homes, source read-only.
- arch Claude/Fable/high `10506821-601a-4a1f-81d2-7e561f2987f3`: tracing
  contract cleanup, source read-only.
Sprint applied the prior arch pass's exact comment-only carrier reference
remaps in eight source/test files. Runtime diagnostic strings remain an owning
dev handoff; no executable token changed. No test rerun needed for citations.

Typecheck producer plan retired: destination-inclusive13,345→6,156 words
(7,189 removed). Current producer contract lives in ast-annotation §2.1 and
typecheck §9.1/§9.7; existing residuals retain their established homes.
ACT-0989 design disposition: retain the test-only predicate family under
cfg(test), advisory dev follow-on; no source implementation in this pass.
Sprint removed the retired collection member and applied exact comment-only
remaps in checker/infer/transfer tests/mono-collector tests/support.
Runtime diagnostic citations remain a dev handoff, not changed here.

Tracing contract retained and condensed6,992→2,383 words (4,609 removed),
source-verified adopted/landed status and current implementation; external
section numbers preserved. ACT-0984 remains the explicit QA obligation for
the obsolete link-rejection test. Sprint corrected the intrinsics trace-test
section citation mechanically. Principle10 references and stale integration
comments remain the arch report's exact owning-role handoffs.
Final integrated document check339→333, six removed and zero introduced
identities;13 source/test citation files verified comment-only by diff.
No runtime tests repeated; C-B prior evidence remains unchanged. C-A remains
user-deferred. Work after6c1fe761 uncommitted; NOTES and .agents untouched.

### Checkpointf84a6d69 and trace evidence reconciliation (2026-09-24)

User requested commit and continuation. Committed28 files asf84a6d69, including
C-B naming fix and typecheck/tracing cleanup; NOTES/.agents excluded. Added
the actual fixing SHA to C-B's regression annotation after commit.
QA Claude/Fable/high `4bcb41b0-0d4b-4c13-ab80-8025a59396df` owns ACT-0984
read-only assessment and minimal evidence allocation. Sprint integrated prior
arch handoffs: removed stale integration comments promising link-mode trace
failure/future trace support; repaired Principle10 citations only, preserving
the principle statement and the Phase7 revision gate. Baseline333 findings.

ACT-0984 probe confirmed the obsolete cell passed solely through its filename:
main returned Trace, validate_main refused non-IO, no linker/trace-runtime error.
Test Claude/Opus/high `c7895261-f754-45e6-822a-8e6e06673059` removed77 lines.
Targeted suite8/9: one unrelated pre-existing source-grep RED; cargo check --tests
passes with only known nix future-incompatibility warning.
QA Claude/Fable/high `55c69a85-5bfd-4a32-9b68-90016d89200f` assesses that stale
source-grep cell in the same file; no tracing-runtime issue inferred.
Sprint completed Decision0040's existing exact retirement checklist: source
observer citation and Decision43/index references repointed to current homes;
record deleted with no unique content moved. Decision label40 remains in index.

QA confirmed ACT-0984 independently complete; sprint deleted its filing and
tracing's now-empty open-obligation section. Known diagnostic empty-span note
remains recorded as observer intake, not a new gate.
QA retired the redundant primitives source-grep allocation: it has observed
only a comment since S117, while every_entry_is_def_kind_primitive checks the
live table. Test Claude/Opus/high `e5f072a8-ab2f-43a5-a22d-d38c540065ff` owns
that deletion and the final8-test run. The remaining source-grep limitations
stay recorded in QA's evidence delta; no compiler defect is inferred.

Final S68 binary8/8 PASS (foreground nextest);137 stale test lines removed in
total. Earlier cargo check --tests passed with only known nix warning; no
import or compiler behavior change. Decision0048 retirement map updated from
three Shape citation blocks to two. No full-suite claim or extra review round
for this QA-directed removal of superseded instruments.

Final integrated document check333→331, no introduced identities. QA working
allocations condensed to final evidence and retained limits after completion.
Whitespace clean; NOTES unchanged. New work uncommitted afterf84a6d69.

### Checkpointb66d3615 and remaining record collections (2026-09-24)

User requested commit and continuation. Committed17 files asb66d3615; NOTES
and .agents excluded. Baseline331 findings.
- arch Claude/Fable/high `6d8c5f27-cef9-4c2c-9dfa-63f52b4226f8`: remaining
  four architecture decisions as one retirement/consolidation batch, source
  read-only with exact cross-owner remaps.
- review Claude/Fable/high `8771bdc0-8170-4a49-80a5-bae49a116ed4`: read-only
  inspection of the historical design/review collection for bulk retirement;
  preserve live cues and unresolved obligations, no fresh compiler audit.
C-A remains user-deferred; C-B fix committed in f84a6d69. No runtime work or
phase transition dispatched.

Retirement integration: review cleared all33 historical reports (90,464 words),
with14 unresolved/unverified points preserved in ACT-0990 for current QA
classification. Report retirement is not defect closure. Root applies the exact
owner remaps; the live review cues remain. Arch's four decision records are
retired after their unique rationale moved to bounded-contexts/interfaces.
- test Claude/Opus/high `d89e22c0-6013-49b1-824f-eb6c46a6625d`: test citation
  remaps and document-checker discovery/class assertions; focused nextest.
- arch Claude/Fable/high `b10a23e5-e53a-4a1d-972c-2ab97ebbfe5f`: review's
  E1/E13/E14 convention and architecture handoffs, docs only.
No cache-corruption hardening approved or implied by historical findings.

Arch follow-up stopped with provider HTTP429 usage credits exhausted, no result
or architecture changes. E1/E13/E14 remain pending, not resolved. Root restored
the historical checklist pending E1's owner decision;32 other review reports
retire with residuals preserved. The temporary historical class is narrowed to
that one original record, not an exemption for new documents.

Integrated outcome:32 historical review reports and the final4 architecture
decision records retired;14 residual review points retained in ACT-0990. The
original checklist remains pending E1. Canonical contracts and label index
retain current rationale. Net Markdown reduction approximately91,000 words.
Final checker331→290 across554 corpus documents, zero introduced identities
(.local/s122-retirement-final-check.json). The last2 reductions are the
exe-bundle memory's stale facade/heading references.
Test dispatch completed: citation_drift discovery + planted-source fault
checks2/2 PASS; overall no-baseline conformance gate remains red for known
findings (3 run,2 pass,1 fail). Affected test targets compile. Root completed
comment/citation-only remaps after test writer finished; no runtime/API delta.
Whitespace check clean; NOTES hash unchanged; .agents untouched by integration.
No repeat independent review for mechanical remaps. New cleanup is uncommitted
afterb66d3615. Further owning-role work awaits Claude quota; no model
substitution or user decision is assumed.

### Opus continuation (2026-09-24)

User authorized Opus5.5 instead of Fable. Shared package unchanged; dispatch
uses the wrapper's explicit model override. Both roles run Opus5.5/high:
- arch `2344eb18-f4f1-484d-a866-d89dccdfb794`: E1/E13/E14 dispositions.
- qa `24329d7f-4058-43f9-9ceb-eb25a71c760c`: E2–E12 current-source
  classification in ACT-0990; no implementation or broad audit.
Baseline290 findings. Root retains mechanical integration ownership.

Arch Opus continuation completed. E1: the historical extra must_use rule is
unadopted; Rust's existing Result warning supplies its stated purpose (owner
analysis, not a new runtime probe). E13: clarified existing extern ownership
scope in bounded-contexts4b invariant6; internal trampoline borrows while
extern consumes. E14: signature already has Clone; root applied exact rustdoc
bound/citation repairs. Decisions25/31 notes already retired into current homes.
All33 historical review reports/checklists can now retire; temporary retention
class removed. No public API, language or runtime change.

QA Opus classified11 points:8 discharged (E2 analyses differ and exhaustive
walks catch variant additions; E4/E5/E6 no credible current obligation under
existing producer/provenance and cache policy; E7 isolated/guarded tests; E8
existing failed-redefinition tests; E11 rewrites removed old premises; E12
obsolete suggestions). Source inspection, not fresh suite evidence.3 bounded
corrections retained; no defect reproduction/new test allocated.
E3 redundant explicit Send is folded into existing ACT-0955's coordinated
public-API baseline work with user review preserved; no source edit now.
Dev int Opus5.5/high `7c860d85-0a7e-4643-842d-cabda55560f0` completed E9:
/help marks /reset unavailable. Cargo check passes; real REPL /help and /reset
confirm matching text. Existing unrelated format_type formatting drift left.
Dev intrinsics Opus5.5/high `d4b57ce9-5a34-4e6e-a87a-e97777626097` owns
E10 rustdoc correction; behavior and tests unchanged.

Dev intrinsics completed E10 rustdoc; compile/format checks pass, no runtime
change or test rerun allocated. Same stale claim found in backend ring2 design.
Design Opus5.5/high `17ec823c-afdb-4a9e-b7ba-a7d4826d45b3` owns that
document's IO-release reconciliation and exact adjacent test citation handoff.
ACT-0990 now carries only this remaining same-fact correction; its other
points are discharged above or retained in ACT-0955.

Backend design reconciled the same IO claim through §3.5, removed the obsolete
0474 open-fix narrative while preserving §3.5.10 as a cited anchor; checker
290→289. Exact three drop-test citation remaps integrated, no predicates or
values changed. The same stale summary remained upstream at BC4b invariant7,
Decision29 index and sequence diagram. Arch Opus5.5/high
`a3c52c3c-dba6-4116-aa19-ae6e8988a9f3` owns that final three-carrier repair.

E10 complete across intrinsics rustdoc, backend §3.5, BC4b invariant7,
Decision29 index and runtime sequence; canonical field rules remain solely in
ownership-and-disposal §6/§7. Root applied the owners' exact test-citation
remaps and removed the same stale universal-shallow claim from run_io rustdoc.
Assertions/behavior unchanged. ACT-0990 deleted:13 points resolved and E3
retained in ACT-0955, not lost. Diagram rendering uses system ARM Chromium
because mmdc's bundled x86 browser cannot run on this host.

Final Opus batch integration: checker290→289 (331 before record retirement),
corpus552, no introduced finding identities. ACT-0990 removed after disposition;
E3 remains explicitly in ACT-0955. SVG regenerated successfully with local CLI
HTML and system ARM Chromium after repairing the pre-existing semicolon parse
error. Source/SVG lockstep restored. Whitespace clean; NOTES unchanged.
No full-suite rerun for documentation/comment changes. Prior scoped compile,
format, checker fault-detection and live REPL observations remain the evidence.
No new language, API, cache or runtime behavior; changes remain uncommitted.

Retained unverified observation for the next architecture sequence refresh:
exec-flow-runtime still depicts Par/rayon, runtime SymbolTable effect lookup
and omits Select/EffectPoll/Launch arms. Arch flagged these outside the current
IO-release correction, not as newly reproduced runtime defects. Backend ring2
pre-fix history and unrelated existing findings remain for its next cleanup.

### Checkpoint fc49541f and historical design/evidence batch (2026-09-24)

User requested commit and continuation. Committed75 files (excluding NOTES and
.agents) asfc49541f. Baseline289 document findings, corpus552.
- design Opus5.5/high `8cf8e3e6-843b-4774-adb4-26785a31fc78`: five
  integration design notes assessed against canonical current homes.
- qa Opus5.5/high `9d7d0e4c-7178-48a4-8f7c-2fd4370a713d`: historical measurement/attribution
  records and read-only S61 evidence-retention assessment; exact handoffs to root.
No source/API/spec changes dispatched; still Phase5.

Batch completed: all5 int notes and5 QA records retired after extraction;
FIXME0795 discharged against trait-prefix enrollment and session-transaction2.5.
S61's11 frozen evidence files retired to byte-exact Git recovery atfc49541f;
incoming links now cite that checkpoint. User's historical-retention ruling
authorizes the Git form, and the raw evidence remains recoverable.

Int contracts now live in int.md5/6.5/6.6/6.7/7 and session-transaction2.5.
The JIT-unit and Code-shape descriptions and cache-entry/error descriptions
were corrected against source. Arch Opus5.5/high
`7cece6e3-f0e4-49c6-b96a-afeeb06097d1` corrected Decision41 and the same
current-state sentence in the deferred LLVM proposal; no LLVM work authorized.
Root applied the exact backend rustdoc cardinality and other-owner remaps.

QA retained3 unclassified leads in PLAN's active allocation: unfinished P24
classification legs, ungraded U-G6 zero-cost-off claim, and the old S109
capacity-window pass/fail/pass observation. None became a new defect or test
allocation. R7 attribution limits and unmeasured reclaim limits remain explicit.
The same-turn cache owner-drop limit remains at session-transaction6.1.

Final integrated checker289→247 across539 corpus documents, zero introduced
identities (.local/s122-int-qa-final-check.json). Net Markdown reduction about
33,300 words including destination growth. Source/test changes are citation
and comment repairs only; no runtime/API/schema/spec change and no suite rerun
needed. Diff whitespace clean; NOTES unchanged; .agents excluded. New work
remains uncommitted afterfc49541f.

Next candidates: macro-resolver-impl/cache-hit-loading and int.md16 history;
remaining backend ring-era design prose. Arch's unverified wording comparison
of persistent-workers4.5's fresh eval JIT and int.md5.3's turn batch is retained
for that int follow-up; no reclaim correctness claim is inferred.

### Checkpoint bad445da and next lineage batch (2026-09-24)

User requested commit and continuation. Committed76 files asbad445da, NOTES
and .agents excluded. Baseline247 findings/corpus539.
- design(int) Opus5.5/high `57fcbf09-1d74-4181-8e91-02855dbbe7b6`: macro
  resolver/cache-loading migration notes and int16 historical backlog.
- design(backend) Opus5.5/high `8d2990da-afc1-48c8-9e7c-135c83324f9b`: ring1-codegen, ring2-rc,
  jit-setup-boundary current-home/retirement assessment and consolidation.
Disjoint documentation writers; root integrates exact cross-owner remaps.
Still Phase5; no runtime/API/spec changes dispatched.

Int lineage pass completed: macro/cache migration docs retired, current macro
contract in int6.8 and restoration parity in int7.5; delivered §16 backlog
removed. Net6,405 words removed. The eval JIT wording question is resolved:
__expr shares its turn batch's JIT; persistent-workers4.5 corrected. Root applied
the exact4 document and2 config remaps.
- qa Opus5.5/high `4ec3560e-9f47-4533-b3aa-b54939ec0650`: classify newly
  preserved dependency-hash/platform-restore leads, source/evidence read-only.
- dev(src) Opus5.5/high `3ce710df-4358-4c67-b763-b356f4e8b454`: same-fact
  macro/cache rustdoc and memory coherence; sole source writer, no behavior edit.
C-A remains user-deferred. Neither cache lead is a reproduced defect.

Backend consolidated1882 lines across4 selected carriers to621 in2. Ring2
retained at its cited anchors; ring1/jit-setup retired; panic boundary corrected
to recorded-error plus returning sentinel (no unwind/trap). Existing capture
borrow default-on and sentinel-safety evidence limits remain explicitly open.
Root applied exact16 remaps (R3's own §7 confirmed as its triage record).
- design(platform) Opus5.5/high `780e16f9-7172-43fa-9454-425233010f25`:
  consuming-capture example correction and canonical-home consolidation.
QA classified CD-1 required reproduction, CD-2 later advisory, CD-3 deferred
under user C-A policy. Dev comment pass complete; cargo check clean; runtime
unchanged. Its additional stale macro comments are retained for next int sweep.
Test owns CD-1's ordinary dependency-edit repro and controls; no fix dispatched.

CD-1 test Opus5.5/high `3c8f4d72-4324-409b-a005-ca88de503749` is the sole
source writer/runner. ACT-0952's statement that the dependency-hash path was
already complete corrected per QA, retaining the planned requirement.
Integrated documentation check currently247→238, no introduced identities.

Platform capture ownership now has one home, platform-dlls4. Root applied the
owner's exact backend/source citation and release-timing remaps; no behavior
changed. Wrong own() descriptions in platforms/stdio/spec.md and
platforms/test-capture/spec.md remain for a focused documentation pass.

CD-1 reproduction completed: four permanent, nonignored tests in tests/cache.rs
are RED in two consecutive targeted nextest runs. Ordinary dependency edits
under an unchanged restored importer accept an ill-typed call (107 vs rejection)
or call the wrong slot (99 vs11), in both --run and --link. Controls establish
cache-use dependence; writer versus restore mechanism is not isolated. QA
reconciliation is next. No compiler fix or broad test run is claimed.

### Checkpoint 5b1a843b and continuation (2026-09-24)

Committed45 files, including four permanently failing CD-1 reproductions,
under the user's checkpoint instruction. Documentation checker247→238,
535 documents, no introduced identities. NOTES hash unchanged; .agents excluded.
QA Opus5.5/high `d204f966-70a0-475b-beb3-3319270981e7` reconciles CD-1
evidence and retains the separate sentinel/M3 instrument candidates.
Spec receives the two platform specifications' factual ownership corrections;
no new language behavior is authorized. Still Phase5.

QA reconciliation complete: direct-import e2e evidence adequate; cache-use
dependence confirmed, precise mechanism remains source-supported/provisional.
Root applied QA's exact artifact-underkey vocabulary/tag remaps, no test logic
changed. The separate panic-sentinel and M3 candidates remain advisory.
Spec Opus5.5/high `a07fe940-296f-4584-ae01-c16e1f8068ee` corrected the two
platform specs against existing authority, no semantic gate. Residuals: platform
spec ownership/establishment absent from root; stale stdio read-line source
comment; language IO ABI wording versus poll leaves; unused test-utility export
requirements; final unterminated-line behavior lacks a pinning test. These
remain open, not silently discharged.

### CD-1 design and filing cleanup (2026-09-24)

User requested continuation. Design(int) Opus5.5/high
`53395bf4-baca-4ffd-9242-697033e4bf23` settles the private cache correction
and same-fact standing claims; no implementation dispatched before that result.
Arch receives the current checker findings in its legacy filing collection for
a coherent cleanup batch, preserving unresolved obligations. Baseline238.

Arch filing pass: Opus5.5/high `772c5b94-f103-4025-8ec8-ddea5f3b7293`.
Root applied the prior spec owner's exact stdio read-line scheduling comment
correction against READ_LINE_DESC; no runtime behavior changed.

Cache design complete: int7.6 records transitive source dependencies using the
existing map, shared across restore and all three writer paths. No public API
or schema-shape change proposed. QA Opus5.5/high
`d3b81897-0789-4486-9abb-28443170f0ca` settles the incremental evidence handoff.
Root applied design's exact backend prose/rustdoc handoffs.

Arch filing cleanup completed:24 touched,10 retired, collection6135→2957
lines. All55 findings sourced in the collection resolved; incoming remaps
being integrated. Open obligations preserved in canonical filings, including
0835's derive ceiling in0815 and0916's backend arm in0903. Owner reroutes
0553/0708 to design(int),0907/0914 to QA reflect verified residual work;
coordinator accepts routing, not evidence closure.

Integrated checker238→183, no introduced identities after filing remaps.
QA settled CL-A–F: two closure-path e2e cells (including rebuild over restored
intermediate), builder/edge units, validity seam, existing hit fences. Test
receives the two RED-first e2e cells; dev implementation waits for the result.

Test Opus5.5/high `f1330d6e-24e0-4a51-957f-0b52092c8612` completed CL-B/C:
both intended RED, re-export-only arming passed without contingency. Full
cache target52:46PASS/6FAIL, all six CD-1. The early hit trace's limits remain
explicit; stale output confirms completed restore in the failing subject.
Dev(src) receives implementation, units, cache/search and wave verification.

Dev(src) Opus5.5/high `3c6460dd-a3f8-477c-aa57-451912c5208b` owns source
and all builds. Design(backend) Opus5.5/high
`ea11a743-88d1-452d-999f-44358c365dc7` condensed module-caching1287→565
lines (11742→4188words), retaining live anchors. Root repaired its one renamed
anchor. Remaining same-fact handoffs: ownership-inference5.1 still claims the
old transitive cascade; cache test14.4 citation should be3; int7.5 malformed
metadata wording; backend master6 disk-IO/resolution attribution; backend
cache rustdoc. Dormant public packet API disposition remains open in cache7,
no removal or public API change authorized.

CD-1 implementation complete in src:61 focused units,96 cache/search/exemplar
e2e pass. Initial full run exposed an unsettled parent/child write omission;
a RED-first deferral unit and retry-before-flush corrected it. Final full run
6049run:6048PASS/1document-conformanceFAIL,1skip. Checker179findings, no
new identities against238 baseline. No public cross-crate API/schema-shape
change; no commit requested in this continuation.

Review Opus5.5/high `f8a9e5fc-941b-4733-9f4b-b3fb506588be` found no blocker
to the allocated implementation, but FQautoload dependency edges remain an
unexecuted required lead. F2 predates final deferral correction. QA
`37110182-ec4a-4020-baed-3474b484ee15` reconciles final evidence and next intake;
design(int) `d80349af-ed9a-4d26-8be2-0b3419dd3e31` updates standing status;
review `a61ba638-847a-40e3-bd76-eaea5d6cbcf9` checks only final F2 correction.
All Opus5.5/high. Root applied backend's exact cache test citation14.4→3.

User ruling (2026-09-25): stdio and test-capture are QA-owned platform
components controlled as test-suite dependencies. Examples, documentation,
demos and the exemplar share them under that ownership. Their behavior is
not language specification. Root guidance establishes both existing contracts;
no new document is needed.

QA accepts CL-A–F as delivered, not the entire cache-validity class. F1 and the
observed fresh-child/restored-library face receive bounded repros under test
Opus5.5/high `6cb50359-8d90-4d2e-8857-8b43c6f5d3ac`. Finding-scoped review
resolved F2 but raised unexecuted D1 depending on a REPL type-changing turn.
QA read-only triage `02cb464f-03af-49ab-a4b4-ed4292e3a5e9` checks whether the
existing dependent-redefinition refusal refutes that trigger before any fix.
Root applied design's exact backend as-built remaps and ACT0952 status update.

D1 triage: the review's ABI-changing/BROKEN trigger is refuted by the dependent
redefinition guard. QA nevertheless holds deferral acceptance on a distinct
allowed macro-edit/restart trigger, with a non-deferred sibling control. Root
integrated that exact QA allocation into the evidence delta; no fix chosen.

F1 followup executed: two permanent REDs, stale slot99vs11 and unchanged warm
load unresolved GOT when only qualified use loads b. Cache target56:54PASS/
2FAIL; the six corrected CD-1 cases remain GREEN. DV3 base and super shapes
GREEN; the original exemplar observation remains unreproduced, not closed.
Design(int) Opus5.5/high `5417a002-566a-4060-8f8e-abcaba85f0b4` now prepares
the F1 carrier/restore correction. Test Opus5.5/high
`7c2ea103-8c63-4aef-bbc6-38733d8f079a` executes QA's D1 macro-deferral cell.
No new runtime fix has been made since the final6049-test run; the current
working suite additionally contains the two newly discovered F1 REDs.

D1 test result (2026-09-25): UNARMED, neither confirmed nor refuted. A legal
observable fixture deferred the parent rather than child (12/12 probes).
The super-edge type-change refusal is now executed. More importantly, the
admitted macro replacement remained live-only: three restart probes persisted
the old definition, extending ACT0970 evidence. No D1 cell was landed; draft
remains local. The deferral acceptance hold is not discharged by this attempt.

F1 design7.6.1 needs a persisted SymbolTable qualified-reference carrier.
Arch Opus5.5/high `e143eb83-5320-41af-9c7d-66e0f4d2bc92` prepares the exact
public-API/schema approval packet; no field or schema change implemented.
The last integrated checker remains179 findings/525documents, no introduced
identities; net Markdown reduction approximately28,200 words before final
proposal/evidence adjustments.

### Qualified-reference cache correction: consume existing callees

Checkpoint `94486f24` contains the private cache corrections and retained F1
guards. The user challenged the proposed additional carrier because `callees`
should support cascading module load. Arch Opus5.5/high
`5e3d1ae5-819c-4031-9672-3adef76583b1` completed a read-only reassessment.

The additional `qualified_reference_modules` field and two-method public API
proposal are withdrawn. For both F1 reproductions, typecheck already records
`b/f` in the callable's persisted callees; cache validity and restoration omit
that existing information. The historical Decision 21 traversal served codegen
readiness among loaded modules, rather than documenting cache restoration,
but the stored dependency fact supports this use.

Recommended correction: derive callee modules from all callable arms through
one shared int helper, and consume them alongside declared dependencies in
cache record building, the index worker and cached-module restoration. No
inter-crate API or schema change is needed. Design(int) must correct §7.6's
claim that no carrier exists and replace the withdrawn §7.6.1 proposal before
implementation. The two existing F1 REDs remain acceptance evidence; this
read-only assessment did not execute a fix.

First-hop re-exports, constructor/accessor/type references and macro-use edges
remain unmeasured completeness questions. QA must distinguish existing
resolved facts from genuinely missing information before proposing another
carrier. D1 macro-deferral acceptance and ACT0970 remain separately open.

The user requests failing tests for the remaining reference kinds now.
QA Opus5.5/high `6899cc19-3604-42a8-a25e-08c1f0ea0f14` allocates one
focused batch before test execution. Leads are not presumed defects; retain
discriminating reproductions and distinguish green controls from unarmed
fixtures. Source-file edits avoid conflating cache invalidation with ACT0970.

QA's settled allocation supplies QR-1 through QR-6: re-export first hop,
constructor tag, dotted accessor, type-only glue, macro expansion and
constructor-only warm loading. Test Opus5.5/high
`607c57fa-1a2d-40b6-baeb-c550957a1bcc` implements and runs the batch in
`tests/cache.rs`. Mount-alias autoload and instance-mediated implementation
visibility are withheld as separate normative questions, not cache failures.

QR execution completed: test added seven permanent cells. QR-1 through QR-5
are RED with explicit-import siblings GREEN: stale re-export target (11 vs
99), constructor tags (11 vs 22), accessor offset (99 vs 11), type-only
allocation/deallocation counts ((5,3) vs (6,6)), and macro expansion (11 vs
99). QR-6 constructor-only warm loading is GREEN. A separate new fresh-compile
guard rejects a module named only in a fully-qualified type annotation;
loading that module first succeeds. This is not a cache failure, and its
attribution remains provisional for QA.

The final foreground cache target run is 63 tests: 55 PASS, 8 FAIL (the two
existing F1 guards plus six new REDs), no skips; repeated runs agree. All prior
CD-1 and DV3 controls remain GREEN. No production code changed. QR-4's fixture
loads b before a to bypass the independently retained fresh-compile defect;
QA must confirm this evidence adjustment and classify that fresh failure.
The prediction that QR-1–5 survive callee consumption remains unexecuted
until that correction is implemented.

Checkpoint `d5b460b6` commits the reference regression tests and evidence.
The user directs the next work back to documentation. Baseline remains177
findings. Three disjoint document-only batches run on Opus5.5/high: arch
`1a93530e-47e6-4e90-8561-887164ed0a9b` (architecture and types memory,
including legacy filings0870/0917/0931/0934); spec
`79cf69d8-af17-46c0-84e5-7c969fa2c3c1` (language and REPL references);
design(int) `07ca6e96-8dd0-48e3-9dde-f2c5b4543a17` (integration designs
and withdrawal of the superseded cache carrier proposal). No source fix,
new semantic ruling or public API change is in these batches.

All three batches completed. Arch resolves all35 allocated findings, int all32,
and spec17 of23. Root applies their mechanical incoming-citation handoffs,
updates the int document collections and removes the empty untracked foo
probe directory responsible for two false path findings. Integrated checker:
177→76 findings, zero introduced identities; approximately32,000 net Markdown
words removed. `git diff --check` is clean. Rust changes are comments only;
parsed Cargo configuration is unchanged. No build or behavioral test was run
for this documentation batch. NOTES.md and the shared package are untouched.

Retirement: the fixed cache-prelude reproduction report moves to Git history;
its current fallback-parity fact and regression reference now live in int§6.5.
Other rewritten documents retain their current contracts and open obligations.
Legacy0870/0917/0931/0934 retain only their unresolved residue; no evidence gap
was closed by deleting narration. The extra qualified-reference carrier is
withdrawn in canonical int design; callee consumption remains unimplemented.

Remaining handoffs from the batch:
- QA: confirm the unchanged executable-output coverage after the CLI table's
  settled wording correction; assess trait-impl carrier unit-evidence gaps,
  0934's unrun-Bind/cancellation evidence, and int's source-observed gaps
  recorded in its revised designs. They are not executed defect attributions.
- Test/platform dev: clear the comment/notation residues in0870 and0917 before
  retiring those filings. 0931 still needs its constructor-population evidence.
- Source rustdoc: RunMode still names a nonexistent backend CompileMode;
  CacheState.recompiled still claims a consumer it lacks; typecheck ownership
  publication still mentions retired set_mode_summary. Correct documentation
  or allocate implementation separately; no code removal is approved here.
- Four spec findings are valid illustrative names/paths misclassified by the
  shared checker; no exception or suppression was added. Shared-tool treatment
  remains separate from these repository prose repairs.
- Spec also retains the obsolete ring-gated conformance sentence pending a
  ruling; int retains the undocumented /reset behavior question. Git-revision
  references preserve the S102 lineage; no historical report is new authority.

User ruling: the REPL specification is correct. The REPL reports the type and
value of the expression, so IO retains its displayed IO type and the completed
IO.Pure wrapper under REPL§1.2. The proposed inner-value-only display is
rejected. Presentation belongs to the REPL specification; language§10.6.2's
conflicting display policy/example must defer to it. The implementation and
test that currently strip the displayed IO type are not authority.

Spec Opus5.5/high `0f46311d-aae9-4692-9350-1742ca521a46` applies the ruling
to the language-spec passage; QA Opus5.5/high
`f4044d03-ed5d-4f8d-a33a-391d83a9caea` allocates a focused regression
correction. No production fix is selected. The document batch remains uncommitted.

The earlier IO-envelope ruling and its IOD-1–3 guards are superseded by the
user's later automatic-execution notice ruling. The delivered IOT evidence and
current requirement are recorded at the end of this sprint log and in the QA
plan; inner-payload display is no longer classified as a defect.

Checkpoint `a07823d8` commits the documentation consolidation and three IO
display guards. The user directs continuation. The next document-only batch
starts from76 findings: QA Opus5.5/high
`2ae38ac3-9d0c-4d9f-8bf8-f22accd4e798` owns retained test-plan cleanup;
dev(exemplar) `126dbf84-aeaa-48c4-8c56-b43aed28ac14` owns exemplar standing
documents; design(backend) `9d8b56e8-68ef-454f-a5d6-2d65fc3a0716` owns
backend design consolidation. The writable surfaces are disjoint; no source
correction, new behavior or runtime testing is in this batch.

The exemplar document pass completed (dev session above): 2,055 lines across
three files become 264 lines across two, preserving four open obligations.
Root establishes the retained design and repairs its incoming performance
reference. Dev(stdlib) Opus5.5/high session
`2cd80c55-399d-4a6c-9980-083dbdcf3f4d` now owns `stdlib/**/*.md`, including
the incoming citation to the retired exemplar review. QA and backend continue
on their reserved surfaces. Platform finding0870 is retired after its last
two ABI comment corrections; the already-settled closure-boundary discrepancy
is removed from architecture's open list. Runtime behavior is unchanged.

QA's document pass completed with all11 QA-plan findings resolved; current
REDs remain open. Backend's five findings are resolved. Root integrates the
QA citation handoffs and updates the IO design's delivered-test status.
Test Opus5.5/high session `3413f932-bd54-4b2f-b809-fd1bb8c6739e` owns
test-side Markdown outside QA plans plus the exact0917 comment/notation tail.
No executable test changes or threshold-cell retirement are allocated in this
document-only pass; the newly extracted QA allocation remains in PLAN.

Stdlib documentation pass completed: five documents/2,603 lines become
two/507 lines. Its backlog and function-valued-def options now live in the
current design, and missing IO self-test obligations have been recovered there.
Root establishes that design and repairs incoming filing citations. The
existing `Ord String` usability gap and stale sconcat spec attribution remain
explicit in its open-obligations section; no feature or semantic change is
implied. The IO type-prefix question has been presented to the user: retain
bare IO as an exception, or follow the general fully-qualified-type rule.
No answer has yet been recorded.

The integrated follow-on documentation check reports76→34 findings:42
baseline identities resolved, zero new identities. Reports are the second-pass
QA/backend/exemplar results and stdlib/test-cleanup results under `.local/`;
the final observation is `.local/s122-doc-followon-final.json`. Eight obsolete
documents are retired in the working tree, with roughly73,000 net Markdown
words removed. Current obligations remain in owned plans/designs; QA's L-B1
corpus-extension disposition is explicitly retained in PLAN.

The test pass completed, including0917's three S120 fixed annotations and the
separate forwarding guard's verified S121 annotation. Its filing remains until
the comment edits are committed, as its closure rule requires; runtime tests
and the residue threshold are unchanged. All Rust diffs are comment-only;
`git diff --check` passes, the index is clean, and NOTES.md retains its original
hash. The independently dirty `.agents` is untouched. These follow-on edits
are uncommitted after checkpoint a07823d8. No phase advancement or push.

Remaining document work includes frontend/typecheck/runtime designs, teaching
and user-document surfaces, and checker false positives on language symbols.
Known source-comment handoffs remain with their owners, including backend
rustdoc under ACT-0964 and stdlib/test references to retired sections. The IO
head-spelling question is settled by the user ruling below; runtime display
correction remains outstanding.

User ruling (2026-09-25): "No exception for IO types - consistency is critical
for simple code and least surprise." IO follows the fully qualified type rule:
`(Pure 42)` displays `:(primitives/IO primitives/Int) (IO.Pure 42)` after
forcing. This changes the type-prefix spelling only; the IO envelope ruling
stands. Spec, test and QA are applying the narrow specification/example,
existing-guard and evidence-plan delta, respectively, on disjoint paths.
Claude Opus5.5/high sessions: spec `f91ea0f8-31cc-424b-b226-e0cf7f0c3adb`,
test `f1083887-8cb7-4177-bfb7-53dbd9deaa3e`, QA
`344400e8-d7a5-4b9c-bbce-60cdf994788d`. Only test runs the affected guards;
production implementation is unchanged.

The IO head delta is complete: spec example and rule, strict three-cell
predicate, QA evidence plan and int design agree on `primitives/IO`.
The affected nextest filter reports3run/3expected failures, still inner-only
display. QA accepts the filtered evidence because only those three cells call
the changed helper; bare-head rejection is structural in its literal regex.
No coverage is marked green and production display remains uncorrected.

Checkpoint `eac3c1be` commits the standing-document consolidation and IO
qualification ruling. The user directs continuation within Phase5. Finding0917
is now retired: its final annotation/comment obligations are committed; the
separate QA residue-threshold obligation remains in PLAN.

The next document-only batch starts from34 findings. Claude Opus5.5/high design
sessions: frontend `a97392f1-8ec2-4a35-96d2-e0db3e3e733a`, typecheck
`e34efdb9-a3fe-4e48-94e4-d555485a7924`, intrinsics/runtime pair
`de45be2e-b50c-45d7-90bf-dac2690a83d6`. Their writable design surfaces are
disjoint; historical crate plans are read-only assessment inputs. No source
change, runtime test or new behavior is allocated.

Runtime design pass completed: all five allocated findings repaired, one
superseded S117 design retired, current contracts preserved. Finding0928's
rulings are recorded, so its filing is retired; the missing debug-only Drop
rustdoc remains explicit in the current consume-funnel design §9.
Arch Opus5.5/high `bd34daf8-9e54-492d-aa63-75f132e03095` now assesses the
implicit-reference false positives read-only across the shared checker and
consumer conventions. No shared-package edit or exception is authorized by
that assessment.

Frontend and typecheck design passes completed. Their superseded Ring0 plans
are retired after checking canonical coverage; frontend's retained annotation
design has a subject-based filename and repaired declaration/incoming link.
Qualified-symbol examples remain unchanged where the checker misclassifies
them. The runtime/frontend/typecheck batch resolves13 of the original34
identities after integration. Current auto-curry and settlement-window counts
are reflected in filing0776 without deciding its proposed general policy.
Dev(backend) Opus5.5/high `b658a038-0a2f-4da7-afa6-3cea74ea5477` owns backend
memory/plan and comment-only ACT-0964 repairs; training
`b8314ed9-ea42-4354-9ba3-739d12fcb0df` owns examples Markdown. Arch's checker
assessment continues read-only. No runtime runner is active.

Training retained and streamlined both examples documents; root applied their
explicit declarations. Test Opus5.5/high `6bb8a074-2b14-45d0-b85a-189470797db6`
owns the remaining REPL Markdown, and docs `006f5e90-40f8-4ff6-8e7e-4f48789bf80c`
owns the user-guide findings. Backend remains the sole source-comment writer.

Arch's checker assessment proposes a shared bare-name extraction correction
(R1) with explicit detection tradeoff, plus optional duplicate deduplication.
The package remains untouched. Root's read-only sibling follow-up found Magic's
legacy declaration/exemption format and no feedback-dev standing declaration;
no fully migrated three-consumer result is claimed. Exact exceptions for the
ambiguous dotted-name and illustrative relative-directory examples have been presented
to the user under the standing contract's explicit exception gate. None is
applied pending that answer.

Docs and REPL-document passes completed. The nonexistent tutorial promise is
removed; ACT-0951 still owns the unspecified /learn feature. Redefinition links
now target their real spec section, although the checker misassociates a section
marker inside a link label with the preceding document. This is an additional
shared-checker extraction defect, not a remaining broken guide citation.
Three old REPL reports are retired after extracting their open obligations
into demo guidance; the Haiku baseline and ACT-0960 are unchanged. Root corrects
the demo memory's declared owner to test. Its one obsolete demo-script comment
will be removed after the backend source-comment writer finishes.

Integrated continuation outcome after checkpoint eac3c1be: checker34→12,
22 baseline identities resolved and zero new identities. Remaining findings
are eight qualified-name extraction false positives, one section-marker/link
misassociation, and three findings on the two ambiguous example spellings
presented for user approval. No exception or baseline has been applied. The
shared-tool corrections remain proposed, not installed; the current package
and sibling repositories are unchanged.

The active Markdown surface loses approximately27,600 net words in this
continuation, including the new frontend design filename in the calculation.
The three Ring0 crate plans, S117 runtime design, three old REPL records and
completed filings0917/0928 are retired with unresolved obligations retained in
current designs/plans. Backend ACT-0964 item3 is complete; items1/2 stay open.
The demo's citation to its retired verification record is removed.

Verification: `.local/s122-doc-third-final.json`; `git diff --check` clean;
16 backend Rust files have identical non-comment tokens and comment-only diff
lines, independently rerun by root. The demo diff removes comments only.
Backend's format check passed; no runtime tests were needed or run in this
document/comment continuation. NOTES.md retains its original hash; the index
is clean. All dispatched roles completed successfully. Changes after eac3c1be
remain uncommitted, including the new
`design/frontend/annotation-and-declaration-shape.md`, which must be added
alongside its old-path deletion at the next checkpoint. Phase5 continues; no
push or phase advancement.

The user approved a trailing, physical-line-scoped HTML annotation for the
binder design's illustrative symbols and the CLI table's hypothetical paths:
`doc-check: literal` with a required reason. It excludes implicit path detection
on that line while preserving explicit Markdown-link and establishment checks.
Central reference exceptions are not the selected solution. Shared checker
implementation and regression evidence are being prepared in an isolated copy
by dev, Claude Opus5.5/high, session
`1e439b95-e413-4985-b874-722dbc8b0ed4`; the independently moved package checkpoint
is preserved. The bare-name heuristic and section-marker fix remain separate
proposals, not approved implementation in this annotation change.

Line annotations are implemented and integrated in the shared package working
tree; its existing eda9132 checkpoint is unchanged. Only the two approved
example lines are annotated. Dev's broader diagnostic overlay is not the
integrated scope. Independent review, Claude Opus5.5/high session
`f0bb77ab-83aa-4eb5-bf6e-ec9f7465f479`, accepts the change and confirms table
rendering. Integrated verification: 27 shared unit tests and 21 consumer CLI
acceptance tests pass; the ordinary checker reports 12→9 findings, three
removed identities and none added. Explicit-link, adjacent-line and orphan
checks remain active. Evidence: `.local/s122-literal-final.json` and
`.local/s122-literal-review-result.md`. No compiler runtime behavior changed;
the known-red citation-drift gate is not claimed green.

Review's low-risk advisory remains: an HTML-comment terminator inside a reason
is accepted and would prematurely close the rendered comment. The two applied
reasons contain no such terminator. A cosmetic contract reflow advisory is also
unresolved. Package changes and consumer changes are uncommitted; no push or
phase transition occurred. NOTES.md is unchanged.

Checkpointed at user request: consumer 50d95d48 and local shared-package
52d7e20. The consumer Gitlink remains on its published revision, following the
package contribution contract; neither checkpoint was pushed. NOTES.md was
excluded. Dev, Claude Opus5.5/high session
`f82fe71e-b39e-43f4-b109-5bce5e3965c4`, now owns an isolated shared-checker
correction for section markers inside explicit Markdown links, plus the small
annotation-reason rendering advisory. A user question remains pending on
whether the eight bare qualified-name findings should use literal annotations
or a shared heuristic that stops detecting unresolved bare paths. No heuristic
change or additional annotation is authorized pending that answer.

Section-association correction integrated after independent review, Claude
Opus5.5/high session `068d729c-b4bd-438e-bb44-aa16d5699813`: 28 unit and 21
consumer CLI acceptance tests pass. Ordinary checker findings fall 9→8 with
one removed identity and none added; three other silent wrong-document
associations are also removed. Existing supported section citations remain
checked. HTML comment terminators in annotation reasons are now rejected and
the remaining cosmetic contract reflow is repaired. These shared changes are
uncommitted after 52d7e20. Evidence: `.local/s122-section-final.json` and
`.local/s122-section-review-result.md`. No compiler runtime suite was run.

The user asks whether source can be recognized reliably and excluded. Fenced
examples are already excluded; source-file inputs already use comment/docstring
extraction. Inline backticks carry both symbols and citations, so their text
alone is ambiguous. A read-only census found 3,066 resolving standalone code-span
path occurrences in 283 live documents (historical records excluded), indicating
the migration size if references were required to be explicit Markdown links.
This is an unclassified occurrence count, not an approved migration inventory.
The eight name findings remain, with no new annotation or heuristic applied.

At the user's request, [ACT-0991](actions/ACT-0991-explicit-markdown-reference-adoption.md)
defers explicit Markdown-reference adoption across the shared package and its
three consumers to a future increment. Current reference checks remain active.
The user subsequently approved literal annotations for the remaining language
examples. Nine physical lines in six documents now carry the annotation;
example spellings and requirements are unchanged. The integrated checker exits
0 across 508 documents, with zero findings, no baseline matches, no configured
reference-exception matches and no stale entries. Evidence:
`.local/s122-annotations-final.json`; `git diff --check` passes. Existing
historical-record policy is unchanged. ACT-0991 records the future migration;
the bare-path heuristic remains unchanged. This clears the checker findings,
not the separate compiler defects or every substantive document obligation.
Follow-on changes remain uncommitted and NOTES.md remains untouched.

### Final acceptance reconciliation (2026-09-25)

The user approved a bounded final QA reconciliation and fresh test run, not
carry acceptance, Phase6 advancement or publication. QA Claude Opus5.5/high
session `4caf3e09-2fd9-49a4-804b-d056f620140e` reports that Phase5 is not yet
ready. Its read-only assessment is `.local/s122-final-qa-result.md`.

Fresh evidence at consumer293534ee with local packagec339fa7:

- Default nextest: 6,060 executed, 6,049 pass, 11 fail, one intentionally ignored
  contention benchmark; 109.2 seconds. `.local/s122-final-nextest.log` and
  `.exit` retain the run. Seven failures concern qualified-reference cache
  invalidation/restoration, one is fresh-compile type-only module loading,
  and three concern the approved REPL IO display. All match existing recorded
  guards; QA found no new regression in this run.
- The prior sandboxed run had 13 additional failures: ten denied ephemeral-port
  binds and three reactor backstop timeouts. All pass in the controlled rerun
  with socket access. The sandbox log is retained separately; it is not product
  failure evidence.
- Citation drift, role wiring and public-API relocation checks pass in the
  default suite. This is maintenance evidence, not proof of substantive coverage.
- Refreshed isolated agent integration lane:81/81 pass. Feature-gated agent
  module selection:137/137 pass, 3,544 outside the selection. Logs are
  `.local/s122-final-agent-lane.log` and `.local/s122-final-agent-modules.log`.
  The latter supplies current evidence but does not repair ACT-0982's launcher
  routing. Offline eval self-check:18/18 cases agree, recorded in
  `.local/s122-final-eval-self-check/report.json`. This refreshes the harness
  evidence that was stale at QA's assessment. No live model rerun was requested
  or performed.

Delivered scope has evidence for generic replacement, public IO composition,
recovery under its approved public-trigger limit, macro-turn ownership fixes,
selected convergence and the shared document checker. The historical Haiku
baseline completed2/2 tasks with one attempt each; it is not a reliability
estimate or a current-binary model-quality claim.

Acceptance work still requires explicit disposition:

- QA recommends implementing the private callee-consumption correction and
  approved IO display, then rerunning the qualified-reference guards before
  deciding whether any additional dependency representation is needed.
  Persistence and fresh type-only loading remain separate defect questions.
- ACT-0970 needs a permanent macro-persistence repro/control; ACT-0983 has a
  passing test for superseded rejection behavior; ACT-0980 is an unexecuted
  potential source-loss lead. Remaining intake actions require bounded QA
  triage, and the platform GOT collision still lacks its allocated fixture.
- The known-issue inventory outcome remains incomplete. Fixed/superseded
  records require owner retirement, remaining records require repair or
  individual carry decisions, and QA must reconcile cleared coverage claims.
  No blanket carry is inferred from the user's wish to wrap the sprint.
- User-facing assessment/action, the selected backend audit and Phase7
  principle/contribution work remain under their declared phase gates.

No source fixes, carry approvals, phase transition or publication occurred
during this reconciliation. The checking-allocator lane, fmt/clippy and API
regeneration were not refreshed by this default-suite run.

The user approves the bounded F1 callee-consumption correction before carry
decisions. Sequence: design(int) reconciles existing §7.6.1 against source;
dev(src) implements the private consumption change with module evidence and
reruns the complete cache target; independent review and QA assess the result.
No new public API, dependency carrier or cache schema is approved. The QR
guards that survive are returned as measured remaining scope; IO display and
other acceptance items are not included in this approval. Design session:
Claude Opus5.5/high `602047c8-2cae-4954-8fdc-d49518b515aa`.

F1 delivered in the uncommitted tree over293534ee. Dev
`aa5943ba-beb5-47f1-ba8f-169793ecbeac` shares the private callee enumeration
between redefinition and cache edges, consumes it after index publication,
and loads callee modules during restoration. No public API or schema changed.
Four new module units failed for the intended reason before implementation;
74 focused tests pass afterward. Both original F1 guards now pass. Final full
run before the extra FN-1 test:6,067 executed,6,058 pass,9 known fail,one skip.
The fail set is the prior11 minus the two F1 guards. Cargo check and check-tests
pass without warnings; clippy has existing warnings and no new changed-site
lint by review inspection, not a measured clean-baseline comparison.

Review `2c866097-38f5-4134-bbca-c8400826fa30` accepts the implementation.
Test `7b65e004-f08e-4fa3-8cc9-c98cfa0dcf6a` independently reconciles arming,
oracles and outcomes; preserves defect-history annotations as fixed and runs
the final cache target:63 executed,57 pass,6 known fail. Design
`5b26ea93-8488-4f96-a338-82f923fdd92c` reconciles delivered status. QA
`3c31f4a5-6046-4154-8717-cf36989b685a` accepts F1 as a bounded correction and
classifies QR-1–5 as measured missing dependency edges, without concluding a
new carrier is necessary. All roles use Claude Opus5.5/high. Root retains three
mechanically qualified typechecker source citations and applies QA's explicit
status-wording handoff. Test annotations must land with the implementation.

QA's additional FN-1 alias-only import fence exposed a cold-start rejection
before its warm leg. Test `435e6a73-a341-4496-92ef-a03a6c6320a7` retains the new
cell:64 cache tests executed,57 pass,7 fail; both original F1 guards still pass.
It is not a restoration failure and does not reopen F1 acceptance. QA
`bf17a803-5866-450e-a303-53ad2f63607c` owns immediate intake and requirement
classification. No alias implementation change is authorized. FN-1 remains
unarmed; the full-suite count above predates this new cell. No source fixes
outside F1, phase transition, publication or carry acceptance occurred.

FN-1 intake complete: QA classifies the cold failure under existing deferred
FIXME0798 (alias-only imports fail to register their alias on the fresh path).
The requirement is unambiguous; source attribution remains provisional because
the diagnostic controls were not executed. Root applies QA's exact test
annotation and design-status handoffs. The new guard remains failing and
unignored, attributed to0798; it does not reopen F1 or claim warm restoration
coverage. Repair scheduling remains a separate user decision. No ACT-0992 was
created. The narrow F1 correction is review-accepted and QA-adequate; overall
Phase5 acceptance and the remaining compiler defects are still open. All
changes in this correction remain uncommitted; NOTES.md is untouched.

The user approves fixing the confirmed remaining failures before close, grouped
as module loading/cache dependencies, then REPL IO display. This authorizes
private corrections to established requirements; any public-API, cache-format
or architectural delta still returns for explicit review. Initial reservations:
arch read-only dependency assessment `434a4038-0943-4fff-96e6-c0be4880de46`;
design(int) read-only IO correction assessment
`27042402-e39a-42cf-8549-8188631b79de`; test is the sole source writer/runner for
narrow loading reproductions `c0c133e2-848b-4f39-a290-4b6d1cd424cb`. All use
Claude Opus5.5/high. The earlier unscheduled0798 status is superseded by this
approval; its correction is now included in the loading group. Existing F1
work remains accepted and uncommitted. No phase transition or publication.

The user's latest IO ruling supersedes the earlier IO-envelope display decision:
automatic REPL execution remains; announce `Executing IO…` before executing an
IO action, then display its returned payload with its fully qualified type.
Pure expressions have no notice; batch output is unchanged. The proposed
original-expression-type field on `EvalResult::Val` is withdrawn, not approved.
No explicit `/run` REPL command or configurable execution mode is included.
Spec `ccd38b5f-98f2-4352-9de8-56ad2ea011e3` reconciles owned requirements;
design(int) `3f5c2309-282c-4dae-9fcd-6447c447b060` assesses the notice placement
read-only before implementation. Both use Claude Opus5.5/high; the user's
question about medium effort did not authorize changing the shared effort.
Spec reconciliation is complete: REPL §1.2.1 owns the notice/payload rule;
language IO/runtime references point there. Document check:508 documents,
zero findings. Design assesses a private pre-driver write/flush with the same
IO predicate used for execution; no API, ABI or cache schema delta. QA readiness
`04944214-75bd-4953-8b3c-50837954b8ef` allocates evidence before the test writer.
QA readiness accepts the bounded notice correction; test
`37eb08d0-3d4c-4065-a3e5-6ecfee60ff59` owns the sole source/test write and Cargo
reservation for IOT acceptance cells and REPL-chrome filtering. Design(int)
`7d39adac-45c4-4e19-80f8-cde56a45d50f` reconciles only the owned IO design while
implementation is pending. No new public surface or phase transition.
IOT preimplementation evidence:278 executed,273 passed, five intended failures
at the missing-notice assertion. Existing mode-output equivalence cells pass.
Dev(src) `e06ff3fd-0bcb-44a3-87b5-2066a5ee4a3b` now owns the sole source/Cargo
reservation to add the private notice and module evidence, then run focused
and default-suite verification. Test edits preserve the existing payload
expectations; the obsolete envelope defect classification is withdrawn.
IO notice focused verification passes278/278. Default suite:6,079 executed,
6,071 pass,8 fail,one skip in112.862s. Seven failures are known QR/fresh-type
loading cases; the eighth is document conformance on renamed IO-test references,
being repaired by QA. Independent review
`468d4f1e-95a3-4a31-ab27-4fe2f9a51c20` is read-only; QA
`95a15b51-c19d-441f-a37d-85eb7da07981` assesses evidence and reconciles the owned
plan/traceability. All roles use Claude Opus5.5/high. This does not close Phase5.

IO notice slice complete in the uncommitted tree: review accepted, QA adequate,
and final code/test hashes match the reviewed checkpoint. Root verified the
advisory source-memory sentence and applied design's exact delivered-status
handoff. QA reconciled the plan and traceability; document checker is clean.
Runtime verification remains the full6,079-test run above; only document-gate
verification is repeated after the citation repairs. Seven cache/loading defect
guards remain; no phase transition, carry acceptance, commit or publication.
Final document gate rerun passes1/1 (two unselected tests); standalone checker
confirms508 documents with zero findings. Diff whitespace check is clean and
NOTES.md retains its protected hash. No second full-suite run was needed for
these document-only repairs.

User authorized checkpoint commit and continuation. Commit bc675d86 contains
F1/callee consumption, alias-only registration, the IO notice and their current
records/tests. NOTES.md and the unpublished package gitlink were excluded.
Next private correction: fresh qualified-type module loading. Design(typecheck)
`29ea95e4-ebb1-4623-8c8c-ab3259b6f96e` owns its design; review(src)
`4ad4cb5a-932d-4c51-a476-065716bd1008` closes the alias-fix inspection; QA
assesses loading evidence. The broader cache-edge/public CheckResult field
proposal has been presented to the user and remains pending, not authorized by
this checkpoint. All roles continue Claude Opus5.5/high in Phase5.
QA loading readiness/alias adequacy `58d7f0e2-d169-4937-90a8-5d8df02815c4`
accepts the alias correction and allocates FT-3/4 plus typecheck module units.
Test `af4cd527-2528-4e1b-be66-b73bfadc7f6e` owns the source/Cargo reservation;
design(int) `e48948c2-a597-404e-bec2-f699f5ac8159` designs the private span
preservation and reconciles alias status. Preserving a required diagnostic is
inside the approved fix scope; no new residual or extra approval is inferred.

The user's callee-identity question prompted arch reassessment
`627d1858-6b8b-4b1d-b69a-aa18a582f765`. It withdraws the earlier transient
CheckResult/session-set proposal: cache restoration followed by rewriting could
lose those edges. Terminal callees remain necessary. The replacement proposal
persists qualified lookup modules on SymbolTable and returns the lookup module
in Resolved, with two public fields and a cache-schema bump. It awaits explicit
user approval; no API/schema implementation is authorized yet.
FT preimplementation evidence:12 focused tests run,9 pass, FT-1/2/3 fail for
the missing qualified-type load request; FT-4's diagnostic-location fence passes.
Alias status comments and citation handoffs are reconciled by test. Dev(typecheck)
`3a42b860-7fa1-4a52-95b8-3088e999037f` now owns the sole source/Cargo reservation;
no full-suite rerun until the dependent int diagnostic repair is complete.
Typecheck dev completes the private producer:909/909 crate tests,3/3 public-API
gates, and101/102 focused tests pass. FT-1/2/3 turn green; FT-4 now measures the
predicted location loss. Dev(src) `0dc719fd-8621-4262-8d17-d55811a9862a` owns the
next source/Cargo reservation for that repair and one integrated full run.
Review(typecheck) `aca04ecb-5e56-4691-9cce-0ceb7563340c` is read-only. The
allocated impl-target unit exposed a discarded qualifier, repaired privately
with the same producer. Two additional annotation/trait-fallback observations
remain QA intake, not silently accepted as residuals. Arch record cleanup
`70110964-85c1-4f51-b8ed-41f9a2aea122` retired0798 after preserving its remaining
facts; root applied its exact inventory-link handoff.
Integrated A2 verification:182/182 focused tests pass; full default suite
6,093 executed,6,088 passed,5 known QR cache failures,one skip in110.251s.
FT-4 now passes. Review(typecheck) accepts source with required QA classification
of the uncovered value-annotation/trait fallback and design-record repair;
design has reconciled the implemented mechanism. QA
`559a6468-9af8-4a65-a562-319345cf7bc5` owns classification and adequacy, and
review(src) `7f836ed9-fbe8-450a-9450-e409991bbed3` inspects the span repair.
The broader dependency representation still awaits the user's decision.
Review(src) identifies R1: member-absent value gaps retain the written alias,
so the new canonical-only location match regresses that path. Design(int)
`d5c9ee7c-e7b7-4e06-88a8-3f9426ce6bca` corrects the premise; dev(src)
`018df75d-1e08-4ef1-8b2f-8a3a1f84586d` owns failing unit then narrow repair.
A finding-scoped review and affected tests suffice; no blanket gate replay.
QA classifies F-a/F-b against existing requirements: no normative decision is
needed, and the initial FT correction can be accepted independently, but edge1
coverage must remain open. Permanent FA/FB probes are allocated next; no carry
or silently accepted residual. The persisted-dependency API proposal remains
pending with the user.
R1 re-review `10dc6f4a-eb88-41d1-9ba1-ed1f169e18cf` passes after184/184 focused
verification. Root applied design's exact int delivered-status handoff. FA/FB
design `ae9bcb4f-3e4b-4eb7-bbcd-bf226e56f2ed` is private; test
`734a531b-97bd-4e5d-95bf-6de8a25f6619` measured10 focused tests:8 pass and the
two new cells fail exactly as QA predicted, all controls green. Dev(typecheck)
`efe2d13f-9883-43e3-a34f-e9b6da8fe259` owns their repair and Cargo reservation.
The observed REDs authorize the private repair under the user's standing scope;
root's same-change-set test/fix rule does not require an intermediate RED-only
commit. No extra commit or public API change has been authorized.


### Cache dependency direction — 2026-09-26

User approved conservative module-hash invalidation now, keeping terminal
callees distinct from qualified lookup dependencies recorded during compilation
and persisted with module metadata. Imports and exports already supply declared
edges. Lookup dependencies serve cache validation and namespace restoration;
they do not by themselves justify loading intermediate executable objects.
Incremental compilation must maintain the recorded dependencies; exact ownership
and replacement granularity remain architecture/design work, not a prescribed
per-form public representation. No selective terminal-body reuse is required now.
Future inlining and constant folding must account for embedded implementation
dependencies; [ACT-0992](actions/ACT-0992-optimisation-aware-cache-invalidation.md)
records that deliberate next increment. Restricting optimisation to release
compilation is a candidate, not a new CLI requirement.

The previous two-field proposal needs reconciliation with this direction before
its exact API/schema approval. Architecture is assigned that bounded revision;
no API implementation or phase transition is implied by the direction approval.
The preceding private loading/annotation correction is independently accepted
by review `3e24375b-7ef4-41a7-a19e-db98b34d3def` and QA
`0f814fe1-a96a-41e3-93ad-42a1badc93cf` (Claude Opus5.5/high).
Latest full evidence: 6,103 executed, 6,098 passed, five known cache-dependency
failures, one skipped. QA's exact record handoffs are reconciled; code is uncommitted.
Architecture revision dispatch: Claude Opus5.5/high, session
`67f4d43b-b7b2-4862-ab13-e8cafd0a5307`; returned the revised proposal in
[interfaces](../design/arch/interfaces.md#qualified-lookup-dependencies).
It proposes a private persisted set, two public access/record methods and one
Resolved provenance field (three added API baseline lines), plus schema29→30.
Lookup dependencies are validity edges only; REPL compilation loads on demand.
Insert-only module-level granularity is proposed for this conservative increment;
obsolete edges clear on fresh compilation. That granularity and the exact API
remain pending user approval. No compiler changes were made by this revision.


### Lookup dependency implementation approval — 2026-09-26

User approved module-wide insert-only maintenance, then explicitly approved the
exact API: `Resolved.lookup_module: Option<ModuleFullPath>`,
`SymbolTable::lookup_dependencies(&self) -> impl Iterator<Item = &ModuleFullPath>`
and `SymbolTable::record_lookup_dependency(&mut self, ModuleFullPath)` backed by a
private persisted set. Schema29→30 is approved. Three added public baseline
entries are expected, no removals or other public deltas. The generated baseline
returns for confirmation after implementation; no phase advancement or commit
is implied. Source checkpoint remains bc675d86 plus the reviewed private fixes.
The earlier pending statements above describe superseded checkpoints.

Design(typecheck), design(int) and QA prepare disjoint bounded handoffs in
parallel; no source/Cargo writer is active during preparation. All dispatched
roles use the user-authorized Claude Opus5.5/high allocation.

Preparation dispatches (Claude Opus5.5/high): typecheck design
`45c2fa49-3d4b-412d-8c73-8637c238928e`, integration design
`389995ef-3b04-419b-bdea-2d6adbcd22a2`, QA
`f6cfb977-1559-4dc7-80b0-7db016c04854`.

Typecheck design completed its producer census. QA readiness is clear; test
`c26f5520-7e78-4a2d-9346-e20428a141f0` (Claude Opus5.5/high) owns the source/Cargo
reservation for LD-2 through LD-5. New source-read trait-bound and pattern
resolution leads are retained, not accepted residuals; QA classifies them
independently of implementing the already-approved carrier.

Integration design completed: macro lookup facts travel with expanded retry
continuations and survive macro checkpoint publication. Lookup edges do not
change restore/object loading. Rewrites with unloaded lookup members can defer
cache writes, retaining the earlier entry under existing validity checks.
QA follow-up `e27bd21e-8889-4714-862f-53c2168c1f12` classifies the source-read
trait/pattern leads. The new integration-specific evidence requests await QA
allocation alongside the already-running test work.

LD pre-fix verification: cache target67 run/60PASS/7FAIL (the five QR guards
plus LD-2 re-export chain and LD-3 REPL rewrite); LD-4/5 controls pass. Dev(types)
`0f36af9a-3ec3-4db7-8d3e-123375e851a6` now owns source/Cargo. QA source-read
classification finds the trait/pattern leads are conformance candidates, not
blockers for the approved cache claim; LB-1/2 and LP-1/2/3 repros are allocated
before the typecheck source visit to avoid revisiting the same resolution code.
QA integration supplement `99507f97-8ecd-447b-9630-b58de698e16a` is read-only.

Types implementation:290/290 crate tests and3/3 API gates pass; exactly three
approved API additions. Root's canonical generator output byte-matches the
baseline, resolving the developer's transport-level regeneration limitation.
Test `d58a3389-d8af-4ac0-a0dd-0297eb8c17ff` owns source/Cargo for the combined
LB/LP conformance repros and LD-6/7/8 cache delta before producers are wired.

Types review `30222c49-1762-4aa2-9ea6-00b97e718278` accepts source and exact API,
with required R1 coverage for the private-ancestor resolver fallback. Route
directly to dev(types) as an extension of the existing T5 module witness; no
new independent acceptance condition or requirement is inferred. QA will judge
the supplemented evidence at adequacy. Types implementation remains unchanged.

Interrupted-turn recovery: test d58a3389 completed successfully. LB1/2 and
LP1/2/3 all have discriminating RED subjects and GREEN controls. LB1 uses a
REPL scheme oracle; LP3 isolates pattern-only loading. A separate unused-bound
enforcement observation is QA intake, not an assumed semantic ruling. LD6..8
cache results match predictions; no fixture is unarmable. Source/Cargo is
released to the narrow types R1 witness, then the schema bump.

Recovery dispatches (Claude Opus5.5/high): dev(types) R1 witness
`3464cbdb-2ee3-431d-b4d2-65b489026444` owns source/Cargo; design(typecheck)
`c6ce826d-38b0-4b78-b657-005c87f4937f` combines confirmed conformance repairs
with the producer design; QA `04faae41-990a-429a-8d5b-dc9bfa2a421d` reconciles
the repro deviations and classifies the separate unused-bound observation.

R1 witness passes5/5 with a discriminating fallback-only fault detected and
restored; production types source/API are unchanged. Backend schema bump is
now the sole source/Cargo reservation.

Backend dev `45baa8e2-da05-4c4f-bc6a-77bbacbd5b8a` delivered schema30;80/80
backend cache units and3/3 API guards pass. Seven schema integration cells pass;
one historical schema28 test hard-codes current29 and needs a test-only update.
QA accepts LB1/LP3 repro adjustments, with a narrow order-independent LB1 oracle
repair required. These two test repairs precede producer implementation. DB1
unused-bound enforcement remains recorded/allocated after this cache chain; it
does not gate the approved correction and is not accepted as residual.

Oracle repair test `b012466b-13d8-4dc3-935d-4639f10f9df9` completed: schema28
refusal/warm-reuse passes under live schema30; order-independent LB1 remains
RED for the expected wrong canonical identity. Backend review
`4e084c64-baf2-47f0-a31f-9a0139d7bfcd` is read-only. Typecheck dev now owns
source/Cargo for the combined §3.4 producer and §3.5 conformance fixes.

Typecheck dev session `4ff66834-720b-4135-b270-d4bf37adf992` owns source/Cargo.
Backend review passes behavior/API with one mechanical version-log correction:
schema29 is refused by the version gate, not payload decoding. Apply its exact
wording handoff at the next source-reservation boundary; no retest is required.

Typecheck dev completes:929/929 crate tests,323/323 focused conformance/macro/API
cells and189/189 remaining quasiquote/regression cells pass. LB/LP all GREEN;
public typecheck API unchanged. Collector is borrowed through the private
staging carrier to retain TypeCheckEnv auto-traits. Integration now owns
source/Cargo; typecheck review and exact as-built design reconciliation run
read-only/document-only in parallel. Backend review's mechanical wording
correction remains queued for the next source reservation boundary.

Integration dev session `87ad2a51-1498-4ed5-95e9-1ecf852cb80f`; typecheck review
`a2fe2610-2078-4e50-bbec-1e9eec4e942d`; typecheck design record
`42b9916a-e6f1-4f8d-82f6-66fbad35a765` (Claude Opus5.5/high).

Typecheck review accepts implementation with no blocker. Required record/evidence
findings: a pre-existing qualified-value early lookup defeats a broad structural
parity claim; per-family alias coverage is overstated. QA classifies these and
design narrows claims while integration continues. No automatic acceptance or
expansion into the pre-existing value-path defect is inferred.

QA bfecdb39 disposes R2 by shared-path coverage, no new module row required, and
accepts types R1 proof. R1 is narrowed to undeclared registered path-children;
(mod)-declared children have aliases. R1-V is allocated after this cache chain
with DB1; A4 is retained as a candidate hygiene lead. Design reconciles scope,
not implementation. No carry is accepted.

Integration focused1151/1151 passes including cache regressions and API guard;
the single full suite is running. Independent integration review begins on
completed source and will check final evidence/hashes.

Integration full suite:6144/6144 passed,1 skipped,213.510s. Source is functionally
verified; int report/review and final QA reconciliation remain. Typecheck scope
record 62baa7ee reconciles the undeclared-child qualification and R2 disposition.
Integration review session a4af5dd7 is active; no phase transition or commit.

Integration dev released source/Cargo; full report confirms69/69 cache cells and
6144/6144 full tests. Root applied the exact backend version-gate comment and
P4 scoped-comment handoffs after release; no behavior changed or retest needed.
Final QA session `3f8ac0ac-abf5-4ee9-9c8d-39264572e8d7` consumes evidence and
classifies integration's source-read empty-expansion publication lead.

Integration review a4af5dd7 reports no blocking or required implementation
finding. Root refreshed LD8 against the final binary (SHA recorded in the
local evidence log): all legs pass, including the exact r-unsettled deferral
trace, unchanged-source warm hit and rebuilt99/warm99 after export change.
This supersedes the earlier one-off trace's imprecise source-hash header.
Evidence: .local/s122-lookup-ld8-final-trace.log. Arch final classification
`5af21fa4-e127-4ba7-8a1c-6d1161a2cd6f` checks root-only helper signatures;
int design reconciliation `2ce8741c-f9b2-4083-8025-65682088257e` updates records.

### Lookup dependency final reconciliation — 2026-09-26

- Final QA (`3f8ac0ac-abf5-4ee9-9c8d-39264572e8d7`, Claude Opus 5.5/high) judged all allocated LD and LB/LP evidence adequate: 6144 passed, one skipped. No blocking or required review findings remain.
- Final arch (`5af21fa4-e127-4ba7-8a1c-6d1161a2cd6f`, Claude Opus 5.5/high) confirmed the approved three-line types API delta and classified the root cluster helpers as having no inter-crate consumer or additional gate.
- Design(int) record (`2ce8741c-f9b2-4083-8025-65682088257e`, Claude Opus 5.5/high) reconciled the delivered design; root applied its mechanical QA-status handoff and QA's citation correction.
- Root independently regenerated the types public API into a temporary file: byte-for-byte equality with the baseline. This supersedes the role reports' earlier regeneration limitation.
- Final-binary LD-8 replay passed every leg and observed the required deferred-entry trace; provenance and output are in `.local/s122-lookup-ld8-final-trace.log`. No executable source changed after the full run.
- Remaining user gate: confirm the generated baseline additions. This does not imply Phase-5 acceptance, commit or closure. Follow-up reproductions remain allocated in the QA plan.
- Final mechanical checks: standing-document checker 508 documents / zero findings; `git diff --check` clean; NOTES hash unchanged. The separate test-citation checker cleared the repaired LB-1 citation but still reports 18 mis-cited and five malformed citations elsewhere. These remain documentation-maintenance intake; the standing-document check does not cover them.

### Generated lookup API baseline confirmed — 2026-09-26

- User explicitly confirmed the generated baseline: exactly the three approved types additions, no removals or other baseline changes. The post-implementation API gate is satisfied. No commit, phase transition or closure is inferred.
- Citation cleanup is assigned to `test`, Claude Opus 5.5/high, session `363d7e5a-6616-4591-9fa8-ec84494704f5`: repair current test-comment destinations and report substantive mismatches, preserving executable behavior.

### Test-citation batch complete — 2026-09-26

- `test` session `363d7e5a-6616-4591-9fa8-ec84494704f5` (Claude Opus 5.5/high) repaired comments in nine test files. Root verified comment-only diffs and no changes to assertions or execution.
- Test-citation checker: 2,588 citations scanned, 2,575 valid, 13 free-form notes skipped, zero mis-cited or malformed. Standing-document checker: 508 documents, zero findings. Diff whitespace check clean; NOTES unchanged. No Cargo rerun for comment-only changes.
- Same-sprint QA intake, not accepted residuals, from the citation pass:
  - H1: `tests/facade_pif_rows.rs` pins backend DTOs whose retention is not required by current design; reconcile with arch before any public-API removal.
  - H2: `platform_repr_c_field_order_frozen` reads alphabetically ordered baseline fields and cannot detect field reordering. Only `PlatformFn` has an offset fence; the broader layout claim for `PlatformManifest` and `HostCallbacks` needs assessment.
  - H3: platform auto-trait baseline assertions will be affected by ACT-0955. Positive obligations need direct evidence when that action is implemented; negative assertions have no identified standing requirement.
  - H4: `process_form_dispatch_function_gap_does_not_speculatively_jit` uses impossible trace substrings (`JitWrite g` / `JitWrite user/g`), and its same-cluster fixture may legitimately compile `g`. QA must allocate a valid observation before test behavior changes.
- Next: QA assess this evidence basket together with the already allocated DB-1, R1-V and LD-9 reproductions. No phase transition or commit authorized.

### Checkpoint and QA batch authorized — 2026-09-26

The user approved the proposed checkpoint commit and consolidated QA batch.
The commit includes the verified lookup dependency correction and citation
cleanup; NOTES and the unpublished shared-package revision remain excluded.
QA will assess DB-1, R1-V, LD-9 and citation-pass H1–H4 together.
No phase transition, push or sprint closure is authorized.
