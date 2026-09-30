# Sprint 122: Known-issue closure and REPL-agent evaluation

**Current work:** PHASE 6a (user-facing assessment), approved 2026-09-30.
The Phase-5 fixing change-set is checkpointed; the residual carries are
approved (see "Phase-5 checkpoint approved" at the end of this plan). ACT-1030's
use-after-free guard stays failing and visible; ACT-1031 resumes that
investigation. Role models: Opus 5.5 by user authorization (see the same
section).

**Approved scope:** The user approves the consolidated K1–K11 disposition:
finish K1–K4 (missing-file diagnostic, bounded ownership evidence, record
cleanup, final verification); carry K5–K11 to S123. ACT-1015/1016/1017 remain
carried. Confirmed memory-unsafe outcomes from K2 return for an attributed
fix decision; ordinary leak findings join the runtime carry. Existing
requirements stand. No commit or phase transition is authorized.
The shared test runner is delivered and its public API
confirmed. P3/P4/P5 persistence corrections and the approved restart boundary
are implemented and have bounded QA adequacy. Structural type changes now
require restart; the live field-type crash and imported-module failed-reload
hang are fixed. The finding-scoped reload-outcome correction passed independent
review. K4 verified the previously approved scope, and its record cleanup
is complete. The subsequent ACT-1030 probe adds an unresolved memory-safety
failure outside that evidence. Whole-sprint acceptance, commit and phase
advancement remain unapproved.

Latest consumer checkpoint: `e4062202`; local shared-package checkpoint:
`c339fa7`. The checkpointed whole-file rebuild installs a fresh namespace at the
approved quiescent boundary and invalidates fully qualified dependents. It
supersedes the earlier per-definition removal and reload-demand mechanisms.
Incremental REPL behavior is preserved. Independent review found no blocking
code defect; bounded QA accepts the correction. All seven generated public-API
baselines are **+0/−0**, which needs no confirmation.

Current verification and dispositions are owned by the
[QA evidence delta](../tests/plan/s122-evidence-delta.md).
The subsequent reload and prelude corrections passed bounded checks and
independent review; ACT-1010 through ACT-1014 are closed. ACT-1015/1016/1017
are approved S123 carries. The last full run, before the new probe: 6,510
of 6,514 tests pass, with exactly
the four recorded leak failures; agent lane81/81, checkers clear, discovery
replay armed/unarmed and memory-lifecycle showcase pass. The canonical QA
record retains exact provenance and limits. Earlier full-suite results remain
historical evidence.

K2 delivers the approved primitive-wrapper, tail-forwarding and vector-COW
memory-safety corrections. The typed extern-entry convention removes the
wrapper double discharge; borrowed COW sources always retain reused boxes,
and exact-site consuming claims support transfers. QA retires the completed
filings with the fixing change-set. All seven public APIs remain +0/−0; the
cache schema value is31 to reject older machine code. Ordinary leak measurements
remain explicit failures; the sprint does not claim a green full suite.

Macro-order edge cases remain deferred to S123 or S124 under
[ACT-1005](actions/ACT-1005-macro-order-regeneration-edge-cases.md).
NOTES and the dirty shared package remain untouched.

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
| Phase 5 → Phase 6a | Delivered compiler/eval capability and evidence | 2026-09-30: “approved” in response to the checkpoint commit, carry batch and transition request | approved; in progress |
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
| Trustworthy recovery and diagnostics | The failed-turn conditions formerly tracked by ACT-0958 are positively armed (resolved); process success and recovery observations are independent; /mem's observation matches its lifetime contract | A now-successful trigger cannot stand in for failure. Diagnostic observations do not silently gate unrelated runtime behavior. |
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

This table records the opening allocation, not the current open set.
The candidate inventory and QA evidence delta own current dispositions;
0745, 0841, 0906 and ACT-0958 have since been retired.

| Closure stream | Filings allocated exactly once |
|---|---|
| Binary / integration | 0604, 0694, 0740, 0745, 0789, 0793, 0795, 0798, 0800, 0818, 0863, 0868, 0889, 0898, 0914, 0921, 0927, 0933, ACT-0958 |
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
ACT-0980 (retired 2026-09-27)
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

ACT-0983 (resolved; filing retired) retains the
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

Checkpoint `56e4d2e1` created successfully; only the excluded `.agents` gitlink
remained dirty immediately afterward. Consolidated QA is active, Claude Opus
5.5/high, session `88b7476b-ccfd-4e2f-88ba-7aaf85935d29`.

### Post-checkpoint QA allocation — 2026-09-26

QA `88b7476b-ccfd-4e2f-88ba-7aaf85935d29` (Claude Opus 5.5/high) completed
the consolidated assessment. Checkpoint evidence stands; no authority decision
is needed. The authoritative batch lives in the QA plan's post-checkpoint
section: T1–T3 reproduce DB-1/R1-V/LD-9 under explicit stop rules; T4 retires
or repairs unsupported/vacuous observations; T5 applies 14 proven fix stamps.
P-1 separately adds a platform module layout fence with a planted-swap proof.
`test` session `a2b27a40-0301-48b9-b26f-4b73d45258b9` (Claude Opus 5.5/high)
is active for T1–T5 and owns Cargo exclusively. No additional commit or phase
transition is inferred.

### Post-checkpoint reproductions — 2026-09-26

Test session `a2b27a40-0301-48b9-b26f-4b73d45258b9` completed T1–T5: 299
focused tests, 296 passed and exactly DB-1/R1-V/LD-9 failed with controls
green. All three are now reproduced defects; none hit its stop rule.
H1/H3/H4 test repairs and 14 checkpoint fix stamps are applied. Checkers
remain clean. Repros and follow-up edits are uncommitted.

Concurrent independent owners (all Claude Opus 5.5/high):
- design(typecheck) `81d2a235-afb1-43e3-952d-88002ef9731d`: DB-1 and R1-V.
- design(int) `1d1704bb-300b-480f-9f8f-c89b89fe783d`: LD-9.
- dev(platform) `3e32b086-13a3-48d8-9c88-7bae9bcfbadb`: P-1 tests and detection proof; sole source/Cargo owner.

The earlier 6144-pass result remains checkpoint evidence, not a green claim
for the current tree with these three new failing reproductions.

### Correction handoffs and interim evidence — 2026-09-26

- P-1 dev `3e32b086-13a3-48d8-9c88-7bae9bcfbadb`: 88/88 platform tests; planted field swaps failed the two new pins and were reverted. Independent review `e672096b-fc4a-4bf5-a41f-dcb133b87061`: no blocking/required findings. QA retains a pre-existing source-read manifest-by-value growth risk for classification; not a P-1 regression.
- LD-9 design `1d1704bb-300b-480f-9f8f-c89b89fe783d` and dev `60903fce-7f8d-4149-a35e-e871f2259f0f`: empty expansion dependency publication implemented; new units and unchanged LD-9 RED→GREEN. No public API/schema change.
- Int control runs exposed intermittent failures in the existing REPL restored-module rewrite and expression-turn cache tests, both with and without LD-9's decision fix. Mechanism unclassified; retain as QA intake, not an accepted residual. Logs and limits are in the int dev result.
- Typecheck design `81d2a235-afb1-43e3-952d-88002ef9731d` supplied one correction handoff for DB-1/R1-V. New source-read leads (bare-name impl matching and import/export undeclared-child lookup) remain in typecheck §11 for QA classification.
- dev(typecheck) `c63e69b9-ab30-410a-a419-19a61e93c17f` owns source/Cargo for both corrections and the final combined suite. review(int) `1ca6e576-b643-4297-9e4b-b8c877945619` independently inspects LD-9 read-only. Both Claude Opus 5.5/high.
- The two document findings seen during concurrent typecheck design writing no longer reproduce: final document checker 508 documents, zero findings.

LD-9 independent review `1ca6e576-b643-4297-9e4b-b8c877945619` found no
blocking finding and one required local correction: `OwedFacts::is_empty`
must use exhaustive field destructuring to justify its completeness claim.
Schedule it with dev(src) after typecheck releases source/Cargo. Review also
retains the controlled REPL flakes for QA attribution and a source-read
module-level unresolved-dispatch overwrite lifecycle lead for design(int).
No new authority decision is required.

### Typecheck correction delivered for review — 2026-09-26

DB-1/R1-V developer `c63e69b9-ab30-410a-a419-19a61e93c17f` released source:
939/939 crate tests and both independent reproductions pass. Combined full
workspace: 6161 run, 6158 passed, three failed, one skipped. Failures are the
known intermittent REPL cache rewrite, a plan citation to the removed plural
lookup helper, and an older `super` trait fixture with no required Int impl.
The fixture attribution awaits QA; do not silently weaken the new check.

Active Claude Opus5.5/high roles:
- review(typecheck) `3881f1fc-c131-4d86-a9b1-9eee3a3f7bf1`, read-only.
- dev(src) `e5936a0e-c1ce-40dd-93d6-a1b14af1834a`, sole source/Cargo owner for cache R-1 only.
- QA `317e68cb-54e4-4fe3-84c4-7e94eb9bbdca`, completed-evidence and new-lead classification.

### QA intake completed — 2026-09-26

QA `317e68cb-54e4-4fe3-84c4-7e94eb9bbdca` closed P-1 as adequate and
judged T1–T5 as allocated. LD-9 adequacy waits only on R-1 review; the exact
exhaustive-destructure correction is now delivered with 5/5 focused checks.

Canonical new-lead dispositions are in the QA plan batch-intake section:
RR-1 is a confirmed intermittent REPL cache restore symptom (provisional
shared-state-write-race), with a discriminating reproduction allocated; IR-1
and BN-1 remain source-read lookup/impl-identity leads with RED-first cells
allocated. PM-1 is the out-of-tree newer manifest growth risk, disposition
asked of the user (future release action versus investigation now). A-3
unresolved-dispatch overwrite remains a future lifecycle question. None is
accepted as a residual.

QA added cross-cluster DB-1 solution legs X1/X2 and two positive module
controls. These arrived after typecheck implementation and are outstanding
evidence handoffs, not failures of the completed module run.

### Independent review reconciliation — 2026-09-26

- review(typecheck) `3881f1fc-c131-4d86-a9b1-9eee3a3f7bf1` found no implementation correctness defect. Required: RQ-1 late QA positive module cells, RQ-2 invalid older fixture repair, RQ-3 current design reconciliation. RQ-1 arrived after the dev brief, so it remains a follow-up evidence allocation.
- dev(src) R-1 `e5936a0e-c1ce-40dd-93d6-a1b14af1834a` added exhaustive destructuring, passed 5/5 focused checks and demonstrated E0027 with a planted field/control. re-review `112b35ff-a9f0-4bd1-bde8-7c129eba05fe` resolved R-1 with no new finding. Root applied its exact mechanical grade/status handoff.
- test `c85f0d6d-093c-48c6-b20d-0e6d6c1dd45c` owns source/Cargo for QA's follow-up batch and the fixture contrast; design(typecheck) `779a44c3-9915-4e0c-8317-8b6329fdc5b2` owns RQ-3 records. All roles Claude Opus5.5/high.
- PM-1 user scope question remains pending; no ABI redesign started.

### Follow-up reproductions and review point — 2026-09-26

Test `c85f0d6d-093c-48c6-b20d-0e6d6c1dd45c` finished the allocated batch:
- DB-1 all six solution legs pass; the super-import fixture's missing-impl contrast establishes its omission and the repaired fixture passes. RQ-2 is implemented; stale inline D4 wording remains to verify in final review.
- IR-1 is RED for both undeclared-child import/export subjects, with declared-child controls GREEN.
- BN-1 is RED: the same-named foreign impl passes typechecking and fails in codegen; distinct-name control correctly gives a type error.
- RR-1 now has a partial reduction and traced controls. Face (i) is supported by traces showing cached `a` failed before callee `c` registration; the `c`-first control removes that face. Face (ii) is SIGSEGV and persists at a lower rate with `c` loaded first, so the sole-mechanism hypothesis is refuted for it. Buffered traces do not survive the signal. QA attribution is needed before a correction.
- Focused final: 18 run, 14 passed, four failed (IR-1, BN-1, RR-1 partial reduction and one older RR-1 session cell). These are open defects, not accepted residuals.
- The v11 pin comment is repaired; citation/document checks remain clear. No new commit.

RQ-1 late positive module evidence is assigned to dev(typecheck)
`5a3eb644-6eb1-42bb-a4c6-95137c54148c`, Claude Opus5.5/high, sole source/Cargo
owner. This completes the original correction evidence before returning the
new findings basket for prioritisation; no additional compiler repair is
started for IR-1/BN-1/RR-1 in this step. PM-1 scope question is still pending.

### Correction basket returned for prioritisation — 2026-09-26

- RQ-1 dev `5a3eb644-6eb1-42bb-a4c6-95137c54148c`: multi-signature positive cell added; 940/940 typecheck tests. HKT cell followed the stop rule.
- Finding-scoped review `9396def4-6b94-4fbc-8c7d-7450eb2d006b`: RQ-1/RQ-2 resolved, no required review findings. Root applied the exact mechanical record handoffs and reduced AD-7's obsolete fixture narrative.
- Closing QA `040ca06d-684b-4b0c-8c21-c05004f09242`: R1-V, LD-9, P-1 adequate; fixture attribution closed; HKT stop rule accepted. DB-1 needs one permanent clause-rejection module cell (AD-6), using the already observed mutant evidence; no new mutant run needed.
- Next planned repair work returns for prioritisation: finish AD-6, fix RR-1 face (i), then measure face (ii)'s remaining SIGSEGV rate before choosing further observation tools; IR-1 and BN-1 also remain Phase5 defects. No residual is accepted. HKT annotation meaning requires spec/user framing separately. PM-1 scope question remains unanswered.
- No further implementation is running. No post-checkpoint commit was made. Before another commit, QA requires one full suite with only the named IR-1/BN-1/RR-1 REDs allowed. Current evidence is the recorded full run plus later focused checks, not a fully green current workspace.

### User priority and DLL protocol disposition — 2026-09-27

The user directs prioritising the REPL crash (RR-1) now. The version-alignment
protocol is deferred to a future sprint in
[ACT-0993](actions/ACT-0993-platform-dll-version-alignment-protocol.md).
This resolves the PM-1 scope question; no ABI implementation is authorised.

RR-1 work proceeds from the established face-(i) evidence and then remeasures
face (ii), without claiming one mechanism explains both. AD-6, IR-1, BN-1 and
the HKT question remain recorded; they do not take priority over this crash.
No commit, phase transition or sprint closure is inferred.

RR-1 design(int) is active on Claude Opus5.5/high, session
`d68580dd-5761-41b2-96c7-0c7c2b10fcab`. No source/Cargo writer is active.

### RR-1 implementation underway — 2026-09-27

Design(int) `d68580dd-5761-41b2-96c7-0c7c2b10fcab` completed the private
restore-before-load / exclusive-claim design in int §7.1. It covers attributed
face(i) and the recogniser bypass; face(ii) remains separate with a source-read
readiness-wait hypothesis and existing `/run-tests` control suggestion. No
public API/schema change or true blocker is reported.

Active Claude Opus5.5/high roles:
- dev(src) `a1756824-300c-4d31-aa48-4e22560d6917`, sole source/Cargo owner.
- QA `fe90700c-fa27-4f3f-8469-2ac57d69aba3`, post-fix measurement allocation.

Independent implementation review will cover the design obligations against
the delivered source. Post-fix stress/control measurements belong to test
under QA's allocation. No unrelated defect correction is started.

### Defensive debugging context — 2026-09-27

The user clarified that RR-1 work is authorised defensive debugging of our
own compiler. Handoffs must state repository ownership, local synthetic
fixtures and the objective of fixing memory-safety failures. Reproduction,
traces and debugger observations serve diagnosis and regression prevention;
no exploitation, third-party targeting or weakening of security protections
is requested.

### RR-1 post-fix investigation — 2026-09-27

Dev(src) and QA have completed and released their surfaces. The cache-load
correction passed 225 scoped module tests; the final workspace run was
6172 passed, 3 failed, 1 skipped. RR-1 still failed in 3 of 20 sessions, all
SIGSEGV with no unresolved-symbol output. BN-1 and IR-1 are the other known
failures. These results do not close RR-1.

Active Claude Opus5.5/high roles, under the existing user allocation:
- test `e2f4192e-76df-4250-a1b3-f3a411c93ce3`, sole tests/cache.rs and Cargo
  owner, executing [QA's allocation](../tests/plan/s122-evidence-delta.md#rr-1-correction--evidence-allocation-2026-09-27).
- review(src) `badf3398-9c32-4ec3-8b04-29f101b11fde`, independent read-only
  inspection of the delivered cache-load correction.

Both briefs include the user's defensive-debugging context. No commit,
phase transition or unrelated correction is authorised by this dispatch.

### RR-1 controls completed; readiness correction — 2026-09-27

Test and review completed. E-1/E-2 observed zero unresolved-symbol failures
in 1000 subject sessions and 1000 callee-first sessions; the rewrite cell
passed 30/30. The remaining SIGSEGV appeared in 51/1000 subject sessions.
C-1 observed 0/1000 crashes with explicit readiness waits versus 31/1000
with two non-waiting control turns. No hangs or other failures occurred.
The permanent test keeps its failure predicate and now classifies failures.
Temporary controls were removed; tests and Cargo are released.

Review identified a recogniser-load panic path that can strand its claim,
and an overstated assurance claim about every loader taking a claim. These
join the readiness correction in one source visit; unconfirmed adjacent
leads remain QA intake. No crash closure is claimed.

Active Claude Opus5.5/high roles:
- QA `0f6b062f-61fa-4f02-965e-52f1cf9c2979`, attribution, adequacy and the
  next evidence delta in the existing QA plan.
- design(int) `aa1c5e2f-cb79-4cdf-ad6c-157965eb7aeb`, the bounded readiness
  correction and review findings. Their settled handoffs precede dev.

### RR-1 readiness design delivered — 2026-09-27

QA confirmed the readiness-race attribution and previous stress counts.
Design(int) completed the private cached-load readiness wait and scheduler
claim ownership design in [int §7.1](../design/int/int.md#71-cache-hit-flow-inside-register_module).
The wait precedes REPL code execution and test discovery. A failed cached
load refuses subsequent code-running steps until re-registration or restart;
this conservative global effect was surfaced to the user. No public API,
cache schema or ABI change is proposed.

QA `ff30a23f-0a11-466e-9e96-3ecaffef3ce3` (Claude Opus5.5/high) is reconciling
one evidence substitution for the new wait seam before dev starts. The
existing observed crash baseline is retained. Design exclusions remain open
QA intake, not accepted residuals. All source and Cargo are currently free.

QA reconciliation is **READY**: the existing e2e baseline is reused, and
new wait rows are proven by bounded planted faults. Two temporary, reverted
compile errors establish the claim/readiness construction checks; no
committed compile-fail suite is added. No user decision blocks the fix.

Dev(src) `7b9c18b9-025c-4165-81a4-df831b72eb36` (Claude Opus5.5/high) now owns
source/module tests and Cargo for the readiness and claim-lifetime repair.
Independent test will run the settled stress allocation after source release.
No other implementation stream is active.

### RR-1 implementation complete; independent verification — 2026-09-27

Dev(src) `7b9c18b9-025c-4165-81a4-df831b72eb36` completed and released
source/Cargo. All allocated scheduler rows pass, with the wait/claim-drop
faults and constructor compile-error observations detected and reverted.
The library tier passed 854/854; the full suite passed 6182/6184 with
1 skipped. Only BN-1 and IR-1 remained RED; RR-1 and the expression-turn
cache regression passed. No public API/schema/ABI change.

Active Claude Opus5.5/high roles:
- test `0de985bd-fd7c-4fe7-8887-a5d7c8cfb089`, sole tests/cache.rs and
  Cargo owner, adding S-2 and executing A-RC plus the final full suite.
- review(src) `48d1c4bc-fb9c-4e16-9c9a-7239080fde15`, finding-scoped
  independent review of readiness, R-1/R-2 and implementation refinements.

The single green RR-1 run is not statistical closure; QA adequacy follows
independent results. All changes remain uncommitted.

### RR-1 verification delivered — 2026-09-27

Independent A-RC passed all 2000 sessions (1000 original, 1000 callee-first),
with zero unresolved symbols, signals, hangs or other failures. E-2 passed
all 72 cache tests in each of 30 iterations; expression-turn and rewrite
cells passed 30/30. The final full suite, including permanent S-2, passed
6183/6185 with 1 skipped. Only the known BN-1 and IR-1 failures remain.

Review closed R-1/R-2 structurally with no blocking implementation finding.
FR-1/FR-2 exact mechanical design handoffs are applied; FR-1's scheduler
doc comment was corrected after test released source/Cargo. This changed
no executable behavior. The failure-refusal record now acknowledges existing
failed-module resets, rather than promising refusal until re-registration.

QA `ce806cb9-4649-464d-b3cc-936935eed6fb` (Claude Opus5.5/high) owns the final
adequacy judgment, test evidence/traceability and FA-1 intake classification.
FA-1 concerns an unobserved stale claim during watcher re-registration.
No residual has been accepted and no commit or phase transition is inferred.

### RR-1 evidence adequate — 2026-09-27

QA `ce806cb9-4649-464d-b3cc-936935eed6fb` judged the bounded RR-1 repair
**adequate**, with no blocker. A-RC, F-1, U-RC/U-R1, S-2 and M-2 are met;
source review is complete and its mechanical record repairs are applied.
QA updated §14.7's traceability for both permanent regressions. Final
verification remains 2000/2000 REPL sessions and 6183 passed, 2 known failures,
1 skipped in the workspace. No production code changed after that evidence;
only FR-1's source documentation comment was corrected.

[ACT-0994](actions/ACT-0994-cached-load-claim-reregistration-intake.md) retains
FA-1 as open QA intake. The five design exclusions remain open and unaccepted.
The four pre-existing cleared-coverage rows in `spec/10-io.md` and
`spec/appendix-a-builtins.md` still need QA disposition before sprint close.
BN-1, IR-1 and the earlier AD-6 requirement remain outside this crash repair.
PM-1 remains deferred under ACT-0993.

No commit, phase transition or sprint closure has occurred. On committing
the correction, append the commit sha to both RR-1 `fixed=S122` stamps.
The user has not yet accepted Phase 5.

### Checkpoint and remaining correction batch authorised — 2026-09-27

The user approved the proposed checkpoint commit, then BN-1 and IR-1
correction, AD-6's missing multi-signature rejection evidence, and QA
disposition of the four cleared-coverage annotations. This continues Phase 5;
its acceptance and the next phase still require a separate checkpoint.

The checkpoint reuses the final RR-1 full-suite and stress evidence above:
only record/comment changes followed those runs. Keep `.agents` and NOTES
out of the commit. Continue Claude Opus5.5/high for subordinate roles, with
one source/Cargo owner at a time. DLL version alignment stays deferred;
ACT-0994 remains open intake outside the selected correction batch.

### Checkpoint 236aa44d and final correction batch — 2026-09-27

Committed the verified correction basket at `236aa44d` (47 files), including
RR-1, declared-bound settlement, resolution and coverage repairs, and
ACT-0993/ACT-0994. `.agents` and NOTES were excluded. No push. The retained
RED guards are BN-1 and IR-1; their correction is now active.

Active Claude Opus5.5/high roles, with separate document reservations:
- design(typecheck) `8d1dacd6-d4c9-4ba6-b6a0-7cabd50f9659`: BN-1 design and
  AD-6 grouping; `design/typecheck/`.
- design(int) `76ea9a99-d1f0-4ed0-b06c-7f794400d391`: IR-1 design;
  `design/int/`.
- QA `ae57ef46-5f82-4699-80eb-cf0317a3bc98`: one evidence delta, four
  cleared-coverage rows and final test-side maintenance.

No source/Cargo writer is active. Implementation follows settled per-surface
handoffs serially. RR-1's `fixed=` sha is `236aa44d`; test owns stamping it
in the final maintenance visit.

Both designs are ready and private: typecheck §9.1.1 (BN-1) and int §6.9
(IR-1). QA's final-basket allocation retains the existing RED evidence,
adds IR-o's root-first/alias legs and DT-1, and replays RR-1 E-1 beside the
import-loading change. One final workspace run follows both source visits.

ACT-0989 joins the BN-1 visit: source verified in `checker.rs` and its
callers on 2026-09-27, its four bare-name helpers have only test consumers.
The existing action's test-only change belongs to the same lookup-function
family that BN-1 changes; no public API or new language behavior is added.

QA `ae57ef46-5f82-4699-80eb-cf0317a3bc98` completed the reconciled delta
with no handoff blocker. The §10.12.8 coverage row is restored. Disconnect
and shutdown rows remain explicitly uncovered under ACT-0977 and must be
presented as carries at close; no new platform capability is selected.
Appendix A awaits DT-1; its warning and link-mode clauses remain separately
open. No normative requirement changed.

Dev(typecheck) `cdea72ee-d086-4ecb-b039-b457cc6b3f14` (Opus5.5/high) owns
source/Cargo for BN-1, AD-6 and ACT-0989. A read-only spec clarification
checks whether existing requirements already settle IR-1's separate-REPL-turn
question; it does not authorize new behavior or block this correction.

### Remaining corrections in implementation and review — 2026-09-27

BN-1, AD-6 and ACT-0989 are implemented; dev(typecheck) released source/Cargo.
All 948 typecheck tests pass, BN-1's permanent regression is green, and IR-1
is the only remaining failure in the focused run. Independent review and
the final integrated evidence are pending.

- dev(src) `f313251e-660c-46b6-b1ec-9a5610f885e4` owns IR-1 and Cargo.
- review(typecheck) `c8e9ded8-6a49-46ef-9844-d360b80288d2` independently
  assesses BN-1, AD-6 and ACT-0989 read-only, without Cargo.
- Both use Claude Opus5.5/high. Final test and QA follow source release.

The user explicitly deferred the later-REPL-turn child declaration question
to the next increment: [ACT-0995](actions/ACT-0995-repl-later-submodule-declaration-resolution.md).
No behavior was selected for that case. Same-cluster IR-1 continues.

Review(typecheck) found no blocking implementation issue and confirmed BN-s
and ACT-0989. Its mechanical design and QA citation repairs are applied;
the standing-document checker reports 510 documents and zero findings.
The allocated test-stamp repair remains in T-F. Advisory design leads are
retained in typecheck §9.1.1; they do not authorize additional source work.

IR-1 is implemented and source/Cargo released. Its crate run passed 3383
tests with one skipped; the sole failure was the document check's two
references to the deleted resolver. Those mechanical references are repaired.
All compiler-behavior tests, including the original IR-1 regression, passed.

- test `2ef62c92-3110-45d9-a1c2-3a78c84e8699` owns T-F and Cargo.
- review(src) `f5354351-99ce-43a1-9e01-23bf3e42c054` is read-only.
- Both use Claude Opus5.5/high. Final QA follows their completed evidence.

Review(src) completed with no blocking or required finding. Its mechanical
status handoffs and the source-memory wording correction are applied.
IR-o and the REPL discovery legs pass; DT-1's named-module `--run` leg is
retained RED (zero rather than three). Test is completing the full suite;
the allocated RR-1 replay passed all 800 sessions with no failure.

QA `49af91e8-246e-43e8-acd0-dbe809ef867a` (Claude Opus5.5/high) assesses
the completed evidence and discovery authority concurrently, without Cargo.
Its final judgment must use the completed test report. Review A4/L1/L2
join its intake; no new runtime work or semantic choice is authorized.

Final test released tests/Cargo: 6201 run, 6200 passed, one failed (DT-1
under `--run`), one skipped. BN-1, IR-1 with both IR-o legs, AD-6 and all
72 cache tests pass. The 800-session RR-1 replay has zero failures. Public
API relocation checks pass; no API, schema or ABI change occurred. Reference
checks report no mis-citations, unresolved citations or document findings.
Appendix A's discovery row remains cleared pending QA's requirement judgment.
No executable source changed during or after these runs.

Final QA judges BN-1, IR-1 and AD-6 adequate; the discovery defect does not
trace to their changes. Coverage bands are reconciled: 893 live citations,
zero unresolved or cleared-awaiting-QA rows, and zero document findings.
Discovery remains explicitly partial, with its RED and open clauses named.

DT-1 returns an empty vector silently under `--run`. QA finds this conforms
to neither the current discovery text nor the user-approved direction of an
explicit test harness and release-like `--run`. On 2026-09-27 the user approved
handling the remedy with ACT-0988 while retaining the RED under ACT-0986.
The rationale is to avoid adding temporary discovery capability to ordinary
`--run` before the explicit harness boundary is implemented. This specific
carry changes no semantics and approves no other residual. No phase
transition or further commit is inferred.

Mechanical review repairs are complete, including BN-1 AD-d's duplicated
fixture comment and IR-1 A2's memory wording. The related unobserved
declaration-lifetime question is retained beside ACT-0995 without extending
its approved deferral. Other advisory review leads remain in the owning
design or QA record, without approval to expand implementation.

### Checkpoint and whole-sprint acceptance reconciliation authorised — 2026-09-27

The user approved committing the verified BN-1/IR-1 correction batch and
recorded carries, excluding `.agents` and NOTES, then reconciling the whole
sprint's Phase 5 acceptance position. Reuse the completed full-suite and
stress evidence: only records changed afterward. The reconciliation must
separate delivered outcomes, approved carries, unresolved obligations and
work belonging to the later user-facing phases. This is not approval to
advance to Phase 6a, close the sprint or push.

Checkpoint `0272a5d9` commits 47 files for the verified correction batch and
approved carries. `.agents` and NOTES were excluded. The 28 changed Rust
source/test inputs match the final suite's recorded hashes. BN-1 and IR-1
regression stamps now name this fixing commit; only comments changed.

QA `c9e0e0c9-a21d-4313-87ca-c87b9a00482b` (Claude Opus5.5/high) owns the
whole-sprint Phase 5 reconciliation in `tests/plan/`, with no Cargo or source
changes. This extends the acceptance assessment across the included sprint
outcomes; it does not repeat the completed implementation reviews.

QA completed the reconciliation and released its reservations. All delivered
compiler corrections have adequate evidence at the checkpoint; Phase 5 as a
whole is not yet ready for acceptance. The canonical QA section above owns
gates G-1–G-7, the inventory dispositions and the proposed T1–T4 test visit.
The proposed visit groups persistence cases on one surface and refreshes the
offline agent lane without another paid model run. It includes no production
fix or semantic decision. T5, platform function-signature rejection evidence,
remains an optional addition. Unapproved carries remain open; later-phase
work stays at its declared checkpoint.

### Grouped acceptance verification authorised — 2026-09-27

The user's “proceed” authorises QA's T1–T4 visit: offline agent verification,
macro replacement persistence, accessor/impl overlap, and warm-cache authored
declaration preservation. T5 is not selected. One test role owns Cargo and test
sources; no production fixes, live-model run, commit or phase transition is
included. Claude Opus 5.5/high follows the user's persistent model allocation.
QA will assess the completed evidence before confirmed defects return for
individual decisions.

Test session `74921814-d0e4-48db-a061-f5c76557965f`, agent
`40d6b7c8-073e-4ca9-8e45-e8e3309c3558`, holds that reservation.

Test completed T1–T4 and released Cargo/test sources. Offline checks pass
81/81 (agent lane), 137/137 (agent modules), 18/18 (eval self-check).
Focused evidence is four failing subjects and four passing controls: macro
persistence, accessor/impl overlap, warm-cache declaration preservation,
and a separately isolated qualified trait-call failure discovered by T3's
first control. Production source is unchanged. QA now assesses attribution,
the adjusted control and the equivalent agent invocation, and reconciles
owned evidence. Two stale test-name citations require mechanical repair.

QA session `30557f17-82d2-4d8a-806f-5f66b2707a23`, agent
`727f58f2-9acd-4251-adb4-fa46007eba4c` (Claude Opus 5.5/high), completed
assessment and released its reservations. The
[assessed T1–T4 evidence](../tests/plan/s122-evidence-delta.md#acceptance-verification-t1t4-2026-09-27)
satisfies G-1 and confirms G-2/G-3/G-4/G-7. The equivalent isolated agent
invocation is adequate; no repeat is needed. Exact QA handoffs repair defect
comments and the stale design citation, without executable changes.

The next proposed decision is repair of authored-source loss (ACT-0980), with
the related macro-persistence defect (ACT-0970) grouped into the same src
implementation visit if both fixes are selected. Integration design must settle
the restoration approach first; any public-API or schema change returns to its
existing approval gate. Typecheck owns the other two failures (ACT-0983 and
ACT-0996); they remain open for subsequent disposition. No carry, fix, commit
or phase transition is inferred from the verification approval.

After mechanical handoffs, the document checker passes (511 documents, zero
findings), all three citation-drift tests pass, and both traceability checkers
report zero unresolved or malformed citations. NOTES retains its prior hash;
no production source changed and no commit was made in this visit.

### Persistence repairs authorised — 2026-09-27

The user's “ye” approves repairing ACT-0980 and ACT-0970 together, following
the presented recommendation. Integration design settles declaration
restoration, then one src implementation visit repairs both failures, with
focused regression evidence, independent review and QA adequacy. Existing
public-API/schema approval gates still apply. The trait defects remain outside
this repair batch; no commit, push or phase transition is authorised.

Design(int) session `e2c47cf1-1cab-4884-8337-133655bf281e`, agent
`3b51cf08-159b-47d3-810a-760b722cfc39` (Claude Opus 5.5/high), owns
the bounded restoration design; no source or Cargo reservation is active.

Design(int) completed a private restoration approach in the existing
persistence design: no public API, cache schema or consumer-edge change.
A missing renderable entry prevents overwriting the backing file and emits a
save warning. QA assesses that material evidence delta and the cold-load face
before implementation. Spec independently reconciles the pre-existing §15.4
rule 6 metadata wording; no normative change is approved. Design's additional
source-read leads remain unconfirmed intake, not expanded repair scope.

Readiness QA `b5cd740d-28f4-4705-96a0-ffa0536c85b8` owns the evidence
delta; spec `8e8d9a26-3aca-411d-aa84-96c2bc34c22c` is read-only on rule 6.
Dev(src) `8e37eea9-aa6c-4588-ac5b-97199edd6e62` owns src/module tests and
Cargo, proceeding from established REDs and the completed private design.
All use Claude Opus 5.5/high. The independent test visit and one full suite
follow release of the source reservation; no concurrent Cargo owner exists.

Dev completed both private fixes: 19/19 focused module cells, 873/873 library
tests and 247/247 neighboring e2e tests pass; zero new clippy warnings. Source
and Cargo are released. Test `4dd16de5-700f-4099-80c3-e7f3c7de6bde` now owns
Cargo and final e2e evidence. PC-1 uses a preserved compiler with the prior
QA binary's identical SHA-256 to establish pre-fix behavior after compilation
of the new test; no source reversion or concurrent build is needed. The full
suite is run once after this change. Independent review is read-only.

Spec found a conflict between the S52 cache-source requirement and later
user-ratified D1/S81 rehydration. The user requested background on the proposed
cache-independence replacement; no wording approval has been given. The repair
is neutral to that pre-existing open requirement, which remains unclaimed.

The first test session's transport wait ended before Cargo release; test
`afb52b8f-95e7-4a48-8e39-0267bcc5eb9b` completed the remaining visit.
The coordinator executed its exact direct-test pre-fix command against the
retained compiler: PC-1 and T4 fail with lost declarations, while the 0220
control passes. This fills the provider-permission execution gap without
source changes or another build. PC-1/T2/T4 and controls pass post-fix.

The full run reports 6222 run, 6218 passed, four failed, one skipped: the
three open trait/discovery guards plus a stale QA citation, now repaired.
The coordinator also ran the literal offline agent launcher: 81/81 pass.

Review `95312c70-f526-4b1a-a8eb-486d746df1fc` raised F1–F3/A1 for
classification. QA `6cd4722e-31f8-4da3-8264-d776cdc167ce` supplied a
bounded before/after probe basket, executed by the coordinator. F1's import
renames and F3's watcher reload fail their preconditions on both binaries;
they do not confirm the predicted regression. F2 duplicates a mixed-section
begin but restores its tested values; pre-fix file loading lost them. A1
agrees across both binaries. QA `e8f155f5-8ec9-4b1f-8c45-c37e5f65f46b`
finalises those observed classifications and the selected-fix adequacy.
All roles remain Claude Opus 5.5/high. No source change followed the full run.

Final QA accepts the two selected persistence corrections and retires
ACT-0970 and ACT-0980. F1 is unreachable until import renames work; ACT-0997
retains that gap and the future identity obligation. F3's predicted successful
reload path was not reached; ACT-0998 retains the existing failed-reload and
source-overwrite observations. A1 agrees across pre/post binaries. Exact
mechanical F1/F3 design-record corrections are applied.

F2 remains an observed, bounded duplicate of a begin spanning declaration
sections; its tested types and values round-trip after the repair. Fix or
carry remains a user choice, not a blocker to the selected correction's
adequacy and not an approved carry. Other G-8 residuals stay explicit in
QA's evidence carrier. Rule 6 wording still awaits the user's decision.
No commit, phase transition or publication has occurred.

Final mechanical verification: 511 documents, zero findings; citation-drift
3/3 pass; 2589 valid test-to-spec citations, zero malformed/mis-cited;
898 live spec-to-test citations, zero unresolved or awaiting QA. NOTES is
unchanged. No role or Cargo reservation remains active.

### Cache-independence requirement approved — 2026-09-27

The user's “yes” approves replacing REPL §15.4 rule 6 with: “Cache
independence: Rules 1–4 MUST hold whether the module's current definitions
were compiled from source or restored from the object cache (§14.7).”
This removes the source-in-cache-metadata obligation; it does not establish
coverage of every regeneration invariant. Spec applies the exact wording,
then QA reassesses the coverage band using existing evidence. Other G-8
residuals, F2 fix/carry, commit and phase transition remain undecided.

Spec `c86f33e5-04ab-4d43-b20b-0276169b4e38` applied the approved sentence
verbatim. Its exact mechanical design handoff is applied. QA
`58ba60ae-a506-405f-abed-a1e715ae9ef3` reassesses only the rule 6 and section
coverage band and stale QA status. Both roles use Claude Opus 5.5/high.
No production code or test execution changes are needed for this wording edit.

The approved rule 6 wording and matching design sentence are applied. QA
marks rule 6 and the §15.4 summary partial: existing evidence covers
round-trip correctness on both source and cache paths; rules 2–4 have no
allocated ordering/qualification/structural-order observations. That coverage
gap remains in G-8; the normative wording decision is settled. Document and
traceability checks pass, with 511 documents and zero findings. No code
changed, no tests reran, no commit occurred, and role reservations are released.

### Mixed-section begin repair approved — 2026-09-27

The user's “continue” approves fixing F2 now: emit one authored begin once
across declaration sections. PC-8 supplies REPL-entered and file-loaded
regressions, then dev repairs the private save path under the existing §1.4
design. Focused validation, independent finding-scoped review and QA follow.
No API/schema change, trait repair, commit or phase transition is included.

Test `e088d4c3-8c46-489a-bb6a-9f78dd93cf82` (Claude Opus 5.5/high)
established both PC-8 legs RED at exactly two copies, with both sibling
controls passing. It released tests and Cargo. Dev(src) now takes the private
section-composition repair, preserving previous fixes and their evidence.

Dev(src) `c597de34-ffd4-48e9-8a9d-a54c3607907f` completed the private
save correction. PC-8 and its controls pass 4/4; persistence passes 43/43;
save module tests pass 60/60. The final-source full run has 6226 tests:
6223 pass, the three known ACT-0983/ACT-0996/DT-1 failures remain, and one
is skipped. Source and Cargo are released.

Independent review(src) `0c3706fa-346b-451d-8c91-8cd1aba674d8` reports no
blocking or required finding. Its evidence advisory, authored-identity lead
and pre-existing macro-ordering lead go to QA for classification. QA
`3aceb6c8-db63-4aea-959c-866f04c96a22` assesses PC-8 adequacy and updates
its current evidence carrier. All three roles use Claude Opus 5.5/high.

QA accepts PC-8: F2 is corrected and the evidence is adequate. The coordinator
executed QA's exact diagnostic basket after its host refused binary execution.
All 28 sessions completed: four broader begin shapes save once and round-trip;
the two macro-ordering examples reload; the generated-name example loses no
type. QA's conditional handoff closes those leads without another role visit.
The evidence carrier and QA-owned §15.4 coverage annotation are updated
mechanically. Existing unrelated residuals remain; no new carry is introduced.
All role and Cargo reservations are released. No commit or phase transition.

### Trait correction batch approved — 2026-09-27

The user's “continue” approves the proposed combined ACT-0983/ACT-0996
correction: accessor-named impl methods and qualified trait-method calls.
The T3/G-7 QA allocation and existing independent REDs govern the batch.
Dev(typecheck) owns private implementation and module evidence; test completes
the allocated ambiguity negative after registration works. One final full
run, independent review and QA adequacy follow. No public API/schema change,
commit or phase transition is included.

Dev(typecheck) `fb8de8e0-d7d3-43f9-832e-c5c90d664da7` established seven
module REDs with two green controls, then corrected both defects privately.
The nine focused cells, 950 crate tests, 308 nearby acceptance tests and 285
additional dispatch checks pass. Its exact stale-design removals are applied.
Source and Cargo are released. Review(typecheck)
`c66ea8fd-5a4e-47a0-b810-621ca71bf2de` inspects independently; test
`0bbfcfd7-6f72-40a9-ad76-c6e6f33fecfd` owns the remaining ambiguity negative,
test comment/format upkeep and the final full run. All use Claude Opus 5.5/high.

Review reports no source blocker. Its stale-design finding R1 is corrected,
including the extra open-item bullet; document checks return to 511/0.
The test visit adds the allocated ambiguous bare-use negative and records
seven focused passes. Final full run: 6229 run, 6228 pass, one known DT-1
failure, one skipped. Source/test hashes are recorded and no source changed
after that run. Test and Cargo are released.

QA `52f70ea7-da85-474a-bec6-af71f7cb816b` (Claude Opus 5.5/high) assesses
adequacy and classifies review R2 (qualified return-type dispatch) and A2
(mode/module qualification coverage). These are observations awaiting
classification, not approved carries or automatic additions to fix scope.

QA accepts and retires ACT-0983. ACT-0996's REPL/module evidence is adequate;
its final mode observation awaits correction of an invalid stdlib fixture.
The coordinator executed the bounded basket: ordinary user-trait batch calls
and module-qualified calls pass. R2 is confirmed: unpinned qualified nullary
calls report an internal codegen error while bare calls report type ambiguity;
pinned controls pass. Per QA's conditional handoff, ACT-0999 retains the
observation. Test `cb5d2d19-8c68-45d6-938e-513a7c61be3f` (Claude Opus
5.5/high) records its RED/control pair and resolves the observer fixture.
No fix or carry of ACT-0999 is presumed.

The corrected A2-R fixture passes through the test harness (batch exit 10),
so QA's conditional handoff retires ACT-0996. Both original trait corrections
are complete. ACT-0999 now has a permanent failing, unignored ambiguity
subject and passing pinned control; the two corrected call controls pass in
the same targeted run (3 pass, 1 intended failure). This addition followed
the full-suite measurement above; no production source changed.

The probe also isolated imported-trait dotted lookup as a separate observation;
ACT-1000 retains it for QA classification. It is not an approved carry or
fix. ACT-0999's fix/defer decision returns to the user. All roles and Cargo
are released. No commit or phase transition occurred; NOTES remains untouched.

### Qualified return-dispatch correction approved — 2026-09-27

The user's “ok” approves fixing ACT-0999 now: qualified unresolved
return-polymorphic calls must report the specified type ambiguity, while
explicitly typed calls continue to dispatch. Existing RED/control evidence
and QA's R2 handoff govern the private typechecker correction. Dev module
evidence, focused/full validation, finding-scoped review and QA adequacy
follow. ACT-1000 remains separate intake; no public API/schema change,
commit or phase transition is approved.

Dev(typecheck) `c05fc487-39e3-45d3-9191-d1e4dc4f975e` confirms the mechanism
with module REDs and corrects the three ambiguity gates privately. Crate
953/953 and nearby acceptance 397/397 pass. Full run: 6234 run, 6233 pass,
one known DT-1 failure, one skipped; two passing search tests have nextest
LEAK markers for QA classification. Source and Cargo are released.
Review(typecheck) `aaad9245-e452-489c-8099-29b674a23fb1` performs the
finding-scoped inspection. Both roles use Claude Opus 5.5/high.

The coordinator replayed the existing QA batch observer in fresh disposable
directories: bare and qualified unpinned calls both produce located §3.11
ambiguity errors (exit 1), and the pinned qualified case exits 7. The dev's
exact mechanical traits-design wording update is applied. No production
source changed after the full run.

Finding-scoped review finds the correction sound with no source blocker.
Its required design-record correction is applied; test defect framing awaits
QA retirement. QA `796e8b2d-6675-42d0-90d4-462e98376720` (Claude Opus
5.5/high) assesses adequacy, the review's advisories and the two nextest
process-output flags. No broader implementation is dispatched.

QA accepts ACT-0999 and retires its filing. The required comment-only test
framing and `fixed=S122` stamp are applied mechanically; a commit SHA awaits
commit authorization. No source behavior changed after the full run.
The nextest flags did not recur in a focused 3/3 run and are diagnostic only.
Review's HKT fallback lead remains in QA's existing same-named-trait coverage
gap; no defect, carry or extra implementation is presumed. ACT-1000 remains
separate unresolved intake. All roles/Cargo are released; no commit or phase
transition, and NOTES remains untouched.

### Imported-trait dotted-member assessment approved — 2026-09-27

The user's “ok” approves assessing ACT-1000 against the specified derived
dotted-member rules and recording a minimal permanent regression if confirmed.
QA classifies the existing observations and allocates independent test evidence.
No production correction, carry, commit or phase transition is presumed.

QA `0bc6d72e-c5a4-471c-a6e9-428c377f7f50` (Claude Opus 5.5/high)
confirms ACT-1000 against settled derived-dotted-access rules. Its source
attribution to type-only parent lookup is provisional; current-binary
execution belongs to the allocated test visit. One regression covers a
same-fixture fully qualified control, direct trait import, and prelude
re-export. No new semantics are needed. QA released its reservation.

Test `9bb2614b-bd01-4f68-a1ec-840ba8163fc9` (Claude Opus 5.5/high)
records the allocated permanent regression. On the current post-ACT-0999
binary, the fully qualified control exits 5, while both imported-parent
subjects fail with undefined `T.m`. The neighboring imported type-member
control passes. Focused result: 1 pass, 1 intended failure. QA's mechanical
coverage-band and intake updates are applied; no extra QA visit is needed
for this as-allocated outcome. Assessment and reproduction are complete;
ACT-1000's fix/defer decision returns to the user. All roles/Cargo released;
no production edit, commit, carry or phase transition.

### Imported-trait dotted-member correction approved — 2026-09-27

The user's “go” approves fixing ACT-1000. Existing QA allocation and
independent RED/control govern the private typechecker correction. Dev first
checks the provisional lookup attribution with module evidence, then implements
and validates; focused review and QA adequacy follow. No public API/schema
change, commit or phase transition is included.

Dev(typecheck) `92e44ba3-b341-419a-882a-79b4c7228ae3` corrects trait-parent
lookup and its immediate dispatch seam, with four module regressions. Crate
957/957 and relevant acceptance 219/219 pass. Full run: 6239 run, 6238 pass,
one known DT-1 failure, one skipped. Source and Cargo are released.
Review `6cac1ba8-5566-4b75-a3a8-a1543240c0df` finds no code blocker; its
required stale-design repair goes to design(typecheck)
`28dbbdee-c4fb-4759-8b5f-ceeec322cb91`. QA
`b596d1d8-2bed-4567-bc99-435f461c8e97` assesses adequacy and classifies the
prelude-shadow precedence lead. These roles use Claude Opus 5.5/high.
No additional implementation, commit or phase transition is presumed.

QA accepts ACT-1000 and retires its intake. Its coverage-band handoffs and
comment-only `fixed=S122` stamp are applied. Design's R1 records repair,
crate guidance, nearby rustdoc and the supplied census wording are applied;
no behavior changed after the full run. Document checks pass at 510/0.

The coordinator executes QA's diagnostic basket on binary `e8c43e58…29bbf3`:
P-1 returns 104 with qualified/prelude controls 5/104; P-2's six legs return
5. Dotted full/partial and qualified partial calls return 5; the bare partial
control lacks a method import and reports undefined `m`. QA
`462807af-39e5-458e-8a8d-fab459318a56` classifies these observations under
ACT-1001. No correction or carry of that separate intake is approved.

QA confirms ACT-1001 P-1 as wrong acceptance under an ambiguous trait
parent; its mechanism remains provisional pending the bare-parent control.
P-2 does not reproduce in the six-leg basket and remains a source lead.
The partial-application subject and independent qualified control pass;
the invalid bare-method fixture invalidates only itself. ACT-1000 remains
accepted. Test `dccf412e-45c4-4986-ac93-4198ccf45dde` (Claude Opus 5.5/high)
records P-1's allocated permanent RED and discriminating control; no production
fix or carry is authorized. Only focused tests are needed.

Test records ACT-1001 P-1 as an unignored RED with passing controls. The
ACT-1000 neighbour remains GREEN (focused one pass, one intended failure).
The bare-parent discriminating control rejects with `unknown trait: T`,
not ambiguity; that diagnostic detail and the provisional locus remain
for QA. The evidence and coverage handoffs are recorded. The approved
ACT-1000 fix is complete; the separate P-1 fix/defer decision returns to
the user. No commit or phase transition occurred; NOTES is unchanged.

### Ambiguous dotted-parent correction approved — 2026-09-28

The user's “fix that” authorizes ACT-1001 P-1's correction. The permanent
wrong-accept RED and its passing controls govern the work. QA settles the
pending attribution/diagnostic detail; design(typecheck) shapes the private
correction before dev implements it. P-2's unreproduced dispatch-index lead
is outside this fix. No public inter-crate API/schema change, commit or phase
transition is authorized. Preserve the existing dirty tree and NOTES.

QA `3ad8b50a-ef74-4e12-9074-6965527f6a6b` retains the typechecker locus
pending module evidence and aligns the regression with §8.6.5: require
both canonical parent alternatives, not a particular ambiguity word. The
coordinator applies that exact assertion handoff and records RED at 104;
the ACT-1000 control remains GREEN. Design
`10703c46-1b1d-4a50-9355-65da63261984` supplies one fallible dotted resolver
with no literal-key fallback. Its changes are private to the typechecker.
Both roles use Claude Opus 5.5/high. Dev implements and validates next.

Dev(typecheck) `5785a5a8-1828-4e6c-a473-1b58d9e0cd72` confirms the
mechanism with four pre-fix REDs (trait/type parent, pattern, eager dispatch)
and a passing unique-parent guard. One fallible dotted core now supplies
identity and type without a literal-name fallback. All 963 crate tests and
302 nearby integration tests pass. Full run: 6246 run, 6245 pass, one known
DT-1 failure, one skipped. Source/Cargo are released. Review
`6a5e4a4a-5653-48fd-95ec-f8cb12246696` inspects the correction independently;
both roles use Claude Opus 5.5/high. Dev's exact design-name handoff is applied.

Review F1 identifies a plausible over-reject introduced by resolving the
parent before filtering its role; F3 identifies a skipped value-path gap
reset. QA `1d690c1d-c477-4410-a07b-972b0e0c59f8` allocates four ordinary-
declaration module guards plus the gap reset test, with no extra e2e.
Design `885fa3a6-d316-48c1-95b7-b1032eaed0ae` amends the private shape to
share the existing type-role predicate and count only type/trait parents.
Dev `b5ed14af-1c50-479b-8998-686ddf97da76` implements that finding-scoped
correction. All use Claude Opus 5.5/high. F2 is mechanically repaired, F4
is answered in the dev result, and QA allocates no additional F5 privacy
cell. P-2 and the separate P-3 impl-head diagnostic remain outside the fix.

F1/F3 dev observes five pre-fix REDs through ordinary declarations, then
corrects role filtering and the stale-gap reset. Four cells turn GREEN;
the pattern cell advances to a separate `instantiate_ctor` lookup failure.
A bare-pattern control fails identically, while constructor calls pass.
Crate result: 968 run, 967 pass, that one retained RED; nearby integration
302/302. No full suite repeated at this point. Source/Cargo are released.
QA `5422f124-3225-49ca-a286-1107f3116cfd` classifies the independent
pattern issue and assesses adequacy. Review
`4746563d-38c3-41db-b203-67151ccb06dc` performs the single F1/F3
re-review. Both use Claude Opus 5.5/high. The newly existing shared predicate
is added to the design's cross-reference list by exact handoff.

QA accepts ACT-1001 P-1 and F1/F3; the single re-review has no blocking
or required finding. Final suite: 6251 run, 6249 pass, two failures (DT-1
and the independent pattern defect, ACT-1002), one skipped. No production
source changed afterwards. The coordinator applies QA's exact H1 module
cell and test annotations: focused one pass (pattern-head resolution),
one expected failure (later pattern instantiation). This satisfies QA's
last condition without another review or full-suite run. The supplied
coverage bands and fixed stamp are applied. P-1 is complete; ACT-1001
remains open only for P-2/P-3, and ACT-1002 retains the newly isolated
pattern fault. No further fix, carry, commit or phase transition is
authorized. NOTES is unchanged.

### Green-suite work approved — 2026-09-28

The user's “agreed” approves fixing ACT-1002, then bringing forward the
minimum explicit `--test` harness work needed to replace DT-1's interim
ordinary-run expectation with correct positive and negative coverage.
Broader project-wide discovery remains deferred. This supersedes the DT-1
carry only for that minimum increment; unsettled harness invocation and
REPL policy return as concrete requirement decisions. No commit, public
inter-crate API change or phase transition is authorized. Preserve NOTES
and the existing dirty tree. Design and QA assess ACT-1002 while spec
prepares the minimum harness requirement decision packet independently.

Design(typecheck) `442d13fc-6c14-4835-9f15-2061c238544e` supplies the
ACT-1002 private design. QA `526479c5-bf71-433e-803a-871dddf86a24`
allocates one independent end-to-end RED and module evidence. Test records
that RED before production changes; the design leaves M4's separate
scrutinee-directed spelling lead out of scope. Spec
`475703ea-daee-408a-8e45-210fb1602ae0` returns the minimum harness decision
packet. The first question, `--test` invocation behavior, is pending with
the user; ACT-1002 proceeds independently. These roles use Claude Opus 5.5/high.

Test `c3fca9ee-dd7e-4ec6-851a-0c6fe355498e` records T1 RED across fresh
and cached REPL/run/link executions; the existing pattern binary otherwise
passes (32 pass, one intended failure). The optional contesting-constructor
control passes and is retained. A warm REPL type-echo omission is a separate
unclassified observation for QA. Dev now owns the private correction and
validation; no harness code changes begin before this correction's gate.

The user selects **automatic discovery and execution** for `--test`, rather
than calling a program-supplied runner `main`. Module selection is the next
pending question (target only versus loaded project modules); broader
unloaded-project discovery remains deferred. Spec prepares the remaining
minimum runner choices. ACT-1002 implementation proceeds independently.

Dev(typecheck) `5f0ee35e-02d0-4803-ac52-d2dcfc6e6a11` observes ACT-1002's
lookup collapse at the seam and implements the private correction. Module
REDs demonstrate each of the three readers, then turn GREEN. Nearby
integration passes 158/158, including T1 across six execution permutations.
Full suite: 6256 run, 6255 pass, one remaining DT-1 failure, one skipped.
Review `301fce82-8faa-4422-9efb-5d6f44d78295` is in progress. Spec
`113eebea-2e13-4292-9e5a-b5925c5d8bd6` prepares automatic-runner details;
the user module-selection answer remains pending. All roles use Claude
Opus 5.5/high; no commit or phase transition.

QA `19b14496-3f56-4073-ba15-ade595d461cb` accepts ACT-1002 against the
logged evidence; review has no blocking or required finding. A1's assessed
residual and A3's assurance grade are recorded by QA's exact handoff. Dev
`d79d86bb-a2fa-4826-8f35-9e6f996e179d` completes A2's comment-only repair;
crate check and formatting pass. Coverage bands and T1's `fixed=S122` stamp
are applied. Actual commit hashes and action retirement await an authorized
checkpoint commit. No production behavior changed after the full run.

ACT-1003 retains the separate warm-REPL echo observation for assessment; it
is not an added fix. The pattern work is complete. Automatic `--test`
implementation awaits the user module-selection ruling, then the remaining
runner-contract decisions prepared by spec. No phase transition or commit;
NOTES remains untouched.

### Automatic test-runner scope settled — 2026-09-28

The user chooses modules reachable from the target through the import chain,
with a default that includes only project-directory modules and excludes
modules on library search paths. This supersedes the pending target-only
versus all-loaded choice: being loaded alone does not establish eligibility.
Configurable module selection is future work. Spec records this ruling and
the previously approved automatic runner; other unresolved runner semantics
remain separate decisions. No commit or phase transition is included.

The user approves that `--test` neither requires nor calls `main`; if
present, `main` compiles as an ordinary definition. This settles QB in the
prepared automatic-runner packet. Spec's next consolidated edit applies that
ruling with the remaining approved runner text. The next pending question
is whether `(mod …)` / `(mod- …)` declarations extend test-module reachability.

The user includes declared child modules in `--test` reachability, including
`(mod …)` and `(mod- …)` children without an explicit import. This settles
the scope packet's Q-A. The project-directory/library-path exclusion remains
in force. The non-empty-run report, continuation and exit policy is the next
pending question; zero-test and trace-policy decisions remain separate.

Arch `53b85716-3f3b-459a-bae0-eedfe197a23c` assesses the minimum runner.
It identifies a root-library public session entry point as an approval-gated
interface delta; no guarded language-library, cache-schema or ABI change is
needed by its proposed boundary. Exact method/result shape follows the
pending reporting policy. The later child-module ruling includes cache/fresh
parity for private children in the runner scope. Spec
`303a0c91-d3b6-4af4-98e0-3783675f5b46` has recorded the earlier approved
automatic/import-chain/project-only/library-excluded requirements. Subsequent
main and child-module rulings await the next consolidated spec application.
Both roles used Claude Opus 5.5/high; no implementation or commit occurred.

The user approves the non-empty-run report, continuation and exit policy:
fully qualified per-test results and a summary on stdout, continuation after
failures and captured panics, exit 0 for all passing and 1 for any failure or
panic; compilation errors prevent execution and go to stderr. The user adds:
“`--test` should be the same code as `/run-tests`, we can keep this simple.”
This establishes shared execution/reporting code, not a separate CLI runner.
The zero-test exit status remains a separate pending user decision. Spec now
consolidates the approved main, children and reporting rulings; remaining
unapproved policies are not implementation authority.

The user also approves a genuinely empty run: print “No tests found” and
exit 0. This settles QC-1; architecture can now present the exact shared
runner interface proposal. Spec consolidation is running as Claude Opus
5.5/high session `68b4825c-09d1-4eaf-ba60-bee4dbd6c3b9`.

Spec consolidation completed and records main, declared children, reports,
continuation and non-empty exit policy. Arch session
`0e4afb74-0aa0-4ffe-ae2a-f1021103a915` (Claude Opus 5.5/high) presents the
exact root-library API proposal; it remains unapproved and unimplemented.

The user settles failure tracing: keep the shared harness simple now;
option-controlled improvements are future work. ACT-0988 retains that scope.
Sprint applies spec's prepared QC-1 exit-0 hunk and QC-2 deletion of the
automatic-trace promise, removing the now-settled CLI trace placeholder.
These mechanical handoffs implement the explicit empty-run and manual-trace
rulings; no unrelated requirement or coverage claim changes.

The user explicitly approves the presented root-library API delta:
`CompilerSession::run_tests(&self) -> Result<TestRunReport, CranelispError>`,
the private-field `TestRunReport` with `text() -> &str`,
`warnings() -> &[Warning]`, and `exit_code() -> i32`, and its `session_v4`
re-export. The exact architecture packet is the implementation contract;
no extra public items, cache-schema, ABI or library-baseline change is
authorized. Actual delivered public diff still returns for confirmation.
Design(int) proceeds on the settled shared-runner behavior; outstanding
selection-edge, normal-mode refusal and CLI-policy questions remain separate.

The user approves rejection of any compiled reference to `discover-tests`
under both `--run` and `--link`, even in an uncalled function; an import alone
remains allowed. The user strengthens the parity requirement explicitly:
“--run and executing the --link output should have exactly the same output.
--run loads and executes, --link produces a freestanding executable of the
same programme.” This concerns program execution, not linker build messages.

Design(int) `cca17f0e-a8a2-49e5-9952-235ef67de6da`, Claude Opus 5.5/high,
completes the shared runner design in `design/int/test-runner.md`. No code or
tests changed. Spec applies the approved normal-execution boundary and parity;
remaining module-edge and CLI-policy decisions precede a settled QA handoff.

The user approves the remaining batch conventions for `--test`: combining it
with `--run` or `--link` is a usage error; a missing entry source file is an
error with exit 1; warnings go to stderr; agent flags follow `--run` behavior.
Existing target resolution, worker flags, `--no-cache`, and rejection of
`-o` continue to apply. The import-chain edge proposal is now with the user;
the mode conventions are settled independently.

The user qualifies the import-chain proposal: the implicit prelude contributes
tests only when it is in the project directory; a prelude found through a
library search path must not bring in library tests. Record the proposed
loading-import/re-export/declared-child chain with this project-only prelude
qualification. Empty and alias-only imports do not load additional modules
for testing; FQ-only references are outside this import-chain default.

Spec `a6cb8210-0311-4e50-9dc8-689208850994` (Claude Opus 5.5/high) completes
the ordinary-mode refusal and execution-output parity requirements and
invalidates the affected mode evidence. Document check: 513 documents,
0 findings. The primitive's availability inside `--test` remains the next
explicit decision before the final harness handoff.

The user rejects exposing `discover-tests` inside tests under `--test`:
“no --test uses the cli test harness/runner.” The CLI invokes compiler-owned
discovery and execution; the language primitive remains REPL-only. This
supersedes the proposed harness-thread runner-state installation and any
positive test expecting programmatic discovery under `--test`. Spec must
reconcile availability and diagnostics with this ruling before the evidence
handoff; the shared CLI/REPL host runner remains approved.

The user explicitly settles traversal at the project/library boundary:
“stop at library modules.” A library contributes no tests and the harness
does not follow its imports or declared children to select further tests.
This settles the prior spec/design R1 question, including project modules
reachable only through a library dependency. The implicit library prelude
remains excluded by the same boundary.

Spec `fee87816-582e-493a-82a7-53ff1cfc24e1` applies the approved CLI
conventions and loading-edge selection. Spec
`6928659a-4ea1-4957-a052-36030f6ba271` records REPL-only primitive
availability and distinguishes the compiler harness in the diagnostic remedy.
Both Claude Opus 5.5/high runs complete with 513 documents and 0 findings.
Spec identifies one remaining refusal-policy distinction for `--test`:
reject the whole run for a compiled reference, or fail only a test that calls
the primitive. That choice is with the user; the coordinator's earlier
rejection statement was a recommendation, not an additional user ruling.

The user approves applying the existing §16.6 compiled-reference rejection
to `--test` as well, and directs: “you are asking too many questions that
depart from --run and --link behaviour and open up air between /run-tests
and --test. we want to use exactly the same code.” Use shared execution,
reporting and refusal behavior; preserve only explicitly approved selection
and CLI process differences. Do not reopen common behavior as separate mode
policy. Option-controlled failure enhancements remain deferred. The library
traversal stop is settled and supersedes design's older R1 interpretation.

The user strengthens the shared-runner direction again: “they will have
everything the same! they will just pass their arguments differently. same
code!” `/run-tests` and `--test` are argument adapters to one runner with
identical behavior. Selection differences are runner inputs, not separate
implementations. Execution, eligibility, warnings, reporting, empty results
and failure handling must share the same code. The host applies the result
to its environment (the CLI exits; the REPL continues); this does not create
a second runner policy. This latest ruling governs the final design and
evidence handoff and supersedes any earlier allowance for divergent messages.

Final consolidation completes: spec `61eef5f3-86cc-48d0-b08c-fd595e953916`,
design(int) `db0be5bf-ad3a-4cb8-8cba-acbcda7b0e32`, and arch
`c05f0743-6b15-4d93-b495-f67c43bdc0cf`, all Claude Opus 5.5/high.
Requirements and design now have one shared runner, the library traversal
stop, common empty report and common batch refusal. No decisions remain
open for implementation. Sprint applies arch's exact inbound-anchor repair.
QA `3b917a93-a787-4655-b82e-cec1d815b1bb` is preparing the settled evidence
delta before test/dev. No production code or tests changed in consolidation.

QA `3b917a93-a787-4655-b82e-cec1d815b1bb` finds the shared-runner change
ready with no blocker. Its final evidence-delta section allocates TR-1–TR-6
and bounded fixture maintenance to test, module evidence to dev, and a full
green suite after focused checks. DT-1's carry is superseded by TR-5. Test
now owns the test files and Cargo for establishing pre-production REDs;
no production writer or commit is active.

Test `65394bf2-d293-4c62-9bf6-2250e6a73e82` (Claude Opus 5.5/high)
establishes all TR cells and fixture maintenance. Full pre-production run:
6266 run, 6254 pass, 12 fail, 1 skip; the 12 are 11 expected runner/maintenance
failures plus the removed DT-1 citation, mechanically repaired by sprint.
TR-5c proves cached refusal is currently an opaque codegen failure rather
than the required diagnostic. ACT-1002 remains green. Dev now owns src and
Cargo; QA reconciles helper/evidence records independently. Docs
`c15a8230-77b7-4326-a274-f62b65b678df` updates the user reference for the
same change, with operational verification awaiting implementation.

Dev `609ba04a-f17b-4fce-8273-942700c30866` (Claude Opus 5.5/high)
implements the shared runner and exact approved public API. Module RED/GREEN
evidence includes failure-value release, exact eligibility, empty reports,
library exclusion, batch source paths, refusal and CLI parsing. Focused
integration: 301 run/300 pass/1 fail. Full: 6297 run/6294 pass/3 fail/1 skip.
The three are TR-1's assumed-polymorphic fixture, the stdlib gate's old
all-modules-under-run premise, and renamed source citations. Sprint repairs
the citations; arch is updating delivered status. QA
`1e5a65a6-0167-4881-a2fa-1c7a3e377da3` classifies the two evidence questions;
independent review `b7fd5289-a945-431b-b8d0-bcb806df76fc` checks code and
actual API. Both use Claude Opus 5.5/high. No commit; full green is pending.

QA classifies TR-1 and SG-1 as evidence-premise errors, not product defects
or normative questions. Sprint removes the superseded pending-question prose
from the design status; its existing post-pinning scheme rule is unchanged.
The interrupted correction dispatch never started; retry starts test
`bd5d81fe-2d81-4ba4-9f9f-cf3a814edb9d`. It owns tests/Cargo for focused
fixture checks. The full suite waits for the remaining source correction.

Review `b7fd5289-a945-431b-b8d0-bcb806df76fc` confirms the public delta
matches exactly. Required R-1: `/tests-for` retains a separate loose predicate;
converge it on shared eligibility. QA `c25ec6e0-e817-430d-8d80-8e8f76431d5f`
allocates its minimal evidence. Review justifies the 23 new `result_large_err`
instances as propagation of the explicitly approved existing error type;
sprint records this narrow METHOD lint deviation without suppressions or an
unapproved API change. No other new lint kind appears. All roles Opus 5.5/high.

Test `bd5d81fe-2d81-4ba4-9f9f-cf3a814edb9d` corrects TR-1 and SG-1;
focused runner/runtime/stdlib checks pass 128/128. QA R-1 assessment requires
only dev's module negative/control, plus maintenance of the existing
`tests/agent.rs` positive fixture. Test `513a0ab6-0cbc-4e88-b57d-2c5e95195777`
owns Cargo for that fixture; dev `8dd44edf-630e-42d0-a465-fc71f86ecf48`
prepares R-1 and waits for the explicit test handoff before source edits and
Cargo. One full suite follows the correction. ACT-1004 retains the separately
reported missing-entry filename diagnostic lead for QA intake. No new runner
policy, public interface or commit is authorized.

The fixture handoff passes 22/22 and releases Cargo. Dev R-1
`8dd44edf-630e-42d0-a465-fc71f86ecf48` records the real mistyped-sibling
RED, converges `/tests-for` on `classify_test_definition`, then passes
39/39 focused checks and the full suite: **6298 passed, 0 failed, 1 skipped**
(108 s). Document checker: 514 documents, 0 findings. API unchanged.
Scoped review `becaab6c-c25c-4ac9-a1dc-f15b33b2ba41` resolves R-1 with no
surviving findings and verifies full-run currency. Sprint applies the exact
predicate-consumer documentation handoff and removes superseded verification
status, keeping the acceptance gate here.

Fresh acceptance smoke uses the final binary and the documented test-add
example in a new temporary project, `CRANELISP_LIB` pointing to this tree's
stdlib and `--no-cache`: passing case exits 0, failure case exits 1, empty
case prints `No tests found` and exits 0. Evidence:
`.local/s122-test-runner-acceptance.log`. QA
`2874eb2a-d2b3-48ec-b839-89020c2999fd` is restoring supported coverage and
making the final adequacy judgment. User confirmation of the exact delivered
public diff remains pending; no commit or phase transition.

QA final adequacy `2874eb2a-d2b3-48ec-b839-89020c2999fd` is **adequate**
and recommends acceptance of the shared runner. Supported coverage bands are
restored, including §17.6.2's negative; G-5 is reconciled. ACT-0986 now retains
only in-language warning and example/citation issues. ACT-1004 remains separate
intake. The full suite, clean scoped review and fresh acceptance smoke support
this recommendation; user public-diff confirmation is the remaining gate.

Sprint independently recounts the clippy JSON baselines and corrects the
reports' arithmetic typo: **23**, not 21, added `result_large_err` diagnostics
(12 run, 4 selection, 3 session tests, 2 result owner, 2 commands), with four
other diagnostics removed; total 785 → 804. The per-file accepted set is
unchanged. No suppression or other lint kind is admitted. The QA plan and
live count are corrected mechanically; original role reports remain evidence
of the typo. No source changed after the 6298-pass full run.

### Delivered shared-runner API confirmed — 2026-09-28

The user answered “yes” to the post-implementation public-diff confirmation:
`CompilerSession::run_tests() -> Result<TestRunReport, CranelispError>`,
`TestRunReport::{text, warnings, exit_code}`, and the `session_v4` re-export.
Independent review verified the delivered surface matches the prior approved
proposal. This closes the runner's final public-API gate. The 6298-pass full
run, clean scoped review and QA adequacy remain current; no source changes
followed them. Phase 5 remains active pending whole-sprint reconciliation.

### Remaining Phase-5 reconciliation — 2026-09-28

The user authorized reconciling the remaining issues into a concrete fix-or-carry
list. QA (Claude Opus 5.5/high), session
`b07b13ce-8feb-46e4-a32f-d352389bf015`, owns the current G-5/G-6/G-8 assessment
and QA evidence-plan update. It checks later deliveries and recorded rulings
against current claims before proposing further work. No source changes,
blanket carries or phase transition are authorized by this dispatch.

QA completed the reconciliation: all delivered corrections retain adequate
evidence, but remaining work is now grouped by persistence, name resolution,
batch/platform admission, runtime ownership, and assurance/maintenance. The
updated evidence plan supersedes the former G-5/G-6/G-8 table. It separates
observed defects, source-confirmed non-conformance, unverified leads and
coverage gaps. No proposed carry is approved by this assessment. Document
checker: 514 documents, zero findings; whitespace clean; NOTES unchanged.

The next authorized evidence visit addresses persistence P1–P4: the observed
watcher refusal and external-edit overwrite, and the rejected-redefinition and
warm-restored macro-definition leads. Its outcome determines implementation
attribution before a fix or any public/schema decision. Other groups remain
explicit in the QA reconciliation.

| Role | Provider / model / effort | Session | Current reservation |
|---|---|---|---|
| test | Claude / Opus 5.5 / high | `f55071b2-d152-44e7-8c9b-def2e5473470` | Persistence P1–P4 reproductions; tests/repl_persist.rs; sole Cargo owner |
| spec | Claude / Opus 5.5 / high | `e6ed4e32-858f-4f83-9c58-97814bf4b91c` | Read-only framing of P7 regeneration-order question |

Persistence evidence visit completed (test session above): seven permanent,
unignored cells added to `tests/repl_persist.rs`; **four RED, three GREEN**.
The complete persistence binary reports **46 passed, four failed**; its 43
pre-existing cells still pass. The prior 6298-pass full-suite run predates
these additions and is no longer a claim that the current tree is all green.
No compiler implementation changed and no commit was made.

- P1 reproduces for product field-count changes; field-type and function-body
  controls reload successfully.
- P3 reproduces after typecheck rejection and commit-gate rejection: a later
  successful turn writes the rejected definition, breaking a cold restart.
- P4's entry-module prediction did not reproduce, including stdlib `def`.
  The cached dependency edited through `/mod` does reproduce; its fresh control
  passes. QA must narrow the record and adjudicate the traceability limits.
- P2 diagnostics show external-edit loss after a parse-error reload as well
  as the P1 refusal. Type-error reloads preserve the edit. Test requests a
  specification disposition before adding a P2 acceptance assertion.

Evidence: `.local/s122-persistence-residual-test-result.md` and the focused
logs it names. QA attribution/reclassification and design handoffs remain;
no carry or implementation mechanism is inferred from these results.

Spec's read-only P7 assessment completed (session above). Authorship order is
an explicit S69 user ruling, not a fresh preference question. The coordinator
retains that authority. A question is pending for the actual conflict:
redefinition in place can put a use before a macro introduced later. The user
is asked about moving only the using form after its required macros. Other
normative questions remain unapproved; no spec edits were made. Assessment:
`.local/s122-persistence-order-spec-result.md`.

### Four reproduced persistence failures — fix-now direction (2026-09-28)

The user directed: “write the action for the deferred and focus on the
reproduced failures.” [ACT-1005](actions/ACT-1005-macro-order-regeneration-edge-cases.md)
records the macro-order edge-case investigation for S123 or S124. This does not
approve changing authorship-order requirements or a general dependency-sort
mechanism. The earlier ordering question is superseded by this deferral.

QA (Claude Opus 5.5/high), session
`58787f90-457e-4efc-b666-0715b130072c`, owns attribution and readiness for the
four permanent REDs: P1, both P3 rejection stages, and P4's cached dependency
face. P2 remains separate intake. No source edits or Cargo during this QA visit;
design and implementation follow the bounded evidence handoff. No commit or
phase transition is authorized.

Design(int), Claude Opus 5.5/high, session
`e5da8d03-b10e-47ed-a596-6e441dd4823c`, inspects the same four failures in
parallel with QA. Its writable reservation is the Binary/int persistence
design; final readiness consumes QA's result. Compiler/test source remains
reserved for the subsequent implementation visit. ACT-1005 establishment
verified: 515 documents, zero findings.

QA completed four-RED readiness (`58787f90…`); requirement support is established
for the cached `/mod` face without a new ruling. Design(int) completed
`e5da8d03…`: P3 uses publication-time source records; P4 recompiles a cached
module through the ordinary reload path before editing. Updating declaration
records through that same writer is necessary related work within the
user-authorized persistence correction, not a separate feature or permission
gate. P1 requires an architecture decision before a public-surface proposal.

Test, Claude Opus 5.5/high, session `d6c7d8b8-cb1d-4626-9438-7dcfb695605b`,
owns PR-2–PR-4 controls and exact defect-comment updates. Arch, same provider,
model and effort, session `c9a14c39-d698-4b39-9d6e-c226592c0cb2`, owns the P1
cross-context assessment and exact public API packet. No unapproved API is
implemented.

Sprint ran the design-authored D1–D7 probe script, unchanged, against the
existing debug binary after inspecting its scratch-only operations. Log:
`.local/s122-persistence-four-design-scratch/probe-observed.log`.
D1/D2/D3/D5 reloads report the origin/lifecycle refusal; D4 leaves removed `h`
callable; D6 accepts the live Int-to-String field change; D7 rejects a live
field-count change. These are diagnostic observations for QA/arch, not new
scope approvals or substitutes for permanent regressions. No Cargo or
production edits occurred in this coordinator probe.

Test PR-2–PR-4 visit completed (`d6c7d8b8…`). Live field-count rejection and
field-reorder dependent recompilation controls pass. Two new field-type
persistence REDs confirm P5, covered by the common publication writer. The
field-count persistence/dependent legs remain blocked by P1. The separate
imported-module failed-reload hang has a permanent unignored reduced test and
`ACT-1006` QA intake;
no carry or mechanism is assumed.

Dev(src), Claude Opus 5.5/high, session
`df5a3760-0258-4e43-950f-d13bea580a96`, owns P3/P4 and the related declaration
record repair, with sole Cargo access. P1 public changes remain gated with
arch. Known P1 and hang failures stay explicit; full-suite green cannot be
claimed until the combined correction and dispositions are complete.

Arch P1 assessment completed (`c9a14c39…`), exact proposal in
`.local/s122-p1-reload-arch-result.md`. Item 1 adds
`StagedPublicationDecision::SupersedeType { type_name: FQTypeName }`; expected
public baseline: variant and field only, no serde/cache/ABI change. The user
has been asked to approve item 1; it is pending. Item 2 (widening the absent-key
`ChangeAbi` contract to slotless callables) is expressly excluded from that
question and remains unapproved. Architecture rejects the design's proposed
whole-module fresh-slot policy, selecting changed-family slots with complete
cascade/retirement instead; design must align before P1 implementation.

Arch identifies ACT-1006's failed-dependent hang as a P1 acceptance dependency,
not an API-proposal blocker. Its absence from the independent P3/P4 source-record
batch remains explicit. Diagnostic D1–D7 results recorded above supersede the
arch report's statement that those probes had not run.

The user chose “Discuss the design first” for P1 item 1. Approval is not
provided. The coordinator explained reload versus live-redefinition authority,
family-atomic replacement, removed-member retirement, slot retention and the
separate dependent-recompile safety obligation. No P1 API implementation
proceeds; P3/P4 implementation continues independently.

Dev P3/P4/P5 completed (`df5a3760…`): five acceptance REDs now pass (the two
rejection stages, cached dependency save, and two declaration-record routes).
914/914 module tests pass. Final focused e2e 233/237 and earlier wider 501/505
fail only at P1/layout preconditions and ACT-1006. No public API/schema/ABI
change. Independent review, Claude Opus 5.5/high, session
`c859437e-503f-4a5a-b4d4-8366f8628965`, inspects this delivered subset.

Sprint executed the developer's archived P2 setup and P2 section in its
scratch (no changed assertions or source). Log:
`.local/s122-persistence-records-dev-scratch/p2-observed.log`; binary digest
`d9a1ebd426996ab96b707ac89f65864e3f04862c686485d6d61abcfe96f02ec1`.
All three failed reload shapes (origin refusal, type error, parse error) are
followed by an accepted definition turn which writes the last published source,
losing the external edit. The user was informed; no retention/loss policy is
approved by this observation. ACT-0998 face 2 remains unresolved.

QA bounded adequacy, Claude Opus 5.5/high, session
`f1542ea8-b452-4bb8-ba09-18e53a504873`, consumes the delivery/review and this
diagnostic, updates PR-6 to the chosen route, and retains P1/ACT-1006/P2 limits.
No whole-sprint green claim or phase transition.

Independent review `c859437e…` reports no blocking correctness finding in
P3/P4/P5. Required F1 is mechanical doc-comment attachment/narration damage.
Advisories F2–F4 concern the effect-free prior helper and evidence descriptions;
F5 records `/mod` recompile cost/changed-source assumptions and its possible
route into ACT-1006. Lint suppressions follow the existing local convention;
review finds no public-API or behavioral-contract change in this subset.

Dev(src), Claude Opus 5.5/high, session
`eaac47ec-7c1d-462a-8bd7-ad520c6dca8d`, applies F1, F2's minimum stale-comment
repair, F4's accurate test claims, and F3's final-text detection proof. No new
behavior or helper redesign is allocated; no re-review for these mechanical
repairs. QA owns bounded adequacy and retained F5 risks. P1 remains unapproved.

QA bounded adequacy `f1542ea8…` completed: P3/P4/P5 adequate, conditional on
the in-flight F1 repair and final-text M5/M7/M10 fault proofs. Review found no
blocking correctness issue. QA records ACT-1007 (removed definition stays
live) and ACT-1008 (live field-type change accepted), both intake without
new fix or carry authority. ACT-1006 remains a P1 acceptance dependency.
Document checker at QA handoff: 518 documents, zero findings.

Mechanical follow-up `eaac47ec…` completed. F1 doc repair, F2 stale claims
and F4 test-claim repairs are applied. F3 faults M1/M5/M6/M7/M10 were each
observed failing against the final test text, then restored; 26 affected
module tests pass. Sprint byte-compared the three production snapshots and
final test snapshot: all match. This discharges QA's named F1/F3 conditions
without a substantive re-review. F2 helper retirement and F5 remain advisory
owner handoffs, not newly approved behavior.

Fresh final acceptance: the five repaired `repl_persist` cells pass **5/5**
on the final tree, through nextest's fresh REPL sessions, in 0.973 s. Log:
`.local/s122-persistence-records-acceptance.log`. Document checker: 518
documents, zero findings; whitespace check clean; NOTES digest unchanged.
The known P1 and ACT-1006 REDs remain. No commit, phase transition or public
API approval occurred. The user's P1 request is discussion first.

### Restart boundary adopted — 2026-09-29

The user asked whether rejecting incompatible changes would simplify the
requirements, then ruled: “restart is a good resting point for now.” Structural
same-name type changes will require restart instead of in-session type-family
supersession. The unapproved `SupersedeType` and associated `ChangeAbi` widening
proposals are withdrawn from this correction. Existing compatible updates stay
available; this ruling does not remove every cascade or approve unrelated
import/export, deletion or macro policy changes.

Spec, Claude Opus 5.5/high, session
`f8cb8915-b6f0-4a5c-a86f-23bb8363d7e1`, records the requirement and directly
necessary consistency repairs. Arch, same allocation, session
`ff2514a2-c170-4e33-b421-a5bd53fa202c`, assesses the smallest rejection-only route and exact
boundary implications; final judgment consumes spec's result. Compiler and
test changes follow the settled evidence delta. No phase move or commit.

Spec `f8cb8915…` completed: REPL §14.8 establishes restart-only structural
changes, restart diagnostics and protection of the rejected backing file;
§15 and §18 mirrors agree. Document checker: 518 documents, zero findings.
QA, Claude Opus 5.5/high, session
`d7ff876b-0f30-40ee-82b3-f974288f99c4`, revises the evidence allocation against
this boundary. Full §18.5 structural identity and rejecting turns that would
overwrite the protected file follow the accepted ruling. The general failed
reload retention question remains separate.

Arch `ff2514a2…` completed: the revised route needs no public API, cache or
ABI delta. An int-owned shared structural guard and session protection implement
§14.8; a types-private synthesized-slot check protects publication. The imported
reload hang remains relevant to required failure handling, subject to QA evidence.
Design(int), Claude Opus 5.5/high, session
`d0adf6cc-9827-48f1-af21-271d87aca824`, aligns current design and prepares the
private implementation handoff.

QA `d7ff876b…` completed: ready for RB-1–RB-6. Old live-layout-success
conditions are retired/inverted; compatible docstring edits retain the P5
regeneration fence. The imported failure cell RB-5 remains subject to
ACT-1006; the independent type-error hang remains open. RB-6 is included in
this correction because the same structural guard governs live definitions.
Test, Claude Opus 5.5/high, session
`7451309e-d412-48ed-ba77-13fd0d62ef97`, authors and observes the settled
cells, with sole Cargo ownership. The correction includes investigation and
repair of ACT-1006's required failure path; no carry is implied.

Design dispatch `d0adf6cc…` failed before inference (DNS EAI_AGAIN, zero
tokens); it made no edits. Retried through the same approved transport with
network authority, session `0b9fc8a9-8253-4cf1-bd15-e21c78411432`, same
Claude Opus 5.5/high allocation.

Test dispatch `7451309e…` likewise failed before inference (DNS EAI_AGAIN,
zero tokens, no edits). Network-authorized retry session
`c78461f8-51f9-481c-82d0-80c35cf189b2` retains Claude Opus 5.5/high and
sole Cargo ownership.

Design `0b9fc8a9…` completed the int handoff with no public delta; document
checker 518/0. Test `c78461f8…` completed: 9 focused cells, 4 pass/5 fail;
71 persistence/watch cases, 65 pass/6 fail (the five revised behaviors plus
ACT-1006). RB-6 reproduced SIGSEGV after the wrong-accepted live field-type
change, making ACT-1008's memory-safety consequence observed. RB-4 fails at
its precondition only; compatible-save legs currently pass. These reports
supersede old P1 success expectations, not the completed P3/P4/P5 fixes.

Dev(types), Claude Opus 5.5/high, session
`cc22d2d6-bd56-4537-b4db-756ea8a5091d`, implements the private publication
backstop and its allocated module evidence. Sole Cargo ownership; no public
delta or source supersession operation.

Dev(types) `cc22d2d6…` completed: 292/292 crate tests pass; four isolated
fault checks discriminate the backstop. Full run: 6318/6324 pass, 1 skipped.
RB-6 now passes (the wrong-accepted field-type crash is prevented). One prior
P5 module unit now fails because its structural-change precondition is forbidden;
src dev transposes it to the already allocated docstring edit. Remaining failures
are the four REPL-facing conditions plus ACT-1006. Arch standing-record session
`f9546238-bf8e-4f4b-a758-7c567e11f7dc` completed, checker 518/0.
Dev(src), Claude Opus 5.5/high, session
`39f78b92-1029-44a6-86fb-13f87eed0871`, implements the int guard/retention
and investigates the reproduced ACT-1006 failure path with discriminating
evidence before attribution. It owns Cargo.

Independent review(types), Claude Opus 5.5/high, session
`59fc3e27-acac-4573-9361-9219d634c8e6`, inspects the completed backstop
read-only while src dev proceeds. No concurrent Cargo or source mutation.

Review(types) `59fc3e27…` completed with no blocking/required correctness
finding and no public delta. Advisory A1 overstates same-typed field-position
protection in comments/prose; narrow wording repairs are owned by dev(types),
session `222422e5-5ab5-4ce3-bd02-88e7f2416d8e`, and arch, session
`952594cc-b3f9-4ee6-91fa-826655091e9a` (Claude Opus 5.5/high). A2's
error-field matcher tightening remains advisory; the existing fault proofs
already discriminate the required check. No behavioral re-review is needed
for wording alone.

Both A1 wording repairs completed; checker 518/0. Dev(src) `39f78b92…`
completed: 924/924 default library tests, 1064/1064 with agent, full suite
6331/6334 with one skipped. Remaining failures are two live-refusal output
matchers and RB-5's exit-0 assertion; QA classifies their authority before
any test changes. ACT-1006's cell and error-blocking control passed 15/15
stress iterations. Runtime evidence and fault replant attribute the hang to
a worker signature barrier registering a waiter after its dependency failed;
the private fail-fast fix matches the already-existing sibling path.
QA final session `d1d09c47-970a-4ff5-a16d-f9308e181df4` and independent
review(src) `5234540b-d769-4a8a-9024-9ce6d5c16625` (Claude Opus 5.5/high)
assess the bounded result. QA first emits a test-expectation classification;
no product semantics are changed to fit those assertions.

QA classified all three remaining full-suite failures as evidence defects,
with no new normative decision. Test session
`56a205fc-6629-4887-9c57-e45a2868b7d5` (Claude Opus 5.5/high) applied
only the allocated E1/E2 assertion repairs; no Cargo run, pending final green.
Design(int) session `77ca0290-eeb7-4cd5-913d-997ad3abbdf0` aligns its pending
status and barrier description with the completed implementation. QA retains
Cargo ownership until its report; reviewer is read-only.

QA `d1d09c47…` found bounded adequacy conditional on test repairs, review
and the lost-wakeup vocabulary entry. Review(src) `5234540b…` then identified
R-1, a required plausible early-read of a module's reload outcome while another
module stands Failed. This is not a new normative decision or approved carry.
QA session `11a7bdbf-7bb8-40de-b12a-52b75f3aa4a5` classifies/allocates R-1
and completes its vocabulary/reference repairs; design(int) session
`8f85a919-b17f-4bb4-b8dc-0a0f54f47d87` resolves the narrow interior issue.
Both use Claude Opus 5.5/high and no Cargo. Sprint ran the test-authored final
commands after E1/E2: persistence/watch binaries now pass 71/71 (fresh run,
5.948 s). RB-5 stress is running; this discharges only the instrument-repair
condition, not R-1.

QA R-1 readiness completed: required correction, module-seam RB-7 allocated;
vocabulary/reference repairs complete. Design R-1 completed: use the existing
per-module completion wait for both failure and success; no public delta.
Dev(src) `8d60b11e-98d6-472b-9460-9425748cc6af` (Claude Opus 5.5/high)
authors RB-7 RED first and applies this finding-scoped correction. Its local
positive control may also observe design's deterministic success-side twin.
The repaired RB-5 now passes 15/15 stress iterations (13.393 s), completing
the instrument-repair evidence.

Dev R-1 `8d60b11e…` completed: RB-7 observed RED before the fix in four
invocations; the success-side U2 was deterministically RED. Both now pass,
including 10 stress iterations. Persistence/watch 71/71, RB-5 15/15 and full
suite **6336 passed, 1 skipped, 0 failed**. The production correction is one
existing wait call plus its comment; no scheduler/public delta.
Finding-scoped review session `c82bee4a-0d64-472f-a887-0584d1959638` and
QA conditional closure session `3d91682a-77c5-4b33-bb08-270869a19db7`
(Claude Opus 5.5/high) consume the final change. Test provenance session
`20901ebb-0e1d-45eb-b8c3-c2e157c0edf8` completed the lost-wakeup annotation;
text checks pass. No commit or phase advancement.

R-1 re-review `c82bee4a…` closed the finding with no required issue left.
QA `3d91682a…` judged RB-1–RB-7 and ACT-1006 adequate; it retained only
RB-6 comment notation before retiring ACT-1008. Test session
`fcfa8cc4-2ab1-413c-9f25-bc5f08ed59f4`, design session
`f245d70d-25c1-4404-92dc-86f68415f0d6`, and mechanical QA closure session
`33d916be-d6c3-4075-ab9b-7da6802758d1` (Claude Opus 5.5/high) finish
those comment/canonical-residual/action updates without code changes or another
adequacy cycle. Final-record design `69b7a4c2-7163-4b25-994d-b68154386a01`
removed stale implementation-status text and preserved guards independently of
retired actions. The coordinator independently verified the full-suite summary
in dev's tool output: 6336 passed, 1 skipped, 118.882 s.

Final mechanical test/design/QA sessions completed. ACT-1006 and ACT-1008
are retired, with salient evidence preserved in the existing QA plan and
permanent regression tests. QA records nothing open for this correction
except adding the commit sha to fixed annotations when a commit is authorized.
The cache-restored dependency residual is now explicit in the canonical design.
Fresh final acceptance on the final implementation: **71/71** persistence/watch
cases pass (6.124 s), log `.local/s122-restart-boundary-final-acceptance.log`.
Binary SHA-256: `dcfab1aef5c2de6c31ee2e7148856a5a457ad13307d52fcacc24e7e0d69f17c3`.
NOTES digest is unchanged. No commit or phase transition occurred.

Final document check: **516 documents, zero findings**, zero unverified
references. Whitespace check clean; public-API baselines unchanged. The final
test source hash matches QA's restored comment-only state.

### General failed-file policy — 2026-09-29

The user approved the proposed checkpoint and reload-cleanup batch, and ruled:
“unsuccessful typecheck of changed files should result in the files being
preserved and error/s listed in the repl. then the module is locked until a
successful typecheck. later we'll add a reset to last known good repl function.”
Checkpoint `63605970` contains the verified work through the restart boundary;
NOTES and the shared-package changes are excluded. No later commit is inferred.

Spec, Claude Opus 5.5/high, session
`916b8dba-3d88-42b2-9c02-4ccacc11ad03`, records the policy and necessary
REPL-spec mirrors. [ACT-1009](actions/ACT-1009-repl-restore-last-known-good.md)
retains the explicitly deferred recovery command. ACT-1007 is checked on this
checkpoint before scheduling a correction. Work remains within Phase 5.

QA readiness session `1adc9292-7049-4439-9041-a0660f5dc1d9` (Claude Opus
5.5/high) allocates one reload/persistence evidence batch including current
ACT-1007 reproduction. Spec `916b8dba…` completed the general failed-reload
lock in §14.5 and mirrors. A narrow spec consistency follow-up,
`fe08ba7c-0feb-4245-aeb5-a01a28b4d6f3`, checks the parse-broken startup
case against the approved rule that restarting cannot bypass the failed-file
protection. No tests or implementation have started for the new batch.

Spec consistency `fe08ba7c…` completed: a startup parse failure locks and
preserves the whole backing file; parseable startup failures retain their
established per-definition repair behavior. QA `1adc9292…` consumed both
spec results and judged ready: FL-1–FL-3 and RM-1–RM-2, with existing RB/startup
controls reused. Design(int) `17ce5da5-3d2b-4188-97d8-2671bd8d94af`
prepares the shared private path. Test `d0aebe00-45be-4dde-afa2-2c8ca2f73549` owns the settled RED
batch and Cargo; RM-1's current observation is published first for design.

Test `d0aebe00…` completed: FL-1–FL-3 and RM-1–RM-2 all RED for the
allocated reasons; the 71 previous persistence/watch cells remain GREEN.
RM-1 confirms the omitted binding survives lookup, introspection, its slot
and regeneration. Design `17ce5da5…` settled the general module-lock path.
Arch `90c7b3bb-c92f-4626-9f3e-0ee5154e8e0d` confirms the published absent-key
ChangeAbi transaction already supports slotted ordinary-function retirement;
no public API/schema/ABI delta. It supersedes design's initial boundary concern.
Generic-template retirement has a separate public-semantic limitation and stays
open, with no user carry or interface extension inferred. Design follow-up
`7a7e98a6-23f4-49c1-a28d-49961c3e9ed0` finishes the same int handoff from
these results before a single source implementation visit. All named roles use
Claude Opus 5.5/high.

Dev(src), Claude Opus 5.5/high, session
`a366ae44-3652-4d30-8c9c-20f9a6fa8c55`, starts the settled FL policy and
module evidence while removal-only design finishes. It owns Cargo and source.
RM implementation remains dependent on the final design handoff; the same
source owner consumes it when ready rather than guessing or holding up FL.

Design follow-up `7a7e98a6…` completed the removal handoff in
`design/int/session-transaction.md` §7.3.1. The existing publication facade
suffices for the allocated concrete-function cases; no public API, schema or
ABI change. Dev `a366ae44…` consumes that handoff in the same source-owner visit.

Review(src), Claude Opus 5.5/high, session
`33bbcf32-59c1-4890-baca-ed53ff178603`, begins read-only inspection of the
implemented batch while dev completes verification. All 76 persistence/watch
cells and 15 imported-refusal stress runs pass. Dev retains sole source/Cargo
ownership; review consumes its final report before concluding.

Final bounded QA, Claude Opus 5.5/high, session
`fdea5d0a-6970-4fe1-9c86-8b9a405ae19f`, starts record reconciliation and the
known QA-anchor repair. Dev's full run has 6353 passes, one skipped and the
single document-conformance failure; QA waits for dev's ownership release
before fresh acceptance, and consumes independent review before judging.

Dev `a366ae44…` completed and released source/Cargo: the full suite's sole
failure is the QA-owned document anchor; release build, 76 persistence/watch
cells, 138 agent units and 15 stress runs pass. Implementation also corrects
two test-reproduced interactions: a post-publication submodule continuation
must not remove its new definitions, and an old expression wrapper must not
block removal. Review and QA consume the final report; standing mirrors remain
to be reconciled by their owners.

Design(int) standing reconciliation, Claude Opus 5.5/high, session
`ad852c6c-66bf-4683-bd09-b75979933646`, verifies the two implementation
refinements against source and updates only their canonical design descriptions.

Review `33bbcf32…` completed. It confirms module-lock behavior and concrete
retirement ownership, but requires bounded corrections/dispositions: R1 source
provenance must distinguish an intentional empty file from internal placeholders;
R2 predicts a false refusal when omitted generic residuals reference removed
concrete functions; R3 a unit pins the open generic limitation as green. QA
classifies the latter two before the correction handoff. Design mirror
`ad852c6c…` completed its two requested refinements; final document check is clean.

QA's canonical judgment accepts FL within allocation and confirms separate
startup dependency loss (ACT-1010 M1). A single correction basket is dispatched:
Design(int) `08208d0f-ea1a-4851-ba5d-9b4c9252d5c9` settles private R1/M1;
Test authors the settled RM-3/RM-4/M1 evidence and RM annotation repairs. Both
use Claude Opus 5.5/high. Generic removal and unloaded-file `/mod` semantics
remain open decisions; neither is silently deferred or expanded.

QA `fdea5d0a…` completed: FL adequate; RM requires R1/R3 and a generic
removal disposition; M1 is reproduced startup file loss covered by the approved
protection policy. Test session `957f17b8-9b2d-4e1a-8b08-f3b07e4a02cc`
holds the settled RED batch. The user is asked whether generic deletion should
require restart temporarily or receive full live removal now; no answer or
requirement change is inferred. M1 correction proceeds under existing authority.

Test `957f17b8…` completed: RM-3, RM-4 and M1 all RED for the allocated
reasons; prior 76 persistence/watch cells stay GREEN. RM-1/RM-2 mechanism
annotations are corrected. No fixed commit marker is added before a commit.
Test identified a binary-hash attribution correction for final QA: nextest
relinks its own current-source executable; both builds postdate the source.

Design `08208d0f…` completed: R1 and M1 are private src corrections, no
semantic/public-boundary choice. Dev(src), Claude Opus 5.5/high, session
`05a0399a-dadc-48b4-8f06-f08feac795b5`, implements R1/R3/M1 in one visit,
including the src guidance mirror and allocated checks. Test and design have
released ownership. RM-3/RM-4 remain explicit ACT-1007 REDs pending user choice.

Correction evidence: R1/M1 module REDs are GREEN, 943 module tests pass,
and persistence/watch is 77 GREEN plus the two expected ACT-1007 REDs.
Finding-scoped Review(src), Claude Opus 5.5/high, session
`ec311b62-acb6-4994-b7de-bf1603ad1fcc`, inspects R1/R3/M1 while dev finishes
its final checks; dev retains Cargo/source until its report returns ownership.

The user clarified that removal means omission from a saved source file and
asked how invalidated foreign callers relate to retaining old versions. No
restart exception or public change was approved. Arch read-only assessment,
Claude Opus 5.5/high, session `0d3f21fe-0653-4c63-be1a-9d830fa0902a`, checks
the outstanding minted-instance question and prepares an exact proposal if
needed; live binding and retained code ownership are separate responsibilities.

Dev `05a0399a…` completed and explicitly released source/Cargo. Default
module tests 943/943, agent module tests 1083/1083, RB5 stress15/15;
full suite 6359 passes, one skipped and exactly ACT-1007 RM-3/RM-4 RED.
M1 passes. No public API/schema/ABI delta. Final bounded QA begins after this
release and consumes the finding-scoped review before judging.

Correction QA session `eac19666-a786-4e6c-8793-9d0c735245d5` uses Claude
Opus 5.5/high. Its scope is the delivered R1/R3/M1 correction, current-source
acceptance and truthful remaining generic/dependency records.


Arch `0d3f21fe…` completed read-only assessment: template removal needs no
old template version; compiled instances own their code and existing reload
demand handling covers retirement. The exact proposed public semantic widening
is now before the user; no implementation is approved yet. No API shape,
cache or ABI change is proposed. Review `ec311b62…` returned an interim
no-finding observation before the dev report arrived, without its required
artifact. Review completion session `293e1e5b-8442-41e1-9c80-6cc1d5c17987`
(Claude Opus 5.5/high) finishes that same R1/R3/M1 handoff; it is not a new
review scope.

Review completion `293e1e5b…` releases R1/R3/M1: no finding survives, final
source/evidence hashes match dev, and the src guidance mirror is accurate.
Generic publication remains a separate user gate, with no producer edits yet.


Correction QA `eac19666…` completed its judgment: FL, concrete RM, R1/R3 and
M1 are adequate; final acceptance is 80 passes with the two known generic REDs
(82 tests including document checks). Documents: 518, zero findings;
traceability: 2629 valid citations and zero unresolved references. Source
hash matches dev/review. ACT-1011 records the measured startup-cascade recovery
problem for the next correction basket; no fix/carry decision is inferred.
The user requests more background on the generic proposal; no approval yet.
No new commit or phase transition occurred.


### Generic removal approval — 2026-09-29

The user said “agreed” to the explained exact public semantic extension in
arch assessment `0d3f21fe…`: absent-key `ChangeAbi` also removes a slotless
Template binding; the consumer includes omitted authored templates. No new
public item, slot for a template, cache-format or ABI change. The expected
generated public baseline is unchanged and returns for post-implementation
confirmation under the root gate. No restart exception, new deletion command,
commit, carry or phase transition is authorized. Producer, design and QA
readiness proceed concurrently on separate owned surfaces; Cargo is serialized.

Active generic-removal roles, all Claude Opus 5.5/high:
- Arch producer `8218fce7-0d89-4c10-95d1-3889787089a5`: approved types
  contract, module evidence and generated baseline; sole Cargo owner.
- Design(int) `efd1a27b-fbd9-4eb0-adbd-2eecec3f6606`: canonical consumer
  design and bounded implementation handoff.
- QA readiness `fa570b82-15ad-4369-8fed-68db7ca1ecb9`: evidence delta for
  generic removal and dependent concrete instances.

Producer `8218fce7…` completed: 294/294 types tests; fresh public-API guard
passes3/3 and reports the expected +0/−0 surface. Cargo released. Design
`efd1a27b…` requires retaining the consumer's slotless non-template exclusion
while adding all-template bindings. QA `fa570b82…` judged ready and allocated
one foreign-caller recovery cell RM-5 before the consumer change.

Test `d50b9d17-17f2-4a21-a8c8-c961bb1d4423` owns RM-5 and Cargo in the
pre-consumer window. Review(types) `afb562fa-a204-4c87-bc44-e553d8a70b29`
independently inspects the completed producer without Cargo. Both use Claude
Opus 5.5/high. Producer implementation and record consumers have no new API
shape or serialization changes.

Test `d50b9d17…` completed: RM-5 RED at the expected import-error/call legs
and an additional stale-import regeneration leg. Existing77cells stayGREEN;
RM3/RM4 remainRED. Consumer proceeds; the extra leg will be classified on the
post-fix binary. Review(types) `afb562fa…` completed with no findings and
confirmed the measured generated0/0 comparison.

Dev(src) `5377c909-1df1-4e49-ab3d-8c31d7ff533c`, Claude Opus5.5/high,
owns consumer integration and Cargo. Design's positive eligibility rule governs
slotless templates; other slotless states stay excluded. The distinct stale
import observation is preserved for post-fix QA, not assumed part of this change.

Consumer `5377c909…` completed: RM3/RM4 GREEN, RM5 invalidation/recovery
legs GREEN; stale-import regeneration leg remainsRED unchanged. Full suite:
6366 passes, one skipped, one failure (RM5). The other77 persistence/watch
cells stayGREEN. Source/Cargo released. Final QA classifies the import leg;
no test expectation is weakened or import-record redesign inferred.

Final roles, Claude Opus5.5/high:
- Review(src) `0f47777b-233a-46c2-8abe-e54a2efb023e`: completed consumer delta.
- QA `a1c69bdc-612d-47ba-80b1-bc972ff5a4c6`: final acceptance and independent
  attribution of RM5's remaining stale-import leg; sole Cargo owner.
- Design(int) `63122993-c9f8-4ab3-be5b-15aa5971572a`: current standing mirrors,
  removing stale implementation timing without claiming the full RM5 is green.

Review(src) `0f47777b…` releases the approved delta with no blocking/required
finding. Its advisory empty-overload predicate mismatch fails closed and has
no current producer; final QA retains its disposition. Design `63122993…`
completed standing technical reconciliation. Mechanical status-only cleanup
`f535327c-84f4-42d3-b1eb-87364c9f2a20` (Claude Opus5.5/high) removes two
stale execution-status mirrors from int.md; no technical design change or
new review cycle.


Final QA `a1c69bdc…` accepts the approved generic behavior and retires
ACT-1007. RM5's unchanged import-regeneration leg is independently reproduced
with concrete and import-only controls and filed as ACT-1012. It remains RED,
not accepted debt. Generated API guard passes3/3, types baseline +0/−0.
Design status reconciliation `f535327c…` completed. Exact reference repair
`ff088848-f7cd-41a5-b448-4d4250672913` (Claude Opus5.5/high) repoints the
retired-action link to the closed QA record; this is mechanical only.
No further implementation, commit or phase transition is inferred. The final
baseline comparison returns to the user under the root post-implementation gate.

Mechanical reference repair `ff088848…` completed. Final document checker:
518 documents, zero findings and zero unverified references. Whitespace check
passes; public baseline files have no diff; NOTES digest remains unchanged.
Implementation and evidence are ready for the required +0/−0 baseline
confirmation. The separate ACT-1012 RED remains explicit.


### Unchanged API baseline needs no confirmation — 2026-09-29

The user ruled: “I don't need to confirm no changes.” Root guidance now requires
post-implementation confirmation only for a non-empty generated baseline diff.
An unchanged result is verification evidence, not a user decision. Prior
approval for actual public-contract changes, including signature-identical
semantic changes, remains required. The generic-removal +0/−0 gate is satisfied;
the previously requested confirmation is withdrawn. ACT-1012 remains open, and
no commit or phase transition is inferred.

Arch guidance mirror `c97b90fd-95f1-4e07-bf83-ca1e9bf8ba2c` (Claude Opus
5.5/high) aligns its local approval wording with the root ruling. This changes
coordination policy only; no source, API baseline or runtime behavior changes.

Guidance alignment completed. Root and architecture guidance agree; document
check: 518 documents, zero findings. No confirmation remains outstanding for
the unchanged generic-removal baseline. No commit was made.

### Omitted import correction — 2026-09-29

The user says “continue” after clearing the unchanged-baseline gate. ACT-1012
is the next correction: the remaining RED is an import omitted by a successful
saved-source reload but retained in lookup and regeneration. Source-first check
opened the append-only writer in form_dispatch.rs, reload_module and save.rs.
QA's C2/C3 allocation is settled; test separates that RED from RM5's verified
generic behavior while design(int) settles the smallest coherent repair.
No new public change, commit or phase transition is inferred.

Test `3ac4467f-8b24-4133-991c-0432ca70751d` owns the settled C2/C3 evidence
and Cargo. Design(int) `dd880e0e-4174-4d95-8070-65571aea10e3` owns the
private correction handoff and standing design. Both use Claude Opus5.5/high;
source implementation waits for the reproducer and any genuine boundary decision.

Test `3ac4467f…` completed and released Cargo: C2 is RED on omitted-import
listing, bare resolution and regeneration; C3 retained-import control and RM5
generic removal are GREEN. The focused persistence/citation run passes 69 of
70 tests, with C2 the sole failure. Design's correction handoff remains in
progress; these focused results do not replace the last full-suite result.

Design `dd880e0e…` completed. Its proposed correction requires a candidate
withdrawal operation absent from the types facade; implementation waits for
architecture assessment and explicit public-contract approval. Arch
`027be541-4e98-4ebe-9a9c-4d3d8dd6d9c4` (Claude Opus5.5/high) prepares the
exact proposal. QA concurrently reconciles the isolated C2 evidence and settles
the correction's evidence delta; neither stream changes implementation.

Arch `027be541…` completed: proposes one private foreign-candidate withdrawal
method (+1/−0 types baseline), plus the whole-source replacement contract for
`imports`; no cache-schema or ABI change. QA
`ee4a5163-dfd2-4b49-adaf-fa7e2a81e97c` (Claude Opus5.5/high) completed the
settled evidence delta and updated bands. No additional end-to-end cell is
required. The proposal is ready for user review; C2 remains RED, no dependent
implementation or commit was made, and Phase5 remains active.

### Whole-file namespace direction — 2026-09-29

The user distinguishes incremental REPL turns, which retain the current
namespace, from whole-file rebuilds, which start with an empty namespace.
Old slots and code remain available where existing callers require them;
changed callable structures receive fresh slots. The proposed import-withdrawal
API is not approved and is superseded as the assumed repair mechanism.
Arch `ee8fa381-bcf9-419c-a58d-d28e03810bf4` (Claude Opus5.5/high) assesses
the existing publication machinery and exact remaining contract changes.
No implementation, public API change, commit or phase transition is inferred.

Arch `ee8fa381…` completed the source assessment. It recommends parking the
prior generation outside lookup while rebuilding the visible namespace from
source, reusing existing slot reconciliation and code retention. The proposed
types contract has four methods (+4/−0); it is not approved. The first open
normative question is whether omitting a live nominal type or trait requires
restart, consistent with the existing structural-change boundary, or requires
a retained nominal identity reservation. The import-only withdrawal proposal
remains superseded. Exact proposal: local assessment
`s122-whole-file-namespace-arch-result.md`; implementation and phase remain
unchanged pending the decisions and focused design handoff.

The user additionally requires reload invalidation through fully qualified
references. The current `dependent_modules` traversal follows imports,
exports and prelude only; the cache dependency code already combines recorded
callee modules and lookup dependencies. The rebuild handoff must include this
missing cascade coverage and its independent regression evidence. Platform
function values are prohibited by spec §10.10.1, but rejection is not yet
implemented: ACT-0979 remains open and the current platform signature gate
checks only the IO return. Do not treat that normative prohibition as measured
compiler enforcement when assessing runtime retention.

### Quiescent reload direction — 2026-09-29

The user rules that cross-area design relies on specified contracts, with
implementation defects tracked separately. Whole-file reload occurs after
evaluation and IO finish and the result is released; platform closures are
excluded by contract. Historical closure/type-identity retention is therefore
not a reload design requirement. Incremental behavior stays unchanged; full
rebuild starts with an empty namespace and invalidates dependents including
fully qualified references. The user authorizes this direction to get green.
The previous nominal-reservation question is withdrawn. Existing retained
code need not be removed merely for cleanup, but cannot justify new machinery.

Arch `a862704d-9585-4efe-ac5e-e95ac987d1a1` (Claude Opus5.5/high) revises
only the consequences of this ruling into the smallest concrete proposal.
QA concurrently allocates minimal fully qualified reload evidence. Any actual
public API delta still needs exact prior approval; no phase transition or
commit is inferred.

QA `1c19e60f-1796-45c5-8b5e-365520f755c0` completed the FQR evidence delta:
two independent function/type-only cells include failure locking and release
after dependency repair. Test `bedf40f8-d520-4541-b237-18374b1171f1` owns their
implementation and Cargo; the conditions do not depend on the pending rebuild
API shape. Spec concurrently scribes the approved dependency definition.
Both use Claude Opus5.5/high. QA flags preservation of failed-attempt FQ edges
as a design input for the combined correction, not a new semantic question.

Arch `a862704d…` completed: the revised correction uses existing public
constructors and GOT field, with no new API (+0/−0 expected). Whole-file
rebuild replaces the table and may reuse slot indices at the quiescent
boundary; complete dependency invalidation and error locking govern resumption.
Those consequences were relayed to the user. The +4 proposal is withdrawn.
Spec `f4653a6c-0fe7-4a75-b119-8d79269787f2` completed the dependency-rule
clarification. Test `bedf40f8…` observed both FQR cells RED, imported controls
GREEN, and released Cargo; no compiler fix was included in that evidence.

Design(int) `b3d96717-ec0e-4eba-847e-4f432a579cf5` settles the private
implementation and failed-FQ-edge recovery. Dev(types)
`031f0ad7-10ce-40b7-8161-b9d09882464b` reverts only the now-unneeded
uncommitted slotless-template extension and owns Cargo until its focused
checks finish. Both use Claude Opus5.5/high. Consumer migration follows in
one src visit; intermediate removal-test failures are not final evidence.

Types `031f0ad7…` completed: crate equals HEAD, 292/292 tests pass, Cargo
released. Arch documentation `e3fc4d3a-6b1d-4992-a171-45b37492cd02`
completed owned alignment. Design `b3d96717…` completed: selection and ordering
share all dependency edges; a held failed-attempt reference preserves FQ
recovery edges; all rebuild callers converge. No public delta is needed.
Dev(src) `badc2363-fccc-426f-8e50-4c1429e98ba6` (Claude Opus5.5/high) now
owns implementation and Cargo through the focused, stress, API and full gates.
Typecheck documentation and one crate-root rustdoc consumer reference are
being aligned independently, without Cargo or behavior changes.


Dev(src) `badc2363…` completed and released Cargo/source. Focused acceptance
passes 260/260; target cells pass; RB5 stress passes 15/15; the canonical
public-API check passes 3/3 with all seven baselines +0/−0. Full run:
6370 passed, one document-gate failure, one skipped. The six document findings
name retired source symbols and are assigned to their record owners.

Arch `cd566f38-f089-4b44-b655-2356b352a375` completed the final owned
alignment and retired superseded filing0553. Sprint repaired its incoming
inventory/action references. Independent review(src)
`3e79067c-8cad-4827-898c-f3c07b56d6c7` is read-only; final QA
`06ee9450-ecc7-40ac-9b4a-ab5d87b5881d` owns fresh acceptance, Cargo and
QA record repair. Both use Claude Opus5.5/high. The typecheck prose-only
alignment sessions `ff46949d…`, `7032f21e…` and `1fa595c8…` completed;
none ran Cargo. No commit or phase transition occurred.


Final QA `06ee9450…` accepts the correction after fresh 101/101 acceptance;
review `3e79067c…` has no blocking code finding. Review R1 remains a separate
startup-repair policy question; qualified-cycle observation is filed as
ACT-1013, not implicitly accepted carry. Design final repair
`a6f27c00-c1c1-4373-ac1e-d434ed91d3f6` (Claude Opus5.5/high) repointed the
retired ACT-1012 link and recorded QA's accepted structural Increments grade.
Coordinator reran `citation_drift`: 3/3 pass, checker 517 documents/0 findings.
The source diff hash remains `f274465e…df51836`, identical to the full-run and
QA tree. All observed test failures for this correction are cleared. NOTES
checksum remains unchanged; no commit, phase transition or whole-sprint
acceptance is inferred. Comment-only defect `fixed=` markers await the next
explicitly authorized checkpoint commit per QA's mechanical handoff.

### Reload follow-through — 2026-09-29

The user directs continuing until input is needed. Checkpoint `e4062202`
commits the verified whole-file rebuild; NOTES and `.agents` were excluded.
R1 is settled: subsequent whole-file failure locking applies to a
startup-degraded entry. Spec records that ruling and frames ACT-1010 M2
(session `1e63354b-be52-408f-bd68-7d166033e3e2`). Test owns the sole Cargo
reservation for ACT-1011/ACT-1013 permanent reproductions and checkpoint
comment upkeep (session `398c9f7d-5169-481b-b180-4a0234e3fed0`). Both
roles use Claude Opus 5.5/high under the user's model override. No phase
transition or carry is inferred.

Spec completed R1 in §15.2.3 and cleared its coverage row for QA re-judgment.
Document checker: 517 documents, zero findings; spec links clean. The required
R1 regression remains to be added. ACT-1010 M2 is now presented to the user:
load the existing file before `/mod` switches (recommended), or refuse until
explicitly loaded. No new M2 behavior is authorized while that answer is pending.

Test completed: ACT-1011 and both ACT-1013 faces have permanent unignored
reproductions in the working tree. Focused run: 214 executed, 211 passed,
three new expected failures; all prior cells passed. Each subject failed
10/10 repeats and each control passed 10/10. ACT-1013's fresh-load face is
now reduced to identical-source REPL/--run diagnostic divergence. QA must
reconcile the provisional attribution and coverage bands; design(int) follows
for correction. R1's cell remains pending. Cargo is released. The comment-only
checkpoint tags preserve original loci and name `e4062202`. No carry is
approved, and no implementation change followed the checkpoint.

### Module navigation ruling — 2026-09-29

The user agrees `/mod` navigates existing modules and does not create them;
unknown names give an error. Scenario 1 never stated that its target was
absent; the earlier creation inference is withdrawn. Scenario 7's suggested
creation remedy contradicts its own error and needs correction. The user
also raised ordinary current-module name resolution as a possible direction;
this is not recorded as an explicit absolute-path requirement.
Spec session `d2fa1e54-b200-45d0-8e7d-c5ff8d7fbb3e` records the ruling.
QA session `230b6bc4-08e1-40c1-8a7f-738bf954416b` assesses the new reload
REDs and allocates R1/navigation evidence. Both use Claude Opus 5.5/high.

Spec completed §3.9 and §8: no creation; unknown-target error preserves current
module; existing file-backed targets load on navigation, derived from §14.1's
existing load-via-/mod requirement. Checker: 517 documents, zero findings.
One material resolution choice is now with the user: `/mod y` from `x` when
both declared child `x.y` and root `y` exist. Ordinary language resolution is
recommended; the spec keeps this open until the ruling. QA readiness continues
independently; no source implementation has begun.

### Shared module resolution approved — 2026-09-29

User: “yes use language module name resolution (share code)”. This settles
child/root and alias resolution for `/mod`; it uses the language resolver,
not separate precedence code. Spec records the final rule (session
`319f7a65-9211-4410-b8dc-5c7e49133a00`). QA's reload readiness is complete:
three sound REDs, R1 acceptance allocation, navigation/fixture allocation.
Design(int) session `009dace3-25e7-467c-9281-2e79e35bf94f` groups ACT-1011,
ACT-1013 and navigation for a coherent correction. All roles remain Claude
Opus 5.5/high. Existing file-backed load-on-switch follows the current spec;
no redundant confirmation is requested.

Spec finalization and QA evidence reconciliation completed. QA session
`fabb6bc4-654e-488d-987c-548729d507ee` releases all seven REDs for correction;
R1 acceptance passes. Five affected binaries: 493 run, 486 pass, seven
expected failures. Design(int) completes one private correction with no
public API/schema/ABI change. Implementation consumes the final spec/QA
record rather than the design report's stale pending-spec note. Independent
review follows the delivered correction. New design probes (incremental
cycle admission and a new failed dependency added by a save) are kept within
the same mechanism and sent to dev's module evidence, with final QA judgment.

### Reload/navigation implementation green — 2026-09-29

Dev(src) `286e3150-3b51-45ba-9941-0898b6b90721` completes the private
correction. All seven REDs pass; full nextest: 6407 passed, zero failed,
one skipped (114 seconds). All eight canonical API baselines are +0/−0;
no confirmation is required. Source and Cargo released.
The first full run exposed four prelude/watcher regressions. Corrected
fallback-edge treatment passes its detection-proven module rows, 270 focused
cells and the full rerun. Design `821c23cf-5d74-4007-8728-2c96e2330a3e`
assesses that measured deviation; review `d67de14a-e79f-4de6-b876-6b84456bb11e`
independently checks final source. QA `2d424e3b-3f43-4010-9c5e-f386ec76847a`
owns final adequacy/fresh acceptance and the Cargo reservation. All use
Claude Opus 5.5/high. No phase transition or new carry is inferred.

### Reload basket accepted evidence; next decisions — 2026-09-29

Final QA `2d424e3b-3f43-4010-9c5e-f386ec76847a` accepts the delivered
change as checkpoint-quality, not complete basket closure. Canonical record:
[reload basket final adequacy](../tests/plan/s122-evidence-delta.md#reload-basket--final-adequacy-2026-09-29).
ACT-1010 is deleted as closed. ACT-1011/ACT-1013 retain two corrected faces
with permanent e2e evidence owed and two newly confirmed uncorrected faces.
ACT-1014 is new, pre-existing prelude/restart divergence intake. No carry is
authorized. QA allocates T1–T5 for one test visit. Source hash remains
`641989110118…b47788`, the reviewed/full-suite/QA tree; NOTES is unchanged.

Spec `7789dba2-f4f3-4074-b4f5-81ba4b43627a` checks P7 against the earlier
ACT-1005 ruling. Authorship order is already required; macro-order edge cases
were deferred without waiving it. The user now has the single scheduling
choice: correct ordinary ordering with an interim macro exception, or carry
ordering together with ACT-1005 to S123/S124 (recommended for one coherent
change). No answer, waiver or carry is inferred. ACT-1014's semantic question
will be framed separately; no second user question is bundled with P7.

### P7 carry approved; reload tails continue — 2026-09-30

The user approves carrying authored-order and structural-section-order
correction P7 with ACT-1005 to S123/S124. ACT-1005 now holds that exact scope,
first deferral for P7. Requirements remain unchanged; no other carry is
inferred. Sprint verified the mismatch in generate_module_source and §15.4.
Test receives QA's bounded T1–T5 allocation for ACT-1011/1013/1014. Spec
frames the prelude-dependency requirement question independently. The earlier
green source remains uncommitted; no new commit or phase transition is implied.

Test session `6a48d067-59bc-4018-a3e1-65af5a3751c4` completes T1–T5:
repl_persist 82 run, 78 pass, four intended REDs (macro-checkpoint cycle,
own-source startup failure via import and qualified references, prelude parity).
All 75 prior cells pass; five repeats preserve every polarity. Source is
unchanged from the accepted correction. The role's non-interactive permission
layer gated direct pre-fix test execution. Coordinator ran the exact two
commands through normal escalation successfully; both returned expected test
failure 101 on the prescribed assertions. Logs: prefix-t1.log and prefix-t2.log
in .local/s122-reload-tails-test-scratch. Prefix binary hash remains
`893bc444…83c1`. This closes the role report's T1/T2 observation gap; QA records
that evidence at its next visit. Source and Cargo are released.

Spec `3894c1e1-09b8-49d7-8e55-ba05d851d9a9` confirms ACT-1014 needs a
ruling: either implicit prelude imports form a cycle for prelude dependencies
unless they opt out, or those dependencies automatically receive no implicit
prelude. The user has this one question with both consequences; no answer
is inferred. The parity RED is independent of the choice. P7 carry remains
approved under ACT-1005. No commit, phase advance or additional carry occurred.

### Implicit-prelude dependency ruling — 2026-09-30

The user confirms that the implicit prelude import is a dependency and a
helper imported by the prelude forms a cycle unless it explicitly opts out
with `(import [prelude []])`. No automatic exception based on prelude reach
is approved. This supersedes the provisional reach-based design/implementation
rule in the current uncommitted correction. Spec records the rule; QA aligns
T5 and allocates fixture repairs with controls. T3/T4 remain current work.

Spec session `9af8eabd-56b5-4a82-bf84-d6d7065e5211` records the prelude
ruling; §8.8/§8.10 coverage is cleared for replacement. QA
`5c0b8023-89a4-45fe-ac3a-8a61f38ca7f6` releases PD1–PD3 and fixture
repairs. It also corrects its prior no-regression judgment: an explicit null
prelude import can fail on reload on the delivered source, while the prefix
build succeeds (ACT-1014 face B). This is included in the same dependency
predicate correction, not a carry. QA accepts T1/T2 pre-fix observations and
records the P7 carry. Design `1598abb2-8c23-4785-af5e-7d676166e42b` owns the
coherent T3/T4/prelude correction. All roles use Claude Opus 5.5/high.

QA `52e8ca5f-da40-4e8f-9f64-8d8ce2f072f0` rejects two proposed residuals
as existing requirements within this correction: export/FQ prelude cycle
diagnostics and dependency recovery before the type pass. No user decision
or carry is needed. Design revision `ebb8dc7e-4604-48d4-a516-8c0fea5c6946`
and test `3ef0e48b-31c5-4157-bffc-106be6288721` cover PD4/PD5/PD4c/T4-p0.
Test `5b360c5d-8209-4397-9f08-5b7a23bf6374` delivered PD1–PD3 and fixture
repairs: 147 run, 134 pass, 13 traced failures. Positive preconditions reveal
ACT-1014's null-import regression at startup too (prelude has a definition).
The same no-null-edge correction covers that publication path. QA files
ACT-1015 (declared-child/in-flight prelude) as separate unmeasured intake;
it does not gate this correction and is not an accepted carry.

Design revision `ebb8dc7e-4604-48d4-a516-8c0fea5c6946` removes the two
rejected residuals through the common attempt-failure exit. No public API
change is required. Test `3ef0e48b-31c5-4157-bffc-106be6288721` establishes
all four added cells RED, with preconditions holding; repl_persist 90 run,
79 pass, 11 allocated failures. PD4c also witnesses the null-import
publication false cycle at restart. Source and Cargo released for one src
implementation visit on the complete revised handoff.

Dev session `4e987c71-2904-4000-881d-7301b0263e78` implements the complete
revised handoff, Claude Opus 5.5/high. Test formatting session
`5c590fd8-18ed-4e35-8ad6-4d5a8b30a266` completes layout-only edits in three
test files without changing assertions or running Cargo. Final formatting
verification remains with the Cargo owner. During implementation the document
checker reports one stale QA citation to the retired prelude-exception unit
test; QA must reconcile it against the final source in its adequacy visit.

The targeted correction basket passes 151/151; unit verification passes
987/987 before allocated detection proofs and final full-suite verification.
Independent review session `adac13ef-3315-4630-b392-4338a5abdccc`
(Claude Opus 5.5/high) inspects src read-only while dev retains Cargo.

Dev completes at source hash `889b6d26…99e7c`: full suite 6440 passes, one
citation-drift failure, one skipped, 113.8 seconds. API baselines unchanged.
Review finds no blocking implementation defect, with R1 requesting QA
adjudication of two omitted module-evidence rows and A1/A2 design
reconciliation. QA `1d383c84-ca10-4b02-9267-2563ab8edc7f` owns fresh
acceptance and records; design `4e40ab37-9eb7-470b-9dd3-0eb689d53da4`
handles the design findings. Both use Claude Opus 5.5/high.

QA final adequacy closes ACT-1011/1013 and retains one helper-end module row
for ACT-1014. Review's transitive row is withdrawn as already covered.
A1's external probe did not reproduce the diagnostic issue in 48 runs;
design nevertheless selects file-derived aliases for the existing deterministic
walk contract. Dev followup `dc575945-9c20-4f9a-b381-7eb90b52a2cd`
(Claude Opus 5.5/high) owns that scoped realization, helper-end evidence and
source formatting/memory repairs. Root rustdoc succeeds with three warnings;
log is .local/s122-reload-tails-rustdoc.log. Source and Cargo remain with dev.

Followup dev completes at `d056842f…74ef53`: alias unit proved RED then GREEN,
source fmt clean; bounded run 1223/1224 passes. The allocated helper-side reload
row exposes a real follow-on defect and remains failing, unignored. QA
`36b7fef3-93d6-42b9-b970-5f8d395eba51` owns attribution/evidence and Cargo;
design `49920aac-6c2d-4f60-9965-bf3de7d3e2ec` selects the internal correction.
Both use Claude Opus 5.5/high. Final finding-scoped review will include the
alias change and any production follow-on correction together. No carry or
new user decision is inferred.

QA corrects the helper-end condition: restart can compile the helper while
failing the prelude, and reload must match. ACT-1014 therefore retains the
unresolved-name diagnostic defect, not a new helper-lock requirement. Design
selects Pass-0 fail-fast for imports/exports against failed modules. Dev
`ceba56fd-3b93-41e2-a468-8f23201f405f` (Claude Opus 5.5/high) owns that
correction and the repaired unit evidence. QA files ACT-1016 for separate
ordinary-module follow-on and export-cycle faces; it is unscheduled intake,
not a carry. Its disposition returns to the user after this correction.

Final correction: review `9afe9ade-b1cb-4bc2-abcd-e79f1f19391b` finds no
blocking or required findings on `f0d1006f…`; QA
`e2d9541b-b0a9-4f7d-9642-96ed32f6ef8e` closes ACT-1014, verifies 4412
bounded passes and reruns citation checks 3/3. The checker has 517 documents
and zero findings. Design status visit `1afa9461-0ed4-4f69-99a4-18d3992e5cd4`
records the delivered implementation; its pending-review/QA wording predates
these final reports and needs mechanical reconciliation at the next touch.
All roles use Claude Opus 5.5/high; source and Cargo are released. QA files
ACT-1017 for diagnostic location/prefix intake. ACT-1015/1016/1017 are not
accepted carries. Sprint returns ACT-1016 first for a fix-now/carry decision;
ACT-1017 follows separately. No commit or phase transition occurred.

### ACT-1016 carry — 2026-09-30

The user chooses “carry” for both ordinary-module cycle faces in ACT-1016.
First deferral, to S123 intake, owned by QA. The action retains the measured
reload/restart mismatch, export-cycle diagnostic defect and completion
criteria. No requirement changes or closure are implied. ACT-1015 and
ACT-1017 remain separate; the next user decision is ACT-1017. No commit or
phase transition is authorized by this carry.

### ACT-1017 carry — 2026-09-30

The user approves carrying ACT-1017's diagnostic location and repeated-prefix
finding to S123. First deferral; QA owns intake and its retained completion
criteria. The refusal remains correct; the misleading diagnostic is an
accepted residual. Sprint verified the scheduler error reconstruction and
REPL §5.1 before recording the carry. ACT-1015 remains unmeasured intake
requiring separate disposition. No commit or phase transition occurred.

### ACT-1015 carry and decision batching — 2026-09-30

The user approves carrying ACT-1015's unconfirmed scheduling investigation to
S123, first deferral, owned by QA. Sprint reopened the named design and
parent/child processing sequence before recording the carry. ACT-1015/1016/1017
are now all explicitly carried; no other item is deferred by implication.

The user directs that remaining decisions be batched, replacing the earlier
one-at-a-time preference. Present one consolidated review of unresolved
choices with context and recommendations; do not ask serial carry questions
or seek confirmation of decisions already recorded. No commit or phase
transition is authorized by these carries.

### Consolidated remaining disposition review — 2026-09-30

The user requests one final fix/carry proposal covering the remaining sprint
work. QA session `d4db3aa9-9db7-4529-a6df-0fadc550ba75` (Claude Opus
5.5/high) reconciles known residuals against current source, later evidence
and prior approvals. This is read-only on source, with no new investigation
or implementation. Existing carries stand; the proposal authorizes no new
carry, commit or phase transition. The review groups actual decisions apart
from routine cleanup and later-phase obligations.

QA completes the consolidated review without source changes or new probes.
The canonical proposal is [K1–K11](../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30):
K1–K4 finish missing-entry diagnostics, bounded ownership evidence, truthful
records and final verification; K5–K11 propose grouped S123 carries. Every
live filing was reread (35 FIXMEs, 46 actions). Prior approvals are preserved.
Source remains `f0d1006f…`; no full run exists on that final tree yet. This
proposal awaits one user decision. Legacy deferral counts are stated where
known; repeat carries require explicit approval as part of the package.

### Consolidated disposition approved — 2026-09-30

After reviewing the [K1–K11 proposal](../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30)
and asking what the scoped sprint delivers, the user answers “ok”. This
approves K1–K4 for completion within Phase 5 and the grouped K5–K11 S123
carries, including the disclosed repeat assurance carries. Previously approved
carries stand; no new semantic rule is inferred. The proposal's named owners,
limitations, revisit triggers and evidence remain the carry contract. Unknown
historic deferral counts remain unknown, not invented.

Execution: one test reservation owns K1 reproductions, K2 bounded evidence
and test-side K3 mechanical fixes. Design(int) settles K1's private correction
in parallel. QA records the approved disposition and performs QA-owned K3
cleanup without Cargo while test holds it. Dev(src) follows established K1
REDs/design. Later owned cleanup is batched by surface before K4 verification.
Memory-unsafe K2 findings return with attribution; ordinary confirmed leaks
are carried under K7. No phase transition or commit is approved by this scope.

Final-scope execution: test `fe6c043d-5f12-40a7-89f4-d693420b0d6e` owns
K1 REDs/K2 measurements/test K3 and Cargo. Design(int)
`6298e43b-46fa-4e46-b52f-2751da564639` delivers K1 §6.1.1 and reconciles
status; QA `3a73d4f0-8c97-4321-b92d-44984ef03980` records carries and retires
ACT-1002. Spec `94b03ece-47bb-41b6-b326-a22281909df9` repairs the /mem
mirror and discovery example (execution still owed). Design(backend)
`b21673ad-33df-4930-8262-822166dcdeca` removes the ACT-0958 dependency;
dev(backend) `d3008d69-dbe6-4a58-8015-44402e1f1da9` retires 0906. Arch
`ff93d81b-523b-496a-bb58-febeeae7687f` records its carries and consolidates
the discovery example; 0789 awaits one source-comment repair. Design(int)
`d25af535-d527-4bdf-a952-1225adf306cf` retires 0745 and marks 0708 resolved
pending cross-owner reference cleanup. All roles use Claude Opus 5.5/high;
no commit or phase transition occurred.

### 2026-09-30 — K2 attribution and structural-prevention direction

- QA (Claude Opus 5.5/high, session `0d3cdff1-1256-4cf6-9640-c479e3a22fcd`) attributes ACT-0974 to wrapper adaptation after a consuming extern shim. Permanent REDs and controls remain; source was unchanged and Cargo released.
- User approves fixing ACT-0974 and requests automatic prevention of the class through typing or other checks. `arch` session `a367c10b-4ab2-4e08-a025-e13d3ec3c918` assesses the contract and prevention guarantee before implementation; no API change is implicitly approved.
- `dev`(src), session `4684bba7-674b-4959-aa57-639117eab8c2`, implements approved K1 and related source record cleanup. Sole Cargo owner; architecture is read-only on code.
- QA records other K2 measurements and remaining disposition edges in the canonical evidence delta. No whole-sprint green claim or phase transition.

### 2026-09-30 — K1 delivered; ACT-0974 prevention proposal

- `dev`(src) completes K1 on source diff `fefd41e8c863c92d93212f7abd774ab612a0611516ee9119c9b90974516113d5`: 997 library and 114 focused integration checks pass. ACT-0976 remains an intended carried RED. No full-suite claim. Source and Cargo released.
- `review`(src), Claude Opus 5.5/high session `68157932-c03b-4995-bed2-aa4d6c5b4358`, independently checks the bounded K1/K3 delta.
- `arch` session `a367c10b-4ab2-4e08-a025-e13d3ec3c918` proposes a uniform consuming extern-primary-entry contract and typed backend convention derivation. Related `string-identity` leak observations require QA intake. Proposal is not approved yet; exact assessment is in `.local/s122-0974-prevention-arch-result.md`.
- User review is pending for that cross-crate semantic contract and the grouped carry of 0934 cancellation, 0694 Class I and ACT-1018. No implementation of the proposed contract has started.

### 2026-09-30 — ACT-0974 contract approved

- User explicitly approves the proposal after reviewing favourable impact, scope and limits: uniform consuming extern primary entry, structural shim parameter restrictions and backend-private typed convention derivation. Expected public API +0/−0; no schema or C ABI change.
- Approval concerns this ownership proposal. The separately queued grouped carry remains unanswered; no new question is raised now.
- K1 review has no blocking or required finding; QA judges it adequate. Commit and phase transition remain unauthorized.
- Dispatch arch to ratify canonical contract; backend and primitives design in parallel on their owned interiors. Follow with QA-allocated permanent REDs before sequential backend/primitives implementation and combined verification.

- Arch ratification session `14044088-a57f-4bdd-8ab0-4fd217bc4e88` records the approved contract and retires 0789. The serialized shape is unchanged; the landing requires a cache-version value bump to reject old machine code. The separate intrinsic-convention wording issue is retained for the consolidated review, not an ACT-0974 blocker.
- `test` session `651e843f-7701-4119-8cff-4560e32159a8` owns the SI evidence delta and K3 test mirrors. No behavioral source changes until test release.
- `design`(primitives) session `06d8e940-720d-4acb-bc71-3fdc4f490bc9` is implementation-ready. Sprint nominates `design`(primitives) as the sole writer for the ACT-0974 update to shared `design/runtime/s119-typed-consume-funnel.md`; perform alongside its final design-currentness pass.

### 2026-09-30 — ACT-0974 independent REDs established

- `test` session `651e843f-7701-4119-8cff-4560e32159a8`: SI-1 through SI-4 each fail with residual +1; SI-5/SI-6 and the original controls pass. Existing double-release REDs remain. No commit occurred. K3 test mirrors and the 0604 reach correction are delivered.
- Executing REPL §16.5 exposed a separate memory-unsafe tail-call binder case, retained in `tests/tail_call_branch_consumed_let_binder.rs`. QA session `fa9e9512-66d3-49e1-b099-a5e43cd98f7b` attributes it before any scope decision. No fix or carry of this new defect is implied.
- `dev`(backend) session `5226f25c-71b2-41d4-9565-3c85fa0218cf` implements approved ACT-0974. Primitives follows sequentially; no runtime suite between paired halves. QA uses prechange evidence and source snapshot while implementation is active.
- Design(int) retires0708 and reconciles K1. Design(primitives), nominated shared writer, updates the runtime mirror. Dev(stdlib) removes stale0815/0868 commentary without code changes.

### 2026-09-30 — tail-call intake for decision

- QA session `fa9e9512-66d3-49e1-b099-a5e43cd98f7b` records ACT-1021, confirmed unsafe symptom with provisional parameter-flush attribution. D1/D2 are required before implementation. A bounded test-and-fix decision is queued; it is separate from approved ACT-0974.
- ACT-1022 retains the companion ordinary-leak lead. The document checker is back to zero findings after QA repairs retired-witness citations.
- 0815 mirrors are resolved and the inventory delinked; QA may delete the filing. 0914 awaits demo replay after the paired ownership code lands.

- User approves ACT-1021 “Test and fix now”: establish D1/D2 after the ACT-0974 pair, then correct the confirmed mechanism. Backend review is consolidated after both corrections. No public API change or phase transition is implied.

### 2026-09-30 — ACT-0974 paired implementation verified

- Backend dev `5226f25c-71b2-41d4-9565-3c85fa0218cf` delivers the private entry convention across call paths and cache version31. Primitive dev `4ea0e307-405a-4904-9a87-16801f2267a7` delivers the Owned move and removal of borrowed shim conversion.
- Both halves together: SI10/10, backend/primitives711/711, existing witness8/8, cache72/72, adjacent357/357, CLIFgoldens unchanged, seven public APIs+0/−0. No full-suite claim. Independent primitive review `115728df-ce87-4f6b-ad9a-1b6f7ffcbcb4` is active; backend review follows ACT-1021 in one visit.
- QA readiness `6cc269b4-2ed5-45ef-98bf-7dc8cbc7112a` settles ACT-1021 evidence, including the slot-ownership correction and COW controls. Test `8b82defc-f3ce-40c7-b293-4044b63c82c2` now owns Cargo and executing evidence. New unallocated leads remain for the consolidated checkpoint.

### 2026-09-30 — ACT-1021 gate passed

- Test `8b82defc-f3ce-40c7-b293-4044b63c82c2` confirms D1RED/D2balanced and C-PTRED/C-LTGREEN. C-M is a pre-fix GREEN fence. Runtime source was unchanged during evidence; concurrent intrinsics rustdoc/test-metadata edits changed the broad hash, so future source reservations exclude even those edits during measurement.
- Dev(backend) `21ee6540-83e6-4a0c-8a98-4dd8170b0de5` implements approved ACT-1021, sole source/Cargo owner. QA `ca4c64cb-a34b-4608-80e9-e7a3cccbc3b7` records gate and separately classifies C-C2′ and W1 unsafe observations. Neither new case has a fix/carry decision yet; regression provenance is unresolved.
- Primitive review has no blocking code issue; its required two-note cleanup is complete. Safety register R22 records structural guarantees and limits without claiming whole-sprint acceptance.
- Intrinsics catalog K3 source/design mirrors are complete, with no runtime change; arch's ACT-0963 item1 retirement remains mechanical. The typecheck/frontend comment obligations are complete.

### 2026-09-30 — ACT-1021 regression held for correction

- Dev ACT-1021 fixes the target REDs and C-C2′, with backend613/613 and 120/122 focused checks. C-C2Consumed now leaks three allocations over three iterations; W1 remainsunsafe. C-M was vacuous due malformedsyntax.
- Acceptance remains blocked. Sprint routes C-C2 design correction to preserve the approved GREEN fence, not acceptance of the newleak. Test repairs C-M and executes already allocated checkpoint diagnostics for W1/C-C2′. No new carry is authorized.

### 2026-09-30 — consuming-COW correction ready for evidence

- QA `4d4f4530-c9a6-416a-b7a3-98d70eeb079a` settles the amendment delta: C-C1c must reproduce before implementation; C-IR guards the changed loop emission. The existing CLIF evidence discharges the design falsifier. Canonical allocation is in `tests/plan/s122-evidence-delta.md`.
- Checkpoint comparison corrects the earlier C-M claim: repaired C-M is RED at HEAD and GREEN after ACT-1021. C-C2′ belongs to ACT-1021; ACT-1023 folds into it after final verification.
- ACT-1024 is an attributed, pre-existing backend use-after-free affecting both parameters and ordinary let bindings. Its fix/carry decision is separately queued; no implementation is authorized yet.
- Test `a6254628-02e5-49c2-bc0b-0607cf214eab` owns the pre-development evidence visit and Cargo. All production source is frozen during measurement. Claude Opus 5.5/high; no commit or phase transition.

- User approves fixing ACT-1024 this sprint. Backend design assesses it alongside the pending ACT-1021 amendment; source implementation remains sequential because both touch the COW ownership seam. Existing evidence and scope are in ACT-1024 and the QA delta; no cross-crate semantic change is implied.

- Test `a6254628-02e5-49c2-bc0b-0607cf214eab` establishes C-C1c RED (one leaked block; correct result8) and C-IR GREEN (five reuse hits over five steps). HEAD confirms C-C1c's unsafe face. Cargo released; detailed evidence is `.local/s122-tail-cow-red-test-result.md`.
- Dev(backend) `097a2633-efe4-482d-a121-2e067cb65bce` implements the ACT-1021 amendment, sole source/Cargo owner. Design(backend) `a9b11982-e8b5-482e-bb5e-ace28ea23a4d` assesses approved ACT-1024 with source read-only. Both Claude Opus 5.5/high. No commit or phase transition.

### 2026-09-30 — ACT-1021 amendment delivered, alias gate held

- Dev `097a2633-efe4-482d-a121-2e067cb65bce`: tail family12/12; C-C2 and C-C1c fixed, detection plant fired and reverted, public API+0/−0. Backend614/615 is held by the existing match-alias control. Full suite6495/6502; exact failures and source provenance are in `.local/s122-tail-cow-dev-result.md`. No acceptance claim.
- Design `a19c9fa1-0baf-41b2-8d33-f565131f0553` resolves that concrete alias conflict. QA `d0c17294-2ee9-46c3-a295-d6f9a89f22b0` attributes additional golden frames, the mode-origin guard and the single worker failure, and consolidates the next evidence visit.
- ACT-1024 design `a9b11982-e8b5-482e-bb5e-ace28ea23a4d` is ready. QA `ad661c02-05cd-400e-8112-179bcb0ea1f9` allocates V1/V2. Arch `269ab375-d354-4ab9-834a-fe9af3b14e7c` confirms private realization only: no API or contract gate, no extra cache-schema bump. The old escape-gated realization is superseded by exact consuming-site ownership; R14's governing statement stays unchanged.
- All roles Claude Opus5.5/high. Dev releases source/Cargo. No commit or phase transition.

- User clarifies the security context: these are authorized local reproductions and corrections in our own Cranelisp compiler/runtime, intended to eliminate memory-safety defects. Subsequent role briefs include `.local/s122-owned-software-debugging-context.md`; command permissions remain handled through the approved execution route. Current work continues without interruption.

### 2026-09-30 — alias correction green; V1 underway

- Dev(backend) `ee150fe0-29b2-4644-9352-c614019180d1` delivers the shared match/let alias last-use rule. Backend617/617; A-T/A-V both flip GREEN, including linked-executable cases. Goldens remain byte-identical to QA's six attributed amendment captures; public API+0/−0. Source/Cargo released.
- Test V1 performs the combined ACT-1021 final evidence/golden update and ACT-1024 pre-fix reproductions. Source remains frozen. Future briefs explicitly identify authorized debugging of our own software; no renewed permission question is needed for those local reproductions.

### 2026-09-30 — V1 accepted evidence; match consequence held

- V1 test `e3c358a7-3989-4a0d-a6bd-7e8549978e37` verifies ACT-1021/alias families and establishes checkpoint A after the six-frame golden update. W1/W-P/W-L/W-LOOP reproduce before ACT-1024. W-M's apparent balance is cancellation, not valid evidence.
- QA `2528e568-1c2e-4a6b-9073-15ee77212047` attributes existing ACT-1026 binder-forwarding join leak and ACT-1027 match-arm copy use-after-free. The proposed ACT-1024 R3 consequence needs a design ruling before implementation. New fix/carry scope remains unapproved.
- Design `8acdf5cc-8b5a-4152-91a2-83c6590936af` prepares the coherent correction and user-reviewable scope; test `a9cece25-a2b5-4038-9de8-03dd5f3ef9f1` owns V1b permanent reproductions and W-M repair. Source frozen; Claude Opus5.5/high.
- Generated-cache purge exposes a stale illustrative cache-directory citation in examples guidance; route to its training owner. ACT-1025 and the cache-writer maintenance intake remain checkpoint items. No commit or phase transition.

### 2026-09-30 — concrete match scope decision ready

- V1b test `a9cece25-a2b5-4038-9de8-03dd5f3ef9f1` confirms D1-M/D1-L leak one block, D2-C/D2-R fail with unsafe faces, all controls balanced, and repaired W-M passes by cancellation. Source/Cargo released; `.local/s122-backend-v1b-test-result.md`.
- Design `8acdf5cc-8b5a-4152-91a2-83c6590936af` supplies the coherent ACT-1024 co-change: retire the match COW exception and treat the result as an ordinary owned temporary. This addresses ACT-1027 with the approved producer repair; exact proposal is `.local/s122-1024-r3-design-result.md`; the standing rule is [backend ownership codegen](../design/backend/ownership-codegen.md#137-cow-mutate-and-grow-branches--the-settled-contract).
- User decision queued: fix the unsafe paths with this co-change and carry ACT-1026's wider ordinary leak, or include ACT-1026 provenance redesign this sprint. Recommendation is the bounded unsafe-path correction plus explicit leak carry. No implementation of ACT-1024/R3 or ACT-1026 before that answer; no new scope is presumed approved.
- All dispatches identify authorized local debugging to secure our own software. No commit or phase transition. NOTES and `.agents` remain preserved.

### 2026-09-30 — unsafe-path correction and leak carry approved

- User agrees to the recommended scoped outcome: ACT-1024 with required match-exception retirement (option A), ACT-1027 verified alongside it, ACT-1026 carried to S123 with failing tests retained and widened leak exposure disclosed. This is scope approval within Phase5, not commit/phase-transition authority.
- QA settles the amended unit/end-to-end conditions and record dispositions before implementation. The V1b REDs and checkpoint A remain the evidence basis. A narrow training-owned repair addresses the generated-cache citation exposed by the clean-cache pre-step; no wider Phase6 training pass is started.

### 2026-09-30 — final unsafe-path implementation started

- QA `251410d4-a6e5-4880-876d-c2ad5fc99ef9` marks ACT-1024 with option A READY. L-CC's invalid comparator is withdrawn; the observed unattributed ordinary leak is preserved separately as deferred ACT-1028. D2-C's limited claim and V2 absolute-count diagnostics are explicit.
- Dev(backend) `0958e343-ca93-4132-8760-dcd4de72521c` now owns source/Cargo and implements the approved COW ownership plus match-exception retirement in one change-set. User requests proceeding from the written handoff. No commit/phase transition; Claude Opus5.5/high.
- Training `600fee5e-d14b-4e37-a7e8-ca3baecb8f37` repairs generated-cache guidance without exception debt. Document checker: 518 documents, zero findings after QA's records; NOTES unchanged.

### 2026-09-30 — unsafe-path fix implemented; independent gates active

- Dev `0958e343-ca93-4132-8760-dcd4de72521c` delivers ACT-1024+optionA/ACT-1027: two-state Borrowed/Owned source ownership, exact-site consuming claims, ordinary match temporary plan, deleted retain/reconciliation machinery. Backend617/617; affected168/170 with D1-M/D1-L accepted REDs at1; W1/W-P/W-L/W-LOOP/W-M/D2-C/D2-R GREEN. Public APIs+0/−0, schema unchanged, checkpoint A goldens unchanged. Source/Cargo released; `.local/s122-1024-dev-result.md`.
- L8's predicted runtime path is refuted: that shadowed site is copy-only and never reads classification. Site identity is still structurally pinned; design/QA reconcile this evidence claim. U-R3a's pre-fix failure was the arm release without a later protect. These are evidence/design corrections, not new scope.
- Independent review `8a97fb2b-62ff-4576-8ebd-957edfab3240` inspects the combined backend fixes. Test V2 `b3dbf551-5587-4ee8-802d-aa8ca38b6f22` owns executing evidence/Cargo with production source frozen. Design(backend) `af97536b-8049-4122-8ac7-78d58ef845f2` updates owned standing claims only. All Claude Opus5.5/high. No commit/phase transition.

### 2026-09-30 — independent unsafe-path verification passed

- V2 test `b3dbf551-5587-4ee8-802d-aa8ca38b6f22`: 178/180, only approved D1-M/D1-L REDs at1; all unsafe-path conditions GREEN, W-M exact1, SI10/10, publicAPI+0/−0, checkpointA goldens identical. Production source unchanged; logs and exact provenance retained in `.local/s122-backend-v2-test-result.md`.
- Combined review `8a97fb2b-62ff-4576-8ebd-957edfab3240`: no blocking introduced defect; R1 existing unmeasured alias-map face goes to QA, R2 grade corrected without runtimechange. Arch `22b18f97-6c7e-4964-8949-8957cd86af31` reconciles R14/R22/R1 using V2; producer Borrowed state structural, claimissuerrestriction asserted with namedfalsifier.
- Dev `498629e9-f7d8-4c4b-831c-7e4fd7c5ee0a` resolves false alias-map/U-R3a comments and ownedguidance; evidence shows comment-only diff, source released. Coordinator's `cargo fmt --all -- --check` passes through the local execution route after delegated formatting was unavailable.
- QA `158ac458-0c2f-4cfa-8fa7-7e4ad7992010` performs final adequacy/remainingK4 allocation. Typecheck design `2481e000-242f-475b-a61e-3ec1abc117ce` repairs retired escape-retain linkage; backend owned grade/currentness follows in its separate narrow deployment. No commit or phase transition.

### 2026-09-30 — bounded adequacy complete; final K4 prepared

- QA confirms the unsafe-path corrections adequate on independent V2 and review. ACT-1024/1027 and folded ACT-1023 filings are retired with the fixing change-set; ACT-0974 waits for standard-library composition and ACT-1021 for the full discovery replay. ACT-1026/1028 remain approved ordinary-leak carries.
- Review's existing alias-map prediction remains unmeasured, recorded as ACT-1029; QA declines an extra probe and carries its disposition to the phase checkpoint. No new confirmed defect or scope expansion is inferred.
- Architecture and backend design finish mechanical link/assurance repairs before the sole final K4 test visit. That visit combines full suite, agent lane, checkers, discovery replay armed/unarmed and memory-lifecycle demo. Claude Opus5.5/high; no commit or phase transition.

- Final K4 preconditions confirmed: backend/architecture repairs released, document checker516/0, source reservations released, index empty and NOTES hash unchanged. Test owns the sole executing/Cargo visit and captures final provenance plus generated-cache purge. No source changes while evidence executes; no extra probes, rebaseline or implicit carry approval.

### 2026-09-30 — final K4 execution complete

- Final test visit: full suite6510/6514 with exactly ACT-0976, ACT-1018 and ACT-1026 D1-M/D1-L REDs; all allocated unsafe-path cells GREEN, W-M exact1, goldens checkpointA unchanged, publicAPI+0/−0. Citation/coverage/document checkers0; REPL discovery replay armed/unarmed clean.
- Delegated host refused the agent/showcase commands. Coordinator executes those exact already-authorized checks locally after test released its reservation: agent81/81; showcase exit0 and closing /mem live+0. Tree/config provenance unchanged before/after; logs retained with test evidence. No permission-policy bypass or new scope.
- QA final adequacy and filing retirements follow. No commit, acceptance or phase transition inferred; remaining review basket is retained.

### 2026-09-30 — final Phase-5 adequacy recorded

- QA confirms all five K4 steps passed within the approved expected-RED set. ACT-0974/1021 and0914 filings retire with the fixing change-set; exact records remain in the QA delta. No runtime rerun follows mechanical links/status/narration repairs.
- Pending user checkpoint remains explicit: acceptance/Phase6a/commit; cancellation evidence0934, intermittent0694ClassI, ordinary-leak1018 confirmation, unmeasured1019/1020/1022/1029 and remaining L-leads, worker1025 and in-place cache-writer intake. Previously approved grouped carries stand.
- ACT-0963's catalog wording half is already retired; its remaining public-field contraction remains the approved S123K11 carry. This is separate from the intrinsic ownership wording question retained in safety registerR22.

### Phase-5 checkpoint proposal — pending user decision

The approved scope has QA adequacy on final K4. Proposed next: checkpoint the fixing change-set (excluding NOTES and the dirty shared package), accept the Phase-5 outcome, then advance to Phase6a for the user-facing assessment and scheduled read-only backend audit. This does not close S122.

Remaining decisions are batched below; none is approved by this proposal. Previously approved K5–K11, ACT-1015/1016/1017 and ACT-1026/1028 carries stand.

| Residual | Consequence / evidence | Recommendation |
|---|---|---|
| 0934 cancellation face | Unrun heap-payload Bind balances, but losing race/select heap-payload disposal has no executing witness | Carry evidence gap to S123 runtime QA |
| 0694 ClassI and ACT-1025 | Intermittent scheduler/worker observations are unattributed; neither recurred at K4 | Carry bounded attribution to S123; preserve observations and falsifiers |
| ACT-1018 and ACT-1022 | Sudoku warm solve retains51 allocations; unreduced match/branch lead reads+2. Neither shows an unsafe fault | Confirm ordinary-leak carry to S123, retaining existing failing evidence and requiring attribution for the lead |
| ACT-1019 / ACT-1020 | Unreadable entry may become empty source; dotted-entry file mapping requirements disagree. Not reproduced as defects | Carry requirement clarification and narrow reproduction to S123 |
| ACT-1029 / ACT-1030 and L2–L7/L9/L10 | The later probe observes ACT-1030’s control use-after-free; ACT-1029’s shadowing mechanism remains unconfirmed. Other L-leads remain unmeasured | User now defers ACT-1029/1030 investigation via ACT-1031; other L-lead carries remain proposed, not approved by that deferral |
| In-place cache writers | Some tests recreate ignored caches in checked-in fixture/example trees; K4 used purged caches | Carry test-directory isolation repair to S123 |
| Intrinsic ownership wording (R22) | The blanket consuming rule conflicts with borrowing trace_format; primitive extern-primary-entry contract is already approved | Limit uniform consumption wording to ExternShim primaries and describe named intrinsic ownership individually; user approves contract correction before arch edits |

The detailed evidence and limitations are [QA's final K4 record](../tests/plan/s122-evidence-delta.md#final-test-visit-k4--record-and-phase-5-adequacy-2026-09-30). The catalog inventory wording half of ACT-0963 is completed; its remaining public-field contraction already belongs to approved K11 and requires no repeat carry decision.

### 2026-09-30 — alias-map probe approved before closure

- After reviewing carry rationale and working-solution limits, the user agrees to probe ACT-1029 now. This replaces the proposal to defer that probe; it does not approve the earlier blanket carry/commit/phase package.
- QA settles one narrow shadowing-versus-renamed-binder evidence delta, then test executes it with memory checking enabled and caches disabled. Confirmed unsafe outcomes return with evidence and a concrete proposed fix before closure. No other L-lead investigation, source correction, API change, commit or phase transition is implied.

- First ACT-1029 test dispatch stops at a provider safety-classifier refusal before edits or execution; no evidence exists. User explicitly requests retry. The fresh test brief clarifies authorized own-compiler lexical-shadowing regression testing and defensive purpose, preserving host permission defaults and original narrow evidence scope.

### 2026-09-30 — shadowing probe runs; control fails

- Test retry executes the single permanent regression cell. Its renamed-binder control aborts under the reference-count checker with a use-after-free in vector copying after vector teardown; subject is unrun because the harness stops on the control.
- This confirms an observed unsafe failure, but neither confirms nor refutes the alias-name-overwrite lead. QA owns attribution and a bounded redesigned evidence delta. No source fix or new carry is presumed approved; existing full-sprint evidence is not a claim that this newly exercised shape is safe.

### 2026-09-30 — investigation deferred; session handoff requested

- User requests a lower model, then directs moving to another task and recording future ownership work. ACT-1031 records resumption of ACT-1029/1030; preserve the failing guard and unresolved unsafe observation. No follow-up probe or fix is running.
- User requests root session.md, now established as a temporary sprint-owned continuation handoff. Test-cache directory isolation is the recommended separate task; no new technical dispatch has started, and the exact lower model remains to be selected.
- This deferral does not authorize the earlier checkpoint package, commit, phase advancement or closure.

### 2026-09-30 — Phase-5 checkpoint approved; Phase 6a entered

The coordinator is now Claude Code (Opus 5.5). It reported that the approved
K1–K4 scope was complete and that the pending checkpoint was the blocker. It
recommended a commit, one carry decision and advancement. The user answered
“approved”. That covers:

- **Checkpoint commit** of the Phase-5 fixing change-set, excluding NOTES,
  the `.agents` submodule pointer and the retired `session.md`. Pre-commit full
  suite on the committed tree: 6,515 run, 6,510 pass, one skipped. The five
  failures are the accepted ACT-0976, ACT-1018 and ACT-1026 D1-M/D1-L guards,
  plus the ACT-1030 guard `vec_push_match_binder_same_name_shadow`.
  Log: `.local/s122-checkpoint-suite/nextest.log`. The filing retirements
  coupled to the fixes (ACT-0974/1021/1023/1024/1027, 0914) now hold.
- **Carries to S123, as proposed in the checkpoint table:** 0934
  cancellation evidence; 0694 Class I with ACT-1025; ACT-1018 and ACT-1022
  ordinary leaks; ACT-1019/1020 clarification and reproduction; the remaining
  L-leads alongside ACT-1031; test-cache directory isolation. `qa` records the
  targets and files any missing intake.
- **Intrinsic ownership wording (R22):** uniform consuming wording is limited
  to `ExternShim` primary entries. Named intrinsics are described one by one
  (`cranelisp_trace_format` borrows). `arch` makes the correction.
- **Phase 5 → Phase 6a.** This is not acceptance of whole-compiler memory
  safety. ACT-1030 is an open, observed unsafe failure.
- **Models:** the user directs “use Opus 5.5 and Sol 6.1 as far as possible
  with the right effort levels”. Opus-allocated roles dispatch natively
  (exact allocation). The Fable-allocated roles (`arch`, `qa`, `audit`,
  `review`) run under the per-run `claude_role.py --model claude-opus-5-5`
  exception, authorized by this direction. Shared effort stays `high`.
  Sol 6.1 (`gpt-6.1-sol`, Codex) has no route: `codex_role.py` refuses
  Claude-allocated roles, and the pinned package allocates every role to
  Claude. Using Sol needs a package reallocation, which is escalated to the
  user.

`session.md` has been absorbed into this plan and deleted.
