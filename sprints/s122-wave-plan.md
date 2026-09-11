# S122 execution waves

Phase 4 organization and Phase 5 implementation were authorized 2026-09-10.
This is the active Phase-5 execution plan. Scope and the exact
88-filing closure allocation remain in [SPRINT.md](SPRINT.md). The
[QA delta](../tests/plan/s122-evidence-delta.md) owns Q1–Q14, E1/E2 and D7 evidence.
ACT-0959 is the approved future public-allocation assessment, outside this
sprint's original inventory and not a prerequisite for delivery.

## Scheduling and retained owners

Source edits and compiler test/build processes run serially. Independent
read-only inspection and nonoverlapping document work may run concurrently.
Retain one dev owner per crate through its dependency pauses; distinct crates
receive separate invocations even when the same agent executes them. Test
retains one reservation for shared solution fixtures/helpers and the eval runner.
A reservation grants only selected paths and attributed corrections, not a
whole-crate rewrite. The original filing allocation is not duplicated here.

| Reservation | Selected writable surface and combined obligations | Release condition |
|---|---|---|
| Shared package | Proposed shared document checker and its unit fixtures under `.agents/tools/`; bounded ACT-0957 missing-contract/SIGTERM evidence and affected package guidance | Shared candidate and existing package residual evidence reviewed; local package changes retained for later publication approval |
| Solution tests | Selected `tests/` files, fixtures, helpers, scripts and produced CLIF goldens; proposed eval runner/corpus and shared-checker CLI integration | Each affected compiler consumer is evidenced; local eval smoke/report and document-checker adoption complete |
| Types | `crates/cranelisp-types/` only if a source-verified selected remainder requires code; otherwise arch reconciles contracts/filings | Existing producer contracts confirmed; any actual approved delta and consumer evidence complete |
| Frontend | `crates/cranelisp-frontend/` selected annotation/reader records and any attributed language defect | Relevant repro/control and owner records settled |
| Typecheck | `crates/cranelisp-typecheck/` selected ownership/mono/traits/form paths; 0779 private drain unit and attributed language/replacement corrections | Producer and downstream evidence complete; reservation retained if a downstream dependency remains |
| Intrinsics | `crates/cranelisp-intrinsics/src/` typed handle/funnel callers and guards, IO Select evidence, attributed runtime correction | Typed consumers in primitives/backend/int work; module and Q3/Q4/Q11 evidence complete |
| Primitives | `crates/cranelisp-primitives/src/` declaration/body ownership plus int/bool/float/string/marshal construction, borrow and storage seams | Exact D8 bounds and shared guard pass with producer, parent/child and macro evidence |
| Backend | `crates/cranelisp-backend/src/lib.rs`, Vec lowering, launch fixture and any attributed correction | Result-root/Vec/typed fixture evidence, affected golden handoff and review complete |
| Binary/int | Selected `src/` reload/redefine/worker, macro/quote, result-owner and REPL command paths; selected integration guidance | Q1/Q2/Q3/Q6–Q9 and attributed language obligations settled; approved wrapper removal verified |
| Platform | `crates/cranelisp-platform/`, selected platform fixtures only if attribution requires changes | Q12 coexist/load/link evidence or source-backed nondefect disposition; no assumed naming rewrite |
| Language consumers | Separate dev invocations for selected `stdlib/` or `exemplar/` paths if reduced evidence attributes there | Omitted shapes/def application and original workload evidence complete |
| Standing records | Each directory's owning role; sprint owns delivery/host guidance, QA owns evidence/ratchet, arch owns architecture and public contract inventory | Repairs joined to their source stream; shared-document inventory, references and filing outcomes reconciled |

Root-library wrapper removal stays with Binary/int implementation and arch's
public-surface check. Executable-bundle changes are conditional on an actual
approved consumer need, not presumed by this reservation. No agent production
change is selected: the eval harness uses the existing process interface.

## Wave 1 — discriminate failures and expose maintenance findings

1. Test reduces existing generic scalar/vector replacement and sequence-IO
   failures with the QA-selected controls (Q1/Q3); preserves the original public
   witnesses. Add missing derive/curry/def-application and platform identity
   discriminators (Q10/Q12). QA attributes each mechanism before assigning a
   corrective design. Independent ready cases need not wait for unrelated ones.
2. Capture the existing macro residue and original workload observations before
   ownership changes (Q4/Q5). Reuse the recorded baseline where comparable;
   remeasure only where the QA allocation requires a fresh before-state.
3. Test authors the bounded eval runner/task corpus and stub grading checks
   (E1), using the same actual process path intended for live runs. It may
   report known compiler failures; it does not require their fixes to exist.
4. Test establishes D7 CLI fixtures; shared-tool dev implements the approved
   [checker contract](../design/arch/s122-shared-document-checker.md), its unit
   evidence, and ACT-0957's separate package test residuals. Run the candidate
   read-only against both projects, producing full discovery and explicit
   old/new Cranelisp finding mappings. Magic uses temporary configuration;
   neither its working tree nor the shared upstream is changed.

These are sequential source reservations, not simultaneous writers. Emit the
shared-checker findings early so document owners repair them during their
existing visits. Keep the old citation gate until cutover. Wave 1 exits with
ready mechanisms attributed and their correction designs routed, a working
local eval slice, and candidate checker evidence/findings. An unresolved
mechanism remains an explicit bounded investigation with its reserved owner;
no speculative correction or silent carry follows from elapsed time.

### Phase-5 scheduling adjustment: ready Q1 slice

The Q1 prior-realization discriminator and corrective design settled before
Q10/Q12. Test released source/build ownership after the Q1/Q3 handoff. Execute
the independent Binary/int original-candidate replacement slice now, retaining the same
owner for the later typed-runtime consumer tail. The runtime-dependent tail
keeps the Wave-3 dependency order; no cross-context contract changes.
Q1 rematerializes within its first ordinary publication; it does not use a
post-publication reload/cascade. Q7 persisted-source reload stays separate. Q10/Q12
and Q3's allocated intrinsics module attribution witness follow the live
reservation order in SPRINT.md. Complete the already-approved shared Q1/D1
real-compile failure evidence in this same Binary/int visit before independent
review; preparation-only candidate drop does not settle rollback.

Review exposed an omitted same-type generic replacement and its producer
completion dependency. The bounded Q10 repros completed during that design
interval so attributed typecheck work could share its visit; all selected
current shapes pass. A distinct typecheck invocation completes ownership
inference through the existing demand API before Binary/int resumes. No new
public delta or weakening of ABI admission is authorized by this scheduling
change. The live sprint record owns exact evidence and reservation state.

### Approved callable-identity dependency sequence

The user-approved [symbol-table identity packet](../design/arch/s122-overload-reorder-publication.md)
adds a bounded producer/consumer sequence to the ready Q1 slice: types,
typecheck, Binary/int, then actual backend key/cache dependencies and solution
evidence. The producer/consumer implementation, public cache/link evidence and
review-directed corrections are complete; the live sprint record carries the
results. The user confirmed the exact generated baseline on 2026-09-10, completing this
identity checkpoint.
This sequence retains the later runtime migration; it does not authorize a wholesale backend
label rename. Generated public-baseline changes return to the user before this
wave passes.

### Current maintenance handoff

Current reservations, completed evidence and unresolved gates live in the
[active sprint](SPRINT.md). The user-approved
[information map and retention policy](METHOD.md#31-where-things-live) govern
D7 cleanup: assess canonical content, fold useful missing substance, retire
superseded originals and establish retained documents. QA and architecture
apply it to representative areas before wider consolidation.

## Wave 2 — complete necessary compiler producers

Visit types only for verified remainder, then frontend and typecheck as required
by the Wave-1 attribution. Combine all selected incoming obligations per crate:
0779's private polarity unit belongs in the typecheck visit; already-delivered
concreteness, cache and demand APIs are verified, not reimplemented. New defects
receive their discriminating module RED before correction. Existing successful
producer evidence is reused rather than copied into new subprocess tests.

The known reload consumer uses the already-existing instantiate-demands API.
No types or typecheck rewrite is a prerequisite merely because an old filing
mentions that surface. If attribution exposes a different actual dependency,
arch names it and sprint adjusts only the affected sequence before writing.
Any new public delta or semantic choice returns for explicit approval.

Exit: selected producers and their local evidence are ready, filings have
source-backed dispositions, and downstream reservations retain any unfinished
consumer-dependent evidence. This is not permission to release an incomplete
stream or claim the full compiler is green.

## Wave 3 — one continuous runtime-to-consumer migration

Execute this exact dependency order:

1. **Intrinsics:** approved handles, nine consuming funnels, current internal
   callers, exact mint/borrow/storage guard allocation, and Q11 ready-loser
   evidence. Include any independently attributed runtime correction here.
2. **Primitives:** typed declaration bodies and all selected consumers; exact
   approved D8 construction/adoption, parent-lifetime borrowing and storage
   transfer. Scalar fields, reused references, nullaries and the existing
   quote error sentinel retain their distinct contracts.
3. **Backend:** canonical result-root and Vec guard consumers plus the launch
   fixture using typed consume-closure; combine any attributed backend fix.
4. **Binary/int:** reload complete-demand staging, approved public wrapper
   removal, macro transfer/quote convergence, result ownership and /mem,
   private real-compile failure-before-publication evidence, and attributed
   replacement/language corrections in the same retained visit.

The approved producer-first exception permits temporary compile failures while
these reservations remain open. No intermediate compile failure is a completed
handoff; inspect it for expected stale consumers before continuing. Do not run
unrelated full suites against a deliberately incomplete migration. Test updates
its affected fixtures/goldens in coordinated pauses; no compiler owner edits
solution-test files by convenience. The original macro workload is remeasured
after the full path works, preserving the approved trap-forfeiture limit.

Separate dev invocations complete platform or stdlib/exemplar corrections only
where Wave 1 attributed a real remainder. Insert them before their dependent
consumer is released; do not park known obligations until after stream closure.

Exit: integrated migration compiles; allocated local and solution evidence pass;
independent review and QA conditions are satisfied per completed surface.
Generated API changes return for confirmation against exact prior approvals.
Mechanical auto-trait baseline contraction is reported separately from functional
changes across the seven baselines. Intrinsics's typed delta and the root
wrapper removal retain their specific checks; private D8 adds no public rows.

## Wave 4 — finish adoption and evaluate delivered behavior

Finish shared-document declarations and owner repairs accumulated since Wave 1.
Re-run full discovery, reference checks and old/new source-check comparisons on
the final tree. Present any specific proposed residual exceptions before
adoption; do not create baseline entries to force a pass. Switch the local
invocation and reconciled ratchet together; remove the duplicate checker code,
retaining at most a delegating launcher. Historical records stay inventoried
and owned; their historical outgoing links are explicitly excluded and counted.
Live links into archives still resolve. No adapter generator is added.

Complete local eval smoke and report validation on the repaired compiler. Before
any live request, present one concrete D6 run configuration: supported provider,
model/endpoint, disclosed task material, autonomy, repeats and bounded budget.
Then run only the approved configuration and retain all-attempt outcomes with
compiler/provider failures classified. Stub success is not a model baseline.
Failure to obtain a live run does not silently satisfy the baseline outcome.

Each original filing receives its allocated owner disposition with current
source/evidence; resolve/delete only when its own closure criteria hold.
ACT-0947's approved scratch cleanup is complete after the source-owner check,
retaining NOTES; see [the closure record](SPRINT.md#runtime-before-state-and-scratch-cleanup).
The future ACT-0959 stays open. Specific unsatisfied obligations return
to the user rather than being erased by aggregate green results.

## Wave 5 — composition and Phase-5 acceptance checkpoint

From the delivered tree, run the required default nextest suite and affected
isolated agent lane, with required network authority for socket evidence.
Run appropriate changed-surface build/lint/API checks; avoid repeating all
surface tests without a new failure or changed condition. Confirm role wiring,
shared document checks, exact filing accounting and final eval provenance.
Use a fresh build/session for acceptance; retain exact source/configuration and
results. Expected stocktake failures are not accepted as permanent exclusions.

QA judges the allocated conditions and remaining limits; independent review
covers material source/API/ownership changes, using a fresh reviewer who did
not author them. Complete source-stream reviews before this composition gate;
this wave is not their first inspection. Unexpected failures reopen only the
owning stream and affected evidence. Return the delivered outcome and request
Phase 5 → Phase 6a. Backend is the selected Phase-6a audit context; docs/training
assessment, subsequent repairs and close operations retain their later gates.

## Authorized Phase-5 operations

The user authorized implementation of these waves on 2026-09-10 using the established native role
allocation: Astra/medium for arch, QA and audit; Sol/high for design, dev, test
and review; Sol/medium for spec/docs/ops when needed. Exact dispatch identities
and reservations are recorded when assigned. Source writes/builds remain serial.
Temporary local fixtures, local shared-package candidate changes, Cranelisp
adoption and approved scratch cleanup are included. Live eval requests await
D6; new public deltas and actual generated-baseline confirmations retain their
gates. Magic writes, upstream publication, commits and pushes are not included.
