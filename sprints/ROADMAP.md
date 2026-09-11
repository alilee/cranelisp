# Cranelisp Delivery Roadmap

Owner: sprint. This roadmap records delivery direction and future sequencing.
The [active sprint](SPRINT.md) owns current execution; [architecture guidance](../design/arch/CLAUDE.md)
owns technical contracts, and the [test plan](../tests/plan/PLAN.md) owns assurance.

## Phases

| Phase | Description | Status |
|-------|-------------|--------|
| A | Extract: spec completion, architecture contracts, QA plan | COMPLETE |
| B | Scaffold: crate structure, interfaces, CLAUDE.md files, experience specs | COMPLETE |
| C | Ring 0 — Core: expressions, types, functions, let, if, match | COMPLETE |
| D | Ring 1 — Heap: strings, ADTs, closures, reference counting | COMPLETE |
| E | Ring 2 — Abstraction: traits, modules, constrained polymorphism | COMPLETE |
| F | Ring 3 — Meta: macros, derive, standard library | COMPLETE |
| G | Ring 4 — Effects: IO, platforms, parallelism, REPL, caching | COMPLETE (S80 closeout; pre-H mainline cleared through S83; **full IO auto-parallelism wired + witnessed S85** — FIXME 0367 resolved, the deferral closed) |
| H | Release compiler: reliability, ownership/memory-model and release-performance work. | Active; current scope is S122. Future performance work follows its measured re-entry conditions below. |

## Sprints

The [active sprint](SPRINT.md) owns current scope, approvals, execution status
and remaining work. [Closed sprint records](archive/) own dated outcomes,
evidence and carries; a closed sprint does not imply an all-green release or
resolution of every carry. The current action and legacy-filing registers,
linked from root guidance, retain unresolved obligations.

Ordinary working history is recoverable from [the earlier roadmap](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/sprints/ROADMAP.md).
Sprint 26 has no standalone archive file; its pipeline-adapter outcome is
recorded in [Sprint 27's context](archive/sprint-27.md#context) and that historical
roadmap.

## Forward Plan

### Current sprint — S122

S122 is in approved Phase 5. The [active sprint](SPRINT.md) owns live delivery
status and approvals; its [wave plan](s122-wave-plan.md) groups known-issue
closure, document conformance and the REPL-agent evaluation baseline by source
owner. The [candidate inventory](s122-candidate-inventory.md) preserves the
opening assessment of 88 filings and audit findings; its recommendations are
historical inputs, not current status. LLVM is excluded by user direction.
Delivery-role models follow the shared allocation linked from root guidance.

The approved limited private allocation ownership change proceeds within S122.
[The full public allocation API redesign](actions/ACT-0959-public-allocation-api-redesign.md)
is a future scoping item; it does not block the limited change. Other unresolved
obligations remain in the current sprint and action/filing registers.

## Delivery history and retained direction

### Pre-Phase-H consolidation arc — COMPLETE (S86 + S87) — Phase H scope decided

The language-facing rebaseline and hygiene outcomes are retained in
[Sprint 86](archive/sprint-86.md) and [Sprint 87](archive/sprint-87.md).
Current user documentation, examples and the exemplar have their own root-linked
owners; the old rebaseline plan is not an additional maintenance checklist.

### Agentic-REPL track — capability ladder (S88 → S90; first track after the pre-H arc)

The capability ladder delivered in [S88](archive/sprint-88.md),
[S89](archive/sprint-89.md), [S90](archive/sprint-90.md) and
[S91](archive/sprint-91.md) is recorded in those outcomes. The
[embedded-agent architecture](../design/arch/repl-embedded-agent.md) owns the
capability model; current evaluation work is scoped in S122.
Self-tuning and automated curation remain deferred by user direction; the
existing log/trace is the manual-insight substrate. This is separate from
establishing repeatable evaluation.

### Phase H sequencing — the effect-concurrency track precedes `--release` (S87, user direction 2026-06-21)

The user ordered the agent track before effect concurrency, then the release
compiler work. Release optimizations must respect the settled concurrency and
ownership models; their contracts live in the architecture documents linked
below. The dated track sequence is preserved in the closed sprint records.

### Effect-concurrency track — delivery sequence (ratified S92)

The [effect-concurrency contract](../design/arch/effect-concurrency.md) owns
the model and its current implementation limits. The original slice outcomes
and platform transitions are retained in [S92](archive/sprint-92.md),
[S93](archive/sprint-93.md), [S94](archive/sprint-94.md),
[S95](archive/sprint-95.md), [S96](archive/sprint-96.md),
[S97](archive/sprint-97.md) and [S98](archive/sprint-98.md).
The optional developer-facing strand inspector remains unscheduled; the
contract retains its observability context. Old ABI transition plans do not
specify the current platform contract.

### Compiler-internal concurrency race — ✅ RESOLVED (S93, the reactor gate)

The [Sprint 93 record](archive/sprint-93.md) owns the race correction and its
reactor-gate evidence. Subsequent concurrency, memory-model and usability
outcomes are in the closed S94–S107 records, including the
[S105 measurement outcome](archive/sprint-105.md) and
[S106 performance-track disposition](archive/sprint-106.md).

The suspended performance work has one current home: the
[performance backlog](../design/arch/backlog/performance.md), with retained
analysis and re-entry triggers. Its consolidation does not schedule it.
The later [`/learn` specification action](actions/ACT-0951-specify-learn-feature.md)
owns the prerequisite for tutorial-engine implementation; old Phase-H forecasts
do not supply that approval.

### Phase H — ownership-inference delivery sequence (designed S100, ratified at S100 close)

The ownership design and initial read/write-path delivery are recorded in
[S100](archive/sprint-100.md), [S101](archive/sprint-101.md),
[S102](archive/sprint-102.md) and [S103](archive/sprint-103.md). The later
[S104](archive/sprint-104.md) and [S105](archive/sprint-105.md) measurements
changed the parallel-floor premise; the old per-sprint forecasts are not
current acceptance gates.

The [ownership-inference contract](../design/arch/ownership-inference.md)
owns technical staging. The [performance backlog](../design/arch/backlog/performance.md)
owns suspended work and re-entry triggers. Multi-field scalar replacement and
register-resident loop locals remain possible future scope, subject to a new
sprint decision. No release backend implementation is authorized by this
roadmap; LLVM is outside the user's current direction.

### Testing-driven defect-fix umbrella — S108 ✅ CLOSED 2026-07-12

Delivered scope, evidence, accepted limitations and carries are retained in
[the Sprint 108 record](archive/sprint-108.md).

### Broad batch — written-type-var semantics + dotted-ctor + defect/audit hygiene — S109 ✅ CLOSED 2026-07-15

Delivered scope, evidence, accepted limitations and carries are retained in
[the Sprint 109 record](archive/sprint-109.md).

### Backend pure keyed-lookup consumer (0583 centrepiece) + src-audit hygiene drain — S110 ✅ CLOSED 2026-07-16

Delivered scope, evidence, accepted limitations and carries are retained in
[the Sprint 110 record](archive/sprint-110.md).

### vec-assoc COW ownership root + backend audit-drain + quasiquote normative + memory-safety-soundness finding — S111 ✅ CLOSED 2026-07-18

Delivered scope, evidence, accepted limitations and carries are retained in
[the Sprint 111 record](archive/sprint-111.md).

### The 0628/I-C compiler wave — corrected §5.1.2 multi-sig inference + the settled trait/impl kind model — S112 ✅ CLOSED 2026-07-19

Delivered scope, evidence, accepted limitations and carries are retained in
[the Sprint 112 record](archive/sprint-112.md).

### Reliability risk-first + the S112 defect-family drain — S113 ✅ CLOSED 2026-07-20

Delivered scope, evidence, accepted limitations and carries are retained in
[the Sprint 113 record](archive/sprint-113.md).

### The typed resolution carrier + full S113-ledger drain — S114 ✅ CLOSED 2026-07-20

Delivered scope, evidence, accepted limitations and carries are retained in
[the Sprint 114 record](archive/sprint-114.md).

### Stabilise — clean & green + the assertion ladder + the constructor-form ruling arc — S115 ✅ CLOSED 2026-07-22

Delivered scope, evidence, accepted limitations and carries are retained in
[the Sprint 115 record](archive/sprint-115.md).

### Safety First, Settled Syntax — S116 ✅ CLOSED 2026-07-23 (explicit carry)

Delivered scope, evidence, accepted limitations and carries are retained in
[the Sprint 116 record](archive/sprint-116.md).

### Conformance and Recovery — S117 ✅ CLOSED 2026-07-25

Delivered scope, evidence, accepted limitations and carries are retained in
[the Sprint 117 record](archive/sprint-117.md).

### Instrumented Ownership Closure — S118 ✅ CLOSED 2026-07-26 (descoped by user to the mechanism collapse)

Delivered scope, evidence, accepted limitations and carries are retained in
[the Sprint 118 record](archive/sprint-118.md).

### The Non-Concrete Release Contract — S119 ⚠️ CLOSED SHORT 2026-08-29 (user-directed; Phase 5 at zero waves)

Delivered scope, evidence, accepted limitations and carries are retained in
[the Sprint 119 record](archive/sprint-119.md).

### FIXME 0917 Provenance Correction and Role-System Proof — S120 ✅ CLOSED 2026-08-31

Delivered scope, evidence, accepted limitations and carries are retained in
[the Sprint 120 record](archive/sprint-120.md).

### Release rebaseline and FIXME closure — S121 CLOSED 2026-09-09

Delivered scope, evidence, accepted limitations and carries are retained in
[the Sprint 121 record](archive/sprint-121.md).

### Pipeline v3 migration — COMPLETE (Sprints 29-38)

Steps 1-10 + 14 delivered. Single-pipeline invariant established. ~2,100 lines of v1 code deleted. Steps 11-13 (concurrency) deferred indefinitely. Step 15 (new main.rs) retired — substantially delivered by Step 6. See `design/arch/archive/pipeline-v3-roadmap.md` §Post-Migration for full assessment.

### Methodology migration — historical S63 schedule

The current [delivery method](METHOD.md), root role declaration and shared
role package replace the S63 migration schedule. Earlier progress is retained
in [the S63 record](archive/sprint-63.md) and the subsequent closed records.
The remaining legacy filing register drains under the current method;
retiring the old migration schedule does not close those obligations.

### Pipeline v4 migration — historical delivery

Root guidance identifies the scheduler-driven pipeline as the sole live
pipeline. The [S58 convergence outcome](archive/sprint-58.md) and later closed
records retain migration evidence. Current mechanisms live in the
[architecture](../design/arch/CLAUDE.md) and integration designs; the old
migration forecast does not schedule further work.

### Ring 4 acceptance criteria gap analysis (verified 2026-04-16)

This was a dated S56-era assessment. Its detailed snapshot remains in the
[historical roadmap](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/sprints/ROADMAP.md).
Current assurance and unresolved evidence obligations are maintained by QA in
the [test plan](../tests/plan/PLAN.md); later Phase-G outcomes are in the closed
records. Removing the old snapshot does not certify today's suite.
