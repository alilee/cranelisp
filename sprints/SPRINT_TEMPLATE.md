# Sprint {ID}: {Title}

**Status**: PHASE 1 SCOPE DRAFT | AWAITING PHASE 2 APPROVAL | PHASE 2 ARCH REVIEW | AWAITING PHASE 3 APPROVAL | PHASE 3 DESIGN | AWAITING PHASE 4 APPROVAL | PHASE 4 WAVE ORG | AWAITING PHASE 5 APPROVAL | PHASE 5 LANGUAGE | AWAITING PHASE 6A APPROVAL | PHASE 6A ASSESSMENT | AWAITING PHASE 6B APPROVAL | PHASE 6B ACTION | AWAITING PHASE 7 APPROVAL | PHASE 7 CLOSE | COMPLETE

**Goal**: {one-sentence sprint goal}

**Audit**: {bounded context — filled at Phase 4 from the rotation, METHOD §2.7; dispatched read-only in the Phase 6/7 window → `audits/{context}-s{ID}.md`; disposed next sprint Phase 1}

## Phase approvals

No work belonging to a phase starts until its transition row records explicit
user approval. The checkpoint names the completed result, next-phase scope,
roles, external operations and exit condition; a link to an exact conversation
turn or dated quotation is sufficient evidence.

| Transition | Checkpoint presented | User approval | State |
|---|---|---|---|
| Start → Phase 1 | {initial framing request} | {date/reference} | approved |
| Phase 1 → Phase 2 | {scope outcome + Phase-2 proposal} | — | pending |
| Phase 2 → Phase 3 | {architecture outcome + Phase-3 proposal} | — | pending |
| Phase 3 → Phase 4 | {readiness outcome + Phase-4 proposal} | — | pending |
| Phase 4 → Phase 5 | {wave plan + Phase-5 proposal} | — | pending |
| Phase 5 → Phase 6a | {accepted delivery + Phase-6a proposal} | — | pending |
| Phase 6a → Phase 6b | {assessment + action proposal} | — | pending |
| Phase 6b → Phase 7 | {delivered artifacts + exact close operations} | — | pending |

## Scope

{What this increment delivers. Must be testable, not scaffolding. State
exclusions, permitted external operations and acceptance basis. Out-of-scope
deferrals are listed explicitly with rationale and target sprint.}

## Evidence authority

{Carry QA's classification into each checkpoint. Diagnostic observers and
maintenance checks are reported but do not become product acceptance gates.}

| Condition or instrument | Class | Governing authority | Result / state |
|---|---|---|---|
| {condition} | acceptance / safety fence / diagnostic observer / maintenance | {requirement, design invariant or owned artifact} | pending |

## FIXME debt

{Open FIXMEs from `design/arch/fixmes/` carried into this sprint, plus any filed during the sprint. Reference by number; do not duplicate file content.}

| FIXME | Target role | Status | Notes |
|---|---|---|---|
| 0042 | `design` | open | … |

## Architecture review (Phase 2)

{Filled by `arch`. Technical coherence, interim-architecture risk, public-API impact, scope adjustments. Verdict + required revisions.}

## Role plans (Phase 3)

### `role-name`

- **Task**: {what this role does in this sprint}
- **Crate** (if narrow-deployed): {cranelisp-frontend | cranelisp-typecheck | cranelisp-backend | cranelisp-primitives+intrinsics | cranelisp-platform | src/}
- **Design refs**: {spec sections, design docs, FIXMEs to read}
- **Acceptance**: {how to verify the task is done}

{Repeat per invoked skill.}

## Waves (Phase 4)

### Wave N — {description}

| Role | Crate | Task | Status |
|---|---|---|---|
| `role` | {crate or —} | task | pending / in-progress / done |

{Repeat per wave.}

## Dispatch log

{One row per named-role dispatch. The recorded model and effort must match the
definitive shared allocation; the harness records where that allocation ran.}

| Wave | Agent | Surface | Model | Effort | Harness |
|---|---|---|---|---|---|
| W1 | `test` | sprint-wide | {shared allocated model} | high | {primary/cross-harness} |

## Notes

{Runtime log: blockers, scope changes, decisions, FIXME activity, gate events,
and any missing dispatch tooling escalated to the user.}

## Outcome (Phase 7)

### Delivered
- {what shipped}

### Deferred (with rationale)
- {item — why deferred, target sprint, escalation count}

### Findings (record in FIXME's if not already)
- {unexpected observations, methodology lessons, skill feedback}
