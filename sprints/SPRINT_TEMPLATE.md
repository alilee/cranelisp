# Sprint {ID}: {Title}

**Status**: PHASE 1 SCOPE DRAFT | PHASE 2 ARCH REVIEW | PHASE 3 DESIGN | PHASE 4 WAVE ORG | PHASE 5 LANGUAGE (ACTIVE) | PHASE 6A ASSESSMENT | PHASE 6B ACTION | PHASE 7 CLOSE | COMPLETE

**Goal**: {one-sentence sprint goal}

**Audit**: {bounded context — filled at Phase 4 from the rotation, METHOD §2.6; dispatched read-only in the Phase 6/7 window → `audits/{context}-s{ID}.md`; disposed next sprint Phase 1}

## Scope

{What this increment delivers. Must be testable, not scaffolding. Out-of-scope deferrals listed explicitly with rationale and target sprint.}

## FIXME debt

{Open FIXMEs from `design/arch/fixmes/` carried into this sprint, plus any filed during the sprint. Reference by number; do not duplicate file content.}

| FIXME | Target skill | Status | Notes |
|---|---|---|---|
| 0042 | /design | open | … |

## Architecture review (Phase 2)

{Filled by /arch. Technical coherence, interim-architecture risk, public-API impact, scope adjustments. Verdict + required revisions.}

## Skill plans (Phase 3)

### /skill-name

- **Task**: {what this skill does in this sprint}
- **Crate** (if narrow-deployed): {cranelisp-frontend | cranelisp-typecheck | cranelisp-backend | cranelisp-primitives+intrinsics | cranelisp-platform | src/}
- **Design refs**: {spec sections, design docs, FIXMEs to read}
- **Acceptance**: {how to verify the task is done}

{Repeat per invoked skill.}

## Waves (Phase 4)

### Wave N — {description}

| Skill | Crate | Task | Status |
|---|---|---|---|
| /skill | {crate or —} | task | pending / in-progress / done |

{Repeat per wave.}

## Notes

{Runtime log: blockers, scope changes, decisions, FIXME activity, gate events.}

## Outcome (Phase 7)

### Delivered
- {what shipped}

### Deferred (with rationale)
- {item — why deferred, target sprint, escalation count}

### Findings (record in FIXME's if not already)
- {unexpected observations, methodology lessons, skill feedback}
