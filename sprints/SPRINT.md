# Sprint 63: Methodology Migration — Opening the §15 Transition Arc

**Status**: PHASE 1 SCOPE DRAFT

**Goal**: Open the methodology migration arc defined in `sprints/METHOD_PROPOSED.md` §15 — author the new per-crate-triad skill definitions and begin extracting per-skill content into its target homes.

## Scope

This is the first sprint of a multi-sprint arc transitioning from the legacy 15-skill cast (with five per-crate compiler skills `/frontend`, `/typecheck`, `/backend`, `/int`, `/platform`) to the 12-skill cast in `METHOD_PROPOSED.md` §2 (with one generic `/dev` narrow-deployed across all 6 crate-shaped surfaces, paired with `/design` and `/review` in the per-crate triad).

The sprint **does not** pre-commit to a fixed task list from §15. It picks up tasks in §15 order and lands what fits cleanly in one sprint; the rest chains into S64+. Refined as it unfolds.

### Likely scope (refined during Phase 1 + 2)

- **M1** — author `/dev`, `/design`, `/review` skill definitions from a shared narrow-deployment template.
  - `/arch` drafts the shared template; user approves before role-specific authoring.
  - `/arch` drafts each of the three skill defs from the template; user approves each before write.
  - `/review` is a **rewrite** of existing `.claude/commands/review.md` (currently coordination-shaped, no narrow deployment); the other two are new files.
  - **M1b deletion** of legacy skill defs (`/frontend`, `/typecheck`, `/backend`, `/int`, `/platform`) **deferred** until M9b + M9c content extraction completes.
- **M9a** — strip duplicated boilerplate (release gate, git discipline, testing ownership, design-doc obligation pattern) from every legacy skill def into METHOD or a shared skill-def appendix. Natural pair with M1: running M9a first clarifies what content remains in each legacy def for M9b/M9c to extract.
- **M9b** — extract per-skill *decisions / direction* content from legacy dev skill defs (e.g. `/backend` Sketch Consultation, `/int` slash-command list + Pass-1/Pass-2 model) into draft `design/{crate}/{crate}.md` overviews. Feeds M2 (per-crate design doc authoring).
- **M9c** — extract per-skill *conventions / API gotchas* (Cranelift v0.125 notes, parser gotchas like `-3` integer parsing) into per-crate `CLAUDE.md`. Feeds M8 (CLAUDE.md rework).
- **M11** — archive `sprints/reimplementation.md` (content is historical now). Cheap; can land any time.
- **M13** — confirm `cranelisp-runtime` ownership reassignment to `/dev` backend mode (paired with `cranelisp-backend`, not owned by `/platform`). Update any `CLAUDE.md` / design / sprint doc that says otherwise. Cheap; can land any time.

### Deferred to S64+ (sized too large for one sprint each, or dependency-blocked)

| Task | Rationale | Depends on |
|---|---|---|
| M1b — delete 5 legacy skill-def files | Blocked on M9b + M9c content extraction | M9b, M9c |
| M2 — author per-crate `design/{crate}/{crate}.md` overviews (6 crates × 0.5 day each) | 3-4 days; benefits from full M9b extraction | M9b |
| M3 — types-crate consolidation (cross-crate types + traits + Decision log) | ≥1 sprint on its own | — |
| M4 — `cargo-public-api` setup + CI gate | 0.5 day setup; pairs with M3 | (loosely) M3 |
| M5 — `pub(crate)` downgrade pass | 1 sprint, mechanical across all crates | M3 (must know what crosses crate boundaries) |
| M6 — facade-module pattern per crate | 1 sprint | M5 |
| M7 — inline `FIXME(/skill)` → `sprints/fixmes/NNNN-*.md` migration | 0.5–1 day; opportunistic slot | — |
| M8 — `CLAUDE.md` rework (root + per-directory) | 0.5 day per skill; chases M9c | M9c |
| M10 — memory retirement | 0.5 day | M8 + skill defs landed |
| M12 — METHOD_PROPOSED.md → METHOD.md rename (METHOD.md archived) | 0.1 day; closes the arc | All other M-tasks done |

### Carries from S62 (held in baseline ledger; not addressed this sprint)

The post-migration concurrency sprint resumes the S62 work product:

- 4 partial design docs (`design/int/concurrency-{architecture,audit,risks,test-strategy}.md`) + `design/int/concurrency/` diagrams committed in the S62 close commit.
- 7 baseline-ledger entries (H6 residue, harness ceiling, 5× Defect 6 family, exemplar entry).
- Wave-1 gate open items (phantom `OnceLock<TraceFilter>`, `cached_modules` dual-store, Decision 3X ratification).
- FIXME(/typecheck) at `crates/cranelisp-typecheck/src/checker.rs:205`.
- Defect 6 implicit 4× deferral — explicit user sign-off required when next picked up.

### Showcase

**Waived** per the three-clause precedent recorded in S62 close:

1. The sprint produces no executable artefact — skill defs and content extraction are process / design / convention changes, not code.
2. Prior-sprint demos replay green as regression guards (verified at close).
3. The next implementation sprint picks up the showcase burden for the combined delivery (the post-migration concurrency sprint, or whichever is first to ship user-visible code).

## FIXME debt

No carried FIXMEs from `sprints/fixmes/` — the file-based FIXME store does not yet exist (M7 introduces it). Inline `FIXME(/skill)` comments throughout the project are the current state and will be migrated in M7. None block this sprint.

| FIXME | Target skill | Status | Notes |
|---|---|---|---|
| (none) | — | — | M7 stands up the `sprints/fixmes/` store; until then inline FIXMEs are tracked via grep |

## Architecture review (Phase 2)

{To be filled by `/arch` in Phase 2.}

`/arch` review focus per `METHOD_PROPOSED.md` §15 task ownership table:
- M1, M9a, M9b, M9c — `/arch` is named owner. Confirm shared template shape; identify any cross-crate concerns the new triad must surface.
- M13 — `/arch` confirms runtime ownership reassignment per §15.

## Skill plans (Phase 3)

{To be filled by each invoked skill in Phase 3. Likely invocation list:}

- **`/arch`** — draft shared narrow-deployment template + the three new skill defs (M1); identify boilerplate-strip targets (M9a); confirm runtime ownership (M13).
- **Each retiring legacy skill** (`/frontend`, `/typecheck`, `/backend`, `/int`, `/platform`) — extract own *decisions / direction* content for M9b and *conventions / API gotchas* content for M9c, before the legacy skill def is eventually deleted in a later sprint.
- **`/sprint`** — archive `sprints/reimplementation.md` (M11); update `METHOD.md` cross-references as the new skill defs land.
- **`/qa`** — no in-sprint code-test work; but `/qa` reads the new `/dev`, `/design`, `/review` skill defs once drafted and confirms they preserve the testing-ownership boundary (`METHOD_PROPOSED §8.1`: unit tests by implementing skill, integration tests by `/qa`).
- **User-proxy skills** — no Phase 6b new demo (showcase waived); confirm at close that prior demos still replay green.

## Waves (Phase 4)

{To be organized after Phase 3 plans land. Provisional sequence:}

### Wave 1 — M1 template + skill-def drafts

| Skill | Crate | Task | Status |
|---|---|---|---|
| /arch | — | Draft shared narrow-deployment template; user approves | pending |
| /arch | — | Draft `/dev`, `/design`, `/review` skill defs from template; user approves each | pending |

### Wave 2 — M9a boilerplate strip

| Skill | Crate | Task | Status |
|---|---|---|---|
| /sprint | — | Identify duplicated boilerplate across all 15 legacy skill defs | pending |
| /arch | — | Decide where boilerplate lives (METHOD vs shared appendix); user approves | pending |
| Each legacy skill | — | Strip own boilerplate; replace with reference | pending |

### Wave 3 — M9b/M9c content extraction (per legacy skill, parallel)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /frontend | cranelisp-frontend | Extract decisions → draft design doc; conventions → CLAUDE.md | pending |
| /typecheck | cranelisp-typecheck | Same | pending |
| /backend | cranelisp-backend | Same (incl. cranelisp-runtime per M13) | pending |
| /int | src/ | Same | pending |
| /platform | cranelisp-platform | Same | pending |

### Wave 4 — Cleanup (M11, M13) and close

| Skill | Crate | Task | Status |
|---|---|---|---|
| /sprint | — | Archive `sprints/reimplementation.md` (M11) | pending |
| /arch + /sprint | — | Confirm `cranelisp-runtime` ownership documented as `/dev` backend mode (M13) | pending |
| /sprint | — | Update `sprints/METHOD.md` to reflect what landed; flag what remains for S64+ | pending |
| User-proxy skills | — | Replay prior demos green (showcase waiver regression guard) | pending |

## Notes

- **Methodology pivot context**: `sprints/METHOD_PROPOSED.md` is the target methodology; `sprints/METHOD.md` is the current consolidated state. The arc opening here rebuilds the skill cast against the proposed model. METHOD_PROPOSED is renamed to METHOD only when M12 lands (last task in the arc).
- **`/sprint` boundary**: cannot edit `.claude/commands/`. M1 skill-def authoring is delegated to `/arch` per §15 task ownership. `/sprint` orchestrates wave gates, gathers user approvals, and updates `sprints/METHOD.md` (its own owned file) as the arc progresses.
- **Iterative scoping**: the §15 task table estimates "4–6 sprints across skills" total. S63 anchors the opening; S64+ scope is clarified as S63 unfolds (which tasks fit, which spill, which surface new dependencies).
- **No code changes expected**. The three skill defs are markdown files; the boilerplate strip and content extractions are pure documentation moves. `cargo nextest run` is not on the gate path for this sprint.
- **Concurrency work is paused, not abandoned.** S62 close commit preserves the four partial design docs + 8 mermaid diagrams as durable input for the post-migration concurrency sprint.

## Outcome (Phase 7)

{To be filled at close.}

### Delivered
- TBD

### Deferred (with rationale)
- TBD

### Findings (record in FIXMEs if not already)
- TBD
