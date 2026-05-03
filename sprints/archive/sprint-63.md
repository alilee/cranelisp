# Sprint 63: Methodology Migration — Opening the §15 Transition Arc

**Status**: COMPLETE — M0 delivered; arc continued informally into adjacent /arch + /design + /qa work; M-sequence superseded by emergent execution

**Goal**: Open the methodology migration arc defined in `sprints/METHOD_PROPOSED.md` §15 — author the new per-crate-triad skill definitions and begin extracting per-skill content into its target homes.

**Boundary relaxation (this sprint only)**: User authorized `/sprint` to edit `.claude/commands/` for M0 + M1 skill-def authoring. Normal `/sprint` boundary (no `.claude/commands/` edits) resumes from S64. /arch is the named owner per METHOD_PROPOSED §15; the relaxation lets `/sprint` execute that authoring directly given the arc-opening nature of these tasks.

## Scope

This is the first sprint of a multi-sprint arc transitioning from the legacy 15-skill cast (with five per-crate compiler skills `/frontend`, `/typecheck`, `/backend`, `/int`, `/platform`) to the 12-skill cast in `METHOD_PROPOSED.md` §2 (with one generic `/dev` narrow-deployed across all 6 crate-shaped surfaces, paired with `/design` and `/review` in the per-crate triad).

The sprint **does not** pre-commit to a fixed task list from §15. It picks up tasks in §15 order and lands what fits cleanly in one sprint; the rest chains into S64+. Refined as it unfolds.

### Likely scope (refined during Phase 1 + 2)

- **M0** (NEW, COMPLETE) — `/arch` skill-def deep rewrite + canonical doc set authoring + existing-doc triage. Pre-M1 boundary contract: M1's triad narrow-deploys to the 6 crate-shaped surfaces and needs the boundary contract first.
  - W1: `.claude/commands/arch.md` rewritten (136 → 204 lines). Restructured per METHOD_PROPOSED §3.1 + §5 + §13. Bounded-context table for 6 surfaces (Binary = `src/` + `crates/cranelisp-exe-bundle/`). Facade specs vs facade convention split. `@design/arch/principles.md` auto-import. Phase 7 principle review codified.
  - W2: `/arch` invoked under new skill def (reflexive validation). Authored `principles.md` (148), `bounded-contexts.md` (249), `overview.md` (128 — skeleton), `facades/{frontend,typecheck,backend,runtime,platform,int}.md` (6 files, 809 lines). Trimmed `design/arch/CLAUDE.md`. Archived `codegen-convergence.md` + `ast-annotation-examples.md` (`git mv`). Surfaced 6 W1 defect notes + 4 cross-skill FIXMEs.
  - W2.5: All 6 W1 defects addressed in arch.md (now 204 lines). 4 FIXMEs filed in `sprints/fixmes/0001..0004`. Both `sprints/fixmes/` and `design/arch/decisions/` directories now stand (partial M7 + partial M3).
- **M1** — author `/dev`, `/design`, `/review` skill definitions from a shared narrow-deployment template.
  - `/arch` rewrite (M0) is the boundary contract that M1 narrow-deploys against.
  - The shared template is captured implicitly via the rewritten `arch.md`'s structure + `bounded-contexts.md` + facade specs; M1 doesn't author a separate template document.
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

`sprints/fixmes/` directory was created during M0 W2.5 (partial M7 standup). Four FIXMEs filed during M0 W2 by `/arch`. None block remaining S63 work.

| FIXME | Target skill | Status | Notes |
|---|---|---|---|
| 0001-non-exhaustive-repr-c-interaction | /arch | open | Affects M6 (facade refactor); needs decision before M6 lands. |
| 0002-typecheck-types-reexports | /arch | open | Affects M5 (`pub(crate)` downgrade); convenience re-export rule needed. |
| 0003-backend-compile-to-module-design | /design | open | Resolves in M2 when `design/backend/{backend}.md` is authored (S64+). |
| 0004-super-import-decisions-candidacy | /arch | open | Migration unblocked (decisions/ dir live); cheap; can land any time in S63 or carry to S64. |

Legacy inline `FIXME(/skill)` comments throughout the project remain pending the full M7 sweep (still S64+).

## Architecture review (Phase 2)

Performed reflexively during M0 W2 — `/arch` was invoked under its own newly-rewritten skill def to author the canonical doc set and triage existing `design/arch/`. The successful W2 invocation (all deliverables produced in one pass; 6 minor defect notes against the W1 rewrite, all addressed in W2.5) constitutes Phase 2 sign-off for M0.

**M13** confirmed in `arch.md` §The crate-shaped surfaces ("Runtime ownership note") — runtime is owned by `/dev` narrow-deployed in backend mode, not by `/platform`. Stale references in `CLAUDE.md` files / older sprint docs sweep as M13 proper lands (cheap, can carry to S64).

`/arch` review focus for remaining S63 work (M1, M9a, M9b, M9c):
- M1 — `/arch`'s rewrite IS the boundary contract; review of M1-authored triad defs ensures they correctly narrow-deploy against `bounded-contexts.md` + `facades/{crate}.md`.
- M9a/b/c — boilerplate strip + content extraction are mechanical against the legacy 5 skill defs; `/arch` reviews the resulting per-crate `design/{crate}/{crate}.md` drafts and per-crate `CLAUDE.md` updates for cross-crate coherence.

## Skill plans (Phase 3)

{To be filled by each invoked skill in Phase 3. Likely invocation list:}

- **`/arch`** — draft shared narrow-deployment template + the three new skill defs (M1); identify boilerplate-strip targets (M9a); confirm runtime ownership (M13).
- **Each retiring legacy skill** (`/frontend`, `/typecheck`, `/backend`, `/int`, `/platform`) — extract own *decisions / direction* content for M9b and *conventions / API gotchas* content for M9c, before the legacy skill def is eventually deleted in a later sprint.
- **`/sprint`** — archive `sprints/reimplementation.md` (M11); update `METHOD.md` cross-references as the new skill defs land.
- **`/qa`** — no in-sprint code-test work; but `/qa` reads the new `/dev`, `/design`, `/review` skill defs once drafted and confirms they preserve the testing-ownership boundary (`METHOD_PROPOSED §8.1`: unit tests by implementing skill, integration tests by `/qa`).
- **User-proxy skills** — no Phase 6b new demo (showcase waived); confirm at close that prior demos still replay green.

## Waves (Phase 4)

### Wave 1 — M0 boundary contract (COMPLETE)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /sprint | — | Rewrite `.claude/commands/arch.md` (W1) | done |
| /arch | — | Author canonical doc set + triage existing `design/arch/` (W2) | done |
| /sprint | — | Apply 6 W1 defect fixes; file 4 FIXMEs (W2.5) | done |
| /sprint | — | This SPRINT.md update (W3) | done |

### Wave 2 — M1 triad skill defs

| Skill | Crate | Task | Status |
|---|---|---|---|
| /sprint | — | Author `.claude/commands/dev.md` against bounded-contexts + facade specs | pending |
| /sprint | — | Author `.claude/commands/design.md` against bounded-contexts + facade specs | pending |
| /sprint | — | Rewrite `.claude/commands/review.md` to narrow-deployment shape | pending |

User approves each skill def at its respective gate before the next is authored. /arch's rewrite (M0) is the boundary contract; the three new skill defs reference `design/arch/bounded-contexts.md` and `design/arch/facades/{crate}.md` rather than duplicating content.

### Wave 3 — M9a boilerplate strip

| Skill | Crate | Task | Status |
|---|---|---|---|
| /sprint | — | Identify duplicated boilerplate across the 5 retiring legacy skill defs (`/frontend`, `/typecheck`, `/backend`, `/int`, `/platform`) | pending |
| /arch | — | Confirm boilerplate destination (METHOD_PROPOSED appendix, or referenced from new triad defs) | pending |
| Each retiring legacy skill | — | Strip own boilerplate; replace with reference | pending |

### Wave 4 — M9b/M9c content extraction (per legacy skill, parallel)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /frontend | cranelisp-frontend | Extract decisions → draft `design/frontend/{frontend}.md`; conventions → `crates/cranelisp-frontend/CLAUDE.md` | pending |
| /typecheck | cranelisp-typecheck | Same | pending |
| /backend | cranelisp-backend | Same (incl. cranelisp-runtime per M13) | pending |
| /int | src/ + crates/cranelisp-exe-bundle/ | Same | pending |
| /platform | cranelisp-platform | Same | pending |

### Wave 5 — Cleanup (M11, M13) and close

| Skill | Crate | Task | Status |
|---|---|---|---|
| /sprint | — | Archive `sprints/reimplementation.md` (M11) | pending |
| /sprint | — | Sweep stale references to `/platform`-owned runtime in `CLAUDE.md` / sprint docs (M13 proper) | pending |
| /sprint | — | Update `sprints/METHOD_PROPOSED.md` Phase 7 to mention principle-review touchpoint (per arch.md §Sprint participation) | pending |
| /arch | — | Phase 7 principles review per `arch.md` §Sprint participation | pending |
| User-proxy skills | — | Replay prior demos green (showcase waiver regression guard) | pending |

## Notes

- **Methodology pivot context**: `sprints/METHOD_PROPOSED.md` is the target methodology; `sprints/METHOD.md` is the current consolidated state. The arc opening here rebuilds the skill cast against the proposed model. METHOD_PROPOSED is renamed to METHOD only when M12 lands (last task in the arc).
- **`/sprint` boundary relaxation (this sprint only)**: User authorized `/sprint` to edit `.claude/commands/` for M0 + M1. Normal `/sprint` boundary resumes from S64. The relaxation lets `/sprint` execute arc-opening skill-def authoring directly given /arch's recursive role (rewriting its own def is awkward to delegate to itself; downstream invocations of /arch in W2 then validate the rewrite reflexively).
- **Iterative scoping**: the §15 task table estimates "4–6 sprints across skills" total. S63 anchors the opening; S64+ scope is clarified as S63 unfolds (which tasks fit, which spill, which surface new dependencies).
- **No code changes expected**. The three skill defs are markdown files; the boilerplate strip and content extractions are pure documentation moves. `cargo nextest run` is not on the gate path for this sprint.
- **Concurrency work is paused, not abandoned.** S62 close commit preserves the four partial design docs + 8 mermaid diagrams as durable input for the post-migration concurrency sprint.

## Outcome (Phase 7)

The sprint opened the methodology migration arc (M0 as planned) and then **substantially overshot the M-sequence** into adjacent /arch configuration closure + /design refreshes + /qa test plan work. Some commits in the latter portion labelled themselves "Sprint 64" — a forward-looking misnomer; SPRINT.md was never formally rolled forward, so all work in this period is captured as Sprint 63's outcome.

### Delivered

**M0 — boundary contract (as planned)**
- `.claude/commands/arch.md` rewritten (W1)
- Canonical doc set authored: `principles.md`, `bounded-contexts.md`, `overview.md`, `facades/{frontend,typecheck,backend,runtime,platform,int}.md` (W2)
- `design/arch/CLAUDE.md` trimmed; `codegen-convergence.md` + `ast-annotation-examples.md` archived (W2)
- 6 W1 defects addressed (W2.5)
- `sprints/fixmes/` and `design/arch/decisions/` directories stood up (partial M7 + partial M3)

**Sequence diagrams established as first-class arch artefacts**
- `.claude/commands/arch.md` §"Sequence diagrams" — lockstep maintenance rule
- Currency sweep across diagrams against post-Sprint-64 facades (commit `fdda4a3`)

**Decision register slim** (active set: 9, down from ~40)
- Decisions 0014/0015/0017 deleted (retracted/superseded)
- 23 + 4 + 2 Decisions moved to `legacy/decisions/` across three commits
- Methodology established: re-derivation from Principles + canonical doc set should suffice; explicit Decisions persist only for environmental constraints, pre-implementation commitments, and forward handoffs

**Principles 14 + 15 added**
- Principle 14 — FFI boundary types governed by `ABI_VERSION` (covers `#[repr(C)]` AND `#[repr(transparent)]`); `#[non_exhaustive]` rule does not apply
- Principle 15 — Facade types live with their behavior; `cranelisp-types` holds only multi-implementation-crate consumers; no umbrella crate; `cranelisp-platform` external-audience exception explicitly permitted
- Both indexed in `principles.md`; `.claude/commands/arch.md` §Facade convention updated with both rules

**Facade refresh (all 6) per Principles 14+15 + Decisions 41/42**
- frontend, typecheck, backend, runtime: replaced "Re-exports from cranelisp-types" sections with "Types originated here"
- platform: kept re-exports under explicit external-audience exception cite; #[non_exhaustive] DTOs section restructured into Exempt/Carries
- runtime: IoTraceTag/IoTracePayload renamed to IoEventTag/IoEvent (matches GotEvent pattern in backend facade)

**Per-crate /design refreshes (all 6 — substantial overshoot of original M2 schedule)**
- design/frontend, design/typecheck, design/backend (committed prior sessions)
- design/runtime, design/platform, design/int (committed `8313b31`)
- Subordinate-doc triage executed: design/platform/runtime.md (mis-located) deleted; design/int/concurrency/ archived; 32 int subordinate docs triaged (11 archive / 9 refresh / 12 keep)

**/qa test plan refresh (committed `32291fc`)**
- Two-tier strategy pinned (e2e against exe + per-crate unit; no middle session-construction tier)
- New `tests/plan/PLAN.md` (spec→tests bridge), `tests/plan/helpers.md` (Cranelisp builder API design), `tests/plan/ledger.md` (renamed from baseline.md)
- 8 superseded plan docs archived to `tests/plan/legacy/`
- Ring axis retired from /qa-owned annotation convention (Sprint 63 user decision: all ring-envisaged functionality delivered; project in maintenance/extension mode)

**FIXME bookkeeping**
- Closed 12 FIXMEs (0001/0002/0004/0005/0048/0053/0091/0092/0093/0094/0095/0097/0105/depth-limit; 0007/0014/0015/0017/0020/0028 deleted as retracted)
- Filed 16 active FIXMEs (0098-0115) for /dev, /spec, /arch, /sprint follow-up work
- Active register holds environmental + pre-implementation + forward-handoff items only

**Strategy memories saved**
- `memory/project_test_strategy.md` — two-tier test strategy (no middle session-construction tier)

### Deferred (with rationale)

| Original M-task | Disposition | Rationale |
|---|---|---|
| M1 — triad skill defs (`/dev`, `/design`, `/review`) | Substantially landed in prior session work — `.claude/commands/dev.md`, `design.md`, `review.md` all exist; no further authoring needed | Was structured as draft-from-template; actual landing was incremental |
| M9a — boilerplate strip from legacy skill defs | Not actioned this sprint — legacy 5 skill defs (`/frontend`, `/typecheck`, `/backend`, `/int`, `/platform`) still exist alongside `/dev` triad | Defer to S64+ — low priority while triad operates well; no active blocker |
| M9b — extract decisions → per-crate `design/{crate}/{crate}.md` | Substantially absorbed by the 6 per-crate /design refreshes that ran this sprint | Original task became unnecessary — design docs were authored fresh, not extracted |
| M9c — extract conventions → per-crate `CLAUDE.md` | FIXME 0102 filed for runtime CLAUDE.md (only crate that lacks one); other crates have working CLAUDE.md content | Defer to S64+ as `/dev` work |
| M2 — per-crate design overviews (6 × 0.5 day each) | All 6 done as part of the /design refreshes | Originally scoped for S64–S65; landed in S63 |
| M3 — types-crate consolidation | FIXME 0100 filed (relocate single-consumer types per Principle 15) | Defer to S64+ as `/dev` work; covered by Principle 15 going forward |
| M5/M6 — `pub(crate)` downgrade + facade module pattern | Not actioned | Defer to S64+; M3 (FIXME 0100) lands first |
| M7 — inline FIXME → file migration | Partial standup happened (`design/arch/fixmes/` directory live; ~16 file FIXMEs created) | Full sweep of inline FIXMEs to S64+ |
| M8/M10 — CLAUDE.md rework + memory retirement | Not actioned | Defer to S64+; chases M9c |
| M11 — archive `sprints/reimplementation.md` | Not actioned | FIXME 0114 covers similar concern (ring-axis retirement implies reimplementation.md is historical) |
| M12 — METHOD_PROPOSED → METHOD rename | Not actioned | Last task in arc; defer until M-sequence formally closes (informal close with this sprint outcome may be sufficient) |
| M13 — runtime ownership confirm | Confirmed in `arch.md` during M0 W2; sweep of stale references deferred to S64+ | Cheap; opportunistic |
| Concurrency work (S62 carries) | Untouched — preserved in `design/int/concurrency/` per S62 close | Defer to post-test-port sprint per FIXME 0115 |

### Findings (record in FIXMEs if not already)

All findings tracked by filed FIXMEs:

- **0098** (`/dev`) — Multi-crate `ResolutionGap`/`CheckError`/`ExpansionError` migration (frontend + typecheck + types + int)
- **0099** (`/dev`) — GotObserver implementation (backend + int)
- **0100** (`/dev`) — Relocate single-consumer types per Principle 15 (types → typecheck/backend/runtime; rewrite int imports)
- **0101** (`/sprint`) — Runtime + platform audit pass after Decision 40 relocation lands
- **0102** (`/dev`) — Author missing `crates/cranelisp-runtime/CLAUDE.md`
- **0103** (`/dev`) — `trace.rs` + `io_trace.rs` relocation per Decision 40
- **0104** (`/dev`) — `PlatformError` adoption per Decision 42
- **0106** (`/design`) — Archive `platform-registry-removal.md`
- **0107** (`/dev`) — `#[non_exhaustive]` on `OwnedPlatformFnDescriptor`
- **0108** (`/dev`) — Relocate `display.rs` from backend to int per BC §6
- **0109** (`/dev`) — Decompose int god-files (`session_v4.rs` + `worker.rs`)
- **0110** (`/int`) — `Cranelisp.toml` + CLI knobs (workers, no-cache, no-times-in-prompt) for test-ordering control
- **0111** (`/int`) — Trace output channel separation (line-prefix or separate trace files)
- **0112** (`/int`) — REPL ready sentinel for stdin scripting (stable prompt shape, explicit flush)
- **0113** (`/spec`) — Strip ring annotations from `spec/*.md` headings
- **0114** (`/arch`) — Update root `CLAUDE.md` annotation convention to drop ring axis
- **0115** (`/sprint`) — **Sequence dedicated test-port sprint BEFORE any crate-refactor sprint** — lock-in: refactors that change `session_v4`/`worker` internals must not run while tests reach into those internals

### Principle review (Phase 7 per `arch.md` §Sprint participation)

The 13 Principles in force at sprint open were extended by 2 (14 + 15) — both addressing real architectural questions surfaced by Sprint 64-shaped work (FFI types vs source-level guards; type ownership across crate facades).

No Principle was found inadequate during sprint execution. Principles 7 (single source of truth), 11 (single pipeline + mode parameters), and 13 (interfaces.md is auditable) all proved load-bearing in the per-crate /design refresh work.

### Showcase (waived per S62 precedent)

Verified at close: prior demos still replay green. Skill defs and content extraction produced no executable artefact requiring a new demo. The next implementation sprint (the test-port sprint per FIXME 0115) picks up the showcase burden.

### Next sprint candidates

Per FIXME 0115's sprint-sequencing lock-in:

1. **Sprint 64**: prep `/int` work (FIXMEs 0110/0111/0112) — three independent items, half-day each. Could land as a small `/int`-only sprint OR be bundled into the test-port sprint's Phase 0.
2. **Sprint 65**: dedicated test-port sprint per FIXME 0115 — build e2e harness, port all tests to two-tier strategy, build coverage documentation in PLAN.md, remove legacy integration-tier scaffolding.
3. **Sprint 66+**: crate-refactor sprints begin (FIXME 0109 int decomposition first; other refactors as scoped).

Concurrency work (S62 carries) re-enters the queue post-test-port sprint, per the same lock-in.
