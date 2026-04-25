# Cranelisp Delivery Method

> **Owner**: `/sprint`.
> **Scope**: how we deliver — project structure, skill model, sprint archetype, cross-skill protocols, testing/agent/collaboration/implementation discipline, deferral principles, showcase discipline.
> **Out of scope**: architectural rules and principles are owned by `/arch` (`design/arch/`) and cited here as acceptance criteria rather than duplicated.
> **Status**: DRAFT — consolidated 2026-04-24 from `CLAUDE.md` (project root), `sprints/reimplementation.md`, `.claude/commands/sprint.md`, and the methodology-relevant `memory/feedback_*.md` files. Pure consolidation pass; no new rules were introduced. Inconsistencies surfaced by the consolidation are flagged as `FIXME(/sprint)` comments and collected in §17.

---

## Table of contents

1. [Knowledge architecture](#1-knowledge-architecture)
2. [Project structure](#2-project-structure)
3. [Skill model](#3-skill-model)
4. [Sprint archetype](#4-sprint-archetype)
5. [Cross-skill protocols](#5-cross-skill-protocols)
6. [Deferral principles](#6-deferral-principles)
7. [Testing discipline](#7-testing-discipline)
8. [Showcase discipline](#8-showcase-discipline)
9. [Collaboration rules](#9-collaboration-rules)
10. [Agent discipline](#10-agent-discipline)
11. [Implementation discipline](#11-implementation-discipline)
12. [Relationship to /arch-owned architectural rules](#12-relationship-to-arch-owned-architectural-rules)
13. [Change control](#13-change-control)
14. [Risk analysis](#14-risk-analysis)
15. [Success criteria](#15-success-criteria)
16. [How the harness documents relate](#16-how-the-harness-documents-relate)
17. [FIXMEs from consolidation](#17-fixmes-from-consolidation)

---

## 1. Knowledge architecture

Two layers of knowledge support the reimplementation, with no duplication between them (source: `sprints/reimplementation.md` §"Knowledge Architecture").

### 1.1 Claude skills — how to work

Each skill is a Claude Code slash command (`/spec`, `/arch`, `/frontend`, etc.) backed by a skill definition file under `.claude/commands/`. Skills capture **process knowledge**: what role the agent plays, what workflow it follows, what artifacts it produces, how it coordinates with other skills. Skills are invoked per-session to set the agent's working mode.

A skill file references the relevant `CLAUDE.md` files rather than duplicating their content.

### 1.2 CLAUDE.md files — what is there

`CLAUDE.md` files live in the repository near the source code they describe. They capture **domain knowledge**: data structures, invariants, patterns, naming conventions, interface contracts. Any skill working in a directory reads its `CLAUDE.md` (and every `CLAUDE.md` in parent directories up to the project root).

Placement:

- **Project root** (`CLAUDE.md`): cross-cutting conventions — naming, error handling, git workflow, build commands, skill inventory
- **Per source/spec directory**: local data structures, algorithm descriptions, invariants, known gotchas
- **Test directories** (`tests/CLAUDE.md`): test helper patterns, fixture conventions
- **Standard library** (`stdlib/CLAUDE.md`): prelude structure, naming conventions, module organization

`CLAUDE.md` files are living documentation — updated as implementation proceeds. When a code change makes a `CLAUDE.md` entry stale, the developer who made the change updates it.

### 1.3 This document

`sprints/METHOD.md` (this file) is the **delivery method** — a third layer above skills and `CLAUDE.md` files. It is the authoritative statement of how we sprint, hand off across skills, defer work, test, and collaborate. Individual skill definitions (`.claude/commands/*.md`) remain canonical for their own archetypes; this document is the place where the *inter-skill* flow lives.

<!-- FIXME(/sprint): current skill definitions (esp. `.claude/commands/sprint.md`) carry the full Sprint Archetype inline. Decide during the rework pass whether sprint.md shrinks to a thin role definition pointing at METHOD, or whether METHOD only summarizes with sprint.md remaining canonical for the archetype detail. -->

---

## 2. Project structure

### 2.1 Macro phases

The reimplementation proceeds through a sequenced set of macro phases (source: `sprints/reimplementation.md` §"Implementation Workflow — Phase sequence"):

- **Phase A — Extract** (parallel): `/spec`, `/arch`, `/qa` extract spec, interface types, and test catalog from the prototype.
- **Phase B — Scaffold** (architect-led, blocking): `/arch` creates crate structure, defines boundary types, writes CLAUDE.md files. `/repl` and `/port` produce their respective design inputs.
- **Phase C — Ring 0 (Core)**: parallel compiler-skill implementation.
- **Phase D — Ring 1 (Heap)**: extends each stage.
- **Phase E — Ring 2 (Abstraction)**.
- **Phase F — Ring 3 (Meta)**.
- **Phase G — Ring 4 (Effects)**.
- **Phase H — Release Compiler** (optional, post-pipeline-stable): Tier 2 release backend.

See `sprints/reimplementation.md` for the per-phase skill activity table.

<!-- FIXME(/sprint): reimplementation.md's Phase B description predates /int and /sprint skills; its per-ring skill list only enumerates 13 skills (missing /int, /sprint from the workflow). Confirm with /arch during rework whether to update reimplementation.md or whether the per-ring workflow is superseded by current SPRINT.md practice. -->

### 2.2 Ring model

The reimplementation uses a **feature-ring model** — concentric rings of capability, each stable before the next begins (source: `sprints/reimplementation.md` §"Decision: Feature-Ring Model"):

| Ring | Capability | Key property |
|---|---|---|
| 0 (core) | Expressions, types, functions, let, if, match | No heap allocation, no RC |
| 1 (heap) | Strings, ADTs, closures, reference counting | Heap management established |
| 2 (abstraction) | Traits, modules, imports, constrained polymorphism | Name resolution and dispatch |
| 3 (meta) | Macros, derive, standard library | Metaprogramming layer |
| 4 (effects) | IO model, platforms, parallelism, caching, REPL | Side effects and build infrastructure |

**Rationale**: each ring establishes a stable foundation. Ring 0 proves the pipeline works without heap complexity. Ring 1 adds heap management as a clean layer. This matches the prototype's hardest lesson: reference counting interacts with everything.

Within each ring, skills deliver vertically — they don't complete an entire pipeline stage before starting the next. Each stage implements enough to support the current ring's features, validates end-to-end, then extends for the next ring.

Ring 0 defines the full `Type` enum (including `ADT`, `Fn`, `Var`) from the start, even though it only exercises `Int`, `Bool`, `Float`, and simple `Fn`. This prevents rework when later rings add types — ring-to-ring transitions are additive, not a redesign.

### 2.3 Sprints

Sprints decompose rings into delivery increments. `/sprint` coordinates; all skills participate in every sprint (see §3.5 Early engagement).

- `sprints/ROADMAP.md` tracks progress sprint-by-sprint.
- `sprints/SPRINT.md` holds the current sprint plan and outcome report.
- `sprints/archive/sprint-{id}.md` holds completed sprint reports.

The intra-sprint flow (Phases 1–6) is defined in §4 below.

---

## 3. Skill model

### 3.1 Skill inventory

The project has **15 skills**, each a slash command backed by `.claude/commands/{skill}.md`. See the root `CLAUDE.md` §Skills for the one-line description of each; see the individual skill definition for role, owned directories, interfaces, and first steps.

- **Compiler skills (6)**: `/frontend`, `/typecheck`, `/backend`, `/platform`, `/int`, `/qa`
- **Review (1)**: `/review`
- **Coordination (2)**: `/sprint`, `/arch`
- **Language authority (1)**: `/spec`
- **User-proxy (5)**: `/stdlib`, `/examples`, `/docs`, `/repl`, `/port`

<!-- FIXME(/sprint): reimplementation.md §"Skill Definitions" only documents 13 skills (it predates /int and /sprint). The role/owns/interfaces fields for /int and /sprint should be added either to reimplementation.md or consolidated here. The skill-by-skill detail is currently spread across reimplementation.md and 15 individual skill definition files with no single overview. -->

<!-- FIXME(/sprint): the category split above (compiler vs coordination vs authority) is inferred from function, not documented anywhere. Ratify with /arch during rework or treat as descriptive only. -->

### 3.2 Ownership boundaries

Each skill owns a directory (enumerated in root `CLAUDE.md` §"Project Layout" and each skill definition). No skill edits files owned by another skill. The single exception is the FIXME protocol (§5.1), which is how cross-skill change requests are made.

### 3.3 Sizing constraint — `/int` as bottleneck

`/int` (Integration Developer) is the primary bottleneck. All pipeline, REPL, slash-command, CLI, and prelude work flows through this one skill owning `src/`. Sprint scope MUST be sized to what `/int` can deliver — other skills can prepare work in parallel, but the sprint does not ship until `/int` integrates it.

When scoping a sprint, assess `/int`'s task list first and cut scope if it is overloaded. (Source: `.claude/commands/sprint.md` §Role; MEMORY.md.)

### 3.4 Testing ownership

Unit tests are owned by the skill that owns the crate — NOT by `/qa`. They are written **during** implementation, inside the same wave that adds the code, in a `#[cfg(test)] mod tests` block alongside the feature.

`/qa` writes integration tests in `tests/` at the project root — full-pipeline, cross-crate, spec-traceable tests. `/qa` does NOT write unit tests for individual crates.

When planning a sprint, list unit tests under the implementing skill's deliverables, not under `/qa`'s. (Source: `memory/feedback_unit_tests_with_dev.md`.)

### 3.5 Early engagement

All skills participate in every sprint — even those whose main deliverables come later (e.g. `/port`, `/stdlib`, `/examples`). Earlier sprints give later-stage skills planning and validation work: survey the spec, validate assumptions about what they will need, provide feedback on direction from their perspective. Each skill maintains a broad plan that is refined sprint-by-sprint.

This means every `SPRINT.md` has an assignment for every skill. For later-stage skills, early-sprint assignments are typically:

- Survey relevant spec sections and sketch assumptions
- Review architectural decisions for impact on their domain
- Document a broad plan for their deliverables
- Flag risks or concerns from their perspective
- Refine their plan based on what was learned in the sprint

(Source: `.claude/commands/sprint.md` §"Early Engagement".)

### 3.6 Feedback loops

User-proxy skills provide feedback that flows back to compiler skills via the FIXME protocol (§5.1) and defect handoff (§5.3–5.4). Compiler skills address the feedback in a subsequent sprint (or the current one when in scope). See `sprints/reimplementation.md` §"Feedback loops" for examples.

---

## 4. Sprint archetype

Every sprint follows this sequential flow. `/sprint` drives the process; other skills execute their work within it. (Source: `.claude/commands/sprint.md` §"Sprint Archetype".)

<!-- FIXME(/sprint): the Sprint Archetype currently lives in full in `.claude/commands/sprint.md`. Decide during rework whether this section in METHOD is the canonical statement and sprint.md shrinks to a role definition + pointer, or whether sprint.md stays canonical and METHOD summarizes. Under current draft, sprint.md remains canonical and this section mirrors the main shape. -->

### 4.1 Two cardinal rules

Two rules govern every sprint:

1. **Design before code** (compiler skills): no coding happens until design docs are written, reviewed by `/arch`, and used by `/qa` to derive test cases. Design docs are prerequisite thinking, not post-hoc documentation.
2. **It's not done unless a user can use it** (user-proxy skills): every sprint must produce visible, usable progress demonstrated through the REPL showcase. Passing tests prove correctness; the showcase proves value. User-proxy skills (`/stdlib`, `/examples`, `/docs`, `/port`, `/repl`) must expose what has been built so far — not plan for the future, but show the present.

The REPL showcase gates sprint close (§8).

### 4.2 Phase 1 — Scope (`/sprint`)

1. **FIXME scan**: scan the entire project for unresolved `FIXME(/skill-name)` comments. FIXMEs are real debt — they represent cross-skill issues an upstream skill filed because it could not fix the problem itself.
   ```
   grep -r "FIXME(" --include="*.md" --include="*.rs" .
   ```
2. **Prior-ring coverage audit**: scan spec files for requirements from completed rings that still lack full test coverage annotations. Three gap kinds, in priority order:
   - **Coverage gap**: requirement tagged `[R{N} S{M}]` where ring N is complete — genuinely untested. Must be addressed.
   - **Negative coverage gap**: MUST/MUST NOT requirement annotated `[Tested ...]` but not `[Tested+Neg ...]` — positive path works but nothing verifies wrong behaviour is absent. Should be addressed, especially for boundary requirements.
   - **Traceability gap**: tests exist but spec annotation wasn't updated from `[R{N} S{M}]` to `[Tested ...]`. Lower priority.
   Also check for stale `IGNORED` annotations that reference tests which no longer exist or now pass.
3. **Assess state**: read `design/arch/roadmap.md`, `sprints/ROADMAP.md`, run tests, survey what exists.
4. **Propose scope**: identify the next coherent increment — a subset of ring work that produces a testable result, has clear skill boundaries, and respects dependencies. Prior-ring coverage gaps from step 2 are included as priority items. Write the scope in `SPRINT.md` as `DRAFT`.
5. **User approval**: present the proposed scope to the user. Adjust if needed.

### 4.3 Phase 2 — Architecture review (`/arch`)

`/arch` reviews the sprint proposal for:

- Technical coherence — does the scope form a complete, testable increment?
- No interim architecture — does any task build throwaway infrastructure that a later ring replaces? (Principle 8 — §12.)
- Design references — are the relevant design docs, interface types, and protocols highlighted for each compiler skill?
- Interface gaps — do boundary types need extending before implementation begins?

`/arch` updates `design/arch/` docs if needed and confirms the sprint is sound.

### 4.4 Phase 3 — Design

**Phase 3 is mandatory.** `/sprint` MUST NOT skip this phase or proceed directly to execution. Design docs are where the hard thinking happens — algorithms, data structures, ownership models, edge cases, trade-offs. Implementation without design produces ad-hoc decisions that cause bugs and deferred debt.

#### 4.4a Design docs (compiler skills)

Compiler skills write or update design docs in `design/{skill}/` for their sprint scope. Each doc must cover:

- The problem being solved and key design decisions
- Data structures, algorithms, or protocols introduced or changed
- Interactions with other crates/skills (ownership, calling conventions, data flow)
- Edge cases and invariants
- Reference to spec sections and sketch implementation where relevant

This is NOT optional documentation — it is the prerequisite thinking that informs implementation. A skill that cannot articulate its design in a document is not ready to write code.

`/arch` reviews the design docs for architectural coherence. `/qa` reviews them to inform test planning — identifies testable invariants, edge cases to cover, interaction boundaries to verify. `/qa` updates the relevant ring test plan (`tests/plan/ring{N}.md`) with test cases derived from the design docs.

#### 4.4b Plans and approach (all skills)

All skills update their plan `.md` files to address:

- FIXMEs assigned to them (incorporate the change or explicitly defer with rationale)
- Their sprint assignment (refine their plan section in `SPRINT.md` with concrete approach)
- Approach MUST reference the design doc — the approach in `SPRINT.md` summarizes *what*; the design doc explains *why* and *how*

`/sprint` collects the updated plans, confirms all FIXMEs are resolved or deferred, and verifies that every compiler skill with implementation work has a current design doc reviewed by `/arch`.

### 4.5 Phase 4 — Wave organization (`/sprint`)

`/sprint` reviews dependencies across the updated skill plans and organizes parallel activities into **waves**. A wave is a set of skill invocations that can run concurrently because they have no inter-dependencies.

`/sprint` writes the wave structure and task list into `SPRINT.md`, marks it `ACTIVE`.

### 4.6 Phase 5 — Wave execution (iterative)

`/sprint` starts waves sequentially. Within each wave, skills run in parallel.

**Terminology note**: "review" in step/phase names means *iterate until settled* — the step repeats until quality criteria are met. This is distinct from the `/review` skill, which is a specific code-quality assessment tool invoked during these iterative steps.

**Wave ordering principle**: design precedes implementation precedes showcase. Standard wave sequence:

1. **Design wave** — compiler skills write/update design docs.
2. **Design review wave** — `/arch` reviews docs; `/qa` derives test cases. Iterate until `/arch` approves.
3. **Implementation + test prep + `/review` wave(s)** — compiler skills write code; `/qa` writes integration tests **in parallel** (see below); `/review` assesses new code within the same wave.
4. **Build/test/review cycle** — run `cargo nextest run`, fix failures, `/review` assesses fixes, iterate until all tests pass and all quality findings are resolved.
5. **Showcase wave** — user-proxy skills expose the progress (§8).

A compiler skill MUST NOT begin implementation until its design doc for the sprint scope exists and has been reviewed by `/arch`. If a design review surfaces issues that change the sprint scope, `/sprint` pauses to re-scope with user approval.

A sprint MUST NOT close until user-proxy skills have demonstrated that the new capabilities are usable.

#### 4.6a Why `/qa` runs in parallel with implementation

When `/qa` runs only after implementation, tests are unconsciously shaped by what exists — testing the code, not the spec. Running `/qa` in parallel forces spec-first test design. Some tests will fail initially; that is expected and correct. The subsequent build/test/review cycle resolves failures.

(Historical: Sprint 16 had `/qa` run post-implementation, wrote 25 passing tests covering only `Pure`/`bind`, missed that `print` — the sprint's headline goal — had no Effect codegen. A parallel `/qa` would have written a `print` test from the spec, gotten `#[ignore]`, and the gap would have been visible before "done" was declared.)

#### 4.6b Build/test/review cycle

Iterate until settled:

a. `/qa` un-ignores tests that should now pass and runs the full suite.
b. Failures are triaged: implementation bug (file FIXME on owning skill) vs test bug (fix test — but see §7.4).
c. Compiler skills address `/review` findings (Blockers and Important) and test failures.
d. `/review` assesses any fix code — all code changes get a `/review` pass, including fixes.
e. Iterate: re-test, `/review` re-assesses, until all tests pass and all B+I findings are resolved.
f. Any tests still `#[ignore]` at cycle end represent genuine implementation gaps — these block sprint close per the deferral principles (§6).

#### 4.6c FIXME gate (between waves)

Before advancing to the next wave, `/sprint` scans all files produced or modified by the current wave for unresolved `FIXME(/skill-name)` comments. Outstanding FIXMEs addressed to a skill in the current wave block advancement — they must be resolved or explicitly deferred with rationale.

### 4.7 Phase 5b — Showcase (mandatory, driven by `/repl`)

See §8 for the full showcase discipline. Summary: every sprint MUST produce a new demo file (`repl/demos/{ring}{letter}.demo`) before close. All prior demos verified green at close.

### 4.8 Phase 6 — Close (`/sprint`)

Sprint close checklist — every item must pass before marking `COMPLETE`:

- [ ] New sprint demo created (`repl/demos/{ring}{letter}.demo`) and plays cleanly
- [ ] All prior demos play cleanly (no regressions)
- [ ] `/port` (exemplar) demo is current — shows what can be built with features so far
- [ ] `/stdlib` demo is current — shows available stdlib functionality
- [ ] All examples compile and run (`cargo run -- --run examples/*.cl`)
- [ ] All tests pass (`cargo nextest run`) — 0 failures
- [ ] **Baseline ledger integrity**: every failing test in a workspace `cargo nextest run --no-fail-fast` appears in `tests/plan/baseline.md` with fully-populated required fields (test name, SHA, signature, owning skill, target sprint, disposition + rationale). No `flaky` / `timing-sensitive` / `pre-existing` dispositions. The workspace stress-run here is a ledger-completeness check, NOT proof of race closure. For concurrency/race defects, require evidence-gated hypothesis + citation + unit-test invariant + integration-regression guard + `/arch` approval — not stress-run counts. (Source: `sprints/archive/sprint-61.md` §Findings "Stress-run verification unmasked as insufficient".)
- [ ] Ignored test count is 0 for in-scope features (ignored tests for future-ring features acceptable with justification)
- [ ] `/qa` confirms spec-surface coverage: every spec requirement in sprint scope has a passing test (not just "all tests pass" but "all requirements are tested")
- [ ] FIXME scan clean (all resolved or explicitly deferred with rationale)
- [ ] Prior-ring coverage audit clean — no coverage gaps (`[R{N}]` where N is complete); negative coverage gaps for MUST requirements documented or addressed
- [ ] `ROADMAP.md` updated with test count and outcomes
- [ ] User-proxy skills confirmed showcase adequacy

Close actions:

1. Write the outcome section in `SPRINT.md`: delivered, deferred, findings.
2. Mark `SPRINT.md` as `COMPLETE`.
3. Move `sprints/SPRINT.md` to `sprints/archive/sprint-{id}.md`.
4. Update `sprints/ROADMAP.md` with the completed sprint and its outcomes.
5. If the ring is not yet complete, begin Phase 1 for the next sprint.
6. If the ring is complete, `/review` performs the ring-gate review.

**Sprint close requires explicit user review and approval.** `/sprint` MUST NOT close a sprint (archive + update ROADMAP) until the user has reviewed. The user confirms close and commit explicitly. (Source: MEMORY.md project notes.)

### 4.9 Mid-sprint adjustment

If the user invokes `/sprint` mid-sprint:

1. Read current `SPRINT.md` task status.
2. Assess progress: what is done, what is blocked, what is at risk.
3. Recommend: continue as planned, re-scope, or close early.
4. **Get user approval before closing early or deferring work.** Never unilaterally close a sprint or skip waves — scope changes require explicit user sign-off.
5. Update `SPRINT.md` with any scope changes (with user approval).

### 4.10 SPRINT.md template

See `.claude/commands/sprint.md` §"SPRINT.md Template" for the canonical layout (status / scope / FIXME debt / architecture review / skill plans / waves / notes / outcome).

---

## 5. Cross-skill protocols

### 5.1 FIXME protocol

FIXMEs flow in one direction: the skill that discovers a problem files a `FIXME(/owning-skill)` on the relevant file. The owning skill resolves it by:

- Incorporating the change into their owned files (plan, spec, code), then removing the FIXME comment
- Or explicitly deferring with rationale recorded in `SPRINT.md` Notes

FIXME syntax:

```html
<!-- FIXME(/skill-name): description of the issue and proposed resolution -->
```

or in code:

```rust
// FIXME(/skill-name): description
```

`/sprint` tracks FIXMEs but MUST NOT rename, remove, or suppress them — only the owning skill removes a FIXME after resolving the underlying issue.

**Writing FIXMEs is the ONE exception to file ownership.** Any skill may write a `FIXME(/target-skill)` comment on any file to pass a request. This is how cross-skill communication works. Example: `/repl` finds a test gap → writes `FIXME(/qa)` on the test plan file. `/sprint` coordinates but still uses the same FIXME protocol to request work from skills.

**Wave gate**: before `/sprint` advances to the next wave, it MUST scan for unresolved FIXMEs in all files touched by the current wave. Outstanding FIXMEs addressed to a skill in the current wave block advancement — they must be resolved or explicitly deferred with rationale.

(Source: root `CLAUDE.md` §"Cross-Skill Changes"; `.claude/commands/sprint.md` §"FIXME Protocol".)

### 5.2 Skill handoff

Every skill plan must end with a **"Next skills"** section recommending which skill(s) the user should invoke next after the plan is implemented. When a sprint is active, consult `sprints/SPRINT.md` for the current task list and blocking dependencies. Otherwise consult `design/arch/roadmap.md` for dependencies.

Example:

```
## Next skills

- `/typecheck` — Ring 0 core inference can now begin against the types defined here
- `/backend` — Ring 0 codegen can begin in parallel with typecheck
```

(Source: root `CLAUDE.md` §"Skill Handoff".)

### 5.3 Usability findings vs defects

User-proxy skills (`/stdlib`, `/examples`, `/docs`, `/port`, `/repl`, `/platform`) routinely encounter problems while exercising the language. Two distinct categories with different handling:

**Usability findings** — corner cases, unhelpful errors, inference friction, missing APIs, ergonomic issues. These are filed as `FIXME(/skill-name)` comments on the relevant spec, design, or plan document. Documentation is sufficient closure.

**Defects** — real compiler bugs, spec violations, runtime crashes, REPL/`--run` divergences, output that does not match the spec. **A user-proxy skill's work is not finished until `/qa` has authored a narrow integration test that reproduces the defect** — failing, un-ignored, with `// spec:` annotation and `FIXME(/owning-skill)` pointing to the resolver. Documentation alone is not closure for defects; the failing test is the durable record + the trigger for compiler-skill resolution.

User-proxy skills feed defects to `/qa` for narrow reproduction; `/qa` writes the test; the owning compiler skill resolves it (this sprint or a future one).

**The distinction matters because defects without failing tests get lost.** A FIXME comment on a design doc captures intent but does not prove the issue exists, does not catch regression, and does not trigger CI. The failing test does all three.

(Source: root `CLAUDE.md` §"Usability Findings and Defects".)

### 5.4 Reproduction discipline

#### 5.4a Minimal repro before handoff (compiler-skill → compiler-skill)

Cross-compiler-skill defect handoff (e.g. `/int` handing a failing test to `/backend`) MUST include a minimal repro, not just an error signature. Error signatures routinely mask layered bugs: the visible error belongs to one skill; the underlying failure belongs to another, and fixing the visible one exposes the next.

Before `/sprint` spawns a cross-compiler-skill triage, the skill that discovered the failure MUST produce a minimal repro — or request `/qa` to do so. The handoff brief names the repro (exact minimal test, symbol-table state at failure, classification), not just the symptom. If the first owner cannot reduce, that itself is diagnostic — tells you the bug is deeper than surface and worth more investigation before handoff.

(Source: `memory/feedback_cross_skill_minimal_repro.md`; root `CLAUDE.md` §"Usability Findings and Defects" extended paragraph on cross-skill defect handoff; `tests/CLAUDE.md §"Isolating Cross-Crate Failures"`. Historical: Sprint 59 Wave 1 cost ~2 hours of misdirected linker work because a `.Ldata0 GOT_LOAD` signature was handed off without reducing first.)

<!-- FIXME(/sprint): confirm `tests/CLAUDE.md §"Isolating Cross-Crate Failures"` exists (referenced but not verified during consolidation). -->

#### 5.4b QA reproduction protocol (failure clusters)

When `/qa` finds multiple integration tests failing with the same or similar failure mode (e.g. a cluster of SIGBUSes across `tests/io.rs` + `stdlib/macro_do_*` + REPL bind-chain tests), the next step is NOT to spawn a compiler skill to bisect commits, stub out suspect code, or eyeball diffs. The next step is **reproduction**.

Protocol:

1. `/qa` picks the simplest failing integration test from the cluster.
2. `/qa` writes an even-more-simplified test in `tests/` that strips away incidental complexity. Keep halving until the minimal repro is identified — the smallest language construct that reliably SIGBUSes / panics / returns wrong.
3. `/qa` hands the minimal repro to the relevant compiler skill — with the minimal-repro test name, the failure mode, and what stripping-back revealed.
4. The compiler skill writes a unit test inside their own crate (`#[cfg(test)] mod tests`) that further isolates the failure to a specific function or code path. This is where the bug actually gets nailed down.
5. Fix based on the unit-test diagnosis, not the integration test.

Reproduction is a core function of `/qa`, not an optional nicety. It belongs in `/qa`'s default workflow for any failure cluster.

**Anti-pattern**: "24 tests SIGBUS in IO path. Spawn `/backend` to stub out the custom Drop and see if it resolves." That is commit-level bisection disguised as reasoning.

**Right approach**: "24 tests SIGBUS in IO path. Pick the simplest — `io_do_print_sequence`. Strip the prints: does `(do (Pure 1) (Pure 2))` SIGBUS? If not, it is something specific to print. If yes, it is the do-chain itself, try `(Pure 1)` alone. Keep reducing." Then hand minimal repro to `/backend` for unit-test isolation.

(Source: `memory/feedback_qa_reproduction.md`.)

#### 5.4c Minimal repro handoff (user-proxy → `/qa` → compiler skill)

When a user-proxy skill (`/port`, `/examples`, `/repl`) isolates a compiler bug to a minimal repro, the repro MUST end up in `tests/` (owned by `/qa`) — NOT in `exemplar/`, `examples/`, or any other user-facing showcase.

Protocol:

1. **User-proxy skill authors the repro in-session** (scratch file, tempdir, or inline in the agent's output). Do NOT commit the repro as an `exemplar/repro-*.cl` or `examples/repro-*.cl` file.
2. **User-proxy skill hands off to `/qa`** with the repro source, the expected vs actual behaviour, and a suggested test name. Handoff happens via `SPRINT.md` readout or direct agent summary — not via checked-in files in user-proxy directories.
3. **`/qa` copies the repro into `tests/`** — either as a fixture under `tests/fixtures/` (when the repro is a standalone `.cl` program) or inline as a string literal / heredoc in a Rust integration test. The test is committed FAILING per §7.2.
4. **Compiler skill works against the `tests/` artefact** — reading it, running it via `cargo nextest run --test ...`, using CLIF / RC trace env vars to investigate. Never editing or reading `exemplar/` / `examples/` files except for documentation context.
5. **After the fix**: the `tests/` test flips green. The originating `exemplar/solver.cl` may also flip green — that verification is the user-proxy skill's, via their own showcase run.

**Boundary corollary**: a compiler skill MUST NOT edit `exemplar/*.cl` or `examples/*.cl` as part of a fix. If applying a user-proxy-side logic change is required, the compiler skill hands the proposed change BACK to the user-proxy skill via a readout, and the user-proxy skill applies it in a follow-on agent. Compiler skill's fix scope stays in `crates/` + `src/` + design docs.

**Why**: `exemplar/` and `examples/` are user-facing showcases that can be rewritten, relocated, or deleted at any time. A test that subprocess-runs `exemplar/foo.cl` has an implicit dependency that survives only as long as `exemplar/foo.cl` exists in that form. Regression guards must not have that coupling.

(Source: `memory/feedback_repro_handoff.md`; explicit user directive 2026-04-22 after Sprint 61 Wave 2 Slice 2 branch-(b) misstep.)

#### 5.4d Repros join the suite for eternity

Every repro reduction — complete or partial — produces a committed failing test. Failing, un-ignored, per §7.2. This applies equally whether the fix lands in the same sprint or the defect carries forward.

Discarding narrowing work (the "these simpler shapes pass; this specific shape fails" reduction that was done in-session) forces the next sprint to redo it from scratch, and loses the regression guard once the bug is fixed. Partial reductions go in as much as was isolated, with `// FIXME(/skill)` naming what is still unknown.

**Keep reductions as small as possible.** Two payoffs beyond regression guarding:

- The fix may become obvious during isolation (Sprint 59: the 4-line prelude parity bug was visible the moment the repro shrank to a single-function prelude).
- When source-level reduction plateaus, a small test produces small CLIF output that can be inspected by eye. Use `/clif <name>` in the REPL or `CRANELISP_CODEGEN_TRACE=1` during test runs to see the compiled IR for the shrunk repro. Codegen-layer bugs (RC mis-count, missing load, incorrect relocation) often become visible in CLIF before they become visible in source reduction.

(Source: `memory/feedback_repros_join_suite.md`; root `CLAUDE.md` §"Usability Findings and Defects" paragraphs "Reproduced defects join the test suite permanently" and "Keep reductions as small as possible".)

---

## 6. Deferral principles

Three anti-patterns govern what may and may not be deferred. (Source: `.claude/commands/sprint.md` §"Deferral Principles".)

### 6.1 Three anti-patterns

1. **Carrying defects out of a sprint is an anti-pattern.** Bugs found during a sprint are fixed in that sprint. A defect is not "out of scope" — it is broken software. If a showcase or test reveals a bug, the sprint does not close until it is fixed. The only exception is a bug that requires architectural work not yet designed (tracked as a FIXME, not silently deferred).
2. **Refactoring during progression is an anti-pattern.** Code that needs cleanup gets harder to clean up as features land on top. "We'll refactor later" is a lie — later never comes, or comes at 3× the cost. When `/review` identifies structural issues (functions too long, parameter counts too high, missing abstractions), fix them in the current sprint while the code is fresh and the context is loaded.
3. **The only legitimate deferral is avoiding interim architecture.** If implementing a feature now would require throwaway infrastructure that a later ring replaces, deferral is correct — it avoids waste and unnecessary complexity. This is `/arch`'s Principle 8 applied to sprint planning. But "the sprint is already large enough" is not a legitimate reason to defer defects or cleanup.

<!-- FIXME(/sprint): the second rule — "refactoring during progression is an anti-pattern" — has been read as "do not refactor in sprint." Distinguish *speculative* refactoring (deferred) from *emergent* refactoring (mandatory in-sprint). When a wave introduces the third instance of a duplicate pattern, extraction happens in that sprint, not as filed debt. The audits of 2026-04-23 (`audits/src-20260423.md`, `audits/backend-20260423.md`, etc.) indicate this clause has over-corrected in practice. Flag for /arch and for the methodology rework pass. -->

### 6.2 2× escalation rule

Items deferred once may be deferred again with rationale. Items deferred twice MUST ship in the current sprint or require explicit user approval to defer a third time. During Phase 1 (scope), `/sprint` checks the deferral history of every carried item by scanning prior sprint archive Deferred sections. Items on their second deferral are flagged in the FIXME Debt table with `**2x deferred**` and included in the sprint scope by default. `/arch` may recommend deferral but `/sprint` escalates to the user rather than accepting automatically.

The same rule applies to `#[ignore]` tests: if an ignored test's target sprint has passed and it was re-targeted once already, it must ship in the current sprint or get explicit user approval to defer again.

### 6.3 Review-finding escalation

Review findings (Important and Blocker) from `/review` follow the same escalation: deferred once is acceptable, deferred twice requires user sign-off. `/sprint` tracks the deferral count in the FIXME Debt table.

**Rationale**: tech debt, test gaps, and review findings are always easy to defer because new features feel more valuable in the moment. But deferred quality work compounds — files that need cleanup get more complex as features land on top, ignored tests mask real bugs, and review findings become harder to address as the code evolves. The deferral principles above draw a bright line: defects and cleanup are not deferrable; only interim-architecture avoidance justifies pushing work to a later sprint.

---

## 7. Testing discipline

### 7.1 Testing ownership

See §3.4. Unit tests are owned by the implementing skill and live inside the crate; integration tests are owned by `/qa` and live in `tests/`.

### 7.2 Tests spec, not code

`/qa` writes tests for the full spec surface. Tests that fail because the implementation violates the spec are CORRECT — they stay failing (not `#[ignore]`'d). Devs make them pass.

`#[ignore]` is valid ONLY for future-sprint requirements not yet scheduled. Everything in scope should fail visibly — including compile failures (missing API = `cargo test` will not build = loud signal). This is TDD.

Do not file FIXMEs for things that are already exposed by a failing test — the test IS the signal. Traceability comes from `// spec:` comments in the test, not from annotations on spec files.

(Source: `memory/feedback_failing_not_ignored.md`; MEMORY.md.)

### 7.3 Running tests

- **Always use `cargo nextest run`** (or the alias `cargo nt`) instead of `cargo test`. Nextest runs each test in its own process, parallelizes across binaries, and completes the full suite in ~9s.
- **Never run tests in background mode.** Wait for the run to complete before proceeding. Background test runs pile up and contend on build locks.
- **30-second timeout expectation.** If a test run exceeds 30s, something is wrong — kill it and investigate.
- **Never run cargo while a subagent is active.** Build lock contention delays both runs. When checking agent progress, use `git diff --stat` only. Do not run cargo commands. Wait for the agent to complete.
- **One agent, one test run.** When multiple agents are active, only the agent that owns source code changes should run tests. Other agents must not run tests concurrently.
- **No `--no-fail-fast`.** It leaves process zombies and runs all tests even when early failures indicate a fundamental problem. (There is one narrow exception: the §4.8 baseline-ledger integrity check at sprint close uses `cargo nextest run --no-fail-fast` to enumerate all failures for the ledger. Outside that, avoid.)
- **Build confidence incrementally.** Run targeted tests first (e.g. `-E 'test(my_feature)'`), expand as confidence grows. Only run the full suite once targeted tests pass.

(Sources: root `CLAUDE.md` §Testing; `memory/feedback_test_serialization.md`; `memory/feedback_no_concurrent_tests.md`; `memory/feedback_test_confidence.md`.)

<!-- FIXME(/sprint): `memory/feedback_test_serialization.md` says "Do NOT use --no-fail-fast — it leaves process zombies." `.claude/commands/sprint.md` §Phase 6 uses `cargo nextest run --no-fail-fast` as a sprint-close ledger-integrity check. Consolidate the policy: either name `--no-fail-fast` as permitted only at sprint close, or resolve the zombie issue. -->

### 7.4 Validate failing tests against spec before fixing code

When diagnosing test failures, explicitly check whether each failing test is valid against the spec BEFORE proposing code changes. The failure may indicate the test relied on non-compliant behavior.

For each failing test, ask: *Does this test program comply with the spec?* Check imports, module visibility, symbol scoping. If the test relies on behavior the spec says should not exist, the test needs fixing. Only propose code changes for tests that are spec-compliant but fail due to a genuine implementation bug.

(Source: `memory/feedback_validate_tests_against_spec.md`. Historical: Sprint 50 — prior implementation implicitly seeded primitives into all module tables, violating spec §8.9.1; tests passed because of this invalid behaviour; when a restructure removed the seeding, tests broke; the initial agent attempt restored the invalid seeding rather than updating the non-compliant tests.)

### 7.5 Test tuning after refactors

After large refactors that pass tests, review for long-running tests and tune where possible. Large mechanical refactors can inadvertently introduce performance regressions in tests (extra cloning, repeated work). Catching slow tests early prevents compound degradation.

After wave completion in sprints with significant refactoring, run tests with timing and flag any tests that take noticeably longer than expected — the full suite should complete in seconds per the 30s timeout expectation.

(Source: `memory/feedback_test_tuning.md`.)

### 7.6 Pre-existing failures

13 tests are known-failing (11 `sprint_port` + 2 `v4_platform`). These are pre-existing and pre-date current work. Track in `tests/plan/baseline.md` with required fields (see §4.8 baseline-ledger integrity).

<!-- FIXME(/sprint): root CLAUDE.md says "11 sketch_port + 2 v4_platform tests fail", memory says "13 pre-existing failures (11 sketch_port + 2 v4_platform)". Confirm current count with /qa during rework. -->

---

## 8. Showcase discipline

**The REPL showcase gates sprint close.** Each sprint's REPL demo is the buyer's first impression of the sprint's deliverables. `/port` uses the showcase to demonstrate what can be built with the features available so far (via REPL until a web platform is in reach). `/examples` ensures the learning sequence works up to the current ring. `/repl` validates the interactive experience. A sprint is not complete until its showcase plays cleanly and user-proxy skills confirm the new capabilities are usable.

Every sprint MUST produce a new demo file (`repl/demos/{ring}{letter}.demo`) before close. This is not optional — even hardening sprints have user-visible changes worth demonstrating.

The demo MUST:

- Showcase every user-visible feature delivered in the sprint (new commands, new behavior, fixed bugs)
- Be self-contained — no dependency on prior demos
- Follow the conventions in `repl/demos/CLAUDE.md` (20–40 lines, narrative structure, use REPL discoverability)
- For bug-fix sprints: demonstrate the corrected behavior (e.g. ADT display fix → show the correct output; RC fix → use `/mem` to show balanced allocation)
- For new commands: show the command in action with realistic input

**Demos MUST be tested by piping through the actual REPL** (`cat demo.demo | cargo run`) before committing. Historical: `ring4g.demo` used `map`, which does not exist in the prelude — caught by user when verifying.

When a demo uses special/imported functions (operators, prelude functions), show their signature with `/sig` before first use. This helps the viewer understand what they're looking at.

All existing demos verified: run every `.demo` file through the REPL and confirm clean output (no crashes, no unexpected errors). A broken prior demo is a regression.

`/port` and `/stdlib` demos updated if the sprint changed exemplar or stdlib capabilities.

**Showcase waiver**: pure-design sprints with no user-visible language change may waive the showcase WHEN (a) the sprint produces no executable artefact, (b) prior-sprint demos are replayed green as regression guards, and (c) the next implementation sprint that follows picks up the showcase burden for the combined delivery. The three-clause precedent was established for Sprint 62 (recorded in `sprints/SPRINT.md` Notes; not codified in `.claude/commands/sprint.md` per user direction 2026-04-22).

(Sources: `.claude/commands/sprint.md` §"Phase 5b: Showcase"; `memory/feedback_demos.md`; `sprints/SPRINT.md` §Notes for S62 waiver.)

---

## 9. Collaboration rules

### 9.1 Review before enact

All code changes must be proposed to the user for review before being enacted. Subagents should research and propose, not implement directly.

When spawning subagents for fix / implementation work, instruct them to research only — diagnose root causes, identify specific files / lines / changes needed, and report back. Present the proposed changes to the user. Only edit code after user approval.

(Source: `memory/feedback_review_before_enact.md`. Historical: the user caught an agent restoring primitives seeding that violated a design principle — autonomous edits risk embedding wrong assumptions.)

### 9.2 Sprint close requires user approval

See §4.8. `/sprint` does NOT close sprints (archive, update ROADMAP) until the user has reviewed. The user confirms close and commit explicitly. (Source: MEMORY.md project notes.)

### 9.3 Communication via artifacts

Skills communicate through files in the repository, not through out-of-band channels:

- Issues and decisions are documented in the relevant spec, arch, or `CLAUDE.md` file
- Test failures are documented in the test plan
- Feedback from user-proxy skills is documented as issues in a tracking file or as FIXMEs

(Source: `sprints/reimplementation.md` §"Communication via artifacts".)

---

## 10. Agent discipline

### 10.1 Separate agents per skill

Never launch a single agent that operates as multiple skills (e.g. "You are `/repl` then `/int` then `/qa`"). Always launch separate agents, one per skill.

Each skill has its own definition file, workflow, owned files, and discipline. A combined agent will not read skill definitions or follow skill-specific processes. It bypasses the ownership boundaries that prevent cross-skill edits.

When work spans multiple skills, launch separate agents — one per skill. They can run in parallel if independent, or sequentially if one depends on another's output. Even for "small" changes, respect skill boundaries.

(Source: `memory/feedback_separate_agents.md`.)

### 10.2 No worktree isolation

Do NOT use `isolation: "worktree"` when spawning subagents for this project.

**Why**: in Sprint 18, 3 of 4 worktree agents misinterpreted the project structure — they saw `sketch/` as the "real" source code and moved it into the main tree, deleting the reimplementation's `crates/`, `design/`, `spec/`, etc. The diffs were 100K+ lines of destruction. None of the worktree changes could be merged.

Always run subagents without worktree isolation (no `isolation` parameter). Add a `CRITICAL:` instruction to every agent prompt: *"This project has TWO codebases. The REIMPLEMENTATION is at the project root (`src/`, `crates/`). The SKETCH/PROTOTYPE is in `sketch/` and MUST NOT be modified or moved."* Run agents sequentially when they touch overlapping files.

(Source: `memory/feedback_worktrees.md`.)

### 10.3 Agents clean their own crate

When spawning a sub-agent for implementation work, the prompt MUST require:

1. Run `cargo check` on the touched crate to see warnings
2. Fix any dead code, unused imports, or unused variables the changes introduced
3. Run `cargo clippy --all-targets -- -D warnings` on the crate (or at minimum `cargo check`) before finishing
4. Report any pre-existing warnings the agent chose to leave (with justification)

Developer skills own their crates and are responsible for "0 clippy warnings" (sprint close criterion). Sub-agents complete their single task and stop — they do not have continuity to notice warnings they introduced elsewhere. Without explicit prompting, they leave behind dead code, unused imports, and unused variables.

Add the following to every implementation-focused sub-agent prompt:

> Before finishing, run `cargo check` on the crates you modified. Fix any warnings your changes introduced (dead code from removed callers, unused imports from removed parameters, unused variables from refactored signatures). Report any warnings you chose to leave and why.

(Source: `memory/feedback_agents_clean_their_crate.md`.)

### 10.4 Git discipline for agents

Subagents MUST NOT run git commands that DISCARD uncommitted work:

- `git stash drop` / `git stash clear` — deletes stashed work
- `git reset --hard` — discards uncommitted working-tree changes
- `git checkout -- <path>` / `git restore <path>` — reverts specific files to HEAD
- `git clean -f` / `git clean -fd` — deletes untracked files
- `git checkout <branch>` with unstaged changes that would be overwritten

`git stash` and `git stash pop` are NOT forbidden. Stash-then-pop preserves work — the agent may use it to briefly test a clean baseline, PROVIDED the pop runs and succeeds before the agent returns. If the pop conflicts, the agent must resolve or STOP and report rather than drop the stash.

**When changes look wrong or need to be set aside** (either by the main session or an agent):

1. Move them to a branch: `git checkout -b save/description && git add -A && git commit -m "save: description"`
2. Return: `git checkout main`
3. Show the user the state and ask how to proceed
4. **Never destroy work** — branches are cheap, lost work is not.

Every subagent prompt MUST include an explicit "Forbidden" clause listing these commands. (Source: `.claude/commands/sprint.md` §"Git discipline"; `memory/feedback_no_git_stash_agents.md`; `memory/feedback_no_destructive_git.md`. Historical: Sprint 49 Wave 2 lost work because a `stash pop` failed on conflict and work was discarded. Sprint 53 dropped a stash and reset hard, destroying evidence of agent work and losing an entire `/backend` agent's output — 5-param `compile_to_module`, 48 ported tests, API lockdown.)

---

## 11. Implementation discipline

### 11.1 Target state first

When the current implementation has the wrong basic structure, do not patch it incrementally — that creates "horrible contortions that aren't even in the target state." Instead, identify the target data model and handoff pattern, then restructure toward it.

Before planning changes, compare current vs target design. If the data model or handoff pattern is wrong, fix the structure first. Ask: *does this change move toward the target state, or does it add another workaround?*

(Source: `memory/feedback_target_state_first.md`.)

### 11.2 No premature performance

Get the single correct path first; tune later. Do not keep a v1 path alive for speed while v2 is being stabilised. (Source: MEMORY.md; historical sprint guidance.)

<!-- FIXME(/sprint): `memory/feedback_no_premature_perf.md` not verified during consolidation — filename does not appear in the memory directory listing. The rule is listed in MEMORY.md index. Confirm file name / location during rework. -->

### 11.3 No snapshot assembly; assign on demand

Referenced in MEMORY.md as implementation-discipline rules (`memory/feedback_no_snapshot_assembly.md`, `memory/feedback_assign_on_demand.md`). These are project-specific technical rules rather than general methodology; they belong in `design/arch/` or crate-local `CLAUDE.md` files, not in this document.

<!-- FIXME(/sprint): confirm with /arch whether feedback_no_snapshot_assembly.md and feedback_assign_on_demand.md should be promoted to design/arch/ as architectural principles (they read more like architecture than methodology) or left as memories. -->

---

## 12. Relationship to `/arch`-owned architectural rules

This document covers **delivery**. Architectural rules live in `design/arch/` under `/arch`'s ownership and are cited here as acceptance criteria at the relevant gates.

Expected `/arch`-owned content (not authoritative until the rework pass):

- **Principle 8 — no interim architecture**: the only legitimate deferral (§6.1 rule 3) cites this principle. The definition lives in `design/arch/principles.md` (or equivalent).
- **Interface freezing via `cranelisp-types`**: cross-crate coupling must go through named DTOs / trait contracts in the `types` crate. (Raised during methodology review 2026-04-24; not yet codified.)
- **Rust-mechanical forcing functions**: `pub(crate)` as default, single facade module per crate, `cargo-public-api` in CI, sealed traits + `#[non_exhaustive]` on DTOs, crate-boundary governance. (Raised 2026-04-24; not yet codified.)

When this document says "at sprint close, `/arch` Principle 8 must hold," the definition of Principle 8 lives in `design/arch/`. `/sprint` does not redefine architectural rules; it cites them and gates on them.

<!-- FIXME(/sprint): verify that `design/arch/principles.md` exists and contains Principle 8 in referenceable form. If not, file a FIXME on /arch's plan to codify. -->

<!-- FIXME(/arch): codify the Rust-mechanical forcing functions (pub(crate) default, facade-module pattern, cargo-public-api, sealed traits) discussed in the 2026-04-24 methodology review. METHOD.md cites these as architectural rules but they do not yet have a home. -->

---

## 13. Change control

(Source: `sprints/reimplementation.md` §"Coordination Model".)

| Change type | Owner | Process |
|---|---|---|
| Interface type change | `/arch` | Proposal → impact assessment → update interface doc → notify affected skills |
| Spec ambiguity | `/spec` | Check prototype behavior → record as normative or propose change → update spec |
| Test failure | `/qa` | Triage → assign to responsible compiler skill → verify fix |
| User experience issue | User-proxy skill | File issue → compiler skill fixes → user-proxy validates |
| Code quality issue | `/review` | Flag to owning skill → skill decides to fix now or defer → update `CLAUDE.md` if recurring |

**Shared artifacts** (referenced by all, owned by one):

- Language spec (`spec/`) — owned by `/spec`
- Interface type definitions — owned by `/arch` (current home: `design/arch/`; <!-- FIXME(/sprint): verify canonical path —  reimplementation.md references `docs/arch/interfaces.md` which may be a stale path -->)
- `CLAUDE.md` files — owned by the skill that owns the directory's code, updated by anyone who changes the code

---

## 14. Risk analysis

High-level risks inherited from the reimplementation plan (source: `sprints/reimplementation.md` §"Risk Analysis"):

- **CompiledModule decomposition (HIGH)** — the prototype's god-object, referenced 133 times across 18 files. Decomposition is `/arch`'s first Phase B deliverable.
- **Macro system complexity (MEDIUM-HIGH)** — macros need a mini-pipeline (parse → typecheck → compile → execute) inside the frontend. Mitigated by deferring to Phase F.
- **REPL state management (MEDIUM)** — ~2K lines, deeply interleaved state. Mitigated by building batch mode first.
- **Spec–implementation divergence (MEDIUM)** — 27 documented known issues. Mitigated by running every spec example against the prototype in Phase A.
- **Cross-ring rework (LOW-MEDIUM)** — later rings may require changes to earlier-ring code. Mitigated by defining the full `Type` enum in Ring 0.

Additional risks surfaced by the 2026-04-24 audit findings (`audits/src-20260423.md`, `audits/backend-20260423.md`, `audits/frontend-20260423.md`, `audits/typecheck-20260423.md`):

- **Structural debt accumulation** — god-files, duplicate code paths, migration residue, poor test locality. Diagnosis: the process sees diffs, not accumulated state; no standing structural signal; no budget on named files; duplication is admitted-with-comment rather than extracted.

<!-- FIXME(/sprint): methodology response to the 2026-04-24 audits is the rework pass (changes 1-4) plus /arch's change 5 and the Rust-mechanical rules (A-G). This risk will be closed when those land. -->

---

## 15. Success criteria

The reimplementation is complete when (source: `sprints/reimplementation.md` §"Success Criteria"):

1. **Spec conformance**: every testable example in `spec/` produces the documented result.
2. **Test suite**: all portable integration tests from the prototype pass (~470 tests).
3. **E2E tests**: all transcript tests pass (`tests/e2e/`).
4. **Standard library**: `stdlib/` compiles and all library tests pass.
5. **Examples**: all example programs run correctly.
6. **Platforms**: platform DLLs load and pass platform tests.
7. **Performance**: within 2× of prototype on representative benchmarks.
8. **Quality**: `cargo nextest run` green, `cargo clippy` clean, no `unwrap()` in the pipeline.
9. **Documentation**: user-facing tutorial, language guide, and getting-started guide exist.
10. **Self-documenting REPL**: every symbol and expression produces useful feedback at the REPL.

---

## 16. How the harness documents relate

Five layers of documentation support the project. Each is authoritative for its scope:

| Layer | Location | Authority |
|---|---|---|
| **Harness configuration** | `.claude/settings.json`, `.claude/commands/*.md` (15 skill definition files) | Runs Claude Code; each skill def is canonical for that skill's role / owns / interfaces / first steps. |
| **Project instructions** | Root `CLAUDE.md`, per-directory `CLAUDE.md` | Project-wide and directory-local conventions, loaded automatically by the harness. |
| **Delivery method** | `sprints/METHOD.md` (this file) | How we sprint, hand off, defer, test, collaborate. Owned by `/sprint`. |
| **Architecture** | `design/arch/` (principles, roadmap, interfaces) | Technical decisions that cross skill boundaries. Owned by `/arch`. |
| **User-preference memory** | `memory/MEMORY.md`, `memory/feedback_*.md`, `memory/project_*.md` | Point-in-time captures of user feedback and project state. Not normative for process — process lives in METHOD.md. |

**Reading order for a new session on this project**:

1. Root `CLAUDE.md` — project overview
2. The skill definition file for the current role (`.claude/commands/{skill}.md`)
3. `sprints/SPRINT.md` for current work
4. `sprints/METHOD.md` (this doc) for the delivery method if the task spans a sprint cycle
5. `design/arch/` for architectural context if the task crosses crate boundaries
6. `memory/MEMORY.md` index for relevant user preferences
7. Per-directory `CLAUDE.md` files when entering a directory

<!-- FIXME(/sprint): `memory/feedback_*.md` currently carries methodology-normative content (e.g. feedback_unit_tests_with_dev.md, feedback_repro_handoff.md). With METHOD.md now canonical, decide during rework whether to: (a) leave memories as point-in-time captures and treat METHOD.md as the single normative source, (b) migrate each methodology-normative memory's content fully into METHOD.md and retire the file, or (c) retain memories as sprintable signals while METHOD.md remains the normative digest. This consolidation pass used option (c) by default — all methodology-relevant memory content is cited and restated in METHOD.md, but the memory files are left in place. -->

---

## 17. FIXMEs from consolidation

FIXMEs raised during this consolidation pass, for action in the methodology rework. Restated here for visibility; the inline `FIXME(/sprint)` or `FIXME(/arch)` comments above are the resolvable form.

### 17.1 Sources out of date

- **17.1a** `sprints/reimplementation.md` predates `/int` and `/sprint` skills. Its skill-definition section enumerates 13 skills; current count is 15. Its per-ring workflow list omits `/int` and `/sprint`.
- **17.1b** `sprints/reimplementation.md` references `docs/spec/` — current path is `spec/`. References `docs/arch/interfaces.md` — canonical path needs verification. References `lib/` — renamed to `stdlib/` (Sprint 11).
- **17.1c** Root `CLAUDE.md` says pre-existing failures are "11 sketch_port + 2 v4_platform"; `memory/feedback_test_serialization.md` says "13 pre-existing failures (11 sketch_port + 2 v4_platform)". Same count; wording differs.

### 17.2 Methodology clauses needing rework

- **17.2a** Phase 2 (refactoring-during-progression anti-pattern, §6.1 rule 2) has been read as "do not refactor in sprint." The 2026-04-24 audits indicate this has over-corrected in practice — duplication is admitted-with-FIXME rather than extracted. Rework should distinguish *speculative* refactoring (deferred) from *emergent* refactoring (mandatory in-sprint).
- **17.2b** `--no-fail-fast` policy has two statements: `memory/feedback_test_serialization.md` and `memory/feedback_test_confidence.md` forbid it (process zombies; overwhelming output); `.claude/commands/sprint.md` §Phase 6 uses it for baseline-ledger integrity. Reconcile.
- **17.2c** Showcase-waiver precedent recorded in `sprints/SPRINT.md` Notes for S62 is explicitly not codified in `.claude/commands/sprint.md` (per user direction 2026-04-22). Decide whether METHOD.md is the right home for the three-clause precedent.

### 17.3 New content to fold in (deferred to the rework pass)

These are the four `/sprint`-owned methodology changes from the 2026-04-24 review that METHOD.md is designed to host:

- **17.3a — Standing structural signal**: `/review` crate-audit pass on a rotation. One crate per sprint, whole-crate scope (file sizes, function sizes, duplication scan, deprecation markers, test-locality ratio, `mirror` / `shared-core` comment count). Findings become FIXMEs on the owning skill's plan.
- **17.3b — Structural budgets on named files**: every file over a threshold (e.g. 1,500 LOC) gets an entry in the owning skill's plan naming ownership, ceiling, and decomposition path if it grows. A diff that breaches the ceiling is a `/review` blocker unless a split or `/arch`-signed budget raise is produced.
- **17.3c — Duplication-admission gate**: any comment containing "mirrors", "shared core of", "same logic as", "parallel migration" is a `/review` blocker. Parallel pipelines require an expiration sprint at admission. `deprecated` markers require a target-sprint tag. No unbounded compat shims.
- **17.3d — Refactoring clause revision**: rewrite §6.1 rule 2 per 17.2a.

And the `/arch`-owned rules METHOD cites but does not define:

- **17.3e — Interface freezing in `cranelisp-types`** (for `/arch`): DTOs + trait contracts live in `types`; ad-hoc inter-crate coupling is a `/review` blocker; changes to existing `types` interfaces require `/arch` sign-off.
- **17.3f — Rust-mechanical forcing functions** (for `/arch`): `pub(crate)` as default with an audit-and-downgrade pass, single facade module per crate, `cargo-public-api` in CI, sealed traits + `#[non_exhaustive]` on DTOs, crate-boundary governance (new cross-crate `pub` requires `/arch` sign-off).

### 17.4 Authority boundaries to confirm

- **17.4a** §1.3 notes that `.claude/commands/sprint.md` still carries the Sprint Archetype in full. Decide whether METHOD §4 is now canonical and sprint.md shrinks to a role-definition pointer, or whether sprint.md stays canonical and METHOD §4 is a summary.
- **17.4b** §16 describes the relationship between `memory/feedback_*.md`, METHOD.md, and skill definitions. The rework pass must confirm which is normative when they disagree (current default: METHOD normative; memories are point-in-time signals).
- **17.4c** `tests/CLAUDE.md §"Isolating Cross-Crate Failures"` is referenced in §5.4a but not verified during consolidation.

---

*End of METHOD.md. For the rework pass (Step 3 of the methodology plan), edit this document directly. For the propagation to `.claude/commands/sprint.md`, `.claude/commands/review.md`, root `CLAUDE.md` (Step 5), wait until METHOD is settled.*
