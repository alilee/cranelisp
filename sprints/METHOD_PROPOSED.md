# Cranelisp Delivery Method — Proposed

> **Status**: SKELETON — structural draft only. Section headers, intents, and table stubs. Prose body deferred until the user signs off on the structure.
> **Relationship to METHOD.md**: METHOD.md is the consolidated current state. METHOD_PROPOSED.md is the target. When METHOD_PROPOSED is signed off, it is renamed to METHOD.md (old METHOD.md archived) and the migration task list (§15) is scheduled.
> **Owner**: `/sprint`.
> **Extract**: §3 (Skill roles, /sprint row), §4 (Sprint archetype, entire), §6.1 (FIXME file protocol), §6.2 (Skill handoff), §7 (Deferral principles), §10 (Collaboration rules relevant to sprint close) extract into the revised `.claude/commands/sprint.md` skill definition.

---

## Table of contents

1. [Purpose and scope](#1-purpose-and-scope)
2. [Skill inventory](#2-skill-inventory)
3. [Skill roles and responsibilities](#3-skill-roles-and-responsibilities)
4. [Sprint archetype](#4-sprint-archetype)
5. [Boundary management](#5-boundary-management)
6. [Cross-skill protocols](#6-cross-skill-protocols)
7. [Deferral principles](#7-deferral-principles)
8. [Testing discipline](#8-testing-discipline)
9. [Showcase discipline](#9-showcase-discipline)
10. [Collaboration rules](#10-collaboration-rules)
11. [Agent discipline](#11-agent-discipline)
12. [Implementation discipline](#12-implementation-discipline)
13. [Change control](#13-change-control)
14. [Relationship to harness documents](#14-relationship-to-harness-documents)
15. [Migration from METHOD to METHOD_PROPOSED](#15-migration-from-method-to-method_proposed)
16. [Appendix A: Extract for /sprint skill definition](#16-appendix-a-extract-for-sprint-skill-definition)

---

## 1. Purpose and scope

**Intent**: This document is the normative delivery method for Cranelisp in maintenance-and-enhancement mode. It defines what each skill does, how sprints are organized, and how skills hand off to each other. Ring / phase re-establishment content is not in scope — the reimplementation re-establishment is complete; the project now operates in steady state.

**Not in this document**:

- Architectural rules and principles — owned by `/arch` in `design/arch/`.
- Per-crate design — owned by `/design` in `design/{crate}/{crate}.md` (narrow deployment, one crate per invocation).
- Agent-facing workflow detail — lives in `.claude/commands/{skill}.md`. This document is the inter-skill view; skill definitions are the intra-skill view.
- Domain knowledge — lives in `CLAUDE.md` files near the code.
- Historical narrative — lives in `sprints/archive/` and git history.

---

## 2. Skill inventory

**Intent**: One-line-per-skill table. Categories reflect function, not hierarchy. Detail lives in `.claude/commands/{skill}.md` and is iterated in place.

Three skills (`/design`, `/dev`, `/review`) are **generic with narrow deployment**: one skill definition each, but each invocation focuses on exactly one crate. Per-crate specialization lives in `design/{crate}/{crate}.md` and per-directory `CLAUDE.md`, not in the skill definition. Together they form the **per-crate triad** — design / implementation / review — applied to whichever of the 6 crate-shaped surfaces is in scope. See §3.2 and §3.3.

| Skill | Category | Owns | Primary output |
|---|---|---|---|
| `/spec` | Authority | `spec/` — language specification | Normative spec text |
| `/arch` | Authority | `design/arch/`; `crates/cranelisp-types/` (types + traits that cross crate boundaries); public-API surfaces of every crate | Interface types, principles, Decisions, public-API approvals |
| `/qa` | Authority | `tests/` — integration tests and test plan; `tests/plan/baseline.md` | Spec-traceable integration tests as the normative conformance evidence linking spec → architecture → release candidate |
| `/design` | Compiler (per-crate triad — design role) | `design/{crate}/{crate}.md` for **all 6 crate-shaped surfaces** (frontend, typecheck, backend, runtime, platform, int); narrow deployment — one crate per invocation | Crate overview doc + subordinate topic docs; does not edit source |
| `/dev` | Compiler (per-crate triad — implementation role) | `crates/cranelisp-frontend/`, `cranelisp-typecheck/`, `cranelisp-backend/`, `cranelisp-runtime/`, `cranelisp-platform/`, `src/` — **all 6 crate-shaped surfaces**; narrow deployment — one crate per invocation. (`cranelisp-runtime` is paired with `cranelisp-backend`; `cranelisp-platform` is consumer of `cranelisp-runtime`, not owner.) | Implementation code + unit tests |
| `/review` | Compiler (per-crate triad — review role) | No persistent directory; narrow deployment across **all 6 crate-shaped surfaces**. Steward of maintainability and extensibility at the change-set grain (notionally a PR). | Quality findings on a round of change, against the crate's design intent and accumulated state |
| `/sprint` | Coordination | `sprints/` — roadmap, current sprint, archive, fixmes | Sprint plans and outcome reports |
| `/stdlib` | User-proxy | `stdlib/` | Standard library in Cranelisp |
| `/examples` | User-proxy | `examples/` | Learning-sequence example programs |
| `/docs` | User-proxy | `user/` | Tutorials, guide, getting-started |
| `/repl` | User-proxy | `repl/` — REPL experience spec, demos, harness | Demos, experience tests |
| `/port` | User-proxy | `exemplar/` | Showcase project (Sudoku solver) |

**Total: 12 skills.** Net change vs current 15-skill state: `/frontend` + `/typecheck` + `/backend` + `/int` + `/platform` merged into `/dev` (now narrow-deployed across all 6 crate-shaped surfaces); `/design` added; `/review` recategorized to Compiler (per-crate triad); `/qa` recategorized to Authority; `cranelisp-runtime` ownership corrected (was assumed `/platform`, is `/dev` paired with backend mode); the integration-bottleneck rule (sprint scope sized to one skill's capacity) is retired — it was a holdover from the per-skill-per-crate model and is no longer load-bearing under narrow-deployment.

<!-- FIXME(/sprint): directory-ownership column above needs verification against current repo layout. crates/cranelisp-types/ ownership shifting to /arch is a new rule and migration item (§15 M3). cranelisp-runtime ownership reassignment to /dev (backend mode) is also new — confirm via /arch review during M3 / M13. -->

---

## 3. Skill roles and responsibilities

**Intent**: Brief prose per category. Per-skill detail lives in skill definitions.

### 3.1 Authority (`/spec`, `/arch`, `/qa`)

**Intent**: Skills that arbitrate questions of correctness. Together they form the chain that links the language to the release candidate:

- **`/spec`** — what the language does. Owns `spec/`. Arbitrates ambiguity. Maintains the normative spec.
- **`/arch`** — how the code is structured. Owns `design/arch/` and `crates/cranelisp-types/`. Decides crate boundaries, interface types and traits, principles. Approves every public-surface change (inwards and outwards) per §5.2.
- **`/qa`** — whether the code does what the spec says. Owns `tests/` and `tests/plan/baseline.md`. Writes integration tests for the full spec surface (not just what is implemented), spec-traceable via `// spec:` comments. The integration test suite is the durable conformance evidence; failing in-scope tests block sprint close (§4.6 exit gate).

Authority skills do not generally implement compiler code. `/spec` writes spec text; `/arch` writes interface types and design rules; `/qa` writes tests. Each produces normative artifacts that other skills work within and verify against.

**Why `/qa` is Authority, not Coordination.** Tests are the durable link between spec and release. `/qa`'s test suite is the contract a release candidate must satisfy — it is normative, not advisory. A defect surfaced by a `/qa` integration test is not a recommendation; it is evidence the release does not meet spec. This is the same authority shape as `/spec` (defines the rule) and `/arch` (defines the structure): `/qa` defines the verification.

**Boundary with implementing skills.** Unit tests are written by the implementing skill, in the same crate, in the same wave. `/qa` does not write unit tests. `/qa`'s scope is integration tests in `tests/` — full-pipeline, cross-crate, spec-traceable.

### 3.2 Design (`/design`)

**Intent**: Per-crate internal design. Translates spec into coherent implementation approach. Produces the master design document per crate (`design/{crate}/{crate}.md`), subordinate topic docs for concurrency / observability / performance where relevant, and updates them for currency. Drives quality attributes (simplicity, maintainability, observability, concurrency-safety, performance) that individual feature designs do not reliably address. Notes testability and coverage but does not own tests. Reviews design fidelity during implementation. **Does not write or edit code.**

**Narrow deployment**: `/design` is one skill, but each invocation focuses on exactly one crate. The agent's first action on invocation is to confirm the crate in scope (from the user's prompt, from the current `SPRINT.md` wave assignment, or by asking) and read `design/{crate}/{crate}.md` plus any subordinate topic docs. Cross-crate design questions route through `/arch` (interface change in `cranelisp-types`); `/design` does not span crates within a single invocation.

**Specialization vector**: per-crate design content lives in the design doc the skill maintains, not in the skill definition. The skill definition is generic — the same `/design` agent works across crates, concentrating on one at a time.

**Boundary with `/arch`**: `/design` is per-crate and intra-crate. `/arch` is between-crate. When `/design`'s approach requires a new cross-crate interface, `/arch` authors it in the types crate.

**Boundary with `/review`**: `/design` produces the design of record; `/review` confirms a change moves toward that design intent at the change-set grain. Both are narrow-deployment, both read the same `design/{crate}/{crate}.md`. `/design` is forward-looking (what should this crate be); `/review` is point-in-time (does this round of change preserve maintainability and extensibility against the crate's design and accumulated state).

**Feature design subordinate to crate design.** Feature-specific design is an elaboration of the crate overview, not a standalone document competing with it. When a feature design would change the crate's overall shape, update the overview first.

### 3.3 Compiler (`/design`, `/dev`, `/review`)

**Intent**: Three skills, all generic with narrow deployment, each playing one role in the **per-crate triad** — design / implementation / review — applied to whichever of the 6 crate-shaped surfaces is in scope. The triad is constant in shape and in skills; only the crate varies.

The 6 crate-shaped surfaces:

- `cranelisp-frontend`
- `cranelisp-typecheck`
- `cranelisp-backend`
- `cranelisp-runtime` (paired with `cranelisp-backend`)
- `cranelisp-platform` (consumer of `cranelisp-runtime`, not owner)
- `src/` (the binary crate — pipeline orchestration, REPL session, CLI)

#### `/design` — design role (covered in §3.2)

What the crate should be. Owns `design/{crate}/{crate}.md` for every crate. Narrow deployment: one crate per invocation. Does not edit code.

#### `/dev` — implementation role

Generic implementation skill, narrow deployment across all 6 crate-shaped surfaces. One skill definition; works on exactly one crate per invocation. The crate in scope is identified at invocation. The agent reads `design/{crate}/{crate}.md` (specialization vector — what to do) and `crates/{crate}/CLAUDE.md` or `src/CLAUDE.md` (local conventions — how the code is) before any work.

Replaces the previous `/frontend`, `/typecheck`, `/backend`, `/int`, and `/platform` per-crate skills. Their distinct content was nearly all *what* (decisions, direction — moved to per-crate design docs) or *how the code is* (API gotchas, build conventions — moved to per-crate `CLAUDE.md`). What remained as genuine *how to work* was the same across all of them, so they collapse to one generic skill.

**Implementation only — does not author its own design.** When `/dev` discovers that the design doc is wrong or incomplete during implementation, it files a FIXME to `/design` rather than editing the design doc directly.

#### `/review` — review role

Generic quality-stewardship skill, narrow deployment across all 6 crate-shaped surfaces. **Steward of crate maintainability and extensibility at the change-set grain (notionally a PR)** — not diff-fixated. Diffs are focus material; the round of change is the unit of review. The agent reads `design/{crate}/{crate}.md` (the standard against which the change is reviewed), the change set (diff + surrounding code), and the crate's accumulated state. Augments `/design` and `/dev` — works alongside, not above. Findings flow as FIXMEs (§6.1) to `/dev` (implementation) or `/design` (design intent should evolve), or — for cross-crate / public-API concerns — to `/arch`. Has no blocking authority on its own; binding force comes through `/sprint` exit gates and the deferral escalation rules (§7).

#### Triad summary

`/design` writes intent; `/dev` implements; `/review` checks the implementation against the intent and the accumulated crate state. The triad runs on the same crate and reads the same documents — only the role differs. Cross-crate work splits into sequential per-crate triad invocations, coordinated by `/sprint` and any required interface change by `/arch`.

### 3.4 Coordination (`/sprint`)

**Intent**: Process orchestration.

- **`/sprint`** — plans sprints, coordinates execution, tracks FIXMEs and deferrals, gates phases and waves, shepherds close. The sprint archetype (§4) is `/sprint`'s core artifact. `/sprint` owns no code or design content — its outputs are sprint plans, wave organization, and outcome reports. Does not arbitrate technical questions; routes them to the appropriate authority skill (`/spec`, `/arch`, `/qa`).

`/qa` was previously listed here; recategorized to Authority (§3.1) on the basis that integration tests are the normative conformance link spec → release. `/review` was previously listed here; recategorized to Compiler (§3.3) as part of the per-crate triad with `/design` and `/dev`.

### 3.5 User-proxy (`/stdlib`, `/examples`, `/docs`, `/repl`, `/port`)

**Intent**: Skills that exercise the language as a user would. They operate in the user-facing phase of each sprint (§4.1 Phase 6), demonstrate what the language can do, and file FIXMEs for gaps. They work from the spec and sprint scope **outside-in** — not from what happened to be built.

---

## 4. Sprint archetype

**Intent**: Every sprint follows this sequential flow. Two phases — language then user-facing — both required for close. `/sprint` orchestrates the process by issuing skill invocations; other skills execute within it.

### 4.1 Phases

The **Agent invocations** column lists the skill invocations that occur during the phase. `/sprint` is the orchestrator (issues the invocations and gates between them) but is also itself an invocation in scope/wave/close phases.

| Phase | Name | Agent invocations | Inputs | Outputs | Exit gate |
|---|---|---|---|---|---|
| 1 | Scope | `/sprint` | ROADMAP, prior-sprint archive, open FIXMEs (`sprints/fixmes/`), prior-ring coverage audit | `SPRINT.md` DRAFT | User approval of scope |
| 2 | Architecture review | `/arch` | Sprint scope, current `design/arch/`, types-crate state | Interface changes approved / deferred; scope adjustments | `/arch` sign-off on scope |
| 3 | Design | `/spec`, `/arch`, `/design` per crate (frontend, typecheck, backend, runtime, platform, int — every crate touched by sprint scope), `/qa` | Sprint scope, current per-crate design docs, current spec, current types crate | Each invoked skill updates its design / spec / interface / test-plan to incorporate sprint scope; interface changes confirmed in types crate; testability assessed | `/arch` confirms public-API + interface set is complete; `/qa` has enough to draft failing integration tests; all touched design docs current with scope |
| 4 | Wave organization | `/sprint` | Updated skill plans from Phase 3, inter-skill dependencies | Wave breakdown in `SPRINT.md`; task list; `SPRINT.md` ACTIVE | Waves written; skills know what to do |
| 5 | Language phase | `/qa` first (sprint-wide: failing integration AND e2e tests against scope). Then per crate in scope, parallel across crates: D/D/R cycle — `/design` (refine per-crate design) → `/dev` (implement + unit tests) → `/review` (change-set review). Iterate D/D/R within each crate as needed. | `/qa` test plan, Phase 3 design intent, interface types, scope | Sprint-wide: passing integration + e2e tests; per crate: refined design doc, implementation, unit tests, change-set review findings, public-API diffs approved | **`/sprint` (with user) decides Phase 5 is concluded.** Authoritative judgment of what ships this sprint. Subsequent phases take what is given. |
| 6a | User-facing assessment | User-proxy skills (`/repl`, `/port`, `/stdlib`, `/examples`, `/docs`) + `/sprint` | Spec, sprint scope, shipped compiler artifacts | Assessment of what was actually delivered vs scope/spec; user-facing work plan (what demos, exemplar updates, stdlib integrations, examples, docs to author against what shipped); FIXMEs filed in `sprints/fixmes/` for gaps observed | Plan agreed; gap FIXMEs filed |
| 6b | User-facing action | User-proxy skills per the 6a plan | 6a plan, shipped compiler artifacts | New sprint demo (`/repl`), exemplar update (`/port`), stdlib integration (`/stdlib`), examples update (`/examples`), docs update (`/docs`); all prior demos replayed green | All planned user-facing artifacts delivered against what shipped; demos replay green |
| 7 | Close | `/sprint` (with user) | Phase 5 + Phase 6 outputs | Sprint outcome report; archive; ROADMAP update; gap FIXMEs from 6a/6b carried to next sprint as input | User approval of close |


### 4.2 Phase 1 — Scope

**Intent**: `/sprint` scans open FIXMEs (`sprints/fixmes/`) + prior-sprint archive for carries + prior-ring coverage audit. Proposes next increment. User approves before Phase 2.

### 4.3 Phase 2 — Architecture review

**Intent**: `/arch` reviews proposed scope for technical coherence, interim-architecture risk (Principle 8), and public-API impact. Updates types crate if new cross-crate interfaces are required. Sign-off gates Phase 3.

### 4.4 Phase 3 — Design

**Intent**: Each invoked skill updates its own design / spec / interface / test-plan to incorporate the sprint scope and confirm interface changes. Phase 3 is where the sprint's intent is committed to writing — across every responsible skill, before any implementation begins.

**Invocations**:

- **`/spec`** — updates spec text if the sprint scope touches language semantics (e.g. new construct, clarified ambiguity).
- **`/arch`** — confirms or extends the cross-crate types and traits in `crates/cranelisp-types/`; updates `design/arch/` decisions if the sprint introduces a new architectural choice. Approves all public-API changes the sprint anticipates.
- **`/design` per crate** — for each crate touched by sprint scope (`cranelisp-frontend`, `cranelisp-typecheck`, `cranelisp-backend`, `cranelisp-runtime`, `cranelisp-platform`, or `src/`), invoked narrow to that crate. Reads the crate's current `design/{crate}/{crate}.md` and updates it to reflect sprint scope. Subordinate topic docs added/updated where the sprint introduces specific concerns (concurrency, performance, observability, etc.). Confirms interface usage against `/arch`'s types-crate updates. **`/design` covers all 6 crate-shaped surfaces** — including `src/` (the binary crate) and `cranelisp-platform/`. `/dev` does not author its own design; that is `/design`'s scope.
- **`/qa`** — reads all updated design docs and the spec; updates `tests/plan/ring{N}.md` with test cases for the sprint scope. By Phase 3 close, `/qa` has a draft test plan covering every spec requirement in scope (whether or not the implementation exists yet).

**Design docs are prerequisite thinking, not post-hoc documentation.** No implementation starts until every Phase-3 invocation has updated its artifact and `/arch` has confirmed the interface set is complete.

**Phase 3 exit gate**: `/arch` confirms public-API and interface changes are settled; `/qa` confirms it has enough to draft failing integration tests; all touched design docs are current with sprint scope.

### 4.5 Phase 4 — Wave organization

**Intent**: `/sprint` organizes parallel work into waves. A wave is a set of skill invocations with no inter-dependencies.

### 4.6 Phase 5 — Language phase

**Intent**: QA-first across the entire solution; then per-crate D/D/R cycle in parallel across crates. Phase 5 close is the **authoritative judgment of what ships this sprint** — subsequent phases (6a, 6b, 7) take what is given and demonstrate / archive it. Feedback from those phases flows forward as FIXMEs to the next sprint.

**Sequence**:

1. **`/qa` first** (one invocation, scope = whole sprint, sprint-wide). Writes failing tests in `tests/` covering the full spec surface in scope. **Both integration tests AND end-to-end tests** — integration verifies cross-crate behaviour at the pipeline level; e2e verifies the full release-candidate behaviour through the binary. Tests are derived from spec + the Phase 3 design docs, not from the implementation. Tests fail because the implementation does not exist yet — this is the intended state. Failing-not-ignored per §8.2.

2. **Per-crate D/D/R cycle** (one cycle per crate in scope, parallel across crates). Each crate runs:

   - **`/design`** (narrow to crate) — refines `design/{crate}/{crate}.md` against the actual implementation problem now in front of it. Phase 3 set the broad design intent; Phase 5's `/design` invocation updates the doc as implementation discovers nuances. Updates subordinate topic docs (concurrency, observability, performance) where a sprint touches those concerns.
   - **`/dev`** (narrow to crate) — implements against the refined design doc and against the failing tests as acceptance criteria. Writes unit tests alongside.
   - **`/review`** (narrow to crate) — reviews the change set against the crate's design intent and accumulated state. Findings flow as FIXMEs to `/dev` (implementation), `/design` (intent should evolve), or `/arch` (public-API / cross-crate concern).

3. **Iterate D/D/R within each crate** as needed: design refinement informs implementation; review findings inform either further implementation or further design refinement; cycle until the crate's portion of the failing-test set passes and review is settled.

**Parallelism**: multiple crates run their D/D/R cycles in parallel. `/qa`'s upfront test wave covers the whole sprint at once, so all crates have their acceptance criteria in place before any starts cycling.

**Why QA-first.** When `/qa` runs after implementation, tests are unconsciously shaped by what exists — testing the code, not the spec. Running `/qa` first forces spec-first test design and gives every implementing crate a concrete, executable acceptance criterion before any cycle begins. Including e2e tests in the upfront wave catches missing cross-pipeline integration that pure unit/integration testing leaves invisible. (Historical: Sprint 16 had `/qa` run post-implementation, wrote 25 passing tests covering only `Pure`/`bind`, missed that `print` — the sprint's headline goal — had no Effect codegen. QA-first would have caught that gap before implementation closed.)

**Phase 5 exit — `/sprint` (with user) decides what ships**:

The exit gate below is the *expected* condition at conclusion. `/sprint` and the user are the authoritative judges. If a feature in scope is not delivered cleanly, the call is taken in Phase 5 — either close Phase 5 short (defer the feature, file a FIXME, ship what is done) or extend Phase 5 to land it. The decision is conscious and explicit. Phase 6 takes what Phase 5 hands over; gaps observed in Phase 6 become FIXMEs forward, not retroactive Phase 5 reopens.

Expected exit condition:

- [ ] All `/qa`-authored failing integration + e2e tests for in-scope features now pass
- [ ] `cargo nextest run` green across the workspace
- [ ] No `#[ignore]`'d tests for in-scope features
- [ ] All `/review` Blocker and Important findings (per crate) resolved
- [ ] All public-API changes approved by `/arch` (cargo-public-api diffs reviewed)
- [ ] Per-crate `design/{crate}/{crate}.md` current with the shipped implementation
- [ ] Baseline ledger (`tests/plan/baseline.md`) integrity verified

### 4.7 Phase 6 — User-facing phase (assessment, then action)

**Intent**: User-proxy skills exercise what shipped (whatever Phase 5 handed over) and demonstrate it. Two sub-phases: first assess what was actually delivered and plan the user-facing work; then execute that plan. **Phase 6 takes what is given** — it does not reopen Phase 5. Gaps observed during assessment or action become FIXMEs in `sprints/fixmes/` for the next sprint to address.

#### 4.7a Phase 6a — Assessment and planning

**Intent**: User-proxy skills assess the delivered compiler artifacts against the spec and sprint scope, identify gaps, and produce a plan for the user-facing work in 6b. Run before any user-facing artifact is authored.

**Invocations**: `/repl`, `/port`, `/stdlib`, `/examples`, `/docs` (each, narrow to its surface) + `/sprint` (collects the assessments and plans).

**Activities**:

- Each user-proxy skill reads the sprint scope, spec sections in scope, and the Phase 5 outputs.
- Each assesses, from outside-in, whether the spec'd capability is reachable from its user surface (REPL, exemplar, stdlib, examples, docs).
- Each produces a 6b plan: what demo / exemplar update / stdlib integration / examples update / docs update will exercise the delivered capability **as it actually shipped**.
- Each files FIXMEs in `sprints/fixmes/` for any gap discovered during assessment (feature missing affordance, friction, unhelpful error, incomplete coverage of spec). These flow forward as input to the next sprint.

**6a exit gate**: `/sprint` confirms each user-proxy skill has produced an assessment and a 6b plan; gap FIXMEs filed.

#### 4.7b Phase 6b — Action

**Intent**: User-proxy skills execute the 6a plan against what shipped.

**Invocations**: `/repl`, `/port`, `/stdlib`, `/examples`, `/docs` (each per its 6a plan; can run in parallel).

**Activities**:

- `/repl` authors the new sprint demo (`repl/demos/{sprint-id}.demo` or equivalent) demonstrating what shipped.
- `/port` extends the exemplar to exercise new features that shipped; verifies existing exemplar still runs.
- `/stdlib` integrates shipped features into the standard library where 6a planned.
- `/examples` updates the learning sequence.
- `/docs` updates user-facing documentation.
- All existing demos are replayed green as regression guards.
- Additional gap FIXMEs filed for anything surfaced during action that 6a missed.

**6b exit gate**: all 6a-planned user-facing artifacts delivered against what shipped; new demo plays green; prior demos replay green.

### 4.8 Phase 7 — Close

**Intent**: `/sprint` authors outcome report, archives `SPRINT.md`, updates ROADMAP. User approves close and commit explicitly.

**Close checklist**:

- [ ] Phase 5 conclusion taken (`/sprint` + user); shipped state documented in outcome report
- [ ] Phase 6a assessment complete; gap FIXMEs filed
- [ ] Phase 6b deliverables complete — new sprint demo plays green, exemplar runs, stdlib/docs/examples updated, prior demos replay green
- [ ] `ROADMAP.md` updated
- [ ] User approves close

### 4.9 Mid-sprint adjustment

**Intent**: If user invokes `/sprint` mid-sprint, `/sprint` reports status + recommends continue / re-scope / close. Scope changes require user sign-off. `/sprint` never closes unilaterally.

### 4.10 SPRINT.md template

**Intent**: Template for current sprint plan. Reference — full template in `.claude/commands/sprint.md` per extract (§16).

---

## 5. Boundary management

**Intent**: Make crate boundaries structural rather than conventional. `/arch` owns boundaries; `/design` audits adherence within crates; enforcement is mechanical where possible.

### 5.1 Types and traits that cross crate boundaries

**Intent**: Defined by `/arch` in `crates/cranelisp-types/`. No cross-crate DTO or trait is authored outside the types crate. Consumer crates depend on the types crate; provider crates implement its traits.

### 5.2 Public-API review — inwards and outwards

**Intent**: Every change to any crate's public surface — new `pub` item, signature change, deletion, re-export — requires `/arch` approval.

- **Inwards** (crate changes its own exports): the owning skill proposes; `/arch` approves before merge.
- **Outwards** (crate consumes a new import from another crate): `/arch` approves the new cross-crate coupling.

Enforced by `cargo-public-api` diff gate in CI (§5.4) plus PR-level review of cross-crate imports.

### 5.3 `pub(crate)` as default

**Intent**: Default privacy is `pub(crate)`. Every `pub` is a deliberate act requiring justification. One-time downgrade pass as part of migration (§15); ongoing enforcement via `/design` audit + `/review` on diffs.

### 5.4 `cargo-public-api` in CI

**Intent**: Tracked public-API file per crate, diffed in CI. Any diff requires `/arch` approval. Makes public-surface growth visible.

### 5.5 Facade module per crate

**Intent**: Each crate exposes its public API through a single facade module (`lib.rs` or `facade.rs`). Internal modules are `pub(crate)` or narrower. Reviewers see the whole public surface in one file.

### 5.6 Sealed traits and `#[non_exhaustive]`

**Intent**: Traits in the types crate that crate X implements for crate Y to consume should be sealed — consumers depend on the shape; only `/arch` extends it. DTOs in the types crate are `#[non_exhaustive]` so adding fields is non-breaking.

---

## 6. Cross-skill protocols

### 6.1 FIXME file protocol

**Intent**: FIXMEs are files in `sprints/fixmes/`, not inline comments. One file per issue. Deleted on resolution (git history is the record). Avoids file-ownership ambiguity and multi-skill edit conflicts.

**File naming**: `sprints/fixmes/NNNN-short-name.md` where NNNN is a unique sequential number. Filing skill scans for max existing number + 1. `/sprint` resolves rare collisions at wave gate.

**File format** (frontmatter + body):

```markdown
---
number: 0042
target: /design
filed_by: /dev
filed_at: 2026-04-24
sprint_filed: 62
refers_to: crates/cranelisp-typecheck/src/checker.rs (ensure_module_exists)
status: open
---

# Short description

## Issue
…

## Proposed resolution
…

## Context
…
```

**Lifecycle**:

1. Filing skill discovers issue → creates numbered file → commits.
2. Owning skill sees file at next wave gate or sprint Phase 1 scan.
3. Owning skill resolves (incorporates change into their owned files) → deletes the FIXME file → commits with a message naming what was resolved.
4. If deferred, `status: deferred` + rationale + target sprint; file remains.

**Wave gate mechanic**: before `/sprint` advances to the next wave, greps `sprints/fixmes/*.md` for `target: /skill-in-wave` AND `status: open`. Any match blocks advancement.

**Only owning skill deletes.** `/sprint` does not delete FIXME files — only the targeted skill resolves and removes.

### 6.2 Skill handoff

**Intent**: Every skill plan ends with **Next skills** section recommending invocation order. Consults `SPRINT.md` for active sprint; `design/arch/roadmap.md` otherwise.

### 6.3 Usability findings vs defects

**Intent**: Two categories of user-proxy feedback.

- **Usability finding**: friction, ergonomics, missing API, unhelpful error. FIXME file is sufficient closure.
- **Defect**: bug, spec violation, crash, output mismatch. FIXME file AND `/qa` authors a failing integration test reproducing the issue. Documentation alone is not closure for defects.

### 6.4 Reproduction discipline

**Intent**: Minimal repro required before any cross-skill defect handoff. Three sub-protocols.

- **6.4a Compiler-skill → compiler-skill**: discovering skill produces minimal repro before handoff. Surface error signatures mask layered bugs.
- **6.4b `/qa` cluster reduction**: multiple failing tests with similar mode → `/qa` halves to minimal repro before spawning a compiler skill.
- **6.4c User-proxy → `/qa` → compiler skill**: user-proxy authors repro in-session; `/qa` copies into `tests/`; compiler skill works against `tests/` only. Repros never live in `exemplar/` or `examples/`.
- **6.4d Repros join suite**: every reduction produces a committed failing test. Partial reductions count. Small repros preferred (fix often obvious during isolation; small CLIF inspectable by eye).

---

## 7. Deferral principles

**Intent**: Three anti-patterns. Revised from current METHOD to separate emergent vs speculative refactoring.

### 7.1 Three anti-patterns

1. **Defects discovered during Phase 5 are addressed in Phase 5.** Phase 5 conclusion is the authoritative judgment of what ships this sprint. `/sprint` (with user) may either fix the defect, defer with explicit rationale, or close Phase 5 short — whichever path is chosen, it is conscious and recorded. The only exception worth carrying without explicit deferral approval is a defect requiring architectural work not yet designed (tracked as FIXME, scoped for a future sprint by `/arch`). Phase 6 does not reopen Phase 5 — observations there flow forward as FIXMEs (§7.3).
2. **Speculative refactoring is deferred; emergent refactoring is mandatory.**
   - *Speculative*: cleanup unrelated to the current work. Deferred unless `/design` explicitly schedules it.
   - *Emergent*: cleanup the current work has made cheap — a duplicate pattern hit its third instance, a function grew past its budget, a `mirror` comment appeared. **Mandatory in-sprint**. Filed as FIXME only if the extraction genuinely can't fit the sprint.
3. **Interim architecture is avoided, not deferred.** If a feature would require throwaway infrastructure a later ring replaces, don't build it. Principle 8.

### 7.2 2× escalation

**Intent**: Items deferred once may be deferred again with rationale. Items deferred twice ship in the current sprint or require explicit user sign-off for a third deferral. Applies to FIXMEs, ignored tests, and `/review` findings.

### 7.3 Phase 6 FIXMEs flow forward as input

**Intent**: Phase 6 takes what Phase 5 hands over. Whatever Phase 6 surfaces — friction, missing affordance, unhelpful error, incomplete coverage of spec — is filed as a FIXME and flows forward to the next sprint as scope input. This is not a carry-out of defects (§7.1 rule 1): Phase 5 conclusion is the authoritative judgment of what shipped this sprint. Phase 6 demonstrates against that judgment. Items not delivered in Phase 5, or items delivered with rough edges, become next-sprint inputs through the FIXME protocol — that is the forward path, not a retroactive Phase 5 reopen.

---

## 8. Testing discipline

**Intent**: Brief — this section references skill-definition detail rather than restating it.

### 8.1 Ownership

Unit tests: implementing skill, inside the crate, during the wave that ships the feature. Integration tests: `/qa`, in `tests/`, spec-traceable. `/qa` does not write unit tests.

### 8.2 Spec-first, failing tests stay failing

`/qa` writes tests for the full spec surface, not just what is implemented. Failing tests due to spec violations stay failing until devs make them pass. `#[ignore]` is reserved for future-sprint requirements not yet scheduled.

### 8.3 Running tests

`cargo nextest run` always. Never background. 30-second expectation. One agent runs at a time. Targeted subsets first, full suite when targeted pass. `--no-fail-fast` permitted only for sprint-close baseline ledger integrity check.

### 8.4 Validate failing tests against spec before fixing code

The failing test may be wrong; check spec compliance first.

### 8.5 Test tuning after large refactors

Review for slow tests after waves that shuffle structure.

---

## 9. Showcase discipline

**Intent**: Now a property of the user-facing phase (§4.7), not a trailing pass on the language phase. Demos operate from spec and sprint scope outside-in, not from what-was-built.

- New demo per sprint authored by `/repl` from sprint scope.
- All prior demos replayed green as regression guards.
- Piped through the real REPL before commit.
- `/sig` shown for key functions to aid understanding.

---

## 10. Collaboration rules

### 10.1 Review before enact

**Intent**: All code changes proposed to user for review before being enacted. Subagents research and propose, not implement.

### 10.2 Sprint close requires user approval

**Intent**: `/sprint` does not close (archive + update ROADMAP) until user has reviewed the outcome. User confirms close and commit explicitly.

### 10.3 Communication via artifacts

**Intent**: Skills communicate through repo files — specs, design docs, FIXME files, SPRINT.md — not out-of-band channels.

---

## 11. Agent discipline

**Intent**: Rules for spawning subagents. Short — detail in skill definitions.

- **Separate agents per skill.** Never one agent across multiple roles.
- **No worktree isolation.** Project-specific: sketch vs reimplementation confusion.
- **Agents clean their own crate.** Every implementation subagent prompt requires `cargo check` + warning cleanup.
- **Git discipline.** Forbidden: `git stash drop`, `git stash clear`, `git reset --hard`, `git checkout --`, `git restore`, `git clean -f`/`-fd`. Permitted: `git stash` + `git stash pop` pairs.

---

## 12. Implementation discipline

**Intent**: Short. Detail in skill definitions.

- **Target state first.** Restructure toward target data model; don't patch current structure.
- **No premature performance.** Single correct path first; tune later.

---

## 13. Change control

**Intent**: Who decides what.

| Change type | Owner | Process |
|---|---|---|
| Spec ambiguity / change | `/spec` | Check prototype → record normative or propose change |
| Cross-crate interface (types crate) | `/arch` | Authored in types crate; reviewed by consuming skills |
| Public-API change (any crate) | `/arch` | Reviewed via cargo-public-api diff; consumer crates approve outwards |
| Crate-internal design | `/design` | Update `design/{crate}/{crate}.md`; subordinate elaborations; `/dev` implements |
| Maintainability / extensibility risk on a change set | `/review` | Reviewed at change-set grain (PR-shaped); FIXMEs to `/dev` (impl) or `/design` (intent should evolve); deferral escalation per §7 |
| Spec conformance — failing integration / e2e test | `/qa` (authoritative) | Test stays failing; triage → assign to owning compiler skill → verify fix. Phase 5 conclusion (`/sprint` + user) decides whether unresolved tests block exit or ship as deferred items per §7.1. |
| User-facing observation (Phase 6) | User-proxy skill | FIXME file → next sprint input. No retroactive Phase 5 reopen. |
| Sprint scope conclusion (Phase 5 → 6) | `/sprint` + user | Authoritative judgment of what ships this sprint |
| Sprint scope (Phase 1) | `/sprint` + user | Proposed by `/sprint`, approved by user |

### Shared artifacts

- Language spec (`spec/`) — `/spec`
- Types crate (`crates/cranelisp-types/`) — `/arch`
- Interface docs and principles (`design/arch/`) — `/arch`
- Integration test suite + baseline ledger (`tests/`, `tests/plan/baseline.md`) — `/qa`
- Per-crate design (`design/{crate}/{crate}.md`) — `/design`
- This methodology document (`sprints/METHOD.md`) — `/sprint`

---

## 14. Relationship to harness documents

**Intent**: What is authoritative for what.

### 14.1 Three-way split for skill content

Three distinct kinds of content, three distinct homes:

| Content kind | Lives in | Example |
|---|---|---|
| **How to work** (process, workflow, agent procedures) | Skill definition (`.claude/commands/{skill}.md`) | "First, confirm the crate in scope. Then read the design doc. Then proceed." |
| **What to decide** (direction, intent, codified design decisions) | Per-crate design doc (`design/{crate}/{crate}.md`) | "RC discipline: borrowed-vs-consumed-vs-unique tracking. Drop glue: closure embedded pointer; ADT field cleanup at dealloc." |
| **How the code is** (data structures, invariants, local conventions) | `CLAUDE.md` per directory | "Cranelift v0.125 API: `jump`/`brif` take `IntoIterator<Item = &'a BlockArg>`; `icmp` returns i8." |

This separation is the rule that lets generic skills (`/dev`, `/design`, `/review`) carry per-crate weight without per-crate skill definitions. The skill is the process; the design doc is the specialization; the `CLAUDE.md` is the code's voice.

When in doubt about where new content belongs:

- **Process / workflow / "before doing X, do Y"** → skill definition
- **Decision / direction / target shape** → per-crate design doc
- **Mechanical / API-surface / convention** → `CLAUDE.md`

### 14.2 Authority and reading order

| Layer | Path | Scope | Authority |
|---|---|---|---|
| Methodology | `sprints/METHOD.md` (this) | How we deliver | `/sprint` |
| Skill definition | `.claude/commands/{skill}.md` | Agent-facing workflow for one skill | Skill owner |
| Architecture | `design/arch/` | Between-crate rules, principles, interface types | `/arch` |
| Crate design | `design/{crate}/{crate}.md` + subordinates | Within-crate implementation approach (the specialization vector) | `/design` |
| Domain knowledge | `CLAUDE.md` per directory | Data structures, invariants, conventions local to code | Directory-owning skill |
| Signals | `memory/` | Point-in-time observations; non-normative | User + Claude |

**`CLAUDE.md` files refer to canonical documents rather than restating them.** Methodology rules live in METHOD.md; architectural rules live in `design/arch/`; skill workflows live in skill definitions. `CLAUDE.md` points to these and carries only domain-local information.

**Reading order for a new session**:

1. Root `CLAUDE.md` — project overview + pointers
2. Skill definition for the current role
3. `sprints/SPRINT.md` for current work
4. `sprints/METHOD.md` for the delivery method
5. `design/arch/` + `design/{crate}/` for current design context
6. Per-directory `CLAUDE.md` when entering a directory

---

## 15. Migration from METHOD to METHOD_PROPOSED

**Intent**: One-shot migration tasks to transition from current state to METHOD_PROPOSED. Executed as a dedicated migration sprint (or sequence).

| # | Task | Owner | Rough size |
|---|---|---|---|
| M1 | Author `/dev`, `/design`, and `/review` skill definitions from a shared narrow-deployment template; retire `/frontend`, `/typecheck`, `/backend`, `/int`, `/platform` skill files (move their distinct content per M9b/M9c, then delete the files). All five retired skills collapse into `/dev`, narrow-deployed across the 6 crate-shaped surfaces. | `/arch` + user | 1 day |
| M2 | Create initial `design/{crate}/{crate}.md` overview docs for each crate (frontend, typecheck, backend, runtime, platform, int). Seed from 2026-04-23 audits (`audits/*.md`) AND from migrated content per M9b. | `/design` | 3–4 days |
| M3 | `/arch` audit — author / migrate cross-crate types + traits into `crates/cranelisp-types/`. Codify Decision log format. | `/arch` | 1–2 sprints |
| M4 | `cargo-public-api` setup — install, generate per-crate tracked API file, add CI gate | `/arch` + `/dev` (narrow to `src/`) | 0.5 day setup; ongoing review |
| M5 | `pub(crate)` downgrade pass — mechanical audit across all crates; downgrade items not legitimately cross-crate | `/arch` leads; `/dev` per crate | 1 sprint |
| M6 | Facade-module pattern — each crate refactored to expose public API through a single facade | `/dev` per crate | 1 sprint |
| M7 | FIXME migration — scan inline `FIXME(/skill)` comments across project; create `sprints/fixmes/NNNN-*.md` for each; remove inline. Establish numbering convention. | `/sprint` | 0.5–1 day |
| M8 | `CLAUDE.md` rework — root + per-directory files shrink to pointers; methodology content removed (lives in METHOD.md); domain knowledge retained per the three-way split (§14.1) | Each directory owner | 0.5 day per skill |
| M9a | **Skill-def boilerplate strip** — extract the duplicated content (release gate, git discipline, testing ownership, design-doc obligation pattern) from every skill def to METHOD or a shared skill-def appendix. | `/sprint` + each skill | 1 day total |
| M9b | **Skill-def "what" extraction** — extract domain-specific decisions / direction content from current dev skill defs (`/backend.md` Sketch Consultation, `/int.md` slash-command list + Pass-1/Pass-2 model, etc.) into the matching `design/{crate}/{crate}.md`. Feeds M2. | Each retiring skill | 0.5–1 day per crate |
| M9c | **Skill-def "code" extraction** — extract mechanical / API-surface / convention content (Cranelift v0.125 notes, parser gotchas like `-3` integer parsing) from current dev skill defs into the matching `crates/{crate}/CLAUDE.md` (or `src/CLAUDE.md` for the binary crate). Feeds M8. | Each retiring skill | 0.5 day per crate |
| M10 | Memory retirement — methodology-normative memories retire as their content migrates into METHOD + skill defs. Project-specific technical memories remain. | `/sprint` + user | 0.5 day |
| M11 | `sprints/reimplementation.md` — archive or repurpose (content is historical now) | `/sprint` | 0.25 day |
| M12 | METHOD.md → METHOD_PROPOSED.md rename (METHOD.md archived; METHOD_PROPOSED renamed to METHOD.md) | `/sprint` | 0.1 day |
| M13 | `cranelisp-runtime` ownership reassignment — confirm runtime is owned by `/dev` in backend mode (paired with `cranelisp-backend`), not by `/platform`. Update any `CLAUDE.md` / design / sprint doc that says otherwise. | `/sprint` + `/arch` | 0.5 day |

**Estimated total**: 4–6 sprints across skills, primarily mechanical work after M1–M3. Some items (M3, M5, M6) are significant and may split across multiple sprints. M9a–M9c are sequenced: M9a removes shared boilerplate first (clarifies what remains); M9b extracts decisions to design docs (feeds M2); M9c extracts conventions to CLAUDE.md (feeds M8).

<!-- FIXME(/sprint): migration ordering — M3 (types crate consolidation) likely blocks M5 + M6 because downgrading and refactoring facades depends on knowing what must cross crate boundaries. M9a should run before M9b/M9c to make the per-skill specialization visible before extraction. M2 depends on M9b for content seeding. Confirm full DAG with /arch before scheduling. -->

---

## 16. Appendix A: Extract for `/sprint` skill definition

**Intent**: The `.claude/commands/sprint.md` skill definition is the sprint-agent's view of "I am /sprint, here is my job." It extracts from METHOD_PROPOSED without restating the whole document.

**Included in extract**:

- §3.4 `/sprint` row of skill roles
- §4 Sprint archetype in full — the phase table (4.1), phase descriptions (4.2–4.8), mid-sprint adjustment (4.9)
- §6.1 FIXME file protocol (as `/sprint` applies it at wave gates)
- §6.2 Skill handoff (as `/sprint` collects "Next skills")
- §7 Deferral principles (as `/sprint` applies them in Phase 1 scoping and Phase 6 gap triage)
- §10.2 Sprint close requires user approval
- §13 Change control table, `/sprint` row

**Referenced but not extracted** (skill def links to METHOD_PROPOSED):

- §5 Boundary management — `/sprint` cites but does not enforce
- §6.3, §6.4 Usability / defects / reproduction — `/sprint` references; full detail stays in METHOD
- §8 Testing discipline — `/sprint` cites acceptance criteria
- §11, §12 Agent and implementation discipline — general rules, cited at agent-spawn time

**Sprint-agent specific content in the skill def** (not in METHOD):

- First steps when invoked (read ROADMAP, SPRINT.md, fixmes/)
- Tools/commands the sprint agent uses
- How to spawn subagents under other skill roles
- Templates for SPRINT.md sections

---

*End of SKELETON. Prose body, detail tables, and worked examples to be filled in after structural sign-off.*
