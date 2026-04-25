# Cranelisp Delivery Method

> **Owner**: `/sprint`.
> **Scope**: how we deliver — skills, sprint phases, artifacts and memory.
> **Out of scope**: architectural rules (`/arch` in `design/arch/`), per-crate implementation design (`/design` in `design/{crate}/`), agent-facing workflow detail (`.claude/commands/{skill}.md`). This document points to these rather than restating them.

---

## Table of contents

1. [Skills and roles](#1-skills-and-roles)
2. [Sprint phases](#2-sprint-phases)
3. [Artifacts and memory](#3-artifacts-and-memory)

---

## 1. Skills and roles

### 1.1 Inventory

12 skills.

| Skill | Category | Owns | Output |
|---|---|---|---|
| `/spec` | Authority | `spec/` | Normative spec text |
| `/arch` | Authority | `design/arch/`; `crates/cranelisp-types/`; public-API surfaces of every crate | Interface types, principles, Decisions, public-API approvals |
| `/qa` | Authority | `tests/`; `tests/plan/baseline.md` | Spec-traceable integration + e2e tests as the normative conformance evidence linking spec → release candidate |
| `/design` | Per-crate triad — design role | `design/{crate}/{crate}.md` for all 6 crate-shaped surfaces (narrow deployment) | Crate overview + subordinate topic docs; does not edit code |
| `/dev` | Per-crate triad — implementation role | All 6 crate-shaped surfaces (narrow deployment) — see §1.3 | Implementation code + unit tests |
| `/review` | Per-crate triad — review role | All 6 crate-shaped surfaces (narrow deployment); no persistent directory | Quality findings on a round of change against design intent + accumulated state |
| `/sprint` | Coordination | `sprints/` | Sprint plans, wave organization, FIXME orchestration, outcome reports |
| `/stdlib` | User-proxy | `stdlib/` | Standard library |
| `/examples` | User-proxy | `examples/` | Learning-sequence examples |
| `/docs` | User-proxy | `user/` | User-facing documentation |
| `/repl` | User-proxy | `repl/` | REPL experience spec, demos, harness |
| `/port` | User-proxy | `exemplar/` | Showcase project |

### 1.2 Categories

- **Authority** (`/spec`, `/arch`, `/qa`) — arbitrate correctness. Together they link the spec → architecture → release candidate.
- **Per-crate triad** (`/design`, `/dev`, `/review`) — generic skills, narrow-deployed one crate per invocation. Same triad shape applied to whichever crate is in scope.
- **Coordination** (`/sprint`) — orchestrates the sprint archetype. Owns no code or design content; routes technical questions to the appropriate authority.
- **User-proxy** (`/stdlib`, `/examples`, `/docs`, `/repl`, `/port`) — exercise the language outside-in. Operate during the user-facing phase of each sprint.

### 1.3 Per-crate triad

Three skills (`/design`, `/dev`, `/review`), one definition each, each invocation focused on exactly one crate. Per-crate specialization lives in `design/{crate}/{crate}.md` (the design doc) and `crates/{crate}/CLAUDE.md` (or `src/CLAUDE.md`), not in the skill definitions.

The 6 crate-shaped surfaces:

- `cranelisp-frontend`
- `cranelisp-typecheck`
- `cranelisp-backend`
- `cranelisp-runtime` (paired with backend)
- `cranelisp-platform` (consumer of runtime, not owner)
- `src/` (binary crate — pipeline, REPL, CLI)

Cross-crate work splits into sequential per-crate triad invocations, coordinated by `/sprint`. Any required interface change goes through `/arch` (in the types crate) before per-crate work proceeds.

### 1.4 Three-way content split

Three kinds of skill-relevant content, three distinct homes. This is the rule that lets generic narrow-deployment skills carry per-crate weight.

| Content kind | Lives in | Example |
|---|---|---|
| **How to work** (process, agent procedures) | Skill definition (`.claude/commands/{skill}.md`) | "Confirm the crate in scope, read the design doc, then proceed." |
| **What to decide** (direction, codified design decisions) | Per-crate design doc (`design/{crate}/{crate}.md`) | "RC discipline: borrowed-vs-consumed-vs-unique tracking." |
| **How the code is** (data structures, invariants, conventions) | `CLAUDE.md` per directory | "Cranelift v0.125: `jump`/`brif` take `IntoIterator<Item = &'a BlockArg>`." |

When in doubt: process / "before doing X, do Y" → skill definition; decision / target shape → design doc; mechanical / API-surface / convention → `CLAUDE.md`.

---

## 2. Sprint phases

Every sprint follows seven phases. `/sprint` orchestrates by issuing skill invocations and gating between them.

### 2.1 Phase table

| Phase | Name | Agent invocations | Outputs | Exit gate |
|---|---|---|---|---|
| 1 | Scope | `/sprint` | `SPRINT.md` DRAFT | User approval of scope |
| 2 | Architecture review | `/arch` | Interface changes approved/deferred; scope adjustments | `/arch` sign-off on scope |
| 3 | Design | `/spec`, `/arch`, `/design` per crate touched, `/qa` | Updated spec / interface types / per-crate design docs / test plan reflecting sprint scope | `/arch` confirms public-API + interface set is complete; `/qa` has enough to draft failing tests; touched design docs current |
| 4 | Wave organization | `/sprint` | Wave breakdown in `SPRINT.md`; `SPRINT.md` ACTIVE | Waves written |
| 5 | Language phase | `/qa` first (sprint-wide: failing integration + e2e tests). Then per crate, parallel: D/D/R cycle (`/design` refines → `/dev` implements → `/review`). Iterate within crate as needed. | Passing integration + e2e tests; per crate: refined design, implementation, unit tests, change-set review findings, public-API diffs approved | `/sprint` (with user) takes the **authoritative judgment of what ships this sprint**. Subsequent phases take what is given. |
| 6a | User-facing assessment | `/repl`, `/port`, `/stdlib`, `/examples`, `/docs`, `/sprint` | Plan for user-facing artifacts against what shipped; gap FIXMEs filed in `sprints/fixmes/` | Plan agreed; gap FIXMEs filed |
| 6b | User-facing action | `/repl`, `/port`, `/stdlib`, `/examples`, `/docs` | New sprint demo; exemplar update; stdlib / examples / docs updates; prior demos replayed green | All planned artifacts delivered; demos play green |
| 7 | Close | `/sprint` (with user) | Outcome report; archive; ROADMAP update; FIXMEs forward | User approval of close |

### 2.2 Phase notes

**Phase 1 — Scope.** `/sprint` scans open FIXMEs (`sprints/fixmes/`) + prior-sprint archive for carries. Proposes the next increment.

**Phase 2 — Architecture review.** `/arch` reviews scope for technical coherence, interim-architecture risk, public-API impact. Updates `crates/cranelisp-types/` if new cross-crate interfaces are required.

**Phase 3 — Design.** Each invoked skill updates its own artifact to incorporate sprint scope. `/design` covers all 6 crate-shaped surfaces — the implementing skill (`/dev`) does not author design. `/qa` drafts a test plan from spec + design docs.

**Phase 4 — Wave organization.** `/sprint` organizes parallel work into waves (sets of skill invocations with no inter-dependencies).

**Phase 5 — Language phase.** **QA-first across the entire solution** (failing integration + e2e tests upfront, sprint-wide), then per-crate D/D/R cycle in parallel across crates. Phase 5 conclusion is **conscious and explicit**: `/sprint` and the user decide what ships. Defects are addressed in Phase 5 or deferred with explicit rationale; speculative refactoring deferred; emergent refactoring (the third instance of a duplicate, a function over budget) handled in-sprint.

**Phase 6a — User-facing assessment.** User-proxy skills assess what was *actually* delivered (not what was scoped) and plan the user-facing work outside-in from spec + scope. Gaps file as FIXMEs to next sprint.

**Phase 6b — User-facing action.** Execute the 6a plan against what shipped. Demos test reachability of the spec'd capability through user surfaces.

**Phase 7 — Close.** `/sprint` authors outcome, archives `SPRINT.md`, updates ROADMAP. **User approves close explicitly** — `/sprint` does not close unilaterally.

### 2.3 FIXME flow within a sprint

- Filed at any time as files in `sprints/fixmes/NNNN-name.md` (see §3.3).
- **Wave gate**: before `/sprint` advances to the next wave, scans for `target: /skill-in-wave` and `status: open`. Outstanding FIXMEs targeting a wave's skill block advancement.
- **Phase 6 → next sprint**: gap FIXMEs flow forward to the next sprint as scope input. Phase 6 does not reopen Phase 5.

### 2.4 Deferral principles

1. **Defects discovered in Phase 5 are addressed in Phase 5** — fix, defer with explicit rationale, or close Phase 5 short. Conscious and recorded. Phase 6 does not retroactively reopen.
2. **Speculative refactoring deferred; emergent refactoring mandatory in-sprint.** When the current work has made cleanup cheap (third duplicate, file over budget, `mirror` comment), extract in-sprint.
3. **Interim architecture avoided, not deferred** — if a feature would require throwaway infrastructure a later increment replaces, don't build it.

**2× escalation.** Items deferred once may be deferred again with rationale. Items deferred twice ship in the current sprint or require explicit user sign-off for a third deferral. Applies to FIXMEs, ignored tests, and `/review` findings.

### 2.5 Mid-sprint adjustment

If `/sprint` is invoked mid-sprint: report status; recommend continue / re-scope / close. Scope changes require user sign-off. `/sprint` never closes unilaterally.

---

## 3. Artifacts and memory

### 3.1 Where things live

| Artifact | Path | Owner | Purpose |
|---|---|---|---|
| Language spec | `spec/` | `/spec` | What the language does |
| Architecture rules and principles | `design/arch/` | `/arch` | Cross-crate decisions, principles, Decisions log |
| Cross-crate types and traits | `crates/cranelisp-types/` | `/arch` | Single home for types and traits crossing crate boundaries |
| Per-crate design | `design/{crate}/{crate}.md` (+ subordinates) | `/design` | What the crate should be — direction, intent, codified design decisions |
| Code conventions per directory | `CLAUDE.md` per directory | Directory-owning skill | How the code is — data structures, invariants, conventions |
| Integration + e2e tests | `tests/`, `tests/plan/baseline.md` | `/qa` | Normative spec-conformance evidence |
| Unit tests | `crates/{crate}/src/.../mod.rs` (`#[cfg(test)]`) | `/dev` | Per-crate invariants, written alongside implementation |
| Methodology | `sprints/METHOD.md` (this) | `/sprint` | How we deliver |
| Skill workflows | `.claude/commands/{skill}.md` | Skill owner | How an agent in that role works |
| Roadmap | `sprints/ROADMAP.md` | `/sprint` | Sprint-by-sprint progress |
| Current sprint plan | `sprints/SPRINT.md` | `/sprint` | Active sprint scope, waves, outcome |
| Sprint archive | `sprints/archive/sprint-{id}.md` | `/sprint` | Completed sprint records |
| FIXMEs | `sprints/fixmes/NNNN-name.md` | Filing skill until resolved | Cross-skill change requests |

### 3.2 Reading order

For a new session on this project:

1. Root `CLAUDE.md` — project overview + pointers
2. The skill definition for the current role (`.claude/commands/{skill}.md`)
3. `sprints/SPRINT.md` for current work
4. `sprints/METHOD.md` (this) for the delivery method
5. `design/arch/` and `design/{crate}/` for current design context
6. Per-directory `CLAUDE.md` when entering a directory
7. `sprints/fixmes/` for open requests targeting the current skill

### 3.3 FIXME file protocol

FIXMEs are files in `sprints/fixmes/`, not inline comments. One file per issue. Avoids file-ownership ambiguity and multi-skill edit conflicts.

**Naming**: `sprints/fixmes/NNNN-short-name.md`. NNNN is unique sequential. Filing skill scans for `max + 1`. `/sprint` resolves rare collisions at wave gate.

**Format**: frontmatter + body.

```markdown
---
number: 0042
target: /design
filed_by: /dev
filed_at: 2026-04-24
sprint_filed: 62
refers_to: crates/cranelisp-typecheck/src/checker.rs
status: open  # open | deferred
---

# Short description

## Issue
…

## Proposed resolution
…
```

**Lifecycle**:

1. Filing skill creates the file, commits.
2. Owning skill (`target`) sees the file at next wave gate or sprint Phase 1 scan.
3. Owning skill resolves — incorporates the change into its owned files — then **deletes** the FIXME file with a commit message naming what was resolved. Git history is the audit trail.
4. If deferred, owning skill sets `status: deferred` and adds rationale + target sprint; the file remains.

**Only the owning skill deletes.** `/sprint` orchestrates and gates on FIXMEs but does not delete them. Filing is the one exception to file ownership — any skill may file a FIXME targeting any other skill.

### 3.4 Skill handoff

Every skill plan ends with a **Next skills** section recommending invocation order, consulting `SPRINT.md` for the active sprint or `design/arch/roadmap.md` otherwise.

### 3.5 Memory and signals

`memory/` holds point-in-time observations and user feedback. Non-normative — METHOD.md is the normative source for delivery method; skill definitions are normative for skill workflows; design docs are normative for crate direction. Memories are signals that may inform the next sprint or the next iteration of a skill definition, but they do not override the canonical sources.

When a memory's content becomes durable, it migrates into the appropriate canonical doc (METHOD, skill def, design doc, or `CLAUDE.md`) and the memory file is retired.

---

## Cross-references

- Architectural rules and principles — `design/arch/`
- Per-crate design intent — `design/{crate}/{crate}.md`
- Skill workflow detail — `.claude/commands/{skill}.md`
- Active sprint — `sprints/SPRINT.md`
- Open FIXMEs — `sprints/fixmes/`
- Predecessor (consolidated current state, retained for reference) — `sprints/METHOD_OLD.md`
- Working draft with deeper prose, migration plan, and worked rationale — `sprints/METHOD_PROPOSED.md`
