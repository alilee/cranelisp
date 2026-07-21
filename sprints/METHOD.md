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

14 skills.

| Skill | Category | Owns | Output |
|---|---|---|---|
| `/spec` | Authority (scribe) | `spec/` | Normative spec text, scribed — the **user** arbitrates semantics; `/spec` records and frames open questions as prose |
| `/arch` | Authority | `design/arch/`; `crates/cranelisp-types/`; public-API surfaces of every crate | Interface types, principles, Decisions, public-API approvals |
| `/qa` | Authority | `tests/plan/` (incl. `PLAN.md`, the normative spec → tests bridge) | Test strategy, risk assessment, coverage process & traceability audit, defect attribution & cross-crate triage briefs |
| `/testing` | Test production | Test sources under `tests/` (files, fixtures, helpers); `tests/CLAUDE.md` | Spec-traceable e2e tests authored to `/qa`'s plan; repro isolation & reduction; `// defect:` notation upkeep (`tests/CLAUDE.md` §"Defect-repro notation"; ledger retired S108) |
| `/audit` | Authority | `audits/` | Rolling whole-context assessments with recommendations (one bounded context per sprint; see §2.6) |
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

- **Authority** (`/spec`, `/arch`, `/qa`, `/audit`) — arbitrate correctness and quality. Together they link the spec → architecture → release candidate. `/spec` is a **scribe**: its arbiter is the user, never itself. `/audit` judges accumulated whole-context state, one bounded context per sprint (§2.6).
- **Per-crate triad** (`/design`, `/dev`, `/review`) — generic skills, narrow-deployed one crate per invocation. Same triad shape applied to whichever crate is in scope.
- **Test production** (`/testing`) — authors the e2e suite and repro reductions to `/qa`'s plan, sprint-wide rather than per-crate.
- **Coordination** (`/sprint`) — orchestrates the sprint archetype. Owns no code or design content; routes technical questions to the appropriate authority.
- **User-proxy** (`/stdlib`, `/examples`, `/docs`, `/repl`, `/port`) — exercise the language outside-in. Operate during the user-facing phase of each sprint.

### 1.3 Per-crate triad

Three skills (`/design`, `/dev`, `/review`), one definition each, each invocation focused on exactly one crate. Per-crate specialization lives in `design/{crate}/{crate}.md` (the design doc) and `crates/{crate}/CLAUDE.md` (or `src/CLAUDE.md`), not in the skill definitions.

The crate-shaped surfaces (7 crates; the two runtime crates form one backend-paired runtime surface):

- `cranelisp-frontend`
- `cranelisp-typecheck`
- `cranelisp-backend`
- `cranelisp-primitives` + `cranelisp-intrinsics` — the **backend-emitted runtime library** (S73 Decision-43 split of the former `cranelisp-runtime`). **Paired with backend, NOT `/int`**: `cranelisp-backend` depends on these crates and emits calls into them (BC §4a/§4b — "backend declares them as imports"; the dep graph confirms it). `/int` is only a *host-client* of the runtime (constructs `HostCtx`, drives `block_on_reactor`) — it does not own the runtime library, and the IO-runtime internals (reactor, `consume_io_tree`, RC) are not an `/int` concern. See FIXME 0486 for the boundary review + the design-doc relocation.
- `cranelisp-platform` (consumer of runtime, not owner)
- `src/` (binary crate — pipeline, REPL, CLI, session; **host-client** to the runtime, not its owner)

Cross-crate work splits into sequential per-crate triad invocations, coordinated by `/sprint`. Any required interface change goes through `/arch` (in the types crate) before per-crate work proceeds.

### 1.4 Three-way content split

Three kinds of skill-relevant content, three distinct homes. This is the rule that lets generic narrow-deployment skills carry per-crate weight.

| Content kind | Lives in | Example |
|---|---|---|
| **How to work** (process, agent procedures) | Skill definition (`.claude/commands/{skill}.md`) | "Confirm the crate in scope, read the design doc, then proceed." |
| **What to decide** (direction, codified design decisions) | Per-crate design doc (`design/{crate}/{crate}.md`) | "RC discipline: borrowed-vs-consumed-vs-unique tracking." |
| **How the code is** (data structures, invariants, conventions) | `CLAUDE.md` per directory | "Cranelift v0.125: `jump`/`brif` take `IntoIterator<Item = &'a BlockArg>`." |

When in doubt: process / "before doing X, do Y" → skill definition; decision / target shape → design doc; mechanical / API-surface / convention → `CLAUDE.md`.

### 1.5 Model allocation

Which model tier each skill runs on, per-dispatch escalation triggers, and the
`.claude/agents/` shim contract are **normative in `sprints/artefacts.md`**
(ratified 2026-07-11): the allocation table §II.3, escalation §II.4, shims
§II.2, and the `/audit` rolling cycle §I.7/§II.1. Any model-tier change
requires user sign-off. `/sprint` records non-default dispatches in the
`SPRINT.md` dispatch log and audits frontmatter against the table at close.

---

## 2. Sprint phases

Every sprint follows seven phases. `/sprint` orchestrates by issuing skill invocations and gating between them.

### 2.1 Phase table

| Phase | Name | Agent invocations | Outputs | Exit gate |
|---|---|---|---|---|
| 1 | Scope | `/sprint` | `SPRINT.md` DRAFT; disposition of the prior sprint's audit assessment (accepted recommendations → FIXMEs, declined → recorded; §2.6) | User approval of scope |
| 2 | Architecture review | `/arch` | Interface changes approved/deferred; scope adjustments | `/arch` sign-off on scope |
| 3 | Design | `/spec`, `/arch`, `/design` per crate touched, `/qa` | Updated spec / interface types / per-crate design docs / test plan reflecting sprint scope | `/arch` confirms public-API + interface set is complete; `/qa` has enough to draft failing tests; touched design docs current |
| 4 | Wave organization | `/sprint` | Wave breakdown in `SPRINT.md`; `SPRINT.md` ACTIVE | Waves written |
| 5 | Language phase | `/testing` first (sprint-wide: failing e2e tests to `/qa`'s plan). Then per crate, parallel: D/D/R cycle (`/design` refines → `/dev` implements → `/review`). Iterate within crate as needed. | Passing e2e tests; per crate: refined design, implementation, unit tests, change-set review findings, public-API diffs approved | `/sprint` (with user) takes the **authoritative judgment of what ships this sprint**. Subsequent phases take what is given. |
| 6a | User-facing assessment | `/repl`, `/port`, `/stdlib`, `/examples`, `/docs`, `/sprint`; `/audit` dispatched on the rotation context (§2.6) | Plan for user-facing artifacts against what shipped; gap FIXMEs filed in `design/arch/fixmes/`; audit assessment in `audits/` | Plan agreed; gap FIXMEs filed |
| 6b | User-facing action | `/repl`, `/port`, `/stdlib`, `/examples`, `/docs` | New sprint demo; exemplar update; stdlib / examples / docs updates; prior demos replayed green | All planned artifacts delivered; demos play green |
| 7 | Close | `/sprint` (with user) | Outcome report; archive; ROADMAP update; FIXMEs forward | User approval of close |

### 2.2 Phase notes

**Phase 1 — Scope.** `/sprint` scans open FIXMEs (`design/arch/fixmes/`) + prior-sprint archive for carries. Proposes the next increment.

**Phase 2 — Architecture review.** `/arch` reviews scope for technical coherence, interim-architecture risk, public-API impact. Updates `crates/cranelisp-types/` if new cross-crate interfaces are required.

**Phase 3 — Design.** Each invoked skill updates its own artifact to incorporate sprint scope. `/design` covers all 6 crate-shaped surfaces — the implementing skill (`/dev`) does not author design. `/qa` drafts a test plan from spec + design docs.

**Phase 4 — Wave organization.** `/sprint` organizes parallel work into waves (sets of skill invocations with no inter-dependencies).

**Phase 5 — Language phase.** **QA-first across the entire solution** — `/testing` authors the failing e2e tests upfront, sprint-wide, to the plan `/qa` produced in Phase 3 — then per-crate D/D/R cycle in parallel across crates. Phase 5 conclusion is **conscious and explicit**: `/sprint` and the user decide what ships. Defects are addressed in Phase 5 or deferred with explicit rationale; speculative refactoring deferred; emergent refactoring (the third instance of a duplicate, a function over budget) handled in-sprint.

**Test-coverage discipline within D/D/R (binding).** Every fix lands with a **unit test (mandatory)**, and the need for an **e2e test is assessed BEFORE the fix is written** — not after. The unit test pins the seam where the bug lived; the e2e (added when the bug is observable end-to-end or crosses `--run`/`--link`/REPL modes) proves the user-observable path. Write the failing test(s) first; the fix flips them green; test(s) and fix land in the **same change-set**. Deferring a fix's test to a follow-up FIXME (the "test owed" anti-pattern) is not permitted. This is the same-skill complement to §2.3's failing-not-ignored cross-skill rule. Source-touching `/dev`/`/testing` agents run **serially** (one at a time — shared working tree; see root `CLAUDE.md` §Testing); only read-only fan-outs parallelise.

**Implementation-strategy unit scenarios (binding, added S101).** The fix-level rule above guards *repairs*; this rule guards *features*. An implementation strategy (a staging/commit split, a retention pool, a cache layer, a batch-derivation pass, a generation counter) creates a scenario space **the spec knows nothing about** — so spec-derived tests, `/qa`'s included, structurally cannot cover it; only the implementer knows it exists. When `/dev` implements, it MUST derive unit scenarios from the strategy explicitly, per seam touched — where **the seam unit is the submodule** (the crate's internal module composition: `compiler/apply`, `heap`, `cache/linker`), not the crate as a whole:

- **Complexity cases** — each algorithmic path and state transition the strategy introduces;
- **Edge cases** — the boundaries the strategy creates: empty/full/exhaustion, collisions, and **every cell of any implied matrix** (displacement shapes, instantiation shapes), not only the cell the design document names;
- **Negative cases** — what the strategy must NOT do: wrong item absent, stale entry never served, forbidden transition rejected.

Scenarios are **expressed through the crate facade** wherever the seam is facade-reachable (internal-invariant tests are permitted, but the facade is the default — the tier then survives refactors and reads as a contract), and unit tiers are **organized by submodule × scenario class**: each strategy-bearing submodule carries its own test module (`foo/tests.rs` or `#[cfg(test)] mod tests` sibling to `foo.rs`), so coverage is attributable and auditable **per submodule** — `/qa` checks the matrix mechanically instead of reverse-engineering intent. A **monolithic crate-root `tests.rs`** is the named anti-pattern: it makes submodule-level coverage unattributable (S101 exhibit: backend's flat 5.9k-line `tests.rs` over 32.5k LOC of well-composed submodules — nobody can see which submodules are thin). The bounded contexts (crates) are settled; this rule governs composition and accounting *inside* them. `/review` verifies that new or changed seams carry all three classes; a strategy-bearing seam with only happy-path pins is an Important finding. (S101 evidence: 0479 — displacement matrix, only the design-named cell was pinned, review caught the complementary cell as a live UAF; 0483/0488 — instantiation matrix, single cells pinned, SIGBUS one step out; D1/D2 — regeneration/adoption strategies with zero unit scenarios.)

**Phase 6a — User-facing assessment.** User-proxy skills assess what was *actually* delivered (not what was scoped) and plan the user-facing work outside-in from spec + scope. Gaps file as FIXMEs to next sprint.

**Phase 6b — User-facing action.** Execute the 6a plan against what shipped. Demos test reachability of the spec'd capability through user surfaces.

**Phase 7 — Close.** `/sprint` authors outcome, archives `SPRINT.md`, updates ROADMAP. **User approves close explicitly** — `/sprint` does not close unilaterally. Checkpoint on adequacy of arch's architectural principles. **Close checklist asserts FIXME-vs-§Delivered consistency (added S115)**: every FIXME the Outcome records as resolved has its file deleted (or its table row updated), and no surviving FIXME file or close-table row contradicts a §Delivered line. (S110 counterexample: the close table carried 0590 "open" beside a §Delivered line recording its convergence — the seed of the S113/S114 zombie chain.)

### 2.3 FIXME flow within a sprint

- Filed at any time as files in `design/arch/fixmes/NNNN-name.md` (see §3.3).
- **Wave gate**: before `/sprint` advances to the next wave, scans for `target: /skill-in-wave` and `status: open`. Outstanding FIXMEs targeting a wave's skill block advancement.
- **Phase 6 → next sprint**: gap FIXMEs flow forward to the next sprint as scope input. Phase 6 does not reopen Phase 5.

### 2.4 Deferral principles

1. **Defects discovered in Phase 5 are addressed in Phase 5** — fix, defer with explicit rationale, or close Phase 5 short. Conscious and recorded. Phase 6 does not retroactively reopen.
2. **Speculative refactoring deferred; emergent refactoring mandatory in-sprint.** When the current work has made cleanup cheap (third duplicate, file over budget, `mirror` comment), extract in-sprint.
3. **Interim architecture avoided, not deferred** — if a feature would require throwaway infrastructure a later increment replaces, don't build it.

**2× escalation.** Items deferred once may be deferred again with rationale. Items deferred twice ship in the current sprint or require explicit user sign-off for a third deferral. Applies to FIXMEs, ignored tests, and `/review` findings.

### 2.5 Mid-sprint adjustment

If `/sprint` is invoked mid-sprint: report status; recommend continue / re-scope / close. Scope changes require user sign-off. `/sprint` never closes unilaterally.

### 2.6 Rolling whole-context audit

One bounded context is audited per sprint, in rotation (normative cycle:
`sprints/artefacts.md` §I.7/§II.1; role: `.claude/commands/audit.md`). The
`SPRINT.md` template carries a standing `Audit: {context}` field filled at
Phase 4 — the structural cue. The dispatch runs read-only in the Phase 6/7
window; the assessment lands in `audits/{context}-sNNN.md` with
recommendations (evidence, cost class, proposed owner). **Next sprint's
Phase 1 disposes each recommendation with the user**: accepted → `/sprint`
files the FIXME targeting the proposed owner; declined → recorded in the
assessment with rationale. `/audit` never files FIXMEs for its own
recommendations and never blocks the current sprint. At Phase 7, `/sprint`
checks the audit's calibration: recommendations that consistently die at
acceptance are a finding about `/audit`. Out-of-rotation pulls: escalation
trigger 6 (`artefacts.md` §II.4).

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
| Test plan + coverage process | `tests/plan/` (`PLAN.md` normative) | `/qa` | Spec → tests bridge; risk register; coverage verdicts |
| E2e tests | `tests/` (sources, fixtures, helpers) | `/testing` | Normative spec-conformance evidence, authored to `/qa`'s plan; repro tests carry `// defect:` tags |
| Whole-context audit assessments | `audits/{context}-sNNN.md` | `/audit` | Accumulated-state assessments + recommendations (§2.6) |
| Artefact structure & model allocation | `sprints/artefacts.md` | `/sprint` | Allocation table, escalation protocol, shim contract, audit cycle |
| Unit tests | `crates/{crate}/src/.../mod.rs` (`#[cfg(test)]`) | `/dev` | Per-crate invariants, written alongside implementation |
| Methodology | `sprints/METHOD.md` (this) | `/sprint` | How we deliver |
| Skill workflows | `.claude/commands/{skill}.md` | Skill owner | How an agent in that role works |
| Roadmap | `sprints/ROADMAP.md` | `/sprint` | Sprint-by-sprint progress |
| Current sprint plan | `sprints/SPRINT.md` | `/sprint` | Active sprint scope, waves, outcome |
| Sprint archive | `sprints/archive/sprint-{id}.md` | `/sprint` | Completed sprint records |
| FIXMEs | `design/arch/fixmes/NNNN-name.md` | Filing skill until resolved | Cross-skill change requests |

### 3.2 Reading order

For a new session on this project:

1. Root `CLAUDE.md` — project overview + pointers
2. The skill definition for the current role (`.claude/commands/{skill}.md`)
3. `sprints/SPRINT.md` for current work
4. `sprints/METHOD.md` (this) for the delivery method
5. `design/arch/` and `design/{crate}/` for current design context
6. Per-directory `CLAUDE.md` when entering a directory
7. `design/arch/fixmes/` for open requests targeting the current skill

### 3.3 FIXME file protocol

FIXMEs are files in `design/arch/fixmes/`, not inline comments. One file per issue. Avoids file-ownership ambiguity and multi-skill edit conflicts.

**Naming**: `design/arch/fixmes/NNNN-short-name.md`. NNNN is unique sequential. Filing skill scans for `max + 1`. `/sprint` resolves rare collisions at wave gate.

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

**Only the owning skill deletes.** `/sprint` orchestrates and gates on FIXMEs but does not delete them. Filing is the one exception to file ownership — any skill may file a FIXME targeting any other skill. (Narrow exception, S115: `/sprint` may delete a FIXME as a Phase-1 audit-disposal action when an `/audit` assessment has verified it resolved against source and the user has approved the disposal — the audit evidence + approval record substitute for the owning skill's resolution.)

**Verify-against-source first (binding, added S115).** Any disposition of a FIXME — resolve, defer, re-target, carry into scope, or a scheduling decision built on it — verifies the FIXME's central claim against its `refers_to` source as its **first act**, and the disposition note records what was opened. A record asserting something about source that a single file-open would refute must not propagate. (S114 exhibit: zombie 0590 — resolved S110, falsely re-dispositioned S113 with "convergence has not happened", then consumed /sprint scheduling, /arch sequencing, /design deferral prose, a /testing probe, and an S115 scope slot across a five-agent chain in which nobody opened the `refers_to` file.)

### 3.4 Skill handoff

Every skill plan ends with a **Next skills** section recommending invocation order, consulting `SPRINT.md` for the active sprint or `sprints/ROADMAP.md` otherwise.

### 3.5 Memory and signals

`memory/` holds point-in-time observations and user feedback. Non-normative — METHOD.md is the normative source for delivery method; skill definitions are normative for skill workflows; design docs are normative for crate direction. Memories are signals that may inform the next sprint or the next iteration of a skill definition, but they do not override the canonical sources.

When a memory's content becomes durable, it migrates into the appropriate canonical doc (METHOD, skill def, design doc, or `CLAUDE.md`) and the memory file is retired.

---

## Cross-references

- Architectural rules and principles — `design/arch/`
- Per-crate design intent — `design/{crate}/{crate}.md`
- Skill workflow detail — `.claude/commands/{skill}.md`
- Active sprint — `sprints/SPRINT.md`
- Open FIXMEs — `design/arch/fixmes/`
- Predecessor (consolidated current state, retained for reference) — `sprints/METHOD_OLD.md`
- Working draft with deeper prose, migration plan, and worked rationale — `sprints/METHOD_PROPOSED.md`
