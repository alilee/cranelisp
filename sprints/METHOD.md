# Cranelisp Delivery Method

> **Owner**: `sprint`.
> **Scope**: what cranelisp adds to the shared role package — the crate-shaped surfaces, the seven-phase increment, and the artifacts each role keeps here.
> **Out of scope**: role authority, boundaries and handoffs (`.agents/skills/{role}/SKILL.md`); the role declaration, phase mapping, model allocation and filing protocol (root `CLAUDE.md`); architectural rules (`design/arch/`); per-crate design (`design/{crate}/`). This document points to these rather than restating them.

---

## 1. Roles here

Root `CLAUDE.md` §Roles is the declaration — which of the package's twelve roles cranelisp dispatches, what each owns here, and the model allocation. This section carries what that declaration is too compact to hold.

### 1.1 The crate-shaped surfaces

`design`, `dev` and `review` are narrow-deployed to exactly one surface per invocation:

- `cranelisp-frontend`
- `cranelisp-typecheck`
- `cranelisp-backend`
- `cranelisp-primitives` + `cranelisp-intrinsics` — the **backend-emitted runtime library** (S73 Decision-43 split of the former `cranelisp-runtime`). **Paired with backend, not with the binary**: `cranelisp-backend` depends on these crates and emits calls into them. The binary is only a *host-client* of the runtime (constructs `HostCtx`, drives `block_on_reactor`); the IO-runtime internals (reactor, `consume_io_tree`, RC) are not its concern.
- `cranelisp-platform` — consumer of the runtime, not its owner
- `src/` — binary crate (pipeline, REPL, CLI, session), plus `crates/cranelisp-exe-bundle/`

The language-facing surfaces — `stdlib/`, `examples/`, `exemplar/`, `user/`, `repl/` — are worked by `dev`, `training`, `docs`, `spec` and `test` per the root declaration, and take the full role set like any other surface.

Cross-surface work is sequential invocations coordinated by `sprint`. Any interface change goes through `arch`, in the types crate, before per-surface work proceeds.

**The architectural principles are the standard these surfaces are built and reviewed against.** `design/arch/principles.md` is the canonical index, one file per principle beneath it, owned by `arch` and revised only at close. `design`, `dev` and `review` read it and cite by name when a structural choice is governed by one. Until the 2026-08-30 wiring change these were injected into every triad dispatch by an `@` import block in the retired command files; that mechanism is gone, and reaching them is now the role's own first-read obligation. Principles 5 (testability is structural), 6 (complexity has a budget), 8 (no interim implementations) and 12 (design for the full spec surface) recur most often.

### 1.2 Where content lives

Three kinds of content, three homes. This is the rule that lets a generic narrow-deployed role carry per-crate weight.

| Content kind | Lives in | Example |
|---|---|---|
| **How to work** — process, role procedure | `.agents/skills/{role}/SKILL.md` — the shared package, changed only through its contribution cadence | "Confirm the surface in scope, read its design, then proceed." |
| **What to decide** — direction, codified design decisions | `design/{crate}/{crate}.md` | "RC discipline: borrowed-vs-consumed-vs-unique tracking." |
| **How the code is** — data structures, invariants, conventions | `CLAUDE.md` per directory | "Cranelift v0.125: `jump`/`brif` take `IntoIterator<Item = &'a BlockArg>`." |

In doubt: process → the package contract; decision or target shape → design doc; mechanical, API-surface or convention → `CLAUDE.md`.

**What a localized `CLAUDE.md` holds.** Written local memory is what keeps a narrow-deployed `dev` from re-deriving invariants out of source, so every workhorse-deployed surface earns one.

- **In**: API gotchas; data-structure invariants with their provenance; the submodule seam map and where each `#[cfg(test)]` module lives (this is what makes the per-submodule scenario accounting in §2.2 auditable); build and debug hooks; known asymmetries a reader would otherwise misread as bugs.
- **Out**: direction and target shape (→ `design/{crate}/`), boundary narrative (→ `design/arch/`), public surface (→ crate-root rustdoc), process (→ the role contract).
- **Budget**: about 150 lines. Past that it is accreting design content, and `review` flags it.
- **Owner**: `dev` narrow per crate, except `crates/cranelisp-types/` → `arch`, which owns that crate's source and so owns the voice of its code.
- **Current-state, not changelog**: at most one "current state" section, consolidated at close. Stacked sprint-stamped sections are the named decay smell.

### 1.3 Where cranelisp overrides the package

**`arch` is a deputy, not an originator of substance.** The package's `arch` contract makes decomposition, facades and technology selections its own to decide and proceed on. **Cranelisp overrides that**: the user is the architect at the language-shape level, and `arch` drafts, ratifies and applies substance the user has approved rather than inventing it.

So before `sprint` files anything *proposing* an architectural decision, or dispatches `arch` to author or amend one, the substance plus rationale plus rejected alternatives go to the user and `sprint` waits for an explicit OK. This binds for formal register decisions and for informal choices that meaningfully affect language shape, compiler structure or boundary contracts. It does **not** bind implementation detail falling out of an approved decision, propagation of approved substance, per-crate slice authorship, or a filing proposing no architectural change. Once the user has approved substance in conversation, proceed without re-asking — but the downstream text or dispatch prompt must match what was reviewed.

The override exists because several S66 decisions landed via `arch` answering `sprint`-filed requests without the substance being endorsed first, and had to be corrected retroactively: Decision 44 amended twice mid-sprint, Decision 45 reversed after a `dev` attempt exposed a lookup-cost mismatch with the user's own principle. Each correction cost an `arch` round and sometimes a `dev` re-run.

---

## 2. The increment

Seven phases. Root `CLAUDE.md` §Delivery maps them onto the ordering the package requires.

### 2.1 Phase table

| Phase | Name | Roles | Outputs | Exit gate |
|---|---|---|---|---|
| 1 | Scope | `sprint` | `SPRINT.md` DRAFT; disposition of the prior sprint's audit assessment | User approval of scope |
| 2 | Architecture review | `arch` | Interface changes approved or deferred; scope adjustments | `arch` sign-off on scope |
| 3 | Design | `spec`, `arch`, `design` per surface, `qa` | Updated spec, interface types, per-surface design, evidence plan | `arch` confirms the interface set is complete; `qa` has enough to allocate; touched design docs current |
| 4 | Wave organization | `sprint` | Wave breakdown; `SPRINT.md` ACTIVE | Waves written |
| 5 | Language phase | `test` first, sprint-wide; then per surface `design` → `dev` → `review` | Passing evidence; refined design, implementation, module tests, review findings, approved public-API diffs | `sprint` with the user takes the authoritative judgment of what ships |
| 6a | User-facing assessment | `docs`, `training`, `dev` on `stdlib/`/`exemplar/`, `spec` on `repl/`, `sprint`; `audit` on the rotation context | Plan for the language-facing surfaces against what shipped; gap filings | Plan agreed |
| 6b | User-facing action | as 6a | New sprint demo; exemplar, stdlib, examples and docs updates; prior demos replayed green | All planned artifacts delivered; demos play green |
| 7 | Close | `sprint` with the user | Outcome report; archive; ROADMAP update; filings forward | User approval of close |

Phases 6a/6b schedule the language-facing work. The standing-quality question each of those roles owes — re-asked against the whole artifact rather than the delta — lives in their contracts, not here.

### 2.2 Phase notes

**Scope a drawdown sprint from a test run, not from prose (S77).** For a get-to-green or defect-drawdown increment, Phase 1 scope is built from an actual `cargo nextest run --no-fail-fast`, collapsed to root causes and classified (code defect / fixture defect / gated) — never from the prior sprint's close notes or ROADMAP prose. Close notes summarise *intent*; named carries drift from the live failing set. S77's prose-built scope covered 13 of the 38 real failures. Two calibrations from the same episode: the 38 collapsed to about 10 roots, so N failing tests never means N fixes; and several "defects" were test-design defects, so check the test against the spec before assuming the code is wrong.

**A ruling is scheduled when it is recorded, not merely routed.** `sprint` writes the implementing wave into `SPRINT.md` at the moment it writes the ruling into the notes. A ruling with no scheduled slot is an open item, not a settled one — S115 lost four waves to a widened trait-method rule that was scribed, routed, and never scheduled. The close checklist asserts it: every ruling recorded this sprint has either landed its implementation or carries an explicit, owned deferral.

**As-built narrower than designed is recorded in the design doc.** A change-set that knowingly implements less than its design states says so *in the design*, dated — "as-built narrower than designed, because …, widens when …" — not only in a code comment or commit message. Where the design doc is another role's, the deviation rides a filing. A design doc is read when the next change is planned; a code comment is read only by whoever is already in that file. (Whether the narrowing should have been caught is `qa`'s: evidence that passes a non-conforming build is a coverage defect, per its contract.)

**Implementation-strategy scenarios are the implementer's to derive.** A staging split, retention pool, cache layer, batch pass or generation counter creates a scenario space the spec knows nothing about, so spec-derived evidence structurally cannot cover it. `dev` derives those scenarios per seam touched, where **the seam unit is the submodule** — `compiler/apply`, `heap`, `cache/linker` — not the crate. Organize unit tiers by submodule × scenario class, each strategy-bearing submodule carrying its own test module, so coverage is attributable per submodule. A **monolithic crate-root `tests.rs` is the named anti-pattern**: backend's flat 5.9k-line `tests.rs` over 32.5k LOC of well-composed submodules made thin submodules invisible (S101).

**A spec change clears its coverage annotations (user-directed, S115).** The traceability band asserts that a named test validates the requirement *as written*. When the requirement changes, that assertion silently becomes a claim about prose that no longer exists, and nothing notices because the citation is still live — the named test still exists; only its subject moved. So: the role changing a normative statement **clears that row's annotation in the same edit**. Clearing is an invalidation, not a coverage judgment, which is what keeps it inside the ownership rule — `spec` may clear; **only `qa` may restore**. Clearing makes the row report as uncovered, which `tests/plan/spec_coverage_reconcile.py` already detects. `test` then walks the `// spec:` backlinks, decides for each covering test whether it still validates the new prose, and adds cells for what is now uncovered including the negative direction. No row may be cleared-and-unrestored at close without an explicit recorded carry.

**Probe hygiene: the repo root is not a clean room (S115).** Module resolution is cwd-relative, so the obvious place to run a two-line `.cl` probe is the repo root — which is also where the REPL writes its session-persistence file (`user.cl`, git-ignored) and its history. A REPL probe there mutates state the next probe inherits; S115 lost a diagnosis to a `deftype` failing with "expected symbol" that was session pollution, not a defect. The rule is one line of setup:

```
cd <own scratch dir> && CRANELISP_LIB=<repo>/stdlib <repo>/target/debug/cranelisp --run probe.cl
```

- **Never write to the repo root** — not `user.cl`, not `.cranelisp_history`, not a stray `probe.cl`. Git-ignored is not harmless; these files are *inputs*.
- **A dispatch names the agent's scratch directory**, and agents do not share one.
- **Do not copy the repo to get an isolated build.** Source-touching work is serial, so revert-in-place is available and cheaper.
- **Clean up, or say you did not.**

### 2.3 Gates that are cranelisp's own

**The `dev` release gate.** Before reporting a change complete, all four hold zero-warning for the surface in scope — warnings, not just errors, because dead code introduced by a change (unused imports after a removed parameter, an unused function after its caller went) is how the next agent's signal degrades:

1. `cargo check -p <crate>`
2. `cargo check --tests -p <crate>` — test code counts
3. `cargo nextest run -p <crate>` — no `--no-fail-fast` here; build confidence by running clean
4. `cargo clippy -p <crate> --all-targets` — zero new lints

For the binary surface the package is `cranelisp`; verify `cranelisp-exe-bundle` too when the change touched it. The completion report states before/after warning counts and confirms each gate. This is `dev`'s own responsibility — `review` checks against design intent, not build cleanliness — and handing off with a broken build, a failing test, or new warnings is not a handoff.

**`review` is executed by an external reviewer.** The role runs on Codex for cross-model independence — the reviewer must not share the implementer's blind spots — and the invoked agent acts as **adjudicator**, not reviewer. Compose the brief (scope, plan-of-record paths, the wave's gate criteria, and **test evidence gathered by the adjudicator**, since the reviewer is sandboxed read-only and cannot run cargo); dispatch `scripts/codex-review.sh (--uncommitted | --commit SHA | --base BRANCH) --brief <file> --out <verdict.json>`; then adjudicate. **Every returned finding is a claim, not a fact**: verify it against the code before accepting, file the survivors, and record the verdict plus the reviewer's identity in the dispatch log. Severity may be reclassified with recorded rationale; a blocking finding may never be silently dropped. If the CLI is unavailable, perform the review directly and record the fallback — the gate is never skipped.

### 2.4 Deferral

1. **Defects discovered in Phase 5 are addressed in Phase 5** — fix, defer with explicit rationale, or close Phase 5 short. Conscious and recorded. Phase 6 does not retroactively reopen it.
2. **Speculative refactoring deferred; emergent refactoring mandatory in-sprint.** When the current work has made cleanup cheap — third duplicate, file over budget, a `mirror` comment — extract in-sprint.
3. **Interim architecture is avoided, not deferred.** If a feature would require throwaway infrastructure a later increment replaces, do not build it.
4. **The backlog is drained, not parked (user, S91).** Phase 1 pulls in every open filing unless there is a genuine reason to defer. Genuine reasons: explicitly release-tier work; a hard dependency on a not-yet-started track; a trigger whose condition is unmet. "Scheduled elsewhere in the roadmap" is not one. Present the deferral list with a reason per item so the user can challenge it.
5. **2× escalation.** Items deferred once may be deferred again with rationale. Items deferred twice ship in the current sprint or require explicit user sign-off for a third deferral. Applies to filings, ignored tests, and review findings.

Size is not among these: the package's `sprint` contract already rules that decomposition comes before any carry, and that a carry needs evidence of unreachability rather than a judgment that the target is far.

### 2.5 Mid-sprint adjustment

If `sprint` is invoked mid-sprint: report status; recommend continue, re-scope or close. Scope changes require user sign-off. `sprint` never closes unilaterally.

### 2.6 Escalation

**Decider**: `sprint`, unilaterally within its orchestration remit. User sign-off only where the method already requires it (a third deferral per §2.4.5; scope changes) — and **all language-normative questions go to the user**, never to a model tier. **Routing beats upgrading**: before raising a dispatch's tier, ask whether the judgment belongs to a role already on the frontier tier, and route it there instead of heating up a production role.

Triggers, normative:

1. **Recurring failure by symptom.** The same symptom — test name, error signature, crash site — still failing after **two** dispatches at default model makes the third a `qa` **attribution** dispatch: minimal repro plus owner under the control discipline, not a fix. The frame shifts from "fix it" to "attribute it".
2. **Contested or layered attribution.** The discovering role and the symptom's apparent owner disagree, or a fix exposed a second failure → `qa` triage before any further `dev` dispatch.
3. **Second deferral.** An item at its 2× point (§2.4.5): the resolving dispatch that sprint runs at the frontier tier, or a frontier `qa`/`arch` triage explains structurally why it keeps deferring.
4. **Review-resistant blockers.** A blocking finding surviving one `dev` fix round → `sprint` chooses: escalated `dev` (genuinely hard to build) or attribution-first (possibly wrongly attributed).
5. **Design-authority contact.** Work touching a principle, facade or bounded context never escalates in place — it files to `arch`. Spec ambiguity routes to `spec`, which frames it for the user.
6. **Out-of-rotation audit.** Triggers 1–4 firing repeatedly in one bounded context, or a major arc completing there, pull that context forward in the audit rotation (§2.7). Attribution fixes the instance; the audit assesses the pattern behind repeated instances.

**Recording**: the dispatch log in `SPRINT.md`, per wave — `| role | surface | model | effort | non-default reason |`. Default rows may be batched; every non-default row cites its trigger number. Phase 7 reviews the log — did escalations correlate with the sprint's hard spots? — and that is the feedback loop for revising the allocation in root `CLAUDE.md` §Roles.

**Dispatch by role agent, never by prose.** "Read the contract and act as X" inside a generic agent bypasses the frontmatter and silently inherits the session model. Model-tier changes need user sign-off; they are a spend decision, the same class as a scope change.

### 2.7 Rolling whole-context audit

One bounded context is audited per sprint, in rotation, so every context gets a fresh assessment on a bounded period and no sprint pays for more than one frontier-tier deep read. The `SPRINT.md` template carries a standing `Audit: {context}` field filled at Phase 4 — the cue is structural, because an audit that depends on someone remembering it decays like everything else.

**The acid test** (user-ratified 2026-07-11), against which the assessment opens with a graded per-attribute verdict: *if we lost this context's code and docs but retained the insight from experience, and produced a lean, high-quality solution second time around — would it look like this?* Evidence follows: design quality, design realisation (drift in both directions — unrealised design, and design the implementation has silently falsified), simplicity and volume optimality, duplication, risk-weighted coverage on the production path, maintainability, memory freshness. Hygiene findings are evidence within that frame, never a substitute for the verdict. The dispatch runs read-only in the Phase 6/7 window; the assessment lands in `audits/{context}-sNNN.md` with recommendations carrying evidence, cost class and proposed owner. **Next sprint's Phase 1 disposes each recommendation with the user**: accepted → `sprint` files against the proposed owner; declined → recorded in the assessment with rationale. `audit` never files for its own recommendations and never blocks the current sprint. At Phase 7, `sprint` checks the audit's calibration — recommendations that consistently die at acceptance are a finding about `audit` — and verifies both halves of the cycle: that this sprint's audit was dispatched, **and that the previous assessment was disposed**. A lapsed disposition is how four recommendations reached their fourth audit untouched (S110).

Assessments are point-in-time records: appended to with acceptance and decline outcomes, never rewritten. Rotation order is coordination state; reordering is a scope-class decision (trigger 6, or user direction).

---

## 3. Artifacts

### 3.1 Where things live

| Artifact | Path | Owner |
|---|---|---|
| Language spec | `spec/` | `spec` |
| REPL experience spec | `repl/spec.md` | `spec` |
| Architecture rules, principles, decisions | `design/arch/` | `arch` |
| Cross-crate types and traits | `crates/cranelisp-types/` | `arch` |
| Per-crate design | `design/{crate}/{crate}.md` and subordinates | `design` |
| Code conventions per directory | `CLAUDE.md` per directory | directory-owning role |
| Evidence plan and coverage process | `tests/plan/` (`PLAN.md` normative) | `qa` |
| E2e tests, fixtures, helpers | `tests/` | `test` |
| Unit tests | `crates/{crate}/src/**` under `#[cfg(test)]` | `dev` |
| Whole-context audit assessments | `audits/{context}-sNNN.md` | `audit` |
| Delivery method | `sprints/METHOD.md` (this) | `sprint` |
| Roadmap | `sprints/ROADMAP.md` | `sprint` |
| Current sprint plan | `sprints/SPRINT.md` | `sprint` |
| Sprint archive | `sprints/archive/sprint-{id}.md` | `sprint` |
| Actions | `sprints/actions/ACT-NNNN-name.md` | filing role until resolved |
| FIXMEs (rundown only) | `design/arch/fixmes/NNNN-name.md` | filing role until resolved |
| Role contracts | `.agents/skills/{role}/SKILL.md` | the shared package |

### 3.2 Reading order

1. Root `CLAUDE.md` — project overview, the role declaration, pointers
2. The role contract at `.agents/skills/{role}/SKILL.md`
3. `sprints/SPRINT.md` for current work
4. `sprints/METHOD.md` (this) for what cranelisp adds
5. `design/arch/` and `design/{crate}/` for design context
6. Per-directory `CLAUDE.md` on entering a directory
7. Open filings targeting the current role

### 3.3 Filing formats

Lifecycle and routing are in root `CLAUDE.md` §Cross-Role Changes. The forms:

**Action** — `sprints/actions/ACT-NNNN-short-name.md`, frontmatter then body:

```markdown
---
id: ACT-0042
title: <the request, as a sentence>
status: open        # open | deferred | resolved
priority: required  # blocking | required | advisory
from: dev
to: design
sprint: 120
filed_at: 2026-08-30
refers_to:
  - crates/cranelisp-typecheck/src/checker.rs
---

## Request
…

## Completion evidence
…
```

**FIXME** — the pre-existing form at `design/arch/fixmes/NNNN-short-name.md`, with `number`, `target`, `filed_by`, `filed_at`, `sprint_filed`, `refers_to`, `status`. No new ones are authored; the open set is run down in place.

Numbers are allocated above the highest used, never reused or backfilled. Only the owning role resolves and deletes; `sprint` gates but does not delete — the narrow exception is a Phase-1 audit disposal where an assessment has verified resolution against source and the user has approved it.

### 3.4 Memory

`memory/` holds point-in-time observations and user feedback. Non-normative: this document is normative for what cranelisp adds, role contracts for how a role works, design docs for crate direction. Memories are signals that may inform the next sprint or the next contract contribution; they do not override the canonical sources. When a memory's content becomes durable it migrates into the appropriate canonical document and the memory is retired.
