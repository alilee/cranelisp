# Agent Artefact Structure & Model Allocation

> **Owner**: `/sprint`.
> **Status**: PROPOSAL — pending user ratification (drafted 2026-07-11, pre-S108).
> **Normative once ratified for**: the allocation table (§II.3), the escalation
> protocol (§II.4), and the `.claude/agents/` shim contract (§II.2).
> `sprints/METHOD.md` §1 gains a §1.5 pointer to this document at adoption
> (migration increment A, §II.7).
> **Scope**: how agent roles are defined, dispatched, and assigned to models.
> Part I is a project-agnostic blueprint, liftable verbatim into another
> project of the same shape. Part II instantiates it for this repository.

---

## Part I — Blueprint (project-agnostic)

### I.1 Shape assumptions

This blueprint applies to a project shaped like:

- **Main binary(ies)** plus **bounded-context library crates** (or modules),
  each with a deliberate public facade;
- **Facade discipline** — cross-context types and traits live in one shared
  home; per-context internals are private;
- **File-based change control** — cross-role change requests are numbered
  files with an owner, resolved and deleted by the owner, gated by a
  coordinator; git history is the audit trail;
- **A delivery method** — phased iterations with explicit gates, orchestrated
  by a single coordination role.

### I.2 Role taxonomy

Four role categories. Every role is exactly one of these:

| Category | Arbitrates / produces | Examples |
|---|---|---|
| **Authority** | Correctness judgments other roles must act on: architecture rulings, test strategy, conformance verdicts | architect, QA strategist |
| **Production triad** | Design–implement–review for one bounded context per invocation; generic definitions, narrow-deployed | designer, developer, reviewer |
| **Coordination** | Phases, waves, gates, dispatch; owns no product content | delivery coordinator |
| **User-proxy** | Exercise the product outside-in; file findings and defects | library author, docs author, example author |

Domains where a **human** is the arbiter (e.g. a language or product
specification whose semantics the project owner decides) get a **scribe**
role, not an authority role: the scribe records settled decisions faithfully
and brings every open normative question to the human framed as prose. A
scribe never rules.

### I.3 Artefact kinds and the command/shim split

Five artefact kinds, each with one owner and one home:

1. **Command definitions** (`.claude/commands/{role}.md`) — the canonical role
   content: identity, boundary, workflow, owned artifacts. One file per role,
   owned by that role, composed with shared procedural files via `@` imports.
   Role content lives here and ONLY here.
2. **Agent shims** (`.claude/agents/{role}.md`) — dispatch configuration only:
   frontmatter (`model:`, `effort:`, `description:`) plus a body of at most a
   few lines that instructs the agent to read the command definition (and
   everything under its `# Imports`) and adopt the role. Owned by the
   coordinator. **A shim containing role prose is a defect** — that is how
   drift starts.
3. **Localized memories** (`CLAUDE.md` per directory) — "how the code is":
   API gotchas, invariants with provenance, seam maps, debug hooks. Governed
   by the three-way content split: *process* → command definition;
   *decisions/direction* → design docs; *mechanics* → `CLAUDE.md`.
4. **Change-control files** — numbered request files; any role may file
   against any role; only the target resolves and deletes; the coordinator
   gates waves on open items but never deletes.
5. **Coordination state** — the method document, the active iteration plan
   (including the dispatch log, §I.6), and the archive.

**Why the split.** Model/effort pinning must be *structural*, not
*behavioral*. A table the coordinator "applies at each dispatch" depends on
an LLM faithfully copying configuration forever under context pressure; a
shim's frontmatter pins the model even when a dispatch prompt is terse.
Conversely, duplicating role prose into shims creates two homes for one
truth. Thin shims over canonical commands get both properties.

### I.4 Model tiering

Two tiers:

- **Frontier tier** (highest-capability model, premium cost) buys **gating
  judgment**: orchestration decisions, architecture rulings, test strategy
  and risk assessment, defect attribution, review verdicts — anything other
  dispatches consume as authority.
- **Workhorse tier** (long-context production model) buys **gated
  production**: code, tests, repro isolation, library and documentation
  volume — anything whose defects a downstream gate catches. Long context is
  the feature that matters here: the workhorse holds the spec, the design
  doc, the crate, and the test suite simultaneously instead of re-deriving.

**The tiering test**: *if this output is wrong, does a gate catch it, or does
it silently steer other agents?* Silently-steering work goes frontier;
gate-caught work goes workhorse.

**Splitting mixed roles.** When one role contains both kinds of work, split
it into **two skills** along the judgment/production seam — strategy on the
frontier tier, execution on the workhorse tier (see Part II §II.1: the QA
split is the worked example). Reserve shim-level mode splits (two shims over
one command file) for mode differences that do not cross the authority line.

**Scribes run on the workhorse tier.** Where the human is the gate (§I.2),
the model buys transcription fidelity, not judgment — production tier, with
every open question routed to the human.

### I.5 Escalation

1. **Routing beats upgrading.** Before raising a dispatch's model tier, ask
   whether the judgment belongs to an authority role that is already on the
   frontier tier — if so, route the question there (change-control file or
   dispatch), don't heat up the production role.
2. **Upgrades fire on mechanical triggers, not vibes** — symptom recurrence
   across dispatches, contested attribution, aging deferrals,
   review-resistant findings. Concrete triggers are instantiated per project
   (Part II §II.4).
3. **The coordinator decides**, unilaterally within its remit; the human
   signs off only where the method already requires it (scope changes, aged
   deferrals) — and always on questions the human arbitrates (§I.2).
4. **Every non-default dispatch is recorded** in a dispatch log (§I.6) and
   reviewed at iteration close: did escalations correlate with the hard
   spots? That review is the feedback loop that revises the allocation table.

### I.6 The dispatch contract and the dispatch log

All pinning, escalation, and logging flows through one choke point: the
coordinator's dispatch contract.

- Dispatch **by agent type** (the shim), never by "read the role file and act
  as X" prose inside a generic agent — the prose path bypasses frontmatter
  and silently inherits the session model.
- The per-dispatch `model` parameter is reserved for **explicit, recorded
  escalations and downgrades**.
- The **dispatch log** is a table in the active iteration plan, one row per
  agent dispatch (default-tier rows may be batched per wave):
  `| agent | surface | model | effort | non-default reason |`.
- **Drift control**: the allocation table is normative in exactly one place;
  shim and command frontmatter are its executable copies; the coordinator
  runs one mechanical audit at iteration close (grep the frontmatter against
  the table).

### I.7 Instantiation checklist for a new project

1. Enumerate roles; classify each into the taxonomy (§I.2); identify
   human-arbitrated domains and make those roles scribes.
2. Apply the tiering test to every role; split any role that straddles the
   judgment/production seam.
3. Write the allocation table (role × model × effort × rationale ×
   escalation trigger); get human sign-off — model allocation is a spend
   decision.
4. Author command definitions (role-owned) and shims (coordinator-owned).
5. Amend the coordinator's dispatch contract: agent-type dispatch, dispatch
   log, escalation triggers, close-time audit.
6. Fill localized-memory gaps for every bounded context the workhorse tier
   will be deployed into — written local memory is what keeps the workhorse
   from re-deriving invariants.
7. Schedule adoption as independent increments, each safe alone, each with a
   named fallback.

---

## Part II — Cranelisp instantiation

### II.1 Role inventory (target: 13 skills)

The 12 live skills of `METHOD.md` §1.1, with two changes:

- **`/qa` splits** into `/qa` and `/testing` along the judgment/production
  seam (user ruling, 2026-07-11: QA planning is underpowered on the
  workhorse tier):
  - **`/qa`** (Authority) — test strategy, risk assessment, coverage process
    & traceability audit, defect attribution & cross-crate triage. Owns
    `tests/plan/`.
  - **`/testing`** (production) — authors integration/e2e tests, repro
    isolation & reduction, ledger upkeep. Owns the test sources under
    `tests/`.
- **`/spec` is confirmed as a scribe** (per the standing user ruling that the
  user is sole arbiter of what the language IS): it records settled
  decisions, runs annotation sweeps and spec/impl reconciliation, and brings
  every open normative question to the user framed as prose. It never rules.
  Category stays Authority-adjacent in METHOD's table but its escalation path
  is the **user**, not a model tier.

The five retired command files (`backend.md`, `frontend.md`, `int.md`,
`platform.md`, `typecheck.md`) are **deleted** in increment A — git history
is the audit trail, and their continued presence is a live mis-invocation
hazard (the harness surfaces them as invocable skills).

### II.2 `.claude/` target tree

```
.claude/
├── commands/          13 canonical role definitions (role-owned)
│   arch.md  spec.md  qa.md  testing.md  design.md  dev.md  review.md
│   sprint.md  stdlib.md  examples.md  docs.md  repl.md  port.md
│   — each gains frontmatter: model + effort per §II.3 (interactive entry)
├── agents/            13 dispatch shims (coordinator-owned)
│   same names — frontmatter + pointer body only
└── settings.local.json
```

**Shim template** (the whole file — anything longer is drifting):

```markdown
---
name: dev
description: Per-crate implementer (triad). Dispatch narrow to one crate-shaped surface.
model: opus[1m]
effort: high
---
You are /dev. First action: Read `.claude/commands/dev.md` AND every file it
lists under `# Imports`, then adopt that role exactly. The dispatch prompt
names your crate in scope; if it does not, stop and ask.
```

Shims use a tool-driven Read of the command file rather than `@` imports
(unverified inside agent definitions — §II.8). Command frontmatter mirrors
the same model/effort values for interactive invocation.

### II.3 The allocation table (normative)

**Frontier tier = `fable`. Workhorse tier = `opus[1m]`** (Opus with 1M
context, same per-token rate as standard Opus). Any change to a Model cell
requires user sign-off (§II.6).

| Skill | Model | Effort | Rationale | Escalation / routing |
|---|---|---|---|---|
| `/sprint` | fable | high | Every dispatch, scope call, and gate judgment propagates into all other spend | n/a (top tier) |
| `/arch` | fable | xhigh | Highest-leverage judgment: principles, facades, public-API approvals, canonical-set consistency | Downgrade mechanical cascade sweeps (settled-ruling cross-ref fixups) to opus[1m] per-dispatch, recorded |
| `/qa` | fable | xhigh | Test strategy, risk assessment, coverage process; defect attribution — a wrong owner costs multiple misdirected dev dispatches (root `CLAUDE.md` §cross-skill handoff) | n/a (top tier) |
| `/review` | fable | high | Verdicts other roles must act on; misclassified severity silently ships defects; cheap insurance on every workhorse change-set | n/a — no downgrade |
| `/spec` | opus[1m] | high | Scribe: the user is the gate; the model buys transcription fidelity. All normative decisions go to the user, framed as prose | To the **user**, always — never to a model tier |
| `/testing` | opus[1m] | high | Volume test authoring + repro isolation; 1M context holds spec + suite + ledger | Attribution questions → `/qa`; triggers 1–2 (§II.4) |
| `/design` | opus[1m] | high | Per-crate translation of settled architecture; Phase-3 exit gate (`/arch` on fable) backstops | Principle/facade/BC contact → FIXME to `/arch` (routing beats upgrading); novel-subsystem design → fable per-dispatch |
| `/dev` | opus[1m] | high | Code + unit tests behind four gates (release gate, `/review`, test suite, `/arch` API approval); 1M earns its keep on backend/typecheck | Trigger 1 (§II.4): 2 failed fix dispatches → `/qa` attribution before a third |
| `/stdlib` | opus[1m] | high | Volume language-writing against a settled spec; defects route to `/qa` → `/testing` | Contested defect handoff → `/qa` |
| `/repl` | opus[1m] | high | Demos/harness are executable artifacts behind the replay-green gate | REPL-spec normative change → user (via `/spec` framing) |
| `/port` | opus[1m] | high | Exemplar is volume language-writing; findings flow back as FIXMEs/defects | Perf/architecture verdicts → `/arch`, not a hotter `/port` |
| `/examples` | opus[1m] | medium | Learning-sequence content; lowest blast radius | Ambiguity → `/spec` (frames for user) |
| `/docs` | opus[1m] | medium | Routine user docs from spec + shipped behavior | Ambiguity → `/spec` (frames for user) |

### II.4 Escalation protocol

**Decider**: `/sprint` (on fable), unilaterally within its orchestration
remit. User sign-off only where the method already requires it (3rd FIXME
deferral per METHOD §2.4; scope changes) — and **all language-normative
questions go to the user**, never to a model tier.

**Triggers** (normative):

1. **Recurring failure by symptom.** The same symptom (test name, error
   signature, crash site) still fails after **two** dispatches at default
   model → the third dispatch is a `/qa` (fable) **attribution**: minimal
   repro + owner, not a fix. The frame shifts from "fix it" to "attribute
   it" per root `CLAUDE.md` §cross-skill handoff.
2. **Contested or layered attribution.** The discovering skill and the
   symptom's apparent owner disagree, or a fix exposed a second failure →
   `/qa` triage before any further `/dev` dispatch.
3. **2× FIXME deferral.** An item at its 2× point (METHOD §2.4): the
   resolving dispatch that sprint runs at fable, or a fable `/qa`/`/arch`
   triage explains structurally why it keeps deferring.
4. **Review-resistant Blockers.** A `/review` Blocker surviving one `/dev`
   fix round → `/sprint` chooses: escalated `/dev` (hard to build) or
   `/qa`-attribution-first (possibly wrongly attributed).
5. **Design-authority contact.** Work touching a principle, facade, or
   bounded context never escalates in place — FIXME to `/arch`. Spec
   ambiguity routes to `/spec`, which frames it for the user.

**Recording**: the **Dispatch log** in `SPRINT.md`, per wave:
`| agent | surface | model | effort | non-default reason |`. Default rows may
be batched (e.g. "W3: dev×frontend, dev×typecheck — defaults"); every
non-default row cites its trigger number. Phase 7 reviews the log ("did
escalations correlate with the sprint's hard spots?") — the feedback loop for
revising §II.3.

### II.5 Localized CLAUDE.md target state

Fill the 7 crate-level gaps — every workhorse-deployed surface gets the
`crates/cranelisp-typecheck/CLAUDE.md` treatment: `cranelisp-frontend`,
`-backend`, `-primitives`, `-intrinsics`, `-platform`, `-types`,
`-exe-bundle`. Under narrow allocation, written local memory is what keeps an
opus[1m] `/dev` dispatch from re-deriving invariants from source.

- **In** (per the three-way split): API gotchas, data-structure invariants
  with provenance (sprint/FIXME numbers), submodule seam map + where each
  `#[cfg(test)]` module lives (serves the S101 submodule×scenario-class
  accounting), build/debug hooks, known asymmetries a reader would misread
  as bugs.
- **Out**: direction/target shape (→ `design/{crate}/`), boundary narrative
  (→ `bounded-contexts.md`), public surface (→ crate-root rustdoc), process
  (→ skill defs).
- **Budget**: ≤ ~150 lines; past that it is accreting design content —
  `/review` flags it.
- **Ownership**: `/dev` narrow per crate, except `cranelisp-types` → `/arch`
  (arch owns that crate's source, so it owns the voice of that code).
- **Seeding**: one `/dev` dispatch per crate (opus[1m]); input = crate
  rustdoc + design doc + recent FIXME/sprint history; run serially
  (shared-working-tree rule).

### II.6 Change control for these artefacts

| Artefact | Owner | Change mechanism |
|---|---|---|
| `.claude/commands/{skill}.md` (role content) | The skill itself | FIXME `target: /{skill}`; owner edits, deletes FIXME (existing protocol) |
| `.claude/agents/*.md` (shims) | `/sprint` | FIXME `target: /sprint` — shims are dispatch configuration, same substance as the Spawning-subagents contract |
| Allocation table + escalation protocol (this doc §II.3–II.4) | `/sprint` | FIXME `target: /sprint` **plus user sign-off for any model-tier change** (spend decision, same class as scope changes) |
| Command frontmatter `model:`/`effort:` lines | Follows §II.3 mechanically | `/sprint` edits in the same change-set as a table change — a narrow, frontmatter-only exception to "sprint never edits commands/", mirroring the FIXME-filing exception |
| sprint.md §Spawning subagents | `/sprint` | Existing ownership |

### II.7 Migration increments (each safe alone)

- **A — Proposal + hygiene** (docs/commands only, zero dispatch-behavior
  change): this doc lands; METHOD §1 gains a §1.5 pointer here; delete the 5
  retired commands; split `qa.md` → `qa.md` (strategy/risk/coverage/triage)
  + `testing.md` (authoring/repro/ledger) with METHOD §1 category update and
  `tests/CLAUDE.md` ownership note (`tests/plan/` → `/qa`, test sources →
  `/testing`); rewrite root `CLAUDE.md`'s stale skill table to the live 13;
  **user ratifies §II.3**.
- **B — Command frontmatter**: `model:` + `effort:` on the 13 live commands.
  Interactive-only effect; cannot break sprint dispatch. Verify
  `fable`/`opus[1m]` alias behavior interactively before proceeding.
- **C — Agents + contract amendment** (the dispatch-behavior change): create
  the 13 shims; rewrite sprint.md §Spawning subagents to agent-type dispatch;
  add the Dispatch log to `SPRINT_TEMPLATE.md`; add the Phase-7
  frontmatter-vs-table audit line. The next sprint's first wave is the live
  test. **Named fallback** if agent-type dispatch misbehaves: per-dispatch
  `model` param applied from §II.3 — the contract text names this fallback so
  `/sprint` degrades gracefully.
- **D — Escalation live + CLAUDE.md seeding**: §II.4 triggers become binding
  (they need the dispatch log from C); seed the 7 crate `CLAUDE.md` files via
  serial `/dev` dispatches (§II.5).
- **E — Settings hygiene**: purge stale macOS paths from
  `settings.local.json` + re-baseline permissions; disposition of the stale
  `.claude/projects/-Users-alilee-…` directory.

### II.8 Mechanics assumptions and fallbacks

The design does not depend on any of these, but each is verified at its
increment:

1. **`@` imports inside `.claude/agents/*.md`** — unverified; shims therefore
   instruct a tool-driven Read of the command file + its imports.
2. **Command `model:` frontmatter applies per-turn only** — a long
   interactive session may fall back to the session model on later turns.
   Mitigation: run sprint sessions with the session model set to fable;
   command frontmatter is a first-turn backstop.
3. **Per-invocation `effort` on the Agent tool** — unverified; effort is
   pinned in shim frontmatter only.
4. **Agent-type dispatch availability** in the harness — increment C's live
   test; fallback is the per-dispatch `model` param (§II.7 C).
5. **Portability note**: root `CLAUDE.md`'s `memory/feedback_*.md` citations
   resolve to the harness memory store
   (`~/.claude/projects/<project>/memory/`), which is per-machine. They are
   live on this machine — do not "fix" them — but §II.4 is written
   self-contained so the escalation protocol survives a machine move.
