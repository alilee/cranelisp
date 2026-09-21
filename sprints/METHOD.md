# Cranelisp Delivery Method

> **Owner**: `sprint`.
> **Scope**: what cranelisp adds to the shared role package — the crate-shaped surfaces, the seven-phase increment, and the artifacts each role keeps here.
> **Out of scope**: role authority, boundaries, handoffs and shared model relationships (`.agents/`); the role declaration, phase mapping and filing protocol (root `CLAUDE.md`); architectural rules (`design/arch/`); per-crate design (`design/{crate}/`). This document points to these rather than restating them.

---

## 1. Roles here

Root `CLAUDE.md` §Roles is the declaration — which of the package's twelve roles cranelisp dispatches, what each owns here, and how the shared allocation is hosted. This section carries what that declaration is too compact to hold.

### 1.1 The crate-shaped surfaces

`design`, `dev` and `review` are narrow-deployed to exactly one surface per invocation:

- `cranelisp-frontend`
- `cranelisp-typecheck`
- `cranelisp-backend`
- `cranelisp-primitives` + `cranelisp-intrinsics` — the primitive declarations and backend-emitted runtime library. The binary is a host client; runtime internals (reactor, IO-tree disposal and RC) belong to intrinsics. [Bounded contexts](../design/arch/bounded-contexts.md) defines their boundaries and dependencies.
- `cranelisp-platform` — consumer of the runtime, not its owner
- `src/` — binary crate (pipeline, REPL, CLI, session), plus `crates/cranelisp-exe-bundle/`

The language-facing surfaces — `stdlib/`, `examples/`, `exemplar/`, `user/`, `repl/` — are worked by `dev`, `training`, `docs`, `spec` and `test` per the root declaration, and take the full role set like any other surface.

Cross-surface work is sequential invocations coordinated by `sprint`. Any interface change goes through `arch`, in the types crate, before per-surface work proceeds.

**The architectural principles are the standard these surfaces are built and reviewed against.** `design/arch/principles.md` is the canonical index, one file per principle beneath it, owned by `arch` and revised only at close. `arch`, `design`, `dev` and `review` read it first and cite by name when a structural choice is governed by one. Principles 5 (testability is structural), 6 (complexity has a budget), 8 (no interim implementations) and 12 (design for the full spec surface) recur most often.

### 1.2 Where content lives

The [information map](#31-where-things-live) identifies canonical homes. Shared
role contracts own procedure; technical documents own system contracts and
mechanisms; local memories supply entry guidance and navigation.

A local `CLAUDE.md` carries only guidance needed to work in that directory:
non-obvious tooling constraints, build/debug entry points and links to its
contracts and tests. Link to canonical invariants and API guarantees rather
than maintaining a second account. Do not repeat parent guidance, sprint
history or a complete source inventory. Source memories belong to `dev`, except
the types crate's memory belongs to `arch`.

### 1.3 Where cranelisp overrides the package

**`arch` is a deputy, not an originator of substance.** The package's `arch` contract makes decomposition, facades and technology selections its own to decide and proceed on. **Cranelisp overrides that**: the user is the architect at the language-shape level, and `arch` drafts, ratifies and applies substance the user has approved rather than inventing it.

So before `sprint` files anything *proposing* an architectural decision, or dispatches `arch` to author or amend one, the substance plus rationale plus rejected alternatives go to the user and `sprint` waits for an explicit OK. This binds for formal register decisions and for informal choices that meaningfully affect language shape, compiler structure or boundary contracts. It does **not** bind implementation detail falling out of an approved decision, propagation of approved substance, per-crate slice authorship, or a filing proposing no architectural change. Once the user has approved substance in conversation, proceed without re-asking — but the downstream text or dispatch prompt must match what was reviewed.

The override exists because several S66 decisions landed via `arch` answering `sprint`-filed requests without the substance being endorsed first, and had to be corrected retroactively: Decision 44 amended twice mid-sprint, Decision 45 reversed after a `dev` attempt exposed a lookup-cost mismatch with the user's own principle. Each correction cost an `arch` round and sometimes a `dev` re-run.

---

## 2. The increment

Seven phases. Root `CLAUDE.md` §Delivery maps them onto the ordering the package requires.

### 2.1 Phase table

| Phase | Name | Roles | Outputs | Checkpoint for advancement |
|---|---|---|---|---|
| 1 | Scope | `sprint` | `SPRINT.md` DRAFT; disposition of the prior sprint's audit assessment | User approves scope and advancement to Phase 2 |
| 2 | Architecture review | `arch` | Interface changes approved or deferred; scope adjustments | `arch` signs off; user approves the result and advancement to Phase 3 |
| 3 | Design | `spec`, `arch`, `design` per surface, `qa` | Updated spec, interface types, per-surface design, evidence plan | Readiness complete; user approves advancement to Phase 4 |
| 4 | Wave organization | `sprint` | Wave breakdown; `SPRINT.md` ACTIVE | User approves the waves and advancement to Phase 5 |
| 5 | Language phase | `test` first, sprint-wide; then per surface `design` → `dev` → `review` | Passing evidence; refined design, implementation, module tests, review findings, approved public-API diffs | User accepts what ships and approves advancement to Phase 6a |
| 6a | User-facing assessment | `docs`, `training`, `dev` on `stdlib/`/`exemplar/`, `spec` on `repl/`, `sprint`; `audit` on the rotation context | Plan for the language-facing surfaces against what shipped; gap filings | User approves the plan and advancement to Phase 6b |
| 6b | User-facing action | as 6a | New sprint demo; exemplar, stdlib, examples and docs updates; prior demos replayed green | User approves the delivered artifacts and the exact Phase-7 close operations |
| 7 | Close | `sprint` with the user | Outcome report; approved archive/commit/ROADMAP/filing operations | Close operations completed as approved; final outcome reported |

No phase advances on an internal role sign-off alone. At each checkpoint,
`sprint` records the completed outcome and evidence, deviations and unresolved
decisions, then presents the next phase's exact scope, roles, external
operations and exit condition. Work for that next phase starts only after the
user approves the named transition. Approval of a correction, an individual
operation, product acceptance or continued work inside the current phase does
not approve a later transition.

QA records each condition as acceptance evidence, a safety fence, a diagnostic
observer or a maintenance check. Phase checkpoints keep those classes visible:
an observer or maintenance failure is reported and routed, but it cannot become
an acceptance gate for unrelated compiler behavior without a new QA
classification grounded in the governing requirement or design.

Phases 6a/6b schedule the language-facing work. The standing-quality question each of those roles owes — re-asked against the whole artifact rather than the delta — lives in their contracts, not here.

### 2.2 Phase notes

**Discovered defects: RED → design → GREEN, with parallel QA review**
(user directive, S121). First preserve each discovered defect as a minimal,
permanent, failing-not-ignored reproduction with a discriminating control.
Then design and implement the correction until the reproductions pass,
including the required module evidence. In parallel, `qa` investigates why
existing coverage missed the scenario and whether a systematic testing gap
needs correction. This review does not delay recording the RED or become a
serial prerequisite to the repair. Reconcile its findings before closure;
existing requirement, architecture, public-API and phase approval gates still
apply. An ambiguous requirement is escalated, not guessed into a test.

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

**Approved cross-crate migrations.** The user-established callee-first rule
(recorded in FIXME 0940) permits a planned producer-to-consumer continuation
with temporary compile failures inside an approved migration. Sprint retains
the affected source reservations and records the remaining consumers; a caller
that still uses the retired interface is migration work, not grounds to restore
it. This continuation is not a completed delivery handoff. The cascade closes
only after its consumers build and the allocated behavioral evidence plus the
full `cargo nextest run --no-fail-fast` establish the accepted outcome; compile
success alone does not prove the migrated behavior (FIXME 0941). Required API
approvals and serial source editing still apply.


**`review` runs in a fresh named subagent.** Fresh context and non-authorship
supply the required independence. Run the shared model and effort allocation
in the primary harness when it is available there, and use the configured
cross-harness transport otherwise. Give the
reviewer the exact change set, governing authorities and already-executed test
evidence, and keep it read-only when the host supports that boundary. Every
returned finding is a claim: `review` verifies and adjudicates technical
findings; `sprint` routes each surviving finding to its owner and records the
reviewer identity and disposition. A
blocking finding may never be silently dropped. Neither same-harness nor
cross-harness delegation needs approval beyond the approved phase and role
work. Missing required dispatch tooling is escalated to the user.

### 2.4 Deferral

1. **Defects discovered in Phase 5 are addressed in Phase 5** — fix, defer with explicit rationale, or close Phase 5 short. Conscious and recorded. Phase 6 does not retroactively reopen it.
2. **Speculative refactoring deferred; emergent refactoring mandatory in-sprint.** When the current work has made cleanup cheap — third duplicate, file over budget, a `mirror` comment — extract in-sprint.
3. **Interim architecture is avoided, not deferred.** If a feature would require throwaway infrastructure a later increment replaces, do not build it.
4. **The backlog is drained, not parked (user, S91).** Phase 1 pulls in every open filing unless there is a genuine reason to defer. Genuine reasons: explicitly release-tier work; a hard dependency on a not-yet-started track; a trigger whose condition is unmet. "Scheduled elsewhere in the roadmap" is not one. Present the deferral list with a reason per item so the user can challenge it.
5. **2× escalation.** Items deferred once may be deferred again with rationale. Items deferred twice ship in the current sprint or require explicit user sign-off for a third deferral. Applies to filings, ignored tests, and review findings.

Size is not among these: the package's `sprint` contract already rules that decomposition comes before any carry, and that a carry needs evidence of unreachability rather than a judgment that the target is far.

### 2.5 Mid-sprint adjustment

If `sprint` is invoked mid-sprint: report the current phase and its approved
scope; recommend continue within it, re-scope, advance or close. Scope changes
and every phase transition require user sign-off. `sprint` never advances or
closes unilaterally.

### 2.6 Escalation

**Decider**: `sprint`, within the currently approved phase and its orchestration
remit. User sign-off is required for every phase transition, scope change, a
third deferral per §2.4.5 and every language-normative question. Routing follows
the definitive shared role, model and effort allocation. Proposed allocation
changes belong in the shared package, not in a sprint-local exception.

Triggers, normative:

1. **Recurring failure by symptom.** The same symptom — test name, error signature, crash site — still failing after **two** dispatches at the role's shared allocation makes the third a `qa` **attribution** dispatch: minimal repro plus owner under the control discipline, not a fix. The frame shifts from "fix it" to "attribute it".
2. **Contested or layered attribution.** The discovering role and the symptom's apparent owner disagree, or a fix exposed a second failure → `qa` triage before any further `dev` dispatch.
3. **Second deferral.** An item at its 2× point (§2.4.5): a shared-judgment-tier `qa`/`arch` triage explains structurally why it keeps deferring before the user decides its disposition.
4. **Review-resistant blockers.** A blocking finding surviving one `dev` fix round → `sprint` chooses: escalated `dev` (genuinely hard to build) or attribution-first (possibly wrongly attributed).
5. **Design-authority contact.** Work touching a principle, facade or bounded context never escalates in place — it files to `arch`. Spec ambiguity routes to `spec`, which frames it for the user.
6. **Out-of-rotation audit.** Triggers 1–4 firing repeatedly in one bounded context, or a major arc completing there, pull that context forward in the audit rotation (§2.7). Attribution fixes the instance; the audit assesses the pattern behind repeated instances.

**Recording**: the dispatch log in `SPRINT.md`, per wave — `| role | surface | model | effort | harness |`. Rows may be batched only when all recorded fields match. Phase 7 checks that execution matched the definitive shared allocation and routes any proposed relationship change back to the shared package.

**Dispatch by a named role agent, never by prose.** The primary harness remains
the coordinator. Use a fresh named subagent there when it offers the exact
shared allocation; otherwise use the configured cross-harness transport. Both
are ordinary dispatch and require no further approval. Escalate missing
required tooling to the user instead of substituting an allocation.

### 2.7 Rolling whole-context audit

One bounded context is audited per sprint, in rotation, so every context gets a fresh assessment on a bounded period and no sprint pays for more than one frontier-tier deep read. The `SPRINT.md` template carries a standing `Audit: {context}` field filled at Phase 4 — the cue is structural, because an audit that depends on someone remembering it decays like everything else.

**The acid test** (user-ratified 2026-07-11), against which the assessment opens with a graded per-attribute verdict: *if we lost this context's code and docs but retained the insight from experience, and produced a lean, high-quality solution second time around — would it look like this?* Evidence follows: design quality, design realisation (drift in both directions — unrealised design, and design the implementation has silently falsified), simplicity and volume optimality, duplication, risk-weighted coverage on the production path, maintainability, memory freshness. Hygiene findings are evidence within that frame, never a substitute for the verdict. The dispatch runs read-only in the Phase 6/7 window; the assessment lands in `audits/{context}-sNNN.md` with recommendations carrying evidence, cost class and proposed owner. **Next sprint's Phase 1 disposes each recommendation with the user**: accepted → `sprint` files against the proposed owner; declined → recorded in the assessment with rationale. `audit` never files for its own recommendations and never blocks the current sprint. At Phase 7, `sprint` checks the audit's calibration — recommendations that consistently die at acceptance are a finding about `audit` — and verifies both halves of the cycle: that this sprint's audit was dispatched, **and that the previous assessment was disposed**. A lapsed disposition is how four recommendations reached their fourth audit untouched (S110).

Assessments are temporary point-in-time records used to reach disposition. Preserve every unaddressed point in its canonical action, existing filing or owning standing document before retiring the report. Undecided recommendations remain pending disposition; moving them does not approve implementation or close them. Historical audit reports and their diagrams live in Git history, not the standing tree. Record provenance with the original checkpoint so the evidence remains recoverable. Rotation order is coordination state; reordering is a scope-class decision (trigger 6, or user direction).

---

## 3. Artifacts

### 3.1 Where things live

| Information | Canonical home | Owner |
|---|---|---|
| Entry guidance and navigation | Root and nearest `CLAUDE.md`; public introduction in `README.md` | Directory owner; root `sprint` |
| Required language / REPL behavior | `spec/index.md` and `repl/spec.md`, leading to their sections | `spec` |
| Using / learning the system | `user/` / `examples/`; callable reference in library docstrings | `docs` / `training`; library `dev` |
| System boundaries and shared guarantees | `design/arch/overview.md`, `design/arch/bounded-contexts.md` and focused shared contracts | `arch` |
| Context mechanisms and invariants | Context master under `design/`, with independently maintained subordinate subjects | `design`; types `arch` |
| Exact Rust API obligations and guarantees | Rustdoc beside public items; `public-api.txt` is surface evidence | `arch` owns public contracts |
| Current assurance and evidence navigation | `tests/plan/PLAN.md`; bounded active evidence plans under `tests/plan/` | `qa` |
| Executable evidence | Solution tests in `tests/`; module tests beside source | `test` / source owner |
| Audit assessments | `audits/` while awaiting disposition; historical reports in Git; unaddressed points in the action/filing or owning standing homes | `audit`; `sprint` coordinates disposition |
| Current increment / future direction | `sprints/SPRINT.md` / `sprints/ROADMAP.md` | `sprint` |
| Unresolved obligations | `sprints/actions/`; existing `design/arch/fixmes/` drained in place | Target role resolves |
| Closed delivery outcomes | Compact `sprints/archive/` records; ordinary working history in Git | `sprint` |
| Role procedure / local delivery additions | Shared `.agents/skills/` / this method | Shared package / `sprint` |
| Host-entry guidance and adapters | `AGENTS.md`, `.codex/`, `.claude/`, `.github/` entry and role wiring | `sprint` |
| Repository verifier implementations / project document declaration | `scripts/` / `standing-documents.toml`; checker implementation in shared package | `test` / `sprint`; shared package |

The primitives/intrinsics shared contracts under `design/runtime/` retain one
nominated design owner; their location is not an instruction to change crate
boundaries. Exact context entry points are linked by the governing design
memories. Substantial technical proposals live with their technical owner and
are linked from the sprint, not copied into a second specification.

Host-entry guidance directs each coding-agent host to the canonical repository
and shared-package authorities. Sprint maintains those entry points and their
consistency with the role adapters; ownership of referenced architecture,
evidence policy and shared role contracts stays with their respective owners.
Copilot retains eleven checked-in role adapters, maintained directly and
verified against the shared package by the existing wiring check. There is no
adapter generator.

Place Claude handoff inventories and scratch reports in ignored `.local/` so
its normal file tools can access them within the repository scope.

#### Retention and maintenance

- Retain a document for a named reader, current purpose, owner and canonical
  content. A link or past approval does not by itself justify retention.
- Maintain each claim authoritatively once. Audience-specific explanations
  link to that authority; indexes and memories remain thin navigation.
- Distinguish current contracts, proposals and historical evidence. Root
  establishment proves discoverability, not approval or currentness.
- Compare a candidate with its canonical destination. Delete redundant or
  obsolete originals when Git suffices; first extract any useful missing
  rules, rationale or evidence in the destination's form. Preserve unresolved
  obligations independently; deleting a record does not resolve its findings.
- Retire working plans after incorporating their useful results. Keep closed
  records only for an explicit evidence or rationale need beyond Git. Preserve
  irreplaceable raw evidence in an established location with its purpose.
- Keep PLAN focused on current assurance and SPRINT on current coordination.
  Completed matrices and transcripts do not accumulate there or move into a
  replacement archive dump. Split only independently maintained subjects.
- Establish every retained document through its governing memory or a coherent
  collection to root `CLAUDE.md`. The project declaration implements discovery,
  not another explanatory map; new exceptions need explicit disposition.
- Judge reduction by active prose, duplicate authorities, and how many places
  a reader or ordinary change must visit. File/finding counts are diagnostic,
  not quotas or proof that retained content is worth keeping.

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

**Action** — an `ACT-NNNN-short-name.md` file under `sprints/actions/`, frontmatter then body:

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

**FIXME** — the pre-existing `NNNN-short-name.md` form under `design/arch/fixmes/`, with `number`, `target`, `filed_by`, `filed_at`, `sprint_filed`, `refers_to`, `status`. No new ones are authored; the open set is run down in place.

Numbers are allocated above the highest used, never reused or backfilled. Only the owning role resolves and deletes; `sprint` gates but does not delete — the narrow exception is a Phase-1 audit disposal where an assessment has verified resolution against source and the user has approved it.

### 3.4 Memory

`memory/` holds point-in-time observations and user feedback. Non-normative: this document is normative for what cranelisp adds, role contracts for how a role works, design docs for crate direction. Memories are signals that may inform the next sprint or the next contract contribution; they do not override the canonical sources. When a memory's content becomes durable it migrates into the appropriate canonical document and the memory is retired.
