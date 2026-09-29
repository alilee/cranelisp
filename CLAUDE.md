# Cranelisp

## First Steps

Before doing any work, find all `CLAUDE.md` files in the project:

```
glob **/CLAUDE.md
```

Before doing work in any directory, read all `CLAUDE.md` files in that directory and every parent directory up to the project root. Local `CLAUDE.md` files contain conventions and context specific to nearby files.

## Project Layout

| Directory | Purpose |
|---|---|
| [spec/](spec/CLAUDE.md) | Language specification — owned by `spec` (scribe; the user arbitrates semantics) |
| [design/](design/CLAUDE.md) | Architecture and per-crate implementation design — `design/arch/` owned by `arch`, `design/{crate}/` by `design` |
| [src/](src/CLAUDE.md) | Compiler binary crate — pipeline, REPL, CLI, session |
| `crates/` | Bounded-context library guidance: [types](crates/cranelisp-types/CLAUDE.md), [frontend](crates/cranelisp-frontend/CLAUDE.md), [typecheck](crates/cranelisp-typecheck/CLAUDE.md), [backend](crates/cranelisp-backend/CLAUDE.md), [primitives](crates/cranelisp-primitives/CLAUDE.md), [intrinsics](crates/cranelisp-intrinsics/CLAUDE.md), [platform](crates/cranelisp-platform/CLAUDE.md), [exe-bundle](crates/cranelisp-exe-bundle/CLAUDE.md) |
| [user/](user/CLAUDE.md) | User-facing documentation — owned by `docs` |
| [stdlib/](stdlib/CLAUDE.md) | Standard library in Cranelisp — a `dev` surface |
| [examples/](examples/CLAUDE.md) | Learning sequence — owned by `training` |
| [exemplar/](exemplar/CLAUDE.md) | Showcase project (Sudoku Solver) — a `dev` surface |
| [repl/](repl/CLAUDE.md) | REPL experience spec (`spec`), demos and harness (`test`) |
| [tests/](tests/CLAUDE.md) | E2e suite — plan owned by `qa`, test sources by `test` |
| [audits/](audits/CLAUDE.md) | Whole-context audit assessments — owned by `audit` |
| `sprints/` | Delivery coordination — method, roadmap, current sprint, actions, archive — owned by `sprint` |
| `.agents/` | The shared role package, pinned as a submodule (`.agents/CONSUMING.md`) |

## Sketch Oracle (retired)

The prototype compiler that lived in `sketch/` was **deleted at the close of Sprint 87** (pre-Phase-H hygiene): language semantics are frozen, and the reimplementation's own references (`design/{crate}/`, `audits/`, `spec/`) long ago superseded it. If a spec ambiguity ever needs the original oracle's behaviour, recover the sketch from git history rather than treating it as a live reference. Historical mentions of the sketch throughout `design/`, `sprints/`, and `audits/` are an accurate record of past consultations.

> **Do not copy the sketch's pipeline structure** (relevant only if recovering it from history). The sketch had a dual-pipeline defect (`TopLevel`/`ReplInput` duplication); the v4 pipeline was designed independently. See `design/arch/archive/pipeline-convergence-review.md` for the historical analysis.

## Pipeline

The v4 scheduler-driven pipeline is the only pipeline. `CompilerSession` in `src/session_v4.rs` is the unified session type. `main.rs` uses one code path for Run/Link/REPL — REPL/`--run`/`--link` divergence is always a defect. See `design/arch/overview.md` and `design/int/CLAUDE.md` for the binary/integration layer.

[README.md](README.md) introduces the compiler and its user documentation.
[AGENTS.md](AGENTS.md) and
[Copilot instructions](.github/copilot-instructions.md) direct coding hosts to
this canonical guidance.

## Active Skill Indicator

The Claude Code status bar shows the currently active skill. This is a **manual, single-session label** — useful when one terminal session is dedicated to a specific role. It does not track parallel subagents.

```bash
echo "/spec" > .claude-role   # set active skill for this session
rm .claude-role               # clear it
```

`.claude-role` is git-ignored and local only.

## Roles

Cranelisp dispatches the shared role package pinned as a submodule at `.agents`. The package defines each role's authority, boundaries and handoffs; `.agents/CONSUMING.md` states the wiring and the convergence cadence. This section is cranelisp's declaration of how it uses them.

**Dispatched — eleven subordinate roles.**

| Role | Owns here | Notes |
|---|---|---|
| `spec` | `spec/` | Scribe: the user arbitrates every normative question |
| `arch` | `design/arch/`, `crates/cranelisp-types/`, every crate's public API | Technical steward for decisions crossing crate boundaries; the user approves every inter-crate public-API change |
| `design` | `design/{crate}/` | Narrow-deployed — one crate-shaped surface per invocation |
| `dev` | `crates/{crate}/src/`, `src/`, `stdlib/`, `exemplar/` | Narrow-deployed |
| `review` | no directory | Narrow-deployed; runs in a fresh named subagent that did not author the change |
| `qa` | `tests/plan/`, `platforms/stdio/`, `platforms/test-capture/` | Risk, evidence allocation, defect intake and attribution, the traceability band; control of test-suite platform dependencies |
| `test` | test sources, fixtures and helpers under `tests/` | |
| `audit` | `audits/` | One bounded context per sprint, in rotation |
| `docs` | `user/` | |
| `training` | `examples/` | The learning sequence |
| `ops` | — | Declared and currently unused: cranelisp ships one CLI executable. Phase H release provenance is its first work |

The primary coordinator loads `sprint` and owns `sprints/`; it is not a
dispatched subagent and owns no technical content. The machine declaration is
`.agents-consumer.toml`.

**Where the retired skills went.** `/stdlib` and `/port` are `dev` narrow-deployed to `stdlib/` and `exemplar/` — those modules take the full role set like any other surface, so an exemplar is architected, designed, built and evidenced rather than written. `/examples` became `training`; `/docs` became `docs`; `/testing` became `test`. `/repl` split: `repl/spec.md` is a surface specification owned by `spec` with `design` for its interior, and the demos and harness are `test` artifacts. The earlier `/frontend`, `/typecheck`, `/backend`, `/int` and `/platform` collapsed into `dev` narrow-deployment at the 2026-07-11 artefact restructure; see git history.

**Narrow deployment.** `design`, `dev` and `review` are dispatched to exactly one crate-shaped surface per invocation, named in the dispatch. Cross-surface work is sequential invocations coordinated by `sprint`; any interface change goes through `arch` first.

**Inter-crate public-API user gate.** Every proposed change to the public API
between crates requires the user's explicit review and approval before
implementation starts. This includes additions, removals, renames, signature,
generic, bound, variant, field or visibility changes, facade re-exports, and a
new or removed cross-crate consumer edge. `arch` presents the exact proposed
delta, affected producers and consumers, compatibility and schema/ABI impact,
and the expected `public-api.txt` effect. After implementation, a non-empty
generated baseline diff returns to the user for confirmation before the wave
passes. An unchanged baseline (+0/−0) is recorded as verification evidence and
requires no user confirmation. This does not waive prior approval for semantic
contract changes that the baseline cannot represent. A phase, wave or general
architecture approval does not satisfy a required gate; an unapproved or
mismatching delta stops the wave and returns to the user.

**Models.** The pinned shared package owns each subordinate role's provider,
model and effort; see `.agents/CONSUMING.md` §Role allocation and dispatch.
The primary harness supplies the `sprint` coordinator and its model. Local
adapters match the shared allocation and add repository entry context only.

**Dispatch.** Use a fresh named subagent in the primary harness when it offers
the exact shared provider, model and effort; fresh context supplies review
independence. The package currently allocates subordinate roles to Claude;
Codex dispatches them through the shared Claude transport.
For a role hosted by another provider, use the corresponding shared transport
from the repository root: `python3 .agents/tools/codex_role.py <role> <brief-file>`
or `python3 .agents/tools/claude_role.py <role> <brief-file>`, as selected by the
shared allocation. Never dispatch `sprint`. Both paths are normal role execution
within the approved phase. If the exact route or required access is unavailable,
escalate the tooling gap instead of substituting a model, effort or harness.

Cross-harness commands require their provider's network authority. In Codex,
request repository-scoped escalation for the Claude transport when needed;
keep that authority scoped to the wrapper. Shared transports retain their
permission and sandbox defaults unless the user explicitly authorizes a change.

**Host adapters.** `.claude/skills` resolves the shared contracts directly.
The eleven checked-in `.claude/agents/` adapters carry the shared provider,
model and effort plus repository-entry context; `.github/agents/` exposes the
same subordinate inventory to Copilot. Adapters carry no independent role
authority. Claude dispatch hooks enforce provider routing and record lifecycle.
The repository wiring verifier composes the pinned package's consumer check.

The optional Rust context standard introduced in the S122 package update is
not adopted. Existing crate and design conventions continue to apply.

## Delivery

Reimplementation phases A–G are complete; the project is in **Phase H (release compiler)**. The ring model that structured phases C–G was retired as a scheduling axis in Sprint 64 — sprint is the sole axis; `[R{N}]` annotations in older documents are historical.

**Phase mapping.** Cranelisp runs seven named phases. The package states the ordering they must encode rather than naming phases of its own (`.agents/skills/sprint/SKILL.md` §Run the increment); cranelisp's correspond:

| Cranelisp phase | Package obligation |
|---|---|
| 1 Scope | Frame |
| 2 Architecture review · 3 Design · 4 Wave organization | Ready |
| 5 Language phase | Realise |
| 6a/6b User-facing | Realise, then Accept |
| 7 Close | Accept, then Close |

Every transition between these declared phases requires explicit user
approval. Completing a phase, resolving a question inside it, accepting the
product outcome or authorizing one operation does not authorize the next phase;
`sprints/METHOD.md` §2.1 defines each checkpoint.

Phase 6a/6b existed to carry the user-proxy standing-quality pass. That question now lives inside the `docs` and `training` contracts, which re-ask it against the whole artifact every increment, so the phase schedules the work without having to carry the discipline.

Current state and trajectory:

- `sprints/METHOD.md` — what cranelisp adds to the role package: the crate-shaped surfaces, the seven phases, escalation, the audit rotation, filing formats
- `sprints/ROADMAP.md` — sprint-by-sprint progress
- `sprints/SPRINT.md` — the active sprint plan (absent between sprints; archived to `sprints/archive/`)
- [Sprint template](sprints/SPRINT_TEMPLATE.md) — canonical starting structure for a new sprint plan

The following collections are established here for document discovery:

| Collection | Scope and purpose |
|---|---|
| `sprint-delivery-documents` | Current sprint coordination, delivery method and roadmap documents under `sprints/`. |
| `delivery-actions` | Open cross-sprint work and defect intake records under `sprints/actions/`. |
| `closed-sprint-records` | Closed sprint records under `sprints/archive/` preserve the decisions and evidence of their delivery date. Their outgoing historical references do not track the current tree. |
| `host-role-adapters` | Checked-in role entry guidance under `.claude/agents/` and `.github/agents/` connects each host to the shared role contracts. |

`arch` is the final arbiter of design decisions that cross crate boundaries.
`sprint` orchestrates within the approved phase; the user approves every phase
transition and all language-normative questions.

## Usability Findings and Defects

Roles working the language from outside — `docs`, `training`, and `dev` on `stdlib/` and `exemplar/` — routinely encounter problems while exercising it. Two categories, different closure rules:

**Usability findings** — corner cases, unhelpful errors, inference friction, missing APIs, ergonomic issues. Filed as actions (see §Cross-Role Changes). Documentation is sufficient closure.

**Defects** — real compiler bugs, spec violations, runtime crashes, REPL/`--run` divergences, output that does not match the spec. **A defect is not closed until `test` has committed a narrow test that reproduces it** — failing, un-ignored, with a `// spec:` annotation. The failing test is the durable record, the trigger for compiler-skill resolution, and the regression guard once fixed. A FIXME on a design doc captures intent but doesn't prove the issue exists, catch regression, or trigger CI; the failing test does all three. (A defect with a failing-not-ignored repro does NOT also need a numbered FIXME — the test is the record and the trigger.)

**Cross-role defect handoff requires a minimal repro.** Error signatures alone — "unresolved symbol X", "SIGSEGV in Y" — routinely mask layered bugs: the visible error belongs to one surface, the underlying failure to another. Before `sprint` spawns a cross-surface triage, the discovering role MUST produce a minimal repro per `tests/CLAUDE.md` §"Isolating Cross-Crate Failures" — or request `test` to. Attribution itself is `qa`'s, under the control discipline its contract carries: a repro confirms a symptom, and only a discriminating control confirms a mechanism. The handoff brief names the repro, not just the symptom.

**Reproduced defects join the test suite permanently, and small is the goal.** Every reduction — complete or partial — lands as a committed test. Small repros pay twice: the fix often becomes obvious during isolation (Sprint 59's prelude-parity bug was visible the moment the repro shrank to a single function), and small tests produce small CLIF — `/clif <name>` in the REPL or `CRANELISP_CODEGEN_DUMP=<name>` (or `*` for all functions) makes codegen-layer bugs (RC mis-count, missing load, bad relocation) visible in IR before source reduction finds them. Partial reductions commit with a comment naming what is still unknown, and an action carrying the remainder.

## Cross-Role Changes

A role MUST NOT silently edit an artifact owned by another. It files, and the owning role resolves in its own files and deletes the filing; git history is the audit trail. Filing is the ONE exception to artifact ownership — any role may file against any other.

**An action is for deliberate cross-sprint work, an accepted residual, or defect intake routed to `qa` — never for a question available now.** A dependency inside the increment is resolved synchronously through `sprint` in the same wave.

**In transition, two surfaces.** New filings are actions under `sprints/actions/`.
Their filename pattern is:

```text
sprints/actions/ACT-NNNN-short-name.md
```

The open FIXMEs at `design/arch/fixmes/` are **run down in place** over the next several sprints rather than converted in bulk; their format and lifecycle stay as `sprints/METHOD.md` §3.3 records them until the directory empties. Inline `FIXME(/skill)` comments are a third and older protocol, superseded at Sprint 63 — do not author new ones.

**Verify against source first.** Any disposition of a filing — resolve, defer, re-target, or a scheduling decision built on it — verifies its central claim against its `refers_to` source as the first act, and the note records what was opened.

**Wave gate**: before `sprint` advances a wave it scans both surfaces for open items targeting a role in that wave; any match blocks until resolved or explicitly deferred with rationale.

## Role Handoff

Each role contract states where its work routes; `sprint` sequences. A role's report ends by recommending what to invoke next. When a sprint is active, consult `sprints/SPRINT.md` for the task list and blocking dependencies; otherwise `sprints/ROADMAP.md`.

## Design Principles

- **Self-documenting REPL**: Every symbol and expression entered at the REPL should produce useful feedback — its type, value, or usage description. No valid language construct should produce an opaque error. Special forms, operators, and user-defined names should all respond with what they are and how to use them. Output reinforces the language syntax using `:Type value` notation with fully-qualified names (e.g. `:primitives/Int 3`, `:(Fn [a] a) user/id`). See `repl/spec.md` for the normative REPL experience specification.
- **Clojure standard library**: Follow the Clojure standard library for function naming and design as much as possible.
- **Optional prelude**: Nothing in the prelude is required for the language to work. An empty prelude is a valid starting point for the REPL or batch programs. The prelude provides convenience (traits, operators, types, macros) but the core language — primitives, special forms, type inference — works without it.
- **Stdlib separation**: Tests (`tests/`) and examples (`examples/`) MUST be free-standing — zero dependency on `stdlib/`. Tests define any needed helpers inline using compiler primitives and special forms. Examples may share helpers through the examples-local library at `examples/lib/`, itself built only from compiler primitives and special forms and admitting a definition only after the example that teaches its mechanism ([library rules](examples/lib/README.md)); the stdlib is learned from the stdlib docs, not from `examples/`. Only the exemplar (`exemplar/`) and production binary (`src/main.rs`) may depend on the standard library. This ensures the language itself is validated independently of any particular library code.

## Assurance — how we know something holds

**Every invariant is either structurally unconstructable or continuously measured. "Graded by inspection" is the failure state.**

An invariant asserted because someone read one site and found it satisfied is not an invariant — it is one function's property, and nothing stops another site from violating it tomorrow. This is not a theoretical concern here:

- Safety-register row **R11 ("Concreteness at codegen") was graded `unconstructable` from S84 to S119 — thirty-five sprints — while two hand-mint sites quietly violated it.** The grade was true of the one function that had been inspected. The S119 census falsified it. The corrective (`P-1`) was not a better inspection; it was converging four decision points onto one gate, so the violating construction stops compiling.
- Invariant **I-CT** was ratified on the premise that its emission pair was behaviour-identical to pre-migration HEAD. It proved the *count* balanced while being silent on whether the counted word was a reference at all — a wild atomic write on scalar payloads at the nullary threshold.
- The `DropGlueRegistry` **passed review and static checks across two sprints and could never have run**, because nothing executed it.

The three admissible grades, in preference order:

1. **Structural** — the violation does not compile, does not link, or does not typecheck. Converging N decision points onto one, making an illegal state unrepresentable, and single-sourcing a fact from its determinant all buy this. Prefer it whenever the cost is bounded.
2. **Measured** — an executing check observes the property continuously, and the check has itself been **proven to detect** (see the arming discipline below). A permanent census whose measured traffic gates its own removal counts; a one-off measurement does not.
3. **Asserted-with-a-named-falsifier** — a claim that is neither, carrying an explicit statement of what observation would refute it and where that observation would come from. Legitimate but temporary; it is a debt, and it is recorded as one.

Anything else — "reviewed and correct", "obviously holds", "checked when written" — is **not a grade**. If that is genuinely the best available, say so in those words rather than borrowing the language of a grade.

Three corollaries the record has already paid for:

- **An instrument is unverified until it is proven to detect.** A check that has never fired against a deliberately planted fault is indistinguishable from a check that cannot fire. Detection proofs are part of the change-set that introduces the instrument, not a follow-up — and the negative leg (the check stays silent when the fault is absent) is as load-bearing as the positive one. Instruments have been observed running *after* the mutation they were meant to catch, and guards have been observed failing for the wrong reason (parse errors masking the real signature), which is indistinguishable from working until someone reads the stderr.
- **Landed with zero consumers under static-only review is not landed.** Crediting foundation work requires a consumer or an executing test in the same change-set.
- **A ruling that has not survived measurement does not bind.** Where a design decision is falsifiable by running something — a corpus, a benchmark, a census — the measurement happens *inside* the design window. This has caught the same wrong ruling twice, one sprint apart, both times before it landed damage.

### Records are claims too

A document, FIXME, plan row, or comment that asserts something about source is a claim, and it decays. Stale records have repeatedly cost whole sprints of misrouting: a locus naming a file the symbol was never in, a scope that suppressed its own scheduling, a cited API that exists nowhere, a tranche scoped at a file in a crate that has none.

Verifying a claim against its `refers_to` source is the binding first act of any FIXME disposition (`sprints/METHOD.md` §3.3) — but a discipline that depends on remembering is not a mechanism. The mechanism is:

```
python3 .agents/tools/check_documents.py --root . --config standing-documents.toml
```

The shared checker discovers documents independently, checks their establishment
chain to this root, and validates local references, source line bounds and
symbol text presence. [standing-documents.toml](standing-documents.toml) owns
project declarations; the [shared contract](.agents/CONSUMING.md#shared-document-checking)
owns checker behavior. Whether a citation supports a document's substantive
claim remains an owner judgment.

Exit 1 reports unresolved findings; exit 2 reports inability to inspect or an
invalid invocation/configuration. The project invocation applies no baseline.
Outstanding findings require repair or explicit disposition; installing the
checker does not accept them as debt. The retired checker's baseline and exact
migration mapping are retained as [reconciliation evidence](tests/plan/s122-document-checker-reconciliation/README.md),
not suppression input.

## Testing

The [stdio contract](platforms/stdio/spec.md) and
[test-capture contract](platforms/test-capture/spec.md) are owned by `qa`,
together with their platform components, because the test suite depends on
them. Changes are controlled as part of the test suite. Examples, user
documentation, REPL demos and the exemplar reuse these components under that
ownership. Platforms are application or standard-library components; their
individual behavior is not language specification.

- **Always use `cargo nextest run --no-fail-fast`** instead of `cargo test`. Nextest runs each test in its own process, parallelizes across binaries, and completes the full suite in **~170s** post-build (measured 2026-08-29 at 5,687 tests; `stdlib_conformance` alone is ~85s of it, and a rebuild adds ~30–60s). `--no-fail-fast` is required for full-picture runs — the intentional defect guards (below) otherwise stop the run early. The suite includes every crate's lib tier via `[workspace] default-members` (S101). The alias `cargo nt` is also available via `.cargo/config.toml`.
- **Never run tests in background mode.** Wait for the run to complete before proceeding. Background test runs pile up and contend on build locks.
- **Five-minute timeout expectation.** The full suite is ~170s post-build. If a run exceeds ~5 minutes including build, something is wrong — kill it and investigate.
- **One agent, one test run.** When multiple agents are active, only the agent that owns source code changes should run tests. Other agents must not run tests concurrently.
- **Single agent at a time for source-touching work.** Worktree isolation is broken on this project, so parallel agents share one working tree. Two agents editing concurrently race on the git index and on the editor/linter — a subagent `git stash` or a mid-edit linter pass will silently clobber another agent's changes (observed Sprint 81: a parallel `/dev` fan-out corrupted the tree; recovery cost a full reconciliation). Read-only fan-outs (search, survey, design-planning that only returns text) may run in parallel; any agent that *edits source* runs serially.
- **Every fix lands with a unit test; assess the e2e need BEFORE writing the fix.** A **unit test is mandatory** for every fix — it pins the behaviour at the exact seam where the bug lived and is the fastest guard against a re-break. **Before** writing the fix, also assess whether an **e2e test** is warranted (add one when the bug is observable end-to-end or crosses `--run`/`--link`/REPL modes — unit and e2e answer different questions). Write the failing test(s) **first**; the fix flips them green; test(s) and fix land in the **same change-set**. A fix guarded only by an e2e — or only by "the suite still passes" — is incomplete, and deferring the test to a follow-up FIXME (the "test owed" anti-pattern) inverts the discipline and routinely never gets done. (Binding statement: `sprints/METHOD.md` §2.2.)
- **Failing-not-ignored defect repros**: the suite deliberately carries a small number of **known-defect guards** — failing, NOT `#[ignore]`'d — so each flips green when the owning role fixes its defect. Hiding a spec violation behind `#[ignore]` is itself a defect. **Do not enumerate or count the guards here** — the set changes every sprint and is knowable from the live sources: run `cargo nextest run --no-fail-fast` to see the current REDs; each intentional guard traces to an open filing naming the owner. A **genuine regression** is any RED that does **not** trace to a known open defect that way. (Defect-repro history/analysis: the `// defect:` notation per `tests/CLAUDE.md` §"Defect-repro notation"; the former failure ledger was retired in S108 (Git history).)

## Git & Remote

- **Remote**: `origin` → `https://github.com/alilee/cranelisp`
- **History**: The remote uses an orphan commit (no prior history). When pushing, always force-push (`git push --force origin main`) since the local repo has a longer reflog that doesn't share ancestry with the remote.
- **Do not push without explicit user request.**
- **Commit directly to `main`; do NOT create branches.** This single-developer repo is managed linearly on `main` — sprint/feature/worktree branches only accumulate as cruft (and worktree isolation is broken here anyway; see §Testing "single agent at a time"). This **overrides** the general "branch first when on the default branch" convention. There is no merge step at sprint close — work is already on `main`. (The forbidden-git-ops list for subagents still applies: no `stash drop/clear`, `reset --hard`, `checkout --`, `restore`, `clean -f/-fd`.)

## Requirements/Test Traceability

Every spec requirement MUST be traceable to a test, and every test MUST trace back to a spec requirement. This creates bidirectional coverage visibility.

### Annotation Convention

Spec headings and table rows use inline annotations to show coverage status:

| Annotation | Meaning |
|---|---|
| `[Tested tests/file::test_name]` | Positive path tested by the named test |
| `[Tested+Neg tests/file::test_name]` | Both positive and negative paths tested (see below) |
| `[Tested]` | Section-level: all sub-requirements have test annotations |
| `[Tested+Neg]` | Section-level: all sub-requirements have positive AND negative coverage |
| `[S{M}]` | Not yet tested; scheduled for sprint M |
| `[S{M} — tests/file::test_name IGNORED]` | Test exists but is `#[ignore]`'d (known gap) |

> The ring axis was retired as a project-wide planning/scheduling axis in Sprint 64 — sprint is the sole scheduling axis. Pre-S64 `[R{N} S{M}]` annotations in archived docs and older spec/test rows are historical. New annotations use sprint-only `[S{M}]`.

**Positive vs negative coverage.** `[Tested]` means the happy path works — the feature produces correct output for valid input. `[Tested+Neg]` means the test suite also verifies **what must NOT happen**: wrong items are absent, invalid input produces the right error, boundary violations are rejected. `[Tested]` without `+Neg` is a coverage gap — the feature works but nobody has verified it doesn't also do wrong things.

**Fine-grained annotations** go on individual table rows and MUST requirements — each row should have its own `[Tested ...]` or `[S{M}]` tag. **Section-level annotations** are summaries: a section heading carries the lowest coverage level of its children.

**Test-side tracing**: Every test function has a `// spec:` comment naming the spec section it validates:
```rust
// spec: repl/spec.md §1.2 — Int display format
#[test]
fn display_int_result() { ... }
```

### Applying Annotations

- `repl/spec.md` — REPL experience spec (owned by `spec`)
- `spec/*.md` — language spec files (owned by `spec`)

When `test` writes a test, it adds the test-side `// spec:` comment. When coverage is verified, **`qa` adds the spec-side `[Tested ...]` annotation directly** — the traceability annotation band (`[Tested …]`, `[Tested+Neg …]`, `[S{M}]`, `[… IGNORED]`) is `qa`'s to maintain, edited in place with **no filing cycle** to `spec` (coverage status is `qa`'s authority; a round-trip to flip a bracket tag is pure friction). Only the requirement *prose* around the annotations stays owner-gated. `qa` audits the two-sided match as part of its coverage process.

**`[Done]` is retired.** It provided no traceability and was applied prematurely. All `[Done]` tags should be replaced with either `[Tested tests/file::test_name]` (if covered) or `[S{M}]` (if not).

## Document maintenance

The [information map and retention policy](sprints/METHOD.md#31-where-things-live)
define canonical content homes. Keep current authority separate from proposals
and history, extract useful missing content before retiring superseded records,
and establish retained documents through this root. Measure reading and update
burden as well as checker findings.

## Known Issues

Current issue dispositions live in the [active sprint](sprints/SPRINT.md),
[open actions](sprints/actions/) and [remaining legacy filings](design/arch/fixmes/).
The retired prototype strategy and issue records are recoverable from Git history.
