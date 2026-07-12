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
| `spec/` | Language specification — owned by `/spec` (scribe; the user arbitrates semantics) |
| `design/` | Architecture and per-crate implementation design — `design/arch/` owned by `/arch`, `design/{crate}/` by `/design` |
| `src/` | Compiler binary crate — pipeline, REPL, CLI, session |
| `crates/` | Bounded-context library crates (types, frontend, typecheck, backend, primitives, intrinsics, platform, exe-bundle) |
| `user/` | User-facing documentation — owned by `/docs` |
| `stdlib/` | Standard library in Cranelisp — owned by `/stdlib` |
| `examples/` | Learning-sequence examples — owned by `/examples` |
| `exemplar/` | Showcase project (Sudoku Solver) — owned by `/port` |
| `repl/` | REPL experience spec, demos, harness — owned by `/repl` |
| `tests/` | E2e suite — strategy/plan owned by `/qa`, test sources by `/testing` |
| `audits/` | Whole-context audit assessments — owned by `/audit` |
| `sprints/` | Delivery coordination — method, roadmap, current sprint, archive — owned by `/sprint` |

## Sketch Oracle (retired)

The prototype compiler that lived in `sketch/` was **deleted at the close of Sprint 87** (pre-Phase-H hygiene): language semantics are frozen, and the reimplementation's own references (`design/{crate}/`, `audits/`, `spec/`) long ago superseded it. If a spec ambiguity ever needs the original oracle's behaviour, recover the sketch from git history rather than treating it as a live reference. Historical mentions of the sketch throughout `design/`, `sprints/`, and `audits/` are an accurate record of past consultations.

> **Do not copy the sketch's pipeline structure** (relevant only if recovering it from history). The sketch had a dual-pipeline defect (`TopLevel`/`ReplInput` duplication); the v4 pipeline was designed independently. See `design/arch/archive/pipeline-convergence-review.md` for the historical analysis.

## Pipeline

The v4 scheduler-driven pipeline is the only pipeline. `CompilerSession` in `src/session_v4.rs` is the unified session type. `main.rs` uses one code path for Run/Link/REPL — REPL/`--run`/`--link` divergence is always a defect. See `design/arch/overview.md` and `design/int/CLAUDE.md` for the binary/integration layer.

## Active Skill Indicator

The Claude Code status bar shows the currently active skill. This is a **manual, single-session label** — useful when one terminal session is dedicated to a specific role. It does not track parallel subagents.

```bash
echo "/spec" > .claude-role   # set active skill for this session
rm .claude-role               # clear it
```

`.claude-role` is git-ignored and local only.

## Skills

14 Claude Code skills are available as slash commands (`.claude/commands/`). Roles, categories, and phase participation are normative in `sprints/METHOD.md` §1; **model/effort allocation per skill is normative in `sprints/artefacts.md` §II.3**.

| Command | Role |
|---|---|
| `/spec` | Language Specification Scribe — owns `spec/`; records settled semantics; brings every open normative question to the user, never rules |
| `/arch` | Compiler Architect — owns `design/arch/` + `crates/cranelisp-types/`; principles, bounded contexts, public-API approvals |
| `/qa` | QA Authority — test strategy, risk assessment, coverage process & traceability audit, defect attribution & cross-crate triage; owns `tests/plan/` |
| `/testing` | Test Developer — authors e2e tests, repro isolation & reduction, `// defect:` notation upkeep; owns test sources under `tests/` |
| `/audit` | Whole-Context Auditor — rolling per-sprint assessment of one bounded context's total state; owns `audits/` |
| `/design` | Per-crate triad, design role — narrow-deployed one crate per invocation; owns `design/{crate}/` |
| `/dev` | Per-crate triad, implementation role — narrow-deployed; code + unit tests |
| `/review` | Per-crate triad, review role — change-set review against design intent |
| `/sprint` | Sprint Manager — plans increments, waves, gates, dispatch; owns `sprints/` |
| `/stdlib` | Standard Library Developer — owns `stdlib/` |
| `/examples` | Example Developer — owns `examples/` |
| `/docs` | Documentation Owner — owns `user/` |
| `/repl` | REPL Experience Developer — owns `repl/` |
| `/port` | Exemplar Project Developer — owns `exemplar/` |

The former `/frontend`, `/typecheck`, `/backend`, `/int`, `/platform` skills were retired (collapsed into `/dev` narrow-deployment) and their command files deleted at increment A of `sprints/artefacts.md`; see git history.

## Delivery

Reimplementation phases A–G are complete; the project is in **Phase H (release compiler)**. The ring model that structured phases C–G was retired as a scheduling axis in Sprint 64 — sprint is the sole axis; `[R{N}]` annotations in older documents are historical. Current state and trajectory:

- `sprints/METHOD.md` — the delivery method (skills, seven sprint phases, FIXME protocol, artifacts)
- `sprints/ROADMAP.md` — sprint-by-sprint progress
- `sprints/SPRINT.md` — the active sprint plan (absent between sprints; archived to `sprints/archive/`)
- `sprints/artefacts.md` — agent artefact structure, model allocation, escalation, audit cycle (ratified 2026-07-11)
- `sprints/reimplementation.md` — the original strategy (historical reference)

`/arch` is the final arbiter of design decisions that cross crate boundaries. `/sprint` orchestrates; the user approves scope, sprint close, and all language-normative questions.

## Usability Findings and Defects

User-proxy skills (`/stdlib`, `/examples`, `/docs`, `/port`, `/repl`) routinely encounter problems while exercising the language. Two categories, different closure rules:

**Usability findings** — corner cases, unhelpful errors, inference friction, missing APIs, ergonomic issues. Filed as FIXME files in `design/arch/fixmes/` (see §Cross-Skill Changes). Documentation is sufficient closure.

**Defects** — real compiler bugs, spec violations, runtime crashes, REPL/`--run` divergences, output that does not match the spec. **A defect is not closed until `/testing` has committed a narrow test that reproduces it** — failing, un-ignored, with a `// spec:` annotation. The failing test is the durable record, the trigger for compiler-skill resolution, and the regression guard once fixed. A FIXME on a design doc captures intent but doesn't prove the issue exists, catch regression, or trigger CI; the failing test does all three. (A defect with a failing-not-ignored repro does NOT also need a numbered FIXME — the test is the record and the trigger.)

**Cross-skill defect handoff requires a minimal repro.** Error signatures alone — "unresolved symbol X", "SIGSEGV in Y" — routinely mask layered bugs: the visible error belongs to one skill, the underlying failure to another. Before `/sprint` spawns a cross-skill triage, the discovering skill MUST produce a minimal repro per `tests/CLAUDE.md` §"Isolating Cross-Crate Failures" — or request `/testing` to. Contested or repeatedly-wrong attribution escalates to `/qa` (fable-tier triage per `sprints/artefacts.md` §II.4). The handoff brief names the repro, not just the symptom.

**Reproduced defects join the test suite permanently, and small is the goal.** Every reduction — complete or partial — lands as a committed test. Small repros pay twice: the fix often becomes obvious during isolation (Sprint 59's prelude-parity bug was visible the moment the repro shrank to a single function), and small tests produce small CLIF — `/clif <name>` in the REPL or `CRANELISP_CODEGEN_TRACE=1` makes codegen-layer bugs (RC mis-count, missing load, bad relocation) visible in IR before source reduction finds them. Partial reductions commit with `// FIXME(/skill)` naming what is still unknown.

## Cross-Skill Changes

A skill MUST NOT silently edit a document owned by another skill. It files a FIXME as a numbered file — `design/arch/fixmes/NNNN-short-name.md` — and the owning skill evaluates, actions it in its own files, and **deletes the FIXME file**; git history is the audit trail. File format, frontmatter, and lifecycle are normative in `sprints/METHOD.md` §3.3. Filing is the ONE exception to file ownership (any skill may file targeting any other).

**Inline `FIXME(/skill)` comments are the OLD protocol** (superseded Sprint 63). Do not author new ones; `/sprint` migrates stragglers opportunistically.

**Wave gate**: before `/sprint` advances a wave, it scans `design/arch/fixmes/` for `target: /skill-in-wave` + `status: open`; any match blocks until resolved or explicitly deferred with rationale.

## Skill Handoff

Every skill plan ends with a **"Next skills"** section recommending what to invoke next. When a sprint is active, consult `sprints/SPRINT.md` for the task list and blocking dependencies; otherwise `sprints/ROADMAP.md`.

## Design Principles

- **Self-documenting REPL**: Every symbol and expression entered at the REPL should produce useful feedback — its type, value, or usage description. No valid language construct should produce an opaque error. Special forms, operators, and user-defined names should all respond with what they are and how to use them. Output reinforces the language syntax using `:Type value` notation with fully-qualified names (e.g. `:primitives/Int 3`, `:(Fn [a] a) user/id`). See `repl/spec.md` for the normative REPL experience specification.
- **Clojure standard library**: Follow the Clojure standard library for function naming and design as much as possible.
- **Optional prelude**: Nothing in the prelude is required for the language to work. An empty prelude is a valid starting point for the REPL or batch programs. The prelude provides convenience (traits, operators, types, macros) but the core language — primitives, special forms, type inference — works without it.
- **Stdlib separation**: Tests (`tests/`) and examples (`examples/`) MUST be free-standing — zero dependency on `stdlib/`. They define any needed helpers inline using compiler primitives and special forms. Only the exemplar (`exemplar/`) and production binary (`src/main.rs`) may depend on the standard library. This ensures the language itself is validated independently of any particular library code.

## Testing

- **Always use `cargo nextest run --no-fail-fast`** instead of `cargo test`. Nextest runs each test in its own process, parallelizes across binaries, and completes the full suite in **~60s** (post-build; a rebuild adds ~30–60s). `--no-fail-fast` is required for full-picture runs — the intentional defect guards (below) otherwise stop the run early. The suite includes every crate's lib tier via `[workspace] default-members` (S101). The alias `cargo nt` is also available via `.cargo/config.toml`.
- **Never run tests in background mode.** Wait for the run to complete before proceeding. Background test runs pile up and contend on build locks.
- **Three-minute timeout expectation.** The full suite is ~60s post-build. If a run exceeds ~3 minutes including build, something is wrong — kill it and investigate.
- **One agent, one test run.** When multiple agents are active, only the agent that owns source code changes should run tests. Other agents must not run tests concurrently.
- **Single agent at a time for source-touching work.** Worktree isolation is broken on this project, so parallel agents share one working tree. Two agents editing concurrently race on the git index and on the editor/linter — a subagent `git stash` or a mid-edit linter pass will silently clobber another agent's changes (observed Sprint 81: a parallel `/dev` fan-out corrupted the tree; recovery cost a full reconciliation). Read-only fan-outs (search, survey, design-planning that only returns text) may run in parallel; any agent that *edits source* runs serially.
- **Every fix lands with a unit test; assess the e2e need BEFORE writing the fix.** A **unit test is mandatory** for every fix — it pins the behaviour at the exact seam where the bug lived and is the fastest guard against a re-break. **Before** writing the fix, also assess whether an **e2e test** is warranted (add one when the bug is observable end-to-end or crosses `--run`/`--link`/REPL modes — unit and e2e answer different questions). Write the failing test(s) **first**; the fix flips them green; test(s) and fix land in the **same change-set**. A fix guarded only by an e2e — or only by "the suite still passes" — is incomplete, and deferring the test to a follow-up FIXME (the "test owed" anti-pattern) inverts the discipline and routinely never gets done. (Binding statement: `sprints/METHOD.md` §2.2.)
- **Failing-not-ignored defect repros**: the suite deliberately carries a small number of **known-defect guards** — failing, NOT `#[ignore]`'d — so each flips green when the owning skill fixes its defect. Hiding a spec violation behind `#[ignore]` is itself a defect. **Do not enumerate or count the guards here** — the set changes every sprint and is knowable from the live sources: run `cargo nextest run --no-fail-fast` to see the current REDs; each intentional guard traces to an open defect (FIXME or `// FIXME(/skill)` annotation) naming the owner. A **genuine regression** is any RED that does **not** trace to a known open defect that way. (Defect-repro history/analysis: the `// defect:` notation per `tests/CLAUDE.md` §"Defect-repro notation"; the former failure ledger `tests/plan/ledger.md` is retired — S108, tombstone only.)

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

- `repl/spec.md` — REPL experience spec (owned by `/repl`)
- `spec/*.md` — language spec files (owned by `/spec`)

When `/testing` writes a test, it adds the test-side `// spec:` comment. When coverage is verified, **`/qa` adds the spec-side `[Tested ...]` annotation directly** — the traceability annotation band (`[Tested …]`, `[Tested+Neg …]`, `[S{M}]`, `[… IGNORED]`) on `spec/*.md` and `repl/spec.md` is `/qa`'s to maintain, edited in place with **no FIXME cycle** to `/spec`/`/repl` (coverage status is `/qa`'s authority; a round-trip to flip a bracket tag is pure friction). Only the requirement *prose* around the annotations stays owner-gated. `/qa` audits the two-sided match as part of its coverage process.

**`[Done]` is retired.** It provided no traceability and was applied prematurely. All `[Done]` tags should be replaced with either `[Tested tests/file::test_name]` (if covered) or `[S{M}]` (if not).

## Known Issues

See `sprints/reimplementation.md` §"Risk Analysis" for known-issues disposition. (The former prototype's `sketch/KNOWN_ISSUES.md` and `sketch/audits/` were removed with the sketch at Sprint 87 close; recover from git history if needed.)
