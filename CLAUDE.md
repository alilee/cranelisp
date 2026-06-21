# Cranelisp

## First Steps

Before doing any work, find all `CLAUDE.md` files in the project:

```
glob **/CLAUDE.md
```

Before doing work in any directory, read all `CLAUDE.md` files in that directory and every parent directory up to the project root. Local `CLAUDE.md` files contain conventions and context specific to nearby files.

## Project Layout

This repository is organized for the Cranelisp reimplementation:

| Directory | Purpose |
|---|---|
| `spec/` | Language specification (16 files) — owned by `/spec` skill |
| `design/` | Architecture and implementation design — owned by `/arch` skill |
| `user/` | User-facing documentation (tutorials, guide) — owned by `/docs` skill |
| `src/` | New compiler source (to be created by `/arch`) |
| `stdlib/` | Standard library in Cranelisp — owned by `/stdlib` |
| `examples/` | Learning-sequence examples — owned by `/examples` skill |
| `exemplar/` | Showcase project (Sudoku Solver) — owned by `/port` skill |
| `tests/` | Reimplementation test suite (to be created by `/qa`) |
| `sprints/` | Delivery coordination — roadmap, current sprint, archive — owned by `/sprint` skill |

## Sketch Oracle (retired)

The prototype compiler that lived in `sketch/` was **deleted at the close of Sprint 87** (pre-Phase-H hygiene): Phases A–G are complete, language semantics are frozen, and the reimplementation has its own working references (`design/{crate}/`, `design/arch/facades/`, `audits/`, `spec/`) that long ago superseded it. If a spec ambiguity ever needs the original oracle's behaviour, recover the sketch from git history (it predates this deletion commit) rather than treating it as a live reference. Historical mentions of the sketch throughout `design/`, `sprints/`, and `audits/` are an accurate record of past consultations and are left intact.

> **Do not copy the sketch's pipeline structure** (relevant only if recovering it from history). The sketch had a dual-pipeline defect (`TopLevel`/`ReplInput` duplication); the v4 pipeline was designed independently. See `design/arch/archive/pipeline-convergence-review.md` for the historical analysis.

## Pipeline

The v4 scheduler-driven pipeline is the only pipeline. `CompilerSession` in `session_v4.rs` is the unified session type. `main.rs` uses one code path for Run/Link/REPL. See `design/arch/pipeline-v4.md` for the target design and `design/arch/pipeline-v4-roadmap.md` for current status.

## Active Skill Indicator

The Claude Code status bar shows the currently active skill. This is a **manual, single-session label** — useful when one terminal session is dedicated to a specific role. It does not track parallel subagents (which run concurrently and would race on the file).

```bash
echo "/spec" > .claude-role   # set active skill for this session
rm .claude-role               # clear it
```

For parallel subagent work, use terminal tabs or tmux panes — one per agent — rather than relying on this file. `.claude-role` is git-ignored and local only.

## Skills

15 Claude Code skills are available as slash commands (`.claude/commands/`). Each skill sets a role for the session:

| Command | Role |
|---|---|
| `/spec` | Language Specification Owner — owns `spec/`, arbitrates ambiguity |
| `/arch` | Compiler Architect — owns `design/arch/`, interface types, crate structure |
| `/frontend` | Frontend Developer — reader, macro expander, AST builder |
| `/typecheck` | Typechecker Developer — Algorithm W, traits, monomorphisation |
| `/backend` | Backend Developer — Cranelift IR, JIT, RC, caching, linking |
| `/int` | Integration Developer — owns `src/`, pipeline orchestration, REPL session, slash commands, prelude loading, CLI |
| `/qa` | Quality Assurance — test suite, spec conformance, coverage analysis |
| `/review` | Code Reviewer — code quality, prevents structural debts |
| `/sprint` | Sprint Manager — plans increments, coordinates skill execution, tracks delivery |
| `/stdlib` | Standard Library Developer — owns `stdlib/` |
| `/examples` | Example Developer — builds learning-sequence `examples/` |
| `/platform` | Platform Developer — `cranelisp-platform/`, `cranelisp-runtime/`, DLLs |
| `/docs` | Documentation Owner — owns `user/` |
| `/repl` | REPL Experience Developer — owns REPL experience spec, test scripts, and harness |
| `/port` | Exemplar Project Developer — ports a showcase project to validate the language at scale |

## Reimplementation Strategy

See `sprints/reimplementation.md` for the full strategy:
- **Ring model**: 5 rings (core → heap → abstraction → meta → effects)
- **Phase sequence**: A (extract) → B (scaffold) → C–G (rings 0–4) → H (release compiler)
- **Parallel work**: compiler skills work in parallel within each ring
- **User-proxy skills**: `/stdlib`, `/examples`, `/platform`, `/docs` validate from user perspective
- **Sprint coordination**: `/sprint` decomposes rings into delivery increments; `sprints/ROADMAP.md` tracks progress, `sprints/SPRINT.md` contains the current sprint plan. All skills participate in every sprint — later-stage skills do planning and validation work until their implementation phase begins.
- **Architectural authority**: `/arch` is the final arbiter of design decisions that cross crate or skill boundaries. See `design/arch/CLAUDE.md` for the principles that guide these decisions.

## Usability Findings and Defects

User-proxy skills (`/stdlib`, `/examples`, `/docs`, `/port`, `/repl`, `/platform`) routinely encounter problems while exercising the language. There are two distinct categories with different handling:

**Usability findings** — corner cases, unhelpful errors, inference friction, missing APIs, ergonomic issues. These are filed as `FIXME(/skill-name)` comments on the relevant spec, design, or plan document — the cross-skill protocol described below. Documentation is sufficient closure.

**Defects** — real compiler bugs, spec violations, runtime crashes, REPL/`--run` divergences, output that does not match the spec. **A user-proxy skill's work is not finished until `/qa` has authored a narrow integration test that reproduces the defect** — failing, un-ignored, with `// spec:` annotation and `FIXME(/owning-skill)` pointing to the resolver. Documentation alone is not closure for defects; the failing test is the durable record + the trigger for compiler-skill resolution. User-proxy skills feed defects to `/qa` for narrow reproduction; `/qa` writes the test; the owning compiler skill resolves it (this sprint or a future one).

**Cross-skill defect handoff also requires minimal repro.** The same rule applies when one compiler skill (e.g., `/int`, `/backend`, `/typecheck`) hands off a failing test to another compiler skill. Error signatures alone — "unresolved symbol X", "SIGSEGV in Y", "type error at Z" — routinely mask layered bugs: the visible error belongs to one skill; the underlying failure belongs to another, and fixing the visible one exposes the next. Before `/sprint` spawns a cross-compiler-skill triage, the skill that discovered the failure MUST produce a minimal repro following `tests/CLAUDE.md §"Isolating Cross-Crate Failures"` — or request `/qa` to do so. The handoff brief names the repro, not just the symptom. Skipping this step trades one 30-minute reduction for multiple hours of misdirected fix work across skills.

**Reproduced defects join the test suite permanently.** Every repro reduction — complete or partial — produces a committed test. Failing, un-ignored, per `memory/feedback_failing_not_ignored.md`. This applies equally whether the fix lands in the same sprint or the defect carries forward. Discarding narrowing work (the "these simpler shapes pass; this specific shape fails" reduction that was done in-session) forces the next sprint to redo it from scratch, and loses the regression guard once the bug is fixed. Partial reductions go in as much as was isolated, with `// FIXME(/skill)` naming what is still unknown.

**Keep reductions as small as possible — small tests aid debugging.** A small repro has two payoffs beyond being a regression guard: the fix may become obvious during isolation (Sprint 59: the 4-line prelude parity bug was visible the moment the repro shrank to a single-function prelude), and when source-level reduction plateaus, a small test produces small CLIF output that can be inspected by eye. Use `/clif <name>` in the REPL or `CRANELISP_CODEGEN_TRACE=1` during test runs to see the compiled IR for the shrunk repro. Codegen-layer bugs (RC mis-count, missing load, incorrect relocation) often become visible in CLIF before they become visible in source reduction.

The distinction matters because defects without failing tests get lost. A FIXME comment on a design doc captures intent but doesn't prove the issue exists, doesn't catch regression, and doesn't trigger CI. The failing test does all three.

## Cross-Skill Changes

When a skill discovers that an upstream document (owned by another skill) needs updating, it MUST NOT silently edit that document. Instead, file a FIXME as a numbered file in `design/arch/fixmes/NNNN-name.md`. The owning skill picks up the FIXME on its next invocation, evaluates it, actions it by editing its own files, and **deletes the FIXME file** with a commit message naming what was resolved. Git history is the audit trail.

**File format** (per `sprints/METHOD.md` §3.3):

```yaml
---
number: NNNN              # unique sequential — scan design/arch/fixmes/ for max+1
target: /skill-name       # the owning skill that resolves
filed_by: /skill-name     # the skill that filed
filed_at: YYYY-MM-DD
sprint_filed: NN
refers_to: path/to/file.md §section, path/to/other.md   # specific anchors
status: open
---

# Title — what needs to change

## Issue
...

## Proposed resolution
...

## Operational implication / Context
...
```

Naming: `design/arch/fixmes/NNNN-short-name.md`. Filing skill scans for `max + 1`; `/sprint` resolves rare collisions at wave gate.

**Inline `FIXME(/skill)` HTML comments are the OLD protocol.** They were superseded in Sprint 63 (M7 — methodology pivot). Pre-S63 inline FIXMEs still scatter the project and are migrated by `/sprint` opportunistically. **Do not author new inline FIXMEs.** All new cross-skill change requests file as `design/arch/fixmes/NNNN-name.md`.

This preserves ownership boundaries — each skill decides how to handle changes in its own files. Filing a FIXME is the ONE exception to file ownership (any skill may file targeting any other skill); editing in response remains the owning skill's prerogative.

**Wave gate**: Before `/sprint` advances to the next wave, it scans `design/arch/fixmes/` for `target: /skill-in-wave` and `status: open`. Outstanding FIXMEs targeting a wave's skill block advancement — they must be resolved or explicitly deferred with rationale.

## Skill Handoff

Every skill plan must end with a **"Next skills"** section recommending which skill(s) the user should invoke next after the plan is implemented. When a sprint is active, consult `sprints/SPRINT.md` for the current task list and blocking dependencies. Otherwise consult `design/arch/roadmap.md` for dependencies. Example:

```
## Next skills

- `/typecheck` — Ring 0 core inference can now begin against the types defined here
- `/backend` — Ring 0 codegen can begin in parallel with typecheck
```

## Design Principles

- **Self-documenting REPL**: Every symbol and expression entered at the REPL should produce useful feedback — its type, value, or usage description. No valid language construct should produce an opaque error. Special forms, operators, and user-defined names should all respond with what they are and how to use them. Output reinforces the language syntax using `:Type value` notation with fully-qualified names (e.g. `:primitives/Int 3`, `:(Fn [a] a) user/id`). See `repl/spec.md` for the normative REPL experience specification.
- **Clojure standard library**: Follow the Clojure standard library for function naming and design as much as possible.
- **Optional prelude**: Nothing in the prelude is required for the language to work. An empty prelude is a valid starting point for the REPL or batch programs. The prelude provides convenience (traits, operators, types, macros) but the core language — primitives, special forms, type inference — works without it.
- **Stdlib separation**: Tests (`tests/`) and examples (`examples/`) MUST be free-standing — zero dependency on `stdlib/`. They define any needed helpers inline using compiler primitives and special forms. Only the exemplar (`exemplar/`) and production binary (`src/main.rs`) may depend on the standard library. This ensures the language itself is validated independently of any particular library code.

## Testing

- **Always use `cargo nextest run`** instead of `cargo test`. Nextest runs each test in its own process, parallelizes across binaries, and completes the full suite in ~9s. The alias `cargo nt` is also available via `.cargo/config.toml`.
- **Never run tests in background mode.** Wait for the run to complete before proceeding. Background test runs pile up and contend on build locks.
- **30-second timeout expectation.** If a test run exceeds 30s, something is wrong — kill it and investigate.
- **One agent, one test run.** When multiple agents are active, only the agent that owns source code changes should run tests. Other agents must not run tests concurrently.
- **Single agent at a time for source-touching work.** Worktree isolation is broken on this project, so parallel agents share one working tree. Two agents editing concurrently race on the git index and on the editor/linter — a subagent `git stash` or a mid-edit linter pass will silently clobber another agent's changes (observed Sprint 81: a parallel `/dev` fan-out corrupted the tree; recovery cost a full reconciliation). Read-only fan-outs (search, survey, design-planning that only returns text) may run in parallel; any agent that *edits source* runs serially.
- **Every fix lands with a unit test; assess the e2e need BEFORE writing the fix.** A **unit test is mandatory** for every fix — it pins the behaviour at the exact seam where the bug lived and is the fastest guard against a re-break. **Before** writing the fix, also assess whether an **integration/e2e test** is warranted (add one when the bug is observable end-to-end or crosses `--run`/`--link`/REPL modes — unit and e2e answer different questions). Write the failing test(s) **first**; the fix flips them green; test(s) and fix land in the **same change-set**. A fix guarded only by an e2e — or only by "the suite still passes" — is incomplete, and deferring the test to a follow-up FIXME (the "test owed" anti-pattern) inverts the discipline and routinely never gets done. See `memory/feedback_unit_test_per_fix.md`.
- **Pre-existing failures**: 11 sketch_port + 2 v4_platform tests fail. These are known and pre-date current work.
- **Failing-not-ignored defect repros (S81 close)**: the canonical `cargo nextest run` carries **14 intentional failing tests** — narrow repros for 7 Phase-6-surfaced defects (`0337` multi-file/sibling module resolution, `0338` REPL `/info`·`/sig`·bare-`trace` self-doc, `0340` `(trace …)` degenerate output, `0341` stacked-annotation parse, `0342` `super` import resolution, `0343` `(mod …)` source-regen corruption, `0344` fold-accumulator over-unification), plus **2 unit-tier** repros (`0341` in `cranelisp-frontend` → 1 red under `-p`; `0344` in `cranelisp-typecheck` → 1 red under `-p`). These are **known-defect guards, not regressions** — un-ignored per `memory/feedback_failing_not_ignored.md` so they flip green when the owning skill fixes each defect. Durable record: `tests/plan/ledger.md` (S81-close entry). A genuine regression is any RED **beyond** these named guards.

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

> The ring axis was retired as a project-wide planning/scheduling axis in Sprint 64 — sprint is the sole scheduling axis. Pre-S64 `[R{N} S{M}]` annotations in archived docs and older spec/test rows are historical; read `R{N}` as "the ring this targeted under the old model" and `S{M}` as the sprint. New annotations use sprint-only `[S{M}]`.

**Positive vs negative coverage.** `[Tested]` means the happy path works — the feature produces correct output for valid input. `[Tested+Neg]` means the test suite also verifies **what must NOT happen**: wrong items are absent, invalid input produces the right error, boundary violations are rejected. A spec section that says "MUST organize symbols into categories" needs positive tests (categories appear) AND negative tests (non-category items are absent, wrong-module items don't leak through). `[Tested]` without `+Neg` is a coverage gap — the feature works but nobody has verified it doesn't also do wrong things.

**Fine-grained annotations** go on individual table rows and MUST requirements — each row should have its own `[Tested ...]` or `[S{M}]` tag. This makes it possible to see at a glance which specific behaviors are covered and which are not.

**Section-level annotations** are summaries. A section heading says `[Tested]` only when ALL its sub-requirements have test annotations. A section heading says `[Tested+Neg]` only when ALL its sub-requirements have both positive and negative annotations. If any child is untested, the section heading carries the lowest coverage level of its children (e.g., `[S8]` if any child is scheduled for sprint 8).

**Test-side tracing**: Every test function has a `// spec:` comment naming the spec section it validates:
```rust
// spec: repl/spec.md §1.2 — Int display format
#[test]
fn display_int_result() { ... }
```

### Applying Annotations

- `repl/spec.md` — REPL experience spec (owned by `/repl`)
- `spec/*.md` — language spec files (owned by `/spec`)

When `/qa` writes a test, it adds the test-side `// spec:` comment. When coverage is verified, the spec-side `[Tested ...]` annotation is added. The two sides cross-reference each other.

**`[Done]` is retired.** It provided no traceability and was applied prematurely. All `[Done]` tags should be replaced with either `[Tested tests/file::test_name]` (if covered) or `[S{M}]` (if not).

## Known Issues

See `sprints/reimplementation.md` §"Risk Analysis" for known-issues disposition. (The former prototype's `sketch/KNOWN_ISSUES.md` and `sketch/audits/` were removed with the sketch at Sprint 87 close; recover from git history if needed.)
