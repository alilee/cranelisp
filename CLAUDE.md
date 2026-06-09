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
| `sketch/` | Prototype compiler — reference oracle, not the active compiler |
| `src/` | New compiler source (to be created by `/arch`) |
| `stdlib/` | Standard library in Cranelisp — owned by `/stdlib` |
| `examples/` | Learning-sequence examples — owned by `/examples` skill |
| `exemplar/` | Showcase project (Sudoku Solver) — owned by `/port` skill |
| `tests/` | Reimplementation test suite (to be created by `/qa`) |
| `sprints/` | Delivery coordination — roadmap, current sprint, archive — owned by `/sprint` skill |

## Sketch Oracle

We have a prototype compiler as a sketch.

> **Important** The sketch is a reference point only, not the destination. Its purpose was to de-risk the reimplementation by informing requirements, design decisions, and technical risk assessments. The reimplementation has matured to the point where the sketch is no longer the default reference for design work — it is consulted **exceptionally**, not by default.

> **When to consult the sketch.** When debugging an unexplained behaviour or design dead-end where a known-working precedent might inform the next move; when the spec is ambiguous and the sketch's behaviour is the available oracle; when an audit, defect, or `/review` finding explicitly cites a sketch comparison as the resolution. *Not* as a routine pre-reading step before design or implementation work — the reimplementation has its own design docs (`design/{crate}/`), facades (`design/arch/facades/`), and audits (`audits/`) that supersede the sketch as the working reference.

> **If you do consult the sketch**, document the consultation in the design doc you're updating: what you looked at, what you took or rejected from it, and why. This keeps the consultation legible to future readers. A "Sketch comparison" section is not mandatory; include one only when the consultation was substantive.

> **First-principles default.** New design work stands on its own — starts from spec + facade + audit + bounded-context statement, not from the sketch. Uninformed divergence from the sketch was a real risk in early reimplementation; routine consultation was the mitigation. That phase is past for most subsystems. Re-engage the sketch when the working materials don't suffice — that is the exception, not the rule.

The prototype compiler lives in `sketch/`. Use it when the spec is ambiguous:

```bash
cd sketch && cargo run -- --run examples/hello.cl
cd sketch && cargo run                    # start REPL
cd sketch && just test                    # run all prototype tests
```

See `sketch/CLAUDE.md` for full oracle instructions and key file locations.

> **Do not copy the sketch's pipeline structure.** The sketch had a dual-pipeline defect (`TopLevel`/`ReplInput` duplication). Study the sketch's *solutions to language-level problems* (RC semantics, match field ownership, closure captures), but design the pipeline independently. See `design/arch/archive/pipeline-convergence-review.md` for the historical analysis.

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
- **Pre-existing failures**: 11 sketch_port + 2 v4_platform tests fail. These are known and pre-date current work.

## Git & Remote

- **Remote**: `origin` → `https://github.com/alilee/cranelisp`
- **History**: The remote uses an orphan commit (no prior history). When pushing, always force-push (`git push --force origin main`) since the local repo has a longer reflog that doesn't share ancestry with the remote.
- **Do not push without explicit user request.**

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

Prototype compromises are documented in `sketch/KNOWN_ISSUES.md`. See `sketch/audits/` for the full audit findings. See `sprints/reimplementation.md` §"Risk Analysis" for known issues disposition.
