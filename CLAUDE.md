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

> **Important** The sketch is a reference point only, not the destination. It's purpose is to de-risk the implementation by informing requirements, design decisions and technical risk assessments. At some point the sketch will be left behind and further development will be on the new system, so new work needs to stand on its own, start from a zero base and first principles - not copy the sketch.

> **Equally important** The sketch embodies hard-won design knowledge — solutions to problems that were discovered during prototyping. Before designing any subsystem, compiler skills MUST study the sketch's approach to the same problem, understand *why* it works that way, and explicitly decide whether to follow the same approach or diverge. Divergence is fine when justified (cleaner architecture, avoiding known sketch debts), but uninformed divergence — reimplementing from scratch without studying the sketch's solution — risks re-discovering problems the sketch already solved. Design docs MUST include a "Sketch comparison" section documenting: (a) how the sketch handles this, (b) whether the reimplementation follows or diverges, and (c) the rationale for divergence if any.

The prototype compiler lives in `sketch/`. Use it when the spec is ambiguous:

```bash
cd sketch && cargo run -- --run examples/hello.cl
cd sketch && cargo run                    # start REPL
cd sketch && just test                    # run all prototype tests
```

See `sketch/CLAUDE.md` for full oracle instructions and key file locations.

> **Do not copy the sketch's pipeline structure.** The sketch has a known dual-pipeline defect (`TopLevel`/`ReplInput` duplication, parallel batch/REPL code paths) that was listed in its own audit as a debt to avoid. Study the sketch's *solutions to language-level problems* (RC semantics, match field ownership, closure captures), but design the pipeline independently. See `design/arch/pipeline-convergence-review.md`.

## Pipeline Transition (Sprint 26)

The reimplementation is transitioning from a v1 pipeline (with known structural defects) to a unified v2 pipeline. All skills should be aware:

- **The pipeline is being unified.** Batch, REPL, and module-loading will share one code path with mode parameters — no parallel types, no parallel functions, no adapter layers.
- **v2 types** will be added to `cranelisp-types` alongside v1 types. Both coexist during transition.
- **`src/pipeline_v2.rs`** is the new orchestration entry point. `src/pipeline.rs` and `src/repl/` are being replaced. **Do not add features to the old pipeline.**
- **Tests run through both pipelines** during transition to verify identical behaviour.
- **v1 architecture docs** are in `design/arch/v1/` for reference. The active target architecture is in `design/arch/` (principles, convergence review, new `interfaces.md`).
- **Call graph** is a new cross-cutting data structure serving incremental recompilation, mutual recursion detection, and non-tail recursion warnings.

See `design/arch/pipeline-convergence-review.md` for the full defect analysis and convergence plan.

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

## Usability Findings

When user-proxy skills (`/stdlib`, `/examples`, `/docs`, `/port`, `/repl`, `/platform`) encounter corner cases, unhelpful errors, inference friction, missing APIs, or ergonomic issues, they file a `FIXME(/skill-name)` comment on the relevant spec, design, or plan document — the same cross-skill protocol described below. This keeps findings in context, discoverable by grep, and owned by the skill that can fix them.

## Cross-Skill Changes

When a skill discovers that an upstream document (owned by another skill) needs updating, it MUST NOT silently edit that document. Instead, add a `FIXME(/skill-name)` HTML comment at the relevant location in the upstream file, describing the issue and proposed resolution. The owning skill picks up the FIXME on its next invocation, evaluates it, and actions it.

```html
<!-- Example FIXME syntax (resolved FIXMEs are removed; see cross-skill protocol above) -->
```

This preserves ownership boundaries — each skill decides how to handle changes in its own files.

**Wave gate**: Before `/sprint` advances to the next wave, it MUST scan for unresolved FIXMEs in all files touched by the current wave. Outstanding FIXMEs addressed to a skill in the current wave block advancement — they must be resolved or explicitly deferred with rationale.

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
| `[R{N} S{M}]` | Not yet tested; targeted for Ring N, Sprint M |
| `[R{N} S{M} — tests/file::test_name IGNORED]` | Test exists but is `#[ignore]`'d (known gap) |

**Positive vs negative coverage.** `[Tested]` means the happy path works — the feature produces correct output for valid input. `[Tested+Neg]` means the test suite also verifies **what must NOT happen**: wrong items are absent, invalid input produces the right error, boundary violations are rejected. A spec section that says "MUST organize symbols into categories" needs positive tests (categories appear) AND negative tests (non-category items are absent, wrong-module items don't leak through). `[Tested]` without `+Neg` is a coverage gap — the feature works but nobody has verified it doesn't also do wrong things.

**Fine-grained annotations** go on individual table rows and MUST requirements — each row should have its own `[Tested ...]` or `[R{N} S{M}]` tag. This makes it possible to see at a glance which specific behaviors are covered and which are not.

**Section-level annotations** are summaries. A section heading says `[Tested]` only when ALL its sub-requirements have test annotations. A section heading says `[Tested+Neg]` only when ALL its sub-requirements have both positive and negative annotations. If any child is untested, the section heading carries the lowest coverage level of its children (e.g., `[R2 S8]` if any child targets Ring 2 Sprint 8).

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

**`[Done]` is retired.** It provided no traceability and was applied prematurely. All `[Done]` tags should be replaced with either `[Tested tests/file::test_name]` (if covered) or `[R{N} S{M}]` (if not).

## Known Issues

Prototype compromises are documented in `sketch/KNOWN_ISSUES.md`. See `sketch/audits/` for the full audit findings. See `sprints/reimplementation.md` §"Risk Analysis" for known issues disposition.
