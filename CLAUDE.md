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
| `lib/` | Standard library in Cranelisp (to be created by `/stdlib`) |
| `examples/` | Learning-sequence examples — owned by `/examples` skill |
| `exemplar/` | Showcase project (Sudoku Solver) — owned by `/port` skill |
| `tests/` | Reimplementation test suite (to be created by `/qa`) |
| `sprints/` | Delivery coordination — roadmap, current sprint, archive — owned by `/sprint` skill |

## Sketch Oracle

We have a prototype compiler as a sketch. 

> **Important** The sketch is a reference point only, not the destination. It's purpose is to de-risk the implementation by informing requirements, design decisions and technical risk assessments. At some point the sketch will be left behind and further development will be on the new system, so new work needs to stand on its own, start from a zero base and first principles - not copy the sketch.     

The prototype compiler lives in `sketch/`. Use it when the spec is ambiguous:

```bash
cd sketch && cargo run -- --run examples/hello.cl
cd sketch && cargo run                    # start REPL
cd sketch && just test                    # run all prototype tests
```

See `sketch/CLAUDE.md` for full oracle instructions and key file locations.

## Active Skill Indicator

The Claude Code status bar shows the currently active skill. This is a **manual, single-session label** — useful when one terminal session is dedicated to a specific role. It does not track parallel subagents (which run concurrently and would race on the file).

```bash
echo "/spec" > .claude-role   # set active skill for this session
rm .claude-role               # clear it
```

For parallel subagent work, use terminal tabs or tmux panes — one per agent — rather than relying on this file. `.claude-role` is git-ignored and local only.

## Skills

14 Claude Code skills are available as slash commands (`.claude/commands/`). Each skill sets a role for the session:

| Command | Role |
|---|---|
| `/spec` | Language Specification Owner — owns `spec/`, arbitrates ambiguity |
| `/arch` | Compiler Architect — owns `design/arch/`, interface types, crate structure |
| `/frontend` | Frontend Developer — reader, macro expander, AST builder |
| `/typecheck` | Typechecker Developer — Algorithm W, traits, monomorphisation |
| `/backend` | Backend Developer — Cranelift IR, JIT, RC, caching, linking |
| `/qa` | Quality Assurance — pipeline wiring, test suite, REPL implementation |
| `/review` | Code Reviewer — code quality, prevents structural debts |
| `/sprint` | Sprint Manager — plans increments, coordinates skill execution, tracks delivery |
| `/stdlib` | Standard Library Developer — rebuilds `lib/` |
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
<!-- FIXME(/spec): Review whether Num trait declarations belong in language spec or stdlib. -->
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

## Git & Remote

- **Remote**: `origin` → `https://github.com/alilee/cranelisp`
- **History**: The remote uses an orphan commit (no prior history). When pushing, always force-push (`git push --force origin main`) since the local repo has a longer reflog that doesn't share ancestry with the remote.
- **Do not push without explicit user request.**

## Known Issues

Prototype compromises are documented in `sketch/KNOWN_ISSUES.md`. See `sketch/audits/` for the full audit findings. See `sprints/reimplementation.md` §"Risk Analysis" for known issues disposition.
