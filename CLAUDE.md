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
| `examples/` | Learning-sequence examples (to be created by `/examples`) |
| `tests/` | Reimplementation test suite (to be created by `/qa`) |

## Sketch Oracle

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

13 Claude Code skills are available as slash commands (`.claude/commands/`). Each skill sets a role for the session:

| Command | Role |
|---|---|
| `/spec` | Language Specification Owner — owns `spec/`, arbitrates ambiguity |
| `/arch` | Compiler Architect — owns `design/arch/`, interface types, crate structure |
| `/frontend` | Frontend Developer — reader, macro expander, AST builder |
| `/typecheck` | Typechecker Developer — Algorithm W, traits, monomorphisation |
| `/backend` | Backend Developer — Cranelift IR, JIT, RC, caching, linking |
| `/qa` | Quality Assurance — pipeline wiring, test suite, REPL implementation |
| `/review` | Code Reviewer — code quality, prevents structural debts |
| `/stdlib` | Standard Library Developer — rebuilds `lib/` |
| `/examples` | Example Developer — builds learning-sequence `examples/` |
| `/platform` | Platform Developer — `cranelisp-platform/`, `cranelisp-runtime/`, DLLs |
| `/docs` | Documentation Owner — owns `user/` |
| `/repl` | REPL Experience Developer — owns REPL experience spec, test scripts, and harness |
| `/port` | Exemplar Project Developer — ports a showcase project to validate the language at scale |

## Reimplementation Strategy

See `design/reimplementation.md` for the full strategy:
- **Ring model**: 5 rings (core → heap → abstraction → meta → effects)
- **Phase sequence**: A (extract) → B (scaffold) → C–G (rings 0–4) → H (release compiler)
- **Parallel work**: compiler skills work in parallel within each ring
- **User-proxy skills**: `/stdlib`, `/examples`, `/platform`, `/docs` validate from user perspective
- **Architectural authority**: `/arch` is the final arbiter of design decisions that cross crate or skill boundaries. See `design/arch/CLAUDE.md` for the principles that guide these decisions.

## Skill Handoff

Every skill plan must end with a **"Next skills"** section recommending which skill(s) the user should invoke next after the plan is implemented. Consult `design/arch/roadmap.md` for dependencies. Example:

```
## Next skills

- `/typecheck` — Ring 0 core inference can now begin against the types defined here
- `/backend` — Ring 0 codegen can begin in parallel with typecheck
```

## Design Principles

- **Self-documenting REPL**: Every symbol and expression entered at the REPL should produce useful feedback — its type, value, or usage description. No valid language construct should produce an opaque error. Special forms, operators, builtins, and user-defined names should all respond with what they are and how to use them. Feedback should reinforce the language syntax, using cranelisp type notation (e.g. `pure :: special form: (fn [a] (IO a))`).
- **Clojure standard library**: Follow the Clojure standard library for function naming and design as much as possible.
- **Optional prelude**: Nothing in the prelude is required for the language to work. An empty prelude is a valid starting point for the REPL or batch programs. The prelude provides convenience (traits, operators, types, macros) but the core language — primitives, special forms, type inference — works without it.

## Git & Remote

- **Remote**: `origin` → `https://github.com/alilee/cranelisp`
- **History**: The remote uses an orphan commit (no prior history). When pushing, always force-push (`git push --force origin main`) since the local repo has a longer reflog that doesn't share ancestry with the remote.
- **Do not push without explicit user request.**

## Known Issues

Prototype compromises are documented in `sketch/KNOWN_ISSUES.md`. See `sketch/audits/` for the full audit findings. See `design/reimplementation.md` §"Risk Analysis" for known issues disposition.
