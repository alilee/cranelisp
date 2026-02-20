# Cranelisp

## First Steps

Before doing any work, find all `CLAUDE.md` files in the project:

```
glob **/CLAUDE.md
```

Before doing work in any directory, read all `CLAUDE.md` files in that directory and every parent directory up to the project root. Local `CLAUDE.md` files contain conventions and context specific to nearby files.

## Commands

All build, test, and run commands are in the `justfile`. Use `just <recipe>`:

- `just build` — compile
- `just test` — run all tests
- `just run <file>` — run a `.cl` source file in batch mode (`--run`)
- `just hello` — run `examples/hello.cl` in batch mode
- `just factorial` — run `examples/factorial.cl` in batch mode
- `just check` — clippy
- `just fmt` — format

## Documentation

Design documents are in `docs/`:

- `docs/architecture.md` — pipeline overview, module responsibilities
- `docs/syntax.md` — S-expression grammar, special forms
- `docs/type-system.md` — Hindley-Milner inference, types
- `docs/codegen.md` — Cranelift IR mapping, JIT lifecycle, builtin FFI

Every plan should include a step to update the documents for completeness and accuracy, and to update the ROADMAP.md for progress.

Code quality audits are in `audits/`:

- `audits/CLAUDE.md` — audit process, prompt template, document structure conventions
- Per-module audit files (e.g., `audits/typechecker.md`) — findings, code examples, prioritized improvement plans

## Design Principles

- **Self-documenting REPL**: Every symbol and expression entered at the REPL should produce useful feedback — its type, value, or usage description. No valid language construct should produce an opaque error. Special forms, operators, builtins, and user-defined names should all respond with what they are and how to use them. Feedback should reinforce the language syntax, using cranelisp type notation (e.g. `pure :: special form: (fn [a] (IO a))`).
- **Clojure standard library**: Follow the Clojure standard library for function naming and design as much as possible.
- **Optional prelude**: Nothing in the prelude is required for the language to work. An empty prelude is a valid starting point for the REPL or batch programs. The prelude provides convenience (traits, operators, types, macros) but the core language — primitives, special forms, type inference — works without it.

## Known Issues

Compromises in implementation (e.g. lack of tail call optimisation or ommissions in shifting reference counts) which are decided upon or deemed too big to resolve at the current stage of development should be documented in the KNOWN_ISSUES.md file.
