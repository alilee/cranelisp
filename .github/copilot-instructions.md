# Copilot Instructions for Cranelisp

## First Steps

Before doing any work, find all `CLAUDE.md` files in the project:

```
glob **/CLAUDE.md
```

Before doing work in any directory, read all `CLAUDE.md` files in that directory and every parent directory up to the project root. Local `CLAUDE.md` files contain conventions and context specific to nearby files.

## Project Context

This repository contains the Cranelisp compiler — a statically typed Lisp targeting Cranelift. The project uses a skill-based development model with 15 specialized roles coordinated through sprint planning.

Key directories:
- `spec/` — Language specification
- `design/` — Architecture and implementation design
- `src/` — Compiler source
- `stdlib/` — Standard library in Cranelisp
- `tests/` — Test suite
- `examples/` — Learning-sequence examples
- `sketch/` — Prototype compiler (reference oracle, not active)

## CLAUDE.md Hierarchy

Each directory may have a `CLAUDE.md` with local conventions relevant for nearby files. 

Always read all files in the hierarchy from root to the working directory before working on files in that location.

## Key Conventions

1. **Minimal changes** — Make surgical, precise edits; don't refactor unrelated code
2. **Cross-skill FIXME protocol** — Use `<!-- FIXME(/skill-name): description -->` for changes to files owned by other skills
3. **Spec traceability** — Tests reference spec sections with `// spec:` comments
4. **Stdlib separation** — Tests and examples must be free-standing, no stdlib dependency
