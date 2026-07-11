# design/frontend/

Solution design documents for the Cranelisp frontend (reader, macro expander, AST builder). Owned by `/design`, narrow-deployed to this crate.

## Purpose

These documents describe *how* the frontend solves problems — algorithms, data structures, internal architecture, and trade-offs. They evolve alongside the implementation: sketched before coding, refined during, and updated when designs change.

This is distinct from:
- `design/arch/interfaces.md` — the *boundary contract* (what goes in and out)
- `spec/` — the *language definition* (what behaviour is correct)

## What to Document

- **Reader internals**: PEG grammar structure, error recovery strategy, span threading
- **Macro expansion**: expansion algorithm, fixed-point iteration, hygiene approach, MacroExpander trait implementation
- **AST builder**: Sexp-to-Expr translation decisions, desugaring rules, validation passes
- **Design evolution**: what changed and why across sprints, and what was considered but rejected (per-sprint history lives in the docs themselves and `sprints/archive/`)

## Conventions

- One file per major subsystem (e.g., `reader.md`, `macro-expansion.md`, `ast-builder.md`)
- Include diagrams (ASCII) for non-obvious data flow
- Record rejected alternatives briefly — "considered X, chose Y because Z"
- Update docs when the implementation changes; stale design docs are worse than none
