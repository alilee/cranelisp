# design/typecheck/

Solution design documents for the Cranelisp typechecker (inference, traits, monomorphisation). Owned by `/design`, narrow-deployed to this crate.

## Purpose

These documents describe *how* the typechecker solves problems — algorithms, data structures, internal architecture, and trade-offs. They evolve alongside the implementation: sketched before coding, refined during, and updated when designs change.

This is distinct from:
- `design/arch/interfaces.md` — the *boundary contract* (what goes in and out)
- `spec/03-types.md`, `spec/07-traits.md` — the *language definition* (what behaviour is correct)

## What to Document

- **Inference engine**: Algorithm W implementation, unification, occurs check, substitution strategy
- **Constraint solving**: trait constraint propagation, constrained polymorphism detection
- **ADT type checking**: constructor inference, pattern exhaustiveness, type parameter instantiation
- **Monomorphisation**: specialisation collection, cross-module specialisation, cache interaction
- **Scope and environment**: scope stack design, variable resolution, module interaction
- **Design evolution**: what changed and why across sprints, and what was considered but rejected (per-sprint history lives in the docs themselves and `sprints/archive/`)

## Conventions

- One file per major subsystem (e.g., `inference.md`, `traits.md`, `monomorphisation.md`)
- Include typing rules in judgement notation where they clarify the algorithm
- Record rejected alternatives briefly — "considered X, chose Y because Z"
- Update docs when the implementation changes; stale design docs are worse than none
