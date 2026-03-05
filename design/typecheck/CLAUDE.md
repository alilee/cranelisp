# design/typecheck/

Solution design documents for the Cranelisp typechecker (inference, traits, monomorphisation). Owned by the `/typecheck` skill.

## Purpose

These documents describe *how* the typechecker solves problems — algorithms, data structures, internal architecture, and trade-offs. They evolve alongside the implementation: sketched before coding, refined during, and updated when designs change.

This is distinct from:
- `design/arch/interfaces.md` — the *boundary contract* (what goes in and out)
- `spec/03-types.md`, `spec/07-traits.md` — the *language definition* (what behaviour is correct)
- `sketch/docs/` — the *prototype rationale* (how the prototype did it, for reference)

## What to Document

- **Inference engine**: Algorithm W implementation, unification, occurs check, substitution strategy
- **Constraint solving**: trait constraint propagation, constrained polymorphism detection
- **ADT type checking**: constructor inference, pattern exhaustiveness, type parameter instantiation
- **Monomorphisation**: specialisation collection, cross-module specialisation, cache interaction
- **Scope and environment**: scope stack design, variable resolution, module interaction
- **Per-ring evolution**: what changes at each ring, why, and what was considered but rejected

## Conventions

- One file per major subsystem (e.g., `inference.md`, `traits.md`, `monomorphisation.md`)
- Include typing rules in judgement notation where they clarify the algorithm
- Record rejected alternatives briefly — "considered X, chose Y because Z"
- Update docs when the implementation changes; stale design docs are worse than none
