# design/arch/

Architecture deliverables for the Cranelisp reimplementation. Owned and maintained by the `/arch` skill.

## Files (to be created by /arch)

- `interfaces.md` — Rust type definitions for all pipeline boundary types with field-level documentation
- `modules.md` — Crate decomposition with dependency DAG (enforced via Cargo)
- `data-flow.md` — Data transformations at each pipeline stage

## Conventions

- Interface types define the contract between pipeline stages; changes require `/arch` review
- Any compiler skill that needs an interface change proposes it here; `/arch` evaluates impact and updates
- Dependency graph must be acyclic — no circular crate dependencies
