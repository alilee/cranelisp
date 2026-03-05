# design/backend/

Solution design documents for the Cranelisp backend (Cranelift codegen, JIT, RC, heap management). Owned by the `/backend` skill.

## Purpose

These documents describe *how* the backend solves problems — IR generation patterns, heap management strategy, RC implementation, and trade-offs. They evolve alongside the implementation: sketched before coding, refined during, and updated when designs change.

This is distinct from:
- `design/arch/interfaces.md` — the *boundary contract* (what goes in and out)
- `spec/12-runtime.md` — the *language definition* (what runtime behaviour is correct)
- `sketch/docs/` — the *prototype rationale* (how the prototype did it, for reference)

## What to Document

- **Cranelift IR patterns**: how each Expr variant compiles to CLIF, builder idioms, block layout
- **Heap management**: allocation strategy, RC inc/dec emission, drop glue generation, last-use analysis
- **String codegen**: extern call patterns, string primitive dispatch
- **ADT codegen**: constructor allocation, field access, match compilation, tag discrimination
- **Closure codegen**: environment capture, calling convention implementation, side-table drop
- **GOT and JIT**: function registration, GOT layout, relocation, caching
- **Per-ring evolution**: what changes at each ring, why, and what was considered but rejected

## Conventions

- One file per major subsystem (e.g., `heap-rc.md`, `closure-codegen.md`, `match-compilation.md`)
- Include CLIF IR examples for non-obvious compilation patterns
- Record rejected alternatives briefly — "considered X, chose Y because Z"
- Update docs when the implementation changes; stale design docs are worse than none
