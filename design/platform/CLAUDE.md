# design/platform/

Solution design documents for the Cranelisp platform layer (runtime, platform abstraction, DLL system). Owned by the `/platform` skill.

## Purpose

These documents describe *how* the platform layer solves problems — allocator design, RC primitive implementation, platform abstraction strategy, and trade-offs. They evolve alongside the implementation: sketched before coding, refined during, and updated when designs change.

This is distinct from:
- `design/arch/interfaces.md` — the *boundary contract* (what goes in and out)
- `spec/10-io.md`, `spec/12-runtime.md` — the *language definition* (what runtime behaviour is correct)
- `sketch/docs/` — the *prototype rationale* (how the prototype did it, for reference)

## What to Document

- **Allocator**: allocation strategy, header layout implementation, alignment, tracking (`LIVE_ALLOCS`)
- **RC primitives**: atomic operations, trace mode (`CRANELISP_RC_TRACE`), debug assertions
- **String runtime**: `HeapString` implementation, intern strategy (if any), rope preparation
- **Platform abstraction**: DLL interface, platform trait design, IO dispatch
- **Per-ring evolution**: what changes at each ring, why, and what was considered but rejected

## Conventions

- One file per major subsystem (e.g., `allocator.md`, `string-runtime.md`, `platform-dll.md`)
- Include memory layout diagrams (ASCII) for heap structures
- Record rejected alternatives briefly — "considered X, chose Y because Z"
- Update docs when the implementation changes; stale design docs are worse than none
