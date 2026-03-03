# design/

Architecture and implementation design documents for the Cranelisp reimplementation. Owned by the `/arch` skill.

## Files

- `reimplementation.md` — Full reimplementation strategy: skill definitions, ring model, phase sequence, risk analysis, success criteria. **Start here.**
- `arch/` — Architecture deliverables from the `/arch` skill (to be created)

## design/arch/ (owned by /arch)

The `/arch` skill creates:
- `arch/interfaces.md` — Boundary type definitions with Rust signatures (Sexp, Expr, Type, CheckResult, etc.)
- `arch/modules.md` — Crate dependency DAG and module decomposition
- `arch/data-flow.md` — Data transformations at each pipeline stage

## Legacy Design Docs

The sketch's 22 design documents live in `sketch/docs/`. Each compiler skill should consult the relevant sketch design doc for context and rationale, but the authoritative architecture for the reimplementation is in `design/arch/`.

Key sketch design docs by skill:
- `/frontend`: `sketch/docs/syntax.md`, `sketch/docs/macro.md`
- `/typecheck`: `sketch/docs/type-system.md`, `sketch/docs/traits.md`, `sketch/docs/adt.md`, `sketch/docs/constrained-polymorphism.md`
- `/backend`: `sketch/docs/codegen.md`, `sketch/docs/data-structures.md`, `sketch/docs/heap_layout.md`, `sketch/docs/closures.md`
- `/qa`: `sketch/docs/testing.md`
- `/stdlib`: `sketch/docs/modules.md`
- `/platform`: `sketch/docs/platform.md`, `sketch/docs/io.md`

## For the `/arch` skill

**First session (Phase B)**:
1. Read `design/reimplementation.md` §"Extract architecture contracts" + §"Delivery Strategy"
2. Read `sketch/audits/*.md` for structural problems to avoid
3. Create a root `Cargo.toml` workspace stub
4. Write `design/arch/interfaces.md` — define all boundary types
5. Write `design/arch/modules.md` — crate dependency DAG
6. Create `src/CLAUDE.md` with cross-cutting conventions
7. Write `design/arch/CLAUDE.md`
