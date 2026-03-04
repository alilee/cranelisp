# design/

Architecture and implementation design documents for the Cranelisp reimplementation. Owned by the `/arch` skill.

## Files

- `reimplementation.md` — Full reimplementation strategy: skill definitions, ring model, phase sequence, risk analysis, success criteria. **Start here.**
- `arch/` — Architecture deliverables from the `/arch` skill

## design/arch/ (owned by /arch)

- `arch/architecture.md` — Overall architecture: 7-crate DAG, single pipeline principle, CompiledModule decomposition, audit findings resolution
- `arch/interfaces.md` — Boundary type definitions with Rust signatures (Sexp, Expr, Type, CheckResult, etc.)
- `arch/roadmap.md` — Ring-by-ring phased progression roadmap with per-skill deliverables and acceptance criteria

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

**Phase B (completed)**:
1. Created `design/arch/architecture.md` — crate DAG, pipeline design, audit resolution
2. Created `design/arch/interfaces.md` — all boundary type definitions
3. Created `design/arch/roadmap.md` — ring-by-ring progression plan
4. Created root `Cargo.toml` workspace with 7 member crates
5. Created `src/CLAUDE.md` with cross-cutting source conventions
6. Updated `sprints/reimplementation.md` — replaced options analysis with ring model decision
7. Updated `design/arch/CLAUDE.md` with cross-references and session decisions
