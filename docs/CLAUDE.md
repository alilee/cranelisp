# docs/

Design documents in this directory describe architecture, rationale, and implementation notes for cranelisp subsystems.

## Spec vs Design Docs

- **`docs/spec/`** contains the **language specification** — a precise record of what the implemented language does. See `docs/spec/CLAUDE.md` for conventions.
- **Other files in `docs/`** (e.g. `architecture.md`, `adt.md`, `codegen.md`) are design documents: they describe how things work, why decisions were made, known limitations, and planned extensions.

When the spec and a design doc conflict, the spec reflects current behaviour; the design doc may describe intent or future direction.
