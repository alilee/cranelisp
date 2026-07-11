# design/

Architecture and per-crate implementation design for Cranelisp.

## Ownership model

Two owners divide this tree:

- **`design/arch/`** — owned by `/arch` (Compiler Architect): principles, bounded contexts, cross-crate interfaces, the newcomer overview, sequence diagrams. See `design/arch/CLAUDE.md`.
- **`design/{crate}/`** — owned by `/design`, the per-crate triad design role. `/design` is **narrow-deployed to one crate-shaped surface per invocation**; each subdirectory holds that surface's interior design (algorithms, data structures, trade-offs) below the level of the arch overview.

The former `/frontend`, `/typecheck`, `/backend`, `/platform` skills were retired and collapsed into `/design` narrow-deployment; they are historical.

## Subdirectories

| Directory | Owner | Content |
|---|---|---|
| `arch/` | `/arch` | Architecture: principles, bounded contexts, cross-crate interfaces, overview, sequence diagrams |
| `frontend/` | `/design` (frontend) | Reader, parser, macro expansion design |
| `typecheck/` | `/design` (typecheck) | HM inference, traits, monomorphisation design |
| `backend/` | `/design` (backend) | Cranelift codegen, RC, JIT lifecycle, caching, linking design |
| `primitives/` | `/design` (primitives) | Static primitive `SymbolTable` + GOT design (D43 split) |
| `intrinsics/` | `/design` (intrinsics) | Drop glue, RC/alloc, IO reactor, intrinsic helpers design (D43 split) |
| `platform/` | `/design` (platform) | DLL loading, IO trampoline, scheduling-class registry design |
| `int/` | `/design` (int) | Binary/integration layer — pipeline orchestration, REPL session, CLI, `--link` |
| `review/` | `/review` | Review checklists, ring-completion reports, code-quality standards |
| `runtime/` | — historical | Pre-D43 `cranelisp-runtime` design; superseded by `primitives/` + `intrinsics/` |
| `stdlib/` | `/stdlib` | Stdlib design records (e.g. examples `--run` path remediation) |

## Design-doc expectations

Per-crate design docs describe *how* a surface solves problems — algorithms, data structures, internal architecture, trade-offs. They are distinct from `design/arch/interfaces.md` (cross-crate boundary contracts) and `spec/` (correct behaviour). A design doc is created or updated as part of the design phase for each surface; see each subdirectory's `CLAUDE.md`.

The content split (skill definition vs design doc vs `CLAUDE.md`) is normative in `sprints/METHOD.md` §1.4.

## Historical reference

`sprints/reimplementation.md` records the original reimplementation strategy (historical). Delivery progress is tracked in `sprints/ROADMAP.md`, owned by `/sprint`.
