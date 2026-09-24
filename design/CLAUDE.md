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
| `platform/` | `/design` (platform) | Host/DLL C-ABI contract, DLL authoring and loading, poll-leaf and ADT-marshalling design |
| `int/` | `/design` (int) | Binary/integration layer — pipeline orchestration, REPL session, CLI, `--link` |
| `review/` | `/review` | Standing change-set cues extending the review standard |
| `runtime/` | `/design` (runtime-pair contract; one nominated crate pass owns each edit) | Shared `cranelisp-primitives` ↔ `cranelisp-intrinsics` ownership/ABI contracts. A sprint reserves each shared file to one crate pass so both sides do not rewrite it. |

## Governing memories and document collections

The existing context memories are [arch](arch/CLAUDE.md),
[frontend](frontend/CLAUDE.md), [typecheck](typecheck/CLAUDE.md),
[backend](backend/CLAUDE.md), [intrinsics](intrinsics/CLAUDE.md),
[platform](platform/CLAUDE.md), [int](int/CLAUDE.md), and
[review](review/CLAUDE.md). They establish their local products and collections.
This memory directly governs the primitives and runtime design
collections below, which have no separate local memory.

| Collection | Purpose | Boundary |
|---|---|---|
| `primitives-designs` | Primitives interior designs and implementation dispositions. | `primitives/*.md`; owned by `/design` (primitives). |
| `runtime-pair-designs` | Shared primitives/intrinsics ownership and ABI contracts with their retained design evidence. | `runtime/*.md`; one nominated `/design` writer per file. |

These are maintained design collections, not historical-reference exemptions.
Individual status continues to distinguish adopted contracts, proposals and
retained evidence; collection membership does not approve a proposal or excuse
a stale live reference.

## Design-doc expectations

Per-crate design docs describe *how* a surface solves problems — algorithms, data structures, internal architecture, trade-offs. They are distinct from `design/arch/interfaces.md` (cross-crate boundary contracts) and `spec/` (correct behaviour). A design doc is created or updated as part of the design phase for each surface; see each subdirectory's `CLAUDE.md`.

The content split (skill definition vs design doc vs `CLAUDE.md`) is normative in `sprints/METHOD.md` §1.2.

## Architecture and delivery

`design/arch/overview.md` introduces the current architecture; `design/arch/bounded-contexts.md` defines context ownership and boundaries. `sprints/METHOD.md` governs delivery, and `sprints/ROADMAP.md` tracks progress under `/sprint` ownership.
