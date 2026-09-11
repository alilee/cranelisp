# design/backend/

Solution design documents for the Cranelisp backend (Cranelift codegen, JIT, RC, heap management). Owned by `/design`, narrow-deployed to this crate.

Current selected delivery delta: `s122-closure.md`. Its result-root and Vec-guard
convergence, typed closure-fixture adaptation, Q4 macro returned-alias correction
and module evidence are delivered and independently reviewed. The Q5 matched
comparison and generated runtime API baseline are confirmed; final integrated
Phase-5 acceptance remains open.
`s121-c4-visit.md` remains the broader preceding design record.

## Purpose

These documents describe *how* the backend solves problems — IR generation patterns, heap management strategy, RC implementation, and trade-offs. They evolve alongside the implementation: sketched before coding, refined during, and updated when designs change.

This is distinct from:
- `design/arch/interfaces.md` — the *boundary contract* (what goes in and out)
- `spec/12-runtime.md` — the *language definition* (what runtime behaviour is correct)

## Document collections

This memory establishes two backend-owned collections:

| Collection | Purpose | Boundary |
|---|---|---|
| `backend-current-designs` | Current backend interior designs and retained live design evidence for Cranelift code generation, RC, heap management, JIT lifecycle, caching and linking. | The named Markdown products directly under `design/backend/`, excluding this memory. |
| `backend-archive-records` | Frozen backend incident-debug records retained where they remain the canonical reproduction context and are not duplicated by current documents. | Markdown products under `design/backend/archive/`. |

Both are established collections and retain live reference checking. Individual
document status still determines whether a record is authoritative, partially
superseded or historical; collection membership does not promote old content to
current design.

## What to Document

- **Cranelift IR patterns**: how each Expr variant compiles to CLIF, builder idioms, block layout
- **Heap management**: allocation strategy, RC inc/dec emission, drop glue generation, last-use analysis
- **String codegen**: extern call patterns, string primitive dispatch
- **ADT codegen**: constructor allocation, field access, match compilation, tag discrimination
- **Closure codegen**: environment capture, calling convention implementation, side-table drop
- **Binding scope**: binder identity, the scope chain and its slots, the capture environment, per-binding-vector lenient state (`binding-scope.md`)
- **GOT and JIT**: function registration, GOT layout, relocation, caching
- **Design evolution**: what changed and why across sprints, and what was considered but rejected (per-sprint history lives in the docs themselves and `sprints/archive/`)

## Conventions

- One file per major subsystem (e.g., `heap-rc.md`, `closure-codegen.md`, `match-compilation.md`)
- Include CLIF IR examples for non-obvious compilation patterns
- Record rejected alternatives briefly — "considered X, chose Y because Z"
- Update docs when the implementation changes; stale design docs are worse than none
- Retain one canonical home for each design fact. Keep an archive record only
  when it remains the canonical source of distinct reproduction context or
  rationale; otherwise fold any still-useful content into a current document
  in current form and delete the duplicate. Git preserves deleted history.
