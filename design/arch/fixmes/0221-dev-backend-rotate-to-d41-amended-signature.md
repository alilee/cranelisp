---
number: 0221
target: /dev (backend)
filed_by: /review
filed_at: 2026-05-26
sprint_filed: 70
refers_to: design/arch/decisions/0041-compile-to-module-per-symbol-jit-direct-writes.md §"S70 Phase B amendment", design/arch/facades/backend.md §"Free functions" (compile_to_module, produce_disasm) + §"Return shapes" (CompilationArtifacts), crates/cranelisp-backend/src/lib.rs, src/worker.rs (call sites)
status: open
---

# Rotate cranelisp-backend source to D41-amended signature (CompilationArtifacts + produce_disasm)

## Issue

Sprint 70 Phase B amended Decision 41 (commit `5e20405`) to retract D41 #3 (the `Introspection` direct-write commitment), resolving the DAG-inversion question surfaced by the Phase B configuration→source completeness sweep. The new canonical shape is:

```rust
pub fn compile_to_module<M: Module>(
    scope: &ModuleFullPath,
    names: &[Symbol],
    symbol_tables: &SymbolTables<Code, ()>,
    module_aliases: &ModuleAliases,
    module: M,
) -> Result<CompilationArtifacts, CompilationError>;

pub struct CompilationArtifacts {
    pub clif_ir: String,
    pub code_size: usize,
    pub compile_duration: std::time::Duration,
}

pub fn produce_disasm(
    fq: &FQSymbol,
    symbol_tables: &SymbolTables<Code, ()>,
) -> Result<String, CompilationError>;
```

D41 #1 (Code direct-write via `SymbolTable::write_code`) and #2 (GOT slot direct-write via `SymbolTable.got`) are preserved.

**Source state**: `crates/cranelisp-backend/` has not been rotated. The current `compile_to_module` signature returns whatever pre-S70 shape was in place (likely `Result<(), CompilationError>` per Decision 41 pre-amendment; verify on pickup). Backend source does not yet take `module_aliases` and does not yet return `CompilationArtifacts`.

D41 §"Operational implication" names this rotation as owed future-sprint work, parallel to typecheck/int wave-3 cascade work (FIXME 0222). This FIXME tracks the backend portion explicitly so it doesn't get lost.

## Proposed resolution

**Phase A — `cranelisp-backend` source** (`/dev (backend)` narrow):

1. Author `pub struct CompilationArtifacts { pub clif_ir: String, pub code_size: usize, pub compile_duration: Duration }` in `cranelisp-backend`. `#[non_exhaustive]` per Principle 18 + workspace DTO convention.
2. Rotate `compile_to_module` signature to match the canonical shape above. Capture `clif_ir` text during compile (Cranelift's `Function::display().to_string()` before the function is consumed by codegen). Wallclock `compile_duration` via `Instant::now()` at start. `code_size` is byproduct of finalization.
3. Author `pub fn produce_disasm(fq, symbol_tables) -> Result<String, _>`. Implementation: look up the function via `symbol_tables.get(scope)?.get(symbol)?` → `ModuleEntry::Def { kind: …, code: Some(Code::Jit { jit, ptr }), .. }`; read `code_size` (separate query or carry on the GOT slot); pass `ptr..ptr+code_size` to the chosen disassembler library.
4. Drop `introspection: Option<&DashMap<FQSymbol, Introspection>>` parameter from `compile_to_module`. Backend no longer names `Introspection`.
5. Backend's `Cargo.toml` no longer needs (or never had) `cranelisp-int`-shaped deps; verify clean.

**Phase B — `src/worker.rs` call sites** (`/dev (int)` narrow):

1. Update the per-symbol JIT loop to receive `CompilationArtifacts` from `compile_to_module`.
2. After each call, if `shared.introspection.is_some()`, compose `Introspection { source, sexp, expanded, ast, clif_ir: Some(artifacts.clif_ir), code_size: Some(artifacts.code_size), compile_duration: Some(artifacts.compile_duration), disasm: None }` and insert into the DashMap.
3. `/disasm <fn>` REPL handler (or equivalent) invokes `cranelisp_backend::produce_disasm(&fq, &shared.symbol_tables)?` lazily; updates the per-symbol Introspection entry's `disasm` field.

**Sequencing**: Phase A can land in isolation; Phase B follows. They can also land together if scope is tight. Bundle with FIXME 0222 (typecheck cascade) if backend-and-typecheck are picked up together.

## Operational implication / Context

Without this rotation, backend's facade target-states a signature that source does not match — same drift class that the Phase B audit was scoped to close for frontend. Backend's S71+ sprint should pick this up alongside any concurrent cascade work touching the JIT compilation path. The S70 frontend cascade does NOT depend on this rotation (frontend's `expand` does not take `Introspection`); the typecheck wave-3 cascade (FIXME 0222) is structurally adjacent but independent.

The `clif_ir: String` field carries a per-function CPU cost (~tens of microseconds string serialization per function). In batch mode (e.g., `--link` to .o object output), this is wasted work; if it becomes a measurable performance issue, the `clif_ir` field could rotate to `Option<String>` with a mode signal. Premature optimization warning: hold the current always-capture shape until evidence of batch-mode regression appears.

Sprint 70 Phase B `/review` verdict (commit `49eb483`+) named this follow-up as **Important** severity.

## Related

- Decision 41 (operative, amended Sprint 70 Phase B)
- FIXME 0222 — typecheck cascade off S70 narrows (parallel scope)
- FIXME 0175 — marshal-deps gap (frontend invocation path; not directly blocked by 0221 but adjacent)
- `design/arch/facades/backend.md` §"Free functions" + §"Return shapes" — current target-stating
- `src/session_v4.rs:566` — `Introspection` struct (stays in int; not touched by this work)
