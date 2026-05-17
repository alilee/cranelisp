---
number: 0041
title: `compile_to_module` per-symbol JIT cardinality; `Code` moves to `cranelisp-backend`; backend writes shared state directly; `Result<(), CompilationError>`
status: operative
---

# 0041 — `compile_to_module` per-symbol JIT cardinality; `Code` moves to `cranelisp-backend`; backend writes shared state directly; `Result<(), CompilationError>`

`compile_to_module` is per-symbol-arity for JIT mode and per-module-arity for object mode (caller controls via `names` length). `Code` enum moves from `src/code.rs` to `cranelisp-backend/src/code.rs` (Decision 35 Layer 2 Option B retracts; backend gains direct construction of `Code`; Principle 3 protected — `Code` does NOT enter `cranelisp-types`). Backend writes `Code::Jit` into symbol-table entries directly via Decision 38's `write_code(&self, sym, code)`; writes `Introspection` into `Option<&introspection>` if `Some`; returns `Result<(), CompilationError>`. Per-symbol JIT cardinality enables true per-redefinition reclaim; Decision 31 amends from per-batch to per-symbol cardinality.

## Three coordinated changes

### 1. Per-symbol JIT cardinality

Each `compile_to_module` call for JIT mode receives `&[symbol]` — one symbol per call. Backend creates one `JITModule`, defines one function, finalises, hands back. Object mode is unchanged: `compile_to_module` receives `&[full module's defined symbols]` and produces a `.o` containing all of them.

Cardinality is determined by the `names` arity at the caller, NOT by mode at the function signature — Decision 23's "mode is a Module property" remains intact. JIT call sites now look like:

```rust
for sym in defined_symbols(&shared.symbol_tables[scope]) {
    let jit = Jit::new_with_symbols(&extra)?;
    compile_to_module(scope, &[sym], &shared.symbol_tables, shared.introspection.as_ref(), jit.jit_module())?;
}
```

Per-redefinition reclaim becomes truly per-symbol: redefine one defn → its `Code::Jit` clone in the table drops → the `Arc<Jit>` hits 0 → custom `Drop` calls `unsafe free_memory()` for that one defn's pages, immediately. Cost: per-symbol `JITModule::new` invocations (~50 intrinsic registrations each per `register_intrinsics` in `jit.rs:166`). Cache-hit `Linker` cardinality is unchanged: one Linker holds many symbols (the `.o` is per-module, not per-symbol).

### 2. `Code` enum moves from `src/code.rs` to `cranelisp-backend/src/code.rs`

Backend already owns `Jit` and `Linker`; it's the natural home for the type that wraps both. Decision 35's "Code lives in `src/`" rationale was Principle 3 — `cranelisp-types` cannot import `Code` because `Code` references backend types. That rationale stands intact — `Code` does NOT move to `cranelisp-types`; it moves to `cranelisp-backend`.

`SymbolTable<C, L>` stays generic in `cranelisp-types`; backend instantiates `SymbolTable<Code, ()>` for its own signatures; frontend/typecheck stay on `SymbolTable<(), ()>` (no `Code` import for them either — the `C` generic continues to serve its purpose). Decision 35 Layer 2 Option B retracts: backend is no longer generic-blind; it knows about and constructs `Code`. The "integration layer is the sole crate that names `Code`" claim from Decision 35 relaxes — int still names `Code` at the session-boundary instantiation, but backend now also names it (in its own crate).

### 3. Backend writes directly to symbol tables and introspection; returns `Result<(), CompilationError>`

Final signature:

```rust
pub fn compile_to_module<M: Module>(
    scope: &ModuleFullPath,
    names: &[Symbol],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<Code, ()>>,
    introspection: Option<&DashMap<FQSymbol, Introspection>>,
    module: M,
) -> Result<(), CompilationError>;
```

Backend writes each compiled symbol's `Code::Jit { jit, ptr }` into its entry via `symbol_tables.get(scope).unwrap().write_code(sym, Code::Jit { jit, ptr })` (Decision 38's `write_code(&self, …)` — interior mutable, no `&mut` flow needed). Backend also stores the GOT slot pointer via the entry's already-existing GOT path. Backend writes `Introspection { clif_ir, disasm, code_size, compile_duration, … }` into the introspection map if and only if `introspection.is_some()` — the `Option`'s `is_some()` IS Decision 38's mode discriminator, reaching backend directly via the parameter.

Decision 37's "no swallowed failures" rule lands as a single `?` inside `compile_to_module` — the per-step cascade collapses; backend errors out at the first invariant breach with a typed `CompilationError` variant.

## Consequences

- `crates/cranelisp-backend/src/code.rs` new (moved from `src/code.rs`); backend exports `pub enum Code { Jit { jit: Arc<Jit>, ptr: *const u8 }, Linker { linker: Arc<Linker>, ptr: *const u8 } }`.
- `src/code.rs` deleted; int imports `cranelisp_backend::Code` for session-boundary instantiation of `SymbolTable<Code, ()>`.
- `crates/cranelisp-backend/src/lib.rs` `compile_to_module` signature updated per §3 above; old `(Arc<Jit>, code_ptrs)` return removed.
- `src/worker.rs:2860-3018` post-loop deleted (the iterate-over-names + GOT-store + `Code::Jit`-construct + three error cascades collapse into the per-symbol call-site loop above).
- `Jit::compile_defn` (audit HIGH-1) confirmed deprecated — paired pin: `Jit` exposes only `new` / `module` / finalize accessors; per-function compilation is via `compile_to_module` only — there is no public `compile_defn`.
- `facades/backend.md` §"Public surface": `compile_to_module` signature spelled per §3; the `CompilationResult` / return-tuple gone; `Code` enum surface added.
- `facades/int.md` §"SharedState — code carrier construction": post-loop description deleted; `Code` import path updates from `src/code.rs` to `cranelisp_backend::Code`.
- `tests/v4_jit_reclaim.rs::decision31_scenario2_per_redefinition_jit_pages_reclaimed` re-verified against per-symbol cardinality — the test's "redefine X, observe pages reclaimed" assertion strengthens (reclaim is now per-symbol-immediate rather than batch-coalesced).

## S66 amendment + rollback — GOT is single source of truth (2026-05-09)

**Phase 1 (commit `b09ec76` + `6f47008`, superseded same day):** The ptr embedded in `Code` variants was migrated to a unified `fn_ptr: Option<*const u8>` field on `ModuleEntry::Def` (which also subsumed the previously-separate `platform_fn_ptr` and superseded the briefly-planned `primitive_fn_ptr`). `Code` variants slimmed to lifecycle owner only:

```rust
pub enum Code {
    Jit(Arc<Jit>),
    Linker(Arc<Linker>),
}
```

**Phase 2 (commit `1dc57ae`, rollback — same day):** The unified `fn_ptr` field was identified as redundant with the per-module `GotTable` already populated at registration. Removed. The variant slim is preserved; the call address now has its single home in the GOT.

**Canonical post-rollback statement:**

> **GOT is the single source of truth for callable addresses.** `ModuleEntry::Def.got_slot: Option<usize>` indexes into `SymbolTable.got()` (a `GotTable` — see `crates/cranelisp-types/src/got.rs`); the runtime address lives at `symbol_table.got().load_slot(slot)`. There is no separate `fn_ptr` / `platform_fn_ptr` / `primitive_fn_ptr` field. Origin (JIT-compiled / linker-loaded / platform DLL / primitive) is encoded by `kind: DefKind`.

Decision 41's substance is unchanged: per-symbol JIT cardinality, `Code` lives in `cranelisp-backend`, backend writes shared state directly, returns `Result<(), CompilationError>`. The post-rollback write pattern is:

1. Backend calls `jit.get_finalized_function(func_id)` to obtain the code ptr.
2. Backend calls `symbol_table.got().store_slot(slot, ptr)` to publish the address (Release; visible to JIT-emitted GOT loads).
3. Backend calls `SymbolTable::write_code(&self, sym, Code::Jit(Arc<Jit>))` to install the lifecycle owner (Decision 38's interior-mutable signature).
4. The entry's `got_slot: Some(slot)` was already allocated at registration; no field-level ptr write occurs.

Decision 31 Scenario 2 reclaim semantics are preserved (lifecycle ownership stays inside `Code::Jit(Arc<Jit>)`; `Drop` chain unchanged; the GOT slot's stored ptr becomes invalid the instant `JITModule::free_memory()` runs). See `design/arch/sprint-66-types-authoring-plan.md` §1.7-revised + §1.8 and `design/arch/facades/{types,backend,primitives,platform}.md` for the as-designed shape.

## Cross-references and amendments

**Decision 31 amends.** "Per-batch JIT" → "per-symbol JIT for `compile_to_module` JIT calls; per-batch retains for object mode (one ObjectModule per `.o`)". Per-redefinition reclaim becomes immediate-per-symbol rather than coalesced-per-batch.

**Decision 35 amends.** Layer 2 Option B retracts; `Code` location moves from `src/` to `cranelisp-backend`; "the integration layer is the sole crate that names `Code`" relaxes (int names it at the session boundary; backend names it in its own crate). The Principle 3 protection (no `cranelisp-types → cranelisp-backend` dep) survives intact.

**Decision 32 unchanged.** The empty-marker `CodeStore` trait still serves: `()` for non-codegen crates, `Code` for backend + int. The `Clone` super-bound stays — `Code` derives `Clone` (Arc clones are cheap).

Sprint 63 substance-scoping resolution §1.2.

## Rationale

- Principle 1 (decoupling) — int no longer duplicates backend's iteration.
- Principle 2 (narrow interfaces) — five parameters, no return tuple to unpack.
- Principle 7 (single source of truth) — backend writes the entry it produced.
- Principle 11 (single pipeline, mode parameters) — same function for JIT and object, mode driven by `Module` impl per Decision 23.

## Canonical location

`crates/cranelisp-backend/src/lib.rs` (`compile_to_module` signature); `crates/cranelisp-backend/src/code.rs` (`Code` enum, post-move). Owner: `/arch` files Decision and authors amended Decision 31 + Decision 35 cross-amendment notes; `/arch` updates `facades/backend.md` and `facades/int.md`. `/dev` (backend) executes the `Code` move and signature refactor; `/dev` (int) deletes the post-loop and refactors call sites.

## Status pointer — Sprint 67 close

S67 close — all four close-out items land in Waves 0+3+4:

- **Wave 0** — `CompilationError` enum + `LinkerError` enum +
  `LinkerArtefact` + `ObjectArtefact` authored in
  `crates/cranelisp-backend/src/{error,artefact}.rs` per REV-4
  (single-consumer placement, not `cranelisp-types`). Verified
  `cargo check -p cranelisp-backend` passes with the new types
  (no consumer wiring at Wave 0).
- **Wave 3** (`/dev (backend)`) — `Code` enum physically relocates
  from `src/code.rs` → `crates/cranelisp-backend/src/code.rs`;
  `compile_to_module` signature lifts to `Result<(), CompilationError>`
  + direct per-symbol writes via Decision 38's `write_code` +
  `got().store_slot`; `load_object` becomes a free function returning
  `LinkerArtefact`; `compile_to_object` becomes a free function
  returning `ObjectArtefact`; `Linker::get_symbol` returns
  `Result<*const u8, LinkerError>` (post-S58 silent-NULL regression
  closure).
- **Wave 4** (`/dev (int)`) — call sites in `worker.rs` /
  `pipeline.rs` collapse to per-symbol pattern; the previous
  multi-step post-loop dissolves.

Decision 41 closes substantively at S67 close.
