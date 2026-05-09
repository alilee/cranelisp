---
number: 0035
title: `Code` enum (the integration layer's concrete `C` for `SymbolTable<C, L>`) lives in `src/` and unifies JIT-backed and Linker-backed compiled code; backend signatures stay generic-blind
status: operative
---

# 0035 — `Code` enum (the integration layer's concrete `C` for `SymbolTable<C, L>`) lives in `src/` and unifies JIT-backed and Linker-backed compiled code; backend signatures stay generic-blind

The integration layer's concrete `C` for `SymbolTable<C, L>` is `Code`, an enum with two variants:

```rust
// src/code.rs (or inline in src/session_v4.rs); owned by /int.
pub enum Code {
    Jit { jit: Arc<cranelisp_backend::jit::Jit>, ptr: *const u8 },
    Linker { linker: Arc<cranelisp_backend::cache::Linker>, ptr: *const u8 },
}
```

The two variants carry the appropriate retention root for each compilation lineage: `Code::Jit` for fresh-build code (the `Arc<Jit>` is the Decision-31 reclaim primitive — when the last clone drops, custom `Drop` calls `unsafe JITModule::free_memory()`); `Code::Linker` for cache-hit `.o`-mapped code (the `Arc<Linker>` is the per-symbol retention root — when the last `Code::Linker` referencing a `Linker` drops, the mmap'd pages can be reclaimed). The `*const u8` is the GOT-target code address; reading it is variant-uniform (`code.ptr()`).

**`Code` lives in the integration layer (`src/`), NOT in `cranelisp-types`.** This is load-bearing: `Code` references both `cranelisp_backend::jit::Jit` and `cranelisp_backend::cache::Linker`, and putting `Code` in `cranelisp-types` would invert the dependency edge that Principle 3 protects (`cranelisp-types → cranelisp-backend` is forbidden). Per Decision 32, `cranelisp-types` exposes only the `CodeStore` empty-marker trait; the integration layer composes the concrete `C = Code` and instantiates `SymbolTable<Code, ()>` at the session boundary in `src/session_v4.rs`.

**`L = ()` (no per-module linker store).** Per-symbol Linker retention via `Code::Linker.linker: Arc<Linker>` covers the only case where a Linker needs to outlive its construction: cache-hit code mapped from `.o` keeps its Linker alive through the Arc on each `Code::Linker` referencing it. There is no scenario today where a Linker must be retained without any `Code::Linker` referencing it; if one emerges, `L` can be reactivated without further generics churn.

**Backend signatures stay `<C, L>`-blind (CP1 arbitration: Layer 2 Option B).** Per Decision 32 + `compile-to-module.md` §17, `cranelisp-backend` operates on `SymbolTable` (i.e., `SymbolTable<(), ()>`) everywhere; the backend never names `Code`. The integration layer is the sole crate that names `Code`. `compile_to_module<M: Module>` returns the raw `(Arc<Jit>, HashMap<Symbol, *const u8>)` pair (or its in-result equivalent — `CompilationResult` carrying `func_ids` + the per-batch `Arc<Jit>`); the integration-layer worker constructs `Code::Jit { jit, ptr }` per defined symbol and writes it onto `Def.code`. This is `/int`'s `symbol-table-generics.md` "Layer 2 Option B" — confirmed as the binding choice at Sprint 58 Phase 3a Architecture Review (CP1 arbitration). Option A (making backend generic over `C: CodeStore + From<RawCode>`) was rejected: it would force `cranelisp-backend` to invent a `RawCode` type for the sole purpose of `From` impls in the integration layer, and would put `<C>` bounds on every backend signature that touches the codegen result. Option B keeps backend signatures stable and the conversion local to the one site that knows the integration's enum. `/backend`'s Wave 2 update to `compile-to-module.md` §17 must spell out the `(Arc<Jit>, HashMap<Symbol, *const u8>)` (or `CompilationResult` extension) shape that the integration layer consumes — `/arch` files this as a Wave-1 follow-on FIXME(/backend), not a sprint blocker.

**`SharedState.kept_jits` AND `SharedState.kept_linkers` both dissolve.** Per Decision 31 Scenario 2 (per-redefinition reclaim) the `Arc<Jit>` retention root moves from the side-store to `Code::Jit`; symmetrically `Arc<Linker>` moves to `Code::Linker`. Both side-stores delete in the Step 5c sweep. `SharedState.kept_dlls` (platform DLL handles) is unchanged — DLLs are session-global and orthogonal to this decision (per `/platform`'s addendum §A3).

**Cache-restore for `.o`-backed modules (`--link` mode)**: the cache loader reads `.o` via `Linker::load_object`, wraps the resulting `Linker` in an `Arc`, and writes `Code::Linker { linker, ptr }` onto each `Def.code` for symbols the linker resolved. The `Arc<Linker>` is shared across every entry the linker materialised; reclamation fires when the last `Code::Linker` clone drops (per-module reclaim, the dual of Scenario 2's per-batch JIT reclaim).

**Mixed-lineage modules are first-class.** A REPL session that loads cached `.o` for module `A` (entries hold `Code::Linker`) and then evaluates `(defn foo [x] x)` in module `A` (the new entry holds `Code::Jit` from the fresh batch) is a normal mixed state — the symbol table holds entries of both variants. There is no "cache mode" vs "JIT mode" — the variant choice lives per-entry, and the mode discriminator that Principle 11 forbids does not appear.

**Pattern-matching and accessor discipline**: every read site that needs the code address calls a `code.ptr()` accessor that variant-matches and returns the inner `*const u8`; sites that need the lifetime root (rare — only at JIT-entry registration and Linker-pages observation) variant-match explicitly. `Code` carries `unsafe impl Send + Sync` (analogous to `ModuleEntry`'s today) — the raw pointer is an integer handle into pages the Arc keeps alive.

Rejected alternatives: (a) `Code` lives in `cranelisp-types` — Principle 3 violation (forces `cranelisp-types → cranelisp-backend` dep); (b) `C = Arc<Jit>` directly with a parallel `cache_code: Option<*const u8>` field on `Def` — re-introduces the splay between fresh-build and cache-hit storage that Decisions 25 and 32 close (Principle 7 violation: two retention disciplines, two reclaim paths); (c) `Code` as a trait object (`Box<dyn CodeStore>`) — gives up monomorphisation, adds vtable indirection on every code-pointer access (Decision 32 already rejected `dyn` for this reason); (d) two separate `SymbolTable<C, _>` instantiations — one for cached, one for fresh — and a session-level multiplex — violates Principle 11 (single pipeline) by re-introducing the dual-pipeline shape Decision 23 closed.

Canonical location: `src/code.rs` (or inline near `SharedState` in `src/session_v4.rs` — `/int`'s implementation choice; the type is integration-layer-owned). Owner: `/int`. Defined Sprint 58 Phase 3a Architecture Review (after the four Wave 1 design-doc sets landed) — formalises `/int`'s `symbol-table-generics.md` §2.1 concrete-type choice and arbitrates CP1 in favour of Layer 2 Option B. Rationale: Principle 3 (dependency flows toward stability — `cranelisp-types` stays Cranelift-ignorant) + Principle 11 (single pipeline — one variant-uniform code-pointer access path across fresh-build and cache-hit) + Principle 8 (the enum IS the §9.1 target shape composed at the integration layer; not interim — this is the final concrete that activates Decision 31 Scenario 2 reclaim and the cache-hit Linker reclaim story together).

## Amendment (Sprint 64, per Decision 41)

**Layer 2 Option B retracts.** Decision 41 moves `Code` from `src/code.rs` to `crates/cranelisp-backend/src/code.rs` so backend can construct `Code::Jit { jit, ptr }` directly inside `compile_to_module` (rather than returning an artefact that int wraps). The "integration layer is the sole crate that names `Code`" claim above relaxes — int still names `Code` at the session-boundary `SymbolTable<Code, ()>` instantiation (re-exporting from backend), but backend now also names it in its own crate.

**Principle 3 protection survives intact.** `Code` does NOT move to `cranelisp-types` — that was the original Layer-2 decision driver and remains the right call. The move from `src/` to `cranelisp-backend` keeps `cranelisp-types → cranelisp-backend` forbidden (the dep direction in question); `cranelisp-backend → cranelisp-types` (the existing direction) is unaffected. The motivation for Layer 2 Option B (keep backend signature simple by returning raw tuples) is replaced by Decision 41's direct-write pattern via Decision 38's `write_code(&self, sym, code)` — backend writes the constructed `Code::Jit` directly rather than handing back parts for int to assemble. The previous post-loop in `worker.rs:2860-3018` collapses; the contract becomes self-contained on the backend side.

See Decision 41 for the full signature, the per-symbol JIT cardinality story (which amends Decision 31), and the consequences listing.

## Amendment (Sprint 66 — fn_ptr unification, 2026-05-09; superseded same day by 1dc57ae)

> **Status note.** This amendment was authored alongside `b09ec76`
> (unified `fn_ptr` field on `ModuleEntry::Def`) and `6f47008`
> (configuration consistency sweep). It was **superseded mid-sprint**
> by commit `1dc57ae` — the rollback of the `fn_ptr` field. The
> variant-slim outcome below STILL HOLDS; only the relocation of the
> per-entry ptr to a sibling field has been undone in favour of the
> GOT (which was already authoritative). See "Amendment (Sprint 66 —
> rollback, 2026-05-09)" below for the post-rollback canonical shape.

**Variant slimming (preserved through rollback).** The two-field
variant shapes shown in the original decision —

```rust
pub enum Code {
    Jit { jit: Arc<Jit>, ptr: *const u8 },
    Linker { linker: Arc<Linker>, ptr: *const u8 },
}
```

— retire. Post-S66 the variants are tuple-variant-shaped, carrying the
lifecycle owner only:

```rust
pub enum Code {
    Jit(Arc<Jit>),
    Linker(Arc<Linker>),
}
```

The per-entry `*const u8` was briefly migrated to a unified
`fn_ptr: Option<*const u8>` field on `ModuleEntry::Def` (b09ec76);
that placement has been reverted by `1dc57ae` — see the rollback
amendment below. The variant-uniform `Code::ptr()` accessor
referenced in the original decision's "Pattern-matching and accessor
discipline" paragraph is **retired** with the embedded ptr — consumers
read the call address from the GOT (the post-rollback single source of
truth — see `facades/types.md` §"Symbol table — the single store"
`got_slot` doc).

**Decision 31 Scenario 2 reclaim semantics preserved.** Lifecycle
ownership stays inside `Code::Jit(Arc<Jit>)`. When the entry's `Code`
clone drops and refcount hits 0, `Drop::drop` on the `Jit` wrapper
calls `unsafe JITModule::free_memory()` — same chain as the original
decision. The GOT slot is updated to the new code address before the
old `Arc<Jit>` clone can drop (atomic ordering per
concurrency-symbol-table-entry.mmd); the GOT slot's stored ptr becomes
invalid the same instant the JIT pages are freed.

**Substance unchanged.** The original decision's load-bearing claims —
`Code` lives in backend (post Sprint 64), `L = ()` is sufficient,
mixed-lineage modules are first-class, `kept_jits` and `kept_linkers`
both dissolve, Principle 3 protection holds — are all preserved. Only
the two-field variant shape and the `Code::ptr()` accessor change.

## Amendment (Sprint 66 — rollback, 2026-05-09)

**The unified `fn_ptr` field is retracted.** Commit `b09ec76` added
`fn_ptr: Option<*const u8>` to `ModuleEntry::Def` as the relocation
target for the per-entry call address removed from the `Code`
variants. Commit `1dc57ae` (same day) **removed** that field after
identifying it as redundant: every callable entry already has a
`got_slot`, and JIT-emitted code reads addresses from the per-module
`GotTable` at `got_base + slot * 8`. Stashing the same address on a
sibling field was duplicate state — a Principle 7 violation.

**Canonical post-rollback shape.** The GOT is the single source of
truth for callable addresses:

- `ModuleEntry::Def.got_slot: Option<usize>` indexes into
  `SymbolTable.got()` (a `GotTable` per module — see
  `crates/cranelisp-types/src/got.rs`).
- The runtime address lives at `symbol_table.got().load_slot(slot)`.
- Backend's `compile_to_module` writes the address via
  `got().store_slot(slot, ptr)` immediately after
  `jit.get_finalized_function`; the `Code::Jit(Arc<Jit>)` lifecycle
  owner is written separately via `SymbolTable::write_code`.
- Platform-fn registration and primitives' static-init follow the
  same GOT-write pattern.
- `got_slot: None` indicates non-callable, non-addressable entries.

The variant slim from the previous amendment is preserved — `Code`
stays tuple-shaped (`Code::Jit(Arc<Jit>)` /
`Code::Linker(Arc<Linker>)`), carrying lifecycle ownership only. The
difference vs. the previous amendment is purely *where* the call
address lives: GOT slot, not sibling field.

See `design/arch/sprint-66-types-authoring-plan.md` §1.7-revised for
the complete authoring brief; `facades/types.md` §"Symbol table — the
single store" and Decision 41's "S66 amendment + rollback" for the
canonical post-rollback statement.
