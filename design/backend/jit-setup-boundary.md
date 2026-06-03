# Minimal JIT-setup boundary — `Jit::new(symbol_tables)`, `INTRINSICS_TABLE`, `.meta.json` platform schema, 0122 re-test

**Status.** Phase 3 design (S76). Design-only; no source edits accompany this doc. Implementation lands in S76 W-Enablement / W-Integrate per `sprints/SPRINT.md`.

**Owner.** `/design` (backend).

**Reads.** `design/arch/bounded-contexts.md` §3 ("Minimal JIT-setup boundary" + invariants 1–7); `design/backend/compile-to-module.md` (S75 banner + §6 + §2.6.5); `design/backend/backend.md` (master, §2.1/§3.3); `crates/cranelisp-backend/src/lib.rs` `//!` + `src/jit.rs` rustdoc; `design/arch/CLAUDE.md` Decision 0048 (primitives precedent), Decision 0041 (per-symbol JIT direct-writes); `sprints/SPRINT.md` §"Architecture review (Phase 2)" Q1/Q2 (the seam dispositions, /arch sign-off); FIXMEs `0232-backend-meta-json-platform-schema.md`, `0122-backend-link-mode-got-alignment-divergence.md`, `0233-int-platform-as-module-*`.

**Scope from BC §3.** Four S76 backend obligations, all W-Enablement / W-Integrate (NOT macro-driven):

| # | Obligation | Wave | §below |
|--:|---|---|---|
| 1 | `Jit::new(symbol_tables)` constructor — the minimal-JIT-setup boundary | W-Enablement | §1 |
| 2 | Consume `intrinsics::INTRINSICS_TABLE` at construct + cache-hit | W-Enablement | §2 |
| 3 | `.meta.json` platform schema (`schema_literal` field) — FIXME 0232 | W-Integrate (platform host-wiring wave) | §3 |
| 4 | 0122 `--link` GOT-alignment defect — re-test + (cheap) fix | W-Integrate | §4 |

**Macro-change NO-OP confirmation (S76 W-Macro).** The macro re-architecture (`MacroExpander` trait, frontend `expand` retirement, typecheck walk+recognize, int execution callback) does **not touch backend**. Confirmation: macro *clauses* are ordinary `Def` entries codegen'd through the existing `compile_to_module` / `compile_constr_adt` paths (a defmacro clause fn is a normal fn on its module's GOT — `memory/MEMORY.md` §"No global GOT"); macro *expansion execution* is int's `src/expander.rs` + `src/marshal.rs` invocation core behind the new `cranelisp_types::MacroExpander` callback, invoked by typecheck — none of which is a backend surface. Backend names no macro type, declares no macro intrinsic (the trace/test intrinsics are int-owned per Decision 40 / `src/CLAUDE.md` §"Int-owned JIT intrinsics"), and emits no macro-specific CLIF. **W-Macro is a backend NO-OP. No backend design change, no baseline change.** Flagged for /arch only if a future wave proposes a macro-clause codegen path distinct from the normal fn path (none is proposed).

---

## §1 `Jit::new(symbol_tables)` — the minimal-JIT-setup boundary

### 1.1 The target the boundary collapses to

BC §3 "Minimal JIT-setup boundary" target-states it: in the converged design `compile_to_module` drives declare → compile → finalize **internally**; the caller (int) only constructs the `Jit`, hands off `jit.jit_module()`, and holds `Arc<Jit>` for reclaim. So the boundary `Jit` surface shrinks to **construct + handoff + reclaim**: the constructor(s), `jit_module()`, and `Drop`.

Today int hand-assembles the entire JIT symbol set before calling `Jit::new_with_symbols(&extra)` (`src/worker.rs::collect_jit_setup` at `worker.rs:2954` + the fold-in at `worker.rs:3242-3296`): it walks every module's `SymbolTable` for `PlatformEffect` jit-names, folds in `crate::session_v4::int_intrinsics()`, and appends one `(got_data_symbol_name(M), got.base_ptr())` pair per module as extra symbols. `Jit::new(symbol_tables)` **absorbs all of that** — int assembles nothing.

### 1.2 Signature

```rust
impl Jit {
    /// Construct a JIT whose entire symbol set is derived from `symbol_tables`.
    ///
    /// Registers, before `JITModule::new`:
    ///   - the runtime + backend-emitted-call intrinsic Import targets from
    ///     `cranelisp_intrinsics::INTRINSICS_TABLE` (replacing the in-crate
    ///     `intrinsic_symbols()` enumeration — §2);
    ///   - one `__cranelisp_got_{M}` → `symbol_tables[M].got().base_ptr()`
    ///     symbol per module in `symbol_tables` (incl. the synthetic
    ///     `primitives` module), named via `cranelisp_types::got_data_symbol_name`;
    ///   - every `PlatformEffect` primitive's `jit_name` → GOT-slot ptr,
    ///     resolved by walking each module's defs + import chains.
    ///
    /// `C`/`L` are the symbol-table carrier params; at int's JIT boundary the
    /// concrete type is `SymbolTables<Code, ()>`. The GOT base-ptr + platform
    /// jit-name walk read only `got()` + `kind`/`got_slot`, so the body is
    /// `<C, L>`-blind (no `Code` knowledge — Principle 3 / Decision 0048 dep-ban
    /// preserved: backend reaches primitives only through the type-erased mount).
    pub fn new<C, L>(
        symbol_tables: &SymbolTables<C, L>,
    ) -> Result<Self, CranelispError>;
}
```

`SymbolTables<C, L>` is the `&DashMap<ModuleFullPath, SymbolTable<C, L>>` alias backend already takes in `compile_to_module` — the **same** value that feeds codegen, so the JIT symbol set and the codegen GOT references derive from one source (BC §3 "int assembles nothing"). Returns `CranelispError` (consistent with the existing `Jit::new*` constructors; not `CompilationError` — construction is not codegen).

### 1.3 Internals — three derivations, all from `symbol_tables`

Pre-`JITModule::new`, on a `JITBuilder`:

1. **Intrinsic Import targets** — `for rec in cranelisp_intrinsics::INTRINSICS_TABLE { builder.symbol(rec.name, rec.ptr) }`. Replaces `register_intrinsics()` (`jit.rs:180`) which iterates the in-crate `intrinsic_symbols()`. See §2.
2. **Per-module GOT data symbols** — `for entry in symbol_tables.iter() { builder.symbol(got_data_symbol_name(entry.key()), entry.value().got().base_ptr()) }`. This is exactly the `got_data_defs` loop currently at `worker.rs:3003-3006`, moved inside the constructor. Uses the **types-crate** `got_data_symbol_name` (already authored — `crates/cranelisp-types/src/module.rs:1722`), not the backend `pub(crate)` one (`compiler/mod.rs:100`), per the Phase-2 review's single-source ruling.
3. **Platform-effect jit-names** — the `collect_jit_setup` def + import-chain walk (`worker.rs:2961-3001`): for each `DefKind::Primitive { primitive_kind: PlatformEffect, jit_name: Some(n) }` with a populated GOT slot, register `(n, got.load_slot(slot))`; follow `ModuleEntry::Import` to the source table for imported platform effects.

Then `JITModule::new(builder)`, `make_context()`, `FunctionBuilderContext::new()` — identical to the existing `from_isa` tail (`jit.rs:338-353`). The 6 convenience `*_func_id` fields stay `None` at construct (they are populated by `declare_intrinsics` during the per-call compile, unchanged — `compile_to_module` calls `declare_intrinsics_generic` internally per `lib.rs:526`).

**ISA.** `Jit::new` builds its ISA via the module-level `build_isa()` (the `from_isa` path). A future micro-optimisation could accept a shared `Arc<dyn TargetIsa>` (the existing `new_with_isa` shape) for per-symbol-cardinality batches that construct many `Jit`s; **not** designed here (premature per `feedback_no_premature_perf` — the per-symbol JIT cost is the accepted Decision-0041 trade).

### 1.4 What it retires / narrows

| Construct | Disposition | Why |
|---|---|---|
| `Jit::new_with_symbols(&[(&str, *const u8)])` | **`pub(crate)` or delete** once int's hand-assembly is gone. int is its only production caller (the two `pipeline.rs` sites collapse with W-Collapse; the `worker.rs:3296` site becomes `Jit::new(symbol_tables)`). Backend tests that use it migrate to `Jit::new(&tables)` or keep a `pub(crate)` test-only path. | BC §3 lists `new_with_symbols`-style construct as int-parallel-path-only; the boundary is `new(symbol_tables)`. `feedback_callee_api_for_caller_only`: a callee API kept only because int calls it is not justified by int. |
| `Jit::new_with_isa` | **`pub(crate)`** — used internally by per-symbol batches if §1.3's shared-ISA optimisation ever lands; no external caller. | Same. |
| `Jit::new()` (no args) | **Keep `pub`** — `Jit::new()` (empty symbol set) is the genuine zero-arg path some backend unit tests use; harmless. Re-expressible as `Jit::new(&empty_tables)` but the no-arg ergonomic is worth keeping `pub`. *(/design call: keep; revisit if baseline review objects.)* |
| `register_intrinsics(&mut JITBuilder)` (`jit.rs:180`) | **Re-point** to iterate `INTRINSICS_TABLE` (§2), OR fold into `Jit::new`'s body. | §2. |
| `collect_jit_setup` / `collect_jit_setup_public` (int, `worker.rs:2954`/`3017`) | **Deleted on the int side** (W-Collapse) — body absorbed into `Jit::new`. Backend gains the walk. | The reach-around int does today moves behind the boundary. |

**Dead-code signal expected.** Narrowing `new_with_symbols`/`new_with_isa` to `pub(crate)` will fire `dead_code` on any field/method reachable only through them until W-Collapse deletes int's parallel path. That is the **expected** signal per `feedback_facade_walk_no_interior` / the `jit.rs:236` `#[allow(dead_code)]` FIXME(W4/S77) — do NOT revert to `pub` to silence it. The S76 collapse removes the allow when the in-crate readers materialise.

### 1.5 Sequencing (per Phase-2 review Q2)

`Jit::new(symbol_tables)` lands **with** the int JIT-setup collapse (W-Collapse), not before — it is the *destination shape* of the collapse. The hand-assembly loop (`collect_jit_setup` + `int_intrinsics` + `got_data_defs` fold) is *replaced by* one `Jit::new(symbol_tables)` call in the same co-edit (backend authors the constructor; int switches the call site + deletes `collect_jit_setup`). `INTRINSICS_TABLE` (intrinsics crate) lands with-or-just-before, since `Jit::new` reads it (§2.3).

### 1.6 Baseline-regen note

`Jit::new(symbol_tables)` is a backend public-API addition; `new_with_symbols`/`new_with_isa` narrowing to `pub(crate)` is a public-API *removal*. Both touch `crates/cranelisp-backend/public-api.txt`. Per baseline-diff discipline (`design/arch/CLAUDE.md` §"Baseline-diff discipline"): `/dev (backend)` regenerates the baseline via `cargo public-api --omit blanket-impls,auto-derived-impls -p cranelisp-backend` in the same change-set, and updates the crate-root `//!` rustdoc (the canonical surface — facade retired S75 W5b) to name `Jit::new(symbol_tables)` as the construct boundary. No `facades/backend.md` (retired); BC §3 already target-states it (no BC edit — Phase-2 review confirmed).

---

## §2 Consume `cranelisp_intrinsics::INTRINSICS_TABLE`

### 2.1 What it is

A NEW published surface on `cranelisp-intrinsics` (BC §4b invariant 11; approved target-stated by the Phase-2 review; authored by `/dev (intrinsics)`): a flat `name → (signature, ptr)` catalog of every runtime + backend-emitted-call intrinsic. **NOT** a mounted GOT-module — intrinsics are `Linkage::Import`-dispatched by name, not GOT-indirect (BC §4b invariants 9/11). This replaces backend's `intrinsic_symbols()` enumeration (`jit.rs:148`) as the single source of intrinsic registration records.

The catalog's home moving to intrinsics means **`backend::IntrinsicSymbol` retires as a public concept** (it is already `pub(crate)` per S75 W3 — `jit.rs:87`). The runtime-vs-primitive `is_runtime` split the record carries is preserved in the intrinsics-published shape (the `jit.rs:96` FIXME(S77) already anticipates this).

### 2.2 The two consumption sites

| Site | Today | Target |
|---|---|---|
| **JIT construct** | `Jit::new`'s `register_intrinsics` / `declare_intrinsics_generic` iterate the in-crate `intrinsic_symbols()` (`jit.rs:148`) | iterate `cranelisp_intrinsics::INTRINSICS_TABLE`. Both the `JITBuilder::symbol(name, ptr)` registration (`register_intrinsics`, `jit.rs:180`) and the `declare_function(name, Linkage::Import, sig)` declaration (`declare_intrinsics_generic`, `jit.rs:733`) read the catalog. `param_count`/`has_return` drive the synthesized `Signature`. |
| **Cache-hit `Linker`** | `worker.rs:3545`: `for sym in cranelisp_backend::jit::intrinsic_symbols() { linker.register_symbol(sym.name, sym.ptr) }` — int reaches into backend's `pub(crate)` enumeration | int iterates `cranelisp_intrinsics::INTRINSICS_TABLE` directly and calls `linker.register_symbol(rec.name, rec.ptr)`. Backend's `intrinsic_symbols()` is no longer reached cross-crate. |

### 2.3 Backend-side disposition of `intrinsic_symbols()` / `IntrinsicSymbol`

- `intrinsic_symbols()` (`jit.rs:148`) — **deleted** once both consumption sites read `INTRINSICS_TABLE`. Its body (the 15-record `vec![...]`) is the data that migrates into the intrinsics-published catalog; `/dev (intrinsics)` authors `INTRINSICS_TABLE` from it (the `cranelisp_intrinsics::*` fn-ptr references the records already use are in-crate for intrinsics, so the catalog is naturally homed there).
- `IntrinsicSymbol` struct (`jit.rs:87`) — **deleted** (its public-concept role moves to whatever record type `INTRINSICS_TABLE` exposes). The convenience-accessor DTOs `IntrinsicFuncIds`/`IntrinsicIds` (the *declared-FuncId* bundles, `jit.rs:704`) **stay** `pub(crate)` — they are the per-call `declare_intrinsics_generic` return, populated from the catalog, consumed by `build_compile_context`. They are not the catalog.
- `declare_intrinsics_generic<M>` (`jit.rs:733`) — **stays** `pub(crate)`, body re-pointed from `intrinsic_symbols()` to `INTRINSICS_TABLE`. It is `compile_to_module`'s internal intrinsic-declaration step (`lib.rs:526`), not a boundary.

### 2.4 Dependency check

`cranelisp-backend` already depends on `cranelisp-intrinsics` (it references `cranelisp_intrinsics::alloc::heap_alloc` etc. in the current `intrinsic_symbols()` body — `jit.rs:151`). Consuming `INTRINSICS_TABLE` adds no new dep edge; the DAG is unchanged. Backend still has **no** dep on `cranelisp-primitives` (Decision 0048 dep-ban) — `INTRINSICS_TABLE` is intrinsics-only; user-callable primitives reach codegen through the GOT, never through this catalog (`jit.rs:108` invariant preserved).

### 2.5 Baseline-regen note

Deleting `intrinsic_symbols()` + `IntrinsicSymbol` (already `pub(crate)`, so NOT in the public baseline) does not move `crates/cranelisp-backend/public-api.txt`. The change is internal. `cranelisp-intrinsics/public-api.txt` gains `INTRINSICS_TABLE` — that baseline regen is `/dev (intrinsics)`'s, not backend's. Backend's only baseline movement this wave is §1.6's `Jit::new`.

---

## §3 `.meta.json` platform schema — FIXME 0232

### 3.1 The obligation

The platform-as-module migration (FIXME 0233) registers platform DLLs as cranelisp modules at `symbol_tables["platform.<name>"]` (spec §8.9.3; `crates/cranelisp-types/src/module.rs:976`). On cache-hit, the host must re-parse the DLL's `Schema` (the ADT-marshaling layout declarations) to re-populate the loaded DLL's `LazyLock<Schema>` static — but the cache (`.meta.json`, per-module) has no canonical place to store the schema text for cross-session continuity (FIXME 0232).

### 3.2 Backend's part of the round-trip

The `.meta.json` is the serialised `SymbolTable` (`cache/serialize.rs` — `serialise_meta(table, schema_version)`). It is NOT a hand-rolled JSON envelope (the legacy `CacheMetadata` is doc-deprecated — `serialize.rs:342`); the schema is whatever `SymbolTable` serializes via serde. So the `schema_literal` field lands as a **field on the platform module's `SymbolTable`**, serialized for free.

**Backend's part is the sidecar emission + round-trip plumbing; the field itself is a `cranelisp-types` addition (filed to /arch).** Concretely:

1. **Field (filed to /arch).** The platform module's `SymbolTable` needs a `schema_literal: Option<String>` (or, more precisely-typed, alongside the existing `platforms: Vec<PlatformSpec>` structural-decl list — the schema is a platform-module property). Backend does not author `cranelisp-types`; **FIXME `target: /arch`** proposing the field, citing 0232's proposed JSON shape and that it rides the existing serde round-trip (no new serializer). Optional/defaulted (`schema_literal: None` / `""`) so pre-S71 DLLs (stdio, test-capture) cache without it — 0232 §"Operational implication".
2. **Write side.** When the nice worker emits the platform module's cache pair (`compile_to_module::<ObjectModule>` + caller `finish().emit()` + sidecar `SymbolTable<(), ()>`), the `schema_literal` is already on the sidecar table (it was set at platform-module registration). No backend code change beyond the field existing — serde carries it. **The `schema_literal` is NOT ABI-version-bumping** (0232 §"Operational implication" — it is cache-layer, not DLL-boundary); `CACHE_SCHEMA_VERSION` (`cache/mod.rs`) bumps only because the serialized `SymbolTable` shape changed (adding a field is a schema change → bump to invalidate stale caches gracefully, not a cryptic deserialise error — Decision 34 / `backend.md` §6.3).
3. **Read side.** On cache-hit, `deserialise_meta` (`serialize.rs:235`) reconstructs the `SymbolTable` including `schema_literal`. Backend's `load_object` path hands the reconstructed sidecar table back to int; int's platform loader (0233) reads `schema_literal` and re-parses it host-side (cheap, sub-ms — 0232 §"Proposed resolution") to re-populate the DLL's `LazyLock<Schema>`, re-validating against the current typecheck symbol-table (FIXME 0231).

### 3.3 Disposition / sequencing

This is **W-Integrate, platform host-wiring wave** (0229–0235), which the Phase-2 review confirmed lands **after** the int W-Absorb cascade defines the host surface. Backend's piece (sidecar schema round-trip) is small and rides the existing serde path; the only authored artefact is the `CACHE_SCHEMA_VERSION` bump + the FIXME to /arch for the `cranelisp-types` field. Sequenced with 0230 (`parse_type_expr`, /frontend) + 0231 (platform sig typecheck, /typecheck) as upstream producers; 0229/0233 (/int) as the host-side consumers of the round-tripped schema.

**Action items:**
- FIXME `target: /arch` — add `schema_literal` to the platform module's `SymbolTable` (cite 0232 + this §3).
- `/dev (backend)` — bump `CACHE_SCHEMA_VERSION` in the same change-set the field lands (serialized shape changed); confirm `serialise_meta`/`deserialise_meta` round-trip the new field (a `cache/serialize.rs` unit test — §5).

---

## §4 0122 `--link` GOT-alignment defect — re-test + fix

### 4.1 The defect

Four `tests/build_confidence.rs` mode-equivalence repros (`mode_equiv_adt_option_match`, `mode_equiv_pattern_match_nested`, `mode_equiv_macro_user_defined`, `mode_equiv_io_pure_primitive`) pass through REPL/`--run` (fresh + cached) but FAILED `--link` (S64) with macOS `ld`:

```
ld: warning: alignment (1) of atom '___cranelisp_got_user' is too small ... → linker error
```

The GOT data atom emitted into the user/prelude `.o` declared alignment 1; macOS `ld` rejects pointer-relocation-carrying atoms that are not pointer-aligned. Shape-specific (ADT ctor / `match` / user defmacro / `Pure` IO — i.e., programs whose GOT carries non-trivial slot contents), per FIXME 0122.

### 4.2 The fix is already in source — this is a RE-TEST, not a new fix

The `ObjectModule` impl of `CodeFinalizer::define_module_got_data` (`crates/cranelisp-backend/src/lib.rs:354-428`) already carries the fix, with a comment that names the exact 0122 diagnostic:

```rust
desc.set_align(8);   // lib.rs:388 — "macOS ld rejects unaligned atoms carrying pointer-sized relocations"
desc.define(vec![0u8; slot_count * 8].into_boxed_slice());  // regular __DATA, NOT __bss (S_ZEROFILL) — ld segfaults relocating BSS
```

Both halves of the likely-correct fix are present: (a) `set_align(8)` (the alignment-1 defect directly); (b) `define(zeros)` rather than `define_zeroinit` so the atom lands in regular `__DATA` (relocations against `S_ZEROFILL` segfault `ld` on macOS). This is the §5.3 Wave-2 `define_module_got_data` work from `compile-to-module.md`, landed since 0122 was filed (S64).

**Therefore the S76 plan for 0122 is: re-test once the workspace builds (W-Green), not re-investigate.** The four repros are present, un-ignored, in `build_confidence.rs` (verified — no `#[ignore]`). They are the durable record either way per `feedback_repros_join_suite`.

### 4.3 Re-test plan + contingency

1. **W-Green gate.** 0122 is gated on `link.rs` + `build_confidence.rs` running, which needs the workspace green (the binary is currently red — int W-Absorb/W-Collapse must land first). Re-test runs in W-Integrate, after W-Green.
2. **Re-run** the four repros through `--link` (fresh + cached): `cargo nextest run --test build_confidence mode_equiv_adt_option_match mode_equiv_pattern_match_nested mode_equiv_macro_user_defined mode_equiv_io_pure_primitive`. `run_through_all_modes(...).assert_all_equal(N)` already exercises `--link` (the helper covers REPL/`--run`/`--link` × fresh/cached).
3. **If green** (expected — the fix is in source): 0122 resolves; `/dev (backend)` or `/sprint` `git rm`s `design/arch/fixmes/0122-*.md` with a commit naming "the `set_align(8)` + regular-`__DATA` fix (lib.rs:388) re-tested green across the four mode-equivalence repros". No code change. Annotate the four tests' `// spec:` lines need no change; the ledger row (`tests/plan/ledger.md` — `out-of-scope (owner=/backend)`) flips to covered.
4. **If still failing** (contingency): the remaining divergence is a *different* GOT-shape bug than the alignment-1 one already fixed. Reduce per `tests/CLAUDE.md` §"Isolating Cross-Crate Failures" + the small-CLIF-by-eye discipline (`/clif` / `CRANELISP_CODEGEN_TRACE=1`): shrink to the smallest failing shape (likely the bare `(match (Some 7) ...)` ctor case), inspect the emitted `.o`'s GOT atom (`otool -l` / `objdump --section-headers` for section placement + alignment), and check whether (a) the prelude module's GOT (`___cranelisp_got_prelude`) — not just `user` — also needs the alignment/section treatment, or (b) a *different* `.o` (the cache-`.o` path vs the `--link`-`.o` path) emits the GOT via a code path that does not go through `define_module_got_data`. Land the narrowed repro as a committed failing-not-ignored test regardless (it is the smaller regression guard). The fix, if needed, stays in `define_module_got_data` (or its prelude-module invocation in `lib.rs:724`).

### 4.4 Baseline / interaction note

`define_module_got_data` is `pub(crate)` (a `CodeFinalizer` trait method on backend's internal trait); the fix is internal — **no baseline change**. 0122 does **not** interact with §1's `Jit::new` (JIT mode's `define_module_got_data` is a no-op — `lib.rs:325`/`5104`; the alignment fix is object-mode-only). It is sequenced independently within W-Integrate, gated only on W-Green.

---

## §5 Unit-test placement (per `feedback_unit_tests_with_dev` — `/dev` authors, in-crate)

`/design` notes the coverage obligations; `/dev (backend)` authors these inside `crates/cranelisp-backend/src/`. `/qa` owns any e2e in `tests/` (the 0122 mode-equiv repros already exist; the platform round-trip e2e is 0235's, /qa).

| Obligation | Test | Crate-narrow shape |
|---|---|---|
| §1 `Jit::new(symbol_tables)` | `jit.rs` `#[cfg(test)]` | Build a `SymbolTables` with two modules (one carrying a `PlatformEffect` def with a populated GOT slot, one plain) + a populated `got().base_ptr()`. `Jit::new(&tables)` → assert it constructs Ok; assert the GOT-data symbol + platform jit-name are registered (observable via compiling a tiny GOT-indirect fn and finalizing — reuses the existing `compile_to_module_writes_got_slot_after_finalize` harness shape). Mirror the existing `from_isa`/`new_with_symbols` tests at `jit.rs:794+`. |
| §1 narrowing | `jit.rs` / baseline | The `pub(crate)` narrowing of `new_with_symbols`/`new_with_isa` is verified by the `public-api.txt` diff (they leave the baseline). No bespoke test. |
| §2 `INTRINSICS_TABLE` consumption | `jit.rs` `#[cfg(test)]` | Assert `declare_intrinsics_generic` over a stub `Module` declares one `FuncId` per `INTRINSICS_TABLE` record with the right param count (replaces any `intrinsic_symbols()`-keyed assertion). Confirms the re-point preserves the 15-symbol set. |
| §3 `.meta.json` schema | `cache/serialize.rs` `#[cfg(test)]` | Extend the existing round-trip test (`serialize.rs:439`): set `schema_literal: Some("((Rectangle ((CLInt w) (CLInt h))))")` on a `SymbolTable`, `serialise_meta` → `deserialise_meta`, assert the field round-trips and `schema_version` matches post-bump. |
| §4 0122 | (no new unit test) | The fix is exercised by the four e2e `build_confidence.rs` repros (the right level — `--link` is an e2e concern, not unit). Contingency-narrowed repro (if §4.3 step 4 fires) is a /qa e2e in `tests/`, not a backend unit test. |

---

## §6 Flags for /arch

1. **FIXME `target: /arch` — `schema_literal` field on the platform module `SymbolTable`** (§3.2 item 1). Backend cannot author `cranelisp-types`; the field is the one cross-crate type the 0232 round-trip needs. Cite 0232 + this §3. *(Filed alongside this Phase-3 doc.)*
2. **No other cross-crate type needed.** `Jit::new(symbol_tables)` consumes `SymbolTables<C, L>` (exists), `got_data_symbol_name` (types, exists — `module.rs:1722`), `INTRINSICS_TABLE` (intrinsics pub, approved target-stated by Phase-2 review, authored by /dev intrinsics). No backend public surface grows beyond `Jit::new` (Phase-2 review Q1/Q2 confirmed).
3. **W-Macro NO-OP for backend** (stated up top) — flagged here only so /arch's W-Macro cascade does not expect a backend /dev wave. None is owed.
