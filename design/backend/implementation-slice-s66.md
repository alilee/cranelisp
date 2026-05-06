# Sprint 66 implementation slice — `cranelisp-backend`

**Status.** draft
**Author.** `/design` (backend), 2026-05-06
**Reads.** `design/arch/facades/backend.md` (final, S65 close); `design/arch/facades/primitives.md`; `design/arch/facades/intrinsics.md`; `design/arch/facades/types.md`; `design/arch/facades/int.md`; `design/arch/decisions/0041-compile-to-module-per-symbol-jit-direct-writes.md`; `design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md`; `design/arch/decisions/0042-platform-error-adopts-error-location.md`; `design/arch/fixmes/0099-*.md`, `0100-*.md`, `0108-*.md`, `0150-*.md`; `design/backend/backend.md` (master); `design/backend/compile-to-module.md` (subordinate). `/qa` S66 test plan slice — when available.

Authored against the slice template at `design/arch/sprint-65-reshape-phase-2-review.md §3`.

---

## 1. Scope from facade

The post-S65 facade `design/arch/facades/backend.md` is target-stating; this slice enumerates the deltas between facade and `crates/cranelisp-backend/src/`. Each row is one logical change.

| # | Delta | Source location(s) | FIXME closed | Acceptance |
|--:|---|---|---|---|
| 1 | Collapse `compile_to_module<M, C, L>` two-front-door entry to `compile_to_module<M: Module>` per facade §"Public surface" + Decision 41. Signature becomes `(scope, names, &DashMap<…, SymbolTable<Code, ()>>, Option<&DashMap<FQSymbol, Introspection>>, M) -> Result<(), CompilationError>`. Drop `<C, L>` generics; freeze `C = Code`, `L = ()`. Remove `CompilationResult` return tuple. | `lib.rs:405` (entry), `lib.rs:24` (`CompilationResult` struct), `compiler/mod.rs` (`CompileContext`), `jit.rs:480` (parallel `Jit::compile_defn`) | 0150 (Phase 3 collateral via D43 backend revisions); contract source 0041 | (a) one public `compile_to_module` symbol; (b) `cargo public-api` shows no `<C, L>` generics on `compile_to_module`; (c) returns `Result<(), CompilationError>` per `audits/backend-20260423.md` Phase 1; (d) `Jit::compile_defn` deletion observed in source. |
| 2 | Backend writes `Code::Jit { jit, ptr }` directly into each compiled symbol's entry via `SymbolTable::write_code(&self, sym, code)` (Decision 38; interior-mutable). Backend writes `Introspection { clif_ir, disasm, code_size, compile_duration }` into the introspection map iff `introspection.is_some()` per Decision 38 mode discriminator. | `lib.rs:405` body (post-finalize loop); int's existing `worker.rs:2860-3018` post-loop is deleted on int side (cross-crate; covered by `int` slice) | 0041 | Backend body emits one `?` cascade; on success, every `name` in `names` has `Code` written to its entry and (when `introspection.is_some()`) an `Introspection` entry. Test `tests/v4_jit_reclaim.rs::decision31_scenario2_per_redefinition_jit_pages_reclaimed` verifies per-symbol immediacy. |
| 3 | Move `Code` enum from `src/code.rs` to `crates/cranelisp-backend/src/code.rs`. Backend constructs `Code::Jit` directly. `unsafe impl Send for Code {}` + `Sync` retained per facade §"Code". Re-export from `cranelisp-backend` as the canonical home; `int` imports from there for `SymbolTable<Code, ()>` instantiation. | `src/code.rs` (deletes); `crates/cranelisp-backend/src/code.rs` (new); `crates/cranelisp-backend/src/lib.rs` `pub mod code; pub use code::Code;`; `src/` callsites (cross-crate; covered by `int` slice) | 0041 | `Code` definition lives in `cranelisp-backend`; `cranelisp-types` does NOT import `Code` (Principle 3 protected). Confirmed via `cargo public-api` on the types crate. |
| 4 | Per-symbol JIT cardinality at JIT-mode `compile_to_module` callers (length-1 `names`). Backend body itself does not branch on cardinality — body iterates `names` regardless. The cardinality contract is upheld at the **caller** (int worker loop). Backend's only obligation is to not assume length > 1 (no batch-amortisation that would hold across calls). | `lib.rs` body (verify no per-call shared state across iterations) | 0041 | Object mode produces a single `compile_to_module` call with full module's `defined_symbols()` `names`; JIT mode produces N calls with length-1 `names`. Both produce byte-identical CLIF for matching defns. |
| 5 | Define `CompilationError` enum per facade §"Errors" with variants `SymbolNotCompilable { module, symbol }`, `CodegenFailed { module, symbol, cause, location: ErrorLocation }`, `ModuleError { module, symbol, cause }`, `#[non_exhaustive]`. Replace ad-hoc `CranelispError::CodegenError { message: "..." }` strings at the boundary with typed variants. Type **lives in `cranelisp-backend`** per Principle 15 (single-consumer; backend originates, only `int` consumes). | `lib.rs` (current `CranelispError::CodegenError { message, span }` returns at lines 421/430/441/449); new file `crates/cranelisp-backend/src/error.rs`; `cranelisp-types` removes any prior `CompilationError` placeholder | 0100 (Phase 2 — single-consumer relocation); contract source §2.7 | `cargo public-api` on `cranelisp-backend` shows `CompilationError`; `cranelisp-types` does not. `CranelispError::Backend(CompilationError)` carrier stays in `cranelisp-types` per Decision 42's per-domain-error pattern (verify against types.md). |
| 6 | Implement `GotObserver` extension point per facade §"GOT-population observation": new file `crates/cranelisp-backend/src/got_observer.rs` with `GotEventTag` enum (`JitWrite`, `LinkerWrite`, `Redefinition`, `#[non_exhaustive]`), `GotEvent` struct, `GotProvenance` enum (`Jit { jit_addr }` \| `Linker { linker_addr }`), `GotObserver` fn type, `register_got_observer(observer: Option<GotObserver>)` free function with atomic-replace semantics. Wire emission sites: (a) `compile_to_module` `write_code` site — emit `JitWrite`; (b) `Linker::load_object` slot-population — emit `LinkerWrite`; (c) detect redefinition via "entry already had `Code::Jit` before write" — emit `Redefinition`. Production batch (no observer) pays one relaxed-load null check per call. | new `got_observer.rs`; emit calls in `lib.rs` post-finalize loop; emit calls in `cache/linker.rs:183` slot-fill loop | 0099 (this FIXME's Phase 1 closes); also closes 0100 Phase 2 for these types | (a) `cargo public-api` shows the four types + free function on `cranelisp-backend`; (b) integration test in `int` (Phase 2 of FIXME 0099, separate slice) sets observer and observes events; (c) `CRANELISP_GOT_TRACE=1` enabled session produces non-empty event stream. |
| 7 | Move `display.rs` from `crates/cranelisp-backend/src/display.rs` (831 LOC) to `src/display.rs` (or sub-module of `src/`) per BC §6 (REPL display orchestration belongs to `int`). Mechanical relocation: `cranelisp-backend/src/lib.rs` removes module declaration; int's callsites switch from `cranelisp_backend::display::*` to `crate::display::*`. Pre-existing display tests move with the file. | `crates/cranelisp-backend/src/display.rs` (deletes); `crates/cranelisp-backend/src/lib.rs` (`pub mod display;` line removes); `src/` (new home; cross-crate, covered by `int` slice) | 0108 | Backend's footprint reduces by ~10%; `cargo public-api` on backend no longer exports `display::*`. Backend's `Cargo.toml` may drop deps the relocated file pulled in (verify; likely none). |
| 8 | Delete trait-knowledge maps per Decision 43 / D14 retraction. Specifically: (a) delete `operators.rs:323-394` `primitive_for_trait_method(t, m, i) -> Option<&'static str>` and the entire `(TraitName, Symbol, TypeName) → primitive-name` table; (b) delete `compiler/literals.rs:323-340` `operator_extern_name(name: &Symbol) -> Option<&'static str>` and the parallel `"+" → "cranelisp_op_add"` map. The substitution table at `operators.rs` line 38 (`"add-i64" => iadd`) survives — name-keyed only. | `operators.rs:323-394` (delete) + corresponding tests `operators.rs` test module (delete `primitive_for_trait_method` tests); `compiler/literals.rs:323-340` (delete) + the operator-as-value codepath that calls `operator_extern_name` (rewrite to GOT-indirect through `+`'s `primitives/<op>` symbol-table entry) | 0150 (Phase 3) | (a) `grep -rn "primitive_for_trait_method\|operator_extern_name\|cranelisp_op_" crates/cranelisp-backend/` returns zero matches; (b) `(let [f +] (f 1 2))` test passes via the `+`-symbol-table-entry's GOT slot, NOT via `cranelisp_op_add`; (c) backend has zero `TraitName`/trait-method names in source. |
| 9 | Rename `crates/cranelisp-backend/src/operators.rs` → `crates/cranelisp-backend/src/primitives_inline.rs` per Decision 43. The surviving substitution table (at line 38 — `"add-i64" => iadd`, etc.) keeps its shape; the file is renamed to reflect its post-D43 purpose (name-keyed inline-substitution at backend's direct call sites, sourced from `primitives/<name>`). | `operators.rs` → `primitives_inline.rs` (rename); `lib.rs` `pub mod operators;` → `pub mod primitives_inline;` (or removed if not pub) | 0150 (Phase 3) | File renamed; CLIF emission for inline-substituted primitives byte-identical pre/post. |
| 10 | Backend's `Cargo.toml` revises depends-on declarations per Decision 43 + facade §"Consumed surface": ADD `cranelisp-primitives` (for the inline-substitution table's name-keying surface alignment + symbol-table seeding registration), ADD `cranelisp-intrinsics` (for backend-emitted-call relocation-time bindings; not a `use` dep but the `.o` resolves intrinsic names against this archive). DROP `cranelisp-runtime` (retires per FIXME 0150 Phase 5). | `crates/cranelisp-backend/Cargo.toml` `[dependencies]` block | 0150 (Phase 3 collateral) | `cargo metadata --format-version 1` on `cranelisp-backend` shows the post-D43 dep set; build green. |
| 11 | Update `jit.rs` `IntrinsicSymbol` registration array per Decision 43: REMOVE `cranelisp_op_*` entries (10 fns: `cranelisp_op_add` … `cranelisp_op_ge`); KEEP the legitimate intrinsics (e.g., `cranelisp_alloc`, `heap_alloc_payload`, `rc_inc`, `rc_dec`, `runtime_panic`, `cranelisp_run_io`, `vec_*`, `ivar_*`, `int-to-string`, `bool-to-string`, `parse-int`). The kept names registered come from `cranelisp-intrinsics` (allocator, RC, panic, IO trampoline) and `cranelisp-primitives` (the named primitives' fn ptrs for indirect call from GOT slots). | `jit.rs` `IntrinsicSymbol` array (~line 166 per audit reference) | 0150 (Phase 3) | Array contains zero `cranelisp_op_*` entries; the operator-as-value test (delta #8) goes through GOT, not direct extern. |
| 12 | Replace `Linker::get_symbol(&self, name: &str) -> Option<*const u8>` with `Linker::get_symbol(&self, name: &LinkerSymbol) -> Result<*const u8, LinkerError>` per facade §"Linker" + Decision 36 + Decision 37 (no swallowed failures). Define `LinkerError` in `cranelisp-backend/src/error.rs` (next to `CompilationError`). Refactor `cache/linker.rs:183` callers; cache-hit caller in backend's own `load_object` returns `Result<LinkerArtefact, CranelispError>` per facade. | `cache/linker.rs:183` (signature change); `cache/linker.rs:192` (`load_object`); new `error.rs::LinkerError` | 0100 (Phase 2 — single-consumer relocation, includes `LinkerError`) | (a) `Linker::get_symbol` returns `Result`, not `Option`; (b) test exists that exercises the failure case (cache-hit with missing symbol surfaces `LinkerError`, NOT silent NULL — pre-S58 regression net per Decision 37). |
| 13 | Reshape `load_object` from method (`Linker::load_object(&mut self, _module_name, bytes)`) to backend free function `pub fn load_object(module: &ModuleFullPath, object: &[u8], symbol_tables: &SymbolTables) -> Result<LinkerArtefact, CranelispError>` per facade §"Public surface". `LinkerArtefact { linker: Arc<Linker>, ptrs: HashMap<Symbol, *const u8> }` is a thin DTO; mark `#[non_exhaustive]`. Internals (mmap + relocator) unchanged; the free function constructs `Arc<Linker>` and resolves bare-name symbols (Decision 36). | `cache/linker.rs:192` (refactor); `lib.rs` `pub use cache::load_object;` | 0150 (Phase 3 collateral); contract source §"Public surface" | `cargo public-api` on `cranelisp-backend` shows `load_object` as a free function returning `LinkerArtefact`. The original method becomes private or deletes. |
| 14 | Define `LinkerArtefact` and `ObjectArtefact` `#[non_exhaustive]` DTOs per facade §"Return shapes". Replace `compile_to_object`'s current return shape with `Result<ObjectArtefact, CranelispError>` where `ObjectArtefact { object: Vec<u8>, sidecar: SymbolTable<(), ()> }`. | `cache/object.rs::compile_to_object` signature; new `LinkerArtefact` + `ObjectArtefact` types in `lib.rs` or sub-module | 0150 (Phase 3 collateral); contract source §"Return shapes" | `cargo public-api` reflects the two DTOs; `int`'s `ObjectCache::write` consumes `ObjectArtefact.object` + `ObjectArtefact.sidecar` for the paired-file write per Decision 25. |
| 15 | Confirm `PlatformError` carriers reach backend via `CranelispError::Platform { error: PlatformError, location: ErrorLocation }` per Decision 42. Backend does not originate `PlatformError`; it surfaces it through `CranelispError` when codegen paths cross platform boundaries (e.g., emitting a call to a platform fn whose declared signature deserialisation failed). Verify backend's error-propagation paths preserve `ErrorLocation`. | grep `PlatformError` in `crates/cranelisp-backend/src/`; verify all error-construction sites set `location` if applicable | facade contract source D42 (no FIXME — verification only) | No `PlatformError` constructed without an `ErrorLocation` carrier in backend; `cargo build` green; relevant integration test in `tests/` exercises a platform-related codegen path with location-bearing error. |
| 16 | Delete deletion candidates per audit MED-1: `crates/cranelisp-backend/src/got.rs` (9-line compatibility re-export) and `crates/cranelisp-backend/src/codegen_types.rs` (9-line compatibility re-export). Update `lib.rs` `pub use` lines accordingly. | `got.rs` (delete), `codegen_types.rs` (delete), `lib.rs` (re-export removals) | (audit-driven; no FIXME) | Files removed; `cargo public-api` shows no missing types (consumers updated to import from canonical locations). Test green. |

**Row count: 16.** Action-class breakdown:

- **Reshape (5)**: rows 1, 2, 12, 13, 14 — facade-driven public-surface shape changes (signature, return shape, error type).
- **Relocate (3)**: rows 3, 5, 7 — moves between crates per Principle 15 / BC §6.
- **Delete (3)**: rows 8, 11, 16 — trait-knowledge maps + duplicate `cranelisp_op_*` registrations + dead compatibility files.
- **New (1)**: row 6 — GotObserver contract + emission wiring.
- **Rename (1)**: row 9 — `operators.rs` → `primitives_inline.rs`.
- **Cargo.toml (1)**: row 10 — dep set revision.
- **Verify-only (2)**: rows 4, 15 — assertions that the existing body upholds an invariant.

---

## 2. Ordering within the slice

Three internal phases, each a unit; phase-internal deltas can be parallelised within a `/dev` agent's context budget where independent.

**Phase A — Type + module relocations (rows 3, 5, 7, 16; row 9 partial — rename)**
Land before public-surface reshape so subsequent steps work against the new homes. Independent of each other (modulo the `display.rs` move being a single mechanical rename); can run in parallel. Row 9 (`operators.rs` rename) lands here too — pure rename, no semantic change yet.

- Move `Code` to `cranelisp-backend/src/code.rs` (row 3).
- Add `crates/cranelisp-backend/src/error.rs` with `CompilationError` + `LinkerError` (row 5 + row 12 type).
- Move `display.rs` to `src/` (row 7 — coordinates with `int` slice).
- Delete `got.rs`, `codegen_types.rs` (row 16).
- Rename `operators.rs` → `primitives_inline.rs` (row 9).

**Phase B — D43 substantive deletions + Cargo.toml (rows 8, 10, 11)**
Lands the trait-knowledge map deletion + intrinsic registration prune + dep-set revision. Sequenced AFTER Phase A so the rename has settled. Row 8 (delete trait-knowledge) and row 11 (prune `IntrinsicSymbol`) MUST land in the same commit pair as stdlib's "trait impls call primitives directly" audit (covered by `/dev (stdlib)` per FIXME 0150 Phase 4) — failing to coordinate breaks the operator-as-value codepath. Row 10 (Cargo.toml) lands when `cranelisp-primitives` + `cranelisp-intrinsics` crates exist (FIXME 0150 Phase 1+2; cross-crate dep — see §4).

**Phase C — Public-surface reshape (rows 1, 2, 4, 6, 12, 13, 14, 15)**
The facade-driven core. Rows 1+2+4 form one coherent change (the `compile_to_module` signature refactor + per-symbol cardinality contract + direct writes). Row 6 (GotObserver) wires into the `compile_to_module` post-finalize loop and `Linker::load_object` slot-population — depends on rows 1+2 being done first, and on row 13 (`load_object` reshape) being done first for the linker emission site. Row 12 + row 13 + row 14 are the cache/linker reshape — coherent unit. Row 15 (PlatformError verify) is independent.

Sequenced ordering within Phase C:

1. Rows 1 + 2 + 4 (one unit — `compile_to_module` reshape).
2. Rows 12 + 13 + 14 (one unit — linker + cache return-shape reshape).
3. Row 6 (GotObserver wiring — depends on emission sites being in their post-reshape shape).
4. Row 15 (PlatformError verify pass — orthogonal; can run anywhere in Phase C).

**Critical coupling point**: rows 1 + 2 + 3 (signature + writes + Code home) must land **together** with the int-side post-loop deletion (`worker.rs:2860-3018`). The change set spans backend slice + int slice; `/sprint` schedules them as a paired wave.

---

## 3. Estimated effort

**Sizing: two triad cycles** (one for Phase A + B; one for Phase C). Equivalent to ~3–5 days of focused `/dev (backend)` work paired with `/dev (int)` for the cross-crate coordination. Drivers:

- Phase A: largely mechanical (type moves, file deletions, file rename). ~half a triad cycle.
- Phase B: row 8's `compiler/literals.rs` operator-as-value codepath rewrite is the substantive work — must verify the GOT-indirect path produces correct CLIF for `(let [f +] (f 1 2))`. Row 11 prune is tracked-down deletion. Cargo.toml is trivial. Cross-crate coordination required (stdlib audit landed before row 8 takes effect). ~half a triad cycle.
- Phase C: rows 1+2+3 are the largest single refactor in the slice. The audit `audits/backend-20260423.md` Phase 1 (single-front-door collapse) is concurrent — `Jit::compile_defn` deletes, `CompileContext` builders converge, `build_isa` consolidates. Row 6 GotObserver is ~150 LOC new code + emission sites. Row 12-14 linker reshape is ~200 LOC refactor. ~one full triad cycle.

`/sprint` may sub-divide if the W4a wave envelope is tighter; the natural dividing line is Phase A+B vs Phase C.

---

## 4. Dependencies on other crates' slices

Bilateral cross-crate dependencies. Each row here MUST have a matching entry in the named slice. This table is the slice-coordination substrate `/sprint` consults at S66 wave-plan time.

| This slice's item | Depends on (the cross-crate landing) | In the other crate's slice |
|---|---|---|
| Row 3 (`Code` move from `src/` to backend) | `int` deletes `src/code.rs`; switches imports to `cranelisp_backend::Code`; instantiates `SymbolTable<Code, ()>` from backend's re-export | `int` slice — `Code` import path update; post-loop deletion at `worker.rs:2860-3018` |
| Row 1+2 (signature + direct writes) | `int` worker call sites switch to per-symbol JIT-mode loop (length-1 `names`); deletes the post-loop iteration that previously constructed `Code::Jit` from a return tuple | `int` slice — per-symbol JIT loop + post-loop deletion |
| Row 5 (`CompilationError` location) | `int` callsites import `CompilationError` from `cranelisp_backend` instead of `cranelisp_types`; `cranelisp-types` removes the type if currently a placeholder | `int` slice — import path update; `types` slice — confirm absence post-relocation |
| Row 6 (GotObserver contract) | `int` implements the ring-buffer state in `src/got_trace/`; `int` registers the observer at session startup conditional on env var or `introspection.is_some()` | `int` slice (FIXME 0099 Phase 2) |
| Row 7 (`display.rs` move) | `int` adds the new module under `src/`; `int` callsites switch to `crate::display::*` | `int` slice — display module landing + callsite updates |
| Row 8 + 11 (trait-knowledge map + `cranelisp_op_*` deletes) | stdlib trait impls (`(impl Num Int)` etc.) audited so each impl body calls the primitive directly; no impl relies on backend's collusion | stdlib slice (FIXME 0150 Phase 4) |
| Row 10 (Cargo.toml `cranelisp-primitives` + `cranelisp-intrinsics` add) | Both new crates exist with the migrated source; `cranelisp-runtime` either retires or is in the retiring slice's transitional state | `primitives` slice + `intrinsics` slice (FIXME 0150 Phase 1+2); `runtime-retiring` slice (FIXME 0150 Phase 5) |
| Row 12 (`Linker::get_symbol` typed result + `LinkerSymbol`) | `cranelisp-types` confirmed `LinkerSymbol` newtype final per S64 substance §2.6 (already landed); `int` cache-load callsites match on `LinkerError` | `types` slice (verify-only); `int` slice (cache-hit error handling) |
| Row 13 (`load_object` free fn) | `int` cache-hit path switches to free-function call; constructs `Code::Linker` per resulting `LinkerArtefact.ptrs` | `int` slice — cache-hit refactor |
| Row 14 (`ObjectArtefact`) | `int` `ObjectCache::write` consumes `ObjectArtefact.object` + `ObjectArtefact.sidecar` | `int` slice — `ObjectCache::write` refactor |
| Row 15 (PlatformError flow) | `cranelisp-types` confirmed `PlatformError` + `ErrorLocation` final per Decision 42 | `types` slice + `platform` slice (verify-only) |

**Cross-crate dependency count: 11 deltas in this slice depend on landings in 7 other slices** (`int`, `types`, `stdlib`, `primitives`, `intrinsics`, `runtime-retiring`, `platform`). The largest coupling is to **`int`** (8 of 11 rows) — backend ↔ int are the D41 mutref pattern boundary. The runtime-retiring + primitives + intrinsics slices co-land Cargo.toml (row 10) with this slice; sequencing requires the new crates to exist before this slice's Phase B.

---

## 5. Test surface impact

### New tests this slice enables

- **GotObserver integration test** (`tests/got_observer_smoke.rs` or similar in `tests/`): exercises observer registration; emits `JitWrite` from a `compile_to_module` call; emits `LinkerWrite` from a cache-hit `load_object`; emits `Redefinition` from a REPL redefinition. **`/qa` slice** must enumerate this test if it does not already; if not, **file FIXME against `/qa`**.
- **`CompilationError` typed-variant tests** in `crates/cranelisp-backend/src/lib.rs` (or unit module): `SymbolNotCompilable` returned when caller passes a name not in `defined_symbols()`; `CodegenFailed` carries `ErrorLocation`. Replaces ad-hoc `CranelispError::CodegenError { message }` string assertions in current backend tests.
- **`Linker::get_symbol` typed-result tests** at `cache/linker.rs` test module: failure case surfaces `LinkerError`; pre-S58 silent-NULL regression net per Decision 37 — write the test that would have caught the original regression.
- **`(let [f +] (f 1 2))` regression test** (likely already exists; if so, must continue passing post-D43 deletes; if it relied on `cranelisp_op_add` symbol presence, refactor). `/qa` slice should cite the test name.

### Existing tests changing shape

- `tests/v4_jit_reclaim.rs::decision31_scenario2_per_redefinition_jit_pages_reclaimed` — assertion strengthens from "after batch" to "after single-symbol redefinition" per Decision 41. **No code change needed in the test if it already names a single redefinition; verify on slice landing.**
- Backend unit tests that rely on `primitive_for_trait_method` (visible in `operators.rs` test module — `test_num_add_int_maps_to_add_i64` etc.): **DELETE per row 8**. The function they tested is gone. `/qa` slice should cite which integration tests cover the post-D43 path so the deletion's coverage is preserved.
- Tests at `lib.rs:3331` and `lib.rs:3391` (`compile_to_module_returns_code_ptrs_after_finalize`, `compile_to_module_object_mode_empty_code_ptrs`) **rewrite shape** per row 1+2 — assertion changes from "returns `CompilationResult` with code_ptrs" to "writes `Code::Jit` directly into passed-in symbol table; returns `Ok(())`".
- `display.rs` internal tests **move with the file** to `src/` (row 7). Backend's test count drops; int's test count rises by the same amount. Net zero.

### `/qa` test plan slice action items

If `/qa`'s S66 plan slice does not enumerate the four new tests above, file `target: /qa` FIXME naming the gaps. (Slice does not pre-empt `/qa`'s authoring; it surfaces the dependency.)

---

## 6. Open questions

These surfaced during slice authoring; the facade does not pin the answer. File as `target: /arch` FIXMEs at slice landing.

- **OQ-1 — Cardinality of GotObserver registration ordering**: facade §"GOT-population observation" commits to "atomic replace, last write wins under happens-before ordering." Implementation question: does `register_got_observer(Some(_))` followed concurrently by `register_got_observer(None)` from a different thread, where between the two writes a `compile_to_module` call fires an event — is the event observed by the first observer, the second observer, or neither? Facade says happens-before-ordered; concrete: the emission-site relaxed-load result is the binding. Confirm. **File `target: /arch`.**
- **OQ-2 — `LinkerError` variant set**: facade pins `Linker::get_symbol -> Result<*const u8, LinkerError>` but does NOT enumerate `LinkerError`'s variants. Slice authoring proposes: `SymbolNotFound { name: LinkerSymbol }`, `RelocationFailed { name: LinkerSymbol, cause: String }`, `#[non_exhaustive]`. Confirm — or `/arch` files an additional row in `facades/backend.md` §"Errors". **File `target: /arch`.**
- **OQ-3 — `CompilationError::CodegenFailed.location`**: facade pins `location: ErrorLocation` per Decision 42 alignment but the existing `lib.rs` `CodegenError { message, span }` carries a `Span`, not an `ErrorLocation`. Mapping: `Span` → `ErrorLocation::Source { span }`? Confirm the conversion. **File `target: /arch`.**
- **OQ-4 — Object-mode `compile_to_module` introspection semantics**: facade says `Introspection` is written iff `introspection.is_some()`; in object mode, the `compile_to_object` caller may pass `None` because the artefact doesn't carry per-symbol introspection. Verify object-mode `compile_to_object` calls `compile_to_module` with `introspection = None` (or document the alternate flow). **File `target: /arch`** if facade silent.
- **OQ-5 — Audit Phase 1 + 2 + 4 scope inside this slice**: the audit `audits/backend-20260423.md` Phases 1 (single-front-door), 2 (mini-monolith decomposition), 4 (cache cleanup + test relocation) are listed as backend-internal refactors that the contract does not constrain. This slice schedules **Phase 1 implicitly** (via row 1's `Jit::compile_defn` deletion + `build_isa` consolidation) — but Phases 2 + 4 are **not in this slice**. Confirm `/sprint` is OK with deferring those to a later vertical sprint; if not, expand this slice. **Sizing implication: full audit-Phase-1234 expansion would more than double the effort estimate.** Default disposition: defer Phases 2 + 4 to a future `/review`-led vertical.

---

## 7. Cross-references

- `design/arch/facades/backend.md` — facade target (authoritative for §1)
- `design/arch/facades/primitives.md`, `design/arch/facades/intrinsics.md` — post-D43 dep targets
- `design/arch/decisions/0041-*.md`, `0042-*.md`, `0043-*.md` — contract sources
- `design/arch/fixmes/0099-*.md`, `0100-*.md`, `0108-*.md`, `0150-*.md` — implementation trackers this slice closes (or partially closes)
- `design/backend/backend.md` §2.6 (deviations table) — the as-built gaps this slice resolves
- `design/backend/compile-to-module.md` — subordinate; needs Decision-41 update post-slice landing
- `audits/backend-20260423.md` — audit phases referenced; Phase 1 covered by this slice, Phases 2+4 deferred (OQ-5)
- `crates/cranelisp-backend/src/` — implementation surface
- The `int`, `types`, `stdlib`, `primitives`, `intrinsics`, `runtime-retiring`, `platform` slices — bilateral cross-crate dependency partners (§4)
