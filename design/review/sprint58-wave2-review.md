# Sprint 58 Wave 2 Review — Step 5a (structural decls on SymbolTable) + Step 5b (cache via SymbolTable)

**Sprint**: 58 Wave 2
**Date**: 2026-04-19
**Reviewer**: `/review`
**Commit reviewed**: `7236aa7`
**Scope**: `/typecheck` `SymbolTable` field additions (4 structural-decl fields + `schema_version`); `/backend` cache rewrite (`.meta.json` IS a serialised `SymbolTable<(), ()>`, `CACHE_SCHEMA_VERSION = 1`, `Linker::ensure_got_slot`, `CodeFinalizer::define_module_got_data`); `/int` worker structural-decl writers, `try_cache_hit_load` with transitive recursion, `_main` alias `.o` for `--link`, scheduler `inmem_claimed` split, swallowed-failure removal; mid-wave architectural reconciliation (Decisions 23, 25 UPDATED; 36, 37 NEW).

## Verdict

**PASS with Importants.** Wave 2 lands a load-bearing architectural reconciliation cleanly. The Decision-36 bare-Local naming change, the Decision-37 cache-hit-into-`register_module` recursion, and the Decision-23 byte-identical-CLIF + two-GOT-resolver model are correctly implemented at the code level. `cargo check` is clean across the workspace, the per-crate clippy gate holds (zero new warnings in `cranelisp-backend`; ~5 cosmetic `slice::from_ref` lints in newly-added Wave 2 unit-test code in `cranelisp` (binary)), and the 12 cache failures the wave targeted are cleared (17 → 5; 5 = pre-existing, all out of scope).

The Importants below are documentation-hygiene issues: one design doc (`module-caching.md` §14.3) still describes the OLD "re-codegen on cache-hit" semantics that Decision 25 explicitly rewrote in this same wave; the `compile-to-module.md` head FIXME claims §17.1.1's C8 follow-on is unresolved when in fact §17.1.1 IS the resolved follow-on text; and `per-module-got.md` §9.2/§9.3 still describes the old two-load shape per the explicit Wave-2 carry. None of these block Wave 3 from opening — the Wave 2 *code* correctly implements the architectural reframing; only the doc trail lags behind.

## Counts

| Severity | Count |
|---|---|
| Blocker | 0 |
| Important | 3 |
| Suggestion | 6 |

---

## Focus area findings

### Focus 1 — Structural target achievement (Principle 8)

**Verdict**: PASS. The Wave 2 code produces the §9 target shape directly; no leftover stepping stones.

**Decision 36 (bare + Local uniformly)**: Verified at `crates/cranelisp-backend/src/lib.rs:397-411` — the function declaration loop unconditionally calls `module.declare_function(defn.name.as_ref(), Linkage::Local, &sig)`. No `user`/`main` branch, no FQ-vs-bare conditional. The pre-existing `lib.rs:182-186` user/main asymmetry is gone. The `--link` `_main` Export alias is correctly externalised to `src/exe.rs::generate_main_alias_object` per Decision 36's `--link` exception, owned by `/int`, isolated from `compile_to_module`.

**Decision 37 (cache-hit-in-`register_module` recursion)**: Verified at `src/worker.rs:1231-1419` (`try_cache_hit_load`) and `:1438-1517` (`register_transitive_cached_imports`). The bespoke `try_cache_hit_load` orchestration is preserved by name but transformed: the function now ends with `register_transitive_cached_imports(ctx, &cached_imports)` (line 1417), which walks the cached module's `imports` and recursively calls `try_cache_hit_load` for each transitive dep — falling over to `ctx.scheduler.register_module(transitive_dep.clone(), true)` for fresh-build registration on cache miss. This is the recursive `register_module(M)` shape Decision 37 mandates, expressed via the existing handler structure. The four call sites (`handle_import` :1158, `handle_export` :1559, `handle_mod` :1644, prelude injection :2143) all flow through this single recursive entry — Principle 11 is upheld.

**Decision 23 + two-GOT model**: Verified at `crates/cranelisp-backend/src/lib.rs:328-565` — `compile_to_module<M: Module + CodeFinalizer>` has four parameters and no mode discriminator. The two-GOT resolver split is implemented via the `CodeFinalizer::define_module_got_data` trait method (`lib.rs:151-156`): `JITModule`'s impl is a no-op (`:171-183`), `ObjectModule`'s impl declares the symbol as `Linkage::Export` with relocation initializers (`:200-268`). The CLIF emitted by `compile_to_module` is byte-identical in both modes (verified by grep — no mode parameter threads through `apply.rs` or `control_flow.rs`'s GOT-related changes). `__cranelisp_got_{M}` resolves to slab base in JIT mode via `JITBuilder::symbol(name, base_ptr)` (per the unified shape removing the old two-load indirection per `cache/linker.rs:11-30` doc-comment).

**Decision 25 (cache stores both `.meta.json` + `.o`; cache-hit LOADS the `.o`, does NOT re-codegen)**: Verified at `src/worker.rs:2920` — the cache-hit path calls `cache::load_cached_object(&mut linker, &cached)?` which mmaps the `.o` and resolves relocations. The path NEVER calls `compile_to_module` for cache-hit modules. `fn_addrs` populates from the linker (`:2920`), and the per-symbol GOT slot population at `:2935-2955` reads slot indices from the cached symbol table and writes the linker-resolved addresses into the live module's GOT. **No code regeneration on cache-hit.**

**Decision 33 (structural decls on `SymbolTable`; `ModuleStructure` fully deleted)**: Verified — the fields are present in `crates/cranelisp-types/src/module.rs:75-90` (imports, exports, platforms, submodules, all `#[serde(default)]`), and all writes have moved into `SymbolTable` per `src/worker.rs::record_imports_on_symbol_table` and similar helpers. The struct `ModuleStructure` is dissolved — the regression-guard test `module_structure_struct_is_deleted_from_save` at `src/worker.rs:4258-4275` greps `src/save.rs` for `pub struct ModuleStructure` and asserts its absence.

### Focus 2 — Latent bugs and code quality

**Verdict**: PASS for all four sub-focuses. Some Suggestion-level cleanups noted.

**`Linker::ensure_got_slot` (`crates/cranelisp-backend/src/cache/linker.rs:137-183`)** — Per-symbol GOT slots from a `MmapMut` page pool, allocated lazily on first reference. Soundness: the slot address is derived from `page.as_ptr() as usize + slot_byte_offset`; the `MmapMut` is held by `self.got_pool: Vec<memmap2::MmapMut>` (Linker-lifetime owned). Slot exhaustion is handled by allocating fresh pages when `got_pool_used >= SLOTS_PER_PAGE` (512 slots/page). Race conditions: `Linker` is not currently shared across threads — it is constructed per cache-hit codegen worker invocation in `worker.rs::load_cached_module_via_linker`, lives only on the call stack, and the resulting `Linker` is moved into `shared.kept_linkers` after `load_cached_module_via_linker` returns. No `&mut self` race surface today. (See I-3 below for a related design-doc gap on §9.2/§9.3.)

**Scheduler `inmem_claimed` split (`src/scheduler.rs:56, 86, 105, 510-526, 759-772`)** — The split correctly separates the "claim" (worker has picked up this work item) from the "complete" (worker has finished). The wait-complete contract is preserved: `wait_inmem_complete` (`:887-905`) reads only `inmem_done`, never `inmem_claimed`. The unit test `level4_claim_guard_sets_inmem_claimed_not_inmem_done` (`:1768-1820`) directly asserts the invariant ("claim guard MUST NOT pre-set inmem_done — that races against wait_inmem_complete which sees inmem_done=true before the cache-hit worker has finished loading"). The completion notify (`notify_inmem_codegen_batch_complete`, `:771-772`) sets `inmem_done = true` and clears `inmem_claimed = false` atomically inside the lock. **Correct.** No edge case where a claimed-but-not-done slot is misread by `wait_inmem_complete`.

**`CodeFinalizer::define_module_got_data` contract (`crates/cranelisp-backend/src/lib.rs:151-156`)** — Doc comment is comprehensive: `:117-150` describes parameters (name, slot_count, slot_funcs), the JIT vs Object semantics asymmetry, and the cross-reference to Decision 23. The empty-slot-list case (modules with no defined symbols / `slot_count == 0`) is explicitly handled at `:212-215`: "No slots to define. Skip — symbol is not needed by callers." Defensive: returns `Ok(())` without calling `declare_data`, so the module's `.o` simply lacks the symbol. This is correct — a module with zero defined functions has no GOT to publish, and downstream importers will not reference its `__cranelisp_got_M`. **Contract clear.**

**`generate_main_alias_object` (`src/exe.rs:140-238`)** — Generates a small Cranelift `.o` containing one Export `main` function whose body GOT-loads from `__cranelisp_got_{entry_module}` at the slot read off `symbol_tables[entry_module].symbols["main"].got_slot`. The slot index is **NOT hard-coded**; it is computed via `entry_main_got_slot(entry_table)` (`src/exe.rs:245-264`) which reads `entry.got_slot.unwrap()` and surfaces a hard error if `main` is missing or has no slot. The error case (entry module with no `main`) is correctly handled by `validate_main` (`:36-51`) before alias generation is even attempted — `validate_main_missing` test at `:599-608` asserts the error message. The tail-call uses `call_indirect` followed by `return_(&[result])` — Cranelift currently handles this as a regular call+return; if a future Cranelift version supports `return_call_indirect`, this could be tightened, but the present shape is correct. (See S-3 below for a minor doc note.)

### Focus 3 — Test coverage

**Verdict**: PASS. The 14+ new tests cover the load-bearing invariants reasonably well; some negative-case coverage gaps are noted as Suggestions.

**Decision 36 (bare + Local for every module path)** — Positive: the regression guards in `tests/wave2_g6.rs` (carried from Sprint 57) cover JIT-mode bare lookup. The new `linker_resolves_arm64_got_load_relocations` at `crates/cranelisp-backend/src/cache/linker.rs:684-802` synthesises an `.o` with `Linkage::Import` data references and verifies the linker resolves them via in-process slots. Negative: I see no specific test that asserts "no FQ-Export symbol leaked into a module's `.o`" — i.e., a regression-guard that would fail if some future change re-introduces `module/name`-qualified Export linkage. The closest is the implicit assertion that `linker.get_symbol(bare_name)` resolves successfully in `load_cached_module_via_linker:2941-2955` — if that swallowed, an FQ leak would be detected at runtime test failure but not via a targeted unit test. Filed as S-2.

**Decision 37 (cache-hit recursion in `register_module`)** — Three of four code paths covered: (a) cache hit (the `try_cache_hit_load → true` branch — covered indirectly by `cache_round_trip_*` integration tests); (b) cache miss → fresh-build registration (line :1510 fall-through — covered by `cache_invalidation_on_dep_change_e2e`); (c) transitive cache hit (the recursive path — directly covered by `register_transitive_cached_imports_filters_synthetic_modules` at `src/worker.rs:4520-4570`); (d) transitive cache miss (the recursive fall-through to `register_module(transitive_dep, true)` at :1510 — covered by the `cache_round_trip_multi_module_observable_equivalence` test which exercises both cache and source paths). All four branches are reachable. **Adequate.**

**GOT shape unification** — End-to-end JIT cross-module dispatch: covered by `tests/wave2_g6.rs` integration tests which exercise the full pipeline. Regression guard distinguishing direct registration from the old pointer-cell wrapper: the `Linker::register_symbol` API at `crates/cranelisp-backend/src/cache/linker.rs:185-188` is unconditional (no second-level wrapping); the new `linker_resolves_arm64_got_load_relocations` (`:684-802`) verifies the GOT_LOAD relocation pathway against the in-process slot. The doc comment at `linker.rs:9-30` records the unified one-load shape. (See I-3 for the unaligned `per-module-got.md` §9.2/§9.3 doc.)

**Swallowed-failure pattern** — The fix at `src/worker.rs:2935-2955` (`load_cached_module_via_linker`) replaces the pre-Sprint-58 unconditional `loaded_symbols.push(name)` with an `else { return Err(CranelispError::ModuleError {...}) }` arm that surfaces the cache-inconsistency error. **Direct regression guard for this is missing** — there is no unit test that constructs a deliberately mismatched cache (`.meta.json` records a defined function whose name is not in the `.o`) and asserts that `load_cached_module_via_linker` returns `Err` rather than silently producing `Ok(loaded_symbols=[])`. Filed as S-1.

### Focus 4 — Per-crate clippy gate

**Verdict**: PASS for `cranelisp-backend`. Pass with cosmetic noise for `cranelisp` (binary).

**`cranelisp-backend`**: Compared HEAD vs baseline `094c183`. Identical lint output: 1 pre-existing `approx_constant` ERROR at `display.rs:655` (Sprint 52 carry, out of scope per task brief), 2 `len_zero` warnings (1 of which is in test at `cache/object.rs:326`, 1 pre-existing in `lib.rs`), and 1 `collapsible_if` warning at `lib.rs:723-727` (the `enrich_expr_from_side_maps` test helper landed in Sprint 57 Wave 2). **Zero new warnings introduced by Wave 2.**

**`cranelisp` (binary)**: 5 new `clippy::clone_on_ref_ptr → slice::from_ref` warnings introduced by Wave 2:
- `src/worker.rs:4163, 4164, 4215` (3 occurrences in newly-added Wave 2 unit tests `multiple_imports_on_same_module_preserve_source_order` and `writer_does_not_record_implicit_prelude_in_imports`)
- `tests/modules.rs:109, 132` (2 occurrences in newly-added integration tests)
- `tests/helpers/mod.rs:332` (carried from baseline — pre-existing)

These are mechanical `.clone()` → `slice::from_ref` rewrites in test code. Cosmetic but should be cleaned up alongside other Wave-3 gardening. Filed as S-6.

### Focus 5 — Documentation hygiene

**Verdict**: 3 Important findings. The wave's mid-cycle architectural reconciliation rewrote three core decisions but two design docs lag behind.

(See I-1, I-2, I-3 below.)

### Focus 6 — Cross-decision coherence

**Verdict**: PASS. Decisions 23, 36, 37 harmonise correctly in the implementation:
- Decision 23 (byte-identical CLIF) + Decision 36 (bare + Local) + Decision 37 (cache-hit-in-recursion) all converge on a single uniform CLIF emission path.
- The cache linker's GOT slot allocation (`Linker::ensure_got_slot`) is consistent with the SymbolTable GOT slot allocation (both use the same indexing scheme — slot index `i` is `M`'s `i`th defined function — verified by Decision 23's "two-GOT model" subsection in `interfaces.md` and by `cache/linker.rs:9-30` cross-referencing).
- The `--link` mode `_main` exception is cleanly contained in `src/exe.rs::generate_main_alias_object`, isolated from `compile_to_module`'s general path; it does not pollute the `--run`/REPL paths.

---

## Important findings

**I-1** (Important, /backend): `design/backend/module-caching.md` §14.3 step [5b] still describes the OLD "re-run codegen via `compile_to_module<JITModule>`" cache-restore semantics that Decision 25 explicitly rewrote in this same wave (cache stores BOTH `.meta.json` AND `.o`; cache-hit LOADS the `.o`, does NOT re-codegen). The head FIXME at lines 3-95 enumerates this as a required Wave-2 rewrite ("§14.3 step [5b] is WRONG"), but the rewrite itself was not landed. §14.6's "Symmetry invariant" text (lines 1300-1304) similarly says cache-restore "populates `code` per Defn entry (driven by the deserialised `ast`)" — i.e., still the re-codegen framing. Recommendation: rewrite §14.3 step [5b] to describe the linker-load path per Decision 25's Wave-2 framing; update §14.6's symmetry-invariant text to distinguish "fresh-build path: `compile_to_module` populates code" from "cache-restore path: `Linker::load_object` + GOT-slot writes populate code". Should land before sprint close — not strictly Wave-3-blocking, but a reader reaching this doc *during* Wave 3 will be misled about the architectural shape Wave 3 is building on. Owner: `/backend`.

**I-2** (Important, /backend): `design/backend/per-module-got.md` §9.2/§9.3 still describes the OLD two-load GOT shape ("Each `__cranelisp_got_{module}` data symbol is an 8-byte literal pool entry containing the GOT table's heap address" → "Two loads: one to get the GOT base from the literal pool, one to get the function pointer from the GOT"). Per the unified one-load shape landed in Wave 2 — confirmed at `crates/cranelisp-backend/src/cache/linker.rs:11-30` — the data symbol address IS the GOT slab base directly, no extra pointer-cell indirection. The CLIF emits one less load, machine-code shape changes from ADRP+LDR (literal pool) + ADD+LDR (GOT slot) + BLR to ADRP+LDR (system GOT pages) + LDR (slot) + BLR. This finding was explicitly flagged by `/backend` as a known follow-on; record here for the Wave-3 doc-update batch. Owner: `/backend`. Future cleanup, not Wave-3-blocking.

**I-3** (Important, /backend): `design/backend/compile-to-module.md` head FIXME (lines 3-17) says "§17 still owes the C8 follow-on (raw-shape return type per CP1 arbitration, Decision 35) — separate FIXME." However, §17.1.1 ("Raw return shape — Decision 35 / Layer 2 Option B (Wave 2 close)", lines 1151-1209) IS the resolved follow-on text — comprehensive, prescriptive, and explicitly labelled "(Wave 2 close)". The head-FIXME stale text creates the false impression that the C8 follow-on remains outstanding. Recommendation: update the head FIXME to record that §17.1.1 was actioned (or remove the head FIXME entirely if all three Wave-2-architectural-reconciliation actions are now landed). Should land before sprint close. Owner: `/backend`.

## Suggestion findings

**S-1** (Suggestion, /qa): `src/worker.rs::load_cached_module_via_linker` at lines 2935-2955 — the swallowed-failure fix correctly returns `Err(CranelispError::ModuleError {...})` when a cached symbol's address fails to resolve through the linker. There is no unit test that constructs a deliberately mismatched cache (`.meta.json` records `Def(foo)` whose name is missing from the `.o`'s symbol table) and asserts the error path. Recommended: add a `cache_load_via_linker_errors_on_missing_symbol` integration test in `tests/cache.rs` that synthesises this mismatch and verifies the `Err` propagates. Owner: `/qa`. Future cleanup.

**S-2** (Suggestion, /qa): No targeted negative regression-guard for Decision 36 (bare + Local everywhere). Recommended: add a unit test in `crates/cranelisp-backend/src/lib.rs` `#[cfg(test)] mod tests` that calls `compile_to_module<ObjectModule>` against a fixture module with multiple defined functions (some in `user`, some in another module path) and uses the `object` crate to introspect the resulting `.o`'s symbol table — assert no symbol carries `Linkage::Export` (apart from the `__cranelisp_got_{M}` data symbol per Decision 23), and assert all function symbols are bare. This would lock the bare-Local invariant in place against future drift. Owner: `/qa` or `/backend`. Future cleanup.

**S-3** (Suggestion, /int): `src/exe.rs::generate_main_alias_object` at lines 215-221 uses `call_indirect` + `return_(&[result])` instead of `return_call_indirect`. Cranelift 0.125 supports `return_call_indirect`; using it would let the linker tail-eliminate one frame on the entry path. Cosmetic — the current shape is correct, just slightly less efficient. Owner: `/int`. Future cleanup.

**S-4** (Suggestion, /backend): `crates/cranelisp-backend/src/lib.rs:200-268` — `<ObjectModule as CodeFinalizer>::define_module_got_data` has good defensive shape (slot range check at `:242-249`, u32 overflow check at `:251-258`). Consider extracting the `slot_count == 0` early return at `:212-215` into a dedicated helper or named constant — at present it inlines the comment "No slots to define. Skip — symbol is not needed by callers." Cosmetic; the current shape is fine. Owner: `/backend`. Future cleanup.

**S-5** (Suggestion, /int): `src/worker.rs::register_transitive_cached_imports` at lines 1438-1517 — the function uses an early-`continue` chain over multiple guards (synthetic-module check, already-installed check, dep-file resolve, cache-hit-load, source-read, parse). Each guard's failure mode is silent (just `continue`). For diagnostic ergonomics in cache-hit corner-cases, consider a TRACE-level log when a transitive dep is skipped at each guard — would help when a `cache_multi_module_*` test fails with "module X never loaded" in CI. Cosmetic. Owner: `/int`. Future cleanup.

**S-6** (Suggestion, /int + /qa): 5 new clippy `slice::from_ref` warnings introduced in Wave 2 unit tests (`src/worker.rs:4163, 4164, 4215`; `tests/modules.rs:109, 132`). Mechanical `&[x.clone()]` → `std::slice::from_ref(&x)` rewrites. Sweep alongside Wave-3 gardening or whenever next touching these test files. Owners: `/int` (worker.rs tests), `/qa` (modules.rs tests). Future cleanup.

---

## Pre-existing issues noted

The clippy baseline state is unchanged from `094c183`:
- `crates/cranelisp-backend/src/display.rs:655` — `approx_constant` ERROR (Sprint 52 carry; explicitly out of Wave 2 scope per task brief).
- `crates/cranelisp-backend/src/cache/object.rs:326` — `len_zero` warning in test code.
- `crates/cranelisp-backend/src/lib.rs:723-727` — `collapsible_if` in the `enrich_expr_from_side_maps` test helper (Sprint 57 Wave 2 carry).
- `src/platform.rs:675, 766` — pre-existing `slice::from_ref` warnings.

Recommendation per Sprint 57 review: schedule a per-crate clippy sweep for Wave 6 cleanup.

## Verification spot-checks

Per "one agent, one test run" — only the targeted clippy verification was run (per task brief).

| Check | Result |
|---|---|
| `cargo clippy -p cranelisp-backend --all-targets` (HEAD vs baseline `094c183`) | identical lint output; 0 new warnings |
| `cargo clippy -p cranelisp --all-targets` (HEAD vs baseline `094c183`) | +5 new `slice::from_ref` warnings in newly-added Wave-2 unit-test code; no pre-existing warnings increased in count |
| `git diff 094c183..7236aa7 --stat` | 28 files changed, +4547 / −627 — matches commit message |
| Confirm `ModuleStructure` struct fully deleted | confirmed via grep; only doc-comments + regression-guard test remain |
| Confirm `try_cache_hit_load` orchestration replaced by recursive flow | confirmed at `src/worker.rs:1417` (`register_transitive_cached_imports` call within `try_cache_hit_load`) and `:1438-1517` (the recursion implementation) |

## Checklist walkthrough

Against `design/review/checklist.md` and the audit checklist:

- **§1 Error Handling**: Cache-load errors (`load_cached_module_via_linker`, `load_meta`, `define_module_got_data`) all use `?` + `CranelispError` with meaningful spans. The swallowed-failure pattern at `worker.rs:2810-2823` (Sprint 57 carry) is correctly replaced with hard-error propagation per Decision 31 safety invariant. PASS.
- **§2 Code Structure**: `compile_to_module` is now ~270 lines (steps 1-5 marked + GOT-data emission step 4a). Borderline at the §2 100-line guideline, but the structure is linear with well-named step comments and helper extractions (`compile_defn_in_module`, `define_module_got_data` via trait). `try_cache_hit_load` is ~190 lines — at the limit but the structure is sequential with comment-marked phases (1-9). Borderline PASS.
- **§3 Naming**: `CACHE_SCHEMA_VERSION`, `Linker::ensure_got_slot`, `register_transitive_cached_imports`, `generate_main_alias_object`, `define_module_got_data` — all descriptive. `String` newtype discipline preserved (Symbol, ModuleFullPath, etc.). PASS.
- **§5 Single Source of Truth**: Decision 25 + 33 + 36 + 37 all converge on single-source-of-truth: `SymbolTable` is the cache shape, structural decls live in one place, function naming is uniform, cache-hit decision lives in one recursive flow. PASS.
- **§6 Duplication**: The `try_cache_hit_load` body has non-trivial overlap with the fresh-build path (cache-state validation, module installation), but the overlap is intrinsic to "cache-hit installs the same kind of state fresh-build installs"; the recursive `register_transitive_cached_imports` correctly replaces what would be a parallel orchestration. The `define_module_got_data` trait method captures the JIT vs Object asymmetry in one place per `CodeFinalizer` impl. PASS.
- **§7 Architectural Boundaries**: `cranelisp-types` carries data only (the four structural-decl fields + `schema_version`). `cranelisp-backend/src/cache/` owns the cache mechanics + `Linker`. `Code` enum lives in integration layer per Decision 35. Boundaries clean. PASS.
- **§7a Idiomatic Rust**: New `unsafe` surface added by Wave 2 — `Linker`'s `mmap` operations, the slot-pool address arithmetic. The page-pool unsafety is contained in `ensure_got_slot` with a single inline pointer derivation. No `unsafe impl Send/Sync` newly added (Linker is not Send across threads under current usage). PASS.
- **§8 Serialization**: `schema_version: u32` `#[serde(default)]` on `SymbolTable` (line 108). All four structural-decl fields `#[serde(default)]`. The new `cache::write_meta` / `cache::load_meta` API correctly stamps `schema_version = CACHE_SCHEMA_VERSION` on write. PASS.
- **§9 Testing**: 14+ new tests across `tests/cache.rs` (4 round-trip integration tests), `crates/cranelisp-backend/src/cache/serialize.rs` (3 schema/round-trip unit tests), `crates/cranelisp-backend/src/cache/linker.rs` (1 GOT_LOAD relocation regression guard), `src/worker.rs` (`register_transitive_cached_imports_filters_synthetic_modules` + `writer_does_not_record_implicit_prelude_in_imports` + `multiple_imports_on_same_module_preserve_source_order` + `module_structure_struct_is_deleted_from_save`), `src/scheduler.rs` (`level4_claim_guard_sets_inmem_claimed_not_inmem_done`). Unit-tests-with-dev principle honoured. PASS with one negative-coverage gap (S-1 swallowed-failure regression guard).

## Unsafe code audit

Per `/review` skill §5:

- `crates/cranelisp-backend/src/cache/linker.rs:137-183` (`ensure_got_slot`): allocates an mmap'd page, pushes onto `self.got_pool`, computes slot address as `page.as_ptr() as usize + slot_byte_offset`, writes the symbol's address into the slot. The `MmapMut` is held by `self.got_pool` (Linker-lifetime). No SAFETY comment is present, but the safety invariant is documented in the function's doc comment (lines 128-136) and in the broader doc comment at `linker.rs:9-30`. The pointer arithmetic stays within the page bounds (verified by the `slot_byte_offset` clamp via `SLOTS_PER_PAGE`). Acceptable.
- `crates/cranelisp-backend/src/cache/linker.rs:373-385` (mprotect): existing `unsafe` for marking code pages executable. Unchanged from baseline.
- `src/exe.rs::generate_main_alias_object` introduces no new `unsafe`.

Scattered `unsafe` / pointer risk: **contained**. The new code does not spread `unsafe` beyond the cache-linker module.

## Design doc assessment

| Doc | Status |
|---|---|
| `design/arch/CLAUDE.md` Decisions 23, 25 (UPDATED), 36, 37 (NEW) | Comprehensive, prescriptive, well cross-referenced. PASS. |
| `design/arch/interfaces.md` "Two-GOT model" subsection (per commit message) | Land confirmed via `git show 7236aa7 --stat` (+17 lines); content not spot-checked (out of scope). PASS. |
| `design/int/symbol-table-cache.md` (post-reconciliation) | Resolved — head FIXME marked resolved at lines 3-8; §3.1 + §3.2 rewritten to match Decision 36 + 37; investigation findings updated. PASS. |
| `design/backend/compile-to-module.md` §17 (Decision 35 Layer 2 Option B) | §17.1.1 IS the resolved follow-on text (lines 1151-1209) — comprehensive. **BUT** the head FIXME (lines 14-17) still says the C8 follow-on is unresolved. Filed as I-3. |
| `design/backend/module-caching.md` §14 | §14.3 step [5b] STILL describes "re-run codegen via `compile_to_module<JITModule>`" (lines 1236-1241) — directly contradicts Decision 25's Wave-2 rewrite. Head FIXME at lines 3-95 enumerates the required rewrites; rewrites were not landed. Filed as I-1. |
| `design/backend/per-module-got.md` §9.2/§9.3 | Still describes old two-load shape. Filed as I-2 (already known follow-on). |

## Gate assessment

Wave 2 gate criterion (sprint plan `sprints/SPRINT.md:591`):

- ✓ Structural decls populated and round-trip — confirmed via `cache_round_trip_multi_field_symbol_table` and `writer_does_not_record_implicit_prelude_in_imports`.
- ✓ `CodegenInput` stashing removed — confirmed; the `module_structure_struct_is_deleted_from_save` regression guard verifies `ModuleStructure` is gone.
- ✓ `CACHE_SCHEMA_VERSION = 1` enforced — confirmed via `cache_schema_version_mismatch_falls_through` test.
- ✓ 13 baseline cache failures cleared — commit message reports 17 → 5 (5 = pre-existing, all out of Wave 2 scope: 2 Step 5d Wave 4 carries + 3 pre-existing REPL/sketch). Net: 12 cleared. Within +/- 1 of the projected 13.
- ✓ `cargo clippy` clean per-crate — confirmed via baseline diff: zero new warnings in `cranelisp-backend`; 5 new cosmetic `slice::from_ref` warnings in `cranelisp` (binary) test code.
- ✓ Test count ≥ baseline — 2604 / 2609 passing per commit message; baseline was 2592.

**Gate PASS.** The Wave-2 fix shape (A + B + C) per `/arch`'s Architecture Review (`SPRINT.md:326`) is correctly implemented. The 3 Importants are documentation-hygiene issues that should land before sprint close but do not block Wave 3 from opening.

## Summary

| Severity | Count | Finding |
|---|---|---|
| Blocker | 0 | — |
| Important | 3 | I-1 module-caching.md §14.3/§14.6 stale; I-2 per-module-got.md §9.2/§9.3 stale; I-3 compile-to-module.md head FIXME stale |
| Suggestion | 6 | S-1 swallowed-failure regression test; S-2 Decision 36 negative regression test; S-3 `return_call_indirect`; S-4 `slot_count == 0` extraction; S-5 transitive-import TRACE logging; S-6 `slice::from_ref` cleanup |

Wave 2 is cleared for close from the code-review perspective. The 3 Importants are doc-trail-lag items; none prevent Wave 3 from opening, but at least I-1 (module-caching.md §14.3) and I-3 (compile-to-module.md head FIXME) should land before sprint close to avoid leaving the Decision-25 architectural rewrite documented in two contradictory places.
