# JIT / Object Codegen Convergence — Sprint 60 Workstream A

**Status**: Phase 3 design (pre-implementation). This doc satisfies Condition 1 of the Sprint 60 /arch review: all nine sections enumerated in `sprints/SPRINT.md §"Phase 3 design-doc requirements"` are present.

**Owner**: `/backend`.
**Reviewed by**: `/arch` (Phase 3a gate) — blocks Wave 1 until signed off.
**Scope**: Design-only. No source edits accompany this doc; implementation lands in a later wave under the scope estimate at §9.

**Input context** (read before reviewing this doc): `design/backend/defects-456-reduction.md` (S59 reduction + Phase-2 conclusion), `design/arch/CLAUDE.md` Decisions 23/25/31/32/35/36/37, `design/arch/pipeline-v4.md` §6 + §9, `design/backend/compile-to-module.md` §17, `design/backend/ring2-rc.md`.

---

## §1 Invariant statement

The reimplementation's single-pipeline architecture (Decision 23's two-GOT model, Decision 36's bare-Local naming, Decision 37's one-recursive-flow cache-hit integration, Decision 35's `Code::Jit` / `Code::Linker` per-entry retention) implies a formal invariant:

> **JIT-object convergence invariant.** For any module `M`, the sequence of steps that carries `M`'s source to reachable executable bytes is identical across the JIT finalize path and the `.o` relocation + link-load path, **except for a single explicitly-bounded fixup-mechanism boundary**. Bytes upstream of the boundary are bitwise-identical; bytes downstream of the boundary carry the same semantics (a function pointer that, when called, executes the same instructions against the same GOT slots), produced by a different mechanism.

### 1.1 What MUST be identical

| Artifact | Rationale |
|---|---|
| **CLIF bytes emitted by `compile_to_module<M: Module>`** | `compile_to_module` is the sole entry point (Decision 23, §17 of `compile-to-module.md`); it is parameterised by Module type but does not branch on `M` for any IR decision that affects emitted instructions. CLIF for `JITModule` and `ObjectModule` from the same `(module_path, names, symbol_tables)` tuple must be byte-identical. |
| **Function symbol names** | Per Decision 36, every user defn is declared with its bare symbol name and `Linkage::Local` uniformly across all modules, in both finalize paths. There is no per-mode name mangling. |
| **GOT slot layout** (which symbol lives in which slot index per-module) | Pinned by typecheck phase before any codegen runs (Decision 37 "Order-independence rationale"). Persisted to cache and re-installed on cache-hit load; unchanged on fresh-build. |
| **Callee resolution shape** — every cross-symbol call, intra- or inter-module, reads a code pointer from `__cranelisp_got_{M}` slot `i` | Decision 36 "Why all-GOT calling"; Decision 31 safety invariant. Direct relocations against function symbols would break REPL redefinition and are forbidden. |
| **RC conventions** — which parameters are consumed, which values are borrowed, where inc/dec emit | `design/backend/ring2-rc.md` Decision 24 consuming convention; convention is a property of the CLIF, not the fixup mechanism. |
| **Drop-glue code pointers** (per Decision 11 closure layout `[header | code_ptr | drop_glue_ptr | captures...]`) referenced through GOT-indirected dispatch | Drop glue is a function like any other; its code_ptr must route through the GOT or through an Arc-rooted allocation that outlives every caller. See §5. |

### 1.2 What MAY differ (the single fixup-mechanism boundary)

| Downstream step | JIT path | Object path |
|---|---|---|
| **Resolve `__cranelisp_got_{M}` data symbol** | `JITBuilder::symbol_lookup_fn` returns `symbol_tables[M].got.base_ptr()` at finalize — the in-process `SymbolTable` GOT | Linker (system `ld` or our `cache::Linker`) reads the `.o`'s `Linkage::Export` `__cranelisp_got_{M}` data symbol initialised with relocations against the local function symbols — the `.o` data-section GOT |
| **Make function pages executable** | `JITModule::finalize_definitions()` via `CodeFinalizer::finalize_for_code_read` (`JITModule` impl) | No-op at compile time; `Linker::load_object` + relocation + mmap at load time |
| **Produce per-symbol `*const u8` entry point** | `module.try_get_finalized_function(func_id)` returns `Some(ptr)`; populated in `CompilationResult.code_ptrs` | `try_get_finalized_function` returns `None` for `ObjectModule`; `code_ptrs` is empty. Per-symbol pointers are resolved **later** on cache-hit load via `linker.get_symbol(bare_name)`. |
| **Retention root on `ModuleEntry::Def.code`** | `Code::Jit { jit: Arc<Jit>, ptr }` | `Code::Linker { linker: Arc<Linker>, ptr }` |
| **Reclamation primitive** | `Jit::Drop` → `unsafe JITModule::free_memory()` when last `Arc<Jit>` clone drops | `Linker::Drop` reclaims mmap'd pages when last `Arc<Linker>` clone drops |

That table is exhaustive. Every other pipeline step — parse, expand, typecheck, AST annotation, signature registration, GOT-slot allocation, CLIF emission including RC ops and drop-glue references, GOT-data emission (`Linkage::Export` inside `compile_to_module<ObjectModule>` per Decision 23 follow-on) — runs identically on both paths.

### 1.3 Why the invariant is falsifiable

Two concrete falsifications are possible:

1. **CLIF-diff**: dump CLIF for `M`'s `names` under `compile_to_module<JITModule>` and `compile_to_module<ObjectModule>` with a fresh `DashMap<ModuleFullPath, SymbolTable<C, L>>` bearing identical typed state. Byte-compare per-function CLIF. Any divergence is a breach. Workstream B's CLIF-dump infrastructure makes this test possible.
2. **GOT-slot contents comparison**: after finalize, for each symbol `s` in `names`, `symbol_tables[M].got.load_slot(st[M].symbols[s].got_slot)` must be non-NULL and must be the same address as what `linker.get_symbol(s)` would return after an immediate cache-hit reload of the identical `.o`. Any divergence is a breach.

S59 Phase-2 gave indirect evidence of a breach: REPL-typed `(solution-cell g g 0)` runs deterministically; the identical-source imported version traps ~75%. Under the invariant above, that is impossible unless the paths differ somewhere downstream of the CLIF — OR the CLIF itself differs — OR a referenced retention root (drop glue, GOT slot) is not reachable from the imported path.

**Citations**: Decision 23 (two-GOT model); Decision 36 (bare-Local, §"Why all-GOT calling"); Decision 37 (recursive register_module, §"No swallowed failures"); Decision 31 (safety invariant + carry-forward); `compile-to-module.md §17.1.1`.

---

## §2 Hypothesis audit

Four hypotheses. For each: what it predicts, the CLIF-dump test that verifies or falsifies it (Workstream B is a precondition for H1 and H2; H3 and H4 need additional runtime probes).

### H1 — Monomorphised defn codegen context divergence across module boundaries

**Prediction**. When `cell-at` is typed in the REPL, it compiles as a single-pass polymorphic defn with full `variable_types` / `borrowed_vars` / `consumed_vars` state available. When `cell-at` is imported and a caller forces monomorphisation to `cell-at$grid.Cell`, the monomorphisation pass reads AST annotations that are incomplete at module boundaries (e.g., `expr_types` not populated for types resolved in `grid`'s module but referenced from `html`'s call site). The two emissions produce DIFFERENT CLIF.

**Audit procedure**.
1. From a bare REPL with no html/grid imports, `(defn cell-at-inline [g idx] ...)` with the same body; `/clif cell-at-inline` captures CLIF.
2. Import `grid`; force monomorphisation (`(let [g (make-grid)] (cell-at g 0))`); `/clif grid/cell-at$grid.Cell` captures mono CLIF.
3. Normalise names (rename `cell-at-inline` → `cell-at$grid.Cell`) and diff.

**Falsify on**: byte-identical CLIF (modulo normalised names) → H1 rejected.

**Confirm on**: any instruction difference. The differences' location pinpoints the annotation source: RC ops differ → `variable_types` incomplete; call resolution differs → `ResolvedCall` state; match codegen differs → ADT info per-module.

**CLIF-dump requirement**: `CRANELISP_CODEGEN_DUMP=grid:cell-at$grid.Cell` must print the mono CLIF to stderr or a file during a normal run. Workstream B delivers this.

### H2 — Auto-curry closure over polymorphic dispatch with RC contract mismatch

**Prediction**. The S59 Pass-2 CLIF observation was `fn3(env) -> v13; fn4(v13); call fn10(v13)` — `cell-at` dispatched via a 2-capture auto-curry closure even when both args are supplied. If AutoCurry fires because the polymorphic return `a` requires a curry level to stall monomorphisation until the return-context unifier runs, the closure-env inc/drop pattern must balance with the caller's consuming convention. If the closure env is freed before the return value's RC stabilises (or after — over-retained), the ledger corrupts.

**Audit procedure**.
1. Dump CLIF for the call site `(cell-at original idx)` inside `solution-cell`.
2. Dump CLIF for the auto-curry wrapper `fn3` / `fn4` if they appear.
3. Verify the closure env's inc (on construction), drop-glue's fields decs (on env release), and the wrapper's consuming behaviour on the captured args match the Decision-24 convention: the wrapper MUST dec every heap arg it does not return.

**Falsify on**: CLIF shows direct call `call fn_cell-at(v_g, v_idx)` with no closure env intermediary → H2 rejected. (I.e., there is no auto-curry for 2-of-2 applications.)

**Confirm on**: auto-curry intermediary present; inc/drop imbalance visible in CLIF. The `emit_guarded_rc_inc` / `emit_rc_dec_with_inline_drop_glue` call sites inside the wrapper give the ledger trace.

**CLIF-dump requirement**: must include wrapper functions synthesised by auto-curry, not just user-defined defns.

### H3 — Cross-module GOT drop-glue `func_addr` × Decision 31 reclaim (/arch ranked most-likely)

**Prediction**. Cell is an ADT defined in `grid`. Cell's drop glue (the function that dec's each field of a Cell when its RC hits 0) is compiled inside `grid`'s batch. The drop-glue `func_addr` is baked into closures over Cell values — specifically, the `drop_glue_ptr` slot in the closure layout, and the `func_addr`-computed constants used by `emit_rc_dec_with_inline_drop_glue` at call sites that consume Cell values.

When `html`'s code dec's a Cell (either in a scope cleanup in `solution-cell` or inside `run-test`'s wrapper), it calls `grid`'s drop glue. If `grid`'s batch was compiled in its own `JITModule` with its own `Arc<Jit>`, and `html`'s code pins the drop-glue code address via a direct `func_addr` constant (not a GOT-indirect call), then:

- On the first REPL import-and-run, `grid`'s `Arc<Jit>` is retained on `grid/cell-drop`'s `ModuleEntry::Def.code = Code::Jit { jit, ptr }`. `html`'s code holds a raw `*const u8` constant into `grid`'s JIT pages.
- REPL-Additive upsert of any entry in `grid` (or even in `html` if the path clones the wrong Arc forward) can trigger Decision 31 Scenario 2 reclaim of `grid`'s `Arc<Jit>`, freeing `grid`'s JIT pages, including the drop-glue pages.
- Allocator re-hands the freed pages to a later batch. The address constant baked into `html`'s code now points into a different module's code bytes.
- Calling through that constant lands on arbitrary instructions — raw trap, no stderr, intermittency determined by whether a subsequent allocation landed on the same VA with instructions that happen to trap (vs happen to decode as a noop + return).

**Audit procedure**.
1. Dump CLIF for `html/solution-cell` and for `html/row-helper` (the caller that dec's each row's accumulator); identify every `emit_rc_dec_with_inline_drop_glue` emission site that targets a Cell or a Grid.
2. Check whether those sites emit `call_indirect` through a GOT slot, or `call f_direct` where `f_direct` is a `func_addr` constant. Under Decision 31's "all-GOT calling" discipline, drop-glue calls MUST go through the GOT; if any do not, that is the H3 breach.
3. Print the address held in `html/solution-cell`'s drop-glue CLIF constant and compare it to `grid`'s `Arc<Jit>` memory range at the moment of first call vs subsequent calls.
4. Enable a heap-debugger (`LIVE_ALLOCS` trace plus a `jit_free_memory_call_count` probe — the latter exists per Decision 31 evidence) and correlate trap intermittency with Arc reclaim events.

**Falsify on**: all drop-glue calls in `html`'s CLIF route through `__cranelisp_got_grid` slots (no direct `func_addr` constants into `grid`'s code pages) → H3 rejected.

**Confirm on**: any direct `func_addr` constant into `grid`'s JIT address space from `html`'s code, or observed reclamation event immediately preceding the trap.

**CLIF-dump requirement**: the dump must show both high-level Cranelift ops (`call`, `call_indirect`) AND the relocations / constants they reference. A pretty-printed CLIF alone is insufficient — we need relocation targets.

### H4 — GOT-slot population NULL-sink (Decision 37 §"No swallowed failures") — /arch addition

**Prediction**. Per Decision 37, slot LAYOUT is pinned at typecheck; slot CONTENTS are written in codegen. If any codegen worker writes `Code::Jit { ... }` onto a `ModuleEntry::Def` AND pushes the symbol to `loaded_symbols` BEFORE the corresponding GOT slot store completes, then a sibling codegen worker whose callee-module imports the not-yet-populated symbol would read NULL at call time. The S58 Wave 2 `try_cache_hit_load` deletion closed this for the cache-hit path, but the fresh-build `inline_jit_codegen_for_names` path (`src/worker.rs:2800+`) might still have the ordering latently, because the loop that writes slots and the loop that writes `Code::Jit` are the same loop — the concern is whether a sibling worker can observe `Code::Jit = Some(_)` (via `all_symbols` iteration on line 2827-2833, which is how OTHER modules' already-compiled functions get registered as JIT symbols) before the GOT slot has been store'd.

Looking at lines 2886-2916 of `worker.rs`: per name, `got.store_slot(slot, code_ptr)` happens FIRST (line 2899), then `*code = Some(Code::jit(...))` SECOND (line 2911). Good. But the loop iterates `names` sequentially; between iteration `i` (storing slot) and iteration `i+1`, another thread iterating `all_symbols` might observe iteration `i`'s `Code::Jit = Some(...)`. That is fine IF every reader of `Code::Jit` uses the `c.ptr()` accessor and we never use `got.load_slot()` as a call target that could still be NULL.

The audit question: are there any code-writing paths where `loaded_symbols.push(...)` (or `Code::Jit = Some(_)`) happens BEFORE the GOT slot is store'd, OR where a worker reports success (typecheck-complete or inmem-codegen-done notification to the scheduler) while any `got_slot` remains `.load()` == NULL?

**Audit procedure**.
1. `grep` every `got.store_slot(...)` call-site in `src/worker.rs` and `crates/cranelisp-backend/`. For each, trace backward to see what condition gates the call (is it inside a "resolved address" check? is there a prior `continue` that could skip it?).
2. `grep` every `Code::jit(...)` / `Code::linker(...)` construction site. For each, verify the matching slot store precedes it on every execution path.
3. `grep` every `notify_inmem_codegen_batch_complete` / `notify_module_failed` call. Trace backward: what asserts every slot is non-NULL at the scheduler-notification point? (Currently: nothing — Decision 37 §"No swallowed failures" explicitly notes this was Bug A's signature and was closed for cache-hit; the same discipline must hold for fresh-build.)

**Falsify on**: every fresh-build codegen path provably stores all slots before notifying the scheduler, AND every `Code::Jit = Some(_)` write is preceded by the matching slot store on every path → H4 rejected.

**Confirm on**: any path where a slot can remain NULL while `Code::Jit = Some(...)` or the scheduler is notified of success. Fix: mirror the cache-hit path's defensive error (return `CranelispError::ModuleError` on NULL resolution) for fresh-build.

**CLIF-dump requirement**: low — this is primarily a read-of-source audit. A runtime assertion that trips if any `got.load_slot(i)` returns NULL at scheduler-notify time is a cheap adjunct guard.

### 2.1 Hypothesis ranking (post-audit)

After reading the S59 §Phase-2 RC trace, the S59 §Resolution signature analysis, and the post-Pass-2 failure pattern (REPL-typed passes 5/5; imported fails 15/20), I concur with /arch: **H3 > H4 > H1 > H2**.

- H3 is consistent with *all* five signature features simultaneously (intermittency, raw trap, no stderr, imported-only, REPL-typed works).
- H4 would mostly produce deterministic NULL traps on first call, not intermittent ~75% — but a race where population completes after most callers read is plausible and would look identical to H3. H4 is the cheaper audit and should run first.
- H1 and H2 each explain the imported-only feature but do not naturally produce raw-trap-without-stderr (a CLIF-level codegen bug would land on a Rust `debug_assert!` or a well-formed `unreachable` trap with panic output).

**Load-bearing bet for the fix**: H3.

---

## §3 Decision-37 alignment

This section confirms that the JIT and object paths of `compile_to_module` share one register-then-codegen flow and identifies the single fixup boundary.

### 3.1 Shared recursive `register_module` flow

Per Decision 37's canonical recursive flow (quoted verbatim in `design/arch/CLAUDE.md` Decision 37):

```
register_module(M):
  if <cache_dir>/M.meta.json exists and schema_version matches:
    deserialise → install SymbolTable for M → mark typecheck-complete
  else:
    parse → typecheck → install SymbolTable for M
  for each import in SymbolTable[M].imports:
    register_module(import.module)   # recursive, blocking on transitive deps
```

Both JIT fresh-build and `.o` cache-hit enter this flow identically. `src/worker.rs::try_cache_hit_load` (line 1389) lives inside the typecheck-or-deserialise branch of `register_module`'s body. Post-register, every transitive import is satisfied uniformly — no separate "cache-hit path" runs in parallel. This is the S58 Wave 2 deletion of the old `try_cache_hit_load` duplicate recursive walk.

### 3.2 Codegen-phase symmetry

After typecheck-phase completion for all reachable modules, the codegen phase runs. Per-module codegen workers have two kernels depending on whether the module is cached (`cached_modules.contains(module)`):

- Fresh build: `inline_jit_codegen_for_names` (`src/worker.rs:2800`). Calls `compile_to_module<JITModule>`, wraps the `Jit` in `Arc`, writes `Code::Jit { jit, ptr }`.
- Cache-hit: `load_cached_module_via_linker` (`src/worker.rs:~3040+`). Calls `Linker::load_object`, writes `Code::Linker { linker, ptr }`.

**These two kernels are the fixup-mechanism boundary.** Upstream of them: identical register_module flow, identical typecheck symbol tables, identical GOT slot layout. Downstream of them: identical `code: Some(Code)` state on every `ModuleEntry::Def`, identical GOT-slot contents (a `*const u8` pointing at valid executable bytes).

The two kernels MUST produce outputs that are **behaviourally identical** from every downstream caller's perspective — a call through `got.load_slot(i)` must land on the same instructions regardless of which kernel populated the slot. Each kernel's internal mechanism (finalize-then-extract vs mmap+relocate+lookup) is the "fixup mechanism" parameter the invariant permits.

### 3.3 Where the divergence could live

Given §3.2, the invariant can break at:

- **(a) `compile_to_module` itself**, if the JIT-vs-object path branches inside. Per `compile-to-module.md` §17 the answer is no — Module trait capability methods (`define_module_got_data`, `finalize_for_code_read`, `try_get_finalized_function`) abstract the per-mode difference. **Audit-required**: grep `compile_to_module` + every helper called from it for any `TypeId::of::<JITModule>()` / downcast / mode-flag branch. Expected result: none.
- **(b) the integration-layer post-call step**, if `inline_jit_codegen_for_names` writes `Code::Jit` in a way that differs semantically from `load_cached_module_via_linker`'s `Code::Linker` write. **Audit-required**: verify both kernels produce, for every name, (i) a populated GOT slot with the same `*const u8`, (ii) a `Code = Some(...)` whose `ptr()` returns that same `*const u8`, (iii) a retention root whose lifetime is at least as long as every caller that holds a reference to the slot or the code.
- **(c) the symbol-table state upstream of codegen**, if typecheck produces different AST annotations for the "module loaded from source" vs the "module loaded from cache" entry paths. Decision 34's `schema_version` + `symbol-table-cache.md`'s round-trip requirements address this: cached typecheck state MUST be a pure function of the serialised form, and fresh-typecheck MUST produce the same serialisable form. Any drift is itself a breach — but a *typecheck-layer* breach, not a backend-layer breach.

**If the divergence lives elsewhere** — e.g., the AST builder emits different `expr_types` for imported vs local calls — this is a `/frontend` or `/typecheck` boundary breach, not a `/backend` one. Section §9 scope-estimate treats this as an out-of-scope escalation path.

---

## §4 Decision-31 carry-forward audit (MANDATORY)

Per /arch Condition 1, absence of §4 blocks Phase 3.

### 4.1 The carry-forward site

`crates/cranelisp-typecheck/src/program.rs:2184-2232` (`register_defn_signature`'s upsert body). On redefinition of an existing `ModuleEntry::Def`, this site reads `(got_slot, ast, code) = existing.clone()` and rebuilds the entry carrying those fields forward. Without this, the typecheck-time upsert would drop the old `Arc<Jit>` mid-typecheck — if no sibling entry referenced the same `Arc<Jit>`, `Jit::Drop` would fire, free the pages, and the GOT slot's old pointer would become invalid before codegen overwrote it.

### 4.2 Does carry-forward fire in the fresh-batch path?

Yes — verified. `inline_jit_codegen_for_names` (`src/worker.rs:2800-2937`):

1. Line 2813-2833: collects `jit_symbols` from every `ModuleEntry::Def.code` that is currently `Some(_)`. This INCLUDES the carried-forward `Code::Jit` from a prior batch, because `register_defn_signature`'s upsert preserves it through typecheck.
2. Line 2864: calls `compile_to_module`, which runs codegen against the current symbol tables (with their carried-forward `code` fields intact).
3. Line 2907-2915: writes `Code::Jit { jit: new_jit_arc, ptr: new_ptr }` onto each compiled name — overwriting the carried-forward `code`. The old `Arc<Jit>` clone that lived in the entry's `code` drops at this moment. If no sibling entry still carries the old Arc, and if the `kept_jits` side-store is dissolved (it is, per Decision 35 Wave 3b), the old Arc's refcount hits 0 and `Jit::Drop` fires.

**This is the correct place for the drop**: it happens *after* the new code is compiled and available, *after* the new `*const u8` is ready to be stored in the GOT slot. Between the old Arc's drop and the new ptr's GOT slot store, the old code pages are freed. If a concurrent reader is mid-call on the old code, Decision 31's safety invariant ("REPL redefinition is the sole GOT-slot-mutating event; between REPL evals the system is still") governs: we require no concurrent call outlives the prompt that issued it.

### 4.3 Does carry-forward fire in the cache-hit load path?

Here is the audit question. `load_cached_module_via_linker` (`src/worker.rs:~3040+`) loads an `.o` for a module that *might* have been previously compiled in the same session (e.g., a REPL session that loaded a cached dep, then redefined an entry, then cache-invalidated, then reloaded the same dep from cache).

Reading lines 3082-3123 of `worker.rs`:

```rust
for (name, entry) in cached.symbol_table().all_symbols() { … }  // writes GOT slots
let linker_arc = std::sync::Arc::new(linker);
if let Some(mut live_table) = shared_state.symbol_tables.get_mut(module) {
    for (name, entry) in live_table.symbols.iter_mut() {
        if let ModuleEntry::Def { code, .. } = entry … {
            *code = Some(Code::linker(Arc::clone(&linker_arc), ptr));
        }
    }
}
```

The `*code = Some(Code::linker(...))` write at line 3117 is an unconditional overwrite. If the entry previously held a `Code::Jit { jit: Arc<Jit>, ptr }`, the Arc clone drops at this moment.

**Finding**: the cache-hit load path DOES fire the same Arc-drop as the fresh-batch path, but the code path that gets to this write may differ from the fresh-batch path in one subtle way. The carry-forward at `program.rs:2184-2232` runs during typecheck-phase signature registration. The cache-hit load uses `restore_cached_module` (line 1484-1487 of `worker.rs`), which **consumes the cached `SymbolTable` and installs it**, potentially without running `register_defn_signature` per-entry. The cached table's `code` field is `None::<Code>` (the cached `<()>` is converted to `<Code, ()>` via `into_concrete`, every entry's `code` becomes `None`).

**So on cache-hit load**, the upsert carry-forward does NOT run — because restore installs the deserialised table wholesale. The prior live table (with its `Code::Jit` / `Code::Linker`) is replaced by the deserialised table (with `code: None` everywhere). **The prior Arc is dropped at the point of install, NOT at the point of the post-codegen `*code = Some(Code::linker(...))` write.** And the install happens BEFORE the linker has loaded the `.o` — i.e., before a new `*const u8` is available for the GOT slot.

**Hypothesis**: there is a race window between `restore_cached_module`'s install (Arc drops) and `load_cached_module_via_linker`'s slot-store (new ptr written). During that window, the GOT slot may still point at the old — now-freed — JIT pages. If the scheduler notification for the cache-hit module fires before `load_cached_module_via_linker` has actually run (per `handle_cached_codegen`'s error-handling path), downstream callers can call through the stale slot.

**Audit-required finding**: this is plausibly the H3 source. Trace:
1. `try_cache_hit_load` (worker.rs:1389) installs the cached table, dropping the prior live table — including any prior `Code::Jit` / `Code::Linker` entries' Arcs. Prior JIT pages may be freed here if no other entry retains them.
2. Later, `handle_cached_codegen` calls `load_cached_module_via_linker` which writes the new `Code::Linker` and stores slots.
3. Between steps 1 and 2, the GOT slot contents are whatever the linker writes into them AFTER the install — but the install itself does not NULL the slot (the cached table's `got` is fresh with uninitialised slots; a fresh `got` is installed; the old `got` is gone).

**This is actually safe via a different mechanism**: the new cached table has a **new `got` table** with freshly-allocated slots. The old `got` (with its references to the old JIT pages) is dropped along with the old table. Downstream callers that read from `symbol_tables[M].got.load_slot(i)` get the NEW got's slot value, which is populated by `load_cached_module_via_linker`. There is no window where they'd read the OLD got's stale pointer.

**But**: callers that cached a GOT-base pointer (via `JITBuilder::symbol_lookup_fn` at a prior finalize) would hold a reference to the OLD got's base. Cranelift's `symbol_lookup_fn` returns an address at finalize time; that address is baked into the JIT'd caller's code. If the callee module's `symbol_tables[M].got` is replaced, callers compiled before the replacement hold the old base pointer. **Reclamation of the old `got` (its `Arc<GotTable>` refcount hitting 0) while callers still reference it is unsafe.**

This is the precise H3 breach, localised. The carry-forward at `program.rs:2184-2232` preserves the `code` field through upsert, but **does not preserve the GOT table across `restore_cached_module`'s wholesale install**. The fix: either (a) `restore_cached_module` merges into the existing table instead of replacing (preserving the `Arc<GotTable>` in `symbol_tables[M].got`), or (b) `Arc<GotTable>` reference-counts per-caller and outlives every caller through a retention root analogous to `Code::Jit`'s Arc.

### 4.4 What populates `Code::Linker` when cache-hit resolves a previously-fresh-batched module?

Trace:
1. REPL loads module `M` from source, fresh-batch codegen runs, entries gain `Code::Jit { jit: Arc<Jit>, ptr }`.
2. REPL does something that invalidates the cache (not typical, but: `/reload`, or session restart, or a rebuild-while-session-live).
3. A new session reload hits `try_cache_hit_load`; `restore_cached_module` installs the deserialised table with `code: None`. The prior `Code::Jit` Arcs drop. If `kept_jits` were still present they'd retain, but Wave 3b dissolved them; the Arcs drop.
4. `handle_cached_codegen` runs `load_cached_module_via_linker`; `Code::Linker { linker: Arc<Linker>, ptr }` is written onto each entry.

In this sequence, `Code::Linker` is populated cleanly. But per §4.3, the prior Arc drop at step 3 and the new slot store at step 4 are separated in time; any caller with a cached GOT-base reference to the PRIOR `got` instance is exposed.

**Specified fix direction** (design proposal, not prescription): `restore_cached_module` MUST NOT replace `symbol_tables[M].got`. If a prior `Arc<GotTable>` exists at module `M`, merge slot contents by in-place store rather than swap.

---

## §5 Drop-glue retention audit (H3)

### 5.1 What retains drop-glue code pointers

For a cross-module drop-glue reference — e.g., Cell ADT's drop glue, compiled inside `grid`'s batch, called from `html`'s code when `html`'s scope cleanup dec's a Cell value — the retention story depends on how the drop-glue function is referenced in `html`'s CLIF:

- **If referenced via GOT-indirect call** — `call_indirect` against `__cranelisp_got_grid` slot `i` where slot `i` holds `grid/cell-drop`'s `*const u8` — retention is correct. The GOT slot is held by `symbol_tables[grid].got`, which lives as long as `grid`'s `SymbolTable` is installed. Per Decision 31 Scenario 2, when `grid/cell-drop`'s entry is replaced (REPL redefinition), the atomic GOT-slot swap retargets all future callers; the old `Arc<Jit>` drops when no entry references it, and the safety invariant requires no in-flight caller survives the redefinition prompt. This is safe.
- **If referenced via direct `func_addr` constant** — e.g., a `const UserExternalName("cell-drop")` that Cranelift resolves at finalize to a raw address into `grid`'s JIT pages — retention is broken. `html`'s `Arc<Jit>` does not retain `grid`'s `Arc<Jit>`; the two are independent. If `grid`'s `Arc<Jit>` reaches refcount 0 (Decision 31 Scenario 2 reclaim), its pages are freed, and `html`'s cached constant dangles.

### 5.2 Audit question: which does the reimplementation emit?

Decision 36 §"Why all-GOT calling" mandates all-GOT for function calls. **The audit question is whether drop-glue calls are treated as "function calls" under this mandate.** The backend emits drop glue via:

- `emit_rc_dec_with_inline_drop_glue` (see `crates/cranelisp-backend/src/compiler/mod.rs` and `heap.rs`). This is emitted at scope-cleanup sites and at `emit_rc_dec` call sites where the type carries an inlineable drop glue.

**If the "inline" means the drop-glue instruction sequence is inlined at the call site**, there is no cross-module call and no retention problem — drop glue for `grid`'s Cell is emitted into `html`'s code as straight-line instructions. `html`'s `Arc<Jit>` retains its own pages; `grid`'s `Arc<Jit>` retains `grid`'s pages; the two are independent and safe.

**If the "inline" means an inline trampoline that computes the drop-glue function address and calls it**, the trampoline's address constant is the vulnerability. If the address is a `func_addr` constant baked into `html`'s code at finalize, H3 fires.

**Audit procedure**:
1. Read `emit_rc_dec_with_inline_drop_glue` in `crates/cranelisp-backend/src/compiler/mod.rs`. Document whether it emits inline instructions, a GOT-indirect call, or a direct call.
2. If direct call, examine whether it references `grid`'s drop glue through a `Linkage::Import` against a symbol that resolves through the GOT.
3. For closure drop glue (`drop_glue_ptr` in the closure layout), examine what address is stored in the slot at closure construction time. Decision 11 says the slot holds the drop-glue code pointer; if that pointer is `grid`'s JIT address and `html`'s closure construction stores it, the closure itself is a cross-JIT reference that must either route through the GOT or retain `grid`'s `Arc<Jit>`.

### 5.3 Specified discipline

For the convergence invariant to hold, drop-glue references from module A to module B MUST route through `__cranelisp_got_B`. This is the natural extension of Decision 36 "all-GOT calling" to all function-pointer references, not just user-defn calls. If any drop-glue emission violates this, the fix is a code-generation change (a CLIF edit, not an interface change), and it belongs inside `crates/cranelisp-backend/src/compiler/`.

**Closure drop-glue slot**: the `drop_glue_ptr` field of a closure layout stores a code pointer that must remain valid as long as the closure exists. Options:

- (a) Store the drop-glue's GOT slot index + a GOT-base pointer; dispatch computes the final address at call time. Safe against Decision 31 reclaim (next-prompt redefinition retargets the slot).
- (b) Store a raw `*const u8` but hold an `Arc<Jit>` clone in the closure's captures. Safe against reclaim because the Arc retains. Shape complexity: adds a captures slot for the owning module's Arc.
- (c) Store a raw `*const u8` and rely on session-global retention. Broken under Decision 31's per-redefinition reclaim — exactly the pre-Wave-3b shape Decision 35 closed.

**Recommended design direction**: (a). Closure layout adds an implicit "owning module's GOT base + drop-glue slot index" pair. Call sites dispatch through it. This is the cleanest extension of Decision 31's all-GOT discipline to closures.

The CLIF-dump (Workstream B) is required to determine which shape the current codegen emits. That determines whether the fix is small (option (a) is already emitted, one closure-layout change) or larger (switch from (c) to (a) across every closure-consuming site).

### 5.4 Wave 2 A.2 audit result (CLIF evidence)

Audited 2026-04-21 using `CRANELISP_CODEGEN_DUMP=*` against `tests/sprint59_defects456_repro::d6_exemplar_propagate_only_does_not_segv` (smallest propagate-focused repro). Dump: 95,027 lines, 320 functions, captured to `/tmp/s60_a2_clif.log`. Full findings at `design/backend/defects-456-reduction.md §"Sprint 60 A.2 audit findings"`; summary here in situ with §5's prediction.

**§5.2 audit question resolved — current codegen emits pattern (c), not (a).**

Three concrete sites where drop-glue code pointers flow as *raw* values, not GOT-indexed:

1. **Closure `drop_glue_ptr` slot** (`control_flow.rs:579`): `func_addr.i64 fn_glue_id` baked into the closure layout at construction; torn down via `call_indirect drop_glue_ptr` at `compiler/mod.rs:1256`. Drop glue declared `Linkage::Local` at line 850. This is /arch's Phase-3a Q2 finding, confirmed by CLIF.

2. **Vec element-dec function pointer passed as a COW helper argument** (observed in `grid::set-cell` lines 73217, and in 15+ other grid/solver sites):
   ```
   fn0 = colocated u0:103 sig0   ; runtime/vec_elem_dec_Cell (Linkage::Local, vec_codegen.rs:711)
   v11 = func_addr.i64 fn0       ; raw address
   v29 = call fn2(v10, v4, v5, v11)   ; passed as 4th arg to COW helper
   ```
   The COW helper dispatches via `call_indirect` on the raw address. Same retention shape as closure drop glue.

3. **Inline ADT drop-glue dispatch** (`heap.rs:285-288`):
   ```rust
   if let Some(glue_id) = drop_glue_id {
       let glue_ref = module.declare_func_in_func(glue_id, builder.func);
       builder.ins().call(glue_ref, &[ptr]);   // direct CLIF call, NOT call_indirect, NOT GOT
   }
   ```
   Drop glue is a `Linkage::Local` symbol; Cranelift's JIT finalize bakes either an absolute address or a relative branch. Cross-batch: not routed through `__cranelisp_got_{M}`. Observable in CLIF as `call fnN(...)` against `u0:1` / `u0:101` / `u0:103` references in propagate blocks 17-20, block 23-28.

**Per-batch replication confirmed.** The dedup at `vec_codegen.rs:694-698` deduplicates within one `Module` compile unit but not across batches. Each importing batch that needs `runtime/vec_elem_dec_Cell` emits its own local copy. The cross-batch `func_addr` values are therefore distinct addresses pointing to distinct page copies of the same CLIF — each address anchored to its own `Arc<Jit>`.

**Cross-reference with §1.1**. §1.1 requires: "Drop-glue code pointers … referenced through GOT-indirected dispatch." Sites (1)(2)(3) above all **violate** this. The convergence invariant is breached at the drop-glue layer regardless of whether the d6 repro's specific crash traces to it.

**Refinement of §5.3's specified discipline.** Option (a) is the correct direction, but scope extends beyond closures — the Vec COW helper's element-dec parameter and the heap.rs inline drop-glue dispatch both need GOT-routing too. Estimated scope 180-280 LOC, reconciling with §9.1's lower bound for H3 (150-250 LOC) and pushing toward the upper bound of the combined estimate.

**H3 causality for d6 specifically — partial.** H3's prediction requires a cross-eval reclaim event (Decision 31 Scenario 2) to invalidate a baked address. The d6 repro crashes on a single-shot `--run` invocation with one batch and no redefinition. No reclaim has fired. The crash therefore has a **second root cause** — a correctness bug in the inlined drop-glue emission (likely per-field dec pairing for `Grid (Vec Cell)` where Cell is a multi-variant Mixed ADT). Both fixes are needed; H3 closes the invariant breach; the drop-glue correctness fix closes the d6 symptom. See `defects-456-reduction.md §"Sprint 60 A.2 audit findings"` for the A.3 decomposition.

---

## §6 GOT-slot population audit (H4)

### 6.1 Reading the fresh-build path

`src/worker.rs:2886-2915` (inline_jit_codegen_for_names per-name loop):

```rust
for name in names {
    let Some(code_ptr) = result.code_ptrs.get(name).copied() else { continue };

    if let Some(slot) = lookup_got_slot(tc_modules, module, name)
        && let Some(st) = tc_modules.get(module) {
        st.got.store_slot(slot, code_ptr);
    }

    if let Some(mut st) = tc_modules.get_mut(module)
        && let Some(entry) = st.symbols.get_mut(name.as_ref())
        && let cranelisp_types::ModuleEntry::Def { code, .. } = entry {
        *code = Some(Code::jit(Arc::clone(&jit_arc), code_ptr));
    }
}
```

**Finding 1**: The `else { continue }` on line 2891 silently skips names with no `code_ptr`. This is a Decision 37 §"No swallowed failures" candidate: if `code_ptrs` is missing a name that `names` includes, we continue without slot store, without `Code::Jit` write, and without error. Downstream, the slot stays at its prior value (NULL on fresh init); a caller that calls through the slot traps.

**Finding 2**: The `if let Some(slot) = lookup_got_slot(...)` on line 2896 silently skips names whose GOT slot lookup fails. Same issue.

**Finding 3**: The `if let Some(entry) = st.symbols.get_mut(...)` on line 2908 silently skips names whose entry has disappeared. Same issue.

All three are Decision 37 §"No swallowed failures" breaches in the fresh-build path, of the same shape that /arch flagged for the cache-hit path in S58 Wave 2 (Bug A). The cache-hit path was fixed (line 3087-3098: hard error on `fn_addrs.get(name).is_none()`); the fresh-build path has three silent-skip holes.

**Fix specification**:
1. Each `else { continue }` / skipped-if becomes a hard error: return `CranelispError::ModuleError` with a message naming the failing step.
2. After the loop, assert that every `name` in `names` has `code.is_some()` AND the matching GOT slot is non-NULL. This is the scheduler-notification precondition: we do not notify `inmem_codegen_batch_complete` until this assertion holds.

### 6.2 Reading the cache-hit path

`src/worker.rs:3082-3101` already does the hard-error variant correctly. Reference model for the fresh-build fix.

### 6.3 Ordering audit

Are slot stores visible to cross-module readers before `Code::Jit` writes? The answer lives in the sequencing within the per-name iteration (slot store @ 2899 precedes code write @ 2911). Between iteration `i` and `i+1`, a concurrent codegen worker for another module might iterate `tc_modules` (via line 2827 `for st_entry in tc_modules.iter()`) and collect this module's partially-populated set of `Code::Jit` entries. That is fine for **JITBuilder symbol registration** (the concurrent worker uses these as extra JIT symbols for a later finalize, not as immediate call targets). It is NOT fine if any downstream execution path dispatches through a GOT slot before the slot has been stored.

**Load-bearing invariant**: The scheduler must not release a module's `inmem-done` state to consumers until its codegen worker's per-name loop has finished and every slot is populated. `notify_inmem_codegen_batch_complete` is the release point; the fix specification at §6.1 pins the pre-notify assertion.

### 6.4 What about parallel codegen across modules?

`codegen_worker(M_1)` and `codegen_worker(M_2)` run concurrently. Per Decision 37 §"Order-independence", M_2's codegen reads from `__cranelisp_got_{M_1}` at *runtime* (not at codegen time), so M_1's slots not yet being populated when M_2 compiles is fine. The concern is at runtime: when M_2 (or M_1) execution dispatches through a M_1 slot, it must be populated.

**Scheduler discipline**: no module's code can execute until all its transitive deps' `inmem-done` notifications have fired. The `block_for_typecheck` / `block_for_codegen` path in the scheduler enforces this — **provided the inmem-done notification is correctly gated on slot population, not just on codegen completion**. That is §6.1's fix specification.

---

## §7 Sketch comparison (MANDATORY)

Per /arch Condition 1, absence of §7 blocks Phase 3. Per root `CLAUDE.md` "Sketch Oracle", sketch patterns must be studied before divergence is justified.

### 7.1 How the sketch handles JIT/object divergence

The sketch has TWO explicit codegen paths (confirmed by file inspection):

- `sketch/src/codegen.rs` — 76 KB, the single-module JIT codegen. Called from `sketch/src/batch.rs` (batch mode) and `sketch/src/repl.rs` (REPL mode).
- `sketch/src/cache.rs` — object-module codegen. Lines 351+ of `sketch/src/cache.rs`: "ObjectModule compilation" section. Creates a fresh `ObjectModule` with the same ISA as the JIT, emits functions against it, finishes, writes bytes. This is the cache-write path.

**This is exactly the dual-path shape that Decision 23 deletes.** The sketch's `cache.rs:351+` and `codegen.rs`-via-`batch.rs` are independent implementations that can (and did) diverge. The audit finding that motivated Decision 23 is recorded in `design/arch/archive/pipeline-convergence-review.md` and is the reason the reimplementation has one `compile_to_module<M: Module>` function.

### 7.2 Divergence and rationale

The reimplementation diverges from the sketch by construction (Decision 23 unifies codegen; Decision 25 unifies retention; Decision 37 unifies the register-then-codegen flow). **This is the correct divergence** — the sketch's dual-path shape IS the defect class S59's carry failures trace to in spirit, and Decision 23 / 36 / 37 eliminate that class at the *structural* level.

**BUT**: convergence is only real if the shared `compile_to_module<M>` genuinely produces identical CLIF (§1.1) for both `M = JITModule` and `M = ObjectModule`. The S59 evidence of REPL-works / imported-fails suggests that WITHIN the single pipeline, some per-entry state (AST annotations, mono context, drop-glue references) still diverges between the "first time this symbol is compiled, typed inline at the REPL" path and the "this symbol is compiled as part of a batch of imported deps" path. The divergence is not in `compile_to_module`'s Module-parameterised branches; it is in the upstream state the single pipeline reads from.

### 7.3 Sketch patterns worth following

The sketch's codegen-level RC/closure/cross-module patterns that the reimplementation already follows or that are relevant to §5 (drop-glue retention):

- **Scope cleanup discipline** (`sketch/src/codegen.rs:176-260`): `borrowed_vars`, `consumed_vars`, `unique_vars` tracking; `pop_scope_for_value` with skip rules for borrowed and consumed. The reimplementation ports this and the S59 Pass-2 fix corrected `protect_return_value` against the same discipline.
- **Closure drop glue** (`sketch/docs/closures.md`): the sketch stores `drop_glue_ptr` as a direct code pointer in the closure layout. Under the sketch's per-session JIT (no per-batch reclaim), this is safe because the JIT lives the full session. Under the reimplementation's Decision 31 per-batch reclaim, the same pattern is unsafe — hence §5.3's specified direction toward GOT-slot-indexed dispatch for drop glue.
- **GOT management** (`sketch/docs/modules.md`): per-module GOT, swap patterns for trace/run-tests. The reimplementation's two-GOT model (Decision 23) is a refinement — the sketch had only the in-process GOT; the `.o` data-section GOT is new.
- **`emit_scope_cleanup_for_tco`** (`sketch/src/codegen.rs:660`): the sketch's TCO scope-cleanup discipline. Sprint 59 ported this to `crates/cranelisp-backend/src/compiler/mod.rs:879-959` (per the S59 §Mechanism addressed notes).

### 7.4 Sketch patterns NOT to follow

- **Dual codegen paths** — the sketch's `cache.rs:351+` separate ObjectModule codegen. Reimplementation: single `compile_to_module<M>`.
- **Per-session JIT lifetime** — the sketch holds one `JITModule` for the whole session; no per-batch reclaim. Reimplementation: per-batch `Arc<Jit>` with custom Drop → `unsafe free_memory()` (Decision 31).
- **Session-global retention via `kept_jits` / `kept_linkers`** — the sketch's mirror of this pattern was what Sprint 58 Wave 3 dissolved. Reimplementation retains via `Code::Jit` / `Code::Linker` per-entry.

### 7.5 Where the sketch's absence of H3/H4 matters

The sketch never ran into H3 (cross-module drop-glue × reclaim race) because it had no per-batch reclaim — `grid`'s JIT pages lived forever. The sketch never ran into H4 (GOT-slot NULL-sink under parallel codegen) because its codegen was serial.

**Implication**: the reimplementation's H3 and H4 exposure is **new** to the reimplementation's architecture. The sketch is not an oracle for these two classes. The fix specification in §5.3 and §6.1 is an extension of Decision 31 + Decision 37, not a port of a sketch solution.

---

## §8 Test plan

Map each of the 5 failing tests to the hypothesis whose resolution flips it; name the regression guard that protects against re-divergence.

### 8.1 Test-to-hypothesis mapping

| Failing test | Expected to flip under | Why |
|---|---|---|
| `sprint59_defects456_repro::d45_solution_cell_single_call_no_rc_underflow` | H3 fix (drop-glue GOT indirection) | Smallest repro of "imported polymorphic, 2× grid arg, match-extract + str-concat". If H3 is the root, the drop-glue-through-GOT fix flips this deterministically. |
| `sprint59_defects456_repro::d45_html_min_v1_no_crash` | H3 fix + §6.1 GOT-slot audit fix | Same shape + tail-recursive loop over 9 cells. Each iteration re-enters the drop-glue path. H3 root. The §6.1 audit fix removes the silent-skip that might mask the H3 symptom during tight loops. |
| `sprint59_defects456_repro::d6_exemplar_propagate_only_does_not_segv` | H3 fix | Tail-recursive propagate with match-projected `g2`; the TCO scope-cleanup dec's the old `g`, which dec's its inner Cells, which calls `grid/cell-drop` via whatever mechanism §5 audits. If that mechanism is direct `func_addr` into `grid`'s JIT and reclaim has fired, trap. GOT indirection fixes. |
| `wave6_demo_repros::exemplar_solver_does_not_stack_overflow_on_small_puzzle` | H3 fix (primary) + §4.3 `restore_cached_module` fix (if triggered on this specific load path) | Larger shape; if H3 alone flips the three minimal repros, the solver likely flips too. The §4.3 fix is a carry-forward hardening that protects against the Arc-drop race during cache reload. |
| `wave6_demo_repros::run_tests_batched_invocation_no_crash` | H3 fix + §6.1 GOT-slot audit fix | Batched `/run-tests` dispatch through GOT slots that may be partially populated during parallel codegen. §6.1 fix pins the notify-after-all-slots-populated invariant. H3 fix pins the per-test drop-glue retention. |

If H3 does not flip all five, escalate to /sprint per Condition 2 (Phase 3 gate). Likely sub-fix: H1 audit (mono codegen context) as the second hypothesis to rule out.

### 8.2 Convergence regression guard

**Permanent committed test** (to be authored by `/qa` during implementation wave, at `tests/v4_convergence.rs`):

```rust
// spec: design/backend/jit-object-convergence.md §1.1 — JIT/Object invariant
#[test]
fn same_source_produces_same_clif_for_jit_and_object() {
    // Given a module M with defns f, g, h:
    //   parse → typecheck → compile_to_module<JITModule> → capture CLIF
    //   parse → typecheck → compile_to_module<ObjectModule> → capture CLIF
    // Assert per-function CLIF bytes are byte-identical.
}
```

#### 8.2.1 Pre- vs post-relocation CLIF — decision

**Decision**: `same_source_produces_same_clif_for_jit_and_object` compares **pre-relocation CLIF text** — the IR emitted by `compile_to_module<M: Module>` *before* any Module-specific finalize step (`finalize_definitions` for JIT, `finish`/relocation-emit for Object). /qa's recommendation at `tests/plan/ring4.md §G.20.10` is adopted.

**Rationale (cited from §1.2 / §3.2 of this doc)**: the invariant at §1.1 names the "fixup-mechanism boundary" as the *single* permitted divergence. Resolving `__cranelisp_got_{M}` (via `JITBuilder::symbol_lookup_fn` on the JIT path vs via linker-emitted `.o` relocations on the object path) and producing per-symbol `*const u8` entry points are listed in §1.2's exhaustive "MAY differ" table. Post-relocation bytes therefore NECESSARILY differ between the two paths at every cross-symbol call site and every GOT-data reference — that is the fixup mechanism *by construction*. Comparing post-relocation bytes would either (a) fail unconditionally (defeating the test), or (b) require the test harness to lift the fixup mechanism into the comparison (re-applying or inverting relocations before diffing), which would effectively re-implement the boundary inside the assertion and destroy the test's ability to guard the invariant.

**What "pre-relocation CLIF" means concretely**: the CLIF function bodies as pretty-printed (or canonically serialised) by Cranelift immediately after `compile_to_module<M>` returns `CompilationResult`, and BEFORE the Module-specific finalize call. At this point:

- Instructions reference external names (`UserExternalName`) and GOT-data symbols symbolically, not as resolved addresses.
- `func_addr`, `call`, `call_indirect`, `global_value` operands carry symbol references, not raw `*const u8` values.
- No `Linkage::Export` / `Linkage::Import` resolution has occurred against concrete module state.

The comparison therefore captures every codegen decision that the Module-parameterised backend makes (RC ops, drop-glue emission, GOT-slot calling convention, monomorphisation choices, ADT match layout, closure construction) without conflating them with the downstream fixup step.

**Harness boundary**: the test harness MUST drive `compile_to_module<JITModule>` and `compile_to_module<ObjectModule>` against (i) the same parsed+typechecked input tuple and (ii) a fresh `DashMap<ModuleFullPath, SymbolTable<C, L>>` bearing identical typed state (per §1.3 falsifiability procedure #1). It MUST capture CLIF per-function BEFORE calling `finalize_definitions` (JIT) or `finish` (Object). Workstream B's CLIF-dump infrastructure (`CRANELISP_CODEGEN_DUMP=...`) is the capture mechanism; the dump fires at the pre-finalize boundary for exactly this reason.

**Byte-identity modulo normalisation**: "byte-identical" at §1.3 means "after normalising function-name symbols and Cranelift-assigned internal IDs (block numbers, value numbers, func refs) that are allocated fresh per-compilation". The comparison is on the *structural* CLIF — instruction sequences, operand shapes, RC-op placements, call-site shapes. A diff tool that canonicalises these auxiliary identifiers is part of the test harness; design decisions about how to canonicalise are recorded alongside the test when it lands.

**Cross-reference**: `tests/plan/ring4.md §G.20.10` (resolution of its FIXME(/backend) points here).

#### 8.2.2 Remaining regression guards

```rust
// spec: design/backend/jit-object-convergence.md §1.3 — GOT-slot address match
#[test]
fn fresh_build_and_cache_hit_produce_matching_got_slot_contents() {
    // Given a module M compiled fresh in session 1, cached, reloaded in session 2:
    //   session 1's symbol_tables[M].got.load_slot(i) for each defined symbol
    //   session 2's symbol_tables[M].got.load_slot(i) for the same symbol
    // Assert the values resolve to byte-equivalent code (call both, verify same behaviour).
}

// spec: design/backend/jit-object-convergence.md §5.3 — Drop glue GOT indirection
#[test]
fn cross_module_drop_glue_routes_through_got_not_direct_func_addr() {
    // Given module A defines an ADT T with drop glue, module B consumes T values:
    //   Inspect B's CLIF for every emit_rc_dec site that dec's a T value.
    //   Assert the dec site emits call_indirect through A's GOT, not a direct func_addr.
}

// spec: design/backend/jit-object-convergence.md §6.1 — No swallowed failures, fresh-build
#[test]
fn fresh_build_codegen_fails_loudly_if_any_slot_is_unpopulated() {
    // Given a module M where compilation of symbol f produces no code_ptr:
    //   inline_jit_codegen_for_names must return CranelispError::ModuleError, not Ok(())
    //   The scheduler must NOT receive a notify_inmem_codegen_batch_complete for M.
}
```

These four tests are the durable regression guard. They trip if any future refactor (e.g., Sprint 61's FQTypeName migration) re-introduces divergence.

---

## §9 Fix scope estimate

### 9.1 Per-hypothesis estimates

| Hypothesis | LOC estimate | Days | Confidence |
|---|---|---|---|
| H3 fix (drop-glue → GOT indirect; closure drop-glue layout revision) | 150–250 LOC in `crates/cranelisp-backend/src/compiler/` (mod.rs, heap.rs, closure-codegen) | 1.5–2.5 days | Medium — scope depends on whether closure layout changes are needed (additive field vs replacement) |
| §4.3 fix (`restore_cached_module` merges GOT rather than swapping; `Arc<GotTable>` retention discipline) | 60–100 LOC in `crates/cranelisp-typecheck/src/` + `src/worker.rs` | 0.5–1 day | Medium — requires careful handling of the symbol-table swap vs merge semantics |
| §6.1 fix (fresh-build no-swallowed-failures; scheduler-notify precondition) | 30–60 LOC in `src/worker.rs::inline_jit_codegen_for_names` + scheduler notify sites | 0.25–0.5 day | High — mirror of the cache-hit path's established pattern |
| H4 audit (if H4 is the root instead of H3) | 30 LOC audit + 30-80 LOC fix | 0.5–1 day | Medium |

### 9.2 Combined estimate

**Assuming H3 + §4.3 + §6.1 all land (likely all three are related)**: 240–410 LOC, 2.25–4 days.

**If H3 alone suffices**: 150–250 LOC, 1.5–2.5 days.

**If H3 does not suffice and H1 audit becomes necessary**: add 2–3 days of investigation (CLIF-diff infrastructure from Workstream B is load-bearing).

### 9.3 Scope classification

Per /arch Condition 2, >500 LOC or >3 days requires scope rescope.

**Status**: **IN SCOPE under H3-only framing; borderline under H3 + §4.3 + §6.1 framing.** The combined path is 2.25–4 days with the upper end exceeding the 3-day threshold.

**Header flag**: `SCOPE RESCOPE NOT YET REQUIRED` — the lower bound of the combined estimate (2.25 days) fits; the upper bound (4 days) exceeds and should trigger rescope IF Workstream B's CLIF-dump reveals all three mechanisms are breaches.

**Recommended Phase 3a action**: /sprint should schedule an audit-wave first (Workstream B delivers CLIF-dump in Wave 1 early; H3 audit uses it; if H3 alone is confirmed the fix fits in budget) before committing the full scope. If the audit confirms all three breaches, /sprint revisits the scope; options include (a) landing H3 + §6.1 in Sprint 60 and carrying §4.3 to Sprint 61, or (b) expanding Sprint 60 by one wave with user sign-off.

### 9.4 Interface-gap check

Per /arch's Phase 3 requirement: file FIXME(/arch) if any new `Code` variant, new boundary type, or new `Module` trait method is required.

**Current assessment — no interface extension required** if:
- H3 fix is a codegen-internal change (drop-glue emission routes through existing GOT mechanism; no new `Code` variant needed).
- §4.3 fix is a symbol-table-merge logic change inside `restore_cached_module` (no new boundary type).
- §6.1 fix is a hard-error escalation inside `inline_jit_codegen_for_names` (uses existing `CranelispError::ModuleError`).

**Possible interface need** (FIXME-escalation conditions):
- IF closure layout grows a "drop-glue owning module's GOT base + slot index" pair, the closure representation in `crates/cranelisp-backend/` changes — but closure representation is backend-internal, not a boundary type. No `/arch` review needed.
- IF `Arc<GotTable>` retention discipline requires changes to `SymbolTable`'s `got` field (e.g., replacing `GotTable` with `Arc<GotTable>` if not already), that IS a boundary type change. File FIXME(/arch).

<!-- /arch answer (Sprint 60 Phase 3a): SymbolTable.got is ALREADY `std::sync::Arc<GotTable>` (see `crates/cranelisp-types/src/module.rs:124`). `base_ptr()` returns a stable address for the lifetime of the Arc (the Wave 0 tests at `module.rs:906-980` verify this). §4.3's fix path therefore does NOT require a SymbolTable shape change. The fix is a logic change inside `src/worker.rs::restore_cached_module` — detect a pre-existing `symbol_tables[M]` entry and either (a) merge slot layout into the preserved `Arc<GotTable>` rather than swap the Arc, or (b) propagate the preserved Arc onto the newly-installed SymbolTable. No interface review needed; estimate recalibrates to ~40–80 LOC. -->

<!-- /arch answer (Sprint 60 Phase 3a): the existing `Linkage::Import` + `__cranelisp_got_{M}` mechanism covers user-defn *calls* (cross-module call emission in `compile_to_module`) but does NOT cover function-pointer *values* stored in data (specifically, the closure `drop_glue_ptr` field). Current closure codegen at `crates/cranelisp-backend/src/compiler/control_flow.rs:574-588` emits `builder.ins().func_addr(types::I64, glue_ref)` — a raw address baked into the closure at construction, resolved against the glue fn's `Linkage::Local` declaration (line 850). The tear-down at `compiler/mod.rs:1229-1256` issues `call_indirect` on that raw pointer. If the closure is constructed in module A's JIT and dropped after A's `Arc<Jit>` has reclaimed (Decision 31 Scenario 2), the raw pointer dangles — this IS the H3 breach applied to closures. Fixing H3 therefore requires NEW codegen: either §5.3 option (a) (store owning-module GOT base + slot index in the closure; GOT-load at drop time — `/arch` recommends) or option (b) (capture the owning-module `Arc<Jit>` in the closure). Option (a) is the natural generalisation of Decision 36's "Why all-GOT calling" to function-pointer-valued fields, and aligns with Decision 31's callback-platform forward commitment which establishes the same principle for host callbacks. The fix is backend-internal (closure layout + drop-glue dispatch); no `cranelisp-types` boundary change. A Decision 38 will be recorded post-implementation once the exact closure-layout shape is validated — deferred per standing Phase 3a rule. -->

---

## Next skills

- `/arch` — Phase 3a review of this doc. Conditions to verify: §1 invariant wording is normative and falsifiable (not merely descriptive); §4.3 finding (carry-forward does NOT fire through `restore_cached_module`) is accurate; §5.3 direction (drop-glue through GOT) aligns with Decision 31 + 36 spirit; the two FIXME(/arch) items above are tractable.
- `/backend` (Wave 1 implementation) — Workstream B (CLIF-dump) lands first. Then H3 audit using the dump. Then §6.1 fix (cheap, highest-confidence). Then H3 fix. Then §4.3 fix (if audit confirms). Regression guards from §8.2 land with each fix.
- `/qa` — author the four regression tests in §8.2 as each fix lands. Add `[Tested]` annotations per `spec/`'s traceability convention.
- `/review` — code review at the close of Wave 1 implementation. Classification focus: did the fix close the invariant breach or patch a symptom? Patch-a-symptom fixes are Blockers per Principle 7.
