# Sprint 56: Single Codegen Entry Point

**Status**: ACTIVE
**Ring**: 4 (Effects — full spec scope)
**Goal**: Route all codegen (JIT batch, REPL expression, object file) through a single `compile_to_module` entry point that reads from the symbol table. Delete `codegen_module_symbols` and its helpers.

## Scope

Phase 2 of `design/arch/pipeline-v4-roadmap.md`. Sprint 55 landed Phase 1 (AST on symbol table): `ModuleEntry::Def.ast` carries typechecked bodies; `Expr` nodes carry `inferred_type` and `resolved_call` annotations; `CheckResult` is no longer a boundary type.

Phase 2 completes the target data model: `compile_to_module` stops taking a `Program` and reads everything from the symbol table, and the separate JIT sweep function (`codegen_module_symbols`) is deleted. After Phase 2, the backend has **one** compilation function.

Three sequential steps, each leaving tests green. **Unifying principle (Principle 11)**: one compilation pipeline, one entry point, one code path. Mode differences (JIT vs Object) are handled entirely by the `Module` implementation, outside `compile_to_module`. No `CompilationEnv` trait, no env types, no wrappers, no `CodegenTarget` enum. If two paths appear anywhere in the design, that is a defect, not a feature.

0. **Wave 0 (Step 1.5)** — Pre-materialise AST on mangled symbol-table entries and pull G7 forward so the symbol table is the single source of truth for both AST bodies and GOT state.
   - **/typecheck**: `register_mangled_variants` must insert each multi-sig variant entry with `ast: Some(...)` — a single-variant `Defn` carrying the typechecked body under the mangled name. `expand_multi_sig_defn` in the backend becomes redundant.
   - **/typecheck**: `register_mono_entry` must insert mono specialisations with `ast: Some(...)` — the annotated body from `MonoDefn.defn` with all post-pass resolutions applied. The `finalize_module` program-inlining path goes away.
   - **/typecheck**: expose `SymbolTable::defined_symbols()` iterator filtering to codegen-compilable entries (`ast.is_some() AND kind != Overloaded AND kind != UserFn{constrained_fn: Some}`). Shared predicate — Decision 22.
   - **G7 pulled forward**: `got: GotTable` moves onto `SymbolTable`. `TypecheckProduct.got` deleted (may collapse `TypecheckProduct` entirely — coordinate `/typecheck` + `/int`). Rationale: unified strategy needs GOT bases on the symbol table so the JIT path can resolve them via `JITBuilder::symbol_lookup_fn` without a second DashMap parameter. See `pipeline-v4-roadmap.md` §Phase 3 Step 3a — we lift it now to keep `compile_to_module` at 4 params.

1. **Step 2a** — `compile_to_module` takes `names: &[Symbol]` (G4). PRESCRIPTIVE signature:
   ```rust
   pub fn compile_to_module<M: Module>(
       module_path: ModuleFullPath,
       names: &[Symbol],
       symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
       module: &mut M,
   ) -> Result<CompilationResult, CranelispError>
   ```
   - **4 parameters.** No env. No mode discriminator. No wrappers.
   - Implementation enumerates `names` and reads `ModuleEntry::Def.ast` for each body.
   - Multi-sig, constrained, and default-method entries are all symbol-table entries — no special expansion in callers or backend.
   - **GOT emission is uniform across modes**: `compile_to_module` emits `global_value` against a `Linkage::Import` data symbol `__cranelisp_got_{module}`. The `Module` resolves it — Object via relocation (linker patches), JIT via caller-registered `JITBuilder::symbol_lookup_fn` returning `symbol_tables[m].got.base_ptr()`. Backend IR is byte-identical in both modes. Tradeoff accepted: one extra memory load per cross-module JIT call vs structural simplicity.
   - `CompilationResult` gains `artifacts: HashMap<Symbol, FunctionArtifacts>` (per-symbol CLIF IR / disasm / code_size) so the priority worker can populate `Introspection` without a separate compilation pass. See `pipeline-v4.md` §9.6.

2. **Step 2b** — Delete `codegen_module_symbols` and route JIT through `compile_to_module` (G5).
   - Priority worker calls `compile_to_module(path, &names, &symbol_tables, &mut jit_module)` directly, after configuring `JITBuilder::symbol_lookup_fn` to resolve `__cranelisp_got_*` names from `symbol_tables`.
   - `compile_regular_defns`, `compile_and_register_defn_shared`, `pre_register_got_slots_in_tc`, `SessionCompilationEnv`, `SessionCompilationEnv.collect_jit_setup_for_module` — all deleted.
   - `src/worker.rs` substantially reduced.
   - Batch and REPL paths converge into one JIT codegen path.

### Direct failure-fixing opportunities

The baseline (1590 passed / 22 failed) includes 3 multi-sig JIT failures (`sketch_multi_sig_type_based_dispatch`, `sketch_multi_sig_different_arities`, `sketch_repl_multi_sig_different_arities`). These fail because the JIT path's multi-sig expansion (`collect_and_declare_defns`) diverged from the object path. Phase 2's unification is expected to fix them.

Other baseline failures (9 cache SIGSEGV, 3 sprint23 cache/link, 1 v4 cache-hit dep, 1 run-tests, 5 v4_platform) are NOT targets of this sprint — they are Phase 3+ or new-feature concerns. Must not regress.

### /int Burden Assessment

**HEAVY.** `codegen_module_symbols` and `compile_regular_defns` live in `src/worker.rs` (owned by `/int`). The priority worker loop, GOT slot pre-registration, and `SessionCompilationEnv.collect_jit_setup_for_module` all require rework. Step 2b is primarily deletion but requires carefully staged replacement of the priority worker codegen dispatch.

Mitigation: Step 2a's signature change alone does NOT delete the JIT sweep — it only reshapes the signature. Callers (including `codegen_module_symbols`) can adopt the new signature first. Step 2b is a separate step that deletes the sweep.

### Deferred Tests from Prior Sprints

22 tests remain deferred — all need later phases:
- 3 multi-sig JIT (**THIS SPRINT — Phase 2 fixes**)
- 9 cache multi-module (Phase 3+5)
- 3 sprint23 cache/link (Phase 5)
- 1 v4 cache-hit dep (Phase 5)
- 1 run-tests special form (new feature, deferred from Ring 4 gaps)
- 5 v4_platform (needs triage — may be platform registry issue)

### FIXME Debt

FIXME scan of `src/`, `crates/`, `design/backend/`, `design/typecheck/`, `design/int/` found no source code FIXMEs needing resolution. Design doc FIXMEs are historical or instructional examples.

### Out of Scope

- Phase 3 (GOT + code on SymbolTable) — independent, next sprint
- Phase 4 (platform functions + persistent priority workers)
- Phase 5 (structural declarations + cache serialization)
- Ring 4 gate review
- Run-tests special form (not a Phase 2 concern)
- `v4_platform` failures (may improve incidentally but not a target)

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| — | — | No active FIXMEs in scope | — |

## Architecture Review

**Reviewer**: `/arch`
**Verdict**: **APPROVED with conditions** — scope is coherent and materially advances the v4 data model, but two prerequisites on `/typecheck` must land in Wave 0 before Step 2a can begin, and the PRESCRIPTIVE sections of `design/backend/compile-to-module.md` MUST be updated before any implementation wave opens.

### 1. Technical Coherence — Step Sequencing

Step 2a → 2b is correctly ordered and each step can land green independently.

- **Step 2a (signature flip)** is a targeted change: `compile_to_module(path, names, symbol_tables, module)`. Implementation enumerates `names`, reads `ast`/`scheme` from `ModuleEntry::Def`, and no longer needs `program: &Program`. Callers (nice worker in `src/session_v4.rs:3346`, cache paths in `crates/cranelisp-backend/src/cache/{mod.rs:473, object.rs:337,547,602}`, and the JIT sweep in `src/worker.rs`) must pass the right name list. **This can ship green without touching the JIT sweep's internal shape** — `codegen_module_symbols` is free to keep compiling one defn at a time internally; what changes is the *inputs it hands to* `compile_to_module`. That is the correct seam to split on.
- **Step 2b (sweep deletion)** is a structural delete. Once the signature reads from the symbol table, `codegen_module_symbols`, `compile_regular_defns`, `pre_register_got_slots_in_tc`, and `collect_jit_setup_for_module` collapse into a per-symbol `compile_to_module` call in the priority worker. The "per-worker `JITModule`" phrasing in scope is consistent with §9.4 (per-function JIT isolation).

The fix for the 3 multi-sig JIT failures in Step 2b is the right place for them — they are a direct symptom of `collect_and_declare_defns` diverging from the object path, and converging on one function is what removes the divergence.

### 2. No Interim Architecture (Principle 8)

Clean. Nothing in the scope builds a throwaway. Specifically:

- `names: &[Symbol]` is the §9.3 target signature verbatim. No intermediate "remove `program` but keep `CheckResult`" or "add a `names` sidecar to `Program`" dodge.
- Per-worker `JITModule` is the §9.4 target, not a stepping stone.
- The removal of `SessionCompilationEnv` / `collect_jit_setup_for_module` tracks the §9.1 "symbol table is the single store" principle — JIT symbols and GOT data defs are derived from `symbol_tables` internally by `ObjectCompilationEnv` (already in place from Phase 1).

One latent risk: Step 2b is described as "per-function `JITModule`" which is correct for §9.4, but the sprint plan does NOT yet commit to the §9.4 *`Code`-on-`ModuleEntry::Def`* target (that is Phase 3, G6). The intervening state — per-function `JITModule` whose lifetime is still managed by `CodegenProduct` — is acceptable as a Phase 2→3 bridge and does not constitute interim architecture. `/int`'s Phase 2 design doc MUST state this explicitly so the Phase 3 transition is a refactor, not a rewrite.

### 3. Design References

The plan cites the right top-level docs (`pipeline-v4.md §9.3`, `pipeline-v4-roadmap.md` Phase 2, `ast-sourced-codegen.md`) but is under-referenced for implementation-specific contracts. Required additions:

- **`/backend` plan**: must cite §2.1 of `compile-to-module.md` (PRESCRIPTIVE — currently 4 params, Sprint 55 removed `typecheck`). The note in §Notes is right that this doc needs an authoritative update; I want this done **in Wave 1 by `/backend`**, not deferred. Leaving a PRESCRIPTIVE "four parameters, no more" section whose parameter list is already stale is exactly the kind of drift that `interfaces.md` coherence (Principle 13) exists to prevent. Also: §2.3 internal-derivation table, §5 GOT reference encoding, §12 ObjectCompilationEnv (already the live `CompilationEnv`).
- **`/typecheck` plan**: must cite `pipeline-v4.md §9.1` (mangled variants / mono / defaults as *separate* symbol-table entries) and Decision 21 in `design/arch/CLAUDE.md` (callees on `ModuleEntry`). The design-doc update to `ast-annotation.md` must explicitly enumerate **which mangled symbols carry `ast: Some(_)`** post-Phase-2 (see §5 below).
- **`/int` plan**: must cite `pipeline-v4.md §9.4` (per-function JIT isolation) and `§9.6` (Introspection separate from compilation). The new `design/int/phase2-codegen-convergence.md` should explicitly document which symbol-table lookups replace which `SessionCompilationEnv` method.
- **Missing entirely**: `design/arch/interfaces.md` — `/arch` will update this in Wave 0 if `compile_to_module`'s contract changes; the sprint should not land with `interfaces.md` stale.

### 4. Interface Changes Required in `cranelisp-types`

**None required for Step 2a.** Phase 1 already landed `ast: Option<Defn>` on `ModuleEntry::Def` and annotations on AST nodes. The Phase 2 signature change is purely a `cranelisp-backend` surface change — `cranelisp-types` is untouched.

For Step 2b, still no boundary type changes. The `code: Option<Code>` field envisioned in §9.1/§9.4 is Phase 3 (G6) and is explicitly out of scope.

**Non-blocking observation**: `CheckResult` in `crates/cranelisp-types/src/check.rs` still carries `method_resolutions`, `mono_defns`, `default_method_defns`, `constrained_fn_names`, `expr_types`, `warnings`, `display`. Per Phase 1 status these are no longer *boundary* data (backend reads from nodes / symbol table), but the struct has not yet been split into the typecheck-internal `CheckOutput` per `ast-sourced-codegen.md §3.7`. This is OK for Phase 2 (signature change doesn't require the type to go away) but `/typecheck` should file a tracking FIXME on `check.rs` so it is not silently forgotten before Phase 5 cache work starts relying on the slimmed shape.

### 5. Prerequisites Not Yet In Place

This is where the sprint as currently drafted has real gaps. Step 2a cannot land green without the following:

**5.1 Multi-sig variants (Wave 0 prerequisite for `/typecheck`)**

`compile_to_module` currently calls `expand_multi_sig_defn` internally (`crates/cranelisp-backend/src/lib.rs:123,379–436`), reading `OverloadVariant` from the `Overloaded` base entry and synthesising `Defn` values with param types and spans derived from the variant list. After Step 2a, callers pass `names: &[Symbol]` — if the caller passes the **base** name, the backend still needs to expand; if it passes **mangled** names, the mangled entries must already exist with populated `ast`.

Inspecting `register_mangled_variants` (`crates/cranelisp-typecheck/src/program.rs:1583–1596`) shows mangled variant entries are inserted with `ast: None`. The *bodies* live only in the base `Defn`, and the backend synthesises per-variant `Defn`s at codegen time.

**Two options, pick one in Wave 0**:

- **(A) Pre-materialise mangled variants with `ast`**: `/typecheck` populates `ModuleEntry::Def.ast = Some(...)` on each mangled-variant entry, cloning the corresponding `DefnVariant` into a single-variant `Defn` under the mangled name. Callers pass mangled names; `compile_to_module` drops `expand_multi_sig_defn` entirely. **This is the §9.1 target** ("the typechecker expands DefnMulti into mangled variant entries ... each as a separate `ModuleEntry::Def` with its own `ast`").
- **(B) Keep `expand_multi_sig_defn` inside `compile_to_module`**: callers pass base names; backend expands internally. Pragmatic, smaller change, but re-enshrines the synthesis-in-backend pattern that §9.1 explicitly moves away from.

**Recommendation: (A).** (B) is a Phase-1.5 half-step: it leaves mangled names in the symbol table with `ast: None` while codegen "knows" where to find the body. That is exactly the kind of split-source-of-truth the v4 data model is eliminating. (A) is also the fix for the 3 multi-sig JIT failures — if mangled entries carry `ast` uniformly, the JIT/object divergence has nowhere to hide.

**5.2 Mono specializations (Wave 0 prerequisite for `/typecheck`)**

`register_mono_entry` at `crates/cranelisp-typecheck/src/program.rs:1648–1660` inserts mono specializations with `ast: None`. The bodies currently ride on `CheckResult.mono_defns: Vec<MonoDefn>` and are inlined into `program` by `finalize_module` (`src/worker.rs:1254–1258`) before codegen.

After Step 2a, the `program` inlining goes away (the caller passes `names`, not a program). Mono entries MUST carry their annotated body in `ast`. This is the `/typecheck` piece of Phase 2; the sprint plan for `/typecheck` correctly states it — it just needs to be flagged as a **hard prerequisite for `/backend`'s Step 2a work**, not a parallel activity.

**5.3 Default method defns (resolved in Phase 1 — confirmed)**

Default method defns are registered via `register_mangled_method` in `crates/cranelisp-typecheck/src/traits.rs:680–700` and DO carry `ast: Some(annotated)`. Good — Phase 1 closed this. The `CheckResult.default_method_defns: Vec<Defn>` list is duplicate data that `finalize_module` re-inlines into `program`; after Step 2a it becomes dead and should be removed alongside the signature change (a few lines in `worker.rs` and `program.rs`).

**5.4 Trait-impl methods (resolved in Phase 1 — confirmed)**

`check_impl_method` writes annotated AST onto the mangled entry (`traits.rs:683–700`). Confirmed OK.

**5.5 REPL synthetic `__expr` defn**

`finalize_module` at `src/worker.rs:1233` retrieves `table.get("__expr")` and its `ast` to recover the annotated expression. After Step 2a, the REPL expression path must pass `__expr` (or whatever mangled name it uses) as an element of `names`. `/int`'s plan should cover this explicitly — it is the one REPL-eval wrinkle that distinguishes §9.3 "pass names" from the current "wrap expr in synthetic program" pattern.

**5.6 What the `defined_symbols()` enumeration must return**

For Step 2a acceptance ("enumerating `symbol_table.defined_symbols()` for a module produces the same set of compilable defns that `compile_to_module` currently derives from `program`"): the enumeration must return, for each module, the set of `ModuleEntry::Def` entries where `ast.is_some()` AND kind is not `Overloaded` (the base entry has `ast: None`, only its mangled variants are compiled) AND kind is not `UserFn { constrained_fn: Some(_) }` (the template is skipped in favour of its mono specializations). `/typecheck`'s plan should specify this filter, ideally by exposing an iterator method on `SymbolTable` so every caller applies the same predicate.

### 6. Conditions for Approval

The following MUST be true before implementation waves open:

1. **Wave 0 is added** before Step 2a, owned by `/typecheck`, with two deliverables:
   - Mangled multi-sig variant entries carry `ast: Some(...)` (prereq 5.1 option A).
   - Mono specialization entries carry `ast: Some(...)` with all annotations the backend reads (prereq 5.2).
   - Both must land green (tests still 1590/22) before `/backend` begins Step 2a.
2. **`design/backend/compile-to-module.md` is updated in Wave 1 by `/backend`** — not deferred. §2.1 PRESCRIPTIVE signature becomes `(module_path, names, symbol_tables, module)`; §4 "Defn Collection" is rewritten around symbol-table enumeration; §9 and §13 migration steps are reflowed. A stale PRESCRIPTIVE design doc is an architecture violation under Principle 13.
3. **`/typecheck`'s `ast-annotation.md` update enumerates every category of symbol-table entry that must carry `ast: Some(_)` post-Phase-2** — regular defns, mangled multi-sig variants, mono specializations, default method defns, trait-impl methods, and the REPL `__expr` synthetic. One table. This is the contract `/backend` implements against.
4. **`/int`'s Phase 2 design doc explicitly scopes the per-function `JITModule` lifetime** so the Phase 3 G6 transition (moving `Code` onto `ModuleEntry::Def`) is a refactor rather than a rewrite. Do NOT delete `CodegenProduct` in Phase 2 if Phase 3 still needs a temporary home for `Code`.
5. **`constrained_fn_names` derivation is centralised**. Currently computed inline in `compile_to_module` (`lib.rs:95–109`) by scanning the symbol table. After Step 2a, the caller (Step 2b: the priority worker) also needs the same predicate to decide which names to pass. Expose a single `SymbolTable` method so both sides agree.
6. **`CheckResult` slimming is filed as a tracking FIXME** by `/typecheck` on `crates/cranelisp-types/src/check.rs` — not done this sprint, but tracked so Phase 5 cache work does not discover it cold.
7. **The `/frontend` "read-only audit" task is strengthened**: confirm (with a FIXME if needed) that the Program→AST pipeline does not silently rely on `program: &Program` downstream via any back-channel (e.g., intern tables, Span reuse). Current annotation-on-AST approach means nothing should, but verification, not assumption.

If conditions 1–5 are met before Wave 1 opens, this sprint lands clean and fixes the 3 multi-sig JIT failures as a direct byproduct of the convergence. Conditions 6–7 are cleanup hygiene and should not block sprint advancement, but must not be dropped.


## Design Review (Phase 3a)

**Reviewer**: `/arch`
**Date**: 2026-04-17
**Verdict**: **APPROVED with conditions** — the three design docs are mutually coherent on the Wave 0 contract, the Step 2a signature, and the Step 2b deletion list. The three cross-skill findings `/int` flagged have clean resolutions within existing principles (see §2). Before Phase 3b opens, two small corrections are needed: (a) the `CompilationResult` shape change must be added as an explicit `/backend` deliverable (not left as a vague §9.3 risk in `/int`'s doc), and (b) `interfaces.md` must drop its stale `CheckResult` boundary-type references.

### 1. Cross-Doc Coherence

The three docs agree on the Wave 0 contract. Specifically:

- **`defined_symbols()` filter** — `/typecheck` §9.5, `/backend` §2.5 / §16.3, and `/int` §2 all specify the same predicate: `ast.is_some() AND kind is not Overloaded AND kind is not UserFn { constrained_fn: Some(_) }`. The iterator return type `(&Symbol, &ModuleEntry)` in `/typecheck` §9.5 is consistent with `/int`'s `Vec<Symbol> = table_ref.defined_symbols().collect()` (§5) and `/backend`'s `t.defined_symbols().collect()` (§16.3). **Aligned.**
- **`ast: Some(_)` categories** — `/typecheck` §9.1's table (7 rows) is the authoritative list. `/backend` §2.3 / §16.1 cites it as the "authoritative table" and §16.4 treats `ast: None` as a codegen error rather than a silent skip. `/int` §2 defers to it. **Aligned.**
- **Ownership sequencing for `finalize_module` deletions** — `/typecheck` §9.4 explicitly says the mono and default-method inlining loops (`src/worker.rs:1245–1258`) become dead **after Wave 0** but "MUST remain in place during Wave 0 to preserve the 1590/22 baseline — Wave 0 is additive to the symbol table only". `/int` §7 items 10–13 (Step 2b) delete them. `/int` §6 says `worker.rs:1229–1238` (`__expr` special case) "goes away entirely" in Step 2b.3. **No overlap — Wave 0 writes, Step 2a/2b deletes.**
- **REPL `__expr` path** — `/typecheck` §9.1 row 7 and §9.4's caveat on batch-vs-REPL, `/backend` §16.3, and `/int` §6 all align: typecheck registers `__expr` as a `ModuleEntry::Def` with `ast: Some(_)` via the same path as any other defn; `compile_to_module` picks it up via `defined_symbols()`. **Aligned.**

One minor mismatch worth flagging but not blocking: `/int` §3 describes `JitCompilationEnv` as "a thin `JitCompilationEnv<'a>` (lives in `cranelisp-backend`, not in `src/`)" but `/backend`'s doc never mentions it — §12 (`ObjectCompilationEnv`) is the live env, and `resolve_got` returns `None`. See Finding 2 below for the arbitration; `/backend` must add a §12.1 subsection acknowledging the JIT-side GOT base resolution.

### 2. Arbitration of /int Findings

**Finding 1 — `CompilationResult` shape**: `/int`'s priority-worker pseudocode (§5) reads `result.artifacts.get(name)` for per-symbol CLIF IR / disasm / code_size. Today `CompilationResult` returns one flattened triple. `/int` §9.3 flags this as a `/backend` coordination concern.

**Decision**: Extend `CompilationResult` with `pub artifacts: HashMap<Symbol, FunctionArtifacts>` where `FunctionArtifacts { clif_ir: String, disasm: Option<String>, code_size: usize }`. Introspection is populated by the caller reading from this map and writing into the separate `introspection: DashMap<FQSymbol, Introspection>` map per `pipeline-v4.md` §9.6. This keeps §9.6's separation intact (Introspection is a display-only, caller-owned map) while giving callers a clean per-symbol artifact bundle from one codegen call.

**Rationale**: The prior-ring pattern (codegen produces CLIF/disasm as a side-output; `Introspection` receives it) is preserved. A symbol-table-sourced mechanism would defeat the point — those artifacts don't exist until codegen runs. A flat triple keyed by "whatever was compiled" would have worked when `compile_to_module` compiled one program; once callers pass `names: &[Symbol]`, keying by Symbol is the only shape that makes sense.

**Who acts**: `/backend` — add `artifacts: HashMap<Symbol, FunctionArtifacts>` to `CompilationResult` as part of Wave 1's signature rewrite. Add a one-paragraph §8.1 "Artifacts by symbol" subsection to `compile-to-module.md` documenting the contract. `/int` updates §5 pseudocode to drop the conditional "(will need extension)" hedge.

**Finding 2 — `JitCompilationEnv` location**: `/int` says a `JitCompilationEnv` must live in `cranelisp-backend` (not `src/`) to provide runtime GOT base addresses. Today `ObjectCompilationEnv::resolve_got` returns `None`.

**Decision**: Add `JitCompilationEnv<'a>` in `crates/cranelisp-backend/src/jit/mod.rs` (or a new sibling `src/compilation_env.rs` — `/backend`'s choice). It implements the same `CompilationEnv` trait as `ObjectCompilationEnv` — all methods except `resolve_got` delegate to the shared symbol-table reads; `resolve_got` returns `Some((got_base_ptr, slot))` by looking up `symbol_tables[target_module].got.base_ptr()` (Phase 2) or `ModuleEntry.got` (Phase 3 G7). `compile_to_module` internally selects the right env based on the `Module` implementor — a runtime type check on `M` is undesirable, so the selection happens via a separate Phase 2 shape: the caller tells the backend which env to build by calling `compile_to_module_jit(...)` vs `compile_to_module_object(...)` as two thin wrappers over a shared core, OR `compile_to_module` takes an `env: &dyn CompilationEnv` parameter. **Preferred: thin wrappers**, because it preserves the four-parameter PRESCRIPTIVE signature and keeps `compile_to_module` itself module-mode-agnostic. `/backend` may choose either; the public API stays `compile_to_module<M: Module>`.

**Rationale**: This does NOT violate the "one `CompilationEnv`" principle — there was never a principle of "one env"; the principle is "one `compile_to_module`" (pipeline-v4 invariant 15). The env is an internal abstraction that already has one trait with two impls. Principle 6 (complexity budget): a small second env struct that shares the trait is strictly cheaper than adding a mode flag to `ObjectCompilationEnv` (the flag would have to be propagated through every method that emits GOT code) or than materialising the JIT GOT base as a data symbol (the object path's trick) — the JIT path has no linker to resolve data symbols. Principle 1 (decoupling over convenience): the two envs represent two genuinely different mechanisms for materialising a GOT base pointer, not two modes of the same mechanism.

**Who acts**: `/backend` — Wave 1. Add `JitCompilationEnv` to the backend crate. Update §12 of `compile-to-module.md` to document both envs side-by-side. **Phase 2 does not require `ModuleEntry.got` to exist** — `JitCompilationEnv` reads the GOT base from `TypecheckProduct.got.base_ptr()` (today's location) via the symbol-tables DashMap key parallel. Phase 3 G7 moves the GOT onto `SymbolTable` and the two envs collapse into one reading `symbol_tables[target].got` uniformly (§9.1 target). `/int` §3's table is correct as written; the only adjustment is that `/backend` (not `/int`) owns the addition.

**Finding 3 — Platform function discoverability**: Is `symbol_tables[..].get(name).ast` populated for platform functions today, or does Phase 2 require Phase 4a (G8) to land first?

**Verification (read-only)**: `crates/cranelisp-types/src/module.rs:207` defines `PrimitiveKind::PlatformEffect`. `src/worker.rs:315–344` (`collect_jit_setup_for_module`) scans both `ModuleEntry::Def` with `PrimitiveKind::PlatformEffect` AND `ModuleEntry::Import` chains that resolve to a platform-effect def, extracting `jit_name` + looking up the function pointer in `platform_registry`. **The mechanism exists today and is used by both the JIT path (via `SessionCompilationEnv`) and the object path (via `ObjectCompilationEnv::resolve_got_module` following Import chains).**

**Decision**: Phase 2 is NOT blocked by Phase 4a / G8. Platform functions are discoverable from `symbol_tables` today. The `collect_jit_setup_for_module` logic (which already handles both `Def` and `Import` cases per the Sprint 50 fix) moves into the backend as part of `JitCompilationEnv`'s responsibility — it walks the module's imports to gather all platform-effect JIT names and function pointers from the `PlatformRegistry` reference it holds. The `PlatformRegistry` remains on `CompilerSession` (DLL lifetime owner) and is passed to `JitCompilationEnv` construction.

**Caveat**: The one open question is whether platform function **pointers** (as opposed to type signatures) live on `ModuleEntry::Def` today or solely in the external `PlatformRegistry`. Per `pipeline-v4.md` §3.4, the target is for platform pointers to live on `ModuleEntry::Def.kind` as `PrimitiveKind::PlatformEffect { fn_ptr, ... }`, eliminating the separate `session.platform` registry. This is Phase 4 / G8 work. **Phase 2 does NOT require that move** — the new `JitCompilationEnv` can hold a `&PlatformRegistry` for now and later lose it when G8 lands. This is a Phase-2→Phase-4 bridge that `/backend`'s doc must acknowledge (§12) so the G8 transition is a refactor, not a rewrite. Pattern matches the Phase-2→Phase-3 bridge for `Code` (§16.7).

**Who acts**: `/backend` — document the platform-registry coupling of `JitCompilationEnv` as a Phase-2→Phase-4 bridge in §12 of `compile-to-module.md`. `/platform` — sprint task §stays unchanged; the audit verifies the bridge works and flags any gap. **Phase 2 is not blocked.**

### 3. Principle 8 Check (No Interim Architecture)

- **`Arc<JITModule>` in `Code`** (`/int` §4, §9.6): This is NOT interim. `/int` §9.6 correctly observes the `Arc` stays valid when `Code` moves onto `ModuleEntry::Def` in Phase 3 G6 (multiple entries sharing one finalised JIT module is a legitimate data sharing pattern, not a workaround). Approved.
- **`JitCompilationEnv` holding `&PlatformRegistry`**: Phase-2→Phase-4 bridge (see Finding 3). Not interim — the env type itself survives; only the field disappears when G8 lands.
- **`CodegenProduct` as the temporary home for `Code`** (`/int` §4, `/backend` §16.7): Phase-2→Phase-3 bridge. Not interim — G6 is a mechanical field relocation, not a rewrite.
- **Dual env types** (`ObjectCompilationEnv` + `JitCompilationEnv`): Not interim — they represent genuinely different mechanisms (see Finding 2). Phase 3 G7 may collapse them when GOT moves onto `SymbolTable`, but both paths still need to distinguish runtime pointer vs symbolic reference emission — so the trait stays, and the two impls stay.

**Clean.** Nothing in the three docs builds a throwaway.

### 4. Principle 13 Check (`interfaces.md` Coherence)

`design/arch/interfaces.md` currently:
- Defines `CheckResult` (§609–668) as the boundary type between typecheck and backend. **Stale after Sprint 55** — Phase 1 eliminated it as a boundary type; annotations are on AST nodes, mono/default bodies are on symbol-table entries.
- References `CheckResult` in typecheck stage signatures (line 1332).
- Has no `compile_to_module` signature or `CompilationResult` definition.

**`interfaces.md` needs refresh.** The `compile_to_module` signature lives in `crates/cranelisp-backend/src/lib.rs`, not `interfaces.md`, per Phase 1 convention (interfaces.md covers cross-crate types, not backend-public API). But the stale `CheckResult` entry is a Principle 13 violation — an auditable design book must not enshrine a deleted boundary type.

**`/arch` will update `interfaces.md` in Wave 0** (before `/backend` opens Step 2a): mark §CheckResult as REMOVED with a pointer to `ast-annotation.md` for the replacement pattern; remove the reference on line 1332; confirm no `compile_to_module` entry is needed (the backend's public API is documented in `compile-to-module.md`, not `interfaces.md`).

Add a new Key Decision 22 to `design/arch/CLAUDE.md`:

> **22. `SymbolTable::defined_symbols()` is the shared codegen-compilable predicate.** Both the backend's `compile_to_module` and the integration layer's priority worker enumerate codegen targets via this iterator. The filter is `ast.is_some() AND kind is not Overloaded AND kind is not UserFn { constrained_fn: Some(_) }`. Living on `SymbolTable` in `cranelisp-types`, it is the single source of truth for "what does codegen compile?" — any call site re-inventing this predicate is an architectural regression. Added Sprint 56 to avoid the duplicate filter that would otherwise arise between the backend's symbol-table scan and the worker's own enumeration.

### 5. Conditions for Phase 3b

The following MUST be true before skill plans are finalized (Phase 3b opens):

1. **`/backend` adds `CompilationResult.artifacts: HashMap<Symbol, FunctionArtifacts>`** to the Wave 1 deliverable and updates `compile-to-module.md` §8 accordingly (Finding 1 resolution). `/int` references this as the source for per-symbol introspection population, matching §5 of its doc.
2. **`/backend` adds `JitCompilationEnv` to `compile-to-module.md` §12** side-by-side with `ObjectCompilationEnv`, and documents the `&PlatformRegistry` field as a Phase-2→Phase-4 bridge (Finding 2 and Finding 3 resolution).
3. **`/arch` refreshes `design/arch/interfaces.md`** to remove stale `CheckResult` boundary-type entries and records Decision 22 (`defined_symbols()` as shared predicate) in `design/arch/CLAUDE.md` (Principle 13 resolution). Non-blocking for `/typecheck` Wave 0 start, but MUST land before `/backend` Wave 1 opens.
4. **`/int` softens §5's `result.artifacts.get(name)` pseudocode** to match the new `CompilationResult` shape once `/backend` confirms it (mechanical edit to `phase2-codegen-convergence.md` §5 and §9.3).

Conditions 1–2 are `/backend` Wave 1 deliverables that must be written into the doc BEFORE implementation opens. Condition 3 is `/arch` own-hand work, landing in the same Wave 0 window as `/typecheck`'s AST materialisation. Condition 4 is `/int`'s follow-up once §8 of `compile-to-module.md` is updated.

**None of these are implementation work.** They are doc-level clarifications required to close the three cross-skill questions. The underlying Phase 2 scope (`/arch` Architecture Review §1–§6 verdict) stands unchanged: sprint approved, Wave 0 is the `/typecheck` prerequisite, Step 2a is the `/backend` signature flip, Step 2b is the `/int` deletion pass.

With conditions 1–4 met, Phase 3b opens cleanly and the three skill plans finalise against a stable, mutually consistent contract.

### Phase 3a Addendum (after iterative review)

Following deeper discussion with the user on Principle 11 coherence, the Phase 3a arbitration evolved:

- **Finding 1 (`CompilationResult.artifacts`)**: stands. `artifacts: HashMap<Symbol, FunctionArtifacts>` added to `CompilationResult` for Introspection.
- **Finding 2 (`JitCompilationEnv` location)**: **WITHDRAWN**. No env type exists in the final design. Mode differences are entirely a Module property resolved at finalize time. See Decision 23.
- **Finding 3 (platform function discoverability)**: stands — platform fns discoverable on `ModuleEntry::Def` with `PrimitiveKind::PlatformEffect`.
- **Wave 0 expansion**: G7 (GOT onto SymbolTable) pulled forward from Phase 3 — see `design/typecheck/ast-annotation.md` §9.8.
- **Final `compile_to_module` signature**: 4 params (`module_path, names, symbol_tables, module`). No env. No mode. No wrappers. No `CodegenTarget`.

The two-wrapper / env-type proposal from the original Phase 3a review is retracted in favour of uniform `global_value` GOT emission with Module-level mode resolution. See Decision 23 in `design/arch/CLAUDE.md` for the full rationale.


## Skill Plans

### /backend
**Task**: Change `compile_to_module` signature to `(module_path, names, symbol_tables, module)` — 4 params, no env. Read bodies from `ModuleEntry::Def.ast`. Delete `expand_multi_sig_defn` (redundant once Wave 0 mangles variant entries carry `ast`). Delete `CompilationEnv` trait and `ObjectCompilationEnv` struct. Emit uniform `global_value` + `Linkage::Import` data symbols for GOT references. Add `FunctionArtifacts` map to `CompilationResult`.
**Design doc**: `design/backend/compile-to-module.md` — LANDED. §2.1 PRESCRIPTIVE at 4 params; §12 (GOT Reference Emission) describes the uniform strategy; §2.4 notes "no internal fork"; §16 migration + deletion list updated. Every reference to withdrawn types (`CompilationEnv`, `ObjectCompilationEnv`, `JitCompilationEnv`, wrappers, `CodegenTarget`) is either historical or in a deletion list.
**Approach**:
1. Enumerate defns to compile: loop over `names`; for each, `symbol_tables[module_path].get(name)` → require `ast: Some(defn)`; return `CodegenError` naming the symbol if `None`.
2. Remove multi-sig expansion: `expand_multi_sig_defn` (`lib.rs:379-436`) deleted; mangled entries already carry single-variant `Defn` bodies after Wave 0.
3. Remove the inline `constrained_fn_names` scan (`lib.rs:95-109`) — `defined_symbols()` pre-filters.
4. GOT reference emission (§12): on first reference to a foreign module's GOT, `module.declare_data("__cranelisp_got_{name}", Linkage::Import, ...)`; emit `global_value` + load at each call site. Identical CLIF for JIT and Object.
5. Remove `CompilationEnv`-trait dispatch code inside `FnCompiler` / `CompileContext`: replace `env.resolve_got_module(name)` with a direct `symbol_tables` lookup helper + GOT-slot read from `ModuleEntry::Def.got_slot`.
6. Extend `CompilationResult` with `artifacts: HashMap<Symbol, FunctionArtifacts>` populated in the same FnCompiler pass that emits the function (single-pass capture).
7. Caller contract: JIT caller registers `JITBuilder::symbol_lookup_fn` BEFORE creating the `JITModule` to resolve `__cranelisp_got_*` → `symbol_tables[m].got.base_ptr()`. Object caller does nothing extra (relocations are default).
**Design refs**: `design/backend/compile-to-module.md` §2.1, §2.4, §12, §16; `design/arch/pipeline-v4.md` §9.1, §9.3, §9.6; `design/arch/CLAUDE.md` Principle 11, Decisions 22, 23; `design/backend/ast-sourced-codegen.md` (Phase 1 groundwork).
**Acceptance**: `compile_to_module(path, names, symbol_tables, module)` in place; 3 multi-sig JIT tests pass (`sketch_multi_sig_type_based_dispatch`, `sketch_multi_sig_different_arities`, `sketch_repl_multi_sig_different_arities`); no `CompilationEnv` trait / `ObjectCompilationEnv` / `expand_multi_sig_defn` in the source tree; `cargo clippy` clean.

### /typecheck
**Task (Wave 0, prerequisite)**: Pre-materialise `ast: Some(...)` on mangled multi-sig variant entries and mono specialisation entries. Expose `SymbolTable::defined_symbols()` with the shared codegen filter. **Pull G7 forward**: move `got: GotTable` onto `SymbolTable`.
**Design doc**: `design/typecheck/ast-annotation.md` §9 (Sprint 56 Wave 0) — LANDED. Four substeps: §9.3 mangled multi-sig `ast`; §9.4 mono `ast`; §9.5 `defined_symbols()`; §9.8 G7 pull-forward. Plus `FIXME(/typecheck)` on `crates/cranelisp-types/src/check.rs` — LANDED.
**Approach**:
1. **Mangled multi-sig** (`register_mangled_variants` at `program.rs:1583`): reuse the already-annotated `ast` from the internal-name entry (`foo__v0`) produced by `check_form_body_multi_sig`; clone onto mangled entry with `defn.name` renamed to the mangled form. Expr nodes unchanged.
2. **Mono specialisations** (`register_mono_entry`): at the `monomorphise_call` insertion point (batch and REPL both flow through it), clone `mono.defn` (already fully annotated by `annotate_defn_from_maps` + `apply_subst_to_defn` at `traits.rs:1140–1145`) onto a new `ModuleEntry::Def` with `ast: Some(defn.clone())`.
3. **`SymbolTable::defined_symbols()`** (new iterator on `SymbolTable` in `crates/cranelisp-types/src/module.rs`): filter `ast.is_some() AND kind != Overloaded AND kind != UserFn{constrained_fn: Some(_)}`. Consumed by both priority-worker (preparing `names`) and backend's internal loop.
4. **G7 pull-forward**: add `pub got: GotTable` field to `SymbolTable` with `#[serde(skip, default)]`. Move `GotTable` type from `cranelisp-backend` into `cranelisp-types` (it's data-only — `Box<[AtomicPtr<u8>; GOT_TABLE_SIZE]>`). Initialize in `SymbolTable::new()`. Delete `got` field from `TypecheckProduct` in `src/session_v4.rs` (coordinate with `/int` — `TypecheckProduct` may collapse entirely).

Wave 0 is strictly additive — `finalize_module`'s inlining loops (`src/worker.rs:1245–1258`) remain untouched to preserve the baseline; `/int` deletes them in Step 2a.
**Design refs**: `design/typecheck/ast-annotation.md` §9.3–§9.5, §9.8; `design/arch/pipeline-v4.md` §9.1; `design/arch/pipeline-v4-roadmap.md` §Phase 3 Step 3a (G7); Decisions 21, 22 in `design/arch/CLAUDE.md`.
**Acceptance**: Wave 0 lands green (1590/22 baseline). `defined_symbols()` yields exactly the set of names that need compiling. `got: GotTable` on `SymbolTable`; `TypecheckProduct.got` deleted; JIT path can read GOT base from `symbol_tables[m].got.base_ptr()`.

### /int
**Task**: Delete `codegen_module_symbols`, `compile_regular_defns`, `compile_and_register_defn_shared`, `pre_register_got_slots_in_tc`, and `SessionCompilationEnv` from `src/worker.rs`. Replace priority-worker dispatch with a direct `compile_to_module` call using a per-worker `JITModule`. Ensure REPL `__expr` synthetic flows as a name in the `names` list. Delete `TypecheckProduct.got` (coordinate with `/typecheck` Wave 0 §9.8) — `TypecheckProduct` likely collapses entirely.
**Design doc**: `design/int/phase2-codegen-convergence.md` — LANDED. §3 env-replacement table (all rows `DELETED`); §4 `JITModule` lifetime; §5 priority-worker pseudocode; §6 REPL `__expr`; §7 deletion list; §8 migration order (2b.1–2b.6); §9 risks.
**Approach**:
1. Extend priority worker's `ProcessResult::Complete` branch (`src/worker.rs:2878` / `:3037`): collect `names` via `symbol_tables[module_path].defined_symbols()`.
2. Construct a per-compile-unit `JITModule` by building a `JITBuilder` with (a) intrinsic symbol registrations (existing pattern), (b) platform function symbol pointers from `PlatformRegistry` — registered directly via `JITBuilder::symbol`, (c) a `symbol_lookup_fn` closure capturing `symbol_tables` that resolves `__cranelisp_got_{name}` to `symbol_tables[name].got.base_ptr()`.
3. Call `cranelisp_backend::compile_to_module(module_path, &names, &symbol_tables, &mut jit_module)?; jit_module.finalize_definitions()?;`.
4. For each `(name, func_id)` in `result.func_ids`: extract function pointer via `jit_module.get_finalized_function`; register in `CodegenProduct` (Phase 2 bridge — Phase 3 G6 moves `Code` onto `ModuleEntry::Def`); atomically store the pointer into the GOT slot on `symbol_tables[module_path].got`.
5. For each `(name, artifacts)` in `result.artifacts`: insert into `SharedState.introspection` keyed by `FQSymbol { module: module_path, symbol: name }`.
6. Notify scheduler: `notify_inmem_codegen_complete` per name; `is_last` on the final one.
7. Delete the `finalize_module` REPL `__expr` special case (`src/worker.rs:1229-1238`) — `__expr` is just another `names` element after Wave 0.
8. Delete `finalize_module`'s mono-inlining (`:1254-1258`), default-method-inlining (`:1245-1247`), and post-pass enrichment (`:1260-1277`) loops — all made redundant by Wave 0.
9. Update the `session_v4.rs:1457` call-site (was `codegen_module_symbols(...)`) to the new inline block.

Staged migration (per §8): 2b.1 worker inlines `compile_to_module` call → 2b.2 delete `codegen_module_symbols` → 2b.3 delete REPL `__expr` special case → 2b.4 delete `compile_regular_defns` + helpers → 2b.5 delete `SessionCompilationEnv` → 2b.6 delete `TypecheckProduct.got` (companion to `/typecheck` §9.8). Each sub-step must build green.
**Design refs**: `design/int/phase2-codegen-convergence.md` §§3–9; `design/arch/pipeline-v4.md` §9.3, §9.4, §9.6; `design/backend/compile-to-module.md` §12 (caller contract); `design/typecheck/ast-annotation.md` §9.8 (G7 coordination); `design/arch/CLAUDE.md` Principle 11, Decision 23.
**Acceptance**: `codegen_module_symbols`, `compile_regular_defns`, `compile_and_register_defn_shared`, `pre_register_got_slots_in_tc`, `SessionCompilationEnv` all deleted; `TypecheckProduct.got` deleted; one JIT codegen path through `compile_to_module`; REPL eval works end-to-end; introspection (`/sig`, `/clif`, `/disasm`, `/source`) works on a sample defn.

### /frontend
**Task**: Verify (not assume) that the Program→AST pipeline does not silently rely on `program: &Program` downstream via any back-channel (e.g., intern tables, Span reuse, shared allocations). Phase 2's `names: &[Symbol]` signature removes `program` from the codegen input — frontend must confirm no hidden dependency breaks.
**Approach**: Read-only audit; file FIXME if any back-channel found; report clean if none.
**Acceptance**: Audit complete; any findings reported as FIXMEs; no blockers surfaced.

### /platform
**Task**: Confirm platform registry interactions still work through the new codegen path (platform function resolution at compile time has been via `SessionCompilationEnv` / `PlatformRegistry`). Validate the 5 failing v4_platform tests have a diagnosis (not necessarily a fix this sprint).
**Approach**: Trace a platform call site from `compile_to_module` through to the intrinsic declaration; document any integration points that must survive Step 2b.
**Acceptance**: Platform call resolution path documented; v4_platform failures triaged to one of {Phase 2 target, deferred, regression needing fix}.

### /qa
**Task**: Derive INTEGRATION tests (in `tests/` at the project root) from the finalized design docs for Step 2a / Step 2b. Focus on multi-sig JIT coverage, REPL expression eval via unified `compile_to_module`, cross-module calls, and risk-targeted tests (GOT slot race, introspection preservation, platform resolution). Write tests in parallel with implementation (spec-first: tests derive from the spec/design docs, not the implementation). **Unit tests are NOT your scope** — the implementing skill writes unit tests inside its own crate (per `memory/feedback_unit_tests_with_dev.md`). Specifically: `/typecheck` writes the 6 Wave 0 unit tests; `/backend` writes the 4 Step 2a unit tests; `/int` writes priority-worker unit tests.
**Design doc**: `tests/plan/ring4.md` Sprint 56 Phase 2 section — LANDED (19 new + 3 flip-green tests planned).
**Approach**:
1. **Wave 0 unit tests** (6 in `crates/cranelisp-typecheck/src/program.rs` / `crates/cranelisp-types/src/module.rs`): mangled variant carries `ast: Some(_)` with correct mangled `defn.name`; no `Type::Var` leaks in annotations; `Overloaded` base has `ast: None`; mono entry carries annotated `ast` + distinct GOT slot; `defined_symbols()` excludes `Overloaded`/constrained-template/TypeDef/Import; REPL multi-sig path registers mangled entries; GOT `base_ptr()` stable across reads; `#[serde(skip)]` roundtrip gives fresh null GOT.
2. **Step 2a backend tests** (4 in `crates/cranelisp-backend/`): call `compile_to_module(path, &names, &symbol_tables, &mut module)` directly; assert `CodegenError` when a name's `ast: None`; assert backend never calls `expand_multi_sig_defn` (e.g., by removing it entirely and relying on compile success); assert backend never re-filters constrained templates.
3. **Step 2b integration tests** (5 new + 3 flip-green in `tests/`): the 3 multi-sig JIT tests flip green; REPL `(+ 1 2)` compiles via unified path returning 3 (exercises `__expr` as a name); batch `.cl` with regular + multi-sig defns compiles and runs; cross-module call to another module's multi-sig function works; regression guard — all 1590 passing tests remain green.
4. **Risk-targeted** (4): GOT slot race (two workers on same module — verify scheduler prevents or test the prevention); introspection preservation (`/sig`, `/clif`, `/disasm`, `/source` still work); platform function resolution through unified path (depends on `/platform` triage); `/list` filter still works after `defined_symbols()` rewire.
5. **Must-not-regress gate**: full 1590 baseline categorised by ring + crate must stay green; all examples compile + run; stdlib + exemplar load cleanly.

Tests committed before/during implementation — failing tests that expose spec-implementation gaps are expected and correct (per `feedback_failing_not_ignored.md`); they become pass-tests as implementation waves complete. NO `#[ignore]` for spec violations.
**Design refs**: `tests/plan/ring4.md` Sprint 56 Phase 2 section; `design/typecheck/ast-annotation.md` §9.7 (test plan highlights); `design/backend/compile-to-module.md` §15 (acceptance); `design/int/phase2-codegen-convergence.md` §10.
**Acceptance**: Phase 2 test cases in ring 4 plan; new tests committed; the 3 deferred multi-sig tests flip green by sprint close; no new failures beyond the 19 acceptable baseline (22 - 3 = 19 post-sprint).

### /review
**Task**: Review all new code in the implementation waves. Independent inspection — not delegated synthesis.
**Approach**: Review after each implementation wave; findings classified B/I/S; blockers gate sprint close.
**Acceptance**: All B+I findings resolved or explicitly deferred with user sign-off.

### /spec
**Task**: Review spec to confirm no spec changes are implied by Phase 2 (this is internal pipeline restructuring). Scan for prior-ring coverage gaps/negative coverage gaps found during Phase 1 audit and file FIXME(/qa) for any found.
**Approach**: Audit `repl/spec.md` and `spec/*.md` for `[R0 S*]` / `[R1 S*]` / `[R2 S*]` / `[R3 S*]` annotations (completed rings without test coverage).
**Acceptance**: Prior-ring coverage gaps surfaced to `/qa`.

### /stdlib
**Task**: Early-engagement planning. Confirm stdlib still compiles via the new codegen path at sprint close. No stdlib code changes expected.
**Approach**: Run stdlib integration tests at close; file FIXME(/backend) if any regression.
**Acceptance**: Stdlib compiles and loads cleanly.

### /examples
**Task**: Early-engagement planning. Ensure all existing `examples/*.cl` still compile via the new codegen path at sprint close.
**Approach**: Run examples suite at close.
**Acceptance**: All examples compile and run.

### /port
**Task**: Validate exemplar project (Sudoku solver) still compiles and runs via the new codegen path.
**Approach**: Run exemplar at close.
**Acceptance**: Exemplar demo plays cleanly.

### /docs
**Task**: Update `user/` references if any user-visible compile behavior changes (unlikely — this is pipeline restructuring).
**Approach**: Audit at close.
**Acceptance**: No stale references.

### /repl
**Task**: Create Sprint 56 demo (`repl/demos/ring4n.demo` — next letter after Sprint 55's ring4m). Showcase any REPL improvements from Phase 2 convergence (e.g., multi-sig JIT working correctly).
**Approach**: Build demo after implementation settles; verify all prior demos still play cleanly.
**Acceptance**: Sprint demo plays cleanly; all prior demos play cleanly.

## Waves

Phase 3 (design) is COMPLETE — all design docs, `/arch` interfaces.md, Decision 23, and `/qa` test plan are in place. Implementation waves open now. Dependencies drive the order: Wave 0 (`/typecheck`) must land before Wave 1 (`/backend`) can begin; Wave 2 (`/int`) depends on both. `/qa` writes tests in parallel with each implementation wave so failures surface early. `/review` runs after each code wave.

### Wave 0 — Symbol table groundwork (`/typecheck`)

Prerequisite for Step 2a. Must land green (1590/22 preserved) before Wave 1 opens.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | Pre-materialise mangled multi-sig variant `ast` (§9.3) | pending | Reuse internal-name annotated `ast`; rename `defn.name`. |
| /typecheck | Pre-materialise mono specialisation `ast` (§9.4) | pending | Clone annotated `mono.defn` at `monomorphise_call` site. |
| /typecheck | Expose `SymbolTable::defined_symbols()` (§9.5) | pending | Shared filter predicate. Decision 22. |
| /typecheck | Pull G7 forward — `got: GotTable` on `SymbolTable` (§9.8) | pending | Move `GotTable` type into `cranelisp-types`; `#[serde(skip, default)]`; `SymbolTable::new()` initialises. Coordinate with `/int` on `TypecheckProduct.got` deletion. |
| /typecheck | 6 Wave 0 unit tests (owning skill writes unit tests) | pending | `#[cfg(test)] mod tests` in `cranelisp-typecheck` / `cranelisp-types`: mangled/mono `ast` presence + `defined_symbols()` filter correctness + `got: GotTable` presence/serde. Written alongside the implementation, not delegated to `/qa`. |
| /review | Review Wave 0 code | pending | After build-green. Blockers gate Wave 1 open. Absence of unit tests = Blocker. |

**Gate criterion**: tests at 1590/22 (baseline); `defined_symbols()` exported and consumed in at least one call site; `TypecheckProduct.got` deleted; `cargo clippy` clean.

### Wave 1 — Backend signature change + unified GOT (`/backend`)

Depends on Wave 0. Delivers Step 2a.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /backend | Change `compile_to_module` signature to 4-param `(path, names, symbol_tables, module)` | pending | Read bodies from `ModuleEntry::Def.ast`. |
| /backend | Delete `expand_multi_sig_defn`; remove inline `constrained_fn_names` scan | pending | Wave 0 mangled entries + `defined_symbols()` replace both. |
| /backend | Delete `CompilationEnv` trait + `ObjectCompilationEnv` struct | pending | Replace with direct `symbol_tables` helpers inside `FnCompiler`. |
| /backend | Implement uniform GOT emission (§12) | pending | `global_value` against `Linkage::Import __cranelisp_got_{m}`. |
| /backend | Extend `CompilationResult` with `artifacts: HashMap<Symbol, FunctionArtifacts>` | pending | Single-pass capture during FnCompiler emission. |
| /backend | Update object-mode callers (nice worker, cache paths) to new signature | pending | JIT callers updated in Wave 2. |
| /backend | 4 Step 2a backend unit tests | pending | `#[cfg(test)] mod tests` in `cranelisp-backend`: direct `compile_to_module` invocation + negative `ast: None` case + multi-sig expansion removed + constrained-template skip. Written alongside the implementation. |
| /review | Review Wave 1 code | pending | After build-green. Blockers gate Wave 2 open. |

**Gate criterion**: all object-mode call sites migrated; JIT path still works via `codegen_module_symbols` temporarily (Wave 2 deletes it); `CompilationEnv`/env types gone from source tree; 1590/22 baseline preserved; `cargo clippy` clean.

### Wave 2 — Delete JIT sweep, unify priority worker (`/int`)

Depends on Wave 1. Delivers Step 2b. Fixes the 3 multi-sig JIT tests.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | 2b.1 — priority worker inlines `compile_to_module` call with `symbol_lookup_fn` | pending | Replace `codegen_module_symbols` call site in worker + `session_v4.rs:1457`. |
| /int | 2b.2 — delete `codegen_module_symbols` | pending | After all callers migrated. |
| /int | 2b.3 — delete `finalize_module` REPL `__expr` special case (`worker.rs:1229-1238`) | pending | `__expr` is just a name in `names`. |
| /int | 2b.3b — delete `finalize_module` mono / default-method / post-pass inlining loops | pending | Wave 0 made these redundant. |
| /int | 2b.4 — delete `compile_regular_defns`, `compile_and_register_defn_shared`, `pre_register_got_slots_in_tc` | pending | All supporting helpers. |
| /int | 2b.5 — delete `SessionCompilationEnv` (and its methods) | pending | Pair with `/backend`'s trait deletion. |
| /int | 2b.6 — delete `TypecheckProduct.got`; collapse `TypecheckProduct` if empty | pending | Coordinated with `/typecheck` §9.8. |
| /qa | 5 Step 2b integration tests + 3 flip-green in `tests/` | pending | REPL `(+ 1 2)`, batch multi-sig, cross-module multi-sig, introspection, regression guard. Integration-scope only — priority worker unit tests live in `/int`'s crate. |
| /int | Priority-worker unit tests in `src/worker.rs` | pending | `#[cfg(test)] mod tests` covering name-list preparation + `symbol_lookup_fn` wiring + artifact routing to `Introspection`. Written alongside 2b.1. |
| /platform | Verify platform functions resolve through unified path | pending | Register platform symbol pointers on `JITBuilder::symbol` in worker. Triage 5 `v4_platform` failures. |
| /review | Review Wave 2 code | pending | After build-green. Blockers gate showcase wave. |

**Gate criterion**: all 6 deletions done; priority worker + REPL + batch + object paths all go through `compile_to_module`; 3 multi-sig JIT tests pass; no regression below 19 (22 baseline - 3 fixed); `cargo clippy` clean.

### Wave 3 — Showcase (user-proxy skills)

Depends on Wave 2. Gates sprint close.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /frontend | Read-only audit: no hidden `program: &Program` back-channel | pending | Can run anytime; fast. Report clean or file FIXMEs. |
| /spec | Scan completed-ring `[R0..R3 Sx]` coverage gaps | pending | Can run anytime; file FIXME(/qa) for any found. |
| /stdlib | Run stdlib integration tests | pending | After Wave 2 ships. |
| /examples | Run all `examples/*.cl` | pending | After Wave 2 ships. |
| /port | Run exemplar project (Sudoku solver) | pending | After Wave 2 ships. |
| /docs | Audit `user/` for stale references | pending | Low-burden — pipeline restructuring has no user-visible surface. |
| /repl | Create `repl/demos/ring4n.demo` showcasing Phase 2 deliverables | pending | After Wave 2 ships. Play all prior demos cleanly. |
| /qa | Final spec-surface coverage audit | pending | Close-time gate per `/sprint` step 22. |

**Gate criterion (sprint close)**: all Phase 5b items in the close checklist met; new demo plays cleanly; prior demos regression-free.

### Cross-wave notes

- **Parallelism**: `/frontend` and `/spec` can run any time (read-only). `/qa` writes tests in parallel with each implementation wave.
- **`/review` is invoked after each code-producing wave** — not batched at the end.
- **Tests are written spec-first**: failing-against-spec tests are committed un-ignored; implementation passes must close them within the sprint (no deferrals — per `feedback_failing_not_ignored.md` and `feedback_no_premature_perf.md`).
- **Build must be green after each sub-step**. If a step breaks the build, fix before proceeding to the next sub-step.

## Notes

- Sprint 55 closed 2026-04-17 with 1589/22/14. Current baseline: 1590 passed / 22 failed. Any new failures are regressions.
- Phase 1 deferred review findings (I1/I4/I5/S1/S2/S5) should be revisited during Phase 2 — some may naturally dissolve when codegen paths converge.
- The design doc `compile-to-module.md` §2.1 is PRESCRIPTIVE with 5 parameters; after Sprint 55 it's already at 4 parameters. Phase 2 moves to 4 parameters with `names` replacing `program`. The doc needs an authoritative update.

## Outcome

(Filled when sprint closes.)
