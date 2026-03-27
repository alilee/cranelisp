# Sprint 36: Pipeline v3 Step 9 — REPL Migration to compile_unit

**Status**: COMPLETE
**Ring**: — (structural)
**Goal**: REPL `eval` calls `compile_unit` instead of its own parallel pipeline. The REPL eval chain (~500 lines of interception logic) is replaced by `process_commands` → `compile_unit` → display.

## Scope

### Step 9: Refactor REPL to use compile_unit

This is the **highest-risk step** in the v3 migration. The REPL currently has its own eval pipeline that duplicates `compile_unit`'s stages (parse, defmacro interception, macro expansion, import handling, platform handling, AST build, typecheck, codegen). After this sprint, the REPL routes all compilation through `compile_unit`.

**What compile_unit already handles** (no REPL-specific code needed):
- defmacro interception (`process_forms_sequentially` → `process_single_form`)
- Import resolution (`extract_module_declarations` + `load_dependencies` + `register_imports`)
- Platform DLL loading (`extract_module_declarations` + stage 2f)
- Macro expansion + begin flattening
- Bind chain analysis
- Typecheck + codegen

**What the REPL must still handle** (outside compile_unit):
1. **Slash commands** — intercepted before compilation (already in REPL)
2. **Blank/comment detection** — skip empty input
3. **Bare symbol introspection** — typing `Num`, `+`, `if` shows info instead of erroring. This is REPL-specific display behavior, not compilation.
4. **Type annotation expressions** — `:Int expr` syntax. This is REPL-specific input parsing.
5. **TC snapshot/restore** — error recovery around compilation
6. **DefCodegen storage** — sexp/source for `/source`, `/sexp` commands. REPL-specific metadata.
7. **Session persistence** — `save_current_module()` after each definition

**New REPL eval flow**:
```
eval(source) →
  1. Skip blank/comment
  2. Parse to sexps
  3. TC snapshot
  4. Check bare symbol introspection → return early if match
  5. Check annotation expression → handle separately
  6. Call compile_unit(session, source, &repl_ctx)
  7. Codegen: push to inmem_queue + flush_inmem_queue
  8. Store DefCodegen metadata (sexp, source)
  9. Save session persistence
  10. On error: TC restore
```

**Key change**: Steps 6-7 replace the current `eval_sexp` → `eval_flattened_forms` → `eval_defmacro`/`eval_import`/`eval_platform`/`compile_and_execute` chain.

**Functions to delete from REPL**:
- `eval_sexp` — replaced by compile_unit
- `eval_flattened_forms` — replaced by compile_unit's process_forms_sequentially
- `eval_defmacro` — replaced by compile_unit's process_single_form
- `eval_import` — replaced by compile_unit's extract_module_declarations + load_dependencies
- `eval_platform` — replaced by compile_unit's stage 2f
- `compile_and_execute` (REPL version) — replaced by codegen_and_execute

**Functions to keep**:
- `eval` — outer entry point, restructured
- `eval_annotation_expr` — REPL-specific `:Type expr` handling
- `check_bare_symbol_introspection` — REPL-specific display

**Challenges**:
1. `compile_unit` takes a source `&str` and parses it internally. But the REPL's `eval` already parses to check for annotations and bare symbols. Either: (a) pass the pre-parsed sexps to compile_unit via a new entry point, or (b) let compile_unit re-parse (wasteful but simple).
2. `compile_unit` works on a module (`ctx.module = "user"`). The REPL evaluates in the "user" module with `ModuleStrategy::Additive`.
3. DefCodegen metadata needs the pre-expansion sexp. `compile_unit` returns `CompileUnitResult` which has the post-expansion program. The REPL needs the original sexps for storage. `process_forms_with_originals` on CompilationSession already exists for this.
4. `compile_unit` calls `extract_module_declarations` which separates imports/exports/mods from remaining forms. REPL input that's just an expression (no declarations) should work fine — it goes straight to the remaining forms.

**Verification**: All REPL tests pass. All demo files play cleanly. Slash commands work. Error recovery works. Session persistence works.

## FIXME Debt

No blocking FIXMEs found.

## Architecture Review

Reviewed by `/arch`. This is the critical pipeline unification step — after this, the REPL no longer has a parallel compilation pipeline. The decisions below are ordered by their impact on the implementation.

### Q1: Re-parse vs pre-parsed-sexps entry point — **Decision: (a) Re-parse**

`compile_unit` takes `&str` and parses internally. The REPL also parses to detect annotations (`:Int expr` → two sexps) and bare symbol introspection (`Num`, `if`). The question is whether to avoid double-parsing.

**Decision**: Let `compile_unit` re-parse. Reasons:

1. **Parsing is cheap.** REPL input is a few lines at most. The cost of parsing twice is unmeasurable against compilation and JIT time.
2. **No new entry points.** The roadmap explicitly deleted `compile_unit_from_sexps` as a transitional API (Step 14). Adding it back contradicts the design direction. The whole point of the v3 pipeline is that `compile_unit(&str)` is the ONE entry point.
3. **Separation of concerns.** The REPL's pre-parse is for REPL-specific interception (annotation detection, bare-symbol introspection). `compile_unit`'s parse is for compilation. These are different concerns happening to use the same parser. Merging them couples REPL display logic into the pipeline.
4. **Simplicity.** The REPL calls `parse()` to inspect sexps, then either handles the input itself (annotation, introspection → return early) or passes the original `source: &str` to `compile_unit`. No data threading, no sexp ownership transfer.

The REPL eval flow becomes:
```
eval(source) →
  1. Skip blank/comment (string-level, no parse)
  2. Parse to sexps (REPL's own parse, for interception only)
  3. TC snapshot
  4. Check bare symbol introspection → return early if match
  5. Check annotation expression → handle via build_repl_input_from_sexps path (kept)
  6. compile_unit(session, source, &repl_ctx)  ← re-parses, that's fine
  7. codegen_and_execute(session, &result, &ctx)
  8. Store DefCodegen metadata
  9. Save session persistence
  10. On error: TC restore
```

### Q2: DefCodegen storage — **Decision: (c) Store sexps from REPL's initial parse**

The REPL needs pre-expansion sexps for `/source` and session persistence. `compile_unit` returns only the post-expansion `Vec<TopLevel>` program. Options (a) and (b) both involve modifying pipeline internals to serve a REPL-specific need.

**Decision**: The REPL stores the original sexps from its own parse at step 2, before calling `compile_unit`. After `compile_unit` + `codegen_and_execute` succeed, the REPL writes the stored sexps into `DefCodegen` entries for any definitions in the result program.

Rationale:
- **No pipeline changes.** `CompileUnitResult` stays clean — it carries compilation artifacts, not REPL metadata.
- **Already works.** The current REPL does exactly this: `original_sexp = sexp.clone()` at line 589, stored at line 678-681. The mechanism survives unchanged.
- **Correct semantics.** What the user typed (pre-expansion) is what gets stored. The REPL is the only consumer that cares about pre-expansion forms — batch mode doesn't need them.

Implementation detail: After `compile_unit` returns, the REPL iterates `result.program` to find `TopLevel::Defn` entries and stores the corresponding original sexp from the parse-step sexps. The pairing is positional — the Nth compilable form in the sexps corresponds to the Nth `TopLevel` in the program. For begin-expanded forms that produce multiple TopLevel items from one sexp, fall back to the expanded form (same as current behavior at line 636-640).

### Q3: Annotation expressions — **Decision: REPL handles annotations outside compile_unit**

`:Type expr` parses as two sexps. `compile_unit` passes each sexp through `build_top_level` independently — it would try to compile `:Int` as a bare expression and `42` as a separate expression. Two problems: (a) `:Int` is not a valid expression, and (b) even if it were, the type constraint wouldn't propagate to the value.

**Decision**: The REPL keeps `eval_annotation_expr` and handles annotations entirely before `compile_unit` is called. Annotations are a REPL-specific input syntax (you don't write `:Int 42` in a `.cl` file). The REPL:

1. Parses to sexps
2. Detects annotation prefix (`sexps.len() > 1 && is_annotation_prefix(&sexps[0])`)
3. Calls `build_repl_input_from_sexps` which combines them into `TopLevel::Expr(Expr::Annotate(...))`
4. Typechecks and executes via the existing `eval_annotation_expr` path (direct `tc.check` + `compile_and_execute`)

This is NOT a pipeline violation. Annotations are a REPL experience feature (repl/spec.md), not a language compilation feature. They don't exist in batch mode. Routing them through `compile_unit` would require `compile_unit` to gain REPL-specific sexp-combination logic, which contradicts the separation principle.

**However**: `eval_annotation_expr` currently calls `self.core.tc.check()` and `self.compile_and_execute()` directly — the old REPL pipeline. After this sprint, it should call `codegen_and_execute` (the v2 pipeline's codegen path) instead of the REPL's own `compile_and_execute`. This ensures annotations go through the same codegen path as everything else, even though the parse+typecheck is REPL-specific.

Concretely, `eval_annotation_expr` should become:
```
fn eval_annotation_expr(&mut self, sexps: Vec<Sexp>) -> Result<ReplResult, CranelispError> {
    let input = build_repl_input_from_sexps(&sexps, &mut self.core.expander)?;
    let ctx = self.build_repl_compile_context();
    let check_result = self.core.tc.check(&[input.clone()], &ctx)?;
    // Use codegen_and_execute (v2 path), not compile_and_execute (old REPL path)
    let codegen_result = codegen_and_execute(&mut self.core, &synthetic_unit_result, &ctx)?;
    // ... convert CodegenResult to ReplResult
}
```
This deletes the REPL's `compile_and_execute` while preserving annotation support.

### Q4: Incremental vs big-bang — **Decision: (b) Incremental, but simpler than the roadmap suggests**

The roadmap suggests moving one interception at a time (defmacro, import, platform, introspection). That's overly cautious given what `compile_unit` already handles.

**Decision**: Two sub-steps, not five:

**Sub-step A: Route normal compilation through compile_unit.** Replace the `eval_sexp` → `eval_flattened_forms` → `compile_and_execute` chain with `compile_unit` + `codegen_and_execute`. This captures defmacro, import, platform, macro expansion, begin-flattening, bind-chain analysis, typecheck, and codegen in one move. These are all already working in `compile_unit` — the risk is not in the individual features but in the wiring.

Keep `check_bare_symbol_introspection` and `eval_annotation_expr` as pre-`compile_unit` interceptions. They return early before `compile_unit` is called.

**Verification gate**: All tests pass. All demos play. Slash commands work.

**Sub-step B: Delete dead code.** Remove `eval_sexp`, `eval_flattened_forms`, `eval_defmacro`, `eval_import`, `eval_platform`, and the REPL's `compile_and_execute`. Refactor `eval_annotation_expr` to use `codegen_and_execute` instead of `compile_and_execute`.

**Verification gate**: Same as sub-step A plus `cargo clippy` clean.

This is two waves, not five. The risk is concentrated in sub-step A, and sub-step B is mechanical deletion.

### Roadmap divergence note

The roadmap (Step 9) says to delete `eval_annotation_expr` and `check_bare_symbol_introspection`. This review overrides that — both are REPL experience features that don't belong in the compilation pipeline. The roadmap was written before the annotation and introspection interactions were fully analyzed. The principle is: `compile_unit` handles compilation; the REPL handles REPL-specific input interpretation.

### Architectural invariants to verify

After this sprint, the following must be true:

1. **No REPL-owned typecheck calls** except for annotation expressions (justified above). All defn/expr/typedef/trait compilation goes through `compile_unit` → `tc.check()`.
2. **No REPL-owned codegen calls.** The REPL's `compile_and_execute` / `execute_expr` / `execute_defn` methods are deleted. All codegen goes through `codegen_and_execute`.
3. **No REPL-owned macro compilation.** `eval_defmacro` is deleted. Macros go through `compile_unit` → `process_single_form` → `compile_and_register_macro`.
4. **No REPL-owned import handling.** `eval_import` is deleted. Imports go through `compile_unit` → `extract_module_declarations` → `load_dependencies`.
5. **No REPL-owned platform loading.** `eval_platform` is deleted. Platforms go through `compile_unit` → stage 2f.
6. **DefCodegen storage** works for definitions compiled via `compile_unit`.
7. **Session persistence** (`save_current_module`) still fires after definitions.
8. **Error recovery** (TC snapshot/restore) still works — `compile_unit` failure triggers restore.

### Risk: REPL display after compile_unit

The current REPL `compile_and_execute` returns `ReplResult` which includes `is_definition`, `definition_display`, and `eval_duration`. After migration, `codegen_and_execute` returns `CodegenResult` which has `value` and `result_type` but NOT `is_definition` or `definition_display`.

`/int` must bridge this gap. Options:
- Derive `is_definition` from the `CompileUnitResult.program` — if all items are `TopLevel::Defn | TopLevel::TypeDef | TopLevel::TraitDecl | TopLevel::TraitImpl`, it's a definition.
- Derive `definition_display` from `CheckResult.display` (which already exists for trait decls, impls, etc.) or build it from the `TopLevel` items.
- Measure `eval_duration` by timing the `codegen_and_execute` call.

This is straightforward but requires care — it's the most likely source of subtle display regressions.

### Risk: REPL module structure tracking

The current `eval_import` appends to `self.current_module_structure.import_specs` (line 858-860). The current `eval_flattened_forms` appends to `self.current_module_structure.impl_sexps` (line 684-688). After migration, `compile_unit` populates its own `ModuleStructure` in the result. The REPL must merge `CompileUnitResult.module_structure` into `self.current_module_structure` after each successful `compile_unit` call. This is the mechanism for session persistence to accumulate imports and impls across multiple REPL inputs.

## Skill Plans

### /int
**Task**: Rewrite REPL eval to use compile_unit
**Design doc**: `design/arch/pipeline-v3-roadmap.md` Step 9
**Approach**: Per /arch: (a) re-parse in compile_unit, (c) store sexps from REPL parse, annotations+introspection stay outside compile_unit, two sub-steps (Wave 0: route through compile_unit, Wave 1: delete dead code)
**Acceptance**: All REPL tests pass, v1 pipeline code deleted ✓

### /qa
**Task**: Verify REPL tests pass, run demo files
**Acceptance**: 1533 passed, 11 pre-existing sketch_port failures ✓

### /review
**Task**: Review implementation — verify 8 architectural invariants
**Acceptance**: All 8 invariants verified ✓ (0B, 0I, 6S)

### /arch
**Task**: Decide on re-parse vs pre-parsed-sexps entry point, DefCodegen storage approach
**Acceptance**: Review written

### /repl, /frontend, /typecheck, /backend, /platform, /stdlib, /examples, /docs, /port
**Task**: No work this sprint (REPL changes are /int scope since they're in src/)

## Waves

### Wave 0: Route normal compilation through compile_unit (Sub-step A)

**Goal**: `eval` calls `compile_unit` + `codegen_and_execute` for all non-annotation, non-introspection input.

- `/int`: Rewrite `eval` to call `compile_unit` for the normal path. Keep `check_bare_symbol_introspection` and `eval_annotation_expr` as pre-compile_unit interceptions. Bridge `CodegenResult` → `ReplResult`. Merge `CompileUnitResult.module_structure` into `current_module_structure`. Store DefCodegen from REPL-parsed sexps.
- `/qa`: Run full test suite + demos after Wave 0. Report any display or behavior regressions.

**Gate**: All tests pass. All demos play cleanly.

### Wave 1: Delete dead code and clean up (Sub-step B)

**Goal**: Remove all REPL v1 pipeline code. Refactor `eval_annotation_expr` to use `codegen_and_execute`.

- `/int`: Delete `eval_sexp`, `eval_flattened_forms`, `eval_defmacro`, `eval_import`, `eval_platform`, `compile_and_execute`, `execute_expr`, `execute_defn`, `execute_typedef`, `execute_trait_decl`, `execute_trait_impl`, `build_check_for_backend`. Refactor `eval_annotation_expr`.
- `/review`: Review for architectural invariants (no REPL-owned typecheck/codegen/macro/import/platform calls remain).
- `/qa`: Re-run full test suite + demos. Verify `cargo clippy` clean.

**Gate**: Same test results as Wave 0. No Blocker review findings. Clippy clean.

## Notes

- The REPL's `eval` function is 3,085 lines in repl/mod.rs. Most of this is slash commands, display formatting, and watch infrastructure — not the eval chain itself. The eval chain is ~500 lines (eval through eval_flattened_forms).
- The roadmap suggests an incremental approach: "move one interception at a time (defmacro first, then import, then platform, then introspection), testing after each." This is wise given the risk.
- `compile_unit` currently returns `CompileUnitResult` with `program: Vec<TopLevel>` but NOT the pre-expansion sexps. DefCodegen storage needs pre-expansion sexps. Options: (a) add original_sexps to CompileUnitResult, (b) have the REPL call `process_forms_with_originals` separately before compile_unit, (c) store sexps in the REPL from the parse step.

## Outcome

### Delivered

**Step 9 — REPL migration to compile_unit (the highest-risk step):**

**Wave 0 — Route through compile_unit:**
- New `eval_via_compile_unit` method: builds CompileContext, calls `compile_unit` + `codegen_and_execute`
- `build_repl_result`: bridges `CompileUnitResult` + `CodegenResult` → `ReplResult` (is_definition, definition_display, eval_duration)
- `build_empty_program_result`: handles defmacro-only, import-only, platform-only inputs
- `build_definition_display`: builds `:Type module/name ; classification` display
- `store_def_codegen`: stores pre-expansion sexps in DefCodegen for introspection
- `track_impl_sexps`: tracks impl sexps for session persistence
- `merge_module_structure`: merges import/platform specs into current module structure
- GOT alias cleanup after codegen (compatibility shim)
- Trace infrastructure setup for (trace ...) and (run-tests ...) expressions

**Wave 1 — Delete dead code (~815 lines):**
- Deleted from repl/mod.rs: `eval_sexp`, `eval_flattened_forms`, `eval_defmacro`, `eval_import`, `eval_platform`, `compile_and_execute`, `execute_expr`, `execute_defn`, `execute_typedef`, `execute_trait_decl`, `execute_trait_impl`, `compile_mono_defns`, `compile_and_register_defn*`, `build_check_for_backend`, `invoke_jit_eval`, `is_import_form`, `loaded_platforms` field
- Deleted from repl/trace.rs: `TracedCompiledExpr`, `compile_expr_with_traced_fns`
- Refactored `eval_annotation_expr` to use `codegen_and_execute` (v3 pipeline)
- Refactored `reload_single_module` to use `compile_unit` (v3 pipeline)

**Architectural invariants verified (all 8 pass):**
1. No REPL-owned typecheck calls (except annotations)
2. No REPL-owned codegen calls
3. No REPL-owned macro compilation
4. No REPL-owned import handling
5. No REPL-owned platform loading
6. DefCodegen storage works
7. Session persistence fires
8. Error recovery works

### Deferred
- GOT alias cleanup shim (S6) — compatibility workaround, proper fix is teaching codegen_and_execute about interactive mode aliases
- `restore_user_cl` still uses v1 patterns (out of scope, tracked)
- Platform display regression (S3) — version/count info lost in empty-program display
- `eval_via_compile_unit` function length (S1, 118 lines)

### Findings
- The REPL migration was less risky than expected because `compile_unit` already handled all the interception points (defmacro, import, platform, macro expansion, begin-flattening). The risk was in the wiring (result bridging, DefCodegen storage, module structure merging), not in the compilation logic.
- repl/mod.rs went from ~3,085 lines to ~2,763 lines (net -322 lines). The deleted code was the most complex part of the REPL — the parallel compilation pipeline that duplicated 6 compile_unit stages.
- `eval_annotation_expr` and `check_bare_symbol_introspection` correctly stay as REPL-specific pre-compile_unit interceptions, overriding the roadmap's suggestion to delete them.
