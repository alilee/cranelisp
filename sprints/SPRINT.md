# Sprint 55: AST on Symbol Table

**Status**: DRAFT
**Ring**: 4 (Effects — full spec scope)
**Goal**: Typecheck writes AST bodies, resolved calls, and expr types directly onto ModuleEntry and AST nodes. CheckResult eliminated as a boundary type.

## Scope

Phase 1 of `design/arch/pipeline-v4-roadmap.md`. The foundational data model change: once AST bodies, types, and resolved calls live on `ModuleEntry`, every downstream convergence step (Phases 2–5) becomes possible.

Four sequential steps, each leaving tests green:

1. **Step 1a**: Add `ast: Option<Defn>` field to `ModuleEntry::Def`. Typecheck stores the typechecked defn body on the entry after `check_form(CheckBody)`. Initially duplicated — both the entry and `CodegenInput.program` carry the body. No consumers change. Write-only.

2. **Step 1b**: Move resolved calls and expr types onto AST nodes. Add `resolved_call: Option<ResolvedCall>` to `Expr::Apply` and `inferred_type: Option<Type>` to `Expr` (or wrapping struct). Typecheck populates these during inference alongside the existing `HashMap<Span, _>` side maps (dual-write). Add assertions that both paths agree.

3. **Step 1c**: Backend reads from AST nodes instead of `CheckResult` side maps. `FnCompiler` and `compile_to_module` switch to AST-node-sourced types and resolved calls. Side maps become optional/deprecated.

4. **Step 1d**: Eliminate `CheckResult` as boundary type. `compile_to_module` no longer takes `CheckResult` — reads everything from `ModuleEntry::Def.ast` (body + resolved calls + types) and `ModuleEntry::Def.scheme` (type signature). `CheckResult` reduced to typecheck-internal type (warnings + display info). `CodegenInput` deleted.

### /int Burden Assessment

Steps 1a and 1d touch `/int`-owned files. Step 1a is small (write to entry in worker.rs). Step 1d is medium (delete `CodegenInput` stashing in worker.rs/session_v4.rs, update callers) — but it's deletion, not new construction. Steps 1b and 1c are entirely within `/typecheck` and `/backend`.

### Deferred Tests from Sprint 54

9 tests remain deferred — all need Phases 2–5:
- 3 multi-sig JIT (Phase 2)
- 4 cache/link GOT (Phase 3+5)
- 1 run-tests special form (new feature)
- 1 cache-hit dep (Phase 5)

This sprint doesn't fix them but must not regress anything. The 9 failures are the known baseline.

### FIXME Debt

No source code FIXMEs found. Design doc FIXMEs are historical (archived sprints).

### Out of Scope

- Phase 2 (single codegen entry point) — depends on Phase 1 completing
- Phase 3 (GOT + code on SymbolTable) — depends on Phase 2
- Phase 4 (platform + persistent workers)
- Phase 5 (structural declarations + cache)
- Ring 4 gate review
- Examples update (pre-existing: examples use removed Ring 0 primitives)

## Architecture Review

**Reviewer**: /arch
**Verdict**: APPROVED with conditions

### 1. Technical Coherence — Step Sequencing

The four steps (1a, 1b, 1c, 1d) are correctly sequenced. Each step adds one capability and leaves the system in a working state:

- 1a (write-only `ast` field) has zero consumers, so it cannot break anything.
- 1b (dual-write annotations) keeps the old path working while the new path is populated.
- 1c (switch readers) is safe because 1b's dual-write assertions have validated data equivalence.
- 1d (delete old path) is safe because 1c has already switched all consumers.

Crate boundaries are respected. Steps 1a and 1b modify `cranelisp-types` (boundary types, requires /arch approval) and `cranelisp-typecheck` (writer). Step 1c modifies `cranelisp-backend` (reader). Step 1d modifies `src/` (integration wiring). No crate introduces an unexpected dependency.

### 2. No Interim Architecture (Principle 8)

The dual-write period in Steps 1a-1b is **not** interim architecture — it is a migration strategy. The side maps are not new; they already exist. The new AST-node fields are the target. The dual-write is the mechanism to validate correctness before switching consumers. It will be deleted in Step 1d of this same sprint. Acceptable.

However, one concern: the sprint describes `CheckResult` being "reduced to typecheck-internal type (warnings + display info)" rather than deleted. This is fine — `CheckResult` continues to serve a legitimate purpose as a typecheck-internal accumulator for warnings and display info. It just stops being a boundary type between typecheck and backend. The name may become misleading; `/typecheck` should consider renaming to `CheckOutput` or similar in the design doc.

### 3. Design References

The sprint correctly references:
- `design/arch/pipeline-v4-roadmap.md` Phase 1 (the authoritative roadmap)
- `design/arch/pipeline-v4.md` Section 9.1 (target data model)

**Gap**: The sprint should also reference `design/backend/compile-to-module.md` Section 10, which already analyzed `CodegenInput` simplification and proposed Option A (the approach this sprint takes). The `/backend` design doc should cite this prior analysis.

### 4. Interface Changes Required in `cranelisp-types`

The sprint correctly identifies the boundary type changes. Specific approved changes:

**Step 1a — `ModuleEntry::Def`** (in `crates/cranelisp-types/src/module.rs`):
```rust
ModuleEntry::Def {
    // ... existing fields ...
    /// Typechecked function body. Written by typecheck after check_form(CheckBody).
    /// Read by codegen. None for primitives, special forms, and pre-body-check entries.
    #[serde(default)]
    ast: Option<Defn>,
}
```
Approved. Uses existing `Defn` type. `Option` is correct — primitives and special forms have no AST body. `#[serde(default)]` for backward-compatible cache deserialization.

**Note**: The roadmap specifies `ast: Option<DefnVariant>` but the sprint uses `ast: Option<Defn>`. Using `Defn` is correct for now because the current `compile_to_module` expects `Defn` (it reads `defn.name`, `defn.variants`, etc.). The roadmap target of `DefnVariant` is a Phase 2 concern — when `compile_to_module` switches to `names: &[Symbol]`, it can read the name from the symbol table key and the body from a single `DefnVariant`. Changing to `DefnVariant` now would require Step 1c to reconstruct `Defn` from entry fields, which is unnecessary work.

**Step 1b — `Expr` annotation**: This is the critical design decision. Two approaches:

**(A) Fields directly on `Expr` variants** — add `inferred_type: Option<Type>` and `resolved_call: Option<ResolvedCall>` (Apply-only) as fields on each variant. Pros: zero indirection, pattern matching works naturally. Cons: `Expr` enum size increases (every variant pays for the largest variant's size), complicates `Serialize`/`Deserialize`, every `Expr` construction site must add `inferred_type: None`.

**(B) Wrapping struct `TypedExpr`** — `struct TypedExpr { pub expr: Expr, pub inferred_type: Option<Type>, pub resolved_call: Option<ResolvedCall> }`. Pros: `Expr` unchanged, clean separation of parsing output (bare `Expr`) vs typecheck output (`TypedExpr`). Cons: extra indirection, recursive `TypedExpr` requires `Box<TypedExpr>` in `Expr::Let`, `Expr::If`, etc.

**Decision**: Neither approach is ideal. The practical path is **(A) with `resolved_call` on `Apply` only, and `inferred_type` as a single field on a wrapping struct at the `DefnVariant` level, not per-`Expr`-node**. Rationale:

- Per-expr `inferred_type` on every node is expensive: `Type` is a recursive enum (can be large), and most expressions' types are not needed by codegen — only call sites, let bindings, match scrutinees, and heap-classified expressions need types. The current `expr_types: HashMap<Span, Type>` is sparse for a reason.
- `resolved_call` on `Apply` is correct — it's specific to call sites and carries only an enum discriminant + small data.
- The right granularity for per-expression types is to keep the `HashMap<Span, Type>` as a field on the `Defn` (or `DefnVariant`) rather than distributing it across every `Expr` node. This preserves sparsity and avoids bloating the AST.

**Approved approach for Step 1b**:
1. Add `resolved_call: Option<ResolvedCall>` to `Expr::Apply` only.
2. Keep `expr_types: HashMap<Span, Type>` but move it from `CheckResult` to a new field on `Defn` (or `DefnVariant`): `expr_types: HashMap<Span, Type>`. This is the per-function type map, co-located with the function body.
3. Similarly, move `method_resolutions: MethodResolutions` to a new field on `Defn` (the `resolved_call` on `Apply` is the primary source; the map is for non-Apply resolutions if any, and for the dual-write verification period).

This achieves the pipeline-v4.md goal (types co-located with AST, not in side maps passed separately) without bloating every `Expr` node. The `/typecheck` design doc must justify whichever approach it takes.

**Condition**: The `/typecheck` design doc (`design/typecheck/ast-annotation.md`) must analyze `Expr` size impact and justify the chosen approach before implementation begins. `/arch` will review in Wave 2.

### 5. Hidden Dependencies

**MonoDefn and default_method_defns**: The sprint plan doesn't explicitly address how `mono_defns` and `default_method_defns` from `CheckResult` will be handled. Currently, `compile_to_module` reads these from `CheckResult` (lines 114-115, 240 of `lib.rs`). In Step 1d, when `CheckResult` is eliminated as a boundary type, these must come from somewhere.

The target design (pipeline-v4.md Section 9.1) says mono specializations and default method implementations are separate `ModuleEntry::Def` entries in the symbol table. This means Step 1d has a hidden prerequisite: typecheck must register mono defns and default method defns as `ModuleEntry::Def` entries on the symbol table (with their own `ast` fields) so that `compile_to_module` can find them by name.

**Condition**: The `/typecheck` design doc must address mono_defns and default_method_defns placement. Either: (a) they become entries on the symbol table before Step 1d (preferred — aligns with target), or (b) Step 1d keeps a slim struct for these alongside the symbol table (not preferred — interim architecture).

**Phase 0 prerequisite**: The roadmap notes "Does not compile at HEAD" and specifies Phase 0 (stabilize) before Phase 1. The sprint plan doesn't mention Phase 0. Either Phase 0 was completed between Sprint 54 and 55, or this sprint has an unstated prerequisite. The sprint must land on a green baseline before data model changes begin.

**Condition**: Wave 3 must not begin until the codebase compiles and the known-failure baseline is established. If Phase 0 is incomplete, Wave 1 should include a Phase 0 task or document that it was completed.

### 6. Single Pipeline Invariant (Principle 11)

Maintained. The changes affect data flow (what types carry the information) but not pipeline structure. There is still one `compile_to_module`, one `process_module_forms`, one `check_form`. The REPL and batch paths both go through the same worker pipeline. No new parallel paths are introduced.

### 7. Phase 1 Alignment

The sprint correctly implements Phase 1 of the roadmap. All four sub-steps (1a through 1d) map directly to the roadmap's Phase 1 steps. The scope is correctly bounded — Phases 2-5 are explicitly out of scope.

The roadmap's Phase 1 exit criterion is: "All tests pass. `CodegenInput` type deleted." The sprint's Wave 4 exit criterion matches.

### 8. /int Burden Assessment

The assessment is **slightly optimistic**. Step 1a is indeed small. Step 1d is described as "deletion, not new construction" — this is mostly true, but `/int` will also need to handle the mono_defns/default_method_defns placement (see Finding 5 above). If those become symbol table entries, `/int` must update the worker loop to register them, which is more than just deleting `CodegenInput`.

The claim that Steps 1b and 1c are "entirely within /typecheck and /backend" is correct for the core work, but Step 1b changes `cranelisp-types` (shared crate), which means all downstream crates recompile. Coordination matters for build times.

### 9. Risk Assessment

**Riskiest step: 1b (AST annotation)**. This is the step with the most design freedom and the most potential for wrong turns. Specifically:
- Adding `Option<Type>` to every `Expr` variant would increase `Expr` enum size by 40+ bytes (Type is a recursive enum) and require touching every `Expr` construction site across the codebase. This is avoidable with the per-function map approach recommended above.
- Adding `Option<ResolvedCall>` to `Expr::Apply` is lower risk — it's one variant, and `ResolvedCall` is moderate size.
- The dual-write verification (asserting side maps agree with node annotations) is the safety net. If assertions fail, the bug is in the new writer, not the old reader.

**Second riskiest: 1d (CheckResult elimination)**. The mono_defns/default_method_defns dependency (Finding 5) could block this step if not planned for. The risk is mitigated if the `/typecheck` design doc addresses it in Wave 1.

### 10. Carried Debt

- 9 deferred tests from Sprint 54 — correctly identified as out of scope (they need Phases 2-5).
- No source code FIXMEs — verified.
- Build status at HEAD — needs resolution before Wave 3 (see Finding 5).
- 200 test failures at HEAD~1 — the sprint should state whether Phase 0 fixes are a prerequisite or whether the 100 non-deferred failures (200 - 9 deferred = ~191 from Phase 0 categories) are the accepted baseline.

### Conditions for Approval

1. `/typecheck` design doc must analyze `Expr` size impact and justify the annotation approach.
2. `/typecheck` design doc must address mono_defns and default_method_defns placement for Step 1d.
3. Wave 3 must not begin until the codebase compiles. The sprint must document the Phase 0 / baseline status.
4. `/backend` design doc should reference `design/backend/compile-to-module.md` Section 10 (prior CodegenInput analysis).

## Skill Plans

### /arch
**Task**: (A) Review sprint scope for coherence with pipeline-v4-roadmap Phase 1. (B) Approve boundary type changes to `cranelisp-types` (new field on `ModuleEntry::Def`, new fields on `Expr`/`Expr::Apply`). (C) Review design docs from /typecheck and /backend.
**Design doc**: `design/arch/pipeline-v4-roadmap.md` (Phase 1 section)
**Acceptance**: All boundary type changes reviewed and approved. No interim architecture.

### /typecheck
**Task**: (A) Step 1a — write typechecked defn body to `ModuleEntry::Def.ast` after `check_form(CheckBody)`. (B) Step 1b — annotate AST nodes with resolved calls and inferred types during inference (dual-write with existing side maps).
**Design doc**: `design/typecheck/ast-annotation.md` (to be written)
**Design refs**: `design/arch/pipeline-v4.md` §9.1 (target data model), `crates/cranelisp-typecheck/src/checker.rs` (current inference), `crates/cranelisp-typecheck/src/program.rs` (FormCheckResult)
**Arch conditions on the design doc** (from review §4 and §5 — must be addressed before Wave 2 approval):
1. **Expr size impact analysis**: Justify the annotation approach. /arch recommends: `resolved_call: Option<ResolvedCall>` on `Expr::Apply` only. Do NOT add `inferred_type: Option<Type>` to every Expr variant — `Type` is recursive and would bloat every variant. Instead, move `expr_types: HashMap<Span, Type>` from `CheckResult` to a field on `Defn` (co-located with body, preserving sparsity).
2. **mono_defns and default_method_defns placement**: Currently on `CheckResult`. Step 1d eliminates `CheckResult` as boundary type. Where do these go? Target (pipeline-v4.md §9.1): they become `ModuleEntry::Def` entries on the symbol table with their own `ast` fields. Design doc must specify how typecheck registers them.
3. **CheckResult rename**: Consider renaming to `CheckOutput` since it stops being a boundary type and becomes typecheck-internal (warnings + display info only).
**Acceptance**: (A) `ModuleEntry::Def.ast` populated for all defns after typecheck. (B) AST nodes carry resolved calls. Expr_types map co-located with Defn. Dual-write assertions pass. All tests green.

### /backend
**Task**: (A) Step 1c — switch `FnCompiler` to read resolved calls and expr types from AST nodes/Defn instead of `CheckResult` side maps. (B) Step 1d — change `compile_to_module` signature to not require `CheckResult` (reads from `ModuleEntry::Def.ast` + `.scheme`).
**Design doc**: `design/backend/ast-sourced-codegen.md` (to be written)
**Design refs**: `design/arch/pipeline-v4.md` §9.1 + §9.3, `crates/cranelisp-backend/src/compiler/*.rs`, `crates/cranelisp-backend/src/lib.rs`
**Arch condition on the design doc** (from review §3 — must be addressed before Wave 2 approval):
1. **Reference prior analysis**: Cite `design/backend/compile-to-module.md` Section 10 (CodegenInput simplification, Option A). Build on that analysis rather than starting fresh.
**Acceptance**: (A) All backend tests pass reading from AST nodes/Defn. (B) `compile_to_module` works without `CheckResult` parameter. `CodegenInput` type deleted.

### /int
**Task**: (A) Step 1a — update `process_module_forms` in worker.rs to write defn body to `ModuleEntry::Def.ast` after typecheck. (B) Step 1d — delete `CodegenInput` stashing in worker.rs (`stash_codegen_input`), delete `CodegenInput` from session_v4.rs (`SharedState`), update all `compile_to_module` callers to new signature.
**Design doc**: n/a (integration wiring — design is in /typecheck and /backend docs)
**Design refs**: `src/worker.rs` (process_module_forms, codegen_module_symbols, stash_codegen_input), `src/session_v4.rs` (SharedState.codegen_inputs)
**Acceptance**: (A) `ModuleEntry::Def.ast` populated in worker pipeline. (B) `CodegenInput` type and `codegen_inputs` DashMap deleted. All callers updated. Tests green.

### /qa
**Task**: (A) Write tests verifying AST annotations agree with side maps (Step 1b verification). (B) Write tests for new `compile_to_module` signature (Step 1d). (C) Verify no regressions in existing 1595 passing tests.
**Design doc**: n/a
**Design refs**: `design/arch/pipeline-v4-roadmap.md` Phase 1 verification criteria
**Acceptance**: New tests pass. 0 regressions. 9 deferred tests unchanged.

### /review
**Task**: Code review of all changes across Steps 1a–1d. Focus on: boundary type changes are minimal, no unnecessary coupling, AST annotation doesn't bloat Expr, compile_to_module signature is clean.
**Acceptance**: 0 Blockers, all Important findings addressed.

### /frontend
**Task**: No primary assignment. May need to update `cranelisp-types/src/ast.rs` for Step 1b (adding fields to Expr) — coordinated with /typecheck.

### /typecheck (boundary type changes)
**Task**: Add fields to `ModuleEntry::Def` (Step 1a) and `Expr` types (Step 1b) in `cranelisp-types`. These are boundary type changes requiring /arch approval.
**Note**: Normally `cranelisp-types` is /arch territory, but the implementation is done by the skill that understands the types. /arch reviews and approves.

### /repl
**Task**: Create sprint demo `repl/demos/ring4m.demo` demonstrating that the REPL still works correctly after the data model change. Verify all prior demos play cleanly.
**Acceptance**: Demo plays cleanly. No regressions in prior demos.

### /port, /examples, /stdlib, /docs, /platform, /spec
**Task**: No primary assignment. Validate that exemplar, examples, and stdlib still work after changes.

## Waves

### Wave 1: Design docs

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | Write `design/typecheck/ast-annotation.md` | **done** | Annotation strategy, dual-write, field placement, Expr size analysis, mono/default placement |
| /backend | Write `design/backend/ast-sourced-codegen.md` | **done** | FnCompiler AST access, new compile_to_module sig, extra defns handling, cites compile-to-module.md §10 |

### Wave 2: Design review

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Review both design docs for coherence | **done** | APPROVED — see Notes for full review |
| /arch | Approve cranelisp-types changes (ModuleEntry, Expr) | **done** | Approved with one advisory (see review) |
| /qa | Derive test cases from design docs | **done** | Test case analysis + test helper assessment — see Notes |

### Wave 3: Steps 1a + 1b (type changes + typecheck writes)

**Prerequisite** (arch condition 3): Baseline must be green (1595 pass, 9 deferred). Confirmed — Sprint 54 commit `1457eb0` is the baseline.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | Add `ast` to ModuleEntry::Def + write body | **done** | 21 construction sites, write in program.rs after body check |
| /int | Update worker.rs to write defn to entry | **done** | Write handled in typecheck; worker.rs construction site updated |
| /typecheck | Annotate AST nodes with types + resolved calls | **FAILED** | Dual-write during infer_expr is incomplete — post-passes modify side maps without updating AST nodes. 59 regressions when Step 1d tried to use the annotations. |
| /qa | Tests: AST annotations agree with side maps | pending | Step 1b verification |
| /review | Review Steps 1a + 1b code | pending | |

**Status**: Step 1b fields are on `Expr` (structural change done) but annotations are incomplete. Needs redesign — see Wave 3b below.

### Wave 3b: Step 1b redesign (post-pass AST annotation)

Discovery: typecheck has 4+ post-passes that modify side maps after `infer_expr`. Step 1b's dual-write only covers `infer_expr`, leaving AST nodes with unresolved type vars and missing resolutions. /arch specified 7 concrete examples in `design/arch/ast-annotation-examples.md`.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Specify AST annotation examples | **done** | 7 examples with expected annotations + failure modes |
| /typecheck | Update design for post-pass annotation | pending | Must address all post-passes, final substitution, mono path |
| /arch | Re-review updated design | pending | 2 blocking findings from prior review |
| /qa | Write tests from arch examples | pending | 7 test cases verifying annotated AST completeness |
| /typecheck | Reimplement 1b: post-passes update AST nodes | pending | |

**Exit criterion**: All 7 arch examples produce correctly annotated ASTs. No `enrich_defn_from_side_maps` needed. All tests green.

### Wave 4: Steps 1c + 1d (backend reads + CheckResult elimination)

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /backend | FnCompiler reads from AST nodes | **done** | Side maps removed from CompileContext |
| /backend | compile_to_module new signature (no CheckResult) | **partial** | Signature changed but 59 regressions from incomplete AST annotations |
| /int | Delete CodegenInput, update callers | **partial** | CodegenInput replaced with codegen_programs but enrichment workaround still present |
| /qa | Tests for new compile_to_module signature | pending | |
| /review | Review Steps 1c + 1d code | pending | |

**Exit criterion**: `compile_to_module` works without `CheckResult`. No enrichment workaround. `CodegenInput` deleted. All tests green.

### Wave 5: Verification + Showcase

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Full suite verification | pending | 0 regressions |
| /repl | Sprint demo + prior demo verification | pending | ring4m.demo |
| /port | Validate exemplar | pending | |

**Exit criterion**: Sprint close checklist passes.

## Notes

- Steps 1a→1b→1c→1d are strictly sequential. Each step lands on a green test suite.
- Step 1b (AST annotation) is the riskiest — it touches `Expr`, which is used everywhere. The dual-write approach mitigates: old side maps continue working until Step 1c switches readers.
- Step 1d is the payoff — `CheckResult` eliminated, `CodegenInput` deleted. This is the gate for Phase 2.
- The 9 deferred tests from Sprint 54 remain deferred. They are the known baseline.

### Wave 2 Architecture Review

**Reviewer**: /arch
**Verdict**: APPROVED

Both design docs are architecturally sound and internally consistent. All four conditions from the Sprint 55 architecture review are satisfied.

#### Condition Verification

1. **Expr size impact analysis** (`ast-annotation.md` Section 4): Present and thorough. The doc correctly rejects Approach A (unboxed `Option<Type>` per variant) and chooses `Option<Box<Type>>` (+8 bytes per variant) and `Option<Box<ResolvedCall>>` (+8 bytes on Apply only). The conclusion that enum size grows from ~64 to ~72 bytes (+12.5%) is directionally correct. Note: the doc estimates `Type` at ~56 bytes, but `Type::ADT(FQTypeName, Vec<Type>)` is actually ~72 bytes (FQTypeName = ModuleFullPath(24) + TypeName(24) = 48, plus Vec<Type> = 24). This does not change the analysis — `Option<Box<Type>>` is 8 bytes regardless of the boxed `Type` size. The architectural decision (box to avoid bloating the enum) is correct and well-justified.

2. **mono_defns/default_method_defns placement** (`ast-annotation.md` Section 5): Clear and well-reasoned. For Step 1d, the typecheck doc specifies registering them as `ModuleEntry::Def` entries on the symbol table (the pipeline-v4.md target). The backend doc (`ast-sourced-codegen.md` Section 3.4) chooses Option A (inline into `program`) as the interim approach for this sprint, since `compile_to_module` still takes `program: &Program`. These two docs are not contradictory — the typecheck side creates the entries, and the backend side reads them from `program` until Phase 2 switches to `names: &[Symbol]`. The timing analysis (Section 5.4) is sound: mono defns appear after `finalize_check_result`, which precedes codegen workers.

3. **Baseline green**: Already confirmed in the sprint plan — Sprint 54 commit `1457eb0` established the baseline (1595 pass, 9 deferred).

4. **Backend doc references compile-to-module.md Section 10**: Present at the top of the backend doc in the References block and in Section 1 (Prior analysis). The doc correctly notes it goes beyond Option A (eliminating both `CodegenInput` AND `CheckResult` as boundary types), which is the right call given that AST node annotations make the side maps redundant.

#### Design Coherence Assessment

**Internal consistency**: The two docs are mutually consistent. The typecheck doc writes; the backend doc reads. The data flow is clear: typecheck populates `inferred_type` and `resolved_call` on `Expr` nodes during inference, then the annotated `Defn` is stored on `ModuleEntry::Def.ast`. Backend reads from the same nodes during compilation. No contradictions found.

**Chosen approach (Option<Box<Type>> on every Expr)**: Architecturally sound. The boxing keeps Expr enum size growth to +8 bytes per variant. This diverges from the /arch recommendation in the Sprint 55 architecture review (which recommended keeping `HashMap<Span, Type>` on `Defn` to preserve sparsity). The typecheck doc provides a clear rationale for the divergence: Span is a fragile key, and per-node annotation eliminates an entire class of bugs. The memory impact analysis (Section 4.3) is reasonable — the 100 box allocations per function are comparable to the HashMap overhead they replace. Approved.

**`&mut Expr` threading during inference**: The doc addresses this concern adequately. Typecheck clones the `Defn` at the start of body checking (it already clones for constrained-fn storage), so all mutation is on the clone. The original AST is untouched. The alternative (post-hoc walk) was considered and rejected for the right reason — it still depends on Span-keyed lookup. The `set_inferred_type` helper method keeps mutation localized. This is a clean approach.

**Dual-write verification strategy**: Adequate. Debug-only assertions comparing old (side-map) and new (AST-node) sources. Both docs describe the same verification at their respective boundaries — typecheck (Section 3.5) verifies the write side, backend (Section 2.6) verifies the read side. The assertions are removed in Step 1d when the side maps are deleted. This provides a two-layer safety net.

**mono_defns "inline into program" (Option A)**: This is technically interim architecture — Phase 2 will switch to `names: &[Symbol]` and read mono defns from the symbol table. However, it is acceptable because: (a) the `program` parameter already exists in this sprint's signature and won't be deleted until Phase 2, (b) the typecheck side is doing the target-state work (registering mono defns as `ModuleEntry::Def` entries), and (c) the interim is confined to a single sprint boundary — Phase 2 removes it. This is a migration strategy, not a structural debt.

**Crate boundary changes**: Minimal and justified. `cranelisp-types` gains two `Option<Box<_>>` fields on `Expr` variants plus one `Option<Defn>` on `ModuleEntry::Def`. No new crate dependencies. No new boundary types. `CheckResult` stops crossing the boundary (reduction in surface area). Approved.

**Sketch comparison sections**: Both docs include substantive sketch comparisons. The typecheck doc (Section 7) correctly identifies that the sketch used `HashMap<Span, Type>` and never annotated AST nodes, explains why this worked for the sketch (single-threaded, single-module), and justifies the divergence (concurrent pipeline, per-entry isolation). The backend doc (Section 6) identifies the sketch's side-map pattern in `FnCompiler` and explains how the access pattern changes. Both sections go beyond "the sketch did X, we do Y" to explain *why* the divergence is necessary.

#### Advisory (non-blocking)

The typecheck doc estimates `Type` size at ~56 bytes (Section 4.1), but `Type::ADT(FQTypeName, Vec<Type>)` is ~72 bytes (`FQTypeName` = two String newtypes at 24 bytes each = 48, plus `Vec<Type>` = 24). This does not affect the architectural decision (boxing is correct regardless), but the size table should be corrected during implementation for accuracy. Filed as advisory, not blocking.

### Wave 2 QA Test Case Analysis

**Reviewer**: /qa

#### Test Strategy

This sprint is an internal restructuring with no new user-visible behavior. The primary test strategy is:

1. **Regression gate**: All 1582 currently passing tests must keep passing (22 failures are the known baseline: 9 deferred from Sprint 54, plus 8 cache SIGSEGV, 2 sketch_port multi-sig, 3 v4_platform).
2. **Dual-write assertions**: `debug_assert!` in Steps 1b and 1c verifies old and new paths agree. These run automatically in test builds (debug profile). No separate test code needed.
3. **No new spec surface**: No new language features, so no new spec-derived tests.

#### Additional Test Cases Beyond Dual-Write

The dual-write `debug_assert!` assertions are the primary verification mechanism. They run on every existing test, providing broad coverage. However, four targeted tests would add value:

**1. Unit test for `Expr::set_inferred_type()` (Step 1b, /typecheck or /backend unit tests)**
- Construct each `Expr` variant with `inferred_type: None`.
- Call `set_inferred_type(Some(Box::new(Type::Int)))`.
- Assert `inferred_type()` returns `Some(&Type::Int)`.
- Value: validates the helper method works for all 14 variants. Low cost, catches mechanical errors in the match arms.

**2. Unit test for `Expr::Apply.resolved_call` round-trip (Step 1b)**
- Construct `Expr::Apply` with `resolved_call: None`.
- Set `resolved_call = Some(Box::new(ResolvedCall::TraitMethod { ... }))`.
- Assert it reads back correctly.
- Value: validates the Apply-specific field works alongside the generic `inferred_type`.

**3. Integration test: AST nodes carry types through full pipeline (Step 1c)**
- Compile a simple program `(defn f [x] (+ x 1))` through the REPL path.
- After compilation, read back the `ModuleEntry::Def.ast` for `f` from the symbol table.
- Assert that the body's `Expr::Apply` node has `inferred_type.is_some()` and `resolved_call.is_some()`.
- Value: validates the end-to-end write path (typecheck wrote it) and persistence (it survived to the symbol table). This is the one test that exercises the NEW path directly rather than just asserting old == new.

**4. Negative test: constrained fn template has AST but is not compiled (Step 1d)**
- Define a constrained fn `(defn add [x y] (+ x y))` and call `(add 1 2)`.
- Verify the base name's `ModuleEntry::Def` has `DefKind::UserFn { constrained_fn: Some(_) }`.
- Verify the mono specialization `add$Int+Int` was compiled (has a GOT slot with a non-null code pointer).
- Verify the base template was NOT compiled directly.
- Value: validates the `constrained_fn_names` derivation from `DefKind` works correctly after `CheckResult` elimination.

#### Tests NOT Recommended

- **Test that CheckResult fields are empty after Step 1d**: Not useful. Step 1d deletes the fields entirely (compile error if anything still reads them). The compiler enforces this statically.
- **Test that CompileContext no longer has method_resolutions/expr_types**: Same reasoning — field deletion is enforced by the compiler. A runtime test adds nothing.
- **Boundary tests for the new `compile_to_module` signature**: The existing 143 backend unit tests already call `compile_to_module` through `test_compile_and_run` / `test_compile_program_and_run`. When the signature changes in Step 1d, these helpers must be updated. The tests themselves become the signature verification.

### Test Helper Assessment

#### Current State

The test infrastructure has two layers:

**Integration test helpers** (`tests/helpers/mod.rs`, 679 lines):
- `ReplSession` wraps `CompilerSession` with test-friendly defaults (no color, no cache, isolated project root).
- 5 session constructors: `new()`, `new_with_prelude()`, `new_for_file()`, `repl_session()`, `repl_session_with_test_prelude()`.
- 8 pipeline helpers: `batch_run()`, `compile_and_run_simple()`, `compile_and_run_typed()`, `compile_and_run_heap()`, `compile_both()`, `assert_type_error()`, `assert_parse_error()`, `assert_error()`.
- 2 RC helpers, 1 platform helper (`TestCapture`), 1 display helper.
- Backward-compatible wrappers preserve old signatures for ~650+ existing call sites.
- `eval_all_forms()` works around REPL single-sexp limitation by parsing and eval'ing form-by-form.

**Backend unit test helpers** (`crates/cranelisp-backend/src/lib.rs`, in `#[cfg(test)]`):
- `test_compile_and_run()` and `test_compile_program_and_run()` call `compile_to_module` directly.
- ~40 call sites within backend unit tests.
- These construct `CheckResult` manually and pass it to `compile_to_module`.

**Assessment**: `ReplSession` adds genuine value — it isolates tests from `CompilerSession` construction boilerplate (settings, project root, lib_dirs). The backward-compatible wrappers (`compile_and_run_simple`, `repl_session`) prevent churn on 650+ call sites. The helper layer is reasonably consistent. Sprint 54's `run_entry` / `project_from_sources` pattern (for file-based projects) was identified as needed but not yet implemented.

#### Sprint 55 Impact

**Integration tests (`tests/`)**: Zero direct impact. Integration tests use `ReplSession` which wraps `CompilerSession`. The `CompilerSession::eval()` API is unchanged — the data model changes are internal to the pipeline. All 1582 passing integration tests should continue passing with no test code changes.

**Backend unit tests (`crates/cranelisp-backend/src/lib.rs`)**: Significant impact. The two test helpers `test_compile_and_run` and `test_compile_program_and_run` construct `CheckResult` and pass it to `compile_to_module`. Step 1d removes the `CheckResult` parameter from `compile_to_module`. This breaks ~40 backend unit test call sites. The helpers must be updated to construct the new inputs (AST nodes with types/resolved calls already populated). The test `CheckResult` construction is replaced by annotating `Expr` nodes directly before passing them to `compile_to_module`.

**`codegen_module_symbols` in `src/worker.rs`**: Takes `check: &CheckResult`. Step 1d must update this function and its 2 call sites. This is `/int` work, not `/qa`.

#### Recommendations

**No separate test helper cleanup task for Sprint 55.** The changes are naturally scoped:

1. **Backend test helpers** (`test_compile_and_run`, `test_compile_program_and_run`): Must be updated in Step 1d when `compile_to_module` signature changes. This is `/backend`-owned work (they own their crate's unit tests). The update is mechanical: instead of building a `CheckResult` with `expr_types` and `method_resolutions` maps, set `inferred_type` and `resolved_call` directly on the `Expr` nodes being compiled. The helpers may actually get simpler (no HashMap construction, no Span tracking).

2. **Integration test helpers** (`tests/helpers/mod.rs`): No changes needed. `ReplSession` wraps `CompilerSession` at the API level, which is unchanged.

3. **Sprint 54's `project_from_sources` / `run_entry` pattern**: Still needed for watch/cache/link test rewriting, but that work is not in Sprint 55 scope. Do not mix it in.

**Summary**: Sprint 55 causes ~40 backend unit test helper updates (mechanical, Step 1d) and zero integration test helper changes. No cleanup task needed — the changes ride naturally with the signature migration.

### Wave 4 Architecture Re-Review

**Reviewer**: /arch
**Context**: Steps 1a-1c landed successfully. Step 1d (eliminate CheckResult as boundary type) introduced 4 regressions + 59 additional failures. Root cause: typecheck post-passes modify side maps AFTER `infer_expr` but do not update AST nodes. The integration layer added `enrich_defn_from_side_maps` as a workaround -- exactly the Span-keyed lookup pattern we are eliminating. Section 3.6 ("Post-Pass AST Update") was added to `design/typecheck/ast-annotation.md` to address this.

#### 1. Post-Pass Completeness (Question 1: Does Section 3.6 identify ALL post-passes?)

**Finding: Mostly complete, one gap.**

Section 3.6.1 identifies four post-passes:
- Phase 3: `resolve_deferred_trait_calls` (infer.rs:504)
- Pass 2.5: `resolve_multi_sig_overloads` (program.rs:1191)
- Pass 5: `resolve_pending_overloads` (program.rs:1395)
- Pass 5: `resolve_auto_curry` (program.rs:2382)

These match what `finalize_check_result_inner` (program.rs:759-889) actually calls. Verified against source -- no additional post-passes exist in that function that write to `state.method_resolutions` or `state.expr_types`.

**Gap: `resolve_inner_constrained_calls` in `recheck_body_for_mono` (traits.rs:1009).** This function adds `SigDispatch` entries for self-recursive constrained calls within mono defn bodies. Section 3.6.4 mentions it ("resolve_inner_constrained_calls adds SigDispatch entries... These must also be applied to AST nodes") but it is not listed as a post-pass in Section 3.6.1. This is adequate because it is scoped to the mono path and covered in 3.6.4, but the doc should be clear that this is a fifth source of `resolved_call` mutations. **Non-blocking.**

**Gap: `monomorphise_expr_calls` in REPL path (program.rs:2141).** This function generates mono defns AND writes `SigDispatch` entries to `state.method_resolutions` for REPL expressions. It is called from `check_repl_input_inner` (line 1555, 1573) but is not mentioned anywhere in Section 3.6. **This is a gap.** The REPL path description in 3.6.5 mentions `resolve_auto_curry` but not `monomorphise_expr_calls`, which is a separate post-pass that writes resolutions. **Blocking for correctness.**

#### 2. Ordering (Question 2: Is Section 3.6.3 correct?)

**Finding: Ordering is correct for the batch path.**

The ordering in 3.6.3 matches `finalize_check_result_inner` exactly:
1. Phase 2 (generalize) -- lines 768-784
2. Phase 3 (resolve_deferred_trait_calls) -- lines 786-810
3. Pass 2.5 (resolve_multi_sig_overloads) -- lines 812-816
4. Pass 3 (detect_constrained_fns) -- lines 818-833
5. Pass 4 (pass4_monomorphise) -- lines 835-836
6. Pass 5 (resolve_pending_overloads) -- line 839
7. Pass 5 (resolve_auto_curry) -- line 840
8. Final substitution -- lines 867-872
9. Write to ModuleEntry -- implied

**Hidden dependency concern**: `resolve_deferred_trait_calls` currently takes `&Expr` (immutable reference, infer.rs:504). The doc says "take `&mut Expr`" but the current Phase 3 loop (lines 786-810) constructs temporary `internal_defn` values for multi-sig variants by cloning from `working_program`. These temporary clones are discarded after the call. For the `&mut` change to work, Phase 3 must either: (a) mutate the annotated ASTs already stored on `ModuleEntry::Def.ast`, not temporary clones from `working_program`, or (b) store the Phase 3 results and apply them to the annotated ASTs later. The doc mentions option (a) implicitly ("walk each defn's `&mut` AST") but the current code walks `working_program`, not the stored ASTs. **The implementer needs to be aware that the loop structure changes -- it must iterate over the entries stored on the symbol table, not `working_program`.**

#### 3. Final Substitution Walk (Question 3: Does it handle all Expr variants?)

**Finding: Yes, with one caveat.**

The pseudocode in 3.6.2 shows recursion into `variant.body` for each defn variant. The comment says "same recursive structure as resolve_deferred_trait_calls." Checking `resolve_deferred_trait_calls` (infer.rs:504-571), it covers: Apply, Let, If, Lambda, Match, Annotate, VecLit, Trace, ParBind, plus a catch-all `_ => {}` for leaf nodes (IntLit, FloatLit, BoolLit, Var, StringLit). All 14 Expr variants are covered.

**Caveat**: The substitution walk must also apply `apply(subst, ty)` to `resolved_call` fields, not just `inferred_type`. `ResolvedCall::AutoCurry` contains a `trait_resolution: Option<Box<ResolvedCall>>` which may reference types indirectly, but more importantly the side-map substitution at line 868-872 operates on `expr_types`, which is separate from `method_resolutions`. The `method_resolutions` map is NOT substituted -- it is taken as-is (line 847-849). So the final substitution walk only needs to substitute `inferred_type` fields, not `resolved_call` fields. The doc is correct on this point.

**Additional caveat**: The substitution walk pseudocode does not show recursion into `Let` binding expressions, only `variant.body`. The actual walk must recurse into `bindings[i].1` as well as `body`. The doc says "same recursive structure as resolve_deferred_trait_calls" which does this correctly (lines 533-536), so this is covered by reference. **Non-blocking.**

#### 4. Mono Defn Path (Question 4: Is Section 3.6.4 complete?)

**Finding: Mostly complete, one structural concern.**

Section 3.6.4 correctly identifies that `recheck_body_for_mono` (traits.rs:976):
1. Calls `check_defn_body_with_types` with `&mut defn` -- Stage 1 dual-write works
2. Calls `resolve_auto_curry` -- drains pending auto-curry
3. Captures `state.method_resolutions` and builds `mono_expr_types`

And specifies:
- After `resolve_auto_curry`, apply deferred-node-update for auto-curry Apply nodes
- `resolve_inner_constrained_calls` entries must also be applied to AST nodes
- Final substitution walk on the mono defn's AST

**Structural concern**: `recheck_body_for_mono` saves and restores `state.method_resolutions` (lines 983, 1000). The mono body's resolutions are captured into a local `resolutions` variable (line 994), which is then passed to `resolve_inner_constrained_calls` (line 1012) and ultimately stored on `MonoDefn.resolutions`. For the AST annotation approach, these resolutions must be written to the mono defn's AST nodes BEFORE the resolutions local is consumed. The doc correctly identifies this but the ordering is tight -- the implementer must apply `resolve_inner_constrained_calls` results to the AST nodes before constructing the `MonoDefn`.

**Missing: `resolve_deferred_trait_calls` is NOT called in `recheck_body_for_mono`.** It is called in the batch path's Phase 3 before monomorphisation, so the original defn's deferred calls are resolved. But the mono re-check (`check_defn_body_with_types`) runs fresh inference on a cloned body with concrete types. If the re-check produces new deferred trait calls (possible when the concrete types reveal new trait method call sites), they would NOT be resolved. This appears to be a pre-existing issue in the current codebase (not introduced by the AST annotation work), but it means the mono defn AST might have missing `resolved_call` entries for trait methods that were deferred during re-check. **Non-blocking for this sprint, but worth noting.**

#### 5. Elimination of `enrich_defn_from_side_maps` (Question 5: Does Section 3.6.6 correctly justify elimination?)

**Finding: Yes, the justification is sound.**

Section 3.6.6 correctly identifies that `enrich_defn_from_side_maps` exists because post-passes wrote to side maps but not AST nodes. With each post-pass updating AST nodes directly (3.6.1), the enrichment function becomes redundant.

The current `enrich_defn_from_side_maps` implementations (worker.rs:1061, backend/lib.rs:443) use Span-keyed lookup with "overwrite if contains_var" heuristics. The doc correctly identifies this as fragile. Once the typecheck crate produces fully annotated ASTs, neither call site is needed.

**Verification**: The doc's claim that "After step 9, AST nodes are self-contained" requires that ALL sources of `resolved_call` and `inferred_type` are handled. Per findings 1 and 2 above, this holds for the batch path. The REPL path has the `monomorphise_expr_calls` gap (Finding 1), which must be addressed.

#### 6. Missed Post-Passes (Question 6)

**Finding: One missed, already noted in Finding 1.**

`monomorphise_expr_calls` (program.rs:2141) writes `SigDispatch` entries to `state.method_resolutions` for constrained-fn call sites in REPL expressions and defn bodies. It is called from `check_repl_input_inner` (lines 1555, 1573) after `resolve_auto_curry`. Section 3.6 does not mention it. Section 3.6.5 must include it.

No other post-passes were found that write to `state.method_resolutions` or `state.expr_types` outside `finalize_check_result_inner`.

#### 7. REPL Path (Question 7: Is Section 3.6.5 covered?)

**Finding: Incomplete.**

Section 3.6.5 says: "The REPL paths (`check_repl_input_inner`, `check_repl_multi_sig`) call `resolve_auto_curry` before building the result. The same pattern applies."

Checking `check_repl_input_inner` (program.rs:1540-1609):
- `TopLevel::Expr`: calls `infer_expr` (Stage 1), then `resolve_auto_curry`, then `monomorphise_expr_calls`, then `build_repl_result`. **Note: no `resolve_deferred_trait_calls` call.** This is because REPL expressions are typically simple and deferred trait calls are rare, but it means the REPL Expr path differs from the batch path.
- `TopLevel::Defn` (single-sig): calls `check_single_defn` which internally calls `resolve_deferred_trait_calls` (line 1934), then `resolve_auto_curry`, then `monomorphise_expr_calls`. This is adequate.
- `TopLevel::Defn` (multi-sig): delegates to `check_repl_multi_sig` which calls `resolve_deferred_trait_calls` per variant (line 2034), then `resolve_pending_overloads`, then `resolve_auto_curry`. Adequate.

**Gaps in 3.6.5**:
1. `monomorphise_expr_calls` not mentioned (Finding 1, repeated).
2. `check_single_defn` (program.rs:1922) calls `resolve_deferred_trait_calls` on `defn_clone.body()` (line 1934), but `defn_clone` is the mutable clone used for body checking. The AST annotation during `infer_expr` was on this clone. The deferred trait resolution also needs to write to this clone's AST nodes. Currently `resolve_deferred_trait_calls` takes `&Expr` (immutable) -- the `&mut` change described in 3.6.1 would fix this, but the REPL path uses `check_single_defn` which has its own flow separate from `finalize_check_result_inner`. The doc must address this path explicitly.
3. `build_repl_result` (program.rs:2425-2438) calls `resolve_expr_types` (line 2427) which applies substitution to `state.expr_types`. The equivalent AST substitution walk must happen before `build_repl_result` is called. The doc mentions this ("the AST walk replaces this for the annotation path") but does not specify the exact location in the REPL flow.

#### Summary of Findings

| # | Finding | Severity | Location in Doc |
|---|---------|----------|-----------------|
| 1 | `monomorphise_expr_calls` missing from 3.6 | **Blocking** | Add to 3.6.1 and 3.6.5 |
| 2 | Phase 3 loop must iterate stored ASTs, not `working_program` | Important | Clarify in 3.6.3 |
| 3 | REPL `check_single_defn` path not addressed for `&mut` threading | Important | Add to 3.6.5 |
| 4 | `resolve_inner_constrained_calls` not listed in 3.6.1 | Non-blocking | Already in 3.6.4 |
| 5 | Substitution walk pseudocode incomplete (missing Let bindings) | Non-blocking | Covered by reference to resolve_deferred_trait_calls |
| 6 | REPL Expr path has no `resolve_deferred_trait_calls` | Pre-existing | Not introduced by this work |
| 7 | `default_method_defns` not walked by Phase 3 | Pre-existing | Not in `working_program`; may need attention |

**Verdict**: Section 3.6 is structurally sound and correctly diagnoses the root cause. Two findings must be addressed before implementation: (1) add `monomorphise_expr_calls` to the post-pass inventory, and (3) explicitly address the REPL `check_single_defn` path where `resolve_deferred_trait_calls` and final substitution must operate on the annotated clone. The remaining findings are non-blocking or pre-existing.
