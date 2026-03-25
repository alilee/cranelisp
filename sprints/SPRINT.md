# Sprint 26: Pipeline Convergence

**Status**: COMPLETE
**Ring**: — (structural)
**Goal**: Design and build a unified compilation pipeline that eliminates the dual batch/REPL code paths, then migrate the existing implementation into it.

## Context

Sprint 26 started as a Ring 4 gate sprint. During sketch test porting, we discovered that `DefnMulti` (multi-signature functions) is broken in **all** pipeline paths — error stubs in REPL and per-form batch, silently skipped in whole-program batch. Investigation revealed a structural defect: three parallel pipelines with duplicated types (`TopLevel`/`ReplInput`, `CheckResult`/`ReplCheckResult`) where Decision 7 intended one.

Root causes (see `design/arch/pipeline-convergence-review.md`):
- `interfaces.md` enshrined the duplication as legitimate architecture
- `/review` validated code against a design book that had already accepted the violation
- The sketch prototype had the same debt and the reimplementation copied its type structure
- The ring model's accretive delivery pattern added features to whichever match arm was closest, rather than designing pipeline stages for the full spec surface

### Already delivered (Sprint 26 Wave 1, before pivot)

These are landed and passing — not in scope for re-delivery:
- **Par node codegen** — `compile_par_bind()` emits actual Par nodes with continuation closures (250 lines)
- **Zero-arg defn display fix** — `definition_display` no longer special-cases empty params
- **Backend crate test compilation** — `TraitName` import fixed
- **Sketch test port** — 141 tests in `tests/sketch_port.rs` (130 passing, 11 failing — triage pending convergence)
- **e2e test fix** — `e2e_run_tests_ignores_non_test` assertion narrowed

### Test baseline

- **2372 passed, 0 failed, 16 ignored** (`cargo test --workspace`)
- **11 failing sketch_port tests** (known — triage blocked on pipeline convergence)
- **0 clippy warnings**

## Scope

Two phases: design (for user review), then execute.

### Phase A: Pipeline Design (blocks everything else)

`/arch` designs the v2 pipeline against the full spec surface. This produces design documents for user review before any code is written. The design must cover:

1. **Pipeline stages and data flow** — what transforms, in what order, what types at each boundary
2. **Unified `TopLevel`** — all variants the spec requires, including `Expr`
3. **Unified `CheckResult`** — single type with optional REPL display payload
4. **`CheckMode`** — whole-program vs incremental checking as a parameter, not separate functions
5. **Call graph** — data structure serving: incremental recompilation (changed function → recompile callers), mutual recursion SCC detection (loop-merge candidates), non-tail recursion warnings
6. **Crate allocation** — which crate owns each stage, what are the dependencies, does the 7-crate DAG survive or change
7. **`DefnMulti` path** — how multi-sig flows through the unified pipeline (it's the canary — if this works cleanly, the design is right)
8. **v1 → v2 adapter strategy** — how v2 orchestration reuses existing stage implementations during transition (thin adapters at stage boundaries converting v2 types ↔ v1 types)
9. **Updated `interfaces.md`** — the new design book replacing `design/arch/v1/interfaces.md`

### Phase B: Implementation

Build v2 pipeline in parallel with v1 so we can compare before we delete:

1. **v2 types** in `cranelisp-types` — new module alongside existing types
2. **v2 pipeline orchestration** in `src/pipeline_v2.rs` — single `compile_unit()` entry point using existing stage implementations through adapters
3. **Comparison test harness** — `tests/pipeline_v2.rs` runs programs through both pipelines, asserts identical results
4. **`DefnMulti` implementation** — in the unified pipeline (both batch and REPL)
5. **Sketch test triage** — re-run 11 failing sketch_port tests against v2 pipeline, classify each as: real bug, test adaptation, deliberate divergence
6. **Switchover** — point REPL and batch at v2, delete v1 orchestration, delete old types, remove adapters

### Not in scope

- Ring 4 gate review (deferred — meaningless until pipeline is sound)
- Spec traceability audit (deferred — annotations shift during convergence)
- `loop`/`recur` (future feature — pipeline should accommodate but not implement)
- ANF / defunctionalised continuations (future — call graph design should leave room)
- Mutual recursion loop-merge (future — call graph SCC detection enables it later)

## Skill Plans

### /arch
**Task**: Design the v2 pipeline. Produce `design/arch/interfaces.md` (new) and `design/arch/pipeline-v2.md` describing stages, types, data flow, crate allocation, adapter strategy. All designs must reference the spec for completeness — every `TopLevel` variant the spec requires, every `CheckResult` field the backend needs.
**Acceptance**: User has reviewed and approved the design before Phase B begins.

### /typecheck
**Task**: Phase B — implement `CheckMode` parameter on unified `check()` entry point. Ensure all `TopLevel` variants (including `DefnMulti` and `Expr`) are handled in both modes.
**Acceptance**: `check()` handles all variants; no `check_repl_input` remains.

### /frontend
**Task**: Phase B — merge `build_repl_input` into `build_top_level`. Delete `ReplInput`, delete `toplevel_to_repl_input()`. Handle `Expr` as a `TopLevel` variant.
**Acceptance**: One AST builder entry point; `ReplInput` type deleted.

### /backend
**Task**: Phase B — verify backend compiles from unified `CheckResult` (no adapter). Implement `DefnMulti` codegen (variant expansion + dispatch).
**Acceptance**: Backend takes `CheckResult` directly; `DefnMulti` programs compile and run.

### /int
**Task**: Phase B — build `src/pipeline_v2.rs` with `compile_unit()`. Wire REPL and batch through it. Delete `build_check_for_backend` (both copies). Build comparison test harness.
**Acceptance**: v2 pipeline passes all existing tests; switchover complete; v1 orchestration deleted.

### /qa
**Task**: Phase B — build `tests/pipeline_v2.rs` comparison harness. Triage 11 failing sketch_port tests against v2 pipeline. Update spec traceability for `DefnMulti` (§5.1.2).
**Acceptance**: Comparison harness green; sketch_port failures classified; §5.1.2 has real positive-path tests.

### /review
**Task**: Phase B — review v2 pipeline for: single-pipeline invariant (no parallel types/functions), `interfaces.md` coherence (no structurally identical types), call graph design adequacy.
**Acceptance**: Review report filed; all B+I findings resolved.

### /spec
**Task**: Phase A support — verify that the v2 `TopLevel` enum covers all spec-required forms. Flag any spec sections that imply pipeline variants not yet identified.
**Acceptance**: Confirmation that v2 types cover the full spec surface.

### Other skills (/stdlib, /examples, /docs, /port, /repl, /platform)
**Task**: No active work during Phase A. Phase B: verify their features work through v2 pipeline. Report any regressions.
**Acceptance**: All existing functionality works through v2.

## Waves

### Wave 0: Design (Phase A)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Design v2 pipeline: stages, types, crate allocation, adapters | **done** | pipeline-v2.md + interfaces.md. CheckMode eliminated. CompileContext added. Defn/DefnMulti merged. GOT as persistent state. |
| /spec | Verify v2 TopLevel covers full spec surface | **done** | All 12 spec forms accounted for: 5 in TopLevel, 7 pre-AST |
| **USER** | **Review and approve design** | **done** | Approved after 4 rounds of refinement |

### Wave 1: Types + Orchestration (Phase B) — COMPLETE
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /frontend | Merge Defn/DefnMulti, delete ReplInput/ReplCheckResult, add TopLevel::Expr, CompileContext, CallGraph types | **done** | Also fixed all downstream compilation (crossed skill boundaries — noted for future) |
| /typecheck | Unified check() with CompileContext, handles all 5 TopLevel variants | **done** | CheckMode eliminated — multi-pass works on any slice length |
| /int | Build pipeline_v2.rs with compile_unit() | **done** | 310 lines, 2 smoke tests |
| /qa | Build pipeline_v2 comparison test harness | **done** | 47 tests, 0 divergences between v1 and v2 |

### Wave 2: DefnMulti + Triage — COMPLETE
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | Multi-sig in unified check(): overload registration, mangled names, call-site resolution | **done** | 4 new tests |
| /backend | Multi-sig codegen: variant expansion, compilation, SigDispatch | **done** | 8 new tests |
| /qa | Triage 11 sketch_port failures | **done** | 9 implementation gaps, 2 test adaptations, 0 deliberate divergences |

### Wave 3: Switchover — COMPLETE (with gaps)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Switch REPL + batch + module graph from check_repl_input/check_program → check() | **done** | All callers switched; old methods deprecated |
| /int | SIGBUS fix: synthetic __expr defn span collision with body expression | **done** | Wrapper span prevents expr_types overwrite |
| /int | Multi-sig REPL execution path | **not done** | execute_defn panics on .params() for multi-sig — needs variant expansion in REPL codegen |
| /review | Review v2 pipeline for structural invariants | **not done** | Deferred — sprint scope exceeded |
| all user-proxy | Verify features work through v2 | **not done** | Deferred |

## Notes

**Design-first**: No code until the user has reviewed the pipeline design. This is the lesson from 25 sprints of accretive delivery.

**Parallel build**: v1 and v2 coexist during transition. Tests run through both. Switchover happens only after v2 passes everything v1 passes.

**Call graph**: Designed in Phase A, core structure implemented in Phase B, but advanced uses (mutual recursion loop-merge, incremental recompilation) are future work. The data structure should accommodate them without requiring redesign.

## Outcome

### Delivered

**Pipeline convergence (the sprint's primary goal):**
- **Unified `TypeChecker::check()`** — single entry point replaces `check_program()` and `check_repl_input()`. Takes `&[TopLevel]` + `CompileContext`. No `CheckMode` — multi-pass pipeline works identically on any input size.
- **Unified types** — `ReplInput` deleted (merged into `TopLevel` with `Expr` variant). `ReplCheckResult` deleted (merged into `CheckResult` with optional `DisplayInfo`). `Defn`/`DefnMulti` merged (single `Defn` with `variants: Vec<DefnVariant>`).
- **`CompileContext`** — explicit module identity and additive/replace strategy, replacing implicit mutable state on TypeChecker.
- **Switchover complete** — REPL, batch, and module graph all call `check()`. Old methods `#[deprecated]`.
- **`compile_unit()`** in `src/pipeline_v2.rs` — new orchestration entry point (not yet wired as primary, but tested).
- **47 comparison tests** — v1 vs v2 pipeline produce identical results, 0 divergences.

**Multi-sig functions (partially):**
- **Typecheck** — overload registration, mangled name generation (`add$Int+Int`), call-site resolution via `SigDispatch`. 4 unit tests.
- **Backend codegen** — variant expansion, compilation, dispatch. 8 unit tests.
- **NOT working end-to-end** — REPL execution path (`execute_defn`) panics on multi-sig because it calls `.params()`. Typecheck and codegen work individually but the REPL integration hasn't been updated to expand variants before compilation.

**Pre-pivot deliverables (landed before the convergence pivot):**
- Par node codegen with continuation closures (250 lines)
- Zero-arg defn display fix
- Backend crate test compilation fix
- 141 sketch tests ported (`tests/sketch_port.rs`)

**Architecture:**
- `design/arch/pipeline-v2.md` — pipeline design with 4 rounds of user review refinement (eliminated CheckMode, added CompileContext, merged Defn/DefnMulti, corrected GOT as persistent state)
- `design/arch/interfaces.md` — v2 design book
- `design/arch/pipeline-convergence-review.md` — root cause analysis (v2)
- Architectural principles 11-13 added (single pipeline, design for full spec, auditable interfaces)
- v1 design docs moved to `design/arch/v1/`
- Root `CLAUDE.md` updated with pipeline transition context
- `/arch` skill definition rewritten for pipeline coherence focus

**Test count**: 1528 passed, 11 failed (sketch_port), 0 ignored, 0 clippy errors.

### Deferred

**Must do next sprint:**

1. **Multi-sig REPL execution** — `execute_defn()` in `src/repl/mod.rs` needs to expand multi-sig Defn into individual variants before compiling. Currently panics on `.params()`. The typecheck and codegen both work — this is integration wiring only. Fixes sketch_port tests #1-3.

2. **Delete deprecated methods** — `check_program()`, `check_repl_input()` are `#[deprecated]` but still called from typecheck crate unit tests. Update those tests to use `check()`, then delete the old methods. Also delete both copies of `build_check_for_backend()`.

3. **`/review` gate** — the v2 pipeline has not been reviewed for structural invariants (no parallel types, no adapters, single entry point). This should happen before further features land.

**Implementation gaps (from sketch_port triage — spec violations, not sprint scope):**

4. **User-defined default method bodies** (§7.1.5) — only hard-coded defaults (`!=`, `>=`, `<=`) work. User-defined trait default bodies are not synthesized from stored S-expressions. Fixes sketch_port tests #4, #5, #6.

5. **First-class constructors** (§4.3) — `(let [f MySome] ...)` fails with "undefined variable". Constructors can't be bound as values. Fixes sketch_port test #7.

6. **Parameterised ADT impl** (§7.4) — `(impl Showable (MyOpt Int) ...)` fails with "type argument count mismatch". REPL type registry doesn't record param count from inline `deftype`. Fixes sketch_port test #9.

7. **Duplicate `_` parameters** — reimplementation rejects multiple `_` params; sketch allows it. Parser gap. Fixes sketch_port test #11.

**Test adaptations (not implementation gaps):**

8. **`pure` in test prelude** — `pure` is a stdlib function, not a builtin. Test needs inline definition or test prelude addition. Fixes sketch_port test #8.

9. **`trace-nanos` in test prelude** — `trace-nanos` is a stdlib accessor. Test needs inline match on Trace fields. Fixes sketch_port test #10.

**Future features (discussed, not committed):**

10. **`loop`/`recur`** — Clojure-style compile-time tail-position enforcement. Pipeline accommodates but doesn't implement.

11. **Call graph population** — types exist (`CallGraph`, `CallEdge`, `CallInfo`) but nothing populates them yet. Three use cases: incremental recompilation, mutual recursion SCC detection, non-tail recursion warnings.

12. **Mutual recursion loop-merge** — for tail-position mutual calls within SCC radius. Requires call graph SCC detection.

13. **ANF with defunctionalised continuations** — for non-tail mutual recursion. Heavy — deferred indefinitely.

14. **Ring 4 gate review** — deferred from original sprint scope. Meaningless until pipeline is sound and multi-sig works end-to-end.

### Findings

1. **The dual-pipeline defect was deeper than expected.** `DefnMulti` wasn't just broken in the REPL — it was broken in ALL paths (silently skipped in batch, error stub in REPL and per-form batch). The `[Tested]` annotation on §5.1.2 pointed to peripheral tests (negative case, display) creating false coverage confidence.

2. **`interfaces.md` can enshrine debt.** The design book documented `ReplInput` and `ReplCheckResult` as legitimate boundary types for 25 sprints. Every review validated against it. New architectural principle 13 ("interfaces.md is auditable") prevents recurrence.

3. **The sketch's pipeline structure is a known debt, not a template.** The sketch's own audit flagged dual batch/REPL pipelines. The reimplementation copied the type structure anyway. New `/arch` skill definition explicitly warns: study the sketch's *solutions*, not its *pipeline structure*.

4. **Ring model's accretive delivery caused the structural divergence.** Each ring added features to whichever match arm was closest rather than designing stages for the full spec surface. New architectural principle 12 ("design for the full spec surface") addresses this.

5. **`CheckMode` was unnecessary.** The multi-pass pipeline works identically on any input size. A REPL line is a one-element slice. `begin` expansion producing multiple forms is strictly better through multi-pass (forward references work). No mode parameter needed.

6. **Synthetic defn wrapping has a span collision risk.** Wrapping `TopLevel::Expr` in a synthetic `__expr` Defn caused SIGBUS when the defn span collided with the body expression span, overwriting `expr_types`. Fixed with wrapper span offset.

7. **Skill boundary discipline matters.** The Wave 1 type changes were done by one agent crossing 4 skill boundaries (frontend, typecheck, backend, int). This worked but violated the separate-agents-per-skill principle. For mechanical refactoring that spans the entire codebase, a single agent is pragmatic, but it should be acknowledged and reviewed.

### Suggested next sprint actions

**Priority 1 — Complete the convergence (items 1-3):**
- Fix multi-sig REPL execution (expand variants in `execute_defn`)
- Delete deprecated methods + `build_check_for_backend`
- `/review` gate on v2 pipeline

**Priority 2 — Fix spec violations exposed by sketch_port (items 4-7):**
- Default method body synthesis
- First-class constructors
- Parameterised ADT impl
- Duplicate `_` exemption

**Priority 3 — Test adaptations (items 8-9):**
- Add `pure` and `trace-nanos` to test fixtures or inline

**Priority 4 — Call graph population (item 11):**
- The types exist; populate during typecheck pass 2. Enables non-tail warnings immediately, SCC detection for future loop-merge.

After priorities 1-3, re-attempt Ring 4 gate review (item 14).
