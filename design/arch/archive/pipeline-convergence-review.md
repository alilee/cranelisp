# Pipeline Convergence Review: Batch/REPL Dual-Pipeline Architectural Defect

**Author:** `/arch`
**Date:** 2026-03-25
**Status:** Architectural review v2 — actionable findings
**Revision:** Added §6.3–6.5 (interfaces.md, review process, sketch influence), updated §8 (interfaces.md remediation)

## 1. Executive Summary

The Cranelisp reimplementation has three parallel compilation pipelines where one was intended. The architecture specified a single `compile_unit()` entry point with a `CompileMode` parameter (Decision 7), but the implementation evolved three divergent paths: (1) whole-program batch (`check_program` + `compile_program`), (2) per-form interactive (`check_repl_input` + `compile_expr_with_got`), and (3) per-form batch via `CompilationSession::compile_form` (which uses `check_repl_input` despite being called from batch module compilation). The type system reflects this split: `TopLevel` and `ReplInput` are structurally identical except `ReplInput` adds an `Expr` variant, and `CheckResult` and `ReplCheckResult` carry the same fields with `ReplCheckResult` adding `ty` and `scheme`. This duplication creates a maintenance trap: features implemented in one path silently fail in another. The `DefnMulti` stub — erroring in all per-form paths and silently skipped in batch — is the known instance, but the pattern makes other divergences likely as the system grows.

This defect has three contributing causes beyond the implementation itself: the design book (`interfaces.md`) enshrined the duplication as legitimate architecture, the `/review` skill never flagged it because the design book said it was correct, and the sketch prototype had the exact same structural problem — which was then copied into the reimplementation despite being listed in the sketch's own audit as a debt to avoid.

## 2. Pipeline Flow Diagrams

### 2.1 Current Architecture: Three Pipelines

```
PIPELINE A: Whole-Program Batch (compile_and_run)
═══════════════════════════════════════════════════

  Source text
       │
       ▼
  ┌─────────────────┐
  │  parse()        │  cranelisp-frontend
  │  Sexp → Vec     │
  └────────┬────────┘
           │
           ▼
  ┌─────────────────────────────────────┐
  │  CompilationSession                 │  src/pipeline.rs
  │  process_and_build_program()        │
  │  • defmacro interception            │
  │  • macro expansion                  │
  │  • begin flattening                 │
  │  → builds Vec<TopLevel> (Program)   │  ◄── uses build_program()
  └────────┬────────────────────────────┘
           │
           ▼
  ┌─────────────────────────────────────┐
  │  TypeChecker::check_program()       │  cranelisp-typecheck
  │  Input:  &[TopLevel]  (Program)     │
  │  Output: CheckResult                │
  │  • Pass 1: register types, traits,  │
  │    impls, fn signatures             │
  │  • Pass 2: check bodies, generalize │
  │  • Pass 3: detect constrained fns   │
  │  • Pass 4: monomorphise             │
  │  • Pass 5: resolve auto-curry       │
  └────────┬────────────────────────────┘
           │
           ▼
  ┌─────────────────────────────────────┐
  │  compile_program()                  │  cranelisp-backend
  │  Input:  &Program + &CheckResult    │
  │  Output: CompiledProgram            │
  │  • Collect defns from Program       │
  │  • Declare all in JIT               │
  │  • Compile each defn                │
  │  • Find entry, finalize, execute    │
  └─────────────────────────────────────┘


PIPELINE B: Per-Form Interactive (REPL eval_sexp)
═══════════════════════════════════════════════════

  User input (one line)
       │
       ▼
  ┌─────────────────┐
  │  parse()        │  cranelisp-frontend
  │  Sexp → single  │
  └────────┬────────┘
           │
           ▼
  ┌─────────────────────────────────────┐
  │  ReplSession::eval_sexp()           │  src/repl/mod.rs
  │  • defmacro interception            │
  │  • import interception              │
  │  • platform interception            │
  │  • macro expansion                  │
  │  • begin flattening                 │
  │  → builds ReplInput                 │  ◄── uses build_repl_input()
  └────────┬────────────────────────────┘
           │
           ▼
  ┌─────────────────────────────────────┐
  │  TypeChecker::check_repl_input()    │  cranelisp-typecheck
  │  Input:  &ReplInput                 │
  │  Output: ReplCheckResult            │
  │  • match on variant:                │
  │    Expr → infer + auto-curry + mono │
  │    Defn → register + check + gen    │
  │    TypeDef → register               │
  │    DefnMulti → ERROR STUB           │  ◄── !! not implemented
  │    TraitDecl → register             │
  │    TraitImpl → register + defaults  │
  └────────┬────────────────────────────┘
           │
           ▼
  ┌─────────────────────────────────────┐
  │  build_check_for_backend()          │  src/repl/mod.rs (ADAPTER)
  │  ReplCheckResult → CheckResult      │
  │  • Clones 7 fields                  │
  │  • Drops ty, scheme                 │
  │  • Sets mono_defns = Vec::new()     │  ◄── !! loses mono_defns
  └────────┬────────────────────────────┘
           │
           ▼
  ┌─────────────────────────────────────┐
  │  compile_expr_with_got()            │  cranelisp-backend
  │  Input:  &Expr + &CheckResult       │
  │  OR                                 │
  │  compile_and_register_defn()        │  src/repl/mod.rs (GOT wrapper)
  │  Input:  &Defn + &CheckResult       │
  │  • Per-form JIT, GOT update         │
  └─────────────────────────────────────┘


PIPELINE C: Per-Form Batch (CompilationSession::compile_form)
═════════════════════════════════════════════════════════════════

  Source text (multi-module)
       │
       ▼
  ┌─────────────────────────────────────┐
  │  CompilationSession::compile_form() │  src/pipeline.rs
  │  • Called from module graph pipeline│
  │  → builds ReplInput                 │  ◄── uses build_repl_input()
  └────────┬────────────────────────────┘
           │
           ▼
  ┌─────────────────────────────────────┐
  │  TypeChecker::check_repl_input()    │  ◄── SAME as Pipeline B
  │  (per-form, not whole-program)      │
  │  DefnMulti → ERROR STUB            │  ◄── !! fails here too
  └────────┬────────────────────────────┘
           │
           ▼
  ┌─────────────────────────────────────┐
  │  build_check_for_backend()          │  src/pipeline.rs (free fn)
  │  (second copy of the adapter)       │
  └────────┬────────────────────────────┘
           │
           ▼
  ┌─────────────────────────────────────┐
  │  compile_and_register_defn()        │  src/pipeline.rs (GOT wrapper)
  │  • Per-form JIT, GOT update         │
  └─────────────────────────────────────┘
```

### 2.2 The Fork Point

The fork happens at the **typecheck boundary**:

```
                    ┌──────────────┐
                    │   Frontend   │
                    │  parse()     │
                    │  build_*()   │
                    └──────┬───────┘
                           │
              ┌────────────┼────────────────┐
              │            │                │
              ▼            ▼                ▼
        build_program  build_repl_input  build_repl_input
        → TopLevel     → ReplInput       → ReplInput
              │            │                │
              ▼            ▼                ▼
        check_program  check_repl_input  check_repl_input
        → CheckResult  → ReplCheckResult → ReplCheckResult
              │            │                │
              │            ├── adapter ──►  ├── adapter ──►
              │            │  CheckResult   │  CheckResult
              ▼            ▼                ▼
        compile_program  compile_expr_*   compile_and_register_defn
        (whole-program)  (per-form JIT)   (per-form JIT)
```

The reconvergence point is the **backend**, which always takes `CheckResult` — but `ReplCheckResult` must be adapted first, and the adapter loses information (`mono_defns` is zeroed; they are compiled separately).

### 2.3 Proposed Converged Pipeline

```
PROPOSED: Single Pipeline
══════════════════════════

  Source text (batch or REPL line)
       │
       ▼
  ┌─────────────────┐
  │  parse()        │  cranelisp-frontend
  └────────┬────────┘
           │
           ▼
  ┌─────────────────────────────────────┐
  │  Preprocessing                      │
  │  • defmacro interception            │
  │  • macro expansion                  │
  │  • begin flattening                 │
  │  → Vec<TopLevel>                    │  ◄── ALWAYS build TopLevel
  └────────┬────────────────────────────┘
           │
           ▼
  ┌─────────────────────────────────────┐
  │  TypeChecker::check()               │  cranelisp-typecheck
  │  Input:  &[TopLevel] + CheckMode    │  ◄── ONE type, ONE function
  │  Output: CheckResult                │  ◄── ONE result type
  │  CheckMode::WholeProgram:           │
  │    multi-pass (forward refs, SCCs)  │
  │  CheckMode::Incremental:            │
  │    single-pass (REPL per-line)      │
  └────────┬────────────────────────────┘
           │
           ▼
  ┌─────────────────────────────────────┐
  │  Backend compilation                │  cranelisp-backend
  │  Mode-selected by CompileMode:      │
  │  • Batch → compile_program          │
  │  • Interactive → GOT-based          │
  └─────────────────────────────────────┘
```

## 3. Type Duplication Inventory

### 3.1 `TopLevel` vs `ReplInput`

| Field / Variant | `TopLevel` | `ReplInput` | Notes |
|---|---|---|---|
| `Defn(Defn)` | Yes | Yes | Identical |
| `DefnMulti { name, docstring, variants, visibility, span }` | Yes | Yes | Identical — both have error stubs in typecheck |
| `TraitDecl(TraitDecl)` | Yes | Yes | Identical |
| `TraitImpl(TraitImpl)` | Yes | Yes | Identical |
| `TypeDef { name, docstring, type_params, constructors, visibility, span }` | Yes | Yes | Identical |
| `Expr(Expr)` | **No** | Yes | REPL-only: bare expressions for evaluation |
| Derives `Serialize, Deserialize` | Yes | **No** | `ReplInput` is never serialized |

**Assessment:** `ReplInput` is `TopLevel` plus an `Expr` variant. The `toplevel_to_repl_input()` function in `ast_builder.rs` mechanically converts every `TopLevel` variant to its `ReplInput` counterpart — a field-by-field copy that adds no value and must be kept in sync manually.

### 3.2 `CheckResult` vs `ReplCheckResult`

| Field | `CheckResult` | `ReplCheckResult` | Notes |
|---|---|---|---|
| `method_resolutions: MethodResolutions` | Yes | Yes | Identical |
| `constrained_fn_names: HashSet<Symbol>` | Yes | Yes | Identical |
| `mono_defns: Vec<MonoDefn>` | Yes | Yes | Identical |
| `expr_types: HashMap<Span, Type>` | Yes | Yes | Identical |
| `default_method_defns: Vec<Defn>` | Yes | Yes | Identical |
| `warnings: Vec<Warning>` | Yes | Yes | Identical |
| `type_defs: HashMap<TypeName, TypeDefInfo>` | Yes | Yes | Identical |
| `constructor_to_type: HashMap<Symbol, TypeName>` | Yes | Yes | Identical |
| `ty: Type` | **No** | Yes | REPL-only: display type |
| `scheme: Option<Scheme>` | **No** | Yes | REPL-only: display scheme |

**Assessment:** `ReplCheckResult` is `CheckResult` plus two display fields (`ty`, `scheme`). The `build_check_for_backend` adapter function clones 7 fields and drops these two — an O(n) clone performed on every REPL input that exists only because the types are separate.

### 3.3 `build_check_for_backend` — Two Copies

| Location | Signature | Notes |
|---|---|---|
| `src/pipeline.rs:988` | `pub fn build_check_for_backend(repl_check: &ReplCheckResult) -> CheckResult` | Free function |
| `src/repl/mod.rs:1314` | `fn build_check_for_backend(&self, repl_check: &ReplCheckResult) -> CheckResult` | Method on `ReplSession` |

Both are identical except that one takes `&self` (unused). This is a textbook violation of Principle 7 (single source of truth).

## 4. Function Duplication Inventory

### 4.1 Typecheck Layer

| Batch Function | REPL Function | What it handles |
|---|---|---|
| `check_program(&[TopLevel])` | `check_repl_input(&ReplInput)` | Main entry point |
| `register_type_defs_from_program()` | inline in `check_repl_input` TypeDef arm | Type registration |
| `register_trait_decls_from_program()` | inline in `check_repl_input` TraitDecl arm | Trait registration |
| `register_trait_impls_from_program()` | inline in `check_repl_input` TraitImpl arm | Impl registration |
| `collect_defns()` | N/A (single defn) | Function collection |
| `pass1_register_signatures()` | `register_defn_signature()` | Signature registration |
| `pass2_check_bodies()` | `check_single_defn()` | Body checking |
| `detect_constrained_fns()` | inline check in `check_single_defn` | Constrained fn detection |
| `pass4_monomorphise()` | `monomorphise_expr_calls()` | Monomorphisation |
| `resolve_auto_curry()` | `resolve_auto_curry()` | Auto-curry (shared) |
| `build_check_result()` | `build_repl_result()` | Result construction |

**Key observation:** The batch path has a structured 5-pass pipeline with inter-defn dependencies handled correctly (forward references, cross-defn type unification). The REPL path processes one form at a time and cannot handle multi-defn interactions. This is a genuine semantic difference — but the current implementation duplicates the mechanics rather than abstracting the difference.

### 4.2 Backend/Pipeline Layer

| Batch | Interactive | What it handles |
|---|---|---|
| `compile_program()` | `compile_expr_with_got()` / `compile_and_register_defn()` | Codegen entry |
| `collect_and_declare_defns()` | inline JIT setup | Function declaration |
| `compile_mono_defns()` (backend) | `compile_mono_defns()` (REPL/pipeline) | Mono specialization |
| `find_entry_and_finalize()` | GOT update + execute | Execution |

### 4.3 Pipeline Orchestration Layer

| `src/pipeline.rs` | `src/repl/mod.rs` | What it handles |
|---|---|---|
| `CompilationSession::compile_form()` | `ReplSession::eval_sexp()` | Per-form dispatch |
| `CompilationSession::compile_checked_program()` | `ReplSession::compile_and_execute()` | Post-typecheck dispatch |
| `build_check_for_backend()` (free fn) | `build_check_for_backend()` (method) | Adapter |
| `CompilationSession::compile_mono_defns()` | `ReplSession::compile_mono_defns()` | Mono compilation |
| `CompilationSession::compile_and_register_defn()` | `ReplSession::compile_and_register_defn()` | GOT defn compilation |

## 5. Gap Analysis

### 5.1 `DefnMulti` — Broken in All Paths

**Evidence:** Three independent error stubs:
- `cranelisp-typecheck/src/program.rs:113` — `check_repl_input` returns error
- `src/pipeline.rs:501` — `CompilationSession::compile_form` returns error
- `src/repl/mod.rs:944` — `compile_and_execute` returns error

**Batch check_program path:** `collect_defns()` at line 218 silently skips `DefnMulti` variants (the `filter_map` returns `None` for non-`Defn` items). The backend's `collect_and_declare_defns` does the same. So `DefnMulti` is not implemented in `check_program` either — it simply gets silently ignored rather than erroring.

**Impact:** Multi-signature functions do not work in any pipeline path in the reimplementation. The spec annotation `[Tested]` on §5.1.2 points to a negative test and a display test — neither exercises actual dispatch.

### 5.2 `TraitDecl` — Functional in Both Paths

- Batch: `register_trait_decls_from_program()` iterates program, calls `register_trait_decl()`.
- REPL: `check_repl_input` TraitDecl arm calls `register_trait_decl()`.
- Both call the same shared method. **No gap.**

### 5.3 `TraitImpl` — Functional in Both Paths

- Batch: `register_trait_impls_from_program()` iterates program, calls `register_trait_impl()`.
- REPL: `check_repl_input` TraitImpl arm calls `register_trait_impl()`.
- Both call the same shared method. **No gap.**

### 5.4 `TypeDef` — Functional in Both Paths

- Batch: `register_type_defs_from_program()` iterates program, calls `register_type_def()`.
- REPL: `check_repl_input` TypeDef arm calls `register_type_def()`.
- Both call the same shared method. **No gap.**

### 5.5 Constrained Polymorphism — Semantic Difference

- Batch (`check_program`): Pass 2 checks all bodies first, then generalizes. Eagerly detects constrained fns during body checking so later call sites don't pin type vars. This handles inter-defn constraint propagation correctly.
- REPL (`check_single_defn`): Processes one defn in isolation. Cannot detect that a function is constrained based on how other functions in the same input call it.
- **Gap:** A REPL input with multiple interacting constrained functions (e.g., via `begin` expansion producing multiple defns) may not resolve constraints correctly. However, this is a genuine semantic limitation of incremental compilation, not a bug.

### 5.6 Forward References — Semantic Difference

- Batch (`check_program`): Pass 1 registers all signatures before Pass 2 checks bodies. Forward references work.
- REPL (`check_repl_input`): One form at a time. Forward references do not work (the referenced function must be defined in a prior input).
- **Gap:** This is also a genuine semantic limitation. The REPL handles this by loading modules via `check_program` (the `compile_module_graph` path uses batch typecheck), and only per-line user input uses `check_repl_input`.

### 5.7 `build_check_for_backend` — Drops `mono_defns`

Both copies of `build_check_for_backend` set `mono_defns: Vec::new()`. This is intentional: `MonoDefn` is not `Clone`, and mono defns are compiled separately via `compile_mono_defns()`. However, the separate handling means the mono compilation path must be manually called at every site — and forgetting to do so would silently produce broken code. Currently both REPL and pipeline do call it, but it's a fragile pattern.

### 5.8 Backend `CompileMode` Branching — Not a Gap

The backend uses `CompileMode` in two places:
- `compile_apply` and `compile_run_tests`: choose between direct calls (`Batch`) and GOT-indirect calls (`Interactive`).
- `compile_trace`: skip GOT-swap in Batch mode.

These are intentional and correct — they handle a genuine compilation strategy difference (direct vs indirect calls). This is exactly what `CompileMode` was designed for.

## 6. Root Cause Analysis

### 6.1 How Decision 7 Failed

Decision 7 specified: *"batch and REPL share `compile_unit()`, no dual pipelines"*. The architecture document shows `compile_unit()` as the single entry point with `CompileMode` parameter.

**What happened:**

1. **`compile_unit()` was never implemented.** The architecture specified it as the binary crate's single pipeline entry point. Instead, three separate orchestration paths emerged: `compile_and_run()`, `CompilationSession::compile_form()`, and `ReplSession::eval_sexp()`.

2. **The typecheck crate created two entry points.** `check_program` and `check_repl_input` were created as separate functions because they address a genuine semantic distinction: whole-program vs incremental checking. But this distinction was modeled as two parallel types (`TopLevel` vs `ReplInput`) rather than as a mode parameter on a single type.

3. **Frontend created a conversion function as a symptom.** `toplevel_to_repl_input()` in `ast_builder.rs` mechanically converts between the two types, demonstrating that they are structurally the same. This function should have been a red flag — its existence proves the types should be unified.

4. **The adapter pattern normalized the split.** `build_check_for_backend()` converting `ReplCheckResult` to `CheckResult` became accepted infrastructure rather than recognized as a code smell. Having two copies of this function (one in pipeline.rs, one in repl/mod.rs) compounded the problem.

5. **Incremental growth hid the divergence.** Each new feature (traits, ADTs, constrained polymorphism, monomorphisation) was added to `check_program` first (for batch tests), then partially ported to `check_repl_input` (for REPL). `DefnMulti` is the case where the port never happened — but the architecture provided no mechanism to detect this.

### 6.2 The Underlying Design Error

The real problem is that the typecheck crate has two fundamentally different compilation strategies:

- **Whole-program** (`check_program`): Sees all definitions at once. Can handle forward references, mutual recursion, and inter-defn constraint propagation.
- **Incremental** (`check_repl_input`): Sees one form at a time. Can only reference previously-defined symbols.

These are genuinely different semantics. The architecture's `CompileMode` enum (`Interactive`, `Batch`, `Release`) controls **codegen strategy** (direct vs GOT-indirect calls), not **typecheck strategy**. The typecheck distinction was overlooked.

However, the typecheck difference does not require separate types. It requires separate orchestration of shared registration and checking primitives.

### 6.3 `interfaces.md` Enshrined the Duplication

The design book (`design/arch/interfaces.md`) documents both `TopLevel` (line 390) and `ReplInput` (line 416) as legitimate boundary types. It even has a section titled "Gap: `ReplCheckResult` Missing Ring 2 Fields" (line 1719) that identified the duplication problem — but proposed **patching the duplicate** rather than eliminating it.

This is the critical process failure. `interfaces.md` is the single source of truth for boundary types (Architectural Principle 2: narrow interfaces). When the design book says "here are two structurally identical types at a pipeline boundary," that should be an architectural violation, not a documented feature. Instead, the duplication was normalised as intentional architecture.

The consequence: every subsequent review — by `/review`, `/arch`, or any skill reading the interfaces document — saw the dual types as correct-by-design. The design book told them it was supposed to be this way.

### 6.4 The `/review` Skill Did Not Catch This

The `/review` skill assesses code quality against the architecture and design documents. When `/review` examined the pipeline, it checked whether the implementation matched the design book. Since `interfaces.md` documented both `TopLevel` and `ReplInput` as boundary types, the dual-pipeline structure appeared compliant. The review process validated the implementation against a design book that had already accepted the duplication.

This reveals a gap in the review process: `/review` checks code against design, but nobody checks design against architectural principles. The design book itself violated Principle 7 (single source of truth) and Principle 2 (narrow interfaces) by documenting two structurally identical types, but no review step catches design-level violations.

**Remediation:** The `/review` checklist should include a design-coherence check: "Do any boundary types in `interfaces.md` have structurally identical counterparts? Do any pipeline entry points in the typecheck or backend crates have parallel implementations for batch vs REPL?" These are architectural invariants that should be verified during every gate review, not just code-level concerns.

### 6.5 The Sketch's Influence

The prototype (`sketch/`) has the exact same structural problem. `sketch/src/ast.rs` defines both `TopLevel` (line 271) and `ReplInput` (line 745) as structurally identical enums, with a mechanical conversion between them. The sketch's own audit (`sketch/CLAUDE.md`) explicitly lists this as a debt to avoid:

> **Dual batch/REPL pipelines** with divergent code paths — single pipeline

Despite this warning, the reimplementation reproduced the same type structure. The ring model's accretive delivery pattern made this easy: Ring 0 needed `Defn` and `Expr`, so someone built `check_repl_input` with two arms based on the sketch's pattern. Each subsequent ring added more arms. The architecture (Decision 7) said "single pipeline," but the sketch's type structure was the template that was actually followed.

This is not a failure of the ring model per se — it is a failure to design each pipeline stage for the **full set of language features** from the start. The ring model manages delivery risk (build the simplest thing first), but it should not drive interface design. The typecheck interface should have been designed in Phase B (scaffold) with one `TopLevel` enum covering all variants the spec requires, even if most arms were initially `todo!()`. Instead, the types were designed for Ring 0's needs and accreted from there.

### 6.6 The Accretive Pattern

The ring model rewarded small, additive changes: add a `TopLevel` variant, add a match arm to `check_program`, add the corresponding arm to `check_repl_input`, make the tests pass, move on. Each individual change was correct and well-tested. But the cumulative effect was three parallel pipelines that nobody designed and nobody reviewed as a whole.

The `DefnMulti` gap is instructive: it was added to `TopLevel` and `ReplInput` (the type definitions), but the `check_program` path silently skips it via `collect_defns()` and the `check_repl_input` path has an error stub. Both omissions are invisible to unit tests because no test exercises multi-sig dispatch end-to-end — the `[Tested]` annotation points to a negative test and a display test, creating a false sense of coverage.

The lesson: accretive feature delivery works for **adding capabilities** but fails for **maintaining structural invariants**. Each ring should have included a structural review: "Does this change maintain the single-pipeline invariant? Are all `TopLevel` variants handled in all paths?" The sprint archetype's Phase 2 (architecture review) exists for exactly this purpose, but it was focused on feature coherence ("does the scope form a testable increment?") rather than structural coherence ("does the implementation still have one pipeline?").

## 7. Risk Assessment

### 7.1 Likelihood of Other Latent Issues

**Medium-high.** The structural pattern that caused the `DefnMulti` gap — feature implemented in `check_program` but stubbed in `check_repl_input` — could recur for any future feature added to `TopLevel`. The current feature set (Defn, TypeDef, TraitDecl, TraitImpl) is covered because the shared primitives (`register_trait_decl`, `register_type_def`, etc.) are called from both paths. But any feature that requires multi-form coordination (like DefnMulti variant expansion) is vulnerable.

### 7.2 Silent Failure Mode

`check_program`'s `collect_defns()` silently skips `DefnMulti` variants. This means a batch program with `DefnMulti` compiles without error but the multi-sig function is simply absent — calls to it will fail with "undefined function" at a different location. This is worse than an error stub because it's harder to diagnose.

### 7.3 Maintenance Burden

Every new `TopLevel` variant requires changes in:
1. `TopLevel` enum definition
2. `ReplInput` enum definition (duplicate)
3. `toplevel_to_repl_input()` conversion
4. `check_program` orchestration
5. `check_repl_input` match arms
6. `build_check_result()` if new fields needed
7. `build_repl_result()` if new fields needed (duplicate)
8. `build_check_for_backend()` adapter (two copies)
9. Backend `collect_and_declare_defns()` filter
10. Pipeline `compile_and_execute()` / `compile_form()` dispatch
11. REPL `compile_and_execute()` dispatch

This is 11 locations across 6 files in 4 crates. Missing any one produces a silent failure or an error stub.

### 7.4 False Coverage Confidence

The `[Tested]` annotation on spec §5.1.2 (Multi-Signature) points to `tests/ring2::neg_multi_sig_bare_value_errors` (a negative test) and `tests/repl_experience::defn_multi_param_reports_full_signature` (a display test). Neither test exercises actual multi-sig dispatch. The annotation creates false confidence that the feature works, while in reality it is broken in every pipeline path. This pattern — testing peripheral behavior (error cases, display) without testing core behavior (dispatch) — can hide gaps in any feature.

## 8. Convergence Proposal

### 8.1 Phase 0: Update `interfaces.md` (Prerequisite)

Before any code changes, `interfaces.md` must be updated to reflect the target architecture. The design book must stop documenting `ReplInput` and `ReplCheckResult` as legitimate boundary types. This ensures that subsequent reviews validate against the correct design.

**Changes to `interfaces.md`:**
- Remove `ReplInput` enum definition (line 416). Replace with a note: "`TopLevel` is used for all pipeline inputs, including REPL. The `Expr` variant handles bare REPL expressions."
- Remove `ReplCheckResult` struct definition (line 1728). Replace with: "`CheckResult` includes an optional `display: Option<CheckResultDisplay>` for REPL display data."
- Update the "Gap: `ReplCheckResult` Missing Ring 2 Fields" section (line 1719) to: "RESOLVED: `ReplCheckResult` eliminated. `CheckResult` is the single result type."
- Add `CheckMode` enum to the typecheck interfaces section.
- Add `Expr(Expr)` variant to the `TopLevel` definition.
- Document the architectural invariant: "The typecheck crate MUST have exactly one entry point (`check`) for type-checking `TopLevel` forms. Separate batch/REPL entry points are an architectural violation."

### 8.2 Phase 1: Unify Types (Low Risk)

**Delete `ReplInput`.** Replace it with `TopLevel` everywhere. The sole difference is `Expr` — handle this by adding `Expr(Expr)` to `TopLevel`:

```rust
pub enum TopLevel {
    Defn(Defn),
    DefnMulti { ... },
    TraitDecl(TraitDecl),
    TraitImpl(TraitImpl),
    TypeDef { ... },
    /// Bare expression (REPL input or module-level effect).
    Expr(Expr),
}
```

This eliminates `ReplInput`, `toplevel_to_repl_input()`, and the `build_repl_input` / `build_top_level` distinction in the frontend.

**Delete `ReplCheckResult`.** Replace it with `CheckResult` plus an optional display payload:

```rust
pub struct CheckResult {
    // ... existing fields unchanged ...

    /// Display information for REPL (None in batch mode).
    pub display: Option<CheckResultDisplay>,
}

pub struct CheckResultDisplay {
    pub ty: Type,
    pub scheme: Option<Scheme>,
}
```

This eliminates `build_check_for_backend()` entirely — the backend ignores the `display` field.

**Changes required:**
- `cranelisp-types/src/ast.rs`: Add `Expr` variant to `TopLevel`, delete `ReplInput`
- `cranelisp-types/src/check.rs`: Merge `ReplCheckResult` into `CheckResult`
- `cranelisp-frontend/src/ast_builder.rs`: Delete `toplevel_to_repl_input()`, delete `build_repl_input`, update `build_top_level` to handle expressions
- `cranelisp-typecheck/src/program.rs`: Delete `check_repl_input`, update `check_program` (see Phase 2)
- `src/pipeline.rs`: Use `CheckResult` directly, delete `build_check_for_backend`
- `src/repl/mod.rs`: Use `CheckResult` directly, delete `build_check_for_backend`

### 8.3 Phase 2: Unify Typecheck Entry Point (Medium Risk)

Create a single `check()` method that handles both whole-program and incremental modes:

```rust
pub enum CheckMode {
    /// Whole-program: register all signatures first, then check all bodies.
    /// Handles forward references and inter-defn constraint propagation.
    WholeProgram,
    /// Incremental: register and check one form at a time.
    /// Used for REPL per-line input.
    Incremental,
}

impl TypeChecker {
    pub fn check(
        &mut self,
        program: &[TopLevel],
        mode: CheckMode,
    ) -> Result<CheckResult, CranelispError> {
        match mode {
            CheckMode::WholeProgram => self.check_whole_program(program),
            CheckMode::Incremental => self.check_incremental(program),
        }
    }
}
```

The key insight is that `check_repl_input` is just `check_program` called with a single-element slice, using the incremental strategy. The shared registration primitives (`register_type_def`, `register_trait_decl`, etc.) are already called identically from both paths.

For the `Expr` variant: wrap it in a synthetic zero-arg `Defn` (the backend already does this in `compile_expr_with_got` — move the wrapping earlier).

**Changes required:**
- `cranelisp-typecheck/src/program.rs`: Refactor to single `check()` entry point
- All callers: pass `CheckMode` parameter

### 8.4 Phase 3: Unify Pipeline Orchestration (Higher Risk, Can Defer)

Consolidate `CompilationSession::compile_form()`, `ReplSession::compile_and_execute()`, and the `compile_and_run()` batch path into a single orchestration function. This is the original `compile_unit()` from the architecture.

This phase is higher risk because the REPL has additional responsibilities (introspection state, trace display, IO formatting, session persistence) that batch does not. These are genuine REPL-specific concerns, not duplicated logic.

**Recommendation:** Defer Phase 3 until Phases 0–2 are stable. The duplication in the pipeline orchestration is less dangerous than the typecheck duplication because it's in a single crate (the binary) under one skill's ownership (`/int`).

### 8.5 Migration Path

Phases 0–2 can be done incrementally:

0. Update `interfaces.md` to reflect the target design (prerequisite — ensures reviews validate against correct architecture)
1. Add `Expr` variant to `TopLevel` (backward compatible — nothing uses it yet)
2. Add `display: Option<CheckResultDisplay>` to `CheckResult`
3. Update `check_program` to handle `Expr` variants (wrap in synthetic defn)
4. Update `check_program` to populate `display` when single-form input
5. Switch REPL callers from `check_repl_input` to `check_program` with single-element slice
6. Delete `ReplInput`, `ReplCheckResult`, `check_repl_input`, `build_check_for_backend`, `toplevel_to_repl_input`
7. Add `CheckMode` parameter to `check_program` (or rename to `check`)

Steps 0–4 are additive (no existing code breaks). Step 5 is the switch-over. Step 6 is cleanup. Step 7 is optional refinement.

### 8.6 Test Impact

- All existing tests continue to pass through steps 0–4 (additive changes).
- Step 5 may require updating REPL tests that assert on `ReplCheckResult` fields — they would use `CheckResult.display.unwrap()` instead.
- No new tests needed for the type unification itself — the behavior is identical.
- New tests SHOULD be added for `DefnMulti` in all paths once the unified pipeline is in place.

### 8.7 Risk of the Change

- **Phase 0 (interfaces.md):** Zero code risk. Design document update only.
- **Phase 1 (type unification):** Low risk. Mechanical refactoring with compiler-enforced correctness (type errors at every missed callsite).
- **Phase 2 (typecheck unification):** Medium risk. The incremental vs whole-program distinction is real and must be preserved. The risk is in subtle behavioral differences (e.g., deferred trait resolution timing) between the two modes.
- **Phase 3 (pipeline unification):** Higher risk, defer.

### 8.8 Review Process Remediation

To prevent similar architectural drift:

1. **`interfaces.md` coherence check.** Every gate review must verify: no structurally identical boundary types exist, no pipeline entry point has parallel batch/REPL implementations.
2. **`/review` checklist update.** Add: "Do any boundary types have structurally identical counterparts? Do batch and REPL paths share the same entry points for typecheck and backend?"
3. **Spec coverage audit.** `[Tested]` annotations must reference tests that exercise **core behavior**, not just peripheral behavior (error cases, display). A feature annotated `[Tested]` with only negative tests is a coverage gap.

## 9. Decision Record

### ADR: Converge Batch/REPL Dual Pipelines

**Decision:** Unify the type system and typecheck entry points to eliminate the dual-pipeline structural defect. Update `interfaces.md` first to ensure the design book reflects the target architecture.

**Context:** The architecture specified a single `compile_unit()` entry point (Decision 7) but the implementation evolved three parallel pipelines with duplicated types (`TopLevel`/`ReplInput`, `CheckResult`/`ReplCheckResult`) and parallel functions. This duplication was enshrined in `interfaces.md` as legitimate architecture, copied from the sketch prototype (which had the same debt), and never caught by `/review` because the design book said it was correct. The pattern caused `DefnMulti` to be implemented in neither path, and creates ongoing risk of feature divergence.

**Resolution:**
0. **Update `interfaces.md`** to document the target: single `TopLevel` (with `Expr`), single `CheckResult` (with optional display), single `check()` entry point with `CheckMode`. Remove `ReplInput` and `ReplCheckResult` definitions.
1. **Merge `ReplInput` into `TopLevel`** by adding an `Expr` variant. Delete `ReplInput` and its conversion functions.
2. **Merge `ReplCheckResult` into `CheckResult`** by adding an optional display payload. Delete `ReplCheckResult` and the adapter functions.
3. **Add `CheckMode` to `check_program`** to distinguish whole-program vs incremental checking. Delete `check_repl_input`.
4. **Defer pipeline orchestration unification** to a later sprint.

**Consequences:**
- Adding a new `TopLevel` variant requires changes in 5 locations (down from 11).
- The `DefnMulti` gap becomes mechanically impossible — any variant handled by `check_program` is automatically handled in all pipeline paths.
- The `build_check_for_backend` adapter and its two copies are eliminated.
- `CompileMode` remains for backend codegen strategy (its intended purpose). `CheckMode` handles the genuine typecheck strategy difference.
- `interfaces.md` becomes the correct design reference, preventing future reviews from validating against a flawed design.

**Tracking:** Sprint backlog item. Blocks `DefnMulti` implementation. Recommended for next sprint's Wave 0 (foundation before features).

**Skills affected:**
- `/arch` — Phase 0 (`interfaces.md` update), review and approve interface changes
- `/typecheck` — Phase 2 (primary implementer)
- `/frontend` — Phase 1 type changes
- `/int` — Phase 1 caller updates, Phase 3 (deferred)
- `/qa` — update tests using `ReplCheckResult`
- `/review` — checklist update for structural invariant checks
