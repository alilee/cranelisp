# Ring 2 Completion Report

**Reviewer**: `/review`
**Date**: 2026-03-07
**Scope**: All 7 workspace crates, binary crate, test suite, design docs. Ring 2 spans Sprints 4-8 (5 sprints, ~6000 new lines of implementation, 166 Ring 2 tests).
**Verdict**: **CONDITIONAL PASS** -- 0 Blockers, 5 Important, 9 Suggestions. Conditions listed in Gate Decision.

Ring 2 is functionally complete. Traits, modules, constrained polymorphism, monomorphisation, multi-sig dispatch, and auto-curry are implemented and tested. 1365 tests pass (5 ignored with rationale), all Ring 0 and Ring 1 tests pass unchanged, and the core Ring 2 functionality is solid. The gate is conditional on three issues: clippy has regressed from 0 to 29 warnings, 8 functions exceed the 100-line guideline (worst: 188 lines), and Ring 2 has no design documents for the trait system, module pipeline, or constrained polymorphism.

---

## Tooling Results

### cargo clippy --workspace

**29 WARNINGS.** Regressed from 0 (Ring 1) to 29. This is a degradation from the clean state established at Ring 1. Breakdown by category:

| Category | Count | Crates |
|---|---|---|
| Collapsible if statements | 18 | frontend (2), typecheck (5), backend (7), binary (2), misc (2) |
| Complex type (type_complexity) | 4 | frontend (1), backend (3) |
| Unnecessary Box allocation (replace_box) | 3 | typecheck (3) |
| Simplified map_or | 2 | backend (2) |
| Too many arguments (8/7) | 1 | backend (1) |
| Summary/duplicate warnings | 1 | -- |

The warnings are stylistic, not correctness issues. However, clippy cleanliness is a gate criterion from Ring 0 and Ring 1. The `collapsible_if` warnings are trivially fixable. The `type_complexity` warnings in the backend indicate bare tuple types that should be named structs (e.g., `HashMap<(ModuleFullPath, Symbol), (i64, usize)>` and `Result<(Option<HashMap<...>>, Option<ModuleCodegenState>), ...>`). The `too_many_arguments` warning on `build_compile_context` (8 params vs clippy's default of 7) is a single-instance violation.

### cargo test --workspace

**ALL PASS.** 1365 tests across all crates. 5 ignored with documented rationale.

| Crate / Suite | Passed | Ignored |
|---|---|---|
| cranelisp-types (unit) | 43 | 0 |
| cranelisp-frontend (unit) | 185 | 0 |
| cranelisp-typecheck (unit) | 219 | 0 |
| cranelisp-backend (unit) | 64 | 0 |
| cranelisp-runtime (unit) | 56 | 0 |
| cranelisp (binary, unit) | 38 | 0 |
| ring0 (integration) | 105 | 0 |
| ring1 (integration) | 162 | 0 |
| ring2 (integration) | 166 | 0 |
| rc (integration) | 74 | 3 |
| repl_experience (integration) | 178 | 0 |
| e2e (integration) | 60 | 2 |
| examples (integration) | 15 | 0 |
| **TOTAL** | **1365** | **5** |

**Ring 0-1 regression gate**: All 105 Ring 0 tests pass unchanged. All 162 Ring 1 tests pass unchanged. All 74 passing RC tests pass. All 178 REPL experience tests pass. All 15 example tests pass. The ring is accretive.

**5 ignored tests** (all with documented rationale):

| Test | File | Root Cause | Status |
|---|---|---|---|
| `rc_u1_3_vec_of_option_string` | rc.rs | Vec element drop glue missing for ADT fields with heap children | Sprint 9 scope |
| `rc_u1_3_nested_option_through_function` | rc.rs | Consuming convention missing dec for intermediate heap ADT temps | Sprint 9 scope |
| `rc_u1_5_closure_captures_string_returned` | rc.rs | Closure env lifetime not managed | Sprint 9 scope |
| `e2e_s1_1_bare_type_int` | e2e.rs | REPL treats bare `Int` as variable lookup | Sprint 9 scope |
| `e2e_s1_1_bare_type_bool` | e2e.rs | REPL treats bare `Bool` as variable lookup | Sprint 9 scope |

The 3 RC bugs are Ring 1 infrastructure issues that have been deferred twice (Sprint 8 and now Sprint 9). They are not Ring 2 gate blockers -- they affect RC correctness for heap-nested types, which exists independently of Ring 2 features. The 2 bare-type introspection gaps are REPL experience issues, also scoped for Sprint 9 fix.

---

## What Ring 2 Delivered

### Trait System (Sprint 4-5)

- **Trait declarations**: `(deftrait (Num a) (+ [a a] a) ...)` registers method signatures in `TraitRegistry`. Method-to-trait reverse lookup enables method resolution.
- **Trait implementations**: `(impl Num Int (defn + [x y] (add-i64 x y)))` type-checks bodies against trait signatures with `SelfType` substitution.
- **Default methods**: `Eq.!=`, `Ord.>`, `Ord.<=`, `Ord.>=` synthesize bodies from other trait methods. Default bodies are AST-constructed (not parsed from source).
- **Method resolution**: Two-phase deferred resolution. During body checking, unresolved trait calls are recorded. After all bodies (and after generalization), `resolve_deferred_trait_calls` pins concrete types and produces `ResolvedCall::TraitMethod` entries.
- **Primitive mapping**: `primitive_for_trait_method` in the backend maps known `(Trait, method, Type)` triples to inline Cranelift IR (26 mappings for Num, Eq, Ord). Per arch decision 14.
- **Builtin trait registration**: `Num`, `Eq`, `Ord`, `Display` registered at startup by Rust code in `builtins.rs`. Decision 17 flags this for elimination (move to Cranelisp source).
- **Core trait implementations registered**: 4 primitive types (Int, Float, Bool, String) have Num, Eq, Ord impls. Display registered for Int, Float, Bool, String.

### Constrained Polymorphism and Monomorphisation (Sprint 5)

- **Constraint propagation**: `generalize` collects active constraints from type variables, resolving through the substitution. `Scheme.constraints` maps type var IDs to required traits.
- **Constrained function detection**: Eager detection in Pass 2 (per body, before later call sites pin vars). Cleared if final generalization shows no constraints.
- **Monomorphisation**: `monomorphise_call` instantiates a constrained function with concrete types, re-checks the body, and harvests per-specialization `method_resolutions` and `expr_types`.
- **Batch pipeline**: `pass4_monomorphise` scans non-constrained function bodies for constrained-fn call sites, looks up concrete arg types from `expr_types`, and generates specializations.
- **REPL pipeline**: `monomorphise_expr_calls` handles on-demand monomorphisation for interactive input. Mono defns are compiled and registered before expression evaluation.
- **Inner call handling**: Mono bodies are scanned for recursive/inner constrained-fn calls, which receive their own `SigDispatch` entries.

### Module System (Sprint 6)

- **Module graph discovery**: `discover_module_graph` recursively parses files to extract `(mod name)` declarations, resolves file paths per spec 8.2.5 (child dir, sibling, root, lib), and detects cycles.
- **Topological sort**: Kahn's algorithm produces compilation order (leaves first, entry last). Cycle guard after sort catches any remaining cycles.
- **Multi-file compilation**: `compile_module_graph` processes modules in topo order with a shared `TypeChecker` and shared `Jit`. Cross-module function signatures are accumulated for downstream module declarations.
- **Import processing**: `register_imports` handles Glob, Specific, and aliased imports. Visibility enforcement prevents importing private symbols from outside the module subtree. Ambiguity detection for conflicting bare names.
- **Module-scoped type environments**: `TypeChecker.modules` maps module paths to per-module `SymbolTable`s. `set_current_module` switches context and seeds builtins from the user module.
- **Qualified name resolution**: `lookup` tries local scope, current module, then `module/name` (child-of-current first, then absolute). Visibility checks on private names.

### Multi-Sig Dispatch and Auto-Curry (Sprint 5)

- **Multi-sig functions**: `(defn f ([x] ...) ([x y] ...))` dispatch by arity and type. Mangled names (`f$Int+Int`) distinguish variants.
- **Auto-curry**: Calling a function with fewer args than its arity returns a closure capturing the partial arguments.
- **Resolution pipeline**: Constrained fn detection -> method resolution -> multi-sig name building -> monomorphise -> overload resolution -> final method resolution.

### REPL Extensions (Sprints 4-8)

- **Trait introspection**: `deftrait` and `impl` inputs produce display with module-qualified names.
- **Constrained fn display**: Shows scheme with constraints (e.g., `:(Fn [:Num a :a] a) user/add`).
- **Module-qualified type display**: All types show fully-qualified names (`primitives/Int`, `user/Option`).
- **Snapshot/restore for error recovery**: Typechecker snapshots before each input; restores on error.
- **GOT-based function management**: Each defn compilation creates a new JIT, registers in GOT, and keeps the JIT alive for code pointer validity.

---

## Ring 2 Checklist Evaluation

### Ring 2 Checklist (10 sections, from `ring2-checklist.md`)

| Section | Status | Notes |
|---|---|---|
| 1. Trait System Correctness | **PASS** | Declarations, impls, default methods, method resolution, primitive mapping all working. 26 primitive mappings. Decision 14 correctly implemented. |
| 2. Constrained Poly / Mono | **PASS** | Detection, monomorphisation, per-specialization isolation, constraint verification, SigDispatch, batch/REPL parity. |
| 3. Module System Correctness | **PASS** | Discovery, cycle detection, toposort, imports (glob/specific/alias), visibility, ambiguity, qualified resolution, builtin seeding. |
| 4. Multi-Sig / Auto-Curry | **PASS** | Arity and type dispatch, mangled names, auto-curry closure generation, resolution pipeline. |
| 5. Cross-Module GOT / Codegen | **PASS** | GOT slot management, shared JIT compilation, function signature accumulation, qualified aliases, JIT lifetime. |
| 6. Ring 0-1 Regression | **PASS** | 105 Ring 0 + 162 Ring 1 + 74 RC + 178 REPL + 15 examples = all pass unchanged. |
| 7. RC for Ring 2 Types | **PASS** (with caveats) | Basic trait dispatch RC works. 3 known RC bugs are Ring 1 infrastructure, not Ring 2 regressions. Documented with ignored tests. |
| 8. Code Quality | **CONDITIONAL** | 1 pipeline unwrap, 0 pipeline panics, but 29 clippy warnings and 8 functions exceed 100 lines. See findings I-1, I-2. |
| 9. Design Documentation | **FAIL** | No Ring 2 design docs exist for traits, modules, constrained poly, or cross-module codegen. See finding I-3. |
| 10. Code Structure | **PASS** | TypeChecker decomposed across 7 files via impl blocks. Clear crate boundaries. Named structs for returns. |

### General Checklist (10 sections, from `checklist.md`)

| Section | Status | Notes |
|---|---|---|
| 1. Error Handling | **PASS** | 1 pipeline unwrap in `program.rs:337` (internal invariant, not user input). Zero pipeline panics. Errors carry spans. Warnings are data. |
| 2. Code Structure | **CONDITIONAL** | 8 functions exceed 100 lines (see I-2). Named structs for returns. Dispatch-per-variant pattern maintained. |
| 3. Naming & Type Safety | **PASS** | String newtypes used throughout (Symbol, TraitName, TypeName, ModuleFullPath, JitSymbol, FQSymbol). Named constants. |
| 4. Scope Management | **PASS** | ScopeStack push/pop. No env.clone(). |
| 5. Single Source of Truth | **PASS** | HeapCategory::classify is sole classifier. Type::from_name() centralizes primitive mapping. Single ISA construction. |
| 6. Duplication | **PASS** | Batch/REPL share `monomorphise_call`. `register_defn_signature` shared between batch and REPL. `build_check_for_backend` shared. Minor duplication in monomorphisation result assembly (see S-5). |
| 7. Architectural Boundaries | **PASS** | Crate DAG correct. Backend depends on types+runtime, not typecheck. No circular deps. |
| 7a. Idiomatic Rust | **CONDITIONAL** | `#[must_use]` still missing on backend public functions (carried from Ring 1 F-7). 19 `#[allow(dead_code)]` suppressions. |
| 8. Serialization | **PASS** | Serde derives on boundary types in cranelisp-types. |
| 9. Testing | **PASS** | Every module has unit tests. 166 Ring 2 integration tests. Test names are behavioral. |
| 10. Performance | **PASS** | HashMap lookups for method resolution, module tables, trait registry. No O(n) scans where HashMap suffices. |

---

## Findings

### Important (I) -- Must be addressed or explicitly deferred

#### I-1: Clippy regressed from 0 to 29 warnings

**Severity**: Important
**Location**: 4 crates (frontend, typecheck, backend, binary)
**Description**: Ring 1 had zero clippy warnings. Ring 2 introduces 29. The `collapsible_if` warnings (18) are trivially auto-fixable. The `type_complexity` warnings (4) indicate bare tuple types that violate the named-struct-for-returns convention (checklist section 2). The `replace_box` warnings (3) in `program.rs` indicate unnecessary heap allocations. The `too_many_arguments` warning on `build_compile_context` (8 params) is a single instance.
**Recommendation**: Run `cargo clippy --fix` for the 18 collapsible-if and 2 map_or warnings. Introduce named types for the 4 complex-type sites. Address the 3 replace_box warnings. The too-many-arguments warning should be addressed by grouping the 8 parameters into a context struct.
**Gate impact**: CONDITIONAL -- must be resolved before Ring 2 is declared clean. Trivially fixable.

#### I-2: 8 functions exceed the 100-line guideline

**Severity**: Important
**Location**: Multiple files across pipeline code

| Function | File | Lines | Category |
|---|---|---|---|
| `compile_and_execute` | `src/repl.rs:130` | 188 | REPL compilation dispatch |
| `monomorphise_call` | `typecheck/traits.rs:637` | 149 | Mono generation |
| `register_imports` | `typecheck/checker.rs:428` | 148 | Import processing |
| `run_repl` | `src/repl.rs:1028` | 141 | REPL main loop |
| `emit_inline_drop_glue` | `backend/compiler/mod.rs:442` | 140 | RC drop glue emission |
| `compile_module_graph` | `src/pipeline.rs:435` | 136 | Multi-file compilation |
| `compile_match` | `backend/match_codegen.rs:19` | 128 | Pattern match codegen |
| `compile_data_pattern` | `backend/match_codegen.rs:274` | 116 | Data constructor pattern |

**Description**: The 100-line guideline is a core convention from `src/CLAUDE.md` and the primary lesson from the prototype audit (which had 7 functions exceeding 200 lines, worst at 603). Ring 1 had zero violations (longest was 70 lines). Ring 2 introduces 8 violations.

The worst offender is `compile_and_execute` (188 lines) in `repl.rs`, which is a large match on `ReplInput` variants with per-variant compilation logic. This is a natural decomposition target: each match arm could be a named method (`compile_expr_input`, `compile_defn_input`, `compile_trait_decl_input`, `compile_trait_impl_input`).

`monomorphise_call` (149 lines) handles instantiation, constraint checking, body re-checking, inner-call scanning, and mono defn assembly in one function. It should be decomposed into `instantiate_and_resolve`, `verify_constraints`, and `build_mono_defn`.

`register_imports` (148 lines) has a deeply nested structure with per-import-kind processing. Each `ImportNames` variant's processing could be a named helper.

**Recommendation**: Decompose all 8 functions before Ring 3 work begins. Priority order: `compile_and_execute` (most over limit), `monomorphise_call` (most complex logic), `register_imports` (deepest nesting).
**Gate impact**: CONDITIONAL -- must be decomposed. This is the same class of structural debt that made the prototype unmaintainable.

#### I-3: No Ring 2 design documents

**Severity**: Important
**Location**: `design/typecheck/`, `design/backend/`, `design/frontend/`
**Description**: Ring 2 introduces the trait system (1660 lines), constrained polymorphism with monomorphisation, a complete module pipeline (913 lines), and significant REPL extensions (1788 lines total). None of these have design documents.

Existing design docs cover Ring 0-1 only:
- `design/typecheck/inference.md` -- Ring 0 inference
- `design/typecheck/adt.md` -- Ring 1 ADTs
- `design/backend/ring1-codegen.md` -- Ring 1 codegen
- `design/frontend/reader.md`, `design/frontend/ast-builder.md` -- Ring 0

Missing for Ring 2:
- Trait system design (declaration, implementation, method resolution, default methods, constraint propagation)
- Module pipeline design (discovery, toposort, cross-module compilation, import processing)
- Constrained polymorphism design (detection, monomorphisation, per-specialization isolation)
- Cross-module codegen design (GOT, shared JIT, function signature accumulation)

**Recommendation**: Each compiler skill should document its Ring 2 design. This is important for onboarding and for Ring 3 (which builds on Ring 2's module and trait infrastructure for the macro system).
**Gate impact**: CONDITIONAL -- design docs must be created. Per `design/CLAUDE.md`, "A design doc should be created or updated as part of every implementation task."

#### I-4: Decision 17 remains (interim trait registration)

**Severity**: Important
**Location**: `crates/cranelisp-typecheck/src/builtins.rs` (765 lines)
**Description**: Core traits (`Num`, `Eq`, `Ord`, `Display`) and their implementations for primitive types are registered by ~400 lines of hand-written Rust code in `builtins.rs`. Decision 17 in `design/arch/CLAUDE.md` explicitly flags this as interim: "This violates Principle 8 [...] This can ship immediately." The `deftrait`/`impl` special forms exist and the named primitives are available. There is no technical blocker.

This is not a Ring 2 gate blocker per se -- the traits work correctly. But it is architectural debt that violates a stated principle and should not carry into Ring 3 without conscious acceptance.

**Recommendation**: Scoped for Sprint 9 (task #4). Proceed.
**Gate impact**: Not blocking. Sprint 9 addresses this.

#### I-5: `#[must_use]` missing on backend public Result functions

**Severity**: Important (carried from Ring 1 F-7)
**Location**: `crates/cranelisp-backend/`
**Description**: Backend public functions returning `Result` lack `#[must_use]`. Frontend has it on `parse()` and `build_program()`. Typecheck has it on `check_program()` and `check_repl_input()`. Backend has it on zero public functions. This has been deferred since Ring 1.

**Recommendation**: 5-minute fix. Add `#[must_use]` to `compile_program`, `compile_and_run_expr_with_got`, `compile_module_program`, `Jit::new`, `Jit::compile_defn`, `Jit::finalize`, `Jit::finalize_and_get_ptr`.
**Gate impact**: Not blocking but should be resolved before Ring 3.

### Suggestions (S) -- Non-blocking improvements

#### S-1: `neq-string` maps to an error path in `primitive_for_trait_method`

**Location**: `crates/cranelisp-backend/src/operators.rs:70-76, 212`
**Description**: `primitive_for_trait_method("Eq", "!=", "String")` returns `Some("neq-string")`, and `emit_builtin_op("neq-string", ...)` returns a `CodegenError("neq-string: use str-eq + not instead")`. This means `(!= "a" "b")` will fail at codegen with a confusing internal error message rather than working correctly or producing a clear type error. No test exercises this path.

**Recommendation**: Either implement `neq-string` as a call to `str-eq` + `not`, or return `None` from `primitive_for_trait_method` so the default method body (`(not (= x y))`) is used instead. The latter is preferred -- it lets the default method mechanism handle it.

#### S-2: 19 `#[allow(dead_code)]` suppressions in pipeline code

**Location**: `traits.rs` (8), `compiler/mod.rs` (6), `lib.rs` (2), `scope.rs` (2), `unify.rs` (1)
**Description**: `#[allow(dead_code)]` suppresses compiler warnings about unused code. 19 instances across pipeline crates suggest either (a) code that was written speculatively for later rings, or (b) code that is actually used but the compiler can't see the usage (e.g., fields accessed via `pub(crate)`). The 8 suppressions in `traits.rs` are particularly concerning -- this is the largest new file and multiple methods are marked dead.

**Recommendation**: Audit each suppression. For genuinely future-facing code, add a comment noting which ring/feature will use it. Remove suppressions for code that is actually used.

#### S-3: TODO comments remaining in pipeline code

**Location**: `src/pipeline.rs:254`, `crates/cranelisp-typecheck/src/program.rs:679,702`, `crates/cranelisp-typecheck/src/checker.rs:108`
**Description**: 4 TODO comments in pipeline code. Two are `TODO(Ring 2)` in `program.rs` referring to commented-out `debug_assert!` for Type::Var in expr_types -- Ring 2 has monomorphisation now, so these should be evaluated. One is in `pipeline.rs` noting inline module body extraction is not yet supported. One in `checker.rs` notes the builtin-seeding approach for new modules should use a proper primitives module.

**Recommendation**: Evaluate the two `TODO(Ring 2)` assertions now that monomorphisation exists. The inline module TODO is a known gap (Ring 3 scope). The primitives module TODO is related to Decision 17.

#### S-4: 1 pipeline `unwrap()` in `program.rs:337`

**Location**: `crates/cranelisp-typecheck/src/program.rs:337`
**Description**: `let (param_types, ret_ty) = type_vars.get(&defn.name).unwrap();` in `pass2_check_bodies`. This is an internal invariant (the name was inserted in Pass 1), but the convention is to use `unwrap_or_else(|| unreachable!("invariant: ..."))` for programmer invariants.

**Recommendation**: Replace with `unwrap_or_else(|| unreachable!("invariant: defn name registered in pass1"))`.

#### S-5: Monomorphisation result assembly duplicated between batch and REPL

**Location**: `program.rs` pass4_monomorphise, `repl.rs` compile_and_execute
**Description**: Both the batch path (in `pass4_monomorphise`) and the REPL path (in `compile_and_execute` for mono defns) build per-mono `CheckResult` with merged resolutions and expr_types using nearly identical code. The REPL path has this pattern repeated in both the `Expr` and `TraitImpl` match arms.

**Recommendation**: Extract a `build_mono_check_result` helper shared by both paths.

#### S-6: `compile_and_execute` has 4 match arms for `ReplInput::DefnMulti` that return a "not supported" error

**Location**: `src/repl.rs:253-256`
**Description**: `ReplInput::DefnMulti` returns "multi-signature functions not supported in Ring 0" even though Ring 2 has been implemented. The error message references Ring 0. This suggests the multi-sig REPL path was never wired.

**Recommendation**: Either implement multi-sig in the REPL `compile_and_execute` path, or update the error message to explain what is actually unsupported. Check whether multi-sig works in the REPL via a different code path (the tests pass, so it likely works through a different mechanism).

#### S-7: `TypeChecker` struct has 13 fields

**Location**: `crates/cranelisp-typecheck/src/checker.rs:26-53`
**Description**: The TypeChecker struct has grown to 13 fields spanning inference state (`next_id`, `subst`, `env`, `expr_types`, `method_resolutions`, `warnings`), module state (`modules`, `current_module`, `module_aliases`), type definitions (`type_defs`), and trait state (`trait_registry`, `impl_registry`, `active_constraints`). While the struct is decomposed into impl blocks across 7 files, the field count is approaching the threshold where subsystem grouping would improve clarity.

**Recommendation**: Not urgent. If Ring 3 (macros) adds more fields, consider grouping related fields into sub-structs (e.g., `TraitState { registry, impl_registry, active_constraints }`, `ModuleState { modules, current_module, aliases }`).

#### S-8: `build_default_body` hard-codes AST construction for default methods

**Location**: `crates/cranelisp-typecheck/src/traits.rs:823-898`
**Description**: Default method bodies for `Eq.!=`, `Ord.>`, `Ord.<=`, `Ord.>=` are constructed as hand-built AST in Rust. This is correct and works, but it means adding new default methods requires modifying Rust code. When Ring 3 macros arrive, default method bodies could potentially be specified as Cranelisp source strings.

**Recommendation**: Acceptable for now. Decision 17 elimination (Sprint 9) may address this for the builtin traits. Note for Ring 3: once macros exist, default method bodies in user-defined traits should be parsed from the trait declaration source, not constructed as AST.

#### S-9: Carry forward of Ring 1 deferred items

**Description**: Three items deferred from Ring 1 remain unresolved:

| ID | Item | Original | Status |
|---|---|---|---|
| F-7 | `#[must_use]` on backend public Result fns | Ring 1 | Promoted to I-5 |
| F-10 | `collect_free_vars` duplicates `collect_var_uses` walker logic | Ring 1 | Still deferred. No third consumer added in Ring 2. Low risk due to exhaustive match. |
| F-12 | `emit_rc_dec` null/low-value guard | Ring 1 | Resolved in Ring 2 -- the RC pipeline is now wired and the guard exists (NULLARY_TAG_THRESHOLD check in rc codegen). |

**Recommendation**: F-7 promoted to I-5. F-10 remains deferred (no observable defect). F-12 confirmed resolved.

---

## Test Coverage Assessment

### Unit Tests (Layer 1) -- per crate

| Crate | Tests | Ring 2 Coverage |
|---|---|---|
| cranelisp-types | 43 | Type display (type_var_names), heap classification (unchanged from Ring 1) |
| cranelisp-frontend | 185 | Trait declaration/impl parsing (16 tests), import/export/mod extraction (12 tests), HKT parameter parsing |
| cranelisp-typecheck | 219 | Trait registry (5), trait impl registration (8), monomorphise_call (6), constrained fn detection (4), scheme constraints (3), module-scoped symbol tables (5), import processing (8). +93 over Ring 1's 126. |
| cranelisp-backend | 64 | Primitive trait method mapping (9 tests), GOT slot management (5 tests), cross-module GOT call (1 detailed test). +41 over Ring 1's 23. |
| cranelisp-runtime | 56 | No Ring 2 additions (runtime unchanged) |
| cranelisp (binary, lib) | 38 | Pipeline unit tests (3), module graph discovery (6), toposort (2). +17 over Ring 1's 21. |

**Assessment**: Unit test coverage is strong for the typecheck and backend additions. The typecheck crate's 93 new tests cover the trait system thoroughly. The backend's cross-module GOT test is detailed (100+ lines) but is only one test for a complex subsystem.

### Integration Tests (Layer 3)

| Test File | Tests | Ring 2 Coverage |
|---|---|---|
| ring2.rs | 166 | Traits (21), default methods (10), ADT trait impls (15), constrained poly (10), multi-sig (4), auto-curry (5), annotations (11), modules (6), imports (6), visibility (5), exports (2), ambiguity (15), functor HKT (11), misc (45) |
| rc.rs | 74 (3 ignored) | Unchanged from Ring 1 + 3 additional RC tests for Ring 2 patterns |
| repl_experience.rs | 178 | Ring 2 REPL display, trait introspection, module navigation (+43 over Ring 1's 135) |
| e2e.rs | 60 (2 ignored) | Black-box tests including Ring 2 features |
| examples.rs | 15 | Example 15 (traits) added |

**Assessment**: 166 Ring 2 integration tests is above the test plan target of ~160. Coverage spans all Ring 2 features. The test plan's test list in `tests/plan/ring2.md` is well-populated. Test names describe behavior clearly.

### Acceptance Criteria Verification

From `design/arch/roadmap.md` Ring 2 acceptance criteria:

| Criterion | Status | Evidence |
|---|---|---|
| `(deftrait (Num a) (+ [a a] a) ...)` type-checks | **PASS** | `ring2.rs::trait_decl_basic`, typecheck unit tests |
| `(impl Num Int ...)` works | **PASS** | `ring2.rs::trait_impl_int_num`, `ring2.rs::trait_operator_dispatches_by_type` |
| `(defn add [x y] (+ x y))` monomorphised at call sites | **PASS** | `ring2.rs::constrained_add_int`, `ring2.rs::constrained_add_float`, `ring2.rs::constrained_add_both_types` |
| `(import [core.option [*]])` cross-module import | **PASS** | `ring2.rs::import_specific_names`, `ring2.rs::import_glob`, `ring2.rs::example_imports` |
| Multi-sig dispatch | **PASS** | `ring2.rs::multi_sig_different_arities`, `ring2.rs::multi_sig_type_based_dispatch` |
| Auto-curry `(map (+ 1) [1 2 3])` | **PASS** | `ring2.rs::auto_curry_simple`, `ring2.rs::auto_curry_higher_order` |
| `/stdlib` trait definitions compile | **PASS** (partial) | Builtin traits compile. Stdlib deferred to Ring 3 macros. |
| ~150 additional integration tests | **PASS** | 166 Ring 2 integration tests (target was ~150). Total delta from Ring 1: 586 tests (779 -> 1365). |

---

## Design Documentation Assessment

| Skill | Directory | Ring 2 Status | Notes |
|---|---|---|---|
| `/frontend` | `design/frontend/` | **Unchanged** | reader.md and ast-builder.md cover Ring 0. No Ring 2 doc for module extraction or trait/impl parsing. |
| `/typecheck` | `design/typecheck/` | **MISSING** | inference.md and adt.md cover Ring 0-1. No doc for trait system (1660 lines), constrained poly, module type environments. |
| `/backend` | `design/backend/` | **MISSING** | ring1-codegen.md covers Ring 1. No doc for trait method primitive mapping, cross-module GOT, mangled names. |
| `/platform` | `design/platform/` | **Adequate** | runtime.md unchanged (runtime had no Ring 2 additions). |
| `/arch` | `design/arch/` | **Current** | CLAUDE.md updated with decisions 14-19. roadmap.md has Ring 2 criteria. interfaces.md has Ring 2 types. |

**Assessment**: `/arch` kept its design docs current with Ring 2 decisions. The compiler skills (`/typecheck`, `/backend`, `/frontend`) did not produce Ring 2 design documents. This is a gap -- the trait system (1660 lines, largest new file) and module pipeline (913 lines) are complex enough to warrant design docs for future maintainability.

---

## Audit Debt Verification

Checked that no HIGH prototype audit findings were reintroduced:

| Audit Finding | Status |
|---|---|
| codegen HIGH-1: FnCompiler init duplication | **Clean** -- `FnCompiler::inner()` constructor maintained |
| codegen HIGH-2: Duplicated heap classification | **Clean** -- `HeapCategory::classify()` is sole authority |
| codegen HIGH-3: Vec ops complexity | **Present but contained** -- `compile_vec_set_cow` at 114 lines (Ring 1 addition, not Ring 2) |
| codegen HIGH-4/HIGH-5: 200+ line functions | **DEGRADED** -- 8 functions exceed 100 lines, worst at 188. See I-2. |
| module HIGH-1: CompiledModule god object | **Clean** -- per-module SymbolTable, no god object |
| typechecker HIGH-3: clone-to-avoid-borrow | **Clean** -- borrow-splitting via impl blocks across files |
| typechecker HIGH-4/HIGH-5: panics in pipeline | **Clean** -- 1 panic (runtime panic handler, intentional), 1 unwrap (invariant) |
| cache HIGH-2: ISA constructed separately | **Clean** -- single ISA construction point maintained |

**Assessment**: The audit debt check reveals one regression: long functions. Ring 1 closed with zero functions over 100 lines (longest was 70). Ring 2 has 8 violations. While none approach the prototype's extremes (603 lines), the trend must be reversed before Ring 3 adds macro infrastructure.

---

## FIXME Scan

### Implementation source code (`crates/`, `src/`)

**CLEAN.** Zero FIXME comments in any `.rs` file.

### Spec and design documents

Active FIXMEs (as documented in `sprints/SPRINT.md`):

| Location | Owner | Issue | Gate Relevant? |
|---|---|---|---|
| `design/arch/roadmap.md:7` | /arch | U0.1 batch hello-world needs IO | No (Ring 4) |
| `design/arch/roadmap.md:39` | /qa | REPL non-conformance (12 items) | No (10/12 fixed, 2 in Sprint 9) |
| `design/arch/roadmap.md:57` | /backend | Missing string primitives | No (Ring 3) |
| `repl/spec.md:5` | /repl | CLI invocation modes | No (Ring 4) |
| `repl/spec.md:22` | /qa | Bare type name lookup | Sprint 9 scope |
| `tests/plan/ring0.md:3` | /qa | U0.2 /learn tutorial | No (Ring 4) |
| `typecheck/plan-typecheck.md:478` | /typecheck | Borrow-splitting doc | Deferred |
| `user/plan-docs.md:236,238` | /repl, /arch | Stale RESOLVED FIXMEs | Sprint 9 cleanup |

**Assessment**: No FIXMEs block the Ring 2 gate. All are either deferred to later rings, scoped for Sprint 9, or stale resolved items.

---

## Outstanding Issues

### Conditions for Ring 2 gate passage (must be resolved)

1. **I-1: Fix 29 clippy warnings.** Run `cargo clippy --fix` for auto-fixable warnings. Introduce named types for complex-type warnings. Address `replace_box` and `too_many_arguments`. Target: zero warnings.

2. **I-2: Decompose 8 oversized functions.** Priority: `compile_and_execute` (188 lines), `monomorphise_call` (149 lines), `register_imports` (148 lines). All 8 must be under 100 lines.

3. **I-3: Create Ring 2 design documents.** At minimum: trait system design, module pipeline design. Constrained poly and cross-module codegen design docs are also needed.

### Non-blocking (carry forward or already scoped)

4. **I-4: Decision 17 elimination.** Sprint 9 task #4. Not a Ring 2 gate blocker.

5. **I-5: `#[must_use]` on backend public functions.** Carried from Ring 1. Should be resolved in Sprint 9.

6. **S-1: `neq-string` error path.** Low risk (no test exercises it, default method body would work if `primitive_for_trait_method` returned `None`). Fix when touching operators.rs.

7. **S-2: 19 `#[allow(dead_code)]` suppressions.** Audit during Sprint 9 cleanup.

8. **S-4: 1 pipeline unwrap.** Minor style issue. Fix when touching program.rs.

9. **S-6: DefnMulti "Ring 0" error message in REPL.** Fix when touching repl.rs.

10. **3 RC bugs** (ignored tests). Sprint 9 task #2. Ring 1 infrastructure, not Ring 2 regressions.

11. **2 bare-type introspection gaps** (ignored tests). Sprint 9 task #3.

---

## Gate Decision

**CONDITIONAL PASS.**

Ring 2 satisfies all functional gate criteria. The trait system, module pipeline, constrained polymorphism, multi-sig dispatch, and auto-curry all work correctly with comprehensive test coverage. All prior-ring tests pass unchanged. The ring is accretive.

Three conditions must be met before Ring 2 is declared fully closed:

| Condition | Criterion | Effort |
|---|---|---|
| **C-1**: Clippy clean | Zero warnings across all crates | Small (most auto-fixable) |
| **C-2**: No function > 100 lines | All 8 oversized functions decomposed | Medium (mechanical decomposition) |
| **C-3**: Ring 2 design docs exist | At minimum: trait system + module pipeline | Medium (document existing code) |

These conditions are Sprint 9 scope. Once met, Ring 2 is PASS and the project is ready for Ring 3 (Meta: macros, derive, standard library).

| Gate Criterion | Satisfied |
|---|---|
| All ring features implemented and tested | Yes -- traits, modules, constrained poly, multi-sig, auto-curry |
| No Blocker findings | Yes -- 0 Blockers |
| Important findings acknowledged | Yes -- 5 Important, 3 are gate conditions, 2 are deferred/scoped |
| All tests pass | Yes -- 1365 passed, 0 failed, 5 ignored (with rationale) |
| Clippy clean | **No** -- 29 warnings (C-1) |
| No function > 100 lines | **No** -- 8 violations (C-2) |
| Design docs current | **No** -- Ring 2 design docs missing (C-3) |
| Prior ring regression gate | Yes -- all Ring 0, Ring 1, RC, REPL, example tests pass unchanged |
| Audit debts not reintroduced | Mostly -- long functions (HIGH-4/5) partially regressed |
| Deferred items tracked | Yes -- F-7 promoted to I-5, F-10 still deferred, F-12 resolved |
| ~150 additional integration tests | Yes -- 166 Ring 2 tests (586 total delta) |

---

## Recommendations for Ring 3

1. **Resolve all three gate conditions before beginning Ring 3 work.** Clippy, function length, and design docs. These are Sprint 9 tasks.

2. **Fix the 3 RC bugs.** These have been deferred twice. Sprint 9 task #2 addresses them. They should not carry into Ring 3.

3. **Eliminate Decision 17.** Move core trait definitions to Cranelisp source. Sprint 9 task #4.

4. **Add `#[must_use]` to backend public functions.** Sprint 9 or early Ring 3. 5-minute fix.

5. **Watch TypeChecker field count.** At 13 fields, it is approaching the point where subsystem grouping would help. Ring 3 will add macro-related state. Plan the grouping before the fields proliferate.

6. **Fix `neq-string` before it causes a user-facing bug.** Either implement it or remove the mapping so the default method body handles it.

7. **Evaluate the two `TODO(Ring 2)` debug assertions.** Monomorphisation exists; decide whether the "no Type::Var in expr_types" invariant should activate now.

---

## Next Skills

- `/sprint` -- Assess gate conditions and plan resolution within Sprint 9 Wave 2
- `/typecheck` -- Fix clippy warnings in typecheck crate; decompose `monomorphise_call` (149 lines) and `register_imports` (148 lines); create trait system design doc
- `/backend` -- Fix clippy warnings in backend crate; decompose `emit_inline_drop_glue` (140 lines), `compile_match` (128 lines), `compile_data_pattern` (116 lines); add `#[must_use]`; fix `neq-string`; create cross-module codegen design doc
- `/qa` -- Decompose `compile_and_execute` (188 lines) and `run_repl` (141 lines) in repl.rs; decompose `compile_module_graph` (136 lines) and `discover_module_recursive` (109 lines) in pipeline.rs; fix clippy in binary crate
- `/arch` -- Review Ring 3 macro design; no gate condition changes needed (arch docs are current)
