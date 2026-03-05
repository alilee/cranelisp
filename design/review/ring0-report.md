# Ring 0 Completion Report

**Reviewer**: `/review`
**Date**: 2026-03-05
**Scope**: All 7 workspace crates, binary crate, test suite
**Verdict**: **PASS WITH CONDITIONS**

Ring 0 is substantially complete and well-engineered. The codebase demonstrates that the architectural decisions from Phase B were correctly implemented: the 7-crate DAG is clean, audit debts are structurally prevented, and the code quality is high. Three conditions must be addressed before the ring gate is officially cleared.

---

## Tooling Results

### cargo clippy --workspace

**CLEAN.** Zero warnings on library and binary crates. Test crates produce only expected dead-code warnings (helper functions are compiled per-test-binary, so each binary sees unused helpers from other tests). No actionable findings.

### cargo test --workspace

**ALL PASS.**

| Suite | Passed | Ignored | Failed |
|---|---|---|---|
| cranelisp (unit) | 13 | 0 | 0 |
| cranelisp-frontend (unit) | 129 | 0 | 0 |
| cranelisp-typecheck (unit) | 94 | 0 | 0 |
| cranelisp-backend (unit) | 14 | 0 | 0 |
| cranelisp-runtime (unit) | 4 | 0 | 0 |
| cranelisp-types (unit) | 23 | 0 | 0 |
| ring0 (integration) | 91 | 11 | 0 |
| examples (integration) | 8 | 0 | 0 |
| repl_experience (integration) | 56 | 0 | 0 |
| **TOTAL** | **432** | **11** | **0** |

The 11 ignored tests are correctly marked `#[ignore]` for Ring 1 features (lambdas, closures, let-bound polymorphic lambdas). This is proper ring discipline -- the tests document expected Ring 1 behavior without blocking Ring 0 advancement.

---

## Overall Assessment

### What Ring 0 Gets Right

1. **Audit debt prevention is structural, not aspirational.** The 59 prototype audit findings are addressed through code organization, not just "we'll be careful." The typechecker's `infer_expr` is 15 lines (prototype: 603). `check_program` is a readable 3-phase sequence (prototype: 318 lines, 17 phases). `compile_apply` dispatches to extracted helpers. Scope management uses push/pop, not env.clone(). `unify()` takes explicit `&mut Subst` for borrow-splitting.

2. **The single primitive table works.** `ring0_primitives()` in `cranelisp-types/src/operator.rs` is the single authoritative source for all 19 primitives. The typechecker's `register_builtins()` reads from this table. The backend's `emit_builtin_op()` matches on primitive names. No parallel lists, no divergence risk. The table has 11 unit tests verifying count, types, param names, and Cranelift ops.

3. **Error handling is disciplined.** Zero `unwrap()` or `expect()` calls in non-test code across all crates. Every error carries a Span. `CranelispError` implements both `Display` and `std::error::Error`. Warnings accumulate as data, never printed to stderr.

4. **The CompileMode abstraction works.** Batch and Interactive modes share a single pipeline with mode-dependent codegen (direct calls vs. GOT-indirect). The `compile_both()` test helper verifies parity. 10 dual-mode tests confirm identical results.

5. **TCO is correctly implemented.** Loop-based self-TCO with proper tail-position tracking. The `tco_deep_countdown` test with 1,000,000 iterations confirms no stack overflow. Tail position is correctly propagated (if/let/match bodies inherit; args/conditions do not). The loop header block is NOT sealed eagerly (back-edges from tail calls). `seal_all_blocks()` is called after body compilation.

6. **REPL error recovery is solid.** Snapshot/restore on both type errors and parse errors. 7 dedicated error-recovery tests verify that definitions survive errors, multiple errors don't accumulate damage, and typedef state persists through failures.

7. **GOT implementation is clean.** Per-module allocation, monotonic slot assignment, `ensure_slot_for` returns `Result` (no `unwrap`), redefinition tests verify GOT pointer update propagates to callers.

8. **Test coverage is excellent.** 432 tests across unit and integration layers. Every Expr variant, every primitive, every error category, every REPL operation has test coverage. 8 example programs with computed expected values.

---

## Findings

### HIGH (Blocking: must resolve before ring gate)

**H-1: `cranelisp_panic` ABI mismatch between JIT declaration and runtime function**

- **File**: `crates/cranelisp-backend/src/jit.rs` line 88 and `crates/cranelisp-runtime/src/lib.rs` line 16
- **Issue**: The runtime declares `cranelisp_panic(msg_ptr: *const u8, msg_len: usize)` -- two parameters. The JIT declares it with one i64 parameter: `panic_sig.params.push(AbiParam::new(types::I64))`. The call site in `emit_match_panic` passes one argument: `[scrut_val]`. This is an ABI mismatch -- calling a two-parameter C function with one argument is undefined behavior. The second parameter (`msg_len`) receives whatever value happens to be in the register.
- **Impact**: Currently works by accident because the panic handler gracefully handles `msg_len == 0`, and the function immediately diverges via `panic!`. But this is UB on all platforms and could break silently with compiler or ABI changes.
- **Fix**: Either (a) add a second parameter to the JIT declaration and pass `(ptr, len)` for a proper error message, or (b) change the runtime function to accept a single i64 "tag" and produce its own error message, matching the current JIT declaration. Option (b) is simpler for Ring 0 and the current usage (scrut_val is just a discriminator tag). Option (a) is more general for Ring 1+.
- **Owner**: `/backend`

### MEDIUM (Important: should resolve before Ring 1, may defer with rationale)

**M-1: `NULLARY_TAG_THRESHOLD` defined in two locations**

- **Files**: `crates/cranelisp-types/src/pipeline.rs` line 74 and `crates/cranelisp-backend/src/codegen_types.rs` line 12
- **Issue**: Violates architectural principle 7 (single source of truth). Both define `pub const NULLARY_TAG_THRESHOLD: usize = 1024`. If one changes, the other must change too, and nothing enforces this.
- **Fix**: Remove the definition from `cranelisp-backend/src/codegen_types.rs` and have the backend import from `cranelisp_types::NULLARY_TAG_THRESHOLD`. The types crate definition already has the correct comment explaining the sharing rationale.
- **Owner**: `/backend`

**M-2: `CheckResult` has two extra fields beyond `interfaces.md` specification**

- **Files**: `crates/cranelisp-types/src/check.rs` lines 60-64 vs `design/arch/interfaces.md` lines 500-513
- **Issue**: The implementation adds `type_defs: HashMap<TypeName, TypeDefInfo>` and `constructor_to_type: HashMap<Symbol, TypeName>` to `CheckResult`. These are needed by the backend for match codegen against ADTs and are correctly used. However, they are not documented in the design book.
- **Fix**: Update `design/arch/interfaces.md` to include these fields, or file a `<!-- FIXME(/arch) -->` requesting `/arch` evaluate and approve the addition.
- **Owner**: `/arch` (interface change requires `/arch` review per checklist 7b)

**M-3: `Warning` type uses bare `String` message, not `WarningKind` enum**

- **File**: `crates/cranelisp-types/src/error.rs` line 79
- **Issue**: `Warning { message: String, span: Span }` uses a bare string message. Per general checklist 7a, warning types should use an enum `WarningKind` for structured handling.
- **Impact**: Low for Ring 0 (no warnings are currently emitted). Becomes important when Ring 1+ introduces unused-variable warnings, shadowing warnings, etc.
- **Fix**: Define `WarningKind` enum variants as needed. Can defer to Ring 1 when the first warnings are actually emitted, as the current structure has no callers producing warnings.
- **Owner**: `/typecheck` (or `/arch` to specify the warning taxonomy)

**M-4: REPL display format uses short type names, not fully-qualified names**

- **File**: `src/repl.rs` lines 241-253
- **Issue**: `format_result` outputs `:Int 42`, `:Bool true`, `:Float 3.14`. The roadmap acceptance criteria and `repl/spec.md` specify `:primitives/Int 42`, `:(Fn [a] a) user/id`. The REPL experience tests document this gap with comments like "Current format_result uses short names (:Int 3). When qualified names are implemented, update."
- **Impact**: The REPL is functional but does not match the spec for output format. Modules arrive in Ring 2, so full qualification is not implementable yet. However, the `primitives/` prefix could be hardcoded now since it is the only module in Ring 0.
- **Fix**: Either (a) add `primitives/` prefix to `format_result` now and update the 10 display tests in `repl_experience.rs`, or (b) explicitly defer to Ring 2 with rationale that the module system is needed for proper qualification.
- **Owner**: `/repl`

**M-5: No `#[must_use]` annotations on public Result-returning functions**

- **Files**: All public functions across all crates
- **Issue**: Per general checklist 7a, public `Result`-returning functions should have `#[must_use]` to prevent silent error drops. Zero `#[must_use]` annotations exist in the codebase.
- **Impact**: Low in practice because Rust warns on unused `Result` values. But `#[must_use]` is the idiomatic Rust practice for API contracts and makes the expectation explicit.
- **Fix**: Add `#[must_use]` to key public API functions: `parse()`, `build_program()`, `build_repl_input()`, `check_program()`, `check_repl_input()`, `compile_program()`, `compile_and_run()`.
- **Owner**: All compiler skills for their respective crates

**M-6: `not` primitive is not in spec/appendix-a-builtins.md**

- **File**: `spec/appendix-a-builtins.md` (Inline Primitives section lists 18 primitives; `not` is absent)
- **Issue**: The implementation provides 19 inline primitives including `not :: (Fn [Bool] Bool)`. The spec's Appendix A lists only 18 inline primitives (4 int arith + 5 int cmp + 4 float arith + 5 float cmp). `not` is exercised by tests and examples but has no spec authority.
- **Impact**: Either the spec is missing `not` or the implementation has added an extra primitive. `not` is a natural and essential boolean primitive, so this is almost certainly a spec omission.
- **Fix**: File `<!-- FIXME(/spec): Add `not :: (Fn [Bool] Bool)` to Appendix A inline primitives. It is implemented and tested but not documented. -->` in the spec file.
- **Owner**: `/spec`

### LOW (Suggestions: nice-to-have, not blocking)

**L-1: `cranelisp-backend/src/compiler/mod.rs` has no unit tests**

- **File**: `crates/cranelisp-backend/src/compiler/mod.rs` line 270
- **Issue**: The `tests` module is empty with a comment explaining that FnCompiler is tested via integration tests. While the 14 unit tests in `lib.rs` and 91+ integration tests provide strong coverage, the empty test module is a missed opportunity for targeted codegen-level testing (e.g., scope push/pop correctness, variable allocation monotonicity).
- **Impact**: Low -- adequate coverage exists through integration tests.

**L-2: `operators.rs` in backend has no unit tests**

- **File**: `crates/cranelisp-backend/src/operators.rs` line 163
- **Issue**: The `tests` module is empty. Primitive codegen is exercised via integration tests, but the `require_args` helper and error paths could benefit from targeted unit tests that don't require a full Cranelift context.
- **Impact**: Low -- the comment acknowledges this and the integration test suite covers all 19 primitives.

**L-3: `DefCodegen` uses `unsafe impl Send + Sync`**

- **File**: `crates/cranelisp-backend/src/codegen_types.rs` lines 31-32
- **Issue**: `DefCodegen` contains `Option<*const u8>` raw pointers and uses `unsafe impl Send` / `unsafe impl Sync` with a safety comment. The comment is adequate but the pattern is inherently fragile. If `DefCodegen` gains additional pointer fields in later rings, each one must be audited.
- **Impact**: Low for Ring 0 (single-threaded JIT). Worth monitoring as more fields are added in Ring 1+.

**L-4: `parens_balanced` has a subtle behavior with unmatched close parens**

- **File**: `src/repl.rs` line 333
- **Issue**: `parens_balanced` returns `true` when `depth <= 0`, meaning unmatched close parens (e.g., `)hello(`) are treated as "balanced." This is intentional (the parse error is caught by the reader), but the `<=` test could mask real issues in multi-line input.
- **Impact**: Low -- the reader produces proper parse errors for malformed input.

---

## Ring 0 Checklist Evaluation

### Ring 0 Constraints (Section 1) -- ALL PASS

- [x] **No heap allocation in compiled code.** No calls to `cranelisp_alloc` or `cranelisp_free`. No alloc/free func IDs in `FnCompiler` or `Jit`. All Ring 0 types are immediate i64 values.
- [x] **No reference counting.** No `emit_inc`, `emit_dec`, `pop_scope_for_value`, drop glue, or RC tracking in codegen paths.
- [x] **No strings as values.** AST builder rejects `Sexp::Str` in expression position. Backend produces "string literals not supported in Ring 0" error. Docstrings accepted as metadata.
- [x] **No closures.** Backend rejects lambdas with "function values require closures -- not yet supported" error. Lambda tests correctly `#[ignore]`d for Ring 1.
- [x] **Enum-only ADTs.** ADT registry validates no type params and no data constructor fields in Ring 0 (`adt.rs` lines 48-62). Constructor patterns have empty bindings. Match codegen rejects data constructor patterns with bindings.
- [x] **No type parameters on ADTs.** ADT registry rejects type params with clear error message.
- [x] **No trait infrastructure.** No `TraitDecl` or `TraitImpl` processing. REPL correctly rejects these forms. `ResolvedCall::TraitMethod`, `SigDispatch`, `AutoCurry` variants exist in the enum but are never produced.
- [x] **No modules beyond "user".** Single implicit module. No `mod`/`import`/`export` forms.
- [x] **No macros.** Ring 0 uses `NoOpExpander`. The `MacroExpander` trait correctly lives in `cranelisp-types` for dependency inversion.

### Error Handling (Section 2) -- ALL PASS

- [x] `resolve_type_expr` returns `Result`, never panics (7 unit tests).
- [x] No `unwrap()` or `expect()` in non-test code (verified by grep across all crates).
- [x] Builtin registration uses `unreachable!` for invariants.
- [x] Type errors include offending types (e.g., "expected Int, got Bool").

### Code Structure (Section 3) -- ALL PASS

- [x] `infer_expr` is a thin dispatcher (~15 lines in `infer.rs`).
- [x] `compile_expr` follows the same pattern (~50 lines in `compiler/mod.rs`).
- [x] `check_program` is a readable 3-phase sequence (`register_type_defs` -> `pass1_register_signatures` -> `pass2_check_bodies`).
- [x] `infer_apply` has exactly one callee concern in Ring 0 (builtin operator resolution).
- [x] `compile_apply` dispatches to extracted helpers (`compile_direct_call`, `compile_tail_self_call`).

### Scope Management (Section 4) -- ALL PASS

- [x] Scope stack implemented. No `local_env.clone()`. 7 unit tests for scope push/pop/bind/lookup.
- [x] `generalize` scans all scopes plus module level via `scope_stack.free_vars_in_env()`.
- [x] Let bindings do not create new scopes (sequential within current scope).

### Type System (Section 5) -- ALL PASS

- [x] Full `Type` enum defined from Ring 0 (all variants present).
- [x] `Type::from_name()` / `type_name()` are the sole primitive mapping (verified by grep).
- [x] `TypeId` is `u32`.
- [x] Let-polymorphism at `defn` boundary only (test coverage in `ring0.rs` and `program.rs`).
- [x] Operator resolution: Ring 0 uses monomorphic named primitives (not polymorphic scheme). Correct for Ring 0. Ring 2 will add trait dispatch.
- [x] Exhaustiveness checking is a hard error (TypeError).
- [x] `unify()` uses borrow-splitting with explicit `&mut Subst`.
- [x] Backend Int/Float disambiguation: not needed -- Ring 0 uses monomorphic named primitives (`add-i64` vs `add-f64`), so the name alone determines the Cranelift instruction.
- [x] `CranelispError` implements `Display` and `std::error::Error`.
- [x] No `Type::is_heap()` calls in Ring 0 codegen (`HeapCategory::classify()` is the authority).

### Backend (Section 6) -- ALL PASS

- [x] Single ISA construction point (`build_isa()` in `jit.rs`).
- [x] `CompileContext` separates shared from per-function state.
- [x] All i64 ABI (verified in `build_sig()`).
- [x] `icmp`/`fcmp` results are `uextend`ed to i64 (verified in `operators.rs`).
- [x] Float operations use `bitcast` through F64 (verified in `emit_binary_float` and `emit_float_cmp`).
- [x] Loop header NOT sealed eagerly (sealed via `seal_all_blocks()` after body compilation).
- [x] Tail position tracking is correct (propagation documented in `mod.rs` comments, tested by 5 TCO tests including 1M-iteration countdown).
- [x] Inline primitive dispatch handles unary (`not`, 1 arg) and binary (18 primitives, 2 args). `require_args` validates arity.
- [x] `NULLARY_TAG_THRESHOLD` is a named constant (defined, but duplicated -- see M-1).

### GOT and Interactive Mode (Section 7) -- ALL PASS

- [x] GOT allocation is per-module (single `ModuleCodegenState` in Ring 0).
- [x] `ensure_got` returns `&mut` reference via `unwrap_or_else(|| unreachable!(...))`.
- [x] GOT slot assignment is monotonic. Redefinition overwrites pointer at existing slot (tested in `repl_redefinition_updates_callers`).

### REPL Integration (Section 8) -- PASS WITH NOTES

- [x] Error recovery does not corrupt state (7 dedicated tests).
- [x] Cross-boundary error recovery works (snapshot/restore covers both typecheck and codegen failure).
- [ ] `:Type value` output format -- uses short names (`:Int`) not qualified (`:primitives/Int`). See M-4.
- [N/A] Self-documenting REPL entries -- not implemented in Ring 0. No slash commands or symbol introspection. This is explicitly a Ring 4/REPL feature.
- [x] Panic handler uses `panic!()` + `catch_unwind`. Tested in `error_non_exhaustive_match_runtime`.

### Frontend (Section 9) -- ALL PASS

- [x] Reader parses ALL lexical forms (129 reader unit tests cover strings, gensyms, anon_fn, percent params, quasiquote, etc.).
- [x] Token precedence follows spec (negative integers, float-before-int, true/false lookahead all tested).
- [x] Annotation handling is context-correct (parameter and argument annotations tested).
- [x] `Sexp::Symbol` uses bare `String`, not `Symbol` newtype (correct layering).
- [x] Span uses `Span { start: u32, end: u32 }`.

### Cross-Crate Consistency (Section 10) -- PASS WITH NOTES

- [ ] `CheckResult` fields match specification -- has 2 extra fields. See M-2.
- [x] `SymbolTable` has entries for all Ring 0 symbols (primitives, special forms, user functions, types, constructors).
- [x] No type defined in the wrong crate. All boundary types in `cranelisp-types`, all internal types in their owning crate.
- [x] `HeapCategory::classify` correctly handles all types (23 unit tests including future ring types).
- [x] Single operator table is the source of truth (`ring0_primitives()` in `cranelisp-types`).
- [x] `MacroExpander` trait lives in `cranelisp-types` (correct for dependency inversion).

---

## General Checklist Evaluation

### Error Handling (Section 1) -- PASS
All 5 items verified. Zero `unwrap()`/`expect()` in pipeline code. Every error has Span. Warnings are data.

### Code Structure (Section 2) -- PASS
All functions under 100 lines. Max 8 parameters (CompileContext groups shared state). One dispatch method per Expr variant. Named structs for returns.

### Naming and Type Safety (Section 3) -- PASS
String newtypes used correctly (Symbol, TypeName, TraitName, ModuleFullPath, etc.). Named constants for magic numbers. Rust naming conventions followed.

### Scope Management (Section 4) -- PASS
Stack-based scope with push/pop. No leaked bindings (7 unit tests).

### Single Source of Truth (Section 5) -- PASS WITH NOTE
`NULLARY_TAG_THRESHOLD` duplication (M-1) is the one violation. `Type::from_name()`/`type_name()` centralized. No batch/REPL code divergence.

### Duplication (Section 6) -- PASS
No copy-pasted blocks. Shared test helpers in `tests/helpers/mod.rs`. Shared primitive table across crates.

### Architectural Boundaries (Section 7) -- PASS
No circular dependencies (Cargo enforces). Boundary types carry minimum surface area (with M-2 noted). `MacroExpander` trait in correct crate.

### Serialization (Section 8) -- PASS
Serde derives on all cross-boundary types in `cranelisp-types`. Internal types (MonoDefn, FnCompiler) do not derive Serialize. Correct separation.

### Testing (Section 9) -- PASS
Every module has `#[cfg(test)] mod tests` (some empty with explanatory comments). Test names describe behavior. No subsystem at zero coverage. Integration tests in `tests/`.

### Performance Awareness (Section 10) -- PASS
HashMap lookups used appropriately. No O(n) scans where HashMap suffices. No redundant sorting.

---

## Spec Compliance: 19 Primitives

The implementation's 19 primitives match the spec's 18 inline primitives plus one additional:

| Primitive | Spec A.3 | Implementation | Match |
|---|---|---|---|
| `add-i64` | Yes | Yes | OK |
| `sub-i64` | Yes | Yes | OK |
| `mul-i64` | Yes | Yes | OK |
| `div-i64` | Yes | Yes | OK |
| `eq-i64` | Yes | Yes | OK |
| `lt-i64` | Yes | Yes | OK |
| `gt-i64` | Yes | Yes | OK |
| `le-i64` | Yes | Yes | OK |
| `ge-i64` | Yes | Yes | OK |
| `add-f64` | Yes | Yes | OK |
| `sub-f64` | Yes | Yes | OK |
| `mul-f64` | Yes | Yes | OK |
| `div-f64` | Yes | Yes | OK |
| `eq-f64` | Yes | Yes | OK |
| `lt-f64` | Yes | Yes | OK |
| `gt-f64` | Yes | Yes | OK |
| `le-f64` | Yes | Yes | OK |
| `ge-f64` | Yes | Yes | OK |
| `not` | **No** | Yes | **M-6: spec gap** |

All 18 spec primitives have correct type signatures, correct Cranelift instruction mappings, and are tested in both unit and integration tests. The `not` primitive is functional and tested but requires spec documentation.

---

## Roadmap Acceptance Criteria Assessment

| Criterion | Status | Notes |
|---|---|---|
| `(+ 1 2)` -> `:primitives/Int 3` | Partial | Ring 0 uses `add-i64` not `+`. Returns `:Int 3` not `:primitives/Int 3`. Both are by design -- `+` is Ring 2 (trait dispatch), qualified names are Ring 2 (modules). |
| `(defn id [x] x)` -> polymorphic Fn type | PASS | Reports `(Fn [Var(n)] Var(n))` for some n. Tested. |
| `(if true 1 2)` -> `:Int 1` | PASS | Tested in ring0.rs and repl_experience.rs. |
| `(let [x 5] ...)` -> correct result | PASS | Tested with nested lets, shadowing, multiple bindings. |
| `deftype` + `match` -> correct result | PASS | Enum-only ADTs with exhaustive match. Tested in batch and REPL. |
| Factorial runs correctly | PASS | Both recursive and accumulator-style. TCO with 1M iterations. |
| Batch and REPL produce identical results | PASS | 10 `compile_both()` tests verify parity. |
| ~50 integration tests green | PASS | 155 integration tests (91 ring0 + 56 repl_experience + 8 examples). |
| REPL experience tests pass | PASS | 56 REPL experience tests. |
| `cargo clippy` clean | PASS | Zero warnings. |
| No `unwrap()` in pipeline code | PASS | Verified by grep. |

---

## Conditions for Ring Gate Clearance

1. **[MUST] H-1: Fix `cranelisp_panic` ABI mismatch.** Either change the runtime function to accept one i64 parameter (matching the JIT declaration), or change the JIT declaration to pass two parameters. This is undefined behavior and must not persist.

2. **[SHOULD] M-1: Remove `NULLARY_TAG_THRESHOLD` duplication.** Delete from `cranelisp-backend/src/codegen_types.rs` and import from `cranelisp-types`. Single-line fix.

3. **[SHOULD] M-2: Update `interfaces.md` with `type_defs` and `constructor_to_type` fields.** File FIXME to `/arch` or update directly. The fields are correctly needed; the design book needs to reflect reality.

---

## Recommendations for Ring 1

1. **Before starting Ring 1**: Resolve H-1 (panic ABI) and M-1 (duplication). File M-2 to `/arch`.

2. **`Warning` type**: When Ring 1 introduces its first real warning (e.g., unused variable in match), address M-3 by introducing `WarningKind` enum rather than using bare strings.

3. **REPL display format**: When Ring 2 introduces modules, address M-4 by switching to fully-qualified type names. Document the deferral rationale now.

4. **`#[must_use]` annotations**: Add to key public API functions during Ring 1 work. Low effort, high value for API clarity.

5. **`not` spec gap**: File FIXME to `/spec` for M-6. The primitive is correct and tested; the spec needs to catch up.

6. **Closure/lambda infrastructure**: Ring 1 adds closures. The 11 ignored lambda tests become the acceptance criteria. The `compile_lambda` error path in the backend will need to become a full environment-capture codegen path.

7. **Heap classification**: `HeapCategory::classify()` is already correct for all types including future rings. This is good forward engineering -- Ring 1 can start using it immediately.

---

## Per-Crate Assessment

### cranelisp-types

**Assessment**: Excellent.

- 23 unit tests covering types, heap classification, operator table.
- Clean data-only crate. No logic beyond type construction, display, and classification.
- String newtypes correctly generated via `string_newtype!` macro.
- `ring0_primitives()` is well-tested and serves as single source of truth.
- **Suggestion**: `NULLARY_TAG_THRESHOLD` should be the sole definition; remove the copy in `cranelisp-backend`.

### cranelisp-frontend

**Assessment**: Excellent.

- 129 unit tests (reader + AST builder).
- Reader parses all lexical forms from the spec, even non-Ring-0 ones.
- AST builder correctly rejects later-ring forms with clear error messages (quote, quasiquote, gensym, vec, anon_fn, percent params, deftrait, impl, trace).
- Span handling is correct throughout.
- Largest files (reader.rs ~52KB, ast_builder.rs ~74KB) are well-structured with clear sections.

### cranelisp-typecheck

**Assessment**: Excellent.

- 94 unit tests across 8 modules.
- Borrow-splitting pattern correctly implemented (explicit `&mut Subst` parameters).
- `ScopeStack` with 7 unit tests eliminates env.clone() debt.
- Two-pass `check_program` (register signatures, then check bodies) enables forward references.
- ADT registry validates Ring 0 constraints (no type params, no data constructor fields).
- Clean separation: `checker.rs` (195 lines), `infer.rs` (1050 lines), `program.rs` (940 lines).

### cranelisp-backend

**Assessment**: Very Good.

- 14 unit tests + 91+ integration tests.
- `CompileContext` and `MatchContext` structs keep parameter counts manageable.
- Single ISA construction point.
- GOT implementation is clean with 5 unit tests.
- `emit_builtin_op` handles all 19 primitives correctly.
- **H-1**: `cranelisp_panic` ABI mismatch must be fixed.
- **M-1**: `NULLARY_TAG_THRESHOLD` duplication must be fixed.

### cranelisp-runtime

**Assessment**: Good.

- 4 unit tests covering panic with message, null pointer, empty length, and catch_unwind compatibility.
- Minimal Ring 0 footprint (just the panic intrinsic).
- `extern "C-unwind"` correctly chosen for panic propagation through Rust frames.

### cranelisp-platform

**Assessment**: Minimal.

- `ABI_VERSION = 1` and nothing else. Correct for Ring 0.
- No tests (nothing to test).

### cranelisp (binary crate)

**Assessment**: Very Good.

- 13 unit tests across pipeline and REPL.
- `compile_and_run()` correctly orchestrates 5 stages with `infer_result_type`.
- `ReplSession` with snapshot/restore is clean and well-tested.
- `format_result` handles Int/Bool/Float correctly (short names -- see M-4).
- `main.rs` is a stub ("not yet implemented") -- acceptable for Ring 0 where the binary is tested via library API.

---

## Wave 2.5 Findings Follow-Up

The Sprint 1 Wave 2 and Wave 2.5 plans specified structural deliverables. Their resolution status:

| Finding | Status |
|---|---|
| Frontend: reader macros → AST builder rejects | DONE. AST builder rejects all non-Ring-0 forms with clear errors. |
| Frontend: `build_defn` dedup between batch/REPL | DONE. `toplevel_to_repl_input` converts without field-by-field destructuring. |
| Frontend: `Symbol` newtype at Sexp boundary | DONE. `Sexp::Symbol` uses bare `String`; `Symbol` newtype applied at AST builder boundary. |
| Typecheck: shared registration helper | DONE. `register_defn_signature` shared between batch and REPL paths. |
| Typecheck: `HashSet` conversion | DONE. `constrained_fn_names` uses `HashSet<Symbol>`. |
| Backend: compiler.rs split | DONE. Split into `compiler/mod.rs`, `apply.rs`, `control_flow.rs`, `literals.rs`, `match_codegen.rs`. |
| Backend: `CompileContext`/`MatchContext` | DONE. Both structs implemented, reducing parameter counts. |
| Backend: GOT-indirect calls | DONE. Interactive mode uses GOT-indirect `call_indirect`; batch uses direct `call`. |

---

## Audit Findings Disposition

The 59 prototype audit findings (15 HIGH, 23 MEDIUM, 21 LOW) that are relevant to Ring 0 have been structurally addressed:

| Audit Finding | Category | Status |
|---|---|---|
| Typechecker HIGH-1: 603-line `infer_expr` | Structure | ADDRESSED. 15-line dispatcher. |
| Typechecker HIGH-2: 318-line `check_program` | Structure | ADDRESSED. 3-phase sequence. |
| Typechecker HIGH-3: Clone-to-avoid-borrow | Borrow | ADDRESSED. Explicit `&mut Subst`. |
| Typechecker HIGH-4: `resolve_type_expr` panics | Error | ADDRESSED. Returns `Result`. |
| Typechecker HIGH-5: `.expect()` panics | Error | ADDRESSED. Zero `expect()` in pipeline. |
| Typechecker MED-4: env.clone() | Scope | ADDRESSED. ScopeStack push/pop. |
| Typechecker LOW-1: 9 duplicate primitive mappings | SSOT | ADDRESSED. `Type::from_name()`/`type_name()`. |
| Codegen HIGH-1: 21-parameter functions | Structure | ADDRESSED. `CompileContext` struct. |
| Codegen MED-1: `.unwrap()` in codegen | Error | ADDRESSED. Zero `unwrap()` in pipeline. |
| Codegen LOW-1: Magic number 1024 | Naming | ADDRESSED. Named constants. |
| Cache HIGH-2: 3 ISA constructions | SSOT | ADDRESSED. Single `build_isa()`. |
| Module LOW-2: `ensure_got` Option | API | ADDRESSED. Returns `&mut` reference. |

No HIGH audit finding has been reintroduced. The reimplementation structurally prevents the classes of debt found in the prototype.

---

## Next Skills

- `/backend` -- Fix H-1 (cranelisp_panic ABI mismatch) and M-1 (NULLARY_TAG_THRESHOLD duplication)
- `/arch` -- Evaluate and approve M-2 (CheckResult extra fields in interfaces.md)
- `/spec` -- Document M-6 (`not` primitive in Appendix A)
- `/sprint` -- Update sprint tracking with Ring 0 gate status
