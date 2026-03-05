# Sprint 1: Ring 0 — Core

**Status**: COMPLETE
**Ring**: 0 (Core)
**Goal**: Build a working compiler pipeline that evaluates core expressions (Int, Bool, Float, functions, let, if, enum match) end-to-end in both batch and REPL modes.

## Scope

The first implementation sprint. Produces a working `cranelisp` binary that can parse, typecheck, compile, and execute programs using Ring 0 features. No heap allocation, no reference counting, no strings, no closures, no traits, no modules, no macros.

By sprint end, this works:

```
$ cranelisp
> (+ 1 2)
:primitives/Int 3
> (defn fact [n] (if (= n 0) 1 (* n (fact (- n 1)))))
:(Fn [primitives/Int] primitives/Int) user/fact
> (fact 10)
:primitives/Int 3628800
> (deftype Color Red Green Blue)
:Type user/Color
> (match Color.Red [Color.Red 1 Color.Green 2 Color.Blue 3])
:primitives/Int 1
```

~80 integration tests pass. `cargo clippy` clean. No `unwrap()` in pipeline code.

## Waves

Ring 0 is organized in 5 waves. Earlier waves produce artifacts that later waves consume. Within a wave, skills can execute in any order (or in parallel if the user has multiple sessions).

| Wave | Skills | What it produces |
|------|--------|-----------------|
| 1 | `/arch` | `cranelisp-types` crate with Ring 0 boundary types; Ring-0-relevant FIXMEs resolved |
| 2 | `/frontend`, `/typecheck`, `/backend` | Three working crates, independently unit-tested against types from Wave 1 |
| 2.5 | `/review` (x3, parallel) | Per-skill code reviews of `/frontend`, `/typecheck`, `/backend` |
| 3 | `/qa`, `/spec` | Pipeline wired (`compile_unit()`), ~80 integration tests, spec ambiguities resolved |
| 3.5 | `/arch` | Unwind interim operator infrastructure → monomorphic named primitives |
| 4 | `/examples`, `/docs`, `/repl` | Example programs, getting-started tutorial, REPL experience tests |
| 5 | `/review` | Ring 0 completion review; ring gate assessment |

Non-blocking skills (`/stdlib`, `/platform`, `/port`) have lightweight assignments that don't depend on waves.

## Skill Assignments

### /arch
**Input**: `design/arch/interfaces.md`, `design/arch/ring0-interfaces.md`, outstanding FIXMEs
**Task**: Implement `cranelisp-types` crate with all Ring 0 boundary types in Rust. Resolve Ring-0-relevant FIXMEs (operator table, `ReplCheckResult`, `MacroExpander` crate location). Create `src/CLAUDE.md` updates as needed.
**Output**: Compilable `cranelisp-types` crate with: `Sexp`, `Span`, `Expr`, `TopLevel`, `Defn`, `Pattern`, `MatchArm`, `TypeExpr`, `Type`, `TypeId`, `Scheme`, `Subst`, `CheckResult`, `ResolvedCall`, `SymbolTable`, `ModuleEntry`, `DefKind`, `CranelispError`, `CompileMode`, all string newtypes (`Symbol`, `TypeName`, etc.), `string_newtype!` macro. All types derive `Serialize`/`Deserialize`.
**Blocked by**: —
**Wave**: 1
**Acceptance**: `cargo check` passes for `cranelisp-types`. All Ring 0 types from `ring0-interfaces.md` exist with correct fields. String newtypes enforce type safety. `cargo test` passes for any unit tests.

### /frontend
**Input**: `cranelisp-types` (Wave 1), `spec/01-lexical.md`, `spec/02-grammar.md`, `crates/cranelisp-frontend/plan-frontend.md`
**Task**: Implement the S-expression reader (source → `Vec<Sexp>`) and AST builder (`Vec<Sexp>` → `Vec<TopLevel>`) in the `cranelisp-frontend` crate. Reader parses all lexical forms (error on unsupported forms at AST level). AST builder handles Ring 0 forms only: `IntLit`, `FloatLit`, `BoolLit`, `Var`, `Let`, `If`, `Lambda`, `Apply`, `Match`, `Annotate`, `Defn`, `TypeDef`. Define the `MacroExpander` trait (stub, no implementation). Unit tests for parser and AST builder.
**Output**: Working `cranelisp-frontend` crate with `Frontend::parse()` and `Frontend::build()` public APIs.
**Blocked by**: `/arch` (Wave 1)
**Wave**: 2
**Acceptance**: Reader parses all Ring 0 acceptance criteria expressions correctly. AST builder produces correct `Expr`/`TopLevel` variants. Unit tests cover every Ring 0 expression form, operator symbols, whitespace/comment handling, negative integers, and parse error cases. `cargo test -p cranelisp-frontend` passes.

### /typecheck
**Input**: `cranelisp-types` (Wave 1), `spec/03-types.md`, `spec/04-expressions.md`, `spec/05-definitions.md`, `spec/06-pattern-matching.md`, `crates/cranelisp-typecheck/plan-typecheck.md`
**Task**: Implement core type inference in the `cranelisp-typecheck` crate. Algorithm W with unification. Scope management via push/pop (not env.clone()). Type checking for all 10 Ring 0 expression forms. Builtin operators hard-wired with fixed type schemes. Enum-only ADT type definitions. Pattern matching type checking (constructor and wildcard patterns). Exhaustiveness checking for enums. `CheckResult` population. Unit tests.
**Output**: Working `cranelisp-typecheck` crate with `TypeChecker::check()` public API producing `CheckResult`.
**Blocked by**: `/arch` (Wave 1)
**Wave**: 2
**Acceptance**: Correctly infers types for all Ring 0 acceptance criteria. Let-polymorphism works (`id` inferred as `(Fn [a] a)`). Builtin operators resolve correctly. Enum match exhaustiveness checked. Type errors produce `CranelispError` with spans. All unification variables resolved (no `Var` in output). `cargo test -p cranelisp-typecheck` passes.

### /backend
**Input**: `cranelisp-types` (Wave 1), `spec/12-runtime.md`, `crates/cranelisp-backend/plan-backend.md`
**Task**: Implement Cranelift IR codegen and JIT execution in the `cranelisp-backend` crate. Single ISA construction point. `FnCompiler` context struct (not 21-parameter functions). Expression codegen for all Ring 0 forms. GOT for interactive mode. TCO (loop-based self-TCO). Enum-only match codegen (bare i64 tag comparison). JIT module lifecycle. Unit tests for IR generation.
**Output**: Working `cranelisp-backend` crate with `Backend::compile()` and `Backend::execute()` public APIs.
**Blocked by**: `/arch` (Wave 1)
**Wave**: 2
**Acceptance**: All Ring 0 expressions compile to correct Cranelift IR. `(fact 10)` returns `3628800`. TCO exercises: `(fact-acc 100000 1)` completes without stack overflow. Enum match codegen uses tag comparison. GOT works for interactive (redefinition) mode. `cargo test -p cranelisp-backend` passes.

### /qa
**Input**: All three compiler crates (Wave 2), `tests/plan/ring0.md`, `tests/plan/strategy.md`
**Task**: Wire the pipeline in the binary crate: implement `compile_unit()` connecting frontend → typecheck → backend. Implement `compile_and_run_simple()`, `compile_both()`, `assert_type_error()`, `assert_parse_error()`, `repl_session()` test helpers. Write ~80 integration tests covering all Ring 0 features (ported from prototype + new). Implement basic batch mode and REPL loop in `src/main.rs`. Ensure `CompileMode::Batch` and `CompileMode::Interactive` produce identical results.
**Output**: Working `cranelisp` binary with batch and REPL modes. ~80 passing integration tests. Test helpers for all layers.
**Blocked by**: `/frontend`, `/typecheck`, `/backend` (Wave 2)
**Wave**: 3
**Acceptance**: All Ring 0 acceptance criteria pass end-to-end. ~80 integration tests green. Batch and REPL parity verified. Error messages include source spans. `cargo test` passes across the workspace. `cargo clippy` clean. No `unwrap()` in pipeline code.

### /spec
**Input**: Ambiguities discovered during Wave 2-3 implementation
**Task**: Arbitrate any spec ambiguities that arise during implementation. Run examples against the sketch oracle when behavior is unclear. Update spec files as needed. Available on-demand throughout the sprint.
**Output**: Spec updates as needed. Oracle verification results.
**Blocked by**: — (reactive, on-demand)
**Wave**: 3 (available throughout)
**Acceptance**: No unresolved spec ambiguities at sprint close.

### /examples
**Input**: Working pipeline (Wave 3), `examples/plan-examples.md`
**Task**: Write 5-8 Ring 0 example programs that exercise core features: arithmetic, factorial, fibonacci, let bindings, conditionals, enum ADTs, pattern matching, polymorphic functions. Programs validate the compiler from a user's perspective.
**Output**: `examples/01-*.cl` through `examples/08-*.cl` (Ring 0 subset of the learning sequence).
**Blocked by**: `/qa` (Wave 3)
**Wave**: 4
**Acceptance**: All example programs compile and run correctly in both batch and REPL modes.

### /docs
**Input**: Working pipeline (Wave 3), `user/plan-docs.md`
**Task**: Write the getting-started tutorial covering: what is Cranelisp, starting the REPL, evaluating expressions, defining functions, types, let bindings, if expressions, enum types, pattern matching.
**Output**: `user/getting-started.md`
**Blocked by**: `/qa` (Wave 3)
**Wave**: 4
**Acceptance**: Tutorial is accurate against the working compiler. A reader can follow it to write their first Cranelisp program.

### /repl
**Input**: Working REPL (Wave 3), `repl/spec.md`
**Task**: Create REPL experience test harness and write Ring 0 experience tests: prompt display, `/help` command, value+type display format (`:Type value`), error recovery (type error doesn't crash session), basic discoverability.
**Output**: `tests/e2e/` REPL test scripts (or integration tests exercising REPL session API), test harness.
**Blocked by**: `/qa` (Wave 3)
**Wave**: 4
**Acceptance**: REPL displays `:primitives/Int 3` for `(+ 1 2)`. `/help` produces useful output. Type errors are recoverable. All Ring 0 REPL experience tests from `repl/spec.md` pass.

### /review (per-skill, Wave 2.5)
**Input**: Each compiler skill's completed crate (Wave 2)
**Task**: Run `/review` once for each compiler skill — `/frontend`, `/typecheck`, `/backend` — after each completes its Wave 2 work. These three reviews can run **in parallel**. Each review checks the crate against `design/review/ring0-checklist.md` and the relevant prototype audit: no `unwrap()` in pipeline, no `panic!()` on input, max ~100 lines/fn, one method per Expr variant, string newtypes enforced, no env.clone(). Flag issues for the skill to fix before Wave 3 integration.
**Output**: Per-skill review findings (inline or in sprint notes). Issues filed back to the owning skill.
**Blocked by**: The respective compiler skill's Wave 2 completion
**Wave**: 2.5 (after each skill completes, before Wave 3 integration)
**Acceptance**: Each crate reviewed. Issues either fixed or explicitly deferred with rationale.

### /arch (operator unwind, Wave 3.5)
**Input**: All 3 compiler crates + integration tests (Waves 2-3)
**Task**: Remove the interim operator dispatch infrastructure (principle 8 violation). Replace `OperatorCategory`/`BuiltinOperator`/`ring0_operators()`/`operator_scheme()`/`resolve_builtin_operator()` with 20 monomorphic named primitives (`int-add`, `float-add`, `int-eq`, etc.) registered as `DefKind::Primitive`. Update integration tests to use primitive names. These primitives and their tests survive permanently — Ring 2 adds `Num.+` dispatching to `int-add`/`float-add`, and new `(+ 1 2)` tests validate trait dispatch separately.
**Output**: Simplified typecheck + backend (no operator special-cases). Tests using primitive names. ~500 lines of throwaway infrastructure removed.
**Blocked by**: `/qa` (Wave 3)
**Wave**: 3.5 (before Wave 4, so examples/docs build on final primitives)
**Acceptance**: All existing test behaviors preserved (using primitive names). `operator.rs` deleted or reduced to instruction mapping only. No `OperatorCategory`, no `operator_scheme()`, no `resolve_builtin_operator()`. `cargo test --workspace` passes. `cargo clippy` clean.

### /review (ring gate, Wave 5)
**Input**: All Ring 0 code (Waves 1-4), per-skill review findings from Wave 2.5
**Task**: Ring 0 completion review. Holistic assessment across all crates: cross-crate interface consistency, no HIGH audit findings reintroduced, overall code quality. Verify all Wave 2.5 findings were addressed. Write Ring 0 review report.
**Output**: `design/review/ring0-report.md`
**Blocked by**: All above (Waves 1-4)
**Wave**: 5
**Acceptance**: All ring0-checklist items pass. No HIGH audit findings reintroduced. All Wave 2.5 findings resolved. Report filed.

### /stdlib
**Input**: `lib/plan-stdlib.md`
**Task**: Confirm Ring 0 stdlib is empty (validates "optional prelude" principle). Review Ring 0 compiler from stdlib author's perspective — does the type inference, function definition, and enum system look sound for building a stdlib on top of? File any usability findings.
**Output**: Brief review note in sprint outcome. Usability findings if any.
**Blocked by**: — (lightweight, can run anytime after Wave 3)
**Wave**: 4 (lightweight)
**Acceptance**: Confirmation that Ring 0 foundation is sound for stdlib work.

### /platform
**Input**: `crates/cranelisp-runtime/plan-platform.md`, Ring-0-relevant FIXMEs
**Task**: Resolve the panic handler FIXME: commit to `panic!()` + `catch_unwind` for Ring 0 (sound because no nested JIT→Rust→JIT calls yet). Document forward reference to Ring 1+ thread-local error flag. Confirm operator wrapper deferral (Ring 1 when closures enable first-class function values). Implement minimal `cranelisp-runtime` crate with: `cranelisp_panic` intrinsic for match exhaustiveness failure.
**Output**: Minimal `cranelisp-runtime` with panic intrinsic. FIXME resolutions documented.
**Blocked by**: — (can work in parallel with Wave 2)
**Wave**: 2 (parallel with compiler skills)
**Acceptance**: `cranelisp_panic` callable from backend codegen. `cargo test -p cranelisp-runtime` passes.

### /port
**Input**: `exemplar/plan-exemplar.md`, Ring 0 acceptance criteria
**Task**: Review Ring 0 features against Sudoku Solver requirements. Identify which Sudoku Solver components could theoretically be implemented with Ring 0 features (answer: very few — no strings, no ADTs with fields, no collections). Update exemplar plan with Ring 0 observations. No implementation work.
**Output**: Updated `exemplar/plan-exemplar.md` with Ring 0 assessment section.
**Blocked by**: — (lightweight, anytime)
**Wave**: 4 (lightweight)
**Acceptance**: Assessment documented.

## Task List

| # | Wave | Skill | Task | Status | Blocked By |
|---|------|-------|------|--------|------------|
| 1 | 1 | /arch | Implement `cranelisp-types` crate with all Ring 0 boundary types | **done** | — |
| 2 | 1 | /arch | Resolve Ring-0-relevant FIXMEs (operator table, ReplCheckResult, MacroExpander location) | **done** | — |
| 3 | 2 | /frontend | Implement S-expression reader | **done** | ~~1~~ |
| 4 | 2 | /frontend | Implement AST builder (Ring 0 forms) | **done** | ~~1~~ |
| 5 | 2 | /frontend | Define MacroExpander trait (stub) | **done** | ~~1~~ |
| 6 | 2 | /typecheck | Implement Algorithm W (unification, generalization, instantiation) | **done** | ~~1~~ |
| 7 | 2 | /typecheck | Implement type inference for all 10 Ring 0 expression forms | **done** | ~~1~~ |
| 8 | 2 | /typecheck | Implement builtin operator type schemes and resolution | **done** | ~~1~~ |
| 9 | 2 | /typecheck | Implement enum ADT type checking and exhaustiveness | **done** | ~~1~~ |
| 10 | 2 | /backend | Implement Cranelift ISA setup and JIT module lifecycle | **done** | ~~1~~ |
| 11 | 2 | /backend | Implement FnCompiler and expression codegen (all Ring 0 forms) | **done** | ~~1~~ |
| 12 | 2 | /backend | Implement GOT for interactive mode | **done** | ~~1~~ |
| 13 | 2 | /backend | Implement TCO (loop-based self-TCO) | **done** | ~~1~~ |
| 14 | 2 | /backend | Implement enum match codegen (tag comparison) | **done** | ~~1~~ |
| 15 | 2 | /platform | Implement minimal cranelisp-runtime (panic intrinsic) | **done** | — |
| 16 | 2.5 | /review | Review `/frontend` crate (parallel with 17, 18) | **done** | ~~3,4,5~~ |
| 17 | 2.5 | /review | Review `/typecheck` crate (parallel with 16, 18) | **done** | ~~6,7,8,9~~ |
| 18 | 2.5 | /review | Review `/backend` crate (parallel with 16, 17) | **done** | ~~10,11,12,13,14~~ |
| 19 | 3 | /qa | Wire pipeline: compile_and_run() in binary crate | **done** | ~~3,4,5,6,7,8,9,10,11,12,13,14,15~~ |
| 20 | 3 | /qa | Implement test helpers (compile_and_run_simple, compile_both, etc.) | **done** | ~~19~~ |
| 21 | 3 | /qa | Write ~80 integration tests | **done** (91 passing + 11 ignored) | ~~20~~ |
| 22 | 3 | /qa | Implement batch mode and REPL loop in main.rs | **done** | ~~19~~ |
| 23 | 3 | /spec | Arbitrate spec ambiguities (on-demand) | **done** (no ambiguities arose) | — |
| 30 | 3.5 | /arch | Update arch docs: specify primitive-based system replacing operator dispatch | **done** | ~~21~~ |
| 32 | 3.5 | /typecheck | Replace operator registration/resolution with monomorphic primitive registration | **done** | ~~30~~ |
| 33 | 3.5 | /backend | Replace operator codegen with primitive-based instruction mapping | **done** | ~~30~~ |
| 34 | 3.5 | /review | Review typecheck + backend primitive changes | **done** | ~~32,33~~ |
| 31 | 3.5 | /qa | Update integration tests: operator syntax → primitive names | **done** | ~~32,33~~ |
| 24 | 4 | /examples | Write 5-8 Ring 0 example programs | **done** | ~~31~~ |
| 25 | 4 | /docs | Write getting-started tutorial | **done** | ~~31~~ |
| 26 | 4 | /repl | Create REPL experience test harness and Ring 0 tests | **done** | ~~31~~ |
| 27 | 4 | /stdlib | Review Ring 0 compiler from stdlib perspective | **done** | ~~31~~ |
| 28 | 4 | /port | Assess Ring 0 against Sudoku Solver requirements | **done** | — |
| 35 | 3.5b | /arch | Update ring0-interfaces.md: rename primitives to spec names, remove neg | **done** | — |
| 36 | 3.5b | /typecheck | Rename primitives in registration code and tests to spec names | **done** | ~~35~~ |
| 37 | 3.5b | /backend | Rename primitives in codegen dispatch and tests to spec names | **done** | ~~35~~ |
| 38 | 3.5b | /qa | Rename primitives in integration tests; cross-check against spec | **done** | — |
| 39 | 3.5b | /arch | Update `design/arch/CLAUDE.md` — rename old primitive names to spec names | **done** | — |
| 40 | 3.5b | /examples | Update all 8 example `.cl` files — rename old primitive names to spec names | **done** | — |
| 41 | 3.5b | /docs | Update `user/getting-started.md` — rename old primitive names to spec names | **done** | — |
| 29 | 5 | /review | Ring 0 completion review (ring gate) | **done** (PASS WITH CONDITIONS → H-1 fixed) | ~~35,36,37,39,40,41~~ |

## FIXMEs Carried from Sprint 0

15 FIXMEs from Sprint 0. Ring 0 dispositions:

**Resolve in this sprint (Wave 1):**
1. `design/arch/ring0-interfaces.md` — operator table (single authoritative source)
2. `design/arch/ring0-interfaces.md` — `MacroExpander` crate location
3. `crates/cranelisp-typecheck/plan-typecheck.md` — `ReplCheckResult` addition to interfaces
4. `design/arch/ring0-interfaces.md` — `is_heap()` removal consideration
5. `design/arch/ring0-interfaces.md` — REPL error recovery protocol

**Resolve in this sprint (Wave 2-3):**
6. `crates/cranelisp-typecheck/plan-typecheck.md` — Int/Float disambiguation protocol
7. `crates/cranelisp-runtime/plan-platform.md` — panic handler commitment (Ring 0: `catch_unwind`)
8. `crates/cranelisp-runtime/plan-platform.md` — operator wrappers ring assignment
9. `crates/cranelisp-typecheck/plan-typecheck.md` — borrow-splitting strategy (promoted from "Defer" — see plan review BLOCKER-1)

**Defer (Ring 2+):**
10. `spec/07-traits.md` — traits-as-stdlib review (Ring 2)
11. `lib/plan-stdlib.md` — `~@` unquote-splicing path (Ring 3)

**Defer (Ring 4+):**
12. `user/plan-docs.md` — docstring display in REPL output (Ring 4)
13. `user/plan-docs.md` — builtin docstrings in compiler (Ring 4)
14. `user/plan-docs.md` — `/learn` as usability finding (Ring 4)

**Already informational:**
15. None reclassified.

## Notes

### Wave 1 complete (2026-03-05)

`/arch` delivered `cranelisp-types` crate: 11 modules, 17 unit tests, clippy-clean. Resolved all 10 interface decisions (see `ring0-interfaces.md` §"Wave 1 Architectural Decisions"). Key deliverables:
- All Ring 0 boundary types implemented with full enum variants (deferred rings defined but not exercised)
- `operator.rs`: single authoritative operator table with 10 Ring 0 operators, three categories, type scheme generation
- `check.rs`: `ReplCheckResult`, `ReplSnapshot`, enriched `CheckResult` with `type_defs`/`constructor_to_type`
- `pipeline.rs`: `MacroExpander` trait + `NoOpExpander` in cranelisp-types (dependency inversion)
- `ResolvedCall::BuiltinFn` enriched with `operand_type: Option<Type>` for Int/Float disambiguation
- Borrow-splitting pattern documented: `unify`/`occurs_check` take explicit `&mut Subst` + `&mut TypeId`
- Wave 2 unblocked: `/frontend`, `/typecheck`, `/backend` can begin; `/platform` was already unblocked

### Wave 2 complete (2026-03-05)

All four Wave 2 skills completed in parallel. 253 tests total across workspace, clippy-clean.

| Crate | Tests | Key deliverables |
|-------|-------|-----------------|
| `cranelisp-frontend` | 103 | Reader (all 7 Sexp variants), AST builder (all Ring 0 forms), 59 reader + 44 AST builder tests |
| `cranelisp-typecheck` | 88 | Algorithm W with borrow-splitting, 10 expression forms, operator resolution, ADT exhaustiveness, snapshot/restore |
| `cranelisp-backend` | 41 | Cranelift 0.116 codegen, FnCompiler context struct, GOT, TCO, enum match, 34 integration + 7 unit tests |
| `cranelisp-runtime` | 4 | `cranelisp_panic` with `extern "C-unwind"` for `catch_unwind` compatibility |

**Note**: Backend uses Cranelift **0.116** (not 0.125 as planned). 0.125 was not available; API differences are minor (`jump`/`brif` take `&[Value]` directly).

Wave 2.5 (/review) and Wave 3 (/qa) are now unblocked.

### Wave 2.5 — Review & Refactor cycle (2026-03-05)

**Round 1 — Initial review** (3 parallel agents):

| Crate | Blockers | Important | Suggestions |
|-------|----------|-----------|-------------|
| `/frontend` | 1 (missing reader macros for `'`, `` ` ``, `~`, `#`, `$`, `%`, `&`) | 5 (build_defn dedup, TypeDef conversion, macro check, bare String→Symbol, plan deviation) | 5 |
| `/typecheck` | 0 | 3 (shared registration helper, let scope comment, HashSet conversion) | 10 |
| `/backend` | 0 | 6 (compiler.rs 693 lines, compile_body 8 params, compile_constructor_pattern 8 params, bare String in GOT, expect() in pipeline) | 9 |

**Round 1 — Refactoring** (3 parallel agents):

- **Backend**: compiler.rs (693 lines) split into 5 submodules under `compiler/` (mod.rs 271, literals.rs 66, control_flow.rs 101, apply.rs 142, match_codegen.rs 194). CompileContext and MatchContext structs introduced. All 6 I + 9 S findings addressed. 41 tests pass.
- **Frontend**: Reader macros added (16 new tests). AST builder rejects non-Ring-0 forms with clear errors (9 new tests). `build_defn` deduplication via `DefnInner`. `Symbol` newtype enforced. 129 tests pass (up from 103).
- **Typecheck**: Shared `register_defn_signature` helper extracted. `builtin_operators` → HashSet. `ctor_infos.clone()` eliminated. `resolve_expr_types` helper extracted. Dead code removed. All 7 findings addressed. 88 tests pass.

**Round 2 — Re-review** (3 parallel agents):

| Crate | Blockers | Important | Suggestions | Verdict |
|-------|----------|-----------|-------------|---------|
| `/frontend` | 0 | 7 | 8 | Gate passes |
| `/typecheck` | 1 (REPL restore — deferred to Wave 3) | 6 | 10 | Gate passes (batch OK) |
| `/backend` | 2 (Cranelift version doc, GOT-indirect calls) | 7 | 8 | Gate blocked |

**Round 2 — Fixes**:
- Backend B1 (doc): Updated ring0-interfaces.md to reflect Cranelift 0.116 (not 0.125)
- Backend B2 (critical): Implemented GOT-indirect calls for Interactive mode — 7 new tests including GOT redefinition verification
- Typecheck B1: REPL snapshot/restore known limitation, deferred to Wave 3 (REPL-only, batch mode unaffected)

**286 tests total (frontend 129, backend 48, typecheck 88, types 17, runtime 4), clippy-clean.**

**FIXME scan**: Zero FIXMEs in source code (.rs files). Plan doc FIXMEs were resolved during Wave 1.

**Wave 2.5 gate: PASS.** All crates ready for pipeline integration.

### Wave 3 complete (2026-03-05)

`/qa` delivered pipeline wiring, batch/REPL modes, test helpers, and 102 integration tests (91 passing, 11 ignored for Ring 1 lambdas).

| Deliverable | Details |
|-------------|---------|
| `src/pipeline.rs` | `compile_and_run(source, mode)` → frontend → typecheck → backend → execute |
| `src/repl.rs` | `ReplSession` with persistent TypeChecker + GOT, `:Type value` output, error recovery |
| `src/main.rs` | Batch (`cranelisp file.cl`) and REPL (`cranelisp`) modes |
| `src/lib.rs` | Library crate exposing pipeline + repl for integration tests |
| `tests/helpers/mod.rs` | 7 helpers: compile_and_run_simple, compile_both, assert_type_error, repl_session, etc. |
| `tests/ring0.rs` | 102 tests: core batch (11), REPL (8), TCO (5), floats (8), errors (13), ADT (4), dual-mode (10), annotations (3), let-poly (2), multi-defn (3), + more |

**390 tests passing, 11 ignored (lambda/Ring 1), clippy-clean, 3.9s total runtime.**

Discoveries: match syntax uses bracket `(match scrut [pat body ...])` not individual lists; REPL defn compilation requires direct Jit API with session GOT (not `compile_program` which creates its own internal GOT); `finalize_definitions()` per-function means source-order matters for forward refs in Batch.

Wave 4 (`/examples`, `/docs`, `/repl`, `/stdlib`, `/port`) now unblocked.

### Wave 3.5 complete (2026-03-05)

Replaced polymorphic operator infrastructure with 21 monomorphic named primitives (principle 8 compliance). These primitives survive permanently — Ring 2 adds `Num.+` dispatching to `int-add`/`float-add`.

| Skill | Changes |
|-------|---------|
| `/arch` | Updated `ring0-interfaces.md` §2 with 21-primitive spec, data flow, removed infrastructure |
| `/typecheck` | Rewrote `operator.rs` → `PrimitiveDef` + `ring0_primitives()`. Updated `builtins.rs`, `checker.rs`, `infer.rs`, `program.rs`. 94 tests (was 88, +6 new) |
| `/backend` | Rewrote `operators.rs` to dispatch on primitive names. Updated `apply.rs`. 24 tests (was 14, +10 new) |
| `/qa` | Updated all 102 integration tests in `ring0.rs` to use primitive names (`int-add`, `float-lt`, etc.) |

Removed infrastructure: `OperatorCategory`, `BuiltinOperator`, `ring0_operators()`, `operator_scheme()`, `resolve_builtin_operator()`, `builtin_operators: HashSet`, `operand_type` field on `ResolvedCall::BuiltinFn`.

**369 tests passing, 11 ignored (lambda/Ring 1), clippy-clean.**

Task 34 (`/review` — review primitive changes): **PASS** — 0 blockers, 0 important, 5 suggestions. All suggestions are cosmetic. Ring 0 checklist items 5.6 and 5.12 noted as outdated (will be updated in ring gate review).

Wave 3.5 complete. Wave 4 (`/examples`, `/docs`, `/repl`, `/stdlib`, `/port`) is now unblocked.

### FINDING: Primitive names don't match spec (discovered post-Wave 4)

**Severity: BLOCKING.** The implementation uses invented names (`int-add`, `float-eq`, `int-neg`, etc.) instead of the spec-defined names from `spec/appendix-a-builtins.md` (`add-i64`, `eq-f64`, etc.). Additionally, `int-neg` and `float-neg` don't exist in the spec at all (19 spec primitives, not 21).

This is a spec compliance bug that propagated through Waves 1–4 because:
1. `/arch` (Wave 1) defined non-spec names in `ring0-interfaces.md`
2. `/typecheck` and `/backend` (Wave 2) implemented the non-spec names
3. `/qa` (Wave 3) wrote tests against the implementation instead of cross-checking against the spec
4. `/review` (Wave 2.5, 3.5) did not catch the naming deviation
5. Wave 4 skills (`/examples`, `/docs`, `/repl`) propagated the wrong names further

**Root cause**: No skill cross-checked primitive names against `spec/appendix-a-builtins.md`. The authoritative primitive table in `cranelisp-types/src/operator.rs` was treated as the source of truth, but it was wrong from the start.

**Required fix** (Wave 3.5b — new wave):
- `/arch`: Update `ring0-interfaces.md` §2 with spec-correct names, remove neg primitives
- `/typecheck`: Rename primitives in registration code and tests
- `/backend`: Rename primitives in codegen dispatch and tests
- `/qa`: Rename primitives in all integration tests; verify against spec this time
- Wave 4 artifacts (`examples/`, `user/getting-started.md`, `tests/repl_experience.rs`) also need updates — defer to owning skills

### Wave 3.5b complete (2026-03-05)

Spec-compliance fix for primitive names. Test-driven: `/qa` fixed tests first (red), then compiler skills fixed the implementation (green).

| Skill | Changes |
|-------|---------|
| `/qa` | Renamed all primitives in `tests/ring0.rs` and `tests/repl_experience.rs` to spec names. Removed 2 neg tests. 71 intentional failures. |
| `/arch` | Updated `ring0-interfaces.md` §2: renamed 18 primitives, removed neg, count 21→19 |
| `/typecheck` | Renamed in `operator.rs` (authoritative table), `builtins.rs`, `infer.rs`, `program.rs`, `check.rs`. 117 crate tests pass. |
| `/backend` | Renamed in `operators.rs` dispatch. Removed `emit_int_neg`/`emit_float_neg`. 14 crate tests pass. |

**Result: 147 tests passing (91 ring0 + 56 repl_experience), 11 ignored (Ring 1), clippy-clean.**

8 example test failures remain — the Wave 4 example `.cl` files still use old names. These are owned by `/examples` and were identified as premature (building against Ring 0 primitives before Ring 2 provides `+`). Defer to next sprint.

Process improvement: `/qa` and `/sprint` skill definitions updated to prevent recurrence — `/qa` now has "Spec-First Testing" section requiring spec cross-checks; `/sprint` now has explicit "MUST NOT edit files outside `sprints/`" boundary rule.

Remaining cleanup (tasks 39-41, parallel): `/arch` fixed 2 references in `design/arch/CLAUDE.md` (Principles 8, 9). `/examples` renamed primitives in all 8 `.cl` files (replaced `int-neg`/`float-neg` with `(sub-i64 0 x)`/`(sub-f64 0.0 x)`). `/docs` renamed primitives in `user/getting-started.md` and removed the Negation subsection (not a spec primitive).

**All 436 tests passing (129 frontend + 94 typecheck + 14 backend + 23 types + 4 runtime + 91 ring0 + 56 repl_experience + 8 examples + 13 binary + 4 other), 11 ignored (Ring 1), 0 failures.**

Wave 3.5b fully complete. Task 29 (Wave 5 — ring gate review) is now unblocked.

### Wave 4 complete (2026-03-05)

All six Wave 4 tasks done (tasks 24-28, 40-41).

| Skill | Deliverable |
|-------|------------|
| `/repl` | 43 new REPL experience tests (56→99 total). Covers: error span quality, type error messages, arity errors, display edge cases (NaN, Infinity, max/min int), error recovery, all 19 primitives in REPL context, performance bounds, discoverability workflow. Deferred to Ring 1+: qualified type names, slash commands, prompt timing, tab completion. |
| `/stdlib` | Ring 0 foundation review: SOUND. HM inference correct (let-poly works), primitive table clean, function definition pipeline solid (two-pass batch, shared REPL path). No concerns at Ring 0. Needs Ring 1 (strings, ADTs with fields, closures, heap) and Ring 2 (traits, modules) before real stdlib work begins. |
| `/port` | Ring 0 assessment: zero implementable Sudoku Solver components. Only expressible fragments are index arithmetic (but no `mod`) and `PropResult` enum. Ring 1 unlocks meaningful prototyping (ADTs with fields, Vec). Ring 3 for full exemplar as pure computation. Updated `exemplar/plan-exemplar.md`. |
| `/examples` | All 8 examples updated to spec-correct names (task 40). |
| `/docs` | `user/getting-started.md` updated to spec-correct names, negation section removed (task 41). |
| `/arch` | `design/arch/CLAUDE.md` updated (task 39). |

**479 tests passing (99 repl_experience + 91 ring0 + 129 frontend + 94 typecheck + 14 backend + 23 types + 8 examples + 13 binary + 4 runtime + 4 other), 11 ignored (Ring 1).**

### Wave 5 — Ring Gate Review (2026-03-05)

`/review` delivered `design/review/ring0-report.md`.

**Verdict: PASS WITH CONDITIONS**

| Severity | Count | Details |
|----------|-------|---------|
| HIGH | 1 | H-1: `cranelisp_panic` ABI mismatch — JIT declares 1 param, runtime expects 2 (`msg_ptr`, `msg_len`). Undefined behavior. |
| MEDIUM | 6 | M-1: `NULLARY_TAG_THRESHOLD` duplicated. M-2: `CheckResult` fields not in interfaces.md. M-3: `Warning` uses bare String. M-4: REPL `:Int` not `:primitives/Int` (Ring 2). M-5: No `#[must_use]`. M-6: `not` in spec ambiguity. |
| LOW | 4 | Empty test modules, unsafe Send+Sync, parens_balanced edge case. |

**Conditions for gate clearance:**
1. **[MUST]** Fix H-1 (panic ABI mismatch)
2. **[SHOULD]** Fix M-1 (remove NULLARY_TAG_THRESHOLD duplication)
3. **[SHOULD]** File FIXME to `/arch` for M-2 (CheckResult interface drift)

### Pre-sprint plan reviews (2026-03-04)

`/review` ran against all three compiler skill plans before sprint approval. Findings below feed into Wave 1 (`/arch` resolving interface questions) and Wave 2 (each skill addressing findings during implementation).

#### /frontend plan — APPROVE WITH COMMENTS

**Blockers:**
- `MacroExpander` crate placement unresolved — plan says "frontend or types"; should be `cranelisp-types` per architectural principle (traits used across crate boundaries live in the most stable crate). `/arch` must resolve in Wave 1.

**Important:**
- Match arm even-element validation not mentioned — `build_match` must validate bracket has even number of elements and produce clear error.
- `par-let` special error message couples to removed spec content — remove or simplify to generic "unknown form" error.
- `desugar_type_def` returns bare tuple `(Vec<Symbol>, Vec<ConstructorDef>)` — use named struct per `src/CLAUDE.md` convention.
- `Trace` rejection should be keyword-based (fire before argument parsing) for forward-compatibility.
- `Warning` type uses bare String in interfaces — upstream issue for `/arch`.

**Suggestions:** Float sign support clarification, parse error test cases, reader macro expansion details, `build_expr` API scope clarification.

#### /typecheck plan — NEEDS REVISION

**Blockers:**
1. Borrow-splitting strategy unresolved — all pseudocode uses `&mut self` signatures. This recreates the prototype's clone-to-avoid-borrow debt (audit HIGH-3). Must specify concrete pattern before implementation: either `unify`/`occurs_check`/`apply`/`fresh_var` take explicit field params (`&mut Subst`, `&mut u32`), or adopt `SubstEnv` sub-struct with `split_borrow_mut()`. **Promoted to "Resolve in this sprint" (FIXME #9).**
2. Operator scheme soundness gap — plan registers all operators as `(Fn [a a] a)` with post-unification validation. But comparison operators (`=`, `<`, `>`, `<=`, `>=`) return `Bool` not `a`, and `not` is monomorphic `(Fn [Bool] Bool)`. Must differentiate three categories: arithmetic `(Fn [a a] a)`, comparison `(Fn [a a] Bool)`, boolean `(Fn [Bool] Bool)`.

**Important:**
- Int/Float disambiguation protocol: backend needs to know which `expr_types` entry to consult for `iadd` vs `fadd`. Recommend enriching `ResolvedCall::BuiltinFn` with `operand_type: Type` to eliminate cross-map lookup.
- REPL error recovery underspecified: what is snapshotted, how are symbol table additions tracked, cross-boundary rollback (typecheck succeeds, codegen fails).
- `ReplCheckResult` missing from `interfaces.md` — FIXME already filed to `/arch`.
- `check_repl_input` not in the 10-step implementation sequence — add as step 11.
- `generalize` calling context should document that scope stack is empty for top-level defns.

#### /backend plan — APPROVE WITH COMMENTS

**Blockers:**
1. Data flow for `type_defs` and `constructor_to_type` into `compile_unit` unclear — `CheckResult` does not expose these; `SymbolTable` is an output type, not input. File `FIXME(/arch)` to clarify: add to `CheckResult`, or have binary crate extract from `SymbolTable`, or create a `TypeContext` struct.
2. Int/Float disambiguation protocol not committed — plan lists both raw names (`+`) and trait-mangled names (`add-i64`) without choosing. Must align with `ring0-interfaces.md` (raw names + `expr_types` lookup), or adopt enriched `BuiltinFn` with `operand_type`.

**Important:**
- `cranelisp_panic` should use `panic!()` + `catch_unwind`, not `exit(1)` — otherwise a non-exhaustive match in REPL kills the session. Align with ring0-checklist.
- Forward-reference batch compilation needs explicit two-pass pattern: (1) declare all function signatures to populate `func_ids`, (2) compile all function bodies.
- `FnSlot` type referenced but never defined — add struct definition.
- GOT-indirect call pattern inconsistent between sections 4.5 and 6.3 — reconcile into one canonical pattern.
- ISA not stored on `Jit` struct — document that this is intentional (each consumer constructs via `build_isa_flags`).

**Suggestions:** Tail-position save/restore should be RAII-safe, `format_result` needs `TypeDefInfo` access for ADT display, consider `types.rs` for backend-local type definitions, line count estimate (940) excludes unit tests (expect 1200-1500 total).

### Actions for Wave 1 (/arch)

Based on the plan reviews, `/arch` must resolve these interface questions before Wave 2 begins:

1. `MacroExpander` trait placement → `cranelisp-types` (recommended)
2. Operator type scheme categories: arithmetic `(Fn [a a] a)`, comparison `(Fn [a a] Bool)`, boolean `(Fn [Bool] Bool)`
3. Int/Float disambiguation protocol — recommend enriching `ResolvedCall::BuiltinFn { name, operand_type }`
4. `ReplCheckResult` addition to `interfaces.md`
5. `type_defs`/`constructor_to_type` data flow into backend
6. REPL error recovery protocol (snapshot/restore across typecheck-codegen boundary)
7. `Warning` type — enum or bare string?
8. Borrow-splitting pattern for typechecker (explicit field params vs sub-struct)

## Outcome

### Delivered

- **7-crate workspace** compiling cleanly: `cranelisp-types`, `cranelisp-frontend`, `cranelisp-typecheck`, `cranelisp-backend`, `cranelisp-runtime`, `cranelisp-platform` (stub), `cranelisp` (binary)
- **Pipeline**: `compile_and_run()` wiring frontend → typecheck → backend → JIT execute
- **Batch and REPL modes** with shared pipeline via `CompileMode` enum
- **19 monomorphic primitives** matching `spec/appendix-a-builtins.md` exactly
- **Type inference**: Algorithm W with borrow-splitting, let-polymorphism, ADT exhaustiveness
- **Codegen**: Cranelift 0.116, GOT-indirect calls for Interactive mode, loop-based self-TCO
- **475 tests** (all passing, 11 ignored for Ring 1), clippy-clean
- **8 example programs**, getting-started tutorial, 99 REPL experience tests
- **Ring gate**: PASS WITH CONDITIONS → H-1 resolved (panic removed, trap used)
- **Review report**: `design/review/ring0-report.md`

### Deferred

- **M-1**: `NULLARY_TAG_THRESHOLD` duplicated in `cranelisp-types` and `cranelisp-backend` — resolve in Ring 1 when backend imports from types
- **M-2**: `CheckResult` fields (`type_defs`, `constructor_to_type`) not in `interfaces.md` — file FIXME to `/arch` in Sprint 2
- **FIXME(/spec)**: Exhaustiveness checking for non-ADT scrutinee types (Int, Bool, Float, String) — spec needs to require wildcard arm or compile-time error for non-ADT match
- **Remaining review M3–M6, L1–L4**: Tracked in `ring0-report.md`, non-blocking

### Findings

- **Spec-compliance process gap**: Primitive names were invented rather than taken from spec. Propagated through 4 waves before discovery. Fixed by adding "Spec-First Testing" to `/qa` skill and boundary rules to `/sprint` skill.
- **No runtime panic mechanism**: The language is pure functional with static exhaustiveness checking — runtime panics are a compiler-bug backstop, not a language feature. `cranelisp_panic` removed; Cranelift traps used instead. Backend no longer depends on `cranelisp-runtime`.
- **`/stdlib` assessment**: Foundation is sound for stdlib work. Needs Ring 1 (strings, closures, heap) and Ring 2 (traits, modules) before real stdlib development begins.
- **`/port` assessment**: Zero Sudoku Solver components expressible at Ring 0. Ring 1 unlocks meaningful prototyping (ADTs with fields, Vec). Ring 3 for full exemplar.
- **Test count growth**: Started at 286 (Wave 2.5), ended at 475. REPL experience tests (99) are the largest single suite.
