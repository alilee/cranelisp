# Sprint 0: Foundation Survey and Planning

**Status**: COMPLETE
**Ring**: Pre-Ring 0 (preparation)
**Goal**: Every skill surveys its domain, validates its foundations, and produces a written plan so Ring 0 implementation can begin with no ambiguity.

## Scope

Planning sprint. Every skill reads the relevant spec, architecture docs, and prototype reference, then produces a plan artifact. No Rust code is written. The output is a set of documents that make Ring 0 implementation a matter of execution, not discovery.

## Skill Assignments

### /sprint
**Input**: `design/arch/roadmap.md`, all skill definitions, current project state
**Task**: Create `SPRINT.md` and update `ROADMAP.md` with Sprint 0 as ACTIVE
**Output**: `SPRINT.md`, updated `ROADMAP.md`
**Blocked by**: —
**Acceptance**: `SPRINT.md` exists with assignments for all 14 skills. `ROADMAP.md` shows Sprint 0.

### /spec
**Input**: `spec/01-06`, `spec/12-runtime.md`, `design/arch/roadmap.md` (Ring 0 acceptance criteria)
**Task**: Verify spec sections 01–06 and 12 contain sufficient detail for Ring 0. Map each Ring 0 acceptance criterion to a spec section with a testable example. Run 5–10 representative examples against the sketch oracle. Document gaps.
**Output**: `spec/ring0-readiness.md`
**Blocked by**: —
**Acceptance**: Every Ring 0 acceptance criterion mapped to a spec section. Gaps documented with proposed resolution.

### /arch
**Input**: `design/arch/interfaces.md`, all `crates/*/Cargo.toml`, `Cargo.toml`
**Task**: Verify workspace builds (`cargo check`). Extract the Ring 0 subset of `interfaces.md` with precise Rust signatures. Confirm `Sexp`, `Expr`, `Span`, `Type` (Ring 0 subset), `CheckResult`, `CranelispError`, `CompileMode`, `SymbolTable`, and `ModuleEntry` are fully specified. Verify Cranelift 0.125 dependencies.
**Output**: `design/arch/ring0-interfaces.md`
**Blocked by**: —
**Acceptance**: `cargo check` succeeds. Ring 0 interface subset is complete and consistent with `interfaces.md`.

### /qa
**Input**: `tests/plan/strategy.md`, `tests/plan/ring0.md`, `design/arch/roadmap.md`
**Task**: Create usability register. Validate Ring 0 test plan covers all acceptance criteria. Verify test helper signatures are consistent with `compile_unit()`. Capture performance baselines from prototype.
**Output**: `tests/plan/usability.md`, `tests/plan/ring0-readiness.md`
**Blocked by**: —
**Acceptance**: Usability register initialized. Ring 0 test coverage gaps documented.

### /frontend
**Input**: `spec/01-lexical.md`, `spec/02-grammar.md`, `design/arch/interfaces.md`, `sketch/src/sexp.rs`, `sketch/src/ast_builder.rs`
**Task**: Study prototype reader and AST builder. Plan Ring 0 implementation: PEG crate choice, grammar rules, Sexp→Expr mapping, known gotchas. Identify interface gaps.
**Output**: `crates/cranelisp-frontend/plan-frontend.md`
**Blocked by**: —
**Acceptance**: Plan covers all Ring 0 AST forms. PEG crate identified. Gotchas documented.

### /typecheck
**Input**: `spec/03-types.md`, `spec/04-expressions.md`, `spec/05-definitions.md`, `spec/06-pattern-matching.md`, `design/arch/interfaces.md`, `sketch/src/typechecker.rs`, `sketch/audits/typechecker.md`
**Task**: Study prototype typechecker and audit. Plan Ring 0 inference: module structure, Algorithm W, scope management, CheckResult population. Address each HIGH audit finding.
**Output**: `crates/cranelisp-typecheck/plan-typecheck.md`
**Blocked by**: —
**Acceptance**: Plan covers all Ring 0 expression forms. Each HIGH typechecker audit finding addressed. Module decomposition proposed.

### /backend
**Input**: `spec/12-runtime.md`, `design/arch/interfaces.md`, `sketch/src/codegen.rs`, `sketch/src/jit.rs`, `sketch/audits/codegen.md`, `sketch/audits/cache.md`
**Task**: Study prototype codegen/JIT and audits. Plan Ring 0 codegen: ISA setup, FnCompiler design, expression codegen, TCO, GOT for interactive mode. Verify Cranelift 0.125 API patterns. Address each HIGH audit finding.
**Output**: `crates/cranelisp-backend/plan-backend.md`
**Blocked by**: —
**Acceptance**: Plan covers all Ring 0 expression codegen. Each HIGH codegen/cache audit finding addressed. Cranelift API patterns noted.

### /review
**Input**: `sketch/audits/typechecker.md`, `sketch/audits/codegen.md`, `sketch/audits/module.md`, `sketch/audits/cache.md`, `src/CLAUDE.md`
**Task**: Read all 4 audit files. Create review infrastructure. Build Ring 0 review checklist from relevant HIGH findings and `src/CLAUDE.md` conventions.
**Output**: `design/review/CLAUDE.md`, `design/review/checklist.md`, `design/review/ring0-checklist.md`
**Blocked by**: —
**Acceptance**: All three files exist. Ring 0 checklist covers: no unwrap, no panic on input, max 100 lines/fn, one method per Expr variant, typed identifiers, no env.clone().

### /stdlib
**Input**: `sketch/lib/prelude.cl`, `sketch/lib/core.cl`, `sketch/lib/core/*.cl`, `sketch/lib/testing.cl`, `spec/11-stdlib.md`
**Task**: Inventory every function, trait, macro, and type in prototype stdlib. Map each to the ring where it becomes buildable. Plan `lib/` directory structure. Identify Clojure naming deviations.
**Output**: `lib/plan-stdlib.md`
**Blocked by**: —
**Acceptance**: Every prototype stdlib item inventoried with ring assignment. Directory structure planned.

### /examples
**Input**: `sketch/examples/*.cl`, `spec/appendix-b-examples.md`, `design/arch/roadmap.md`
**Task**: Read all 25 prototype examples. Design numbered learning sequence (one concept per example). Determine which examples work at Ring 0 (Int, Bool, Float, functions, let, if, enum match — no strings, no heap, no IO).
**Output**: `examples/plan-examples.md`
**Blocked by**: —
**Acceptance**: Learning sequence covers all language features. Ring 0 examples are concrete (source code sketched).

### /docs
**Input**: `user/CLAUDE.md`, `spec/` (concept inventory), `design/arch/roadmap.md`
**Task**: Design user documentation structure. Plan per-ring content. Outline getting-started guide (Ring 0). Plan tutorial chapters parallel to learning sequence.
**Output**: `user/plan-docs.md`
**Blocked by**: —
**Acceptance**: Documentation structure designed. Getting-started outline covers installation, first program, REPL basics.

### /repl
**Input**: `sketch/src/repl/`, root `CLAUDE.md` (self-documenting REPL principle), `sketch/audits/*.md`
**Task**: Study prototype REPL. Write experience specification: discoverability (what a new user finds in 5 minutes), input/feedback matrix, self-documentation contract, performance targets, error quality criteria. Map experience tests to rings.
**Output**: `repl/spec.md` (normative REPL experience specification), `repl/CLAUDE.md` (ownership)
**Blocked by**: —
**Acceptance**: Experience spec covers all 16 slash commands. Concrete performance targets defined. Tests mapped to rings.

### /platform
**Input**: `sketch/cranelisp-platform/`, `sketch/cranelisp-runtime/`, `sketch/platforms/stdio/`, `sketch/platforms/test-capture/`, `spec/10-io.md`, `spec/12-runtime.md`
**Task**: Inventory C-ABI contract, runtime primitives, and both platform DLLs. Plan per-ring deliverables. Validate crate stub names and dependencies. Address panic handler redesign.
**Output**: `crates/cranelisp-runtime/plan-platform.md`
**Blocked by**: —
**Acceptance**: C-ABI contract fully inventoried. Per-ring deliverables planned. Panic handler redesign addressed.

### /port
**Input**: `spec/` (full language surface), `sketch/examples/`, `sketch/lib/`, `spec/10-io.md`, `spec/08-modules.md`
**Task**: Evaluate 3–5 exemplar project candidates against the 9 selection criteria. Sketch ADTs, traits, IO, and modules for each. Perform gap analysis against stdlib. Propose 2–3 finalists.
**Output**: `exemplar/plan-exemplar.md`
**Blocked by**: —
**Acceptance**: At least 3 candidates evaluated with feature matrix. Module structure sketched for each.

## Task List

| # | Skill | Task | Status | Blocked By |
|---|-------|------|--------|------------|
| 1 | /sprint | Create SPRINT.md and update ROADMAP.md | done | — |
| 2 | /spec | Validate spec completeness for Ring 0 | done | — |
| 3 | /arch | Validate crate stubs and produce Ring 0 interface subset | done | — |
| 4 | /qa | Create usability register and validate Ring 0 test plan | done | — |
| 5 | /frontend | Survey spec/prototype, plan Ring 0 reader and AST builder | done | — |
| 6 | /typecheck | Survey spec/prototype, plan Ring 0 inference engine | done | — |
| 7 | /backend | Survey spec/prototype, plan Ring 0 codegen and JIT | done | — |
| 8 | /review | Establish review infrastructure and Ring 0 checklist | done | — |
| 9 | /stdlib | Survey prototype stdlib, plan lib/ structure | done | — |
| 10 | /examples | Survey prototype examples, design learning sequence | done | — |
| 11 | /docs | Survey documentation needs, plan user/ structure | done | — |
| 12 | /repl | Write REPL experience specification (`repl/spec.md`) | done | — |
| 13 | /platform | Survey prototype platform crates, plan reimplementation | done | — |
| 14 | /port | Evaluate exemplar project candidates | done | — |

## Execution Order

**Wave 1 — Infrastructure** (sets context for others):
`/sprint` → `/arch` → `/spec` → `/qa`

**Wave 2 — Compiler skills** (produce Ring 0 implementation plans):
`/frontend`, `/typecheck`, `/backend` (parallel)

**Wave 3 — Support skills**:
`/review`, `/repl`, `/platform` (parallel)

**Wave 4 — Content skills** (benefit from all prior context):
`/stdlib`, `/examples`, `/docs`, `/port` (parallel)

## Notes

- Sprint 0 is a preparation sprint — no Rust code is written
- All tasks are parallel (no blocking dependencies between skills)
- Recommended execution follows waves for best information flow, but any order works

### REPL Display Format Change (post-Wave 1)

REPL output format changed from `value :: Type` to `:Type value` (mirrors language syntax). All Wave 1 documents updated. Acceptance criteria in `design/arch/roadmap.md`, `spec/ring0-readiness.md`, `tests/plan/ring0-readiness.md` now use the new format. Operator display format deferred pending §7.7 FIXME resolution.

### Wave 1→2 FIXME Gate

1 FIXME outstanding: `spec/07-traits.md` §7.7 (`/spec`) — review whether Num/Eq/Ord trait declarations belong in language spec or stdlib. **Deferred to Wave 3+** (traits are Ring 2, not needed for Wave 2 compiler planning).

### Wave 2→3 FIXME Gate

2 FIXMEs outstanding, both safe to defer:

1. `crates/cranelisp-typecheck/plan-typecheck.md` — `FIXME(/arch)`: Add `ReplCheckResult` to `interfaces.md`. **Deferred to Sprint 1** (interface addition needed before Ring 0 implementation, not before Sprint 0 planning completes).
2. `spec/07-traits.md` §7.7 — `FIXME(/spec)`: Review whether Num/Eq/Ord trait declarations belong in language spec or stdlib. **Deferred to Wave 3+** (carried from Wave 1; traits are Ring 2 scope).

### Wave 3→4 FIXME Gate

No new FIXMEs from Wave 3 outputs. Carried FIXMEs unchanged.

### Wave 4 (Final) FIXME Gate

4 new FIXMEs from Wave 4 (post-review revisions):

1. `user/plan-docs.md` — `FIXME(/repl)`: Add docstring display to REPL output format specification.
2. `user/plan-docs.md` — `FIXME(/arch)`: Ensure all builtin types, primitive functions, and special forms have docstrings registered in the compiler.
3. `user/plan-docs.md` — `FIXME(/qa)`: Usability findings including `/learn` as Ring 0 implementation work.
4. `lib/plan-stdlib.md` — `FIXME(/frontend)`: `~@` unquote-splicing emits `core.syntax/sconcat`; new module layout places this at `macros/sconcat`. Coordinate qualified path.

Carried FIXMEs (all safe to defer to Sprint 1):
- `design/arch/ring0-interfaces.md` (5): operator table, `is_heap()` removal, `MacroExpander` crate, REPL error recovery, `ReplCheckResult`
- `crates/cranelisp-typecheck/plan-typecheck.md` (3): Int/Float disambiguation protocol, borrow-splitting strategy, `ReplCheckResult`
- `crates/cranelisp-runtime/plan-platform.md` (2): operator wrappers ring assignment, panic handler commitment
- `spec/07-traits.md` (1): traits-as-stdlib review

**Total: 15 FIXMEs outstanding.** All are design clarifications, none are blockers for Ring 0 implementation.

### Wave 1 FIXME Resolution (post-review)

After Wave 1 completion, user review identified 3 FIXMEs in `ring0-interfaces.md` and spec gaps. These were resolved:

1. **`par-let` removed from spec**: §4.12 deleted; lenient evaluation (§12.4.3) upgraded from MAY to MUST; auto IO scheduling (§10.12) upgraded to MUST. `ParLet` and `ParBind` removed from `Expr` enum in both `interfaces.md` and `ring0-interfaces.md`.
2. **String newtypes enforced**: All bare `String` identifier fields in interface types replaced with `Symbol`, `TypeName`, `TraitName`, `ModuleName`, `ModuleFullPath`, or `JitSymbol`. Hard rule documented in `design/arch/CLAUDE.md`.
3. **`CompileMode` expanded**: Added `Release` variant (deferred to Phase H). Interactive, Batch, Release.
4. **Spec gaps resolved**: Roadmap match syntax fixed (bracket form), batch mode clarified (shared pipeline), trait scope made explicit (builtins in Ring 0, traits in Ring 2), factorial criterion corrected (not tail-recursive).
5. **REPL experience spec**: Created `repl/spec.md` (normative) and `repl/CLAUDE.md` (ownership). Task 12 output updated from `design/repl-experience.md` to `repl/spec.md`.
6. **Readiness re-validated**: `spec/ring0-readiness.md`, `tests/plan/ring0-readiness.md` updated with all resolutions.

## Outcome

**Status**: COMPLETE

### Delivered

All 14 tasks completed. Sprint 0 produced 14 planning artifacts:

| # | Artifact | Lines |
|---|----------|-------|
| 1 | `SPRINT.md` + `ROADMAP.md` | — |
| 2 | `spec/ring0-readiness.md` | ~135 |
| 3 | `design/arch/ring0-interfaces.md` | ~990 |
| 4 | `tests/plan/usability.md` + `tests/plan/ring0-readiness.md` | ~135 |
| 5 | `crates/cranelisp-frontend/plan-frontend.md` | ~422 |
| 6 | `crates/cranelisp-typecheck/plan-typecheck.md` | ~650 |
| 7 | `crates/cranelisp-backend/plan-backend.md` | ~780 |
| 8 | `design/review/CLAUDE.md` + `checklist.md` + `ring0-checklist.md` | ~340 |
| 9 | `lib/plan-stdlib.md` | ~505 |
| 10 | `examples/plan-examples.md` | ~400+ |
| 11 | `user/plan-docs.md` | ~463 |
| 12 | `repl/spec.md` + `repl/CLAUDE.md` | ~300 |
| 13 | `crates/cranelisp-runtime/plan-platform.md` | ~545 |
| 14 | `exemplar/plan-exemplar.md` | ~404 |

### Deferred

- 15 FIXMEs deferred to Sprint 1 (see Wave 4 FIXME Gate above). All are design clarifications, none are blockers.

### Findings

1. **REPL display format redesigned**: Changed from `value :: Type` to `:Type value` during Wave 1 review. All documents updated. Key principle: "the REPL reinforces the syntax of the language."
2. **Cross-skill FIXME protocol established**: Skills add `FIXME(/skill-name)` comments in upstream files; owning skill resolves. Wave gates scan for unresolved FIXMEs.
3. **Operator display deferred**: The `+` story (stdlib home, trait constraints, Ring 0 builtins) depends on the §7.7 FIXME. Normal symbols used in examples.
4. **No hello-world at Ring 0**: IO requires Ring 4. Ring 0 examples use REPL-only evaluation. `/docs` filed this as a usability finding.
5. **Ring 0 stdlib is empty**: Validates the "optional prelude" design principle.
6. **Review found 13 cross-plan gaps**: Sprint 0 review (Wave 3) identified gaps in operator tables, borrow-splitting, panic handler, error recovery, and type discipline. All captured as FIXMEs and review checklist items.
7. **Exemplar project selected**: Sudoku Solver (best balance of feature coverage and scope).
8. **Exemplar web platform**: Sudoku Solver includes a custom web platform DLL (part of the exemplar, not infrastructure). Both IO models demonstrated: serve-loop (Cranelisp manages accept/send) and callback (platform calls pure handler). Pure handler `Request → Response` is the key architectural property.
9. **Interactive REPL tutorial**: `/learn` command designed with Socratic method — REPL asks questions, student answers by typing expressions. Data structure: `(section, prompt, trigger, answer)` with REPL watch mechanism. 33-section curriculum from Int to IO.
10. **User persona**: Documentation targets Sam, a motivated 12-year-old with no programming background. Tutorial teaches programming through Cranelisp, not lateral moves from other languages.
11. **Consistent REPL qualification**: `:primitives/Int` from day one, no short-form mode. Docstrings in REPL output provide comprehension context (e.g., `primitives/Int ; Integer numbers between -100 billion and 100 billion`).
12. **Stdlib end-state design**: Module organization redesigned from first principles (not from sketch). 14 top-level entries with depth-as-signal principle. Key decisions: Option/Result in `fn/` (composition tools), Functor/Foldable in `collections/` (abstract container interface), Seq separate from collections (lazy computation, not storage). Self-testing via own harness from Ring 2. ~30-name minimal prelude.
