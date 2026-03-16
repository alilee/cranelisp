# Sprint 18: Ring 4C — REPL Hardening & E2E Infrastructure

**Status**: COMPLETE
**Ring**: 4 (Effects) — third increment
**Goal**: Fix prelude ADT display, establish E2E test infrastructure with test prelude, harden REPL slash command coverage, spec runtime error semantics.

## Scope

Sprint 17 delivered IO sequencing and the export mechanism. Sprint 18 hardens the REPL experience and test infrastructure. Two bugs from Sprint 17 (prelude ADT display, type annotations) are defects that must be fixed. E2E test infrastructure (test prelude fixture, helpers) is formalized. REPL slash commands get full test coverage. Checked arithmetic replaces `process::exit(1)` with recoverable panics, un-ignoring vec bounds tests.

### Deferred Debt (priority — defects cannot be carried further)

| # | Item | Owner | Deferrals | Description |
|---|------|-------|-----------|-------------|
| D1 | Prelude ADT display shows raw pointers | /int | 1x (S17) | `(Some 42)` displays `34506671232` instead of `(Option.Some 42)` when Option comes from prelude import. 5 failing tests. **DEFECT.** |
| D2 | Type annotation expressions | /frontend + /int | 1x (S17) | `:Int 42` not parsed as expression (spec §2.3.8). 3 failing tests. **DEFECT.** |
| D3 | I1 unused heap lambda params leak | /backend | 2x (S16, S17) | Pre-existing RC issue. **2x deferred — must fix or get user approval.** |
| D4 | Exemplar IO integration | /port | 1x (S17) | Pure exemplar works; IO capabilities not demonstrated. |
| D5 | Docs IO guide section | /docs | 1x (S17) | IO sequencing guide not written. |

### Ring 4C: REPL Hardening

| # | Feature | Owner | Description |
|---|---------|-------|-------------|
| C1 | E2E test prelude fixture | /qa | Formalize `tests/fixtures/prelude.cl` as QA-owned test prelude. Document test isolation strategy (tests use fixture, not stdlib). |
| C2 | Runtime error spec | /spec | Define panic/error semantics: what errors are recoverable vs fatal, user-facing error format, REPL vs batch behavior, interaction with IO model. Spec gap in §12.7. |
| C3 | REPL slash command test coverage | /qa + /repl | Write E2E and integration tests for all slash commands: `/doc`, `/source`, `/sexp`, `/ast`, `/clif`, `/disasm`, `/expand`, `/mod`, `/time`, `/mem`, `/reload`. Per ring4.md test plan. |
| C4 | IO examples + docs | /examples + /docs | Complete IO learning sequence. Write IO guide section for user docs. |
| C5 | Exemplar IO | /port | Add IO capabilities to exemplar (formatted output via `print`). |

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `repl/spec.md:837` | /repl | Terminal styling — Ring 4 scope | Carry — not this sprint |
| `.claude/commands/platform.md:73` | /platform | stderr `write` for REPL | Carry — evaluate for Ring 4D |
| `spec/10-io.md:52` | /spec | resource_token field for Par | Carry — Par is later Ring 4 |

## Architecture Review

**Reviewer**: /arch
**Date**: 2025-03-10
**Status**: APPROVED with notes

### 1. Technical Coherence ✓

The sprint scope forms a complete, testable increment:
- **D1 (ADT display)** + **D2 (type annotations)** are isolated defect fixes with clear acceptance criteria (6 failing tests → 0)
- **D3 (lambda param RC leak)** is a well-scoped backend fix with existing diagnostic tooling (`CRANELISP_RC_TRACE=1`)
- **C1-C5** are infrastructure and polish tasks that don't introduce new language semantics

All items have concrete test criteria — no "we'll know it when we see it" scope.

### 2. No Interim Architecture ✓

No task builds throwaway infrastructure:
- **D1**: Display fix is permanent — ADT formatting must work regardless of defining module
- **D2**: Type annotation expressions are spec §2.3.8 — a permanent language feature
- **D3**: RC fix is correctness, not architecture
- **C2 (runtime error spec)**: Spec work only — implementation deferred until spec is written
- **C3 (slash command tests)**: E2E tests are permanent assets

### 3. Design References

| Skill | Design refs needed | Status |
|-------|-------------------|--------|
| /frontend | `spec/02-grammar.md` §2.3.8 | ✓ in SPRINT.md |
| /typecheck | `spec/02-grammar.md` §2.3.8 | ✓ in SPRINT.md |
| /int | `src/repl.rs` format_adt_value | ✓ in SPRINT.md |
| /backend | `design/backend/ring2-rc.md` §3 | **Add**: §2 (scope cleanup), §3.3 (lambda params) |
| /spec | `spec/12-runtime.md` §12.7 | ✓ in SPRINT.md |

**Recommendation**: Update /backend design refs to include `design/backend/ring2-rc.md` §2-3.

### 4. Interface Gaps

No boundary type changes required:
- D1: Display is presentation, not interface
- D2: AST already has `Expr::Annotate` (check `interfaces.md`)
- D3: Internal to backend scope management

### 5. Debt Assessment

| Item | Deferrals | Verdict |
|------|-----------|---------|
| D1 | 1x | Include — defect |
| D2 | 1x | Include — defect |
| D3 | **2x** | **MUST include or user approval** — exceeds automatic deferral threshold |
| D4 | 1x | Acceptable deferral (feature, not defect) |
| D5 | 1x | Acceptable deferral (docs, not defect) |

**D3 note**: The lambda param RC leak (I1 from Sprint 17 review) was deferred from S16 and S17. Per sprint archetype §Deferral Principles, items deferred twice require user approval to defer again. Given this is an RC correctness bug (potential memory leak), I recommend inclusion in Sprint 18. The fix scope is bounded: `compile_lambda_body` in backend needs to mirror `compile_body`'s scope handling pattern (already demonstrated working in the `then` double-free fix from S17).

### 6. Foundation-Before-Features ✓

No new features building on code with known review findings. The sprint is primarily defect fixes and test coverage — appropriate scope for a hardening sprint.

### Verdict: APPROVED

Proceed to Phase 3 (Design). Notes:
1. Update /backend design refs per §3 above
2. D3 (2x deferred) is flagged for mandatory inclusion — if /backend cannot fix in this sprint, escalate to user

## Skill Plans

### /arch
**Task**: Review sprint scope. Review panic redesign approach (C2) — must not be interim architecture.
**Acceptance**: APPROVED or revision requested.

### /frontend
**Task**: (D2) Implement type annotation expression parsing. `:Int 42` should parse as a type-constrained expression per spec §2.3.8.
**Design refs**: `spec/02-grammar.md` §2.3.8, `src/sexp.rs` (reader), `src/ast.rs` (AST builder)
**Acceptance**: `:Int 42` parses and evaluates. `:(Option Int) None` constrains polymorphic constructor. 3 e2e tests pass.

### /typecheck
**Task**: Support type annotation expressions in inference. Type annotation constrains the inferred type of the inner expression.
**Design refs**: `spec/02-grammar.md` §2.3.8
**Acceptance**: Type annotations unify correctly. Error on type mismatch.

### /backend
**Task**: (D3) Fix unused heap lambda params RC leak.
**Design refs**: `design/backend/ring2-rc.md` §2 (scope cleanup), §3.3 (lambda params); `crates/cranelisp-backend/src/compiler/` — lambda compilation, RC emit paths
**Acceptance**: RC balanced for lambda params. No leak under `CRANELISP_RC_TRACE=1`.

### /platform
**Task**: No new platform work. Carry stderr FIXME.
**Acceptance**: Confirm no changes needed.

### /int
**Task**: (D1) Fix prelude-imported ADT display — `format_adt_value()` must work for types defined in prelude modules, not just user module. (D2) Wire type annotation expression support from frontend through pipeline.
**Design refs**: `src/repl.rs` — `format_adt_value()`, `describe_symbol()`
**Acceptance**: `(Some 42)` displays `(Option.Some 42)` with prelude loaded. 5 display tests pass. Type annotations work end-to-end.

### /qa
**Task**: (C1) Formalize test prelude fixture. (C3) Write REPL slash command tests.
**Design refs**: `tests/plan/ring4.md` — slash command test list
**Acceptance**: Test prelude documented. All slash commands have at least 1 test.

### /stdlib
**Task**: No new stdlib work. Verify prelude works correctly with new display fix.
**Acceptance**: All existing stdlib tests pass.

### /examples
**Task**: (C4) Complete IO learning sequence.
**Acceptance**: All examples compile and run.

### /repl
**Task**: (C3) Validate REPL experience for slash commands. Write demo if needed.
**Acceptance**: All slash commands produce expected output format per spec.

### /port
**Task**: (C5) Add IO to exemplar — formatted output via `print`, interactive mode if feasible.
**Acceptance**: Exemplar demo updated with IO. Runs cleanly.

### /docs
**Task**: (C4) Write IO sequencing guide section. (D5) Covers `do`, `bind!`, `print`, `read-line`.
**Acceptance**: Guide section complete with examples.

### /review
**Task**: Code review after implementation. Focus: panic redesign correctness, ADT display fix completeness.
**Acceptance**: 0 Blockers, 0 Important findings unresolved.

### /spec
**Task**: (C2) Define runtime error semantics in `spec/12-runtime.md` §12.7. Currently four lines with three "implementation-defined". Needs to specify: (a) which errors are recoverable vs fatal, (b) user-facing error format in REPL and batch, (c) interaction with IO model (does an error in IO produce a failed IO value or abort?), (d) whether there's a `panic` or `error` mechanism exposed to user code, (e) checked vs unchecked arithmetic policy. Consider: Rust-style panic (unwind/abort), Result-based errors, Clojure-style exceptions, or keeping it simple with process abort + good error messages.
**Design refs**: `spec/12-runtime.md` §12.7, `spec/04-expressions.md` (match exhaustiveness), sketch `cranelisp_panic` implementation
**Acceptance**: §12.7 expanded with clear semantics for division-by-zero, vec bounds, stack overflow, match failure. Each error has specified behavior (not "implementation-defined"). Ring tag updated.

## Waves

### Wave 0: Spec (complete)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /spec | C2: runtime error spec §12.7 | done | Expanded from 4 lines to 7 subsections. All new reqs tagged [R4 S18]. |

### Wave 1: Defect fixes + test infrastructure (parallel)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /backend | D3: fix lambda param RC leak | done | Root cause: `derive_param_type()` returns None for unused params → no type recorded → no RC dec. Fix: use lambda's inferred `Type::Fn` from `expr_types`. 3 tests un-ignored. |
| /int | D1: fix prelude ADT display | done | Nullary constructors (None) were intercepted by `special_form_feedback()` instead of evaluating as values. Fixed guard to skip nullary ctors. |
| /frontend | D2: type annotation expressions (parser + AST) | done | Already implemented. 3 e2e tests now pass. |
| /qa | C1: test prelude fixture + C3: slash command tests | done | C1: fixtures documented in tests/CLAUDE.md. C3: 18 new slash command tests (5 passing, 13 #[ignore] for unimplemented commands). |

### Wave 2: Integration + build/test/review
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | D2: wire type annotation through pipeline | done | Already implemented (prior work). |
| /backend | I3: defn unused-param RC leak (review finding) | done | Same pattern as lambda fix. Typechecker now records defn span in expr_types. 1 new test. |
| /qa | Un-ignore tests, run full suite | done | 1269 passing, 0 failures, 21 ignored. |
| /review | Code review | done | 0B, 2I, 9S. I3: defn has same unused-param RC vulnerability. I10: 12 new ignored tests (legitimate). |

### Wave 3: Showcase
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /examples | C4: IO examples | done | All 24 examples pass (verified Wave 3). |
| /docs | C4+D5: IO guide section | done | 250-line IO section added to getting-started.md. Covers print, pure, do, bind!, read-line, platforms, batch programs. |
| /port | C5: exemplar IO diagnosis | done | Root cause: batch mode sets project_root to file parent, misses stdlib/. FIXME(/int) filed on src/main.rs:58. Fix deferred to S19. |
| /repl | Validate slash commands, demo if needed | done | Existing ring4a + ring4b demos present. No new demo needed for S18 (hardening sprint). |

## Notes

- C2 (runtime error spec) completed in Wave 0. User approved the spec.
- D3 initially partial (batch-mode leak). Root cause found: `derive_param_type()` returns None for unused params. Fixed by using lambda's inferred `Type::Fn` from `expr_types`. 3 tests un-ignored.
- I3 review finding (defn same vulnerability) fixed same sprint. Typechecker now records defn span in `expr_types`. 1 additional test.
- Exemplar failure diagnosed: batch `project_root` set to file parent dir, misses stdlib/. FIXME(/int) filed on src/main.rs:58.
- Worktree isolation caused 3/4 agents to restructure the project (merged sketch into main tree). Lesson: do NOT use worktree isolation for this project — agents misinterpret the sketch subdirectory. Sequential execution without isolation works reliably.

## Outcome

### Delivered
- **D1**: Prelude ADT display fix — nullary constructors (`None`) now evaluate as values, not introspection. 5 tests pass.
- **D2**: Type annotation expressions — already implemented; 3 e2e tests now pass.
- **D3**: Lambda unused heap param RC leak — `compile_lambda_body` uses authoritative `Type::Fn` from `expr_types` instead of `derive_param_type`. 3 new RC tests.
- **D3+**: Defn unused heap param RC leak (I3 review finding) — same fix applied to `compile_body`. Typechecker records defn span. 1 new RC test.
- **C1**: Test prelude fixture formalized (`tests/fixtures/prelude.cl`), documented in `tests/CLAUDE.md`.
- **C2**: Runtime error spec — `spec/12-runtime.md` §12.7 expanded from 4 lines to 7 subsections covering panic semantics, arithmetic policy, REPL/batch behavior, IO interaction, error format.
- **C3**: 18 new E2E slash command tests (5 passing, 13 `#[ignore]` for unimplemented commands).
- **D5**: IO guide section — 250 lines added to `user/getting-started.md` covering print, pure, do, bind!, read-line, platforms, batch programs.
- **Review**: 0 Blockers, 2 Important (both resolved in-sprint), 9 Suggestions.

### Deferred
- **D4 (exemplar IO)**: Batch mode prelude loading broken — `project_root` set to file parent dir. FIXME(/int) filed on `src/main.rs:58`. 2x deferred (S17, S18). → Sprint 19 mandatory.
- **13 slash command tests**: `/source`, `/sexp`, `/ast`, `/clif`, `/disasm`, `/mod` not yet registered in REPL command dispatch. Tests are spec-first placeholders. → Sprint 19+ when commands are wired.

### Findings
- **Worktree isolation anti-pattern**: Agents in worktrees consistently restructured the project by merging the sketch into the main tree. Root cause: agents see `sketch/` as the "real" source and the reimplementation crates as redundant. Mitigation: run agents sequentially without worktree isolation, with explicit "CRITICAL: do NOT restructure" instructions.
- **RC leak pattern generalized**: The `derive_param_type()` → None → no dec pattern affected both lambdas and defns. The fix (use `expr_types` span lookup) is now applied to both code paths. Any future function-like compilation should use the same pattern.
- **`special_form_feedback()` intercept**: Nullary constructors were incorrectly treated as introspection targets. The fix (skip nullary ctors) is narrowly scoped but correct — nullary ctors ARE values, non-nullary ctors ARE signatures.
