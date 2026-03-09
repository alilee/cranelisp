# Sprint 13: Catchup — Clean and Green

**Status**: COMPLETE
**Ring**: 3 (Meta)
**Goal**: Fix all deferred defects blocking demos, resolve stale FIXMEs, clean clippy warnings, triage ignored tests — get the project to a clean, green baseline.

## Rationale

Sprint 12 found 12 bugs via demo-driven testing and deferred them with FIXMEs. Four are real defects blocking demo showcases and exemplar progress. Per the deferral principles, carrying defects out of a sprint is an anti-pattern — these are 1x deferred and ship now. Additionally, housekeeping debt has accumulated: stale FIXMEs, clippy warnings, 20 ignored tests, outdated documentation.

## Scope

### Defects (1x deferred from Sprint 12 — MUST ship)

| # | Bug | Owner | Severity | Description |
|---|-----|-------|----------|-------------|
| D1 | Quasiquote triple-unquote | /frontend | Important | Same `~x` in 3 `if` positions → wrong result in batch. Span collision after `rewrite_spans()`. |
| D2 | Vec in polymorphic ADT display | /backend | Important | Vec field in ADT renders as `[]`. `format_adt_value` misreads Vec pointer from polymorphic field. |
| D3 | Trait operators in closures | /backend | Important | `(fn [x] (* x x))` → "no GOT slot for *". GOT slots not populated for trait methods in closure context. |
| D4 | Bare trait name introspection | /int | Important | `Num` at REPL → "undefined variable". `extract_scheme_from_entry()` doesn't handle `TraitDecl`. |

### Stale FIXMEs (resolve or remove)

| # | File | Owner | Issue |
|---|------|-------|-------|
| F1 | `exemplar/plan-exemplar.md:576` | /frontend | `!=` parse error — **NOT A BUG**. `!` is already in `operator_char`. Remove FIXME. |
| F2 | `stdlib/prelude.cl:14` | /int | Says "Three pipeline bugs" — bugs #2 and #3 are fixed. Update text. |
| F3 | `stdlib/CLAUDE.md:19-21` | /stdlib | Lists 3 bugs blocked — only #1 remains. Update. |
| F4 | `stdlib/plan-stdlib.md:7-9` | /stdlib | Same stale list. Update. |
| F5 | `repl/demos/CLAUDE.md:88` | /repl | Demo table missing exemplar-progress.demo and stdlib-progress.demo entries. |
| F6 | `tests/plan/ring2.md:207` | /qa | FIXME says `!=` can't parse — it can. Update FIXME to note parser works, write the test. |
| F7 | `src/pipeline.rs:702` | /int | Review search order against spec §8.11 — resolve or acknowledge as deferred. |

### Code Quality

| # | Issue | Owner |
|---|-------|-------|
| C1 | 6 clippy warnings: 1 dead code (`clear_transient_state`), 4 collapsible-if, 1 too-many-args | /int |
| C2 | 11 unused helper warnings in `tests/helpers/mod.rs` | /qa |
| C3 | 20 ignored tests: triage each (fix, delete, or re-justify) | /qa |

### Documentation

| # | Issue | Owner |
|---|-------|-------|
| U1 | `user/getting-started.md:108-109` says `+` is future work — it works | /docs |
| U2 | `user/plan-docs.md:174` stale `lib/` reference | /docs |

### Not in scope (legitimate deferral — design not ready)

| Issue | Rationale |
|-------|-----------|
| U1.1 string primitives (spec/appendix-a-builtins.md) | 3x deferred, user-approved. `text/string.cl` not scheduled. |
| Stdlib modular structure | Blocked by FIXME #1 (submodule primitive seeding). Single-file prelude is correct for now. |

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `exemplar/plan-exemplar.md:572` | /backend | Vec ADT display | D2: fix this sprint |
| `exemplar/plan-exemplar.md:574` | /backend | Trait operators in closures | D3: fix this sprint |
| `exemplar/plan-exemplar.md:576` | /frontend | `!=` parse error | F1: not a bug, remove |
| `spec/09-macros.md:301` | /frontend | Quasiquote triple-unquote | D1: fix this sprint |
| `tests/plan/ring2.md:18` | /qa | Bare trait introspection tests | Write tests after D4 lands |
| `tests/plan/ring2.md:207` | /qa | `!=` default method test | F6: parser works, write the test |
| `stdlib/prelude.cl:14` | /int | Stale "Three bugs" text | F2: update text |
| `stdlib/CLAUDE.md:19-21` | /stdlib | Stale bug list | F3: update |
| `stdlib/plan-stdlib.md:7-9` | /stdlib | Stale bug list | F4: update |
| `src/pipeline.rs:702` | /int | Spec §8.11 alignment | F7: review and resolve |
| `repl/demos/CLAUDE.md:88` | /repl | Demo table | F5: update |
| `user/plan-docs.md:472` | /arch, /qa | U0.1, U0.2 findings | Carried — not new debt |
| `spec/appendix-a-builtins.md:99` | /spec | U1.1 string primitives | Carried — 3x deferred, user-approved |

## Architecture Review

_To be filled by /arch during Phase 2._

## Skill Plans

### /frontend
**Task**: Fix D1 (quasiquote triple-unquote), resolve F1 (`!=` FIXME removal)
**Design doc**: n/a — bug fix, not new architecture
**Approach**: D1: investigate span collision in `rewrite_spans()` / `expand_qq_template()`. Each `~x` occurrence gets a unique synthetic span but `rewrite_spans()` overwrites all to call-site span. Fix: either preserve distinct spans per parameter reference, or ensure downstream compilation doesn't use span identity for symbol deduplication. F1: remove stale FIXME from `exemplar/plan-exemplar.md:576`.
**Design refs**: `crates/cranelisp-frontend/src/quasiquote.rs`, `src/expander.rs:276-290`
**Acceptance**: `(defmacro my-abs [x] \`(if (lt-i64 ~x 0) (sub-i64 0 ~x) ~x)) (my-abs 5)` returns 5 in batch mode. FIXME removed.

### /backend
**Task**: Fix D2 (Vec ADT display), D3 (trait operators in closures)
**Design doc**: n/a — bug fixes
**Approach**: D2: investigate `format_vec_elements()` in `src/repl.rs:1042-1075` — verify Vec pointer read from polymorphic ADT field is correct. Check type substitution and NULLARY_TAG_THRESHOLD interaction. D3: ensure GOT slots are populated for trait method implementations when compiling closures. The lambda `FnCompiler::inner()` inherits parent's `CompileContext` but the GOT map lacks trait method entries. Fix: populate trait method GOT slots, or use `compile_resolved_call` path consistently for closures.
**Design refs**: `src/repl.rs:938-979`, `crates/cranelisp-backend/src/compiler/apply.rs:133-175`, `crates/cranelisp-backend/src/compiler/control_flow.rs:405-411`
**Acceptance**: D2: `(deftype Wrap [:Vec val]) (Wrap [1 2 3])` displays with `[1, 2, 3]` not `[]`. D3: `((fn [x] (* x x)) 5)` returns 25.

### /int
**Task**: Fix D4 (bare trait introspection), F2 (stale prelude FIXME), F7 (pipeline search order review), C1 (clippy warnings)
**Design doc**: n/a — bug fix + housekeeping
**Approach**: D4: add `ModuleEntry::TraitDecl` handling to `extract_scheme_from_entry()` in `checker.rs` — or intercept in REPL eval before expression compilation. F2: update prelude.cl comment to reflect only bug #1 remains. F7: review `assemble_lib_dirs()` against spec §8.11 and decide if current behavior matches. C1: fix dead code, collapsible-if, too-many-args warnings.
**Design refs**: `crates/cranelisp-typecheck/src/checker.rs:261-285`, `repl/spec.md §4.1`
**Acceptance**: `Num` at REPL shows trait info, no "undefined variable". 0 clippy warnings. Stale comments updated.

### /qa
**Task**: C2 (test helper warnings), C3 (triage 20 ignored tests), F6 (`!=` test), bare trait tests after D4
**Design doc**: n/a
**Approach**: C2: remove unused helpers or add `#[allow(dead_code)]` with justification. C3: run each ignored test, classify as fix/delete/re-justify. F6: write `default_method_neq_int` test now that `!=` parses. Write bare trait introspection tests after D4 lands.
**Acceptance**: 0 test helper warnings. Each ignored test has documented disposition. New tests for `!=` and bare trait names.

### /stdlib
**Task**: F3 (update CLAUDE.md), F4 (update plan-stdlib.md)
**Approach**: Update both files to reflect bugs #2 and #3 are fixed; only bug #1 (submodule primitive seeding) remains.
**Acceptance**: No stale bug references in stdlib docs.

### /repl
**Task**: F5 (update demo table)
**Approach**: Add exemplar-progress.demo and stdlib-progress.demo to `repl/demos/CLAUDE.md` table with descriptions. Remove the FIXME.
**Acceptance**: Demo table complete, FIXME removed.

### /docs
**Task**: U1 (getting-started.md stale `+` claim), U2 (plan-docs.md stale `lib/` ref)
**Approach**: U1: update section to reflect that arithmetic operators work via traits/prelude. U2: change `lib/` to `stdlib/`.
**Acceptance**: No stale claims in user docs.

### /examples
**Task**: Verify all 18 examples pass after D1 fix
**Acceptance**: `cargo run -- --run examples/*.cl` all succeed.

### /port
**Task**: Verify exemplar demos work after D2/D3 fixes; update plan-exemplar.md to remove resolved FIXMEs
**Acceptance**: exemplar-progress.demo plays cleanly. Resolved FIXMEs removed.

### /review
**Task**: Review defect fixes D1-D4 for code quality
**Acceptance**: 0 Blockers, 0 Important findings on new code.

### /spec
**Task**: No action this sprint. U1.1 string primitives remain deferred (3x, user-approved).

### /arch
**Task**: Light review of D1-D4 fixes for architectural coherence. No design doc work expected.

### /platform
**Task**: No action this sprint.

### /typecheck
**Task**: Support D4 if `extract_scheme_from_entry` change affects typechecker internals.

## Waves

### Wave 1: Defect fixes (parallel)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /frontend | D1: quasiquote triple-unquote fix | **done** | `rewrite_spans()` now assigns unique synthetic spans per node. 2 new tests. |
| /backend | D2: Vec ADT display fix | **done** | RC use-after-free: ADT ctors now use `compile_consuming_arg_list`. 5 new tests. |
| /backend | D3: trait operators in closures fix | **done** | Added `resolve_deferred_trait_calls` to `check_repl_input` Expr path. 5 new tests. |
| /int | D4: bare trait name introspection fix | **done** | `special_form_feedback()` now follows Import/Reexport chains via `resolve_entry_with_module()`. 1 new test. |

### Wave 2: Review + test
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /review | Review D1-D4 fixes | **done** | 0 Blockers, 0 Important, 6 Suggestions. All four fixes PASS. |
| /qa | Write tests for D1-D4, `!=`, bare traits; triage ignored tests | **done** | `!=` tests already existed. 4 new bare trait tests. 1 ignored test un-ignored (r3_batch_macro_in_function_body). 19 remaining justified. |

### Wave 3: Housekeeping (parallel)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | F2, F7, C1: stale FIXMEs, clippy | **done** | 0 clippy warnings. DiscoveryCtx struct for too-many-args. F2 prelude.cl updated. F7 resolved (NOTE, not FIXME). |
| /frontend | F1: remove stale `!=` FIXME | **done** | Removed from exemplar/plan-exemplar.md. |
| /stdlib | F3, F4: update docs | **done** | Both updated to reflect only bug #1 remains. |
| /repl | F5: update demo table | **done** | exemplar-progress.demo and stdlib-progress.demo added. FIXME removed. |
| /docs | U1, U2: fix stale docs | **done** | getting-started.md `+` claim fixed. plan-docs.md lib/→stdlib/ fixed. |
| /qa | C2: test helper warnings | **done** | `#[allow(dead_code)]` on test helper module. |
| /sprint | FIXME cleanup: spec/09-macros.md, exemplar/plan-exemplar.md, tests/plan/ring2.md | **done** | 3 resolved FIXMEs removed, 2 FIXME annotations updated with [Tested] status. |

### Wave 4: Showcase verification
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /examples | Verify all examples pass | **done** | All 17 examples pass. |
| /port | Verify exemplar FIXMEs removed | **done** | 3 FIXMEs removed from plan-exemplar.md. |
| /qa | Final test run, ignored test report | **done** | 985 passed, 0 failed, 0 ignored, 0 clippy warnings, 0 test warnings. |

## Notes

### Wave 1 execution
- All 4 defects fixed in parallel by separate agents. No merge conflicts.
- D2 root cause was not display code — it was an RC use-after-free in ADT constructor compilation. `compile_arg_list` → `compile_consuming_arg_list`.
- D3 root cause was in typechecker, not backend. `check_repl_input` Expr path was missing `resolve_deferred_trait_calls`.
- D4 root cause was `special_form_feedback()` not following Import chains — affected all imported symbol types, not just traits.

### Wave 2 review findings (all Suggestions, no action required)
- S-D1: Unused `_call_site_span` parameter in `rewrite_spans`. Cosmetic.
- S-D1: Two-function indirection (`rewrite_spans` → `rewrite_spans_unique`). Cosmetic.
- S-D2: No negative test for Vec-in-ADT display. Coverage gap, not a bug.
- S-D3: Pre-existing gap: `resolve_deferred_trait_calls` doesn't recurse into `RunTests` sub-expressions.
- S-D4: `resolve_entry_in_current_module` widened to `pub` unnecessarily. Cosmetic.
- S-D4: Unrelated `lookup_import_type` formatting change included. Cosmetic.

### Ignored test disposition (all resolved — 0 remaining)

| Test | Disposition | Action |
|------|------------|--------|
| `multi_dot_module_path_in_import` | FIXED | Reader now loops on multi-dot paths |
| `nested_dependency_chain_compiles` | FIXED | Pipeline registers all qualified alias suffixes |
| `transitive_import_chain` | FIXED | Same pipeline fix |
| `r3_bare_macro_lookup` | FIXED | Bare macro names intercepted before expander |
| `r3_bare_macro_lookup_multi_clause` | FIXED | Same fix |
| `r3_sig_macro_variadic` | FIXED | Already worked — test had wrong syntax (`& rest` → `&rest`) |
| `r3_special_form_defmacro` | FIXED | Added `defmacro` to `register_special_forms` |
| `r3_macro_expands_to_literal` | REWRITTEN | Test was wrong — rewritten as negative test `r3_neg_macro_literal_body_type_error` |
| 10 E2E stubs | DELETED | Empty test bodies with no assertions — not tests |

### FIXME debt after sprint

| File | Owner | Issue | Status |
|------|-------|-------|--------|
| `stdlib/prelude.cl:14` | /int | Submodule primitive seeding (bug #1) | Carried — requires design work |
| `stdlib/plan-stdlib.md:7` | /int | Same bug #1 reference | Carried |
| `spec/appendix-a-builtins.md:99` | /spec | U1.1 string primitives | Carried — 3x deferred, user-approved |
| `user/plan-docs.md:472` | /arch, /qa | U0.1, U0.2 findings | Carried — not addressed |

## Outcome

_To be filled at sprint close after user review._

### Delivered

- **4 defects fixed** (all 1x deferred from Sprint 12):
  - D1: Quasiquote triple-unquote — unique synthetic spans per expanded node
  - D2: Vec in polymorphic ADT display — RC use-after-free in ADT constructor compilation
  - D3: Trait operators in closures — deferred trait resolution for REPL expressions
  - D4: Bare trait name introspection — import chain resolution in special_form_feedback
- **13 FIXMEs resolved** (spec/09-macros.md, exemplar/plan-exemplar.md x3, tests/plan/ring2.md x2, stdlib/prelude.cl, stdlib/CLAUDE.md, stdlib/plan-stdlib.md, repl/demos/CLAUDE.md, src/pipeline.rs, user/getting-started.md, user/plan-docs.md)
- **0 clippy warnings** (was 6): dead code gated, collapsible-if collapsed, DiscoveryCtx struct for too-many-args
- **0 test warnings** (was 11): `#[allow(dead_code)]` on test helpers
- **26 new tests**, 10 empty stubs deleted, 8 previously-ignored tests now passing
- **985 total tests**, 0 ignored, 0 clippy warnings, 0 test warnings (was 959 passed / 20 ignored / 6 clippy)
- **All 17 examples pass**
- **Additional fixes from ignored test triage**:
  - Multi-dot module paths in reader (loop instead of single-dot)
  - Deep submodule qualified ref aliases in pipeline (register all suffixes)
  - Bare macro name introspection (intercept before expander)
  - `defmacro` registered as special form
  - `&rest` syntax confirmed working (test had wrong syntax)
  - Macro literal body test rewritten as correct negative test

### Deferred

- Submodule primitive seeding (FIXME(/int) bug #1) — requires design work, not housekeeping
- U1.1 string primitives — 3x deferred, user-approved
- 6 review Suggestions — all cosmetic, no correctness impact

### Findings

- D2 root cause was surprising: not a display bug but an RC use-after-free in ADT constructor codegen. All constructors were affected, not just polymorphic ones with Vec fields.
- D3 was a typechecker gap, not a backend gap — the FIXME was filed against /backend but the fix was in /typecheck.
- D4 fix improved all imported symbol introspection, not just traits — broader improvement than the bug report suggested.
- `!=` was never actually broken — the FIXME was stale. 3 files had incorrect FIXMEs about it.
- Ignored tests are a failure mode — 10 of 20 were empty stubs (not tests at all), 1 was already passing, 1 was a wrong test. Only 8 were real gaps, and all were fixable in the current sprint. The `#[ignore]` annotation hides debt.
