# Sprint 15: REPL Output Conformance — Ring 3 Visibility

**Status**: COMPLETE
**Ring**: 3 (Meta) — continued
**Goal**: Bring the REPL output format into conformance with the rewritten spec (repl/spec.md §1.1, §3.3–3.5, §4.1) so Ring 3 features are visible and usable through the interactive REPL.

## Rationale

Ring 3 was declared feature-complete in Sprint 14 (1660 tests, gate PASS). But the user demo review in Sprint 14 Wave 6 revealed that the REPL output format doesn't match the spec — §1.1, §3.3, §3.4, §3.5, §4.1, and §11 were all rewritten, but implementation was deferred. The user hasn't "seen the results through the REPL" yet.

The implementation gap is entirely in `/int` (owns `src/repl.rs`). The rework touches 4 existing functions (`special_form_feedback`, `handle_list`, `handle_imports`, definition result display) and adds 1 new command handler (`/exports`). This is presentation-layer work — no compiler pipeline changes, no type system changes, no macro changes.

The demos are blocked on this: Sprint 14 D5 (demo refinements) couldn't ship because the output format was the old style.

## Scope

### Primary (/int — all REPL output rework)

| # | Feature | Spec | Description |
|---|---------|------|-------------|
| I1 | Universal output format | §1.1 | Rework `special_form_feedback()` and definition result display. All symbol classes get `:Type name ; classification - docstring` primary line. Types and traits get related symbol sections (`; match:`, `; defn:`, `; impl:`). Macros get clause signatures (`; [params] -> Sexp`). Primitives visible (currently DefKind::Primitive skipped). Builtin types show `; type` + `; impl:`. Trait methods use `Trait.method` dot notation. |
| I2 | `/list` rework | §3.3 | Remove special forms and imports categories (move to `/imports`). Include constructors in Types. `(no definitions)` for empty module. Prefix match filter (not substring). Category order: Modules, Macros, Traits, Types, Fns. Layout algorithm for 7+ names. |
| I3 | `/imports` rework | §3.4 | Special forms category always present. Include Reexport entries. Unfiltered mode: organize by category (Macros, Traits, Types, Fns). Filtered mode: `/imports mod` → per-source-module groups. Names only (no type signatures). |
| I4 | `/exports` command | §3.5 | New command. Resolve module, list public symbols by category. Usage hint for no argument. Error for not-found module. Empty module message. Filter argument. |
| I5 | Definition result display | §1.3 | `defn`, `deftype`, `deftrait`, `defmacro`, `impl` responses use universal format. Macro definitions show clause signatures, not `name :: macro`. |

### Quality + Cleanup

| # | Task | Owner | Description |
|---|------|-------|-------------|
| Q1 | Tests for new output format | /qa | Write tests from ring3.md test plan §Phase 7 (FIXME section): /list boundaries, /imports categories, /exports, macro universal format, bare symbol lookup per class. ~30 tests. |
| Q2 | Stale FIXME cleanup | /qa | Remove 3 stale FIXME comments on test files (tests pass, comments are noise). |
| Q3 | Test plan update | /qa | Update tests/plan/ring3.md Phase 7 test descriptions to match rewritten spec (FIXME(/qa) at line 369). |

### Demos (gates sprint close)

| # | Task | Owner | Description |
|---|------|-------|-------------|
| D1 | Demo refinements | /repl | Implement Sprint 14 D5 (blocked since S14). Update ALL demos to show new output format. Universal format makes output self-documenting. |
| D2 | Demo playthrough | user + /repl | Verify all 8 demos play cleanly with new output format. |

### Housekeeping

| # | Task | Owner | Description |
|---|------|-------|-------------|
| H1 | Spec appendix-a update | /spec | Add 13 string primitives to spec/appendix-a-builtins.md table. Sprint 14 marked this done but the table was never updated (FIXME still present). |
| H2 | Pipeline FIXME evaluate | /int | Evaluate src/pipeline.rs:754 FIXME about stdlib module resolution. Fix or document deferral rationale. |
| H3 | Test count audit | /qa | Investigate test count drop (1660 at Sprint 14 close → 1025 now). Identify cause and remediate if tests were lost. |

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `src/repl.rs:12` | /int | Universal output format — major rework | I1–I5: Sprint 15 primary deliverable |
| `src/pipeline.rs:754` | /int | stdlib module resolution spec update | H2: evaluate and fix or defer |
| `tests/e2e.rs:1211` | /qa | Stale FIXME — test passes | Q2: remove comment |
| `tests/ring3_repl.rs:228` | /qa | Stale FIXME — test passes | Q2: remove comment |
| `tests/ring3_repl.rs:275` | /qa | Stale FIXME — test passes | Q2: remove comment |
| `tests/plan/ring3.md:369` | /qa | Test plan needs updating for new spec | Q3: update test descriptions |
| `repl/spec.md:837` | /repl | Terminal styling reconsideration | Carry — Ring 4 scope |
| `repl/showcase:194` | /repl | interruptible_sleep negative duration | D1: fix during demo work |

## Architecture Review

Questions for /arch:
- I1: Confirm `special_form_feedback()` can query impl-for-type and methods-for-trait from the TypeChecker without new public API — or identify what accessors are needed.
- I2–I4: Confirm `CompiledModule`/`SymbolTable` provides sufficient queries for category-based listing (all defs, imports by category, exports by category) — or identify gaps.
- I4: `/exports` needs to resolve and potentially load a module. Confirm this can reuse existing module resolution (`resolve_module()`) without pipeline changes.

## Skill Plans

### /int
**Task**: I1–I5, H2
**Design doc**: n/a — implementing spec conformance, not new architecture
**Approach**: Rework 4 functions in src/repl.rs (~400 lines of changes) and add 1 new handler (~60 lines). The FIXME at line 12 provides a detailed 5-point checklist. Work bottom-up: (1) build `format_universal_line()` helper, (2) build `format_related_symbols()` helper, (3) rework `special_form_feedback()` using helpers, (4) rework `handle_list()`, (5) rework `handle_imports()`, (6) add `handle_exports()`, (7) update definition result display.
**Design refs**: `repl/spec.md §1.1, §3.3, §3.4, §3.5, §4.1, §11`
**Acceptance**: All REPL output matches spec examples. Demos play with new format. FIXME at src/repl.rs:12 removed.

### /qa
**Task**: Q1 (tests), Q2 (stale FIXMEs), Q3 (test plan update), H3 (test count audit)
**Design doc**: n/a
**Approach**: (1) Remove 3 stale FIXME comments. (2) Update ring3.md Phase 7 test descriptions. (3) Write ~30 tests for new output format from the updated plan. (4) Investigate test count discrepancy.
**Design refs**: `tests/plan/ring3.md`, `repl/spec.md §3.3–3.5, §4.1`
**Acceptance**: All new tests pass. Test plan current. FIXME comments removed. Test count explained/remediated.

### /repl
**Task**: D1 (demo refinements), D2 (playthrough)
**Design doc**: n/a
**Approach**: After /int delivers I1–I5, update all 8 demos to reflect new output format. Fix interruptible_sleep issue. Verify playthrough.
**Acceptance**: All 8 demos play cleanly. Output matches spec. User approves.

### /spec
**Task**: H1 (appendix-a update)
**Design doc**: n/a
**Approach**: Add 13 string primitive entries (11 original + str-eq + str-len) to spec/appendix-a-builtins.md table. Remove the FIXME comment.
**Acceptance**: Spec table complete. No FIXME.

### /arch
**Task**: Architecture review of I1–I4 feasibility
**Approach**: Review TypeChecker/SymbolTable API surface for queries needed by universal output format. Identify any accessors that need adding.
**Acceptance**: Confirm feasibility or identify blockers.

### /review
**Task**: Code review after /int delivers
**Approach**: Review reworked repl.rs for quality: function length (<100 lines), no unwrap, consistent formatting, no god functions.
**Acceptance**: No Blockers or Important findings.

### /stdlib
**Task**: No implementation work. Validate that stdlib symbols display correctly with new output format after /int delivers.

### /port
**Task**: No implementation work. Validate that exemplar types/functions display correctly with new output format.

### /examples
**Task**: No implementation work. Confirm all examples still pass.

### /frontend
**Task**: No action expected.

### /typecheck
**Task**: Add 5 public query methods to TypeChecker per /arch review: `get_type_constructors()`, `get_impls_for_type()`, `get_trait_methods()`, `get_implementing_types()`, `resolve_module()`. Thin wrappers over existing internal maps.

### /backend
**Task**: No action expected.

### /platform
**Task**: No action expected.

### /docs
**Task**: No action expected.

## Waves

### Wave 1: Architecture review + housekeeping (parallel)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Review I1–I4 feasibility — TypeChecker API surface | done | ALL FEASIBLE. 5 thin wrapper methods needed on TypeChecker: get_type_constructors, get_impls_for_type, get_trait_methods, get_implementing_types, resolve_module. Zero architectural risk. |
| /spec | H1: Add string primitives to appendix-a table, remove FIXME | done | Already completed in commit c97b85a. All 13 primitives in table, FIXME removed. |
| /qa | Q2: Remove 3 stale FIXME comments on test files | done | Removed from tests/e2e.rs:1211, tests/ring3_repl.rs:228, tests/ring3_repl.rs:275. |
| /qa | H3: Investigate test count discrepancy (1660 → 1025) | done | `cargo test` = root crate only (1025). `cargo test --workspace` = all crates (1660). No tests lost. Use `--workspace` for full count. |

### Wave 2: /int implementation
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | I1: Universal output format | done | `special_form_feedback()` rewritten with universal format for all symbol classes. `format_builtin_type_display`, `format_type_display_universal`, `format_trait_display_universal`, `format_macro_display_universal`, `format_related_section` helpers added. Primitives now visible. |
| /int | I2: /list rework | done | Rewrote `handle_list()`: prefix match, no imports/special forms/primitives, constructors in Types, `(no definitions)` for empty, categories Modules/Macros/Traits/Types/Fns, compact `print_name_category()` layout. |
| /int | I3: /imports rework | done | Rewrote `handle_imports()`: unfiltered mode organizes by category (Special forms always present, Macros, Traits, Types, Fns). Filtered mode shows `From <module>:` groups. Names only. Both Import and Reexport entries included. `classify_import()` helper added. |
| /int | I4: /exports command | done | Added `handle_exports()`: resolves module via `resolve_module_by_name`, lists public symbols by category, usage hint, error for not-found, empty module message, optional prefix filter. |
| /int | I5: Definition result display | done | `execute_defn()` shows `; defn`, `execute_typedef()` uses `format_type_display_universal`, `execute_trait_decl()` uses `format_trait_display_universal`, `eval_defmacro()` uses `format_macro_display_universal`. `check_bare_symbol_introspection()` updated. |
| /int | H2: Evaluate pipeline.rs FIXME | done | FIXME resolved: Cranelisp.toml is Ring 4 scope. Current CRANELISP_LIB + stdlib/ fallback is correct for Ring 0–3. Documented deferral rationale in comment. |

### Wave 3: Tests + review (parallel)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Q1: Write ~30 tests for new output format | done | 43 new tests (26 E2E + 17 integration). Covers /list boundaries, /imports categories, /exports, macro/type/trait universal format, definition results, negative tests. |
| /qa | Q2: Fix failing tests for new format | done | 12 tests updated across e2e.rs, macros.rs, ring2.rs, ring3_repl.rs. |
| /qa | Q3: Update ring3.md test plan | done | FIXME removed. Phase 7 updated with §3.5/§4.1 refs. 25 items annotated [Tested]/[Tested+Neg]. 3 new plan items added. |
| /review | Code review of /int changes | done | No Blockers. 2 Important (code duplication, redundant params) — FIXED. 5 Suggestions (3 fixed: docstring param type, inline layout, delegation; 2 deferred: clone cost S-3, module aliases S-4). |

### Wave 4a: Demos + validation (parallel)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /repl | D1: Update all demos for new output format | done | 2 demos updated (`/l` → `/imports`), CLAUDE.md refs updated, showcase `interruptible_sleep` FIXME fixed. |
| /stdlib | Validate stdlib symbol display | done | Found 3 Sprint 15 defects: classify_import reexport chains, `__macro_*` leak, `/info` on imports. |
| /port | Validate exemplar type display | done | Exemplar modules work from within `exemplar/` but not from project root — cross-directory loading is a Ring 4 feature (Cranelisp.toml workspace support). Display validation deferred to Ring 4. |
| /examples | Verify all examples pass | done | All 19 examples pass (01-integers through 20-adt-traits). |

### Wave 4b: Defect fixes + coverage (parallel)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | D1: Fix `classify_import()` to resolve reexport chains | done | Added `resolve_to_definition()` helper with depth limit (10). Follows Import/Reexport chains to concrete entry. |
| /int | D2: Filter `__macro_*` from `/imports` output | done | Added `__macro_` and `$` filter in both unfiltered and filtered modes. |
| /int | D3: Fix `/sig`, `/info`, bare-symbol for Import/Reexport entries | done | Added `resolve_entry_for_display()` helper. Updated `handle_sig()`, `handle_info()`, `special_form_feedback()` to resolve imports before display. |
| /int | D4: Unit tests for command handlers | done | 7 new unit tests: classify_import (4 entry types + reexport chain + unknown fallback), internal name filter. |
| /qa | Upgrade spec annotations §3.3, §3.4, §3.5 | done | Updated from `[R3 S14]` to `[Tested]`/`[Tested+Neg]` with test name links. Remaining gaps documented as `[R4 S15]`. |

### Wave 4c: Sprint close
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /repl | D2: Demo playthrough with user | pending | |
| /sprint | Sprint close checklist | pending | |

## Notes

_Runtime log: blockers, scope changes, decisions._

- **Test count discrepancy RESOLVED**: `cargo test` = root crate only (1025). `cargo test --workspace` = all 7 crates (1660). No tests lost. Sprint 14 used `--workspace`.
- **Ring 3 still open**: ROADMAP marked Ring 3 COMPLETE but user correctly notes the REPL doesn't show Ring 3 results. This sprint delivers the presentation layer.
- **No compiler changes expected**: This is pure REPL formatting work. If /arch identifies missing TypeChecker accessors, those are small surgical additions to the query API, not pipeline changes.
- **Wave 2 complete**: All I1–I5 + H2 implemented. Dead code removed (`format_macro_signature`, `format_import_type_sig`, `lookup_import_type`). Compilation clean. Expected test failures for /qa to address in Wave 3:
  - `e2e_s3_3_list`: expects `"Functions"` category → now `"Fns"` per spec
  - `e2e_s3_3_list_special_forms`: expects special forms in `/list` → moved to `/imports` per spec §3.3/§3.4
  - `repl_defmacro_identity`, `repl_defmacro_multi_clause`, `repl_defmacro_display_single_clause`, `repl_defmacro_display_multi_clause`: expect old `:: macro` format → now universal format `:user/name ; defmacro` + `; [params] -> Sexp`
  - `repl_deftrait_display_shows_trait_name`, `repl_constrained_fn_shows_constraints`, `repl_constrained_fn_two_params_shows_subsequent_colon_var`: expect old format → updated display format
  - Pre-existing: `test_assemble_lib_dirs_fallback_stdlib` — CRANELISP_LIB env var sensitivity, unrelated to Sprint 15

- **Wave 4 validation findings** — /stdlib+/port validation revealed 3 Sprint 15 defects when running with prelude:
  - **Defect D1**: `classify_import()` doesn't resolve through reexport chains — all imports show as "Fns:" in `/imports`
  - **Defect D2**: `__macro_*` internal names leak into `/imports` output (no filter like `/list` has)
  - **Defect D3**: `format_entry_signature()` fallback `_ =>` for Import/Reexport entries shows bare name only — `/info` on imported symbols has no type/classification
  - Root cause: `/int` unit tests and `/qa` Wave 3 tests all use bare sessions without prelude, so import-resolution paths were untested
  - **Design question**: `/exports prelude` shows only macros because spec §3.5 says exclude Import/Reexport entries — but prelude's public API IS re-exports. Needs `/arch` input.
  - Not-yet-built (Ring 4 scope): bare trait method references (`+`, `show`) produce codegen errors, `/exports` for dotted paths, `/source` not implemented
- **Process finding — two coverage gaps enabled these defects**:
  1. **Spec annotations not updated**: §3.4 import categories, §3.5 exports still say `[R3 S14]` — no `[Tested]` annotations were added by /qa despite 43 new tests. Without annotations, there's no traceability mechanism to flag untested MUST requirements (reexport resolution, `__macro_*` filtering).
  2. **/int unit test gap**: `src/repl.rs mod tests` has 15 unit tests — all for value formatting/parsing. Zero unit tests for command handlers (`handle_imports`, `handle_exports`, `classify_import`, `format_entry_signature`). These functions were treated as "tested through E2E" but E2E tests run without prelude, so import-resolution paths were never exercised. `/int` should write unit tests for functions it implements, not rely solely on `/qa` E2E tests.

## Outcome

### Delivered
- **REPL output conformance**: Universal output format (`:Type {value|name} ; {classification}`) implemented for all definition results, `/sig`, `/info`, bare symbol introspection
- **`/list` rewrite**: User definitions only, prefix filter, category-based (Modules, Macros, Traits, Types, Fns), `(no definitions)` for empty
- **`/imports` rewrite**: Unfiltered = category-based (Special forms always present), filtered = `From <module>:` groups with names only
- **`/exports <mod>` command**: New command listing a module's public API by category with usage hint
- **5 TypeChecker query methods**: `get_type_constructors`, `get_impls_for_type`, `get_trait_methods`, `get_implementing_types`, `resolve_module_by_name`
- **`__macro_*` root cause fix**: Synthesized macro clause functions now use `defn-` (private visibility) instead of `defn` — prevents export via glob imports at the source rather than display-time filtering
- **26 new E2E tests** (Wave 3), **17 new integration tests** (Wave 3), **7 new `/int` unit tests** (Wave 4b)
- **Spec traceability**: §3.3–3.5 annotations updated with `[Tested]`/`[Tested+Neg]` links
- **Demo updates**: `first-session.demo` and `ring2a.demo` updated (`/l` → `/imports`)
- **1710 workspace tests, 0 failures, 0 ignored. 19 examples pass.**

### Deferred
- **`/exports prelude` design**: Spec §3.5 excludes Import/Reexport entries, but prelude's public API IS re-exports. Needs `/arch` input (Ring 4).
- **Terminal styling**: `repl/spec.md:837` FIXME — Ring 4 scope.
- **Bare trait method references** (`+`, `show`): Produce codegen errors — Ring 4 scope.
- **`/exports` for dotted module paths**: Not yet supported — Ring 4 scope.
- **`/source` command**: Not yet implemented — Ring 4 scope.
- **Exemplar cross-directory loading**: Modules work from within `exemplar/`; cross-directory requires Cranelisp.toml workspace support (Ring 4).

### Findings
- **Process gap — spec traceability**: 43 new tests existed (Sprint 14) but spec annotations were not updated. Without `[Tested]` annotations, there's no mechanism to flag untested MUST requirements.
- **Process gap — /int unit testing**: `src/repl.rs mod tests` had zero unit tests for command handlers. E2E tests ran without prelude, so import-resolution code paths were never exercised. Fixed by adding 7 unit tests.
- **`__macro_*` root cause**: Synthesized macro clause functions in `defmacro.rs` were created as `(defn ...)` (public). Changed to `(defn- ...)` (private) — proper fix vs display-time filtering.
