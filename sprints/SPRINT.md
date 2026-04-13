# Sprint 52: Clean & Green

**Status**: ACTIVE
**Ring**: 4 (Effects — full spec scope)
**Goal**: Zero test failures, zero compiler/clippy warnings, ungate sprint23 tests (validate against spec first), CLI project root support. Establish a clean baseline for Ring 4 gate review.

## Scope

We are now at full spec scope — all rings are complete and every spec requirement is in play. This sprint focuses on getting to a clean, green test suite as the precondition for Ring 4 gate review and Phase H.

### Track 1: Ungate and triage sprint23 tests (70 tests → 63 after /reset deletion)

Gate removed. 30 pass, 40 fail. Triage complete — results by category:

**Delete (7 tests):** `/reset` command tests — `/reset` contradicts session persistence and is not in the current spec (§12 was rewritten to "Demo Trampoline"). Tests have stale spec references to sections that no longer exist.

**Not implemented — build (24 tests):**
- Session persistence (13): spec §15.2-15.3 says "not yet implemented" — update spec to normative, then implement. Source regeneration (`user.cl` backing file), cache integration, restart survival.
- File watching E2E (11): spec §14 is normative. `FileWatcher` infrastructure exists but E2E integration (shell escape to modify files, `[updated: ...]` notifications) is incomplete.

**Impl bugs — fix (8 tests):**
- Shell escape (5): change syntax from `;#!` to `/sh` (slash command, consistent with REPL command pattern). Partially implemented (`run_shell_command` exists) but output not reaching E2E stdout, exit code display missing (spec §13.4). `/repl` updates spec §13 for new syntax.
- Link mode (3): multi-module primitive resolution, output naming, `--no-cache` + `--link` rejection.

**Passing (30 tests):** batch main (3), link errors (4), link happy path (4), shell escape subset (6), watch subset (2), reset subset (6 — vacuously), persistence subset (3 — vacuously), cache (2).

### Track 2: Fix 25 existing test failures

Triage complete. Each test validated against spec.

**IMPL BUG — 14 tests (test correct, fix implementation):**

| Root Cause | Tests | Count | Spec |
|------------|-------|-------|------|
| DefnMulti crash (ast.rs:193 `params()` on multi-sig) | sketch_multi_sig_* (3), neg_multi_sig_bare_value_errors | 4 | §5.1.2 |
| Default method lookup ("no hard-coded default body") | sketch_default_method_* (3) | 3 | §7.1.5 |
| checked_div codegen (panic not triggering) | checked_div_* (2), sketch_checked_div | 3 | §12.7.3 |
| First-class constructor (`let [f MySome]` undefined) | sketch_adt_first_class_constructor | 1 | §5.2.7 |
| ADT type arg mismatch (`(MyOpt Int)` gets 0 params) | sketch_adt_display_option_int_batch | 1 | §7.3.2 |
| IO bind undefined var in .o compilation | io_bind_with_named_function | 1 | §10.3 |
| Platform not found in submodule | io_platform_non_entry_module_error | 1 | graceful error |

**TEST BUG — 4 tests (fix the test, not the implementation):**

| Test | Issue | Fix |
|------|-------|-----|
| parse_int_valid, parse_int_invalid | Defines inline `Option` conflicting with `primitives/Option` | Use `primitives/Option` constructors |
| sketch_pure_lifts_value | Uses lowercase `(pure 42)` — a library fn not in test prelude | Use `(Pure 42)` constructor directly |
| io_repl_forces_and_displays | Expects `IO` in output but REPL forces trampoline to inner value | Update assertion |

**SPEC GAP — 3 tests (spec needs clarification, then fix test or impl):**

| Test | Issue | Resolution needed |
|------|-------|-------------------|
| sketch_run_tests_pass_fn_called | `(fn [acc _ _] ...)` rejected as duplicate `_` | Spec should say `_` is exempt from dup check |
| sketch_trace_nanos_is_positive | `trace-nanos` undefined — name unclear | Clarify trace accessor names in spec |
| synthetic_primitives_bare_without_import_fails_batch | Batch auto-imports prelude which re-exports primitives | Clarify batch primitive scoping |

**PRELUDE/STDLIB — 4 tests (test infrastructure or import issues):**

| Test | Issue | Fix |
|------|-------|-----|
| sketch_platform_capture_read_input | `str-concat` needs explicit import | Add `(import [primitives [str-concat]])` |
| e2e_imported_fn_as_higher_order_arg_repl | Module `num.int` not discoverable | Fix test lib path configuration |
| cache_multi_module_transitive_imports | Submodule `main.mid` not found | Fix cache test module discovery |
| cache_quick_build_links_cached_objects | `undefined function: double` | Fix cross-module .o cache resolution |

### Track 3: Warnings cleanup

110 compiler/clippy warnings across 4 crates:
- cranelisp-typecheck: 22 (dead code, clippy suggestions)
- cranelisp-backend: 12 (unused import, unused field, clippy)
- cranelisp (lib): 75 (unsafe block annotations, unused vars, dead code, private interfaces)
- cranelisp (bin): 1 (dead code)

Many are auto-fixable. The unsafe block warnings (Rust 2024 edition compatibility) need `unsafe {}` blocks inside unsafe functions.

### Track 4: CLI positional arguments for project root & entry module

Currently the CLI has no way to specify project root or entry module — REPL mode hardcodes `user.cl` in cwd. The desired behaviour:

| Invocation | Project root | Entry module |
|---|---|---|
| `cranelisp` | cwd | `user` (default) |
| `cranelisp user` | cwd | `user` |
| `cranelisp mymod` | cwd | `mymod` |
| `cranelisp dir` | `dir` | `user` (default, looked up in dir) |
| `cranelisp dir/mymod` | `dir` | `mymod` |

This requires:
1. `/repl` specifies the behaviour in `repl/spec.md` §0
2. `/int` implements: `parse_args` returns project root and entry module as separate values (not a single path)
3. `/qa` writes tests covering the new invocation forms

### Out of scope

- Performance benchmarking (Sprint 53 — Ring 4 gate)
- Ring 4 gate review (Sprint 53 — after clean baseline)
- Phase H (Tier 2 backend)
- Post-restructure architecture doc (deferred — document current state after stabilisation)

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `checker.rs:302` | /arch | Remove type_modules map (FQTypeName done) | in scope — verify and delete |
| `linker.rs:231` | /backend | Runtime intrinsic and platform DLL function calls | triage — assess if blocking |
| `sprint23.rs:11` | /qa | Sprint23 tests disabled for v4 | **in scope — ungate, triage against spec** |
| `v4_pipeline.rs:359` | /frontend | Macro define-before-use not enforced (spec §5.13.2) | triage — validate spec requirement |
| `spec/08-modules.md:82` | /spec | Remove sibling fallback rule | in scope if touched |
| `session_v4.rs:3190` | /arch | Object codegen should accept CodegenInput directly | carried |
| `worker.rs:1181` | /int | Import/export/mod/platform dead code comment | in scope — cleanup |
| `worker.rs:1982` | /backend | Dep symbol compilation | triage |
| `worker.rs:2814` | /int | process_module_forms refactor | triage |
| `design/int/terminal-styling.md:367` | /int | println! not eprintln! | in scope if touching output |

## Architecture Review

**Reviewer**: /arch
**Verdict**: APPROVED

**Technical coherence**: PASS. Four tracks are independent workstreams converging on zero failures. Sprint23 ungating (Track 1) and existing failure fixes (Track 2) have no hidden dependencies. Track 3 (warnings) is mechanical. Track 4 (CLI args) is self-contained.

**No interim architecture**: PASS.
- Track 4 (parse_args): Returning `(Action, PathBuf, String, SessionSettings)` with project root and entry module separated is the right target structure. Eliminates the `slug()` and `base_dir()` helpers where the caller re-derives what the parser already knew. No interim infrastructure.
- Track 3 (warnings): Unsafe block changes (Rust 2024 edition) are straightforward `unsafe {}` wrapping. No semantic changes. Low risk.

**Design references**: Adequate. No new design doc needed — this is bug fixes and cleanup, not new mechanism.

**Interface gaps**: None. The `parse_args` change is internal to `main.rs`. `CompilerSession::new()` already takes `(SessionSettings, PathBuf)` for project root, and `register_module()` takes `&str` for module name. No boundary type changes required.

**Risk assessment**: Sprint23 ungating (70 tests, 3x deferred) is the main risk. Mitigated by spec-first triage approach. Total scope (95 test fixes + 110 warnings + 1 CLI feature) is ambitious but feasible — most work is mechanical (warnings) or diagnostic (triage).

**FIXME assessment**:
- `checker.rs:302` — Safe to delete. The `type_modules` map has been eliminated by FQTypeName migration. The `modules()` accessor is legitimate. /typecheck removes the stale FIXME during warnings cleanup.
- `session_v4.rs:3190` — Correctly carried. Real architecture debt (CheckResult reconstruction from CodegenInput). Not blocking this sprint; address before Phase H gate.
- All other FIXMEs correctly triaged.

## Skill Plans

### /qa
**Task**: (A) ~~Remove cfg gate~~ DONE. (B) ~~Triage sprint23 tests~~ DONE — 30 pass, 7 to delete (/reset), 32 to fix. (C) ~~Triage 25 existing failures~~ DONE — 14 impl bug, 4 test bug, 3 spec gap, 4 prelude. (D) Delete 7 /reset tests. (E) Fix 4 test bugs (parse-int Option, pure lowercase, IO display). (F) Fix 3 spec gap tests after /spec clarifies. (G) Fix 4 prelude/stdlib test infrastructure issues. (H) Update spec annotations for newly-passing tests.
**Design doc**: n/a
**Approach**: Triage complete. Delete /reset tests first. Fix test bugs. Await /spec for 3 spec gaps. Update traceability annotations as tests go green.
**Design refs**: `repl/spec.md`, `spec/*.md`, all test files
**Acceptance**: All test bugs fixed. /reset tests deleted. Spec annotations current. Zero test-side issues remaining.

### /int
**Task**: (A) Fix implementation defects identified by /qa triage (IO, shell escape, platform). (B) Implement CLI positional arguments per §0.5 — `parse_args` returns `(Action, PathBuf /* project_root */, String /* entry_module */, SessionSettings)`. (C) Implement `/sh` shell escape (replace `;#!` syntax per updated §13). (D) Implement session persistence per updated §15 (source regeneration to `user.cl`, cache integration, restart survival). (E) Fix file watching E2E integration (notifications reaching subprocess stdout). (F) Fix all compiler warnings in `src/`. (G) Resolve owned FIXMEs (worker.rs:1181, worker.rs:2814).
**Design doc**: `design/int/session-persistence.md` (update existing), `design/int/shell-escape.md` (if needed)
**Approach**: {to be filled by /int}
**Design refs**: `repl/spec.md` §0, §13, §14, §15, `src/main.rs`, `src/session_v4.rs`, `src/worker.rs`
**Acceptance**: Zero warnings in main crate. Positional CLI args work per §0.5. `/sh` replaces `;#!`. Session persistence works per §15. File watching E2E notifications work per §14. All /int-owned implementation gaps fixed.

### /typecheck
**Task**: (A) Fix multi-sig dispatch crash (ast.rs:193). (B) Fix default method lookup. (C) Fix parse-int Option FQTypeName mismatch. (D) Fix warnings in typecheck crate.
**Design doc**: n/a (regression fixes)
**Approach**: {to be filled by /typecheck}
**Design refs**: `crates/cranelisp-typecheck/src/`, `crates/cranelisp-types/src/ast.rs`
**Acceptance**: Zero warnings in typecheck crate. Multi-sig, default methods, and parse-int tests pass.

### /backend
**Task**: (A) Fix checked_div codegen. (B) Fix cache submodule resolution. (C) Fix cross-module fn-as-value. (D) Fix warnings in backend crate. (E) Resolve linker.rs:231 FIXME.
**Design doc**: n/a (bug fixes)
**Approach**: {to be filled by /backend}
**Design refs**: `crates/cranelisp-backend/src/`, `crates/cranelisp-backend/src/cache/`
**Acceptance**: Zero warnings in backend crate. checked_div, cache, and HOF tests pass.

### /frontend
**Task**: (A) Assess macro define-before-use FIXME (v4_pipeline.rs:359) — validate against spec §5.13.2. (B) Fix duplicate `_` param handling if spec allows it.
**Design doc**: n/a
**Approach**: {to be filled by /frontend}
**Design refs**: `spec/05-definitions.md` §5.13.2, `crates/cranelisp-frontend/src/`
**Acceptance**: FIXME assessed and resolved or deferred with rationale.

### /spec
**Task**: (A) Clarify 3 spec gaps identified by triage: (1) `_` as duplicate parameter name — should be exempt from dup check per functional language convention, (2) `trace-nanos` accessor name — clarify in appendix-a or §4.12, (3) batch primitive scoping — clarify whether batch mode auto-imports prelude (and thus primitives). (B) Resolve spec/08-modules.md:82 FIXME (sibling fallback rule). (C) Update spec annotations for tests fixed in this sprint.
**Design doc**: n/a
**Approach**: {to be filled by /spec}
**Design refs**: `spec/*.md`, `repl/spec.md`, `spec/appendix-a-builtins.md`, `spec/04-expressions.md` §4.12
**Acceptance**: 3 spec gaps clarified. All spec FIXMEs resolved. Annotations updated.

### /arch
**Task**: (A) Architecture review of sprint scope. (B) Resolve checker.rs:302 FIXME (type_modules cleanup). (C) Assess session_v4.rs:3190 FIXME.
**Design doc**: n/a
**Approach**: {to be filled by /arch}
**Design refs**: `design/arch/`
**Acceptance**: Architecture review complete. type_modules FIXME resolved.

### /stdlib
**Task**: (A) Validate stdlib compiles after fixes. (B) Verify prelude symbol availability (pure, str-concat, trace-nanos). (C) Assess parse-int stdlib migration.
**Design doc**: n/a
**Approach**: {to be filled by /stdlib}
**Design refs**: `stdlib/`, `stdlib/prelude.cl`
**Acceptance**: All stdlib modules compile. Prelude symbols available.

### /repl
**Task**: (A) ~~Specify CLI positional arguments in §0~~ DONE (§0.5 written). (B) Update spec §13 — change shell escape syntax from `;#!` to `/sh` slash command. (C) Update spec §15 — change session persistence from "not yet implemented" to normative requirements. (D) Remove any stale §12 references to `/reset` (§12 is now Demo Trampoline). (E) Create sprint demo `repl/demos/ring4k.demo`. (F) Verify all prior demos play cleanly.
**Design doc**: n/a (spec updates in repl/spec.md)
**Approach**: Spec-first: update §13 and §15, then /int implements, then /qa validates.
**Design refs**: `repl/spec.md` §0, §13, §14, §15, `repl/demos/CLAUDE.md`
**Acceptance**: §0.5 specifies positional args. §13 uses `/sh` syntax. §15 is normative. No stale /reset references. Demo plays cleanly.

### /review
**Task**: Code review of all bug fixes and warning cleanups.
**Acceptance**: 0 Blockers, all Important findings addressed.

### /port
**Task**: Validate exemplar compiles and runs after fixes.
**Acceptance**: Exemplar batch mode runs.

### /examples
**Task**: Verify all examples compile and run.
**Acceptance**: All `examples/*.cl` run successfully.

### /docs, /platform
**Task**: No primary assignment. Validate after fixes.

## Waves

### Wave 1: Spec updates + test cleanup (no code changes to src/)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /repl | Update §13: `;#!` → `/sh` slash command syntax | pending | Spec-first |
| /repl | Update §15: session persistence from "not yet implemented" to normative | pending | Spec-first |
| /repl | Remove stale /reset references from spec | pending | §12 is Demo Trampoline now |
| /spec | Clarify `_` duplicate param exemption | pending | Spec gap 1 |
| /spec | Clarify `trace-nanos` accessor name | pending | Spec gap 2 |
| /spec | Clarify batch primitive scoping | pending | Spec gap 3 |
| /spec | Resolve spec/08-modules.md:82 FIXME | pending | Sibling fallback rule |
| /qa | Delete 7 /reset tests from sprint23.rs | pending | Contradicts persistence |
| /qa | Fix 4 test bugs (parse-int Option, pure, IO display) | pending | Test-side only |
| /qa | Fix 4 prelude/stdlib test infrastructure issues | pending | Import/path fixes |

### Wave 2: Implementation — bug fixes (parallel, independent)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | Fix DefnMulti crash (ast.rs:193 `params()` on multi-sig) | pending | 4 tests |
| /typecheck | Fix default method lookup ("no hard-coded default body") | pending | 3 tests |
| /typecheck | Fix ADT type arg mismatch (`(MyOpt Int)` expects 0 params) | pending | 1 test |
| /typecheck | Fix checker.rs:302 stale FIXME (delete) | pending | Per /arch review |
| /backend | Fix checked_div codegen (panic not triggering) | pending | 3 tests |
| /backend | Fix cache submodule resolution + cross-module .o | pending | 2 tests |
| /backend | Fix linker.rs:231 FIXME (assess) | pending | |
| /int | Fix IO bind undefined var in .o compilation | pending | 1 test |
| /int | Fix platform not found in submodule (graceful error) | pending | 1 test |
| /int | Fix first-class constructor (`let [f MySome]`) | pending | 1 test — may be /typecheck |
| /int | Fix link multi-module primitive resolution | pending | 1 test |
| /int | Fix link output naming | pending | 1 test |
| /int | Fix `--no-cache` + `--link` rejection | pending | 1 test |
| /frontend | Fix duplicate `_` param (after /spec clarifies) | pending | 1 test |
| /frontend | Assess macro define-before-use FIXME (v4_pipeline.rs:359) | pending | |

### Wave 3: Implementation — new features (parallel, after Wave 1 spec)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | CLI positional arguments per §0.5 | pending | parse_args returns root + module |
| /int | `/sh` shell escape (replace `;#!` per §13) | pending | 5 tests |
| /int | Session persistence per §15 (source regen, cache, restart) | pending | 13 tests — largest item |
| /int | File watching E2E integration (notifications to stdout) | pending | 11 tests |
| /int | Resolve worker.rs:1181, worker.rs:2814 FIXMEs | pending | |

### Wave 4: Warnings cleanup (parallel with Wave 2-3 if no conflicts)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | Fix 22 warnings in typecheck crate | pending | Dead code, clippy |
| /backend | Fix 12 warnings in backend crate | pending | Unused import/field, clippy |
| /int | Fix 75 warnings in main crate | pending | Unsafe blocks, unused vars, dead code |
| /int | Fix 1 warning in binary crate | pending | Dead code |
| /qa | Fix test file warnings (scheduler, cache, v4_repl_eval, repl_experience) | pending | Unused vars/imports |

### Wave 5: Build/test/review
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Run full suite — target: 0 failures, 0 ignored | pending | |
| /qa | Update spec annotations for newly-passing tests | pending | |
| /review | Code review all changes | pending | 0 Blockers required |
| all | Fix failures + review findings, iterate | pending | |

### Wave 6: Showcase
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /repl | Create sprint demo repl/demos/ring4k.demo | pending | Persistence, /sh, CLI args |
| /repl | Verify all prior demos play cleanly | pending | |
| /port | Validate exemplar compiles and runs | pending | |
| /stdlib | Validate stdlib compiles | pending | |
| /examples | Verify all examples run | pending | |

## Notes

- **Spec-first triage is critical**: The user has emphasised that tests must be validated against the spec before assuming the implementation is wrong. The spec may need clarification in some cases.
- **Sprint 23 tests are 3x deferred**: User has approved ungating them. They should not survive behind a feature gate.
- **Full spec scope**: We are no longer ring-gating requirements. All spec requirements are in play.
- **Prior-ring coverage gaps**: 39 requirements from Rings 0-3 still lack [Tested] annotations. 11 MUST requirements lack +Neg coverage. These should be addressed as tests are fixed/validated.

## Outcome

{To be filled when sprint closes}

### Delivered

### Deferred

### Findings
