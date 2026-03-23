# Sprint 23a: UAT Findings

**Status**: COMPLETE
**Ring**: 2–4 (cross-ring defects found during UAT)
**Goal**: Fix spec violations discovered during user acceptance testing — primitive name scoping (§8.9.1), QA process update.

## Scope

User acceptance testing after Sprint 23 exposed spec §8.9.1 violations that have been present since Ring 2. The compiler registers primitives as bare names in every module, violating the spec requirement that primitives are qualified-only (`primitives/add-i64`) unless explicitly imported. Additionally, qualified access and specific imports of primitives don't work.

This is a defect-fix sprint. No new features.

### Defect 1: Bare primitives resolve without import (§8.9.1)

Primitives like `add-i64`, `sub-i64` are registered as `Def` entries in every module's symbol table. The spec says they should only be in the `primitives` synthetic module.

**Owner**: `/int`
**Tests**: `module_neg_unimported_primitive_unbound`, `module_neg_primitive_module_scoping`, `synthetic_primitives_bare_without_import_fails_repl`, `synthetic_primitives_bare_without_import_fails_batch`

### Defect 2: Qualified `primitives/name` access fails (§8.9.1)

`(primitives/add-i64 2 3)` → "undefined variable: primitives/add-i64". Qualified access to synthetic modules should work.

**Owner**: `/int`
**Test**: `synthetic_primitives_qualified_access`

### Defect 3: Specific import from primitives fails (§8.9)

`(import [primitives [add-i64]])` → "'add-i64' not found in module 'primitives'". Only glob `(import [primitives [*]])` works.

**Owner**: `/int`
**Test**: `synthetic_primitives_explicit_import`

### Impact: stdlib needs import statements

Once defects 1-3 are fixed, stdlib files that use bare primitives (e.g., `stdlib/num/int.cl`, `stdlib/compare/eq.cl`) will break. `/stdlib` must add `(import [primitives [...]])` to affected files.

### QA process change (already applied)

The `/qa` skill definition was updated during this UAT cycle:
- Failing tests are the deliverable — `#[ignore]` only for future-sprint requirements
- Tests that expose in-scope spec violations stay failing until devs fix them
- Traceability via `// spec:` comments in tests, not spec-side annotations

## FIXME Debt

None — the failing tests ARE the signal. No FIXMEs needed.

## Waves

### Wave 1: Fix primitive name scoping (`/int`)

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Move primitive registration from per-module to `primitives` CompiledModule only | pending | Defect 1 |
| /int | Fix qualified name resolution for synthetic modules | pending | Defect 2 |
| /int | Fix specific import resolution for synthetic modules | pending | Defect 3 |

### Wave 2: stdlib import fixes (`/stdlib`)

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /stdlib | Add `(import [primitives [...]])` to all stdlib files using bare primitives | pending | Blocked on Wave 1 |

### Wave 3: Verify and close

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Verify all 6 failing tests pass | pending | |
| /qa | Check for regressions across full suite | pending | |

## Test Baseline

**6 failing tests** (all §8.9.1):
- `module_neg_unimported_primitive_unbound` (repl_negative.rs)
- `module_neg_primitive_module_scoping` (repl_negative.rs)
- `synthetic_primitives_qualified_access` (ring2.rs)
- `synthetic_primitives_explicit_import` (ring2.rs)
- `synthetic_primitives_bare_without_import_fails_repl` (ring2.rs)
- `synthetic_primitives_bare_without_import_fails_batch` (ring2.rs)

**0 failing tests. 4 ignored** (future sprint HKT/lazy).

**1211 tests passing** across 16 test binaries + 132 lib unit tests.

## Notes

- QA skill definition updated: failing tests are the deliverable, not `#[ignore]`
- `#[ignore]` only valid for future sprints or process-killing crashes
- Negative coverage plan updated: §8.9.1 entries changed from false "OK" to "FAILING"
- This sprint originated from a `/spec` investigation into how `stdlib/num/int.cl` references primitives without import
- Test helpers redesigned: `repl_session(prelude, preamble)` pattern with fixture files
- All tests now run through REPL sessions (not batch pipeline) — exposed 11 REPL-vs-batch divergences
- These divergences are real defects: REPL and batch must behave identically

## Outcome

### Delivered

**Spec §8.9.1 primitive name scoping** (3 compiler bugs fixed):
- Primitives no longer auto-seeded as bare names in every module — now only in `primitives` CompiledModule
- Qualified `primitives/add-i64` access works
- Specific `(import [primitives [add-i64]])` works (was broken, only glob worked)

**Duplicate parameter name rejection** (`/frontend`):
- `(defn bad [x x] ...)` now produces a parse error in all modes

**REPL trait constraint eagerness** (`/typecheck`):
- `(+ true true)` now produces "no impl of trait Num for type Bool" in REPL mode (was silently deferred)

**Cross-eval constrained poly monomorphisation** (`/backend`):
- GOT slots for monomorphised specializations now created across REPL eval boundaries
- TCO recognized for monomorphised self-recursion via SigDispatch

**Multi-module JIT name collision fix** (`/backend`):
- Functions in shared JIT now use module-qualified names to avoid collisions between modules
- Fixed SIGBUS/SIGSEGV crashes in `closure_and_tco`, `io_bind_with_named_function`, `io_trampoline_deep_bind_chain`

**Constrained type display fix** (`/int`):
- `:Num a :Num a` (constraint repeated on every occurrence per spec §3.5.1), was `:Num a :a`

**Test fixture bug** (ring2 inline trait preludes):
- Eq/Ord/Num trait definitions changed from `[self other]` to `[self self]` per spec §7.1.1

**QA process overhaul**:
- `/qa` skill definition rewritten: failing tests are the deliverable, `#[ignore]` only for future sprints
- Test helpers redesigned: `repl_session_with(prelude, preamble)` pattern with fixture files
- All batch-mode test helpers now use REPL sessions internally (single pipeline)
- `tests/fixtures/preamble_primitives.cl` created for standard primitive import preamble

### Deferred
- None — all defects fixed

### Findings
- Inline trait preludes in ring2.rs had `[self other]` instead of `[self self]` — violating spec §7.1.1. This masked the `(= 1 true)` type error for the entire project history.
- Switching test infrastructure from batch to REPL sessions exposed 11 REPL-vs-batch divergences — all fixed. REPL and batch now behave identically for all tested features.
- The `#[ignore]` philosophy was fundamentally wrong — it hid real defects behind a green build. The new rule: failing tests are the signal, `#[ignore]` is only for unscheduled future work.
