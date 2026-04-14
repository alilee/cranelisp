# Sprint 54: Clean & Green

**Status**: DRAFT
**Ring**: 4 (Effects — full spec scope)
**Goal**: Zero test failures — triage and fix all 58 failures to establish a clean baseline for Ring 4 gate review.

## Scope

Sprint 53 fixed the workspace build (backend API conformance, broken call site repairs) and unmasked 29 additional failures. The true failure inventory is 58 tests across these categories:

| Category | Count | Owner | Notes |
|----------|-------|-------|-------|
| ring4_trace | 20 | /backend or /int | Unmasked by S53 — trace codegen or pipeline issue |
| File watching E2E | 11 | /int | Pre-existing from S52 |
| Cache SIGSEGV/FAIL | 9 | /backend | 2 pre-existing + 7 unmasked (nice worker .o path) |
| Link tests | 5 | /backend | 1 pre-existing + 4 unmasked |
| Multi-sig batch | 4 | /typecheck | Pre-existing |
| Default method dispatch | 3 | /typecheck | Pre-existing |
| Persistence edge cases | 1 | /int | Pre-existing |
| parse-int Option | 2 | /typecheck | Pre-existing |
| checked_div panics | 2 | /backend or /int | Pre-existing |
| Constructor as value | 1 | /typecheck | Pre-existing |
| run-tests | 1 | /int | Pre-existing |
| v4_pipeline cache_hit | 1 | /backend | Unmasked |
| v4_repl_eval trace | 1 | /int | Unmasked |
| Batch primitive scoping | 1 | /int | Pre-existing |

### FIXME Debt (carried from S53)

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `linker.rs:231` | /backend | BL range limit for runtime/platform calls | pending |
| `session_v4.rs:3269` | /arch | Object codegen reconstructs CheckResult from CodegenInput fields | pending |
| `worker.rs:1205` | /int | Import/export/mod/platform forms redundant in Pass 2 | pending |
| `worker.rs:2011` | /backend | Dep symbol compilation is a no-op | pending |
| `worker.rs:2855` | /int | Refactor process_module_forms to take &mut ModuleSuspendState | pending |

{Remaining sections to be filled during sprint planning}
