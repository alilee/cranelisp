# Pipeline v4 Roadmap

Status of the scheduler-driven architecture described in `pipeline-v4.md` and `concurrent-pipeline.md`.

## Current State (verified 2026-04-11)

The v4 pipeline is the only pipeline. `CompilerSession` in `session_v4.rs` is the unified session type. `main.rs` uses one code path for Run/Link/REPL. There is no `--v4` flag.

**What works:**
- One `CompilerSession`, one `run()`, all modes (Run, Link, REPL)
- `CompileScheduler` with full module lifecycle, priority ladder, blocking/unblocking
- Per-form typecheck via `tc.check_form()`
- Form-by-form worker loop in `process_module_forms()`
- Macro expansion blocking via scheduler priority codegen queue
- Lazy dependency discovery during form processing
- Expansion is a free function in `src/expander.rs` (MacroExpander trait deleted)
- REPL eval with TC snapshot/restore and scheduler-driven definitions
- Platform registry (`PlatformRegistry` with `HashMap<FQSymbol, PlatformFunction>`)
- Error cascade via `notify_module_failed` + `cascade_failure_locked`
- DashMap-backed TypeChecker module tables and codegen products
- Cache-hit loading via `try_cache_hit_load()` in worker.rs
- GOT with atomic slot-based table (`GotTable` with `AtomicPtr`)
- Scoped priority workers spawned per `register_module_with_source()` call
- Nice workers spawned as persistent threads in `CompilerSession::new()`, `.o` files produced
- `--link` mode fully implemented (`link_by_name` calls exe infrastructure)
- `--v4` CLI flag removed; `ReplSession` moved to `tests/helpers/mod.rs` (test-only)
- `src/repl/` directory deleted; `ModuleCodegenState`, `MacroEnv`, `CompilationSession` deleted
- Introspection fully populated (source, sexp, expanded, ast, clif_ir, disasm, code_size), gated on `--repl`
- File watcher extracted to `src/watch.rs`, wired into REPL loop in `main.rs` (init, sync, poll_and_reload)
- Session restructure phases A–F complete (new types: TypecheckProduct, CodegenProduct, Code, Introspection)
- Old pipeline code deleted (~12k+ lines removed across sprints 49 and session restructure)

**What doesn't work (test failures as of 2026-04-11):**
- Stdlib macro tests: 30/54 failing — session restructure regressed macro symbol availability (was 54/54 at commit `17a9906`)
- ring4_trace: 48 failures — trace tests broken (likely same macro/prelude regression)
- Cache tests: 36 failures
- sketch_port: 15 failures (down from 23, some fixed)
- IO tests: 24 failures
- v4_pipeline: 9 failures (cross-module macro + platform symbol resolution)
- Other: e2e (14), ring2 (8), macros (8), modules (6), lenient (6), ring3_repl (4), ring0 (2 checked_div), repl_negative (4), exemplar (1)
- Total: ~1407 passed, ~137 failed out of 1544

## Completed Steps

| Step | Description | Sprint |
|------|-------------|--------|
| 0 | North-star main.rs — one `run()`, all modes | 49 |
| 1 | Per-form typecheck API (`tc.check_form()`, `FormCheckResult`) | 40 |
| 2 | CompileScheduler (lifecycle, priority ladder, condvar blocking) | 41 |
| 3 | Form-by-form worker loop (`process_module_forms()`) | 41 |
| 4 | Macro expansion blocking (`block_for_macro_codegen()`) | 42 |
| 5 | Lazy dependency discovery (imports trigger recursive loading) | 43 |
| 6 | Remove MacroExpander trait (expansion is free fn in `expander.rs`) | 43 |
| 7 | REPL eval via scheduler (Additive strategy, TC snapshot/restore) | 44 |
| 8 | Platform registry (`PlatformRegistry`, DLL loading) | 45 |
| 9 | Error cascade (`notify_module_failed`, `cascade_failure_locked`) | 45 |
| 10 | Nice workers as persistent threads (`.o` production, `wait_object_complete`) | 46 |
| 11 | Persistent priority workers — **deferred**, scoped workers are correct | — |
| 12 | DashMap (TC module tables, codegen products; TC serialized via `tc_mutex`) | 47 |
| 13 | Cache-hit loading (`try_cache_hit_load()`, symbol table restore) | 48 |
| 14 | File watcher (`src/watch.rs`, init/sync/poll_and_reload in REPL loop) | REPL rework |
| 15a | `link_by_name` (exe validation, startup object, system linker) | 49+ |
| 15b | v4_pipeline test infrastructure (`--v4` flag references removed) | 49+ |
| 15c | Dead code cleanup — `src/repl/` deleted, `CompilationSession`/`MacroEnv`/`ModuleCodegenState` deleted | session restructure |

## Remaining Work

### 1. Macro/prelude regression (BLOCKING — ~120 of 137 test failures)

The session restructure (GOT unification, SharedState DashMaps, introspection gating) regressed macro symbol availability. At commit `17a9906` all 54 stdlib tests passed; currently 30/54 fail. This is the root cause of most test failures across stdlib, trace, cache, IO, and e2e test binaries.

**Symptoms:** `"undefined variable: SexpStr"`, `"undefined variable: cond"`, macro expansion can't find `macros` module constructors or prelude macro names in user module scope.

**Likely cause:** Macro symbol table registration or prelude export propagation broken during session restructure commits. The prelude loads successfully but its macros are not accessible at expansion time.

**Investigation:** Compare macro registration path at `17a9906` vs HEAD. Focus on `inject_macros_import`, prelude symbol export, and how expanded macro code resolves `macros` module symbols in user context.

### 2. Dead code in `src/session.rs` (MINOR — 35 lines)

`ObjectWorkerState` struct and impl (lines 139–173) are defined but never used outside session.rs. Safe to delete.

### 3. FQTypeName migration (DEFERRED — architectural improvement)

FIXME in `crates/cranelisp-types/src/types.rs:23`: `Type::ADT(TypeName, ...)` should be `Type::ADT(FQTypeName, ...)`. Requires ~182 call sites. Not blocking functionality — display works via separate `type_modules` lookup.

### 4. Persistent priority workers (DEFERRED — design improvement)

Priority workers are scoped per `register_module_with_source()` call, not session-persistent. Functionally correct for batch and REPL. Suboptimal for REPL (fresh thread scope per eval). Not blocking any tests.

### 5. BL range fix (DEFERRED — correctness on large binaries)

FIXME in `crates/cranelisp-backend/src/cache/linker.rs:231`: runtime intrinsic and platform DLL function calls use BL (±128MB range). If loaded `.o` code is far from these functions, BL will fail. Fix: use literal pool entries (ADRP+LDR+BLR). Only manifests with very large codebases or unlucky memory layout.

### 6. File watcher manual testing (DEFERRED — interactive-only)

Code is fully wired (src/watch.rs → session_v4.rs → main.rs). Needs end-to-end manual verification with actual file edits in a running REPL session.

### 7. Ring 4 acceptance gaps

| Gap | Status |
|-----|--------|
| Sketch-port test triage | 15 failures (down from 23). Need triage: real gaps vs sketch-specific |
| Performance benchmarking | Not measured. No benchmark infrastructure exists |
| Exemplar validation | 1 test failure (`exemplar_batch_cross_module_adt`). Not fully E2E validated |
| REPL experience edge cases | Coverage gaps in spec conformance |
| Ring 4 gate review | Not performed |
| checked_div runtime panics | 2 ring0 failures: `div-i64` doesn't panic on ÷0 or i64::MIN/-1 |

## Priority Order

```
1. Fix macro/prelude regression     ── unblocks ~120 test failures
   │
   ▼
2. Delete ObjectWorkerState         ── trivial cleanup
   │
   ▼
3. Sketch-port test triage          ── determine real gaps (15 failures)
   │
   ▼
4. checked_div runtime panics       ── 2 ring0 failures, spec §12.7.3
   │
   ▼
5. Exemplar E2E validation          ── validates language at scale
   │
   ▼
6. Ring 4 gate review               ── formal review before Phase H
```

Items 3–5 (FQTypeName, persistent priority workers, BL range) are deferred indefinitely — they don't block Ring 4 completion.
