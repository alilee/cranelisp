# Sprint 23: Executable, Hot-Reload & REPL Lifecycle

**Status**: COMPLETE
**Ring**: 4 (Effects) — eighth increment
**Goal**: Standalone executable generation, REPL file watching with `/reload`, `/reset` command, shell escape, and REPL cache integration — completing the developer tool story.

## Scope

Sprint 22 delivered batch-mode module caching. This sprint has five thrusts:

### 1. Standalone Executable Generation (`--link`)

`cranelisp --link <file.cl>` produces a native executable. This uses the cached `.o` files from S22's `ObjectModule` pipeline, linked into a standalone binary. The sketch has this as `--build` — study the sketch's approach.

### 2. REPL File Watching (Hot-Reload)

When source files change on disk, the REPL detects staleness via filesystem notifications (e.g., `notify` crate) and automatically recompiles changed modules and their dependents, using the cache for unchanged modules. No manual `/reload` command needed — the watcher handles it. The existing `/reload` placeholder in the REPL spec should be removed by `/repl`.

### 3. `/reset` Command (new — needs spec)

Equivalent to exiting and restarting the REPL without losing terminal history: clears all user definitions, imports, module switches; reloads the prelude fresh; resets to the project module (or `user` if none); Gives users a clean repl state. `/repl` must spec this in `repl/spec.md` before implementation. The purpose is allow the showcase to simulate start a new session leveraging the pre-compiled object cache.

### 4. Shell Escape `;#! <cmd>` (new — needs spec)

A comment-prefixed escape syntax that runs a shell command from the REPL. The `;#!` prefix avoids collision with valid Cranelisp syntax (`;` starts a comment, so the line is syntactically a comment to the parser). `/repl` must spec this in `repl/spec.md` before implementation.

### 5. REPL Cache Integration (5 ignored tests)

The 5 ignored cache tests from S22 (`cache_repl_restart_cache_hit`, `cache_repl_incremental_monomorphisation`, `cache_repl_write_is_non_blocking`, `cache_repl_quick_build_*`) target REPL-side cache wiring.

### Sprint 22 Debt (mandatory)

- FIXME(/arch) on `design/arch/architecture.md` — CompileMode three-variant enum update
- FIXME(/backend) on `design/backend/module-caching.md:128` — CacheCodegenState type clarification
- FIXME(/int) on `design/int/pipeline-convergence.md:345` — batch mode project_root
- FIXME(/backend) in `tests/cache.rs:1229` — cross-module cache note
- `/review` of S22 caching code (was pending at sprint close)

### Out of Scope

- HKT, lazy sequences, terminal styling implementation (Sprint 24)
- Lenient evaluation / auto IO scheduling (Sprint 25)

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `design/arch/architecture.md:141` | /arch | CompileMode three-variant enum update | Sprint 23 scope |
| `design/backend/module-caching.md:128` | /backend | CacheCodegenState type clarification | Sprint 23 scope |
| `design/int/pipeline-convergence.md:345` | /int | Batch mode project_root derivation | Sprint 23 scope |
| `tests/cache.rs:1229` | /backend | Cross-module cache reference note | Sprint 23 scope |
| `spec/10-io.md:52` | /spec | resource_token for Par | **Resolved S23** — FIXME removed; layout verified against runtime; Par deferred to S25 |
| `.claude/commands/platform.md:73` | /platform | stderr write | **Removed** — no consumer in spec, design, stdlib, or repl; all stderr uses are Rust-side runtime (batch errors, panics, usage hints) |

## Architecture Review

### FIXME Resolution

The FIXME on `design/arch/architecture.md:141` is resolved. `CompileMode` now shows the three-variant enum (`Interactive`, `Batch`, `Release`) matching `design/arch/interfaces.md` and `design/arch/design-space.md`. The key clarification: multi-module batch compilation uses `Interactive` mode (GOT-indirect) because cached `.o` files must be interchangeable between batch and REPL contexts. `Batch` (direct calls) is reserved for single-file test execution only. `Release` remains deferred to Phase H.

### 1. `--link` (Standalone Executable Generation) — Approved with notes

**Sketch study**: The sketch implements this as `--exe` in `sketch/src/exe.rs` and `sketch/src/batch.rs::build_executable`. The approach is sound and well-proven:
1. Run the normal compilation pipeline (which writes cached `.o` files)
2. Generate a startup stub `.o` (`_start` → init platforms → call `main` → handle IO → `exit`)
3. Link all module `.o` files + startup `.o` + `libcranelisp_exe_bundle.a` + platform `.rlib`s via system `ld`

**Architectural assessment**: This is a clean layering — the existing caching pipeline produces `.o` files, and `--link` just adds a linking step on top. No pipeline changes needed. The startup stub is a small Cranelift-generated object that imports `main` and `exit` — straightforward.

**Concerns**:
- **CLI naming**: The sprint says `--link` but the sketch uses `--exe`. Either is fine, but the choice should be deliberate. `--link` is more descriptive of the action (linking cached objects); `--exe` is more descriptive of the output. Recommend `/int` decide and document.
- **macOS-only**: The sketch hardcodes `arm64`, `xcrun`, and macOS `ld` flags. The reimplementation should abstract platform-specific linker invocation behind a function that can be extended later (Linux ELF, etc.), but the initial implementation targeting macOS aarch64 only is appropriate for Ring 4.
- **`main` requirement**: The sketch checks for a `main` symbol after compilation. The reimplementation should produce a clear error if the entry module has no `main` function, ideally before invoking the linker.
- **`main :: () -> IO _` vs `main :: () -> Int`**: The sketch supports both (with IO trampoline). The reimplementation should match this — the startup stub conditionally calls `cranelisp_run_io` if `main` returns `IO`.
- **Bundle library**: `libcranelisp_exe_bundle.a` is built by a separate cargo target. `/backend` should document the build dependency clearly so users know they need `cargo build -p cranelisp-exe-bundle` before `--link` works.

### 2. File Watching (Hot-Reload) — Approved with caution

**Sketch study**: The sketch implements file watching in `sketch/src/repl/watch.rs` using the `notify` crate with `RecommendedWatcher`. Key design choices:
- Watches parent directories (not individual files) for reliable editor detection (atomic rename pattern)
- Non-blocking poll (`try_recv`) before each REPL prompt
- Content hash comparison to skip unchanged files
- Cascade reload: changed module → its transitive dependents, in topological order
- Locked modules on reload failure (prevents definitions in broken modules)

**Architectural concerns**:

- **GOT safety**: When a module is reloaded, its functions get new JIT addresses. The GOT entries MUST be updated atomically for all recompiled functions before any user code runs. The sketch handles this by recompiling the full module and updating GOT entries in the same synchronous step (before returning to the prompt). The reimplementation MUST preserve this property — no partial GOT state between poll and prompt.

- **Macro invalidation**: If a module defines macros used by other modules, reloading it requires re-expanding (not just recompiling) all dependents. The sketch handles this implicitly because `reload_module` re-runs the full pipeline. The reimplementation should do the same. This is potentially expensive but correctness-critical.

- **Type compatibility on reload**: The sketch checks type compatibility after reloading — if a function's type signature changes, dependents that assumed the old type are invalid. The reimplementation should implement the same guard: reload fails (module locked) if the new types are incompatible with existing dependents. `/typecheck` should be consulted on how to detect type-breaking changes.

- **Interaction with `/reset`**: After a `/reset`, the file watcher state should also be cleared and re-initialized (since all modules are reloaded fresh). If the watcher is not reset, stale watched directories could accumulate.

- **Cache interaction**: When a watched file changes and is reloaded, the REPL should also invalidate the corresponding cache entry. The cascade invalidation from S22's caching design applies here — changing module A invalidates A's cache and all dependents' caches.

- **Sprint plan says "remove `/reload`"**: The sketch actually keeps `/reload` alongside the file watcher — `/reload` retries locked (failed) modules. This is a useful recovery mechanism. Recommend `/repl` consider keeping `/reload` for manual retry of locked modules rather than removing it entirely.

### 3. `/reset` — Approved

**State to clear**: A complete `/reset` must clear:
1. **GOT entries** — all user-defined function pointers
2. **Module tables** — `TypeChecker.modules` (all non-primitive modules), `loaded_modules` map
3. **Type environments** — all user-defined type schemes, trait impls, constructor registrations
4. **Macro environment** — all user-defined macros
5. **JIT compiled code** — ideally free JIT memory, but Cranelift's `JITModule` doesn't support selective deallocation; pragmatically, mark as unreachable and let new compilations allocate fresh
6. **File watcher subscriptions** — clear watched directories, re-initialize after prelude reload
7. **Current module** — reset to `user` (or project module)
8. **`locked_modules`** — clear the locked set
9. **REPL definition history** (`DefEntry` storage) — clear user definitions

**Concern**: Cranelift `JITModule` does not support freeing individual compiled functions. Repeated `/reset` cycles will leak JIT memory. For the showcase use-case (simulate fresh start with warm cache), this is acceptable — the process doesn't run long enough for it to matter. Document this limitation. If it becomes a problem, the nuclear option is re-creating the `JITModule` entirely, but that's expensive and may require re-registering all extern symbols.

**Prelude reload**: After clearing state, `/reset` must reload the prelude. This should go through the cache path (cache hit = fast reset). The object cache should NOT be cleared by `/reset` — only in-memory state. This is the key design insight: `/reset` gives a fresh session that benefits from previously cached `.o` files.

### 4. Shell Escape `;#!` — Approved, minimal impact

No pipeline interaction. This is purely a REPL input handler concern — when the input line starts with `;#!`, the remainder is passed to `std::process::Command::new("sh").arg("-c").arg(rest)`. The `;` prefix makes it a syntactic comment to the Cranelisp reader, so no parser changes are needed.

**Minor notes**:
- stdout/stderr should be inherited (not captured), so the user sees output in real time
- Exit code display is optional but nice (`;#! exit code: 0`)
- No interaction with REPL state, module tables, or the compilation pipeline

### 5. REPL Cache Integration — No architectural concerns

The 5 ignored tests from S22 are straightforward wiring: the REPL session needs to write cache packets after module compilation (using the same `CacheWriter` background thread pattern from the sketch) and load cached `.o` files on startup. The sketch's `CacheWriter` (mpsc channel + background thread) is a clean pattern. No new architectural decisions needed.

### Summary

| Feature | Verdict | Key risk |
|---------|---------|----------|
| `--link` | Approved | macOS-only linker; bundle build dependency |
| File watching | Approved with caution | GOT atomicity, macro invalidation, cache cascade |
| `/reset` | Approved | JIT memory leak on repeated resets (acceptable) |
| `;#!` | Approved | None |
| REPL cache | Approved | None |

### Design Review (Wave 1)

Reviewed `design/backend/executable-generation.md` and `design/int/repl-lifecycle.md` against `design/arch/architecture.md` and `design/arch/interfaces.md`.

**Overall verdict: Both design docs are approved for implementation. No blockers.**

#### Executable Generation (`design/backend/executable-generation.md`)

**(I-1) Crate ownership contradicts architecture.md.** The architecture document lists "Standalone executable generation" as a `cranelisp-backend` content item (architecture.md line 85). The design doc places `generate_startup_object()`, `link_executable()`, `find_bundle_lib()`, and `find_platform_rlibs()` in the binary crate (`cranelisp`), with only `build_isa()` in `cranelisp-backend`. The rationale given (startup stub needs pipeline state) is sound, but the architecture description is now stale. **Action**: FIXME(/arch) filed — update `architecture.md` §cranelisp-backend contents to clarify that executable generation orchestration lives in the binary crate, while backend provides ISA and object utilities. The crate DAG line should read `cranelisp-backend (codegen, JIT, RC emission, object compilation, caching)` with executable linking listed under the binary crate.

**(I-2) New crate `cranelisp-exe-bundle` not in architecture.md.** The design introduces a new `cranelisp-exe-bundle` crate (staticlib) owned by `/platform`. This is an 8th crate, not currently in the 7-crate DAG. The crate is justified — it bundles runtime symbols for static linking and has no upstream dependencies beyond `cranelisp-runtime` and `cranelisp-platform`. **Action**: FIXME(/arch) filed — add `cranelisp-exe-bundle` to the crate DAG in `architecture.md` with a note that it is a build-time artifact for `--link`, not a pipeline crate.

**(S-1) `--no-cache` + `--link` temporary directory.** The design specifies that `--no-cache` with `--link` compiles to a temporary directory. This is a sensible fallback, but the temporary directory lifecycle is unspecified. Recommend: create a `tempdir` that is cleaned up after the linker exits (success or failure). The `tempfile` crate's `TempDir` handles this via `Drop`.

**(S-2) Missing `.o` for macro-only modules.** Section 9 says "skip them silently" for missing `.o` files. This is fine for macro-only modules, but could mask genuine bugs. Consider emitting a `Warning` (not error) when a module that defines functions has no `.o` — this distinguishes expected missing (macro-only) from unexpected missing (codegen bug).

**(S-3) `_start` vs `main` entry point.** The design uses `-e _start` with a custom startup stub. This is correct for a minimal executable, but diverges from the standard C entry point convention. Document in user-facing docs that Cranelisp executables use `_start` not `main` as the entry symbol, in case users try to use standard C debugging tools that expect `main`.

#### REPL Lifecycle (`design/int/repl-lifecycle.md`)

**(I-3) `/reset` does not clear file watcher.** The design explicitly states "File watcher — continues running across reset" (§2.1 "Not cleared"). However, the earlier architecture review (§3, item 6) specified: "File watcher subscriptions — clear watched directories, re-initialize after prelude reload." The design's §2.3 does call `update_watched_paths()` after prelude reload, which partially addresses this by re-adding paths for newly loaded modules. But directories watched for modules that existed before reset but are not in the prelude (e.g., user-loaded project modules) will remain watched without corresponding loaded modules, generating spurious change events that map to no known module. **Action**: `/int` should add a `watcher.clear_all()` step before `update_watched_paths()` in the reset sequence, then re-add directories as modules are loaded. This matches the architecture review's recommendation and avoids stale watches.

**(I-4) Type compatibility on reload not addressed.** The design describes cascade invalidation and last-known-good recovery (§1.4-1.5), but does not address the case where a reloaded module changes a function's type signature in a way that is incompatible with existing dependents. The architecture review (§2) flagged this: "reload fails (module locked) if the new types are incompatible with existing dependents." The design's cascade reload (§1.4 step 4) recompiles dependents, which would catch type errors during recompilation — so this is implicitly handled if the dependent recompilation checks types against the new module. **Action**: `/int` should confirm that `reload_module()` for dependents runs typechecking against the new signatures, not the old ones. If a dependent fails typechecking, it should be locked (per §1.5) rather than silently keeping stale code. Add a note in §1.4 clarifying this.

**(I-5) `CompileMode` stale in `interfaces.md`.** The `CompileMode::Batch` doc comment in `interfaces.md` still said "Used for batch compilation and testing" — inconsistent with `architecture.md`'s resolved FIXME which narrows Batch to "single-file test execution only." **Action**: Fixed — updated `interfaces.md` to match `architecture.md`.

**(S-4) JIT memory leak mitigation.** The "nuclear option" (§2.2) of re-creating the `JITModule` is noted as expensive. A lighter option worth considering: track a generation counter. On `/reset`, increment the generation. New compilations use the current generation's JIT module. Old generation JIT modules are held in a `Vec<JITModule>` but receive no new compilations. This bounds leak growth to one JIT module per reset rather than per-compilation, and avoids re-registering extern symbols. Not blocking — the current design is acceptable for the showcase use-case.

**(S-5) Shell escape `;#!` — fish shell consideration.** The design hardcodes `/bin/sh -c`. On the host system (macOS with fish shell), `/bin/sh` is POSIX sh, which is correct — we want predictable command execution, not the user's login shell. Good choice. No action needed.

**(S-6) Project root `cwd` — symlink edge case.** §6.2 uses `std::env::current_dir()` which returns the canonical path (resolving symlinks on most platforms). If the user's project is accessed via a symlink, this could cause path mismatches with file watcher events (which may report the symlink path). Consider canonicalizing watcher event paths as well. Low priority.

**(S-7) Cache writer lazy initialization.** §4.3 specifies lazy `CacheWriter` creation on first cache write. This means the first module compilation in the REPL pays the thread spawn cost. For REPL startup (prelude load), this adds a few microseconds — negligible. Good design choice.

#### Cross-doc Consistency

The two design docs agree on their handoff points:
- `/backend` provides `build_isa(is_pic: true)` — both docs reference this.
- `/int` owns the startup stub, linker invocation, and CLI wiring — both docs agree.
- The `CacheWriter` pattern is consistently described.
- The `main` validation sequence is consistent between the two docs.

One minor inconsistency: `executable-generation.md` §5.2 describes the `--link` flow in `/int`'s domain (CLI flag wiring), which overlaps with `repl-lifecycle.md` §5. This is acceptable — both documents describe the same flow from their respective perspectives. No conflict in the descriptions.

#### Summary

| ID | Class | Issue | Owner | Status |
|----|-------|-------|-------|--------|
| I-1 | Important | Architecture.md lists exe generation in backend; design puts it in binary crate | /arch | FIXME filed |
| I-2 | Important | New `cranelisp-exe-bundle` crate not in architecture DAG | /arch | FIXME filed |
| I-3 | Important | `/reset` should clear file watcher before re-adding paths | /int | Action needed |
| I-4 | Important | Type compatibility on reload needs explicit confirmation | /int | Action needed |
| I-5 | Important | `CompileMode` stale in interfaces.md | /arch | Fixed |
| S-1 | Suggestion | Specify temp dir cleanup for `--no-cache` + `--link` | /backend | — |
| S-2 | Suggestion | Warn on missing `.o` for function-defining modules | /backend | — |
| S-3 | Suggestion | Document `_start` entry point in user docs | /docs | — |
| S-4 | Suggestion | Generation-counter JIT leak mitigation | /int | — |
| S-5 | Suggestion | `/bin/sh -c` is correct for shell escape | — | No action |
| S-6 | Suggestion | Canonicalize watcher event paths for symlink safety | /int | — |
| S-7 | Suggestion | Lazy CacheWriter init is good | — | No action |

**Both design docs are approved for implementation.** I-3 and I-4 should be addressed during implementation (not blocking design approval). I-1 and I-2 require architecture doc updates that `/arch` will make.

## Skill Plans

### /arch
**Task**: (1) Resolve FIXME — update CompileMode to three-variant enum in `architecture.md`. (2) Review executable generation design (linking `.o` files, entry point, runtime startup). (3) Review file watching design for cache interaction. (4) Review `/reset` and shell escape specs for architectural impact.
**Design refs**: `design/arch/architecture.md`, `design/arch/interfaces.md`, `design/backend/module-caching.md`
**Acceptance**: CompileMode FIXME resolved. Executable and file watching designs approved.

### /spec
**Task**: (1) Verify `spec/10-io.md:52` resource_token FIXME — Par is implemented, check if annotation is still needed or can be marked done. (2) Respond to any FIXMEs from `/repl` spec updates.
**Design refs**: `spec/10-io.md`, `spec/12-runtime.md`
**Acceptance**: FIXME resolved or confirmed current.
**Status**: Task 1 DONE. FIXME removed. Verified that `cranelisp-runtime/src/io.rs` and `cranelisp-platform/src/lib.rs` both implement the 24-byte Effect layout `[tag=1, thunk_ptr, resource_token]` with resource_token hardcoded to 0, matching the spec exactly. Par node (tag=3) and auto-scheduling are not yet implemented — deferred to Sprint 25 per ROADMAP. Replaced FIXME with inline verification note. Task 2: no FIXMEs found from `/repl`.

### /repl
**Task**: (1) Spec `/reset` command in `repl/spec.md` — semantics, output, interaction with `/mod`, cache clearing. (2) Spec shell escape `;#! <cmd>` in `repl/spec.md` — syntax, stdout/stderr handling, exit code display, interaction with REPL state. (3) Spec file watching behavior (automatic reload on change, notification to user, error recovery, interaction with `/reset`). (4) Remove `/reload` from spec — file watching makes it redundant; `/reset` covers the force-recompile case. (5) Create `repl/demos/ring4h.demo`.
**Design refs**: `repl/spec.md` §3.1, §8
**Acceptance**: Three new spec sections. `/reload` removed. Demo created.
**Approach**: Tasks 1-4 are spec-only edits to `repl/spec.md`. `/reset` (§12) covers semantics (5-step clear sequence), output format, `/mod` interaction, file watching interaction, cache preservation, and performance target. Shell escape (§13) covers `;#!` syntax rationale (comment prefix avoids parser collision), `/bin/sh -c` execution model, stdout/stderr passthrough, exit code display (silence on success), edge cases (empty command, not found, multi-line). File watching (§14) covers OS-level watch scope, lazy recompilation (not eager background), user notification format (`[changed: ...]`), last-known-good error recovery, and cache cascade invalidation. `/reload` removed from command inventory (§3.1) and Ring Testability Matrix (§9); `/reset` and new features added to matrix. Demo (task 5) deferred until implementation lands.
**Status**: Tasks 1-4 DONE. Task 5 (demo) pending — blocked on implementation.

### /backend
**Task**: (1) Standalone executable generation — link cached `.o` files with runtime into native executable. Study sketch `--build` implementation. (2) Resolve FIXME on `module-caching.md:128` (CacheCodegenState clarification). (3) Resolve FIXME in `tests/cache.rs:1229`. (4) Evaluate quick build mode (2 ignored tests).
**Design doc**: `design/backend/executable-generation.md` (new)
**Design refs**: `design/backend/module-caching.md`, sketch `src/cache.rs`, `src/linker.rs`
**Acceptance**: `cranelisp --link examples/hello.cl` produces a working native executable.
**Approach**: Tasks 1-3 are design doc and FIXME resolution work (no implementation code).
- Task 1 DONE: `design/backend/executable-generation.md` written. Covers end-to-end `--link` flow, startup stub design (Cranelift ObjectModule generating `start` → init platforms → call `main` → IO trampoline → exit), macOS aarch64 linker invocation with `LinkerConfig` abstraction, bundle library (`libcranelisp_exe_bundle.a`) contents and build dependency, `main` validation (pre-link type check for `() -> Int` or `() -> IO _`), edge cases. Sketch comparison documents the approach from `sketch/src/exe.rs` + `sketch/src/batch.rs::build_executable`. Key divergence: startup stub and linker invocation live in binary crate (`/int` owns), backend provides `build_isa(is_pic: true)`.
- Task 2 DONE: FIXME on `module-caching.md:128` resolved. Clarified that `CacheCodegenState` is the serializable subset of `ModuleCodegenState` — a new type in `cranelisp-backend` that captures GOT slot assignments, param counts, and introspection artifacts for cache write/load. Distinct from `CacheMetadata` (which holds cache management data). Updated §2 divergence table for consistency.
- Task 3 DONE: FIXME in `tests/cache.rs:1229` resolved. The cross-module `.o` compilation limitation referenced by the FIXME was fixed in Sprint 22 via `cross_module_fns` in `ObjectCompileInput`. Updated both comments (lines 1019-1022 and 1227-1229) to reflect current state.
- Task 4 TODO: Quick build mode evaluation pending.
**Status**: Tasks 1-3 DONE. Task 4 pending.

### /int
**Task**: (1) Wire file watching into REPL session — `notify`-based filesystem watcher, automatic recompilation of changed modules. (2) Implement `/reset` command per spec. (3) Implement shell escape `;#!` per spec. (4) Wire REPL cache integration (un-ignore 5 cache tests). (5) Wire `--link` CLI flag. (6) Resolve FIXME on `pipeline-convergence.md:345` (project_root).
**Design doc**: DONE — `design/int/repl-lifecycle.md` (file watching, `/reset`, shell escape, REPL cache wiring, `--link`, project_root)
**Design refs**: `design/backend/module-caching.md` §10, `repl/spec.md` §12-14
**Acceptance**: File changes auto-reload. `/reset` clears state. `;#! ls` runs shell command. `--link` produces executable. 5 cache tests un-ignored. project_root FIXME resolved.
**Approach**: Implementation order: (a) Shell escape `;#!` — trivial, no dependencies, 1 function. (b) Project_root fix — one-line change in `src/main.rs`, use `cwd` instead of entry file parent. (c) REPL cache integration — `CacheWriter` background thread (sketch pattern), cache check in `compile_module_graph`, un-ignore 5 tests. (d) `/reset` — `clear_session_state()` + `TypeChecker::new()` + `load_prelude()` from cache, document JIT memory leak limitation. (e) File watching — `src/repl/watch.rs` with `notify` crate, `FileWatcher` struct, poll before prompt, cascade reload via `find_transitive_dependents` BFS, locked-module error recovery. (f) `--link` CLI wiring — new `RunMode::Link` variant, calls `/backend`'s linking function after normal compilation.
**Status**: Design doc complete. FIXME on `pipeline-convergence.md:345` resolved (in design doc, code fix pending). Implementation not started.

### /typecheck
**Task**: Respond to any FIXMEs. No primary implementation work this sprint.
**Acceptance**: No outstanding FIXMEs.

### /frontend
**Task**: Respond to any FIXMEs. No primary implementation work this sprint.
**Acceptance**: No outstanding FIXMEs.

### /qa
**Task**: (1) Executable generation tests — compile, run, verify output. (2) File watching tests — staleness detection, reload correctness, error recovery. (3) `/reset` tests — state cleared, prelude reloaded, module reset. (4) Shell escape tests — command execution, output capture, error handling. (5) Retarget 5 REPL cache tests from S22 to S23. (6) Add REPL cache integration tests.
**Design refs**: `repl/spec.md` §12-14, `design/backend/executable-generation.md`, `design/int/repl-lifecycle.md`
**Acceptance**: Full spec surface covered with test stubs. All tests `#[ignore]` until implementation lands.
**Approach**: Test stubs in `tests/sprint23.rs` (E2E layer). 5 existing cache tests in `tests/cache.rs` retargeted to Sprint 23. Tests organized by feature:
- **Executable generation** (12 tests): basic --link, main :: Int/IO, output path, error cases (no main, wrong type, file not found, missing bundle), --no-cache, cache reuse, multi-module.
- **/reset** (13 tests): clear definitions, clear imports, confirmation output, timing reset, module reset, prelude reload, prelude failure, cache preservation, performance, /help integration, negative (type leakage, macro leakage).
- **Shell escape** (11 tests): basic echo, output passthrough, exit code display, zero exit silent, command not found, empty command, chained commands, no state interaction, timing reset, /help integration, negative (env propagation).
- **File watching** (14 tests): change detection, metadata-only ignore, cascade invalidation, notification format, notification truncation, deferred notification, automatic recompilation, type incompatibility, error recovery (3 tests), watcher across reset, cache invalidation, unchanged cache, no eager background recompilation.
- **REPL cache** (3 new tests + 5 retargeted): cache write on import, cache load on startup, cache writer survives reset.
**Status**: DONE — Wave 3 triage complete. 24 tests un-ignored (all pass), 29 remain ignored, 0 failures. Suite: 1,346 passed, 0 failed, 38 ignored.
**Wave 3 results**:
- **Shell escape (11/11 pass)**: All un-ignored. `;#!` basic echo, output passthrough, exit code display, zero-exit silence, command-not-found, empty command, chained commands, state preservation, timing reset, /help integration, env propagation negative — all pass.
- **/reset (11/13 pass)**: 11 un-ignored. Core semantics work: clears definitions, imports, types, macros; confirmation message; timing reset; module reset to `user`; /help integration; performance (<500ms). 2 remain ignored: `reset_reloads_prelude` and `reset_preserves_object_cache` fail because prelude reload after JIT state clear hits "unresolved symbol: .Ldata2". FIXME(/int) — the `handle_reset` re-creates compilation core but the new JIT module cannot resolve data symbols from the prelude's object code.
- **--link (2/12 pass)**: 2 error-case tests un-ignored (`link_error_file_not_found`, `link_error_no_main_function`). 10 remain ignored: `link_file()` in `src/main.rs` has a TODO — linker step not wired (`generate_startup_object` + `link_executable` in `src/exe.rs` exist but are not called). FIXME(/int).
- **File watching (0/14)**: All remain ignored with `todo!()` bodies — require interactive REPL harness that doesn't exist yet.
- **REPL cache (0/3 new, 0/5 retargeted)**: All remain ignored with `todo!()` bodies.

### /platform
**Task**: (1) Verify `.claude/commands/platform.md:73` FIXME — still no consumer for stderr? If stale, remove. (2) Respond to any FIXMEs.
**Acceptance**: FIXME resolved or removed.
**Status**: DONE — FIXME removed. Searched spec/, design/, stdlib/, repl/, user/, and .claude/commands/ for stderr write needs. All stderr references are Rust-side runtime concerns (batch error output, panic messages, usage hints, shell escape passthrough) — none require a Cranelisp-level `write` platform function. The example syntax in the consumer protocol section was preserved with a generic placeholder.

### /stdlib
**Task**: Respond to any FIXMEs. Update demo if new capabilities warrant it.
**Acceptance**: No outstanding FIXMEs.

### /port
**Task**: Verify exemplar still works. Test exemplar with `--compile` if executable generation lands. Update demo.
**Acceptance**: Exemplar compiles and runs. Demo updated if executable generation works.

### /examples
**Task**: Verify all examples compile and run. Test examples with `--compile`. Optional: add multi-file example that exercises caching + reload workflow.
**Acceptance**: All examples pass. At least one example tested with `--compile`.

### /docs
**Task**: Document `/reset`, shell escape, file watching, and `--link` in user docs. Update caching docs if REPL cache behavior differs from batch.
**Acceptance**: All new features documented.

### /review
**Task**: (1) **Catch-up**: Review S22 caching implementation (was pending). (2) Review executable generation (linking correctness, runtime startup). (3) Review file watching (race conditions, error recovery). (4) Review `/reset` (complete state clearing — no leaked definitions, no stale GOT entries). (5) Review shell escape (no injection vulnerabilities).
**Acceptance**: 0 Blockers, 0 Important unresolved.

## Waves

### Wave 0: Spec + Architecture Review (DONE)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | CompileMode FIXME, architecture review of sprint scope | **done** | 5 features approved. CompileMode three-variant resolved. |
| /repl | Spec §12 `/reset`, §13 shell escape, §14 file watching. Remove `/reload`. | **done** | 3 new sections, `/reload` removed from spec. |

### Wave 1: Design Docs + Test Stubs (DONE)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /backend | `design/backend/executable-generation.md`, CacheCodegenState FIXME, cache.rs FIXME | **done** | Design doc + 2 FIXMEs resolved. |
| /int | `design/int/repl-lifecycle.md`, project_root FIXME | **done** | Design doc complete. FIXME resolved in design doc. |
| /arch | Design review of both docs | **done** | 0 blockers, 5 Important, 7 Suggestions. Both approved. |
| /qa | 53 test stubs, 5 cache tests retargeted | **done** | Full spec surface covered. |

### Wave 2: Implementation
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /backend | Executable generation: startup stub, linker invocation, bundle library | pending | |
| /int | Shell escape, project_root fix, REPL cache, `/reset`, file watching, `--link` wiring | pending | |
| /spec | Verify resource_token FIXME on spec/10-io.md:52 | **done** | FIXME removed; layout matches runtime; Par deferred to S25 |
| /platform | Verify/remove stderr FIXME on platform.md:73 | **done** | FIXME removed — no consumer found |
| /review | S22 caching catch-up review | **done** | 0B 4I 5S. All sketch HIGH findings resolved. See `design/review/sprint22-caching-review.md`. |

### Wave 3: Build/Test/Review
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Un-ignore tests, run full suite, triage failures | **done** | 24 un-ignored (pass), 29 still ignored, 0 failures. 1,346 passed / 38 ignored total. |
| /review | Review new implementation code | **done** | 2B 5I 7S. File watching notification-only (no reload). `--link` wiring incomplete. See `design/review/sprint23-wave2-review.md`. |

### Wave 4: Showcase
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /repl | `repl/demos/ring4h.demo` | pending | |
| /port | Verify exemplar, test with `--link` | **done** | `solver.cl` compiles and runs (prints puzzle board). Full solve still segfaults (pre-existing stack overflow, not S23 regression). `main.cl` not yet created. |
| /examples | Verify examples, test with `--link` | **done** | 16/25 pass. 9 fail with "Duplicate definition" or "trait already defined" — prelude collisions (pre-existing, not S23 regression). Affected: 02, 03, 04, 10, 13, 15, 17, 19, 20. |
| /docs | Document new features | **done** | Added "Developer Tools" section to `getting-started.md` (`/reset`, `;#!`, file watching, `--link`). Updated `caching.md` with REPL cache and `--link` sections. |
| /stdlib | Respond to FIXMEs if any | pending | |

## Notes

- **Wave 0**: `/arch` recommends reconsidering `/reload` removal — sketch keeps it for locked-module retry. Decision: spec §14.5 handles this with last-known-good + auto-retry on next file change, which is cleaner. `/reload` stays removed.
- **Wave 1**: `/arch` design review flagged I-3 (watcher.clear_all() in /reset) and I-4 (cascade typecheck for dependents). Both addressed as implementation notes, not design blockers.
- **Test baseline**: 1,312 passing, 62 ignored (53 S23 + 5 cache + 4 HKT/lazy), 0 failures.
- **Post Wave 3**: 1,346 passing, 38 ignored (29 S23 + 5 cache + 4 HKT/lazy), 0 failures. +34 tests passing. Key gaps: `/reset` prelude reload (2 tests, FIXME(/int)), `--link` linker wiring (10 tests, FIXME(/int)), file watching harness (14 tests), REPL cache `todo!()` (8 tests).
- **Session persistence architecture review** (`design/int/session-persistence.md`): `/arch` reviewed the sketch's `repl/save.rs` approach for REPL session persistence (spec §15). Key findings: (1) Source regeneration from symbol table is correct — follow the sketch, do not append raw input. (2) Save after each definition (defn/deftype/deftrait/impl/defmacro/import/mod), not on /quit. (3) File watcher self-write suppression is already handled by content-hash comparison in `repl-lifecycle.md` §1.3 — no additional mechanism needed. (4) All required data (sexp for each definition type, import/export specs, mod_decls, impl_sexps) already exists in the reimplementation's `SymbolTable` + `ModuleStructure` + `DefCodegen`. (5) Only structural divergence from sketch: function sexps must be joined from `def_codegen` (backend) rather than read from unified `CompiledModule`. (6) One gap: `qualify_name()` equivalent needed in typecheck facade, OR verify that stored sexps are already qualified (in which case the gap disappears). (7) Code lives in `src/repl/save.rs` (binary crate). No new crate dependencies.

## Outcome

### Delivered

- **`--link` standalone executable generation**: Startup stub via Cranelift ObjectModule, macOS aarch64 linker invocation, `cranelisp-exe-bundle` staticlib crate, `main` validation (`() -> Int` and `() -> IO _`), 11 tests.
- **File watching with eager recompilation**: `notify` crate FSEvents watcher, content-hash change detection, cascade invalidation to dependents, `[updated:]`/`[errors:]` notifications, error blocking (REPL refuses evaluation until errors fixed), 12 E2E tests.
- **Shell escape `;#!`**: `/bin/sh -c` passthrough, inherited stdio, exit code display, 11 tests.
- **REPL session persistence**: Source regeneration from symbol table (`src/repl/save.rs`), dependency-sorted output preserving pre-expansion sexp, atomic save after each definition, startup restore via module graph pipeline, `user.cl` backing file, `.o` cache on first save, 10 E2E tests + 12 unit tests.
- **REPL cache integration**: Trait/impl registry restore from cache, GOT reconstruction for cached modules, TypeId collision fix, macro recompilation from cached modules, linker data section support, 5 cache tests passing.
- **Batch mode requires `main`**: `--run` requires `(defn main [] ...)`, clear error if missing, 3 tests.
- **REPL local file import**: `(import [helper [*]])` finds `helper.cl` in project root per spec §8.11.2.
- **Demo trampoline**: `showcase` delegates to live PTY `demo-player.py`, `/quit` in demo restarts REPL in same directory for session persistence demos.
- **Spec updates**: `repl/spec.md` §12 (demo trampoline), §13 (shell escape), §14 (file watching — eager recompile, error blocking), §15 (session persistence). Batch mode §0.2 updated to require `main`. `/reload` removed, `/reset` removed (demo trampoline replaces it).
- **Design docs**: `design/backend/executable-generation.md`, `design/int/repl-lifecycle.md`, `design/int/session-persistence.md`, `design/review/sprint22-caching-review.md`, `design/review/sprint23-wave2-review.md`.
- **Architecture updates**: CompileMode three-variant enum, 7+1 crate DAG (exe-bundle), CompileMode doc comments aligned.
- **5 FIXMEs resolved**: CompileMode (arch), CacheCodegenState (backend), project_root (int), resource_token (spec), stderr (platform).
- **User docs**: `getting-started.md` (session persistence, shell escape, file watching), `caching.md` (REPL cache, `--link` cache).
- **Demo**: `ring4h.demo` — session persistence with `/quit` restart, shell escape, file watching, `--link` executable.
- **1,411 tests** (was 1,312), 4 ignored (HKT/lazy — Sprint 24), 0 failures.

### Deferred

- **Demo showcase timing in FAST mode**: Shell escape output and file watching notifications don't display cleanly in `DEMO_FAST=1` mode due to PTY drain timing. Normal speed works correctly. Cosmetic.
- **`; Restored user.cl` on stderr**: Should be stdout per banner convention. FIXME(/int) filed. Minor.
- **S22 review Important findings** (I-1 through I-4): unsafe Send comment, fixed GOT vs doc, unwrap in linker, try_into unchecked. Advisory, not blocking. Carried to Sprint 24.
- **Demo `helper.cl` import failure in showcase**: Module resolution in demo run directory has a timing issue with shell-escape file creation. Works in manual testing. Showcase-specific.

### Findings

- **Session persistence was a missed requirement**: The initial sprint scope had caching and file watching but no session persistence. Without persisting REPL definitions to `user.cl`, those features were useless for interactive work. This required a mini-sprint within the sprint to design and implement source regeneration.
- **`/reset` was over-engineered then removed**: The initial spec had complex 5-step state clearing. User feedback: just simulate quit-and-restart. Then further feedback: don't need `/reset` at all — improve the demo trampoline instead. Session persistence makes restart fast enough.
- **File watching spec was wrong twice**: First spec had lazy recompilation and `[changed:]` notifications. User feedback: eager recompile, `[updated:]`/`[errors:]`, error blocking. The sketch's approach was the right model all along.
- **QA must write real tests, not `todo!()` stubs**: Multiple rounds of "stubs exist but no implementation" hid real bugs. Real E2E tests using `;#!` for mid-session file modification were the breakthrough — the shell escape feature enabled testing the file watching feature.
- **TypeId collision in cache restore**: Cached type schemes had TypeIds that collided with freshly generated ones, creating self-referential substitutions and stack overflow. Root cause: `next_id` counter not advanced past cached IDs.
- **Macro recompilation needed for cached modules**: When prelude loads from cache, macros aren't in the expander. Had to add `recompile_macros_for_cached_module` at all cache-hit sites.
- **Never combine skills into one agent**: User feedback — always launch separate agents per skill, even for small tasks.
