# Sprint 23 Wave 2 Code Review

**Reviewer**: `/review`
**Date**: 2026-03-22
**Scope**: Sprint 23 Wave 2 implementation code — shell escape, `/reset`, file watching, REPL cache integration, `--link` CLI wiring, executable generation backend, exe-bundle crate, project root fix.

**Files reviewed**:
- `src/repl/mod.rs` — shell escape, `/reset`, watcher integration, REPL cache (lines 100-1488)
- `src/repl/watch.rs` — new file (115 lines)
- `src/main.rs` — `--link` CLI wiring, project root fix (199 lines)
- `src/exe.rs` — new file, executable generation orchestration (552 lines)
- `crates/cranelisp-backend/src/exe.rs` — new file, startup stub generation (221 lines)
- `crates/cranelisp-exe-bundle/src/lib.rs` — new crate (44 lines)
- `crates/cranelisp-exe-bundle/Cargo.toml` — new crate manifest
- `src/pipeline.rs` — `CacheState`, non-fatal cache writes (reviewed cache-related sections)

## Summary

The Wave 2 implementation is well-structured overall. Function sizes are within limits, error handling is clean, and the code follows the design docs closely. The executable generation pipeline is a clean layering on top of the existing caching infrastructure. The shell escape and `/reset` implementations are correct and minimal.

However, file watching is **notification-only** — changes are detected and reported but never trigger recompilation. This is a significant gap relative to the design doc (`design/int/repl-lifecycle.md` §1.4) and the spec (`repl/spec.md §14`). The `pending_changes` vector is populated but never consumed, and no `reload_module()`, cascade invalidation, or locked-module error recovery exists.

## Findings

### B-1: File watching does not recompile changed modules (Blocker)

**Files**: `src/repl/mod.rs:1272-1282`, `src/repl/watch.rs`
**Severity**: Blocker

The `poll_and_notify_changes()` function detects changed files and displays a `[changed: ...]` notification, then stores paths in `session.pending_changes`. But `pending_changes` is never consumed — no code maps changed paths to `ModuleFullPath`, calls `reload_module()`, performs cascade invalidation, or implements locked-module error recovery. The field is only cleared by `/reset`.

The design doc (`design/int/repl-lifecycle.md` §1.4) specifies a full cascade reload pipeline: map file to module, reload module via full pipeline, find transitive dependents via BFS, reload dependents in topo order, update GOT atomically. The spec (`repl/spec.md §14`) specifies automatic recompilation.

The current implementation is notification-only. All 14 file watching test stubs from `/qa` will fail on the reload/cascade/error-recovery behaviors. This blocks the showcase use-case (hot-reload workflow).

**Recommendation**: Implement the reload pipeline per the design doc, or explicitly mark file watching as "notification-only (reload deferred)" in the design doc and sprint plan, and adjust the 14 test stubs accordingly. The notification infrastructure is correct and can serve as the foundation.

---

### B-2: Content hash verification missing from file watcher (Blocker)

**File**: `src/repl/watch.rs:69-102`
**Severity**: Blocker (if reload is implemented; downgrade to Important if B-1 is deferred)

The design doc (`design/int/repl-lifecycle.md` §1.3) specifies: "After detecting a file change event, read the file and compute its SHA-256 hash. Compare against the hash stored in the `CompiledModule`. If the hash is unchanged [...] skip reloading."

The `poll_changes()` function only checks the file extension (`.cl`) and skips `.cl.tmp` files. It does not read the file or compare hashes. This means metadata-only changes (e.g., `touch foo.cl`) will trigger spurious reload notifications and, once reload is implemented, unnecessary recompilation.

The comment in the file header references "content hash comparison" as if it were implemented, but the code does not contain any hash computation.

**Recommendation**: Add content hash comparison in `poll_changes()` or in the (not-yet-implemented) reload path. Store file hashes in `FileWatcher` or reference them from the compilation session.

---

### I-1: `--link` CLI wiring is a stub — does not link

**File**: `src/main.rs:152-198`
**Severity**: Important

The `link_file()` function compiles the module graph successfully but then prints a `TODO(/backend)` message and exits with code 1:
```
error: --link is not yet fully implemented (pending /backend executable generation)
```

Meanwhile `src/exe.rs` contains the full working implementation: `validate_main()`, `link_executable()`, `find_bundle_lib()`, `find_platform_rlibs()`, `generate_startup_object()`. The backend crate also has `generate_startup_object()` working (with unit tests).

The `link_file()` function needs to be wired to call `src/exe.rs` functions. The compilation result, module symbol tables, and `.o` file paths need to be threaded from `compile_module_graph_cached()` to the executable generation functions.

**Recommendation**: `/int` should complete the wiring: after `compile_module_graph_cached()` succeeds, validate main, collect `.o` paths from the cache directory, call `generate_startup_object()`, write the stub to a temp file, call `link_executable()`. This is orchestration code, not new logic.

---

### I-2: `--no-cache` + `--link` silently ignored

**File**: `src/main.rs:83-88`
**Severity**: Important

When `--no-cache` and `--link` are both specified, the `no_cache` flag is accepted but silently discarded — `RunMode::Link` does not carry a `no_cache` field. The comment says "handled in link_file" but `link_file()` always creates a `CacheConfig::Enabled`. The design doc (`design/backend/executable-generation.md`) specifies a temporary directory for `--no-cache` + `--link`.

**Recommendation**: Either (a) add `no_cache: bool` to `RunMode::Link` and implement temp directory behavior, or (b) reject the combination with an error message: "`--no-cache` is not supported with `--link`".

---

### I-3: `cranelisp_init_platform` uses `transmute` without SAFETY comment

**File**: `crates/cranelisp-exe-bundle/src/lib.rs:39`
**Severity**: Important (unsafe audit)

```rust
let manifest_fn: ManifestFn = unsafe { std::mem::transmute(manifest_fn_ptr) };
```

Per `src/CLAUDE.md` and the review checklist: "Every `unsafe` block must have a `// SAFETY:` comment explaining why the invariants hold." The transmute converts an `i64` to a function pointer. The invariant is that `manifest_fn_ptr` was obtained from Cranelift's `func_addr` for a function with the correct `ManifestFn` signature. This must be documented.

Additionally, there is no null-pointer check. If `manifest_fn_ptr` is 0 (e.g., due to a codegen bug), the transmute-and-call would segfault. A debug assertion would be appropriate.

**Recommendation**: Add `// SAFETY:` comment and a `debug_assert!(manifest_fn_ptr != 0)` guard.

---

### I-4: `unwrap_or(path)` in `poll_changes()` may silently lose paths

**File**: `src/repl/watch.rs:87`
**Severity**: Important

```rust
let canonical = path.canonicalize().unwrap_or(path);
```

If `canonicalize()` fails (file deleted between event and canonicalization), the non-canonical path is kept. This can cause path mismatches when comparing against module paths stored with canonical paths in the compilation session. The design doc S-6 flagged symlink path issues; this is the same class of problem.

This is more concerning in the context of cascade reload (when B-1 is implemented): the non-canonical path may not match any known module, causing changed files to be silently ignored.

**Recommendation**: Log a debug warning when `canonicalize()` fails, and consider filtering out paths that fail canonicalization (the file is likely deleted/in-flight).

---

### I-5: `link_executable()` uses `to_string_lossy()` for paths passed to `ld`

**File**: `src/exe.rs:177, 183, 187, 197`
**Severity**: Important

Paths containing non-UTF-8 characters (rare but possible on macOS with legacy HFS+ filenames) will have replacement characters injected by `to_string_lossy()`, producing invalid linker arguments. The `ld` command would fail with a cryptic "file not found" error.

**Recommendation**: Use `OsString` arguments via `.arg()` instead of building a `Vec<String>`. Alternatively, use `Command::args()` with `OsStr` slices. Since `ld` is invoked via `Command::new("ld").args(&ld_args)`, changing `ld_args` to `Vec<OsString>` would be a clean fix.

---

### S-1: `handle_reset` does not re-register platform DLLs

**File**: `src/repl/mod.rs:1395-1445`
**Severity**: Suggestion

The `/reset` implementation re-creates the `CompilationSession` (which creates a new `TypeChecker`) but does not re-register platform DLL symbols. The `loaded_platforms` vector is preserved (the DLLs stay loaded), but the new `TypeChecker` has no knowledge of platform modules, and the new JIT has no platform function pointers registered.

The prelude reload may not trigger platform re-loading if platforms are loaded via `(platform ...)` declarations in the entry file rather than the prelude. After `/reset`, platform functions would be unavailable.

**Recommendation**: After re-creating the `CompilationSession`, re-register platform symbols from `loaded_platforms` into the new session's JIT and TypeChecker. Or document that `/reset` does not restore platform modules (acceptable if the showcase doesn't use platforms).

---

### S-2: `link_executable()` function is 82 lines — near the 100-line limit

**File**: `src/exe.rs:152-240`
**Severity**: Suggestion

At 82 lines, `link_executable()` is within the limit but dense. The ld argument construction could be extracted into a `build_ld_args()` helper, leaving `link_executable()` as a thin wrapper that validates config, builds args, invokes `ld`, and checks the result.

---

### S-3: `run_shell_command` writes to `stdout` parameter, not to actual stdout

**File**: `src/repl/mod.rs:1453-1487`
**Severity**: Suggestion

The shell command's output goes to the real process stdout/stderr (via `Stdio::inherit()`), but the exit status message goes to the `stdout` parameter (which is the locked stdout handle). This is correct for the current implementation but creates a subtle inconsistency: if `stdout` were ever redirected (e.g., for testing), the shell command's output would still go to the real stdout while the exit status would go to the redirected handle.

Not a practical issue currently, but worth noting for testability.

---

### S-4: `generate_startup_object` function is 150 lines

**File**: `crates/cranelisp-backend/src/exe.rs:31-186`
**Severity**: Suggestion

At ~150 lines (including the function body), this exceeds the 100-line guideline in `src/CLAUDE.md`. The function handles declaration of 4+ imported functions, building the function body, compiling, and emitting. Consider extracting the declaration block (lines 46-119) into a `declare_startup_imports()` helper and the function body construction (lines 127-168) into a `build_startup_body()` helper.

---

### S-5: `collect_platform_manifest_names` always returns the same single name

**File**: `src/exe.rs:390-401`
**Severity**: Suggestion

The function checks if any `platform.*` module exists and returns `["cranelisp_platform_manifest"]`. This hardcodes the assumption that all platforms share a single manifest name. If multiple platform crates are used (each with their own manifest function), this would only call one. The sketch has the same simplification. Acceptable for Ring 4 but worth documenting.

---

### S-6: Tests in `src/exe.rs` use `unsafe { std::env::set_var/remove_var }`

**File**: `src/exe.rs:502, 521, 524`
**Severity**: Suggestion

These are in test code so `unsafe` is permitted, but `set_var`/`remove_var` are not thread-safe in Rust 2024. If these tests run in parallel with other tests that also manipulate `CRANELISP_BUNDLE_PATH`, they could race. Consider using a `#[serial]` attribute (from the `serial_test` crate) or a mutex.

---

### S-7: `update_watched_paths` uses `dummy.cl` as a path fabrication trick

**File**: `src/repl/mod.rs:1225, 1230, 1237`
**Severity**: Suggestion

`watcher.watch_file(&dir.join("dummy.cl"))` is used to get `watch_file()` to watch the parent directory. This works because `watch_file()` calls `path.parent()`, but it's indirect and relies on the internal implementation of `watch_file()`. Consider adding a `watch_dir()` method to `FileWatcher` that takes a directory path directly, making the intent explicit.

---

## S22 Finding Disposition

All four Important findings from `design/review/sprint22-caching-review.md` are **still present** and unresolved:

| S22 ID | Issue | Status |
|--------|-------|--------|
| I-1 | `unsafe impl Send for CacheWritePacket` lacks SAFETY justification | **Still present** — `crates/cranelisp-backend/src/cache/object.rs:130-132` |
| I-2 | Linker GOT overflow error but design doc says "growable GOT" | **Still present** — `crates/cranelisp-backend/src/cache/linker.rs:129-134` |
| I-3 | `got_mmap.as_mut().unwrap()` in non-test linker code | **Still present** — `crates/cranelisp-backend/src/cache/linker.rs:124, 143` |
| I-4 | `try_into().unwrap()` in relocation patching (7 instances) | **Still present** — `crates/cranelisp-backend/src/cache/linker.rs:364-462` |

These are not regressions (they were flagged in S22 and haven't been addressed yet), but they should be tracked as ongoing debt.

## Positive Findings

1. **Shell escape implementation is clean and minimal** (35 lines). Uses `/bin/sh -c` with inherited stdio, handles empty commands, displays exit codes, handles signal termination. Matches the spec and design doc exactly.

2. **`/reset` correctly addresses `/arch` I-3**. The file watcher is cleared (`watcher.clear_all()`) before re-adding paths after prelude reload. This prevents stale watches for modules that no longer exist in the session.

3. **`/reset` preserves object cache on disk** (design intent). Only in-memory state is cleared. The prelude reload benefits from cached `.o` files via `CacheState::new()`.

4. **`CacheState` integration in REPL** is well-structured. The pattern of `Option<CacheState>` (None = disabled) threads cleanly through `load_prelude_into_session()`. Non-fatal cache writes (`let _ = ...`) prevent cache failures from crashing the REPL.

5. **`src/exe.rs` unit tests** are thorough: 10 tests covering main validation (Int, IO, missing, wrong return type, with params), bundle lib discovery (not found, via env var), platform rlib discovery, manifest collection, and linker config.

6. **Startup stub generation** (`crates/cranelisp-backend/src/exe.rs`) is a correct Cranelift `ObjectModule` implementation: declares imports, builds function body, handles conditional IO trampoline, uses `trap` for unreachable-after-exit.

7. **Project root fix** is correct and well-commented. Uses `current_dir()` instead of entry file parent, with a clear reference to the FIXME it resolves.

8. **`LinkerConfig` abstraction** for platform-specific linker settings is a clean extensibility point for future Linux support.

## Design Doc Adherence

### `design/backend/executable-generation.md`

The implementation in `src/exe.rs` and `crates/cranelisp-backend/src/exe.rs` follows the design doc closely:
- Startup stub generation matches §4 (platform init, main call, IO trampoline, exit).
- Main validation matches §7 (pre-link type check).
- Bundle library search matches §6 (env var, exe dir, sibling target dirs).
- `LinkerConfig` matches §5 divergence from sketch.
- The only gap is the `--link` wiring in `src/main.rs` which is a stub (I-1 above).

### `design/int/repl-lifecycle.md`

- §2 (`/reset`): Implementation matches design well. Clears session, watcher, reloads prelude, syncs type defs, resets to user module.
- §3 (shell escape): Implementation matches design exactly.
- §4 (REPL cache): Integration matches design. `CacheState` is created for prelude loading and for `/reset` prelude reload.
- §5 (`--link`): Wiring is incomplete (I-1).
- §6 (project root): Fix is correct.
- §1 (file watching): **Major gap** — notification-only, no reload/cascade/recovery (B-1, B-2).

## Verdict

**2 Blockers, 5 Important, 7 Suggestions.**

The executable generation backend and REPL lifecycle features (`/reset`, shell escape, cache integration, project root) are well-implemented. The file watching is notification-only without the reload pipeline, which is the primary gap. The `--link` CLI wiring needs to be connected to the existing `src/exe.rs` functions.

## Next skills

- `/int` — Address B-1 (file watching reload), B-2 (content hash), I-1 (`--link` wiring), I-2 (`--no-cache` + `--link`), I-4 (canonicalize), S-1 (platform re-registration), S-7 (watch_dir)
- `/backend` — Address S-4 (`generate_startup_object` size), S22 I-1 through I-4 (ongoing debt)
- `/platform` — Address I-3 (SAFETY comment on transmute)
