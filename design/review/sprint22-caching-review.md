# Sprint 22 Caching Code Review

**Reviewer**: `/review`
**Date**: 2026-03-22
**Scope**: Module caching implementation — S22 catch-up review for Sprint 23 Wave 2
**Files reviewed**:
- `crates/cranelisp-backend/src/cache/` (5 files, 2,823 lines)
- `src/pipeline.rs` (cache-related sections, ~400 lines of caching code)
- `src/main.rs` (--no-cache CLI wiring)

## Summary

The reimplementation's caching system is a **substantial improvement** over the sketch. Every HIGH-severity finding from `sketch/audits/cache.md` has been addressed:

- **HIGH-1 (intrinsic coverage)**: `IntrinsicTable` unifies all extern symbol declarations as a single source of truth. No more separate enumeration in JIT vs cache paths.
- **HIGH-2 (ISA divergence)**: Single `build_isa(is_pic: bool)` function used by both JIT and ObjectModule paths.
- **HIGH-3 (21 parameters)**: `ObjectCompileInput` struct replaces 21 positional params. `compile_module_to_object` takes a single `&ObjectCompileInput`.

The design doc (`design/backend/module-caching.md`) is thorough, covers sketch comparison properly, and the implementation follows it closely.

## Findings

### I-1: `unsafe impl Send for CacheWritePacket` lacks SAFETY justification

**File**: `crates/cranelisp-backend/src/cache/object.rs:130-132`
**Severity**: Important (unsafe audit)

```rust
// CacheWritePacket must be Send for background thread use.
// ObjectCompileInput contains no raw pointers.
unsafe impl Send for CacheWritePacket {}
```

The comment states "ObjectCompileInput contains no raw pointers" but does not justify the unsafe impl per `src/CLAUDE.md` conventions. A `// SAFETY:` comment should enumerate which fields are non-auto-Send and why they are safe. More importantly: if `ObjectCompileInput` truly contains no non-Send fields, then `CacheWritePacket` should derive `Send` automatically — the `unsafe impl` suggests something is preventing auto-derivation. Audit all fields to confirm whether the unsafe impl is actually necessary, or if a dependency type is blocking auto-Send.

**Recommendation**: Either (a) remove the `unsafe impl Send` by making all contained types auto-Send, or (b) add a full `// SAFETY:` comment identifying the specific non-Send field and why cross-thread transfer is safe.

---

### I-2: Linker GOT overflow returns error but design doc promises growable GOT

**File**: `crates/cranelisp-backend/src/cache/linker.rs:129-137`
**Severity**: Important (design doc/code divergence)

```rust
if self.got_count >= self.got_capacity {
    return Err(CranelispError::CodegenError {
        message: format!(
            "linker GOT overflow: {} entries used, capacity {}. \
             Growable GOT not yet implemented.",
            self.got_count, self.got_capacity
        ),
        ...
    });
}
```

The design doc (module-caching.md §2 divergence table) says: "Growable `Vec<u64>` with mprotect before use (Addresses MED-4)." The actual implementation still has a fixed 512-entry limit and returns an error on overflow with the message "Growable GOT not yet implemented." This is better than the sketch's `assert!` panic, but the design doc overpromises.

**Recommendation**: Either implement growable GOT (remmap a larger region) or update the design doc's divergence table to say "Error on overflow (improved from panic) — growable deferred." The current error message at least makes the limitation discoverable.

---

### I-3: `got_mmap.as_mut().unwrap()` in non-test linker code

**File**: `crates/cranelisp-backend/src/cache/linker.rs:124, 143`
**Severity**: Important (robustness)

Two `.unwrap()` calls on `self.got_mmap.as_mut()` in `get_or_create_got_slot`. The field is `Option<MmapMut>` and is always `Some` after construction, but per `src/CLAUDE.md` conventions: "No `unwrap()` in pipeline code." The `got_mmap` is `Option` only because `MmapMut` doesn't implement `Default`.

**Recommendation**: Use `unwrap_or_else(|| unreachable!("invariant: got_mmap always Some after Linker::new"))` to satisfy the convention and document the invariant, or restructure so `got_mmap` is not `Option` (e.g., use a wrapper that initializes in `new()`).

---

### I-4: `try_into().unwrap()` in relocation patching (non-test code)

**File**: `crates/cranelisp-backend/src/cache/linker.rs:364, 376, 387, 435, 446, 455, 462`
**Severity**: Important (robustness)

Seven `.unwrap()` calls on `mmap[offset..offset + 4].try_into()` in `apply_macho_arm64_reloc` and `apply_elf_aarch64_reloc`. These convert `&[u8]` to `[u8; 4]` and are infallible when the slice length is exactly 4, but a malformed `.o` file with a relocation pointing past the end of the section could cause an out-of-bounds slice access *before* the `try_into` (the slice indexing itself would panic). The `try_into` itself cannot fail given the 4-byte slice, but the slice access is the real risk.

**Recommendation**: Add a bounds check before each relocation patch: if `offset + 4 > mmap.len()`, return a `CranelispError` instead of panicking. The `try_into` unwrap is then safe by construction but could use `unreachable!` for clarity.

---

### S-1: `module_dir_and_stem` does not sanitize path-traversal characters

**File**: `crates/cranelisp-backend/src/cache/mod.rs:59-71`
**Severity**: Suggestion (security hardening)

`module_dir_and_stem` converts module paths like `core.numerics` to `("core", "numerics")` and joins them into cache filesystem paths. If a `ModuleFullPath` ever contained `..` or absolute path components, the resulting path could escape the cache directory. Currently this is safe because module paths are derived from filesystem discovery in the module graph (which validates paths), but there is no defensive check at the cache layer.

**Recommendation**: Add a debug assertion or validation that the computed (dir, stem) does not contain `..`, `/` (in stem), or start with `/`. This is defense-in-depth — the current code is safe given the module graph's path derivation.

---

### S-2: Binary fingerprint empty-string fallback silently disables cache invalidation

**File**: `crates/cranelisp-backend/src/cache/manifest.rs:111-117`
**Severity**: Suggestion (robustness)

```rust
let current_mtime = binary_fingerprint();
if !current_mtime.is_empty()
    && !manifest.compiler_mtime.is_empty()
    && manifest.compiler_mtime != current_mtime
{
    return Err(CacheInvalidReason::CompilerChanged);
}
```

If `binary_fingerprint()` returns an empty string (because `current_exe()` or `metadata()` fails), the check is silently skipped, accepting potentially stale caches. The design doc acknowledges this is the sketch's approach (mtime-based, retained for pragmatic reasons), but the silent skip is worth noting. The reimplementation already improved the triple check (exact `target_lexicon::Triple` comparison, addressing MED-6).

**Recommendation**: Consider logging a warning (to the warning accumulator, not stderr) when `binary_fingerprint()` returns empty, so cache developers know invalidation is degraded. Low priority.

---

### S-3: `CacheWritePacket` stores `ObjectCompileInput` by value — large clone

**File**: `crates/cranelisp-backend/src/cache/object.rs:127`
**Severity**: Suggestion (performance)

`CacheWritePacket` owns a full `ObjectCompileInput` which contains cloned `Vec<(Defn, Scheme)>`, `HashMap<Span, Type>`, etc. For large modules, this is a significant allocation. The packet is built on the main thread and consumed on the background thread. For batch mode (where `process_cache_packet` runs synchronously), this means an unnecessary clone.

**Recommendation**: For batch mode, consider passing `&ObjectCompileInput` directly to `compile_module_to_object` without building a packet. The packet pattern is appropriate for the REPL's background writer but unnecessary overhead in batch. This could be a future optimization — the current approach is correct.

---

### S-4: Atomic write temp file has predictable name

**File**: `crates/cranelisp-backend/src/cache/mod.rs:228`
**Severity**: Suggestion (robustness)

```rust
let tmp_path = path.with_extension("tmp");
```

If two processes write to the same cache concurrently (unlikely but possible with parallel editor processes), the `.tmp` file could be clobbered. The sketch has the same pattern.

**Recommendation**: Use a unique temp file name (e.g., include PID or random suffix) for truly atomic writes. Low priority — concurrent cache writes are rare and result in a retry on next run, not data corruption.

---

### S-5: Design doc stale comment about `CacheCodegenState` placement

**File**: `design/backend/module-caching.md:128`
**Severity**: Suggestion (documentation)

The FIXME on line 128 was resolved per the sprint plan, but the surrounding text at the design doc's §4 could be clearer about `CacheCodegenState` living in `cranelisp-backend::cache::serialize` rather than in `cranelisp-types`. The implementation matches the design doc's intent but the crate location is stated in §2's divergence table and could be restated in §4 for clarity.

---

## Positive Findings

These aspects of the implementation are well-executed and merit explicit acknowledgment:

1. **Decomposed module structure**: The 5-file cache module (`mod.rs`, `manifest.rs`, `serialize.rs`, `object.rs`, `linker.rs`) cleanly separates concerns. Each file has a single responsibility. This directly addresses the sketch's monolithic `cache.rs` (1,069 lines).

2. **`IntrinsicTable` as single source of truth**: The unified intrinsic table shared between JIT and ObjectModule is the right architectural fix for HIGH-1. The `intrinsic_symbols()` function in `jit.rs` populates both paths.

3. **`build_isa(is_pic: bool)`**: Clean, single ISA construction point. Both JIT and ObjectModule share all flags except `is_pic`. Addresses HIGH-2 definitively.

4. **`CacheInvalidReason` enum**: Replacing the sketch's boolean return with a reason enum makes cache misses debuggable. The `Display` impl produces clear messages.

5. **Dependency hash tracking**: The manifest stores per-module dependency hashes, enabling precise cascade invalidation. Better than the sketch's linear scan approach.

6. **Exact triple comparison**: Using `target_lexicon::Triple::host().to_string()` for exact matching instead of the sketch's brittle string containment. Addresses MED-6.

7. **Nested cache directories**: `module_dir_and_stem` maps module hierarchy to filesystem hierarchy (`core.numerics` -> `core/numerics.{meta.json,o}`). Solves the sketch's LOW-4 (collision risk from `.` to `_` replacement).

8. **Unit test coverage**: 35+ unit tests across the cache module, covering round-trips, edge cases (corrupt files, empty .o, path mismatches), and the end-to-end compile-link-execute path. This addresses LOW-5 comprehensively.

9. **`Linker::new()` returns `Result`**: The sketch's `.expect("failed to mmap")` is replaced with proper error propagation. Addresses part of MED-4.

10. **Dead code eliminated**: No equivalent of the sketch's `write_module_cache()` (MED-1). The packet-based write path is the sole mechanism.

## Audit Finding Disposition

| Sketch Finding | Disposition | Notes |
|---|---|---|
| HIGH-1 (intrinsic coverage) | **Resolved** | `IntrinsicTable` + `intrinsic_symbols()` |
| HIGH-2 (ISA divergence) | **Resolved** | `build_isa(is_pic: bool)` |
| HIGH-3 (21 params) | **Resolved** | `ObjectCompileInput` struct |
| MED-1 (dead code) | **Resolved** | No dead `write_module_cache` |
| MED-2 (238-line function) | **Resolved** | `try_load_cached_module` is 36 lines; `try_restore_from_cache` in pipeline.rs is 38 lines |
| MED-3 (silent failures) | **Improved** | `Result<T, CranelispError>` throughout; `process_cache_packet` returns `Err` instead of `None` |
| MED-4 (GOT overflow panic) | **Partially resolved** | Error instead of panic (I-2 above); growable GOT deferred |
| MED-5 (mtime fingerprint) | **Retained** | Design doc documents the pragmatic choice. Acceptable. |
| MED-6 (triple containment) | **Resolved** | Exact `target_lexicon::Triple` comparison |
| MED-7 (O(n) per module) | **N/A** | Pipeline structure changed; no linear scan of all modules |
| LOW-1 (unnamed tuples) | **Resolved** | `FnSlotInfo { slot, param_count }` struct |
| LOW-2 (unused return_count) | **Resolved** | Intrinsic table handles all declarations uniformly |
| LOW-3 (Option\<bool\>) | **Resolved** | `try_load_cached_module` returns `Option<CachedModule>` |
| LOW-4 (module filename collision) | **Resolved** | Nested directories with `module_dir_and_stem` |
| LOW-5 (zero unit tests) | **Resolved** | 35+ unit tests |

## Verdict

**0 Blockers, 4 Important, 5 Suggestions.**

The implementation is structurally sound and addresses all major sketch audit findings. The Important findings are incremental quality issues (unsafe documentation, unwrap in non-test code, design doc accuracy) — none are correctness risks. The caching system is ready for Sprint 23's REPL cache integration and executable generation.

## Next skills

- `/int` — Wire REPL cache integration using the patterns established here
- `/backend` — Address I-2 (update design doc divergence table for GOT overflow)
