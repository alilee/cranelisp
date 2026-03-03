# Cache System Audit

**Module**: `src/cache.rs`, `src/cache_writer.rs`, `src/linker.rs` (3 files, 1,704 lines)
**Date**: 2026-03-03
**Scope**: Simplicity, maintainability, complexity, duplication, data modeling, test coverage

## Module Overview

The cache system persists compiled Cranelift modules to disk so that subsequent runs avoid recompilation. The pipeline has three parts:

1. **`cache.rs`** — reads/writes cache files (`manifest.json`, `<module>.meta.json`, `<module>.o`), hashes source for invalidation, builds `CacheWritePacket` snapshots, calls `compile_module_to_object()` to re-emit each module's code into a relocatable `ObjectModule`, and validates manifest compatibility.

2. **`cache_writer.rs`** — a background mpsc thread used by the REPL to write cache packets asynchronously, accumulating manifest updates and flushing on shutdown.

3. **`linker.rs`** — a minimal ELF/Mach-O linker that loads cached `.o` files, resolves symbol relocations against the live JIT symbol table, and maps code pages executable with `mmap`/`mprotect`.

The JIT path (`jit.rs`) compiles functions into a live `JITModule`. The cache path is supposed to persist that result; instead it independently re-runs codegen through `compile_module_to_object()` targeting `ObjectModule`. Both paths call the same `compile_function_indirect()` entry point but arrive there through divergent setup paths that have significant duplication.

### File Metrics

| File | Lines | Responsibility | Tests |
|---|---|---|---|
| `src/cache.rs` | 1,069 | Manifest, hashing, object compilation, write packets | ~14 integration (e2e via subprocess) |
| `src/cache_writer.rs` | 139 | Background write thread, deferred manifest flush | 0 unit |
| `src/linker.rs` | 496 | Object loading, relocation resolution, mmap execution | 0 unit |

**Total integration-only tests**: ~14 subprocess tests in `tests/integration.rs:5462-5870`. Zero unit tests for cache, cache_writer, or linker modules.

---

## Findings

### HIGH-1: RC, trace, and operator intrinsics not declared in ObjectModule — silent code divergence ✓ RESOLVED (invariant documented)

**File**: `src/cache.rs:448-476`
**Severity**: High (robustness)
**Resolution**: Investigation confirmed the finding overstates the risk. All RC/trace symbols ARE
correctly declared in the ObjectModule — not missing:
- `dec_guarded`, `dec_mixed_guarded`, `dec_closure_guarded`: added to `builtin_method_info` by
  `declare_non_platform_functions()` in jit.rs; declared via the `builtin_method_info` loop in
  `compile_module_to_object()` in cache.rs.
- `rc_underflow_check`: declared on-demand by `FnCompiler::emit_rc_underflow_check()` (codegen.rs)
  via `module.declare_function()` — self-declares in whichever module is being compiled.
- Trace symbols: declared on-demand by `FnCompiler::declare_trace_extern()` (codegen/trace.rs)
  via `module.declare_function()` — same self-declaring pattern.
An invariant comment was added to `compile_module_to_object()` in cache.rs documenting these
three coverage paths and the requirement that new intrinsics follow one of them.

`compile_module_to_object()` declares seven named intrinsics (alloc, free, panic, par_eval, ivar_create, ivar_spark, ivar_force) and then delegates all other builtins to `builtin_method_info` and `primitive_entries`. However, the JIT declares additional intrinsics in `declare_non_platform_functions()` (`jit.rs:544-576`) that are **never present in `builtin_method_info`**:

- `cranelisp_dec_guarded` (3 args) — reference counting dec for heap values
- `cranelisp_dec_mixed_guarded` (3 args) — mixed RC dec
- `cranelisp_dec_closure_guarded` (2 args) — closure environment RC dec
- `cranelisp_rc_underflow_check` — RC underflow assertion

Similarly, the JIT registers these trace symbols in `register_non_platform_symbols()` (`jit.rs:178-206`) that are completely absent from the ObjectModule setup:

- `cranelisp_trace_enter`, `cranelisp_trace_exit`, `cranelisp_trace_swap_got`, `cranelisp_trace_restore_got`, `cranelisp_collect_trace`, `cranelisp_trace_first_child_nanos`, `cranelisp_trace_format`

These are registered with the linker via `register_runtime_symbols()` (`jit.rs:823-910`), so if the cached `.o` references them, the linker can resolve them — but the ObjectModule will fail to compile the `.o` in the first place because it does not know their signatures. The current code only works because codegen happens to not emit ObjectModule calls to these symbols directly through the `builtin_methods` map; but if codegen were ever changed to route an RC or trace call through the builtin method dispatch table, the cache path would silently fail to declare it.

```rust
// cache.rs:448-476 — only 7 intrinsics declared; RC/trace/operator intrinsics absent
let alloc_func_id = declare_imported_func(&mut obj_module, alloc_jit_name, 1, 1)?;
let free_func_id = declare_imported_func(&mut obj_module, free_jit_name, 1, 1)?;
let panic_func_id = declare_imported_func(&mut obj_module, panic_jit_name, 1, 1)?;
// ... 4 more ...
// cranelisp_dec_guarded, cranelisp_dec_closure_guarded, cranelisp_dec_mixed_guarded,
// cranelisp_rc_underflow_check, cranelisp_trace_*, operator wrappers: NOT declared
```

**Impact**: Any codegen change that routes RC decrements or trace symbols through the `builtin_methods` map will cause the cache `.o` compilation to fail silently (currently `process_cache_packet` returns `None` on failure), leaving a stale but valid-looking `.meta.json` without a corresponding `.o`. The next run will then try to load from cache, find the `.meta.json`, load the GOT-populated `CompiledModule`, but fail to find the `.o` — silently falling back to recompilation.

**Recommendation**: Introduce a `CacheIntrinsicEntry { name: &str, param_count: usize, return_count: usize }` table shared between `declare_non_platform_functions()` and `compile_module_to_object()`. Replace the positional parameters `alloc_jit_name`, `free_jit_name`, etc. with a single `&[CacheIntrinsicEntry]` slice that is constructed once in `jit.rs` and passed through `CacheInputs`. This eliminates the separate enumeration in `cache.rs` and makes adding a new intrinsic automatically update both paths.

---

### HIGH-2: Duplicate ISA construction in `compile_module_to_object()` diverges from `build_isa()`

**File**: `src/cache.rs:385-403`, `src/jit.rs:77-103`
**Severity**: High (duplication / robustness)

`compile_module_to_object()` builds its own ISA from scratch:

```rust
// cache.rs:385-403
let mut flag_builder = settings::builder();
flag_builder.set("is_pic", "true")...;
let isa_builder = cranelift_native::builder()...;
let isa = isa_builder.finish(settings::Flags::new(flag_builder))...;
```

`build_isa()` in `jit.rs` builds a different ISA:

```rust
// jit.rs:77-103
let mut flag_builder = settings::builder();
flag_builder.set("use_colocated_libcalls", "false")...;
flag_builder.set("is_pic", "false")...;
let isa_builder = cranelift_native::builder()...;
let isa = isa_builder.finish(settings::Flags::new(flag_builder))...;
```

These differ in two flags: `is_pic` (JIT=false, cache=true — correct by design since ObjectModule needs PIC) and `use_colocated_libcalls` (JIT=false, cache=absent — implicit default). A third ISA construction exists in `exe.rs:46-60` for the standalone executable path. Any new Cranelift flag tuned for performance (e.g., `opt_level`, `regalloc`) added to the JIT ISA must be manually replicated in the cache ISA, or cached and freshly-compiled code will have different optimization levels.

**Impact**: ISA flag drift is invisible at runtime but silently produces binaries with different optimization characteristics depending on whether they were compiled from cache or from source. Any developer adding an ISA flag to `build_isa()` is unlikely to notice they also need to update `compile_module_to_object()`.

**Recommendation**: Extract a `build_isa_flags(is_pic: bool) -> settings::Flags` function in `jit.rs` that applies all shared flags plus the `is_pic` parameter. Call it from `build_isa()`, `compile_module_to_object()`, and `exe.rs`. This ensures all ISA variants share one authoritative flag set.

---

### HIGH-3: `compile_module_to_object()` has 21 positional parameters — long argument lists mask API changes

**File**: `src/cache.rs:362-383`
**Severity**: High (maintainability)

The function signature has 21 parameters including seven JIT name strings passed individually:

```rust
// cache.rs:362-383
pub fn compile_module_to_object(
    module_path: &ModuleFullPath,
    defns: &[(&Defn, &Scheme)],
    method_resolutions: &MethodResolutions,
    fn_slots_base: &HashMap<String, FnSlot>,
    fn_to_module: &HashMap<String, String>,
    primitive_entries: &[PrimitiveEntry],
    global_names: &HashSet<String>,
    builtin_method_info: &HashMap<String, (String, usize)>,
    trait_method_names: &HashSet<String>,
    type_defs: Option<&HashMap<String, TypeDefInfoCg>>,
    constructor_to_type: Option<&HashMap<String, String>>,
    expr_types: &HashMap<Span, Type>,
    alloc_jit_name: &str,
    free_jit_name: &str,
    panic_jit_name: &str,
    par_eval_jit_name: &str,
    ivar_create_jit_name: &str,
    ivar_spark_jit_name: &str,
    ivar_force_jit_name: &str,
    next_got_slot: usize,
) -> Result<Vec<u8>, CranelispError>
```

The seven JIT name strings (`alloc_jit_name`, ..., `ivar_force_jit_name`) are always the same string literals at both call sites (`write_module_cache` at `cache.rs:819-826` and `process_cache_packet` at `cache.rs:998-1005`). This pattern is also how `#[allow(clippy::too_many_arguments)]` ends up applied.

**Impact**: Every caller must supply identical string literals, creating risk of one call site diverging. Any new intrinsic requires adding another parameter at both call sites. The function is impossible to call correctly without reading every argument.

**Recommendation**: Consolidate the seven JIT name strings into a `struct IntrinsicNames<'a>` with named fields, or better, fold them into `CacheInputs` so that `compile_module_to_object` receives `&CacheInputs` directly. This would also unblock HIGH-1's fix.

---

### MED-1: `write_module_cache()` is dead code — superseded by `build_cache_packet` / `process_cache_packet`

**File**: `src/cache.rs:763-839`
**Severity**: Medium (duplication / maintainability)

`write_module_cache()` (76 lines) duplicates the logic of `build_cache_packet()` + `process_cache_packet()`. It reads from `modules`, clones defns, calls `extract_cache_inputs`, calls `compile_module_to_object` with hardcoded string literals, and writes files. However, the batch path and REPL path both use `build_cache_packet` + `process_cache_packet` exclusively. `write_module_cache` is declared `pub` and is not referenced by any caller in the current codebase:

```rust
// cache.rs:763 — pub but unused
pub fn write_module_cache(
    cache_dir: &Path,
    mod_path: &ModuleFullPath,
    mod_name: &str,
    modules: &mut HashMap<ModuleFullPath, CompiledModule>,
    // ...
```

**Impact**: Maintenance burden: any change to the cache write protocol must be applied to three functions instead of two. Risk that `write_module_cache` is re-introduced into a call site in a different form without the deferred-write guarantees of `CacheWritePacket`.

**Recommendation**: Remove `write_module_cache`. If a synchronous write API is needed in the future, it should delegate to `build_cache_packet` + `process_cache_packet`, not re-implement them.

---

### MED-2: `try_load_cached_module()` is 238 lines with duplicated import-resolution logic

**File**: `src/batch.rs:1074-1307`
**Severity**: Medium (complexity / duplication)

The cache-load path re-implements the same import resolution and module alias registration steps that the normal compilation path performs at `batch.rs:302-333`:

```rust
// batch.rs:1100-1127 (cache path) — near-identical to batch.rs:302-333 (normal path)
let resolved_imports = resolve_module_imports(&module.imports, &session.tc, mod_name_to_short)?;
if !resolved_imports.is_empty() {
    session.tc.begin_module_scope(&resolved_imports)?;
}
for import in &module.imports {
    if let Some(ref alias) = import.alias {
        // ... 15 lines of alias registration ...
    }
}
```

Both blocks are identical. If the import-resolution logic ever changes (e.g., new import forms), both blocks must be updated in sync. The function also handles GOT restoration, macro reconstruction, overload reconstruction, and trait method registration — each as a separate block, totalling 238 lines in a single `pub(crate)` function.

**Impact**: High probability of divergence when the module resolution protocol changes. The function is difficult to test in isolation because it takes a `&mut ReplSession` and `&mut Linker`.

**Recommendation**: Extract the import-resolution and alias-registration steps into a `fn install_module_scope(session, module, mod_name_to_short)` helper shared between the cache-load and normal paths. Decompose `try_load_cached_module` into: `load_and_verify_cache_files()`, `install_cached_module()`, and `reconstruct_macros_from_cache()`.

---

### MED-3: Silent failure of cache writes makes cache-miss silent and undebuggable

**File**: `src/cache.rs:943-1033` (`process_cache_packet`)
**Severity**: Medium (robustness)

`process_cache_packet` returns `None` on any `.meta.json` write failure (line 958), and on any `.o` compile/write failure it prints a warning and continues (lines 1013-1025). In both cases the manifest is not updated, so the module appears uncached on next run, triggering a full recompilation. The failures are silent in non-verbose mode. There is no retry, no fallback, and no indication to the user beyond `warning: ...` on stderr.

```rust
// cache.rs:948-959
if let Err(e) = fs::create_dir_all(&packet.cache_dir) {
    eprintln!("warning: failed to create cache dir for {}: {}", mod_name, e);
    return None;
}
// ...
if let Err(e) = atomic_write(&meta_path, &packet.meta_json_bytes) {
    eprintln!("warning: failed to write .meta.json for {}: {}", mod_name, e);
    return None; // silently abandoned
}
```

A partial failure where `.meta.json` succeeds but `.o` fails leaves the cache in an inconsistent state: the manifest gets updated (via the `Some(...)` return) but no `.o` file is written. On the next run, `try_load_cached_module` loads the `.meta.json`, finds no `.o`, and proceeds without linking (correct for macro-only modules, but incorrect for modules that did have definitions). This is not verified against the `defn_data.is_empty()` check.

**Impact**: A full disk or permission error during the first run silently leaves the project without a cache. Subsequent runs pay full compile cost with no user-visible explanation.

**Recommendation**: Distinguish transient errors (disk full, permission) from permanent ones. Add a `CRANELISP_CACHE=warn|error|silent` env var. On write error for a module with definitions, consider writing a sentinel file so the next run can report "cache was attempted but failed" rather than silently recompiling.

---

### MED-4: Linker GOT table is a fixed-size 512-entry hard limit with `assert!` on overflow

**File**: `src/linker.rs:59-60`, `src/linker.rs:99-102`
**Severity**: Medium (robustness)

The linker allocates a fixed 512-entry internal GOT for GOT-load relocations at construction time:

```rust
// linker.rs:59-60
const LINKER_GOT_MAX_ENTRIES: usize = 512;

// linker.rs:99-102
assert!(
    self.got_count < LINKER_GOT_MAX_ENTRIES,
    "linker GOT overflow: too many GOT-load symbols"
);
```

This `assert!` panics in release mode. A large project that introduces many platform functions or trait method specializations could exceed 512 unique GOT-load symbols. The GOT mmap in `Linker::new()` also panics if `mmap_anon` fails (line 74): `let got_mmap = MmapMut::map_anon(got_size).expect("failed to mmap linker GOT")`.

**Impact**: Projects that grow beyond 512 GOT-load symbols crash the process. The limit is not communicated to users, and there is no graceful degradation.

**Recommendation**: Replace the assert with a `Result`-returning resize: grow the GOT mmap when the current page is full, or switch to a `Vec<u64>` that grows on demand (then mprotect-lock it before use). Replace the `expect()` in `Linker::new()` with a `Result` return so callers can handle memory exhaustion.

---

### MED-5: Binary fingerprint uses mtime, not content hash — can fail to detect incremental Cargo rebuilds

**File**: `src/cache.rs:197-224`
**Severity**: Medium (robustness)

The binary fingerprint used for cache invalidation is the executable's modification time:

```rust
// cache.rs:214-217
let duration = mtime.duration_since(std::time::UNIX_EPOCH).unwrap_or_default();
let fp = format!("mtime-{}.{}", duration.as_secs(), duration.subsec_nanos());
```

Incremental Cargo builds may update some object files without touching the final binary if no public-symbol change occurred (e.g., a pure-private-function optimization). Conversely, a `touch target/debug/cranelisp` or a filesystem copy that preserves mtime would produce a false negative (cache appears valid but binary changed). The fingerprint is also silently empty if `current_exe()` or `metadata()` or `modified()` fails, which causes the binary fingerprint check to be skipped entirely:

```rust
// cache.rs:1049-1054
let current_fp = binary_fingerprint();
if !current_fp.is_empty()
    && !manifest.binary_fingerprint.is_empty()
    && manifest.binary_fingerprint != current_fp
{
    return false;
}
```

Both `current_fp.is_empty()` and `manifest.binary_fingerprint.is_empty()` are treated as "skip the check" rather than "invalidate the cache", meaning a failed fingerprint lookup silently accepts potentially stale caches.

**Impact**: On platforms where `FileTime::modified()` is unavailable or where incremental builds don't update mtime, the fingerprint provides no protection. A developer who changes codegen internals (e.g., modifying `codegen/expr.rs`) without bumping `CACHE_FORMAT_VERSION` will silently run cached `.o` files compiled with the old codegen.

**Recommendation**: Replace mtime with a SHA-256 of the executable bytes (at most a few MB; can be streamed). Add `CACHE_FORMAT_VERSION` to the binary fingerprint computation as a belt-and-suspenders measure. Document that `CACHE_FORMAT_VERSION` must be bumped for any codegen semantic change.

---

### MED-6: `is_manifest_compatible` OS check uses string containment on triple — brittle

**File**: `src/cache.rs:1038-1069`
**Severity**: Medium (robustness)

The target triple compatibility check uses `contains()` on an ad-hoc OS string:

```rust
// cache.rs:1056-1068
if !manifest.target_triple.contains(std::env::consts::ARCH) {
    return false;
}
let os = std::env::consts::OS;
if manifest.target_triple.contains(os) {
    return true;
}
if os == "macos" && manifest.target_triple.contains("darwin") {
    return true;
}
false
```

This admits false positives: a triple `x86_64-unknown-linux-gnu` contains `"x86_64"` for the ARCH check, but also contains `"linux"` for the OS check. A manifest triple `aarch64-apple-darwin` on an `x86_64` host would correctly fail the ARCH check, but if someone stored `"x86_64-apple-ios-macabi"` it would incorrectly pass both ARCH and OS checks. The function returns `false` by default (line 1068) rather than returning `false` after the OS check fails, which could be confusing.

**Impact**: Wrong architecture caches could be accepted on cross-compilation setups or simulators. The triple comparison is not exact, so any architectural variant (e.g., `x86_64h`) would be accepted for `x86_64`.

**Recommendation**: Parse the triple with `cranelift_native::builder().triple()` at manifest-write time and store it structured. At read time, compare `manifest.target_triple == current_triple.to_string()` using the Cranelift triple's `Display` representation, special-casing only the `macos`/`darwin` alias. Alternatively, use `target_lexicon::Triple::from_str` for both and compare components.

---

### MED-7: `extract_cache_inputs` is O(n) linear scan over all modules for every cache write

**File**: `src/cache.rs:60-124`
**Severity**: Medium (performance)

`extract_cache_inputs` iterates every module's every symbol three times per batch (once at `write_module_cache`, once at `build_cache_packet` after the compile loop). In batch mode with 20+ modules, this is called once and the result is shared — but in the REPL path, `build_cache_packet` is called per module and each call receives the same pre-extracted `cache_inputs`, so this is fine. However, `write_module_cache` (flagged for removal in MED-1) calls `extract_cache_inputs` inside its own body, performing a redundant full scan:

```rust
// cache.rs:801 — inside write_module_cache, full scan on every call
let cache_inputs = extract_cache_inputs(modules);
```

The `filter_fn_slots_for_module` function also traverses all module symbols twice (once via `collect_module_deps`, once to build `relevant_fn_names`), and the entire resulting map may be rebuilt per module in the background writer.

**Impact**: For a 30-module project, the batch cache write phase performs 30 symbol-table scans for `fn_slots_snapshot` filtering. Currently acceptable, but could be significant if the project grows to 100+ modules with dense symbol tables.

**Recommendation**: Compute `extract_cache_inputs` once before the cache-write loop (already done in batch mode). Remove `write_module_cache` (MED-1) to eliminate its redundant call. Profile before optimizing further.

---

### LOW-1: `CacheWritePacket.fn_slots_snapshot` stores `(usize, usize)` tuples — lossy representation

**File**: `src/cache.rs:853`
**Severity**: Low (data modeling)

`fn_slots_snapshot` converts `FnSlot { got_ref, slot, param_count }` down to `(usize, usize)` (slot, param_count) to avoid the non-`Send` `GotReference::Immediate(usize)`. The `GotReference` is then reconstructed as `GotReference::Immediate(0)` (a placeholder) in `process_cache_packet`. This means the `FnSlot` type's `got_ref` field is meaningless during background write but cannot be omitted.

```rust
// cache.rs:853
pub fn_slots_snapshot: HashMap<String, (usize, usize)>, // fn name → (slot, param_count)
// ...
// cache.rs:964-977 — placeholder reconstructed at use time
FnSlot {
    got_ref: GotReference::Immediate(0), // placeholder
    slot: *slot,
    param_count: *param_count,
}
```

**Impact**: The `(usize, usize)` type has no names for its fields; readers must know the order. If `FnSlot` gains a third meaningful field, the snapshot must be updated separately.

**Recommendation**: Introduce a `FnSlotSnapshot { slot: usize, param_count: usize }` struct (or make `FnSlot` serializable by storing `slot` and `param_count` without the non-Send pointer). This makes the intent explicit and survives `FnSlot` evolution.

---

### LOW-2: `declare_imported_func` signature hardcodes `I64` for all params and returns

**File**: `src/cache.rs:671-690`
**Severity**: Low (code clarity)

Every function in the cranelisp ABI uses only `I64` parameters and returns. `declare_imported_func` accepts `param_count` and `return_count` integers but hardcodes `types::I64` for all of them. This is correct by design but obscures that the function could be simplified to just `(module, name, param_count) -> Result<FuncId>` since `return_count` is always 1.

```rust
// cache.rs:671-690
fn declare_imported_func(
    module: &mut ObjectModule,
    name: &str,
    param_count: usize,
    return_count: usize, // always called with 1
) -> Result<FuncId, CranelispError> {
```

**Impact**: Minor readability issue. `return_count: usize` in the signature implies flexibility that doesn't exist.

**Recommendation**: Remove `return_count` and hardcode `sig.returns.push(AbiParam::new(types::I64))` directly, or add a comment `// ABI: all cranelisp functions return exactly one i64`. This makes the constraint explicit rather than buried in parameter conventions.

---

### LOW-3: `try_load_cached_module` returns `Option<bool>` — two-level optionality is confusing

**File**: `src/batch.rs:1074`, `src/batch.rs:1083`
**Severity**: Low (data modeling)

The return type `Result<Option<bool>, CranelispError>` encodes three outcomes: `Ok(None)` = cache miss (files not found), `Ok(Some(true))` = cache hit (caller should continue), and a hypothetical `Ok(Some(false))` that never occurs. The `Some(false)` variant exists in the old code structure but the current code always returns `Ok(Some(true))` or `Ok(None)`:

```rust
// batch.rs:1083
) -> Result<Option<bool>, CranelispError> {
// ...
// only two return points:
return Ok(None);   // cache miss
// ...
Ok(Some(true))     // cache hit
```

**Impact**: Callers must handle a `Some(false)` case that can never happen. The `bool` inside `Some` is meaningless.

**Recommendation**: Change the return type to `Result<Option<()>, CranelispError>` or better `Result<CacheLoadResult, CranelispError>` where `enum CacheLoadResult { Hit, Miss }`. The `()` variant eliminates the dead `Some(false)` state; the enum makes the semantics self-documenting.

---

### LOW-4: `module_file_name` replaces `.` with `_` — collision risk for nested module paths

**File**: `src/cache.rs:343-349`
**Severity**: Low (robustness)

The cache filename for a module is computed by replacing `.` with `_`:

```rust
// cache.rs:343-349
pub fn module_file_name(module_path: &ModuleFullPath) -> String {
    if module_path.is_root() {
        "_root".to_string()
    } else {
        module_path.0.replace('.', "_")
    }
}
```

A module named `core_io` and another named `core.io` would both map to `core_io.meta.json`. The chance of collision is low given the current naming conventions, but there is no assertion or check.

**Impact**: Cache files for two differently-named modules could overwrite each other silently.

**Recommendation**: Use a separator that cannot appear in module names, such as `__`, or escape dots as `__dot__`. Alternatively, URL-encode the path.

---

### LOW-5: Zero unit tests for cache, cache_writer, and linker

**File**: `src/cache.rs`, `src/cache_writer.rs`, `src/linker.rs`
**Severity**: Low (quality assurance)

All 14 cache tests are subprocess-level integration tests that run the cranelisp binary and inspect disk files. There are no unit tests for:

- `hash_source()` (pure function, trivially testable)
- `is_manifest_compatible()` (complex multi-condition logic with the OS/arch quirks)
- `CacheManifest::is_cached()` and `upsert_module()`
- `module_file_name()` (the `.`-to-`_` replacement)
- `atomic_write()` failure modes
- `filter_fn_slots_for_module()` and `collect_module_deps()`
- `Linker::load_object()` with synthetic object bytes

**Impact**: The integration tests verify end-to-end correctness but cannot isolate failures in individual cache functions. Changes to `is_manifest_compatible` or `module_file_name` have no unit-level regression coverage.

**Recommendation**: Add `#[cfg(test)]` unit tests inside `cache.rs` for the pure functions (`hash_source`, `is_manifest_compatible`, `module_file_name`, `CacheManifest::is_cached`). Use `tempfile` for `atomic_write` and `write_manifest` tests. These do not require a full JIT session and can run in milliseconds.

---

## Prioritized Improvement Plan

### Phase 1: Safety — Eliminate Panics and Silent Failures

1. **HIGH-2**: Extract `build_isa_flags(is_pic: bool)` shared by JIT, cache, and exe paths. One-file change in `jit.rs`, eliminates ISA flag drift.
2. **MED-4**: Make `Linker::new()` return `Result<Linker, CranelispError>` and replace the GOT overflow `assert!` with a `Result` error. Update callers in `batch.rs`.
3. **MED-3**: Add a distinct log level or env var for cache write failures. Ensure partial failure (`.meta.json` written, `.o` not) does not update the manifest.

### Phase 2: Correctness — Close the JIT/Cache Divergence Gap

4. **HIGH-1**: Create a `CacheIntrinsicEntry` table that lists all intrinsics (including RC and trace) with their names and signatures. Thread it through `CacheInputs` and declare all of them in `compile_module_to_object()`. This is the single most important correctness fix.
5. **HIGH-3**: Consolidate the 7 JIT name string parameters into a field on `CacheInputs`. Reduces `compile_module_to_object` from 21 to ~13 parameters.

### Phase 3: Maintainability — Remove Dead Code and Simplify

6. **MED-1**: Remove `write_module_cache()`. Verify no callers exist, then delete.
7. **MED-2**: Extract `install_module_scope(session, module, mod_name_to_short)` shared helper. Decompose `try_load_cached_module` into 3 smaller functions.
8. **LOW-3**: Change `try_load_cached_module` return type to `Result<Option<()>, CranelispError>`.
9. **LOW-1**: Introduce `FnSlotSnapshot { slot: usize, param_count: usize }` in `CacheWritePacket`.
10. **LOW-2**: Remove `return_count` from `declare_imported_func`, hardcode the single-return ABI.

### Phase 4: Robustness — Improve Fingerprinting and Validation

11. **MED-5**: Replace mtime fingerprint with SHA-256 of binary bytes. Document the `CACHE_FORMAT_VERSION` bump requirement in `src/cache.rs` header comment.
12. **MED-6**: Replace triple-string containment check with exact string comparison using the Cranelift triple's `Display` output.
13. **LOW-4**: Change `module_file_name` separator from `_` to `__` to avoid collision.

### Phase 5: Test Coverage

14. **LOW-5**: Add `#[cfg(test)]` unit tests in `cache.rs` for `hash_source`, `is_manifest_compatible`, `module_file_name`, `CacheManifest::is_cached`/`upsert_module`. Target: 10-15 unit tests.
15. Add a cache-hit correctness test that verifies execution result of cached code equals result of freshly compiled code for a non-trivial program (currently the integration tests only check output equality, which passes through the full subprocess).

---

## Verification

```sh
# Ensure no regressions after changes
just test

# Check for remaining panics in non-test cache code
grep -n 'panic!\|\.unwrap()\|\.expect(' src/cache.rs src/cache_writer.rs src/linker.rs

# Verify no remaining callers of write_module_cache after MED-1 removal
grep -rn 'write_module_cache' src/

# Confirm ISA flag extraction after HIGH-2
grep -n 'flag_builder\|is_pic\|use_colocated' src/jit.rs src/cache.rs src/exe.rs

# Run cache-specific integration tests
cargo test --test integration cache -- --nocapture 2>&1 | tail -30

# Check clippy (the too_many_arguments attribute should be removable after HIGH-3)
just check
```
