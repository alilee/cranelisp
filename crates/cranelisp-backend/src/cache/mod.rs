//! Module caching — backend's persistence half (an internal implementation
//! detail, NOT a separate bounded-context surface).
//!
//! Serialises the typecheck product (sidecar) + the codegen product (`.o`) to
//! disk, validates cache hits against current source hashes and toolchain
//! fingerprints, and reads them back into memory at session start. It lives in
//! `cranelisp-backend` because the cache `Linker` newtype mediates ELF/Mach-O
//! object loading — a Cranelift-adjacent capability `cranelisp-types` may not
//! name (Principle 3).
//!
//! On-disk layout:
//! ```text
//!   .cranelisp-cache/
//!     manifest.json           # version, target triple, module hashes
//!     <module>.meta.json      # serialized SymbolTable (includes GOT slot assignments)
//!     <module>.o              # relocatable object file
//! ```
//! See `design/backend/module-caching.md` for the full design.
//!
//! # Four sibling submodules
//!
//! | Submodule | Role |
//! |---|---|
//! | [`linker`] | Mach-O / ELF object loading + per-symbol resolution (wraps `memmap2` + `object`). |
//! | [`manifest`] | Cache index (`manifest.json`): per-module source + dependency hashes; cache-validity check against compiler fingerprint, target triple, cranelift version, format version. |
//! | [`object`] | `.o` build-packet construction + processing; `ObjectModule` + `TargetIsa` plumbing; GOT data-symbol naming. Drives the object path `compile_to_module::<ObjectModule>` + caller `finish().emit()`. |
//! | [`serialize`] | Sidecar (`.meta.json`) read/write; `SymbolTable<(), ()>` serde; `CacheStale` discrimination at deserialise time. |
//!
//! This crate-internal root holds the genuine multi-submodule orchestration
//! helpers ([`CachedModule`], [`module_cache_path`], [`try_load_cached_module`],
//! [`load_cached_object`]) and the version consts ([`CACHE_SCHEMA_VERSION`],
//! `CACHE_FORMAT_VERSION`, [`BUILD_ID`]). The canonical home of every cache
//! type is exactly one submodule.
//!
//! # Cache invariants (internal implementation invariants)
//!
//! These describe how the cache submodule behaves internally — they are not
//! contracts the rest of the workspace reasons about at the bounded-context
//! boundary:
//!
//! 1. **`Linker` is the only mmap-holder.** No other type in the workspace
//!    holds mmap'd object memory. Per-symbol retention via `Arc<Linker>`
//!    (cloned per `Code::Linker` clone) keeps pages alive until the last
//!    reference drops. (See [`linker`].)
//! 2. **`CacheManifest` is the single index.** Per-module sidecars
//!    (`{module}.meta.json`) and objects (`{module}.o`) are referenced via
//!    `CacheManifest::modules`, pair-invariantly (sidecar present implies
//!    object present, and vice versa). (See [`manifest`].)
//! 3. **Cache-validity is checked at every cache-hit attempt.**
//!    `manifest::check_manifest` runs before any [`try_load_cached_module`];
//!    a stale cache surfaces as `serialize::CacheStale` and the caller
//!    recompiles — no implicit "use stale cache anyway" fallback.
//! 4. **One version number covers the manifest and the sidecars.**
//!    `CACHE_FORMAT_VERSION` is an alias of [`CACHE_SCHEMA_VERSION`]. A
//!    version-mismatched manifest invalidates all cached modules atomically; a
//!    mismatched sidecar invalidates only that one module.
//! 5. **No re-codegen on cache-hit.** Cache-hit modules skip
//!    `compile_to_module` entirely; [`load_cached_object`] maps the pre-built
//!    `.o` into the caller's `Linker` and returns one address per target, and
//!    int writes the GOT slots and `Code::Linker` lifecycle owners. The `.o`
//!    byte content is authoritative; no
//!    per-symbol re-emission ever happens.
//!
//! # Forbidden patterns
//!
//! - **No `pub` items shared across submodules without a single canonical
//!   home.** Each cache type lives in exactly one submodule by responsibility;
//!   new types are NOT re-exported at `cache::` root unless they are genuine
//!   multi-submodule orchestration helpers.
//! - **No serde-shape change without a [`CACHE_SCHEMA_VERSION`] bump** (see
//!   [`serialize`]).

use cranelisp_types::ErrorLocation;

pub mod linker;
pub mod manifest;
pub mod object;
pub mod serialize;

// No root re-export layer: each item has one canonical path in its submodule
// (`manifest`, `serialize`, `object`, `linker`), and callers use that path.
// `public-api.txt` is the evidence of the published paths.

/// Cache schema version (Decision 34, Sprint 58 §14.2).
///
/// Stamped onto `SymbolTable.schema_version` at cache-write time. Cache-load
/// peeks the field first; mismatch returns `CacheStale::SchemaMismatch` and
/// the caller falls through to a fresh build (same code path as dep-hash
/// mismatch).
///
/// Bump on:
/// * field deletions on `SymbolTable` / any `ModuleEntry` variant,
/// * field type changes (`deserialise<New>` would fail on persisted Old),
/// * enum variant additions to a serde-tagged enum used inside `SymbolTable`,
/// * variant renames.
///
/// Field additions with `#[serde(default)]` whose default matches a fresh-build
/// value do NOT require a bump.
///
/// Also bump on a **value-only** change: the serde shape is unchanged, but a
/// persisted value, or the RC contract baked into the paired `.o`, now means
/// something else, so a warm hit on unchanged source would load the old
/// meaning. `BUILD_ID` does not cover this case, because an uncommitted build
/// stamps its base commit's sha.
///
/// A bump refuses every older sidecar and its paired object wholesale; there
/// is no translation path. The reason for each past bump is in Git history.
pub const CACHE_SCHEMA_VERSION: u32 = 37;

/// Compile-time build identifier (Sprint 60 Workstream C).
///
/// Emitted by `build.rs` as `<pkg_version>+<git_sha>` (e.g. `0.1.0+3b2df720fe63`),
/// stamped onto `.meta.json` next to `schema_version`, and compared on cache-load.
/// Mismatch routes through the same `CacheStale` fall-through as a schema-version
/// bump or a source-mtime change.
///
/// **This is an ADDITIONAL cache-invalidation trigger, not a substitute for the
/// manual `CACHE_SCHEMA_VERSION` bump that Decision 34 requires on explicit
/// serialised-shape changes.** The build-id catches the "I rebuilt the compiler
/// and forgot the cache was keyed on the old shape" class of mystery; it does
/// NOT replace the discipline of bumping `CACHE_SCHEMA_VERSION` whenever a
/// `SymbolTable` / `ModuleEntry` field is deleted, retyped, or renamed. Both
/// triggers coexist: shape changes that also rebuild the compiler hit the
/// build-id gate first; shape changes that land without a compiler-side rebuild
/// (cross-branch cache reuse) are caught only by the schema-version gate.
///
/// Pre-Sprint-60 `.meta.json` files lack the `build_id` field; they deserialise
/// with the `#[serde(default)]` empty string, which never matches a non-empty
/// `BUILD_ID` and routes through the same fall-through path.
pub const BUILD_ID: &str = env!("CRANELISP_BUILD_ID");

/// The manifest's format version: an alias of [`CACHE_SCHEMA_VERSION`], so the
/// manifest and every sidecar are versioned by one number.
pub(crate) const CACHE_FORMAT_VERSION: u32 = CACHE_SCHEMA_VERSION;

/// Compute the cache directory path for module files.
///
/// Module hierarchy maps to filesystem directories:
///   `core.numerics` -> `core/numerics.{meta.json,o}`
///   `user` -> `user.{meta.json,o}`
///   entry module -> `_entry.{meta.json,o}`
pub fn module_cache_path(
    cache_dir: &std::path::Path,
    module_path: &cranelisp_types::ModuleFullPath,
) -> (std::path::PathBuf, std::path::PathBuf) {
    let (dir, stem) = module_dir_and_stem(module_path);
    let base = if dir.is_empty() {
        cache_dir.to_path_buf()
    } else {
        cache_dir.join(dir)
    };
    (
        base.join(format!("{stem}.meta.json")),
        base.join(format!("{stem}.o")),
    )
}

/// Split a module path into (directory, stem) components.
/// `core.numerics` -> ("core", "numerics")
/// `user` -> ("", "user")
/// Root/entry -> ("", "_entry")
fn module_dir_and_stem(module_path: &cranelisp_types::ModuleFullPath) -> (String, String) {
    let path_str: &str = module_path.as_ref();
    if path_str.is_empty() || path_str == "_root" || path_str == "_entry" {
        return (String::new(), "_entry".to_string());
    }
    if let Some(dot_pos) = path_str.rfind('.') {
        let dir = path_str[..dot_pos].replace('.', "/");
        let stem = path_str[dot_pos + 1..].to_string();
        (dir, stem)
    } else {
        (String::new(), path_str.to_string())
    }
}

/// Result of loading a cached module from disk.
///
/// Contains all the metadata needed to restore a module into the compilation
/// session without re-parsing, expanding macros, or type-checking. The `/int`
/// pipeline installs these into the TypeChecker and codegen state.
///
/// **Sprint 22 scope**: Metadata-only cache. On cache hit, the symbol table
/// and module structure are restored from `.meta.json`, allowing downstream
/// modules to typecheck against this module's exports. Codegen is still
/// re-done from source (fast compared to full pipeline). Full `.o` loading
/// via the Linker is deferred to a future sprint.
#[derive(Debug, Clone)]
pub struct CachedModule {
    /// The deserialized module symbol table (structure + codegen state).
    ///
    /// **S111 CS-5 (FIXME 0634)**: the deprecated `CacheMetadata` envelope is
    /// gone — `load_meta` deserialises the `SymbolTable` directly (the on-disk
    /// format has been SymbolTable-direct since Sprint 58 Wave 2b; the envelope
    /// was an in-memory back-compat wrapper only). Consume this field directly.
    pub symbol_table: cranelisp_types::SymbolTable,
    /// Path to the `.meta.json` file (for diagnostics).
    pub meta_path: std::path::PathBuf,
    /// Path to the `.o` file (may not exist yet in metadata-only mode).
    pub object_path: std::path::PathBuf,
    /// Whether a valid `.o` file exists on disk.
    pub has_object: bool,
}

impl CachedModule {
    /// Get the restored symbol table.
    pub fn symbol_table(&self) -> &cranelisp_types::SymbolTable {
        &self.symbol_table
    }

    /// Extract the set of module paths this cached module imports from.
    ///
    /// Scans Import entries in the symbol table and collects the unique
    /// source module paths. The orchestration layer uses this to
    /// recursively load transitive dependencies from cache.
    ///
    /// Excludes `primitives` and `macros` (synthetic compiler modules)
    /// since they are always available without cache loading.
    pub fn imported_modules(&self) -> std::collections::HashSet<cranelisp_types::ModuleFullPath> {
        let mut modules = std::collections::HashSet::new();
        for (_name, candidate) in self.symbol_table.all_name_candidates() {
            let mod_path = &candidate.source.module;
            if *mod_path != self.symbol_table.path
                && mod_path.as_ref() != "primitives"
                && mod_path.as_ref() != "macros"
            {
                modules.insert(mod_path.clone());
            }
        }
        modules
    }
}

/// Attempt to load a cached module from disk.
///
/// Returns `Ok(Some(CachedModule))` if the `.meta.json` exists and is valid.
/// Returns `Ok(None)` if the cache files are missing or corrupt (cache miss).
/// Returns `Err` only on unexpected I/O errors.
///
/// The caller (pipeline) is responsible for:
/// 1. Checking the manifest first via `check_manifest()` to confirm the
///    module's source hash is current.
/// 2. Installing the returned `CachedModule` into the TypeChecker.
/// 3. Deciding whether to skip codegen (if `.o` exists) or recompile
///    (metadata-only mode).
///
/// **Cache-load/fresh-compile equivalence invariant**: The deserialized
/// `SymbolTable` must have the same entries as a freshly typechecked module.
/// This is enforced structurally: both paths feed the same
/// `install_module_scope()` function in the pipeline.
pub fn try_load_cached_module(
    cache_dir: &std::path::Path,
    module_path: &cranelisp_types::ModuleFullPath,
) -> Result<Option<CachedModule>, cranelisp_types::CranelispError> {
    let (meta_path, object_path) = module_cache_path(cache_dir, module_path);

    // Use the authoritative `load_meta` API; treat any `CacheStale` variant
    // as a cache miss (§14.7 — every variant maps to "fall through to fresh
    // build" caller-side).
    let symbol_table = match serialize::load_meta(&meta_path) {
        Ok(t) => t,
        Err(_stale) => return Ok(None),
    };

    // Validate the module path matches (defense against file mix-ups)
    if symbol_table.path != *module_path {
        return Ok(None);
    }

    // Check for .o file existence (for future full-cache-hit path)
    let has_object = object_path.exists()
        && std::fs::metadata(&object_path)
            .map(|m| m.len() > 0)
            .unwrap_or(false);

    Ok(Some(CachedModule {
        symbol_table,
        meta_path,
        object_path,
        has_object,
    }))
}

/// Load a cached module's `.o` file into the linker and return function addresses.
///
/// This is the entry point for `/int` to use on cache hit with `has_object: true`.
/// It reads the `.o` file, loads it into the linker (resolving relocations against
/// registered symbols), and returns exact callable targets paired with code
/// pointers for wiring into the live GOT.
///
/// **Prerequisites** (the caller must ensure before calling):
/// 1. All external symbols the `.o` references are registered with the linker:
///    - Runtime intrinsics (`linker.register_symbol("runtime/alloc", ptr)`)
///    - Functions from already-loaded modules (topo order guarantees this)
///    - GOT base pointers for already-compiled modules
/// 2. The `CachedModule` was loaded via `try_load_cached_module()` and
///    `has_object` is `true`.
///
/// **After calling**, the caller should wire each returned target into the live
/// GOT using the slot carried by that exact target's callable arm.
///
/// Returns a map of semantic execution target → code pointer (`*const u8`).
pub fn load_cached_object(
    linker: &mut linker::Linker,
    cached: &CachedModule,
) -> Result<
    std::collections::HashMap<cranelisp_types::CallableTarget, *const u8>,
    cranelisp_types::CranelispError,
> {
    let obj_bytes = std::fs::read(&cached.object_path).map_err(|e| {
        cranelisp_types::CranelispError::CodegenError {
            message: format!(
                "failed to read cached object file '{}': {e}",
                cached.object_path.display()
            ),
            location: ErrorLocation::from_span(cranelisp_types::Span::SYNTHETIC),
        }
    })?;

    linker.load_object(cached.symbol_table.path.as_ref(), &obj_bytes)?;

    // The emitted spelling remains backend-private. Only the semantic target
    // crosses back to integration, so cache restore cannot depend on the label
    // grammar used by JIT/ObjectModule.
    let mut fn_addrs = std::collections::HashMap::new();
    for (target, _) in cached.symbol_table().codegen_targets() {
        if let Some(label) = crate::callable_target_label(&target)
            && let Ok(addr) = linker.get_symbol(label.as_ref())
        {
            fn_addrs.insert(target, addr);
        }
    }

    Ok(fn_addrs)
}

/// Atomic file write: write a temporary beside `path`, flush it and rename it
/// onto `path`, so a reader never sees a partial file. Concurrent writers of
/// one target never share a temporary, so each publishes whole bytes and the
/// last rename wins. A failed step removes the temporary.
pub(crate) fn atomic_write(path: &std::path::Path, data: &[u8]) -> std::io::Result<()> {
    use std::io::Write;
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let temporary = write_temporary(path);
    let mut file = std::fs::File::create_new(&temporary)?;
    let written = file.write_all(data).and_then(|()| file.sync_all());
    drop(file);
    let published = written.and_then(|()| std::fs::rename(&temporary, path));
    if published.is_err() {
        // Best effort: readers open only the target, never a temporary.
        let _ = std::fs::remove_file(&temporary);
    }
    published
}

/// A name beside `path` that no other write, in this process or another, uses.
fn write_temporary(path: &std::path::Path) -> std::path::PathBuf {
    static NEXT_WRITE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let write = NEXT_WRITE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let mut name = path.file_name().unwrap_or_default().to_os_string();
    name.push(format!(".{}.{write}.tmp", std::process::id()));
    path.with_file_name(name)
}

#[cfg(test)]
mod tests;
