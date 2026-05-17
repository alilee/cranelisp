// cranelisp-backend / src/artefact.rs — return shapes for the backend's
// non-`compile_to_module` codegen entry points
//
// Per `design/arch/facades/backend.md` §"Return shapes":
//
// - `compile_to_module` returns `Result<(), CompilationError>` — no
//   artefact struct. Backend writes Code and Introspection directly into
//   the passed-in stores per Decision 41.
//
// - `load_object` returns a `LinkerArtefact` — the per-module retention
//   root for cache-hit code (`Arc<Linker>`) plus a per-symbol address map
//   that `int` walks to populate `Code::Linker` lifecycle owners and write
//   each per-symbol code address into the entry's GOT slot via
//   `got().store_slot(slot, ptr)`.
//
// - `compile_to_object` returns an `ObjectArtefact` — the native `.o`
//   bytes plus a sidecar `SymbolTable<(), ()>` for the cache
//   `.meta.json`. Backend writes nothing to disk; `int`'s
//   `ObjectCache::write` does the file IO.
//
// Both DTOs are `#[non_exhaustive]` per the facade's `#[non_exhaustive]`
// DTOs policy. They live in `cranelisp-backend` (not `cranelisp-types`)
// per REV-4 — backend is the sole constructor; `int` is the sole consumer.
// Hoisting these into `cranelisp-types` would invert the dependency edge
// `cranelisp-types → cranelisp-backend` that Principle 3 protects (both
// shapes reference backend-owned `Arc<Linker>` / Cranelift artefacts that
// `cranelisp-types` may not name).

use std::collections::HashMap;
use std::sync::Arc;

use cranelisp_types::{Symbol, SymbolTable};

use crate::cache::linker::Linker;

/// Return shape of `load_object`.
///
/// Per `facades/backend.md` §"Return shapes" — `int` consumes the artefact
/// per-symbol: for each `(symbol, ptr)` in `ptrs`, the integration layer
/// stores `Code::Linker(linker.clone())` as the lifecycle owner on the
/// matching `ModuleEntry::Def`, and writes `ptr` into the entry's GOT
/// slot via `symbol_table.got().store_slot(entry.got_slot.unwrap(), ptr)`.
/// The GOT (post-rollback `1dc57ae`) is the single source of truth for
/// callable addresses — `ptr` does not live on the entry itself.
///
/// Per-module cardinality: one `Linker` holds many symbols, so a single
/// `LinkerArtefact` covers the whole cache-hit module's defined symbols.
/// Distinct from `compile_to_module`'s per-symbol cardinality (Decision
/// 41 — per-redefinition reclaim).
#[non_exhaustive]
pub struct LinkerArtefact {
    /// Per-module retention root for cache-hit code. Analogous to
    /// `Arc<Jit>` for JIT-mode code; the `Arc<Linker>` keeps the mmap'd
    /// object alive for as long as any per-symbol `Code::Linker` clone
    /// references it. Reclaim fires when the last clone drops.
    pub linker: Arc<Linker>,
    /// Per-symbol code addresses. `int` walks this map per the
    /// per-symbol direct-write pattern described above.
    pub ptrs: HashMap<Symbol, *const u8>,
}

// SAFETY: `*const u8` is a code address into pages held alive by
// `Arc<Linker>`; the pointers are read but never dereferenced as Rust
// references. The Linker itself is `Send + Sync`. `int` only reads the
// map on the main thread (during cache-hit population) before workers
// observe the GOT writes.
unsafe impl Send for LinkerArtefact {}
unsafe impl Sync for LinkerArtefact {}

/// Return shape of `compile_to_object`.
///
/// Per `facades/backend.md` §"Return shapes" — the `.o` bytes are the
/// native host-platform format (Mach-O / ELF / COFF), and the sidecar is
/// the serialised `SymbolTable<(), ()>` that `int`'s `ObjectCache::write`
/// pairs as `M.meta.json` alongside `M.o`. Per Decision 25 the sidecar
/// carries types, schemes, AST bodies, GOT slot layout, structural
/// decls, and `schema_version` per Decision 34.
///
/// Backend writes nothing to disk; the artefact is plain data handed
/// back to `int` for cache write.
#[non_exhaustive]
pub struct ObjectArtefact {
    /// ELF / Mach-O / COFF bytes for the host platform's native object
    /// format. Produced by Cranelift's `ObjectModule`.
    pub object: Vec<u8>,
    /// Serialised `SymbolTable<(), ()>` for the cache `.meta.json` (no
    /// code, no linker — `C = (), L = ()` per Decision 32). Written by
    /// `int` next to the `.o`.
    pub sidecar: SymbolTable<(), ()>,
}
