//! Return shapes for the backend's codegen entry points.
//!
//! Backend's three codegen free functions return:
//!
//! - `compile_to_module` returns `CompilationArtifacts` (defined in `lib.rs`,
//!   not here) by value, and writes the compiled fn pointer directly into the
//!   entry's GOT slot via `got().store_slot(slot, ptr)`. It constructs no
//!   `Code` and no per-symbol artefact map: the caller composes `Code::Jit`
//!   from its own `Arc<Jit>` after the call.
//!
//! - `load_object` returns a [`LinkerArtefact`]: the per-module retention root
//!   for cache-hit code (`Arc<Linker>`) plus a per-symbol address map `int`
//!   walks to populate `Code::Linker` lifecycle owners and write each
//!   per-symbol address into the entry's GOT slot via `got().store_slot`.
//!
//! - `produce_disasm` returns a `String` (not an artefact).
//!
//! [`ObjectArtefact`] is a typed shape that is **not currently produced** by
//! any backend code path. The object path is `compile_to_module::<ObjectModule>`
//! followed by the caller's `obj_module.finish().emit()` for the `.o` bytes,
//! with the sidecar `SymbolTable<(), ()>` serialised by `cache::serialize`.
//! It is retained only because it is named in the public-API baseline; it is a
//! delete-candidate for a future backend sprint (removal is a public-API edge
//! change, out of scope for doc-only work).
//!
//! Both DTOs are `#[non_exhaustive]`. They live in `cranelisp-backend` (not
//! `cranelisp-types`) because both reference backend-owned types
//! (`Arc<Linker>` / a serialised symbol table); hoisting them into
//! `cranelisp-types` would invert the `cranelisp-types` -> `cranelisp-backend`
//! dependency edge that Principle 3 protects.

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

/// A sidecar + `.o` pair shape — **not currently produced** by any backend
/// code path.
///
/// The object path is `compile_to_module::<ObjectModule>` plus the caller's
/// `obj_module.finish().emit()` (which yields the `.o` bytes) and the sidecar
/// `SymbolTable<(), ()>` serialised by `cache::serialize`; backend never
/// constructs an `ObjectArtefact`. The two fields below describe the shape a
/// future single-call object entry might return: the native host-platform
/// bytes (Mach-O / ELF / COFF) and the no-code/no-linker sidecar
/// (`C = (), L = ()` per Decision 32; carries types, schemes, AST bodies, GOT
/// slot layout, structural decls, and `schema_version` per Decisions 25/34).
///
/// **Delete-candidate.** Retained only because it is named in the public-API
/// baseline; removal is a public-API edge change for a future backend sprint.
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
