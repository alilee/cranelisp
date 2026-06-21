//! Per-function compiled-code handle (Decision 35 + Decision 41).
//!
//! `Code` is the per-symbol lifecycle owner — carried on
//! `ModuleEntry::Def.code` in the integration layer's `SymbolTable<Code, ()>`.
//! It unifies fresh-build (JIT-backed) and cache-hit (Linker-backed) code
//! into one shape so the same field carries either provenance.
//!
//! # Placement (Decision 41 + facade `design/arch/facades/backend.md`)
//!
//! The enum lives in `cranelisp-backend` because both variants reference
//! backend-owned types (`Jit`, `cache::Linker`). Principle 3's protection
//! (no `cranelisp-types → cranelisp-backend` dep) survives intact — `Code`
//! does NOT live in `cranelisp-types`. The integration layer instantiates
//! `SymbolTable<Code, ()>` by importing this type; that's the only crate
//! crossing.
//!
//! # Design
//!
//! `Code` carries **lifecycle ownership ONLY** (S75 W2 slim per
//! `facades/backend.md` §"Code"). The fn ptr for an indirect call lives in
//! the per-module `GotTable` — read via
//! `symbol_table.got().load_slot(entry.got_slot.unwrap())`. The GOT is the
//! single source of truth for callable addresses; there is no per-variant
//! `ptr` field and no `ptr()` accessor (the S66 same-day `fn_ptr` unification
//! rollback `1dc57ae` settled the GOT as authoritative).
//!
//! - `Code::Jit(Arc<Jit>)` — fresh-build batch. `Arc<Jit>` is the retention
//!   root for the JIT-mmap'd executable pages. Multiple entries from the same
//!   compile batch share an `Arc<Jit>` clone (one increment per defined
//!   symbol).
//! - `Code::Linker(Arc<Linker>)` — cache-hit `.o`-mapped batch.
//!   `Arc<Linker>` is the retention root for the mmap'd code regions.
//!
//! # Reclaim (Decision 41 Scenario 2; formerly D31)
//!
//! Per-redefinition reclaim falls out of refcounting:
//! 1. REPL user redefines `(defn f [x] x)`.
//! 2. The old `ModuleEntry::Def` is replaced by `worker::register_def_in_module`;
//!    the prior `code: Some(Code::Jit(Arc<Jit>))` value drops.
//! 3. That decrements the `Arc<Jit>` refcount. If no other entry from the
//!    same batch is still alive, the count hits zero, `Arc::drop` fires
//!    `Jit::drop`, which calls `unsafe JITModule::free_memory()` and
//!    reclaims the mmap'd pages.
//! 4. `Code::Linker` follows the same pattern — when the last
//!    `Code::Linker` referencing an `Arc<Linker>` drops, the linker's
//!    code regions reclaim.
//!
//! # Safety
//!
//! The `unsafe impl Send + Sync` is needed because `cranelift_jit::JITModule`
//! contains non-`Sync` interior mutability (symbol cache); after
//! `compile_to_module` finalises the JIT, the pages are stable and the
//! `Jit` is effectively read-only from external observers. Workers only
//! clone the `Arc` and read `ptr`; they do not call mutating methods on
//! the contained `Jit` after construction.

use std::sync::Arc;

use crate::cache::linker::Linker;
use crate::jit::Jit;

/// Per-function compiled-code handle. Lives on `ModuleEntry::Def.code` in
/// the integration layer's `SymbolTable<Code, ()>` (Decision 35).
///
/// See the module-level docs for the full safety + reclaim contract.
///
/// Manual `Debug` impl (instead of `#[derive(Debug)]`) — `Jit` and `Linker`
/// don't implement `Debug`, but `Code` needs to satisfy `Debug` because
/// `ModuleEntry<C>: Debug` requires `C: Debug`. The Debug output is
/// intentionally minimal (variant tag only); the inner `Arc<Jit>` /
/// `Arc<Linker>` is opaque (would dump JIT internals which is noise at the
/// `:?` debug-print level).
///
/// S75 W2 slim per `facades/backend.md` §"Code": variants carry the
/// lifecycle owner ONLY (no per-variant `ptr`); the `Code::Primitive`
/// marker is deleted (primitive-ness reads from `kind: DefKind::Primitive`;
/// primitives entries carry `code: None`).
#[non_exhaustive]
#[derive(Clone)]
pub enum Code {
    /// Fresh-build code emitted by a `compile_to_module` invocation.
    /// `Arc<Jit>` is the retention root for the JIT-mmap'd pages; the
    /// per-symbol entry-point address lives in the per-module `GotTable`.
    Jit(Arc<Jit>),
    /// Cache-hit code loaded from a `.o` file via the in-process Linker.
    /// `Arc<Linker>` is the retention root for the mmap'd code regions; the
    /// per-symbol resolved address lives in the per-module `GotTable`.
    Linker(Arc<Linker>),
}

impl std::fmt::Debug for Code {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Code::Jit(_) => f.write_str("Code::Jit"),
            Code::Linker(_) => f.write_str("Code::Linker"),
        }
    }
}

// SAFETY: see module-level docs. The `Arc<Jit>` / `Arc<Linker>` carriers
// are themselves `Send + Sync` (Arc requires `T: Send + Sync` to be
// `Send + Sync`). `Jit` (cranelift JIT module wrapper) is not auto-`Sync`
// because of `JITModule`'s interior mutability around its symbol cache, but
// the post-finalize state we hold here is read-only: `Code` instances only
// support cloning the Arc (which is thread-safe refcount bumps). Callable
// addresses are read from the GOT, not from `Code`.
unsafe impl Send for Code {}
unsafe impl Sync for Code {}

impl Code {
    /// Construct a fresh-build `Code::Jit` from the JIT batch's retention
    /// root.
    pub fn jit(jit: Arc<Jit>) -> Self {
        Code::Jit(jit)
    }

    /// Construct a cache-hit `Code::Linker` from the linker's retention
    /// root.
    pub fn linker(linker: Arc<Linker>) -> Self {
        Code::Linker(linker)
    }
}

#[cfg(test)]
mod tests;
