//! Per-function compiled-code handle carried on `ModuleEntry::Def.code`.
//!
//! This is the thin, stable-types handle (Decision 25, `design/arch/CLAUDE.md`).
//! It holds only what `cranelisp-types` can express without depending on
//! `cranelisp-backend`: the raw code pointer.
//!
//! The full runtime record — `{ jit: Arc<Jit>, ptr: *const u8 }` — lives in the
//! integration layer (`src/session_v4.rs`). The session owns the `Arc<Jit>`
//! handles (one per `compile_to_module` call; Decision 28 — per-worker JIT is
//! session-lifetime) so the mmap'd executable pages stay alive for as long as
//! any `Code::ptr` into those pages is reachable.
//!
//! # Safety
//!
//! `ptr` is a raw code address pointing into a `cranelift_jit::JITModule`'s
//! mmap'd executable pages. It is valid for as long as the `Jit` that produced
//! it is alive. The invariant is maintained at the session level, not here:
//!
//! - Sessions own `Arc<Jit>` instances (Decision 28).
//! - Jits outlive every `ModuleEntry::Def.code` that references pages they
//!   emitted.
//! - Dropping a `SymbolTable` (and its `ModuleEntry::Def.code` fields) does
//!   NOT free the JIT's pages by itself — the integration layer's
//!   `Arc<Jit>` count does.
//!
//! The field is `#[serde(skip)]` on `ModuleEntry::Def`; cache-hit loads
//! re-initialise it to `None` and codegen repopulates it on demand.

use serde::{Deserialize, Serialize};

/// Thin compiled-code handle: a raw code pointer, nothing else.
///
/// See the module-level docs for the full safety contract. In short:
/// `ptr` is valid as long as the `Jit` (held in the integration layer) that
/// emitted it is alive. Sessions manage that lifetime.
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct Code {
    /// Raw code pointer into a JIT-owned mmap'd executable page. Not
    /// serialised meaningfully — the enclosing field on `ModuleEntry::Def`
    /// is `#[serde(skip)]`, so this type never actually serialises through
    /// the cache path. The `Serialize`/`Deserialize` derives exist only so
    /// that containers holding `Code` (e.g. `Option<Code>` on
    /// `ModuleEntry::Def`) can derive the traits uniformly; the `skip`
    /// attribute on the containing field is what enforces the runtime-state
    /// discipline.
    #[serde(skip, default = "default_ptr")]
    pub ptr: *const u8,
}

fn default_ptr() -> *const u8 {
    std::ptr::null()
}

// SAFETY: `Code` holds only a raw pointer to JIT-owned, mmap'd executable
// pages. The pointer value is an integer; transmitting the integer across
// threads is safe. The backing pages are owned by `Arc<Jit>` in the
// integration layer, whose lifetime is managed by the session (Decision 28).
// Threads that read `Code.ptr` must hold a live handle (directly or
// transitively via the session) to the `Jit` that emitted the page — the
// session enforces this by keeping its `Arc<Jit>` set alive for as long as
// any `SymbolTable` holding `Code` entries is reachable.
unsafe impl Send for Code {}
unsafe impl Sync for Code {}

impl Code {
    /// Construct a `Code` handle from a raw code pointer. Caller asserts the
    /// pointer is valid for the lifetime of the enclosing session's Jit set.
    pub fn new(ptr: *const u8) -> Self {
        Code { ptr }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn code_new_roundtrips_ptr() {
        let fake = 0xDEAD_BEEFusize as *const u8;
        let code = Code::new(fake);
        assert_eq!(code.ptr, fake);
    }
}
