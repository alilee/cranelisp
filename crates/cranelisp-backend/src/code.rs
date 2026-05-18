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
//! - `Code::Jit { jit, ptr }` — fresh-build batch. `Arc<Jit>` is the
//!   retention root for the JIT-mmap'd executable pages; `ptr` is the
//!   runtime address of the per-symbol entry point. Multiple entries from
//!   the same compile batch share an `Arc<Jit>` clone (one increment per
//!   defined symbol).
//! - `Code::Linker { linker, ptr }` — cache-hit `.o`-mapped batch.
//!   `Arc<Linker>` is the retention root for the mmap'd code regions;
//!   `ptr` is the linker-resolved per-symbol address.
//!
//! # Reclaim (Decision 31 Scenario 2)
//!
//! Per-redefinition reclaim falls out of refcounting:
//! 1. REPL user redefines `(defn f [x] x)`.
//! 2. The old `ModuleEntry::Def` is replaced by `worker::register_def_in_module`;
//!    the prior `code: Some(Code::Jit { jit, ptr })` value drops.
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
//! `ptr` is a raw code address. It is valid as long as the `Arc<Jit>` /
//! `Arc<Linker>` carrying the backing pages is alive — which is enforced
//! structurally because they're co-located in the same enum variant.
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
/// intentionally minimal (variant tag + ptr value); the inner `Arc<Jit>`
/// / `Arc<Linker>` is opaque (would dump JIT internals which is noise
/// at the `:?` debug-print level).
#[non_exhaustive]
#[derive(Clone)]
pub enum Code {
    /// Fresh-build code emitted by a `compile_to_module` invocation.
    /// `jit` is the retention root for the JIT-mmap'd pages; `ptr` is the
    /// per-symbol entry point address.
    Jit {
        jit: Arc<Jit>,
        ptr: *const u8,
    },
    /// Cache-hit code loaded from a `.o` file via the in-process Linker.
    /// `linker` is the retention root for the mmap'd code regions; `ptr`
    /// is the linker-resolved per-symbol address.
    Linker {
        linker: Arc<Linker>,
        ptr: *const u8,
    },
    /// Process-static lifecycle marker for primitives (Decision 0048 A2,
    /// revised S68 Phase 3 2026-05-17). No payload — Decision 35's
    /// "GOT is the single source of truth for callable addresses; no
    /// per-entry pointer field" invariant is preserved. The marker
    /// expresses the *lifecycle category* (process-static, externally
    /// owned by the primitives crate's `PRIMITIVES_TABLE` `LazyLock`)
    /// at every `match` site over `Code`; the fn ptr continues to live
    /// in the per-module `GotTable` indexed by `ModuleEntry::Def.got_slot`.
    /// Wave 3 of S68 constructs primitives' `ModuleEntry::Def` entries
    /// with `code = Some(Code::Primitive)`.
    Primitive,
}

impl std::fmt::Debug for Code {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Code::Jit { ptr, .. } => f.debug_struct("Code::Jit").field("ptr", ptr).finish(),
            Code::Linker { ptr, .. } => f.debug_struct("Code::Linker").field("ptr", ptr).finish(),
            Code::Primitive => f.write_str("Code::Primitive"),
        }
    }
}

// SAFETY: see module-level docs. The `Arc<Jit>` / `Arc<Linker>` carriers
// are themselves `Send + Sync` (Arc requires `T: Send + Sync` to be
// `Send + Sync`); the `*const u8` pointer is an integer handle into pages
// the Arc keeps alive. `Jit` (cranelift JIT module wrapper) is not
// auto-`Sync` because of `JITModule`'s interior mutability around its
// symbol cache, but the post-finalize state we hold here is read-only:
// `Code` instances only support cloning the Arc (which is thread-safe
// refcount bumps) and reading `ptr` (no method dispatch on `Jit`).
unsafe impl Send for Code {}
unsafe impl Sync for Code {}

impl Code {
    /// Construct a fresh-build `Code::Jit` from the JIT batch's retention
    /// root and the per-symbol code pointer.
    pub fn jit(jit: Arc<Jit>, ptr: *const u8) -> Self {
        Code::Jit { jit, ptr }
    }

    /// Construct a cache-hit `Code::Linker` from the linker's retention
    /// root and the per-symbol resolved address.
    pub fn linker(linker: Arc<Linker>, ptr: *const u8) -> Self {
        Code::Linker { linker, ptr }
    }

    /// Read the per-symbol code pointer. Uniform across `Code::Jit` and
    /// `Code::Linker` — every read site that previously did `c.ptr` on
    /// the pre-Wave-3b struct now calls `c.ptr()` on the enum.
    ///
    /// For `Code::Primitive` (the process-static marker variant added by
    /// Decision 0048 §"Shape" S68 Phase 3 amendment), this returns
    /// `std::ptr::null()` — the variant carries no payload because
    /// Decision 35's "GOT is the single source of truth for callable
    /// addresses" invariant places the primitives' fn ptr in the
    /// per-module `GotTable` indexed by `ModuleEntry::Def.got_slot`,
    /// NOT inside `Code`. Callers needing the primitive's fn ptr must
    /// read the GOT slot directly via
    /// `symbol_table.got().load_slot(entry.got_slot.unwrap())`.
    pub fn ptr(&self) -> *const u8 {
        match self {
            Code::Jit { ptr, .. } | Code::Linker { ptr, .. } => *ptr,
            Code::Primitive => std::ptr::null(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // spec: design/int/symbol-table-generics.md §3 Layer 3 + Decision 31
    //       Scenario 2 reclaim primitive.
    //
    // Construct `Code::Jit { jit, ptr }`; assert `Arc::strong_count` semantics:
    // cloning bumps the count, dropping decrements, and the underlying Jit
    // drops only when the last Arc clone drops.
    #[test]
    fn code_enum_jit_variant_carries_arc_jit() {
        let jit = Arc::new(Jit::new().expect("Jit::new must succeed for test"));
        assert_eq!(Arc::strong_count(&jit), 1, "fresh Arc has refcount 1");

        let fake_ptr = 0xCAFEF00Dusize as *const u8;
        let code1 = Code::jit(Arc::clone(&jit), fake_ptr);
        assert_eq!(Arc::strong_count(&jit), 2, "Code::jit clones the Arc");
        assert_eq!(code1.ptr(), fake_ptr, "Code::ptr() returns Jit ptr");

        let code2 = code1.clone();
        assert_eq!(Arc::strong_count(&jit), 3, "Code::clone bumps refcount");

        drop(code2);
        assert_eq!(Arc::strong_count(&jit), 2, "drop decrements refcount");

        drop(code1);
        assert_eq!(
            Arc::strong_count(&jit),
            1,
            "after dropping all Code::Jit clones, only the local Arc remains"
        );

        // Now drop the local Arc; the underlying Jit::drop fires (calling
        // unsafe JITModule::free_memory).
        let pre = crate::jit::jit_free_memory_call_count();
        drop(jit);
        let post = crate::jit::jit_free_memory_call_count();
        assert_eq!(
            post,
            pre + 1,
            "dropping the last Arc<Jit> must invoke Jit::drop's free_memory call"
        );
    }

    // spec: design/int/symbol-table-generics.md §2.1 — Code enum unifies
    //       fresh-build (Jit) and cache-hit (Linker) into one shape.
    #[test]
    fn code_enum_linker_variant_constructible() {
        let linker = Arc::new(
            crate::cache::linker::Linker::new().expect("Linker::new must succeed for test"),
        );
        let fake_ptr = 0xDEADBEEFusize as *const u8;
        let code = Code::linker(Arc::clone(&linker), fake_ptr);

        assert_eq!(code.ptr(), fake_ptr, "Code::ptr() returns Linker ptr");
        assert_eq!(
            Arc::strong_count(&linker),
            2,
            "Code::linker clones the Arc"
        );

        drop(code);
        assert_eq!(
            Arc::strong_count(&linker),
            1,
            "dropping Code::Linker decrements the Arc"
        );
    }

    // spec: design/typecheck/ast-annotation.md §12 + Decision 32 —
    //       SymbolTable<Code, ()> resolves; Code implements CodeStore via
    //       the blanket impl.
    #[test]
    fn code_implements_code_store() {
        fn _requires_code_store<T: cranelisp_types::CodeStore>() {}
        _requires_code_store::<Code>();
    }

    // spec: design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md
    //       §"Shape" (S68 Phase 3 amendment, 2026-05-17 user revision) —
    //       `Code::Primitive` marker variant added; no payload (Decision 35
    //       invariant preserved); expresses process-static lifecycle category
    //       only. Construction, pattern-matching, and distinctness from
    //       `Code::Jit` / `Code::Linker` all required.
    #[test]
    fn code_primitive_marker_variant_constructible_and_distinct() {
        // 1. Construction — no payload, no constructor fn needed.
        let prim = Code::Primitive;

        // 2. Pattern-match against `Code::Primitive` succeeds for a
        //    Primitive value.
        let matched_prim = matches!(prim, Code::Primitive);
        assert!(matched_prim, "Code::Primitive must pattern-match itself");

        // 3. A `Code::Jit { .. }` value MUST NOT pattern-match `Code::Primitive`.
        let jit_val = Code::jit(
            Arc::new(Jit::new().expect("Jit::new must succeed for test")),
            0xDEADBEEFusize as *const u8,
        );
        assert!(
            !matches!(jit_val, Code::Primitive),
            "Code::Jit value must NOT pattern-match Code::Primitive"
        );
        assert!(
            matches!(jit_val, Code::Jit { .. }),
            "Code::Jit value must pattern-match Code::Jit"
        );

        // 4. A `Code::Linker { .. }` value MUST NOT pattern-match `Code::Primitive`.
        let linker_val = Code::linker(
            Arc::new(
                crate::cache::linker::Linker::new().expect("Linker::new must succeed for test"),
            ),
            0xCAFEF00Dusize as *const u8,
        );
        assert!(
            !matches!(linker_val, Code::Primitive),
            "Code::Linker value must NOT pattern-match Code::Primitive"
        );
        assert!(
            matches!(linker_val, Code::Linker { .. }),
            "Code::Linker value must pattern-match Code::Linker"
        );

        // 5. `Code::Primitive` value MUST NOT pattern-match Jit or Linker.
        assert!(
            !matches!(prim, Code::Jit { .. }),
            "Code::Primitive must NOT pattern-match Code::Jit"
        );
        assert!(
            !matches!(prim, Code::Linker { .. }),
            "Code::Primitive must NOT pattern-match Code::Linker"
        );

        // 6. `Code::Primitive::ptr()` returns null per the Decision 35
        //    invariant — the GOT is the single source of truth; the
        //    primitive's fn ptr lives in `SymbolTable.got()`, not inside
        //    `Code`. Callers needing the ptr read the GOT slot directly.
        assert!(
            prim.ptr().is_null(),
            "Code::Primitive::ptr() returns null per Decision 35 \
             (GOT is single source of truth; no per-entry pointer field)"
        );

        // 7. `Code::Primitive` Clone is no-op (no payload to refcount).
        let prim_clone = prim.clone();
        assert!(
            matches!(prim_clone, Code::Primitive),
            "Code::Primitive clones to Code::Primitive"
        );
    }
}
