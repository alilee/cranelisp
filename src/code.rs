//! Per-function compiled-code handle for the integration layer (Decision 35).
//!
//! Replaces the pre-Wave-3b `cranelisp_types::Code` pointer-only struct. The
//! enum unifies fresh-build (JIT-backed) and cache-hit (Linker-backed) code
//! into one shape so `SymbolTable<Code, ()>` carries either provenance
//! through the same field.
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
//! Pre-Wave-3b, `Arc<Jit>` lived in `SharedState.kept_jits` (a side
//! retention pool); reclaim only fired at session teardown. Wave 3b
//! dissolves `kept_jits` and `kept_linkers` — the per-entry `Arc` IS the
//! retention root.
//!
//! # Safety
//!
//! `ptr` is a raw code address. It is valid as long as the `Arc<Jit>` /
//! `Arc<Linker>` carrying the backing pages is alive — which is enforced
//! structurally because they're co-located in the same enum variant.
//! Unlike the pre-Wave-3b shape (where the lifetime invariant was
//! "session keeps `kept_jits` alive while entries reference its pages"),
//! here it is "the `Arc` and the `ptr` drop together, atomically".
//!
//! The `unsafe impl Send + Sync` is needed because `cranelift_jit::JITModule`
//! contains non-`Sync` interior mutability (symbol cache); after
//! `compile_to_module` finalises the JIT, the pages are stable and the
//! `Jit` is effectively read-only from external observers. Workers only
//! clone the `Arc` and read `ptr`; they do not call mutating methods on
//! the contained `Jit` after construction. This mirrors the pre-Wave-3b
//! `unsafe Send + Sync` impls on `KeptJit`.

use std::sync::Arc;

use cranelisp_backend::cache::Linker;
use cranelisp_backend::jit::Jit;

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
}

impl std::fmt::Debug for Code {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Code::Jit { ptr, .. } => f.debug_struct("Code::Jit").field("ptr", ptr).finish(),
            Code::Linker { ptr, .. } => f.debug_struct("Code::Linker").field("ptr", ptr).finish(),
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
    pub fn ptr(&self) -> *const u8 {
        match self {
            Code::Jit { ptr, .. } | Code::Linker { ptr, .. } => *ptr,
        }
    }
}

/// Strongly typed alias for the integration layer's `SymbolTable`
/// instantiation. Per Decision 35: `C = Code`, `L = ()` (per-symbol
/// `Code::Linker.linker: Arc<Linker>` retention covers every Linker
/// retention scenario; the parallel `linker: Option<L>` field on the
/// `SymbolTable` itself is reserved for future expansion).
pub type SessionSymbolTable = cranelisp_types::SymbolTable<Code, ()>;

/// Strongly typed alias for the integration layer's `ModuleEntry`
/// instantiation. `C = Code` (matches `SessionSymbolTable`).
pub type SessionModuleEntry = cranelisp_types::ModuleEntry<Code>;

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_backend::jit::Jit;
    use std::sync::Arc;

    // spec: design/int/symbol-table-generics.md §3 Layer 3 + Decision 31
    //       Scenario 2 reclaim primitive.
    //
    // Construct `Code::Jit { jit, ptr }`; assert `Arc::strong_count` semantics:
    // cloning bumps the count, dropping decrements, and the underlying Jit
    // drops only when the last Arc clone drops (i.e., the per-redefinition
    // reclaim primitive holds).
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
        // unsafe JITModule::free_memory). We can't observe the free_memory
        // call directly here, but JIT_FREE_MEMORY_CALL_COUNT in jit.rs
        // tracks it for cross-test instrumentation.
        let pre = cranelisp_backend::jit::jit_free_memory_call_count();
        drop(jit);
        let post = cranelisp_backend::jit::jit_free_memory_call_count();
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
            cranelisp_backend::cache::Linker::new()
                .expect("Linker::new must succeed for test"),
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
    //       SessionSymbolTable resolves to SymbolTable<Code, ()>; both Code
    //       variants implement CodeStore via the blanket impl.
    #[test]
    fn session_symbol_table_concrete_type_choice() {
        // Compile-time assertion via a require_*_store helper.
        fn _requires_code_store<T: cranelisp_types::CodeStore>() {}
        _requires_code_store::<Code>();

        // SessionSymbolTable resolves to SymbolTable<Code, ()>.
        let st: SessionSymbolTable =
            cranelisp_types::SymbolTable::<Code, ()>::new_with_params(
                cranelisp_types::ModuleFullPath::from("user"),
            );
        // Sanity: empty entries on fresh construction.
        assert!(st.symbols.is_empty());
        assert!(st.linker.is_none());
    }

    // spec: design/int/symbol-table-generics.md §6 (mixed-lineage modules)
    //       — A SessionSymbolTable can carry both Code::Jit and Code::Linker
    //       entries simultaneously; serde skips both uniformly (the field is
    //       `#[serde(skip)]`).
    #[test]
    fn code_enum_jit_and_linker_coexist_serde_skip() {
        use cranelisp_types::{
            DefKind, Defn, DefnVariant, Expr, ModuleEntry, ModuleFullPath, Scheme, Span,
            Symbol, Type, Visibility,
        };
        use std::collections::HashMap;

        fn trivial_defn(name: &str) -> Defn {
            Defn {
                name: Symbol::from(name),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![],
                    param_annotations: vec![],
                    body: Expr::IntLit {
                        value: 0,
                        span: Span::SYNTHETIC,
                        inferred_type: Some(Box::new(Type::Int)),
                    },
                    span: Span::SYNTHETIC,
                }],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            }
        }

        fn mk_def(code: Option<Code>, name: &str) -> SessionModuleEntry {
            ModuleEntry::Def {
                scheme: Scheme {
                    vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Int,
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                callees: Vec::new(),
                got_slot: None,
                trait_origin: None,
                ast: Some(trivial_defn(name)),
                code,
                platform_fn_ptr: None,
            }
        }

        let jit = Arc::new(Jit::new().expect("Jit::new must succeed"));
        let linker = Arc::new(
            cranelisp_backend::cache::Linker::new().expect("Linker::new must succeed"),
        );

        let mut st: SessionSymbolTable = cranelisp_types::SymbolTable::<Code, ()>::new_with_params(
            ModuleFullPath::from("user"),
        );
        st.insert(
            Symbol::from("fresh"),
            mk_def(
                Some(Code::jit(Arc::clone(&jit), 0xAAAAusize as *const u8)),
                "fresh",
            ),
        );
        st.insert(
            Symbol::from("cached"),
            mk_def(
                Some(Code::linker(
                    Arc::clone(&linker),
                    0xBBBBusize as *const u8,
                )),
                "cached",
            ),
        );

        // Both variants coexist in the same table.
        match st.get("fresh") {
            Some(ModuleEntry::Def { code: Some(Code::Jit { ptr, .. }), .. }) => {
                assert_eq!(*ptr, 0xAAAAusize as *const u8);
            }
            other => panic!("expected Code::Jit, got {:?}", other),
        }
        match st.get("cached") {
            Some(ModuleEntry::Def { code: Some(Code::Linker { ptr, .. }), .. }) => {
                assert_eq!(*ptr, 0xBBBBusize as *const u8);
            }
            other => panic!("expected Code::Linker, got {:?}", other),
        }

        // Serde-skip semantics are covered by the cranelisp-types-side
        // tests (`module.rs::tests::module_entry_def_code_field_is_optional_c`
        // exercises `<i64>`, `code_serialise_round_trip_skips_field`
        // exercises `<()>`); replicating here would require adding
        // `serde_json` to cranelisp's dev-deps for one assertion. Coexistence
        // of the two enum variants in one table is what this test
        // exclusively asserts; the structural serde discipline is already
        // covered downstream.
    }

    // spec: design/int/symbol-table-generics.md §2.3 — `SharedState.kept_jits`
    //       and `SharedState.kept_linkers` dissolved (Wave 3b regression guard).
    //
    // This is a compile-time + textual regression guard: the test references
    // SharedState's field set by name; removed fields would surface elsewhere
    // (the SharedState constructor sites in session_v4.rs and scheduler.rs
    // tests). For the textual half, see the integration test below.
    #[test]
    fn kept_jits_and_kept_linkers_fields_dissolved() {
        // Read the live source for SharedState and confirm the fields
        // are gone. Strip comments to avoid matching documentation that
        // describes the historical state.
        let src = include_str!("session_v4.rs");
        let mut in_block_comment = false;
        let stripped: String = src
            .lines()
            .map(|line| {
                let mut out = String::new();
                let mut chars = line.chars().peekable();
                while let Some(c) = chars.next() {
                    if in_block_comment {
                        if c == '*' && chars.peek() == Some(&'/') {
                            chars.next();
                            in_block_comment = false;
                        }
                        continue;
                    }
                    if c == '/' && chars.peek() == Some(&'/') {
                        // line comment — drop the rest
                        break;
                    }
                    if c == '/' && chars.peek() == Some(&'*') {
                        chars.next();
                        in_block_comment = true;
                        continue;
                    }
                    out.push(c);
                }
                out
            })
            .collect::<Vec<_>>()
            .join("\n");

        assert!(
            !stripped.contains("kept_jits"),
            "SharedState.kept_jits must be dissolved (Wave 3b); found non-comment reference"
        );
        assert!(
            !stripped.contains("kept_linkers"),
            "SharedState.kept_linkers must be dissolved (Wave 3b); found non-comment reference"
        );
        // Counter-regression: kept_dlls survives — platform DLLs are
        // session-scoped and orthogonal to Step 5c.
        assert!(
            stripped.contains("kept_dlls"),
            "SharedState.kept_dlls must survive (platform DLLs are session-scoped, not Step 5c scope)"
        );
    }
}
