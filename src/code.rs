//! Integration-layer aliases for `cranelisp_backend::Code`.
//!
//! Per Decision 41 + `design/arch/facades/backend.md` (S67 close-out): the
//! `Code` enum lives in `cranelisp-backend` — the variants reference
//! backend-owned `Arc<Jit>` / `Arc<Linker>` so the type belongs in the
//! same crate as those primitives. This module re-exports `Code` for
//! existing `crate::code::Code` consumers in `src/` and provides the
//! integration-layer `SessionSymbolTable` / `SessionModuleEntry` type
//! aliases that pin the symbol-table generics (`C = Code, L = ()`) per
//! Decision 32 + Decision 35.

pub use cranelisp_backend::Code;

/// Strongly typed alias for the integration layer's `SymbolTable`
/// instantiation. Per Decision 35: `C = Code`, `L = ()` (per-symbol
/// `Code::Linker.linker: Arc<Linker>` retention covers every Linker
/// retention scenario; the parallel `linker: Option<L>` field on the
/// `SymbolTable` itself is reserved for future expansion).
pub type SessionSymbolTable = cranelisp_types::SymbolTable<Code, ()>;

/// Strongly typed alias for the integration layer's `ModuleEntry`
/// instantiation. `C = Code` (matches `SessionSymbolTable`).
///
/// No production callers — `ModuleEntry<Code>` is spelled inline where used;
/// referenced only by this module's unit tests. Retained as the canonical
/// alias name, so `#[allow(dead_code)]` (dead in a non-test build).
#[allow(dead_code)]
pub(crate) type SessionModuleEntry = cranelisp_types::ModuleEntry<Code>;

#[cfg(test)]
mod tests {
    use super::*;

    // spec: design/int/symbol-table-generics.md §6 (mixed-lineage modules)
    //       — A SessionSymbolTable can carry both Code::Jit and Code::Linker
    //       entries simultaneously; serde skips both uniformly (the field is
    //       `#[serde(skip)]`).
    #[test]
    fn code_enum_jit_and_linker_coexist_serde_skip() {
        use cranelisp_backend::cache::linker::Linker;
        use cranelisp_backend::jit::Jit;
        use cranelisp_types::{
            DefKind, DefnVariant, Expr, ModuleEntry, ModuleFullPath, Scheme, Span,
            Symbol, Type, Visibility,
        };
        use std::collections::HashMap;
        use std::sync::Arc;

        /// S69 Submission 35: `ModuleEntry::Def.ast` is `DefnVariant`.
        fn trivial_variant() -> DefnVariant {
            DefnVariant {
                params: vec![],
                body: Expr::IntLit {
                    value: 0,
                    span: Span::SYNTHETIC,
                    inferred_type: Some(Box::new(Type::Int)),
                },
                span: Span::SYNTHETIC,
            }
        }

        fn mk_def(code: Option<Code>, _name: &str) -> SessionModuleEntry {
            // Struct literal (not the builder) because this test sets `code`
            // explicitly, which the builder deliberately does not expose.
            ModuleEntry::Def {
                scheme: Scheme {
                    type_vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Int,
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::UserFn {
                    fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None },
                }),
                callees: Vec::new(),
                trait_origin: None,
                seq: 0,
                ast: Some(trivial_variant()),
                codegen_view: None,
                code,
                value_use: false,
            }
        }

        let empty_tables: cranelisp_types::SymbolTables<Code, ()> = dashmap::DashMap::new();
        let jit = Arc::new(Jit::new(&empty_tables).expect("Jit::new must succeed"));
        let linker = Arc::new(Linker::new().expect("Linker::new must succeed"));

        let mut st: SessionSymbolTable =
            cranelisp_types::SymbolTable::<Code, ()>::new_with_params(
                ModuleFullPath::from("user"),
            );
        st.insert(
            Symbol::from("fresh"),
            mk_def(Some(Code::jit(Arc::clone(&jit))), "fresh"),
        );
        st.insert(
            Symbol::from("cached"),
            mk_def(Some(Code::linker(Arc::clone(&linker))), "cached"),
        );

        // Both variants coexist in the same table (S75 slim: lifecycle owner
        // only; callable address lives in the GOT, not on `Code`).
        match st.get("fresh") {
            Some(ModuleEntry::Def { code: Some(Code::Jit(_)), .. }) => {}
            other => panic!("expected Code::Jit, got {:?}", other),
        }
        match st.get("cached") {
            Some(ModuleEntry::Def { code: Some(Code::Linker(_)), .. }) => {}
            other => panic!("expected Code::Linker, got {:?}", other),
        }
    }

    // spec: design/int/symbol-table-generics.md §2.3 — `SharedState.kept_jits`
    //       and `SharedState.kept_linkers` dissolved (Wave 3b regression guard).
    //
    // This is a textual regression guard: read the live source for SharedState
    // and confirm the fields are gone.
    #[test]
    fn kept_jits_and_kept_linkers_fields_dissolved() {
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
