//! S97 — the inline Vec-op temporary release MUST be **rc-checked**, not an
//! unconditional `vec_drop`.
//!
//! Pins the seam where the nested-ADT-wrapping-Vec double-use heap-corruption
//! lived (`design/backend/ring2-rc.md §5.5`; `tests/regression.rs::
//! nested_adt_wrapping_vec_looped_double_use_corrupts_heap_neg`). After an
//! inline `vec-get` / `vec-len` consumes a **temporary** Vec expression (one
//! that is not a named `Var`), `emit_vec_drop_if_temporary` releases the
//! temporary's reference. A temporary is NOT always the sole owner: when it is
//! a borrowed ADT field — `(vec-get (gcells g) 0)` where `gcells` returns the
//! inner Vec still owned by the live Grid `g` — the Vec's rc is > 1, and the
//! old UNCONDITIONAL `vec_drop` freed the data buffer + struct out from under
//! the still-reachable Grid → use-after-free on the next write.
//!
//! The fix routes the release through `emit_vec_rc_dec_with_drop`: an atomic
//! rc dec, then `vec_drop` ONLY on the last reference (old_rc == 1). This test
//! pins that the emitted CLIF for a temporary-vec `vec-get` contains the
//! rc-check (an `atomic_rmw.i64 sub` guarding a `brif`), i.e. the release is
//! rc-aware. Before the fix the CLIF released the temporary with a bare
//! `call` to `vec_drop` and no preceding atomic dec on that pointer.

use crate::jit::Jit;
use cranelisp_types::{Defn, DefnVariant, Expr, Span, Symbol, Type, Visibility};
use std::collections::HashMap;

/// Compile a zero-arg `defn` whose body is `body`, returning the emitted CLIF.
fn clif_of_body(body: Expr) -> String {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    jit.declare_intrinsics().expect("intrinsics declare");

    let name = Symbol::from("temp_drop_probe");
    let defn = Defn {
        name: name.clone(),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };

    let func_ids = jit.declare_functions(&[&defn]).expect("declare");
    let func_arities: HashMap<Symbol, usize> = HashMap::new();
    let symbol_tables: dashmap::DashMap<
        cranelisp_types::ModuleFullPath,
        cranelisp_types::SymbolTable,
    > = dashmap::DashMap::new();
    let module_path = cranelisp_types::ModuleFullPath::from("user");
    symbol_tables.insert(
        module_path.clone(),
        cranelisp_types::SymbolTable::new(module_path.clone()),
    );
    let module_aliases: cranelisp_types::ModuleAliases = dashmap::DashMap::new();
    let compile_ctx = jit.build_compile_context(
        &func_ids,
        &func_arities,
        &symbol_tables,
        &module_aliases,
        module_path,
    );
    jit.compile_defn(&defn, compile_ctx)
        .expect("compile")
        .clif_ir
}

fn int_lit(v: i64) -> Expr {
    Expr::IntLit {
        value: v,
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

fn vec_ty() -> Type {
    let fqtn = cranelisp_types::FQTypeName::new(
        cranelisp_types::ModuleFullPath::from("primitives"),
        cranelisp_types::TypeName::from("Vec"),
    );
    Type::ADT(fqtn, vec![Type::Int])
}

/// A temporary `(Vec Int)` expression: a vec literal `[10 20 30]`. Not a `Var`,
/// so `emit_vec_drop_if_temporary` fires after the inline `vec-get`.
fn temp_vec() -> Expr {
    Expr::VecLit {
        elements: vec![int_lit(10), int_lit(20), int_lit(30)],
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(vec_ty())),
    }
}

/// `(vec-get <temp-vec> 0)` — resolved to the `vec-get` builtin so codegen
/// reaches `compile_vec_op` and, since arg0 is a temporary, the
/// `emit_vec_drop_if_temporary` release path.
fn vec_get_of_temp() -> Expr {
    Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-get"),
            span: Span::SYNTHETIC,
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![temp_vec(), int_lit(0)],
        span: Span::SYNTHETIC,
        resolved_call: Some(Box::new(cranelisp_types::ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-get"),
        })),
        inferred_type: Some(Box::new(Type::Int)),
    }
}

// spec: design/backend/ring2-rc.md §5.5 — the inline Vec-op temporary release
// must be rc-CHECKED. A temporary Vec consumed by `vec-get` may be a shared
// borrowed ADT field (rc > 1); releasing it unconditionally frees it while
// still reachable. The release must atomically dec the rc and free only on the
// last reference.
#[test]
fn vec_get_temporary_release_is_rc_checked_not_unconditional_drop() {
    let clif = clif_of_body(vec_get_of_temp());

    // The temporary release must dec the rc atomically before any free. With a
    // vec literal of Int (NeverHeap) elements + an Int vec-get result, the ONLY
    // RC traffic in this function is the temporary-vec release — so an
    // `atomic_rmw.i64 sub` is present iff the release is rc-checked. The old
    // unconditional `vec_drop` emitted no such dec (a bare `call`).
    assert!(
        clif.contains("atomic_rmw.i64 sub"),
        "the inline vec-get temporary release MUST be rc-checked (atomic rc dec \
         before free) — an unconditional vec_drop frees a shared borrowed-field \
         Vec while still reachable (the S97 heap-corruption seam, ring2-rc.md \
         §5.5). CLIF:\n{clif}"
    );

    // And the free must be guarded by a conditional branch (free only on the
    // last reference), not a straight-line call.
    assert!(
        clif.contains("brif"),
        "the temporary release's free must be guarded by a last-reference \
         branch (brif), not an unconditional call. CLIF:\n{clif}"
    );
}
