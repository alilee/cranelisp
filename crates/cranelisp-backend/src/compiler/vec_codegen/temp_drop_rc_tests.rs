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
    clif_of_body_with_params(body, vec![])
}

/// Compile a `defn` with the given params whose body is `body`, returning the
/// emitted CLIF.
fn clif_of_body_with_params(
    body: Expr,
    params: Vec<(Symbol, Option<cranelisp_types::TypeExpr>)>,
) -> String {
    // S111 R4 §1.3: probe rides the production per-body seam.
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");

    let name = Symbol::from("temp_drop_probe");
    let defn = Defn {
        name: name.clone(),
        docstring: None,
        variants: vec![DefnVariant {
            params,
            body,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };

    let symbol_tables: dashmap::DashMap<
        cranelisp_types::ModuleFullPath,
        cranelisp_types::SymbolTable,
    > = dashmap::DashMap::new();
    let module_path = cranelisp_types::ModuleFullPath::from("user");
    symbol_tables.insert(
        module_path.clone(),
        cranelisp_types::SymbolTable::new(module_path.clone()),
    );
    let no_targets: HashMap<Span, cranelisp_types::FQSymbol> = HashMap::new();
    crate::test_support::probe_defn_clif(
        &defn,
        &[],
        &no_targets,
        &symbol_tables,
        module_path,
        jit.jit_module(),
    )
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

// =============================================================================
// S115 W4c / FIXME 0781 — the NEGATIVE face: an `If` that merely YIELDS a
// borrowed param is not a temporary and MUST NOT be released.
// =============================================================================

/// A `(Vec Int)` param reference — a scope binding whose owner is the caller.
fn vec_param(name: &str) -> Expr {
    Expr::Var {
        name: Symbol::from(name),
        span: Span::SYNTHETIC,
        resolved_call: None,
        inferred_type: Some(Box::new(vec_ty())),
    }
}

/// `(if b v v)` — a control-flow join over the SAME borrowed param in both
/// arms. Not a `Var`, but its value is the caller's vector.
fn if_joined_param() -> Expr {
    Expr::If {
        cond: Box::new(Expr::Var {
            name: Symbol::from("b"),
            span: Span::SYNTHETIC,
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Bool)),
        }),
        then_branch: Box::new(vec_param("v")),
        else_branch: Box::new(vec_param("v")),
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(vec_ty())),
    }
}

/// `(vec-get <container> 0)`, resolved to the `vec-get` builtin.
fn vec_get_of(container: Expr) -> Expr {
    Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-get"),
            span: Span::SYNTHETIC,
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![container, int_lit(0)],
        span: Span::SYNTHETIC,
        resolved_call: Some(Box::new(cranelisp_types::ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-get"),
        })),
        inferred_type: Some(Box::new(Type::Int)),
    }
}

/// `[v b]` — the param list of the 0781 repro `(defn f [v b] …)`.
fn v_b_params() -> Vec<(Symbol, Option<cranelisp_types::TypeExpr>)> {
    vec![(Symbol::from("v"), None), (Symbol::from("b"), None)]
}

// spec: spec/12-runtime.md §12.1 / FIXME 0781 — an inline `vec-get` whose
// container merely YIELDS a borrowed binding must emit NO release. The release
// gate used to be the syntactic node-kind test
// `matches!(vec_expr, MonoExpr::Var { .. })`, so an `If` joining two borrowed
// arms fell through to the rc-checked dec and freed a vector the caller still
// owns: `(defn f [v b] (vec-get (if b v v) 0))` aborted with exit 134
// ("corrupted double-linked list") under `--link`. The gate now reads the
// derived provenance (`fn_compiler::yields_owned_temporary`).
//
// DETECTION PROOF (the standing instrument's measurement): restoring the
// `matches!(vec_expr, MonoExpr::Var { .. })` early-return flips this test RED
// (the `atomic_rmw.i64 sub` release reappears) while the positive twin above
// stays GREEN — the pair brackets the gate from both sides.
#[test]
fn if_joined_borrowed_param_emits_no_temporary_release_neg() {
    let clif = clif_of_body_with_params(vec_get_of(if_joined_param()), v_b_params());

    // With Int elements and an Int `vec-get` result, the ONLY rc decs this body
    // can emit are (a) the Decision-24 scope-exit release of the owned `v`
    // param and (b) — the defect — a second release of the SAME box through the
    // `If` join. Exactly ONE is correct; TWO is the double-dec that aborts.
    // MEASURED: 2 with the `matches!(.., MonoExpr::Var { .. })` gate restored,
    // 1 with the provenance gate.
    let decs = clif.matches("atomic_rmw.i64 sub").count();
    assert_eq!(
        decs, 1,
        "an `If` joining two BORROWED arms yields the caller's vector, not a \
         temporary: releasing it decs a box the enclosing scope already \
         releases (FIXME 0781, `--link` exit 134 'corrupted double-linked \
         list'). Expected exactly the one scope-exit dec, found {decs}. \
         CLIF:\n{clif}"
    );
}

// spec: spec/12-runtime.md §12.1 / FIXME 0781 (the POSITIVE control for the
// cell above) — the same `If` join over two FRESH vec literals IS this frame's
// temporary and MUST still be released. Without this control the negative cell
// above would also pass if the release were deleted outright.
#[test]
fn if_joined_fresh_vec_literals_still_release_the_temporary() {
    let if_fresh = Expr::If {
        cond: Box::new(Expr::Var {
            name: Symbol::from("b"),
            span: Span::SYNTHETIC,
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Bool)),
        }),
        then_branch: Box::new(temp_vec()),
        else_branch: Box::new(temp_vec()),
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(vec_ty())),
    };
    let clif = clif_of_body_with_params(
        vec_get_of(if_fresh),
        vec![(Symbol::from("b"), None)],
    );

    assert!(
        clif.contains("atomic_rmw.i64 sub"),
        "an `If` joining two FRESH vec literals yields an owned temporary — \
         the release must still fire, or the fix has narrowed into a leak. \
         CLIF:\n{clif}"
    );
}
