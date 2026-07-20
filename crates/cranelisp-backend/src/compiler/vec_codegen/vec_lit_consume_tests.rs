//! FIXME 0668 sub-fix — the vec-lit element store consuming discrimination.
//!
//! `compile_vec_lit` stores each element through the SAME rule the call seam uses
//! (`element_consuming_inc` / DEF-2/DEF-3): a heap-typed `Var` element is an owned
//! scope binding whose scope-dec still fires, so the container takes its own count
//! (an `rc_inc` before the store) — else the binding's scope-dec frees the element
//! the returned container holds (`(let [q [7 8 9]] [q])` → garbage BOTH toggles).
//! A temporary element (literal / ctor / fn result / COW result) transfers its
//! rc=1 reference — no inc.
//!
//! These pin the EMISSION at the store seam: a heap `Var` element emits exactly one
//! `atomic_rmw.i64 add` (the element inc); a temporary element emits none. Failing-
//! first: before the sub-fix the Var case emitted zero element incs (the garbage).

use crate::jit::Jit;
use cranelisp_types::{
    Defn, DefnVariant, Expr, ModuleFullPath, Span, Symbol, Type, TypeName, Visibility,
};

fn vec_int() -> Type {
    Type::adt(ModuleFullPath::from("primitives"), TypeName::from("Vec"), vec![Type::Int])
}

/// Probe a single-`Var`-param defn whose body is the given `VecLit` `Expr`, and
/// return its emitted CLIF text (through the production per-body seam).
fn clif_of_veclit_body(body: Expr) -> String {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let name = Symbol::from("veclit_probe");
    let defn = Defn {
        name: name.clone(),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("v"), None)],
            body,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };
    let symbol_tables: dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable> =
        dashmap::DashMap::new();
    let module_path = ModuleFullPath::from("user");
    let mut st = cranelisp_types::SymbolTable::new(module_path.clone());
    crate::test_support::insert_user_fn_stub(&mut st, "veclit_probe", 1);
    symbol_tables.insert(module_path.clone(), st);
    let resolved_targets = crate::test_support::call_carriers(defn.body(), &module_path, &[]);
    crate::test_support::probe_defn_clif(
        &defn,
        &[],
        &resolved_targets,
        &symbol_tables,
        module_path,
        jit.jit_module(),
    )
}

/// `atomic_rmw.i64 add` occurrences — for a body that is a single vec-lit store
/// (no other RC traffic), the ONLY such op is the element consuming inc.
fn rc_inc_count(clif: &str) -> usize {
    clif.matches("atomic_rmw.i64 add").count()
}

fn var(name: &str, ty: Type) -> Expr {
    Expr::Var { name: Symbol::from(name), span: Span::SYNTHETIC, resolved_call: None, inferred_type: Some(Box::new(ty)) }
}
fn int_lit(n: i64) -> Expr {
    Expr::IntLit { value: n, span: Span::SYNTHETIC, inferred_type: Some(Box::new(Type::Int)) }
}
fn veclit(elements: Vec<Expr>, ty: Type) -> Expr {
    Expr::VecLit { elements, span: Span::SYNTHETIC, inferred_type: Some(Box::new(ty)) }
}

// spec: design/backend/ownership-codegen.md §13.5 / FIXME 0668 — a heap-typed
// `Var` element is an owned scope binding: the vec-lit store MUST take its count
// (one element inc) so the returned container's element survives the binding's
// scope-dec. Failing-first: zero element incs before the sub-fix (the garbage).
#[test]
fn veclit_heap_var_element_takes_its_count() {
    // (defn f [v] [v])  — v : Vec<Int> (AlwaysHeap), element is an owned Var.
    let body = veclit(vec![var("v", vec_int())], Type::adt(
        ModuleFullPath::from("primitives"), TypeName::from("Vec"), vec![vec_int()],
    ));
    let clif = clif_of_veclit_body(body);
    assert_eq!(
        rc_inc_count(&clif),
        1,
        "a heap `Var` vec-lit element MUST take exactly one consuming inc (its \
         count) at the store — else the binding's scope-dec frees the element the \
         container holds (§0668). CLIF:\n{clif}"
    );
}

// spec: FIXME 0668 — NEGATIVE: a temporary element (a nested `VecLit` literal)
// starts at rc=1 and transfers its single reference into the container — NO inc
// (a spurious inc would leak the temp). Leak-side-safe: only owned bindings inc.
#[test]
fn veclit_temporary_element_transfers_no_inc_neg() {
    // (defn f [v] [[1 2 3]])  — the element is a fresh literal (temp).
    let inner = veclit(vec![int_lit(1), int_lit(2), int_lit(3)], vec_int());
    let body = veclit(vec![inner], Type::adt(
        ModuleFullPath::from("primitives"), TypeName::from("Vec"), vec![vec_int()],
    ));
    let clif = clif_of_veclit_body(body);
    assert_eq!(
        rc_inc_count(&clif),
        0,
        "a temporary (literal) vec-lit element transfers its rc=1 reference — the \
         store MUST emit NO consuming inc (an inc would leak the temp). CLIF:\n{clif}"
    );
}

// spec: FIXME 0668 — NEGATIVE: a NeverHeap (Int) `Var` element carries no RC, so
// the discrimination emits no inc even for a Var (the category gate).
#[test]
fn veclit_int_var_element_no_inc_neg() {
    // (defn f [v] [v])  — but v : Int (NeverHeap) ⇒ no inc.
    let body = veclit(vec![var("v", Type::Int)], vec_int());
    let clif = clif_of_veclit_body(body);
    assert_eq!(
        rc_inc_count(&clif),
        0,
        "a NeverHeap (Int) `Var` element carries no RC — no consuming inc. \
         CLIF:\n{clif}"
    );
}
