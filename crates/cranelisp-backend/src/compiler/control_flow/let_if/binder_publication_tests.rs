//! M2 — per-binder publication order, observed at the seam it lives at
//! (`design/backend/binding-scope.md` §3.3).
//!
//! `bind_local` publishes a binder's `Variable` and its `Type` TOGETHER, after
//! its initializer has been compiled. The pre-repair order inserted the type
//! into the name-keyed `variable_types` map BEFORE `compile_expr(val_expr)` and
//! the variable after it, so for a REPEATED name the initializer resolved its
//! *type* from binder `i` while the value map still answered with binder `i−1`'s
//! `Variable` — a split state by construction.
//!
//! **What is observed, and why it discriminates.** The consuming calling
//! convention (`apply.rs`) emits an `rc_inc` for a heap-typed bare-`Var`
//! argument, and it reads the binding's recorded TYPE to decide. So
//! `(let [s "he" s (g s)] 0)`, with `g : (Fn [String] Int)`, is a probe on
//! exactly the question "which binder's type does the initializer resolve `s`
//! to": binder 0 (`String`) ⇒ the inc is emitted; binder 1 (`Int`, the
//! half-published state) ⇒ it is not. The one-identifier rename control
//! `(let [s "he" t (g s)] 0)` cannot rebind, so it fixes the expected answer
//! without relying on the subject.
//!
//! This is a MODULE observation on purpose. `qa` established that no aggregate
//! e2e marginal can separate publication order from the frame-cleanup loss: any
//! same-name heap rebinding leaked from the cleanup defect too, so the two
//! mechanisms produce one symptom. The seam answers about the mechanism.
//!
//! The current subject, rename control, and scalar-polarity cell execute. The
//! recorded post-implementation fault plant fired, but cannot be re-executed
//! without a forbidden production seam; this is a measured positive leg that
//! is non-re-executable, not a historical RED. The scalar cell remains the
//! negative leg showing the instrument reads the resolved type.

use std::collections::HashMap;

use cranelisp_types::{
    CranelispError, Defn, DefnVariant, Expr, FQSymbol, ModuleFullPath, Span, Symbol, SymbolTable,
    Type, Visibility,
};

const PROBE: &str = "probe";
const G: &str = "g";

fn module_path() -> ModuleFullPath {
    ModuleFullPath::from("user")
}

fn var(name: &str, span: Span, ty: Type) -> Expr {
    Expr::Var {
        name: Symbol::from(name),
        span,
        resolved_call: None,
        inferred_type: Some(Box::new(ty)),
    }
}

fn int_lit(value: i64, span: Span) -> Expr {
    Expr::IntLit {
        value,
        span,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

fn string_lit(span: Span) -> Expr {
    Expr::StringLit {
        value: "he".into(),
        span,
        inferred_type: Some(Box::new(Type::String)),
    }
}

/// `(g <arg>)` — a one-argument user call whose parameter type is `param`.
fn call_g(arg: Expr, param: Type) -> Expr {
    Expr::Apply {
        callee: Box::new(var(
            G,
            Span::new(301, 302),
            Type::Fn(vec![param], Box::new(Type::Int)),
        )),
        args: vec![arg],
        span: Span::new(300, 310),
        resolved_call: None,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

/// `(let [<n0> <v0> <n1> <v1>] 0)`.
fn two_binding_let(n0: &str, v0: Expr, n1: &str, v1: Expr) -> Expr {
    Expr::Let {
        bindings: vec![(Symbol::from(n0), v0), (Symbol::from(n1), v1)],
        body: Box::new(int_lit(0, Span::new(400, 401))),
        span: Span::new(200, 410),
        inferred_type: Some(Box::new(Type::Int)),
    }
}

fn probe_defn(body: Expr) -> Defn {
    Defn {
        name: Symbol::from(PROBE),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    }
}

/// `(defn g [x] 0)` — declared, never compiled; the probe body's call resolves
/// through its `FuncId`, and its stub entry supplies the parameter type.
fn g_defn() -> Defn {
    Defn {
        name: Symbol::from(G),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None)],
            body: int_lit(0, Span::new(500, 501)),
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    }
}

/// Compile the probe body through the production per-body seam, returning its
/// CLIF. `g_param` is the declared parameter type of the callee.
fn probe_clif(body: Expr, g_param: Type) -> Result<String, CranelispError> {
    let mut jit = crate::jit::Jit::new_with_symbols(&[]).expect("JIT construction");
    let module_path = module_path();

    let symbol_tables: dashmap::DashMap<ModuleFullPath, SymbolTable> = dashmap::DashMap::new();
    let mut st = SymbolTable::new(module_path.clone());
    crate::test_support::insert_user_fn_stub_typed(&mut st, PROBE, &[], Type::Int);
    crate::test_support::insert_user_fn_stub_typed(&mut st, G, &[g_param], Type::Int);
    symbol_tables.insert(module_path.clone(), st);

    let defn = probe_defn(body);
    let callee = g_defn();
    let resolved_targets: HashMap<Span, FQSymbol> =
        crate::test_support::call_carriers(defn.body(), &module_path, &[G]);

    crate::test_support::try_compile_defns_in_module(
        &[&defn],
        &[None],
        &[&callee],
        &resolved_targets,
        &symbol_tables,
        module_path,
        jit.jit_module(),
    )
    .map(|mut clifs| clifs.remove(0))
}

/// Consuming `rc_inc`s in the emitted body: the instrument. An inc is an
/// `atomic_rmw … add`; a release is a `call` to canonical glue, so the two
/// cannot be confused.
fn consuming_incs(clif: &str) -> usize {
    clif.lines()
        .filter(|line| line.contains("atomic_rmw") && line.contains(" add "))
        .count()
}

// spec: spec/04-expressions.md §4.3 — a repeated binding's initializer sees the
// PRECEDING binding, including its type.
#[test]
fn a_repeated_binders_initializer_resolves_the_preceding_binders_type() {
    let subject = two_binding_let(
        "s",
        string_lit(Span::new(210, 214)),
        "s",
        call_g(var("s", Span::new(303, 304), Type::String), Type::String),
    );
    let control = two_binding_let(
        "s",
        string_lit(Span::new(210, 214)),
        "t",
        call_g(var("s", Span::new(303, 304), Type::String), Type::String),
    );

    let subject_incs =
        consuming_incs(&probe_clif(subject, Type::String).expect("subject compiles"));
    let control_incs =
        consuming_incs(&probe_clif(control, Type::String).expect("control compiles"));

    assert!(
        control_incs > 0,
        "the control must emit the consuming inc for a heap-typed argument, \
         or this instrument reads nothing"
    );
    assert_eq!(
        subject_incs, control_incs,
        "the initializer must resolve `s` to the preceding String binder, so the \
         consuming inc is emitted exactly as in the one-identifier rename control \
         (subject {subject_incs} incs, control {control_incs})"
    );
}

// spec: spec/04-expressions.md §4.3 (NEGATIVE polarity) — when the preceding
// binder is a scalar, no consuming inc is owed, so the instrument stays silent.
// This is what shows it reads the resolved TYPE rather than reacting to the
// repeated name itself.
#[test]
fn a_scalar_preceding_binder_owes_no_consuming_inc() {
    let subject = two_binding_let(
        "s",
        int_lit(1, Span::new(210, 214)),
        "s",
        call_g(var("s", Span::new(303, 304), Type::Int), Type::Int),
    );
    assert_eq!(
        consuming_incs(&probe_clif(subject, Type::Int).expect("subject compiles")),
        0,
        "a scalar binder is never RC-managed"
    );
}
