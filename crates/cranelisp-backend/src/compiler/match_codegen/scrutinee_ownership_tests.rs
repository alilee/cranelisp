//! S115 W4c / FIXME 0781 — the match seam's scrutinee-ownership gate is the
//! value's PROVENANCE, not the node kind.
//!
//! `compile_var_pattern_arm`'s `is_alias` and `dec_temporary_scrutinee`'s
//! `is_temp` are the same question asked with opposite polarity: does THIS
//! frame own the scrutinee's value? Both used to answer
//! `matches!(scrutinee, MonoExpr::Var { .. })`, so an `If`/`Match`/`Let` that
//! merely YIELDS a borrowed param was registered for scope cleanup AND dec'd
//! as a temporary — two releases of a box the caller already owns.
//!
//! Measured before the fix, `PrimitivesOnly`, `--link`:
//! `(defn f [v b] (match (if b v v) [xs (vec-get xs 0)]))` → exit 134
//! "corrupted double-linked list"; the `let`-yielding-a-binding twin
//! `(match (let [w v] w) …)` and the ADT-pattern twin
//! `(match (if b t t) [(Wrap xs) …])` abort identically. All three exit 9
//! (clean) after routing both gates through
//! `fn_compiler::yields_owned_temporary`.
//!
//! DETECTION PROOF: restoring either `matches!(.., MonoExpr::Var { .. })` test
//! flips `if_joined_borrowed_param_scrutinee_is_not_released_neg` RED (the dec
//! count rises from 1); the control below stays GREEN in both states, so the
//! pair discriminates "the gate narrowed correctly" from "the release was
//! deleted".

use crate::jit::Jit;
use cranelisp_types::{Defn, DefnVariant, Expr, MatchArm, Pattern, Span, Symbol, Type, Visibility};
use std::collections::HashMap;

/// Compile `(defn probe <params> <body>)` and return the emitted CLIF.
fn clif_of(body: Expr, params: Vec<(Symbol, Option<cranelisp_types::TypeExpr>)>) -> String {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let defn = Defn {
        name: Symbol::from("scrutinee_ownership_probe"),
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

fn vec_ty() -> Type {
    Type::ADT(
        cranelisp_types::FQTypeName::new(
            cranelisp_types::ModuleFullPath::from("primitives"),
            cranelisp_types::TypeName::from("Vec"),
        ),
        vec![Type::Int],
    )
}

fn int_lit(v: i64) -> Expr {
    Expr::IntLit {
        value: v,
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

fn var(name: &str, ty: Type) -> Expr {
    Expr::Var {
        name: Symbol::from(name),
        span: Span::SYNTHETIC,
        resolved_call: None,
        inferred_type: Some(Box::new(ty)),
    }
}

fn vec_lit() -> Expr {
    Expr::VecLit {
        elements: vec![int_lit(7), int_lit(8), int_lit(9)],
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(vec_ty())),
    }
}

/// `(vec-get <container> 0)`.
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

/// `(match <scrutinee> [xs (vec-get xs 0)])` — a var-pattern arm whose body
/// does NOT forward the scrutinee, so the consume path runs.
fn match_reading_scrutinee(scrutinee: Expr) -> Expr {
    Expr::Match {
        scrutinee: Box::new(scrutinee),
        arms: vec![MatchArm {
            pattern: Pattern::Var {
                name: Symbol::from("xs"),
                span: Span::SYNTHETIC,
            },
            body: vec_get_of(var("xs", vec_ty())),
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
        compiler_generated: false,
    }
}

/// `(if b v v)` over a borrowed `(Vec Int)` param.
fn if_joined_param() -> Expr {
    Expr::If {
        cond: Box::new(var("b", Type::Bool)),
        then_branch: Box::new(var("v", vec_ty())),
        else_branch: Box::new(var("v", vec_ty())),
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(vec_ty())),
    }
}

// spec: spec/12-runtime.md §12.1 / FIXME 0781 — a match scrutinee that merely
// YIELDS a borrowed binding is not this frame's to release. With Int elements
// and an Int result the only legitimate rc dec in this body is the Decision-24
// scope-exit release of the owned `v` param; the defect added the scrutinee
// temp-dec and the pattern-alias cleanup dec on top of it.
// MEASURED: `--link` exit 134 before, exit 9 after.
#[test]
fn if_joined_borrowed_param_scrutinee_is_not_released_neg() {
    let clif = clif_of(
        match_reading_scrutinee(if_joined_param()),
        vec![(Symbol::from("v"), None), (Symbol::from("b"), None)],
    );
    let decs = clif.matches("atomic_rmw.i64 sub").count();
    assert_eq!(
        decs, 1,
        "an `If` joining two BORROWED arms yields the caller's vector: neither \
         the scrutinee temp-dec nor the pattern-alias scope cleanup may claim \
         it (FIXME 0781, `--link` exit 134). Expected exactly the one \
         scope-exit dec, found {decs}. CLIF:\n{clif}"
    );
}

// spec: spec/12-runtime.md §12.1 / FIXME 0781 — the DISCRIMINATING CONTROL
// (METHOD §2.2 "only a control confirms a mechanism"): the same match over a
// FRESH vec literal IS this frame's temporary, and its release must survive the
// narrowing. Without this cell the negative above would also pass if the
// release had simply been deleted.
//
// (This shape has a separate, PRE-EXISTING over-release — the var-pattern arm
// registers the alias for scope cleanup while the merge-block consume also
// decs — measured at HEAD and unchanged by this change-set; see FIXME 0782.
// The assertion here is deliberately "at least one release", so it pins the
// narrowing without freezing that unrelated count.)
#[test]
fn fresh_vec_literal_scrutinee_still_releases() {
    let clif = clif_of(match_reading_scrutinee(vec_lit()), vec![]);
    assert!(
        clif.contains("atomic_rmw.i64 sub"),
        "a FRESH vec-literal scrutinee is an owned temporary — its release must \
         still be emitted, or the 0781 narrowing has become a leak. CLIF:\n{clif}"
    );
}

// spec: spec/12-runtime.md §12.1 / FIXME 0781 — a bare `Var` scrutinee is
// unchanged by the narrowing (the shape test and the provenance answer agree
// on every `Var`), so this cell is the byte-level no-regression fence for the
// overwhelmingly common shape.
#[test]
fn bare_var_scrutinee_is_unchanged_by_the_narrowing() {
    let clif = clif_of(
        match_reading_scrutinee(var("v", vec_ty())),
        vec![(Symbol::from("v"), None)],
    );
    let decs = clif.matches("atomic_rmw.i64 sub").count();
    assert_eq!(
        decs, 1,
        "a bare `Var` scrutinee is dec'd by its owning scope exactly once — the \
         provenance gate must agree with the old shape test here. Found {decs}. \
         CLIF:\n{clif}"
    );
}
