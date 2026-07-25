//! Shared `#[cfg(test)]` fixtures for the per-submodule `program/` test files
//! (S115 W4, FIXME 0722 — the `program/tests.rs` split).
//!
//! The 10,576-line pooled `program/tests.rs` was cut into per-production-submodule
//! sibling files so a RED attributes to ONE production unit by file (METHOD §2.2 /
//! Principle 23, the `design/typecheck/program-decomposition.md` §3 distribution).
//! Everything shared by more than one of those files — the world builders, the AST
//! constructors, the annotated-tree walkers, the assertion helpers — lives HERE,
//! once (Principle 7). It also RE-EXPORTS the common `cranelisp_types` surface, so
//! each test file needs exactly two glob imports (`use super::*;` for its own
//! production module, `use crate::program::test_support::*;` for the fixtures) and
//! no per-file import churn.

use super::*;

pub(crate) use crate::checker::TestFixture;
pub(crate) use cranelisp_types::{
    CompileContext, DefnVariant, Expr, FQSymbol, FQTypeName, ModuleEntry, ModuleFullPath,
    MonoDefnVariant, MonoExpr, Symbol, TraitImpl, TraitName, TypeExpr, TypeName, Visibility,
};

/// Seed glob-import edges from `source` into the fixture's CURRENT module,
/// mirroring `(import [source [*]])`. Import registration is no longer a
/// typecheck concern (facade `typecheck.md`); tests seed edges directly.
pub(crate) fn seed_glob_import(tc: &mut TestFixture, source: &ModuleFullPath) {
    let names: Vec<Symbol> = {
        let src = tc.modules.get(source).expect("source module exists");
        src.all_symbols()
            .filter(|(_, e)| e.is_public())
            .map(|(n, _)| n.clone())
            .collect()
    };
    for name in names {
        tc.symbol_table_mut().insert(
            name.clone(),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: source.clone(),
                    symbol: name,
                },
                visibility: Visibility::Public,
            },
        );
    }
}

/// Seed specific-import edges for `names` from `source` into the fixture's
/// CURRENT module, mirroring `(import [source [a b]])`. See `seed_glob_import`.
pub(crate) fn seed_specific_import(tc: &mut TestFixture, source: &ModuleFullPath, names: &[&str]) {
    for name in names {
        tc.symbol_table_mut().insert(
            Symbol::from(*name),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: source.clone(),
                    symbol: Symbol::from(*name),
                },
                visibility: Visibility::Public,
            },
        );
    }
}

/// Test helper: create an FQTypeName in the "test" module (used by tc_with_prims()).
pub(crate) fn test_fqtn(name: &str) -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from("test"), TypeName::from(name))
}

pub(crate) fn span(start: u32, end: u32) -> Span {
    Span::new(start, end)
}

/// Create a single-sig Defn (convenience for tests).
///
/// Per S69 Submission 23: `DefnVariant.params: Vec<(Symbol, Option<TypeExpr>)>`
/// (fused) — the prior parallel-vec `params: Vec<Symbol>` +
/// `param_annotations: Vec<Option<TypeExpr>>` shape was eliminated.
pub(crate) fn make_defn(
    name: &str,
    params: Vec<Symbol>,
    param_annotations: Vec<Option<TypeExpr>>,
    body: Expr,
    visibility: Visibility,
    span: Span,
) -> Defn {
    assert_eq!(
        params.len(),
        param_annotations.len(),
        "params/annotations must lockstep"
    );
    let fused: Vec<(Symbol, Option<TypeExpr>)> = params
        .into_iter()
        .zip(param_annotations.into_iter())
        .collect();
    Defn {
        name: Symbol::from(name),
        docstring: None,
        variants: vec![DefnVariant {
            params: fused,
            body,
            span,
        }],
        visibility,
        span,
    }
}

/// Create a TypeChecker with primitives imported into a "test" module.
///
/// Narrowed (FIXME 0243) from `TestFixture::new()` (= `full()`) to the
/// content the program-level pipeline tests in this file consume: builtin
/// type names + the Ring 0/1/3 primitive `Def`s + the synthetic `macros`
/// module + the IO ADT (`Bind`/`Pure`/`Effect` are referenced directly).
/// Only `with_special_forms()` is dropped — special forms are resolved at
/// the AST level, never via symbol-table name lookup, and no test in this
/// file probes the special-form entries. Bootstrap order requires
/// `with_builtin_type_names()` before primitives / macros / IO.
pub(crate) fn tc_with_prims() -> TestFixture {
    let mut tc = TestFixture::with_content(
        crate::builtins::FixtureBuilder::new()
            .with_builtin_type_names()
            .with_primitives()
            .with_macros_sexp()
            .with_io(),
    );
    tc.set_current_module(ModuleFullPath::from("test"));
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    tc
}

/// Test helper: walk an Expr tree, recording whether any node carries an
/// `inferred_type` annotation and whether all annotations are resolved
/// (no `Type::Var`). Used by tests that previously inspected
/// `CheckResult.expr_types` — the post-slim equivalent is reading
/// `inferred_type` from annotated AST nodes.
pub(crate) fn walk_inferred_types(expr: &Expr, any_typed: &mut bool, all_resolved: &mut bool) {
    if let Some(ty) = expr.inferred_type() {
        *any_typed = true;
        if let Type::Var(_) = ty {
            *all_resolved = false;
        }
    }
    match expr {
        Expr::Apply { callee, args, .. } => {
            walk_inferred_types(callee, any_typed, all_resolved);
            for a in args {
                walk_inferred_types(a, any_typed, all_resolved);
            }
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            walk_inferred_types(cond, any_typed, all_resolved);
            walk_inferred_types(then_branch, any_typed, all_resolved);
            walk_inferred_types(else_branch, any_typed, all_resolved);
        }
        Expr::Let { bindings, body, .. } => {
            for (_, bexpr) in bindings {
                walk_inferred_types(bexpr, any_typed, all_resolved);
            }
            walk_inferred_types(body, any_typed, all_resolved);
        }
        Expr::Lambda { body, .. } => {
            walk_inferred_types(body, any_typed, all_resolved);
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            walk_inferred_types(scrutinee, any_typed, all_resolved);
            for arm in arms {
                walk_inferred_types(&arm.body, any_typed, all_resolved);
            }
        }
        Expr::VecLit { elements, .. } => {
            for e in elements {
                walk_inferred_types(e, any_typed, all_resolved);
            }
        }
        Expr::Annotate { expr, .. } => {
            walk_inferred_types(expr, any_typed, all_resolved);
        }
        Expr::Trace { body, .. } => {
            walk_inferred_types(body, any_typed, all_resolved);
        }
        Expr::ParBind { bindings, body, .. } => {
            for (_, bexpr) in bindings {
                walk_inferred_types(bexpr, any_typed, all_resolved);
            }
            walk_inferred_types(body, any_typed, all_resolved);
        }
        _ => {}
    }
}

/// Register a minimal Num trait with `+` method, plus an impl for Int,
/// so tests using `(+ x y)` work after Decision 17 elimination.
pub(crate) fn register_num_trait_inline(tc: &mut TestFixture) {
    let num_decl =
        crate::traits::test_helpers::parse_trait_decl("(deftrait Num (+ [lhs rhs] self))");
    tc.register_trait_decl_self(&num_decl).unwrap();

    // impl Num for Int: + → add-i64
    let impl_ = TraitImpl {
        head_con_var: None,
        trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Num")),
        target: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(
            None,
            TypeName::from("Int"),
        )),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("+"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("add-i64"), Span::SYNTHETIC)),
                    args: vec![
                        Expr::var(Symbol::from("x"), Span::SYNTHETIC),
                        Expr::var(Symbol::from("y"), Span::SYNTHETIC),
                    ],
                    span: Span::SYNTHETIC,
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
    };
    tc.register_trait_impl_self(&impl_).unwrap();
    tc.clear_transient_state();
}

// A `var_refs` map carrying a `VarRef::Global` entry for EVERY `Var` span in
// `expr` — so the FIXME-0653 shadow guard (`callee_has_keyed_carrier`, which
// under the S114 carrier flip discriminates `Global` from `Local`) treats
// every callee as a genuine keyed TABLE reference. These name-scan-mechanism
// tests exercise the collector's name matching, not the shadow discipline, so
// a full-Global map keeps them testing exactly what they did before the guard.
pub(crate) fn all_var_carriers(expr: &Expr) -> HashMap<Span, cranelisp_types::VarRef> {
    fn walk(e: &Expr, m: &mut HashMap<Span, cranelisp_types::VarRef>) {
        if let Expr::Var { span, .. } = e {
            m.insert(
                *span,
                cranelisp_types::VarRef::Global(FQSymbol {
                    module: ModuleFullPath::from("test"),
                    symbol: Symbol::from("x"),
                }),
            );
        }
        crate::program::for_each_child_expr(e, |c| walk(c, m));
    }
    let mut m = HashMap::new();
    walk(expr, &mut m);
    m
}

/// Walk a `MonoExpr` collecting `(node_label, resolved_target)` for every
/// `Var` (labelled by its `name`) and `Apply` (labelled `"@apply"`) node.
///
/// **S114 carrier flip.** The `Option<FQSymbol>` carrier the pre-flip tests
/// assert against is now the typed `VarRef`/`ApplyRef` sums. This helper
/// projects the typed verdict back onto the pre-flip `Option<FQSymbol>` shape
/// so every downstream assertion (a table reference carries `Some(fq)`, a
/// local / ViaCallee carries `None`) reads unchanged: `VarRef::Global(fq)` /
/// `ApplyRef::Dispatch(fq)` → `Some(fq)`; `VarRef::Local` / `ApplyRef::ViaCallee`
/// → `None`.
pub(crate) fn collect_resolved_targets(e: &MonoExpr, out: &mut Vec<(String, Option<FQSymbol>)>) {
    match e {
        MonoExpr::Var {
            name, resolution, ..
        } => {
            let rt = match resolution {
                cranelisp_types::VarRef::Global(fq) => Some(fq.clone()),
                cranelisp_types::VarRef::Local { .. } => None,
            };
            out.push((name.as_ref().to_string(), rt));
        }
        MonoExpr::Apply {
            callee,
            args,
            dispatch,
            ..
        } => {
            let rt = match dispatch {
                cranelisp_types::ApplyRef::Dispatch(fq) => Some(fq.clone()),
                cranelisp_types::ApplyRef::ViaCallee => None,
            };
            out.push(("@apply".to_string(), rt));
            collect_resolved_targets(callee, out);
            for a in args {
                collect_resolved_targets(a, out);
            }
        }
        MonoExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_resolved_targets(cond, out);
            collect_resolved_targets(then_branch, out);
            collect_resolved_targets(else_branch, out);
        }
        MonoExpr::Let { bindings, body, .. } => {
            for (_, b) in bindings {
                collect_resolved_targets(b, out);
            }
            collect_resolved_targets(body, out);
        }
        MonoExpr::Lambda { body, .. } => collect_resolved_targets(body, out),
        MonoExpr::Match {
            scrutinee, arms, ..
        } => {
            collect_resolved_targets(scrutinee, out);
            for arm in arms {
                collect_resolved_targets(&arm.body, out);
            }
        }
        _ => {}
    }
}

pub(crate) fn main_codegen_view_of(tc: &TestFixture, name: &str) -> MonoDefnVariant {
    match tc.symbol_table().get(name) {
        Some(ModuleEntry::Def {
            codegen_view: Some(v),
            ..
        }) => v.clone(),
        other => panic!("{name} has no codegen_view: {other:?}"),
    }
}

/// Every current-module symbol name whose bare key CONTAINS `substr` — used
/// to locate a minted mono instance (`idpoly$Int`, `ga$Int`, …) without
/// hard-coding the home-qualified mangle grammar.
pub(crate) fn symbol_names_containing(tc: &TestFixture, substr: &str) -> Vec<String> {
    tc.symbol_table()
        .all_symbols()
        .map(|(n, _)| n.as_ref().to_string())
        .filter(|n| n.contains(substr))
        .collect()
}

/// The `codegen_view` of the first current-module symbol whose key contains
/// `substr` (the minted mono instance).
pub(crate) fn mono_instance_view_containing(tc: &TestFixture, substr: &str) -> MonoDefnVariant {
    let key = tc
        .symbol_table()
        .all_symbols()
        .find(|(n, e)| {
            n.as_ref().contains(substr)
                && matches!(
                    e,
                    ModuleEntry::Def {
                        codegen_view: Some(_),
                        ..
                    }
                )
        })
        .map(|(n, _)| n.as_ref().to_string())
        .unwrap_or_else(|| panic!("no mono instance with codegen_view contains `{substr}`"));
    main_codegen_view_of(tc, &key)
}

/// Walk a `MonoExpr` collecting `(name, VarRef)` for every `Var` node — the
/// typed-carrier sibling of `collect_resolved_targets` (S114 binder-provenance
/// pins).
pub(crate) fn collect_var_resolutions(
    e: &MonoExpr,
    out: &mut Vec<(String, cranelisp_types::VarRef)>,
) {
    if let MonoExpr::Var {
        name, resolution, ..
    } = e
    {
        out.push((name.as_ref().to_string(), resolution.clone()));
    }
    match e {
        MonoExpr::Apply { callee, args, .. } => {
            collect_var_resolutions(callee, out);
            for a in args {
                collect_var_resolutions(a, out);
            }
        }
        MonoExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_var_resolutions(cond, out);
            collect_var_resolutions(then_branch, out);
            collect_var_resolutions(else_branch, out);
        }
        MonoExpr::Let { bindings, body, .. } => {
            for (_, b) in bindings {
                collect_var_resolutions(b, out);
            }
            collect_var_resolutions(body, out);
        }
        MonoExpr::Lambda { body, .. } => collect_var_resolutions(body, out),
        MonoExpr::Match {
            scrutinee, arms, ..
        } => {
            collect_var_resolutions(scrutinee, out);
            for arm in arms {
                collect_var_resolutions(&arm.body, out);
            }
        }
        _ => {}
    }
}

/// The enclosing fn's own storage FQ, for the "must NOT carry this" asserts.
pub(crate) fn enclosing_test_fq(name: &str) -> FQSymbol {
    FQSymbol {
        module: ModuleFullPath::from("test"),
        symbol: Symbol::from(name),
    }
}

/// Walk a `MonoExpr` collecting every reachable `MonoMatchArm.resolved_ctor`
/// (source order).
pub(crate) fn collect_resolved_ctors(e: &MonoExpr, out: &mut Vec<Option<FQSymbol>>) {
    match e {
        MonoExpr::Match {
            scrutinee, arms, ..
        } => {
            collect_resolved_ctors(scrutinee, out);
            for arm in arms {
                out.push(arm.resolved_ctor.clone());
                collect_resolved_ctors(&arm.body, out);
            }
        }
        MonoExpr::Apply { callee, args, .. } => {
            collect_resolved_ctors(callee, out);
            for a in args {
                collect_resolved_ctors(a, out);
            }
        }
        MonoExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_resolved_ctors(cond, out);
            collect_resolved_ctors(then_branch, out);
            collect_resolved_ctors(else_branch, out);
        }
        MonoExpr::Let { bindings, body, .. } => {
            for (_, b) in bindings {
                collect_resolved_ctors(b, out);
            }
            collect_resolved_ctors(body, out);
        }
        MonoExpr::Lambda { body, .. } => collect_resolved_ctors(body, out),
        _ => {}
    }
}

/// Find a mono-instance ctor-pattern view in `module`: scan every mangled
/// mono `Def` (name contains `mangle_frag`) whose `codegen_view` body holds
/// a ctor-pattern arm, and return that FIRST arm's `resolved_ctor`. Outer
/// `Option` = a mono ctor-pattern view was found; inner = its carrier.
pub(crate) fn mono_match_arm_ctor(
    tc: &TestFixture,
    module: &str,
    mangle_frag: &str,
) -> Option<Option<FQSymbol>> {
    let st = tc.modules.get(&ModuleFullPath::from(module))?;
    for (name, entry) in st.all_symbols() {
        if !name.as_ref().contains(mangle_frag) {
            continue;
        }
        if let ModuleEntry::Def {
            codegen_view: Some(v),
            ..
        } = entry
        {
            let mut ctors = Vec::new();
            collect_resolved_ctors(&v.body, &mut ctors);
            if let Some(first) = ctors.into_iter().next() {
                return Some(first);
            }
        }
    }
    None
}

/// Helper to build a CompileContext for test module.
pub(crate) fn test_ctx() -> CompileContext {
    CompileContext {
        module: ModuleFullPath::from("test"),
        codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
    }
}

/// Helper to build a multi-sig Defn.
pub(crate) fn make_multi_defn(name: &str, variants: Vec<DefnVariant>, span: Span) -> Defn {
    Defn {
        name: Symbol::from(name),
        docstring: None,
        variants,
        visibility: Visibility::Public,
        span,
    }
}

/// Helper: create a CompileContext for the "test" module (check_form tests).
pub(crate) fn cf_test_ctx() -> CompileContext {
    CompileContext {
        module: ModuleFullPath::from("test"),
        codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
    }
}

/// Helper: build an "inc" defn: (defn inc [x] (add-i64 x 1))
pub(crate) fn make_inc_defn() -> Defn {
    make_defn(
        "inc",
        vec![Symbol::from("x")],
        vec![None],
        Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("add-i64"), span(16, 23))),
            args: vec![
                Expr::var(Symbol::from("x"), span(24, 25)),
                Expr::IntLit {
                    value: 1,
                    span: span(26, 27),
                    inferred_type: None,
                },
            ],
            span: span(15, 28),
            resolved_call: None,
            inferred_type: None,
        },
        Visibility::Public,
        span(0, 29),
    )
}

/// Helper: build a Color typedef with Red and Green constructors.
pub(crate) fn make_color_typedef() -> TopLevel {
    TopLevel::TypeDef {
        name: TypeName::from("Color"),
        docstring: None,
        type_params: vec![],
        constructors: vec![
            cranelisp_types::ConstructorDef {
                name: Symbol::from("Red"),
                docstring: None,
                fields: vec![],
                span: span(200, 203),
            },
            cranelisp_types::ConstructorDef {
                name: Symbol::from("Green"),
                docstring: None,
                fields: vec![],
                span: span(204, 209),
            },
        ],
        visibility: Visibility::Public,
        span: span(190, 210),
    }
}

/// Helper: build an is-red defn that matches on Color.
pub(crate) fn make_is_red_defn() -> Defn {
    Defn {
        name: Symbol::from("is-red"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("c"), None)],
            body: Expr::Match {
                scrutinee: Box::new(Expr::var(Symbol::from("c"), span(230, 231))),
                arms: vec![
                    cranelisp_types::MatchArm {
                        pattern: cranelisp_types::Pattern::Constructor {
                            name: cranelisp_types::SymbolRef::new(None, Symbol::from("Red")),
                            bindings: vec![],
                            span: span(233, 236),
                        },
                        body: Expr::BoolLit {
                            value: true,
                            span: span(237, 241),
                            inferred_type: None,
                        },
                        span: span(233, 241),
                    },
                    cranelisp_types::MatchArm {
                        pattern: cranelisp_types::Pattern::Wildcard {
                            span: span(242, 243),
                        },
                        body: Expr::BoolLit {
                            value: false,
                            span: span(244, 249),
                            inferred_type: None,
                        },
                        span: span(242, 249),
                    },
                ],
                span: span(224, 250),
                compiler_generated: false,
                inferred_type: None,
            },
            span: span(211, 251),
        }],
        visibility: Visibility::Public,
        span: span(211, 251),
    }
}

/// Helper: build the forward-reference program (double calls add-self).
pub(crate) fn make_forward_ref_program() -> Vec<TopLevel> {
    vec![
        TopLevel::Defn(Defn {
            name: Symbol::from("double"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("add-self"), span(318, 326))),
                    args: vec![Expr::var(Symbol::from("x"), span(327, 328))],
                    span: span(317, 329),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(300, 330),
            }],
            visibility: Visibility::Public,
            span: span(300, 330),
        }),
        TopLevel::Defn(Defn {
            name: Symbol::from("add-self"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("y"), None)],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("add-i64"), span(348, 355))),
                    args: vec![
                        Expr::var(Symbol::from("y"), span(356, 357)),
                        Expr::var(Symbol::from("y"), span(358, 359)),
                    ],
                    span: span(347, 360),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(331, 361),
            }],
            visibility: Visibility::Public,
            span: span(331, 361),
        }),
    ]
}

// ---- Category 1: Behavioral Identity ----

/// Walk an Expr tree and collect all (span, inferred_type) pairs.
pub(crate) fn collect_inferred_types(expr: &Expr, out: &mut Vec<(Span, Option<Type>)>) {
    out.push((expr.span(), expr.inferred_type().cloned()));
    match expr {
        Expr::Apply { callee, args, .. } => {
            collect_inferred_types(callee, out);
            for arg in args {
                collect_inferred_types(arg, out);
            }
        }
        Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
            for (_, binding_expr) in bindings {
                collect_inferred_types(binding_expr, out);
            }
            collect_inferred_types(body, out);
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_inferred_types(cond, out);
            collect_inferred_types(then_branch, out);
            collect_inferred_types(else_branch, out);
        }
        Expr::Lambda { body, .. } => {
            collect_inferred_types(body, out);
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            collect_inferred_types(scrutinee, out);
            for arm in arms {
                collect_inferred_types(&arm.body, out);
            }
        }
        Expr::Annotate { expr: inner, .. } => {
            collect_inferred_types(inner, out);
        }
        Expr::VecLit { elements, .. } => {
            for elem in elements {
                collect_inferred_types(elem, out);
            }
        }
        Expr::Trace { body, .. } => {
            collect_inferred_types(body, out);
        }
        _ => {}
    }
}

/// Find the resolved_call on an Apply node with a given span.
pub(crate) fn find_resolved_call(expr: &Expr, target_span: Span) -> Option<ResolvedCall> {
    if let Expr::Apply {
        resolved_call,
        span,
        callee,
        args,
        ..
    } = expr
    {
        if *span == target_span {
            return resolved_call.as_ref().map(|rc| *rc.clone());
        }
        if let Some(rc) = find_resolved_call(callee, target_span) {
            return Some(rc);
        }
        for arg in args {
            if let Some(rc) = find_resolved_call(arg, target_span) {
                return Some(rc);
            }
        }
    }
    match expr {
        Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
            for (_, binding_expr) in bindings {
                if let Some(rc) = find_resolved_call(binding_expr, target_span) {
                    return Some(rc);
                }
            }
            find_resolved_call(body, target_span)
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => find_resolved_call(cond, target_span)
            .or_else(|| find_resolved_call(then_branch, target_span))
            .or_else(|| find_resolved_call(else_branch, target_span)),
        Expr::Lambda { body, .. } => find_resolved_call(body, target_span),
        Expr::Match {
            scrutinee, arms, ..
        } => find_resolved_call(scrutinee, target_span).or_else(|| {
            arms.iter()
                .find_map(|arm| find_resolved_call(&arm.body, target_span))
        }),
        Expr::Annotate { expr: inner, .. } | Expr::Trace { body: inner, .. } => {
            find_resolved_call(inner, target_span)
        }
        _ => None,
    }
}

/// Build a two-variant multi-sig `add` defn:
///   (defn add
///     ([:Int a :Int b]   (add-i64 a b))
///     ([:Float a :Float b] (add-f64 a b)))
pub(crate) fn make_add_multi_sig_int_float() -> Defn {
    make_multi_defn(
        "add",
        vec![
            DefnVariant {
                params: vec![
                    (
                        Symbol::from("a"),
                        Some(TypeExpr::Named(cranelisp_types::TypeRef::new(
                            None,
                            TypeName::from("Int"),
                        ))),
                    ),
                    (
                        Symbol::from("b"),
                        Some(TypeExpr::Named(cranelisp_types::TypeRef::new(
                            None,
                            TypeName::from("Int"),
                        ))),
                    ),
                ],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("add-i64"), span(510, 517))),
                    args: vec![
                        Expr::var(Symbol::from("a"), span(518, 519)),
                        Expr::var(Symbol::from("b"), span(520, 521)),
                    ],
                    span: span(509, 522),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(505, 523),
            },
            DefnVariant {
                params: vec![
                    (
                        Symbol::from("a"),
                        Some(TypeExpr::Named(cranelisp_types::TypeRef::new(
                            None,
                            TypeName::from("Float"),
                        ))),
                    ),
                    (
                        Symbol::from("b"),
                        Some(TypeExpr::Named(cranelisp_types::TypeRef::new(
                            None,
                            TypeName::from("Float"),
                        ))),
                    ),
                ],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("add-f64"), span(530, 537))),
                    args: vec![
                        Expr::var(Symbol::from("a"), span(538, 539)),
                        Expr::var(Symbol::from("b"), span(540, 541)),
                    ],
                    span: span(529, 542),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(525, 543),
            },
        ],
        span(500, 544),
    )
}

/// Register a single-method trait `name` whose method `method` takes a
/// `Self`-typed param and returns `Int`, plus an `impl name for Int` whose
/// method body is `(add-i64 self self)` — into the fixture's CURRENT module.
/// Used by the cross-module mono test so an imported constrained fn's body
/// has a trait method to dispatch (FIXME 0355). `add-i64` is a Ring-0
/// primitive (`(Fn [Int Int] Int)`); applying it to `self` twice keeps the
/// impl body trivially `(Fn [Int] Int)`-typed.
pub(crate) fn register_int_returning_trait(tc: &mut TestFixture, name: &str, method: &str) {
    let decl = crate::traits::test_helpers::parse_trait_decl(&format!(
        "(deftrait {name} ({method} [self] Int))"
    ));
    tc.register_trait_decl_self(&decl).unwrap();

    let impl_ = TraitImpl {
        head_con_var: None,
        trait_name: cranelisp_types::TraitRef::new(None, TraitName::from(name)),
        target: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from(method),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("self"), None)],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("add-i64"), Span::SYNTHETIC)),
                    args: vec![
                        Expr::var(Symbol::from("self"), Span::SYNTHETIC),
                        Expr::var(Symbol::from("self"), Span::SYNTHETIC),
                    ],
                    span: Span::SYNTHETIC,
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
    };
    tc.register_trait_impl_self(&impl_).unwrap();
    tc.clear_transient_state();
}

// Vec has no dedicated `Type` variant; it is encoded as
// `Type::ADT(primitives/Vec, [elem])` (see builtins.rs
// `register_builtin_type_names`). The over-unification defect stamps this
// ADT onto the accumulator var.
pub(crate) fn is_vec(t: &Type) -> bool {
    matches!(t, Type::ADT(name, _) if name.name.as_ref() == "Vec")
}

/// Register a minimal single-method trait `name` (method `method` with a
/// `Self`-typed parameter and `Bool` return) in the fixture's current
/// module, so a `Bounds([..])` param annotation can resolve it.
pub(crate) fn register_marker_trait(tc: &mut TestFixture, name: &str, method: &str) {
    let decl = crate::traits::test_helpers::parse_trait_decl(&format!(
        "(deftrait {name} ({method} [self] Bool))"
    ));
    tc.register_trait_decl_self(&decl).unwrap();
    tc.clear_transient_state();
}

/// Parse + build a whole program from source and assert it fails to check.
/// Mirrors the legacy `assert_type_error(src, "")` helper at the typecheck
/// seam (no REPL / no binary).
pub(crate) fn assert_check_rejects(src: &str) {
    let mut tc = tc_with_prims();
    let sexps = cranelisp_frontend::parse(src).expect("parse must succeed");
    let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms must succeed");
    let result = tc.check(
        &program,
        &test_ctx(),
        cranelisp_types::ModuleStrategy::Additive,
    );
    assert!(result.is_err(), "expected a type error for {src:?}, got Ok");
}

/// Register an `Option` ADT (`None` | `(Some [v])`) in the current `test`
/// module — the result-only-var shape needs `None`. Returns the TopLevel.
pub(crate) fn option_typedef() -> TopLevel {
    TopLevel::TypeDef {
        name: TypeName::from("Option"),
        docstring: None,
        type_params: vec![Symbol::from("a")],
        constructors: vec![
            cranelisp_types::ConstructorDef {
                name: Symbol::from("None"),
                docstring: None,
                fields: vec![],
                span: Span::SYNTHETIC,
            },
            cranelisp_types::ConstructorDef {
                name: Symbol::from("Some"),
                docstring: None,
                fields: vec![cranelisp_types::FieldDef {
                    name: Symbol::from("v"),
                    type_expr: TypeExpr::TypeVar(Symbol::from("a")),
                    span: Span::SYNTHETIC,
                }],
                span: Span::SYNTHETIC,
            },
        ],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    }
}

/// `(defn identity [x] x)` — the polymorphic identity, used to produce an
/// unpinned `(Option a)` value as `(identity None)` (the call does not pin
/// the var; `identity`'s result is `a`, instantiated to `(Option a)`).
pub(crate) fn identity_defn() -> TopLevel {
    TopLevel::Defn(make_defn(
        "identity",
        vec![Symbol::from("x")],
        vec![None],
        Expr::var(Symbol::from("x"), span(20, 21)),
        Visibility::Public,
        span(10, 22),
    ))
}

/// `(identity None)` — an `Apply` producing the unpinned `(Option a)` value.
pub(crate) fn identity_none(call_span: Span) -> Expr {
    Expr::Apply {
        callee: Box::new(Expr::var(
            Symbol::from("identity"),
            span(call_span.start, call_span.start + 8),
        )),
        args: vec![Expr::var(
            Symbol::from("None"),
            span(call_span.start + 9, call_span.end),
        )],
        span: call_span,
        resolved_call: None,
        inferred_type: None,
    }
}

/// `(defn consume [y] 0)` — discards its arg, returns a concrete `Int`. Used
/// to bury an ambiguous value in a value position while keeping the enclosing
/// defn `m`'s OWN result type concrete (`(Fn [] Int)`, no free var) so the
/// offending var is genuinely free-at-root, not quantified into `m`'s scheme.
pub(crate) fn consume_defn() -> TopLevel {
    TopLevel::Defn(make_defn(
        "consume",
        vec![Symbol::from("y")],
        vec![None],
        Expr::IntLit {
            value: 0,
            span: span(30, 31),
            inferred_type: None,
        },
        Visibility::Public,
        span(28, 32),
    ))
}

/// Wrap `inner` (the value position under test) in `(consume <inner>)` so the
/// enclosing `m`'s result is concrete `Int`. Returns the wrapping body.
pub(crate) fn consume_wrap(inner: Expr) -> Expr {
    let inner_span = inner.span();
    Expr::Apply {
        callee: Box::new(Expr::var(Symbol::from("consume"), span(101, 108))),
        args: vec![inner],
        span: span(100, inner_span.end + 1),
        resolved_call: None,
        inferred_type: None,
    }
}

/// Assert checking `[Option, identity, consume, defn m with `body`]` rejects
/// with an "ambiguous" error (the §3.11.1 position-complete verdict). `m`'s
/// own result is kept concrete by `consume_wrap` so the offending var is
/// free-at-root (not a quantified scheme var).
pub(crate) fn assert_ambiguous(body: Expr, what: &str) {
    let mut tc = tc_with_prims();
    let ctx = cf_test_ctx();
    let m = TopLevel::Defn(make_defn(
        "m",
        vec![],
        vec![],
        body,
        Visibility::Public,
        span(100, 200),
    ));
    let result = tc.check(
        &[option_typedef(), identity_defn(), consume_defn(), m],
        &ctx,
        ModuleStrategy::Additive,
    );
    let err = result.err().unwrap_or_else(|| {
        panic!("an unpinned `(Option a)` value in a {what} must be rejected as ambiguous (§3.11.1)")
    });
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("ambiguous"),
        "the §3.11.1 rejection at a {what} must name 'ambiguous'; got: {msg}",
    );
}

/// Read the `callees` list off a module entry (owned copy).
pub(crate) fn callees_of(tc: &TestFixture, module: &str, name: &str) -> Vec<FQSymbol> {
    let path = ModuleFullPath::from(module);
    let guard = tc.modules.get(&path).expect("module exists");
    guard
        .get(name)
        .unwrap_or_else(|| panic!("`{name}` not found in module `{module}`"))
        .callees()
        .to_vec()
}

pub(crate) fn fq_sym(module: &str, symbol: &str) -> FQSymbol {
    FQSymbol {
        module: ModuleFullPath::from(module),
        symbol: Symbol::from(symbol),
    }
}

/// Parse + check `src` in the fixture's current module.
pub(crate) fn check_src(tc: &mut TestFixture, src: &str) {
    let sexps = cranelisp_frontend::parse(src).expect("parse");
    let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
    tc.check_program_self(&program)
        .unwrap_or_else(|e| panic!("check failed for:\n{src}\n error: {e:?}"));
}

/// Collect the first `SigDispatch` mangled name found on any Apply node in
/// a body Expr tree (helper for the 0488 collection-shape tests).
pub(crate) fn first_sig_dispatch(expr: &Expr) -> Option<String> {
    if let Expr::Apply {
        callee,
        args,
        resolved_call,
        ..
    } = expr
    {
        if let Some(ResolvedCall::SigDispatch { mangled_name }) = resolved_call.as_deref() {
            return Some(mangled_name.as_ref().to_string());
        }
        if let Some(m) = first_sig_dispatch(callee) {
            return Some(m);
        }
        for a in args {
            if let Some(m) = first_sig_dispatch(a) {
                return Some(m);
            }
        }
    }
    None
}

/// Does any `Var` node in the tree carry the given name? (fn-value rewrite
/// witness for signature (b)).
pub(crate) fn body_has_var_named(expr: &Expr, target: &str) -> bool {
    match expr {
        Expr::Var { name, .. } => name.as_ref() == target,
        Expr::Apply { callee, args, .. } => {
            body_has_var_named(callee, target) || args.iter().any(|a| body_has_var_named(a, target))
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            body_has_var_named(cond, target)
                || body_has_var_named(then_branch, target)
                || body_has_var_named(else_branch, target)
        }
        Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
            bindings.iter().any(|(_, b)| body_has_var_named(b, target))
                || body_has_var_named(body, target)
        }
        Expr::Lambda { body, .. }
        | Expr::Annotate { expr: body, .. }
        | Expr::Trace { body, .. } => body_has_var_named(body, target),
        Expr::VecLit { elements, .. } => elements.iter().any(|e| body_has_var_named(e, target)),
        _ => false,
    }
}

/// The stored annotated body of `name` in the fixture's current module.
pub(crate) fn stored_body(tc: &TestFixture, name: &str) -> Expr {
    match tc.symbol_table().get(name) {
        Some(ModuleEntry::Def {
            ast: Some(variant), ..
        }) => variant.body.clone(),
        other => panic!("`{name}` has no stored annotated body: {other:?}"),
    }
}

// The signature-(c) fixture, mirroring the e2e FOLD_MODULE: a same-module
// generic fold (`vreduce`/`vreduce-loop`) whose helper threads a polymorphic
// accumulator, and `vconcat` — a fold-bodied generic passing the builtin
// `vec-push` as a VALUE into the fold.
pub(crate) const FOLD_SRC: &str = "\
    (defn vreduce [f init v] (vreduce-loop f init v (vec-len v) 0))\n\
    (defn vreduce-loop [f acc v :primitives/Int len :primitives/Int i]\n  \
      (if (ge-i64 i len) acc\n    \
        (vreduce-loop f (f acc (vec-get v i)) v len (add-i64 i 1))))\n\
    (defn vconcat [va vb] (vreduce vec-push va vb))";
