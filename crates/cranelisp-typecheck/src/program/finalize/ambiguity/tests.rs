//! Per-submodule tests for `program/finalize/ambiguity.rs` — the §3.11
//! codegen-ambiguity admission scan: a residual free type variable reaching a
//! codegen position is rejected, while a named polymorphic definition and a
//! result-only free var are admitted.

use super::*;
use crate::program::test_support::*;

// spec: spec/03-types.md §3.11.1 — a CODEGEN-REACHING unpinned polymorphic
//       value is an ambiguity error. A `let`-bound `None` whose type stays
//       `(Option a)` (the `match` scrutinises only the tag) must be
//       REJECTED. Mirrors the e2e
//       `regression::mono_ambiguous_unconstrained_top_level_var_rejected_neg`.
#[test]
fn ambiguity_check_rejects_codegen_reaching_unpinned_let_binding() {
    let mut tc = tc_with_prims();
    let ctx = cf_test_ctx();
    // (defn m [] (let [x None] (match x [None 0 (Some _) 1])))
    // `x : (Option a)`, `a` unpinned (match reads only the tag) — §3.11.1.
    let body = Expr::Let {
        bindings: vec![(
            Symbol::from("x"),
            Expr::var(Symbol::from("None"), span(60, 64)),
        )],
        body: Box::new(Expr::Match {
            scrutinee: Box::new(Expr::var(Symbol::from("x"), span(70, 71))),
            arms: vec![
                cranelisp_types::MatchArm {
                    pattern: cranelisp_types::Pattern::Constructor {
                        name: cranelisp_types::SymbolRef::new(None, Symbol::from("None")),
                        bindings: vec![],
                        span: span(73, 77),
                    },
                    body: Expr::IntLit {
                        value: 0,
                        span: span(78, 79),
                        inferred_type: None,
                    },
                    span: span(73, 79),
                },
                cranelisp_types::MatchArm {
                    pattern: cranelisp_types::Pattern::Constructor {
                        name: cranelisp_types::SymbolRef::new(None, Symbol::from("Some")),
                        bindings: vec![Symbol::from("_")],
                        span: span(82, 87),
                    },
                    body: Expr::IntLit {
                        value: 1,
                        span: span(88, 89),
                        inferred_type: None,
                    },
                    span: span(82, 89),
                },
            ],
            span: span(66, 90),
            compiler_generated: false,
            inferred_type: None,
        }),
        span: span(55, 91),
        inferred_type: None,
    };
    let m = TopLevel::Defn(make_defn(
        "m",
        vec![],
        vec![],
        body,
        Visibility::Public,
        span(50, 92),
    ));
    let result = tc.check(&[option_typedef(), m], &ctx, ModuleStrategy::Additive);
    let err = result.expect_err(
        "a codegen-reaching unpinned `let`-bound `(Option a)` value must be \
         rejected as ambiguous (§3.11.1)",
    );
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("ambiguous"),
        "the §3.11.1 rejection must name 'ambiguous'; got: {msg}",
    );
}

// spec: spec/03-types.md §3.11.3 — a NAMED polymorphic defn with
//       result-only free vars is ADMITTED (sound, dead-for-codegen). The
//       §3.11.1 check MUST NOT fire on `(defn ambig [] None)`. Mirrors the
//       e2e `regression::mono_ambiguous_neg_does_not_reach_codegen`.
#[test]
fn ambiguity_check_admits_named_polymorphic_defn() {
    let mut tc = tc_with_prims();
    let ctx = cf_test_ctx();
    // (defn ambig [] None) — `(Fn [] (Option a))`, result-only var. ADMIT.
    let ambig = TopLevel::Defn(make_defn(
        "ambig",
        vec![],
        vec![],
        Expr::var(Symbol::from("None"), span(40, 44)),
        Visibility::Public,
        span(38, 45),
    ));
    tc.check(&[option_typedef(), ambig], &ctx, ModuleStrategy::Additive)
        .expect("a named result-only-var defn is sound and must be admitted (§3.11.3)");
    // It is slot-less `Polymorphic` (NOT a `test-*` fn, so no mono root).
    let table = tc.symbol_table();
    let entry = table.get("ambig").expect("ambig registered");
    assert!(
        matches!(
            entry,
            ModuleEntry::Def { kind, .. }
                if matches!(
                    kind.as_ref(),
                    DefKind::UserFn { fn_state: UserFnState::Polymorphic(_) }
                )
        ),
        "a named result-only-var defn is slot-less `Polymorphic`, got {entry:?}",
    );
}

// =====================================================================
// §7(e) POSITION-COMPLETE §3.11.1 (S84, FIXME 0379/0380 → tightened 0386).
// An ADT-with-free-var (`(Option a)`, `a` unpinned) reaching a codegen
// value position in a NON-`let` slot — match scrutinee, fn-call arg, vec
// element, ctor field, if-branch — must be REJECTED as ambiguous. The old
// scanner only checked `let` bindings; the position-complete scanner checks
// every value-producing child. The `let`-position case stays an asserted
// positive control
// (`ambiguity_check_rejects_codegen_reaching_unpinned_let_binding`).
//
// TIGHTENED §3.11.1 (commit 2290aa9, FIXME 0386): the verdict is FULL
// CONCRETENESS (`!ty.is_concrete()`) — NO representation exemption. A
// free-at-root `(Vec a)`/`(Fn [a] a)` value at a codegen-reaching position
// is now REJECTED too (it was admitted under the old
// representation-determinacy verdict). Result-only free vars (a definition's
// own scheme vars, §3.11.3) stay admitted — they are quantified, pinned
// per-instantiation, not free-at-root.
// =====================================================================

// spec: spec/03-types.md §3.11.1 — MATCH SCRUTINEE position (non-`let`).
#[test]
fn mixed_adt_free_var_in_match_scrutinee_is_ambiguous() {
    // (defn m [] (match (identity None) [None 0 (Some _) 1]))
    let body = Expr::Match {
        scrutinee: Box::new(identity_none(span(110, 124))),
        arms: vec![
            cranelisp_types::MatchArm {
                pattern: cranelisp_types::Pattern::Constructor {
                    name: cranelisp_types::SymbolRef::new(None, Symbol::from("None")),
                    bindings: vec![],
                    span: span(126, 130),
                },
                body: Expr::IntLit {
                    value: 0,
                    span: span(131, 132),
                    inferred_type: None,
                },
                span: span(126, 132),
            },
            cranelisp_types::MatchArm {
                pattern: cranelisp_types::Pattern::Constructor {
                    name: cranelisp_types::SymbolRef::new(None, Symbol::from("Some")),
                    bindings: vec![Symbol::from("_")],
                    span: span(135, 140),
                },
                body: Expr::IntLit {
                    value: 1,
                    span: span(141, 142),
                    inferred_type: None,
                },
                span: span(135, 142),
            },
        ],
        span: span(105, 145),
        compiler_generated: false,
        inferred_type: None,
    };
    assert_ambiguous(body, "match scrutinee");
}

// spec: spec/03-types.md §3.11.1 — FUNCTION-CALL ARGUMENT position (non-`let`).
#[test]
fn mixed_adt_free_var_in_call_arg_is_ambiguous() {
    // (defn m [] (consume (identity None))) — `(identity None)` : `(Option a)`,
    // unpinned (the call to `consume` discards its arg, pins nothing). `m`'s
    // result is concrete `Int` (consume returns 0), so `a` is free-at-root.
    let body = consume_wrap(identity_none(span(115, 129)));
    assert_ambiguous(body, "call argument");
}

// spec: spec/03-types.md §3.11.1 — VEC ELEMENT position (non-`let`). The
// value INSIDE the vec is `(Option a)`-with-free-var (the vec's own type
// `(Vec (Option a))` is admitted, but its element is checked too).
#[test]
fn mixed_adt_free_var_in_vec_element_is_ambiguous() {
    // (defn m [] (consume [(identity None)]))
    let body = consume_wrap(Expr::VecLit {
        elements: vec![identity_none(span(116, 130))],
        span: span(115, 131),
        inferred_type: None,
    });
    assert_ambiguous(body, "vec element");
}

// spec: spec/03-types.md §3.11.1 — CONSTRUCTOR FIELD position (non-`let`).
#[test]
fn mixed_adt_free_var_in_ctor_field_is_ambiguous() {
    // (defn m [] (consume (Some (identity None)))) — the `Some` field holds an
    // unpinned `(Option a)`; `consume` keeps `m`'s result concrete `Int`.
    let body = consume_wrap(Expr::Apply {
        callee: Box::new(Expr::var(Symbol::from("Some"), span(116, 120))),
        args: vec![identity_none(span(121, 135))],
        span: span(115, 136),
        resolved_call: None,
        inferred_type: None,
    });
    assert_ambiguous(body, "constructor field");
}

// spec: spec/03-types.md §3.11.1 — IF BRANCH position (non-`let`).
#[test]
fn mixed_adt_free_var_in_if_branch_is_ambiguous() {
    // (defn m [] (consume (if true (identity None) (identity None))))
    let body = consume_wrap(Expr::If {
        cond: Box::new(Expr::BoolLit {
            value: true,
            span: span(118, 122),
            inferred_type: None,
        }),
        then_branch: Box::new(identity_none(span(123, 137))),
        else_branch: Box::new(identity_none(span(138, 152))),
        span: span(115, 155),
        inferred_type: None,
    });
    assert_ambiguous(body, "if branch");
}

// spec: spec/03-types.md §3.11.3 — a RESULT-ONLY free var (a definition's
// own scheme var, NOT free-at-root) is ADMITTED. `(defn m [] [[]])` has type
// `(Fn [] (Vec (Vec a)))`; `a` is quantified into `m`'s scheme and pinned
// per-instantiation by monomorphisation, so the inner `(Vec a)` element is
// sound (disposition 1, dead-for-codegen until a concrete use). The §4.4
// `allowed_vars` filter excludes `m`'s scheme vars, so the full-concreteness
// verdict does NOT over-fire on a definition. (This is distinct from the
// free-at-root `(Vec a)` rejection below — there the var is NOT in any
// enclosing scheme.)
#[test]
fn vec_result_only_free_var_definition_is_admitted() {
    let mut tc = tc_with_prims();
    let ctx = cf_test_ctx();
    // (defn m [] [[]]) — outer `(Vec (Vec a))`, inner element `(Vec a)` free.
    let body = Expr::VecLit {
        elements: vec![Expr::VecLit {
            elements: vec![],
            span: span(106, 108),
            inferred_type: None,
        }],
        span: span(105, 109),
        inferred_type: None,
    };
    let m = TopLevel::Defn(make_defn(
        "m",
        vec![],
        vec![],
        body,
        Visibility::Public,
        span(100, 110),
    ));
    tc.check(&[m], &ctx, ModuleStrategy::Additive)
        .expect("a result-only `(Vec a)` defn (§3.11.3 disposition 1) MUST be admitted");
}

// spec: spec/03-types.md §3.11.1 — TIGHTENED full-concreteness verdict
// (FIXME 0386): a FREE-AT-ROOT `(Vec a)` value at a codegen-reaching value
// position is REJECTED as ambiguous. `(consume (identity []))` — `[]` is
// `(Vec a)`, `(identity [])` keeps `a` free, `consume` discards it (pinning
// nothing) and keeps `m`'s result concrete `Int`, so `a` is free-at-root.
// No representation exemption: `Vec` being uniformly heap-allocated does NOT
// rescue the unpinned element var. This is the seam witness for the e2e
// `regression::mono_vec_free_var_value_rejected_neg`.
#[test]
fn vec_free_at_root_value_position_is_ambiguous() {
    // (defn m [] (consume (identity []))) — `(identity [])` : `(Vec a)`,
    // `a` free-at-root.
    let empty_vec = Expr::VecLit {
        elements: vec![],
        span: span(125, 127),
        inferred_type: None,
    };
    let identity_empty_vec = Expr::Apply {
        callee: Box::new(Expr::var(Symbol::from("identity"), span(116, 124))),
        args: vec![empty_vec],
        span: span(115, 128),
        resolved_call: None,
        inferred_type: None,
    };
    assert_ambiguous(consume_wrap(identity_empty_vec), "vec value (free-at-root)");
}

// spec: spec/03-types.md §3.11.1 — TIGHTENED full-concreteness verdict
// (FIXME 0386): a FREE-AT-ROOT `(Fn [a] a)` polymorphic-function value at a
// codegen-reaching position is REJECTED as ambiguous. `(consume identity)` —
// `identity` : `(Fn [a] a)`, passed to `consume` which discards it. A
// closure's uniform machine shape does NOT rescue the unpinned type var.
// Seam witness for `regression::mono_fn_free_var_value_rejected_neg`.
#[test]
fn fn_free_at_root_value_position_is_ambiguous() {
    // (defn m [] (consume identity)) — `identity` : `(Fn [a] a)`, free-at-root.
    let identity_value = Expr::var(Symbol::from("identity"), span(115, 123));
    assert_ambiguous(consume_wrap(identity_value), "fn value (free-at-root)");
}

// spec: spec/03-types.md §3.11.1 — the full-concreteness verdict ADMITS a
// fully concrete value at a codegen-reaching position. `(consume (identity
// 7))` — `(identity 7)` : `Int` (fully concrete, no free var), so the check
// MUST NOT fire. Pairs with the free-at-root rejections above (same
// `consume`-wrap shape; only the inner type differs).
#[test]
fn concrete_value_position_is_admitted() {
    let mut tc = tc_with_prims();
    let ctx = cf_test_ctx();
    // (defn m [] (consume (identity 7)))
    let identity_int = Expr::Apply {
        callee: Box::new(Expr::var(Symbol::from("identity"), span(116, 124))),
        args: vec![Expr::IntLit {
            value: 7,
            span: span(125, 126),
            inferred_type: None,
        }],
        span: span(115, 127),
        resolved_call: None,
        inferred_type: None,
    };
    let m = TopLevel::Defn(make_defn(
        "m",
        vec![],
        vec![],
        consume_wrap(identity_int),
        Visibility::Public,
        span(100, 130),
    ));
    tc.check(
        &[identity_defn(), consume_defn(), m],
        &ctx,
        ModuleStrategy::Additive,
    )
    .expect("a fully concrete `Int` value at a codegen position MUST be admitted (§3.11.1)");
}

// spec: spec/07-traits.md §7.1.5 + spec/08-modules.md §8.6 — DEFECT D1 (S86):
//   a SYNTHESIZED default-method body's free names MUST resolve in the trait's
//   DEFINING module, not the impl-writer's (caller's) module. A trait `Foo`
//   declared in module `trait_mod` (which globs primitives) has a default
//   method `bar` whose body references the bare primitive `add-i64`. An impl
//   in module `user` (NO primitives glob) omits `bar`, so
//   `generate_default_methods` synthesizes the body and `check_impl_method_with_sig`
//   checks it. Before the fix, that check runs in `user`'s `current_module`, so
//   `add-i64` resolves there and fails (`undefined variable: add-i64`). The fix
//   mirrors `recheck_body_for_mono`'s defining-module switch into the
//   default-method check path, so the body re-checks in `trait_mod`'s import
//   context and `add-i64` resolves.
#[test]
fn default_method_body_resolves_in_trait_defining_module() {
    let mut tc = tc_with_prims();
    let trait_mod = ModuleFullPath::from("trait_mod");
    let user = ModuleFullPath::from("user");

    // --- DEFINING module `trait_mod`: globs primitives; declares `Foo` with a
    //     required `req` and a DEFAULT `bar` whose body uses bare `add-i64`. ---
    tc.set_current_module(trait_mod.clone());
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));

    let decl = crate::traits::test_helpers::parse_trait_decl(
        "(deftrait Foo (req [self] self) (bar [a b] :Int (add-i64 a b)))",
    );
    tc.register_trait_decl_self(&decl)
        .expect("`Foo` declares in its defining module");

    // --- IMPL module `user`: does NOT glob primitives; imports the trait +
    //     methods, and registers an impl that OMITS `bar` (forcing default
    //     synthesis + check). `add-i64` is NOT bare-in-scope here. ---
    tc.set_current_module(user.clone());
    seed_specific_import(&mut tc, &trait_mod, &["Foo", "req", "bar"]);
    // `user` needs `Int` reachable for the impl target / sig resolution, but
    // explicitly NOT `add-i64`.
    seed_specific_import(&mut tc, &ModuleFullPath::from("primitives"), &["Int"]);

    let impl_ = TraitImpl {
        head_con_var: None,
        trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Foo")),
        target: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("req"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("self"), None)],
                body: Expr::var(Symbol::from("self"), Span::SYNTHETIC),
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
    };

    // CRUX: registering the impl synthesizes + checks the default `bar` body.
    // Before the fix this fails with `undefined variable: add-i64` (the body
    // is checked in `user`'s scope). After the fix the body re-checks in
    // `trait_mod`'s scope, where `add-i64` resolves.
    tc.register_trait_impl_self(&impl_).unwrap_or_else(|e| {
        panic!(
            "default-method body must resolve `add-i64` in the trait's \
             DEFINING module (`trait_mod`), not the impl writer's (`user`); \
             got: {e:?}"
        )
    });
}

// =====================================================================
// `Def.callees` completeness contract (FIXME 0470, S101 Wave 2)
//
// spec: tests/plan/s101-coverage-postmortem.md §2.1 — every statically-
//   resolved user-fn reference (call-position AND value-position) must be
//   recorded in the checked entry's `callees`; no spurious edges for
//   shadowed names, primitives/special forms, non-UserFn Def kinds, or
//   unrelated siblings. Consumer: the S101 R3 dependent-recompilation
//   transaction's reverse index (design/int/session-transaction.md §3.2).
// =====================================================================
