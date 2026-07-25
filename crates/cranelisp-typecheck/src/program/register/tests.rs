//! Per-submodule tests for `program/register.rs` — Pass-1 registration: a
//! `TopLevel` becomes symbol-table signature / type-var / constrained-marker
//! state, including the §8.6.4 name-freedom arms and the bound-param /
//! trait-bound annotation legs. Split from the pooled `program/tests.rs`
//! (FIXME 0722); the multi-sig overload family is a sibling.

use super::*;

use crate::program::test_support::*;

// spec: 05-definitions §5.1 — defn registers function with inferred type
#[test]
fn test_check_program_simple_defn() {
    let mut tc = tc_with_prims();
    // (defn add-one [x] (add-i64 x 1))
    let program = vec![TopLevel::Defn(Defn {
        name: Symbol::from("add-one"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None)],
            body: Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("add-i64"), span(20, 27))),
                args: vec![
                    Expr::var(Symbol::from("x"), span(28, 29)),
                    Expr::IntLit {
                        value: 1,
                        span: span(30, 31),
                        inferred_type: None,
                    },
                ],
                span: span(19, 32),
                resolved_call: None,
                inferred_type: None,
            },
            span: span(0, 33),
        }],
        visibility: Visibility::Public,
        span: span(0, 33),
    })];

    let _result = tc.check_program_self(&program).unwrap();

    // Check the function was registered with correct type: Fn([Int], Int)
    if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add-one") {
        assert_eq!(scheme.ty, Type::Fn(vec![Type::Int], Box::new(Type::Int)));
    } else {
        panic!("add-one not found in symbol table");
    }
}

// spec: 03-types §3.4 — identity function generalized to polymorphic scheme
#[test]
fn test_check_program_identity_is_polymorphic() {
    let mut tc = tc_with_prims();
    // (defn id [x] x)
    let program = vec![TopLevel::Defn(Defn {
        name: Symbol::from("id"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None)],
            body: Expr::var(Symbol::from("x"), span(14, 15)),
            span: span(0, 16),
        }],
        visibility: Visibility::Public,
        span: span(0, 16),
    })];

    tc.check_program_self(&program).unwrap();

    if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("id") {
        // Should be forall [a]. Fn([a], a)
        assert_eq!(scheme.type_vars.len(), 1, "id should have 1 quantified var");
        match &scheme.ty {
            Type::Fn(params, ret) => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0], **ret);
            }
            _ => panic!("expected Fn type"),
        }
    } else {
        panic!("id not found in symbol table");
    }
}

// spec: 05-definitions §5.2 — deftype registers constructors and enables match
#[test]
fn test_check_program_with_typedef() {
    let mut tc = tc_with_prims();
    let program = vec![
        TopLevel::TypeDef {
            name: TypeName::from("Color"),
            docstring: None,
            type_params: vec![],
            constructors: vec![
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("Red"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("Green"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
            ],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        },
        TopLevel::Defn(Defn {
            name: Symbol::from("is-red"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("c"), None)],
                body: Expr::Match {
                    scrutinee: Box::new(Expr::var(Symbol::from("c"), span(30, 31))),
                    arms: vec![
                        cranelisp_types::MatchArm {
                            pattern: cranelisp_types::Pattern::Constructor {
                                name: cranelisp_types::SymbolRef::new(None, Symbol::from("Red")),
                                bindings: vec![],
                                span: span(33, 36),
                            },
                            body: Expr::BoolLit {
                                value: true,
                                span: span(37, 41),
                                inferred_type: None,
                            },
                            span: span(33, 41),
                        },
                        cranelisp_types::MatchArm {
                            pattern: cranelisp_types::Pattern::Wildcard { span: span(42, 43) },
                            body: Expr::BoolLit {
                                value: false,
                                span: span(44, 49),
                                inferred_type: None,
                            },
                            span: span(42, 49),
                        },
                    ],
                    span: span(24, 50),
                    compiler_generated: false,
                    inferred_type: None,
                },
                span: span(0, 51),
            }],
            visibility: Visibility::Public,
            span: span(0, 51),
        }),
    ];

    let _result = tc.check_program_self(&program).unwrap();

    if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("is-red") {
        assert_eq!(
            scheme.ty,
            Type::Fn(
                vec![Type::ADT(test_fqtn("Color"), vec![])],
                Box::new(Type::Bool)
            )
        );
    } else {
        panic!("is-red not found in symbol table");
    }

    // Type defs should be in the result
    assert!(tc.lookup_type_def(&TypeName::from("Color")).is_some());
    assert!(tc.lookup_constructor_type("Red").is_some());
}

// spec: 03-types §3.4 — REPL defn produces polymorphic scheme
#[test]
fn test_check_repl_defn() {
    let mut tc = tc_with_prims();
    let input = TopLevel::Defn(Defn {
        name: Symbol::from("id"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None)],
            body: Expr::var(Symbol::from("x"), span(14, 15)),
            span: span(0, 16),
        }],
        visibility: Visibility::Public,
        span: span(0, 16),
    });
    let result = tc.check_repl_input_self(&input).unwrap();

    // The scheme should be polymorphic
    let scheme = result.display.as_ref().unwrap().scheme.clone().unwrap();
    assert_eq!(scheme.type_vars.len(), 1);
}

// spec: 05-definitions §5.2 — REPL typedef registers type and constructors
#[test]
fn test_check_repl_typedef() {
    let mut tc = tc_with_prims();
    let input = TopLevel::TypeDef {
        name: TypeName::from("Dir"),
        docstring: None,
        type_params: vec![],
        constructors: vec![
            cranelisp_types::ConstructorDef {
                name: Symbol::from("North"),
                docstring: None,
                fields: vec![],
                span: Span::SYNTHETIC,
            },
            cranelisp_types::ConstructorDef {
                name: Symbol::from("South"),
                docstring: None,
                fields: vec![],
                span: Span::SYNTHETIC,
            },
        ],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };
    let result = tc.check_repl_input_self(&input).unwrap();
    assert_eq!(
        result.display.as_ref().unwrap().ty,
        Type::ADT(test_fqtn("Dir"), vec![])
    );
    assert!(tc.lookup_type_def(&TypeName::from("Dir")).is_some());
}

// spec: 05-definitions §5.2.2 — polymorphic typedef registers constructors with type params
#[test]
fn test_check_program_polymorphic_typedef() {
    let mut tc = tc_with_prims();
    // (deftype (Option a) None (Some [:a val]))
    // (defn unwrap-or [opt default] (match opt [(Some x) x (None default)]))
    let program = vec![TopLevel::TypeDef {
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
                    name: Symbol::from("val"),
                    type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                    span: Span::SYNTHETIC,
                }],
                span: Span::SYNTHETIC,
            },
        ],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    }];

    let _result = tc.check_program_self(&program).unwrap();
    assert!(tc.lookup_type_def(&TypeName::from("Option")).is_some());
    assert!(tc.lookup_constructor_type("Some").is_some());
    assert!(tc.lookup_constructor_type("None").is_some());
}

// spec: 05-definitions §5.2.2 — REPL polymorphic typedef registers type defs
#[test]
fn test_check_repl_polymorphic_typedef() {
    let mut tc = tc_with_prims();
    let input = TopLevel::TypeDef {
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
                    name: Symbol::from("val"),
                    type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                    span: Span::SYNTHETIC,
                }],
                span: Span::SYNTHETIC,
            },
        ],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };
    let _result = tc.check_repl_input_self(&input).unwrap();
    assert!(tc.lookup_type_def(&TypeName::from("Option")).is_some());
}

// spec: 03-types §3.3 [S109] / §3.9.2 (u5) — a KNOWN trait-name annotation
// still takes the constraint path, unaffected by the written-free-var minting
// rule. `(defn show2 [:Num x] x)` yields a CONSTRAINED polymorphic scheme
// (Num constraint on the param var), NOT a plain minted free var and NOT an
// `unknown type Num` error. Pins that the §3.3 free-var fix keys on
// `TypeExpr::TypeVar` (lowercase) and does not intercept the uppercase
// `Named` → try-type-then-trait path (FV-14's seam).
#[test]
fn u5_trait_constraint_annotation_unaffected_by_free_var_rule() {
    let mut tc = tc_with_prims();
    register_num_trait_inline(&mut tc);
    // (defn show2 [:Num x] x)
    let program = vec![TopLevel::Defn(Defn {
        name: Symbol::from("show2"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(
                Symbol::from("x"),
                Some(cranelisp_types::TypeExpr::Named(
                    cranelisp_types::TypeRef::new(None, TypeName::from("Num")),
                )),
            )],
            body: Expr::var(Symbol::from("x"), span(18, 19)),
            span: span(0, 20),
        }],
        visibility: Visibility::Public,
        span: span(0, 20),
    })];

    // Must type-check (no `unknown type Num` error).
    tc.check_program_self(&program).unwrap();

    if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("show2") {
        assert!(
            !scheme.constraints.is_empty(),
            "show2's `:Num` annotation must produce a constrained scheme, not a plain free var"
        );
        assert!(
            !scheme.type_vars.is_empty(),
            "show2 stays polymorphic (constrained), not concrete"
        );
    } else {
        panic!("show2 not found in symbol table");
    }
}

// spec: 03-types §3.3.1 [S109 W6.3] (U1) — a BARE written parameter type var
// is an ORDINARY FLEXIBLE inference variable carrying a display name, NOT a
// rigid skolem (W6.3 backs out the W6.2 rigid-bare model). Two facets at the
// program seam: (a) unconstrained → stays polymorphic (`(defn id [:a x] x)` →
// `∀a. a→a`); (b) a body USE that pins it is ACCEPTED and the scheme reflects
// the concrete type (`(defn f [:a x] (add-i64 1 x))` → `(Fn [Int] Int)`, row
// 2) — the defining contrast with the superseded rigid model (which rejected
// (b) as a skolem escape). Fails on a revert to rigid-bare.
#[test]
fn u1_bare_written_param_var_is_flexible_body_may_pin() {
    // (a) a written var the body does not constrain stays polymorphic.
    let mut tc = tc_with_prims();
    let sexps = cranelisp_frontend::parse("(defn id [:a x] x)").expect("parse");
    let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
    tc.check_program_self(&program).unwrap();
    if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("id") {
        assert!(
            !scheme.ty.is_concrete(),
            "id must stay polymorphic (∀a. a→a)"
        );
        assert!(!scheme.type_vars.is_empty(), "id's `a` must be quantified");
    } else {
        panic!("id not found");
    }

    // (b) a body USE that pins the bare var to a concrete type is ACCEPTED,
    //     and the inferred scheme reflects the pin `(Fn [Int] Int)` (row 2).
    let mut tc2 = tc_with_prims();
    let sexps2 = cranelisp_frontend::parse("(defn f [:a x] (add-i64 1 x))").expect("parse");
    let program2 = cranelisp_frontend::build_forms(&sexps2).expect("build_forms");
    tc2.check_program_self(&program2)
        .expect("a bare `:a` pinned by the body MUST be accepted (§3.3.1 MUST (a))");
    let table = tc2.symbol_table();
    let Some(ModuleEntry::Def { scheme, .. }) = table.get("f") else {
        panic!("f not found");
    };
    assert!(
        scheme.ty.is_concrete() && scheme.type_vars.is_empty(),
        "the body pin MUST narrow `a := Int` → concrete `(Fn [Int] Int)`; got {:?}",
        scheme.ty
    );
}

// spec: 03-types §3.3.1 / §3.3.5 row 4 [S109 W6.3] (0588) — a bare written
// param var `:a` and a body VALUE-POSITION annotation `:a "hello"` carrying
// the SAME name CO-REFER within one definition boundary, via the
// `written_var_scope` threaded from `register_defn_signature` into
// `infer_annotate`. The body annotation therefore pins the PARAM to
// `String`: `(defn f [:a x] :a "hello")` → concrete `(Fn [String] String)`,
// and `(f 3)` is a unification error. This is the distinguishing cell of
// 0588 — co-reference held only "when unification incidentally connects
// them" would leave the param as a free `a` here (`(Fn [a] String)`); the
// shared scope makes it `String`. Fails on a revert to per-Annotate fresh
// var maps.
#[test]
fn u1b_bare_param_corefers_body_annotation_pins_param_row4() {
    let mut tc = tc_with_prims();
    let sexps = cranelisp_frontend::parse("(defn f [:a x] :a \"hello\")").expect("parse");
    let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
    tc.check_program_self(&program)
        .expect("a body `:a` annotation co-referring the param `:a` MUST be accepted (row 4)");
    let table = tc.symbol_table();
    let Some(ModuleEntry::Def { scheme, .. }) = table.get("f") else {
        panic!("f not found");
    };
    assert!(
        scheme.type_vars.is_empty(),
        "the param `a` MUST be pinned, not quantified"
    );
    assert_eq!(
        scheme.ty,
        Type::Fn(vec![Type::String], Box::new(Type::String)),
        "param↔body co-reference MUST pin the param to String → `(Fn [String] String)`; got {:?}",
        scheme.ty
    );
}

// spec: 03-types §3.3.2 [S109 W6.3] (U3) — a CONSTRAINT at a parameter
// position (`:C x`) is held ABSTRACT over `C` for the body-check, at the
// program seam. R5 (accepted): `(defn f5 [:Num2 x] (nadd x x))` uses only the
// trait interface → stays constrained-polymorphic. R6 (rejected): `(defn f6
// [:Num2 x] (add-i64 1 x))` narrows the held-abstract var to Int → a skolem
// escape type error (never `unknown type`). This is the 0590-convergence
// guard: the constraint path is the rigid-aware one. Fails on a revert that
// stops seeding `rigid_vars` from asserted-constraint param vars.
#[test]
fn u3_constraint_param_held_abstract_body_narrow_is_skolem_escape() {
    const NUM2: &str = "(deftrait Num2 (nadd [a b] self))\n\
         (impl Num2 Int (defn nadd [a b] (add-i64 a b)))\n";
    // R5 accepted — interface-only use keeps a constrained polymorphic scheme.
    let mut tc = tc_with_prims();
    let sexps =
        cranelisp_frontend::parse(&format!("{NUM2}(defn f5 [:Num2 x] (nadd x x))")).expect("parse");
    let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
    tc.check_program_self(&program)
        .expect("interface-only use of a `:Num2` param MUST be accepted (row 5)");
    let table = tc.symbol_table();
    let Some(ModuleEntry::Def { scheme, .. }) = table.get("f5") else {
        panic!("f5 not found");
    };
    assert!(
        !scheme.constraints.is_empty() && !scheme.type_vars.is_empty(),
        "f5 MUST stay constrained-polymorphic `∀a. Num2 a => (Fn [a] a)`; got {:?} / {:?}",
        scheme.ty,
        scheme.constraints
    );

    // R6 rejected — the body narrows the held-abstract `:Num2` var to Int.
    let mut tc2 = tc_with_prims();
    let sexps2 = cranelisp_frontend::parse(&format!("{NUM2}(defn f6 [:Num2 x] (add-i64 1 x))"))
        .expect("parse");
    let program2 = cranelisp_frontend::build_forms(&sexps2).expect("build_forms");
    let err = tc2
        .check_program_self(&program2)
        .expect_err("a `:Num2` param narrowed to Int by its body MUST be rejected (row 6)");
    let msg = format!("{err:?}");
    assert!(
        !msg.contains("unknown type"),
        "the skolem-escape rejection MUST be a type error, never `unknown type` \
         (§3.3.2 MUST (b)); got: {msg}"
    );
}

// spec: 03-types §3.3.1 × 05-definitions §5.1.2 [S109 W6.3] (U9) — sibling
// multi-arity clauses are DISJOINT lexical scopes: each clause's bare `:a` is
// pinned INDEPENDENTLY by its OWN body (co-reference merges NESTED scopes
// only, never sibling clauses). `(defn h ([:a x] (add-i64 x 1)) ([:a x :Int n]
// (str-concat x x)))` — clause 1 pins `a := Int` → `(Fn [Int] Int)`, clause 2
// pins `a := String` → `(Fn [String Int] String)`; the DIFFERENT pins are the
// clause-independence guard (C-4). The whole defn type-checks (no cross-clause
// skolem-escape from the two different pins).
#[test]
fn u9_multi_arity_clauses_pin_written_var_independently() {
    let mut tc = tc_with_prims();
    let src = "(defn h ([:a x] (add-i64 x 1)) ([:a x :Int n] (str-concat x x)))";
    let sexps = cranelisp_frontend::parse(src).expect("parse");
    let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
    tc.check_program_self(&program).expect(
        "each clause's bare `:a` pinned by its OWN body MUST be accepted \
         (§3.3.1 MUST (a), §5.1.2 clause independence)",
    );
}

// spec: 03-types §3.3.1 [S109 W6.3] (U2) — nested-`fn` lexical CO-REFERENCE
// SURVIVES the W6.3 backout: the enclosing definition's written-var scope
// THREADS into the nested `fn` (`infer_lambda` shares `written_var_scope`), so
// an inner `:a` resolves to the SAME `TypeId` as the enclosing `defn`'s `:a`.
// `(defn g [:a x] (fn [:a y] y))` MUST have scheme `∀a. (Fn [a] (Fn [a] a))` —
// ONE quantified var in all three positions (row 8). Under a SHADOW reading
// the inner `:a` would mint a SECOND var, which this cell rejects (0588).
#[test]
fn u2_nested_fn_written_var_corefers_enclosing_same_typeid() {
    let mut tc = tc_with_prims();
    let sexps = cranelisp_frontend::parse("(defn g [:a x] (fn [:a y] y))").expect("parse");
    let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
    tc.check_program_self(&program).unwrap();

    let table = tc.symbol_table();
    let Some(ModuleEntry::Def { scheme, .. }) = table.get("g") else {
        panic!("g not found");
    };
    // Exactly ONE quantified var — co-reference, not a fresh nested shadow.
    assert_eq!(
        scheme.type_vars.len(),
        1,
        "nested `:a` must CO-REFER (one quantified var), not shadow; got scheme {:?}",
        scheme.ty
    );
    // Structural: (Fn [Var(a)] (Fn [Var(a)] Var(a))) — the SAME TypeId in all
    // three positions.
    let Type::Fn(outer_params, outer_ret) = &scheme.ty else {
        panic!("g scheme is not a Fn: {:?}", scheme.ty);
    };
    let Type::Var(a_outer) = outer_params[0] else {
        panic!("outer param not a Var: {:?}", outer_params[0]);
    };
    let Type::Fn(inner_params, inner_ret) = outer_ret.as_ref() else {
        panic!("g result is not a Fn: {:?}", outer_ret);
    };
    assert_eq!(
        inner_params[0],
        Type::Var(a_outer),
        "inner param must be the outer rigid `a`"
    );
    assert_eq!(
        **inner_ret,
        Type::Var(a_outer),
        "inner result must be the outer rigid `a`"
    );
    assert_eq!(
        scheme.type_vars[0], a_outer,
        "the one quantified var IS `a`"
    );
}

// spec: design/typecheck/check-form-api.md §check_form — single defn Register pass
#[test]
fn test_check_form_single_defn_register() {
    let mut tc = tc_with_prims();
    let module = ModuleFullPath::from("test");
    let mut accumulator = ModuleCheckAccumulator::new();

    let defn = make_inc_defn();
    let form = TopLevel::Defn(defn);
    let result = tc
        .check_form(&module, &form, CheckPass::Register, &mut accumulator)
        .unwrap();

    // Register pass should produce empty method_resolutions and expr_types
    assert!(
        result.method_resolutions.is_empty(),
        "Register pass produces no method resolutions"
    );
    assert!(
        result.expr_types.is_empty(),
        "Register pass produces no expr types"
    );
    assert!(
        result.constrained_fn.is_none(),
        "Register pass has no constrained fn"
    );
    assert!(
        result.mono_defns.is_empty(),
        "Register pass has no mono defns"
    );

    // Signature should be registered in the accumulator's defn_type_vars
    assert!(
        accumulator
            .defn_type_vars
            .contains_key(&Symbol::from("inc")),
        "defn_type_vars should contain 'inc' after Register pass"
    );

    // Signature should be registered in symbol table
    assert!(
        tc.symbol_table().get("inc").is_some(),
        "inc should be in symbol table after Register pass"
    );
}

// spec: design/typecheck/check-form-api.md §check_form — TypeDef Register pass
#[test]
fn test_check_form_typedef_register() {
    let mut tc = tc_with_prims();
    let module = ModuleFullPath::from("test");
    let mut accumulator = ModuleCheckAccumulator::new();

    let form = make_color_typedef();
    let result = tc
        .check_form(&module, &form, CheckPass::Register, &mut accumulator)
        .unwrap();

    // Registration should be mostly empty result (type is registered internally)
    assert!(result.default_method_defns.is_empty());

    // Constructors should be registered in symbol table
    assert!(
        tc.symbol_table().get("Red").is_some(),
        "Red constructor should be in symbol table"
    );
    assert!(
        tc.symbol_table().get("Green").is_some(),
        "Green constructor should be in symbol table"
    );
}

// spec: design/typecheck/check-form-api.md §check_form — TraitDecl Register pass
#[test]
fn test_check_form_trait_decl_register() {
    let mut tc = tc_with_prims();
    let module = ModuleFullPath::from("test");
    let mut accumulator = ModuleCheckAccumulator::new();

    let decl = crate::traits::test_helpers::parse_trait_decl("(deftrait Eq (eq [lhs rhs] Bool))");
    let form = TopLevel::TraitDecl(decl);
    let result = tc
        .check_form(&module, &form, CheckPass::Register, &mut accumulator)
        .unwrap();

    // Should produce an empty result (registration is internal)
    assert!(result.method_resolutions.is_empty());
    assert!(result.expr_types.is_empty());
    assert!(result.default_method_defns.is_empty());
}

// spec: design/typecheck/check-form-api.md §check_form — TraitImpl Register pass
#[test]
fn test_check_form_trait_impl_register() {
    let mut tc = tc_with_prims();
    register_num_trait_inline(&mut tc);
    let module = ModuleFullPath::from("test");
    let mut accumulator = ModuleCheckAccumulator::new();

    // Register a new trait (Eq) then impl it for Int
    let decl = crate::traits::test_helpers::parse_trait_decl("(deftrait Eq (eq [a b] Bool))");
    let decl_form = TopLevel::TraitDecl(decl);
    let _ = tc
        .check_form(&module, &decl_form, CheckPass::Register, &mut accumulator)
        .unwrap();

    // Now impl Eq for Int
    let impl_ = TraitImpl {
        head_con_var: None,
        trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Eq")),
        target: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(
            None,
            TypeName::from("Int"),
        )),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("eq"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("a"), None), (Symbol::from("b"), None)],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("eq-i64"), Span::SYNTHETIC)),
                    args: vec![
                        Expr::var(Symbol::from("a"), Span::SYNTHETIC),
                        Expr::var(Symbol::from("b"), Span::SYNTHETIC),
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
    let impl_form = TopLevel::TraitImpl(impl_);
    let result = tc
        .check_form(&module, &impl_form, CheckPass::Register, &mut accumulator)
        .unwrap();

    // Impl registration should succeed (no error).
    // default_method_defns contains mangled-name defns for each impl method
    // (e.g., "Eq.eq$Int") that need signature registration and body checking.
    assert!(
        !result.default_method_defns.is_empty(),
        "impl should produce mangled method defns for backend compilation"
    );
    // The mangled defn name should follow the pattern Trait.method$Type
    assert!(
        result
            .default_method_defns
            .iter()
            .any(|d| d.name.as_ref().contains("Eq.eq$primitives/Int")),
        "should contain Eq.eq$primitives/Int mangled defn (S102 FQ `$Type` suffix)"
    );
}

// spec: design/typecheck/check-form-api.md §Invariant 1 — CheckBody before Register errors
#[test]
fn test_check_form_check_body_before_register_errors() {
    let mut tc = tc_with_prims();
    let module = ModuleFullPath::from("test");
    let mut accumulator = ModuleCheckAccumulator::new();

    let defn = make_inc_defn();
    let form = TopLevel::Defn(defn);

    // Try CheckBody without registering first — should error
    let result = tc.check_form(&module, &form, CheckPass::CheckBody, &mut accumulator);
    assert!(
        result.is_err(),
        "CheckBody before Register should produce an error"
    );
}

// spec: design/typecheck/check-form-api.md §Invariant 1 — Register populates defn_type_vars
#[test]
fn test_check_form_register_populates_defn_type_vars() {
    let mut tc = tc_with_prims();
    let module = ModuleFullPath::from("test");
    let mut accumulator = ModuleCheckAccumulator::new();

    let defn = make_inc_defn();
    let form = TopLevel::Defn(defn);

    let _ = tc
        .check_form(&module, &form, CheckPass::Register, &mut accumulator)
        .unwrap();

    // defn_type_vars should contain the defn's name with type vars
    let (param_types, _ret_ty) = accumulator
        .defn_type_vars
        .get(&Symbol::from("inc"))
        .expect("inc should be in defn_type_vars");

    // inc has 1 parameter
    assert_eq!(param_types.len(), 1, "inc has 1 parameter");
}

// spec: design/typecheck/check-form-api.md §Invariant 2 — TypeDef before defn using constructors
#[test]
fn test_check_form_typedef_before_defn() {
    let mut tc = tc_with_prims();
    let module = ModuleFullPath::from("test");
    let mut accumulator = ModuleCheckAccumulator::new();

    // Register TypeDef(Color) first
    let typedef_form = make_color_typedef();
    let result = tc
        .check_form(
            &module,
            &typedef_form,
            CheckPass::Register,
            &mut accumulator,
        )
        .unwrap();
    tc.merge_form_result(&module, &mut accumulator, result);

    // Then register Defn(is-red) which uses Color constructors
    let defn_form = TopLevel::Defn(make_is_red_defn());
    let result = tc
        .check_form(&module, &defn_form, CheckPass::Register, &mut accumulator)
        .unwrap();
    tc.merge_form_result(&module, &mut accumulator, result);

    // Pass 2: check body — should resolve constructor types correctly
    // TypeDef is no-op in CheckBody
    let _ = tc
        .check_form(
            &module,
            &typedef_form,
            CheckPass::CheckBody,
            &mut accumulator,
        )
        .unwrap();

    let body_result = tc
        .check_form(&module, &defn_form, CheckPass::CheckBody, &mut accumulator)
        .unwrap();

    // Should succeed and produce expr_types
    assert!(
        !body_result.expr_types.is_empty(),
        "is-red body should have expr_types"
    );
}

// spec: spec/03-types.md §3.9.3 — a stacked trait-bound parameter annotation
//   (`[:Eq :Display a]`) resolves the binder to a FRESH type variable
//   constrained by ALL stacked traits (try-type-then-trait), accumulating
//   both traits onto the defn's generalized `Scheme.constraints`.
//
// This is the TYPECHECK half of defect 0341 (the frontend parse half lands
// separately). Constructed at the typecheck seam — the param annotation is a
// `TypeExpr::Bounds([Eq, Display])` (the shape the frontend will emit), so
// no frontend dependency. (FIXME 0346 carrier; FIXME 0341 typecheck half.)
#[test]
fn stacked_trait_bounds_param_accumulates_constraints() {
    let mut tc = tc_with_prims();
    register_marker_trait(&mut tc, "Eq", "eq?");
    register_marker_trait(&mut tc, "Display", "show");

    // (defn identity [:Eq :Display x] x) — the param `x` carries a run of
    // two stacked trait bounds; the body returns it unchanged so its type
    // stays the constrained binder var.
    let bounds = TypeExpr::Bounds(vec![
        cranelisp_types::TraitRef::new(None, TraitName::from("Eq")),
        cranelisp_types::TraitRef::new(None, TraitName::from("Display")),
    ]);
    let defn = Defn {
        name: Symbol::from("identity"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), Some(bounds))],
            body: Expr::var(Symbol::from("x"), Span::SYNTHETIC),
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };
    let program = vec![TopLevel::Defn(defn)];
    tc.check_program_self(&program)
        .expect("defn with stacked trait-bound param must type-check");

    let scheme = match tc.symbol_table().get("identity") {
        Some(ModuleEntry::Def { scheme, .. }) => scheme.clone(),
        other => panic!("identity not a Def: {other:?}"),
    };

    // The scheme generalizes over the single binder var, and that var
    // carries BOTH trait constraints (Eq AND Display).
    assert_eq!(
        scheme.type_vars.len(),
        1,
        "identity generalizes over its single constrained binder: {scheme:?}",
    );
    let binder = scheme.type_vars[0];
    let constraints = scheme
        .constraints
        .get(&binder)
        .unwrap_or_else(|| panic!("binder var {binder} has no constraints: {scheme:?}"));
    let names: std::collections::HashSet<&str> =
        constraints.iter().map(|t| t.name.as_ref()).collect();
    assert!(
        names.contains("Eq") && names.contains("Display"),
        "binder must be constrained by BOTH Eq and Display, got {names:?} \
         (FIXME 0341 typecheck half)",
    );
    // The function shape is `(Fn [a] a)` over that single binder.
    match &scheme.ty {
        Type::Fn(params, ret) => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0], Type::Var(binder));
            assert_eq!(ret.as_ref(), &Type::Var(binder));
        }
        other => panic!("identity scheme not a fn type: {other:?}"),
    }
}

// spec: spec/03-types.md §3.9.3 — Annotation Resolution (S86 D4). A SINGLE
//   annotation `:Eq a` is ambiguous (could be a concrete type OR a trait).
//   The typechecker first attempts to resolve it as a concrete type; if NO
//   type with that name exists, it resolves as a TRAIT CONSTRAINT
//   (try-type-then-trait). The frontend deliberately leaves a run-of-length-1
//   annotation as the resolved `TypeExpr::Named` (NOT `Bounds`) — see
//   `cranelisp-frontend::ast_builder::annotation_run_carrier` — delegating the
//   disambiguation to this seam. This is the typecheck half of FIXME 0346 /
//   0341 that was missing: before the D4 fix `:Eq a` errored
//   `unknown type \`Eq\` (from module \`\`)` because the `Named` arm only
//   tried type resolution and never fell back to a trait bound.
#[test]
fn single_trait_bound_param_resolves_via_try_type_then_trait() {
    let mut tc = tc_with_prims();
    register_marker_trait(&mut tc, "Eq", "eq?");

    // (defn use-it [:Eq a] a) — `a` carries a SINGLE `:Eq` annotation, which
    // the frontend leaves as `TypeExpr::Named(Eq)`. `Eq` is a trait, not a
    // type, so type resolution fails and the binder must resolve as a trait
    // constraint.
    let single = TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Eq")));
    let defn = Defn {
        name: Symbol::from("use-it"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("a"), Some(single))],
            body: Expr::var(Symbol::from("a"), Span::SYNTHETIC),
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };
    let program = vec![TopLevel::Defn(defn)];
    tc.check_program_self(&program).expect(
        "defn with a single trait-bound param `:Eq a` must type-check via \
         try-type-then-trait (spec §3.9.3, S86 D4)",
    );

    let scheme = match tc.symbol_table().get("use-it") {
        Some(ModuleEntry::Def { scheme, .. }) => scheme.clone(),
        other => panic!("use-it not a Def: {other:?}"),
    };
    // The single binder is generalized and carries the `Eq` constraint.
    assert_eq!(
        scheme.type_vars.len(),
        1,
        "use-it generalizes over its single constrained binder: {scheme:?}",
    );
    let binder = scheme.type_vars[0];
    let constraints = scheme
        .constraints
        .get(&binder)
        .unwrap_or_else(|| panic!("binder var {binder} has no constraints: {scheme:?}"));
    let names: std::collections::HashSet<&str> =
        constraints.iter().map(|t| t.name.as_ref()).collect();
    assert!(
        names.contains("Eq"),
        "binder must be constrained by Eq (single-bound try-type-then-trait), \
         got {names:?} (S86 D4)",
    );
}

// spec: spec/03-types.md §3.9.3 — a single annotation naming a CONCRETE TYPE
//   (`:Int x`) still resolves as a type, NOT a trait (the try-type-then-trait
//   fallback only fires when type resolution fails). Negative guard that the
//   D4 fix does not over-trigger and turn every single annotation into a
//   constrained var.
#[test]
fn single_concrete_type_annotation_stays_concrete_neg() {
    let mut tc = tc_with_prims();
    // (defn id-int [:Int x] x) — `Int` is a real type, so the binder MUST be
    // the concrete `Int`, never a constrained var.
    let int_ann = TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int")));
    let defn = Defn {
        name: Symbol::from("id-int"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), Some(int_ann))],
            body: Expr::var(Symbol::from("x"), Span::SYNTHETIC),
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };
    let program = vec![TopLevel::Defn(defn)];
    tc.check_program_self(&program)
        .expect("defn with concrete `:Int` param must type-check");

    let scheme = match tc.symbol_table().get("id-int") {
        Some(ModuleEntry::Def { scheme, .. }) => scheme.clone(),
        other => panic!("id-int not a Def: {other:?}"),
    };
    // No constrained generalization — the param is the concrete `Int`.
    assert!(
        scheme.constraints.is_empty(),
        "a concrete `:Int` annotation must NOT become a constrained var: {scheme:?}",
    );
    match &scheme.ty {
        Type::Fn(params, _) => assert_eq!(
            params[0],
            Type::Int,
            "param annotated `:Int` must be the concrete Int type, got {:?}",
            params[0],
        ),
        other => panic!("id-int scheme not a fn type: {other:?}"),
    }
}

// spec: spec/03-types.md §3.11.3 / FIXME 0378 issue 3 — a `test-*` fn is
//       registered as a monomorphisation ROOT. The degenerate
//       `(defn test-x [] None)` (type `(Fn [] (Option a))`) is slot-less
//       `Polymorphic`, but the test-fn-root pass mints a concrete
//       `(Fn [] (Option String))` instance UNDER THE BARE NAME with a slot
//       — so discovery (which reads `callable_got_slot()`) still finds it.
#[test]
fn test_fn_registered_as_mono_root_gets_concrete_instance() {
    let mut tc = tc_with_prims();
    let ctx = cf_test_ctx();
    // (deftype Option None (Some [v])) + (defn test-x [] None)
    let test_x = TopLevel::Defn(make_defn(
        "test-x",
        vec![],
        vec![],
        Expr::var(Symbol::from("None"), span(40, 44)),
        Visibility::Public,
        span(38, 45),
    ));
    tc.check(&[option_typedef(), test_x], &ctx, ModuleStrategy::Additive)
        .unwrap();
    let table = tc.symbol_table();
    let entry = table.get("test-x").expect("test-x registered");
    // After the mono-root pass the BARE-name entry is `Concrete{slot}` with
    // a concrete `(Fn [] (Option String))` scheme.
    entry
        .callable_got_slot()
        .expect("test-x must carry a concrete callable slot after mono-root minting");
    match entry {
        ModuleEntry::Def { scheme, kind, .. } => {
            assert!(
                matches!(
                    kind.as_ref(),
                    DefKind::UserFn {
                        fn_state: UserFnState::Concrete { .. }
                    }
                ),
                "test-x must be `Concrete{{slot}}` after mono-root minting, got {kind:?}",
            );
            // Scheme is the concrete `(Fn [] (Option String))`.
            match &scheme.ty {
                Type::Fn(params, ret) => {
                    assert!(params.is_empty(), "test-x is nullary");
                    match ret.as_ref() {
                        Type::ADT(fqtn, args) => {
                            assert_eq!(fqtn.name.as_ref(), "Option");
                            assert_eq!(args.len(), 1);
                            assert!(
                                matches!(args[0], Type::String),
                                "the minted instance pins the result var to \
                                 String — got {:?}",
                                args[0],
                            );
                        }
                        other => panic!("test-x result not (Option …): {other:?}"),
                    }
                }
                other => panic!("test-x scheme not a Fn: {other:?}"),
            }
        }
        other => panic!("test-x entry not a Def: {other:?}"),
    }
}

// TB-24 (§3.2) — a conventional (kind-`*`) trait impl over a POLY-APPLIED
// target `(Box a)` MUST accept: the lowercase con-var `a` binds as a fresh
// type var through the ONE shared type-expr resolver, NOT reject as
// `unknown type a` before the §7.3.5 arity gate (the pre-fix bare-head
// NAMED lookup). `check_src` panics on any check error, so a clean return
// IS the assertion (the impl registers a polymorphic impl over every
// `(Box a)`).
#[test]
fn conventional_impl_poly_applied_target_binds_con_var() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(deftype (Box a) (Box [:a val]))\n\
         (deftrait Disp (dp [x] primitives/Int))\n\
         (impl Disp (Box a) (defn dp [x] 7))",
    );
}

// TB24b (§7.3.3 + §8.5) — an UNKNOWN trait in the impl-target constraint slot
// (`(Box :NoSuchTrait a)`) MUST be rejected. The constraint rides
// `impl_.type_constraints` (typecheck-reachable) but pre-fix was never routed
// through trait resolution → silent-accept. A KNOWN trait (`:Disp`) still
// accepts (the accept fence). `check_program_self` returns Err on the reject.
#[test]
fn impl_target_unknown_trait_constraint_rejected_tb24b() {
    // Known trait in the constraint slot — ACCEPTS.
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(deftype (Box a) (Box [:a val]))\n\
         (deftrait Disp (dp [x] primitives/Int))\n\
         (impl Disp (Box :Disp a) (defn dp [x] 7))",
    );
    // Unknown trait `NoSuchTrait` in the constraint slot — REJECTS.
    let mut tc2 = tc_with_prims();
    let sexps = cranelisp_frontend::parse(
        "(deftype (Box a) (Box [:a val]))\n\
         (deftrait Disp (dp [x] primitives/Int))\n\
         (impl Disp (Box :NoSuchTrait a) (defn dp [x] 7))",
    )
    .expect("parse");
    let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
    let result = tc2.check_program_self(&program);
    assert!(
        result.is_err(),
        "an unknown trait `:NoSuchTrait` in the impl-target constraint slot \
         MUST be rejected (TB24b), not silently accepted; got Ok"
    );
}

// spec: spec/08-modules.md §8.6.6 + S113 0655 — `test/x` in module `test`
// (after §8.6.6 alias substitution) IS the bare `x`; a genuine cross-module
// qualifier and Principle-16 literal `/`-names are left untouched. Direct
// unit of the normalization seam.
#[test]
fn normalize_self_qualified_collapses_current_module_spelling() {
    let tc = tc_with_prims(); // current module = "test"
    // An alias `t -> test` so the alias-spelled current module also collapses
    // (§8.6.6 longest-prefix substitution applied BEFORE the current-module
    // comparison).
    tc.module_aliases.insert(
        ModuleFullPath::from("t"),
        cranelisp_types::ModuleAliasEntry::new(
            ModuleFullPath::from("test"),
            Visibility::Public,
            cranelisp_types::Span::SYNTHETIC,
        ),
    );
    let env = tc.env();
    // Current-module-qualified → bare local.
    assert_eq!(
        env.normalize_self_qualified(&tc.state, "test/qloop"),
        "qloop"
    );
    // Alias-spelled current module → bare local (MC-X3c).
    assert_eq!(env.normalize_self_qualified(&tc.state, "t/qloop"), "qloop");
    // Bare name → unchanged.
    assert_eq!(env.normalize_self_qualified(&tc.state, "qloop"), "qloop");
    // Genuine cross-module qualifier → NOT normalized.
    assert_eq!(
        env.normalize_self_qualified(&tc.state, "other/qloop"),
        "other/qloop"
    );
    // A submodule-child qualifier names `test.util`, NOT the current module —
    // NOT normalized (left for the child-first qualified leg).
    assert_eq!(
        env.normalize_self_qualified(&tc.state, "util/helper"),
        "util/helper"
    );
    // Principle-16 literal `/`-names → unchanged (never a qualified form).
    assert_eq!(env.normalize_self_qualified(&tc.state, "foo/"), "foo/");
    assert_eq!(env.normalize_self_qualified(&tc.state, "/bar"), "/bar");
    assert_eq!(env.normalize_self_qualified(&tc.state, "/"), "/");
}

// spec: spec/08-modules.md §8.6.6 + S113 0655 — the ONE candidate-order source
// both `lookup` and `resolve_ref_target` walk: child-of-current-module BEFORE
// absolute (Principle 7 — the former hand-rolled `resolve_ref_target` mirror
// is retired). Guards the twin collapse.
#[test]
fn qualified_candidate_modules_child_before_absolute() {
    let tc = tc_with_prims(); // current module = "test"
    let env = tc.env();
    let (name_part, [child, abs]) = env
        .qualified_candidate_modules(&tc.state, "util/helper")
        .expect("a two-part qualified name yields candidates");
    assert_eq!(name_part, "helper");
    assert_eq!(
        child,
        ModuleFullPath::from("test.util"),
        "child-of-current first"
    );
    assert_eq!(abs, ModuleFullPath::from("util"), "absolute path second");
    // A bare name / Principle-16 literal has no qualified candidates.
    assert!(
        env.qualified_candidate_modules(&tc.state, "helper")
            .is_none()
    );
    assert!(env.qualified_candidate_modules(&tc.state, "foo/").is_none());
}
