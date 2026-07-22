//! Per-submodule test module for `registry.rs` — the write-side: a parsed
//! `TraitDecl` becomes symbol-table state (`ActiveConstraints` + per-method
//! `Def`s). Relocated verbatim from the pooled `traits/tests.rs` (S102 FIXME
//! 0497 de-pool), now a sibling of the code it exercises so attribution is
//! structural, per METHOD §2.2 / Principle 23.

use cranelisp_types::{ModuleEntry, Symbol, TraitName, TypeName};

use super::*;
use crate::traits::test_helpers::*;

fn parsed_trait(source: &str) -> TraitDecl {
    let sexps = cranelisp_frontend::parse(source).expect("trait source parses");
    match cranelisp_frontend::build_form(&sexps[0])
        .expect("trait source builds")
        .remove(0)
    {
        cranelisp_types::ParsedEntry::TraitDecl { decl } => decl,
        other => panic!("expected trait declaration, got {other:?}"),
    }
}

// spec: 07-traits §7.1 — a resolvable bare type tail classifies as required.
#[test]
fn classifier_records_required_type_tail() {
    let mut tc = tf_prims();
    tc.register_trait_decl_self(&parsed_trait("(deftrait T (m [x] Int))"))
        .unwrap();
    let decl = tc.lookup_trait_decl(&TraitName::from("T")).unwrap();
    assert!(matches!(
        decl.methods[0].kind,
        TraitMethodKind::Required { .. }
    ));
}

// spec: 07-traits §7.1, §7.1.5 — an ordinary expression tail is a default.
#[test]
fn classifier_records_unannotated_default_body() {
    let mut tc = tf_prims();
    tc.register_trait_decl_self(&parsed_trait("(deftrait T (m [x] x))"))
        .unwrap();
    let decl = tc.lookup_trait_decl(&TraitName::from("T")).unwrap();
    assert!(matches!(
        decl.methods[0].kind,
        TraitMethodKind::Default {
            result_constraint: None,
            ..
        }
    ));
}

// spec: 07-traits §7.1 — an annotated tail bypasses type-tail classification.
#[test]
fn classifier_records_annotated_default_constraint() {
    let mut tc = tf_prims();
    tc.register_trait_decl_self(&parsed_trait("(deftrait T (m [x] :Int 1))"))
        .unwrap();
    let decl = tc.lookup_trait_decl(&TraitName::from("T")).unwrap();
    assert!(matches!(
        decl.methods[0].kind,
        TraitMethodKind::Default {
            result_constraint: Some(_),
            ..
        }
    ));
}

// spec: 07-traits §7.1.1 — a default's bare parameter supplies dispatch.
#[test]
fn default_occurrence_accepts_bare_parameter() {
    let mut tc = tf_prims();
    tc.register_trait_decl_self(&parse_trait_decl("(deftrait T (m [x] x))"))
        .unwrap();
}

// spec: 07-traits §7.1.1 — an annotated default may dispatch by `self` result.
#[test]
fn default_occurrence_accepts_self_result_constraint() {
    let mut tc = tf_prims();
    tc.register_trait_decl_self(&parse_trait_decl(
        "(deftrait T (m [:Int x] :self x))",
    ))
    .unwrap();
}

// spec: 07-traits §7.1.1 — body references do not create dispatch positions.
#[test]
fn default_body_self_reference_does_not_satisfy_occurrence() {
    let mut tc = tf_prims();
    let err = tc
        .register_trait_decl_self(&parse_trait_decl(
            "(deftrait T (m [:Int x] :Bool self))",
        ))
        .unwrap_err();
    assert!(
        err.message().contains("no occurrence of the implementing type"),
        "{err:?}"
    );
    assert!(tc.lookup_trait_decl(&TraitName::from("T")).is_none());
}

// spec: 07-traits §7.1 — an unknown type-looking tail takes the body branch;
// the non-raising recognizer emits no type-expression diagnostic.
#[test]
fn unknown_type_looking_tail_classifies_as_default_body() {
    let mut tc = tf_prims();
    tc.register_trait_decl_self(&parse_trait_decl(
        "(deftrait T (m [x] MissingType))",
    ))
    .unwrap();
    let decl = tc.lookup_trait_decl(&TraitName::from("T")).unwrap();
    assert!(matches!(decl.methods[0].kind, TraitMethodKind::Default { .. }));
}

// spec: 07-traits §7.1 — no traits registered at startup
#[test]
fn test_no_traits_at_startup() {
    let tc = tf();
    // No traits should be discoverable via lookup
    assert!(
        tc.lookup_trait_decl(&TraitName::from("TestTrait"))
            .is_none()
    );
}

// spec: 07-traits §7.3 — no impls registered at startup
#[test]
fn test_no_impls_at_startup() {
    let tc = tf();
    // No impls should be discoverable via has_impl
    assert!(!tc.has_impl(&TraitName::from("Num"), &TypeName::from("Int")));
}

// spec: 03-types §3.6.1 — constraint detection: add and get trait constraints
#[test]
fn test_active_constraints_add_and_get() {
    let mut ac = ActiveConstraints::default();
    ac.add(0, test_fqtn_trait("Num"));
    assert_eq!(ac.get(0).map(|v| v.len()), Some(1));
    assert!(ac.get(1).is_none());
}

// spec: 03-types §3.6.2 — constraint propagation: duplicate adds are idempotent
#[test]
fn test_active_constraints_add_is_idempotent() {
    let mut ac = ActiveConstraints::default();
    ac.add(0, test_fqtn_trait("Num"));
    ac.add(0, test_fqtn_trait("Num"));
    ac.add(0, test_fqtn_trait("Eq"));
    ac.add(0, test_fqtn_trait("Eq"));
    let traits = ac.get(0).unwrap();
    assert_eq!(traits.len(), 2, "duplicate adds should be ignored");
    assert_eq!(traits[0].name.as_ref(), "Num");
    assert_eq!(traits[1].name.as_ref(), "Eq");
}

// spec: 03-types §3.6.2 — collect constraints for specific type variable set
#[test]
fn test_active_constraints_collect_for_vars() {
    let mut ac = ActiveConstraints::default();
    ac.add(0, test_fqtn_trait("Num"));
    ac.add(1, test_fqtn_trait("Eq"));

    let collected = ac.collect_for_vars(&[0, 2]);
    assert!(collected.contains_key(&0));
    assert!(!collected.contains_key(&1));
    assert!(!collected.contains_key(&2));
}

// spec: 03-types §3.6.2 — constraint state can be cleared
#[test]
fn test_active_constraints_clear() {
    let mut ac = ActiveConstraints::default();
    ac.add(0, test_fqtn_trait("Num"));
    ac.clear();
    assert!(ac.constraints.is_empty());
}

// spec: 07-traits §7.1 — deftrait registers trait and methods in symbol table
#[test]
fn test_register_trait_decl() {
    let mut tc = tf_prims();
    let decl = make_test_trait_decl();
    tc.register_trait_decl_self(&decl).unwrap();

    // Trait should be discoverable via SymbolTable lookup
    assert!(
        tc.lookup_trait_decl(&TraitName::from("TestTrait"))
            .is_some()
    );
    // Method should be reverse-mapped via trait_origin on ModuleEntry::Def
    assert_eq!(
        tc.method_to_trait(&Symbol::from("test-op")),
        Some(TraitName::from("TestTrait"))
    );
    // Trait should be in symbol table
    assert!(matches!(
        tc.symbol_table().get("TestTrait"),
        Some(ModuleEntry::TraitDecl { .. })
    ));
}

// spec: 07-traits §7.1 — a genuinely-DIFFERENT redeclaration of the same
// trait name is an error. The conflicting decl shares the name `TestTrait`
// but declares a different method (`other-op` instead of `test-op`), so it
// is NOT the idempotent retry re-submission accommodated below — it must be
// rejected.
#[test]
fn test_register_conflicting_duplicate_trait_fails() {
    let mut tc = tf_prims();
    let decl = make_test_trait_decl();
    tc.register_trait_decl_self(&decl).unwrap();

    // Same name, DIFFERENT method set — a real conflict.
    let mut conflicting = make_test_trait_decl();
    conflicting.methods[0].name = Symbol::from("other-op");
    let err = tc.register_trait_decl_self(&conflicting).unwrap_err();
    assert!(err.message().contains("already defined"));
}

// spec: spec/08-modules.md §8.2 — S86 D3. Re-registering the IDENTICAL trait
// declaration is idempotent (a no-op), NOT an "already defined" error. The
// cluster orchestration retries a module's typecheck from the top with no
// saved resume index when a declared `(mod child)` submodule must load, so a
// trait-defining module's `(deftrait …)` is re-submitted unchanged on the
// retry pass; the registration must absorb the re-submission the same way
// `register_type_def` upserts. Before the D3 fix this errored
// `trait TestTrait already defined`.
#[test]
fn test_register_identical_trait_twice_is_idempotent() {
    let mut tc = tf_prims();
    let decl = make_test_trait_decl();
    tc.register_trait_decl_self(&decl).unwrap();
    // Identical re-submission (the retry-from-top shape) must succeed.
    tc.register_trait_decl_self(&decl)
        .expect("identical re-registration must be idempotent (S86 D3)");
    // The trait is still registered exactly once and resolvable.
    assert!(
        tc.lookup_trait_decl(&TraitName::from("TestTrait"))
            .is_some()
    );
}

// =================== §7.1.1 occurrence rule (S115 W4, FIXME 0709) ============
//
// The registration seam's accept/reject triple. The reject is DECLARATION-TIME
// (Principle 18 — enforced where the malformed form is representable), so the
// downstream `undefined function: zed` codegen leak is closed with no use-site
// work: an unregistered trait has no method to call.

/// A conventional (bare-head) trait `T` with one method `m` of the given
/// parameter list and return type — the occurrence-rule fixture.
fn occurrence_decl(
    trait_name: &str,
    method: &str,
    params: Vec<(Symbol, cranelisp_types::TypeExpr)>,
    ret_type: cranelisp_types::TypeExpr,
) -> cranelisp_types::TraitDecl {
    cranelisp_types::TraitDecl {
        name: TraitName::from(trait_name),
        docstring: None,
        type_params: vec![],
        methods: vec![cranelisp_types::UnresolvedTraitMethodSig {
            name: Symbol::from(method),
            docstring: None,
            params,
            tail: type_expr_sexp(ret_type),
            span: cranelisp_types::Span::SYNTHETIC,
            hkt_param_index: None,
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: cranelisp_types::Span::SYNTHETIC,
    }
}

fn named_ty(n: &str) -> cranelisp_types::TypeExpr {
    cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from(n)))
}

// spec: spec/07-traits.md §7.1.1 — a NULLARY method mentioning the implementing
// type nowhere (`(zed [] Int)`) has nothing to dispatch on and MUST be rejected
// at declaration, with the spec-pinned reason substring.
#[test]
fn occurrence_rule_rejects_nullary_method_with_no_self_occurrence() {
    let mut tc = tf_prims();
    let decl = occurrence_decl("Zeroable", "zed", vec![], named_ty("Int"));
    let err = tc
        .register_trait_decl_self(&decl)
        .expect_err("a nullary no-occurrence method MUST be rejected at declaration");
    assert!(
        err.message()
            .contains("no occurrence of the implementing type"),
        "the diagnostic MUST carry the §7.1.1 reason (never the §7.2.3 \
         'not a type constructor' HK wording); got: {}",
        err.message()
    );
    // The reject fires BEFORE the write — nothing is registered, so the
    // downstream `(zed)` call can never reach codegen (the F-D2 leak's closure).
    assert!(
        tc.lookup_trait_decl(&TraitName::from("Zeroable")).is_none(),
        "a rejected declaration MUST NOT leave a partially-written trait entry"
    );
    assert!(
        tc.symbol_table().get("zed").is_none(),
        "a rejected declaration MUST NOT register its method binding"
    );
}

// spec: spec/07-traits.md §7.1.1 — GREEN boundary (a): `self` in RETURN position
// satisfies the occurrence rule, so the return-type-dispatched form
// `(zed [] self)` stays accepted; its resolution is at USE (§3.3.3 ascription /
// §3.11 ambiguity), never at declaration.
#[test]
fn occurrence_rule_accepts_nullary_self_return_method() {
    let mut tc = tf_prims();
    let decl = occurrence_decl("Zero", "z", vec![], cranelisp_types::TypeExpr::SelfType);
    tc.register_trait_decl_self(&decl)
        .expect("`(z [] self)` satisfies the occurrence rule via its return type");
    assert!(tc.lookup_trait_decl(&TraitName::from("Zero")).is_some());
}

// spec: spec/07-traits.md §7.1.1 — GREEN boundary (b): a BARE parameter is the
// implementing type, so `(size [x] Int)` satisfies the rule even with a concrete
// return. The reject must fire on the CONJUNCTION (no param occurrence ∧ no self
// return), never on "concrete return" alone.
#[test]
fn occurrence_rule_accepts_bare_param_method_with_concrete_return() {
    let mut tc = tf_prims();
    let decl = occurrence_decl(
        "Sizeable",
        "size",
        vec![(Symbol::from("x"), cranelisp_types::TypeExpr::SelfType)],
        named_ty("Int"),
    );
    tc.register_trait_decl_self(&decl)
        .expect("a bare param carries the occurrence — concrete return is fine");
    assert!(tc.lookup_trait_decl(&TraitName::from("Sizeable")).is_some());
}

// spec: spec/07-traits.md §7.1.1 "The occurrence rule is broad, not a nullary
// corner" [S115] — THE RULED SCOPE fence (was the W4 shipped-scope fence for
// FIXME 0770; re-decided by the user's 2026-07-21 ruling, widened at S115 W8).
// The rule is scoped by OCCURRENCE, not by parameter count: `(convert [:String s]
// Int)` mentions the implementing type nowhere — no bare param, no `:self`
// annotation, no `self` return — and is REJECTED on exactly the same ground as
// the nullary `(zed [] Int)`, with the same spec-pinned reason substring. A
// non-empty parameter list does not rescue it: with no explicit-qualification
// call syntax in the language, nothing could ever dispatch it, and accepting it
// only defers the fault to a misleading call-site `no impl of trait …` (0805).
// This cell is the deliberate record of the scope; a future narrowing must
// re-decide it, not silently pass.
#[test]
fn occurrence_rule_rejects_annotated_param_method_with_no_self_occurrence() {
    let mut tc = tf_prims();
    let decl = occurrence_decl(
        "Convertible",
        "convert",
        vec![(Symbol::from("s"), named_ty("String"))],
        named_ty("Int"),
    );
    let err = tc.register_trait_decl_self(&decl).expect_err(
        "the occurrence rule is scoped by OCCURRENCE, not parameter count — an \
         all-annotated non-`self` signature MUST be rejected at any arity (§7.1.1)",
    );
    assert!(
        err.message()
            .contains("no occurrence of the implementing type"),
        "the reject MUST carry the §7.1.1 reason substring at every arity, not \
         only the nullary one; got: {}",
        err.message()
    );
    // Reject-before-write, exactly as in the nullary column: no trait entry and
    // no method binding, so the accepted-impl-then-misleading-call-site leak
    // (0805) is closed at the declaration.
    assert!(
        tc.lookup_trait_decl(&TraitName::from("Convertible"))
            .is_none(),
        "a rejected declaration MUST NOT leave a partially-written trait entry"
    );
    assert!(
        tc.symbol_table().get("convert").is_none(),
        "a rejected declaration MUST NOT register its method binding"
    );
}

// spec: spec/07-traits.md §7.1.1 [S115] — the arity column generalises: a
// TWO-parameter all-annotated signature (`(cvt2 [:String s :Int n] Bool)`, the
// second live-probe shape in FIXME 0805) is rejected identically. Arity is not
// the discriminator; occurrence is.
#[test]
fn occurrence_rule_rejects_multi_annotated_param_method_at_higher_arity() {
    let mut tc = tf_prims();
    let decl = occurrence_decl(
        "Conv2",
        "cvt2",
        vec![
            (Symbol::from("s"), named_ty("String")),
            (Symbol::from("n"), named_ty("Int")),
        ],
        named_ty("Bool"),
    );
    let err = tc
        .register_trait_decl_self(&decl)
        .expect_err("no occurrence at arity 2 MUST be rejected too");
    assert!(
        err.message()
            .contains("no occurrence of the implementing type"),
        "got: {}",
        err.message()
    );
}

// spec: spec/07-traits.md §7.1.1 [S115] "Method-level type variables are
// unaffected" — the widened rule bites ONLY on the ABSENCE of the implementing
// type; it places no restriction on other type variables. A signature mixing a
// method-level type variable with a bare (implementing-type) parameter stays
// ACCEPTED. This is the over-reach guard on the widening: the ruling must not
// take the §7.1.4 method-level-type-variable forms with it.
#[test]
fn occurrence_rule_accepts_method_type_vars_when_self_also_occurs() {
    let mut tc = tf_prims();
    let decl = occurrence_decl(
        "Mappable",
        "map-val",
        vec![
            (
                Symbol::from("f"),
                cranelisp_types::TypeExpr::FnType(
                    vec![cranelisp_types::TypeExpr::TypeVar(Symbol::from("a"))],
                    Box::new(cranelisp_types::TypeExpr::TypeVar(Symbol::from("b"))),
                ),
            ),
            (Symbol::from("x"), cranelisp_types::TypeExpr::SelfType),
        ],
        cranelisp_types::TypeExpr::SelfType,
    );
    tc.register_trait_decl_self(&decl).expect(
        "method-level type variables are legal wherever the implementing type \
         also occurs (§7.1.1 [S115])",
    );
    assert!(tc.lookup_trait_decl(&TraitName::from("Mappable")).is_some());
}

// spec: spec/07-traits.md §7.1.1 — the occurrence may be NESTED: `(Option self)`
// in return position mentions the implementing type ("It may appear in return
// types and in applied type positions"), so the predicate must search the type
// expression tree, not just its head.
#[test]
fn occurrence_rule_accepts_self_nested_in_applied_or_fn_type() {
    // Asserted at the PREDICATE (the applied/`Fn` head types are not in the
    // prims fixture world, so a full registration would fail on type resolution
    // for an unrelated reason and could not discriminate).
    let applied = occurrence_decl(
        "Maybeish",
        "mk",
        vec![],
        cranelisp_types::TypeExpr::Applied(
            cranelisp_types::TypeRef::new(None, TypeName::from("Option")),
            vec![cranelisp_types::TypeExpr::SelfType],
        ),
    );
    assert!(
        method_mentions_self(&applied.methods[0]),
        "`(Option self)` in return position is an occurrence"
    );
    let fn_ty = occurrence_decl(
        "Mapper",
        "mk",
        vec![(
            Symbol::from("f"),
            cranelisp_types::TypeExpr::FnType(
                vec![cranelisp_types::TypeExpr::SelfType],
                Box::new(named_ty("Int")),
            ),
        )],
        named_ty("Int"),
    );
    assert!(
        method_mentions_self(&fn_ty.methods[0]),
        "`:(Fn [self] Int)` in parameter position is an occurrence"
    );
    // NEGATIVE: nothing anywhere in the tree.
    let none = occurrence_decl("Nope", "n", vec![], named_ty("Int"));
    assert!(
        !method_mentions_self(&none.methods[0]),
        "a signature with no `self` anywhere has no occurrence"
    );
}

// spec: 03-types §3.4.1 — trait method scheme carries trait constraint
#[test]
fn test_trait_method_has_constrained_scheme() {
    let mut tc = tf_prims();
    let decl = make_test_trait_decl();
    tc.register_trait_decl_self(&decl).unwrap();

    if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("test-op") {
        assert_eq!(
            scheme.type_vars.len(),
            1,
            "test-op should have 1 quantified var"
        );
        assert!(
            !scheme.constraints.is_empty(),
            "test-op should have TestTrait constraint"
        );
        let var_id = scheme.type_vars[0];
        let traits = scheme.constraints.get(&var_id).unwrap();
        assert_eq!(traits.len(), 1);
        assert_eq!(traits[0].name.as_ref(), "TestTrait");
    } else {
        panic!("test-op should be registered");
    }
}

// spec: pipeline-orchestration §5 — no core traits at startup (Decision 17 eliminated)
#[test]
fn test_no_core_traits_at_startup() {
    let tc = tf();
    // Traits come from prelude .cl files, NOT compiler builtins.
    // No traits should be discoverable via SymbolTable lookup.
    assert!(
        tc.lookup_trait_decl(&TraitName::from("Num")).is_none(),
        "no traits should be registered at startup"
    );
    assert!(
        !tc.has_impl(&TraitName::from("Num"), &TypeName::from("Int")),
        "no impls should be registered at startup"
    );
}

// spec: pipeline-orchestration §5 — operator symbols NOT in symbol table at startup
#[test]
fn test_no_operators_at_startup() {
    let tc = tf();
    let ops = ["+", "-", "*", "/", "=", "!=", "<", ">", "<=", ">="];
    for op in ops {
        assert!(
            tc.symbol_table().get(op).is_none(),
            "operator {op} should NOT be in symbol table at startup"
        );
    }
}

// ---------------------------------------------------------------------------
// S112 — kind derived ONCE at declaration; the never-applied `(X a)` head is a
// declaration-time reject (spec §7.1/§7.2.1; `design/typecheck/hkt.md` §5.1).
// ---------------------------------------------------------------------------

use cranelisp_types::{Span, TraitDecl, TypeExpr, TypeRef};

/// `(deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))` — a
/// genuinely higher-kinded trait: the con_var `f` is APPLIED in the method sig.
fn functor_decl() -> TraitDecl {
    TraitDecl {
        name: TraitName::from("Functor"),
        docstring: None,
        type_params: vec![Symbol::from("f")],
        methods: vec![cranelisp_types::UnresolvedTraitMethodSig {
            name: Symbol::from("fmap"),
            docstring: None,
            params: vec![
                (
                    Symbol::from("func"),
                    TypeExpr::FnType(
                        vec![TypeExpr::TypeVar(Symbol::from("a"))],
                        Box::new(TypeExpr::TypeVar(Symbol::from("b"))),
                    ),
                ),
                (
                    Symbol::from("x"),
                    TypeExpr::Applied(
                        TypeRef::new(None, TypeName::from("f")),
                        vec![TypeExpr::TypeVar(Symbol::from("a"))],
                    ),
                ),
            ],
            tail: type_expr_sexp(TypeExpr::Applied(
                TypeRef::new(None, TypeName::from("f")),
                vec![TypeExpr::TypeVar(Symbol::from("b"))],
            )),
            span: Span::SYNTHETIC,
            hkt_param_index: None,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    }
}

// spec: 07-traits §7.1/§7.2.1 — NEGATIVE. A parenthesized head whose con_var is
// NEVER applied is malformed and rejected AT `deftrait` (declaration time), not
// at impl time. `(deftrait (Zeroable a) (zed [] :a))` — `a` bare in the return,
// never `(a …)`. The diagnostic names the con_var and points at the bare-head +
// `self` fix.
#[test]
fn deftrait_never_applied_head_var_rejected_at_declaration() {
    let mut tc = tf_prims();
    let decl = TraitDecl {
        name: TraitName::from("Zeroable"),
        docstring: None,
        type_params: vec![Symbol::from("a")],
        methods: vec![cranelisp_types::UnresolvedTraitMethodSig {
            name: Symbol::from("zed"),
            docstring: None,
            params: vec![],
            tail: type_expr_sexp(TypeExpr::TypeVar(Symbol::from("a"))), // bare `a`, never applied
            span: Span::SYNTHETIC,
            hkt_param_index: None,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };
    let err = tc
        .register_trait_decl_self(&decl)
        .expect_err("a never-applied `(Zeroable a)` head is malformed (§7.2.1)");
    let msg = err.message();
    assert!(
        msg.contains("Zeroable"),
        "diagnostic names the trait: {msg}"
    );
    assert!(msg.contains('a'), "diagnostic names the con_var: {msg}");
    assert!(
        msg.contains("self"),
        "diagnostic points at the bare-head + self fix: {msg}"
    );
    // And nothing registered.
    assert!(tc.lookup_trait_decl(&TraitName::from("Zeroable")).is_none());
}

// spec: 07-traits §7.2 — POSITIVE (kind-derivation collapse, HKT side). A trait
// whose con_var IS applied `(f a)` registers via the HKT path — `register_hkt_trait`
// sets `hkt_param_index: Some(_)` on the stored method sig, the observable that
// the declaration-derived kind routed correctly (no usage re-scan downstream).
#[test]
fn deftrait_applied_con_var_registers_as_hkt() {
    let mut tc = tf_prims();
    tc.register_trait_decl_self(&functor_decl())
        .expect("an applied-con_var trait is genuinely HKT and must register");
    let info = tc
        .lookup_trait_decl(&TraitName::from("Functor"))
        .expect("Functor registered");
    assert_eq!(
        info.type_params,
        vec![Symbol::from("f")],
        "HKT: non-empty type_params"
    );
    assert_eq!(
        info.methods[0].hkt_param_index,
        Some(1),
        "register_hkt_trait set the dispatch param index (x at idx 1)"
    );
}

// spec: 07-traits §7.1 — POSITIVE (kind-derivation collapse, conventional side).
// A bare-head `self` trait registers via the conventional path and NEVER routes
// to `register_hkt_trait` — empty `type_params`, `hkt_param_index: None`.
#[test]
fn deftrait_bare_head_registers_conventional_not_hkt() {
    let mut tc = tf_prims();
    tc.register_trait_decl_self(&make_nullary_return_poly_trait_decl())
        .expect("a bare-head self trait registers conventionally");
    let info = tc
        .lookup_trait_decl(&TraitName::from("NullaryRP"))
        .expect("NullaryRP registered");
    assert!(
        info.type_params.is_empty(),
        "conventional: empty type_params"
    );
    assert_eq!(
        info.methods[0].hkt_param_index, None,
        "the conventional path never sets hkt_param_index"
    );
}
