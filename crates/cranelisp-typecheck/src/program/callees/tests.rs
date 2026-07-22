//! Per-submodule tests for `program/callees.rs` — the S101 `Def.callees`
//! completeness contract (`crates/cranelisp-typecheck/CLAUDE.md`, FIXME
//! 0470/0472): every statically-resolved user-fn reference, call- AND
//! value-position, at every body-check seam. Split from the pooled
//! `program/tests.rs` (FIXME 0722).

use super::*;

use crate::program::test_support::*;



// spec: tests/plan/s101-coverage-postmortem.md §2.1 item 1(a) — a plain
//   fully-applied direct call to a single-sig concrete user fn records the
//   caller→callee edge (the 0470 headline gap: this was EMPTY before).
#[test]
fn callees_records_direct_call_to_user_fn() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn callee [:primitives/Int x] :primitives/Int x)\n\
         (defn c [:primitives/Int x] :primitives/Int (callee x))",
    );
    assert!(
        callees_of(&tc, "test", "c").contains(&fq_sym("test", "callee")),
        "direct call must record the callee edge; got {:?}",
        callees_of(&tc, "test", "c"),
    );
}

// spec: tests/plan/s101-coverage-postmortem.md §2.1 item 1(b) — a user fn
//   passed as a HOF argument (value position) records the edge; the HOF
//   call itself also records its (call-position) edge.
#[test]
fn callees_records_fn_as_value_hof_argument() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn callee [:primitives/Int x] :primitives/Int x)\n\
         (defn hof [f :primitives/Int x] :primitives/Int (f x))\n\
         (defn c [:primitives/Int x] :primitives/Int (hof callee x))",
    );
    let edges = callees_of(&tc, "test", "c");
    assert!(
        edges.contains(&fq_sym("test", "callee")),
        "fn-as-value HOF argument must record the callee edge; got {edges:?}",
    );
    assert!(
        edges.contains(&fq_sym("test", "hof")),
        "the HOF call itself must record a call-position edge; got {edges:?}",
    );
}

// spec: tests/plan/s101-coverage-postmortem.md §2.1 item 1(c) — a user fn
//   returned as a bare value records the edge.
#[test]
fn callees_records_fn_as_value_returned() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn callee [:primitives/Int x] :primitives/Int x)\n\
         (defn c [] callee)",
    );
    assert!(
        callees_of(&tc, "test", "c").contains(&fq_sym("test", "callee")),
        "returned fn-as-value must record the callee edge; got {:?}",
        callees_of(&tc, "test", "c"),
    );
}

// spec: tests/plan/s101-coverage-postmortem.md §2.1 item 1(d) — a user fn
//   stored in a container literal records the edge.
#[test]
fn callees_records_fn_as_value_stored_in_container() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn callee [:primitives/Int x] :primitives/Int x)\n\
         (defn c [] [callee])",
    );
    assert!(
        callees_of(&tc, "test", "c").contains(&fq_sym("test", "callee")),
        "container-stored fn-as-value must record the callee edge; got {:?}",
        callees_of(&tc, "test", "c"),
    );
}

// spec: tests/plan/s101-coverage-postmortem.md §2.1 item 1(e) — a curried
//   partial application records the edge to the curried target.
#[test]
fn callees_records_curried_partial_application() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn callee2 [:primitives/Int a :primitives/Int b] :primitives/Int (add-i64 a b))\n\
         (defn c [:primitives/Int x] :primitives/Int ((callee2 x) x))",
    );
    assert!(
        callees_of(&tc, "test", "c").contains(&fq_sym("test", "callee2")),
        "curried partial application must record the target edge; got {:?}",
        callees_of(&tc, "test", "c"),
    );
}

// spec: tests/plan/s101-coverage-postmortem.md §2.1 item 1(f) — a reference
//   inside a nested lambda attributes the edge to the ENCLOSING defn (the
//   L-R2 carrier shape).
#[test]
fn callees_records_reference_inside_nested_lambda() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn callee [:primitives/Int x] :primitives/Int x)\n\
         (defn c [] (fn [x] (callee x)))",
    );
    assert!(
        callees_of(&tc, "test", "c").contains(&fq_sym("test", "callee")),
        "a nested-lambda reference must attribute the edge to the enclosing \
         defn; got {:?}",
        callees_of(&tc, "test", "c"),
    );
}

// spec: tests/plan/s101-coverage-postmortem.md §2.1 item 1(g) — a
//   qualified cross-module reference records the edge with the DEFINING
//   module's FQ identity.
#[test]
fn callees_records_qualified_cross_module_reference() {
    let mut tc = tc_with_prims();
    let util = ModuleFullPath::from("util");
    tc.set_current_module(util.clone());
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    check_src(
        &mut tc,
        "(defn ucallee [:primitives/Int x] :primitives/Int x)",
    );
    tc.set_current_module(ModuleFullPath::from("test"));
    check_src(
        &mut tc,
        "(defn c [:primitives/Int x] :primitives/Int (util/ucallee x))",
    );
    assert!(
        callees_of(&tc, "test", "c").contains(&fq_sym("util", "ucallee")),
        "qualified cross-module call must record the (util, ucallee) edge; \
         got {:?}",
        callees_of(&tc, "test", "c"),
    );
}

// spec: tests/plan/s101-coverage-postmortem.md §2.1 item 1(g) (companion) —
//   an IMPORTED bare-name reference chain-follows to the defining module:
//   the edge is (util, ucallee), NOT (test, ucallee).
#[test]
fn callees_records_imported_bare_name_at_home_module() {
    let mut tc = tc_with_prims();
    let util = ModuleFullPath::from("util");
    tc.set_current_module(util.clone());
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    check_src(
        &mut tc,
        "(defn ucallee [:primitives/Int x] :primitives/Int x)",
    );
    tc.set_current_module(ModuleFullPath::from("test"));
    seed_specific_import(&mut tc, &util, &["ucallee"]);
    check_src(
        &mut tc,
        "(defn c [:primitives/Int x] :primitives/Int (ucallee x))",
    );
    let edges = callees_of(&tc, "test", "c");
    assert!(
        edges.contains(&fq_sym("util", "ucallee")),
        "imported bare-name call must chain-follow to the HOME module; \
         got {edges:?}",
    );
    assert!(
        !edges.contains(&fq_sym("test", "ucallee")),
        "the edge must NOT be recorded against the importing module; \
         got {edges:?}",
    );
}

// spec: design/typecheck/ownership-inference.md §15.5 (FIXME 0621) — a
//   RENAMED import `[lib [foo as bar]]` records the callees edge under the
//   SOURCE storage key `lib/foo` (`resolved.storage_fq()`), NOT the written
//   alias `lib/bar` (`resolved.fq`, composed from the alias spelling — no
//   such entry exists). Same storage-key discipline the `var_refs`
//   (S114 carrier flip — was `resolved_targets`) carrier already uses; both
//   feeds now agree by the schema-20 flip.
#[test]
fn callees_records_renamed_import_by_storage_key() {
    let mut tc = tc_with_prims();
    // `foo` (0-arg user fn) lives in module `lib`.
    tc.set_current_module(ModuleFullPath::from("lib"));
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    check_src(&mut tc, "(defn foo [] 0)");
    // Back in `test`: import `foo` RENAMED to `bar`, then call `(bar)`.
    tc.set_current_module(ModuleFullPath::from("test"));
    tc.symbol_table_mut().insert(
        Symbol::from("bar"),
        ModuleEntry::Import {
            source: FQSymbol {
                module: ModuleFullPath::from("lib"),
                symbol: Symbol::from("foo"),
            },
            visibility: Visibility::Public,
        },
    );
    check_src(&mut tc, "(defn use-bar [] (bar))");
    let edges = callees_of(&tc, "test", "use-bar");
    assert!(
        edges.contains(&fq_sym("lib", "foo")),
        "renamed-import call must record the SOURCE storage key lib/foo; got {edges:?}",
    );
    assert!(
        !edges.contains(&fq_sym("lib", "bar")) && !edges.contains(&fq_sym("test", "bar")),
        "the callees edge must NOT be the written alias `bar`; got {edges:?}",
    );
}

// spec: tests/plan/s101-coverage-postmortem.md §2.1 item 2(a) — a SHADOWED
//   name (fn param, let binding) records NO edge to the same-named
//   module-level fn.
#[test]
fn callees_neg_shadowed_name_records_no_edge() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn callee [:primitives/Int x] :primitives/Int x)\n\
         (defn c [callee :primitives/Int x] :primitives/Int (callee x))\n\
         (defn c2 [:primitives/Int x] :primitives/Int\n\
           (let [callee (fn [y] (add-i64 y 0))] (callee x)))",
    );
    assert!(
        !callees_of(&tc, "test", "c")
            .contains(&fq_sym("test", "callee")),
        "a param-shadowed name must record no module edge; got {:?}",
        callees_of(&tc, "test", "c"),
    );
    assert!(
        !callees_of(&tc, "test", "c2")
            .contains(&fq_sym("test", "callee")),
        "a let-shadowed name must record no module edge; got {:?}",
        callees_of(&tc, "test", "c2"),
    );
}

// spec: tests/plan/s101-coverage-postmortem.md §2.1 item 2(b) — primitives
//   and special forms record NO user-fn edge (BuiltinFn deliberately
//   skipped: always available, no codegen dependency).
#[test]
fn callees_neg_primitives_and_special_forms_record_no_edge() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn c [:primitives/Int x] :primitives/Int\n\
           (if (lt-i64 x 1) (add-i64 x x) x))",
    );
    assert!(
        callees_of(&tc, "test", "c").is_empty(),
        "primitive calls + special forms must record no edges; got {:?}",
        callees_of(&tc, "test", "c"),
    );
}

// spec: tests/plan/s101-coverage-postmortem.md §2.1 item 2(b)/(c) — a
//   non-UserFn `Def` kind records no edge. Probed with a Constructor (the
//   constructible case); the same `DefKind::UserFn` gate excludes
//   `DefKind::Macro` entries — macro USES never reach typecheck (expanded
//   upstream), so macro edges ride their own channel (save.rs macro
//   partition), and a macro name can never enter `callees` here.
#[test]
fn callees_neg_constructor_reference_records_no_edge() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(deftype Box [:primitives/Int v])\n\
         (defn c [] (Box 1))",
    );
    assert!(
        !callees_of(&tc, "test", "c")
            .iter()
            .any(|e| e.symbol.as_ref() == "Box"),
        "a constructor reference must record no user-fn edge; got {:?}",
        callees_of(&tc, "test", "c"),
    );
}

// spec: tests/plan/s101-coverage-postmortem.md §2.1 item 2(d) — unrelated
//   fns sharing a module record no edge to each other (the L-R3(b)
//   exactness negative at the unit grain).
#[test]
fn callees_neg_unrelated_siblings_record_no_edges() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn a [:primitives/Int x] :primitives/Int x)\n\
         (defn b [:primitives/Int x] :primitives/Int (add-i64 x 1))",
    );
    assert!(
        callees_of(&tc, "test", "a").is_empty(),
        "unrelated `a` must have no edges; got {:?}",
        callees_of(&tc, "test", "a"),
    );
    assert!(
        callees_of(&tc, "test", "b").is_empty(),
        "unrelated `b` must have no edges; got {:?}",
        callees_of(&tc, "test", "b"),
    );
}

// spec: tests/plan/s101-coverage-postmortem.md §2.1 item 3 — uniformity:
//   call-position and value-position references record the SAME
//   `Vec<FQSymbol>` carrier; consumers cannot distinguish them
//   (design/int/session-transaction.md §3.2 — sound at stage M because
//   every ABI change is a type change, which breaks value uses too).
#[test]
fn callees_uniform_carrier_for_call_and_value_position() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn callee [:primitives/Int x] :primitives/Int x)\n\
         (defn call-pos [:primitives/Int x] :primitives/Int (callee x))\n\
         (defn value-pos [] callee)",
    );
    assert_eq!(
        callees_of(&tc, "test", "call-pos"),
        callees_of(&tc, "test", "value-pos"),
        "call-position and value-position edges must be indistinguishable \
         in the carrier",
    );
    assert_eq!(
        callees_of(&tc, "test", "call-pos"),
        vec![fq_sym("test", "callee")],
    );
}

// spec: design/arch/fixmes/0472 + tests/plan/s101-coverage-postmortem.md
//   §2.1 (impl-method-caller row) — a trait-impl method body checked at the
//   Pass-1 seam (`check_impl_method`, outside the Pass-2 per-form delta)
//   must STILL record its statically-resolved user-fn references on the
//   mangled entry. Before the cure: `Sizey.bump$Int/Def.callees = []`
//   (the recorder fired but every Pass-2 snapshot preceded its spans).
#[test]
fn callees_records_impl_method_body_reference() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn helper [:primitives/Int x] :primitives/Int x)",
    );

    // (deftrait Sizey [a] (defn bump [self] Int))
    let decl = crate::traits::test_helpers::parse_trait_decl(
        "(deftrait Sizey (bump [self] Int))",
    );
    tc.register_trait_decl_self(&decl).unwrap();

    // (impl Sizey Int (defn bump [a] (helper a))) — the body calls the
    // module-level user fn `helper`. Distinct spans: the recorder is
    // span-keyed, so synthetic-span collisions would mask the reference.
    let impl_ = TraitImpl {
        head_con_var: None,
        trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Sizey")),
        target: TypeExpr::Named(cranelisp_types::TypeRef::new(
            None,
            TypeName::from("Int"),
        )),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("bump"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("a"), None)],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(
                        Symbol::from("helper"),
                        Span::new(900, 906),
                    )),
                    args: vec![Expr::var(Symbol::from("a"), Span::new(907, 908))],
                    span: Span::new(899, 909),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::new(890, 910),
            }],
            visibility: Visibility::Public,
            span: Span::new(890, 910),
        }],
        span: Span::new(880, 911),
    };
    tc.register_trait_impl_self(&impl_).unwrap();

    let edges = callees_of(&tc, "test", "Sizey.bump$primitives/Int");
    assert!(
        edges.contains(&fq_sym("test", "helper")),
        "an impl-method body reference must record the edge on the \
         mangled entry (FIXME 0472); got {edges:?}",
    );
}

// spec: design/arch/fixmes/0472 — the DEFAULT-method seam shares the
//   impl-method writeback; a synthesized default body (checked under the
//   trait's DEFINING module, D1/S86) records its user-fn references on
//   the mangled entry, with the FQ resolved in the trait-home context.
#[test]
fn callees_records_default_method_body_reference() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn dhelper [:primitives/Int x] :primitives/Int x)",
    );

    // (deftrait Doubly [a]
    //   (defn req [self] Self)
    //   (defn dbl [a] Int (dhelper a)))   ; default body calls dhelper
    let decl = crate::traits::test_helpers::parse_trait_decl(
        "(deftrait Doubly (req [self] self) (dbl [a] :Int (dhelper a)))",
    );
    tc.register_trait_decl_self(&decl).unwrap();

    // (impl Doubly Int (defn req [a] a)) — omits `dbl`, forcing default
    // synthesis + body check through the same writeback seam.
    let impl_ = TraitImpl {
        head_con_var: None,
        trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Doubly")),
        target: TypeExpr::Named(cranelisp_types::TypeRef::new(
            None,
            TypeName::from("Int"),
        )),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("req"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("a"), None)],
                body: Expr::var(Symbol::from("a"), Span::new(940, 941)),
                span: Span::new(935, 942),
            }],
            visibility: Visibility::Public,
            span: Span::new(935, 942),
        }],
        span: Span::new(930, 943),
    };
    tc.register_trait_impl_self(&impl_).unwrap();

    let edges = callees_of(&tc, "test", "Doubly.dbl$primitives/Int");
    assert!(
        edges.contains(&fq_sym("test", "dhelper")),
        "a default-method body reference must record the edge on the \
         mangled entry (FIXME 0472, same writeback seam); got {edges:?}",
    );
}

// spec: tests/plan/s101-coverage-postmortem.md §2.1 item 1(e)/(g) (F4
//   sibling, /review S101) — a curried partial application of an IMPORTED
//   fn records the recorder's HOME-module edge. Pins the dual-channel
//   cover: the AutoCurry `ResolvedCall` channel stamps `current_module`
//   (the pre-existing Step-5 approximation), so the recorder's
//   chain-followed home edge is what makes the reverse index reach the
//   defining module.
#[test]
fn callees_records_cross_module_curried_imported_fn_at_home() {
    let mut tc = tc_with_prims();
    let util = ModuleFullPath::from("util");
    tc.set_current_module(util.clone());
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    check_src(
        &mut tc,
        "(defn ucallee2 [:primitives/Int a :primitives/Int b] :primitives/Int (add-i64 a b))",
    );
    tc.set_current_module(ModuleFullPath::from("test"));
    seed_specific_import(&mut tc, &util, &["ucallee2"]);
    check_src(
        &mut tc,
        "(defn c [:primitives/Int x] :primitives/Int ((ucallee2 x) x))",
    );
    let edges = callees_of(&tc, "test", "c");
    assert!(
        edges.contains(&fq_sym("util", "ucallee2")),
        "curried imported fn must record the recorder's home-module edge; \
         got {edges:?}",
    );
}

// Self-edge disposition (FIXME 0470: "may be recorded or skipped — pick
// whichever is cheaper and document it"). SKIPPED is the structural
// outcome and the cheap choice: `check_defn_body` binds the recursion
// name as a LOCAL (`mono(fn_type)`), so the local-shadow gate in
// `record_user_fn_ref` never sees a module reference — zero extra checks.
// The transaction's SCC condensation is indifferent, and
// `save.rs::dependency_sort` filters self-edges anyway.
// spec: design/int/session-transaction.md §3.2
#[test]
fn callees_skips_recursive_self_edge() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn r [:primitives/Int x] :primitives/Int\n\
           (if (lt-i64 x 1) x (r (sub-i64 x 1))))",
    );
    assert!(
        !callees_of(&tc, "test", "r").contains(&fq_sym("test", "r")),
        "recursion records NO self-edge (documented disposition: the \
         recursion name is a local binding); got {:?}",
        callees_of(&tc, "test", "r"),
    );
}

// =====================================================================
// FIXME 0488 — generic-fn missing monomorphisation (typecheck-side)
// Unit shapes per `tests/plan/0488-isolation.md` §"Unit-test shapes".
// =====================================================================
