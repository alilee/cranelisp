use super::*;

/// Test helper: create an FQTypeName in a "test" module.
fn test_fqtn(name: &str) -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from("test"), TypeName::from(name))
}

/// Test helper: create an FQTypeName in the "primitives" module.
fn primitives_fqtn(name: &str) -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from(name))
}

// Decision 0047 (FQTypeName binding) cement. `Type::adt` is the one
// constructor inside cranelisp-types that takes a bare `TypeName` and lifts
// it to the fully-qualified `Type::ADT(FQTypeName, _)` form — the single
// place a bare-name leak could originate from within the crate. This test
// pins (a) the module context is preserved (non-empty, == the supplied
// module), and (b) module is load-bearing for identity — same local name in
// different modules produces distinct, unequal ADT types. A regression that
// dropped the module qualification (the FQTypeName leak Decision 0047
// forbids) is caught here. See design/arch/bounded-contexts.md §7.
#[test]
fn test_adt_construction_is_fully_qualified() {
    let ty = Type::adt(
        ModuleFullPath::from("option"),
        TypeName::from("Option"),
        vec![Type::Int],
    );
    match &ty {
        Type::ADT(fq, args) => {
            assert!(!fq.module.is_empty(), "FQTypeName module must be populated");
            assert_eq!(fq.module, "option", "module context must be preserved");
            assert_eq!(fq.name, "Option");
            assert_eq!(args, &vec![Type::Int]);
        }
        other => panic!("Type::adt must produce Type::ADT, got {other:?}"),
    }
}

#[test]
fn test_adt_same_name_different_module_are_distinct() {
    let a = Type::adt(ModuleFullPath::from("foo"), TypeName::from("T"), vec![]);
    let b = Type::adt(ModuleFullPath::from("bar"), TypeName::from("T"), vec![]);
    // Module is load-bearing for identity — a bare-name-only ADT would
    // collapse these to equal, which Decision 0047 forbids.
    assert_ne!(
        a, b,
        "same local name in different modules must not be equal"
    );
}

#[test]
fn test_apply_identity() {
    let subst = Subst::new();
    assert_eq!(apply(&subst, &Type::Int), Type::Int);
}

#[test]
fn test_apply_var_substitution() {
    let mut subst = Subst::new();
    subst.insert(0, Type::Int);
    assert_eq!(apply(&subst, &Type::Var(0)), Type::Int);
}

// FIXME 0279/0295 — defensive cycle guard. A well-formed substitution
// never maps a var to itself; if a pathological self-map `{0 -> Var(0)}`
// is ever constructed, `apply` must NOT recurse forever. In debug builds
// the `debug_assert!` surfaces the occurs-check violation as a panic; in
// release builds the fallthrough keeps it bounded (returns the var).
#[test]
#[cfg_attr(debug_assertions, should_panic(expected = "cyclic substitution"))]
fn test_apply_self_map_does_not_overflow() {
    let mut subst = Subst::new();
    subst.insert(0, Type::Var(0)); // identity self-map
    // Must terminate (panic in debug via the guard; bounded in release).
    let result = apply(&subst, &Type::Var(0));
    // Reached only in release builds — the guard returns the var unchanged.
    assert_eq!(result, Type::Var(0));
}

#[test]
fn test_apply_fn_substitution() {
    let mut subst = Subst::new();
    subst.insert(0, Type::Int);
    let fn_type = Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0)));
    let expected = Type::Fn(vec![Type::Int], Box::new(Type::Int));
    assert_eq!(apply(&subst, &fn_type), expected);
}

#[test]
fn test_free_vars() {
    let ty = Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(1)));
    let fv = free_vars(&ty);
    assert!(fv.contains(&0));
    assert!(fv.contains(&1));
    assert_eq!(fv.len(), 2);
}

#[test]
fn test_free_vars_no_vars() {
    let ty = Type::Fn(vec![Type::Int], Box::new(Type::Bool));
    let fv = free_vars(&ty);
    assert!(fv.is_empty());
}

#[test]
fn test_contains_var_primitive() {
    assert!(!Type::Int.contains_var());
    assert!(!Type::Bool.contains_var());
    assert!(!Type::String.contains_var());
    assert!(!Type::Float.contains_var());
}

#[test]
fn test_contains_var_direct() {
    assert!(Type::Var(0).contains_var());
}

#[test]
fn test_contains_var_nested_fn() {
    let ty = Type::Fn(vec![Type::Int], Box::new(Type::Var(0)));
    assert!(ty.contains_var());

    let ty2 = Type::Fn(vec![Type::Int], Box::new(Type::Bool));
    assert!(!ty2.contains_var());
}

#[test]
fn test_contains_var_nested_adt() {
    let ty = Type::ADT(test_fqtn("Option"), vec![Type::Var(0)]);
    assert!(ty.contains_var());

    let ty2 = Type::ADT(test_fqtn("Option"), vec![Type::Int]);
    assert!(!ty2.contains_var());
}

// Principle 20 / BC §7 "Callability is structural": `is_concrete` is the
// GOT-slot-eligibility predicate. "Concrete" is strictly stronger than
// "unconstrained" — a generic-but-unconstrained type is NOT concrete.
#[test]
fn test_is_concrete_primitive() {
    assert!(Type::Int.is_concrete());
    assert!(Type::Bool.is_concrete());
    assert!(Type::String.is_concrete());
    assert!(Type::Float.is_concrete());
}

#[test]
fn test_is_concrete_var_is_not() {
    // The leak case: a bare type var is not concrete (no slot).
    assert!(!Type::Var(0).is_concrete());
    // ∀a. a→a (the `id` shape): unconstrained, but NOT concrete.
    let id = Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0)));
    assert!(!id.is_concrete());
}

#[test]
fn test_is_concrete_adt_field_var_is_not() {
    // The S84 SIGSEGV shape: a HOF result `(Box a)` carries a Type::Var
    // field — non-concrete, must NOT be slotted.
    let box_a = Type::ADT(test_fqtn("Box"), vec![Type::Var(0)]);
    assert!(!box_a.is_concrete());
    // Its monomorphised instance `(Box Int)` IS concrete (gets a slot).
    let box_int = Type::ADT(test_fqtn("Box"), vec![Type::Int]);
    assert!(box_int.is_concrete());
}

#[test]
fn test_is_concrete_nested_fn() {
    let concrete = Type::Fn(vec![Type::Int, Type::Bool], Box::new(Type::String));
    assert!(concrete.is_concrete());
    let leaky = Type::Fn(vec![Type::Int], Box::new(Type::Var(7)));
    assert!(!leaky.is_concrete());
}

#[test]
fn test_is_concrete_tyconapp_is_not() {
    // A type-constructor application's head is an unresolved HKT var.
    assert!(!Type::TyConApp(0, vec![Type::Int]).is_concrete());
}

#[test]
fn test_is_concrete_is_inverse_of_contains_var_first_order() {
    // For the first-order fragment, is_concrete == !contains_var.
    for ty in [
        Type::Int,
        Type::Fn(vec![Type::Int], Box::new(Type::Bool)),
        Type::Fn(vec![Type::Var(0)], Box::new(Type::Bool)),
        Type::ADT(test_fqtn("Box"), vec![Type::Var(1)]),
    ] {
        assert_eq!(ty.is_concrete(), !ty.contains_var(), "{ty}");
    }
}

#[test]
fn test_display() {
    assert_eq!(format!("{}", Type::Int), "Int");
    let fn_ty = Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int));
    assert_eq!(format!("{fn_ty}"), "(Fn [Int Int] Int)");
    let adt = Type::ADT(test_fqtn("Color"), vec![]);
    assert_eq!(format!("{adt}"), "test/Color");
}

// --- IO type detection ---

// spec: 10-io §10.6.1 — Type::is_io detects IO ADT
#[test]
fn test_is_io_positive() {
    let io_int = Type::ADT(primitives_fqtn("IO"), vec![Type::Int]);
    assert!(io_int.is_io());
}

// spec: 10-io §10.6.1 — Type::is_io rejects non-IO types
#[test]
fn test_is_io_negative() {
    assert!(!Type::Int.is_io());
    assert!(!Type::Bool.is_io());
    let option_int = Type::ADT(test_fqtn("Option"), vec![Type::Int]);
    assert!(!option_int.is_io());
}

// spec: 10-io §10.6.1 — Type::is_io rejects user-defined IO type in wrong module
#[test]
fn test_is_io_wrong_module() {
    let user_io = Type::ADT(test_fqtn("IO"), vec![Type::Int]);
    assert!(!user_io.is_io());
}

// spec: 10-io §10.6.1 — Type::unwrap_io unwraps IO
#[test]
fn test_unwrap_io() {
    let io_int = Type::ADT(primitives_fqtn("IO"), vec![Type::Int]);
    assert_eq!(io_int.unwrap_io(), &Type::Int);

    let io_string = Type::ADT(primitives_fqtn("IO"), vec![Type::String]);
    assert_eq!(io_string.unwrap_io(), &Type::String);
}

// spec: 10-io §10.8 — Type::unwrap_io fallback for non-IO
#[test]
fn test_unwrap_io_no_args() {
    let io_bare = Type::ADT(primitives_fqtn("IO"), vec![]);
    assert_eq!(io_bare.unwrap_io(), &io_bare);
}

// --- U1.6: type variable display name tests ---

/// Helper: render with the lettered (value-display) convention, deriving the
/// var-name map from the type — the behaviour the deleted `format_type_display`
/// free fn provided, now expressed through the shared `render_type` walk.
fn lettered(ty: &Type) -> String {
    let names = type_var_names(ty);
    render_type(ty, PrimitiveNaming::Bare, VarNaming::Lettered(&names))
}

#[test]
fn test_format_type_display_single_var() {
    // A single type variable should display as "a", not "t42".
    let ty = Type::Var(42);
    assert_eq!(lettered(&ty), "a");
}

#[test]
fn test_format_type_display_identity_fn() {
    // (Fn [Var(5)] Var(5)) should display as "(Fn [a] a)".
    let ty = Type::Fn(vec![Type::Var(5)], Box::new(Type::Var(5)));
    assert_eq!(lettered(&ty), "(Fn [a] a)");
}

#[test]
fn test_format_type_display_two_vars() {
    // Two distinct vars should be "a" and "b".
    let ty = Type::Fn(vec![Type::Var(10), Type::Var(20)], Box::new(Type::Var(10)));
    assert_eq!(lettered(&ty), "(Fn [a b] a)");
}

#[test]
fn test_format_type_display_concrete_type() {
    // Concrete types should display normally.
    assert_eq!(lettered(&Type::Int), "Int");
    assert_eq!(lettered(&Type::Bool), "Bool");
}

#[test]
fn test_format_type_display_polymorphic_adt() {
    // (test/Option Var(3)) should display as "(test/Option a)".
    let ty = Type::ADT(test_fqtn("Option"), vec![Type::Var(3)]);
    assert_eq!(lettered(&ty), "(test/Option a)");
}

// --- S87 render_type: the byte-for-byte §2.4 contract guard ---

#[test]
fn render_type_primitive_naming_axis() {
    // spec: design/typecheck/s87-fq-walk-consolidation.md §2.4 — primitive axis.
    for (ty, bare, fq) in [
        (Type::Int, "Int", "primitives/Int"),
        (Type::Bool, "Bool", "primitives/Bool"),
        (Type::String, "String", "primitives/String"),
        (Type::Float, "Float", "primitives/Float"),
    ] {
        assert_eq!(
            render_type(&ty, PrimitiveNaming::Bare, VarNaming::Numbered),
            bare
        );
        assert_eq!(
            render_type(&ty, PrimitiveNaming::Qualified, VarNaming::Numbered),
            fq
        );
    }
}

#[test]
fn render_type_var_naming_axis() {
    // spec: design/typecheck/s87-fq-walk-consolidation.md §2.4 — Var axis.
    let ty = Type::Var(7);
    assert_eq!(
        render_type(&ty, PrimitiveNaming::Bare, VarNaming::Numbered),
        "t7"
    );
    let mut map = std::collections::HashMap::new();
    map.insert(7u32, "a".to_string());
    assert_eq!(
        render_type(&ty, PrimitiveNaming::Bare, VarNaming::Lettered(&map)),
        "a"
    );
    // Absent id falls back to t{id}.
    let empty = std::collections::HashMap::new();
    assert_eq!(
        render_type(&ty, PrimitiveNaming::Bare, VarNaming::Lettered(&empty)),
        "t7"
    );
}

#[test]
fn render_type_tyconapp_four_cells() {
    // spec: design/typecheck/s87-fq-walk-consolidation.md §2.4 — the TyConApp
    // two-shape coupling. Numbered always wraps `(TyCon t{id} …)` incl. empty;
    // Lettered emits bare head, no `TyCon`, no empty parens. (No integration
    // test reliably hits the empty-args `(TyCon t{id})` shape — §4.3.)
    let empty_args = Type::TyConApp(3, vec![]);
    let with_args = Type::TyConApp(3, vec![Type::Int]);

    // Numbered: literal TyCon prefix, parens even when empty.
    assert_eq!(
        render_type(&empty_args, PrimitiveNaming::Bare, VarNaming::Numbered),
        "(TyCon t3)"
    );
    assert_eq!(
        render_type(&with_args, PrimitiveNaming::Bare, VarNaming::Numbered),
        "(TyCon t3 Int)"
    );

    // Lettered: bare head, no TyCon, no empty parens.
    let mut map = std::collections::HashMap::new();
    map.insert(3u32, "f".to_string());
    assert_eq!(
        render_type(
            &empty_args,
            PrimitiveNaming::Bare,
            VarNaming::Lettered(&map)
        ),
        "f"
    );
    assert_eq!(
        render_type(
            &with_args,
            PrimitiveNaming::Qualified,
            VarNaming::Lettered(&map)
        ),
        "(f primitives/Int)"
    );
    // Lettered head fallback to t{id} when absent.
    let empty = std::collections::HashMap::new();
    assert_eq!(
        render_type(
            &empty_args,
            PrimitiveNaming::Bare,
            VarNaming::Lettered(&empty)
        ),
        "t3"
    );
}

#[test]
fn test_type_var_names_ordering() {
    // Variable names assigned in order of first occurrence.
    let ty = Type::Fn(vec![Type::Var(99), Type::Var(50)], Box::new(Type::Var(99)));
    let names = type_var_names(&ty);
    assert_eq!(names.get(&99), Some(&"a".to_string()));
    assert_eq!(names.get(&50), Some(&"b".to_string()));
}

// FIXME 0437: the canonical first-occurrence walk MUST number the `TyConApp`
// head (a type-constructor variable), not only its args, so HKT
// alpha-equivalence / display stays correct.
#[test]
fn test_collect_var_ids_ordered_numbers_tyconapp_head() {
    // (TyCon t7 t3): head 7 is seen first (first occurrence), then arg 3.
    let ty = Type::TyConApp(7, vec![Type::Var(3)]);
    let mut ids = Vec::new();
    collect_var_ids_ordered(&ty, &mut ids);
    assert_eq!(ids, vec![7, 3], "head must be numbered before its args");
}

#[test]
fn test_collect_var_ids_ordered_head_shared_with_var_seen_once() {
    // (Fn [t5] (TyCon t5 t9)): the head id 5 also appears as a `Var` arg; it is
    // numbered once, at its first occurrence (the param), and not re-pushed.
    let ty = Type::Fn(
        vec![Type::Var(5)],
        Box::new(Type::TyConApp(5, vec![Type::Var(9)])),
    );
    let mut ids = Vec::new();
    collect_var_ids_ordered(&ty, &mut ids);
    assert_eq!(ids, vec![5, 9]);
}

#[test]
fn test_type_var_names_assigns_letter_to_tyconapp_head() {
    // The head var becomes nameable like any other var (strict display
    // improvement — pre-0437 the head got no name and fell back to `t{id}`).
    let ty = Type::TyConApp(11, vec![Type::Var(4)]);
    let names = type_var_names(&ty);
    assert_eq!(names.get(&11), Some(&"a".to_string()));
    assert_eq!(names.get(&4), Some(&"b".to_string()));
}
