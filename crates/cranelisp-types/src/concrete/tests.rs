use super::*;
use crate::{ModuleFullPath, TypeName};

fn opt(arg: Type) -> Type {
    Type::adt(
        ModuleFullPath::from("primitives"),
        TypeName::from("Option"),
        vec![arg],
    )
}

#[test]
fn scalars_convert() {
    for (ty, ct) in [
        (Type::Int, ConcreteType::Int),
        (Type::Bool, ConcreteType::Bool),
        (Type::String, ConcreteType::String),
        (Type::Float, ConcreteType::Float),
    ] {
        assert_eq!(ConcreteType::from_type(&ty), Ok(ct.clone()));
        assert_eq!(ct.to_type(), ty);
    }
}

#[test]
fn bare_var_is_not_concrete() {
    assert_eq!(
        ConcreteType::from_type(&Type::Var(7)),
        Err(NotConcrete::Var(7))
    );
}

#[test]
fn tyconapp_head_is_not_concrete() {
    assert_eq!(
        ConcreteType::from_type(&Type::TyConApp(3, vec![Type::Int])),
        Err(NotConcrete::HktHead(3))
    );
}

#[test]
fn concrete_adt_converts_and_round_trips() {
    let ty = opt(Type::Int);
    let ct = ConcreteType::from_type(&ty).expect("concrete");
    assert!(matches!(ct, ConcreteType::ADT(_, ref args) if args == &vec![ConcreteType::Int]));
    assert_eq!(ct.to_type(), ty);
}

#[test]
fn adt_with_free_var_arg_is_not_concrete() {
    // (Option a) — the var rides in the arg, the FIXME-0379 `Mixed`-family case.
    assert_eq!(
        ConcreteType::from_type(&opt(Type::Var(0))),
        Err(NotConcrete::Var(0))
    );
}

#[test]
fn fn_with_var_param_is_not_concrete() {
    let ty = Type::Fn(vec![Type::Var(1)], Box::new(Type::Int));
    assert_eq!(ConcreteType::from_type(&ty), Err(NotConcrete::Var(1)));
}

#[test]
fn fn_with_var_return_is_not_concrete() {
    let ty = Type::Fn(vec![Type::Int], Box::new(Type::Var(2)));
    assert_eq!(ConcreteType::from_type(&ty), Err(NotConcrete::Var(2)));
}

#[test]
fn nested_concrete_fn_round_trips() {
    // (Fn [Int (Option Bool)] String) — concrete at every depth.
    let ty = Type::Fn(vec![Type::Int, opt(Type::Bool)], Box::new(Type::String));
    let ct = ConcreteType::from_type(&ty).expect("concrete");
    assert_eq!(ct.to_type(), ty);
}

#[test]
fn deeply_nested_var_is_caught() {
    // (Fn [Int] (Option (Option a))) — the var is two levels deep.
    let ty = Type::Fn(vec![Type::Int], Box::new(opt(opt(Type::Var(9)))));
    assert_eq!(ConcreteType::from_type(&ty), Err(NotConcrete::Var(9)));
}

#[test]
fn from_type_agrees_with_is_concrete() {
    // The conversion succeeds iff `Type::is_concrete()` — the two predicates
    // are the same verdict (one at the gate on `Type`, one at the boundary).
    for ty in [
        Type::Int,
        opt(Type::Int),
        Type::Fn(vec![Type::Int], Box::new(Type::Bool)),
        Type::Var(0),
        opt(Type::Var(1)),
        Type::TyConApp(2, vec![]),
    ] {
        assert_eq!(
            ConcreteType::from_type(&ty).is_ok(),
            ty.is_concrete(),
            "disagreement on {ty:?}"
        );
    }
}

// ---- result_root — the ONE IO-head-strip rule (S118 ruling, FIXME 0898) ----

fn adt(module: &str, name: &str, args: Vec<ConcreteType>) -> ConcreteType {
    ConcreteType::ADT(
        crate::FQTypeName::new(
            crate::ModuleFullPath::from(module),
            crate::TypeName::from(name),
        ),
        args,
    )
}

// spec: design/arch/fixmes/0898 ruling — `(IO a)` strips ONE hop to `a`;
// `(IO (IO a))` strips to `(IO a)`, never recursively.
#[test]
fn result_root_strips_exactly_one_io_hop() {
    let io_int = adt("primitives", "IO", vec![ConcreteType::Int]);
    assert_eq!(io_int.result_root(), &ConcreteType::Int);

    let io_io_int = adt("primitives", "IO", vec![io_int.clone()]);
    assert_eq!(io_io_int.result_root(), &io_int, "one hop only");
}

// spec: design/arch/fixmes/0898 ruling — everything that is not the
// `primitives/IO` non-empty-args head is its own root: scalars, other ADTs,
// a USER-module type named IO, and a nullary IO head.
#[test]
fn result_root_is_identity_off_the_io_head() {
    let int = ConcreteType::Int;
    assert_eq!(int.result_root(), &int);

    let opt = adt("primitives", "Option", vec![ConcreteType::Int]);
    assert_eq!(opt.result_root(), &opt);

    let user_io = adt("user", "IO", vec![ConcreteType::Int]);
    assert_eq!(user_io.result_root(), &user_io, "user IO is not primitives/IO");

    let nullary_io = adt("primitives", "IO", vec![]);
    assert_eq!(nullary_io.result_root(), &nullary_io, "nullary head is itself");
}
