//! `TraitImpl::authored_label`: the one derivation of a writer record's label
//! from an `impl` form (`design/arch/trait-impl-cache-carrier.md` §2.1).

use super::*;
use crate::{ModuleFullPath, TraitName, TypeName};

fn trait_ref(module: Option<&str>, name: &str) -> TraitRef {
    TraitRef::new(module.map(ModuleFullPath::from), TraitName::from(name))
}

fn type_ref(module: Option<&str>, name: &str) -> TypeRef {
    TypeRef::new(module.map(ModuleFullPath::from), TypeName::from(name))
}

fn impl_form(trait_name: TraitRef, head_con_var: Option<&str>, target: TypeExpr) -> TraitImpl {
    TraitImpl {
        trait_name,
        head_con_var: head_con_var.map(Symbol::from),
        target,
        type_constraints: Vec::new(),
        methods: Vec::new(),
        span: Span::SYNTHETIC,
    }
}

fn label(form: &TraitImpl) -> String {
    form.authored_label().to_string()
}

// spec: spec §7.3 — impl head; design/arch/trait-impl-cache-carrier.md §2.1
#[test]
fn label_is_the_written_trait_and_target_head() {
    let bare = impl_form(
        trait_ref(None, "Show"),
        None,
        TypeExpr::Named(type_ref(None, "B")),
    );
    assert_eq!(label(&bare), "Show.B");

    // An applied target contributes its head only, the grain of the record key.
    let applied = impl_form(
        trait_ref(None, "Show"),
        None,
        TypeExpr::Applied(
            type_ref(None, "Box"),
            vec![TypeExpr::TypeVar(Symbol::from("a"))],
        ),
    );
    assert_eq!(label(&applied), "Show.Box");
}

// spec: spec §8.5 — qualified references; design/arch/trait-impl-cache-carrier.md §2.1
#[test]
fn label_keeps_each_written_qualifier() {
    let through_a = impl_form(
        trait_ref(Some("fmt"), "Show"),
        None,
        TypeExpr::Named(type_ref(Some("a"), "Box")),
    );
    let through_b = impl_form(
        trait_ref(Some("fmt"), "Show"),
        None,
        TypeExpr::Named(type_ref(Some("b"), "Box")),
    );
    let bare_trait = impl_form(
        trait_ref(None, "Show"),
        None,
        TypeExpr::Named(type_ref(Some("a"), "Box")),
    );
    assert_eq!(label(&through_a), "fmt/Show.a/Box");
    // Two heads that differ only in a qualifier are two labels: with bare
    // names they would share one, and the keyed read would be ambiguous.
    assert_ne!(label(&through_a), label(&through_b));
    assert_ne!(label(&through_a), label(&bare_trait));
}

// spec: spec §7.3.5 — higher-kinded impl head; design/arch/trait-impl-cache-carrier.md §2.1
#[test]
fn higher_kinded_label_names_the_constructor_before_and_after_the_rewrite() {
    let constructor = type_ref(Some("lib"), "Opt");
    let as_built = impl_form(
        trait_ref(None, "Functor"),
        Some("f"),
        TypeExpr::Applied(
            type_ref(None, "Functor"),
            vec![TypeExpr::Named(constructor.clone())],
        ),
    );
    // Typecheck's normalisation replaces the pairing with the bare constructor
    // and keeps the echoed head.
    let rewritten = TraitImpl {
        target: TypeExpr::Named(constructor),
        ..as_built.clone()
    };
    assert_eq!(label(&as_built), "Functor.lib/Opt");
    assert_eq!(label(&rewritten), label(&as_built));

    // Without an echoed head the same target is a conventional applied type,
    // and its own head is the label's type.
    let conventional = TraitImpl {
        head_con_var: None,
        ..as_built
    };
    assert_eq!(label(&conventional), "Functor.Functor");
}

// spec: design/arch/trait-impl-cache-carrier.md §2.1 — a target with no head reference
#[test]
fn headless_target_contributes_an_underscore() {
    let headless = impl_form(
        trait_ref(None, "Show"),
        None,
        TypeExpr::TypeVar(Symbol::from("a")),
    );
    assert_eq!(label(&headless), "Show._");

    // An echoed head whose pairing argument has no head reference falls back to
    // the target's own head.
    let pairing_of_var = impl_form(
        trait_ref(None, "Functor"),
        Some("f"),
        TypeExpr::Applied(
            type_ref(None, "Functor"),
            vec![TypeExpr::TypeVar(Symbol::from("g"))],
        ),
    );
    assert_eq!(label(&pairing_of_var), "Functor.Functor");
}
