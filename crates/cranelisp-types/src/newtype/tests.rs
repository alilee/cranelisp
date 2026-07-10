//! Minimal cover for the string-newtype macro and the qualified-name types
//! (FIXME 0498).
//!
//! `newtype.rs` is *logic*, not pure data: the `string_newtype!` macro emits
//! the `Deref`/`Borrow`/`From`/`PartialEq`/`Display` impls that the whole
//! codebase relies on, and `TraitRef`/`SymbolRef`/`TypeRef` carry the
//! conditional module-qualification Display logic (`None` → bare, `Some` →
//! `module/name`). The audit flagged the module as zero-test. These pin:
//! - the macro-generated conversions + `Borrow<str>` HashMap-lookup contract
//!   (the load-bearing one — symbol tables are keyed by these newtypes and
//!   queried with `&str`), and
//! - both arms of every qualified-name `Display` (positive AND the
//!   unqualified/negative cell).

use super::*;
use std::borrow::Borrow;
use std::collections::HashMap;

// --- string_newtype! generated impls -------------------------------------

// spec: design/arch/CLAUDE.md §"String Newtypes" — From<&str>/From<String>
// agree; Deref/AsRef expose the inner &str; Display echoes it verbatim.
#[test]
fn newtype_conversions_and_display() {
    let from_str = Symbol::from("foo");
    let from_string = Symbol::from("foo".to_string());
    assert_eq!(from_str, from_string);
    // Deref to str
    assert_eq!(&*from_str, "foo");
    assert_eq!(from_str.len(), 3); // via Deref<Target=str>
    // AsRef<str>
    assert_eq!(AsRef::<str>::as_ref(&from_str), "foo");
    // Display
    assert_eq!(from_str.to_string(), "foo");
}

// spec: design/arch/CLAUDE.md §"String Newtypes" — PartialEq<str> / PartialEq<&str>
// let call sites compare a newtype to a string literal without allocating.
#[test]
fn newtype_partial_eq_with_str() {
    let s = TypeName::from("Int");
    assert!(s == "Int");
    assert!(s == "Int"); // &str form
    assert!(!(s == "Bool"));
}

// spec: design/arch/CLAUDE.md §"String Newtypes" — `Borrow<str>` is the
// load-bearing property: a HashMap keyed by a newtype MUST be queryable by
// `&str` (symbol-table lookups do exactly this). A Hash/Borrow inconsistency
// would make every by-name lookup miss.
#[test]
fn newtype_borrow_enables_hashmap_lookup_by_str() {
    let mut m: HashMap<Symbol, i32> = HashMap::new();
    m.insert(Symbol::from("answer"), 42);
    // Borrow<str> + matching Hash/Eq → lookup by &str hits.
    assert_eq!(m.get("answer"), Some(&42));
    assert_eq!(m.get("missing"), None);
    // Explicitly exercise the Borrow impl.
    let key = Symbol::from("answer");
    let b: &str = key.borrow();
    assert_eq!(b, "answer");
}

// --- FQSymbol / FQTypeName / FQTraitName Display -------------------------

// spec: design/arch/CLAUDE.md §"String Newtypes" — FQ names render `module/name`.
#[test]
fn fq_names_render_module_slash_name() {
    let fqs = FQSymbol {
        module: ModuleFullPath::from("core.option"),
        symbol: Symbol::from("Some"),
    };
    assert_eq!(fqs.to_string(), "core.option/Some");

    let fqt = FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Point"));
    assert_eq!(fqt.to_string(), "user/Point");

    let fqtr = FQTraitName::new(ModuleFullPath::from("fmt"), TraitName::from("Display"));
    assert_eq!(fqtr.to_string(), "fmt/Display");
}

// --- syntactic-stage refs: conditional module qualification --------------

// spec: newtype.rs rustdoc — TraitRef Display: None (unqualified) is the common
// cell; Some (qualified) prints `module/name`. Both arms pinned.
#[test]
fn trait_ref_display_both_arms() {
    let unqualified = TraitRef::new(None, TraitName::from("Display"));
    assert_eq!(unqualified.to_string(), "Display");
    let qualified = TraitRef::new(Some(ModuleFullPath::from("fmt")), TraitName::from("Display"));
    assert_eq!(qualified.to_string(), "fmt/Display");
}

// spec: newtype.rs rustdoc — SymbolRef Display: both arms.
#[test]
fn symbol_ref_display_both_arms() {
    let unqualified = SymbolRef::new(None, Symbol::from("Some"));
    assert_eq!(unqualified.to_string(), "Some");
    let qualified = SymbolRef::new(
        Some(ModuleFullPath::from("core.option")),
        Symbol::from("Some"),
    );
    assert_eq!(qualified.to_string(), "core.option/Some");
}

// spec: newtype.rs rustdoc — TypeRef Display: both arms.
#[test]
fn type_ref_display_both_arms() {
    let unqualified = TypeRef::new(None, TypeName::from("Option"));
    assert_eq!(unqualified.to_string(), "Option");
    let qualified = TypeRef::new(Some(ModuleFullPath::from("option")), TypeName::from("Option"));
    assert_eq!(qualified.to_string(), "option/Option");
}

// spec: newtype.rs rustdoc — the `new` constructors store their fields verbatim
// (round-trips through the public fields).
#[test]
fn syntactic_ref_new_stores_fields() {
    let r = SymbolRef::new(Some(ModuleFullPath::from("m")), Symbol::from("x"));
    assert_eq!(r.module.as_deref(), Some("m"));
    assert_eq!(r.name, "x");
    let none = TypeRef::new(None, TypeName::from("T"));
    assert!(none.module.is_none());
}
