//! Unit tests for the R5 `value_layout` predicate — the single-sourced
//! Copy/value-layout carrier (`design/arch/ownership-inference.md` §6.3,
//! `design/backend/ownership-codegen.md` §7.1).
//!
//! Wave-1 carrier only: exercises the predicate in isolation (no typecheck or
//! backend consumer). The tests build minimal `SymbolTables` by hand for each
//! type shape and assert the `Some(ValueLayout { words })` / `None` verdict.

use super::*;
use crate::{ModuleFullPath, Scheme, TypeDefInfo, TypeName, Visibility};
use std::collections::HashMap;

type Tables = SymbolTables<(), ()>;

const M: &str = "test";

fn fqtn(name: &str) -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from(M), TypeName::from(name))
}

fn mono_scheme(ty: Type) -> Scheme {
    Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty,
    }
}

/// A constructor `Def` whose scheme is `field_tys… -> ADT(type)`.
fn ctor_entry(type_name: &str, field_tys: Vec<Type>, is_product: bool) -> ModuleEntry<()> {
    let adt = Type::ADT(fqtn(type_name), vec![]);
    let ty = if field_tys.is_empty() {
        adt
    } else {
        Type::Fn(field_tys.clone(), Box::new(adt))
    };
    let type_def = is_product.then(|| {
        Box::new(TypeDefInfo {
            name: fqtn(type_name),
            type_params: vec![],
            constructors: vec![Symbol::from(type_name)],
        })
    });
    ModuleEntry::def(
        mono_scheme(ty),
        DefKind::Constructor {
            got_slot: 0,
            type_name: fqtn(type_name),
            tag: 0,
            field_count: field_tys.len(),
            internal: false,
            type_def,
            mode_summary: None,
        },
    )
    .build()
}

fn type_def_entry(name: &str, ctors: &[&str]) -> ModuleEntry<()> {
    ModuleEntry::TypeDef {
        info: TypeDefInfo {
            name: fqtn(name),
            type_params: vec![],
            constructors: ctors.iter().map(|c| Symbol::from(*c)).collect(),
        },
        visibility: Visibility::Public,
        docstring: None,
    }
}

/// Build a one-module `SymbolTables` from `(key, entry)` pairs.
fn tables(entries: Vec<(&str, ModuleEntry<()>)>) -> Tables {
    let mut table = SymbolTable::<(), ()>::new_with_params(ModuleFullPath::from(M));
    for (name, entry) in entries {
        table.insert(Symbol::from(name), entry);
    }
    let map: Tables = dashmap::DashMap::new();
    map.insert(ModuleFullPath::from(M), table);
    map
}

// --- scalars (the value base case) ------------------------------------------

// spec: design/arch/ownership-inference.md §6.3 — scalars are the Copy base case
#[test]
fn scalars_are_one_word_values() {
    for ty in [ConcreteType::Int, ConcreteType::Bool, ConcreteType::Float] {
        let vl = value_layout::<(), ()>(&ty, None).expect("scalar is value-eligible");
        assert_eq!(vl.words, 1, "{ty:?} is one word");
    }
}

// spec: design/backend/ownership-codegen.md §7.1 — String/Fn keep heap identity
#[test]
fn heap_identities_are_not_values() {
    assert!(value_layout::<(), ()>(&ConcreteType::String, None).is_none());
    let f = ConcreteType::Fn(vec![ConcreteType::Int], Box::new(ConcreteType::Int));
    assert!(value_layout::<(), ()>(&f, None).is_none());
}

// --- the F2v witness: single-ctor scalar-payload product --------------------

// spec: design/backend/ownership-codegen.md §7.3 — (Cell Int) flattens to 1 word
#[test]
fn single_ctor_scalar_product_flattens() {
    // (deftype Cell (Cell [:Int value])) — product: type-name == ctor-name.
    let t = tables(vec![("Cell", ctor_entry("Cell", vec![Type::Int], true))]);
    let cell = ConcreteType::ADT(fqtn("Cell"), vec![]);
    let vl = value_layout(&cell, Some(&t)).expect("Cell is value-eligible");
    assert_eq!(vl.words, 1);
}

// spec: design/backend/ownership-codegen.md §7.1 — sum-shaped single-ctor product
#[test]
fn single_ctor_sum_type_flattens() {
    // (deftype Foo (Bar [:Int x])) — type-name != ctor-name: TypeDef + ctor Def.
    let t = tables(vec![
        ("Foo", type_def_entry("Foo", &["Bar"])),
        ("Bar", ctor_entry("Foo", vec![Type::Int], false)),
    ]);
    let foo = ConcreteType::ADT(fqtn("Foo"), vec![]);
    assert_eq!(value_layout(&foo, Some(&t)).unwrap().words, 1);
}

// --- size-bound and structural rejections (each a monotone-sound None) ------

// spec: design/backend/ownership-codegen.md §7.2 — >1 word exceeds the first-landing bound
#[test]
fn two_field_product_exceeds_word_bound() {
    // (deftype Pair (Pair [:Int a :Int b])) — 2 words > VALUE_LAYOUT_MAX_WORDS.
    assert_eq!(VALUE_LAYOUT_MAX_WORDS, 1);
    let t = tables(vec![(
        "Pair",
        ctor_entry("Pair", vec![Type::Int, Type::Int], true),
    )]);
    let pair = ConcreteType::ADT(fqtn("Pair"), vec![]);
    assert!(value_layout(&pair, Some(&t)).is_none(), "2 words > bound");
}

// spec: design/backend/ownership-codegen.md §7.1 — multi-ctor needs a tag word
#[test]
fn multi_ctor_adt_is_not_a_value() {
    // (deftype Opt (Some [:Int v]) (Nil))
    let t = tables(vec![
        ("Opt", type_def_entry("Opt", &["Some", "Nil"])),
        ("Some", ctor_entry("Opt", vec![Type::Int], false)),
        ("Nil", ctor_entry("Opt", vec![], false)),
    ]);
    let opt = ConcreteType::ADT(fqtn("Opt"), vec![]);
    assert!(value_layout(&opt, Some(&t)).is_none());
}

// spec: design/backend/ownership-codegen.md §7.1 — a heap-typed field disqualifies
#[test]
fn product_with_heap_field_is_not_a_value() {
    // (deftype Named (Named [:String s]))
    let t = tables(vec![(
        "Named",
        ctor_entry("Named", vec![Type::String], true),
    )]);
    let named = ConcreteType::ADT(fqtn("Named"), vec![]);
    assert!(value_layout(&named, Some(&t)).is_none());
}

// spec: design/backend/ownership-codegen.md §7.3 — Vec is a heap collection
#[test]
fn vec_is_never_a_value() {
    let v = ConcreteType::ADT(fqtn("Vec"), vec![ConcreteType::Int]);
    // Vec short-circuits before any table lookup.
    assert!(value_layout(&v, Some(&tables(vec![]))).is_none());
    assert!(value_layout::<(), ()>(&v, None).is_none());
}

// --- nesting and conservatism ----------------------------------------------

// spec: design/arch/ownership-inference.md §6.3 — value-eligibility is transitive
#[test]
fn nested_value_field_counts_its_words() {
    // (deftype Cell (Cell [:Int v]))  +  (deftype Wrap (Wrap [:Cell c]))
    let cell = Type::ADT(fqtn("Cell"), vec![]);
    let t = tables(vec![
        ("Cell", ctor_entry("Cell", vec![Type::Int], true)),
        ("Wrap", ctor_entry("Wrap", vec![cell], true)),
    ]);
    // Wrap { Cell { Int } } = 1 word total → still within the bound.
    let wrap = ConcreteType::ADT(fqtn("Wrap"), vec![]);
    assert_eq!(value_layout(&wrap, Some(&t)).unwrap().words, 1);
}

// spec: design/backend/ownership-codegen.md §7.2 — a nested value can push over the bound
#[test]
fn nested_value_can_exceed_bound() {
    // (deftype Cell (Cell [:Int v]))  +  (deftype Two (Two [:Cell a :Cell b]))
    let cell = Type::ADT(fqtn("Cell"), vec![]);
    let t = tables(vec![
        ("Cell", ctor_entry("Cell", vec![Type::Int], true)),
        ("Two", ctor_entry("Two", vec![cell.clone(), cell], true)),
    ]);
    let two = ConcreteType::ADT(fqtn("Two"), vec![]);
    assert!(value_layout(&two, Some(&t)).is_none(), "2 words > bound");
}

// spec: design/backend/ownership-codegen.md §7.1 — a 0-FIELD single-ctor product
// is NOT value-eligible. The flattening the backend implements is the identity
// move of one value word; a fieldless product has no word to move. (Its heap
// classification is `NeverHeap` — a bare tag — which is RC-free regardless of
// mode, so keeping it `None`/non-Copy is consistent, not a precision loss that
// matters.) Wave-3a /review single-source ruling: `Some(0)` here split
// typecheck `Copy` from the backend verdict.
#[test]
fn nullary_single_ctor_product_is_not_a_value() {
    // (deftype Unit (Unit []))
    let t = tables(vec![("Unit", ctor_entry("Unit", vec![], true))]);
    let unit = ConcreteType::ADT(fqtn("Unit"), vec![]);
    assert!(value_layout(&unit, Some(&t)).is_none());
}

// spec: design/backend/ownership-codegen.md §7.1 — Wave-3a /review BLOCKER 1
// (0-word-but-≥1-field product): the divergence-class guard. `(P [:U u])` whose
// sole field `U` is a nullary (0-word) product has word-count 0 but ONE field.
// The OLD `sum ≤ 1` predicate returned `Some(0)` → typecheck's
// `value_layout(..).is_some()` made P `Copy` (no caller `rc_inc`) while the
// backend kept P a heap object → a heap value across a Copy edge with no inc →
// leak/UAF. FIXED: single-field-∧-value-field ⇒ `None` (P is heap + Owned +
// RC everywhere — typecheck and backend agree because they read THIS verdict).
#[test]
fn zero_word_field_product_is_not_a_value() {
    // (deftype U (U []))  +  (deftype P (P [:U u]))
    let u_ty = Type::ADT(fqtn("U"), vec![]);
    let t = tables(vec![
        ("U", ctor_entry("U", vec![], true)),
        ("P", ctor_entry("P", vec![u_ty], true)),
    ]);
    let p = ConcreteType::ADT(fqtn("P"), vec![]);
    assert!(
        value_layout(&p, Some(&t)).is_none(),
        "a single-ctor product whose one field is a 0-word type must NOT be \
         value-eligible — else typecheck Copy and backend heap diverge (Blocker 1)",
    );
}

// spec: design/backend/ownership-codegen.md §7.1 — Wave-3a /review BLOCKER 2
// (multi-field-but-≤1-word): the second divergence class. `(M [:Int x :U u])` is
// Int(1) + U(0) = 1 word across TWO fields. The OLD word-count predicate
// returned `Some(1)` → the backend classified M `Value`, but construction
// (`value_construct` keys on `field_vals.len()==1`) kept the 2-field build on
// the heap while the match `is_value` path bound EVERY field to the scrutinee
// word → a garbage pointer + leak. FIXED: exactly-one-field ⇒ `None` (M is heap
// everywhere; construction↔match agree).
#[test]
fn multi_field_one_word_product_is_not_a_value() {
    // (deftype U (U []))  +  (deftype M (M [:Int x :U u]))
    let u_ty = Type::ADT(fqtn("U"), vec![]);
    let t = tables(vec![
        ("U", ctor_entry("U", vec![], true)),
        ("M", ctor_entry("M", vec![Type::Int, u_ty], true)),
    ]);
    let m = ConcreteType::ADT(fqtn("M"), vec![]);
    assert!(
        value_layout(&m, Some(&t)).is_none(),
        "a ≥2-field product must NOT be value-eligible even at ≤1 word — else \
         construction (heap) and match (flat) split the representation (Blocker 2)",
    );
}

// spec: design/backend/ownership-codegen.md §7.1 — None type_defs classifies ADTs conservatively
#[test]
fn absent_tables_classify_adts_as_ineligible() {
    let cell = ConcreteType::ADT(fqtn("Cell"), vec![]);
    assert!(value_layout::<(), ()>(&cell, None).is_none());
}

// spec: design/arch/ownership-inference.md §6.3 — unresolvable / non-ctor entry is None
#[test]
fn unresolvable_type_is_none() {
    let t = tables(vec![]); // empty module, "Ghost" not present
    let ghost = ConcreteType::ADT(fqtn("Ghost"), vec![]);
    assert!(value_layout(&ghost, Some(&t)).is_none());
}

// --- recursion (compiler-DoS) cycle guard -----------------------------------

// spec: design/arch/ownership-inference.md §6.3 — a self-recursive concrete
// product is unbounded-size ⇒ conservative None, and MUST NOT stack-overflow.
#[test]
fn self_recursive_type_is_none_without_overflow() {
    // (deftype Stream (Stream [:Int head :Stream tail])) — the `tail` field is
    // `Type::ADT("Stream", [])`, concrete and single-ctor, so without the cycle
    // guard `layout_words` re-enters `Stream` forever.
    let stream = Type::ADT(fqtn("Stream"), vec![]);
    let t = tables(vec![(
        "Stream",
        ctor_entry("Stream", vec![Type::Int, stream], true),
    )]);
    let s = ConcreteType::ADT(fqtn("Stream"), vec![]);
    assert!(
        value_layout(&s, Some(&t)).is_none(),
        "recursive type is never a bounded inline value",
    );
}

// spec: design/arch/ownership-inference.md §6.3 — a mutually-recursive
// A-holds-B / B-holds-A pair is unbounded-size ⇒ None, and MUST NOT overflow.
#[test]
fn mutually_recursive_pair_is_none_without_overflow() {
    // (deftype A (A [:B b]))  +  (deftype B (B [:A a]))
    let a_ty = Type::ADT(fqtn("A"), vec![]);
    let b_ty = Type::ADT(fqtn("B"), vec![]);
    let t = tables(vec![
        ("A", ctor_entry("A", vec![b_ty], true)),
        ("B", ctor_entry("B", vec![a_ty], true)),
    ]);
    let a = ConcreteType::ADT(fqtn("A"), vec![]);
    assert!(value_layout(&a, Some(&t)).is_none());
    // Both entry points into the cycle must be guarded.
    let b = ConcreteType::ADT(fqtn("B"), vec![]);
    assert!(value_layout(&b, Some(&t)).is_none());
}

// spec: design/backend/ownership-codegen.md §7.2 — generic (non-concrete) ctor field ⇒ conservative None
#[test]
fn generic_ctor_field_is_conservatively_ineligible() {
    // (deftype Box (Box [:a value])) — the stored ctor-scheme field type is a
    // `Type::Var`; the first landing does no per-instantiation substitution, so
    // even `(Box Int)` is conservatively heap (monotone-sound).
    let t = tables(vec![("Box", ctor_entry("Box", vec![Type::Var(0)], true))]);
    let boxed = ConcreteType::ADT(fqtn("Box"), vec![ConcreteType::Int]);
    assert!(value_layout(&boxed, Some(&t)).is_none());
}

// ---------------------------------------------------------------------------
// `ctor_field_types_at` — the instantiation-substituting projection (S119
// types-first slice; register rows R-6/R-16;
// design/arch/concreteness-types-first.md §3.5).
// ---------------------------------------------------------------------------

/// A GENERIC constructor `Def`: scheme `∀vars. field_tys… -> ADT(type, vars)`.
fn generic_ctor_entry(
    type_name: &str,
    type_var_ids: &[crate::TypeId],
    field_tys: Vec<Type>,
) -> ModuleEntry<()> {
    let adt = Type::ADT(
        fqtn(type_name),
        type_var_ids.iter().map(|&id| Type::Var(id)).collect(),
    );
    let ty = if field_tys.is_empty() {
        adt
    } else {
        Type::Fn(field_tys.clone(), Box::new(adt))
    };
    ModuleEntry::def(
        Scheme {
            type_vars: type_var_ids.to_vec(),
            constraints: HashMap::new(),
            ty,
        },
        DefKind::Constructor {
            got_slot: 0,
            type_name: fqtn(type_name),
            tag: 0,
            field_count: field_tys.len(),
            internal: false,
            type_def: None,
            mode_summary: None,
        },
    )
    .build()
}

fn one_table(entries: Vec<(&str, ModuleEntry<()>)>) -> SymbolTable<(), ()> {
    let mut table = SymbolTable::<(), ()>::new_with_params(ModuleFullPath::from(M));
    for (name, entry) in entries {
        table.insert(Symbol::from(name), entry);
    }
    table
}

// spec: design/arch/concreteness-types-first.md §3.5 — substitution instantiates
// the generic field type at the supplied concrete args.
#[test]
fn ctor_field_types_at_substitutes_generic_field() {
    // (deftype (Bx a) [:a v]) at (Bx Int) ⇒ field types [Int].
    let t = one_table(vec![(
        "Bx",
        generic_ctor_entry("Bx", &[7], vec![Type::Var(7)]),
    )]);
    let got = ctor_field_types_at(&t, &Symbol::from("Bx"), &[ConcreteType::Int])
        .expect("concrete instantiation must project");
    assert_eq!(got, vec![ConcreteType::Int]);
}

// spec: design/arch/concreteness-types-first.md §3.5 — a concrete ctor projects
// its declared field types verbatim at the empty instantiation.
#[test]
fn ctor_field_types_at_concrete_ctor_projects_verbatim() {
    let t = one_table(vec![(
        "Tally",
        ctor_entry("Tally", vec![Type::Int, Type::String], true),
    )]);
    let got = ctor_field_types_at(&t, &Symbol::from("Tally"), &[])
        .expect("concrete ctor projects");
    assert_eq!(got, vec![ConcreteType::Int, ConcreteType::String]);
}

// spec: design/arch/concreteness-types-first.md §3.5 — a nullary ctor has zero
// fields at any well-formed instantiation.
#[test]
fn ctor_field_types_at_nullary_is_empty() {
    let t = one_table(vec![("None", generic_ctor_entry("Option", &[3], vec![]))]);
    let got = ctor_field_types_at(&t, &Symbol::from("None"), &[ConcreteType::Bool])
        .expect("nullary ctor projects");
    assert!(got.is_empty());
}

// spec: design/arch/concreteness-types-first.md §3.5 — ONE residual field
// refuses the whole ctor (the model-site spelling; never fabricates). The
// IO.Bind existential shape: a field var NOT bound by the result params.
#[test]
fn ctor_field_types_at_refuses_residual_field() {
    // Bind : ∀a b. (IO b, Fn [b] (IO a)) -> IO a — `b` does not occur in the
    // result params, so no instantiation of `IO a` can pin it.
    let io_b = Type::ADT(fqtn("IO"), vec![Type::Var(11)]);
    let t = one_table(vec![(
        "IO.Bind",
        generic_ctor_entry("IO", &[10], vec![io_b]),
    )]);
    let err = ctor_field_types_at(&t, &Symbol::from("IO.Bind"), &[ConcreteType::Int])
        .expect_err("existential payload must refuse");
    assert!(
        matches!(err, CtorFieldsAtError::NotConcrete(NotConcrete::Var(11))),
        "refusal names the residual var: {err:?}"
    );
}

// spec: design/arch/concreteness-types-first.md §3.5 — caller-side bugs are
// distinct from refusals: wrong key / non-ctor / wrong arity.
#[test]
fn ctor_field_types_at_caller_bug_arms() {
    let t = one_table(vec![
        ("Bx", generic_ctor_entry("Bx", &[7], vec![Type::Var(7)])),
        ("T", type_def_entry("T", &["A"])),
    ]);
    assert_eq!(
        ctor_field_types_at(&t, &Symbol::from("missing"), &[]),
        Err(CtorFieldsAtError::NotACtor)
    );
    assert_eq!(
        ctor_field_types_at(&t, &Symbol::from("T"), &[]),
        Err(CtorFieldsAtError::NotACtor),
        "a TypeDef entry is not a ctor"
    );
    assert_eq!(
        ctor_field_types_at(&t, &Symbol::from("Bx"), &[]),
        Err(CtorFieldsAtError::ParamArity {
            expected: 1,
            got: 0
        })
    );
}

// spec: design/arch/concreteness-types-first.md §3.5 — an already-concrete
// result param must agree with the supplied instantiation argument.
#[test]
fn ctor_field_types_at_instantiation_mismatch() {
    // Ctor of a type whose result param is pinned Int; instantiating at Bool
    // is a caller bug, not a refusal.
    let adt = Type::ADT(fqtn("P"), vec![Type::Int]);
    let entry = ModuleEntry::def(
        mono_scheme(Type::Fn(vec![Type::Int], Box::new(adt))),
        DefKind::Constructor {
            got_slot: 0,
            type_name: fqtn("P"),
            tag: 0,
            field_count: 1,
            internal: false,
            type_def: None,
            mode_summary: None,
        },
    )
    .build();
    let t = one_table(vec![("P", entry)]);
    assert_eq!(
        ctor_field_types_at(&t, &Symbol::from("P"), &[ConcreteType::Bool]),
        Err(CtorFieldsAtError::InstantiationMismatch { position: 0 })
    );
    assert_eq!(
        ctor_field_types_at(&t, &Symbol::from("P"), &[ConcreteType::Int]),
        Ok(vec![ConcreteType::Int]),
        "the agreeing instantiation projects"
    );
}
