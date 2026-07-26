//! S118 — `design/backend/transitive-drop-glue.md` §4.1 (the ruling) and §10
//! row 4: the ONE sanctioned non-concrete release site is the **constructor
//! template's own parameter**, and the gate that admits it is keyed on the
//! **frame**, never on the type.
//!
//! A constructor `Def` is compiled ONCE per declaration, so its parameter types
//! come from the entry's `scheme` and two legal declaration shapes hand that
//! scheme a non-concrete parameter — a generic field (`(deftype (Option a)
//! (Some [:a v]))`) and an undeclared field (`(deftype B (Mk [v]))`). In that
//! frame the scope-exit release is not a teardown: it is the balancing half of
//! the guarded consuming inc `compile_consuming_arg_list` emitted on the same
//! value, on a word the returned box now also holds (invariant **I-CT**), so the
//! shallow dec can never observe the last reference.
//!
//! **What these cells fence, and what they deliberately do NOT.** These are §10
//! row 4's positive and edge cells: the balance itself, for both non-concrete
//! template shapes and for the multi-field case, plus the boundary that being a
//! ctor template is *necessary but not sufficient* (a concrete field takes the
//! ordinary `drop<T>` path). They hold under any admission key.
//!
//! Row 4's **negative** half — "a non-concrete binding in a NON-ctor-template
//! frame is a located error" — is **not landed here**, and the reason is a
//! measurement, not an omission. §4.1's gate was implemented as ruled (a
//! frame-level `is_ctor_template` boolean computed in `compile_body` from the
//! body node, threaded to the shared release body as a two-state
//! `NonConcreteRelease` verdict, with both tail-jump flushes passing the
//! rejecting arm) and the negatives went RED-then-GREEN exactly as designed —
//! but the corpus went the other way:
//!
//! * baseline `binary(/^spec_/)`: 893 run, 8 pre-existing failures;
//! * under the ruled frame key: 893 run, **24** failures — 16 NEW hard codegen
//!   refusals across `spec_03_types` (7), `spec_07_traits` (5),
//!   `spec_field_accessor` (2), `spec_04_expressions` (1),
//!   `spec_05_definitions` (1).
//!
//! Two further families reach the arm in ordinary `defn`-shaped frames that
//! I-CT does not cover: synthetic **field accessors** of a generic or
//! undeclared-field product (`Box.v`'s `self: ADT(user/Box, [Var(0)])`) and
//! generic **trait-method instances** (`Functor.fmap$primitives/Option`'s
//! `Fn([Var(9)], Var(8))` parameter). So §4.1's premise — "the migration
//! measured exactly one class" — is false, and the narrowing cannot land until
//! the whole measured class is ruled: FIXME 0903 → `/design`(backend), which
//! carries the implemented gate and both negative cells verbatim for re-landing.
//!
//! The consequence for a reader of THIS file: the cells below pass under the
//! type-keyed gate that is still in place *and* under the frame key that will
//! replace it. They are not evidence that the key is right.

use std::collections::HashMap;

use dashmap::DashMap;

use cranelisp_types::{
    CranelispError, DefKind, Defn, DefnVariant, Expr, FQSymbol, FQTypeName, ModuleEntry,
    ModuleFullPath, Scheme, Span, Symbol, SymbolTable, Type, TypeDefInfo, TypeName, Visibility,
};

use crate::test_support::count_release_ops;

/// The nullary-tag discriminator both halves of the pair share
/// (`cranelisp_types::NULLARY_TAG_THRESHOLD`), as it renders in CLIF. Counting
/// it is how a cell asserts that the inc and the dec skip the SAME words — the
/// "no polarity gap" half of I-CT.
const NULLARY_GUARD: &str = "iconst.i64 1024";

fn module_path() -> ModuleFullPath {
    ModuleFullPath::from("user")
}

fn var(name: &str, span: Span, ty: Type) -> Expr {
    Expr::Var {
        name: Symbol::from(name),
        span,
        resolved_call: None,
        inferred_type: Some(Box::new(ty)),
    }
}

/// A constructor template `(deftype T (Ctor [f0 f1 …]))`: the synthetic
/// `Expr::ConstrADT` body typecheck synthesises for the constructor `Def`, plus
/// the symbol tables that give it its signature.
///
/// `fields` carries each field's SIGNATURE type — the `scheme` is where
/// `bind_defn_params` reads parameter types from, so this is the ONLY place the
/// non-concreteness under test can be spelled.
fn ctor_template(
    type_name: &str,
    ctor: &str,
    fields: &[(&str, Type)],
) -> (Defn, DashMap<ModuleFullPath, SymbolTable>) {
    let module = module_path();
    let fqtn = FQTypeName::new(module.clone(), TypeName::from(type_name));
    let adt = Type::ADT(fqtn.clone(), vec![]);

    let field_exprs: Vec<Expr> = fields
        .iter()
        .enumerate()
        .map(|(i, (name, ty))| {
            let base = 100 + (i as u32) * 10;
            var(name, Span::new(base, base + 1), ty.clone())
        })
        .collect();

    let body = Expr::ConstrADT {
        type_name: fqtn.clone(),
        tag: 0,
        fields: field_exprs,
        span: Span::new(10, 90),
        inferred_type: Some(Box::new(adt.clone())),
    };

    let defn = Defn {
        name: Symbol::from(ctor),
        docstring: None,
        variants: vec![DefnVariant {
            params: fields
                .iter()
                .map(|(name, _)| (Symbol::from(*name), None))
                .collect(),
            body,
            span: Span::new(0, 100),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 100),
    };

    let mut st = SymbolTable::new(module.clone());
    st.insert(
        Symbol::from(type_name),
        ModuleEntry::TypeDef {
            info: TypeDefInfo {
                name: fqtn.clone(),
                type_params: vec![],
                constructors: vec![Symbol::from(ctor)],
            },
            visibility: Visibility::Public,
            docstring: None,
        },
    );
    st.insert(
        Symbol::from(ctor),
        ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(
                    fields.iter().map(|(_, ty)| ty.clone()).collect(),
                    Box::new(adt),
                ),
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: fields.iter().map(|(name, _)| Symbol::from(*name)).collect(),
            kind: Box::new(DefKind::Constructor {
                got_slot: 0,
                type_name: fqtn,
                tag: 0,
                field_count: fields.len(),
                internal: false,
                type_def: None,
                mode_summary: None,
            }),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: None,
            codegen_view: None,
            code: None,
            value_use: false,
        },
    );

    let tables = DashMap::new();
    tables.insert(module, st);
    (defn, tables)
}

/// Compile `defn` through the production per-body seam and return the compiler's
/// verdict (CLIF text, or the located refusal).
fn compile(
    defn: &Defn,
    tables: &DashMap<ModuleFullPath, SymbolTable>,
) -> Result<String, CranelispError> {
    let mut jit = crate::jit::Jit::new_with_symbols(&[]).expect("JIT construction");
    let module = module_path();
    // A ctor template's body is one straight-line construction: no calls, so no
    // dispatch carriers to thread.
    let resolved_targets: HashMap<Span, FQSymbol> = HashMap::new();
    crate::test_support::try_compile_defns_in_module(
        &[defn],
        &[],
        &[],
        &resolved_targets,
        tables,
        module,
        jit.jit_module(),
    )
    .map(|mut clifs| clifs.pop().expect("one compiled defn"))
}

fn count(clif: &str, needle: &str) -> usize {
    clif.matches(needle).count()
}

/// The shared assertion for both template shapes of §10 row 4's positive cell:
/// ONE guarded inc, ONE balancing guarded dec, both behind the SAME
/// nullary-threshold predicate, and no drop-glue call (there is no concrete type
/// to derive one from — that is the whole point of the admission).
fn assert_balanced_guarded_pair(clif: &str, fields: usize, what: &str) {
    assert_eq!(
        count(clif, "atomic_rmw.i64 add"),
        fields,
        "{what}: the consuming inc must fire once per heap-classified field \
         parameter — it is the half the scope-exit dec balances\n{clif}"
    );
    assert_eq!(
        count(clif, "atomic_rmw.i64 sub"),
        fields,
        "{what}: exactly one balancing shallow dec per field parameter (I-CT); \
         more is a double-release, fewer is the leak direction\n{clif}"
    );
    assert_eq!(
        count_release_ops(clif),
        fields,
        "{what}: the shallow decs are the ONLY releases — a canonical `drop<T>` \
         call here would mean a concrete type was invented for a non-concrete \
         parameter\n{clif}"
    );
    assert_eq!(
        count(clif, NULLARY_GUARD),
        fields * 2,
        "{what}: the inc and the dec must share ONE runtime predicate (a bare \
         nullary tag skips both). A polarity gap between what the inc treats as \
         a pointer and what the dec does breaks I-CT\n{clif}"
    );
}

// spec: spec/05-definitions.md §5.3 (deftype); appendix-c-nfr §C.1.4 —
// `transitive-drop-glue.md` §4.1 / §10 row 4 POSITIVE: the generic template
// `(deftype (Option a) (Some [:a v]))`. The field parameter's signature type is
// the declared type variable, so no `ConcreteType` exists for it; the guarded
// consuming inc and the balancing guarded scope-exit dec are emitted on the same
// word, behind the same nullary predicate.
#[test]
fn a_generic_ctor_template_balances_its_guarded_inc_with_a_guarded_dec() {
    let (defn, tables) = ctor_template("Option", "Some", &[("v", Type::Var(0))]);
    let clif = compile(&defn, &tables).expect("the generic ctor template must compile");
    assert_balanced_guarded_pair(&clif, 1, "generic ctor template");
}

// spec: spec/05-definitions.md §5.3 (deftype); appendix-c-nfr §C.1.4 —
// `transitive-drop-glue.md` §4.1 / §10 row 4 POSITIVE: the undeclared-field
// template `(deftype B (Mk [v]))`. `B` is monomorphic and no instantiation ever
// pins the field, so typecheck leaves it a free type variable. The class is
// intrinsic to compiling a ctor `Def` ONCE per declaration — not to generics —
// which is why this shape must take the identical path.
#[test]
fn an_undeclared_field_ctor_template_takes_the_same_admission() {
    let (defn, tables) = ctor_template("B", "Mk", &[("v", Type::Var(7))]);
    let clif = compile(&defn, &tables).expect("the undeclared-field template must compile");
    assert_balanced_guarded_pair(&clif, 1, "undeclared-field ctor template");
}

// spec: spec/05-definitions.md §5.3 (deftype); appendix-c-nfr §C.1.4 —
// `transitive-drop-glue.md` §10 row 4 EDGE: a multi-field template incs and decs
// EVERY field parameter. The admission is per-binding, not per-frame-once.
#[test]
fn a_multi_field_template_incs_and_decs_every_field_parameter() {
    let (defn, tables) = ctor_template(
        "Pair",
        "MkPair",
        &[("a", Type::Var(0)), ("b", Type::Var(1))],
    );
    let clif = compile(&defn, &tables).expect("the multi-field template must compile");
    assert_balanced_guarded_pair(&clif, 2, "multi-field ctor template");
}

// spec: spec/05-definitions.md §5.3 (deftype); appendix-c-nfr §C.1.4 —
// `transitive-drop-glue.md` §10 row 4 EDGE: a CONCRETE-field template takes the
// ordinary `drop<T>` path, no exception. Being a ctor template is necessary for
// the admission, never sufficient — the binding must also fail
// `ConcreteType::from_type`.
//
// The design row spells this shape `(deftype B (Mk [:Int v]))`; `Int` is
// `NeverHeap`, so it never reaches a release seam at all and cannot show which
// path was taken. A concrete HEAP field is the observing form of the same claim:
// an unguarded inc (String is `AlwaysHeap`, no nullary tags in its domain) and
// ONE canonical glue call, with no inline shallow dec anywhere.
#[test]
fn a_concrete_heap_field_template_takes_the_ordinary_drop_glue_path() {
    let (defn, tables) = ctor_template("Box", "MkBox", &[("s", Type::String)]);
    let clif = compile(&defn, &tables).expect("the concrete-field template must compile");
    assert_eq!(
        count(&clif, "atomic_rmw.i64 sub"),
        0,
        "a concrete field must not take the §4.1 shallow dec\n{clif}"
    );
    assert_eq!(
        count_release_ops(&clif),
        1,
        "the concrete field's release is ONE call to the canonical `drop<String>` \
         glue — the ordinary path\n{clif}"
    );
    assert_eq!(
        count(&clif, NULLARY_GUARD),
        0,
        "an `AlwaysHeap` field carries no nullary-tag guard at either half\n{clif}"
    );
}
