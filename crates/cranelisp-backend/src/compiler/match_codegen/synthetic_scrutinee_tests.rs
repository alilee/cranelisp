//! S123 U-12 (golden G-1): a synthetic accessor's scrutinee is counted at its
//! binder's recorded type (`uniform-counting.md` §3.4 items 1 and 2).
//!
//! A concrete product's accessor body `(match self [(Ctor f…) field])` is built
//! by the all-local synthesis builder, whose nodes carry the `Int` placeholder
//! type. Its parameter carries the signature's product type. The match owns
//! the scrutinee and releases it at arm entry, so the release must classify
//! the scrutinee as the binder does; reading the placeholder emitted no
//! release, and every accessor call leaked its input.

use crate::test_support::*;
use cranelisp_types::{
    CallableOrigin, ConcreteType, FQTypeName, MatchArm, MonoDefnVariant, MonoExpr, Pattern,
    Realization, Scheme, SymbolRef, TypeDefInfo, TypeName, VarRef,
};

const SELF: &str = "self$accessor";

fn user() -> ModuleFullPath {
    ModuleFullPath::from("user")
}

fn vec_int() -> Type {
    Type::ADT(
        FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Vec")),
        vec![Type::Int],
    )
}

/// A concrete product `name` with `fields`, and its canonical accessor for
/// `field`, installed as typecheck installs it (`adt.rs`,
/// `synthesise_one_accessor`) and returned as a compile target.
///
/// `typed_scrutinee` retypes the scrutinee node with the product type, the
/// shape a strictly typed body has.
fn product_with_accessor(
    name: &str,
    fields: &[(&str, Type)],
    field: &str,
    typed_scrutinee: bool,
) -> (DashMap<ModuleFullPath, SymbolTable>, CallableTarget) {
    let tables = empty_tables();
    let fqtn = FQTypeName::new(user(), TypeName::from(name));
    let product = Type::ADT(fqtn.clone(), vec![]);
    let field_names: Vec<Symbol> = fields.iter().map(|(n, _)| Symbol::from(*n)).collect();
    let mut table = SymbolTable::new(user());
    install_ctor_fixture(
        &mut table,
        Symbol::from(name),
        Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Fn(
                fields.iter().map(|(_, t)| t.clone()).collect(),
                Box::new(product.clone()),
            ),
        },
        field_names.clone(),
        fqtn.clone(),
        0,
        fields.len(),
        Some(Box::new(TypeDefInfo {
            name: fqtn.clone(),
            type_params: vec![],
            constructors: vec![Symbol::from(name)],
        })),
        None,
        None,
    );

    let field_ty = fields
        .iter()
        .find(|(n, _)| *n == field)
        .map(|(_, t)| t.clone())
        .expect("accessor field");
    let self_sym = Symbol::from(SELF);
    let body = Expr::Match {
        scrutinee: Box::new(Expr::var(self_sym.clone(), Span::SYNTHETIC)),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: SymbolRef::new(None, Symbol::from(name)),
                bindings: field_names,
                span: Span::SYNTHETIC,
            },
            body: Expr::var(Symbol::from(field), Span::SYNTHETIC),
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
        compiler_generated: true,
        inferred_type: None,
    };
    let ast = DefnVariant {
        params: vec![(self_sym.clone(), None)],
        body,
        span: Span::SYNTHETIC,
    };
    let pattern_ctors = HashMap::from([(
        Span::SYNTHETIC,
        FQSymbol {
            module: user(),
            symbol: Symbol::from(name),
        },
    )]);
    let accessor = Symbol::from(format!("{name}.{field}"));
    let mut view_body = MonoExpr::synthetic_local_from_expr(&ast.body, &pattern_ctors);
    if typed_scrutinee {
        let MonoExpr::Match { scrutinee, .. } = &mut view_body else {
            panic!("accessor body is a match");
        };
        let MonoExpr::Var { ty, resolution, .. } = scrutinee.as_mut() else {
            panic!("accessor scrutinee is a variable");
        };
        assert!(matches!(resolution, VarRef::Local { .. }));
        *ty = ConcreteType::from_type(&product).expect("concrete product");
    }
    let view = MonoDefnVariant {
        name: accessor.clone(),
        params: vec![self_sym.clone()],
        body: view_body,
        span: Span::SYNTHETIC,
        mode_summary: None,
    };
    table
        .install_concrete(
            accessor.clone(),
            Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(vec![product], Box::new(field_ty)),
            },
            vec![self_sym],
            None,
            0,
            CallableOrigin::Accessor {
                type_name: fqtn,
                field: Symbol::from(field),
            },
            Realization::Body { view, code: None },
            Some(ast),
            Vec::new(),
            Visibility::Public,
        )
        .expect("install accessor");
    tables.insert(user(), table);
    (tables, binding_target(&user(), &accessor))
}

fn accessor_clif(tables: &DashMap<ModuleFullPath, SymbolTable>, target: &CallableTarget) -> String {
    let mut jit = Jit::new(tables).unwrap();
    compile_to_module(
        user(),
        std::slice::from_ref(target),
        tables,
        &std::collections::BTreeSet::new(),
        jit.jit_module(),
        true,
    )
    .expect("compile accessor")
    .clif_ir
}

fn retain_count(clif: &str) -> usize {
    clif.matches("atomic_rmw.i64 add").count()
}

// spec: design/backend/uniform-counting.md §3.4 items 1-2 — a scalar-field
// accessor of a concrete product consumes its input: one release, no retain.
#[test]
fn scalar_field_accessor_releases_its_input() {
    let (tables, target) =
        product_with_accessor("Point", &[("x", Type::Int), ("y", Type::Int)], "y", false);
    let clif = accessor_clif(&tables, &target);
    assert_eq!(
        count_release_ops(&clif),
        1,
        "the input is released once:\n{clif}"
    );
    assert_eq!(
        retain_count(&clif),
        0,
        "a scalar field needs no retain:\n{clif}"
    );
}

// spec: design/backend/uniform-counting.md §3.4 items 1-3 — an owning-field
// accessor duplicates the projected field (typed from the constructor) and
// releases its input once.
#[test]
fn owning_field_accessor_retains_its_field_and_releases_its_input() {
    let (tables, target) = product_with_accessor("Box", &[("items", vec_int())], "items", false);
    let clif = accessor_clif(&tables, &target);
    assert_eq!(
        count_release_ops(&clif),
        1,
        "the input is released once:\n{clif}"
    );
    assert_eq!(
        retain_count(&clif),
        1,
        "the returned field is retained once:\n{clif}"
    );
}

// spec: design/backend/uniform-counting.md §3.4 item 2 (NEGATIVE) — the
// placeholder is the only thing the accessor body disagrees on: the same body
// with its scrutinee node typed like its binder is counted identically, so the
// fix adds no second release where the node was already right.
#[test]
fn a_correctly_typed_scrutinee_is_released_once_neg() {
    let (tables, target) =
        product_with_accessor("Point", &[("x", Type::Int), ("y", Type::Int)], "y", true);
    let clif = accessor_clif(&tables, &target);
    assert_eq!(count_release_ops(&clif), 1, "one release, not two:\n{clif}");
}
