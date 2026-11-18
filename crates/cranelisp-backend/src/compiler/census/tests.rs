//! The census's detection legs (`non-concrete-release-contract.md` §7.3, §9
//! census row; evidence rows CEN-1 and CEN-2).
//!
//! Each positive fixture plants one arm through the production per-body
//! function and observes the in-process tally of its own frame; each negative
//! twin is the same frame at a concrete type. Every fixture compiled as a
//! codegen target also tallies its one frame record, so a twin's tally is that
//! record alone. Frames are named per test, so the tally of one test is not
//! disturbed by another running in the process.

use std::collections::BTreeMap;

use cranelisp_types::{
    CallableOrigin, ConcreteType, FQTraitName, FQTypeName, MatchArm, MonoExpr, Pattern, Scheme,
    SymbolRef, SynthSpec, TemplateBody, TemplateKind, TraitName, TypeDefInfo, TypeName,
};

use super::{Frame, Partition, tally};
use crate::compiler::CompileContext;
use crate::test_support::*;

fn user() -> ModuleFullPath {
    ModuleFullPath::from("user")
}

fn tally_of(frame: &str) -> BTreeMap<String, u64> {
    tally(&format!("user/{frame}"))
}

fn expect(rows: &[(&str, u64)]) -> BTreeMap<String, u64> {
    rows.iter().map(|(k, v)| (k.to_string(), *v)).collect()
}

/// The tally rows of one census point, so a twin can assert that point alone.
fn point(tally: &BTreeMap<String, u64>, point: &str) -> BTreeMap<String, u64> {
    tally
        .iter()
        .filter(|(k, _)| k.starts_with(&format!("{point} ")))
        .map(|(k, v)| (k.clone(), *v))
        .collect()
}

fn origin(partition: Partition) -> CallableOrigin {
    let bx = FQTypeName::new(user(), TypeName::from("Bx"));
    match partition {
        Partition::Plain => CallableOrigin::Plain,
        Partition::Ctor => CallableOrigin::Ctor {
            type_name: bx,
            tag: 0,
            field_count: 1,
            internal: false,
            type_def: None,
        },
        Partition::Accessor => CallableOrigin::Accessor {
            type_name: bx,
            field: Symbol::from("v"),
        },
        Partition::TraitMethod => CallableOrigin::TraitMethod {
            shell: FQSymbol {
                module: user(),
                symbol: Symbol::from("impl$Size$Bx"),
            },
            trait_name: FQTraitName::new(user(), TraitName::from("Size")),
            impl_type: bx,
        },
    }
}

fn scheme(ty: Type) -> Scheme {
    Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty,
    }
}

/// Bind frame `name` with `ty` as its selected scheme and `partition` as its
/// origin, the two facts the per-body function reads from the binding. A
/// constructor or accessor cannot be declared, only settled, and a residual
/// one settles as a synthesized template.
fn declare_frame(
    table: &mut SymbolTable,
    name: &str,
    params: &[&str],
    ty: Type,
    partition: Partition,
) {
    let param_names: Vec<Symbol> = params.iter().map(|p| Symbol::from(*p)).collect();
    match partition {
        Partition::Plain | Partition::TraitMethod => table.declare(
            Symbol::from(name),
            scheme(ty),
            param_names,
            None,
            0,
            origin(partition),
            Visibility::Public,
        ),
        Partition::Ctor | Partition::Accessor => table.install_template(
            Symbol::from(name),
            scheme(ty),
            param_names.clone(),
            None,
            0,
            origin(partition),
            synth(&param_names),
            TemplateKind::Parametric,
            Vec::new(),
            Visibility::Public,
        ),
    }
    .expect("bind census frame");
}

fn synth(params: &[Symbol]) -> TemplateBody {
    TemplateBody::Synth(SynthSpec::new(DefnVariant {
        params: params.iter().map(|p| (p.clone(), None)).collect(),
        body: int(0, 0),
        span: Span::SYNTHETIC,
    }))
}

fn defn(name: &str, params: &[&str], body: Expr) -> Defn {
    Defn {
        name: Symbol::from(name),
        docstring: None,
        variants: vec![DefnVariant {
            params: params.iter().map(|p| (Symbol::from(*p), None)).collect(),
            body,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    }
}

fn int(value: i64, at: u32) -> Expr {
    Expr::IntLit {
        value,
        span: Span::new(at, at + 1),
        inferred_type: Some(Box::new(Type::Int)),
    }
}

fn var(name: &str, at: u32) -> Expr {
    Expr::var(Symbol::from(name), Span::new(at, at + 1))
}

/// Compile `defn` through the production per-body function; `edit` stands in
/// for a node type a hand-built `Expr` cannot carry.
fn compile(
    tables: &DashMap<ModuleFullPath, SymbolTable>,
    defn: &Defn,
    pattern_ctors: &HashMap<Span, FQSymbol>,
    edit: &dyn Fn(&mut MonoExpr),
) -> String {
    try_compile(tables, defn, pattern_ctors, edit).expect("census fixture compiles")
}

fn try_compile(
    tables: &DashMap<ModuleFullPath, SymbolTable>,
    defn: &Defn,
    pattern_ctors: &HashMap<Span, FQSymbol>,
    edit: &dyn Fn(&mut MonoExpr),
) -> Result<String, CranelispError> {
    let mut module = make_object_module();
    crate::test_support::try_compile_defns_in_module_with_pattern_ctors(
        &[defn],
        &[],
        &HashMap::new(),
        pattern_ctors,
        tables,
        user(),
        &mut module,
        edit,
    )
    .map(|mut clifs| clifs.remove(0))
}

fn no_edit(_: &mut MonoExpr) {}

fn tables_with(table: SymbolTable) -> DashMap<ModuleFullPath, SymbolTable> {
    let tables = empty_tables();
    tables.insert(user(), table);
    tables
}

/// `(defn name [x] body)` with `x : param`, in `partition`.
fn try_one_param_frame(
    name: &str,
    param: Type,
    body: Expr,
    partition: Partition,
) -> Result<String, CranelispError> {
    let mut table = SymbolTable::new(user());
    declare_frame(
        &mut table,
        name,
        &["x"],
        Type::Fn(vec![param], Box::new(Type::Int)),
        partition,
    );
    let tables = tables_with(table);
    try_compile(
        &tables,
        &defn(name, &["x"], body),
        &HashMap::new(),
        &no_edit,
    )
}

fn one_param_frame(name: &str, param: Type, body: Expr, partition: Partition) {
    try_one_param_frame(name, param, body, partition).expect("census fixture compiles");
}

// --- Residual parameters ---

/// `(let [a x] x)`: `x` is duplicated into `a` and moved out.
fn duplicated(at: u32) -> Expr {
    Expr::Let {
        bindings: vec![(Symbol::from("a"), var("x", at))],
        body: Box::new(var("x", at + 10)),
        span: Span::new(at, at + 20),
        inferred_type: None,
    }
}

// spec: design/backend/non-concrete-release-contract.md §7.4 step 2, §9 —
// the retain and release arms are gone: a parameter is typed once, from its
// target's concrete scheme, so a residual one (a bare `Var` or an
// `ADT(<concrete>, [Var…])`, in any partition) is a located invariant error
// where the target is selected. Nothing reaches a category, a duplicate, a
// release or a field read, so the frame is its only record.
#[test]
fn a_residual_parameter_is_refused_where_its_target_is_selected() {
    let bx_var = Type::ADT(
        FQTypeName::new(user(), TypeName::from("Bx")),
        vec![Type::Var(0)],
    );
    for (partition, name) in [
        (Partition::Plain, "Plain"),
        (Partition::Ctor, "Ctor"),
        (Partition::Accessor, "Accessor"),
        (Partition::TraitMethod, "TraitMethod"),
    ] {
        for (residual, shape) in [(Type::Var(0), "var"), (bx_var.clone(), "adt")] {
            for (body, use_) in [(duplicated(1), "duplicated"), (int(0, 1), "dropped")] {
                let frame = format!("census_residual_{name}_{shape}_{use_}");
                let refused = try_one_param_frame(&frame, residual.clone(), body, partition)
                    .expect_err("a residual parameter is refused");
                assert!(
                    refused.to_string().contains("non-concrete parameter type"),
                    "{frame}: {refused}"
                );
                assert_eq!(
                    tally_of(&frame),
                    expect(&[(&format!("frame {name} - -"), 1)]),
                    "{frame}"
                );
            }
        }
    }
}

// spec: design/backend/non-concrete-release-contract.md §7.4 step 2 (NEGATIVE)
// — the same frames at a concrete heap type compile and record nothing.
#[test]
fn a_concrete_parameter_duplicated_or_dropped_records_nothing_neg() {
    one_param_frame(
        "census_retain_twin",
        Type::String,
        duplicated(1),
        Partition::Plain,
    );
    assert_eq!(
        tally_of("census_retain_twin"),
        expect(&[("frame Plain - -", 1)])
    );
    one_param_frame(
        "census_release_twin",
        Type::String,
        int(0, 1),
        Partition::Plain,
    );
    assert_eq!(
        tally_of("census_release_twin"),
        expect(&[("frame Plain - -", 1)])
    );
}

// --- Absent ---

/// `(defn name [] (fn [p] 0))`, with the `Lambda` node given `lambda_ty`.
fn lambda_frame(name: &str, lambda_ty: ConcreteType, partition: Partition) {
    try_lambda_frame(name, lambda_ty, partition).expect("census fixture compiles");
}

/// The lambda's span, at which a refusal of its parameter is located.
fn lambda_span() -> Span {
    Span::new(1, 10)
}

fn try_lambda_frame(
    name: &str,
    lambda_ty: ConcreteType,
    partition: Partition,
) -> Result<String, CranelispError> {
    let mut table = SymbolTable::new(user());
    declare_frame(
        &mut table,
        name,
        &[],
        Type::Fn(vec![], Box::new(Type::Int)),
        partition,
    );
    let tables = tables_with(table);
    let body = Expr::Lambda {
        params: vec![(Symbol::from("p"), None)],
        body: Box::new(int(0, 5)),
        span: lambda_span(),
        inferred_type: None,
    };
    let retype = move |body: &mut MonoExpr| {
        let MonoExpr::Lambda { ty, .. } = body else {
            panic!("the frame's body is the lambda");
        };
        *ty = lambda_ty.clone();
    };
    try_compile(&tables, &defn(name, &[], body), &HashMap::new(), &retype)
}

/// A refusal located at `span`.
fn assert_located(refused: &CranelispError, span: Span) {
    let CranelispError::CodegenError { location, .. } = refused else {
        panic!("expected a codegen refusal, got {refused:?}");
    };
    assert_eq!(location.span, span, "{refused}");
}

// spec: design/backend/non-concrete-release-contract.md §7.3, §7.4 step 2,
// §9 — a `Lambda` node whose type is not a function type is a producer
// refusal located at the lambda. The absent point keeps recording there: one
// record, made by the inner compiler and carried in the frame's partition.
#[test]
fn an_untyped_lambda_parameter_is_refused_and_records_one_absent() {
    let refused = try_lambda_frame("census_absent_lambda", ConcreteType::Int, Partition::Plain)
        .expect_err("an untyped lambda parameter is refused");
    assert_located(&refused, lambda_span());
    assert_eq!(
        tally_of("census_absent_lambda"),
        expect(&[("absent Plain absent -", 1), ("frame Plain - -", 1)])
    );
    try_lambda_frame(
        "census_absent_inner",
        ConcreteType::Int,
        Partition::TraitMethod,
    )
    .expect_err("an untyped lambda parameter is refused");
    assert_eq!(
        tally_of("census_absent_inner"),
        expect(&[
            ("absent TraitMethod absent -", 1),
            ("frame TraitMethod - -", 1),
        ])
    );
}

// spec: design/backend/non-concrete-release-contract.md §7.3 (NEGATIVE) — the
// same lambda typed as a function, at a scalar and at a heap parameter,
// records nothing on the absent arm.
#[test]
fn a_function_typed_lambda_parameter_records_nothing_neg() {
    let fn_of = |param| ConcreteType::Fn(vec![param], Box::new(ConcreteType::Int));
    lambda_frame(
        "census_absent_twin_int",
        fn_of(ConcreteType::Int),
        Partition::Plain,
    );
    assert_eq!(
        tally_of("census_absent_twin_int"),
        expect(&[("frame Plain - -", 1)])
    );
    lambda_frame(
        "census_absent_twin_str",
        fn_of(ConcreteType::String),
        Partition::Plain,
    );
    assert_eq!(
        tally_of("census_absent_twin_str"),
        expect(&[("frame Plain - -", 1)])
    );
}

// spec: design/backend/non-concrete-release-contract.md §7.3, §7.4 step 2,
// §9 — a defn with a parameter and a non-function scheme is a located
// invariant error where its target is selected, and records one absent.
#[test]
fn a_defn_parameter_the_scheme_does_not_type_is_refused_and_records_one_absent() {
    let mut table = SymbolTable::new(user());
    declare_frame(
        &mut table,
        "census_absent_defn",
        &["x"],
        Type::Int,
        Partition::Plain,
    );
    let tables = tables_with(table);
    let refused = try_compile(
        &tables,
        &defn("census_absent_defn", &["x"], int(0, 1)),
        &HashMap::new(),
        &no_edit,
    )
    .expect_err("an untyped defn parameter is refused");
    assert!(refused.to_string().contains("types 0"), "{refused}");
    assert_located(&refused, Span::SYNTHETIC);
    assert_eq!(
        tally_of("census_absent_defn"),
        expect(&[("absent Plain absent -", 1), ("frame Plain - -", 1)])
    );
}

/// Compile a defn with `params` against `scheme`, expecting the parameter
/// channel's refusal, and return its message.
fn refused_defn_frame(name: &str, params: &[&str], scheme: Type) -> String {
    let mut table = SymbolTable::new(user());
    declare_frame(&mut table, name, params, scheme, Partition::Plain);
    let tables = tables_with(table);
    let refused = try_compile(
        &tables,
        &defn(name, params, int(0, 1)),
        &HashMap::new(),
        &no_edit,
    )
    .expect_err("a scheme not typing exactly the parameters is refused");
    assert_located(&refused, Span::SYNTHETIC);
    refused.to_string()
}

// spec: design/backend/non-concrete-release-contract.md §7.3, §7.4 (B4′),
// §9 (edge) — a two-parameter defn whose scheme types one parameter is
// refused, and records one absent per parameter of the refused list: two.
#[test]
fn a_two_parameter_short_scheme_records_two_absent() {
    let scheme = Type::Fn(vec![Type::Int], Box::new(Type::Int));
    let refused = refused_defn_frame("census_absent_short2", &["x", "y"], scheme);
    assert!(refused.contains("has 2 parameter(s)"), "{refused}");
    assert!(refused.contains("types 1"), "{refused}");
    assert_eq!(
        tally_of("census_absent_short2"),
        expect(&[("absent Plain absent -", 2), ("frame Plain - -", 1)])
    );
}

// spec: design/backend/non-concrete-release-contract.md §7.3, §7.4 (B4′),
// §9 (NEGATIVE) — a scheme with more parameter types than the defn has
// parameters is a located invariant error, never an ignored excess, with one
// absent record per parameter.
#[test]
fn an_excess_scheme_is_refused_and_records_one_absent_per_parameter_neg() {
    let scheme = Type::Fn(vec![Type::Int, Type::String], Box::new(Type::Int));
    let refused = refused_defn_frame("census_absent_excess", &["x"], scheme);
    assert!(refused.contains("has 1 parameter(s)"), "{refused}");
    assert!(refused.contains("types 2"), "{refused}");
    assert_eq!(
        tally_of("census_absent_excess"),
        expect(&[("absent Plain absent -", 1), ("frame Plain - -", 1)])
    );
}

// spec: design/backend/non-concrete-release-contract.md §7.3 (NEGATIVE) — a
// scalar parameter the scheme types is not absent.
#[test]
fn a_scheme_typed_scalar_parameter_records_nothing_neg() {
    one_param_frame(
        "census_absent_defn_twin",
        Type::Int,
        int(0, 1),
        Partition::Plain,
    );
    assert_eq!(
        tally_of("census_absent_defn_twin"),
        expect(&[("frame Plain - -", 1)])
    );
}

// --- Field reads ---

fn bx() -> FQTypeName {
    FQTypeName::new(user(), TypeName::from("Bx"))
}

fn pt() -> FQTypeName {
    FQTypeName::new(user(), TypeName::from("Pt"))
}

/// `(deftype (Bx a) [:a v])` and `(deftype Pt [:Int v])`. `short` drops the
/// field types from `Pt`'s constructor scheme.
fn product_table(short: bool) -> SymbolTable {
    let mut table = SymbolTable::new(user());
    let products = [
        (
            bx(),
            vec![Symbol::from("a")],
            Type::Var(0),
            vec![Type::Var(0)],
        ),
        (pt(), vec![], Type::Int, vec![]),
    ];
    for (fqtn, type_params, field, args) in products {
        let name = Symbol::from(fqtn.name.as_ref());
        let result = Type::ADT(fqtn.clone(), args);
        let generic = !type_params.is_empty();
        let ctor_ty = if short && !generic {
            result
        } else {
            Type::Fn(vec![field], Box::new(result))
        };
        let type_def = Some(Box::new(TypeDefInfo {
            name: fqtn.clone(),
            type_params,
            constructors: vec![name.clone()],
        }));
        let fields = vec![Symbol::from("v")];
        if generic {
            // A generic constructor has no slot: it settles as a template.
            table
                .install_template(
                    name,
                    scheme(ctor_ty),
                    fields.clone(),
                    None,
                    0,
                    CallableOrigin::Ctor {
                        type_name: fqtn,
                        tag: 0,
                        field_count: 1,
                        internal: false,
                        type_def,
                    },
                    synth(&fields),
                    TemplateKind::Parametric,
                    Vec::new(),
                    Visibility::Public,
                )
                .expect("install generic constructor");
        } else {
            install_ctor_fixture(
                &mut table,
                name,
                scheme(ctor_ty),
                fields,
                fqtn,
                0,
                1,
                type_def,
                None,
                None,
            );
        }
    }
    table
}

/// `(defn name [b] (match b [(Ctor v) 0]))` with `b : scrutinee`.
fn match_frame(name: &str, ctor: &FQTypeName, scrutinee: Type, short: bool) {
    try_match_frame(name, ctor, scrutinee, short).expect("census fixture compiles");
}

fn try_match_frame(
    name: &str,
    ctor: &FQTypeName,
    scrutinee: Type,
    short: bool,
) -> Result<String, CranelispError> {
    let mut table = product_table(short);
    declare_frame(
        &mut table,
        name,
        &["b"],
        Type::Fn(vec![scrutinee], Box::new(Type::Int)),
        Partition::Plain,
    );
    let tables = tables_with(table);
    let pattern_span = Span::new(20, 25);
    let body = Expr::Match {
        scrutinee: Box::new(var("b", 1)),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: SymbolRef::new(None, Symbol::from(ctor.name.as_ref())),
                bindings: vec![Symbol::from("v")],
                span: pattern_span,
            },
            body: int(0, 30),
            span: Span::new(19, 32),
        }],
        span: Span::new(0, 40),
        compiler_generated: false,
        inferred_type: None,
    };
    let pattern_ctors = HashMap::from([(
        pattern_span,
        FQSymbol {
            module: user(),
            symbol: Symbol::from(ctor.name.as_ref()),
        },
    )]);
    try_compile(&tables, &defn(name, &["b"], body), &pattern_ctors, &no_edit)
}

// spec: design/backend/non-concrete-release-contract.md §7.3, §7.4 step 1 — a
// match on a generic product whose scrutinee carries no arguments records one
// field read in the absent class, and the read then refuses it as a keying
// error: this traffic cannot reach emission.
#[test]
fn a_generic_product_matched_without_arguments_records_an_absent_field_read() {
    let refused = try_match_frame("census_field_absent", &bx(), Type::ADT(bx(), vec![]), false)
        .expect_err("a field read without the type's arguments refuses");
    assert!(
        refused.to_string().contains("expected 1 type argument"),
        "{refused}"
    );
    assert_eq!(
        point(&tally_of("census_field_absent"), "field"),
        expect(&[("field Plain full absent", 1)])
    );
}

// spec: design/backend/non-concrete-release-contract.md §7.3 (NEGATIVE) — the
// same match at a concrete instantiation records once in the concrete class,
// which is also the proof that the point executes.
#[test]
fn a_generic_product_matched_at_a_concrete_instantiation_reads_concrete_neg() {
    match_frame(
        "census_field_twin",
        &bx(),
        Type::ADT(bx(), vec![Type::Int]),
        false,
    );
    assert_eq!(
        tally_of("census_field_twin"),
        expect(&[("field Plain full concrete", 1), ("frame Plain - -", 1)])
    );
}

// spec: design/backend/non-concrete-release-contract.md §7.3 (edge) — a
// non-parametric product's field read is concrete, and its scalar field
// records nothing on the absent arm.
#[test]
fn a_non_parametric_products_field_read_is_concrete() {
    match_frame("census_field_pt", &pt(), Type::ADT(pt(), vec![]), false);
    assert_eq!(
        tally_of("census_field_pt"),
        expect(&[("field Plain full concrete", 1), ("frame Plain - -", 1)])
    );
}

// spec: design/backend/non-concrete-release-contract.md §7.3, §7.4 step 1 — a
// constructor whose scheme supplies fewer field types than its field count is
// recorded in the field record's shape, and then refused.
#[test]
fn a_short_constructor_declaration_is_recorded_in_the_shape() {
    let refused = try_match_frame("census_field_short", &pt(), Type::ADT(pt(), vec![]), true)
        .expect_err("a short declaration refuses");
    assert!(refused.to_string().contains("keying drift"), "{refused}");
    assert_eq!(
        point(&tally_of("census_field_short"), "field"),
        expect(&[("field Plain short concrete", 1)])
    );
}

// spec: design/backend/non-concrete-release-contract.md §7.3, §7.4 step 1 —
// the residual class, at the read itself: the match lowering hands the read
// its scrutinee's counted type, which is concrete by construction, so this
// class is planted at the seam (see the next cell). The residual read is
// refused at the reference and the argument-less one as a keying error; each
// records first.
#[test]
fn a_field_read_at_a_residual_instantiation_records_the_residual_class() {
    let tables = tables_with(product_table(false));
    let func_ids = HashMap::new();
    let func_arities = HashMap::new();
    let ctx = CompileContext {
        func_ids: &func_ids,
        func_arities: &func_arities,
        symbol_tables: &tables,
        current_module: user(),
        alloc_func_id: None,
        dealloc_func_id: cranelift_module::FuncId::from_u32(0),
        alloc_string_func_id: None,
        panic_func_id: None,
        vec_new_func_id: None,
        vec_drop_func_id: None,
    };
    let key = FQSymbol {
        module: user(),
        symbol: Symbol::from("Bx"),
    };
    let frame = |name: &str| Frame::new(Partition::Accessor, &user(), &Symbol::from(name));
    let reference = Span::new(7, 9);
    let residual = Type::ADT(bx(), vec![Type::Var(0)]);
    let refused = ctx
        .ctor_field_types(
            &key,
            Some(&residual),
            reference,
            &frame("census_seam_residual"),
        )
        .expect_err("a residual instantiation refuses");
    let CranelispError::CodegenError { location, .. } = &refused else {
        panic!("expected a codegen refusal, got {refused:?}");
    };
    assert_eq!(location.span, reference);
    assert_eq!(
        tally_of("census_seam_residual"),
        expect(&[("field Accessor full residual", 1)])
    );
    let concrete = Type::ADT(bx(), vec![Type::String]);
    ctx.ctor_field_types(&key, Some(&concrete), reference, &frame("census_seam_twin"))
        .expect("Bx resolves");
    assert_eq!(
        tally_of("census_seam_twin"),
        expect(&[("field Accessor full concrete", 1)])
    );
    ctx.ctor_field_types(&key, None, reference, &frame("census_seam_none"))
        .expect_err("a parametric constructor without arguments refuses");
    assert_eq!(
        tally_of("census_seam_none"),
        expect(&[("field Accessor full absent", 1)])
    );
}

// spec: design/backend/non-concrete-release-contract.md §7.3, §7.4 step 2 —
// the F1 shape: an accessor of a generic product matching its own residual
// parameter. The parameter is refused where the target is selected, so the
// match never reads a field.
#[test]
fn a_match_on_a_residual_parameter_is_refused_before_its_field_read() {
    let refused = try_match_frame(
        "census_field_f1",
        &bx(),
        Type::ADT(bx(), vec![Type::Var(0)]),
        false,
    )
    .expect_err("a residual parameter is refused");
    assert!(
        refused.to_string().contains("non-concrete parameter type"),
        "{refused}"
    );
    assert_eq!(point(&tally_of("census_field_f1"), "field"), expect(&[]));
}

// --- The production target selection ---

// spec: design/backend/non-concrete-release-contract.md §7.3 "Key" — the
// partition is taken where `compile_to_module` selects the codegen target: an
// installed accessor of `(Bx Int)` records its concrete field read as
// `Accessor`.
#[test]
fn compile_to_module_attributes_records_to_the_targets_partition() {
    let mut table = product_table(false);
    let name = Symbol::from("Bx.v$census");
    let self_sym = Symbol::from("self");
    let pattern_span = Span::SYNTHETIC;
    let body = Expr::Match {
        scrutinee: Box::new(Expr::var(self_sym.clone(), Span::SYNTHETIC)),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: SymbolRef::new(None, Symbol::from("Bx")),
                bindings: vec![Symbol::from("v")],
                span: pattern_span,
            },
            body: Expr::var(Symbol::from("v"), Span::SYNTHETIC),
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
        compiler_generated: true,
        inferred_type: None,
    };
    let pattern_ctors = HashMap::from([(
        pattern_span,
        FQSymbol {
            module: user(),
            symbol: Symbol::from("Bx"),
        },
    )]);
    let ast = DefnVariant {
        params: vec![(self_sym.clone(), None)],
        body,
        span: Span::SYNTHETIC,
    };
    let view = cranelisp_types::MonoDefnVariant {
        name: name.clone(),
        params: vec![self_sym.clone()],
        body: MonoExpr::synthetic_local_from_expr(&ast.body, &pattern_ctors),
        span: Span::SYNTHETIC,
        mode_summary: None,
    };
    table
        .install_concrete(
            name.clone(),
            scheme(Type::Fn(
                vec![Type::ADT(bx(), vec![Type::Int])],
                Box::new(Type::Int),
            )),
            vec![self_sym],
            None,
            0,
            origin(Partition::Accessor),
            cranelisp_types::Realization::Body { view, code: None },
            Some(ast),
            Vec::new(),
            Visibility::Public,
        )
        .expect("install accessor");
    let tables = tables_with(table);
    let mut jit = Jit::new(&tables).unwrap();
    compile_to_module(
        user(),
        &[binding_target(&user(), &name)],
        &tables,
        jit.jit_module(),
        false,
    )
    .expect("compile accessor");
    assert_eq!(
        tally(&format!("user/{name}")),
        expect(&[
            ("field Accessor full concrete", 1),
            ("frame Accessor - -", 1)
        ])
    );
}

/// Install `(defn name [] body)` as a concrete codegen target whose binding
/// carries `partition`'s origin.
fn install_target(table: &mut SymbolTable, name: &str, partition: Partition, body: Expr) {
    let name = Symbol::from(name);
    let ast = DefnVariant {
        params: vec![],
        body,
        span: Span::SYNTHETIC,
    };
    let view = cranelisp_types::MonoDefnVariant {
        name: name.clone(),
        params: vec![],
        body: MonoExpr::synthetic_local_from_expr(&ast.body, &HashMap::new()),
        span: Span::SYNTHETIC,
        mode_summary: None,
    };
    table
        .install_concrete(
            name,
            scheme(Type::Fn(vec![], Box::new(Type::Int))),
            vec![],
            None,
            0,
            origin(partition),
            cranelisp_types::Realization::Body { view, code: None },
            Some(ast),
            Vec::new(),
            Visibility::Public,
        )
        .expect("install census target");
}

// spec: design/backend/non-concrete-release-contract.md §7.3 "The frame
// record" — compiling N targets through `compile_to_module` records N frames,
// one per target, each in its target's partition. An inner compiler (the
// lambda) records no frame of its own, and a binding that is not a target
// records none (NEGATIVE).
#[test]
fn compiling_n_targets_records_n_frames_each_in_its_partition() {
    let mut table = SymbolTable::new(user());
    let targets = [
        ("census_frames_plain", Partition::Plain, "Plain"),
        ("census_frames_accessor", Partition::Accessor, "Accessor"),
        (
            "census_frames_method",
            Partition::TraitMethod,
            "TraitMethod",
        ),
    ];
    // A synthesized body carries only synthetic spans.
    let zero = || Expr::IntLit {
        value: 0,
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    };
    for (name, partition, _) in targets {
        install_target(&mut table, name, partition, zero());
    }
    let lambda = Expr::Lambda {
        params: vec![],
        body: Box::new(zero()),
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Fn(vec![], Box::new(Type::Int)))),
    };
    install_target(&mut table, "census_frames_lambda", Partition::Plain, lambda);
    install_target(
        &mut table,
        "census_frames_unselected",
        Partition::Plain,
        zero(),
    );
    let tables = tables_with(table);
    let names: Vec<Symbol> = targets
        .iter()
        .map(|(name, ..)| *name)
        .chain(["census_frames_lambda"])
        .map(Symbol::from)
        .collect();
    let mut jit = Jit::new(&tables).unwrap();
    compile_to_module(
        user(),
        &binding_targets(&user(), &names),
        &tables,
        jit.jit_module(),
        false,
    )
    .expect("compile census targets");
    for (name, _, partition) in targets {
        assert_eq!(
            tally_of(name),
            expect(&[(&format!("frame {partition} - -"), 1)]),
            "{name}"
        );
    }
    assert_eq!(
        point(&tally_of("census_frames_lambda"), "frame"),
        expect(&[("frame Plain - -", 1)])
    );
    assert_eq!(tally_of("census_frames_unselected"), expect(&[]));
}

// --- The census file and emission (CEN-2) ---

const CENSUS_VAR: &str = "CRANELISP_CATEGORY_CENSUS";

/// Child body: compile a concrete frame, plant an absent field read under it
/// at the read itself (a frame making one no longer compiles, §7.4 step 1),
/// attempt a second frame whose untyped lambda parameter is refused and
/// records an absent binder, and write the first frame's CLIF to the path the
/// parent names.
#[test]
fn census_file_child() {
    if !crate::test_child::selected("census_file_child") {
        return;
    }
    let mut table = product_table(false);
    declare_frame(
        &mut table,
        "census_child",
        &["b"],
        Type::Fn(vec![Type::ADT(bx(), vec![Type::Int])], Box::new(Type::Int)),
        Partition::TraitMethod,
    );
    let tables = tables_with(table);
    let pattern_span = Span::new(20, 25);
    let body = Expr::Match {
        scrutinee: Box::new(var("b", 1)),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: SymbolRef::new(None, Symbol::from("Bx")),
                bindings: vec![Symbol::from("v")],
                span: pattern_span,
            },
            body: int(0, 30),
            span: Span::new(19, 32),
        }],
        span: Span::new(0, 40),
        compiler_generated: false,
        inferred_type: None,
    };
    let pattern_ctors = HashMap::from([(
        pattern_span,
        FQSymbol {
            module: user(),
            symbol: Symbol::from("Bx"),
        },
    )]);
    let clif = compile(
        &tables,
        &defn("census_child", &["b"], body),
        &pattern_ctors,
        &no_edit,
    );
    let func_ids = HashMap::new();
    let func_arities = HashMap::new();
    let ctx = CompileContext {
        func_ids: &func_ids,
        func_arities: &func_arities,
        symbol_tables: &tables,
        current_module: user(),
        alloc_func_id: None,
        dealloc_func_id: cranelift_module::FuncId::from_u32(0),
        alloc_string_func_id: None,
        panic_func_id: None,
        vec_new_func_id: None,
        vec_drop_func_id: None,
    };
    ctx.ctor_field_types(
        &FQSymbol {
            module: user(),
            symbol: Symbol::from("Bx"),
        },
        None,
        Span::SYNTHETIC,
        &Frame::new(
            Partition::TraitMethod,
            &user(),
            &Symbol::from("census_child"),
        ),
    )
    .expect_err("an absent field read refuses");
    try_lambda_frame(
        "census_child_absent",
        ConcreteType::Int,
        Partition::TraitMethod,
    )
    .expect_err("an untyped lambda parameter is refused");
    let out: String = crate::test_child::arg("CENSUS_CHILD_CLIF");
    std::fs::write(out, clif).expect("write the child's CLIF");
}

// spec: design/backend/non-concrete-release-contract.md §7.3 "Output" and §8
// reject 14 (evidence CEN-2) — with the variable set the child appends one
// line per reported record to the file and nothing to either stream; unset, it
// writes no file; and the CLIF is identical either way.
#[test]
fn the_census_file_is_written_only_when_set_and_emission_is_unchanged() {
    let dir = std::env::temp_dir().join(format!("census-cen2-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let census = dir.join("census.tsv");
    let _ = std::fs::remove_file(&census);
    let path = crate::test_child::child_path(module_path!(), "census_file_child");
    let run = |clif: &std::path::Path, set: bool| {
        let mut env = vec![("CENSUS_CHILD_CLIF", clif.display().to_string())];
        if set {
            env.push((CENSUS_VAR, census.display().to_string()));
        }
        let ending = crate::test_child::run(&path, &env);
        assert_eq!(ending.code, Some(0), "child failed:\n{}", ending.stderr);
        ending
    };

    let unset_clif = dir.join("unset.clif");
    let unset = run(&unset_clif, false);
    assert!(!census.exists(), "no census file without the variable");

    let set_clif = dir.join("set.clif");
    let set = run(&set_clif, true);
    let lines = std::fs::read_to_string(&census).expect("the census file is written");
    let distinct: std::collections::BTreeSet<&str> = lines.lines().collect();
    assert_eq!(
        distinct,
        [
            "absent\tTraitMethod\tabsent\t-\tuser/census_child_absent",
            "field\tTraitMethod\tfull\tabsent\tuser/census_child",
            "frame\tTraitMethod\t-\t-\tuser/census_child",
            "frame\tTraitMethod\t-\t-\tuser/census_child_absent",
        ]
        .into_iter()
        .collect(),
        "the frame's reported records, and only those:\n{lines}"
    );
    assert_eq!(
        lines
            .lines()
            .filter(|line| line.starts_with("frame\t"))
            .count(),
        2,
        "two frames compiled, two frame lines:\n{lines}"
    );
    // Both streams carry libtest's own lines and nothing else, in either run,
    // so census output of any form on either stream fails here.
    let libtest_line = |line: &str| {
        line.is_empty()
            || line == "running 1 test"
            || line == format!("test {path} ... ok")
            || line.starts_with("test result: ok. 1 passed; 0 failed;")
    };
    for (run, ending) in [("unset", &unset), ("set", &set)] {
        assert_eq!(ending.stderr, "", "{run}: the child wrote to stderr");
        let foreign: Vec<&str> = ending.stdout.lines().filter(|l| !libtest_line(l)).collect();
        assert!(
            foreign.is_empty(),
            "{run}: the child wrote to stdout:\n{}",
            ending.stdout
        );
    }
    assert_eq!(
        std::fs::read_to_string(&set_clif).unwrap(),
        std::fs::read_to_string(&unset_clif).unwrap(),
        "emission depends on the census variable"
    );
    let _ = std::fs::remove_dir_all(&dir);
}
