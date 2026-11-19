//! The constructor field channel (`design/backend/non-concrete-release-contract.md`
//! §7.4 step 1, §9 `compiler/context` row; evidence row M-1062).
//!
//! A pattern constructor's field types are read at the scrutinee's
//! instantiation. Each field takes the argument of the declared parameter it
//! mentions, whatever order the fields mention the parameters in and whether
//! every parameter is mentioned. Pairing arguments with type variables by first
//! appearance across the fields is the ACT-1062 defect: a binder then records
//! another parameter's type and its counting follows that type.

use std::collections::HashMap;

use cranelift_module::FuncId;
use cranelisp_types::{
    CallableOrigin, ConcreteType, CranelispError, DefnVariant, Expr, FQSymbol, FQTypeName,
    ModuleFullPath, Scheme, Span, Symbol, SymbolTable, SynthSpec, TemplateBody, TemplateKind, Type,
    TypeDefInfo, TypeName, Visibility,
};
use dashmap::DashMap;

use super::CompileContext;
use crate::compiler::census::Frame;
use crate::test_support::{install_ctor_fixture, install_type_fixture};

const REFERENCE: Span = Span { start: 40, end: 52 };

fn user() -> ModuleFullPath {
    ModuleFullPath::from("user")
}

fn fqtn(name: &str) -> FQTypeName {
    FQTypeName::new(user(), TypeName::from(name))
}

/// Install `name` with `params` and its constructors, each as
/// `(ctor, field types, result arguments)`. Type variable `i` is parameter
/// `i`, so a result spelled `[Var(0), Var(1)]` is the declared order.
fn install_type(
    table: &mut SymbolTable,
    name: &str,
    params: &[&str],
    ctors: Vec<(&str, Vec<Type>, Vec<Type>)>,
) {
    install_type_fixture(
        table,
        Symbol::from(name),
        TypeDefInfo {
            name: fqtn(name),
            type_params: params.iter().map(|p| Symbol::from(*p)).collect(),
            constructors: ctors.iter().map(|(c, ..)| Symbol::from(*c)).collect(),
        },
    );
    for (tag, (ctor, fields, result_args)) in ctors.into_iter().enumerate() {
        let result = Type::ADT(fqtn(name), result_args);
        let ty = if fields.is_empty() {
            result
        } else {
            Type::Fn(fields.clone(), Box::new(result))
        };
        let scheme = Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty,
        };
        let field_names: Vec<Symbol> = (0..fields.len())
            .map(|i| Symbol::from(format!("f{i}")))
            .collect();
        if scheme.ty.is_concrete() {
            install_ctor_fixture(
                table,
                Symbol::from(ctor),
                scheme,
                field_names,
                fqtn(name),
                tag,
                fields.len(),
                None,
                None,
                None,
            );
            continue;
        }
        table
            .install_template(
                Symbol::from(ctor),
                scheme,
                field_names,
                None,
                tag as u64,
                CallableOrigin::Ctor {
                    type_name: fqtn(name),
                    tag,
                    field_count: fields.len(),
                    internal: false,
                    type_def: None,
                },
                TemplateBody::Synth(SynthSpec::new(DefnVariant {
                    params: vec![],
                    body: Expr::IntLit {
                        value: tag as i64,
                        span: Span::SYNTHETIC,
                        inferred_type: Some(Box::new(Type::Int)),
                    },
                    span: Span::SYNTHETIC,
                })),
                TemplateKind::Parametric,
                vec![],
                Visibility::Public,
            )
            .expect("install constructor template");
    }
}

/// `(deftype (P a b) (MkP [:b y :a x]))`, `(deftype (R a b) (MkR [:b y]))`,
/// `(deftype (E a b) (L [:b l]) (R [:a r]))`, `(deftype (Q a b) (MkQ [:a x :b y]))`,
/// `(deftype (O a) Non (Som [:a v]))`, the nullary-constructor product `Pt`,
/// and the short declaration `Sh`.
fn tables() -> DashMap<ModuleFullPath, SymbolTable> {
    let (a, b) = (Type::Var(0), Type::Var(1));
    let in_order = || vec![Type::Var(0), Type::Var(1)];
    let mut table = SymbolTable::new(user());
    install_type(
        &mut table,
        "P",
        &["a", "b"],
        vec![("MkP", vec![b.clone(), a.clone()], in_order())],
    );
    install_type(
        &mut table,
        "R",
        &["a", "b"],
        vec![("MkR", vec![b.clone()], in_order())],
    );
    install_type(
        &mut table,
        "E",
        &["a", "b"],
        vec![
            ("L", vec![b.clone()], in_order()),
            ("Rt", vec![a.clone()], in_order()),
        ],
    );
    install_type(
        &mut table,
        "Q",
        &["a", "b"],
        vec![("MkQ", vec![a.clone(), b.clone()], in_order())],
    );
    install_type(
        &mut table,
        "O",
        &["a"],
        vec![
            ("Non", vec![], vec![Type::Var(0)]),
            ("Som", vec![a], vec![Type::Var(0)]),
        ],
    );
    install_type(&mut table, "Pt", &[], vec![("MkPt", vec![], vec![])]);
    install_short(&mut table);
    let tables = DashMap::new();
    tables.insert(user(), table);
    tables
}

/// `Sh`, whose constructor declares one field and supplies no field type.
fn install_short(table: &mut SymbolTable) {
    install_type_fixture(
        table,
        Symbol::from("Sh"),
        TypeDefInfo {
            name: fqtn("Sh"),
            type_params: vec![],
            constructors: vec![Symbol::from("MkSh")],
        },
    );
    install_ctor_fixture(
        table,
        Symbol::from("MkSh"),
        Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: at("Sh", vec![]),
        },
        vec![Symbol::from("f0")],
        fqtn("Sh"),
        0,
        1,
        None,
        None,
        None,
    );
}

fn read(
    tables: &DashMap<ModuleFullPath, SymbolTable>,
    ctor: &str,
    scrutinee: Option<&Type>,
) -> Result<Vec<Type>, CranelispError> {
    let func_ids = HashMap::new();
    let func_arities = HashMap::new();
    let ctx = CompileContext {
        func_ids: &func_ids,
        func_arities: &func_arities,
        symbol_tables: tables,
        trace_modules: &std::collections::BTreeSet::new(),
        current_module: user(),
        alloc_func_id: None,
        dealloc_func_id: FuncId::from_u32(0),
        alloc_string_func_id: None,
        panic: None,
        vec_new_func_id: None,
        vec_drop_func_id: None,
    };
    let key = FQSymbol {
        module: user(),
        symbol: Symbol::from(ctor),
    };
    ctx.ctor_field_types(&key, scrutinee, REFERENCE, &Frame::for_test())
        .map(|fields| fields.iter().map(ConcreteType::to_type).collect())
}

fn at(name: &str, args: Vec<Type>) -> Type {
    Type::ADT(fqtn(name), args)
}

// spec: design/backend/non-concrete-release-contract.md §7.4 step 1 — fields
// that mention the parameters out of declaration order each take their own
// parameter's argument: `MkP [:b y :a x]` at `(P Int String)` is
// `[String, Int]` (ACT-1062's subject; first-appearance pairing gives
// `[Int, String]`).
#[test]
fn fields_out_of_declaration_order_take_their_own_parameters() {
    let fields = read(
        &tables(),
        "MkP",
        Some(&at("P", vec![Type::Int, Type::String])),
    )
    .expect("MkP at (P Int String)");
    assert_eq!(fields, vec![Type::String, Type::Int]);
}

// spec: §7.4 step 1 — a parameter no field mentions keeps its position:
// `MkR [:b y]` at `(R Int String)` is `[String]` (first-appearance pairing
// gives `[Int]`).
#[test]
fn an_unmentioned_parameter_keeps_its_position() {
    let fields = read(
        &tables(),
        "MkR",
        Some(&at("R", vec![Type::Int, Type::String])),
    )
    .expect("MkR at (R Int String)");
    assert_eq!(fields, vec![Type::String]);
}

// spec: §7.4 step 1 — the pairing is each constructor's own declared
// parameters, not an order computed across constructors: in
// `(E a b) (L [:b l]) (Rt [:a r])` at `(E Int String)`, `Rt` binds `Int` and
// `L` binds `String`.
#[test]
fn a_sums_constructors_pair_by_declared_parameter_not_across_constructors() {
    let tables = tables();
    let scrutinee = at("E", vec![Type::Int, Type::String]);
    assert_eq!(
        read(&tables, "Rt", Some(&scrutinee)).expect("Rt"),
        vec![Type::Int]
    );
    assert_eq!(
        read(&tables, "L", Some(&scrutinee)).expect("L"),
        vec![Type::String]
    );
}

// spec: §7.4 step 1 (control) — fields in declaration order read the same
// under either pairing.
#[test]
fn fields_in_declaration_order_take_their_parameters_in_order() {
    let fields = read(
        &tables(),
        "MkQ",
        Some(&at("Q", vec![Type::Int, Type::String])),
    )
    .expect("MkQ at (Q Int String)");
    assert_eq!(fields, vec![Type::Int, Type::String]);
}

// spec: §9 `compiler/context` row (edge) — a nullary constructor has zero
// fields at its instantiation.
#[test]
fn a_nullary_constructor_has_zero_fields() {
    let fields = read(&tables(), "Non", Some(&at("O", vec![Type::String]))).expect("Non");
    assert!(fields.is_empty(), "{fields:?}");
}

// spec: §9 `compiler/context` row (edge) — a non-parametric constructor reads
// its declared fields with no arguments, whatever the scrutinee's placeholder.
#[test]
fn a_non_parametric_constructor_reads_without_arguments() {
    let tables = tables();
    assert!(read(&tables, "MkPt", None).expect("MkPt").is_empty());
    assert!(
        read(&tables, "MkPt", Some(&Type::Int))
            .expect("MkPt at a placeholder")
            .is_empty()
    );
}

// spec: §7.4 step 1 (NEGATIVE) — a parametric constructor reached without type
// arguments is a keying error, not a read of the declaration's variables.
#[test]
fn a_parametric_constructor_without_type_arguments_is_a_keying_error_neg() {
    let tables = tables();
    for scrutinee in [None, Some(Type::Int), Some(at("P", vec![]))] {
        let err = read(&tables, "MkP", scrutinee.as_ref())
            .expect_err("no arguments for a parametric constructor");
        let text = err.to_string();
        assert!(text.contains("keying"), "{text}");
        assert!(text.contains("expected 2 type argument"), "{text}");
        let CranelispError::CodegenError { location, .. } = &err else {
            panic!("expected a codegen error, got {err:?}");
        };
        assert_eq!(location.span, REFERENCE, "{text}");
    }
}

// spec: §7.4 step 1 (NEGATIVE) — a residual instantiation is a located refusal
// at the reference's span, never a field list carrying a type variable.
#[test]
fn a_residual_instantiation_is_refused_at_the_reference_neg() {
    let err = read(
        &tables(),
        "MkP",
        Some(&at("P", vec![Type::Var(7), Type::Int])),
    )
    .expect_err("a residual instantiation refuses");
    let CranelispError::CodegenError { message, location } = &err else {
        panic!("expected a codegen refusal, got {err:?}");
    };
    assert_eq!(location.span, REFERENCE, "{message}");
    assert!(!message.contains("keying"), "{message}");
}

// spec: §7.4 step 1 (NEGATIVE) — a constructor whose scheme supplies fewer
// field types than it declares fields is refused; no field is defaulted to
// `Int`.
#[test]
fn a_short_declaration_is_refused_not_defaulted_neg() {
    let err = read(&tables(), "MkSh", None).expect_err("a short declaration refuses");
    assert!(err.to_string().contains("keying"), "{err}");
}

/// Compile `(defn f [params] body)` with `f : Fn [params] Int` against
/// [`tables`], through the production per-body function.
fn compile_against_short(
    params: &[(&str, Type)],
    body: Expr,
    resolved_targets: &HashMap<Span, FQSymbol>,
    pattern_ctors: &HashMap<Span, FQSymbol>,
) -> Result<String, CranelispError> {
    use cranelisp_types::{CallableOrigin, Defn, DefnVariant};
    let tables = tables();
    let param_names: Vec<Symbol> = params.iter().map(|(p, _)| Symbol::from(*p)).collect();
    tables
        .get_mut(&user())
        .expect("user table")
        .declare(
            Symbol::from("f"),
            Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(
                    params.iter().map(|(_, t)| t.clone()).collect(),
                    Box::new(Type::Int),
                ),
            },
            param_names.clone(),
            None,
            0,
            CallableOrigin::Plain,
            Visibility::Public,
        )
        .expect("declare f");
    let defn = Defn {
        name: Symbol::from("f"),
        docstring: None,
        variants: vec![DefnVariant {
            params: param_names.into_iter().map(|p| (p, None)).collect(),
            body,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };
    let mut module = crate::test_support::make_object_module();
    crate::test_support::try_compile_defns_in_module_with_pattern_ctors(
        &[&defn],
        &[],
        resolved_targets,
        pattern_ctors,
        &tables,
        user(),
        &mut module,
        &|_| {},
    )
    .map(|mut clifs| clifs.remove(0))
}

fn mk_sh() -> FQSymbol {
    FQSymbol {
        module: user(),
        symbol: Symbol::from("MkSh"),
    }
}

/// A short declaration's refusal: a keying error located at `at`.
fn assert_short_refusal(result: Result<String, CranelispError>, at: Span) {
    let err = result.expect_err("a short declaration must refuse, not lower");
    let CranelispError::CodegenError { message, location } = &err else {
        panic!("expected a codegen refusal, got {err:?}");
    };
    assert!(message.contains("keying"), "{message}");
    assert!(message.contains("MkSh"), "{message}");
    assert_eq!(location.span, at, "{message}");
}

// spec: §7.4 step 1 (NEGATIVE) — a match arm naming a short constructor with
// no bindings is refused; it does not take the nullary bare-tag comparison, which
// would read a one-field record's heap pointer as a tag.
#[test]
fn a_short_constructor_is_not_matched_as_nullary_neg() {
    let pattern_span = Span::new(20, 24);
    let body = Expr::Match {
        scrutinee: Box::new(Expr::var(Symbol::from("b"), Span::new(10, 11))),
        arms: vec![cranelisp_types::MatchArm {
            pattern: cranelisp_types::Pattern::Constructor {
                name: cranelisp_types::SymbolRef::new(None, Symbol::from("MkSh")),
                bindings: vec![],
                span: pattern_span,
            },
            body: Expr::IntLit {
                value: 0,
                span: Span::new(30, 31),
                inferred_type: Some(Box::new(Type::Int)),
            },
            span: Span::new(19, 32),
        }],
        span: Span::new(0, 40),
        compiler_generated: false,
        inferred_type: None,
    };
    let pattern_ctors = HashMap::from([(pattern_span, mk_sh())]);
    assert_short_refusal(
        compile_against_short(
            &[("b", at("Sh", vec![]))],
            body,
            &HashMap::new(),
            &pattern_ctors,
        ),
        pattern_span,
    );
}

// spec: §6.2.1, §7.4 step 1 (NEGATIVE) — a value reference to a short
// constructor is refused; it is not folded to a bare tag.
#[test]
fn a_short_constructor_reference_is_not_a_bare_tag_neg() {
    let reference = Span::new(5, 9);
    let body = Expr::var(Symbol::from("MkSh"), reference);
    let targets = HashMap::from([(reference, mk_sh())]);
    assert_short_refusal(
        compile_against_short(&[], body, &targets, &HashMap::new()),
        reference,
    );
}

// spec: §7.4 step 1 (NEGATIVE) — constructing a short constructor is refused
// at either argument count: its arity is the declaration's, never the shortened
// field list's.
#[test]
fn a_short_constructor_call_is_refused_at_any_arity_neg() {
    for args in [
        vec![],
        vec![Expr::IntLit {
            value: 1,
            span: Span::new(12, 13),
            inferred_type: Some(Box::new(Type::Int)),
        }],
    ] {
        let callee = Span::new(6, 10);
        let call = Span::new(5, 14);
        let body = Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("MkSh"), callee)),
            args,
            span: call,
            resolved_call: None,
            inferred_type: Some(Box::new(at("Sh", vec![]))),
        };
        let targets = HashMap::from([(callee, mk_sh())]);
        let result = compile_against_short(&[], body, &targets, &HashMap::new());
        let err = result.expect_err("a short constructor call must refuse");
        let text = err.to_string();
        assert!(text.contains("keying"), "{text}");
        assert!(!text.contains("expects 0 args"), "{text}");
    }
}

// spec: §7.4 step 1 (NEGATIVE) — the type-wide constructor read refuses a type
// with a short constructor rather than reporting it with fewer fields.
#[test]
fn a_type_with_a_short_constructor_has_no_constructor_metadata_neg() {
    let tables = tables();
    let func_ids = HashMap::new();
    let func_arities = HashMap::new();
    let ctx = CompileContext {
        func_ids: &func_ids,
        func_arities: &func_arities,
        symbol_tables: &tables,
        trace_modules: &std::collections::BTreeSet::new(),
        current_module: user(),
        alloc_func_id: None,
        dealloc_func_id: FuncId::from_u32(0),
        alloc_string_func_id: None,
        panic: None,
        vec_new_func_id: None,
        vec_drop_func_id: None,
    };
    let type_def = ctx.lookup_type_def(&fqtn("Sh")).expect("Sh");
    let err = ctx
        .constructor_metas(&type_def)
        .expect_err("a short constructor has no metadata");
    assert!(err.to_string().contains("MkSh"), "{err}");
    assert!(
        ctx.constructor_metas(&ctx.lookup_type_def(&fqtn("P")).expect("P"))
            .is_ok()
    );
}

// spec: §6.2.1, §7.4 step 1 (NEGATIVE) — a short declaration yields no
// constructor record at all, so no reader can see its shortened field list as
// a bare tag or as a smaller arity; a full declaration of the same type shape
// still yields its record.
#[test]
fn a_short_declaration_builds_no_constructor_record_neg() {
    let tables = tables();
    let func_ids = HashMap::new();
    let func_arities = HashMap::new();
    let ctx = CompileContext {
        func_ids: &func_ids,
        func_arities: &func_arities,
        symbol_tables: &tables,
        trace_modules: &std::collections::BTreeSet::new(),
        current_module: user(),
        alloc_func_id: None,
        dealloc_func_id: FuncId::from_u32(0),
        alloc_string_func_id: None,
        panic: None,
        vec_new_func_id: None,
        vec_drop_func_id: None,
    };
    assert!(ctx.ctor_meta_at(&mk_sh()).is_err());
    let full = FQSymbol {
        module: user(),
        symbol: Symbol::from("MkPt"),
    };
    let (_, meta) = ctx
        .ctor_meta_at(&full)
        .expect("MkPt is fully declared")
        .expect("MkPt is a constructor");
    assert!(meta.fields.is_empty());
}
