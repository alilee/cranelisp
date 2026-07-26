//! S118 slice S1 — [`FnCompiler::emit_typed_rc_dec`] is the canonical
//! glue-CALL emitter (`design/backend/transitive-drop-glue.md` §4, §10 row 3).
//!
//! The observable claim: a release site for an owned heap value **requests the
//! canonical per-concrete-type glue from the registry**, so the module carries
//! that `Linkage::Export` symbol after body compilation. Before the migration
//! the same site expanded a depth-bounded inline field walk and minted nothing.
//!
//! These cells probe through the PRODUCTION per-body seam
//! (`test_support::compile_defns_in_module` → `compile_defn_in_module`), so
//! they pin the registry as reached from real body compilation — the exact
//! thing the S116 foundation could not do (design §3.4 D1).

use std::collections::HashMap;

use cranelift_module::{FuncOrDataId, Module};
use cranelisp_types::{
    ConcreteType, DefKind, Defn, DefnVariant, Expr, FQSymbol, FQTypeName, ModuleFullPath, Scheme,
    Span, Symbol, SymbolTable, Type, TypeDefInfo, TypeName, Visibility, drop_glue_symbol_name,
};
use dashmap::DashMap;

fn module_path() -> ModuleFullPath {
    ModuleFullPath::from("user")
}

fn wrap_fqtn() -> FQTypeName {
    FQTypeName::new(module_path(), TypeName::from("Wrap"))
}

/// `(deftype Wrap (Wrap [:String s]))` — a single-constructor product whose one
/// field is heap-owning. The smallest shape whose release must reach a field.
fn wrap_tables() -> DashMap<ModuleFullPath, SymbolTable> {
    let tables = DashMap::new();
    let mut st = SymbolTable::new(module_path());
    let fqtn = wrap_fqtn();
    st.insert(
        Symbol::from("Wrap"),
        cranelisp_types::ModuleEntry::TypeDef {
            info: TypeDefInfo {
                name: fqtn.clone(),
                type_params: vec![],
                constructors: vec![Symbol::from("MkWrap")],
            },
            visibility: Visibility::Public,
            docstring: None,
        },
    );
    st.insert(
        Symbol::from("MkWrap"),
        cranelisp_types::ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(
                    vec![Type::String],
                    Box::new(Type::ADT(fqtn.clone(), vec![])),
                ),
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![Symbol::from("s")],
            kind: Box::new(DefKind::Constructor {
                got_slot: 0,
                type_name: fqtn,
                tag: 0,
                field_count: 1,
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
    tables.insert(module_path(), st);
    tables
}

fn str_lit(span: Span) -> Expr {
    Expr::StringLit {
        value: "hi".into(),
        span,
        inferred_type: Some(Box::new(Type::String)),
    }
}

/// `(defn probe [] (let [w <binding>] 0))` compiled onto a fresh `ObjectModule`;
/// returns the module so the caller can ask which symbols body compilation
/// declared.
fn compile_let_probe(
    binding: Expr,
    resolved_targets: HashMap<Span, FQSymbol>,
) -> cranelift_object::ObjectModule {
    let body = Expr::Let {
        bindings: vec![(Symbol::from("w"), binding)],
        body: Box::new(Expr::IntLit {
            value: 0,
            span: Span::new(90, 91),
            inferred_type: Some(Box::new(Type::Int)),
        }),
        span: Span::new(1, 100),
        inferred_type: Some(Box::new(Type::Int)),
    };
    let defn = Defn {
        name: Symbol::from("probe"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };
    let tables = wrap_tables();
    let mut module = crate::test_support::make_object_module();
    crate::test_support::compile_defns_in_module(
        &[&defn],
        &[],
        &resolved_targets,
        &tables,
        module_path(),
        &mut module,
    );
    module
}

fn declares(module: &cranelift_object::ObjectModule, ty: &ConcreteType) -> bool {
    let symbol = drop_glue_symbol_name(&module_path(), ty);
    matches!(
        module.get_name(symbol.as_ref()),
        Some(FuncOrDataId::Func(_))
    )
}

// spec: appendix-c-nfr §C.1.4 — every generated release site calls the named
// drop function for the value's concrete type. A `Wrap` binding released at
// scope exit reaches its heap `String` field through the CANONICAL glue, so
// body compilation mints `String` glue in this module.
#[test]
fn a_release_site_requests_canonical_glue_for_the_owned_field_type() {
    let ctor_span = Span::new(10, 14);
    let mut targets = HashMap::new();
    targets.insert(
        ctor_span,
        FQSymbol {
            module: module_path(),
            symbol: Symbol::from("MkWrap"),
        },
    );
    let binding = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("MkWrap"),
            span: ctor_span,
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![str_lit(Span::new(15, 19))],
        span: Span::new(9, 20),
        resolved_call: None,
        inferred_type: Some(Box::new(Type::ADT(wrap_fqtn(), vec![]))),
    };
    let module = compile_let_probe(binding, targets);
    assert!(
        declares(&module, &ConcreteType::String),
        "the Wrap release site must reach its String field through canonical \
         glue — the inline depth-bounded field walk minted no symbol at all"
    );
}

// spec: appendix-c-nfr §C.1.4 (NEGATIVE) — glue is minted from DEMAND, not
// speculatively. A body whose only binding owns nothing heap requests nothing,
// so the migration adds no symbol to a scalar-only module.
#[test]
fn a_scalar_only_body_requests_no_glue_neg() {
    let binding = Expr::IntLit {
        value: 7,
        span: Span::new(10, 11),
        inferred_type: Some(Box::new(Type::Int)),
    };
    let module = compile_let_probe(binding, HashMap::new());
    assert!(!declares(&module, &ConcreteType::String));
    assert!(!declares(&module, &ConcreteType::ADT(wrap_fqtn(), vec![])));
    assert!(!declares(&module, &ConcreteType::Int));
}

// spec: appendix-c-nfr §C.1.4 (NEGATIVE, structural) — the `needs_guard`
// parameter must NOT survive on the release emitter. It was the last place a
// SITE could disagree with a TYPE about how a value is released; the nullary
// guard is now derived once, inside the glue body, from the type's own
// constructor set (`GlueShape::guard_nullary`).
#[test]
fn the_release_emitter_takes_no_needs_guard_parameter_neg() {
    let source = include_str!("../rc_emission.rs");
    let start = source
        .find("pub(crate) fn emit_typed_rc_dec(")
        .expect("the canonical release emitter must exist");
    let signature = &source[start..start + 200];
    assert!(
        !signature.contains(concat!("needs_", "guard")),
        "emit_typed_rc_dec regained a site-supplied guard parameter: {signature}"
    );
    assert!(
        !signature.contains("dealloc"),
        "emit_typed_rc_dec regained a site-supplied dealloc id: {signature}"
    );
}

// spec: appendix-c-nfr §C.1.4 (NEGATIVE) — D2: a release site that cannot
// supply a concrete type is a LOCATED error naming the type and the requesting
// function, never a shallow dec. The message is the whole diagnostic value, so
// it is pinned directly.
#[test]
fn a_non_concrete_release_type_produces_a_located_error_neg() {
    let err = super::release_site_type_error(Some(&Symbol::from("user/step")), &Type::Var(7));
    let text = err.to_string();
    assert!(
        text.contains("user/step"),
        "must name the requester: {text}"
    );
    assert!(text.contains("Var(7)"), "must name the type: {text}");
    assert!(
        text.contains("no shallow fallback"),
        "must state that no fallback exists: {text}"
    );
    // An anonymous inner body (lambda / continuation / glue body) still
    // produces a located error rather than an unattributed one.
    let anon = super::release_site_type_error(None, &Type::Var(7)).to_string();
    assert!(anon.contains("<anonymous body>"), "{anon}");
}
