//! Return protection reads the result half of the callee's derived entry
//! convention (`design/backend/non-concrete-release-contract.md` §7.6, the §9
//! "fn_compiler return protection" row). A transferred result — a compiled
//! body's or an extern shim's — needs no protective retain when it is
//! returned; an owned but unverified result keeps it. The compiled-body row is
//! pinned by `rc_emission::return_ownership_tests`.

use crate::compiler::apply::extern_entry_convention_tests::{
    call, primitive_carriers, primitives, retains_around_call, string_var,
};
use crate::test_support::*;
use cranelisp_types::{CallableOrigin, LinkerSymbol, Realization, Scheme};

// spec: spec/12-runtime.md §12.3.1 — the shim transfers an owned result, so
// returning it adds no reference the caller will not release (ACT-0974 F3).
#[test]
fn a_body_returning_string_identity_emits_no_return_protect() {
    let body = call(
        "string-identity",
        string_var("p0", 20),
        Type::String,
        10,
        true,
    );
    let carriers = primitive_carriers(&body);
    let clif = probe_caller_clif(
        &primitives(),
        &carriers,
        &[Type::String],
        Type::String,
        body,
    );
    assert_eq!(retains_around_call(&clif).1, 0, "{clif}");
}

// spec: spec/12-runtime.md §12.3.1 — a result whose ownership nothing in this
// crate checks keeps its protective retain.
#[test]
fn an_owned_unverified_result_keeps_its_return_protect() {
    let tables = primitives();
    let user = ModuleFullPath::from("user");
    let mut table = SymbolTable::new(user.clone());
    table
        .install_concrete(
            Symbol::from("facade"),
            Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(vec![Type::String], Box::new(Type::String)),
            },
            vec![Symbol::from("s")],
            None,
            0,
            CallableOrigin::RustPrimitive,
            Realization::FacadeOf {
                abi_name: LinkerSymbol::from("facade_body"),
            },
            None,
            vec![],
            Visibility::Public,
        )
        .expect("install facade fixture");
    tables.insert(user.clone(), table);
    let body = call("facade", string_var("p0", 20), Type::String, 10, false);
    let carriers = call_carriers(&body, &user, &["facade"]);
    let clif = probe_caller_clif(&tables, &carriers, &[Type::String], Type::String, body);
    assert!(retains_around_call(&clif).1 >= 1, "{clif}");
}
