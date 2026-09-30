//! Static argument lists follow the callee's derived entry convention
//! (`design/backend/non-concrete-release-contract.md` §7.6, the §9 "apply
//! static argument lists" row). An extern shim takes ownership of every heap
//! argument (BC §4a invariant 8), so a live `Var` argument is retained once
//! before the call and a temporary transfers, whatever the extern declares and
//! whichever call path reaches it.

use crate::test_support::*;
use cranelisp_types::{FQSymbol, Mode, ModeSummary, ParamFlow, ResultMode, Scheme};

pub(in crate::compiler) fn string_var(name: &str, start: u32) -> Expr {
    Expr::Var {
        name: name.into(),
        span: Span::new(start, start + 1),
        resolved_call: None,
        inferred_type: Some(Box::new(Type::String)),
    }
}

/// `(callee arg)` at span `start`, typed `result`; `builtin` selects the
/// typechecker's `BuiltinFn` resolution rather than a bare-`Var` call.
pub(in crate::compiler) fn call(
    callee: &str,
    arg: Expr,
    result: Type,
    start: u32,
    builtin: bool,
) -> Expr {
    Expr::Apply {
        callee: Box::new(Expr::Var {
            name: callee.into(),
            span: Span::new(start + 1, start + 2),
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Fn(
                vec![Type::String],
                Box::new(result.clone()),
            ))),
        }),
        args: vec![arg],
        span: Span::new(start, start + 10),
        resolved_call: builtin.then(|| {
            Box::new(cranelisp_types::ResolvedCall::BuiltinFn {
                name: callee.into(),
            })
        }),
        inferred_type: Some(Box::new(result)),
    }
}

/// The `primitives` fixture: `string-identity` declares the move of its
/// argument into its result, `str-len` a borrowed read. Neither declaration
/// is its entry's convention.
pub(in crate::compiler) fn primitives() -> DashMap<ModuleFullPath, SymbolTable> {
    let path = ModuleFullPath::from("primitives");
    let mut table = SymbolTable::new(path.clone());
    let declared = [
        (
            "string-identity",
            Type::String,
            ModeSummary {
                param_modes: vec![Mode::Owned],
                result: ResultMode::AliasOf(0),
                param_flow: vec![ParamFlow::IntoResult],
                ..ModeSummary::default()
            },
        ),
        (
            "str-len",
            Type::Int,
            ModeSummary {
                param_modes: vec![Mode::Borrowed],
                ..ModeSummary::default()
            },
        ),
    ];
    for (name, result, summary) in declared {
        table
            .install_extern(
                Symbol::from(name),
                Scheme {
                    type_vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![Type::String], Box::new(result)),
                },
                vec![Symbol::from("s")],
                None,
                0,
                None,
                Some(summary),
                Visibility::Public,
            )
            .expect("install extern fixture");
    }
    let tables = empty_tables();
    tables.insert(path, table);
    tables
}

pub(in crate::compiler) fn primitive_carriers(body: &Expr) -> HashMap<Span, FQSymbol> {
    call_carriers(
        body,
        &ModuleFullPath::from("primitives"),
        &["string-identity", "str-len"],
    )
}

/// Retains (`atomic_rmw … add`) emitted before and after the first target call.
pub(in crate::compiler) fn retains_around_call(clif: &str) -> (usize, usize) {
    let (before, after) = clif
        .split_once("call_indirect")
        .expect("the body dispatches through the GOT");
    let retains = |text: &str| {
        text.lines()
            .filter(|line| line.contains("atomic_rmw") && line.contains("add"))
            .count()
    };
    (retains(before), retains(after))
}

// spec: spec/12-runtime.md §12.3.1 items 1–2 — the shim takes the caller's
// reference, so the caller retains its live binding once (ACT-0974 F2a).
#[test]
fn a_direct_string_identity_call_retains_a_live_var_once() {
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
    assert_eq!(retains_around_call(&clif).0, 1, "{clif}");
}

// spec: spec/12-runtime.md §12.3.1 — a temporary argument transfers its one
// reference into the shim: no retain before the call, no release after it.
#[test]
fn a_temporary_argument_transfers_without_retain_or_release() {
    let literal = Expr::StringLit {
        value: "temporary".into(),
        span: Span::new(20, 31),
        inferred_type: Some(Box::new(Type::String)),
    };
    let body = call("string-identity", literal, Type::String, 10, true);
    let carriers = primitive_carriers(&body);
    let clif = probe_caller_clif(&primitives(), &carriers, &[], Type::String, body);
    assert_eq!(retains_around_call(&clif), (0, 0), "{clif}");
    assert_eq!(count_release_ops(&clif), 0, "{clif}");
}

// spec: spec/12-runtime.md §12.3.1 — a `Borrowed`-declared extern reached by
// a bare-`Var` (moded) call still consumes, so the live binding is retained.
#[test]
fn a_borrowed_declared_extern_on_a_moded_path_still_consumes() {
    let body = call("str-len", string_var("p0", 20), Type::Int, 10, false);
    let carriers = primitive_carriers(&body);
    let clif = probe_caller_clif(&primitives(), &carriers, &[Type::String], Type::Int, body);
    assert_eq!(retains_around_call(&clif).0, 1, "{clif}");
}
