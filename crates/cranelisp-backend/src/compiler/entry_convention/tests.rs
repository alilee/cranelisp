//! The entry-convention derivation, row by row
//! (`design/backend/non-concrete-release-contract.md` §7.6 and the §9
//! derivation row). Exhaustiveness over `Life` × `Realization` is enforced by
//! the compiler and needs no row here.

use super::{EntryConvention, ParamKind, ResultKind};
use cranelisp_types::{
    CallableSlot, CallableTarget, FQSymbol, Life, LinkerSymbol, Mode, ModeSummary, ModuleFullPath,
    ParamFlow, Realization, ResultMode, Scheme, Span, Symbol, SymbolTable, Type, Visibility,
};
use std::collections::HashMap;

const HEAP_POSITIONS: usize = 3;

fn declared(param_modes: Vec<Mode>, result: ResultMode) -> ModeSummary {
    ModeSummary {
        param_modes,
        result,
        ..ModeSummary::default()
    }
}

/// `(Borrowed, Owned, Copy)` with a `Fresh` result: one position of each kind.
fn mixed_summary() -> ModeSummary {
    declared(
        vec![Mode::Borrowed, Mode::Owned, Mode::Copy],
        ResultMode::Fresh,
    )
}

fn string_scheme(arity: usize) -> Scheme {
    Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty: Type::Fn(vec![Type::String; arity], Box::new(Type::String)),
    }
}

fn params(convention: &EntryConvention) -> Vec<ParamKind> {
    (0..HEAP_POSITIONS).map(|i| convention.param(i)).collect()
}

fn consumes(convention: &EntryConvention) -> bool {
    convention.consumes_every_param()
        && params(convention)
            .iter()
            .all(|kind| *kind == ParamKind::Consume)
}

/// A slot minted by a real table, since `CallableSlot` has no public
/// constructor.
fn slot() -> CallableSlot {
    let mut table: SymbolTable = SymbolTable::new(ModuleFullPath::from("fixture"));
    table
        .install_extern(
            Symbol::from("f"),
            string_scheme(1),
            vec![Symbol::from("s")],
            None,
            0,
            None,
            None,
            Visibility::Public,
        )
        .expect("mint a fixture slot")
}

fn concrete(realization: Realization, mode_summary: Option<ModeSummary>) -> Life {
    Life::Concrete {
        slot: slot(),
        realization,
        minted_from: None,
        ast: None,
        callees: vec![],
        value_use: true,
        mode_summary,
    }
}

fn body(mode_summary: Option<ModeSummary>) -> Life {
    let variant = cranelisp_types::DefnVariant {
        params: vec![("a".into(), None), ("b".into(), None), ("c".into(), None)],
        body: cranelisp_types::Expr::IntLit {
            value: 0,
            span: Span::SYNTHETIC,
            inferred_type: Some(Box::new(Type::Int)),
        },
        span: Span::SYNTHETIC,
    };
    let mut view =
        crate::test_support::test_codegen_view(&Symbol::from("f"), &variant, &HashMap::new());
    view.mode_summary = mode_summary.clone();
    concrete(Realization::Body { view, code: None }, mode_summary)
}

fn extern_shim(mode_summary: Option<ModeSummary>) -> Life {
    concrete(
        Realization::ExternShim {
            borrowed_sibling: None,
        },
        mode_summary,
    )
}

// --- Body rows: the only realization that can borrow. ---

#[test]
fn body_summary_yields_its_own_kinds_and_a_transferred_result() {
    let convention = EntryConvention::of(Some(&body(Some(mixed_summary()))));
    assert_eq!(
        params(&convention),
        [
            ParamKind::Borrow,
            ParamKind::Consume,
            ParamKind::NoReference
        ]
    );
    assert!(!convention.consumes_every_param());
    assert_eq!(convention.result(), ResultKind::Transferred);
}

#[test]
fn body_without_a_summary_or_with_a_conservative_one_consumes() {
    for summary in [
        None,
        Some(declared(
            vec![Mode::Owned; HEAP_POSITIONS],
            ResultMode::Fresh,
        )),
    ] {
        let convention = EntryConvention::of(Some(&body(summary.clone())));
        assert!(consumes(&convention), "{summary:?}");
        assert_eq!(convention.result(), ResultKind::Transferred, "{summary:?}");
    }
}

#[test]
fn body_positions_beyond_the_summary_consume() {
    let convention = EntryConvention::of(Some(&body(Some(declared(
        vec![Mode::Borrowed],
        ResultMode::AliasOf(0),
    )))));
    assert_eq!(convention.param(0), ParamKind::Borrow);
    assert_eq!(convention.param(1), ParamKind::Consume);
}

// --- Extern shim rows: a declaration is analysis input, never the entry. ---

#[test]
fn extern_shim_consumes_whatever_it_declares() {
    let borrowed_read = mixed_summary();
    let mut into_result = declared(vec![Mode::Owned], ResultMode::AliasOf(0));
    into_result.param_flow = vec![ParamFlow::IntoResult];
    for summary in [None, Some(borrowed_read), Some(into_result)] {
        let convention = EntryConvention::of(Some(&extern_shim(summary.clone())));
        assert!(consumes(&convention), "{summary:?}");
        assert_eq!(convention.result(), ResultKind::Transferred, "{summary:?}");
    }
}

// --- Rows whose result ownership nothing in this crate checks. ---

#[test]
fn unverified_entries_consume_and_keep_return_protection() {
    let borrowed = Some(mixed_summary());
    let rows: [(&str, Life); 6] = [
        ("Dll", concrete(Realization::Dll, borrowed.clone())),
        (
            "FacadeOf",
            concrete(
                Realization::FacadeOf {
                    abi_name: LinkerSymbol::from("facade"),
                },
                borrowed.clone(),
            ),
        ),
        (
            "Inline",
            Life::Inline {
                mode_summary: borrowed,
            },
        ),
        ("HostPromised", Life::HostPromised),
        ("Declared", Life::Declared { prior: None }),
        (
            "Broken",
            Life::Broken {
                slot: slot(),
                error: cranelisp_types::BrokenProvenance::new(
                    FQSymbol {
                        module: ModuleFullPath::from("fixture"),
                        symbol: Symbol::from("g"),
                    },
                    "broken".into(),
                ),
            },
        ),
    ];
    for (row, life) in rows {
        let convention = EntryConvention::of(Some(&life));
        assert!(consumes(&convention), "{row}");
        assert_eq!(convention.result(), ResultKind::OwnedUnverified, "{row}");
    }
}

#[test]
fn an_entry_less_callable_consumes_with_an_unverified_result() {
    let convention = EntryConvention::of::<()>(None);
    assert!(consumes(&convention));
    assert_eq!(convention.result(), ResultKind::OwnedUnverified);
}

// --- The keyed reads feed the derivation the arm the call site selected. ---

#[test]
fn keyed_reads_derive_from_the_selected_arm() {
    let primitives = ModuleFullPath::from("primitives");
    let mut table: SymbolTable = SymbolTable::new(primitives.clone());
    table
        .install_extern(
            Symbol::from("str-len"),
            string_scheme(1),
            vec![Symbol::from("s")],
            None,
            0,
            None,
            Some(declared(vec![Mode::Borrowed], ResultMode::Fresh)),
            Visibility::Public,
        )
        .expect("install extern fixture");
    let tables = crate::test_support::empty_tables();
    tables.insert(primitives.clone(), table);
    let mut jit = crate::jit::Jit::new_with_symbols(&[]).expect("jit");
    let intrinsics = crate::jit::declare_intrinsics_generic(jit.jit_module()).expect("intrinsics");
    let (func_ids, func_arities) = (HashMap::new(), HashMap::new());
    let ctx = crate::compiler::CompileContext {
        func_ids: &func_ids,
        func_arities: &func_arities,
        symbol_tables: &tables,
        current_module: ModuleFullPath::from("user"),
        alloc_func_id: intrinsics.alloc,
        dealloc_func_id: intrinsics.dealloc.expect("dealloc"),
        alloc_string_func_id: intrinsics.alloc_string,
        panic_func_id: intrinsics.panic,
        vec_new_func_id: intrinsics.vec_new,
        vec_drop_func_id: intrinsics.vec_drop,
    };
    let key = FQSymbol {
        module: primitives.clone(),
        symbol: Symbol::from("str-len"),
    };
    let keyed = ctx.entry_convention_at(Some(&key));
    assert!(consumes(&keyed));
    assert_eq!(keyed.result(), ResultKind::Transferred);
    assert_eq!(
        ctx.entry_convention_of(&CallableTarget::Binding(key)),
        keyed
    );

    let missing = ctx.entry_convention_at(Some(&FQSymbol {
        module: primitives,
        symbol: Symbol::from("absent"),
    }));
    assert_eq!(missing, EntryConvention::of::<()>(None));
    assert_eq!(ctx.entry_convention_at(None), missing);
}
