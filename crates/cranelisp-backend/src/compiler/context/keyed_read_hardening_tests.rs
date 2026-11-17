//! ACT-0964 item 1 — the two keyed type and constructor reads that used to
//! degrade silently in release builds now fail in every profile (S123 evidence
//! U-9). Each pair plants a missing lookup against an intact control.

use std::collections::HashMap;

use cranelift_module::FuncId;
use cranelisp_types::{FQSymbol, FQTypeName, ModuleFullPath, Symbol, TypeDefInfo, TypeName};

use super::CompileContext;
use crate::test_support::option_type_tables;

fn with_context<R>(read: impl FnOnce(&CompileContext<'_>) -> R) -> R {
    let tables = option_type_tables();
    let func_ids = HashMap::new();
    let func_arities = HashMap::new();
    let ctx = CompileContext {
        func_ids: &func_ids,
        func_arities: &func_arities,
        symbol_tables: &tables,
        current_module: ModuleFullPath::from("main"),
        alloc_func_id: None,
        dealloc_func_id: FuncId::from_u32(0),
        alloc_string_func_id: None,
        panic_func_id: None,
        vec_new_func_id: None,
        vec_drop_func_id: None,
    };
    read(&ctx)
}

fn option_def(constructors: &[&str]) -> TypeDefInfo {
    TypeDefInfo {
        name: FQTypeName::new(ModuleFullPath::from("main"), TypeName::from("Option")),
        type_params: vec![],
        constructors: constructors.iter().map(|c| Symbol::from(*c)).collect(),
    }
}

fn main_key(symbol: &str) -> FQSymbol {
    FQSymbol {
        module: ModuleFullPath::from("main"),
        symbol: Symbol::from(symbol),
    }
}

// spec: design/backend/backend.md §2 "Keyed type and constructor reads fail in every profile" —
// control: every constructor of an intact type resolves.
#[test]
fn every_constructor_of_an_intact_type_resolves() {
    let metas = with_context(|ctx| ctx.constructor_metas(&option_def(&["None", "Some"])));
    assert_eq!(metas.expect("intact type").len(), 2);
}

// spec: design/backend/backend.md §2 "Keyed type and constructor reads fail in every profile" — a
// planted constructor no probe can resolve is an error, not a dropped entry.
#[test]
fn a_constructor_no_probe_resolves_is_an_error_not_a_dropped_entry() {
    let err = with_context(|ctx| ctx.constructor_metas(&option_def(&["None", "Ghost"])))
        .expect_err("a missing constructor must fail");
    assert!(err.to_string().contains("keying drift"), "{err}");
}

// spec: design/backend/backend.md §2 "Keyed type and constructor reads fail in every profile" — a
// type whose module has no table is an error, not an empty constructor list.
#[test]
fn a_type_with_no_module_table_is_an_error() {
    let mut def = option_def(&["None"]);
    def.name = FQTypeName::new(ModuleFullPath::from("nowhere"), TypeName::from("Option"));
    let err = with_context(|ctx| ctx.constructor_metas(&def)).expect_err("no table");
    assert!(err.to_string().contains("keying drift"), "{err}");
}

// spec: design/backend/backend.md §2 "Keyed type and constructor reads fail in every profile" —
// control: a resolvable pattern constructor yields its field types.
#[test]
fn a_resolvable_pattern_constructor_yields_its_field_types() {
    let fields = with_context(|ctx| {
        ctx.ctor_field_types(
            &main_key("Some"),
            None,
            cranelisp_types::Span::SYNTHETIC,
            &crate::compiler::census::Frame::for_test(),
        )
    });
    assert_eq!(
        fields.expect("Some resolves"),
        vec![cranelisp_types::ConcreteType::Int]
    );
}

// spec: design/backend/backend.md §2 "Keyed type and constructor reads fail in every profile" — a
// planted pattern-constructor key that misses is an error, never an empty field
// list (which made every field of the arm an unreleased scalar).
#[test]
fn a_missed_pattern_constructor_key_is_an_error_not_no_fields() {
    let err = with_context(|ctx| {
        ctx.ctor_field_types(
            &main_key("Ghost"),
            None,
            cranelisp_types::Span::SYNTHETIC,
            &crate::compiler::census::Frame::for_test(),
        )
    })
    .expect_err("a missed key must fail");
    assert!(err.to_string().contains("keying drift"), "{err}");
}
