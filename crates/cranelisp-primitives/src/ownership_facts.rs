//! Ownership-summary constructors used directly by declaration rows.
//!
//! There is deliberately no name-keyed classifier here: every callable row in
//! `declarations.rs` carries its finished summary in the sole inventory.

use cranelisp_types::{Mode, ModeSummary, ParamFlow, ResultMode, Type};

fn summary(param_modes: Vec<Mode>, param_flow: Vec<ParamFlow>, result: ResultMode) -> ModeSummary {
    ModeSummary {
        param_modes,
        result,
        param_flow,
        ..Default::default()
    }
}

pub(crate) fn copy_fresh_for_type(ty: &Type) -> ModeSummary {
    let Type::Fn(params, _) = ty else {
        panic!("primitive declaration must carry a function type");
    };
    assert!(
        params
            .iter()
            .all(|ty| matches!(ty, Type::Int | Type::Bool | Type::Float)),
        "copy/fresh declaration contains a heap parameter"
    );
    summary(
        vec![Mode::Copy; params.len()],
        Vec::new(),
        ResultMode::Fresh,
    )
}

pub(crate) fn uniform_for_type(ty: &Type, heap_mode: Mode) -> ModeSummary {
    let Type::Fn(params, _) = ty else {
        panic!("primitive declaration must carry a function type");
    };
    let param_modes = params
        .iter()
        .map(|ty| {
            if matches!(ty, Type::Int | Type::Bool | Type::Float) {
                Mode::Copy
            } else {
                heap_mode
            }
        })
        .collect();
    summary(
        param_modes,
        vec![ParamFlow::Consumed; params.len()],
        ResultMode::Fresh,
    )
}

pub(crate) fn alias_of_zero() -> ModeSummary {
    summary(
        vec![Mode::Owned],
        vec![ParamFlow::IntoResult],
        ResultMode::AliasOf(0),
    )
}

pub(crate) fn vec_get() -> ModeSummary {
    summary(
        vec![Mode::Borrowed, Mode::Copy],
        vec![ParamFlow::Consumed, ParamFlow::Consumed],
        ResultMode::ProjectionOf(0),
    )
}

pub(crate) fn vec_set() -> ModeSummary {
    summary(
        vec![Mode::Owned, Mode::Copy, Mode::Owned],
        vec![
            ParamFlow::Consumed,
            ParamFlow::Consumed,
            ParamFlow::IntoResult,
        ],
        ResultMode::MayAliasOf(0),
    )
}

pub(crate) fn vec_push() -> ModeSummary {
    summary(
        vec![Mode::Owned, Mode::Owned],
        vec![ParamFlow::Consumed, ParamFlow::IntoResult],
        ResultMode::MayAliasOf(0),
    )
}

#[cfg(test)]
mod tests;
