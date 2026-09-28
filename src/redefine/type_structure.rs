//! Type re-establishment (`design/int/session-transaction.md` §2.6; REPL §18.5,
//! §14.8): a live nominal type is re-established only with an identical
//! structure, compared from the recorded determinants of its layout.

use cranelisp_types::{
    Binding, CallableOrigin, CranelispError, Decl, ErrorLocation, FQTypeName, Span, Symbol,
    TypeDefInfo, Visibility, member_key,
};

use super::LanguageType;
use crate::code::{Code, SessionSymbolTable};

/// A staged redeclaration of a live type whose structure differs from the
/// live declaration. The scheduler records it for the reloaded module, so a
/// failed reload can tell this refusal from any other failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StructuralTypeChange {
    pub(crate) type_name: FQTypeName,
}

impl StructuralTypeChange {
    pub(crate) fn to_error(&self) -> CranelispError {
        CranelispError::TypeError {
            message: format!(
                "cannot re-establish type {}: its structure differs from the live declaration; \
                 keep the live structure, use a new name, or edit the saved source and restart \
                 the REPL to establish the changed type",
                self.type_name
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }
    }
}

/// Everything about a type that fixes its runtime layout and user-visible
/// shape. Docstrings and sum payload labels are excluded.
#[derive(Debug, PartialEq)]
struct TypeShape {
    visibility: Visibility,
    product: bool,
    type_param_count: usize,
    constructors: Vec<CtorShape>,
}

#[derive(Debug, PartialEq)]
struct CtorShape {
    name: Symbol,
    /// `None` when the constructor binding is absent or not a constructor.
    origin: Option<CtorOrigin>,
    scheme: Option<LanguageType>,
    /// Field (and accessor) names; products only.
    field_names: Option<Vec<Symbol>>,
}

#[derive(Debug, PartialEq)]
struct CtorOrigin {
    tag: usize,
    field_count: usize,
    internal: bool,
}

/// Compare the type declared under `name` in `live` and `staging`. Only a key
/// whose live and staged bindings both declare a defined type is compared;
/// a class change between a type and a callable keeps its own refusal.
pub(crate) fn structural_type_change(
    live: &SessionSymbolTable,
    staging: &SessionSymbolTable,
    name: &Symbol,
) -> Option<StructuralTypeChange> {
    let live_binding = live.get(name.as_ref())?;
    let staged_binding = staging.get(name.as_ref())?;
    let live_info = live_binding.type_def_info()?;
    let staged_info = staged_binding.type_def_info()?;
    let unchanged = type_shape(live, live_binding, live_info)
        == type_shape(staging, staged_binding, staged_info);
    (!unchanged).then(|| StructuralTypeChange {
        type_name: live_info.name.clone(),
    })
}

fn type_shape(
    table: &SessionSymbolTable,
    binding: &Binding<Code>,
    info: &TypeDefInfo,
) -> TypeShape {
    let product = matches!(binding.declaration, Decl::Callable(_));
    let constructors = info
        .constructors
        .iter()
        .map(|ctor| {
            let ctor_binding = if product {
                Some(binding)
            } else {
                table.get(member_key(&info.name.name, ctor.as_ref()).as_ref())
            };
            ctor_shape(ctor, ctor_binding, product)
        })
        .collect();
    TypeShape {
        visibility: binding.visibility,
        product,
        type_param_count: info.type_params.len(),
        constructors,
    }
}

fn ctor_shape(name: &Symbol, binding: Option<&Binding<Code>>, product: bool) -> CtorShape {
    let callable = binding.and_then(Binding::callable);
    let origin = callable.and_then(|callable| match callable.origin {
        CallableOrigin::Ctor {
            tag,
            field_count,
            internal,
            ..
        } => Some(CtorOrigin {
            tag,
            field_count,
            internal,
        }),
        _ => None,
    });
    CtorShape {
        name: name.clone(),
        origin,
        scheme: callable.map(|callable| LanguageType::of_scheme(&callable.arm.scheme)),
        field_names: callable
            .filter(|_| product)
            .map(|callable| callable.arm.param_names.clone()),
    }
}

#[cfg(test)]
mod tests;
