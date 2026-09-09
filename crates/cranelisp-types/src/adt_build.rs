//! Pure ADT synthesis recipes for the unified callable lifecycle.
//!
//! The builder derives names, schemes, constructor provenance, synthesized
//! bodies, aliases, and type facets. It deliberately does not allocate slots
//! or construct callable bindings: callers submit callable recipes to the
//! symbol-table settlement funnel.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use crate::{
    Binding, CallableOrigin, DefnVariant, Expr, FQTypeName, FieldInfo, Scheme, Span, Symbol,
    SynthSpec, Type, TypeDefInfo, TypeExpr, TypeId, TypeRecord, Visibility, member_key,
};

/// One constructor in an ADT declaration.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct AdtCtorSpec {
    /// Constructor name as declared by the ADT.
    pub name: Symbol,
    /// Constructor fields in declaration order.
    pub fields: Vec<FieldInfo>,
    /// Constructor documentation, if supplied independently of the ADT.
    pub docstring: Option<String>,
    /// Whether the constructor is compiler-internal rather than user-authored.
    pub internal: bool,
}

impl AdtCtorSpec {
    /// Create one constructor specification in declaration order.
    pub fn new(
        name: Symbol,
        fields: Vec<FieldInfo>,
        docstring: Option<String>,
        internal: bool,
    ) -> Self {
        Self {
            name,
            fields,
            docstring,
            internal,
        }
    }
}

/// A callable recipe which must be settled through a SymbolTable funnel
/// before it becomes a binding.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct AdtCallableSpec {
    /// Constructor callable's declared type scheme.
    pub scheme: Scheme,
    /// Parameter names projected from constructor fields, in field order.
    pub param_names: Vec<Symbol>,
    /// Documentation attached to the callable constructor binding.
    pub docstring: Option<String>,
    /// Constructor provenance used by lifecycle validation and synthesis.
    pub origin: CallableOrigin,
    /// Slotless synthesis recipe retained for concrete realization.
    pub synth: SynthSpec,
    /// Visibility of the eventual callable binding.
    pub visibility: Visibility,
}

/// One ordered result of build_adt_entries.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
#[allow(clippy::large_enum_variant)]
pub enum AdtEntrySpec<C: crate::CodeStore = ()> {
    /// An ordered, slotless callable recipe owned by the caller until it is
    /// submitted to [`SymbolTable::install_template`](crate::SymbolTable::install_template)
    /// or [`SymbolTable::install_concrete`](crate::SymbolTable::install_concrete),
    /// according to whether its scheme is generic or concrete.
    Callable(AdtCallableSpec),
    /// An ordered non-callable binding owned by the caller and accepted
    /// unchanged by [`SymbolTable::install_binding`](crate::SymbolTable::install_binding).
    Binding(Binding<C>),
}

/// Build the ordered recipes for an ADT registration.
pub fn build_adt_entries<C: crate::CodeStore>(
    fqtn: &FQTypeName,
    type_params: &[Symbol],
    type_var_ids: &[TypeId],
    adt_docstring: Option<&str>,
    ctors: &[AdtCtorSpec],
    visibility: Visibility,
) -> Vec<(Symbol, AdtEntrySpec<C>)> {
    let adt_type = Type::ADT(
        fqtn.clone(),
        type_var_ids.iter().map(|&id| Type::Var(id)).collect(),
    );
    let type_def_info = TypeDefInfo {
        name: fqtn.clone(),
        type_params: type_params.to_vec(),
        constructors: ctors.iter().map(|ctor| ctor.name.clone()).collect(),
    };
    let is_product = ctors.len() == 1 && ctors[0].name.as_ref() == fqtn.name.as_ref();
    let mut entries = Vec::new();

    for (tag, ctor) in ctors.iter().enumerate() {
        let param_names: Vec<Symbol> = ctor.fields.iter().map(|field| field.name.clone()).collect();
        let scheme_ty = if ctor.fields.is_empty() {
            adt_type.clone()
        } else {
            Type::Fn(
                ctor.fields.iter().map(|field| field.ty.clone()).collect(),
                Box::new(adt_type.clone()),
            )
        };
        let scheme = Scheme {
            type_vars: type_var_ids.to_vec(),
            constraints: HashMap::new(),
            ty: scheme_ty,
        };
        let span = Span::SYNTHETIC;
        let variant = DefnVariant {
            params: param_names
                .iter()
                .cloned()
                .map(|name| (name, None::<TypeExpr>))
                .collect(),
            body: Expr::ConstrADT {
                type_name: fqtn.clone(),
                tag,
                fields: param_names
                    .iter()
                    .cloned()
                    .map(|name| Expr::var(name, span))
                    .collect(),
                span,
                inferred_type: None,
            },
            span,
        };
        let callable = AdtEntrySpec::Callable(AdtCallableSpec {
            scheme,
            param_names,
            docstring: ctor.docstring.clone().or_else(|| {
                is_product
                    .then(|| adt_docstring.map(str::to_owned))
                    .flatten()
            }),
            origin: CallableOrigin::Ctor {
                type_name: fqtn.clone(),
                tag,
                field_count: ctor.fields.len(),
                internal: ctor.internal,
                type_def: is_product.then(|| Box::new(type_def_info.clone())),
            },
            synth: SynthSpec { variant },
            visibility,
        });

        if is_product {
            entries.push((ctor.name.clone(), callable));
        } else {
            let canonical_key = member_key(&fqtn.name, ctor.name.as_ref());
            entries.push((canonical_key, callable));
        }
    }

    if !is_product {
        entries.push((
            Symbol::from(fqtn.name.as_ref()),
            AdtEntrySpec::Binding(Binding::new(
                crate::Decl::Type(TypeRecord::Defined {
                    info: type_def_info,
                    docstring: adt_docstring.map(str::to_owned),
                }),
                visibility,
            )),
        ));
    }

    entries
}

#[cfg(test)]
mod tests;
