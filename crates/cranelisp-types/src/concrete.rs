//! The concrete-only codegen-boundary type.
//!
//! `ConcreteType` is a fully-concrete mirror of [`Type`](crate::Type) with **no
//! `Var` and no `TyConApp` variant**. A representation-undetermined type (a
//! generic / `Type::Var` / unpinned higher-kinded head) is *structurally
//! unrepresentable* as a `ConcreteType` — by construction of the enum, not by a
//! downstream check (Principle 18 — enforce invariants structurally).
//!
//! **The target architecture this scaffold begins.** Today the typed AST carries
//! `inferred_type: Option<Box<Type>>` on every node, and `Type` *has* a `Var`
//! variant, so a generic IS representable at every codegen-reaching position; the
//! entire S83/S84 defence is a pile of downstream guards (`contains_var`
//! debug-assert, the §3.11.1 position-complete ambiguity check, the
//! `classify == Mixed && is_representation_undetermined()` backstop, the
//! `is_concrete()` slot gate) all enforcing "no `Type::Var` reaches codegen"
//! *behaviourally*. The user ruling (2026-06-16): "remove passing generics to the
//! backend — they shouldn't even be REPRESENTABLE there." This type is the
//! structural foreclosure — the backend consumes only `ConcreteType`, so
//! `HeapCategory::classify` becomes total (no `Var` arm, no panic case), and the
//! four behavioural guards collapse to one structural property + one fallible
//! conversion choke point ([`ConcreteType::from_type`]).
//!
//! **Phase 1 scaffold only.** This type is introduced additively and is dead code
//! until the mono pass produces it (Phase 2) and the backend consumes it (Phase
//! 3). The full arc — including generic-body-codegen elimination (Phase 4, the
//! cause-fix for the FIXME-0381 317× backstop fire) — is
//! `design/arch/concrete-boundary-type.md`.

use serde::{Deserialize, Serialize};

use crate::{FQTypeName, Type, TypeId};

/// A fully-concrete type at the typecheck→backend boundary.
///
/// **Structural guarantee:** this enum has no `Var` and no `TyConApp` variant.
/// The recursion is on `ConcreteType` itself (an `ADT`'s args and an `Fn`'s
/// params/return are `ConcreteType`), so concreteness is total at every depth —
/// there is no way to nest a `Type::Var` inside a `ConcreteType`.
///
/// `Eq + Hash` (which `Type` cannot derive — it carries `Var(TypeId)` that hashes
/// unstably across inference runs) make `ConcreteType` a stable key for the mono
/// `done`-set and the codegen cache key.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ConcreteType {
    Int,
    Bool,
    String,
    Float,
    /// Function type: concrete params -> concrete return.
    Fn(Vec<ConcreteType>, Box<ConcreteType>),
    /// Algebraic data type: fully-qualified type name + **fully-concrete** type
    /// arguments.
    ADT(FQTypeName, Vec<ConcreteType>),
}

/// Why a [`Type`] could not be converted to a [`ConcreteType`].
///
/// The conversion failure IS the unified expression of three errors that are
/// currently three separate guards: the §3.11.1 "ambiguous type" error, the
/// "monomorphisation could not produce a concrete type here" error, and the
/// `classify(Type::Var)` panic. They are the same fact — *this position's type is
/// not concrete* — surfaced at the one boundary where it is structurally caught.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NotConcrete {
    /// A residual unification variable — under full monomorphisation-from-roots a
    /// free var in a codegen-reaching position means no root pins it (the 0373(ii)
    /// ambiguity error).
    Var(TypeId),
    /// An unresolved higher-kinded type-constructor head.
    HktHead(TypeId),
}

impl ConcreteType {
    /// The ONLY way to obtain a `ConcreteType` from a [`Type`]. Succeeds **iff**
    /// the `Type` is fully concrete; the failure IS the
    /// "could-not-monomorphise" / §3.11.1-ambiguity error (Principle 18 — the
    /// illegal state is caught at the one boundary it cannot pass, not by N
    /// downstream guards).
    pub fn from_type(ty: &Type) -> Result<ConcreteType, NotConcrete> {
        match ty {
            Type::Int => Ok(ConcreteType::Int),
            Type::Bool => Ok(ConcreteType::Bool),
            Type::String => Ok(ConcreteType::String),
            Type::Float => Ok(ConcreteType::Float),
            Type::Fn(params, ret) => Ok(ConcreteType::Fn(
                params
                    .iter()
                    .map(ConcreteType::from_type)
                    .collect::<Result<Vec<_>, _>>()?,
                Box::new(ConcreteType::from_type(ret)?),
            )),
            Type::ADT(name, args) => Ok(ConcreteType::ADT(
                name.clone(),
                args.iter()
                    .map(ConcreteType::from_type)
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Type::Var(id) => Err(NotConcrete::Var(*id)),
            Type::TyConApp(id, _) => Err(NotConcrete::HktHead(*id)),
        }
    }

    /// The inverse embedding — a `ConcreteType` is always a valid [`Type`]
    /// (the embedding is total; no `Type` variant is unreachable from a
    /// `ConcreteType`).
    pub fn to_type(&self) -> Type {
        match self {
            ConcreteType::Int => Type::Int,
            ConcreteType::Bool => Type::Bool,
            ConcreteType::String => Type::String,
            ConcreteType::Float => Type::Float,
            ConcreteType::Fn(params, ret) => Type::Fn(
                params.iter().map(ConcreteType::to_type).collect(),
                Box::new(ret.to_type()),
            ),
            ConcreteType::ADT(name, args) => {
                Type::ADT(name.clone(), args.iter().map(ConcreteType::to_type).collect())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ModuleFullPath, TypeName};

    fn opt(arg: Type) -> Type {
        Type::adt(
            ModuleFullPath::from("primitives"),
            TypeName::from("Option"),
            vec![arg],
        )
    }

    #[test]
    fn scalars_convert() {
        for (ty, ct) in [
            (Type::Int, ConcreteType::Int),
            (Type::Bool, ConcreteType::Bool),
            (Type::String, ConcreteType::String),
            (Type::Float, ConcreteType::Float),
        ] {
            assert_eq!(ConcreteType::from_type(&ty), Ok(ct.clone()));
            assert_eq!(ct.to_type(), ty);
        }
    }

    #[test]
    fn bare_var_is_not_concrete() {
        assert_eq!(ConcreteType::from_type(&Type::Var(7)), Err(NotConcrete::Var(7)));
    }

    #[test]
    fn tyconapp_head_is_not_concrete() {
        assert_eq!(
            ConcreteType::from_type(&Type::TyConApp(3, vec![Type::Int])),
            Err(NotConcrete::HktHead(3))
        );
    }

    #[test]
    fn concrete_adt_converts_and_round_trips() {
        let ty = opt(Type::Int);
        let ct = ConcreteType::from_type(&ty).expect("concrete");
        assert!(matches!(ct, ConcreteType::ADT(_, ref args) if args == &vec![ConcreteType::Int]));
        assert_eq!(ct.to_type(), ty);
    }

    #[test]
    fn adt_with_free_var_arg_is_not_concrete() {
        // (Option a) — the var rides in the arg, the FIXME-0379 `Mixed`-family case.
        assert_eq!(
            ConcreteType::from_type(&opt(Type::Var(0))),
            Err(NotConcrete::Var(0))
        );
    }

    #[test]
    fn fn_with_var_param_is_not_concrete() {
        let ty = Type::Fn(vec![Type::Var(1)], Box::new(Type::Int));
        assert_eq!(ConcreteType::from_type(&ty), Err(NotConcrete::Var(1)));
    }

    #[test]
    fn fn_with_var_return_is_not_concrete() {
        let ty = Type::Fn(vec![Type::Int], Box::new(Type::Var(2)));
        assert_eq!(ConcreteType::from_type(&ty), Err(NotConcrete::Var(2)));
    }

    #[test]
    fn nested_concrete_fn_round_trips() {
        // (Fn [Int (Option Bool)] String) — concrete at every depth.
        let ty = Type::Fn(vec![Type::Int, opt(Type::Bool)], Box::new(Type::String));
        let ct = ConcreteType::from_type(&ty).expect("concrete");
        assert_eq!(ct.to_type(), ty);
    }

    #[test]
    fn deeply_nested_var_is_caught() {
        // (Fn [Int] (Option (Option a))) — the var is two levels deep.
        let ty = Type::Fn(vec![Type::Int], Box::new(opt(opt(Type::Var(9)))));
        assert_eq!(ConcreteType::from_type(&ty), Err(NotConcrete::Var(9)));
    }

    #[test]
    fn from_type_agrees_with_is_concrete() {
        // The conversion succeeds iff `Type::is_concrete()` — the two predicates
        // are the same verdict (one at the gate on `Type`, one at the boundary).
        for ty in [
            Type::Int,
            opt(Type::Int),
            Type::Fn(vec![Type::Int], Box::new(Type::Bool)),
            Type::Var(0),
            opt(Type::Var(1)),
            Type::TyConApp(2, vec![]),
        ] {
            assert_eq!(
                ConcreteType::from_type(&ty).is_ok(),
                ty.is_concrete(),
                "disagreement on {ty:?}"
            );
        }
    }
}
