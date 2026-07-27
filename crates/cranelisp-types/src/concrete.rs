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
///
/// **Constructibility — sealing DECLINED (S119 ruling, register row R-5;
/// `design/arch/concreteness-types-first.md` §3.7).** The variants stay `pub`
/// and directly constructible: exhaustive backend matching over the closed sum
/// is a Principle-18 safety feature (a `_ =>` arm compelled by privatised
/// variants would hide missed variants), and legitimate known-`Int` literal
/// construction exists. The defence against fabrication ("manufacture a
/// `ConcreteType` where the real type is unknown") is NOT a constructor gate —
/// it is the NC-2 two-family fabrication census (family A: discarded
/// `from_type` `Result`s; family B: a `Type` fabricated upstream so it passes
/// `from_type` cleanly), with a pinned allow-list in which every entry cites an
/// open defect. Residual grade: asserted-with-a-named-falsifier.
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

    /// The program-result ROOT of this type — the IO-head-strip rule
    /// (S118 ruling, FIXME 0898; the single derivation behind backend's
    /// result-root glue enumeration in `compile_to_module` and int's
    /// `release_key` in `src/result_owner.rs`, whose two literal encodings
    /// re-express over this method and delete — Principle 7).
    ///
    /// `(IO a)` — the `primitives/IO` ADT with non-empty args — strips to
    /// `a`; anything else is itself. **ONE hop, no recursion**
    /// (`(IO (IO a))` → `(IO a)`), by design: both consumers' semantics are
    /// pinned to the single-hop form. A user-module type named `IO` is NOT
    /// stripped (the match is on the canonical `primitives` home), and a
    /// nullary `IO` head (no args) is itself.
    ///
    /// Part of the result-root grammar whose other authority is
    /// `drop_glue_symbol_name` (`module.rs`) — the release symbol for a
    /// program result is minted over THIS root.
    pub fn result_root(&self) -> &ConcreteType {
        match self {
            ConcreteType::ADT(name, args)
                if name.module.as_ref() == "primitives"
                    && name.name.as_ref() == "IO"
                    && !args.is_empty() =>
            {
                &args[0]
            }
            other => other,
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
            ConcreteType::ADT(name, args) => Type::ADT(
                name.clone(),
                args.iter().map(ConcreteType::to_type).collect(),
            ),
        }
    }
}

#[cfg(test)]
mod tests;
