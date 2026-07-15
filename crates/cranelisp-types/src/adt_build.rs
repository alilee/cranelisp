//! ADT-entry construction — the ONE builder for the symbol-table entry set an
//! ADT registration produces (S110, the R-2 mirror cure; FIXME 0583 fold-in).
//!
//! Registering an ADT — user `deftype` (typecheck `adt.rs::
//! register_type_def_with_ctor_infos`) or a synthetic bootstrap seed (int
//! `src/bootstrap.rs::register_synth_adt`) — must produce an IDENTICAL entry
//! shape: the product/sum split (S79 Option 3a), per-ctor got-slotted
//! `DefKind::Constructor` `Def`s with `ConstrADT` synthesised bodies, canonical
//! `member_key(Type, Ctor)` keying with bare-name `Import` aliases for sum
//! ctors (S109 dotted-ctor keying, `design/arch/dotted-ctor-canonical-keys.md`
//! §1), and the sum-only `ModuleEntry::TypeDef`. Before S110 that shape was
//! maintained as a near-line-for-line MIRROR across the two writers — S109 had
//! to hand-apply the canonical-key change to BOTH (the audit R-2 finding; the
//! Principle-7 divergent-duplication class Principle 24 "Resolve once" names).
//! [`build_adt_entries`] is the single derivation; the two writers become thin
//! callers.
//!
//! # What the builder owns vs what callers keep
//!
//! The builder is a PURE function from an ADT description to the ordered
//! `(key, entry)` list. It owns: the product/sum split, ctor schemes, the
//! synthesised `DefnVariant` body wrapping `Expr::ConstrADT`, tag assignment
//! (positional), canonical `member_key` + bare-alias edge construction, the
//! product type facet + docstring fallback, and the `TypeDefInfo` (computed
//! ONCE, shared by the facet / `TypeDef` entry).
//!
//! Callers keep everything stateful:
//! - **GOT-slot allocation** — each [`AdtCtorSpec`] carries a pre-allocated
//!   `got_slot` (typecheck allocates from staging, bootstrap from the session
//!   table; the builder never sees a table).
//! - **Insertion policy** — bootstrap inserts every pair verbatim (synthetic
//!   modules have no contests); typecheck inserts the `Def`/`TypeDef` pairs
//!   verbatim but classifies each **`ModuleEntry::Import` bare-alias pair**
//!   through its §8.6.5 contest logic (install / poison `Ambiguous` / leave a
//!   non-ctor binding untouched — `adt.rs::register_constructors`). The alias
//!   pairs are structurally discriminable: they are the ONLY `Import` entries
//!   the builder returns.
//! - **Pre-seeding + field resolution** — the recursive-field `TypeDef`
//!   placeholder and `TypeExpr` → [`Type`] field resolution happen before the
//!   specs exist (typecheck-only concerns).
//! - **Field-accessor synthesis** — product accessors
//!   (`adt.rs::synthesise_field_accessors`) are a typecheck-only follow-on;
//!   bootstrap's seeded product (`Pair`) deliberately has none.
//!
//! # Ordering contract
//!
//! The returned list is insertion-ordered so a sequential caller preserves the
//! as-built semantics: for each ctor (tag order) the canonical `Def` pair
//! precedes its bare-alias `Import` pair (typecheck's contest probe follows
//! the bare alias to a canonical entry that must already be inserted); the
//! sum-only `TypeDef` pair comes last.
//!
//! No serde shape changes here: the builder produces existing entry shapes
//! (no `CACHE_SCHEMA_VERSION` impact). Narrative: `design/arch/interfaces.md`
//! §"ADT-entry builder"; cross-surface: `bounded-contexts.md` §7.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use crate::{
    CodeStore, DefKind, DefnVariant, Expr, FQSymbol, FQTypeName, FieldInfo, ModuleEntry, Scheme,
    Span, Symbol, Type, TypeDefInfo, TypeExpr, TypeId, Visibility, member_key,
};

/// One constructor of an ADT registration — the caller-resolved description
/// [`build_adt_entries`] derives the ctor's `Def` entry from.
///
/// Fields are already RESOLVED: `fields` carry [`Type`]s (typecheck resolves
/// `TypeExpr`s before building specs; bootstrap constructs FQ types directly —
/// synthetic modules have empty imports, Principle 17). `got_slot` is
/// pre-allocated by the caller from the target module's GOT (the builder is
/// pure; slot allocation is table state). Tag is NOT a field — it is assigned
/// positionally by [`build_adt_entries`] (both prior writers enumerated).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct AdtCtorSpec {
    /// Bare constructor name (`Some`, `Pair`).
    pub name: Symbol,
    /// Named, resolved field types in declaration order. Empty ⇒ nullary.
    pub fields: Vec<FieldInfo>,
    /// Ctor-level docstring. A product ctor with `None` falls back to the
    /// deftype-level docstring (it has no separate `TypeDef` entry to hold it).
    pub docstring: Option<String>,
    /// Internal ctor (`IO`'s `Bind`/`Pure`/`Effect`): excluded from user
    /// exhaustiveness; rides `DefKind::Constructor.internal`.
    pub internal: bool,
    /// Pre-allocated GOT slot for the ctor's callable `Def` (S83: the slot
    /// rides the `DefKind::Constructor` variant, Principle 20).
    pub got_slot: usize,
}

impl AdtCtorSpec {
    /// Construct a ctor spec (the struct is `#[non_exhaustive]`; this is the
    /// cross-crate construction path).
    pub fn new(
        name: Symbol,
        fields: Vec<FieldInfo>,
        docstring: Option<String>,
        internal: bool,
        got_slot: usize,
    ) -> Self {
        AdtCtorSpec { name, fields, docstring, internal, got_slot }
    }
}

/// Build the complete symbol-table entry set for an ADT registration — the
/// single derivation both writers (typecheck `deftype` registration, int
/// synthetic bootstrap) call (S110 R-2; module rustdoc has the caller/builder
/// split and the ordering contract).
///
/// - **Sum/enum** (type name distinct from every ctor name): per ctor, a
///   got-slotted `DefKind::Constructor { type_def: None }` `Def` keyed under
///   the canonical `member_key(Type, Ctor)` plus a bare-name
///   `ModuleEntry::Import` alias onto it; then one `ModuleEntry::TypeDef`
///   keyed at the type name carrying the full constructor list.
/// - **Single-ctor product** (type name == sole ctor name): ONE got-slotted
///   `Def` keyed at the bare type name carrying the **type facet**
///   (`type_def: Some(TypeDefInfo)`) — no canonical re-key, no alias, no
///   separate `TypeDef` (S79 Option 3a; the degenerate `member_key("Point",
///   "Point")` is never minted).
///
/// Each ctor `Def` has scheme `forall type_var_ids. (Fn [field-tys] ADT)`
/// (bare `ADT` for nullary), `param_names` = field names, and a synthesised
/// `DefnVariant` whose body is `Expr::ConstrADT` (the backend lowers it
/// directly). `type_var_ids` MUST correspond positionally to `type_params`;
/// `adt` type is `Type::ADT(fqtn, [Var(id)…])`.
pub fn build_adt_entries<C: CodeStore>(
    fqtn: &FQTypeName,
    type_params: &[Symbol],
    type_var_ids: &[TypeId],
    adt_docstring: Option<&str>,
    ctors: &[AdtCtorSpec],
    visibility: Visibility,
) -> Vec<(Symbol, ModuleEntry<C>)> {
    let adt_type = Type::ADT(
        fqtn.clone(),
        type_var_ids.iter().map(|&id| Type::Var(id)).collect(),
    );

    // The TypeDefInfo — computed ONCE; shared by the product type facet or the
    // sum TypeDef entry (the R-2 mirror had each writer deriving it twice).
    let type_def_info = TypeDefInfo {
        name: fqtn.clone(),
        type_params: type_params.to_vec(),
        constructors: ctors.iter().map(|c| c.name.clone()).collect(),
    };

    // Product/sum split (S79 Option 3a): single ctor whose name equals the
    // type name ⇒ product (type and ctor collide on one key, dual facet).
    let is_product = ctors.len() == 1 && ctors[0].name.as_ref() == fqtn.name.as_ref();

    let mut entries: Vec<(Symbol, ModuleEntry<C>)> = Vec::new();

    for (tag, ctor) in ctors.iter().enumerate() {
        let param_names: Vec<Symbol> = ctor.fields.iter().map(|f| f.name.clone()).collect();

        // Scheme: nullary → bare ADT; data ctor → (Fn [field-tys] ADT). Both
        // quantify the type's vars (monomorphic when type_var_ids is empty).
        let scheme_ty = if ctor.fields.is_empty() {
            adt_type.clone()
        } else {
            Type::Fn(
                ctor.fields.iter().map(|f| f.ty.clone()).collect(),
                Box::new(adt_type.clone()),
            )
        };
        let scheme = Scheme {
            type_vars: type_var_ids.to_vec(),
            constraints: HashMap::new(),
            ty: scheme_ty,
        };

        // The product ctor carries the type facet; sum ctors carry None.
        let ctor_type_def: Option<Box<TypeDefInfo>> =
            is_product.then(|| Box::new(type_def_info.clone()));

        // Synthesised DefnVariant body wrapping Expr::ConstrADT — the backend
        // lowers this directly (ctor metadata on DefKind::Constructor serves
        // pattern matching + introspection, not codegen).
        let body_span = Span::SYNTHETIC;
        let synth_params: Vec<(Symbol, Option<TypeExpr>)> =
            param_names.iter().cloned().map(|n| (n, None)).collect();
        let synth_body = Expr::ConstrADT {
            type_name: fqtn.clone(),
            tag,
            fields: param_names
                .iter()
                .map(|n| Expr::var(n.clone(), body_span))
                .collect(),
            span: body_span,
            inferred_type: None,
        };
        let ast = DefnVariant { params: synth_params, body: synth_body, span: body_span };

        let mut builder = ModuleEntry::def(
            scheme,
            DefKind::Constructor {
                got_slot: ctor.got_slot,
                type_name: fqtn.clone(),
                tag,
                field_count: ctor.fields.len(),
                internal: ctor.internal,
                type_def: ctor_type_def,
                mode_summary: None,
            },
        )
        .visibility(visibility)
        .param_names(param_names)
        .ast(ast);
        // Ctor docstring wins; the product ctor (no separate TypeDef entry to
        // hold the deftype-level docstring) falls back to it.
        let doc = ctor
            .docstring
            .clone()
            .or_else(|| if is_product { adt_docstring.map(str::to_string) } else { None });
        if let Some(doc) = doc {
            builder = builder.docstring(doc);
        }
        let entry = builder.build();

        if is_product {
            // Product dual-facet: single key at the type name.
            entries.push((ctor.name.clone(), entry));
        } else {
            // Sum ctor — uniform canonical keying (S109): the real Def under
            // member_key(Type, Ctor); the bare name an Import alias onto it.
            // Callers with a contest policy (§8.6.5) classify the alias pair;
            // it is the only Import shape this builder returns.
            let canonical_key = member_key(&fqtn.name, ctor.name.as_ref());
            entries.push((canonical_key.clone(), entry));
            entries.push((
                ctor.name.clone(),
                ModuleEntry::Import {
                    source: FQSymbol { module: fqtn.module.clone(), symbol: canonical_key },
                    visibility,
                },
            ));
        }
    }

    // Sum/enum: the separate TypeDef entry (constructor-name list + deftype
    // docstring). The product's type facet already rode the lone ctor Def.
    if !is_product {
        entries.push((
            Symbol::from(fqtn.name.as_ref()),
            ModuleEntry::TypeDef {
                info: type_def_info,
                visibility,
                docstring: adt_docstring.map(str::to_string),
            },
        ));
    }

    entries
}

#[cfg(test)]
mod tests;
