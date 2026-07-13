//! ADT type definitions: registration, constructor lookup, exhaustiveness checking.
//!
//! Handles both enum-only ADTs (nullary constructors, Ring 0) and parameterized
//! ADTs with data constructor fields (Ring 1). Polymorphic types produce
//! polymorphic constructor schemes via `build_constructor_scheme`.
//!
//! Type definitions are stored on per-module SymbolTables as `ModuleEntry::TypeDef`
//! entries. The old `TypeDefRegistry` global cache has been eliminated — all lookups
//! go through the module system.

use std::collections::HashMap;

use cranelisp_types::{ErrorLocation,
    ConstructorDef, CranelispError, DefKind, DefnVariant, Expr, FQTypeName, FieldInfo,
    ModuleEntry, ModuleFullPath, Scheme, Span, Symbol, Type, TypeDefInfo, TypeId, TypeName,
    Visibility, member_key,
};

use crate::checker::{CheckState, TypeCheckEnv};

/// Local typecheck-internal intermediate: a constructor with its resolved field
/// types, used during `register_type_def` to build per-constructor `Def`
/// entries. Not part of the cranelisp-types surface — the canonical store is
/// the per-ctor `ModuleEntry::Def { kind: DefKind::Constructor, .. }` entry.
#[derive(Clone)]
pub(crate) struct CtorBuild {
    pub name: Symbol,
    pub tag: usize,
    pub fields: Vec<FieldInfo>,
    pub docstring: Option<String>,
    pub internal: bool,
}

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Register a type definition from a TopLevel::TypeDef.
    ///
    /// Handles both nullary enums (Ring 0) and parameterized ADTs with data
    /// constructor fields (Ring 1). Allocates fresh type vars for type parameters,
    /// resolves field types, and produces polymorphic constructor schemes.
    ///
    /// **FQTypeName exception 2 (receiver-pinned).** `name: &TypeName` is
    /// correct here per `design/arch/facades/types.md` §"FQTypeName migration
    /// plan (Sprint 67)" §"typecheck" row 269 — the writer's module context
    /// is supplied by `state.current_module`; the `FQTypeName` is constructed
    /// inside this function at line 42 (`FQTypeName::new(state.current_module
    /// .clone(), name.clone())`). The bare-name parameter encodes the
    /// post-resolution lift point itself.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn register_type_def(
        &self,
        state: &mut CheckState,
        name: &TypeName,
        docstring: &Option<String>,
        type_params: &[Symbol],
        constructors: &[ConstructorDef],
        visibility: Visibility,
        span: Span,
    ) -> Result<(), CranelispError> {
        // Allocate fresh type vars for type parameters
        let (var_map, type_var_ids) = self.allocate_type_params(type_params);

        // Build the fully-qualified type name
        let fqtn = FQTypeName::new(state.current_module.clone(), name.clone());

        // Pre-seed the type name in the symbol table so recursive constructor
        // fields (e.g., `:(List a) tail` inside a `(deftype (List a) ...)`) can
        // resolve the type during `build_constructor_infos`. The full TypeDefInfo
        // replaces this placeholder below.
        self.current_symbol_table_mut(state).insert(
            Symbol::from(name.as_ref()),
            ModuleEntry::TypeDef {
                info: TypeDefInfo {
                    name: fqtn.clone(),
                    type_params: type_params.to_vec(),
                    constructors: vec![],
                },
                visibility,
                docstring: None,
            },
        );

        // Build constructor infos with resolved field types.
        // If resolution fails, remove the pre-seeded placeholder so it
        // doesn't pollute known_types for subsequent definitions.
        let ctor_infos = match self.build_constructor_infos(
            state, name, constructors, &var_map, span,
        ) {
            Ok(infos) => infos,
            Err(e) => {
                self.current_symbol_table_mut(state)
                    .symbols.remove(&Symbol::from(name.as_ref()));
                return Err(e);
            }
        };

        self.register_type_def_with_ctor_infos(
            state,
            name,
            docstring,
            type_params,
            &type_var_ids,
            ctor_infos,
            visibility,
        );

        Ok(())
    }

    /// Register a type definition using pre-resolved constructor builds.
    ///
    /// This is the synthetic-bootstrap path used when a type's constructor
    /// fields reference types in foreign synthetic modules (e.g. `Trace` in
    /// `primitives` referencing `macros/SList`). Per Principle 17, synthetic
    /// modules have empty imports, so short-name resolution via TypeExpr
    /// cannot reach foreign-module type names — the caller must construct
    /// FQ field types directly using `*_fqtn(...)` helpers and supply them
    /// here as already-built `CtorBuild`s.
    ///
    /// Caller's responsibility: `type_var_ids` MUST correspond positionally
    /// to `type_params` (i.e. the type vars that should be quantified in
    /// each constructor's scheme).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn register_type_def_with_ctor_infos(
        &self,
        state: &mut CheckState,
        name: &TypeName,
        docstring: &Option<String>,
        type_params: &[Symbol],
        type_var_ids: &[TypeId],
        ctor_infos: Vec<CtorBuild>,
        visibility: Visibility,
    ) {
        let fqtn = FQTypeName::new(state.current_module.clone(), name.clone());
        let type_args: Vec<Type> = type_var_ids.iter().map(|&id| Type::Var(id)).collect();
        let adt_type = Type::ADT(fqtn.clone(), type_args);

        // Capture ctor names for the TypeDefInfo before consuming ctor_infos
        // during per-ctor Def registration.
        let ctor_names: Vec<Symbol> =
            ctor_infos.iter().map(|c| c.name.clone()).collect();

        let type_def_info = TypeDefInfo {
            name: fqtn.clone(),
            type_params: type_params.to_vec(),
            constructors: ctor_names,
        };

        // **Product/sum split (S79 Option 3a, FIXME 0319).** A single-ctor
        // **product** type has type-name == ctor-name, so the type and its
        // constructor collide on one symbol-table key (`"Rectangle"`). Rather
        // than overwrite the got-slotted ctor `Def` with a `ModuleEntry::TypeDef`
        // (the prior model — which dropped the ctor's `param_names` field names
        // and broke product-ctor-as-first-class-value), the surviving entry is
        // the **got-slotted ctor `Def`** carrying a **type facet**
        // (`DefKind::Constructor { type_def: Some(..) }`) so it ALSO answers as
        // its own type. A sum/enum type registers a separate `ModuleEntry::TypeDef`
        // under its distinct key and its ctors carry `type_def: None`.
        let is_product = ctor_infos.len() == 1
            && ctor_infos[0].name.as_ref() == name.as_ref();
        let product_type_def: Option<TypeDefInfo> =
            is_product.then(|| type_def_info.clone());

        if !is_product {
            // Sum/enum: pre-seed the type entry (the `register_type_def` path
            // pre-seeds; direct callers may not have, so do it here
            // defensively) so recursive ctor-field resolution can see the type
            // while constructors register.
            self.current_symbol_table_mut(state).insert(
                Symbol::from(name.as_ref()),
                ModuleEntry::TypeDef {
                    info: TypeDefInfo {
                        name: fqtn.clone(),
                        type_params: type_params.to_vec(),
                        constructors: vec![],
                    },
                    visibility,
                    docstring: None,
                },
            );
        }

        // Register each constructor as a ModuleEntry::Def with
        // kind: DefKind::Constructor { type_name, tag, field_count, internal,
        // type_def } and a synthesised DefnVariant body wrapping Expr::ConstrADT.
        // The product ctor receives the type facet (`type_def: Some(..)`); every
        // sum/enum ctor receives `type_def: None`.
        self.register_constructors(
            state,
            &fqtn,
            &ctor_infos,
            &adt_type,
            type_var_ids,
            visibility,
            product_type_def.as_ref(),
            docstring,
        );

        // Register the sum/enum type's separate `TypeDef` entry. The product
        // case has NO `TypeDef` entry — its type facet lives on the ctor `Def`
        // registered just above, under the shared `"Rectangle"` key.
        if !is_product {
            self.current_symbol_table_mut(state).insert(
                Symbol::from(name.as_ref()),
                ModuleEntry::TypeDef {
                    info: type_def_info,
                    visibility,
                    docstring: docstring.clone(),
                },
            );
        }
    }

    /// Allocate fresh type variables for type parameters.
    /// Returns a var_map (param name -> TypeId) and the ordered list of TypeIds.
    fn allocate_type_params(
        &self,
        type_params: &[Symbol],
    ) -> (HashMap<Symbol, TypeId>, Vec<TypeId>) {
        let mut var_map = HashMap::new();
        let mut type_var_ids = Vec::new();
        for param in type_params {
            let (_, id) = self.fresh_var_id();
            var_map.insert(param.clone(), id);
            type_var_ids.push(id);
        }
        (var_map, type_var_ids)
    }

    /// Build CtorBuild entries with resolved field types.
    fn build_constructor_infos(
        &self,
        state: &CheckState,
        type_name: &TypeName,
        constructors: &[ConstructorDef],
        var_map: &HashMap<Symbol, TypeId>,
        span: Span,
    ) -> Result<Vec<CtorBuild>, CranelispError> {
        constructors
            .iter()
            .enumerate()
            .map(|(tag, ctor)| {
                self.build_single_ctor_info(
                    state, type_name, ctor, tag, var_map, span,
                )
            })
            .collect()
    }

    /// Build a single CtorBuild with resolved field types.
    fn build_single_ctor_info(
        &self,
        state: &CheckState,
        _type_name: &TypeName,
        ctor: &ConstructorDef,
        tag: usize,
        var_map: &HashMap<Symbol, TypeId>,
        span: Span,
    ) -> Result<CtorBuild, CranelispError> {
        let fields: Vec<FieldInfo> = ctor
            .fields
            .iter()
            .map(|field| {
                let ty = self.resolve_type_expr_in_module(
                    &field.type_expr, var_map, &state.current_module, span,
                )?;
                Ok(FieldInfo {
                    name: field.name.clone(),
                    ty,
                })
            })
            .collect::<Result<Vec<_>, CranelispError>>()?;

        Ok(CtorBuild {
            name: ctor.name.clone(),
            tag,
            fields,
            docstring: ctor.docstring.clone(),
            internal: false,
        })
    }

    /// Register constructors in the current module's symbol table.
    ///
    /// Each constructor becomes a `ModuleEntry::Def` with
    /// `kind: DefKind::Constructor { type_name, tag, field_count, internal,
    /// type_def }` and a synthesised `DefnVariant` body whose body expression is
    /// `Expr::ConstrADT { type_name, tag, fields, span }` (per S69 Submission 35
    /// and `DefKind::Constructor` rustdoc in `cranelisp_types::module`).
    ///
    /// **Product type facet (S79 Option 3a, FIXME 0319).** When
    /// `product_type_def` is `Some`, this registration is for a single-ctor
    /// **product** type (type-name == ctor-name); the lone ctor's `Def` carries
    /// `type_def: Some(..)` so the shared `"Rectangle"` entry answers both as a
    /// got-slotted ctor `Def` AND as its own type. Sum/enum ctors pass `None`
    /// and carry `type_def: None`. `type_docstring` is the deftype-level
    /// docstring, applied to the product ctor's `Def` when the ctor itself has
    /// none (the product `Def` has no separate `TypeDef` entry to hold it).
    #[allow(clippy::too_many_arguments)]
    fn register_constructors(
        &self,
        state: &mut CheckState,
        fqtn: &FQTypeName,
        ctor_builds: &[CtorBuild],
        adt_type: &Type,
        type_var_ids: &[TypeId],
        visibility: Visibility,
        product_type_def: Option<&TypeDefInfo>,
        type_docstring: &Option<String>,
    ) {
        for ctor in ctor_builds {
            // The product type facet (if any) attaches to the ctor whose name
            // matches the type name — for a product that is the single ctor.
            let ctor_type_def: Option<Box<TypeDefInfo>> = product_type_def
                .filter(|td| td.name.name.as_ref() == ctor.name.as_ref())
                .map(|td| Box::new(td.clone()));
            let ctor_scheme = build_constructor_scheme(
                ctor, adt_type, type_var_ids,
            );
            let param_names: Vec<Symbol> =
                ctor.fields.iter().map(|f| f.name.clone()).collect();
            // Synthesise a DefnVariant body whose body expression is
            // Expr::ConstrADT. Per `DefKind::Constructor` rustdoc — the
            // backend lowers `Expr::ConstrADT` directly; the ctor's metadata
            // (type_name, tag, field_count) lives on `DefKind::Constructor`.
            let body_span = Span::SYNTHETIC;
            let synth_params: Vec<(Symbol, Option<cranelisp_types::TypeExpr>)> =
                param_names.iter().cloned().map(|n| (n, None)).collect();
            let synth_body = Expr::ConstrADT {
                type_name: fqtn.clone(),
                tag: ctor.tag,
                fields: param_names
                    .iter()
                    .map(|n| Expr::var(n.clone(), body_span))
                    .collect(),
                span: body_span,
                inferred_type: None,
            };
            let ast = DefnVariant {
                params: synth_params,
                body: synth_body,
                span: body_span,
            };

            // 0249-a: constructors are GOT-slotted callable values, exactly
            // like user fns (program.rs user-fn slotting). Without a slot, a
            // constructor reached *as a value* (`(map Some xs)`, `(let [f None]
            // f)`) has no address to load — BC §3's minimal-JIT-setup boundary
            // assumes the slot exists on the entry before int enumerates the
            // name into the compile batch (0249-b). Allocated at registration
            // (Decision 0048 primitives-got-slotting precedent). Nullary
            // constructors are slotted too — addressability does not depend on
            // arity. The slot is allocated before the entry is built; the
            // `&mut` guard is dropped before the later `.insert` re-acquires it.
            // The ctor is a concrete callable born with its slot (S83 deferred
            // allocation, Principle 20): the slot rides on
            // `DefKind::Constructor.got_slot`, not a flat `Def` field.
            let slot = self.current_symbol_table_mut(state).allocate_got_slot();
            let is_product_ctor = ctor_type_def.is_some();
            let mut builder = ModuleEntry::def(
                ctor_scheme,
                DefKind::Constructor {
                    got_slot: slot,
                    type_name: fqtn.clone(),
                    tag: ctor.tag,
                    field_count: ctor.fields.len(),
                    internal: ctor.internal,
                    type_def: ctor_type_def,
                    mode_summary: None,
                },
            )
            .visibility(visibility)
            .param_names(param_names)
            .ast(ast);
            // Ctor docstring wins; for the product ctor (which has no separate
            // `TypeDef` entry) fall back to the deftype-level docstring.
            let doc = ctor.docstring.clone().or_else(|| {
                if is_product_ctor { type_docstring.clone() } else { None }
            });
            if let Some(doc) = doc {
                builder = builder.docstring(doc);
            }
            // COMMIT 1 (reader-widening) keeps the CURRENT bare keying — the
            // canonical-key writer flip (gated on `is_product_ctor`) lands in
            // commit 2 (design §4).
            self.current_symbol_table_mut(state).insert(ctor.name.clone(), builder.build());

            // **Field accessors (S83, FIXME 0351(a), spec §5.2.6).** For each
            // named field of a **product** type, auto-generate a free accessor
            // fn `field :: (Fn [ProductType] FieldType)` whose body is a
            // single-arm `match` over the product ctor binding all fields and
            // returning the named one. Accessors are first-class concrete
            // callables (born with a GOT slot, like the ctor). Only products
            // get accessors — a sum/enum field accessor would be partial
            // (undefined for the other ctors). The backend lowers the
            // `Expr::Match` body; no new node, no backend change.
            if is_product_ctor {
                self.synthesise_field_accessors(
                    state, fqtn, ctor, adt_type, type_var_ids, visibility,
                );
            }
        }
    }

    /// Synthesise free field-accessor fns for a product type's ctor.
    ///
    /// Each named field `f` of `(deftype Box [:Int v ..])` yields a free fn
    /// `v :: (Fn [Box] Int)` with body `(match self [(Box v ..) v])`. Born
    /// concrete (GOT slot at synthesis), registered under the field name in the
    /// type's own module.
    ///
    /// **Collision policy (spec §5.2.6 "Duplicate field names in the same
    /// scope" + §8.6.5 bare-name ambiguity; user ruling S83 W2).** Before
    /// inserting an accessor `f`:
    /// - If `f` already names a **field accessor** for ANOTHER product type in
    ///   this module (cross-type duplicate field name), the bare name `f` is
    ///   **ambiguous (poisoned)** under the §8.6.5 distinct-terminal rule: the
    ///   symbol-table entry is replaced with `ModuleEntry::Ambiguous` (the same
    ///   sentinel an import collision installs), and any later use of bare `f`
    ///   is a compile-time error listing the qualified alternatives (`Box.v`,
    ///   `Cup.v`). The compiler MUST NOT fold the colliding accessors into an
    ///   argument-type-dispatched overload and MUST NOT silently pick a winner.
    ///   The field stays reachable via `match` (§6) and module-qualification
    ///   (§8.5.1).
    /// - If `f` already names a NON-accessor binding (a user `(defn f ..)`, a
    ///   ctor, etc.), the synthesis is **refused with a clear diagnostic** —
    ///   the accessor does not silently shadow or corrupt the existing binding.
    fn synthesise_field_accessors(
        &self,
        state: &mut CheckState,
        fqtn: &FQTypeName,
        ctor: &CtorBuild,
        adt_type: &Type,
        type_var_ids: &[TypeId],
        visibility: Visibility,
    ) {
        let all_field_names: Vec<Symbol> =
            ctor.fields.iter().map(|f| f.name.clone()).collect();
        for field in &ctor.fields {
            self.synthesise_one_accessor(
                state,
                fqtn,
                ctor,
                adt_type,
                type_var_ids,
                visibility,
                field,
                &all_field_names,
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn synthesise_one_accessor(
        &self,
        state: &mut CheckState,
        fqtn: &FQTypeName,
        ctor: &CtorBuild,
        adt_type: &Type,
        type_var_ids: &[TypeId],
        visibility: Visibility,
        field: &FieldInfo,
        all_field_names: &[Symbol],
    ) {
        use cranelisp_types::{MatchArm, Pattern, SymbolRef};

        let accessor_name = field.name.clone();
        let body_span = Span::SYNTHETIC;

        // Accessor scheme `(Fn [ProductType] FieldType)`, quantified over the
        // type's params (so `(Fn [(Box a)] a)` for a polymorphic product).
        let accessor_ty = Type::Fn(
            vec![adt_type.clone()],
            Box::new(field.ty.clone()),
        );
        let scheme = Scheme {
            type_vars: type_var_ids.to_vec(),
            constraints: HashMap::new(),
            ty: accessor_ty,
        };

        // Body: `(fn [self] (match self [(Ctor f1 f2 ..) field]))`.
        let self_sym = Symbol::from("self$accessor");
        let body = Expr::Match {
            scrutinee: Box::new(Expr::var(self_sym.clone(), body_span)),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: SymbolRef::new(None, ctor.name.clone()),
                    bindings: all_field_names.to_vec(),
                    span: body_span,
                },
                body: Expr::var(field.name.clone(), body_span),
                span: body_span,
            }],
            span: body_span,
            compiler_generated: true,
            inferred_type: None,
        };
        let ast = DefnVariant {
            params: vec![(self_sym, None)],
            body,
            span: body_span,
        };

        // Collision inspection (read the current entry, if any). A name is an
        // ACCESSOR collision only when THIS check previously synthesised it as
        // an accessor (tracked in `synthesised_accessor_names`); any other
        // pre-existing binding — a user `defn`, a ctor, an import — is a
        // NON-accessor collision (refused). Classifying by `DefKind` alone is
        // insufficient: a user `(defn v ..)` is also a `UserFn`.
        //
        // An ACCESSOR collision (cross-type duplicate field name) POISONS the
        // bare name per §5.2.6/§8.6.5 — it does NOT overload (user ruling
        // S83 W2). Once poisoned, a further accessor of the same name (a third
        // colliding type) leaves it poisoned and extends the alternatives list.
        //
        // FIXME 0365 — read the UNION view (staging-first, then live) rather
        // than staging alone. In the REPL each form is its own cluster, so a
        // pre-existing `(defn v ..)` from an EARLIER cluster is committed to
        // LIVE, not the current cluster's staging; a staging-only probe missed
        // it and the §5.2.6 collision warning never fired across cluster
        // boundaries. `probe_module_entry_owned` checks staging then live, so
        // the collision is detected whether the colliding binding is in the
        // same cluster (staging) or a prior one (live).
        //
        // FIXME 0366 — re-derive the accessor collision from the COMMITTED LIVE
        // entry, not solely the per-`CheckState` `synthesised_accessor_names`
        // set. At the REPL each input is a separate cluster, so the FIRST
        // accessor `v` (from `Box`) is committed to LIVE in a PRIOR cluster and
        // is therefore absent from THIS cluster's `synthesised_accessor_names`.
        // A set-only probe mis-classifies the collision as `NonAccessor`
        // (suppress-and-first-wins) instead of the spec'd cross-type ambiguity
        // (§5.2.6 + §8.6.5). The fix: structurally recognise a committed
        // synthesised accessor in the probed entry (its `self$accessor` param +
        // `Fn [ADT] _` scheme name the owning type) and, when that owning type
        // DIFFERS from the type now being synthesised, treat it as the same
        // `Accessor` poison the same-cluster path produces. A committed accessor
        // for the SAME type (a redefinition of that one deftype) is NOT a
        // cross-type collision and must NOT poison.
        let probed = self
            .probe_module_entry_owned(&state.current_module, accessor_name.as_ref());
        let existing_present = probed.is_some();
        // Structurally classify a COMMITTED (prior-cluster) entry under the bare
        // name as a synthesised accessor (FIXME 0366). Under the INVERTED model
        // (§1.6) the bare key is normally an `Import` ALIAS onto the canonical
        // `Type.field` accessor — so FOLLOW that alias edge to the canonical
        // `Def` and classify THAT (a bare `Import → m/Box.v` means bare `v` is
        // already an accessor alias of `Box`, the first owner of a contested
        // field). `committed_accessor_kind` itself only classifies a `Def`/
        // `Ambiguous`; the bare-alias follow is added here. `Concrete` carries
        // the owning product type; `Poisoned` is an already-`Ambiguous` bare name
        // (third+ colliding type); `NotAccessor` is a genuine non-accessor (user
        // defn, ctor) or absent entry.
        let committed = match probed.as_ref() {
            Some(ModuleEntry::Import { source, .. })
                if source.module == fqtn.module =>
            {
                // Follow the bare alias to its canonical accessor source.
                self.probe_module_entry_owned(&source.module, source.symbol.as_ref())
                    .as_ref()
                    .map(committed_accessor_kind)
                    .unwrap_or(CommittedAccessor::NotAccessor)
            }
            Some(entry) => committed_accessor_kind(entry),
            None => CommittedAccessor::NotAccessor,
        };
        // The prior owning type when the committed entry is a single concrete
        // accessor — used to keep the cross-cluster ambiguity hint complete.
        let committed_accessor_owner: Option<FQTypeName> = match &committed {
            CommittedAccessor::Concrete(owner) => Some(owner.clone()),
            _ => None,
        };
        let existing_kind: Option<AccessorCollision> = if !existing_present {
            None
        } else if state.synthesised_accessor_names.contains(&accessor_name) {
            // Either a single concrete accessor (first collision) or an
            // already-poisoned name (third+ collision) — both are accessor
            // collisions and poison.
            Some(AccessorCollision::Accessor)
        } else {
            // The set is per-cluster, so a committed accessor from a PRIOR
            // cluster is absent from it. Re-derive the collision from the
            // committed LIVE entry instead (FIXME 0366) so the REPL behaves like
            // `--run`/`--link` (one cluster).
            match &committed {
                // Same-type redefinition (the one deftype re-run): overwrite the
                // accessor afresh — NOT a cross-type duplicate-field clash.
                CommittedAccessor::Concrete(owner) if owner == fqtn => None,
                // Cross-type committed accessor, or an already-poisoned accessor
                // name: poison the bare name as ambiguous.
                CommittedAccessor::Concrete(_) | CommittedAccessor::Poisoned => {
                    Some(AccessorCollision::Accessor)
                }
                // A non-accessor binding (user defn, ctor, import, …): refuse.
                CommittedAccessor::NotAccessor => Some(AccessorCollision::NonAccessor),
            }
        };

        // Per-type-qualified CANONICAL accessor key (`Box.v`) — the `Type.field`
        // canonical field accessor (FIXME 0365 Item 1 / spec §8.5.2, INVERTED
        // model §1.6). `Box.v` is ALWAYS the real, uniformly-Public compiled
        // accessor `Def`; bare `field` (`v`) is a CONVENIENCE ALIAS onto it.
        let qualified_key = member_key(&fqtn.name, accessor_name.as_ref());

        // The CANONICAL accessor `Def` (`Box.v`) is minted UNCONDITIONALLY (in
        // every arm — fresh, contested, or over a non-accessor bare binding): it
        // is the real `DefKind::UserFn` with its own GOT slot + body, uniformly
        // `Visibility::Public`, carrying the `self$accessor` marker so
        // `committed_accessor_kind` recognises it. One compiled function per
        // `(type, field)`, keyed `Type.field` (§1.6.1). Because it is always
        // real, there is NO poison re-mint / reconstruction (the as-built's
        // `remint_first_accessor_under_qualified_key` + poison-arm `Def`-minting
        // are DELETED — net deletion, Principle 6).
        let canonical_slot = self.current_symbol_table_mut(state).allocate_got_slot();
        let canonical = ModuleEntry::def(
            scheme,
            DefKind::UserFn {
                fn_state: cranelisp_types::UserFnState::Concrete { got_slot: canonical_slot, mode_summary: None },
            },
        )
        .visibility(Visibility::Public)
        .param_names(vec![Symbol::from("self$accessor")])
        .ast(ast)
        .docstring(format!(
            "Canonical field accessor `{}.{}` of type `{}`.",
            fqtn.name, accessor_name, fqtn.name
        ));
        self.current_symbol_table_mut(state)
            .insert(qualified_key.clone(), canonical.build());

        // Track the field's owning type for the bare-alias ambiguity diagnostic.
        state.synthesised_accessor_names.insert(accessor_name.clone());
        state
            .accessor_owning_types
            .entry(accessor_name.clone())
            .or_default()
            .push(fqtn.clone());

        match existing_kind {
            None => {
                // Bare `field` (`v`) → a CONVENIENCE ALIAS onto the canonical
                // `Box.v` (§1.6.1). An `ModuleEntry::Import` entry is EXCLUDED
                // from `defined_symbols()` (no second compiled function) and
                // carries NO GOT slot of its own; `resolve_got_target`'s
                // `resolve_chain` FOLLOWS the `Import` edge to the canonical slot
                // for BOTH call and value-position dispatch, and
                // `extract_scheme_from_entry_owned` follows it for typing. ZERO
                // extra compiled function + ZERO extra GOT slot — the alias is
                // free. When exactly one type owns `field`, the bare alias
                // resolves cleanly to the canonical accessor.
                self.current_symbol_table_mut(state).insert(
                    accessor_name.clone(),
                    ModuleEntry::Import {
                        source: cranelisp_types::FQSymbol {
                            module: fqtn.module.clone(),
                            symbol: qualified_key.clone(),
                        },
                        visibility,
                    },
                );
            }
            Some(AccessorCollision::Accessor) => {
                // Cross-type duplicate field name (spec §5.2.6 + §8.6.5; user
                // ruling S83 W2 + the INVERTED model §1.6.2): ambiguity lives in
                // the BARE ALIAS. The canonical `Box.v`/`Cup.v` `Def`s are each
                // unconditionally real (minted above) and stay valid — no cliff,
                // no re-mint, because they were always real. The bare `v` key (an
                // alias to the FIRST type's `Box.v`) now has two candidate targets
                // → replace it with the `Ambiguous` sentinel (the same sentinel an
                // import collision installs, §8.6.4), listing the canonical
                // alternatives `Box.v` / `Cup.v`. Any later BARE use of `v` is a
                // compile-time error naming those alternatives.
                self.current_symbol_table_mut(state).insert(
                    accessor_name.clone(),
                    ModuleEntry::Ambiguous { visibility },
                );
                // Seed the FIRST owning type (cross-cluster: recorded in a now-
                // discarded prior cluster's state, FIXME 0366) before this one so
                // the ambiguity hint's alternatives are complete. The per-cluster
                // `accessor_owning_types` push above already added `fqtn`.
                if let Some(prior) = &committed_accessor_owner {
                    let alts = state
                        .accessor_owning_types
                        .entry(accessor_name.clone())
                        .or_default();
                    if !alts.contains(prior) {
                        // Insert the prior owner ahead of the current one so the
                        // alternatives read first-defined-first.
                        alts.insert(0, prior.clone());
                    }
                }
            }
            Some(AccessorCollision::NonAccessor) => {
                // A pre-existing NON-accessor bare binding (a user `(defn v …)`,
                // a ctor, an import): the canonical `Box.v` accessor is still
                // minted (unconditionally, above), so the field stays reachable
                // via `Box.v`. The bare alias is NOT installed over the
                // conflicting user binding (no silent shadow / dispatch
                // corruption); record a deferred diagnostic and leave bare `v` as
                // the user's binding (§1.6.2).
                state.deferred_accessor_collisions.push((
                    accessor_name.clone(),
                    fqtn.name.as_ref().to_string(),
                ));
            }
        }
    }

    /// Enumerate the **field-accessor names** owned by `fqtn` — the single
    /// enumeration point for impl-time collision checking (FIXME 0365 Item 2)
    /// and any future "list this type's accessors" introspection (Principle 7).
    ///
    /// The returned names are the BARE field names (`v`): a trait `impl` method
    /// is written with the bare name, and §7.3.1 scopes the collision to that
    /// bare name.
    ///
    /// **Inverted model (§1.6 / §2.3).** The CANONICAL field accessor of `fqtn`
    /// is a real Public `Def` keyed `Type.field` (`Box.v`) in `fqtn.module` —
    /// `committed_accessor_kind` classifies it `Concrete(fqtn)`. The field name
    /// is the **terminal segment after the last `.`** of the canonical key
    /// (`Box.v` → `v`). Because the canonical accessor is ALWAYS real (never
    /// poisoned — poison lives only in the bare alias, §1.6.2), the recognizer
    /// walk alone is complete: the as-built's `accessor_owning_types` poison-
    /// consult and the import-alias witness branch both drop out (§2.6,
    /// Principle 6 — the inversion deletes those special-cases). The enumeration
    /// reads the **union view** (staging then live) via `for_each_in_module` so
    /// a REPL `impl` colliding with a canonical accessor defined in an earlier
    /// cluster is still detected (the FIXME-0366 cross-cluster footgun).
    pub(crate) fn field_accessor_names_of(
        &self,
        _state: &CheckState,
        fqtn: &FQTypeName,
    ) -> std::collections::HashSet<Symbol> {
        let mut names = std::collections::HashSet::new();

        // The recognizer over the owning module's union view: every canonical
        // `Concrete(fqtn)` accessor `Def`. The field name is the terminal segment
        // after the last `.` of the canonical key (`Box.v` → `v`); a defensively
        // bare-keyed accessor (no `.`) contributes its whole key.
        self.for_each_in_module(&fqtn.module, |name, entry| {
            if matches!(
                committed_accessor_kind(entry),
                CommittedAccessor::Concrete(ref owner) if owner == fqtn
            ) {
                let field = name.as_ref().rsplit('.').next().unwrap_or(name.as_ref());
                names.insert(Symbol::from(field));
            }
        });

        names
    }

    /// Reconstruct the canonical accessor alternatives (`Box.v`, `Cup.v`) for a
    /// poisoned bare field name from the DURABLE symbol table — the cross-cluster
    /// (REPL) fallback for the ambiguity diagnostic.
    ///
    /// Same-cluster (`--run`) the alternatives are carried on the per-`CheckState`
    /// `accessor_owning_types` map, populated as each accessor is synthesised in
    /// the SAME `check_forms` call that later sees the bare use. The REPL drives
    /// each form as its own cluster with a FRESH `CheckState` (`form.rs`), so by
    /// the time `(v …)` is checked the map is empty — the `deftype`s that poisoned
    /// `v` ran in now-discarded prior clusters. The poison itself survives (it is
    /// the `ModuleEntry::Ambiguous` sentinel in the live table), but the owning-
    /// type list does not. This re-derives that list structurally, mirroring the
    /// cross-cluster recognition `committed_accessor_kind` already does for the
    /// FIXME-0366 impl-collision case: it walks the current module's union view
    /// for every canonical `Type.field` accessor `Def` whose terminal field
    /// segment equals `name` and reads each owner off the accessor's
    /// `(Fn [Owner] _)` scheme. Returns the owners in first-defined order
    /// (symbol-table iteration is registration-ordered) so the rendered hint reads
    /// `Box.v or Cup.v`. Empty when `name` owns no synthesised accessor (caller
    /// then emits the bare ambiguity message with no qualified-accessor hint).
    pub(crate) fn reconstruct_accessor_alternatives(
        &self,
        state: &CheckState,
        name: &str,
    ) -> Vec<FQTypeName> {
        let mut owners: Vec<FQTypeName> = Vec::new();
        self.for_each_in_module(&state.current_module, |key, entry| {
            // The canonical member key is `Type.member` (a field accessor `Box.v`
            // OR a sum constructor `Maybe.Some`, S109); its terminal segment
            // (after the last `.`) is the bare member name. A defensively
            // bare-keyed member (no `.`) contributes its whole key.
            let member = key.as_ref().rsplit('.').next().unwrap_or(key.as_ref());
            if member != name {
                return;
            }
            if let Some(owner) = committed_member_owner(entry)
                && !owners.contains(&owner)
            {
                owners.push(owner);
            }
        });
        owners
    }
}

/// Classification of a COMMITTED (live, prior-cluster) symbol-table entry as a
/// synthesised field accessor (FIXME 0366). The same-cluster path keys off the
/// per-`CheckState` `synthesised_accessor_names` set; cross-cluster (the REPL)
/// must instead re-derive the accessor identity structurally from the committed
/// entry, since the prior accessor was committed in a now-discarded cluster.
pub(crate) enum CommittedAccessor {
    /// A single concrete synthesised accessor; carries its owning product type
    /// (read from the accessor's `(Fn [ADT] _)` scheme).
    Concrete(FQTypeName),
    /// An already-poisoned (`Ambiguous`) accessor name — a third colliding type
    /// re-poisons it; no single owning type to read.
    Poisoned,
    /// Not a synthesised accessor (a user `defn`, a ctor, an import, …).
    NotAccessor,
}

/// Recognise a committed entry as a synthesised field accessor and read its
/// owning product type (FIXME 0366).
///
/// A synthesised accessor is registered (in `synthesise_one_accessor`) as a
/// concrete `DefKind::UserFn` whose sole parameter is the `self$accessor`
/// sentinel and whose scheme is `(Fn [ProductType] FieldType)`. The
/// `self$accessor` param + the `Fn [ADT] _` scheme shape together uniquely mark
/// an accessor and name its owning type — no user `(defn …)` mints that
/// signature. A poisoned accessor name surfaces as `ModuleEntry::Ambiguous`.
pub(crate) fn committed_accessor_kind<C: cranelisp_types::CodeStore>(
    entry: &ModuleEntry<C>,
) -> CommittedAccessor {
    match entry {
        ModuleEntry::Ambiguous { .. } => CommittedAccessor::Poisoned,
        ModuleEntry::Def { kind, scheme, param_names, .. }
            if matches!(
                kind.as_ref(),
                DefKind::UserFn {
                    fn_state: cranelisp_types::UserFnState::Concrete { .. }
                }
            ) && param_names.len() == 1
                && param_names[0].as_ref() == "self$accessor" =>
        {
            match &scheme.ty {
                Type::Fn(params, _) if params.len() == 1 => match &params[0] {
                    Type::ADT(fqtn, _) => CommittedAccessor::Concrete(fqtn.clone()),
                    _ => CommittedAccessor::NotAccessor,
                },
                _ => CommittedAccessor::NotAccessor,
            }
        }
        _ => CommittedAccessor::NotAccessor,
    }
}

/// The owning type of a canonical dotted MEMBER `Def` — either a synthesised
/// field accessor (`Box.v`, owner read from its `(Fn [ADT] _)` scheme) OR a sum
/// constructor (`Maybe.Some`, owner read directly from `DefKind::Constructor
/// .type_name`) (S109, design §1.2/§3.1). The single "owning type of the member
/// under this key" recognizer both the dotted resolver (`resolve_dotted_member
/// _entry`) and the registration collision classifier share, so accessor and
/// ctor members resolve + poison through ONE shape (Principle 7). Returns `None`
/// for a non-member entry (a plain user `defn`, an `Ambiguous` sentinel, a
/// non-`Constructor` `Def`, an `Import`/`Reexport` edge, …).
pub(crate) fn committed_member_owner<C: cranelisp_types::CodeStore>(
    entry: &ModuleEntry<C>,
) -> Option<FQTypeName> {
    // Field accessor?
    if let CommittedAccessor::Concrete(owner) = committed_accessor_kind(entry) {
        return Some(owner);
    }
    // Sum constructor? (The product ctor also carries a `type_name` but is keyed
    // at the type name, never probed as a canonical dotted member — so reading
    // its `type_name` here is harmless; the resolver's degenerate-key miss and
    // the registration product gate keep products out of this path.)
    if let ModuleEntry::Def { kind, .. } = entry
        && let DefKind::Constructor { type_name, .. } = kind.as_ref()
    {
        return Some(type_name.clone());
    }
    None
}

/// The kind of pre-existing binding an accessor synthesis collides with.
enum AccessorCollision {
    /// Another field accessor (same field name across product types) — POISON
    /// the bare name as ambiguous per §5.2.6 + §8.6.5 (no overload, no winner).
    Accessor,
    /// A non-accessor binding (user defn, ctor, …) — refuse the synthesis.
    NonAccessor,
}

/// Build a type scheme for a constructor.
///
/// Nullary constructors: `forall [vars]. ADT_Type`
/// Data constructors:    `forall [vars]. (Fn [field_types] ADT_Type)`
///
/// If there are no type parameters (vars is empty), the scheme is monomorphic.
fn build_constructor_scheme(
    ctor: &CtorBuild,
    adt_type: &Type,
    type_var_ids: &[TypeId],
) -> Scheme {
    let type_vars: Vec<TypeId> = type_var_ids.to_vec();

    let ty = if ctor.fields.is_empty() {
        // Nullary constructor: just the ADT type
        adt_type.clone()
    } else {
        // Data constructor: Fn([field types...], ADT type)
        let param_types: Vec<Type> = ctor
            .fields
            .iter()
            .map(|f| f.ty.clone())
            .collect();
        Type::Fn(param_types, Box::new(adt_type.clone()))
    };

    Scheme {
        type_vars,
        constraints: HashMap::new(),
        ty,
    }
}

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Check exhaustiveness of match arms against an ADT type.
    ///
    /// Returns Ok(()) if the match is exhaustive, Err with details otherwise.
    /// A match is exhaustive if:
    /// 1. All constructors of the ADT are covered, OR
    /// 2. A wildcard or variable pattern is present.
    #[allow(dead_code)] // default-rooted accessor pair; exercised via TestFixture in `#[cfg(test)]`.
    pub(crate) fn check_exhaustiveness(
        &self,
        type_name: &TypeName,
        covered_ctors: &[Symbol],
        has_wildcard: bool,
        span: Span,
    ) -> Result<(), CranelispError> {
        self.check_exhaustiveness_in_module(
            &cranelisp_types::FQTypeName::new(ModuleFullPath::from("user"), type_name.clone()),
            covered_ctors,
            has_wildcard,
            span,
        )
    }

    /// Module-rooted variant of [`Self::check_exhaustiveness`].
    ///
    /// **FQTypeName migration (Sprint 67 Wave 3 — FIXME 0151).** Takes
    /// `&FQTypeName` per `design/arch/facades/types.md` §"FQTypeName migration
    /// plan (Sprint 67)" §"typecheck" — match-arm checks are post-resolution,
    /// so the type identifier carries its module context binding.
    pub(crate) fn check_exhaustiveness_in_module(
        &self,
        fq_type_name: &cranelisp_types::FQTypeName,
        covered_ctors: &[Symbol],
        has_wildcard: bool,
        span: Span,
    ) -> Result<(), CranelispError> {
        if has_wildcard {
            return Ok(());
        }

        let type_def = self.lookup_type_def_in_module(&fq_type_name.module, &fq_type_name.name).ok_or_else(|| {
            CranelispError::TypeError {
                message: format!("unknown type in match: {}", fq_type_name.name),
                location: ErrorLocation::from_span(span),
            }
        })?;

        // Exclude internal constructors from exhaustiveness — user code cannot
        // and need not cover them (design/typecheck/io-types.md §1). Per-ctor
        // `internal` lives on `DefKind::Constructor.internal`; resolve each
        // name to its Def in the type's defining module.
        let ctor_internal_flags: Vec<(Symbol, bool)> = type_def
            .constructors
            .iter()
            .map(|ctor_sym| {
                // **BR-2 (S109 blast radius, design §4.2).** Post the dotted-ctor
                // keying change the bare key is an `Import` alias (or `Ambiguous`),
                // so a raw bare probe no longer lands on the `Constructor` `Def`
                // and every ctor would default `internal: false` — silently
                // admitting `IO`'s internal `Bind`/`Pure`/`Effect` into user
                // exhaustiveness. Probe the CANONICAL `member_key(Type, Ctor)`
                // first (where a sum ctor's real `Def` now lives), then fall back
                // to a chain-follow of the bare name (covers a hand-seeded internal
                // ctor like `Bind` that kept its bare storage key, and the product
                // dual-facet at the type-name key).
                let internal = self
                    .probe_module_entry_owned(
                        &fq_type_name.module,
                        member_key(&fq_type_name.name, ctor_sym.as_ref()).as_ref(),
                    )
                    .or_else(|| {
                        self.resolve_terminal_entry_and_home(
                            &fq_type_name.module,
                            ctor_sym.as_ref(),
                        )
                        .map(|(e, _)| e)
                    })
                    .and_then(|e| match e {
                        ModuleEntry::Def { kind, .. } => match kind.as_ref() {
                            DefKind::Constructor { internal, .. } => Some(*internal),
                            _ => None,
                        },
                        _ => None,
                    })
                    .unwrap_or(false);
                (ctor_sym.clone(), internal)
            })
            .collect();
        let all_ctors: std::collections::HashSet<String> = ctor_internal_flags
            .iter()
            .filter(|(_, internal)| !*internal)
            .map(|(name, _)| name.as_ref().to_string())
            .collect();

        // Normalise covered constructor names to their bare terminal segment so
        // both FQ pattern names (`macros/SCons` — module-qualified, Principle 17)
        // AND dotted canonical names (`Maybe.Some` — the S109 dotted-ctor form,
        // design §4.1 / BR-1) compare equal to `type_def`'s bare constructor
        // names (`SCons`, `Some`). Strip after BOTH separators: the `/` module
        // prefix first, then the `.` type prefix of the terminal segment. Without
        // the `.`-strip a TOTAL match written with dotted arms is falsely reported
        // non-exhaustive.
        let covered: std::collections::HashSet<String> = covered_ctors
            .iter()
            .map(|c| {
                let s = c.as_ref();
                let after_slash = s.rsplit('/').next().unwrap_or(s);
                after_slash.rsplit('.').next().unwrap_or(after_slash).to_string()
            })
            .collect();

        let missing: Vec<String> = all_ctors.difference(&covered).cloned().collect();

        if missing.is_empty() {
            Ok(())
        } else {
            let mut missing_sorted = missing;
            missing_sorted.sort();
            Err(CranelispError::TypeError {
                message: format!(
                    "non-exhaustive match on {}: missing constructor(s) {}",
                    fq_type_name.name,
                    missing_sorted.join(", ")
                ),
                location: ErrorLocation::from_span(span),
            })
        }
    }
}

#[cfg(test)]
mod tests;
