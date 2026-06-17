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
    Visibility,
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
        // Structurally classify a COMMITTED (prior-cluster) entry under this name
        // as a synthesised accessor (FIXME 0366). `CommittedAccessor::Concrete`
        // carries the owning product type (read off the accessor's `Fn [ADT] _`
        // scheme + `self$accessor` param marker); `Poisoned` is an already-
        // ambiguous accessor name (a third colliding type — stays poisoned, no
        // single owner to read); `None` is a non-accessor / absent entry.
        let committed = probed
            .as_ref()
            .map(committed_accessor_kind)
            .unwrap_or(CommittedAccessor::NotAccessor);
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

        match existing_kind {
            None => {
                // Fresh accessor: a single concrete callable born with its slot.
                let slot = self.current_symbol_table_mut(state).allocate_got_slot();
                let builder = ModuleEntry::def(
                    scheme,
                    DefKind::UserFn {
                        fn_state: cranelisp_types::UserFnState::Concrete { got_slot: slot },
                    },
                )
                .visibility(visibility)
                .param_names(vec![Symbol::from("self$accessor")])
                .ast(ast)
                .docstring(format!(
                    "Field accessor for `{}` of type `{}`.",
                    accessor_name, fqtn.name
                ));
                self.current_symbol_table_mut(state)
                    .insert(accessor_name.clone(), builder.build());
                state.synthesised_accessor_names.insert(accessor_name.clone());
                // Record this name's sole owning type so a later collision can
                // list all qualified alternatives in the ambiguity error.
                state
                    .accessor_owning_types
                    .entry(accessor_name.clone())
                    .or_default()
                    .push(fqtn.clone());
            }
            Some(AccessorCollision::Accessor) => {
                // Cross-type duplicate field name (spec §5.2.6 + §8.6.5; user
                // ruling S83 W2): POISON the bare name. Replace the symbol-table
                // entry with `ModuleEntry::Ambiguous` — the same sentinel an
                // import collision installs (§8.6.4). No overload, no winner.
                // Any later use of bare `v` is a compile-time error listing the
                // qualified alternatives. The field stays reachable via `match`
                // and module-qualification.
                self.current_symbol_table_mut(state).insert(
                    accessor_name.clone(),
                    ModuleEntry::Ambiguous { visibility },
                );
                // Extend the alternatives list with this colliding type. The
                // name is kept in `synthesised_accessor_names` so a third
                // colliding type re-enters this same poison arm.
                let alts = state
                    .accessor_owning_types
                    .entry(accessor_name.clone())
                    .or_default();
                // FIXME 0366 — cross-cluster case: the FIRST owning type was
                // recorded in a now-discarded prior cluster's state, so seed it
                // from the committed accessor we just probed before appending
                // this one, keeping the ambiguity hint's alternatives complete.
                if let Some(prior) = &committed_accessor_owner
                    && !alts.contains(prior)
                {
                    alts.push(prior.clone());
                }
                alts.push(fqtn.clone());
            }
            Some(AccessorCollision::NonAccessor) => {
                // Refuse: record a deferred collision diagnostic. The accessor
                // is NOT inserted (no silent shadow / dispatch corruption). The
                // existing binding is left intact.
                state.deferred_accessor_collisions.push((
                    accessor_name.clone(),
                    fqtn.name.as_ref().to_string(),
                ));
            }
        }
    }

}

/// Classification of a COMMITTED (live, prior-cluster) symbol-table entry as a
/// synthesised field accessor (FIXME 0366). The same-cluster path keys off the
/// per-`CheckState` `synthesised_accessor_names` set; cross-cluster (the REPL)
/// must instead re-derive the accessor identity structurally from the committed
/// entry, since the prior accessor was committed in a now-discarded cluster.
enum CommittedAccessor {
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
fn committed_accessor_kind<C: cranelisp_types::CodeStore>(
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
                let internal = self
                    .probe_module_entry_owned(&fq_type_name.module, ctor_sym.as_ref())
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

        // Strip optional module prefix from covered constructor names so FQ
        // pattern names (`macros/SCons`) compare equal to type_def's bare
        // constructor names (`SCons`). FQ constructor references are valid
        // under Principle 17 cross-module navigation.
        let covered: std::collections::HashSet<String> = covered_ctors
            .iter()
            .map(|c| {
                let s = c.as_ref();
                s.rsplit('/').next().unwrap_or(s).to_string()
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
mod tests {
    use super::*;
    use crate::builtins::FixtureBuilder;
    use crate::checker::TestFixture;
    use cranelisp_types::{ConstructorDef, ModuleFullPath};

    /// Minimal fixture for the ADT-registration tests (FIXME 0243 narrowing).
    ///
    /// These tests register their OWN ADTs via `register_type_def_self` and,
    /// where a constructor field is a builtin scalar (`:Int`/`:Bool`/…), seed
    /// the corresponding `primitives` import edge into the user module inline
    /// (see `test_register_product_type_with_fields`). None of them consult the
    /// heavy `full()` world (special forms, seeded primitives, the `macros`
    /// module, the IO ADT). An empty builder is the minimal starting position;
    /// `user` is the current module exactly as under `TestFixture::new()`.
    fn tf() -> TestFixture {
        TestFixture::with_content(FixtureBuilder::new())
    }

    /// Minimal fixture for the internal-constructor tests (FIXME 0243
    /// narrowing). These consult the seeded `IO` ADT in `primitives` (whose
    /// `Bind` constructor carries `internal: true`); `with_io()` seeds it and
    /// requires `with_builtin_type_names()` first (bootstrap order — IO's field
    /// types reference builtin scalars). Nothing heavier (special forms, the
    /// Ring 0/1/3 primitive `Def`s, the `macros` module) is consulted.
    fn tf_io() -> TestFixture {
        TestFixture::with_content(
            FixtureBuilder::new().with_builtin_type_names().with_io(),
        )
    }

    /// Test helper: create an FQTypeName in the "user" module (default current
    /// module for both `TestFixture::new()` and the narrowed `tf()`).
    fn user_fqtn(name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from("user"), TypeName::from(name))
    }

    fn make_ctor(name: &str) -> ConstructorDef {
        ConstructorDef {
            name: Symbol::from(name),
            docstring: None,
            fields: vec![],
            span: Span::SYNTHETIC,
        }
    }

    // spec: 05-definitions §5.2.3 — enum type registers constructors in symbol table
    #[test]
    fn test_register_enum_type() {
        let mut tc = tf();
        tc.register_type_def_self(
            &TypeName::from("Color"),
            &None,
            &[],
            &[make_ctor("Red"), make_ctor("Green"), make_ctor("Blue")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // Type should be registered in symbol table
        assert!(tc.lookup_type_def(&TypeName::from("Color")).is_some());

        // Constructors should be in symbol table
        assert!(tc.symbol_table().get("Red").is_some());
        assert!(tc.symbol_table().get("Green").is_some());
        assert!(tc.symbol_table().get("Blue").is_some());

        // Constructor type lookup
        assert_eq!(
            tc.lookup_constructor_type("Red"),
            Some(TypeName::from("Color"))
        );
    }

    // spec: 05-definitions §5.2.7 — nullary constructor scheme is ADT type
    #[test]
    fn test_constructor_scheme_is_adt_type() {
        let mut tc = tf();
        tc.register_type_def_self(
            &TypeName::from("Bool2"),
            &None,
            &[],
            &[make_ctor("True2"), make_ctor("False2")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        if let Some(ModuleEntry::Def { kind, scheme, .. }) = tc.symbol_table().get("True2")
            && matches!(kind.as_ref(), DefKind::Constructor { .. })
        {
            assert_eq!(scheme.ty, Type::ADT(user_fqtn("Bool2"), vec![]));
        } else {
            panic!("True2 should be a Constructor entry");
        }
    }

    // spec: 05-definitions §5.2.2 — polymorphic sum type: None and Some constructors
    #[test]
    fn test_register_polymorphic_option() {
        let mut tc = tf();
        tc.register_type_def_self(
            &TypeName::from("Option"),
            &None,
            &[Symbol::from("a")],
            &[
                make_ctor("None"),
                ConstructorDef {
                    name: Symbol::from("Some"),
                    docstring: None,
                    fields: vec![cranelisp_types::FieldDef {
                        name: Symbol::from("val"),
                        type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                        span: Span::SYNTHETIC,
                    }],
                    span: Span::SYNTHETIC,
                },
            ],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // None should be polymorphic: forall [a]. (Option a)
        if let Some(ModuleEntry::Def { kind, scheme, .. }) = tc.symbol_table().get("None")
            && matches!(kind.as_ref(), DefKind::Constructor { .. })
        {
            assert_eq!(scheme.type_vars.len(), 1, "None should have 1 quantified var");
            match &scheme.ty {
                Type::ADT(name, args) => {
                    assert_eq!(name.name.as_ref(), "Option");
                    assert_eq!(args.len(), 1);
                    assert!(matches!(args[0], Type::Var(_)));
                }
                _ => panic!("None should have ADT type, got {:?}", scheme.ty),
            }
        } else {
            panic!("None should be a Constructor entry");
        }

        // Some should be polymorphic: forall [a]. (Fn [a] (Option a))
        if let Some(ModuleEntry::Def { kind, scheme, .. }) = tc.symbol_table().get("Some")
            && matches!(kind.as_ref(), DefKind::Constructor { .. })
        {
            assert_eq!(scheme.type_vars.len(), 1, "Some should have 1 quantified var");
            match &scheme.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params.len(), 1);
                    assert!(matches!(params[0], Type::Var(_)));
                    match ret.as_ref() {
                        Type::ADT(name, args) => {
                            assert_eq!(name.name.as_ref(), "Option");
                            assert_eq!(args.len(), 1);
                            // The type var in Fn param should match the one in ADT args
                            assert_eq!(params[0], args[0]);
                        }
                        _ => panic!("Some return should be ADT"),
                    }
                }
                _ => panic!("Some should have Fn type, got {:?}", scheme.ty),
            }
        } else {
            panic!("Some should be a Constructor entry");
        }
    }

    // spec: 05-definitions §5.2.1 — product type constructor is function from fields to ADT
    #[test]
    fn test_register_product_type_with_fields() {
        // This test's product ctor has `:Int`/`:Bool` fields and seeds the
        // matching `primitives` Import edges inline, so the `Int`/`Bool`
        // IntrinsicType entries must exist in the `primitives` module —
        // `with_builtin_type_names()` seeds them (FIXME 0243: the one adt.rs
        // test that genuinely needs builtin scalar field types in scope).
        let mut tc = TestFixture::with_content(FixtureBuilder::new().with_builtin_type_names());
        // Phase B Part 2b: bare `Int`/`Bool` references in field types
        // require explicit import per Principle 17 (no Tier 2 universe walk).
        // Import registration is no longer a typecheck concern (facade
        // `typecheck.md` §"Import/export registration is not a typecheck
        // concern"); seed the needed `Int`/`Bool` import edges directly into
        // the user module's symbol table, mirroring what the orchestrator's
        // import installer would land.
        {
            let mut user = tc.symbol_table_mut();
            for ty in ["Int", "Bool"] {
                user.insert(
                    Symbol::from(ty),
                    cranelisp_types::ModuleEntry::Import {
                        source: cranelisp_types::FQSymbol {
                            module: cranelisp_types::ModuleFullPath::from("primitives"),
                            symbol: Symbol::from(ty),
                        },
                        visibility: Visibility::Public,
                    },
                );
            }
        }
        tc.register_type_def_self(
            &TypeName::from("Pair"),
            &None,
            &[],
            &[ConstructorDef {
                name: Symbol::from("MkPair"),
                docstring: None,
                fields: vec![
                    cranelisp_types::FieldDef {
                        name: Symbol::from("x"),
                        type_expr: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
                        span: Span::SYNTHETIC,
                    },
                    cranelisp_types::FieldDef {
                        name: Symbol::from("y"),
                        type_expr: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Bool"))),
                        span: Span::SYNTHETIC,
                    },
                ],
                span: Span::SYNTHETIC,
            }],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // MkPair :: (Fn [Int Bool] Pair)
        if let Some(ModuleEntry::Def { kind, scheme, .. }) = tc.symbol_table().get("MkPair")
            && matches!(kind.as_ref(), DefKind::Constructor { .. })
        {
            assert!(scheme.type_vars.is_empty(), "MkPair should be monomorphic");
            assert_eq!(
                scheme.ty,
                Type::Fn(
                    vec![Type::Int, Type::Bool],
                    Box::new(Type::ADT(user_fqtn("Pair"), vec![]))
                )
            );
        } else {
            panic!("MkPair should be a Constructor entry");
        }

        // Per S70: TypeDefInfo.constructors is Vec<Symbol>; per-ctor metadata
        // (param_names, field types from scheme.ty) lives on the ctor's Def.
        let info = tc.lookup_type_def(&TypeName::from("Pair")).unwrap();
        assert_eq!(info.constructors.len(), 1);
        assert_eq!(info.constructors[0].as_ref(), "MkPair");
        if let Some(ModuleEntry::Def { kind, scheme, param_names, .. }) =
            tc.symbol_table().get("MkPair")
        {
            if let DefKind::Constructor { field_count, .. } = kind.as_ref() {
                assert_eq!(*field_count, 2);
            } else {
                panic!("MkPair should be DefKind::Constructor");
            }
            assert_eq!(param_names.len(), 2);
            assert_eq!(param_names[0].as_ref(), "x");
            assert_eq!(param_names[1].as_ref(), "y");
            let field_types = match &scheme.ty {
                Type::Fn(p, _) => p.clone(),
                _ => panic!("MkPair scheme should be Fn"),
            };
            assert_eq!(field_types[0], Type::Int);
            assert_eq!(field_types[1], Type::Bool);
        } else {
            panic!("MkPair should be a Def in symbol table");
        }
    }

    /// Seed `Int`/`Bool` import edges into the user module so bare scalar field
    /// types resolve (mirrors `test_register_product_type_with_fields`).
    fn tf_with_scalar_imports() -> TestFixture {
        let tc = TestFixture::with_content(FixtureBuilder::new().with_builtin_type_names());
        {
            let mut user = tc.symbol_table_mut();
            for ty in ["Int", "Bool"] {
                user.insert(
                    Symbol::from(ty),
                    cranelisp_types::ModuleEntry::Import {
                        source: cranelisp_types::FQSymbol {
                            module: cranelisp_types::ModuleFullPath::from("primitives"),
                            symbol: Symbol::from(ty),
                        },
                        visibility: Visibility::Public,
                    },
                );
            }
        }
        tc
    }

    fn product_int_field(type_name: &str, field: &str) -> ConstructorDef {
        ConstructorDef {
            name: Symbol::from(type_name),
            docstring: None,
            fields: vec![cranelisp_types::FieldDef {
                name: Symbol::from(field),
                type_expr: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(
                    None,
                    TypeName::from("Int"),
                )),
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        }
    }

    // spec: 05-definitions §5.2.6 — Generated Accessors. A product field
    // synthesises a free accessor fn `field :: (Fn [ProductType] FieldType)`,
    // born concrete (UserFn with a GOT slot), registered under the field name.
    #[test]
    fn product_field_synthesises_concrete_accessor() {
        let mut tc = tf_with_scalar_imports();
        tc.register_type_def_self(
            &TypeName::from("Box"),
            &None,
            &[],
            &[product_int_field("Box", "v")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // `v` is a concrete UserFn accessor with a GOT slot.
        match tc.symbol_table().get("v") {
            Some(entry @ ModuleEntry::Def { kind, scheme, ast, param_names, .. }) => {
                assert!(
                    matches!(
                        kind.as_ref(),
                        DefKind::UserFn {
                            fn_state: cranelisp_types::UserFnState::Concrete { .. }
                        }
                    ),
                    "accessor `v` must be a concrete UserFn"
                );
                assert!(entry.callable_got_slot().is_some(), "accessor needs a GOT slot");
                assert!(ast.is_some(), "accessor carries a synthesised match body");
                assert_eq!(param_names.len(), 1, "accessor takes one parameter");
                // Scheme: (Fn [Box] Int).
                match &scheme.ty {
                    Type::Fn(params, ret) => {
                        assert_eq!(params.len(), 1);
                        assert_eq!(params[0], Type::ADT(user_fqtn("Box"), vec![]));
                        assert_eq!(ret.as_ref(), &Type::Int);
                    }
                    other => panic!("accessor scheme must be Fn, got {other:?}"),
                }
            }
            other => panic!("accessor `v` must be a Def, got {other:?}"),
        }
    }

    // spec: 05-definitions §5.2.6 — accessor synthesis over an existing
    // NON-accessor binding is refused (safe disposition): the existing binding
    // is kept, the collision is recorded for a non-fatal diagnostic, and the
    // accessor is NOT inserted (no silent shadow).
    #[test]
    fn accessor_collision_with_nonaccessor_is_refused() {
        let mut tc = tf_with_scalar_imports();
        // Seed a user binding `v` (a NotDetermined UserFn) BEFORE the deftype.
        tc.symbol_table_mut().insert(
            Symbol::from("v"),
            ModuleEntry::def(
                Scheme { type_vars: vec![], constraints: HashMap::new(), ty: Type::Int },
                DefKind::UserFn { fn_state: cranelisp_types::UserFnState::NotDetermined },
            )
            .visibility(Visibility::Public)
            .build(),
        );
        tc.register_type_def_self(
            &TypeName::from("Box"),
            &None,
            &[],
            &[product_int_field("Box", "v")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // A NotDetermined UserFn is NOT an accessor → the collision is refused.
        // The existing entry is unchanged (still NotDetermined), and the clash
        // is recorded as a deferred collision for the finalize warning.
        match tc.symbol_table().get("v") {
            Some(ModuleEntry::Def { kind, .. }) => assert!(
                matches!(
                    kind.as_ref(),
                    DefKind::UserFn {
                        fn_state: cranelisp_types::UserFnState::NotDetermined
                    }
                ),
                "existing non-accessor `v` must be preserved, not overwritten"
            ),
            other => panic!("`v` must still be the user binding, got {other:?}"),
        }
        assert!(
            tc.state
                .deferred_accessor_collisions
                .iter()
                .any(|(n, _)| n.as_ref() == "v"),
            "the accessor/binding collision must be recorded for a diagnostic"
        );
    }

    // spec: 05-definitions §5.2.6 "Duplicate field names in the same scope" +
    // 08-modules §8.6.5 bare-name ambiguity (user ruling S83 W2) — two product
    // types with the same field name POISON the bare accessor: it becomes
    // ambiguous (`ModuleEntry::Ambiguous`), NOT an argument-type-dispatched
    // overload and NOT a silently-picked winner. The second deftype is not
    // rejected as a duplicate definition; the colliding field's value stays
    // reachable via `match`. The owning types are recorded as the qualified
    // alternatives the ambiguity error lists.
    #[test]
    fn cross_type_duplicate_field_poisons_bare_accessor() {
        let mut tc = tf_with_scalar_imports();
        tc.register_type_def_self(
            &TypeName::from("Box"),
            &None,
            &[],
            &[product_int_field("Box", "v")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // Before the collision, `v` is a normal concrete first-class accessor.
        assert!(
            matches!(
                tc.symbol_table().get("v"),
                Some(ModuleEntry::Def { kind, .. })
                    if matches!(
                        kind.as_ref(),
                        DefKind::UserFn {
                            fn_state: cranelisp_types::UserFnState::Concrete { .. }
                        }
                    )
            ),
            "single-type accessor `v` is a concrete UserFn before any collision"
        );

        // The SECOND deftype with the same field name MUST NOT be rejected as a
        // duplicate definition — registration succeeds.
        tc.register_type_def_self(
            &TypeName::from("Cup"),
            &None,
            &[],
            &[product_int_field("Cup", "v")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // `v` is now POISONED — an `Ambiguous` sentinel, NOT an `Overloaded`
        // base and NOT a winner-picked concrete UserFn.
        match tc.symbol_table().get("v") {
            Some(ModuleEntry::Ambiguous { .. }) => {}
            other => panic!(
                "`v` must be poisoned (Ambiguous) after the cross-type field-name \
                 collision, got {other:?}"
            ),
        }
        // It is NOT folded into the overload mechanism: no `Overloaded` base, no
        // mangled `v$Box`/`v$Cup` variants exist.
        assert!(
            tc.symbol_table().get("v$Box").is_none()
                && tc.symbol_table().get("v$Cup").is_none(),
            "duplicate-field accessors MUST NOT be folded into mangled overload \
             variants (no v$Box / v$Cup)"
        );

        // Both owning types are recorded as the qualified alternatives the
        // ambiguity error lists (`Box.v` and `Cup.v`).
        let alts = tc
            .state
            .accessor_owning_types
            .get(&Symbol::from("v"))
            .expect("poisoned accessor must record its owning-type alternatives");
        assert_eq!(alts.len(), 2, "Box + Cup are the alternatives");
        let names: Vec<&str> = alts.iter().map(|t| t.name.as_ref()).collect();
        assert!(names.contains(&"Box"));
        assert!(names.contains(&"Cup"));

        // The field stays reachable via `match` to each colliding type: a
        // single-arm match binding the product's field type-checks for both
        // Box and Cup (an e2e asserts the runtime values; here we assert the
        // typechecker accepts the destructuring path the spec promises).
        for ty in ["Box", "Cup"] {
            use cranelisp_types::{MatchArm, Pattern, SymbolRef};
            let scrutinee = Expr::ConstrADT {
                type_name: user_fqtn(ty),
                tag: 0,
                fields: vec![Expr::IntLit {
                    value: 5,
                    span: Span::SYNTHETIC,
                    inferred_type: None,
                }],
                span: Span::SYNTHETIC,
                inferred_type: None,
            };
            let mut match_expr = Expr::Match {
                scrutinee: Box::new(scrutinee),
                arms: vec![MatchArm {
                    pattern: Pattern::Constructor {
                        name: SymbolRef::new(None, Symbol::from(ty)),
                        bindings: vec![Symbol::from("v")],
                        span: Span::SYNTHETIC,
                    },
                    body: Expr::var(Symbol::from("v"), Span::SYNTHETIC),
                    span: Span::SYNTHETIC,
                }],
                span: Span::SYNTHETIC,
                compiler_generated: false,
                inferred_type: None,
            };
            let ty_result = tc.infer_expr_for_test(&mut match_expr);
            assert!(
                ty_result.is_ok(),
                "`(match ({ty} 5) [({ty} v) v])` must type-check despite the \
                 poisoned bare accessor — match access is always available \
                 (§5.2.6); got {ty_result:?}"
            );
        }
    }

    /// Simulate the REPL's per-input cluster boundary: each input line is a
    /// SEPARATE cluster with a FRESH per-`CheckState` accessor-tracking state,
    /// while the live symbol table (committed entries) persists. Clearing the
    /// two per-cluster sets reproduces exactly the condition FIXME 0366 closes —
    /// the second deftype's accessor synthesis cannot see the first accessor in
    /// `synthesised_accessor_names`, only in the committed live table.
    fn new_cluster(tc: &mut TestFixture) {
        tc.state.synthesised_accessor_names.clear();
        tc.state.accessor_owning_types.clear();
        tc.state.deferred_accessor_collisions.clear();
    }

    // spec: 05-definitions §5.2.6 + 08-modules §8.6.5 (FIXME 0366) — at the REPL
    // each input is its own cluster, so a duplicate field-name accessor defined
    // in a LATER cluster must still POISON the bare name (ambiguous), re-deriving
    // the collision from the COMMITTED live accessor entry — NOT silently
    // first-wins. This pins the typecheck seam the e2e
    // `repl_cross_cluster_duplicate_field_accessor_is_ambiguous` exercises.
    #[test]
    fn cross_cluster_duplicate_field_poisons_bare_accessor() {
        let mut tc = tf_with_scalar_imports();
        // Cluster 1: `Box` — `v` is a normal concrete accessor.
        tc.register_type_def_self(
            &TypeName::from("Box"),
            &None,
            &[],
            &[product_int_field("Box", "v")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();
        assert!(
            matches!(
                tc.symbol_table().get("v"),
                Some(ModuleEntry::Def { kind, .. })
                    if matches!(
                        kind.as_ref(),
                        DefKind::UserFn {
                            fn_state: cranelisp_types::UserFnState::Concrete { .. }
                        }
                    )
            ),
            "single-type accessor `v` is a concrete UserFn after cluster 1"
        );

        // Cluster boundary: fresh per-`CheckState` accessor tracking; the live
        // `v` accessor entry from cluster 1 stays committed.
        new_cluster(&mut tc);

        // Cluster 2: `Cup` with the SAME field name `v`. The set-only classifier
        // would mis-read this as a non-accessor collision (suppress-and-first-
        // wins); the committed-live re-derivation poisons it instead.
        tc.register_type_def_self(
            &TypeName::from("Cup"),
            &None,
            &[],
            &[product_int_field("Cup", "v")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // `v` is POISONED (`Ambiguous`), exactly as in the single-cluster
        // (`--run`/`--link`) path — NOT first-wins-suppressed.
        match tc.symbol_table().get("v") {
            Some(ModuleEntry::Ambiguous { .. }) => {}
            other => panic!(
                "cross-cluster duplicate-field accessor `v` must be poisoned \
                 (Ambiguous), got {other:?}"
            ),
        }
        // It was NOT routed down the suppress-and-first-wins (non-accessor)
        // refusal path: no deferred collision recorded for `v`.
        assert!(
            !tc.state
                .deferred_accessor_collisions
                .iter()
                .any(|(n, _)| n.as_ref() == "v"),
            "cross-cluster duplicate field must poison, not record a \
             suppress-and-first-wins refusal"
        );
        // The cross-cluster ambiguity hint lists BOTH owning types even though
        // `Box` was recorded in the now-discarded cluster-1 state — the prior
        // owner is re-seeded from the committed accessor.
        let alts = tc
            .state
            .accessor_owning_types
            .get(&Symbol::from("v"))
            .expect("poisoned accessor must record its owning-type alternatives");
        let names: Vec<&str> = alts.iter().map(|t| t.name.as_ref()).collect();
        assert!(names.contains(&"Box"), "Box must be an alternative, got {names:?}");
        assert!(names.contains(&"Cup"), "Cup must be an alternative, got {names:?}");
    }

    // spec: 05-definitions §5.2.6 (FIXME 0366) — NEGATIVE: a SINGLE product
    // type's accessor synthesised in its own cluster, with no duplicate field
    // name across types, must remain a normal concrete accessor across cluster
    // boundaries (the legitimate case must not be wrongly poisoned).
    #[test]
    fn cross_cluster_single_type_accessor_not_poisoned() {
        let mut tc = tf_with_scalar_imports();
        tc.register_type_def_self(
            &TypeName::from("Box"),
            &None,
            &[],
            &[product_int_field("Box", "v")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();
        // A LATER cluster with an UNRELATED type/field — no collision on `v`.
        new_cluster(&mut tc);
        tc.register_type_def_self(
            &TypeName::from("Cup"),
            &None,
            &[],
            &[product_int_field("Cup", "w")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();
        // `v` stays a concrete accessor; `w` is a fresh concrete accessor.
        for name in ["v", "w"] {
            assert!(
                matches!(
                    tc.symbol_table().get(name),
                    Some(ModuleEntry::Def { kind, .. })
                        if matches!(
                            kind.as_ref(),
                            DefKind::UserFn {
                                fn_state: cranelisp_types::UserFnState::Concrete { .. }
                            }
                        )
                ),
                "distinct-field accessor `{name}` must remain a concrete UserFn \
                 across clusters (no spurious poison), got {:?}",
                tc.symbol_table().get(name)
            );
        }
    }

    // spec: 05-definitions §5.2.6 (FIXME 0366) — NEGATIVE: re-running the SAME
    // deftype in a later cluster (a redefinition, NOT two distinct types sharing
    // a field name) must NOT poison its accessor — the committed accessor's
    // owning type equals the type being re-synthesised, so it overwrites afresh.
    #[test]
    fn cross_cluster_same_type_redefinition_not_poisoned() {
        let mut tc = tf_with_scalar_imports();
        tc.register_type_def_self(
            &TypeName::from("Box"),
            &None,
            &[],
            &[product_int_field("Box", "v")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();
        // Cluster boundary, then RE-DEFINE the same `Box` type.
        new_cluster(&mut tc);
        tc.register_type_def_self(
            &TypeName::from("Box"),
            &None,
            &[],
            &[product_int_field("Box", "v")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();
        // `v` is still a normal concrete accessor — a same-type redefinition is
        // not a cross-type duplicate-field collision.
        match tc.symbol_table().get("v") {
            Some(ModuleEntry::Def { kind, .. })
                if matches!(
                    kind.as_ref(),
                    DefKind::UserFn {
                        fn_state: cranelisp_types::UserFnState::Concrete { .. }
                    }
                ) => {}
            other => panic!(
                "`v` after a same-type Box redefinition must stay a concrete \
                 accessor, not be poisoned, got {other:?}"
            ),
        }
    }

    // spec: 06-pattern-matching §6.5.1 — all constructors covered passes exhaustiveness
    #[test]
    fn test_exhaustiveness_all_covered() {
        let mut tc = tf();
        tc.register_type_def_self(
            &TypeName::from("Color"),
            &None,
            &[],
            &[make_ctor("Red"), make_ctor("Green"), make_ctor("Blue")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        let covered = vec![
            Symbol::from("Red"),
            Symbol::from("Green"),
            Symbol::from("Blue"),
        ];
        assert!(tc
            .check_exhaustiveness(&TypeName::from("Color"), &covered, false, Span::SYNTHETIC)
            .is_ok());
    }

    // spec: 06-pattern-matching §6.5.1 — missing constructor fails exhaustiveness check
    #[test]
    fn test_exhaustiveness_missing_constructor() {
        let mut tc = tf();
        tc.register_type_def_self(
            &TypeName::from("Color"),
            &None,
            &[],
            &[make_ctor("Red"), make_ctor("Green"), make_ctor("Blue")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        let covered = vec![Symbol::from("Red"), Symbol::from("Green")];
        let err = tc
            .check_exhaustiveness(&TypeName::from("Color"), &covered, false, Span::SYNTHETIC)
            .unwrap_err();
        assert!(err.message().contains("Blue"));
    }

    // spec: 06-pattern-matching §6.5.1 — wildcard pattern covers all constructors
    #[test]
    fn test_exhaustiveness_wildcard_covers_all() {
        let mut tc = tf();
        tc.register_type_def_self(
            &TypeName::from("Color"),
            &None,
            &[],
            &[make_ctor("Red"), make_ctor("Green"), make_ctor("Blue")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // Empty covered but has wildcard -- ok
        assert!(tc
            .check_exhaustiveness(&TypeName::from("Color"), &[], true, Span::SYNTHETIC)
            .is_ok());
    }

    // spec: 05-definitions §5.2.7 — constructors receive sequential integer tags
    #[test]
    fn test_constructor_tags() {
        let mut tc = tf();
        tc.register_type_def_self(
            &TypeName::from("Dir"),
            &None,
            &[],
            &[
                make_ctor("North"),
                make_ctor("South"),
                make_ctor("East"),
                make_ctor("West"),
            ],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        let info = tc.lookup_type_def(&TypeName::from("Dir")).unwrap();
        // Per S70: info.constructors is Vec<Symbol>; tag lives on the ctor's
        // ModuleEntry::Def's DefKind::Constructor.
        let table = tc.symbol_table();
        for (i, name) in ["North", "South", "East", "West"].iter().enumerate() {
            assert_eq!(info.constructors[i].as_ref(), *name);
            if let Some(ModuleEntry::Def { kind, .. }) = table.get(*name) {
                if let DefKind::Constructor { tag, .. } = kind.as_ref() {
                    assert_eq!(*tag, i, "{name} should have tag {i}");
                } else {
                    panic!("{name} should be DefKind::Constructor");
                }
            } else {
                panic!("{name} should be a Def in symbol table");
            }
        }
    }

    // --- Ring 1: Polymorphic ADT tests ---

    /// Helper: register (Option a) with None and Some[:a val].
    fn register_option(tc: &mut TestFixture) {
        tc.register_type_def_self(
            &TypeName::from("Option"),
            &None,
            &[Symbol::from("a")],
            &[
                make_ctor("None"),
                ConstructorDef {
                    name: Symbol::from("Some"),
                    docstring: None,
                    fields: vec![cranelisp_types::FieldDef {
                        name: Symbol::from("val"),
                        type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                        span: Span::SYNTHETIC,
                    }],
                    span: Span::SYNTHETIC,
                },
            ],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();
    }

    // spec: 05-definitions §5.2.2 — polymorphic type parameters recorded in TypeDefInfo
    #[test]
    fn test_polymorphic_type_params_recorded() {
        let mut tc = tf();
        register_option(&mut tc);

        let info = tc.lookup_type_def(&TypeName::from("Option")).unwrap();
        assert_eq!(info.type_params.len(), 1);
        assert_eq!(info.type_params[0].as_ref(), "a");
    }

    // spec: 05-definitions §5.2.7 — polymorphic ADT constructors receive sequential tags
    #[test]
    fn test_polymorphic_constructor_tags() {
        let mut tc = tf();
        register_option(&mut tc);

        let info = tc.lookup_type_def(&TypeName::from("Option")).unwrap();
        // Per S70: info.constructors is Vec<Symbol>; tags live on the per-ctor
        // ModuleEntry::Def's DefKind::Constructor.
        assert_eq!(info.constructors[0].as_ref(), "None");
        assert_eq!(info.constructors[1].as_ref(), "Some");
        let table = tc.symbol_table();
        for (i, name) in ["None", "Some"].iter().enumerate() {
            if let Some(ModuleEntry::Def { kind, .. }) = table.get(*name)
                && let DefKind::Constructor { tag, .. } = kind.as_ref()
            {
                assert_eq!(*tag, i, "{name} should have tag {i}");
            } else {
                panic!("{name} should be Def(Constructor)");
            }
        }
    }

    // spec: 04-adt §4.2 — constructors are GOT-slotted callable values (0249-a)
    //
    // Every synthesised `DefKind::Constructor` entry must carry a `got_slot`,
    // exactly like a user fn — a constructor reached as a value (`(map Some
    // xs)`, `(let [f None] f)`) needs an address to load. Distinct
    // constructors get distinct slots (monotonic allocator, no aliasing). The
    // +Neg facet: the nullary `None` is slotted too — addressability does not
    // depend on arity, so a naive "only data ctors need slots" implementation
    // (which would leave `None` at `None`) is rejected.
    #[test]
    fn constructors_get_got_slots() {
        let mut tc = tf();
        register_option(&mut tc);

        let table = tc.symbol_table();
        let slot_of = |name: &str| -> Option<usize> {
            match table.get(name) {
                Some(entry @ ModuleEntry::Def { kind, .. }) => {
                    assert!(
                        matches!(kind.as_ref(), DefKind::Constructor { .. }),
                        "{name} should be a Constructor entry"
                    );
                    // S83 (Principle 20): the ctor's slot rides on
                    // `DefKind::Constructor.got_slot`, read via the accessor.
                    entry.callable_got_slot()
                }
                _ => panic!("{name} should be a Def(Constructor) entry"),
            }
        };

        // Data constructor `Some` is slotted.
        let some_slot = slot_of("Some").expect("Some must have a GOT slot");
        // +Neg: the nullary constructor `None` is slotted too — not left at
        // `None` by an arity-gated implementation.
        let none_slot = slot_of("None").expect("nullary None must have a GOT slot");

        // Distinct constructors get distinct slots (monotonic allocator).
        assert_ne!(
            some_slot, none_slot,
            "distinct constructors must not alias the same GOT slot"
        );
    }

    // spec: 03-types §3.3 — polymorphic field type resolves to type variable
    #[test]
    fn test_polymorphic_field_has_var_type() {
        let mut tc = tf();
        register_option(&mut tc);

        let info = tc.lookup_type_def(&TypeName::from("Option")).unwrap();
        // Per S70: info.constructors[i] is Symbol; field metadata lives on the
        // ctor's Def — param_names + scheme.ty's Fn signature.
        assert_eq!(info.constructors[1].as_ref(), "Some");
        if let Some(ModuleEntry::Def { kind, scheme, param_names, .. }) =
            tc.symbol_table().get("Some")
        {
            if let DefKind::Constructor { field_count, .. } = kind.as_ref() {
                assert_eq!(*field_count, 1);
            } else {
                panic!("Some should be DefKind::Constructor");
            }
            assert_eq!(param_names.len(), 1);
            assert_eq!(param_names[0].as_ref(), "val");
            // Field type should be a type variable (the allocated ID)
            match &scheme.ty {
                Type::Fn(params, _) => {
                    assert_eq!(params.len(), 1);
                    assert!(matches!(params[0], Type::Var(_)));
                }
                _ => panic!("Some scheme should be Fn"),
            }
        } else {
            panic!("Some should be a Def in symbol table");
        }
    }

    // spec: 06-pattern-matching §6.5.1 — exhaustiveness with mixed nullary and data constructors
    #[test]
    fn test_exhaustiveness_with_mixed_constructors() {
        let mut tc = tf();
        register_option(&mut tc);

        // Missing None
        let covered = vec![Symbol::from("Some")];
        let err = tc
            .check_exhaustiveness(
                &TypeName::from("Option"),
                &covered,
                false,
                Span::SYNTHETIC,
            )
            .unwrap_err();
        assert!(err.message().contains("None"));

        // Missing Some
        let covered = vec![Symbol::from("None")];
        let err = tc
            .check_exhaustiveness(
                &TypeName::from("Option"),
                &covered,
                false,
                Span::SYNTHETIC,
            )
            .unwrap_err();
        assert!(err.message().contains("Some"));

        // Both covered
        let covered = vec![Symbol::from("None"), Symbol::from("Some")];
        assert!(tc
            .check_exhaustiveness(
                &TypeName::from("Option"),
                &covered,
                false,
                Span::SYNTHETIC,
            )
            .is_ok());
    }

    // spec: 05-definitions §5.2.4 — shortcut product type with bare field names gets type vars
    #[test]
    fn test_shortcut_product_type() {
        // (deftype Pair [first second]) -- bare field names with type vars
        let mut tc = tf();
        tc.register_type_def_self(
            &TypeName::from("Pair"),
            &None,
            &[Symbol::from("a"), Symbol::from("b")],
            &[ConstructorDef {
                name: Symbol::from("MkPair"),
                docstring: None,
                fields: vec![
                    cranelisp_types::FieldDef {
                        name: Symbol::from("first"),
                        type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                        span: Span::SYNTHETIC,
                    },
                    cranelisp_types::FieldDef {
                        name: Symbol::from("second"),
                        type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("b")),
                        span: Span::SYNTHETIC,
                    },
                ],
                span: Span::SYNTHETIC,
            }],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // MkPair :: forall [a, b]. (Fn [a b] (Pair a b))
        if let Some(ModuleEntry::Def { kind, scheme, .. }) = tc.symbol_table().get("MkPair")
            && matches!(kind.as_ref(), DefKind::Constructor { .. })
        {
            assert_eq!(scheme.type_vars.len(), 2, "MkPair should have 2 quantified vars");
            match &scheme.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params.len(), 2);
                    match ret.as_ref() {
                        Type::ADT(fqtn, args) => {
                            assert_eq!(fqtn.name.as_ref(), "Pair");
                            assert_eq!(args.len(), 2);
                            // param vars should match the ADT arg vars
                            assert_eq!(params[0], args[0]);
                            assert_eq!(params[1], args[1]);
                        }
                        _ => panic!("MkPair return should be ADT"),
                    }
                }
                _ => panic!("MkPair should have Fn type"),
            }
        } else {
            panic!("MkPair should be a Constructor entry");
        }
    }

    // spec: 05-definitions §5.2.2 — multi-parameter polymorphic ADT registration
    #[test]
    fn test_register_multi_param_type() {
        // (deftype (Either a b) (Left [:a val]) (Right [:b val]))
        let mut tc = tf();
        tc.register_type_def_self(
            &TypeName::from("Either"),
            &None,
            &[Symbol::from("a"), Symbol::from("b")],
            &[
                ConstructorDef {
                    name: Symbol::from("Left"),
                    docstring: None,
                    fields: vec![cranelisp_types::FieldDef {
                        name: Symbol::from("val"),
                        type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                        span: Span::SYNTHETIC,
                    }],
                    span: Span::SYNTHETIC,
                },
                ConstructorDef {
                    name: Symbol::from("Right"),
                    docstring: None,
                    fields: vec![cranelisp_types::FieldDef {
                        name: Symbol::from("val"),
                        type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("b")),
                        span: Span::SYNTHETIC,
                    }],
                    span: Span::SYNTHETIC,
                },
            ],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        let info = tc.lookup_type_def(&TypeName::from("Either")).unwrap();
        assert_eq!(info.type_params.len(), 2);
        assert_eq!(info.constructors.len(), 2);

        // Both constructors should have 2 quantified vars
        if let Some(ModuleEntry::Def { kind, scheme, .. }) = tc.symbol_table().get("Left")
            && matches!(kind.as_ref(), DefKind::Constructor { .. })
        {
            assert_eq!(scheme.type_vars.len(), 2);
        } else {
            panic!("Left should be a Constructor entry");
        }
    }

    // spec: 03-types §3.2.2 — type-expr resolution validates ADT arity against
    // the registered TypeDef's type-parameter count.
    #[test]
    fn test_resolution_validates_registered_arity() {
        use cranelisp_types::{TypeExpr, TypeRef};

        let mut tc = tf();
        register_option(&mut tc);
        tc.register_type_def_self(
            &TypeName::from("Color"),
            &None,
            &[],
            &[make_ctor("Red")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // `Option` has arity 1: `(Option Color)` resolves; applying it with
        // zero args is rejected. (`Color` is registered in `user`; `Int` lives
        // in `primitives` and is not import-reachable from `user` here.)
        let opt_color = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Option")),
            vec![TypeExpr::Named(TypeRef::new(None, TypeName::from("Color")))],
        );
        assert!(tc.resolve_type_expr_in_user(&opt_color).is_ok());

        let opt_zero =
            TypeExpr::Applied(TypeRef::new(None, TypeName::from("Option")), vec![]);
        assert!(tc.resolve_type_expr_in_user(&opt_zero).is_err());

        // `Color` has arity 0: bare `Color` resolves to its ADT type.
        let color = TypeExpr::Named(TypeRef::new(None, TypeName::from("Color")));
        assert!(tc.resolve_type_expr_in_user(&color).is_ok());

        // Unknown type name errors.
        let bogus = TypeExpr::Named(TypeRef::new(None, TypeName::from("Nope")));
        assert!(tc.resolve_type_expr_in_user(&bogus).is_err());
    }

    // spec: 05-definitions §5.2.7 — nullary monomorphic constructor scheme is bare ADT type
    #[test]
    fn test_build_constructor_scheme_nullary_mono() {
        let ctor = CtorBuild {
            name: Symbol::from("Red"),
            tag: 0,
            fields: vec![],
            docstring: None,
            internal: false,
        };
        let adt_type = Type::ADT(user_fqtn("Color"), vec![]);
        let scheme = build_constructor_scheme(&ctor, &adt_type, &[]);

        assert!(scheme.type_vars.is_empty());
        assert_eq!(scheme.ty, Type::ADT(user_fqtn("Color"), vec![]));
    }

    // spec: 05-definitions §5.2.1 — data constructor scheme is Fn from fields to ADT
    #[test]
    fn test_build_constructor_scheme_data_mono() {
        let ctor = CtorBuild {
            name: Symbol::from("Point"),
            tag: 0,
            fields: vec![
                FieldInfo { name: Symbol::from("x"), ty: Type::Int },
                FieldInfo { name: Symbol::from("y"), ty: Type::Int },
            ],
            docstring: None,
            internal: false,
        };
        let adt_type = Type::ADT(user_fqtn("Point"), vec![]);
        let scheme = build_constructor_scheme(&ctor, &adt_type, &[]);

        assert!(scheme.type_vars.is_empty());
        assert_eq!(
            scheme.ty,
            Type::Fn(
                vec![Type::Int, Type::Int],
                Box::new(Type::ADT(user_fqtn("Point"), vec![]))
            )
        );
    }

    // spec: 05-definitions §5.2.2 — polymorphic constructor scheme quantifies over type params
    #[test]
    fn test_build_constructor_scheme_polymorphic() {
        let ctor = CtorBuild {
            name: Symbol::from("Some"),
            tag: 1,
            fields: vec![
                FieldInfo { name: Symbol::from("val"), ty: Type::Var(42) },
            ],
            docstring: None,
            internal: false,
        };
        let adt_type = Type::ADT(user_fqtn("Option"), vec![Type::Var(42)]);
        let scheme = build_constructor_scheme(&ctor, &adt_type, &[42]);

        assert_eq!(scheme.type_vars, vec![42]);
        assert_eq!(
            scheme.ty,
            Type::Fn(
                vec![Type::Var(42)],
                Box::new(Type::ADT(user_fqtn("Option"), vec![Type::Var(42)]))
            )
        );
    }

    // spec: 10-io §10.1 — is_internal_constructor returns true for internal ctors
    #[test]
    fn test_is_internal_constructor() {
        let tc = tf_io();
        let primitives_path = ModuleFullPath::from("primitives");
        let env = tc.env();
        // Bind carries `internal: true` on its `DefKind::Constructor`. Rooted
        // at its home module (primitives), the check resolves the Constructor
        // Def and reads the discriminator.
        assert!(
            env.is_internal_constructor_check_in_module(&primitives_path, "Bind"),
            "Bind must be reported internal"
        );
        // Non-internal IO constructors return false.
        assert!(!env.is_internal_constructor_check_in_module(&primitives_path, "Pure"));
        assert!(!env.is_internal_constructor_check_in_module(&primitives_path, "Effect"));
        // Unknown constructors return false.
        assert!(!env.is_internal_constructor_check_in_module(&primitives_path, "NoSuchCtor"));
    }

    // spec: 10-io §10.1 — internal-ctor check chain-follows Import entries.
    //
    // Regression for the Wave-4c enforcement defect: when `Bind` is reachable
    // from a module via a glob import (the realistic shape — `user`/`test`
    // imports `primitives`), the `internal` discriminator must still be read
    // through the Import entry. A direct probe returned the Import (not the
    // Constructor Def) and silently reported `false`, so `(Bind …)` resolved
    // and compiled in user code.
    #[test]
    fn test_is_internal_constructor_through_import() {
        use cranelisp_types::{ModuleEntry, Symbol, FQSymbol, Visibility};
        let tc = tf_io();
        let user_path = ModuleFullPath::from("user");
        // Seed user-module Imports of `Bind` and its parent `IO` type from
        // primitives — what a glob import of primitives materialises (both the
        // constructor name and the type name land as Import entries).
        {
            let mut user_tbl = tc.modules.get_mut(&user_path).unwrap();
            for name in ["Bind", "IO"] {
                user_tbl.insert(
                    Symbol::from(name),
                    ModuleEntry::Import {
                        source: FQSymbol {
                            module: ModuleFullPath::from("primitives"),
                            symbol: Symbol::from(name),
                        },
                        visibility: Visibility::Public,
                    },
                );
            }
        }
        let env = tc.env();
        assert!(
            env.is_internal_constructor_check_in_module(&user_path, "Bind"),
            "Bind imported into user must still be reported internal \
             (chain-follow the Import to the primitives Constructor Def)"
        );
    }

    // spec: 10-io §10.1 — exhaustiveness excludes internal constructors
    #[test]
    fn test_exhaustiveness_excludes_internal_constructors() {
        let tc = tf_io();
        let primitives_path = ModuleFullPath::from("primitives");
        // IO has Pure (tag=0), Effect (tag=1), Bind (tag=2, internal).
        // Exhaustiveness should only require Pure and Effect.
        let covered = vec![Symbol::from("Pure"), Symbol::from("Effect")];
        assert!(tc
            .check_exhaustiveness_in_module(
                &primitives_path,
                &TypeName::from("IO"),
                &covered,
                false,
                Span::SYNTHETIC,
            )
            .is_ok(),
            "matching Pure + Effect should be exhaustive (Bind is internal)"
        );

        // Missing Effect should fail.
        let covered = vec![Symbol::from("Pure")];
        let err = tc
            .check_exhaustiveness_in_module(
                &primitives_path,
                &TypeName::from("IO"),
                &covered,
                false,
                Span::SYNTHETIC,
            )
            .unwrap_err();
        assert!(err.message().contains("Effect"), "should report missing Effect, got: {}", err.message());
        // Should NOT mention Bind.
        assert!(!err.message().contains("Bind"), "should not mention internal Bind");
    }
}
