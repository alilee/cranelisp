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

use cranelisp_types::{
    AdtEntrySpec, Binding, CallableOrigin, ConstructorDef, CranelispError, Decl, DefnVariant,
    ErrorLocation, Expr, FQSymbol, FQTypeName, FieldInfo, Life, ModuleFullPath, Realization,
    Scheme, Span, Symbol, SynthSpec, TemplateBody, TemplateKind, Type, TypeDefInfo, TypeId,
    TypeName, TypeRecord, Visibility, member_key,
};

use crate::checker::{CheckState, TypeCheckEnv};

/// Local typecheck-internal intermediate: a constructor with its resolved field
/// types, used during `register_type_def` to build per-constructor `Def`
/// entries. Not part of the cranelisp-types surface — the canonical store is
/// the per-ctor `ModuleEntry::Def { kind: DefKind::Constructor, .. }` entry.
#[derive(Clone)]
pub(crate) struct CtorBuild {
    pub name: Symbol,
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
        let type_already_resolves = self
            .probe_module_entry_owned(&state.current_module, name.as_ref())
            .as_ref()
            .and_then(Binding::type_def_info)
            .is_some_and(|info| info.name == fqtn);
        if !type_already_resolves {
            self.current_symbol_table_mut(state)
                .install_binding(
                    Symbol::from(name.as_ref()),
                    Binding::new(
                        Decl::Type(TypeRecord::Defined {
                            info: TypeDefInfo {
                                name: fqtn.clone(),
                                type_params: type_params.to_vec(),
                                constructors: vec![],
                            },
                            docstring: None,
                        }),
                        visibility,
                    ),
                )
                .map_err(|error| CranelispError::TypeError {
                    message: error.to_string(),
                    location: ErrorLocation::from_span(span),
                })?;
        }

        // Build constructor infos with resolved field types.
        // If resolution fails, remove the pre-seeded placeholder so it
        // doesn't pollute known_types for subsequent definitions.
        let ctor_infos =
            match self.build_constructor_infos(state, name, constructors, &var_map, span) {
                Ok(infos) => infos,
                Err(e) => {
                    self.current_symbol_table_mut(state)
                        .remove_non_callable(&Symbol::from(name.as_ref()))
                        .map_err(crate::result::lifecycle_error)?;
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
        )?;

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
    ) -> Result<(), CranelispError> {
        let fqtn = FQTypeName::new(state.current_module.clone(), name.clone());
        let type_args: Vec<Type> = type_var_ids.iter().map(|&id| Type::Var(id)).collect();
        let adt_type = Type::ADT(fqtn.clone(), type_args);

        let is_product = ctor_infos.len() == 1 && ctor_infos[0].name.as_ref() == name.as_ref();

        // A product's type facet and constructor share one binding.  Retire the
        // provisional type-only declaration before the constructor settlement;
        // `build_adt_entries` carries the completed `TypeDefInfo` on the
        // constructor origin, preserving the dual facet without a raw overwrite.
        if is_product
            && self
                .probe_module_entry_owned(&state.current_module, name.as_ref())
                .as_ref()
                .is_some_and(|binding| binding.callable().is_none())
        {
            self.current_symbol_table_mut(state)
                .remove_non_callable(&Symbol::from(name.as_ref()))
                .map_err(crate::result::lifecycle_error)?;
        }

        // Sum/enum: pre-seed the type-name placeholder before minting ctor `Def`s
        // (the `register_type_def` path pre-seeds; direct callers may not have —
        // do it defensively so any staging read during insertion sees the type).
        // The real `TypeDef` (with the ctor-name list + docstring) is minted by
        // `build_adt_entries` below and overwrites this placeholder.
        if !is_product {
            self.current_symbol_table_mut(state)
                .install_binding(
                    Symbol::from(name.as_ref()),
                    Binding::new(
                        Decl::Type(TypeRecord::Defined {
                            info: TypeDefInfo {
                                name: fqtn.clone(),
                                type_params: type_params.to_vec(),
                                constructors: vec![],
                            },
                            docstring: None,
                        }),
                        visibility,
                    ),
                )
                .map_err(|error| CranelispError::TypeError {
                    message: error.to_string(),
                    location: ErrorLocation::unknown(),
                })?;
        }

        // **R-2 (S110, the bootstrap↔typecheck ADT-mirror cure; Principle 24).**
        // The ordered `(key, entry)` set an ADT registration produces is derived
        // ONCE by `cranelisp_types::build_adt_entries` — the single derivation
        // both this writer and `src/bootstrap.rs::register_synth_adt` call. This
        // caller stays thin: it builds the specs, settles each returned binding
        // or callable recipe, and exposes sum constructors under their bare
        // spelling. Product field-accessor synthesis is a typecheck-only
        // follow-on kept here (below).
        let specs: Vec<cranelisp_types::AdtCtorSpec> = ctor_infos
            .iter()
            .map(|c| {
                cranelisp_types::AdtCtorSpec::new(
                    c.name.clone(),
                    c.fields.clone(),
                    c.docstring.clone(),
                    c.internal,
                )
            })
            .collect();

        let entries = cranelisp_types::build_adt_entries::<C>(
            &fqtn,
            type_params,
            type_var_ids,
            docstring.as_deref(),
            &specs,
            visibility,
        );

        for (key, entry) in entries {
            match entry {
                AdtEntrySpec::Binding(binding) => {
                    self.current_symbol_table_mut(state)
                        .install_binding(key, binding)
                        .map_err(|error| CranelispError::TypeError {
                            message: error.to_string(),
                            location: ErrorLocation::unknown(),
                        })?;
                }
                AdtEntrySpec::Callable(spec) => {
                    let bare_ctor = matches!(
                        &spec.origin,
                        CallableOrigin::Ctor { type_name, .. }
                            if key.as_ref() != type_name.name.as_ref()
                    )
                    .then(|| {
                        Symbol::from(
                            key.as_ref()
                                .rsplit('.')
                                .next()
                                .expect("canonical member key has a terminal segment"),
                        )
                    });
                    let variant = spec.synth.variant.clone();
                    let mut table = self.current_symbol_table_mut(state);
                    let existing_life = table
                        .get(key.as_ref())
                        .and_then(Binding::callable)
                        .map(|callable| &callable.arm.life);
                    let keep_existing_template =
                        matches!(existing_life, Some(Life::Template { .. }));
                    if matches!(
                        existing_life,
                        Some(Life::Concrete { .. } | Life::Broken { .. })
                    ) {
                        table
                            .retire_abi_changing(&key)
                            .map_err(crate::result::lifecycle_error)?;
                    }
                    let result = if keep_existing_template {
                        Ok(())
                    } else if spec.scheme.ty.is_concrete() {
                        let view = cranelisp_types::MonoDefnVariant {
                            name: key.clone(),
                            params: spec.param_names.clone(),
                            body: cranelisp_types::MonoExpr::synthetic_local_from_expr(
                                &variant.body,
                                &HashMap::new(),
                            ),
                            span: variant.span,
                            mode_summary: None,
                        };
                        table
                            .install_concrete(
                                key.clone(),
                                spec.scheme,
                                spec.param_names,
                                spec.docstring,
                                0,
                                spec.origin,
                                Realization::Body { view, code: None },
                                Some(variant),
                                Vec::new(),
                                spec.visibility,
                            )
                            .map(|_| ())
                    } else {
                        table.install_template(
                            key.clone(),
                            spec.scheme,
                            spec.param_names,
                            spec.docstring,
                            0,
                            spec.origin,
                            TemplateBody::Synth(spec.synth),
                            TemplateKind::Parametric,
                            Vec::new(),
                            spec.visibility,
                        )
                    };
                    result.map_err(|error| CranelispError::TypeError {
                        message: error.to_string(),
                        location: ErrorLocation::unknown(),
                    })?;
                    drop(table);
                    if let Some(bare_ctor) = bare_ctor {
                        self.current_symbol_table_mut(state)
                            .expose_candidate(
                                bare_ctor,
                                FQSymbol {
                                    module: fqtn.module.clone(),
                                    symbol: key,
                                },
                                visibility,
                            )
                            .map_err(|error| CranelispError::TypeError {
                                message: error.to_string(),
                                location: ErrorLocation::unknown(),
                            })?;
                    }
                }
            }
        }

        // **Field accessors (S121, spec §5.2.6) — typecheck-only follow-on.**
        // Generate total accessors only for the one same-name constructor of a
        // product type. Sum-constructor payload labels are positional metadata;
        // extracting them requires `match`, so no partial runtime-checking
        // accessor is minted for a sum arm.
        if is_product {
            self.synthesise_field_accessors(
                state,
                &fqtn,
                &ctor_infos[0],
                &adt_type,
                type_var_ids,
                visibility,
            )?;
        }

        Ok(())
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
        state: &mut CheckState,
        type_name: &TypeName,
        constructors: &[ConstructorDef],
        var_map: &HashMap<Symbol, TypeId>,
        span: Span,
    ) -> Result<Vec<CtorBuild>, CranelispError> {
        constructors
            .iter()
            .map(|ctor| self.build_single_ctor_info(state, type_name, ctor, var_map, span))
            .collect()
    }

    /// Build a single CtorBuild with resolved field types. The ctor's tag is
    /// assigned positionally by `cranelisp_types::build_adt_entries` (S110 R-2);
    /// `CtorBuild` carries no tag.
    fn build_single_ctor_info(
        &self,
        state: &mut CheckState,
        _type_name: &TypeName,
        ctor: &ConstructorDef,
        var_map: &HashMap<Symbol, TypeId>,
        span: Span,
    ) -> Result<CtorBuild, CranelispError> {
        let fields: Vec<FieldInfo> = ctor
            .fields
            .iter()
            .map(|field| {
                let ty = self
                    .resolve_type_expr_in_module(
                        &field.type_expr,
                        var_map,
                        &state.current_module,
                        span,
                    )
                    .map_err(|failure| failure.into_form_error(state))?;
                Ok(FieldInfo {
                    name: field.name.clone(),
                    ty,
                })
            })
            .collect::<Result<Vec<_>, CranelispError>>()?;

        Ok(CtorBuild {
            name: ctor.name.clone(),
            fields,
            docstring: ctor.docstring.clone(),
            internal: false,
        })
    }

    /// Synthesise free field-accessor fns for a product type's ctor.
    ///
    /// Each named field `f` of `(deftype Box [:Int v ..])` yields a free fn
    /// `v :: (Fn [Box] Int)` with body `(match self [(Box v ..) v])`. Born
    /// concrete (GOT slot at synthesis), registered under the field name in the
    /// type's own module.
    ///
    /// The canonical binding is stored at `Type.field`; the bare field spelling
    /// exposes that terminal as one candidate. Other candidates and a local
    /// declaration may coexist under the bare spelling without overwriting the
    /// canonical accessor.
    fn synthesise_field_accessors(
        &self,
        state: &mut CheckState,
        fqtn: &FQTypeName,
        ctor: &CtorBuild,
        adt_type: &Type,
        type_var_ids: &[TypeId],
        visibility: Visibility,
    ) -> Result<(), CranelispError> {
        let all_field_names: Vec<Symbol> = ctor.fields.iter().map(|f| f.name.clone()).collect();
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
            )?;
        }
        Ok(())
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
    ) -> Result<(), CranelispError> {
        use cranelisp_types::{MatchArm, Pattern, SymbolRef};

        let accessor_name = field.name.clone();
        let body_span = Span::SYNTHETIC;

        // Accessor scheme `(Fn [ProductType] FieldType)`, quantified over the
        // type's params (so `(Fn [(Box a)] a)` for a polymorphic product).
        let accessor_ty = Type::Fn(vec![adt_type.clone()], Box::new(field.ty.clone()));
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

        // The canonical accessor key `Type.field` (`Box.v`; spec §8.5.2).
        let qualified_key = member_key(&fqtn.name, accessor_name.as_ref());

        // The canonical accessor binding is minted unconditionally — whatever
        // else shares the bare spelling — as an always-Public callable with
        // `CallableOrigin::Accessor`, which `committed_accessor_kind`
        // recognises (`fixme-0365-field-accessor-dotted.md` §1.6.1). A concrete
        // type installs a concrete callable carrying its codegen view; a generic
        // type installs a template carrying its synthesis recipe.
        //
        // The synthetic body `(match self [(Ctor …) field])` has no inferred
        // types, so strict `from_expr` cannot build its view. Build it here with
        // the pattern's constructor identity supplied directly: the synthetic
        // span is outside the span-keyed sidecar, but the identity is known — the
        // product constructor's storage key, which is the bare type name
        // (`ctor.name == fqtn.name`). The backend reads the constructor from this
        // identity and has no fallback for a pattern without one.
        let docstring = Some(format!(
            "Canonical field accessor `{}.{}` of type `{}`.",
            fqtn.name, accessor_name, fqtn.name
        ));
        let origin = CallableOrigin::Accessor {
            type_name: fqtn.clone(),
            field: accessor_name.clone(),
        };
        let mut table = self.current_symbol_table_mut(state);
        let existing_life = table
            .get(qualified_key.as_ref())
            .and_then(Binding::callable)
            .map(|callable| &callable.arm.life);
        let keep_existing_template = matches!(existing_life, Some(Life::Template { .. }));
        let replace_existing_synth = matches!(
            existing_life,
            Some(Life::Concrete { .. } | Life::Broken { .. })
        );
        let result = if keep_existing_template {
            Ok(())
        } else if scheme.ty.is_concrete() {
            let mut accessor_pattern_ctors = HashMap::new();
            accessor_pattern_ctors.insert(
                body_span,
                FQSymbol {
                    module: fqtn.module.clone(),
                    symbol: ctor.name.clone(),
                },
            );
            let accessor_view = cranelisp_types::MonoDefnVariant {
                name: qualified_key.clone(),
                params: vec![Symbol::from("self$accessor")],
                body: cranelisp_types::MonoExpr::synthetic_local_from_expr(
                    &ast.body,
                    &accessor_pattern_ctors,
                ),
                span: body_span,
                mode_summary: None,
            };
            if replace_existing_synth {
                table
                    .replace_unpublished_synthesized_concrete(
                        qualified_key.clone(),
                        scheme,
                        vec![Symbol::from("self$accessor")],
                        docstring,
                        origin,
                        SynthSpec::new(ast),
                        accessor_view,
                        Visibility::Public,
                    )
                    .map(|_| ())
            } else {
                table
                    .install_concrete(
                        qualified_key.clone(),
                        scheme,
                        vec![Symbol::from("self$accessor")],
                        docstring,
                        0,
                        origin,
                        Realization::Body {
                            view: accessor_view,
                            code: None,
                        },
                        Some(ast),
                        Vec::new(),
                        Visibility::Public,
                    )
                    .map(|_| ())
            }
        } else if replace_existing_synth {
            table.replace_unpublished_synthesized_template(
                qualified_key.clone(),
                scheme,
                vec![Symbol::from("self$accessor")],
                docstring,
                origin,
                SynthSpec::new(ast),
                Visibility::Public,
            )
        } else {
            table.install_template(
                qualified_key.clone(),
                scheme,
                vec![Symbol::from("self$accessor")],
                docstring,
                0,
                origin,
                TemplateBody::Synth(SynthSpec::new(ast)),
                TemplateKind::Parametric,
                Vec::new(),
                Visibility::Public,
            )
        };
        result.map_err(|error| CranelispError::TypeError {
            message: error.to_string(),
            location: ErrorLocation::unknown(),
        })?;
        drop(table);

        // Track the field's owning type for the bare-candidate ambiguity diagnostic.
        let owners = self.reconstruct_accessor_alternatives(state, accessor_name.as_ref());
        state
            .accessor_owning_types
            .insert(accessor_name.clone(), owners);

        self.current_symbol_table_mut(state)
            .expose_candidate(
                accessor_name,
                FQSymbol {
                    module: fqtn.module.clone(),
                    symbol: qualified_key,
                },
                visibility,
            )
            .map_err(|error| CranelispError::TypeError {
                message: error.to_string(),
                location: ErrorLocation::unknown(),
            })?;

        Ok(())
    }

    /// Enumerate the bare **field-accessor names** owned by `fqtn` (`Box.v` →
    /// `v`), for the impl-time collision gate
    /// `traits/impl_check.rs::check_impl_method_accessor_collisions`, its only
    /// consumer.
    ///
    /// Both are superseded by spec §7.3.1 and are removed together once
    /// `ACT-0983` intake completes
    /// (`design/typecheck/fixme-0365-field-accessor-dotted.md` §2.1, §2.3).
    ///
    /// It walks the owning module's union view (staging then live) through
    /// `for_each_in_module`, keeping entries `committed_accessor_kind`
    /// classifies as accessors of `fqtn`, so an accessor from an earlier REPL
    /// cluster counts.
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

    /// Reconstruct the canonical accessor alternatives (`Box.v`, `Cup.v`) for an
    /// ambiguous bare field spelling from the durable symbol table.
    ///
    /// Same-cluster (`--run`) the alternatives are carried on the per-`CheckState`
    /// `accessor_owning_types` map, populated as each accessor is synthesised in
    /// the SAME `check_forms` call that later sees the bare use. The REPL drives
    /// each form as its own cluster with a fresh `CheckState`, so by the time
    /// `(v …)` is checked the per-cluster owner map is empty. The candidate
    /// references survive in the table. This helper re-derives display owners:
    /// it walks the current module's union view for every canonical
    /// `Type.member` binding whose terminal segment equals `name` and reads its
    /// owner through `committed_member_owner`. It lists accessor and
    /// constructor owners only, never a non-member candidate sharing the
    /// spelling (`dotted-ctor-registration.md` §1.3). Returns the owners in first-defined order
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

/// Classification of a COMMITTED symbol-table entry as a synthesised field
/// accessor. Accessor identity is re-derived structurally from the durable
/// entry so same-cluster and cross-cluster resolution use one source.
pub(crate) enum CommittedAccessor {
    /// A synthesised accessor, concrete or template; carries its owning
    /// product type (read from the accessor's `(Fn [ADT] _)` scheme).
    Concrete(FQTypeName),
    /// Not a synthesised accessor (a user `defn`, a ctor, an import, …).
    NotAccessor,
}

/// Recognise a committed entry as a synthesised field accessor and read its
/// owning product type.
///
/// `synthesise_one_accessor` registers each accessor with
/// `CallableOrigin::Accessor` and the scheme `(Fn [ProductType] FieldType)`.
/// The origin marks the accessor; the scheme's sole parameter names its owning
/// type (`fixme-0365-field-accessor-dotted.md` §1.6.1).
pub(crate) fn committed_accessor_kind<C: cranelisp_types::CodeStore>(
    entry: &Binding<C>,
) -> CommittedAccessor {
    match &entry.declaration {
        Decl::Callable(callable)
            if matches!(callable.origin, CallableOrigin::Accessor { .. })
                && matches!(
                    callable.arm.life,
                    Life::Concrete { .. } | Life::Template { .. }
                ) =>
        {
            match &callable.arm.scheme.ty {
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

/// The owning type of a canonical dotted member binding — either a synthesised
/// field accessor (`Box.v`, owner read from its `(Fn [ADT] _)` scheme) or a sum
/// constructor (`Maybe.Some`, owner read from `CallableOrigin::Ctor.type_name`)
/// (`dotted-ctor-registration.md` §1.2, §3.1). It is the one recogniser the
/// dotted resolver (`resolve_dotted_member_entry`) and
/// `reconstruct_accessor_alternatives` use for both member kinds. Returns
/// `None` for a non-member binding.
pub(crate) fn committed_member_owner<C: cranelisp_types::CodeStore>(
    entry: &Binding<C>,
) -> Option<FQTypeName> {
    // Field accessor?
    if let CommittedAccessor::Concrete(owner) = committed_accessor_kind(entry) {
        return Some(owner);
    }
    // Sum constructor? (The product ctor also carries a `type_name` but is keyed
    // at the type name, never probed as a canonical dotted member — so reading
    // its `type_name` here is harmless; the resolver's degenerate-key miss and
    // the registration product gate keep products out of this path.)
    if let Some(callable) = entry.callable()
        && let CallableOrigin::Ctor { type_name, .. } = &callable.origin
    {
        return Some(type_name.clone());
    }
    None
}

/// Build a type scheme for a constructor.
///
/// Nullary constructors: `forall [vars]. ADT_Type`
/// Data constructors:    `forall [vars]. (Fn [field_types] ADT_Type)`
///
/// If there are no type parameters (vars is empty), the scheme is monomorphic.
///
/// **S110 R-2:** the production ctor-scheme derivation moved into
/// `cranelisp_types::build_adt_entries` (the single ADT-entry builder). This
/// free function is retained only for the `adt/tests.rs` scheme-shape unit
/// tests, which assert the scheme grammar independently of the builder.
#[cfg(test)]
fn build_constructor_scheme(ctor: &CtorBuild, adt_type: &Type, type_var_ids: &[TypeId]) -> Scheme {
    let type_vars: Vec<TypeId> = type_var_ids.to_vec();

    let ty = if ctor.fields.is_empty() {
        // Nullary constructor: just the ADT type
        adt_type.clone()
    } else {
        // Data constructor: Fn([field types...], ADT type)
        let param_types: Vec<Type> = ctor.fields.iter().map(|f| f.ty.clone()).collect();
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

        let type_def = self
            .lookup_type_def_in_module(&fq_type_name.module, &fq_type_name.name)
            .ok_or_else(|| CranelispError::TypeError {
                message: format!("unknown type in match: {}", fq_type_name.name),
                location: ErrorLocation::from_span(span),
            })?;

        // Exclude internal constructors from exhaustiveness — user code cannot
        // and need not cover them (design/typecheck/io-types.md §1). Per-ctor
        // `internal` lives on `DefKind::Constructor.internal`; resolve each
        // name to its Def in the type's defining module.
        let ctor_internal_flags: Vec<(Symbol, bool)> = type_def
            .constructors
            .iter()
            .map(|ctor_sym| {
                // `dotted-ctor-registration.md` §4.2. A sum ctor's binding lives
                // under the canonical `member_key(Type, Ctor)`; its bare spelling
                // is only a candidate exposure. A bare-only probe would miss it,
                // default `internal: false`, and require user matches on `IO` to
                // cover the internal `Bind`. Probe the
                // canonical key first, then the bare name, which serves the
                // product dual-facet at the type-name key alone.
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
                    .and_then(|e| {
                        e.callable().and_then(|callable| match &callable.origin {
                            CallableOrigin::Ctor { internal, .. } => Some(*internal),
                            _ => None,
                        })
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
                after_slash
                    .rsplit('.')
                    .next()
                    .unwrap_or(after_slash)
                    .to_string()
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
