//! Shared immutable compilation context (`CompileContext`) and the
//! constructor/type-def lookups that read from it, plus the constructor
//! metadata DTOs (`CtorField`, `CtorMeta`) those lookups produce.
//!
//! `CompileContext` is the one `pub`-to-boundary item under `compiler::`; it is
//! re-exported `pub` from the `compiler` hub so its public path is preserved.

use std::collections::HashMap;

use cranelift_module::FuncId;

use dashmap::DashMap;

use cranelisp_types::{
    Binding, CallableOrigin, ConcreteType, CranelispError, CtorFieldsAtError, Decl, ErrorLocation,
    FQSymbol, FQTypeName, Life, ModuleFullPath, Span, Symbol, SymbolTable, Type, TypeDefInfo,
};

/// A single field of a constructor, as reconstructed for backend codegen.
///
/// The field type is recovered from the constructor `Def`'s `scheme` (a data
/// constructor's scheme is `Type::Fn(field_types, result_adt)`; a nullary
/// constructor's scheme is just the result ADT and carries no fields).
/// Codegen consumes field types (heap classification, drop-glue field decs,
/// type-substitution); field names are not needed at codegen and are not
/// carried (minimum mechanism — Principle 6).
#[derive(Debug, Clone)]
pub(crate) struct CtorField {
    pub ty: Type,
}

/// Backend-internal constructor metadata, reconstructed from a constructor's
/// `ModuleEntry::Def { kind: DefKind::Constructor { .. }, .. }` entry.
///
/// Replaces the retired `cranelisp_types::ConstructorInfo` struct (S70
/// ctor-as-Def collapse). The metadata (`tag`, `field_count`) is read from
/// `DefKind::Constructor`; field names from `param_names`; field types
/// reconstructed from the `Def.scheme`. See `design/backend/compile-to-module.md`
/// §2.6 and `DefKind::Constructor` rustdoc in `cranelisp-types::module`.
///
/// `fields` has exactly one entry per declared field: a constructor whose
/// scheme supplies fewer field types than it declares fields is refused when
/// its metadata is read ([`ShortDeclaration`]), so no reader can take it for a
/// nullary or smaller-arity constructor.
#[derive(Debug, Clone)]
pub(crate) struct CtorMeta {
    pub tag: usize,
    pub fields: Vec<CtorField>,
    /// The declared parameters of the type this constructor builds, in
    /// declaration order: the arguments of its scheme's result ADT. A field
    /// takes the argument of the parameter it mentions (ACT-1062).
    pub params: Vec<Type>,
}

/// A constructor whose scheme supplies fewer field types than it declares
/// fields. Its metadata is never built; every read of it is a keying error.
#[derive(Debug, Clone)]
pub(crate) struct ShortDeclaration {
    pub type_name: FQTypeName,
    declared: usize,
    supplied: usize,
}

impl ShortDeclaration {
    /// The keying error for a read of `ctor`, located at `at`.
    pub(crate) fn refusal(&self, ctor: &dyn std::fmt::Display, at: Span) -> CranelispError {
        keying_drift_at(
            at,
            format!(
                "constructor '{ctor}' declares {} field(s) but its scheme supplies types for {}",
                self.declared, self.supplied
            ),
        )
    }
}

/// What a constructor reference's VALUE carries
/// (`design/backend/non-concrete-release-contract.md` §6.2.1).
///
/// "Not a constructor" is not a variant here — it is the probe returning
/// `None`, i.e. declining to answer. Absence is cardinality, so a
/// non-constructor global can never be mistaken for a constructor verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CtorValueShape {
    /// Zero fields: the value IS the tag, lowered to a bare `iconst` below
    /// `NULLARY_TAG_THRESHOLD`, so it carries no heap reference at all.
    BareTag,
    /// One or more fields: using the constructor mints or moves a payload box.
    Payload,
}

impl CtorMeta {
    /// The ONE read of a constructor's field list (Principle 24 — one
    /// determinant, one read). The bare-tag lowering
    /// (`literals::nullary_constructor_tag`) answers from here; a second
    /// `fields.is_empty()` elsewhere would be a channel on which a lowering
    /// could disagree with what a constructor carries (FIXME 0917).
    pub(crate) fn value_shape(&self) -> CtorValueShape {
        if self.fields.is_empty() {
            CtorValueShape::BareTag
        } else {
            CtorValueShape::Payload
        }
    }
}

/// Shared immutable context for compilation, bundling references that
/// are threaded through from `compile_body` to all expression compilers.
///
/// All fields are references or `Copy`-ish types, so the struct is `Clone`.
/// This avoids verbose field-by-field copies when constructing inner compilers
/// (e.g., for lambda bodies).
// Sprint 58 Wave 3b (Decision 35 / 32): `CompileContext` is generic over
// `C: CodeStore` and `L: LinkerStore` so it can hold a borrow of the
// integration layer's `SymbolTable<Code, ()>` (or any other instantiation
// — the typecheck-product `<(), ()>` works too via the defaults). Backend
// reads only `code`-independent fields (`ast`, `scheme`, `got_slot`,
// `kind`, `param_names`), so the `C`/`L` parameters propagate as opaque
// type variables that never get named — consistent with Decision 35's
// "backend stays generic-blind" framing.
//
// Manual `Clone` impl (instead of `#[derive(Clone)]`) avoids the auto-
// derived `C: Clone, L: Clone` bounds that the macro would impose. Every
// field is either `Copy`, an `&` reference (which is `Copy`), or already
// owned-cloneable (`ModuleFullPath`); none of them depend on `C` or `L`
// being `Clone`. This keeps the trait bound surface minimal.
pub struct CompileContext<'a, C = (), L = ()>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Function IDs for direct calls (Batch mode).
    pub func_ids: &'a HashMap<Symbol, FuncId>,
    /// Function parameter counts, for generating closure wrappers.
    pub func_arities: &'a HashMap<Symbol, usize>,
    /// Per-module symbol tables (shared, authoritative source for type defs,
    /// constructors, GOT slots, and post-G7 GOT base pointers). The backend
    /// reads GOT slots/bases directly from this map — no env abstraction.
    pub symbol_tables: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,
    /// Current module being compiled (for constructor/type lookups).
    pub current_module: ModuleFullPath,

    // --- Ring 1 intrinsic FuncIds ---
    /// FuncId for runtime/alloc. None in Ring 0 (no heap).
    pub alloc_func_id: Option<FuncId>,
    /// FuncId for runtime/dealloc. Non-optional: Decision 24 retires the
    /// Option<...> conditional. Codegen always assumes dealloc is declared
    /// — all compile paths since Ring 1 require heap + RC support.
    pub dealloc_func_id: FuncId,
    /// FuncId for runtime/alloc_string. None in Ring 0 (no strings).
    pub alloc_string_func_id: Option<FuncId>,
    /// The declared panic funnel. A panic site with `None` is a located codegen error (backend.md §7).
    pub panic: Option<crate::raise::PanicHandle>,
    /// FuncId for runtime/vec_new. None in Ring 0 (no Vecs).
    pub vec_new_func_id: Option<FuncId>,
    /// FuncId for runtime/vec_drop. None in Ring 0 (no Vecs).
    pub vec_drop_func_id: Option<FuncId>,
}

// Manual Clone impl so neither `C: Clone` nor `L: Clone` is required —
// every field is either `Copy` or `&`-referenced or `ModuleFullPath`
// (which has its own `Clone` independent of `C`/`L`). See the type-decl
// comment above for rationale.
impl<'a, C, L> Clone for CompileContext<'a, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    fn clone(&self) -> Self {
        CompileContext {
            func_ids: self.func_ids,
            func_arities: self.func_arities,
            symbol_tables: self.symbol_tables,
            current_module: self.current_module.clone(),
            alloc_func_id: self.alloc_func_id,
            dealloc_func_id: self.dealloc_func_id,
            alloc_string_func_id: self.alloc_string_func_id,
            panic: self.panic,
            vec_new_func_id: self.vec_new_func_id,
            vec_drop_func_id: self.vec_drop_func_id,
        }
    }
}

impl<'a, C, L> CompileContext<'a, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Resolve a constructor by its STORAGE `FQSymbol` (the key its `Def` was
    /// stored under, carried on `MonoMatchArm.resolved_ctor` from typecheck's
    /// `pattern_ctors` sidecar) — a DIRECT keyed read, NO name resolution, NO
    /// import-chain walk, NO global fallback, NO DashMap-iteration order (S109
    /// W1.2, `dotted-ctor-canonical-keys.md` §10.3). This is the ONLY resolver
    /// pattern position uses; the deterministic, run-to-run-stable answer to
    /// "which ctor did typecheck pick" that `lookup_constructor`'s context-free
    /// re-resolution could not give for a scrutinee-directed same-named ctor.
    ///
    /// `Ok(None)` is "not a constructor"; a short declaration is an error, never
    /// a constructor with fewer fields.
    pub(crate) fn ctor_meta_at(
        &self,
        fq: &FQSymbol,
    ) -> Result<Option<(FQTypeName, CtorMeta)>, ShortDeclaration> {
        let Some(table) = self.symbol_tables.get(&fq.module) else {
            return Ok(None);
        };
        table
            .get(fq.symbol.as_ref())
            .and_then(Self::extract_constructor)
            .transpose()
    }

    /// [`Self::ctor_meta_at`] for a pattern constructor, which must be one: a
    /// miss and a short declaration are keying errors located at `reference`.
    /// The short refusal is recorded as a field read, so the census sees it.
    pub(crate) fn pattern_ctor_meta(
        &self,
        resolved_ctor: &FQSymbol,
        scrut_type: Option<&Type>,
        reference: Span,
        census: &super::census::Frame,
    ) -> Result<(FQTypeName, CtorMeta), CranelispError> {
        match self.ctor_meta_at(resolved_ctor) {
            Ok(Some(found)) => Ok(found),
            Ok(None) => Err(keying_drift_at(
                reference,
                format!("pattern constructor '{resolved_ctor}' has no constructor Def"),
            )),
            Err(short) => {
                self.record_field_read(
                    census,
                    &short.type_name,
                    scrut_type,
                    super::census::Declaration::Short,
                );
                Err(short.refusal(resolved_ctor, reference))
            }
        }
    }

    fn record_field_read(
        &self,
        census: &super::census::Frame,
        type_name: &FQTypeName,
        scrut_type: Option<&Type>,
        declaration: super::census::Declaration,
    ) {
        let type_params = self
            .lookup_type_def(type_name)
            .map_or(0, |type_def| type_def.type_params.len());
        super::census::record(census, || super::census::Record::Field {
            class: super::census::FieldClass::of(type_params, scrut_type),
            declaration,
        });
    }

    /// The ONE keyed fetch (S110 W1, `backend-keyed-consumer.md` §1.3) — the
    /// `ctor_meta_at` generalisation. A DIRECT two-level map read
    /// (`symbol_tables.get(&fq.module)` → `table.get(fq.symbol)`), NO
    /// import-chain walk, NO alias substitution, NO global fallback, NO
    /// DashMap-iteration order. The fetched entry is cloned out (the guard is
    /// released immediately, so no shard lock is held across codegen emission);
    /// callers discriminate on its `DefKind` — got-slot dispatch via
    /// `callable_got_slot()`, platform/poll via `DefKind::PlatformEffect`,
    /// extern via `DefKind::PrimitiveExtern`, ctor via `DefKind::Constructor`,
    /// arity via `param_names`.
    ///
    /// Carrier-miss (a `None` `resolved_target` on a table-reference kind) or
    /// entry-miss (`Some(fq)` that fetches nothing here) is a hard
    /// `CodegenError` at the call site (Principle 18; Rev-2 no-soft-fallback) —
    /// this reader itself just reports `None`, and the caller names the
    /// reference + the missing carrier in the error.
    pub(crate) fn entry_at(&self, fq: &FQSymbol) -> Option<(ModuleFullPath, Binding<C>)> {
        let table = self.symbol_tables.get(&fq.module)?;
        let entry = table.get(fq.symbol.as_ref())?;
        Some((fq.module.clone(), entry.clone()))
    }

    /// Reject an expansion-only macro clause carried into ordinary expression
    /// codegen. The caller has already selected `fq`; this is a checked keyed
    /// read of that exact storage identity, never another resolution pass.
    ///
    /// Missing entries are left to the existing call/value miss diagnostics.
    /// Macro expansion invokes clauses through int's dedicated ABI path and
    /// never enters this backend expression-codegen seam.
    pub(crate) fn ensure_language_callable_target(
        &self,
        fq: &FQSymbol,
        span: Span,
    ) -> Result<(), CranelispError> {
        if self
            .entry_at(fq)
            .is_some_and(|(_, entry)| matches!(entry.declaration, Decl::Macro(_)))
        {
            return Err(CranelispError::CodegenError {
                message: format!(
                    "resolved target '{fq}' is an expansion-only macro clause and cannot be used as an ordinary language value or call"
                ),
                location: ErrorLocation::from_span(span),
            });
        }
        Ok(())
    }

    // === S110 W2 value-seam keyed reads (`backend-keyed-consumer.md` §1.3/§4;
    // §3 S10–S18). Each is a kind-arm projection off the ONE `entry_at` fetch,
    // replacing the value-site reach of a `resolution.rs` resolver. ===

    /// S12 (fn-as-value gate) / kind arm: `true` iff `fq` fetches a dispatchable
    /// call target ([`ModuleEntry::is_callable_target`] — slot-dispatched OR
    /// inline-dispatched). Replaces the `resolve_is_callable_target` value-site
    /// reach (`is_known_function`).
    pub(crate) fn is_callable_target_at(&self, fq: &FQSymbol) -> bool {
        self.entry_at(fq)
            .is_some_and(|(_, e)| e.is_callable_target())
    }

    /// S14 (closure-wrapper arity) kind arm: the callee's param count read off
    /// the fetched `Def` entry. Replaces the `resolve_func_arity` value-site
    /// reach.
    pub(crate) fn arity_at(&self, fq: &FQSymbol) -> Option<usize> {
        self.entry_at(fq).and_then(|(_, e)| {
            e.callable()
                .map(|callable| callable.arm.param_names.len())
                .or_else(|| e.trait_method().map(|method| method.param_names.len()))
        })
    }

    /// Whether the resolved entry is a slotless inline primitive. The Vec
    /// family includes `vec-get`, `vec-set`, `vec-push`, and `vec-len`.
    pub(crate) fn is_inline_primitive_at(&self, fq: &FQSymbol) -> bool {
        self.entry_at(fq).is_some_and(|(_, e)| {
            matches!(
                e.callable(),
                Some(callable)
                    if matches!(callable.origin, CallableOrigin::RustPrimitive)
                        && matches!(callable.arm.life, Life::Inline { .. })
            )
        })
    }

    /// S10 (fn-as-value wrapper GOT entry) kind arm: `(defining_module,
    /// got_slot)` read off the fetched entry via `callable_got_slot()`. Replaces
    /// the `resolve_got_entry`/`resolve_got_target` value-site reach; `None` when
    /// the carrier fetches nothing or the entry carries no slot (the caller
    /// hard-errors — Rev-2, no name-resolver fallback).
    pub(crate) fn got_entry_at(&self, fq: &FQSymbol) -> Option<(ModuleFullPath, usize)> {
        self.entry_at(fq)
            .and_then(|(home, e)| e.callable_got_slot().map(|slot| (home, slot)))
    }

    /// The 0585 loud backstop discriminator (`backend-keyed-consumer.md` §7 leg
    /// 2): `true` iff `fq` fetches a **slot-less generic template** — a `UserFn`
    /// in the `Polymorphic` or `Constrained` state, which carries no mono
    /// instance. A value-position `Var` resolving to such an entry reached
    /// codegen without a mint; the caller raises the precise §7 error instead of
    /// the misleading `undefined variable` leak.
    pub(crate) fn is_slotless_template_at(&self, fq: &FQSymbol) -> bool {
        self.entry_at(fq).is_some_and(|(_, e)| {
            matches!(
                e.callable(),
                Some(callable) if matches!(callable.arm.life, Life::Template { .. })
            )
        })
    }

    /// Extract constructor metadata from a module entry.
    ///
    /// Post-S70: constructors are uniformly `ModuleEntry::Def { kind:
    /// DefKind::Constructor { type_name, tag, field_count, .. }, .. }`; field
    /// types are recovered from the `scheme` (`Type::Fn(field_types, _)` for
    /// data constructors; nullary constructors carry no `Fn`).
    ///
    /// **Product types** (single constructor whose name equals the type name,
    /// e.g. `(deftype Point [:Int x :Int y])`) are NO LONGER special — S79
    /// Option 3a makes the product ctor a got-slotted `Def` exactly like a sum
    /// ctor (with a `DefKind::Constructor { type_def: Some(..) }` type facet);
    /// the prior `ModuleEntry::TypeDef.constructor_scheme` smuggling field is
    /// retired. The product ctor enters this routine through the one `Def` arm
    /// below, reading its field types from the `Def`'s own `scheme`.
    ///
    /// `None` is "not a constructor"; `Some(Err)` is a short declaration.
    fn extract_constructor<C2: cranelisp_types::CodeStore>(
        entry: &Binding<C2>,
    ) -> Option<Result<(FQTypeName, CtorMeta), ShortDeclaration>> {
        match &entry.declaration {
            Decl::Callable(callable) => {
                let CallableOrigin::Ctor {
                    type_name,
                    tag,
                    field_count,
                    ..
                } = &callable.origin
                else {
                    return None;
                };
                let field_types: &[Type] = match &callable.arm.scheme.ty {
                    Type::Fn(params, _) => params.as_slice(),
                    _ => &[],
                };
                if field_types.len() < *field_count {
                    return Some(Err(ShortDeclaration {
                        type_name: type_name.clone(),
                        declared: *field_count,
                        supplied: field_types.len(),
                    }));
                }
                let fields: Vec<CtorField> = field_types
                    .iter()
                    .take(*field_count)
                    .map(|ty| CtorField { ty: ty.clone() })
                    .collect();
                let params = crate::schema::declared_params(&callable.arm.scheme.ty).to_vec();
                Some(Ok((
                    type_name.clone(),
                    CtorMeta {
                        tag: *tag,
                        fields,
                        params,
                    },
                )))
            }
            _ => None,
        }
    }

    /// Materialise `CtorMeta` for every constructor named in a `TypeDefInfo`.
    ///
    /// `TypeDefInfo.constructors` is `Vec<Symbol>` (names only) post-S70; each
    /// name resolves to its own `DefKind::Constructor` Def via the type's
    /// owning module. Returns the per-constructor metadata in declaration
    /// order. Used by heap classification, drop-glue emission, and field-type
    /// resolution — all of which previously walked `Vec<ConstructorInfo>`.
    ///
    /// A type whose owning table or one of whose constructors cannot be read
    /// is keying drift, and is an error in every profile: a dropped
    /// constructor would surface only as a wrong heap classification or drop
    /// glue (ACT-0964 item 1).
    pub(crate) fn constructor_metas(
        &self,
        type_def: &TypeDefInfo,
    ) -> Result<Vec<CtorMeta>, CranelispError> {
        let table = self
            .symbol_tables
            .get(&type_def.name.module)
            .ok_or_else(|| {
                keying_drift(format!(
                    "type '{}' has no symbol table for its module",
                    type_def.name
                ))
            })?;
        type_def
            .constructors
            .iter()
            .map(|ctor_name| {
                // Probe the canonical `member_key(Type, Ctor)` key first (S109 W1
                // — a sum ctor's real `Def` lives under `Result.Err`, the bare
                // name being an `Import` alias that `extract_constructor` skips),
                // bare fallback for the product dual-facet.
                let canonical =
                    cranelisp_types::member_key(&type_def.name.name, ctor_name.as_ref());
                match table
                    .get(canonical.as_ref())
                    .or_else(|| table.get(ctor_name.as_ref()))
                    .and_then(Self::extract_constructor)
                {
                    Some(Ok((_, meta))) => Ok(meta),
                    Some(Err(short)) => Err(short.refusal(&ctor_name, Span::SYNTHETIC)),
                    None => Err(keying_drift(format!(
                        "constructor '{ctor_name}' of '{}' has no resolvable Def",
                        type_def.name
                    ))),
                }
            })
            .collect()
    }

    /// The field types of the pattern constructor stored at `resolved_ctor`, at
    /// the scrutinee's instantiation: the one backend read of field types that
    /// feeds classification and release. It delegates to
    /// [`cranelisp_types::ctor_field_types_at`], which pairs each argument with
    /// the declared parameter in its position, so a field takes the argument of
    /// the parameter it mentions (ACT-1062).
    ///
    /// The arguments are the scrutinee's when it is an ADT, and none otherwise.
    /// A residual instantiation is refused. A missed key, a parametric
    /// constructor reached without its arguments, an argument that disagrees
    /// with the declaration and a short declaration are keying errors. Every
    /// error is located at `reference`.
    pub(crate) fn ctor_field_types(
        &self,
        resolved_ctor: &FQSymbol,
        scrut_type: Option<&Type>,
        reference: Span,
        census: &super::census::Frame,
    ) -> Result<Vec<ConcreteType>, CranelispError> {
        let (fqtn, ctor) = self.pattern_ctor_meta(resolved_ctor, scrut_type, reference, census)?;
        let type_def = self.lookup_type_def(&fqtn).ok_or_else(|| {
            keying_drift_at(reference, format!("type '{fqtn}' has no type definition"))
        })?;
        super::census::record(census, || super::census::Record::Field {
            class: super::census::FieldClass::of(type_def.type_params.len(), scrut_type),
            declaration: super::census::Declaration::Full,
        });

        let args: Vec<ConcreteType> = match scrut_type {
            Some(Type::ADT(_, args)) => args
                .iter()
                .map(ConcreteType::from_type)
                .collect::<Result<_, _>>()
                .map_err(|residual| residual_instantiation(resolved_ctor, &residual, reference))?,
            _ => Vec::new(),
        };
        let table = self
            .symbol_tables
            .get(&resolved_ctor.module)
            .ok_or_else(|| {
                keying_drift_at(
                    reference,
                    format!(
                        "pattern constructor '{resolved_ctor}' has no symbol table for its module"
                    ),
                )
            })?;
        let fields = cranelisp_types::ctor_field_types_at(&table, &resolved_ctor.symbol, &args)
            .map_err(|refusal| match refusal {
                CtorFieldsAtError::NotConcrete(residual) => {
                    residual_instantiation(resolved_ctor, &residual, reference)
                }
                keying => keying_drift_at(
                    reference,
                    format!(
                        "pattern constructor '{resolved_ctor}' at {} type argument(s): {keying}",
                        args.len()
                    ),
                ),
            })?;
        if fields.len() != ctor.fields.len() {
            return Err(keying_drift_at(
                reference,
                format!(
                    "constructor '{resolved_ctor}' declares {} fields but its scheme supplies {}",
                    ctor.fields.len(),
                    fields.len()
                ),
            ));
        }
        Ok(fields)
    }

    /// Look up a TypeDefInfo by FQTypeName from the symbol tables.
    ///
    /// The info lives on a `ModuleEntry::TypeDef` entry (sum/enum) or, for a
    /// single-ctor **product** type (S79 Option 3a), on the got-slotted product
    /// ctor `Def`'s `DefKind::Constructor { type_def: Some(..) }` type facet —
    /// the product `type_name` key IS the ctor `Def`, not a `TypeDef`.
    pub fn lookup_type_def(&self, fqtn: &FQTypeName) -> Option<TypeDefInfo> {
        let table = self.symbol_tables.get(&fqtn.module)?;
        table
            .get(fqtn.name.as_ref())
            .and_then(Binding::type_def_info)
            .cloned()
    }
}

#[cfg(test)]
mod ctor_value_shape_tests;

#[cfg(test)]
mod keyed_read_hardening_tests;

#[cfg(test)]
mod ctor_field_channel_tests;

/// The refusal of a constructor field read at an instantiation that is not
/// concrete, located at the reference that made it.
fn residual_instantiation(
    resolved_ctor: &FQSymbol,
    residual: &cranelisp_types::NotConcrete,
    reference: Span,
) -> CranelispError {
    CranelispError::CodegenError {
        message: format!(
            "constructor '{resolved_ctor}' is matched at an instantiation that is not concrete ({residual:?})"
        ),
        location: ErrorLocation::from_span(reference),
    }
}

/// The error for a keyed type or constructor read that missed.
fn keying_drift(detail: String) -> CranelispError {
    keying_drift_at(Span::SYNTHETIC, detail)
}

/// [`keying_drift`] located at the reference that made the read.
pub(super) fn keying_drift_at(reference: Span, detail: String) -> CranelispError {
    CranelispError::CodegenError {
        message: format!("internal invariant violation (keying drift): {detail}"),
        location: ErrorLocation::from_span(reference),
    }
}
