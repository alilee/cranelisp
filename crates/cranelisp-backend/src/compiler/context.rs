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
    DefKind, FQSymbol, FQTypeName, ModeSummary, ModuleEntry, ModuleFullPath, PrimitiveBody, Symbol,
    SymbolTable, Type, TypeDefInfo, UserFnState,
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
#[derive(Debug, Clone)]
pub(crate) struct CtorMeta {
    pub tag: usize,
    pub fields: Vec<CtorField>,
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
    /// (`literals::nullary_constructor_tag`) and the provenance lattice
    /// (`fn_compiler::value_provenance`) both answer from here; a second
    /// `fields.is_empty()` elsewhere would be a channel on which a provenance
    /// verdict could disagree with what was actually emitted, which is FIXME
    /// 0917's own shape one level down.
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
    /// FuncId for runtime/panic. None in Ring 0 (uses trap instead).
    pub panic_func_id: Option<FuncId>,
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
            panic_func_id: self.panic_func_id,
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
    pub(crate) fn ctor_meta_at(&self, fq: &FQSymbol) -> Option<(FQTypeName, CtorMeta)> {
        let table = self.symbol_tables.get(&fq.module)?;
        let entry = table.get(fq.symbol.as_ref())?;
        Self::extract_constructor(entry)
    }

    /// The constructor probe
    /// (`design/backend/non-concrete-release-contract.md` §6.2.1): what the
    /// global reference `fq` names, derived from the ONE keyed
    /// [`Self::ctor_meta_at`] read and the ONE field-list read
    /// ([`CtorMeta::value_shape`]). `None` ⇒ not a constructor.
    pub(crate) fn ctor_value_shape_at(&self, fq: &FQSymbol) -> Option<CtorValueShape> {
        self.ctor_meta_at(fq).map(|(_, meta)| meta.value_shape())
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
    /// ownership summary via `mode_summary()`, arity via `param_names`.
    ///
    /// Carrier-miss (a `None` `resolved_target` on a table-reference kind) or
    /// entry-miss (`Some(fq)` that fetches nothing here) is a hard
    /// `CodegenError` at the call site (Principle 18; Rev-2 no-soft-fallback) —
    /// this reader itself just reports `None`, and the caller names the
    /// reference + the missing carrier in the error.
    pub(crate) fn entry_at(&self, fq: &FQSymbol) -> Option<(ModuleFullPath, ModuleEntry<C>)> {
        let table = self.symbol_tables.get(&fq.module)?;
        let entry = table.get(fq.symbol.as_ref())?;
        Some((fq.module.clone(), entry.clone()))
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
        self.entry_at(fq).and_then(|(_, e)| match e {
            ModuleEntry::Def { param_names, .. } => Some(param_names.len()),
            _ => None,
        })
    }

    /// S15 (wrapper return-protection summary) kind arm: the callee's ownership
    /// [`ModeSummary`] read off the fetched entry. Replaces the
    /// `resolve_callee_summary` value-site reach. `None` ⇒ the Decision-24
    /// conservative point (no summary carried).
    pub(crate) fn callee_summary_at(&self, fq: &FQSymbol) -> Option<ModeSummary> {
        self.entry_at(fq)
            .and_then(|(_, e)| e.mode_summary().cloned())
    }

    /// S17/S18 (vec-query wrapper discrimination) kind arm: `true` iff `fq`
    /// fetches a slot-less inline primitive (`DefKind::Primitive { body:
    /// PrimitiveBody::Inline }` — the vec-query trio `vec-get`/`vec-set`/
    /// `vec-push`, the ONLY inline primitives; §12.7). Replaces the
    /// `resolve_vec_query_primitive` value-site reach; the canonical bare name
    /// the wrapper inline-emits is `fq.symbol`.
    pub(crate) fn is_inline_primitive_at(&self, fq: &FQSymbol) -> bool {
        self.entry_at(fq).is_some_and(|(_, e)| {
            matches!(
                &e,
                ModuleEntry::Def { kind, .. }
                    if matches!(
                        kind.as_ref(),
                        DefKind::Primitive { body: PrimitiveBody::Inline, .. }
                    )
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
                &e,
                ModuleEntry::Def { kind, .. }
                    if matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Polymorphic(_) }
                            | DefKind::UserFn { fn_state: UserFnState::Constrained(_) }
                    )
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
    fn extract_constructor<C2: cranelisp_types::CodeStore>(
        entry: &ModuleEntry<C2>,
    ) -> Option<(FQTypeName, CtorMeta)> {
        match entry {
            ModuleEntry::Def { kind, scheme, .. } => {
                let DefKind::Constructor {
                    type_name,
                    tag,
                    field_count,
                    ..
                } = &**kind
                else {
                    return None;
                };
                let field_types: &[Type] = match &scheme.ty {
                    Type::Fn(params, _) => params.as_slice(),
                    _ => &[],
                };
                let fields: Vec<CtorField> = (0..*field_count)
                    .map(|i| CtorField {
                        ty: field_types.get(i).cloned().unwrap_or(Type::Int),
                    })
                    .collect();
                Some((type_name.clone(), CtorMeta { tag: *tag, fields }))
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
    pub(crate) fn constructor_metas(&self, type_def: &TypeDefInfo) -> Vec<CtorMeta> {
        let table = match self.symbol_tables.get(&type_def.name.module) {
            Some(t) => t,
            None => return Vec::new(),
        };
        type_def
            .constructors
            .iter()
            .filter_map(|ctor_name| {
                // Probe the canonical `member_key(Type, Ctor)` key first (S109 W1
                // — a sum ctor's real `Def` lives under `Result.Err`, the bare
                // name being an `Import` alias that `extract_constructor` skips),
                // bare fallback for the product dual-facet. Without the canonical
                // probe the drop-glue emitter sees ZERO data ctors → emits no
                // field decs → heap fields (e.g. an `Err(String)`) leak
                // (`tests/spec_12_runtime.rs::catch_runtime_error_..._leaks`).
                let canonical =
                    cranelisp_types::member_key(&type_def.name.name, ctor_name.as_ref());
                let meta = table
                    .get(canonical.as_ref())
                    .or_else(|| table.get(ctor_name.as_ref()))
                    .and_then(Self::extract_constructor)
                    .map(|(_, meta)| meta);
                // §10.5: a ctor whose canonical AND bare probes both miss is
                // silently dropped — the next keying drift would surface as a
                // wrong heap classification / drop glue, not an error. Fail loud
                // in CI (release skips — the `filter_map` still drops it).
                debug_assert!(
                    meta.is_some(),
                    "ctor '{ctor_name}' of '{}' has no resolvable Def — keying drift",
                    type_def.name
                );
                meta
            })
            .collect()
    }

    /// Look up a TypeDefInfo by FQTypeName from the symbol tables.
    ///
    /// The info lives on a `ModuleEntry::TypeDef` entry (sum/enum) or, for a
    /// single-ctor **product** type (S79 Option 3a), on the got-slotted product
    /// ctor `Def`'s `DefKind::Constructor { type_def: Some(..) }` type facet —
    /// the product `type_name` key IS the ctor `Def`, not a `TypeDef`.
    pub fn lookup_type_def(&self, fqtn: &FQTypeName) -> Option<TypeDefInfo> {
        let table = self.symbol_tables.get(&fqtn.module)?;
        match table.get(fqtn.name.as_ref()) {
            Some(ModuleEntry::TypeDef { info, .. }) => Some(info.clone()),
            Some(ModuleEntry::Def { kind, .. }) => match &**kind {
                DefKind::Constructor {
                    type_def: Some(td), ..
                } => Some((**td).clone()),
                _ => None,
            },
            _ => None,
        }
    }
}

#[cfg(test)]
mod ctor_value_shape_tests;
