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
    DefKind, FQTypeName, ModuleEntry, ModuleFullPath, Symbol, SymbolTable,
    Type, TypeDefInfo,
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
    /// Session-level module-alias table (spec §8.6.6). Threaded into
    /// `resolve_got_target` / `resolve_func_arity` so qualified-name
    /// resolution can substitute an alias prefix with its target module
    /// before walking the symbol tables. Added S75 W2 (D41 rotation).
    pub module_aliases: &'a cranelisp_types::ModuleAliases,
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
            module_aliases: self.module_aliases,
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
    /// Look up a constructor by name from the symbol tables.
    ///
    /// Accepts both bare names (`"SexpStr"`) and qualified names (`"macros/SexpStr"`).
    /// For qualified names, looks up directly in the specified module.
    /// For bare names, searches the current module's symbol table (following imports).
    /// Returns `(FQTypeName, CtorMeta)` if found.
    ///
    /// Post-S70 ctor-as-Def: constructors are `ModuleEntry::Def` entries with
    /// `kind: DefKind::Constructor { type_name, tag, field_count, .. }`. The
    /// returned `CtorMeta` reconstructs field names (from `param_names`) and
    /// field types (from the `Def.scheme`'s `Type::Fn` params).
    pub(crate) fn lookup_constructor(&self, name: &str) -> Option<(FQTypeName, CtorMeta)> {
        // Determine which module to search and the bare name within it.
        let (search_module, bare_name) = if let Some(slash_pos) = name.find('/') {
            let module_str = &name[..slash_pos];
            let bare = &name[slash_pos + 1..];
            (ModuleFullPath::from(module_str), bare)
        } else {
            (self.current_module.clone(), name)
        };

        // 1. Direct lookup in the target module.
        if let Some(table) = self.symbol_tables.get(&search_module) {
            if let Some(entry) = table.get(bare_name)
                && let Some(result) = Self::extract_constructor(entry)
            {
                return Some(result);
            }

            // Follow import chain.
            if let Some(ModuleEntry::Import { source, .. }) = table.get(bare_name) {
                let source_mod = source.module.clone();
                let source_name = source.symbol.clone();
                drop(table); // Drop guard before getting another
                if let Some(source_table) = self.symbol_tables.get(&source_mod)
                    && let Some(entry) = source_table.get(source_name.as_ref())
                    && let Some(result) = Self::extract_constructor(entry)
                {
                    return Some(result);
                }
            }
        }

        // 2. Global fallback: search all modules for an unqualified name.
        //    This handles cases where constructors from synthetic modules
        //    (primitives, macros) are used without an explicit import.
        if !name.contains('/') {
            for guard in self.symbol_tables.iter() {
                if *guard.key() == self.current_module {
                    continue; // Already searched above
                }
                if let Some(entry) = guard.get(bare_name)
                    && let Some(result) = Self::extract_constructor(entry)
                {
                    return Some(result);
                }
            }
        }

        None
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
                let DefKind::Constructor { type_name, tag, field_count, .. } = &**kind else {
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
                table
                    .get(ctor_name.as_ref())
                    .and_then(Self::extract_constructor)
                    .map(|(_, meta)| meta)
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
                DefKind::Constructor { type_def: Some(td), .. } => Some((**td).clone()),
                _ => None,
            },
            _ => None,
        }
    }
}
