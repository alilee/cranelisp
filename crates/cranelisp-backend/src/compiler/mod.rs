//! Per-function CLIF emission — internal codegen primitives.
//!
//! `FnCompiler` owns a `FunctionBuilder` + `&mut M: Module` and holds all the
//! state needed to compile one function (NOT a 21-parameter function — this
//! addresses the prototype's primary structural debt). One dispatch method per
//! `Expr` variant (`compile_int_lit`, `compile_let`, …).
//!
//! These types (`FnCompiler`, `CompileContext`, `MatchContext`)
//! are `pub` codegen primitives reached only via the
//! `compile_to_module` free function in production; the `pub` exists for
//! test-side AST-fragment compilation. The GOT-target resolution helpers
//! `resolve_func_arity` / `resolve_got_target` / `got_data_symbol_name` are the
//! canonical per-symbol-table probing primitives (no equivalent at the
//! `cranelisp-types` boundary).
//!
//! **Forbidden pattern.** Every primitive — including `not`, `+`, `=`, and the
//! arithmetic/comparison operators — goes through the SAME GOT-indirect
//! dispatch path as any user function. Inline substitution (`primitives_inline`)
//! is a name-keyed shortcut over that path, never a parallel dispatch; backend
//! has no trait knowledge and MUST NOT key on `(trait, method, type)` triples.

// Codegen submodules — narrowed to `pub(crate)` in S75 W3 (they export no
// items externally; codegen lives in `impl FnCompiler` blocks inside them and
// no out-of-crate consumer exists).
pub(crate) mod apply;
pub(crate) mod control_flow;
pub(crate) mod literals;
pub(crate) mod match_codegen;
pub(crate) mod trace_codegen;
pub(crate) mod vec_codegen;

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};

use dashmap::DashMap;

use cranelisp_types::{
    ConcreteType, CranelispError, DefKind, Defn, MonoExpr, FQTypeName,
    ModuleEntry, ModuleFullPath, Span, Symbol, SymbolTable,
    Type, TypeDefInfo,
};

use crate::heap::{self, HeapCategory};

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

// Variable allocation is per-FnCompiler instance via next_var field.

/// GOT data symbol name for a module. Single source of truth.
/// Used as the Cranelift data symbol name for the module's GOT table in both
/// JIT and object codegen. See session-restructure.md.
///
/// Convention: `__cranelisp_got_<flat_path>` where dots are replaced by
/// underscores. Each `.o` file defines all GOT data symbols it needs
/// (own module + imported modules) as `Export` with a placeholder value;
/// the linker/loader patches them at load time.
///
/// # Linker-symbol ABI (preserved here before the S75 W3 `pub(crate)` narrow)
///
/// Returns the per-module GOT data-symbol name `__cranelisp_got_{M}` (the
/// module path flattened, `.`→`_`). This is the relocation target every CLIF
/// call site references (`Linkage::Import` against `__cranelisp_got_{M}`,
/// indexed by `SymbolTable[M].symbols[name].got_slot`); the defining `.o`
/// exports it (`Linkage::Export`) per Decision 23/36. This is the single
/// source of truth for the GOT data-symbol naming scheme.
///
/// Narrowed to `pub(crate)` per the S75 W3 /arch re-ruling: this is a
/// codegen-internal relocation-symbol naming primitive, not a backend
/// boundary. `compiler/mod.rs` is the canonical home; `cache::object` re-exports
/// it `pub(crate)`. int names it (`exe.rs:163`, `worker.rs:3004/3590`) only to
/// construct the same relocation name int-side — int reaching into backend's
/// codegen-naming internals; re-wired S77.
pub(crate) fn got_data_symbol_name(module_path: &ModuleFullPath) -> String {
    let flat = module_path.as_ref().replace('.', "_");
    format!(
        "__cranelisp_got_{}",
        if flat.is_empty() { "_entry" } else { &flat }
    )
}

/// Pure core of `FnCompiler::inner_fn_discriminator` (FIXME 0347 defect 1).
///
/// Returns the mono-instance discriminator prefix for a span-derived inner-fn
/// name: the sanitized enclosing-fn name + `"__"` when an enclosing name is
/// present, else the empty string. Sanitization maps every non-`[A-Za-z0-9_]`
/// char to `_` so a mangled mono name (`reduce$Int+Vec`) yields a clean symbol
/// prefix (`reduce_Int_Vec__`). Free function so the uniqueness property is
/// unit-testable without constructing a full `FnCompiler`.
pub(crate) fn inner_fn_discriminator_for(current_fn_name: Option<&Symbol>) -> String {
    match current_fn_name {
        Some(name) => {
            let sanitized: String = name
                .as_ref()
                .chars()
                .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
                .collect();
            format!("{sanitized}__")
        }
        None => String::new(),
    }
}

/// Resolve a function name to `(defining_module, module_local_slot)` by
/// walking `symbol_tables` starting at `current_module`.
///
/// Uniform replacement for the Sprint-56-retracted `CompilationEnv` trait.
/// Handles:
/// - Bare names: resolved in `current_module`, following Import/Reexport chains.
/// - Qualified `"module/name"`: tries `current_module.module`, then absolute
///   `module` path; the bare name is then resolved in the target module.
/// - Global fallback: walks all modules for names that weren't import-linked
///   (e.g., mangled trait methods written without an explicit import).
///
/// Returns `None` if the symbol is not found, is not a `Def` with a `got_slot`,
/// or if the Import chain exceeds the depth limit (10).
///
/// Narrowed to `pub(crate)` in S75 W3 — backend-internal GOT-resolution
/// primitive (no `cranelisp-types` equivalent; no int caller).
pub(crate) fn resolve_got_target<C, L>(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_aliases: &cranelisp_types::ModuleAliases,
    current_module: &ModuleFullPath,
    name: &Symbol,
) -> Option<(ModuleFullPath, usize)>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    const MAX_IMPORT_DEPTH: usize = 10;

    fn resolve_in_module<C, L>(
        tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
        module: &ModuleFullPath,
        bare: &str,
        depth: usize,
    ) -> Option<(ModuleFullPath, usize)>
    where
        C: cranelisp_types::CodeStore,
        L: cranelisp_types::LinkerStore,
    {
        if depth > MAX_IMPORT_DEPTH {
            return None;
        }
        let st = tables.get(module)?;
        let entry = st.get(bare)?;
        // Read the callable address through `callable_got_slot()`. Post the
        // S83 Option-A reshape (FIXME 0356/0358, Principle 20) the GOT slot
        // lives on the callable `DefKind` variant — there is no longer a flat
        // `got_slot` field to read around. The accessor is now a trivial
        // variant-present read: it returns `Some` exactly for the kinds that
        // structurally own a slot (concrete user fns, primitives, constructors,
        // platform effects) and `None` for the slot-less kinds (constrained
        // templates, `Macro` parent, `PrimitiveExtern`, `Overloaded` base). The
        // once-illegal "constrained template holding a callable slot" pairing
        // that previously read as a NULL phantom slot → `call_indirect` through
        // null → SIGSEGV (FIXME 0354) is now *unrepresentable* — the constrained
        // template variant carries no slot field at all, so the read-around
        // stopgap that guarded it retires.
        if let Some(slot) = entry.callable_got_slot() {
            return Some((module.clone(), slot));
        }
        match entry {
            ModuleEntry::Import { source, .. } => {
                let source_module = source.module.clone();
                let source_symbol = source.symbol.clone();
                drop(st);
                resolve_in_module(tables, &source_module, source_symbol.as_ref(), depth + 1)
            }
            _ => None,
        }
    }

    // 1. Try current module first.
    if let Some(result) = resolve_in_module(symbol_tables, current_module, name.as_ref(), 0) {
        return Some(result);
    }

    // 2. Qualified "module/name".
    if let Some(slash) = name.as_ref().find('/') {
        let module_part = &name.as_ref()[..slash];
        let bare_name = &name.as_ref()[slash + 1..];
        if !module_part.is_empty() && !bare_name.is_empty() {
            // 2a. Alias substitution (spec §8.6.6 step 5): the qualified
            // prefix may be a session-level module alias (import-alias
            // §8.3.4 or export-mount §8.4.4). The alias is keyed by
            // `<owner>.<alias>`; substitute the matched alias prefix with
            // its `target` module path, then resolve the bare name there.
            // This is the resolution the ad-hoc child/absolute parse below
            // cannot perform (it has no knowledge of the alias table).
            let alias_key =
                ModuleFullPath::from(format!("{current_module}.{module_part}"));
            if let Some(alias) = module_aliases.get(&alias_key) {
                let target = alias.target.clone();
                drop(alias);
                if let Some(result) = resolve_in_module(symbol_tables, &target, bare_name, 0) {
                    return Some(result);
                }
            }

            // 2b. Child-of-current, then absolute (no-alias fast paths).
            let child_path =
                ModuleFullPath::from(format!("{}.{}", current_module, module_part));
            if let Some(result) = resolve_in_module(symbol_tables, &child_path, bare_name, 0) {
                return Some(result);
            }
            let abs_path = ModuleFullPath::from(module_part);
            if let Some(result) = resolve_in_module(symbol_tables, &abs_path, bare_name, 0) {
                return Some(result);
            }
        }
    }

    // 3. Global fallback: walk all modules. Handles mangled trait methods
    //    referenced without an explicit import.
    for entry in symbol_tables.iter() {
        if entry.key() == current_module {
            continue;
        }
        if let Some(result) = resolve_in_module(symbol_tables, entry.key(), name.as_ref(), 0) {
            return Some(result);
        }
    }

    None
}

/// Resolve a callee name to `(defining_module, slot, defining_bare_name)` **iff**
/// the resolved entry is a `DefKind::PlatformEffect` Def (the GOT-indirect
/// platform-dispatch arm).
///
/// Mirrors `resolve_got_target`'s import-chain walk but returns `Some` only when
/// the terminal Def carries `kind: DefKind::PlatformEffect { .. }` — used by the
/// backend to discriminate the platform-fn dispatch arm (the only arm that bakes
/// the fn-name and stamps it into the returned Effect node's field-3 post-call,
/// S81 / FIXME 0327 the fault-guarded dispatch funnel, step 2/4; BC §3 "the
/// platform-dispatch fn-name bake" + §5 invariant 9 Option A). The returned bare
/// name is the **defining** entry's key (the canonical name at the end of the
/// import chain), composed with the defining module into the FQ name the backend
/// bakes. A non-PlatformEffect entry (user fn, primitive, trait method) returns
/// `None` so its dispatch arm is left untouched — only platform effects stamp.
pub(crate) fn resolve_platform_effect_target<C, L>(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_aliases: &cranelisp_types::ModuleAliases,
    current_module: &ModuleFullPath,
    name: &Symbol,
) -> Option<(ModuleFullPath, usize, Symbol)>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    const MAX_IMPORT_DEPTH: usize = 10;

    fn resolve_in_module<C, L>(
        tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
        module: &ModuleFullPath,
        bare: &str,
        depth: usize,
    ) -> Option<(ModuleFullPath, usize, Symbol)>
    where
        C: cranelisp_types::CodeStore,
        L: cranelisp_types::LinkerStore,
    {
        if depth > MAX_IMPORT_DEPTH {
            return None;
        }
        let st = tables.get(module)?;
        let entry = st.get(bare)?;
        match entry {
            ModuleEntry::Def { kind, .. }
                if matches!(kind.as_ref(), DefKind::PlatformEffect { .. }) =>
            {
                // The platform effect's GOT slot rides on the variant (S83
                // reshape, FIXME 0358).
                let DefKind::PlatformEffect { got_slot, .. } = kind.as_ref() else {
                    unreachable!("matched PlatformEffect above")
                };
                Some((module.clone(), *got_slot, Symbol::from(bare)))
            }
            ModuleEntry::Import { source, .. } => {
                let source_module = source.module.clone();
                let source_symbol = source.symbol.clone();
                drop(st);
                resolve_in_module(tables, &source_module, source_symbol.as_ref(), depth + 1)
            }
            _ => None,
        }
    }

    // 1. Current module.
    if let Some(result) = resolve_in_module(symbol_tables, current_module, name.as_ref(), 0) {
        return Some(result);
    }
    // 2. Qualified "module/name" (alias substitution, then child/absolute).
    if let Some(slash) = name.as_ref().find('/') {
        let module_part = &name.as_ref()[..slash];
        let bare_name = &name.as_ref()[slash + 1..];
        if !module_part.is_empty() && !bare_name.is_empty() {
            let alias_key =
                ModuleFullPath::from(format!("{current_module}.{module_part}"));
            if let Some(alias) = module_aliases.get(&alias_key) {
                let target = alias.target.clone();
                drop(alias);
                if let Some(result) = resolve_in_module(symbol_tables, &target, bare_name, 0) {
                    return Some(result);
                }
            }
            let child_path =
                ModuleFullPath::from(format!("{}.{}", current_module, module_part));
            if let Some(result) = resolve_in_module(symbol_tables, &child_path, bare_name, 0) {
                return Some(result);
            }
            let abs_path = ModuleFullPath::from(module_part);
            if let Some(result) = resolve_in_module(symbol_tables, &abs_path, bare_name, 0) {
                return Some(result);
            }
        }
    }
    // 3. Global fallback.
    for entry in symbol_tables.iter() {
        if entry.key() == current_module {
            continue;
        }
        if let Some(result) = resolve_in_module(symbol_tables, entry.key(), name.as_ref(), 0) {
            return Some(result);
        }
    }

    None
}

/// Resolve a callee name to the ABI key of a `DefKind::PrimitiveExtern` entry,
/// walking `symbol_tables` starting at `current_module` (following Import edges).
///
/// A `PrimitiveExtern` entry (`discover-tests`) is a host-promised callable
/// whose body lives in `int` and is settled at JIT-finalize via
/// `Jit::define_symbol`. It carries `got_slot: None` (so `resolve_got_target`
/// returns `None` for it) and **no `jit_name`** — the symbol-table key IS the
/// ABI name (`src/CLAUDE.md` §"JIT Symbol Names"). Backend lowers a call to it
/// as a `Linkage::Import` against that key, identical in shape to the
/// platform-effect / intrinsic import path (test-discovery.md §6
/// "Backend — one kind-dispatched call arm"; BC §3 invariant 8 / §7 types).
///
/// Returns the resolved ABI key (the defining entry's symbol-table key, which
/// may differ from the local alias when an Import edge was followed), or `None`
/// if the symbol is absent, is not a `Def`, or is not a `PrimitiveExtern`.
pub(crate) fn resolve_extern_target<C, L>(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_aliases: &cranelisp_types::ModuleAliases,
    current_module: &ModuleFullPath,
    name: &Symbol,
) -> Option<String>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    const MAX_IMPORT_DEPTH: usize = 10;

    fn probe<C, L>(
        tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
        module: &ModuleFullPath,
        bare: &str,
        depth: usize,
    ) -> Option<String>
    where
        C: cranelisp_types::CodeStore,
        L: cranelisp_types::LinkerStore,
    {
        if depth > MAX_IMPORT_DEPTH {
            return None;
        }
        let st = tables.get(module)?;
        let entry = st.get(bare)?;
        match entry {
            ModuleEntry::Def { kind, .. }
                if matches!(kind.as_ref(), DefKind::PrimitiveExtern) =>
            {
                // The symbol-table key IS the ABI name (no jit_name).
                Some(bare.to_string())
            }
            ModuleEntry::Import { source, .. } => {
                let source_module = source.module.clone();
                let source_symbol = source.symbol.clone();
                drop(st);
                probe(tables, &source_module, source_symbol.as_ref(), depth + 1)
            }
            _ => None,
        }
    }

    // 1. Current module first.
    if let Some(key) = probe(symbol_tables, current_module, name.as_ref(), 0) {
        return Some(key);
    }

    // 2. Qualified "module/name" — alias prefix, then child, then absolute.
    if let Some(slash) = name.as_ref().find('/') {
        let module_part = &name.as_ref()[..slash];
        let bare_name = &name.as_ref()[slash + 1..];
        if !module_part.is_empty() && !bare_name.is_empty() {
            let alias_key =
                ModuleFullPath::from(format!("{current_module}.{module_part}"));
            if let Some(alias) = module_aliases.get(&alias_key) {
                let target = alias.target.clone();
                drop(alias);
                if let Some(key) = probe(symbol_tables, &target, bare_name, 0) {
                    return Some(key);
                }
            }
            let child_path =
                ModuleFullPath::from(format!("{}.{}", current_module, module_part));
            if let Some(key) = probe(symbol_tables, &child_path, bare_name, 0) {
                return Some(key);
            }
            let abs_path = ModuleFullPath::from(module_part);
            if let Some(key) = probe(symbol_tables, &abs_path, bare_name, 0) {
                return Some(key);
            }
        }
    }

    // 3. Global fallback — primitives lives in the synthetic `primitives`
    //    module, reached here when the call site has no explicit import.
    for entry in symbol_tables.iter() {
        if entry.key() == current_module {
            continue;
        }
        if let Some(key) = probe(symbol_tables, entry.key(), name.as_ref(), 0) {
            return Some(key);
        }
    }

    None
}

/// Resolve a function's parameter count by walking `symbol_tables` starting at
/// `current_module`. Replacement for the Sprint-56-retracted
/// `CompilationEnv::func_arity`. Used when generating closure wrappers for
/// cross-module function references.
///
/// Narrowed to `pub(crate)` in S75 W3 — backend-internal arity-resolution
/// primitive (no int caller).
pub(crate) fn resolve_func_arity<C, L>(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_aliases: &cranelisp_types::ModuleAliases,
    current_module: &ModuleFullPath,
    name: &Symbol,
) -> Option<usize>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    const MAX_IMPORT_DEPTH: usize = 10;

    fn arity_in_module<C, L>(
        tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
        module: &ModuleFullPath,
        bare: &str,
        depth: usize,
    ) -> Option<usize>
    where
        C: cranelisp_types::CodeStore,
        L: cranelisp_types::LinkerStore,
    {
        if depth > MAX_IMPORT_DEPTH {
            return None;
        }
        let st = tables.get(module)?;
        let entry = st.get(bare)?;
        match entry {
            ModuleEntry::Def { param_names, .. } => Some(param_names.len()),
            ModuleEntry::Import { source, .. } => {
                let source_module = source.module.clone();
                let source_symbol = source.symbol.clone();
                drop(st);
                arity_in_module(tables, &source_module, source_symbol.as_ref(), depth + 1)
            }
            _ => None,
        }
    }

    // 1. Try current module first.
    if let Some(arity) = arity_in_module(symbol_tables, current_module, name.as_ref(), 0) {
        return Some(arity);
    }

    // 2. Qualified "module/name".
    if let Some(slash) = name.as_ref().find('/') {
        let module_part = &name.as_ref()[..slash];
        let bare_name = &name.as_ref()[slash + 1..];
        if !module_part.is_empty() && !bare_name.is_empty() {
            // 2a. Alias substitution (spec §8.6.6 step 5) — mirror
            // `resolve_got_target` so arity resolution follows the same
            // qualified-name path as the GOT-slot resolution.
            let alias_key =
                ModuleFullPath::from(format!("{current_module}.{module_part}"));
            if let Some(alias) = module_aliases.get(&alias_key) {
                let target = alias.target.clone();
                drop(alias);
                if let Some(arity) = arity_in_module(symbol_tables, &target, bare_name, 0) {
                    return Some(arity);
                }
            }

            // 2b. Child-of-current, then absolute (no-alias fast paths).
            let child_path =
                ModuleFullPath::from(format!("{}.{}", current_module, module_part));
            if let Some(arity) = arity_in_module(symbol_tables, &child_path, bare_name, 0) {
                return Some(arity);
            }
            let abs_path = ModuleFullPath::from(module_part);
            if let Some(arity) = arity_in_module(symbol_tables, &abs_path, bare_name, 0) {
                return Some(arity);
            }
        }
    }

    // 3. Global fallback.
    for entry in symbol_tables.iter() {
        if entry.key() == current_module {
            continue;
        }
        if let Some(arity) = arity_in_module(symbol_tables, entry.key(), name.as_ref(), 0) {
            return Some(arity);
        }
    }

    None
}

/// Information about a single function to be traced by `(trace ...)`.
///
/// **Backend-internal** (S76 FIXME 0255, `tracing.md` §5). Discovery moved into
/// backend trace-codegen — `trace_codegen::discover_traced_fns` builds these by
/// iterating `symbol_tables` directly. They no longer cross the int↔backend
/// boundary, so this type is `pub(crate)` and the `CompileContext::traced_fns`
/// field is gone. Per-param/result display descriptors are baked at
/// wrapper-compile time (`trace_codegen`), not carried on this struct.
#[derive(Debug, Clone)]
pub(crate) struct TracedFnInfo {
    /// Fully-qualified function name (e.g., "user/fact").
    pub name: String,
    /// Module that defines this function (e.g., "user", "primitives"). The
    /// grouping key for `compile_trace`, and used to reference the module's GOT
    /// **data symbol** (`got_data_symbol_name`) via relocation in both JIT and
    /// object mode — the GOT base is never baked as a compiling-process
    /// `iconst` (FIXME 0275).
    pub module_path: cranelisp_types::ModuleFullPath,
    /// GOT slot index for this function. At runtime the wrapper reaches the
    /// ORIGINAL implementation by loading `got_base[slot]` BEFORE the swap (into
    /// a per-group originals buffer); the address is never baked at codegen.
    pub got_slot: usize,
    /// Number of parameters.
    pub arity: usize,
    /// Static parameter types (from function's type scheme).
    pub param_types: Vec<Type>,
    /// Static return type (from function's type scheme).
    pub result_type: Type,
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

/// Match-arm-invariant data bundled to reduce parameter counts in
/// `compile_constructor_pattern`.
///
/// Narrowed to `pub(crate)` in S75 W3 — per-arm codegen state, no out-of-crate
/// consumer.
pub(crate) struct MatchContext {
    /// The compiled scrutinee value.
    pub scrut_val: Value,
    /// The inferred type of the scrutinee expression (for field type resolution).
    pub scrut_type: Option<Type>,
    /// The block to branch to if this arm does not match.
    pub next_block: Block,
    /// The merge block where all arms converge.
    pub merge_block: Block,
    /// The saved tail-position flag from before the match.
    pub saved_tail: bool,
}

/// Per-function compilation context.
///
/// Generic over `M: Module` so the same codegen can target both `JITModule`
/// (for immediate execution) and `ObjectModule` (for `.o` file generation).
/// See design/backend/module-caching.md §13.2 for rationale.
// Sprint 58 Wave 3b (Decision 35): generic over `C: CodeStore` and
// `L: LinkerStore` so it can hold `CompileContext<'a, C, L>`. Defaults
// to `<()>`-pinned for backward compat with the typecheck-product flavour.
//
// Narrowed to `pub(crate)` in S75 W3 — the per-function CLIF emitter; no
// out-of-crate consumer (int reaches codegen only via the free fn
// `compile_to_module`). Its `pub` methods/fields drop from the public API
// with the type.
pub(crate) struct FnCompiler<'a, M: Module, C = (), L = ()>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Cranelift function builder.
    pub builder: FunctionBuilder<'a>,
    /// Reference to the compilation module (JITModule or ObjectModule).
    pub module: &'a mut M,
    /// Local variable bindings (name -> Cranelift Variable).
    pub(crate) variables: HashMap<Symbol, Variable>,
    /// Scope stack: each frame is a list of variable names introduced.
    pub(crate) scope_stack: Vec<Vec<Symbol>>,
    /// Shared immutable compilation context.
    pub(crate) ctx: CompileContext<'a, C, L>,

    /// Next Cranelift Variable index (per-function counter).
    pub(crate) next_var: u32,

    // --- TCO state ---
    //
    // Tail Call Optimization (TCO): loop-based self-TCO.
    //
    // Self-recursive tail calls are compiled as jumps to a loop header block
    // instead of actual function calls. This converts recursion into iteration
    // with O(1) stack usage.
    //
    // The pattern:
    //   1. compile_body creates a loop_header block with block params for each fn param
    //   2. Entry block jumps to loop_header with initial param values
    //   3. Loop_header is NOT sealed eagerly (back-edges from tail calls added later)
    //   4. Body is compiled with in_tail_position = true
    //   5. Tail self-calls jump back to loop_header with new arg values
    //   6. All blocks sealed at the end
    //
    // CRITICAL: compile_apply must set in_tail_position = false before compiling args.
    // Tail position propagation:
    //   - If body / else body: inherits tail position
    //   - Let body: inherits tail position
    //   - Match arm bodies: inherit tail position
    //   - Args, conditions, bindings: NOT in tail position

    /// Name of the current function being compiled (for self-call detection).
    pub(crate) current_fn_name: Option<Symbol>,
    /// Loop header block for TCO (back-edge target for self-recursive tail calls).
    pub(crate) tail_loop_block: Option<Block>,
    /// Whether the current expression is in tail position.
    pub(crate) in_tail_position: bool,
    /// Number of parameters of the current function.
    pub(crate) fn_param_count: usize,

    // --- Ring 1 heap state (scaffolding for RC emission in Ring 2) ---

    /// Types of local variables, for RC management.
    pub(crate) variable_types: HashMap<Symbol, Type>,
    /// Last-use information: (var_name, span) -> is_last_use.
    pub(crate) last_uses: HashMap<(Symbol, Span), bool>,
    /// Set of variables whose ownership has been transferred (consumed).
    pub(crate) consumed_vars: std::collections::HashSet<Symbol>,
    /// Variables that borrow from a parent (e.g., pattern match field bindings).
    /// Borrowed vars skip both inc (at extraction) and dec (at scope exit).
    /// The owner (scrutinee) handles cleanup via its own RC management.
    pub(crate) borrowed_vars: std::collections::HashSet<Symbol>,
    /// Captured variable names (variables closed over by a lambda).
    /// These are NEVER eligible for last-use transfer.
    pub(crate) captured_vars: std::collections::HashSet<Symbol>,

    /// Drop glue FuncIds for closure variables.
    /// When a closure with heap-typed captures is bound to a variable,
    /// the drop glue function is stored here so that `pop_scope_with_cleanup`
    /// can pass it to `emit_rc_dec` when freeing the closure.
    pub(crate) closure_drop_glue: HashMap<Symbol, FuncId>,

    /// Depth counter for inline drop glue generation.
    /// Prevents infinite IR for recursive types (e.g., List).
    /// Allows limited nesting for non-recursive parametric types (e.g., Option(Option(String))).
    pub(crate) drop_glue_depth: u32,

    /// Pending closure drop glue from the last `compile_lambda` call.
    /// Set by `compile_lambda`, consumed by `compile_let` or `compile_body`
    /// when binding the closure value to a variable name.
    pub(crate) pending_closure_drop_glue: Option<FuncId>,

    /// Whether we are compiling inside a `(trace ...)` body.
    /// When true, sparkability analysis is disabled — trace bodies must
    /// execute sequentially to produce deterministic trace trees.
    pub(crate) in_trace_body: bool,
}

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Create an inner `FnCompiler` for lambda bodies, continuations,
    /// or (future) drop glue. This is the single construction point for
    /// inner compilers (ring1-checklist section 5.9).
    ///
    /// TCO state is disabled for inner functions (no self-call detection,
    /// no tail loop). The scope and variable maps start fresh.
    pub(crate) fn inner(
        builder: FunctionBuilder<'a>,
        module: &'a mut M,
        ctx: CompileContext<'a, C, L>,
        fn_param_count: usize,
        last_uses: HashMap<(Symbol, Span), bool>,
    ) -> Self {
        FnCompiler {
            builder,
            module,
            variables: HashMap::new(),
            scope_stack: vec![vec![]],
            ctx,
            next_var: 0,
            current_fn_name: None,
            tail_loop_block: None,
            in_tail_position: false,
            fn_param_count,
            variable_types: HashMap::new(),
            last_uses,
            consumed_vars: std::collections::HashSet::new(),
            borrowed_vars: std::collections::HashSet::new(),
            captured_vars: std::collections::HashSet::new(),
            closure_drop_glue: HashMap::new(),
            drop_glue_depth: 0,
            pending_closure_drop_glue: None,
            in_trace_body: false,
        }
    }

    /// Monomorphisation-aware discriminator for span-derived inner-function
    /// names (lambdas, fn-as-value wrappers, operator-as-value wrappers).
    ///
    /// **FIXME 0347 defect (1).** Inner functions are named by source span
    /// (`__lambda_<start>_<end>__`, `__wrap_<name>_<start>_<end>__`). When the
    /// ENCLOSING function is monomorphised — the same source span compiled into
    /// N distinct monomorphic instances within ONE `Module` — every instance
    /// re-emits the same span-derived name, so the second `define_function`
    /// collides (`Duplicate definition of identifier`). The enclosing function's
    /// name IS the per-instance discriminator: each mono copy carries a distinct
    /// mangled name (`reduce$Int+Vec`, `id$Int`, …), so prefixing the inner
    /// name with it uniquifies the N copies. When no enclosing name is set
    /// (top-level expression, nested-lambda inner compiler), the span alone
    /// suffices for uniqueness within that scope, so the prefix is empty.
    ///
    /// Non-`[A-Za-z0-9_]` chars in the enclosing name (`$`, `+`, `/`, `.`) are
    /// mapped to `_` so the result is a clean Cranelift symbol.
    pub(crate) fn inner_fn_discriminator(&self) -> String {
        inner_fn_discriminator_for(self.current_fn_name.as_ref())
    }

    /// Compile a function definition body into Cranelift IR.
    ///
    /// This is the main entry point called by Jit::compile_defn.
    /// Creates the entry block, loop header (for TCO), binds parameters,
    /// compiles the body, and finalizes.
    pub fn compile_body(
        defn: &Defn,
        body: &MonoExpr,
        func: &mut cranelift::codegen::ir::Function,
        func_ctx: &mut FunctionBuilderContext,
        module: &'a mut M,
        ctx: CompileContext<'a, C, L>,
    ) -> Result<(), CranelispError> {
        let mut builder = FunctionBuilder::new(func, func_ctx);

        // Entry block: receives function parameters.
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        // Create loop header block for TCO: one i64 block param per function param.
        let loop_header = builder.create_block();
        for _ in defn.params() {
            builder.append_block_param(loop_header, types::I64);
        }

        // Jump from entry to loop header with initial parameter values.
        let entry_params: Vec<Value> = builder.block_params(entry_block).to_vec();
        builder.ins().jump(loop_header, &entry_params);

        // Switch to loop header. Do NOT seal it yet -- back-edges from tail calls
        // will be added during body compilation.
        builder.switch_to_block(loop_header);

        // Compute last-use info for the body.
        let last_uses = heap::compute_last_uses(body);

        let mut compiler = FnCompiler {
            builder,
            module,
            variables: HashMap::new(),
            scope_stack: vec![vec![]],
            ctx,
            next_var: 0,
            current_fn_name: Some(defn.name.clone()),
            tail_loop_block: Some(loop_header),
            in_tail_position: true,
            fn_param_count: defn.params().len(),
            variable_types: HashMap::new(),
            last_uses,
            consumed_vars: std::collections::HashSet::new(),
            borrowed_vars: std::collections::HashSet::new(),
            captured_vars: std::collections::HashSet::new(),
            closure_drop_glue: HashMap::new(),
            drop_glue_depth: 0,
            pending_closure_drop_glue: None,
            in_trace_body: false,
        };

        // Look up the defn's inferred type to get authoritative parameter types.
        // This is essential for unused parameters: derive_param_type scans
        // use sites, so unused params (e.g., `_s` in `(defn f [:String _s] 42)`)
        // would have no type recorded and scope cleanup would skip their RC dec.
        //
        // Read from the symbol table's Scheme.ty (authoritative source) rather
        // than from expr_types side map (Step 1c: AST-sourced codegen).
        let defn_param_types: Vec<Option<Type>> = compiler.ctx.symbol_tables
            .get(&compiler.ctx.current_module)
            .and_then(|table| {
                if let Some(ModuleEntry::Def { scheme, .. }) = table.get(defn.name.as_ref())
                    && let Type::Fn(ref param_types, _) = scheme.ty {
                        return Some(param_types.iter().map(|t| Some(t.clone())).collect());
                }
                None
            })
            .unwrap_or_else(|| vec![None; defn.params().len()]);

        // Bind function parameters from loop header block params (not entry block).
        // Also record parameter types in variable_types so scope cleanup
        // can emit rc_dec for heap-typed parameters at function exit.
        for (i, (param_name, _)) in defn.params().iter().enumerate() {
            let val = compiler.builder.block_params(loop_header)[i];
            let var = compiler.fresh_variable();
            compiler.builder.declare_var(var, types::I64);
            compiler.builder.def_var(var, val);
            compiler.variables.insert(param_name.clone(), var);
            compiler
                .scope_stack
                .last_mut()
                .unwrap_or_else(|| unreachable!("invariant: scope_stack non-empty"))
                .push(param_name.clone());

            // Use the defn's inferred param type (from symbol table) first.
            // Fall back to derive_param_type_from_body (use-site inference) if the
            // defn type isn't available.
            if let Some(Some(ty)) = defn_param_types.get(i) {
                compiler.variable_types.insert(param_name.clone(), ty.clone());
            } else if let Some(ty) = Self::derive_param_type_from_body(body, param_name) {
                compiler.variable_types.insert(param_name.clone(), ty);
            }
        }

        // Compile the function body with scope cleanup for parameters.
        // This implements the consuming calling convention: the callee owns
        // heap-typed parameters and dec's them at exit. The caller inc's
        // variable arguments before the call.
        let skip_var = Self::return_var_in_scope(body, compiler.scope_stack.last());
        let result = compiler.compile_expr(body)?;
        compiler.protect_return_value(&skip_var, result, body);
        compiler.pop_scope_with_cleanup(skip_var.as_ref());

        // Return the result.
        compiler.builder.ins().return_(&[result]);

        // Seal all blocks (including loop_header which may have back-edges).
        compiler.builder.seal_all_blocks();
        compiler.builder.finalize();

        Ok(())
    }

    // --- Expression dispatch ---

    /// Compile a monomorphised expression, dispatching to the appropriate
    /// handler.
    ///
    /// The codegen walk is over [`MonoExpr`] (concrete-boundary-type.md §3.1,
    /// FIXME 0391): every node carries a `ty: ConcreteType` non-optionally, so a
    /// `Type::Var` is *unrepresentable* at every codegen-reaching position. The
    /// `Annotate` variant is erased at the `MonoExpr::from_expr` build, so it has
    /// no arm here.
    pub fn compile_expr(&mut self, expr: &MonoExpr) -> Result<Value, CranelispError> {
        match expr {
            MonoExpr::IntLit { value, .. } => self.compile_int_lit(*value),
            MonoExpr::FloatLit { value, .. } => self.compile_float_lit(*value),
            MonoExpr::BoolLit { value, .. } => self.compile_bool_lit(*value),
            MonoExpr::StringLit { value, span, .. } => self.compile_string_lit(value, *span),
            MonoExpr::Var {
                name,
                span,
                resolved_call,
                ty,
            } => {
                // The signature-path bridge: `compile_var` reads the variable's
                // type as a `&Type` (for the value-position trait-method arity).
                // The node's `ConcreteType` embeds losslessly into a `Type`.
                let inferred = ty.to_type();
                self.compile_var(name, *span, resolved_call.as_deref(), Some(&inferred))
            }
            MonoExpr::Let {
                bindings,
                body,
                span,
                ..
            } => self.compile_let(bindings, body, *span),
            MonoExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => self.compile_if(cond, then_branch, else_branch),
            MonoExpr::Lambda {
                params, body, span, ty,
            } => {
                let lambda_type = ty.to_type();
                self.compile_lambda(params, body, *span, Some(&lambda_type))
            }
            MonoExpr::Apply {
                callee,
                args,
                span,
                resolved_call,
                ty,
            } => {
                let apply_type = ty.to_type();
                self.compile_apply(
                    callee,
                    args,
                    *span,
                    resolved_call.as_deref(),
                    Some(&apply_type),
                )
            }
            MonoExpr::Match {
                scrutinee,
                arms,
                span,
                ..
            } => self.compile_match(scrutinee, arms, *span),
            MonoExpr::VecLit { elements, span, .. } => self.compile_vec_lit(elements, *span),
            MonoExpr::Trace {
                modules,
                body,
                span,
                ..
            } => self.compile_trace(modules, body, *span),
            MonoExpr::ParBind {
                bindings,
                body,
                span,
                ..
            } => self.compile_par_bind(bindings, body, *span),
            MonoExpr::ConstrADT {
                tag,
                fields,
                span,
                ..
            } => self.compile_constr_adt(*tag, fields, *span),
        }
    }

    // --- Variable allocation ---

    /// Allocate a fresh Cranelift Variable index.
    pub(crate) fn fresh_variable(&mut self) -> Variable {
        let idx = self.next_var;
        self.next_var += 1;
        Variable::new(idx as usize)
    }

    // --- Scope management ---

    pub(crate) fn push_scope(&mut self) {
        self.scope_stack.push(vec![]);
    }

    pub(crate) fn pop_scope(&mut self) {
        if let Some(frame) = self.scope_stack.pop() {
            for name in frame {
                self.variables.remove(&name);
                self.variable_types.remove(&name);
            }
        }
    }

    /// Pop a scope frame and emit `rc_dec` for all heap-typed bindings,
    /// except the variable named by `skip_var` (whose ownership transfers
    /// to the caller as the return value).
    ///
    /// Key invariant: "Scope cleanup emits dec for all heap-typed bindings
    /// EXCEPT the return value, consumed vars, and borrowed vars."
    ///
    /// Borrowed vars (e.g., pattern match field bindings) are skipped entirely —
    /// they share the owner's (scrutinee's) reference and the owner handles cleanup.
    ///
    /// ADT field cleanup happens inside the RC=0 dealloc path (via
    /// `emit_rc_dec_with_inline_drop_glue`), NOT as a separate step before dec.
    /// This prevents double-free when fields are independently referenced.
    pub(crate) fn pop_scope_with_cleanup(
        &mut self,
        skip_var: Option<&Symbol>,
    ) {
        if let Some(frame) = self.scope_stack.last() {
            // Collect bindings that need dec before we mutate state.
            let to_dec: Vec<(Symbol, Type, bool)> = frame
                .iter()
                .filter(|name| {
                    // Skip the return value variable.
                    if let Some(skip) = skip_var
                        && *name == skip {
                            return false;
                        }
                    // Skip consumed variables (ownership transferred to callee).
                    if self.consumed_vars.contains(*name) {
                        return false;
                    }
                    // Skip borrowed variables (owner handles cleanup).
                    if self.borrowed_vars.contains(*name) {
                        return false;
                    }
                    // Check if this binding is heap-typed.
                    if let Some(ty) = self.variable_types.get(*name) {
                        self.is_heap_type(ty)
                    } else {
                        false
                    }
                })
                .map(|name| {
                    let ty = self.variable_types.get(name).cloned()
                        .unwrap_or(Type::Int); // fallback, should not happen
                    let needs_guard = matches!(
                        signature_heap_category(&ty, Some(self.ctx.symbol_tables)),
                        HeapCategory::Mixed
                    );
                    (name.clone(), ty, needs_guard)
                })
                .collect();

            // Emit rc_dec for each heap-typed binding.
            let dealloc = self.ctx.dealloc_func_id;
            for (name, ty, needs_guard) in &to_dec {
                if let Some(var) = self.variables.get(name) {
                    let val = self.builder.use_var(*var);

                    // For closures (Type::Fn), use runtime-embedded drop glue.
                    // This handles both locally-created closures AND closures
                    // received as function parameters (where the static
                    // closure_drop_glue map has no entry).
                    if matches!(ty, Type::Fn(_, _)) {
                        self.emit_closure_dec_inline(val, dealloc);
                        continue;
                    }

                    // For Vec-typed bindings: must route through vec_drop to
                    // dec each element and free the data buffer; the generic
                    // rc_dec → dealloc path leaks both.
                    if let Some(elem_ty) =
                        crate::compiler::vec_codegen::vec_element_type(ty)
                    {
                        let elem_ty = elem_ty.clone();
                        let span = cranelisp_types::Span::new(0, 0);
                        let _ = self.emit_vec_aware_rc_dec(val, &elem_ty, span);
                        continue;
                    }

                    // For ADTs: emit RC dec with inline drop glue in the
                    // dealloc path. Field cleanup ONLY happens when RC
                    // reaches 0 (inside the free branch), not unconditionally.
                    // This prevents double-free when fields are independently
                    // referenced (e.g., extracted via pattern match).
                    self.emit_rc_dec_with_inline_drop_glue(val, ty, dealloc, *needs_guard);
                }
            }
        }

        // Now actually pop the scope (remove variables from maps).
        self.pop_scope();
    }

    /// Emit inline drop glue for an ADT: dec each AlwaysHeap field.
    ///
    /// This is a temporary measure until proper drop glue functions are
    /// generated. It handles the common case of ADTs with String or other
    /// heap-typed fields.
    ///
    /// For Mixed ADTs (with both nullary and data constructors), the field
    /// dec is guarded by a heap-pointer check: if the value is a bare
    /// nullary tag, no fields exist to dec.
    fn emit_inline_drop_glue(
        &mut self,
        adt_val: Value,
        ty: &Type,
        dealloc: FuncId,
        is_mixed: bool,
    ) {
        let fqtn = match ty {
            Type::ADT(fqtn, _) => fqtn,
            _ => return, // Not an ADT; nothing to do.
        };

        let type_def = match self.ctx.lookup_type_def(fqtn) {
            Some(td) => td,
            None => return,
        };

        // Constructor metadata is reconstructed from each ctor's
        // DefKind::Constructor Def post-S70.
        let all_ctors = self.ctx.constructor_metas(&type_def);
        let subst = build_adt_type_substitution(ty, &all_ctors);

        // Collect data constructors (those with fields).
        let data_ctors: Vec<CtorMeta> = all_ctors
            .into_iter()
            .filter(|c| !c.fields.is_empty())
            .collect();

        if data_ctors.is_empty() {
            return; // No data constructors, nothing to drop.
        }

        // Check if any data constructor has heap-typed fields.
        let has_heap_fields = data_ctors.iter().any(|ctor| {
            ctor.fields.iter().any(|f| {
                let resolved = substitute_type_inline(&f.ty, &subst);
                matches!(
                    signature_heap_category(&resolved, Some(self.ctx.symbol_tables)),
                    HeapCategory::AlwaysHeap | HeapCategory::Mixed
                )
            })
        });

        if !has_heap_fields {
            return; // No heap fields to drop.
        }

        // For Mixed ADTs, guard the field dec with a heap-pointer check.
        let cont_block = if is_mixed {
            Some(self.emit_mixed_adt_heap_guard(adt_val))
        } else {
            None
        };

        // Emit field decs for each data constructor.
        self.emit_drop_glue_field_decs(adt_val, &data_ctors, &subst, dealloc);

        // Jump to continuation for Mixed guard.
        if let Some(cont) = cont_block {
            self.builder.ins().jump(cont, &[]);
            self.builder.switch_to_block(cont);
            self.builder.seal_block(cont);
        }
    }

    /// Emit a heap-pointer guard for Mixed ADTs in drop glue.
    ///
    /// Creates a branch that skips field dec if the value is a bare nullary
    /// tag (below the heap threshold). Returns the continuation block that
    /// the caller must jump to when field dec is done.
    fn emit_mixed_adt_heap_guard(&mut self, adt_val: Value) -> Block {
        let cont = self.builder.create_block();
        let glue_block = self.builder.create_block();

        let threshold = self
            .builder
            .ins()
            .iconst(types::I64, heap::NULLARY_THRESHOLD_I64);
        let is_heap = self.builder.ins().icmp(
            IntCC::UnsignedGreaterThanOrEqual,
            adt_val,
            threshold,
        );
        self.builder
            .ins()
            .brif(is_heap, glue_block, &[], cont, &[]);

        self.builder.switch_to_block(glue_block);
        self.builder.seal_block(glue_block);
        cont
    }

    /// Emit field decs for data constructors in drop glue.
    ///
    /// For a single data constructor, dec fields directly.
    /// For multiple data constructors, emit tag-based dispatch
    /// (branch chain like match codegen).
    fn emit_drop_glue_field_decs(
        &mut self,
        adt_val: Value,
        data_ctors: &[CtorMeta],
        subst: &std::collections::HashMap<cranelisp_types::TypeId, Type>,
        dealloc: FuncId,
    ) {
        use crate::heap::HeapAdt;

        if data_ctors.len() == 1 {
            let ctor = &data_ctors[0];
            self.emit_field_decs(adt_val, ctor, subst, dealloc);
        } else {
            // Multiple data constructors: load the tag and branch to the
            // correct field-dec block for each variant.
            let heap_tag = heap::heap_load(
                &mut self.builder,
                adt_val,
                HeapAdt::TAG_OFFSET,
            );

            let done_block = self.builder.create_block();

            for (idx, ctor) in data_ctors.iter().enumerate() {
                let ctor_block = self.builder.create_block();
                let next_block = if idx + 1 < data_ctors.len() {
                    self.builder.create_block()
                } else {
                    // Last data constructor: fallthrough to done.
                    done_block
                };

                let tag_val = self.builder.ins().iconst(types::I64, ctor.tag as i64);
                let cmp = self.builder.ins().icmp(IntCC::Equal, heap_tag, tag_val);
                self.builder.ins().brif(cmp, ctor_block, &[], next_block, &[]);

                self.builder.switch_to_block(ctor_block);
                self.builder.seal_block(ctor_block);

                self.emit_field_decs(adt_val, ctor, subst, dealloc);
                self.builder.ins().jump(done_block, &[]);

                if idx + 1 < data_ctors.len() {
                    self.builder.switch_to_block(next_block);
                    self.builder.seal_block(next_block);
                }
            }

            self.builder.switch_to_block(done_block);
            self.builder.seal_block(done_block);
        }
    }

    /// Emit rc_dec for each heap-typed field of a single constructor.
    ///
    /// Used by `emit_inline_drop_glue` for both the single-constructor case
    /// and within each branch of the multi-constructor tag dispatch.
    ///
    /// For ADT-typed fields, uses `emit_rc_dec_with_inline_drop_glue` to
    /// recursively handle nested ADT field cleanup when the field's RC
    /// reaches 0. For non-ADT heap types (String, closures), uses plain
    /// `emit_rc_dec` since they have no sub-fields.
    fn emit_field_decs(
        &mut self,
        adt_val: Value,
        ctor: &CtorMeta,
        subst: &std::collections::HashMap<cranelisp_types::TypeId, Type>,
        dealloc: FuncId,
    ) {
        use crate::heap::HeapAdt;

        for (i, field) in ctor.fields.iter().enumerate() {
            let resolved_ty = substitute_type_inline(&field.ty, subst);
            let category = signature_heap_category(&resolved_ty, Some(self.ctx.symbol_tables));
            match category {
                HeapCategory::AlwaysHeap => {
                    let field_val = heap::heap_load(
                        &mut self.builder,
                        adt_val,
                        HeapAdt::field_offset(i),
                    );
                    // Vec-typed fields must route through vec_drop, not
                    // dealloc — otherwise elements and the data buffer leak.
                    if let Some(elem_ty) =
                        crate::compiler::vec_codegen::vec_element_type(&resolved_ty)
                    {
                        let elem_ty = elem_ty.clone();
                        // span not readily available here; use a synthetic span.
                        let span = cranelisp_types::Span::new(0, 0);
                        // Failing here is a backend-setup invariant breach
                        // (vec_drop must be declared whenever Vec types are
                        // in play). Swallow the Result rather than propagate
                        // — emit_field_decs is infallible by signature.
                        let _ = self.emit_vec_aware_rc_dec(field_val, &elem_ty, span);
                    } else if matches!(resolved_ty, Type::ADT(_, _)) {
                        // For ADT-typed fields, recursively handle nested field cleanup.
                        self.emit_rc_dec_with_inline_drop_glue(
                            field_val, &resolved_ty, dealloc, false,
                        );
                    } else if matches!(resolved_ty, Type::Fn(_, _)) {
                        self.emit_closure_dec_inline(field_val, dealloc);
                    } else {
                        heap::emit_rc_dec(
                            &mut self.builder,
                            self.module,
                            field_val,
                            dealloc,
                            None,
                        );
                    }
                }
                HeapCategory::Mixed => {
                    let field_val = heap::heap_load(
                        &mut self.builder,
                        adt_val,
                        HeapAdt::field_offset(i),
                    );
                    // Mixed fields may be ADTs with nested heap fields.
                    if matches!(resolved_ty, Type::ADT(_, _)) {
                        self.emit_rc_dec_with_inline_drop_glue(
                            field_val, &resolved_ty, dealloc, true,
                        );
                    } else {
                        heap::emit_rc_dec_guarded(
                            &mut self.builder,
                            self.module,
                            field_val,
                            dealloc,
                            None,
                            true,
                        );
                    }
                }
                HeapCategory::NeverHeap => {}
            }
        }
    }

    // --- Return value identification ---

    /// If `body` is a direct variable reference to a name in the current scope
    /// frame, return that name. Used to skip rc_dec for the return value.
    pub(crate) fn return_var_in_scope(
        body: &MonoExpr,
        scope_frame: Option<&Vec<Symbol>>,
    ) -> Option<Symbol> {
        if let MonoExpr::Var { name, .. } = body
            && let Some(frame) = scope_frame
                && frame.contains(name) {
                    return Some(name.clone());
                }
        None
    }

    /// If `skip_var` is None and the return value has a heap type, emit
    /// `rc_inc` on the value so it survives the subsequent scope cleanup.
    /// Scope cleanup will dec all heap bindings, which may include the
    /// value being returned (when the body is a non-trivial expression like
    /// `if` or `match` that resolves to a scope binding). The caller will
    /// dec it later, so the net ownership is correct.
    pub(crate) fn protect_return_value(
        &mut self,
        skip_var: &Option<Symbol>,
        body_val: Value,
        body: &MonoExpr,
    ) {
        if skip_var.is_some() {
            return; // The skip_var mechanism already protects the return value.
        }
        // Fresh allocations (Lambda, StringLit) cannot be the same as any
        // scope binding, so scope cleanup cannot affect them. Skip protect.
        if matches!(body, MonoExpr::Lambda { .. } | MonoExpr::StringLit { .. }) {
            return;
        }
        // Only protect if the current scope has heap-typed bindings that
        // scope cleanup will dec. Borrowed and consumed vars are skipped by
        // `pop_scope_with_cleanup`, so their presence alone does NOT justify
        // a protective inc — emitting one would leave the return value with
        // an inflated RC that the caller cannot balance.
        let has_cleanup_targets = self.scope_stack.last().is_some_and(|frame| {
            frame.iter().any(|name| {
                if self.borrowed_vars.contains(name) || self.consumed_vars.contains(name) {
                    return false;
                }
                self.variable_types.get(name).is_some_and(|ty| self.is_heap_type(ty))
            })
        });
        if !has_cleanup_targets {
            return;
        }
        let category = HeapCategory::classify(body.ty(), Some(self.ctx.symbol_tables));
        match category {
            HeapCategory::AlwaysHeap => {
                heap::emit_rc_inc(&mut self.builder, body_val);
            }
            HeapCategory::Mixed => {
                heap::emit_rc_inc_guarded(&mut self.builder, body_val);
            }
            HeapCategory::NeverHeap => {}
        }
    }

    // --- Heap helpers (scaffolding for RC emission in Ring 2) ---

    /// Check if a type is heap-allocated and needs RC management.
    pub(crate) fn is_heap_type(&self, ty: &Type) -> bool {
        matches!(
            signature_heap_category(ty, Some(self.ctx.symbol_tables)),
            HeapCategory::AlwaysHeap | HeapCategory::Mixed
        )
    }

    /// Derive a function parameter's type by finding a Var reference with the
    /// given name in the function body and reading its `inferred_type()`.
    ///
    /// Function parameters don't have their own `inferred_type`, but every
    /// Var reference to the parameter in the body does. We walk the body AST
    /// to find the first Var node matching the name.
    pub(crate) fn derive_param_type_from_body(body: &MonoExpr, name: &Symbol) -> Option<Type> {
        find_var_type_in_expr(body, name)
    }

    /// Check if a variable use is the last use (for ownership transfer).
    pub(crate) fn is_last_use(&self, name: &Symbol, span: Span) -> bool {
        if self.captured_vars.contains(name) {
            // Captured variables are NEVER eligible for last-use transfer.
            return false;
        }
        if self.borrowed_vars.contains(name) {
            // Borrowed variables (extracted from a match scrutinee's field)
            // do NOT own the value — the scrutinee still holds it. A
            // textually-last use of a borrowed var does not imply ownership
            // transfer, so Vec COW mutate-in-place on such a binding would
            // alias the scrutinee's field and cause a double-free once the
            // scrutinee's drop glue dec's the field independently. See
            // `design/backend/ring2-rc.md §3.1` (Decision 24 consuming
            // convention) and §5.5 (captured_vars rule — the borrowed_vars
            // rule is its structural twin: neither owns the value, so
            // neither may transfer ownership via last-use).
            // Regression: repro-slice2.cl — `(consume (Box [0]))` read len=0.
            return false;
        }
        self.last_uses
            .get(&(name.clone(), span))
            .copied()
            .unwrap_or(false)
    }

    /// Emit RC dec for a closure value using its embedded drop glue pointer.
    ///
    /// Unlike `emit_rc_dec` which takes a compile-time `drop_glue_id`,
    /// this loads the drop glue pointer from the closure's embedded
    /// `DROP_GLUE_PTR_OFFSET` field at runtime and calls it if non-zero.
    ///
    /// Used for:
    /// - Closure parameters received from callers (type unknown at compile time)
    /// - Temporary closure expressions used as callees
    /// - Any closure variable where the static drop glue is not available
    pub(crate) fn emit_closure_dec_inline(&mut self, closure_val: Value, dealloc_id: FuncId) {
        use crate::heap::HeapClosure;
        use cranelisp_types::HeapHeader;
        use cranelift_codegen::ir::AtomicRmwOp;

        let cont_block = self.builder.create_block();

        // Decrement RC.
        let rc_addr = self
            .builder
            .ins()
            .iadd_imm(closure_val, i64::from(HeapHeader::RC_OFFSET));
        let one = self.builder.ins().iconst(types::I64, 1);
        let old_rc = self.builder.ins().atomic_rmw(
            types::I64,
            MemFlags::trusted(),
            AtomicRmwOp::Sub,
            rc_addr,
            one,
        );

        // Branch: if old_rc == 1, free the closure.
        let cmp = self.builder.ins().icmp(IntCC::Equal, old_rc, one);
        let free_block = self.builder.create_block();
        self.builder
            .ins()
            .brif(cmp, free_block, &[], cont_block, &[]);

        // Free path.
        self.builder.switch_to_block(free_block);
        self.builder.seal_block(free_block);
        self.builder.ins().fence();

        // Load drop_glue_ptr from the closure.
        let drop_glue_ptr = heap::heap_load(
            &mut self.builder,
            closure_val,
            HeapClosure::DROP_GLUE_PTR_OFFSET,
        );

        // If drop_glue_ptr != 0, call it.
        let zero = self.builder.ins().iconst(types::I64, 0);
        let has_glue = self
            .builder
            .ins()
            .icmp(IntCC::NotEqual, drop_glue_ptr, zero);
        let glue_block = self.builder.create_block();
        let dealloc_block = self.builder.create_block();
        self.builder
            .ins()
            .brif(has_glue, glue_block, &[], dealloc_block, &[]);

        // Call drop glue: (closure_ptr: i64) -> ()
        self.builder.switch_to_block(glue_block);
        self.builder.seal_block(glue_block);

        let mut glue_sig = self.module.make_signature();
        glue_sig.params.push(AbiParam::new(types::I64));
        let glue_sig_ref = self.builder.import_signature(glue_sig);
        self.builder
            .ins()
            .call_indirect(glue_sig_ref, drop_glue_ptr, &[closure_val]);
        self.builder.ins().jump(dealloc_block, &[]);

        // Dealloc the closure.
        self.builder.switch_to_block(dealloc_block);
        self.builder.seal_block(dealloc_block);
        let dealloc_ref = self
            .module
            .declare_func_in_func(dealloc_id, self.builder.func);
        self.builder.ins().call(dealloc_ref, &[closure_val]);
        self.builder.ins().jump(cont_block, &[]);

        // Continue.
        self.builder.switch_to_block(cont_block);
        self.builder.seal_block(cont_block);
    }

    /// Emit RC dec for an ADT value with inline drop glue in the dealloc path.
    ///
    /// Unlike the old `emit_inline_drop_glue` + `emit_rc_dec` pattern (which
    /// dec'd fields unconditionally before dec'ing the ADT), this method
    /// only dec's fields inside the "RC reached 0" branch. This prevents
    /// double-free when fields have independent references (e.g., extracted
    /// via pattern match binding).
    ///
    /// Flow:
    /// ```text
    /// if needs_guard && val < NULLARY_THRESHOLD: skip (bare tag)
    /// old_rc = atomic_sub(val.rc, 1)
    /// if old_rc == 1:
    ///     fence()
    ///     emit_inline_drop_glue(val)   // dec heap-typed fields
    ///     dealloc(val)
    /// ```
    pub(crate) fn emit_rc_dec_with_inline_drop_glue(
        &mut self,
        val: Value,
        ty: &Type,
        dealloc: FuncId,
        needs_guard: bool,
    ) {
        use cranelisp_types::HeapHeader;
        use cranelift_codegen::ir::AtomicRmwOp;

        // Depth limit for inline drop glue: prevents infinite IR for
        // recursive types (e.g., List contains List). Allows several
        // levels of nesting for non-recursive parametric types like
        // Option(Option(String)). Beyond the limit, fall back to plain
        // dec (fields leak — known limitation of inline drop glue,
        // to be replaced by proper drop-glue functions later).
        const MAX_DROP_GLUE_DEPTH: u32 = 4;
        if self.drop_glue_depth >= MAX_DROP_GLUE_DEPTH {
            if needs_guard {
                heap::emit_rc_dec_guarded(
                    &mut self.builder, self.module, val, dealloc, None, true,
                );
            } else {
                heap::emit_rc_dec(
                    &mut self.builder, self.module, val, dealloc, None,
                );
            }
            return;
        }
        self.drop_glue_depth += 1;

        let cont_block = self.builder.create_block();

        // Guard: if value is a bare nullary tag, skip the dec entirely.
        if needs_guard {
            let threshold = self
                .builder
                .ins()
                .iconst(types::I64, heap::NULLARY_THRESHOLD_I64);
            let is_tag = self.builder.ins().icmp(
                IntCC::UnsignedLessThan,
                val,
                threshold,
            );
            let dec_block = self.builder.create_block();
            self.builder
                .ins()
                .brif(is_tag, cont_block, &[], dec_block, &[]);
            self.builder.switch_to_block(dec_block);
            self.builder.seal_block(dec_block);
        }

        // Atomic dec RC.
        let rc_addr = self
            .builder
            .ins()
            .iadd_imm(val, i64::from(HeapHeader::RC_OFFSET));
        let one = self.builder.ins().iconst(types::I64, 1);
        let old_rc = self.builder.ins().atomic_rmw(
            types::I64,
            MemFlags::trusted(),
            AtomicRmwOp::Sub,
            rc_addr,
            one,
        );

        // Branch: if old_rc == 1 (last reference), free the object.
        let cmp = self.builder.ins().icmp(IntCC::Equal, old_rc, one);
        let free_block = self.builder.create_block();
        self.builder
            .ins()
            .brif(cmp, free_block, &[], cont_block, &[]);

        // Free path: Acquire fence, drop glue for fields, then dealloc.
        self.builder.switch_to_block(free_block);
        self.builder.seal_block(free_block);
        self.builder.ins().fence();

        // Emit inline drop glue for ADT fields (only in the dealloc path).
        // This is safe because RC==0 means we are the sole owner.
        self.emit_inline_drop_glue(val, ty, dealloc, false);

        // Call runtime/dealloc.
        let dealloc_ref = self
            .module
            .declare_func_in_func(dealloc, self.builder.func);
        self.builder.ins().call(dealloc_ref, &[val]);
        self.builder.ins().jump(cont_block, &[]);

        // Continue path.
        self.builder.switch_to_block(cont_block);
        self.builder.seal_block(cont_block);

        // Restore depth counter.
        self.drop_glue_depth -= 1;
    }

    /// Mark a variable as borrowed (skip scope-exit dec — owner handles cleanup).
    pub(crate) fn mark_borrowed(&mut self, name: &Symbol) {
        self.borrowed_vars.insert(name.clone());
    }
}

// --- Free helper functions for type variable resolution ---

/// Build a substitution map from type variable IDs to concrete types
/// for an ADT value. Extracts the concrete type args from the ADT type
/// and maps them positionally to the Var IDs found in the type definition.
pub(crate) fn build_adt_type_substitution(
    ty: &Type,
    ctors: &[CtorMeta],
) -> std::collections::HashMap<cranelisp_types::TypeId, Type> {
    // Get concrete type args from the variable's type.
    let concrete_args = match ty {
        Type::ADT(_, args) => args.clone(),
        _ => return std::collections::HashMap::new(),
    };

    // Build substitution from Var ids to concrete types.
    let mut unique_var_ids: Vec<cranelisp_types::TypeId> = Vec::new();
    for c in ctors {
        for field in &c.fields {
            collect_var_ids_from_type(&field.ty, &mut unique_var_ids);
        }
    }
    unique_var_ids
        .iter()
        .zip(concrete_args.iter())
        .map(|(&id, arg)| (id, arg.clone()))
        .collect()
}

/// Collect all unique Var ids from a type, in order of first appearance.
pub(crate) fn collect_var_ids_from_type(ty: &Type, ids: &mut Vec<cranelisp_types::TypeId>) {
    match ty {
        Type::Var(id)
            if !ids.contains(id) => {
                ids.push(*id);
            }
        Type::ADT(_, args) => {
            for a in args {
                collect_var_ids_from_type(a, ids);
            }
        }
        Type::Fn(params, ret) => {
            for p in params {
                collect_var_ids_from_type(p, ids);
            }
            collect_var_ids_from_type(ret, ids);
        }
        _ => {}
    }
}

/// Substitute type variables in a type using a Var id -> Type mapping.
pub(crate) fn substitute_type_inline(
    ty: &Type,
    subst: &std::collections::HashMap<cranelisp_types::TypeId, Type>,
) -> Type {
    match ty {
        Type::Var(id) => {
            subst.get(id).cloned().unwrap_or_else(|| ty.clone())
        }
        Type::ADT(name, args) => {
            let new_args = args.iter().map(|a| substitute_type_inline(a, subst)).collect();
            Type::ADT(name.clone(), new_args)
        }
        Type::Fn(params, ret) => {
            let new_params = params.iter().map(|p| substitute_type_inline(p, subst)).collect();
            let new_ret = Box::new(substitute_type_inline(ret, subst));
            Type::Fn(new_params, new_ret)
        }
        _ => ty.clone(),
    }
}

/// Find the inferred type of a Var reference with the given name in an expression tree.
///
/// Walks the AST recursively and returns the first Var node's `inferred_type()`
/// that matches the name. Used by `derive_param_type_from_body` to find parameter
/// types from use sites when the defn-level type is not available.
fn find_var_type_in_expr(expr: &MonoExpr, name: &Symbol) -> Option<Type> {
    match expr {
        MonoExpr::Var { name: var_name, ty, .. } if var_name == name => {
            Some(ty.to_type())
        }
        MonoExpr::Let { bindings, body, .. } => {
            for (_, val) in bindings {
                if let Some(ty) = find_var_type_in_expr(val, name) {
                    return Some(ty);
                }
            }
            find_var_type_in_expr(body, name)
        }
        MonoExpr::If { cond, then_branch, else_branch, .. } => {
            find_var_type_in_expr(cond, name)
                .or_else(|| find_var_type_in_expr(then_branch, name))
                .or_else(|| find_var_type_in_expr(else_branch, name))
        }
        MonoExpr::Lambda { body, .. } => find_var_type_in_expr(body, name),
        MonoExpr::Apply { callee, args, .. } => {
            find_var_type_in_expr(callee, name)
                .or_else(|| args.iter().find_map(|a| find_var_type_in_expr(a, name)))
        }
        MonoExpr::Match { scrutinee, arms, .. } => {
            find_var_type_in_expr(scrutinee, name)
                .or_else(|| arms.iter().find_map(|arm| find_var_type_in_expr(&arm.body, name)))
        }
        MonoExpr::VecLit { elements, .. } => {
            elements.iter().find_map(|e| find_var_type_in_expr(e, name))
        }
        MonoExpr::Trace { body, .. } => find_var_type_in_expr(body, name),
        MonoExpr::ParBind { bindings, body, .. } => {
            for (_, val) in bindings {
                if let Some(ty) = find_var_type_in_expr(val, name) {
                    return Some(ty);
                }
            }
            find_var_type_in_expr(body, name)
        }
        _ => None,
    }
}

/// Heap-classify a SIGNATURE-PATH field/binding `Type` (concrete-boundary-type.md
/// §3.1.1, FIXME 0391/0394). The body-AST codegen walk classifies a `ConcreteType`
/// off each `MonoExpr` node directly — no `Var` by construction. But the
/// `Type`-typed RC machinery (`variable_types`, `CtorField`, `resolve_field_types`)
/// reads field/binding types from the **signature** (the `scheme`, `Type::Fn`
/// params), and a `Var` legitimately survives there in ONE case: the **generic
/// constructor `Def`'s own codegen**. A `(deftype (Option a) … (Some [:a val]))`
/// ctor `Def` is codegen'd ONCE as a generic template whose field param is
/// `Type::Var a` — its runtime representation is uniform (i64 tag-or-pointer), the
/// `Mixed` heap category. (§3.1.1's "ctor field types are always concrete at
/// codegen" holds for ctor USE sites — a `(Some 1)` instance pins `a := Int` — but
/// NOT for the generic ctor `Def`'s own template body; that gap is FIXME 0394.)
///
/// So this helper classifies a concrete field type via the total
/// `HeapCategory::classify(&ConcreteType, …)`, and maps a residual `Var`/`TyConApp`
/// (a generic-ctor-template field param) to `Mixed` — the uniform-representation
/// category, restoring the pre-Phase-3 generic-ctor-`Def` behaviour. This does NOT
/// widen the `ConcreteType` `classify` (which stays total, no `Var` arm) and does
/// NOT affect the body-AST path (still 100% `Var`-free by construction).
pub(crate) fn signature_heap_category<C, L>(
    ty: &Type,
    symbol_tables: Option<&dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>>,
) -> HeapCategory
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    match ConcreteType::from_type(ty) {
        Ok(ct) => HeapCategory::classify(&ct, symbol_tables),
        // A generic-ctor-template field param (`Type::Var`) / unresolved HKT head:
        // uniform i64 representation → `Mixed` (the guarded RC path). FIXME 0394.
        Err(_) => HeapCategory::Mixed,
    }
}

#[cfg(test)]
mod tests {
    // FnCompiler is tested via the public compile_and_run_expr API in lib.rs
    // and through the Jit::compile_defn path. Direct unit testing of FnCompiler
    // requires constructing a full Cranelift context, which is covered by
    // the integration tests.

    use super::*;
    use cranelisp_types::{
        DefKind, ModuleAliasEntry, ModuleAliases, ModuleEntry, Scheme, Type, UserFnState,
        Visibility,
    };

    fn def_with_slot(slot: usize) -> ModuleEntry {
        ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: std::collections::HashMap::new(),
                ty: Type::Int,
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(DefKind::UserFn {
                fn_state: UserFnState::Concrete { got_slot: slot },
            }),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: None,
            codegen_view: None,
            code: None,
        }
    }

    // ── inner-fn name discriminator (FIXME 0347 defect 1) ────────────────────

    // spec: design/arch/fixmes/0347 — span-derived inner-fn names
    //   (`__lambda_…`, `__wrap_…`) MUST be uniquified per monomorphic instance
    //   of the enclosing fn, else N mono copies collide on one symbol.
    #[test]
    fn inner_fn_discriminator_uniquifies_per_mono_instance() {
        use cranelisp_types::Symbol;
        // Two monomorphic instances of one source fn carry distinct mangled
        // names; the discriminator must differ so a shared lambda span yields
        // distinct symbols.
        let a = inner_fn_discriminator_for(Some(&Symbol::from("reduce$Int+Vec")));
        let b = inner_fn_discriminator_for(Some(&Symbol::from("reduce$Float+Vec")));
        assert_ne!(a, b, "distinct mono instances must yield distinct discriminators");

        // The composed lambda names (the actual collision surface) differ.
        let span = (305usize, 312usize);
        let name_a = format!("__lambda_{a}{}_{}__", span.0, span.1);
        let name_b = format!("__lambda_{b}{}_{}__", span.0, span.1);
        assert_ne!(
            name_a, name_b,
            "two mono copies of one lambda span must emit distinct symbols \
             (else the 2nd define_function collides)"
        );

        // Sanitization: $/+/./ become _, leaving a clean Cranelift symbol.
        assert!(
            a.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'),
            "discriminator must be a clean symbol: {a:?}"
        );
        assert_eq!(a, "reduce_Int_Vec__");

        // No enclosing fn (top-level expr / nested-lambda inner compiler): empty
        // prefix — the span alone disambiguates within that scope.
        assert_eq!(inner_fn_discriminator_for(None), "");
    }

    // spec: design/arch/fixmes/0350 — the span-derived closure DROP-GLUE name
    //   (`runtime/closure_drop_glue_<start>_<end>`) MUST be uniquified per
    //   monomorphic instance the SAME way the lambda body name is (0347), else
    //   N mono copies of one lambda span emit N drop-glue defs with the
    //   identical name → linker `Duplicate definition of identifier`.
    #[test]
    fn closure_drop_glue_name_uniquifies_per_mono_instance() {
        use cranelisp_types::Symbol;
        // Two monomorphic instances of one source fn — the same shape that
        // collided on the lambda body name in 0347.
        let a = inner_fn_discriminator_for(Some(&Symbol::from("apply$Int+Vec")));
        let b = inner_fn_discriminator_for(Some(&Symbol::from("apply$Float+Vec")));

        // The composed drop-glue names (the 0350 collision surface) differ.
        let span = (2004usize, 2022usize);
        let glue_a =
            format!("runtime/closure_drop_glue_{a}{}_{}", span.0, span.1);
        let glue_b =
            format!("runtime/closure_drop_glue_{b}{}_{}", span.0, span.1);
        assert_ne!(
            glue_a, glue_b,
            "two mono copies of one lambda span must emit distinct drop-glue \
             symbols (else the 2nd define_function collides)"
        );

        // The drop-glue name MUST share the lambda body's discriminator scheme
        // so the (body, drop-glue) pair stay paired per mono instance.
        let body_a = format!("__lambda_{a}{}_{}__", span.0, span.1);
        let body_b = format!("__lambda_{b}{}_{}__", span.0, span.1);
        assert!(
            glue_a.contains(&a) && body_a.contains(&a),
            "body+drop-glue of instance A must carry the same discriminator"
        );
        assert!(
            glue_b.contains(&b) && body_b.contains(&b),
            "body+drop-glue of instance B must carry the same discriminator"
        );

        // No enclosing fn: empty prefix, span alone disambiguates — the
        // pre-0350 behaviour for top-level / nested-lambda scopes is preserved.
        let none = inner_fn_discriminator_for(None);
        assert_eq!(none, "");
        assert_eq!(
            format!("runtime/closure_drop_glue_{none}{}_{}", span.0, span.1),
            "runtime/closure_drop_glue_2004_2022"
        );
    }

    /// A `DefKind::PrimitiveExtern` entry — host-promised, slot-less, no
    /// codegen body. Mirrors the `discover-tests` shape int seeds into the
    /// `primitives` table.
    fn primitive_extern_def() -> ModuleEntry {
        ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: std::collections::HashMap::new(),
                ty: Type::Int,
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(DefKind::PrimitiveExtern),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: None,
            codegen_view: None,
            code: None,
        }
    }

    // spec: design/arch/test-discovery.md §6 "Backend — one kind-dispatched
    //       call arm"; BC §3 invariant 8 / §7 types — a `DefKind::PrimitiveExtern`
    //       callee (`discover-tests`) carries `got_slot: None`, so
    //       `resolve_got_target` misses it; `resolve_extern_target` recognises
    //       the kind and returns its ABI key (the symbol-table key, no
    //       jit_name) for a `Linkage::Import` lowering. Confirms global-fallback
    //       resolution (the call site has no explicit import of `primitives`)
    //       and that a non-extern Def is NOT matched.
    #[test]
    fn resolve_extern_target_finds_primitive_extern_by_kind() {
        let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();

        // Synthetic `primitives` module seeds `discover-tests` as a
        // PrimitiveExtern (got_slot: None) and an ordinary slotted Def.
        let prims = ModuleFullPath::from("primitives");
        {
            let mut st = SymbolTable::new(prims.clone());
            st.insert(Symbol::from("discover-tests"), primitive_extern_def());
            st.insert(Symbol::from("add-i64"), def_with_slot(7));
            tables.insert(prims.clone(), st);
        }
        // Call site is in `user`, with no import of `primitives`.
        let user = ModuleFullPath::from("user");
        tables.insert(user.clone(), SymbolTable::new(user.clone()));
        let aliases: ModuleAliases = DashMap::new();

        // The extern resolves via global fallback to its ABI key.
        assert_eq!(
            resolve_extern_target(&tables, &aliases, &user, &Symbol::from("discover-tests")),
            Some("discover-tests".to_string()),
            "PrimitiveExtern callee resolves to its symbol-table key (ABI name)",
        );
        // `resolve_got_target` does NOT match it (no GOT slot).
        assert_eq!(
            resolve_got_target(&tables, &aliases, &user, &Symbol::from("discover-tests")),
            None,
            "a PrimitiveExtern has no GOT slot — the GOT path must miss it",
        );
        // A slotted ordinary Def is NOT a PrimitiveExtern.
        assert_eq!(
            resolve_extern_target(&tables, &aliases, &user, &Symbol::from("add-i64")),
            None,
            "a slotted UserFn/primitive is not a PrimitiveExtern",
        );
        // Absent name resolves to nothing.
        assert_eq!(
            resolve_extern_target(&tables, &aliases, &user, &Symbol::from("nonesuch")),
            None,
        );
    }

    /// A `DefKind::PlatformEffect` Def. Post the S83 Option-A reshape (FIXME
    /// 0358) a platform effect ALWAYS carries its GOT slot on the variant — it
    /// is a GOT-addressable callable, so there is no longer a slot-less
    /// "as-built" PlatformEffect shape to contrast against.
    fn platform_effect_def_new_shape(slot: usize) -> ModuleEntry {
        ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: std::collections::HashMap::new(),
                ty: Type::Int,
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(DefKind::PlatformEffect {
                scheduling_class: cranelisp_types::SchedulingClass::Sequential,
                got_slot: slot,
            }),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: None,
            codegen_view: None,
            code: None,
        }
    }

    // spec: design/arch/platform-interface.md §6.2/§6.3; BC §3 "the
    //       platform-interface codegen role" — the platform GOT-indirect call
    //       arm activates for a `DefKind::PlatformEffect` entry, which (post the
    //       S83 Option-A reshape, FIXME 0358) ALWAYS carries its GOT slot on the
    //       variant: `resolve_got_target` resolves it to (module, slot) so the
    //       dispatch arm emits GOT-indirect. A genuinely slot-less kind
    //       (`PrimitiveExtern`) misses the GOT path and falls to the
    //       direct-extern (`Linkage::Import`) path.
    #[test]
    fn platform_effect_new_shape_resolves_got_indirect() {
        let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let plat = ModuleFullPath::from("platform.shapes");
        {
            let mut st = SymbolTable::new(plat.clone());
            // PlatformEffect: carries its got_slot on the variant (DLL-exported
            // GOT adoption) → GOT-indirect resolvable.
            st.insert(Symbol::from("rectangle-area"), platform_effect_def_new_shape(2));
            // A genuinely slot-less host-promised extern — misses the GOT path
            // and stays on the direct-extern fallback.
            st.insert(Symbol::from("print"), primitive_extern_def());
            tables.insert(plat.clone(), st);
        }
        let user = ModuleFullPath::from("user");
        tables.insert(user.clone(), SymbolTable::new(user.clone()));
        let aliases: ModuleAliases = DashMap::new();

        // PlatformEffect resolves to (defining module, slot) → GOT-indirect arm.
        assert_eq!(
            resolve_got_target(&tables, &aliases, &user, &Symbol::from("rectangle-area")),
            Some((plat.clone(), 2)),
            "PlatformEffect resolves GOT-indirect at its adopted slot",
        );
        // The slot-less PrimitiveExtern misses the GOT path → direct-extern stays live.
        assert_eq!(
            resolve_got_target(&tables, &aliases, &user, &Symbol::from("print")),
            None,
            "a slot-less PrimitiveExtern stays on the direct-extern path",
        );
    }

    // spec: design/arch/bounded-contexts.md §5 invariant 9 + §3 "the
    //       platform-dispatch fn-name bake" (S81 / FIXME 0327, the dispatch
    //       funnel step 2/4) — `resolve_platform_effect_target` is the
    //       discriminator that decides whether the GOT-indirect arm stamps the
    //       baked fn-name into the returned Effect node's field-3. It must
    //       return `Some((defining_module, slot, defining_bare_name))` for a
    //       new-shape `DefKind::PlatformEffect`, follow Import edges to the
    //       DEFINING entry (so the baked FQ name is canonical, not the local
    //       alias), and return `None` for every other kind — so ONLY the
    //       PlatformEffect arm stamps and user fns / primitives / trait methods
    //       are left untouched.
    #[test]
    fn resolve_platform_effect_target_discriminates_kind_and_follows_imports() {
        let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let plat = ModuleFullPath::from("platform.shapes");
        {
            let mut st = SymbolTable::new(plat.clone());
            // New-shape PlatformEffect — the only kind that stamps.
            st.insert(Symbol::from("rectangle-area"), platform_effect_def_new_shape(2));
            // A slotted USER fn at the same module — must NOT match.
            st.insert(Symbol::from("helper"), def_with_slot(5));
            tables.insert(plat.clone(), st);
        }
        // `user` imports `rectangle-area` under a local alias `area`.
        let user = ModuleFullPath::from("user");
        {
            let mut st = SymbolTable::new(user.clone());
            st.insert(
                Symbol::from("area"),
                ModuleEntry::Import {
                    source: cranelisp_types::FQSymbol {
                        module: plat.clone(),
                        symbol: Symbol::from("rectangle-area"),
                    },
                    visibility: Visibility::Public,
                },
            );
            tables.insert(user.clone(), st);
        }
        let aliases: ModuleAliases = DashMap::new();

        // Direct reference in the defining module: Some(module, slot, bare).
        assert_eq!(
            resolve_platform_effect_target(
                &tables, &aliases, &plat, &Symbol::from("rectangle-area")
            ),
            Some((plat.clone(), 2, Symbol::from("rectangle-area"))),
            "new-shape PlatformEffect resolves to (defining module, slot, defining bare name)",
        );
        // Import-aliased reference resolves to the DEFINING entry — so the baked
        // FQ name is `platform.shapes/rectangle-area`, never `user/area`.
        assert_eq!(
            resolve_platform_effect_target(&tables, &aliases, &user, &Symbol::from("area")),
            Some((plat.clone(), 2, Symbol::from("rectangle-area"))),
            "Import edge resolves to the defining module + canonical name, not the local alias",
        );
        // A slotted USER fn is NOT a PlatformEffect → None (its arm must not stamp).
        assert_eq!(
            resolve_platform_effect_target(&tables, &aliases, &plat, &Symbol::from("helper")),
            None,
            "a slotted UserFn must not be discriminated as a platform effect",
        );
        // Absent name → None.
        assert_eq!(
            resolve_platform_effect_target(&tables, &aliases, &user, &Symbol::from("nonesuch")),
            None,
        );
    }

    // spec: design/arch/test-discovery.md §6 — `resolve_extern_target` follows
    //       an Import edge to the defining module and returns the DEFINING
    //       entry's key (the canonical ABI name), not the importing alias.
    #[test]
    fn resolve_extern_target_follows_import_edge() {
        let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let prims = ModuleFullPath::from("primitives");
        {
            let mut st = SymbolTable::new(prims.clone());
            st.insert(Symbol::from("discover-tests"), primitive_extern_def());
            tables.insert(prims.clone(), st);
        }
        // `user` imports `discover-tests` under a local alias `discover`.
        let user = ModuleFullPath::from("user");
        {
            let mut st = SymbolTable::new(user.clone());
            st.insert(
                Symbol::from("discover"),
                ModuleEntry::Import {
                    source: cranelisp_types::FQSymbol {
                        module: prims.clone(),
                        symbol: Symbol::from("discover-tests"),
                    },
                    visibility: Visibility::Public,
                },
            );
            tables.insert(user.clone(), st);
        }
        let aliases: ModuleAliases = DashMap::new();
        assert_eq!(
            resolve_extern_target(&tables, &aliases, &user, &Symbol::from("discover")),
            Some("discover-tests".to_string()),
            "Import edge resolves to the defining module's ABI key, not the local alias",
        );
    }

    // spec: spec/08-modules.md §8.6.6 step 5 — qualified-name resolution
    //       substitutes a module-alias prefix with its target before walking
    //       the symbol tables. S75 W2 (D41 rotation) threaded `module_aliases`
    //       into `resolve_got_target` to perform this substitution; without it
    //       a qualified `alias/name` whose prefix is an alias (not a real
    //       child/absolute module) would not resolve.
    #[test]
    fn resolve_got_target_follows_module_alias_prefix() {
        let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        // Real target module `core.string` defines `concat` at GOT slot 3.
        let target = ModuleFullPath::from("core.string");
        {
            let mut st = SymbolTable::new(target.clone());
            st.insert(Symbol::from("concat"), def_with_slot(3));
            tables.insert(target.clone(), st);
        }
        // Current module `user` has NO `str` child module and NO `concat`.
        let current = ModuleFullPath::from("user");
        tables.insert(current.clone(), SymbolTable::new(current.clone()));

        // Alias `user.str` → `core.string` (an import-alias owned by `user`).
        let aliases: ModuleAliases = DashMap::new();
        aliases.insert(
            ModuleFullPath::from("user.str"),
            ModuleAliasEntry::new(target.clone(), Visibility::Private, cranelisp_types::Span::SYNTHETIC),
        );

        // With the alias table, `str/concat` from `user` resolves to
        // (core.string, slot 3) via §8.6.6 step-5 substitution.
        let resolved = resolve_got_target(
            &tables,
            &aliases,
            &current,
            &Symbol::from("str/concat"),
        );
        assert_eq!(
            resolved,
            Some((target.clone(), 3)),
            "alias prefix `str` must substitute to `core.string` and resolve `concat`"
        );

        // Without the alias entry, the same qualified name does NOT resolve
        // (no `user.str` child module, no absolute `str` module).
        let empty_aliases: ModuleAliases = DashMap::new();
        let unresolved = resolve_got_target(
            &tables,
            &empty_aliases,
            &current,
            &Symbol::from("str/concat"),
        );
        assert_eq!(
            unresolved, None,
            "without the alias, `str/concat` has no child/absolute target to resolve"
        );
    }
}
