//! Symbol-table import-chain resolution — the GOT/arity/extern/platform-effect
//! resolver seam, plus the resolution-adjacent symbol-naming primitives.
//!
//! All four public resolvers (`resolve_got_target`, `resolve_platform_effect_target`,
//! `resolve_extern_target`, `resolve_func_arity`) share one import-chain walker
//! (`resolve_chain`) and one current → qualified(alias/child/absolute) → global
//! driver (`resolve_driven`); each resolver supplies only its terminal `read`
//! closure (P7 — single source of truth; audit F11). `got_data_symbol_name` and
//! `inner_fn_discriminator_for` are the resolution-adjacent symbol-naming
//! primitives.

use dashmap::DashMap;

use cranelisp_types::{
    DefKind, ModuleEntry, ModuleFullPath, PrimitiveBody, Symbol, SymbolTable, Type,
};

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

const MAX_IMPORT_DEPTH: usize = 10;

/// Walk the import chain from `module`/`bare`, applying `read` to each entry on
/// the way. `read` returns `Some(T)` to stop with a result; on `None` the walk
/// follows an `Import` edge (if the entry is one) or gives up. Single source for
/// the four resolver walkers (P7; audit F11).
///
/// `read` receives the module the entry lives in, the entry's bare key in that
/// module (so a resolver can recover the canonical name at the end of the import
/// chain), and the entry itself.
fn resolve_chain<C, L, T>(
    tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module: &ModuleFullPath,
    bare: &str,
    depth: usize,
    read: &impl Fn(&ModuleFullPath, &str, &ModuleEntry<C>) -> Option<T>,
) -> Option<T>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    if depth > MAX_IMPORT_DEPTH {
        return None;
    }
    let st = tables.get(module)?;
    let entry = st.get(bare)?;
    if let Some(found) = read(module, bare, entry) {
        return Some(found);
    }
    if let ModuleEntry::Import { source, .. } = entry {
        let source_module = source.module.clone();
        let source_symbol = source.symbol.clone();
        drop(st);
        return resolve_chain(tables, &source_module, source_symbol.as_ref(), depth + 1, read);
    }
    None
}

/// The shared resolution driver: current module → qualified `module/name`
/// (alias substitution per spec §8.6.6 step 5, then child-of-current, then
/// absolute) → global fallback (all other modules). Each resolver supplies only
/// its terminal `read` closure; the import-chain walk and the driver order are
/// single-sourced here (P7; audit F11).
///
/// The alias substitution (2a) handles a session-level module alias (import-alias
/// §8.3.4 or export-mount §8.4.4), keyed by `<owner>.<alias>`: the matched alias
/// prefix is replaced with its `target` module path before the bare name is
/// resolved there — the resolution the ad-hoc child/absolute parse below cannot
/// perform (it has no knowledge of the alias table). The global fallback (3)
/// handles names that weren't import-linked (e.g. mangled trait methods, or
/// primitives in the synthetic `primitives` module referenced without an import).
fn resolve_driven<C, L, T>(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_aliases: &cranelisp_types::ModuleAliases,
    current_module: &ModuleFullPath,
    name: &Symbol,
    read: impl Fn(&ModuleFullPath, &str, &ModuleEntry<C>) -> Option<T>,
) -> Option<T>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    // 1. Current module first.
    if let Some(result) = resolve_chain(symbol_tables, current_module, name.as_ref(), 0, &read) {
        return Some(result);
    }

    // 2. Qualified "module/name".
    if let Some(slash) = name.as_ref().find('/') {
        let module_part = &name.as_ref()[..slash];
        let bare_name = &name.as_ref()[slash + 1..];
        if !module_part.is_empty() && !bare_name.is_empty() {
            // 2a. Alias substitution.
            let alias_key =
                ModuleFullPath::from(format!("{current_module}.{module_part}"));
            if let Some(alias) = module_aliases.get(&alias_key) {
                let target = alias.target.clone();
                drop(alias);
                if let Some(result) = resolve_chain(symbol_tables, &target, bare_name, 0, &read) {
                    return Some(result);
                }
            }

            // 2b. Child-of-current, then absolute (no-alias fast paths).
            let child_path =
                ModuleFullPath::from(format!("{}.{}", current_module, module_part));
            if let Some(result) = resolve_chain(symbol_tables, &child_path, bare_name, 0, &read) {
                return Some(result);
            }
            let abs_path = ModuleFullPath::from(module_part);
            if let Some(result) = resolve_chain(symbol_tables, &abs_path, bare_name, 0, &read) {
                return Some(result);
            }
        }
    }

    // 3. Global fallback.
    for entry in symbol_tables.iter() {
        if entry.key() == current_module {
            continue;
        }
        if let Some(result) = resolve_chain(symbol_tables, entry.key(), name.as_ref(), 0, &read) {
            return Some(result);
        }
    }

    None
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
    resolve_driven(symbol_tables, module_aliases, current_module, name, |module, _bare, entry| {
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
        entry.callable_got_slot().map(|slot| (module.clone(), slot))
    })
}

/// Resolve whether `name` designates a **dispatchable call target** — a
/// callable entry reachable by the same precedence walk `resolve_got_target`
/// uses, but with the stop condition flipped from `callable_got_slot().is_some()`
/// to [`ModuleEntry::is_callable_target`] (S102, FIXME 0476). This covers both
/// slot-dispatched callables (concrete user fns, `Extern` primitives,
/// constructors, platform effects — for which `resolve_got_target` also returns
/// `Some`) AND **inline-dispatched primitives** (the vec-query trio,
/// `PrimitiveBody::Inline`, which carry no slot and so are invisible to
/// `resolve_got_target`).
///
/// Used by the fn-as-value gate (`is_known_function`): an inline vec primitive
/// referenced as a value is a *known function* (it wraps to a closure whose body
/// inline-emits the op), even though it has no GOT slot. For every non-inline
/// name this is byte-identical to `resolve_got_target(..).is_some()` (they agree
/// wherever a slot exists), so no shadowing precedence or emission changes.
pub(crate) fn resolve_is_callable_target<C, L>(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_aliases: &cranelisp_types::ModuleAliases,
    current_module: &ModuleFullPath,
    name: &Symbol,
) -> bool
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    resolve_driven(symbol_tables, module_aliases, current_module, name, |_module, _bare, entry| {
        entry.is_callable_target().then_some(())
    })
    .is_some()
}

/// Resolve a name to the canonical bare name of a **vec-query-family
/// primitives-table entry** (`vec-get` / `vec-set` / `vec-push`) — the
/// inline-dispatched, slot-less entries
/// (`cranelisp-primitives::insert_vec_query_entries`) that the fn-as-value /
/// auto-curry wrapper paths must INLINE-emit instead of calling through
/// (`design/backend/ownership-codegen.md` §12.7 — the S100 SIGSEGV defect).
///
/// Precedence-faithful: the `read` closure STOPS at the first **callable
/// target** ([`ModuleEntry::is_callable_target`] — the resolution stop
/// condition post-FIXME-0476, covering both slot-dispatched Extern
/// primitives / user fns AND inline-dispatched primitives), then reports
/// whether that entry is a [`PrimitiveBody::Inline`] primitive. A user-defined
/// function shadowing one of these names resolves first (a callable target with
/// a slot → `Some(None)` result) and keeps the ordinary GOT-indirect dispatch,
/// exactly as before. The S101 stringly-typed name-list
/// (`matches!(bare, "vec-get" | ...)`) retires: the inline-primitive *kind* is
/// the discriminator (Principle 20 — the vec trio are the only inline
/// primitives, so `PrimitiveBody::Inline` is exactly the vec-query family).
/// `vec-len` is naturally EXCLUDED: it carries a real extern shim + populated
/// slot (`PrimitiveBody::Extern`), so it reports `None` here and dispatches
/// through its slot (the green control path — `tests/vec_query_value_use.rs`).
pub(crate) fn resolve_vec_query_primitive<C, L>(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_aliases: &cranelisp_types::ModuleAliases,
    current_module: &ModuleFullPath,
    name: &Symbol,
) -> Option<Symbol>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    resolve_driven(
        symbol_tables,
        module_aliases,
        current_module,
        name,
        |_module, bare, entry| {
            // Stop at the first callable target (FIXME 0476: the resolution
            // stop condition flips `callable_got_slot().is_some()` →
            // `is_callable_target()` so inline primitives participate in
            // shadowing precedence identically to slot-carrying ones). A
            // non-callable terminal (type / macro / non-concrete template) is
            // not a stop point — keep walking precedence.
            if !entry.is_callable_target() {
                return None;
            }
            match entry {
                ModuleEntry::Def { kind, .. }
                    if matches!(
                        kind.as_ref(),
                        DefKind::Primitive { body: PrimitiveBody::Inline, .. }
                    ) =>
                {
                    Some(Some(Symbol::from(bare)))
                }
                _ => Some(None),
            }
        },
    )
    .flatten()
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
    resolve_driven(symbol_tables, module_aliases, current_module, name, |module, bare, entry| {
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
            _ => None,
        }
    })
}

/// Resolve a callee name to `(defining_module, slot)` **iff** the resolved entry
/// is a **poll-shape** `DefKind::PlatformEffect { poll_shape: true, .. }` — the
/// keying for the backend's poll-construction arm (FIXME 0457, S94 R1;
/// `design/backend/io-trampoline.md §12`). A blocking effect
/// (`poll_shape: false`, every v6 platform) returns `None`, so it takes the
/// unchanged GOT-indirect blocking-call path — the default build constructs no
/// `IO_TAG_EFFECT_POLL` node and stays byte-identical. No cargo feature: the arm
/// is selected on the data field (Principle 11).
///
/// S96 Wave A4 (step 0): the result additionally surfaces the already-destructured
/// `scheduling_class` (a long-standing `DefKind::PlatformEffect` field — **no new
/// `cranelisp-types` edge, no ABI bump**). The producer pass
/// [`crate::inject_poll_leading_pair`] keys the inject-vs-leave-alone decision on
/// it: `Commutative` ⇒ inject the tokenless `(0, 1)` sentinel; `ResourceSerial` /
/// `Sequential` ⇒ leave the source-supplied live `(token, capacity)` leading pair
/// intact (`poll-support.md §3.4.2`). The bake/peel itself stays keyed ONLY on
/// `poll_shape: bool` (the one uniform path) — `scheduling_class` gates only the
/// producer, never a second node discriminator.
pub(crate) fn resolve_poll_effect_target<C, L>(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_aliases: &cranelisp_types::ModuleAliases,
    current_module: &ModuleFullPath,
    name: &Symbol,
) -> Option<(ModuleFullPath, usize, Vec<Type>, cranelisp_types::SchedulingClass)>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    resolve_driven(symbol_tables, module_aliases, current_module, name, |module, _bare, entry| {
        match entry {
            ModuleEntry::Def { kind, scheme, .. } => match kind.as_ref() {
                DefKind::PlatformEffect {
                    poll_shape: true,
                    got_slot,
                    scheduling_class,
                    ..
                } => {
                    // The effect's param types (for the state-closure capture-dec
                    // glue). A platform effect's scheme is a concrete `Fn`.
                    let params = match &scheme.ty {
                        Type::Fn(ps, _ret) => ps.clone(),
                        _ => Vec::new(),
                    };
                    Some((module.clone(), *got_slot, params, *scheduling_class))
                }
                _ => None,
            },
            _ => None,
        }
    })
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
    resolve_driven(symbol_tables, module_aliases, current_module, name, |_module, bare, entry| {
        match entry {
            ModuleEntry::Def { kind, .. }
                if matches!(kind.as_ref(), DefKind::PrimitiveExtern) =>
            {
                // The symbol-table key IS the ABI name (no jit_name).
                Some(bare.to_string())
            }
            _ => None,
        }
    })
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
    resolve_driven(symbol_tables, module_aliases, current_module, name, |_module, _bare, entry| {
        match entry {
            ModuleEntry::Def { param_names, .. } => Some(param_names.len()),
            _ => None,
        }
    })
}
