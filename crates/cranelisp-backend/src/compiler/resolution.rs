//! Resolution-adjacent symbol-naming primitives.
//!
//! **S110 W3 (`design/arch/backend-keyed-consumer.md`): the entire `resolve_*`
//! resolver family was DELETED here.** The backend is now a pure keyed-lookup
//! consumer — it reads typecheck's per-reference `resolved_target` carrier and
//! performs ONE direct keyed fetch (`CompileContext::entry_at` /
//! `ctor_meta_at` / `got_entry_at` in `context.rs`), hard-erroring on a carrier
//! or entry miss (Principle 24 "Resolve once"; Rev-2 no-soft-fallback). Gone
//! with this wave: `resolve_driven`, `resolve_chain`, the arbitrary-order
//! `symbol_tables.iter()` global scan, and the ten entry points
//! (`resolve_got_target`, `resolve_is_callable_target`,
//! `resolve_vec_query_primitive`, `resolve_callee_summary`,
//! `resolve_platform_effect_target`, `resolve_poll_effect_target`,
//! `resolve_extern_target`, `resolve_func_arity`, plus `lookup_constructor` in
//! `context.rs` and `resolve_got_entry` in `apply.rs`).
//!
//! What survives are the two **symbol-naming primitives** — `got_data_symbol_name`
//! and `inner_fn_discriminator_for`. These are NOT resolvers: no symbol-table
//! scan, no precedence walk, no import-chain follow — each is a fixed
//! compile-time string-composition scheme.

use cranelisp_types::{ModuleFullPath, Symbol};

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

#[cfg(test)]
mod tests;
