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

use cranelisp_types::{ModuleFullPath, Span, Symbol};

/// GOT data symbol name for a module. Single source of truth.
/// Used as the Cranelift data symbol name for the module's GOT table in both
/// JIT and object codegen. See session-restructure.md.
///
/// Convention: `__cranelisp_got_<escaped path>`. Each `.o` file defines all GOT data symbols it needs
/// (own module + imported modules) as `Export` with a placeholder value;
/// the linker/loader patches them at load time.
///
/// # Principle 7 — this is a DELEGATION, not a second scheme (S115 W3)
///
/// The canonical home is [`cranelisp_types::got_data_symbol_name`], relocated
/// DOWN from this module at S76 precisely so the scheme is not duplicated: the
/// backend REFERENCES the symbol (`Linkage::Import` at every cross-module
/// GOT-indirect call site) while **int DEFINES it** (`jit.rs::symbol_lookup_fn`,
/// `src/worker.rs`, `src/exe.rs` — all on the types-owned fn). A backend-local
/// copy of the scheme is therefore a definer/consumer divergence channel: change
/// one side and every cross-module call fails to link with
/// `can't resolve symbol __cranelisp_got_…`.
///
/// It is a one-line forward; the agreement is unit-fenced
/// (`resolution::tests::got_data_symbol_name_agrees_with_the_types_owned_home`).
/// The escape and its injectivity are documented at the types home.
pub(crate) fn got_data_symbol_name(module_path: &ModuleFullPath) -> String {
    cranelisp_types::got_data_symbol_name(module_path)
}

/// Pure core of `FnCompiler::inner_fn_discriminator` (FIXME 0347 defect 1).
///
/// Returns the mono-instance discriminator prefix for a span-derived inner-fn
/// name: the escaped enclosing-fn name + `"__"` when an enclosing name is
/// present, else the empty string (`reduce$Int+Vec` → `reduce_24Int_2bVec__`).
///
/// Injective and prefix-free: ASCII alphanumerics are kept and every other
/// UTF-8 byte, `_` included, becomes `_` plus two lowercase hex digits. `__`
/// therefore never occurs inside the escaped name and terminates it. Symbol
/// constituents such as `-`, `_` and `?` must not collapse together, since
/// instances of one template share every span-derived inner-fn name except
/// this prefix.
pub(crate) fn inner_fn_discriminator_for(current_fn_name: Option<&Symbol>) -> String {
    use std::fmt::Write as _;
    let Some(name) = current_fn_name else {
        return String::new();
    };
    let mut disc = String::new();
    for byte in name.as_ref().bytes() {
        if byte.is_ascii_alphanumeric() {
            disc.push(char::from(byte));
        } else {
            write!(disc, "_{byte:02x}").expect("String write");
        }
    }
    disc.push_str("__");
    disc
}

// =========================================================================
// Drop-glue linker-name composition (S111 R6 §4.1 — the ONE naming-identity
// home). Three named functions, one per glue kind — naming is a FUNCTION, never
// an inline `format!` (the A.4 caveat: the identity test must call the
// PRODUCTION naming fn, not re-compose the format). Two are span+disc-keyed (the
// closure/curry span×mono collision class — FIXME 0350 / ledger item 25); the
// ADT is INSTANTIATION-keyed (module + name + concrete args via
// `adt_instantiation_mangle`) — its body is per-instantiation, so the bare-name
// key it carried through CS-1 under-determined the glue and collided on
// heap-category-divergent siblings (FIXME 0633, re-keyed CS-1.1).
// =========================================================================

/// Linker name for a **lambda-closure** capture drop glue (S111 R6). Keyed by
/// `disc` (`FnCompiler::inner_fn_discriminator()` — the mono instance +
/// create-gate arm) and `span`, IDENTICALLY to the lambda body name so the
/// body+drop-glue symbol pair stay paired per mono instance. Span alone
/// under-keys: N mono instances of one lambda span emit their own drop-glue copy
/// (different capture layout), so span-only would collide (`Duplicate definition
/// of identifier: runtime/closure_drop_glue_…`) — the FIXME 0350 class.
pub(crate) fn closure_drop_glue_name(disc: &str, span: Span) -> String {
    format!(
        "runtime/closure_drop_glue_{}{}_{}",
        disc, span.start, span.end
    )
}

/// Linker name for an **auto-curry** closure's capture drop glue (S111 R6).
/// Keyed by `disc` + `span`, IDENTICALLY to its sibling wrapper name
/// `__curry_{target}_{disc}{span}__` (F2, P7/P8: wrapper + drop glue must share
/// one identity). Span alone under-keys: two monomorphizations of one span with
/// different capture `HeapCategory`s produce distinct wrappers but would collide
/// on a span-only glue name, silently mis-dropping captures (ledger item 25).
/// Folding `disc` makes glue identity track wrapper identity.
pub(crate) fn curry_drop_glue_name(disc: &str, span: Span) -> String {
    format!(
        "runtime/curry_drop_glue_{}{}_{}",
        disc, span.start, span.end
    )
}

// S118 slice S6 (§8) — `adt_instantiation_mangle`, `escape_symbol` and
// `adt_drop_glue_name` are DELETED. They were the naming half of the SECOND
// named-glue identity home (`vec_codegen::build_adt_drop_glue_fn` /
// `build_elem_dec_fn`): a per-INSTANTIATION compiled artifact keyed by a
// backend-local mangle rather than the types-owned
// `cranelisp_types::drop_glue_symbol_name`. Two type-directed glue mechanisms
// under two identity schemes is the exact state arch ruling 10 exists to
// prevent, so they go with the inline emitter, in the same change-set. The
// injectivity discipline they carried (FIXME 0633/0640) now lives in the
// types-owned symbol authority, which is injective over the complete concrete
// type by construction. `closure_drop_glue_name` / `curry_drop_glue_name`
// survive: they name capture ENVELOPES (span + mono discriminator), not type
// glue.

#[cfg(test)]
mod tests;
