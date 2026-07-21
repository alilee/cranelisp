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

use cranelisp_types::{
    ModuleFullPath, PrimitiveNaming, Span, Symbol, Type, VarNaming, render_type,
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
/// # Principle 7 — this is a DELEGATION, not a second scheme (S115 W3)
///
/// The canonical home is [`cranelisp_types::got_data_symbol_name`], relocated
/// DOWN from this module at S76 precisely so the scheme is not duplicated: the
/// backend REFERENCES the symbol (`Linkage::Import` at every cross-module
/// GOT-indirect call site) while **int DEFINES it** (`jit.rs::symbol_lookup_fn`,
/// `worker.rs:1610`, `exe.rs:862` — all on the types-owned fn). A backend-local
/// copy of the scheme is therefore a definer/consumer divergence channel: change
/// one side and every cross-module call fails to link with
/// `can't resolve symbol __cranelisp_got_…`.
///
/// The S76 relocation left this function behind as a live duplicate body; it is
/// now a one-line forward. The agreement is unit-fenced
/// (`resolution::tests::got_data_symbol_name_agrees_with_the_types_owned_home`).
///
/// # R4 status — OWED at the types home, not here
///
/// `design/arch/safety-invariants.md` §4 R4 (census:
/// `design/backend/s115-carrier-and-rc-sweep.md` §4) records this family as the
/// one backend-facing OWED-witness: the `.`→`_` flatten is **not injective** —
/// module names admit `_` as well as `.`, so the two-component path `a.b` and
/// the one-component module `a_b` both flatten to `__cranelisp_got_a_b`, i.e.
/// two modules sharing ONE GOT slab data symbol (cross-module wrong-slab
/// dispatch, the R4 class one level up from the drop-glue keying defect
/// 0633/0640). Constructible in a multi-module program.
///
/// The fix is a `cranelisp-types` edit (the scheme's canonical home) and is
/// filed as FIXME 0748 `target: /arch` with the pinned diff — an injective,
/// prefix-free escape with a round-trip decoder, exactly the CS-1.2 model
/// `escape_symbol` already provides for drop-glue keying. Fixing it HERE alone
/// is the divergence above (verified: the whole stdlib fails to load).
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
    cranelisp_types::got_data_symbol_name(module_path)
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
    format!("runtime/closure_drop_glue_{}{}_{}", disc, span.start, span.end)
}

/// Linker name for an **auto-curry** closure's capture drop glue (S111 R6).
/// Keyed by `disc` + `span`, IDENTICALLY to its sibling wrapper name
/// `__curry_{target}_{disc}{span}__` (F2, P7/P8: wrapper + drop glue must share
/// one identity). Span alone under-keys: two monomorphizations of one span with
/// different capture `HeapCategory`s produce distinct wrappers but would collide
/// on a span-only glue name, silently mis-dropping captures (ledger item 25).
/// Folding `disc` makes glue identity track wrapper identity.
pub(crate) fn curry_drop_glue_name(disc: &str, span: Span) -> String {
    format!("runtime/curry_drop_glue_{}{}_{}", disc, span.start, span.end)
}

/// Symbol-safe identity mangle of a fully concrete ADT **instantiation**
/// (`Type::ADT(fqtn, concrete_args)`): module + type name + concrete type args.
///
/// This is the drop-glue keying identity (FIXME 0633). An ADT drop glue's BODY
/// is per-INSTANTIATION — `build_adt_drop_glue_fn` substitutes `concrete_args`
/// into each ctor field and classifies per-field heap-ness *before* emitting the
/// field decs — so the glue **key** must carry that same instantiation identity.
/// Keying on the bare `fqtn.name` alone (dropping module + concrete args) let the
/// first-build-wins `get_name` skip serve one instantiation's glue to a
/// heap-category-divergent sibling in the same `compile_to_module` batch:
/// `(Vec (Duo Int Str))` then `(Vec (Duo Str Int))` reused the first glue, so
/// `atomic_rmw Sub` ran against the second's raw `Int` field (SIGBUS) and its
/// `Str` field leaked. Distinct instantiations MUST get distinct mangles;
/// identical instantiations MUST get a stable mangle (so the `get_name` reuse is
/// sound). This is the Principle-24 "resolve once" keyed-identity discipline: the
/// key fully determines the artifact.
///
/// Built from the canonical single-source `render_type` walk (Principle 7 — the
/// ONE `Type`→string renderer in the workspace) with `PrimitiveNaming::Qualified`
/// so the module qualifier of every referenced type is present, then INJECTIVELY
/// escaped into a Cranelift symbol name by `escape_symbol`.
///
/// # Injectivity is load-bearing (FIXME 0640)
///
/// The CS-1.1 predecessor "sanitized" the render by mapping every
/// non-`[A-Za-z0-9_]` char to `_` — the same scheme `inner_fn_discriminator_for`
/// uses. That map is **not injective**: `-`, `?`, `!`, `.`, `/`, space all
/// collapse to `_`, and `_` maps to itself, so `render_type` outputs that differ
/// only in those chars produce the SAME symbol. Distinct instantiations
/// (idiomatic hyphenated names `A-B` vs `A_B`; dotted vs hyphenated module paths
/// `a.b/T` vs `a-b/T`) then shared one drop glue → the FIXME 0633 mis-drop
/// reproduced as a reachable SIGBUS. The `inner_fn_discriminator_for` sanitize is
/// safe ONLY because every name it feeds is additionally span+disc-keyed (the
/// span breaks sanitize ties); `adt_instantiation_mangle` is a pure CONTENT key
/// with no disambiguator, so its injectivity must be exact. `escape_symbol`
/// provides it by construction (a decoder exists), keeping the output a legal
/// Cranelift symbol (`[A-Za-z0-9_]`).
///
/// The reaching `Type::ADT` is post-monomorphisation concrete; a non-concrete
/// type would embed a `render_type` `t{id}` var whose numbering is
/// session-dependent, making the identity key unstable across builds — asserted
/// in debug (S-2).
pub(crate) fn adt_instantiation_mangle(ty: &Type) -> String {
    debug_assert!(
        ty.is_concrete(),
        "adt_instantiation_mangle requires a concrete Type::ADT (post-mono) — a \
         non-concrete type embeds a session-dependent `t{{id}}` var, making the \
         drop-glue identity key unstable across builds; got: {}",
        render_type(ty, PrimitiveNaming::Qualified, VarNaming::Numbered)
    );
    escape_symbol(&render_type(ty, PrimitiveNaming::Qualified, VarNaming::Numbered))
}

/// Injective, prefix-free escaping of an arbitrary string into a legal Cranelift
/// symbol (`[A-Za-z0-9_]`).
///
/// `_` is reserved as the escape char: an alphanumeric passes through verbatim, a
/// literal `_` doubles to `__`, and every other char maps to `_` followed by a
/// UNIQUE marker letter (`/`→`_s`, `-`→`_h`, `.`→`_d`, ` `→`_w`, `(`→`_l`,
/// `)`→`_r`, `[`→`_k`, `]`→`_j`, `?`→`_q`, `!`→`_e`, `,`→`_c`), with any char
/// outside that fixed map escaping to the catch-all `_u{codepoint:06x}` (six hex
/// digits, so it is fixed-width and self-delimiting). Every escape sequence
/// decodes unambiguously — on `_`, the next char selects: `_`⇒literal `_`, `u`⇒a
/// six-hex catch-all, any other marker⇒its char — so a total deterministic
/// decoder exists and the map is **injective**: distinct inputs yield distinct
/// outputs. That is the property the drop-glue identity key requires
/// (Principle 24 "Resolve once"; FIXME 0640). `u` is reserved for the catch-all
/// and is deliberately absent from the single-char marker set.
fn escape_symbol(s: &str) -> String {
    use std::fmt::Write;
    let mut out = String::with_capacity(s.len() + 8);
    for c in s.chars() {
        match c {
            'A'..='Z' | 'a'..='z' | '0'..='9' => out.push(c),
            '_' => out.push_str("__"),
            '/' => out.push_str("_s"),
            '-' => out.push_str("_h"),
            '.' => out.push_str("_d"),
            ' ' => out.push_str("_w"),
            '(' => out.push_str("_l"),
            ')' => out.push_str("_r"),
            '[' => out.push_str("_k"),
            ']' => out.push_str("_j"),
            '?' => out.push_str("_q"),
            '!' => out.push_str("_e"),
            ',' => out.push_str("_c"),
            other => {
                // Catch-all for any char the fixed map misses: fixed-width six-hex
                // codepoint escape, self-delimiting so it stays decodable.
                let _ = write!(out, "_u{:06x}", other as u32);
            }
        }
    }
    out
}

/// Linker name for an **ADT** field drop glue (S111 R6; re-keyed S111 CS-1.1,
/// FIXME 0633). Keyed by the full concrete instantiation
/// (`adt_instantiation_mangle` — module + type name + concrete type args), NOT
/// the bare type name: the glue body is per-instantiation, so distinct
/// instantiations (different module, different name, or different concrete args)
/// get distinct glue and the `get_name` idempotency skip dedups ONLY the
/// per-module re-emit of the *same* instantiation. The vec elem-dec layer
/// (`build_elem_dec_fn`) keys on the same mangle, so the two under-keyed layers
/// discriminate instantiations identically.
pub(crate) fn adt_drop_glue_name(ty: &Type) -> String {
    format!("runtime/drop_glue_{}", adt_instantiation_mangle(ty))
}

#[cfg(test)]
mod tests;
