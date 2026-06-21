//! Macro-clause compiler (S87 §1.1 extraction from `process_form.rs`).
//!
//! The SINGLE clause-compiler implementation (`compile_macro_clause_core`) plus
//! its `_with_state` adapter (resolver path, raw refs). The `_inline` adapter
//! (the `&mut ModuleCompiler` Pass-2 path) lives in `macro_resolution.rs` since
//! it sources its refs from `ctx`. This module is the **codegen** of a clause
//! (synthesize → expand-qq → build → check → `inline_jit_codegen_for_names`),
//! distinct from `macro_resolution`'s *recognize/drive* concern
//! (`src/CLAUDE.md §"Macro-clause single implementation"`).

use cranelisp_types::{
    CranelispError, ErrorLocation, ModuleFullPath, Span, Symbol, TopLevel,
};

use crate::worker::{
    ModuleCheckAccumulator, build_program_compat,
    check_program_compat_no_gap, ensure_typecheck_product,
    inline_jit_codegen_for_names,
};

use cranelisp_typecheck::CheckState;

/// Compile a single macro clause — the SINGLE implementation shared by both
/// entry shapes (FIXME 0109 Wave D collapse).
///
/// Post-Decision-44 the `_with_state` (raw-refs, resolver path) and `_inline`
/// (`&mut ModuleCompiler`, Pass-2 path) clause compilers had byte-identical
/// bodies — the only difference was where the references came from. This core
/// takes the references explicitly; the two thin adapters
/// (`compile_macro_clause_with_state` / `compile_macro_clause_inline`) source
/// them from their respective callers. No behavioural change: each adapter
/// passes exactly the references its former body used (the `_with_state`
/// shared-state→aliases/prelude resolution, incl. the unit-test leaked-default
/// fallback, lives in that adapter, unchanged).
pub(super) fn compile_macro_clause_core(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module_aliases: &cranelisp_types::ModuleAliases,
    prelude_fallback: &cranelisp_typecheck::PreludeFallback,
    target_module: &ModuleFullPath,
    macro_name: &Symbol,
    clause_idx: usize,
    clause: &cranelisp_frontend::MacroClause,
    span: Span,
    typecheck_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    shared_state: Option<&crate::session_v4::SharedState>,
) -> Result<(), CranelispError> {
    // Step 1: Synthesize the defn Sexp.
    let synth_sexp = cranelisp_frontend::synthesize_macro_clause_defn(
        macro_name.as_ref(), clause_idx, clause, span,
    );

    // Step 2: Expand quasiquotes.
    let expanded_sexp = cranelisp_frontend::expand_quasiquotes(&synth_sexp)?;

    // Step 3: Build AST. Macro clause synthesis emits compiler-generated
    // bodies whose Sexp tree comes from `synthesize_macro_clause_defn`; user
    // `(trace ...)` cannot reach this synthesis path. `InMemoryAndObject`
    // bypasses the validator.
    let program = build_program_compat(&[expanded_sexp])?;

    // Step 4: Typecheck via the collapsed `check_forms` surface (Decision 44
    // 2026-05-13 third amendment). `check_program_compat` runs the internal
    // Pass 1 + Pass 2 + finalize sequence in one call.
    check_program_compat_no_gap(
        symbol_tables,
        module_aliases,
        prelude_fallback,
        target_module,
        &program,
    )?;

    // Step 5: Extract the defn from the annotated symbol table (not the unannotated program).
    // The typechecker stores annotated defns (with resolved_call on AST nodes) in
    // ModuleEntry::Def.ast. Using the unannotated program would lose these annotations.
    let defn_name = program
        .iter()
        .find_map(|tl| match tl {
            TopLevel::Defn(d) => Some(d.name.clone()),
            _ => None,
        })
        .ok_or_else(|| CranelispError::MacroError {
            message: format!(
                "macro clause {} for '{}' produced no defn",
                clause_idx, macro_name
            ),
            location: ErrorLocation::from_span(span),
        })?;

    // Compile macro clause through the unified compile_to_module path.
    // Macro clause functions are normal functions on per-module GOTs — the
    // typechecker has registered `defn_name` on `target_module`'s symbol
    // table with `ast: Some(_)` and `got_slot: Some(_)` (Wave 0 invariant).
    // S69 Submission 35: `ModuleEntry::Def.ast` is now `DefnVariant` (no
    // `name` field); the codegen `names` array is keyed off the already-
    // extracted `defn_name`, so the prior `Defn` reconstruction is dropped.
    let tc_modules = symbol_tables;
    ensure_typecheck_product(typecheck_products, target_module);
    let names = [defn_name.clone()];
    inline_jit_codegen_for_names(
        target_module,
        &names,
        tc_modules,
        None,
        &[],
        shared_state,
    )?;

    Ok(())
}

/// Compile a single macro clause from the resolver's raw references (no
/// `&mut ModuleCompiler`). Thin adapter over [`compile_macro_clause_core`].
///
/// `check_state` / `accumulator` / `next_type_id` are vestigial under the
/// collapsed `check_forms` surface (kept for source-compat with the resolver
/// call site). `module_aliases` / `prelude_fallback` derive from `shared_state`
/// — when absent (unit-test paths) an empty leaked default is a safe stand-in
/// (macro clause bodies use qualified `macros/*` refs, never aliases or the
/// prelude bare-name fallback).
#[allow(clippy::too_many_arguments)]
pub(super) fn compile_macro_clause_with_state(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    next_type_id: &std::sync::atomic::AtomicU32,
    check_state: &mut CheckState,
    target_module: &ModuleFullPath,
    macro_name: &Symbol,
    clause_idx: usize,
    clause: &cranelisp_frontend::MacroClause,
    span: Span,
    accumulator: &mut ModuleCheckAccumulator,
    typecheck_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    shared_state: Option<&crate::session_v4::SharedState>,
) -> Result<(), CranelispError> {
    let _ = (check_state, accumulator, next_type_id);
    let module_aliases: &cranelisp_types::ModuleAliases = match shared_state {
        Some(s) => &s.module_aliases,
        None => Box::leak(Box::new(cranelisp_types::ModuleAliases::default())),
    };
    let prelude_fallback: &cranelisp_typecheck::PreludeFallback = match shared_state {
        Some(s) => &s.prelude_fallback,
        None => Box::leak(Box::new(cranelisp_typecheck::PreludeFallback::default())),
    };
    compile_macro_clause_core(
        symbol_tables,
        module_aliases,
        prelude_fallback,
        target_module,
        macro_name,
        clause_idx,
        clause,
        span,
        typecheck_products,
        shared_state,
    )
}
