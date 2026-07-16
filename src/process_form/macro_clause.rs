//! Macro-clause compiler (S87 §1.1 extraction from `process_form.rs`).
//!
//! The SINGLE clause-compiler implementation (`compile_macro_clause_core`),
//! taking a [`MacroClauseEnv`] of the threaded references. Both callers build
//! the env from their own sources: the resolver path (`compile_macro_with_state`
//! in `macro_resolution.rs`, raw refs + shared-state→aliases derivation) and the
//! `_inline` adapter (the `&mut ModuleCompiler` Pass-2 path, also in
//! `macro_resolution.rs`, sourcing from `ctx`). This module is the **codegen**
//! of a clause
//! (synthesize → expand-qq → build → check → `inline_jit_codegen_for_names`),
//! distinct from `macro_resolution`'s *recognize/drive* concern
//! (`src/CLAUDE.md §"Macro-clause single implementation"`).

use cranelisp_types::{
    CranelispError, ErrorLocation, ModuleFullPath, Span, Symbol, TopLevel,
};

use crate::worker::{
    build_program_compat, check_program_compat_no_gap, ensure_typecheck_product,
    inline_jit_codegen_for_names,
};

/// The session/table + resolution environment threaded through on-demand
/// macro-clause compilation. Groups the cohesive reference set (module symbol
/// tables, the module-alias + prelude-fallback resolution scope, the per-module
/// typecheck products, and the optional live session) so the clause compiler
/// stays under the 8-param cap (Principle 6 — complexity has a budget). Each
/// entry shape (`compile_macro_clause_inline` from `&mut ModuleCompiler`, the
/// resolver's `compile_macro_with_state` from raw refs) builds the env from its
/// own reference sources; the values threaded are unchanged from the former
/// flat parameter lists.
pub(super) struct MacroClauseEnv<'a> {
    pub symbol_tables:
        &'a dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    pub module_aliases: &'a cranelisp_types::ModuleAliases,
    pub prelude_fallback: &'a cranelisp_typecheck::PreludeFallback,
    pub typecheck_products:
        &'a dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    pub shared_state: Option<&'a crate::session_v4::SharedState>,
}

/// Compile a single macro clause — the SINGLE implementation shared by both
/// entry shapes (FIXME 0109 Wave D collapse).
///
/// Post-Decision-44 the resolver path (`compile_macro_with_state`, raw refs)
/// and the `_inline` (`&mut ModuleCompiler`, Pass-2) clause compilers had
/// byte-identical bodies — the only difference was where the references came
/// from. This core takes them as a [`MacroClauseEnv`]; each caller builds the
/// env from its own reference sources. No behavioural change: each passes
/// exactly the references its former body used (the resolver path's
/// shared-state→aliases/prelude resolution, incl. the unit-test leaked-default
/// fallback, lives in the caller, unchanged).
pub(super) fn compile_macro_clause_core(
    env: &MacroClauseEnv<'_>,
    target_module: &ModuleFullPath,
    macro_name: &Symbol,
    clause_idx: usize,
    clause: &cranelisp_frontend::MacroClause,
    span: Span,
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
        env.symbol_tables,
        env.module_aliases,
        env.prelude_fallback,
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
    let tc_modules = env.symbol_tables;
    ensure_typecheck_product(env.typecheck_products, target_module);
    let names = [defn_name.clone()];
    inline_jit_codegen_for_names(
        target_module,
        &names,
        tc_modules,
        None,
        &[],
        env.shared_state,
    )?;

    Ok(())
}
