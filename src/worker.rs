// Worker functions for the v4 scheduler-driven pipeline (Steps 3-5).
//
// `process_module_forms` — drives two-pass typecheck for a single module,
//   with per-sexp macro expansion interleaved in Pass 2 (Step 4).
//   Lazily discovers dependencies (imports, prelude, platform) in Step 5.
// `codegen_module_symbols` — post-typecheck codegen sweep.
// `priority_worker_loop` — dispatches work items from the scheduler.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use cranelisp_types::{
    CheckResult, CranelispError, DefKind, Defn, ExportSpec, ImportNames, ImportSpec,
    MacroClauseInfo, ModuleEntry, ModuleFullPath, ModuleStrategy,
    PlatformSpec, PrimitiveKind, Sexp, Span, Symbol, TopLevel, Type, Visibility,
};

use cranelisp_typecheck::{CheckPass, CheckState, ModuleCheckAccumulator};

use crate::expander::{
    self, MacroClauseEntry, MacroEntry, MacroResolver,
};
use crate::pipeline::compile_and_register_defn_shared;
use crate::platform_registry::PlatformRegistry;
use crate::scheduler::{CompileScheduler, PriorityWork};

// ---------------------------------------------------------------------------
// ModuleCompiler — bundled worker parameters (G-1)
// ---------------------------------------------------------------------------

/// Shared context for the priority worker loop and process_module_forms.
///
/// TypeChecker state (symbol_tables, next_type_id) lives on SharedState.
/// Workers create `TypeCheckEnv` on the stack from these references.
/// PlatformRegistry remains `&mut` because `register()` needs mutation
/// during platform form processing.
pub struct ModuleCompiler<'a> {
    pub symbol_tables: &'a dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    pub next_type_id: &'a std::sync::atomic::AtomicU32,
    /// Per-invocation typecheck state. For REPL: extracted from SharedState.repl_check_state.
    /// For batch workers: created fresh per module.
    pub check_state: CheckState,
    /// Current module path. Mirrors check_state.current_module (which is pub(crate)).
    /// Updated alongside check_state by set_current_module().
    pub current_module: ModuleFullPath,
    pub scheduler: &'a CompileScheduler,
    pub platform_registry: &'a mut PlatformRegistry,
    /// Per-module typecheck products (GOT tables).
    pub typecheck_products: &'a dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    /// Per-module codegen products. Workers write Code directly here.
    pub codegen_products: &'a dashmap::DashMap<ModuleFullPath, crate::session_v4::CodegenProduct>,
    /// Per-symbol introspection data (REPL slash commands). None in batch mode.
    pub introspection: Option<&'a dashmap::DashMap<cranelisp_types::FQSymbol, crate::session_v4::Introspection>>,
    pub lib_dirs: &'a [PathBuf],
    pub platform_dirs: &'a [PathBuf],
    pub project_root: &'a Path,
    /// Optional reference to v4 shared state for cache-hit loading and
    /// codegen input stashing for nice workers.
    /// None for REPL contexts where caching is not used.
    pub shared_state: Option<&'a crate::session_v4::SharedState>,
}

impl<'a> ModuleCompiler<'a> {
    /// Create a TypeCheckEnv borrowing the shared state.
    pub fn tc_env(&self) -> cranelisp_typecheck::TypeCheckEnv<'_> {
        cranelisp_typecheck::TypeCheckEnv::new(self.symbol_tables, self.next_type_id)
    }

    /// Set the current module on both the check_state and the mirror field.
    pub fn set_current_module(&mut self, module: ModuleFullPath) {
        self.tc_env().ensure_module_exists(&module);
        // CheckState.current_module is pub(crate) — use CheckState::new to replace.
        // We create a new CheckState with the new module and copy over the needed fields.
        // For now, we just create a new one (batch mode creates fresh per module).
        // REPL mode preserves state through the repl_check_state mutex.
        self.check_state = CheckState::new(module.clone());
        self.current_module = module;
    }
}

// ---------------------------------------------------------------------------
// SessionCompilationEnv — CompilationEnv backed by TC + GOT registry
// ---------------------------------------------------------------------------

/// Implementation of `CompilationEnv` that reads live from the TypeChecker's
/// module symbol tables and per-module GOT tables from typecheck products.
pub struct SessionCompilationEnv<'a> {
    /// Reference to TC's per-module symbol tables (DashMap).
    pub tc_modules: &'a dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    /// Per-module typecheck products (GOT tables live here).
    pub typecheck_products: &'a dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    /// The module currently being compiled.
    pub current_module: ModuleFullPath,
}

impl cranelisp_backend::compiler::CompilationEnv for SessionCompilationEnv<'_> {
    fn resolve_got(&self, name: &Symbol) -> Option<(i64, usize)> {
        // 1. Try current module first (catches local defs, trait impls, mono names).
        if let Some(result) = self.resolve_in_module(&self.current_module, name.as_ref(), 0) {
            return Some(result);
        }

        // 2. Qualified "module/name" → split, look up target module.
        // Only split on '/' if the name is truly module-qualified (not a mangled
        // trait method like "Num./$Int" where '/' is part of the method name).
        if let Some(slash) = name.as_ref().find('/') {
            let module_part = &name.as_ref()[..slash];
            let bare_name = &name.as_ref()[slash + 1..];
            if !module_part.is_empty() && !bare_name.is_empty() {
                // Try child-of-current first (submodule reference)
                let child_path = ModuleFullPath::from(
                    format!("{}.{}", self.current_module, module_part),
                );
                if let Some(result) = self.resolve_in_module(&child_path, bare_name, 0) {
                    return Some(result);
                }
                // Fall back to absolute module path
                let abs_path = ModuleFullPath::from(module_part);
                if let Some(result) = self.resolve_in_module(&abs_path, bare_name, 0) {
                    return Some(result);
                }
            }
        }

        // 3. Global fallback: search all modules for the name.
        // Handles mangled trait methods (e.g., "Classify.classify$Color") that
        // are defined in a dependency module but referenced by the mangled name
        // in method resolution without an explicit import.
        for entry in self.tc_modules.iter() {
            if *entry.key() == self.current_module {
                continue; // Already checked above.
            }
            if let Some(result) = self.resolve_in_module(entry.key(), name.as_ref(), 0) {
                return Some(result);
            }
        }

        None
    }

    fn resolve_got_module(&self, name: &Symbol) -> Option<(ModuleFullPath, usize)> {
        // 1. Try current module first.
        if let Some(result) = self.resolve_module_slot(&self.current_module, name.as_ref(), 0) {
            return Some(result);
        }

        // 2. Qualified "module/name" → split.
        if let Some(slash) = name.as_ref().find('/') {
            let module_part = &name.as_ref()[..slash];
            let bare_name = &name.as_ref()[slash + 1..];
            if !module_part.is_empty() && !bare_name.is_empty() {
                let child_path = ModuleFullPath::from(
                    format!("{}.{}", self.current_module, module_part),
                );
                if let Some(result) = self.resolve_module_slot(&child_path, bare_name, 0) {
                    return Some(result);
                }
                let abs_path = ModuleFullPath::from(module_part);
                if let Some(result) = self.resolve_module_slot(&abs_path, bare_name, 0) {
                    return Some(result);
                }
            }
        }

        // 3. Global fallback: search all modules.
        for entry in self.tc_modules.iter() {
            if *entry.key() == self.current_module {
                continue;
            }
            if let Some(result) = self.resolve_module_slot(entry.key(), name.as_ref(), 0) {
                return Some(result);
            }
        }

        None
    }

    fn func_arity(&self, name: &Symbol) -> Option<usize> {
        // 1. Try current module first.
        if let Some(arity) = self.arity_in_module(&self.current_module, name.as_ref(), 0) {
            return Some(arity);
        }

        // 2. Qualified "module/name" → split.
        if let Some(slash) = name.as_ref().find('/') {
            let module_part = &name.as_ref()[..slash];
            let bare_name = &name.as_ref()[slash + 1..];
            if !module_part.is_empty() && !bare_name.is_empty() {
                let child_path = ModuleFullPath::from(
                    format!("{}.{}", self.current_module, module_part),
                );
                if let Some(arity) = self.arity_in_module(&child_path, bare_name, 0) {
                    return Some(arity);
                }
                let abs_path = ModuleFullPath::from(module_part);
                if let Some(arity) = self.arity_in_module(&abs_path, bare_name, 0) {
                    return Some(arity);
                }
            }
        }

        // 3. Global fallback: search all modules.
        for entry in self.tc_modules.iter() {
            if *entry.key() == self.current_module {
                continue;
            }
            if let Some(arity) = self.arity_in_module(entry.key(), name.as_ref(), 0) {
                return Some(arity);
            }
        }

        None
    }
}

impl SessionCompilationEnv<'_> {
    /// Resolve a bare name in a specific module to (got_base, slot).
    /// Follows Import chains with depth limit.
    fn resolve_in_module(&self, module: &ModuleFullPath, name: &str, depth: usize) -> Option<(i64, usize)> {
        if depth > 10 { return None; }
        let st = self.tc_modules.get(module)?;
        let entry = st.get(name)?;
        match entry {
            ModuleEntry::Def { got_slot: Some(slot), .. } => {
                let tp = self.typecheck_products.get(module)?;
                let got_base = tp.got.base_ptr() as i64;
                Some((got_base, *slot))
            }
            ModuleEntry::Import { source } => {
                let source_module = source.module.clone();
                let source_symbol = source.symbol.clone();
                drop(st); // release DashMap guard before recursive lookup
                self.resolve_in_module(&source_module, source_symbol.as_ref(), depth + 1)
            }
            ModuleEntry::Reexport { source } => {
                let source_module = source.module.clone();
                let source_symbol = source.symbol.clone();
                drop(st);
                self.resolve_in_module(&source_module, source_symbol.as_ref(), depth + 1)
            }
            _ => None,
        }
    }

    /// Resolve a bare name in a specific module to (defining_module, slot).
    /// Follows Import chains with depth limit. Returns the module that defines
    /// the function (for GOT data symbol lookup).
    fn resolve_module_slot(&self, module: &ModuleFullPath, name: &str, depth: usize) -> Option<(ModuleFullPath, usize)> {
        if depth > 10 { return None; }
        let st = self.tc_modules.get(module)?;
        let entry = st.get(name)?;
        match entry {
            ModuleEntry::Def { got_slot: Some(slot), .. } => {
                Some((module.clone(), *slot))
            }
            ModuleEntry::Import { source } => {
                let source_module = source.module.clone();
                let source_symbol = source.symbol.clone();
                drop(st);
                self.resolve_module_slot(&source_module, source_symbol.as_ref(), depth + 1)
            }
            ModuleEntry::Reexport { source } => {
                let source_module = source.module.clone();
                let source_symbol = source.symbol.clone();
                drop(st);
                self.resolve_module_slot(&source_module, source_symbol.as_ref(), depth + 1)
            }
            _ => None,
        }
    }

    /// Look up arity for a bare name in a specific module. Follows Import chains.
    fn arity_in_module(&self, module: &ModuleFullPath, name: &str, depth: usize) -> Option<usize> {
        if depth > 10 { return None; }
        let st = self.tc_modules.get(module)?;
        let entry = st.get(name)?;
        match entry {
            ModuleEntry::Def { param_names, .. } => Some(param_names.len()),
            ModuleEntry::Import { source } => {
                let source_module = source.module.clone();
                let source_symbol = source.symbol.clone();
                drop(st);
                self.arity_in_module(&source_module, source_symbol.as_ref(), depth + 1)
            }
            ModuleEntry::Reexport { source } => {
                let source_module = source.module.clone();
                let source_symbol = source.symbol.clone();
                drop(st);
                self.arity_in_module(&source_module, source_symbol.as_ref(), depth + 1)
            }
            _ => None,
        }
    }

    /// Collect all JIT symbols needed to compile a module.
    ///
    /// Scans the module's symbol table to find:
    /// - Platform function pointers (from PlatformRegistry, for PlatformEffect primitives)
    /// - GOT base pointers (for each referenced module, including self)
    ///
    /// Collect JIT symbols and GOT data definitions for a module compilation.
    ///
    /// Returns:
    /// - `jit_symbols`: platform function pointers for `Jit::new_with_symbols`
    /// - `got_data_defs`: `(name, got_base_ptr)` pairs for GOT literal pool entries
    ///   that must be defined as data in the JIT module (8 bytes each)
    #[allow(clippy::type_complexity)]
    pub fn collect_jit_setup_for_module(
        &self,
        platform_registry: &crate::platform_registry::PlatformRegistry,
    ) -> (Vec<(String, *const u8)>, Vec<(String, *const u8)>) {
        let mut jit_symbols = Vec::new();
        let mut got_data_defs = Vec::new();

        if let Some(st) = self.tc_modules.get(&self.current_module) {
            for (_name, entry) in st.all_symbols() {
                match entry {
                    // Direct platform function definition.
                    ModuleEntry::Def { kind, .. } => {
                        if let DefKind::Primitive {
                            primitive_kind: PrimitiveKind::PlatformEffect,
                            jit_name: Some(jit_name),
                        } = kind.as_ref()
                            && let Some(ptr) = platform_registry.fn_ptr_by_jit_name(jit_name) {
                                jit_symbols.push((jit_name.0.clone(), ptr));
                            }
                    }
                    // Import that may resolve to a platform function.
                    ModuleEntry::Import { source } => {
                        if let Some(source_table) = self.tc_modules.get(&source.module)
                            && let Some(ModuleEntry::Def { kind, .. }) =
                                source_table.get(source.symbol.as_ref())
                                && let DefKind::Primitive {
                                    primitive_kind: PrimitiveKind::PlatformEffect,
                                    jit_name: Some(jit_name),
                                } = kind.as_ref()
                                    && let Some(ptr) = platform_registry.fn_ptr_by_jit_name(jit_name) {
                                        jit_symbols.push((jit_name.0.clone(), ptr));
                                    }
                    }
                    _ => {}
                }
            }
        }

        // GOT literal pool entries: each module's GOT base address is defined
        // as 8 bytes of data in the JIT module. The code loads from these entries
        // to get GOT base addresses for indirect calls.
        for entry in self.typecheck_products.iter() {
            let name = cranelisp_backend::compiler::got_data_symbol_name(entry.key());
            got_data_defs.push((name, entry.value().got.base_ptr()));
        }

        (jit_symbols, got_data_defs)
    }
}

// ---------------------------------------------------------------------------
// SymbolTableMacroResolver — on-demand macro resolution from symbol tables
// ---------------------------------------------------------------------------

/// Macro resolver backed by the TypeChecker symbol tables and CodegenProduct DashMaps.
///
/// Walks the symbol table on each name encounter, follows Import/Reexport chains
/// to the defining module, checks codegen products there, compiles on demand if
/// needed, and returns the MacroEntry.
///
/// Uses the `take_state`/`restore_state` pattern: the caller extracts `CheckState`
/// from the `TypeChecker` before creating this resolver, so the resolver holds
/// `&TypeChecker` (shared ref for DashMap reads) and `&mut CheckState` separately.
struct SymbolTableMacroResolver<'a> {
    /// Per-module symbol tables (DashMap, interior mutability).
    symbol_tables: &'a dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    /// Monotonic counter for fresh type variable IDs.
    next_type_id: &'a std::sync::atomic::AtomicU32,
    /// CheckState — needed for on-demand compilation (check_form_with_state).
    check_state: &'a mut CheckState,
    /// Current module path (starting point for symbol lookup).
    current_module: ModuleFullPath,
    /// Per-module codegen products (DashMap, interior mutability).
    codegen_products: &'a dashmap::DashMap<ModuleFullPath, crate::session_v4::CodegenProduct>,
    /// Per-module typecheck products (DashMap, interior mutability).
    typecheck_products: &'a dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    /// Accumulator for check_form_with_state during on-demand compilation.
    accumulator: &'a mut ModuleCheckAccumulator,
    /// Platform registry — needed for JIT setup during on-demand compilation.
    platform_registry: &'a mut PlatformRegistry,
    /// Scheduler — for notify_inmem_codegen_complete after on-demand compilation.
    scheduler: &'a CompileScheduler,
    /// Defining modules for macros that were resolved during expansion.
    /// Used to qualify bare symbols in expanded output (cross-module hygiene).
    macro_defining_modules: Vec<ModuleFullPath>,
}

impl MacroResolver for SymbolTableMacroResolver<'_> {
    fn resolve_macro(
        &mut self,
        name: &str,
        span: Span,
    ) -> Result<Option<MacroEntry>, CranelispError> {
        // Step 1: Walk symbol table to find the defining module and clause infos.
        let resolved = resolve_macro_definition(
            self.symbol_tables, &self.current_module, name, 16,
        );
        let (defining_module, clauses, docstring) = match resolved {
            Some(r) => r,
            None => return Ok(None),
        };

        // Record the defining module for post-expansion symbol qualification.
        if defining_module != self.current_module {
            self.macro_defining_modules.push(defining_module.clone());
        }

        // Step 2: Check if all clauses are compiled. If so, build entry directly.
        let macro_sym = Symbol::from(name);
        let all_compiled = clauses.iter().enumerate().all(|(idx, _)| {
            let clause_name = macro_clause_jit_name(&macro_sym, idx);
            has_code_ptr(self.codegen_products, &defining_module, &clause_name)
        });

        if !all_compiled {
            // Step 3: Compile inline. We need DefmacroInfo to drive compilation.
            // Look up the sexp from the defining module's symbol table.
            let macro_sexp = resolve_macro_sexp_from(self.symbol_tables, &defining_module, name);
            if let Some(sexp) = macro_sexp {
                let info = cranelisp_frontend::parse_defmacro(&sexp)?;
                compile_macro_with_state(
                    self.symbol_tables, self.next_type_id, self.check_state, &defining_module,
                    &info, span, self.accumulator,
                    self.codegen_products, self.typecheck_products,
                    self.platform_registry, self.scheduler,
                )?;
            } else {
                // No sexp available — cannot compile. Return None.
                return Ok(None);
            }
        }

        // Step 4: Build MacroEntry from code pointers.
        build_macro_entry_from_clauses(
            self.codegen_products, &defining_module, &macro_sym, &clauses, docstring,
        )
    }
}

/// Follow Import/Reexport chains to find the defining module, clauses, and docstring.
///
/// Generic recursive chain walker with depth limit to prevent infinite loops.
pub(crate) fn resolve_macro_definition(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    module: &ModuleFullPath,
    name: &str,
    max_depth: usize,
) -> Option<(ModuleFullPath, Vec<MacroClauseInfo>, Option<String>)> {
    if max_depth == 0 {
        return None;
    }
    let table = symbol_tables.get(module)?;
    let entry = table.get(name)?;
    match entry {
        ModuleEntry::Macro { clauses, docstring, .. } => {
            Some((module.clone(), clauses.clone(), docstring.clone()))
        }
        ModuleEntry::Import { source } | ModuleEntry::Reexport { source, .. } => {
            let next_mod = source.module.clone();
            let next_sym: String = source.symbol.as_ref().to_string();
            drop(table); // Release DashMap guard before recursing.
            resolve_macro_definition(symbol_tables, &next_mod, &next_sym, max_depth - 1)
        }
        _ => None,
    }
}

/// Resolve a macro's sexp from the defining module's symbol table.
///
/// Unlike `resolve_macro_definition`, this specifically looks up the sexp
/// stored on the `ModuleEntry::Macro` in the defining module.
fn resolve_macro_sexp_from(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    defining_module: &ModuleFullPath,
    name: &str,
) -> Option<Sexp> {
    let table = symbol_tables.get(defining_module)?;
    match table.get(name)? {
        ModuleEntry::Macro { sexp, .. } => sexp.clone(),
        _ => None,
    }
}

/// Compile a macro's clauses using the `_with_state` API (no &mut TypeChecker needed).
///
/// This is the on-demand compilation path for the resolver. Uses
/// `check_form_with_state` and `merge_form_result_with_state` which take
/// `&self` on TypeChecker + `&mut CheckState`.
#[allow(clippy::too_many_arguments)]
fn compile_macro_with_state(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    next_type_id: &std::sync::atomic::AtomicU32,
    check_state: &mut CheckState,
    target_module: &ModuleFullPath,
    info: &cranelisp_frontend::DefmacroInfo,
    span: Span,
    accumulator: &mut ModuleCheckAccumulator,
    codegen_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::CodegenProduct>,
    typecheck_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    platform_registry: &PlatformRegistry,
    scheduler: &CompileScheduler,
) -> Result<(), CranelispError> {
    let total_clauses = info.clauses.len();
    for (clause_idx, clause) in info.clauses.iter().enumerate() {
        let clause_name = macro_clause_jit_name(&info.name, clause_idx);
        if has_code_ptr(codegen_products, target_module, &clause_name) {
            continue;
        }

        compile_macro_clause_with_state(
            symbol_tables, next_type_id, check_state, target_module,
            &info.name, clause_idx, clause, span,
            accumulator, codegen_products, typecheck_products,
            platform_registry,
        )?;
        let is_last = clause_idx + 1 == total_clauses;
        scheduler.notify_inmem_codegen_complete(target_module, &clause_name, is_last);
    }
    Ok(())
}

/// Compile a single macro clause using the `_with_state` API.
///
/// Mirrors `compile_macro_clause_inline` but uses `&TypeChecker` + `&mut CheckState`
/// instead of `&mut ModuleCompiler`.
#[allow(clippy::too_many_arguments)]
fn compile_macro_clause_with_state(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    next_type_id: &std::sync::atomic::AtomicU32,
    check_state: &mut CheckState,
    target_module: &ModuleFullPath,
    macro_name: &Symbol,
    clause_idx: usize,
    clause: &cranelisp_frontend::MacroClause,
    span: Span,
    accumulator: &mut ModuleCheckAccumulator,
    codegen_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::CodegenProduct>,
    typecheck_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    platform_registry: &PlatformRegistry,
) -> Result<(), CranelispError> {
    // Step 1: Synthesize the defn Sexp.
    let synth_sexp = cranelisp_frontend::synthesize_macro_clause_defn(
        macro_name.as_ref(), clause_idx, clause, span,
    );

    // Step 2: Expand quasiquotes.
    let expanded_sexp = cranelisp_frontend::expand_quasiquotes(&synth_sexp)?;

    // Step 3: Build AST.
    let program = cranelisp_frontend::build_program(&[expanded_sexp])?;

    // Step 4: Typecheck using _with_state API (Register + CheckBody).
    for form in &program {
        let result = cranelisp_typecheck::TypeCheckEnv::new(symbol_tables, next_type_id).check_form(
            target_module, form, CheckPass::Register, check_state, accumulator,
        )?;
        cranelisp_typecheck::TypeCheckEnv::new(symbol_tables, next_type_id).merge_form_result(target_module, check_state, accumulator, result);
    }
    for form in &program {
        let result = cranelisp_typecheck::TypeCheckEnv::new(symbol_tables, next_type_id).check_form(
            target_module, form, CheckPass::CheckBody, check_state, accumulator,
        )?;
        cranelisp_typecheck::TypeCheckEnv::new(symbol_tables, next_type_id).merge_form_result(target_module, check_state, accumulator, result);
    }

    // Build a CheckResult from the accumulator for codegen.
    let check = build_check_from_accumulator_tc(symbol_tables, accumulator);

    // Step 5: Extract the defn and compile it.
    let defn = program
        .iter()
        .find_map(|tl| match tl {
            TopLevel::Defn(d) => Some(d),
            _ => None,
        })
        .ok_or_else(|| CranelispError::MacroError {
            message: format!(
                "macro clause {} for '{}' produced no defn",
                clause_idx, macro_name
            ),
            span,
        })?;

    // Compile macro clause with dealloc disabled.
    let tc_modules = symbol_tables;
    let env_impl = SessionCompilationEnv {
        tc_modules,
        typecheck_products,
        current_module: target_module.clone(),
    };
    let env: &dyn cranelisp_backend::compiler::CompilationEnv = &env_impl;
    ensure_typecheck_product(typecheck_products, target_module);
    let module_got = typecheck_products.get(target_module)
        .expect("invariant: just ensured typecheck product exists")
        .got.clone();
    let (macro_jit_symbols, macro_got_data_defs) =
        env_impl.collect_jit_setup_for_module(platform_registry);
    pre_register_got_slots_in_tc(tc_modules, target_module, &program, &check);
    compile_and_register_defn_shared(
        &macro_jit_symbols, &macro_got_data_defs, defn, &check, env, &module_got,
        codegen_products, None, target_module, true, symbol_tables,
    )?;

    Ok(())
}

/// Build a CheckResult from the accumulator for codegen (TC shared-ref version).
fn build_check_from_accumulator_tc(
    _symbol_tables: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    accumulator: &ModuleCheckAccumulator,
) -> CheckResult {
    CheckResult {
        method_resolutions: accumulator.method_resolutions.clone(),
        constrained_fn_names: accumulator.constrained_fn_names.clone(),
        mono_defns: Vec::new(),
        expr_types: accumulator.expr_types.clone(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
        display: None,
    }
}

/// Build a MacroEntry from compiled clause code pointers.
fn build_macro_entry_from_clauses(
    codegen_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::CodegenProduct>,
    defining_module: &ModuleFullPath,
    macro_sym: &Symbol,
    clauses: &[MacroClauseInfo],
    docstring: Option<String>,
) -> Result<Option<MacroEntry>, CranelispError> {
    let mut compiled_clauses = Vec::new();
    for (idx, clause_info) in clauses.iter().enumerate() {
        let clause_name = macro_clause_jit_name(macro_sym, idx);
        match get_code_ptr(codegen_products, defining_module, &clause_name) {
            Some(ptr) => {
                compiled_clauses.push(MacroClauseEntry {
                    func_ptr: ptr,
                    params: clause_info.params.clone(),
                    rest_param: clause_info.rest_param.clone(),
                });
            }
            None => return Ok(None), // Clause not compiled — skip this macro.
        }
    }
    if compiled_clauses.is_empty() {
        return Ok(None);
    }
    Ok(Some(MacroEntry {
        clauses: compiled_clauses,
        docstring,
    }))
}

/// Scope the resolver's borrows to just the expansion phase.
///
/// Creates a SymbolTableMacroResolver, runs expand_sexp_recursive,
/// drops the resolver, returns the expanded sexp. After this returns,
/// ctx and accumulator are available for the caller to use freely.
fn try_expand_sexp(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexp: &Sexp,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<Option<Sexp>, CranelispError> {
    // No need to extract/restore CheckState — TypeCheckEnv borrows are
    // separate from CheckState. The resolver holds &DashMap (from tc_env)
    // and &mut CheckState separately.
    let (result, defining_modules) = {
        let mut resolver = SymbolTableMacroResolver {
            symbol_tables: ctx.symbol_tables,
            next_type_id: ctx.next_type_id,
            check_state: &mut ctx.check_state,
            current_module: module.clone(),
            codegen_products: ctx.codegen_products,
            typecheck_products: ctx.typecheck_products,
            accumulator,
            platform_registry: ctx.platform_registry,
            scheduler: ctx.scheduler,
            macro_defining_modules: Vec::new(),
        };

        let r = expander::expand_sexp_recursive(sexp.clone(), &mut resolver, 0);
        let dms = std::mem::take(&mut resolver.macro_defining_modules);
        (r, dms)
        // resolver dropped here, releasing all borrows on check_state
    };

    let expanded = result?;

    if expanded == *sexp {
        Ok(None)
    } else {
        // Qualify bare symbols from defining modules (cross-module macro hygiene).
        let qualified = if defining_modules.is_empty() {
            expanded
        } else {
            qualify_expanded_sexp(ctx.symbol_tables, module, &defining_modules, expanded)
        };
        Ok(Some(qualified))
    }
}

/// Qualify bare symbols in macro-expanded sexp with their defining module paths.
///
/// After macro expansion, bare symbol references like `make-seven` may refer to
/// symbols in the macro's defining module. These must be qualified (e.g.,
/// `helper/make-seven`) so the consuming module's typechecker can resolve them.
///
/// Only qualifies symbols that:
/// - Are bare (no `/` already) and not type annotations (`:` prefix)
/// - Are found in a defining module's symbol table
/// - Are NOT already available in the current module
fn qualify_expanded_sexp(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    current_module: &ModuleFullPath,
    defining_modules: &[ModuleFullPath],
    sexp: Sexp,
) -> Sexp {
    match sexp {
        Sexp::Symbol(ref name, span) => {
            // Skip already-qualified names, type annotations, special names
            if name.contains('/') || name.starts_with(':') || name.starts_with('_') {
                return sexp;
            }
            // Skip if the symbol is already available in the current module
            if let Some(table) = symbol_tables.get(current_module)
                && table.get(name).is_some() {
                    return sexp;
                }
            // Check defining modules for this symbol
            for def_mod in defining_modules {
                if let Some(table) = symbol_tables.get(def_mod)
                    && let Some(entry) = table.get(name) {
                        // Follow imports to find the true source module for qualification
                        let qual_module = match entry {
                            ModuleEntry::Import { source } => &source.module,
                            ModuleEntry::Reexport { source, .. } => &source.module,
                            _ => def_mod,
                        };
                        let qualified = format!("{}/{}", qual_module.as_ref(), name);
                        return Sexp::Symbol(qualified, span);
                    }
            }
            sexp
        }
        Sexp::List(children, span) => {
            // Don't qualify the head of special forms like defn, let, etc.
            // But DO qualify function call targets and their arguments.
            let qualified_children: Vec<Sexp> = children
                .into_iter()
                .map(|c| qualify_expanded_sexp(symbol_tables, current_module, defining_modules, c))
                .collect();
            Sexp::List(qualified_children, span)
        }
        Sexp::Bracket(children, span) => {
            let qualified_children: Vec<Sexp> = children
                .into_iter()
                .map(|c| qualify_expanded_sexp(symbol_tables, current_module, defining_modules, c))
                .collect();
            Sexp::Bracket(qualified_children, span)
        }
        // Other sexp types (Int, Float, String, Bool) pass through unchanged.
        other => other,
    }
}

// ---------------------------------------------------------------------------
// ProcessResult — suspension-aware return type
// ---------------------------------------------------------------------------

/// Result of processing module forms. Either the module is fully typechecked,
/// or it blocked on a dependency and needs to be resumed later.
#[allow(clippy::large_enum_variant)]
pub enum ProcessResult {
    /// Module fully typechecked.
    Complete {
        check_result: CheckResult,
        program: Vec<TopLevel>,
    },
    /// Blocked on a dependency. Resume from the given form index.
    Blocked {
        form_index: usize,
        dep_module: ModuleFullPath,
        dep_sexps: Vec<Sexp>,
    },
}

/// Ensure a TypecheckProduct entry exists for a module, creating one with a
/// fresh GOT table if needed. GOT tables are allocated at module registration
/// time so their base addresses are stable before any codegen begins.
pub(crate) fn ensure_typecheck_product(
    typecheck_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    module: &ModuleFullPath,
) {
    typecheck_products.entry(module.clone()).or_insert_with(|| {
        crate::session_v4::TypecheckProduct {
            got: std::sync::Arc::new(cranelisp_backend::got::GotTable::new()),
            file_path: None,
            source_text: None,
        }
    });
}

// ---------------------------------------------------------------------------
// FormKind — per-sexp form classification for Pass 2
// ---------------------------------------------------------------------------

/// Classification of a top-level sexp for Pass 2 dispatch.
enum FormKind {
    Import(Vec<ImportSpec>),
    Export(Vec<ExportSpec>),
    Mod(cranelisp_types::ModDecl),
    Platform(PlatformSpec),
    Defmacro,
    Regular,
}

/// Classify a top-level sexp for Pass 2 dispatch.
///
/// Recognizes import/export/mod/platform/defmacro forms. Everything else
/// is Regular (defn, deftype, deftrait, impl, expr).
fn classify_form(sexp: &Sexp) -> Result<FormKind, CranelispError> {
    match sexp {
        Sexp::List(items, _span) if !items.is_empty() => {
            if let Sexp::Symbol(name, _) = &items[0] {
                match name.as_str() {
                    "import" => {
                        let specs = cranelisp_frontend::parse_import_sexp(sexp)?;
                        Ok(FormKind::Import(specs))
                    }
                    "export" => {
                        let specs = cranelisp_frontend::parse_export_sexp(sexp)?;
                        Ok(FormKind::Export(specs))
                    }
                    "mod" | "mod-" => {
                        let decl = cranelisp_frontend::parse_mod_sexp(sexp)?;
                        Ok(FormKind::Mod(decl))
                    }
                    "platform" => {
                        let spec = cranelisp_frontend::parse_platform_sexp(sexp)?;
                        Ok(FormKind::Platform(spec))
                    }
                    "defmacro" => Ok(FormKind::Defmacro),
                    _ => Ok(FormKind::Regular),
                }
            } else {
                Ok(FormKind::Regular)
            }
        }
        _ => Ok(FormKind::Regular),
    }
}

// ---------------------------------------------------------------------------
// BlockAction — import/mod handler result
// ---------------------------------------------------------------------------

/// Signals the Pass 2 loop whether to continue or block.
enum BlockAction {
    /// Continue processing the next form.
    Continue,
    /// Block: a dependency was discovered. Store state and return.
    Block {
        dep_module: ModuleFullPath,
        dep_sexps: Vec<Sexp>,
    },
}

// ---------------------------------------------------------------------------
// process_module_forms — two-pass per-form typecheck (C1)
// ---------------------------------------------------------------------------

/// Expand, build AST, and typecheck all forms in a module from pre-parsed sexps.
///
/// Drives the two-pass iteration required by Algorithm W:
/// - Pass 1 (Register): register type defs, trait decls, signatures.
///   Defmacro forms are parsed and registered in the module table.
/// - Pass 2 (CheckBody): per-sexp expand-then-check. Macro calls are
///   expanded inline (compiling macro deps on demand). Import/export/mod/
///   platform forms are handled lazily (Step 5).
///
/// On success, notifies the scheduler of each typechecked symbol and
/// calls `notify_typecheck_done`. On error, calls `notify_module_failed`.
///
/// `start_form_index`: the Pass 2 form to resume from (0 for fresh modules).
/// On resume, Pass 1 is skipped (already done).
///
/// `state`: per-module suspension state (accumulator, expanded_program, pass1_done).
/// May be a resumed state (saved across suspension) or freshly created.
pub fn process_module_forms(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexps: &[Sexp],
    start_form_index: usize,
    state: &mut ModuleSuspendState,
    strategy: ModuleStrategy,
) -> Result<ProcessResult, CranelispError> {
    let is_fresh = !state.pass1_done;

    if is_fresh && strategy == ModuleStrategy::Replace {
        // Set active module. Symbol table is preserved for slot reuse
        // and type-change detection.
        ctx.set_current_module(module.clone());
        // clear_module_for_replace_public is a no-op with stateless TC;
        // symbol table clearing happens through the module system.

        // Zero GOT slots and clear codegen artifacts for this module's
        // symbols. Slot assignments are preserved so re-compiled code
        // lands in the same slots.
        clear_module_codegen(ctx, module);

        // Prelude injection: inject (import [prelude [*]]) for non-prelude modules
        // unless the source explicitly references prelude in an import or export (§8.8.1).
        if let Some(result) = inject_prelude_if_needed(ctx, module, sexps)? {
            return Ok(result);
        }
    } else if is_fresh && strategy == ModuleStrategy::Additive {
        // Additive: just set the active module. Module state persists
        // from previous evals — no clear, no re-injection.
        ctx.set_current_module(module.clone());
    } else {
        // Resume: set active module (may have been changed by dep processing).
        ctx.set_current_module(module.clone());
    }

    // --- Pass 1: only on fresh start (not on resume after blocking) ---
    if is_fresh {
        // Pass 0: Process import/export/mod forms before Pass 1.
        // Imported symbols must be in scope before pass1_register checks
        // trait impl bodies. If a dependency isn't loaded yet, we block
        // and resume here later (pass1_done is still false).
        for (form_idx, sexp) in sexps.iter().enumerate() {
            match classify_form(sexp)? {
                FormKind::Import(specs) => {
                    // Record import specs for source regeneration (§15).
                    if let Some(shared) = ctx.shared_state {
                        let mut ms = shared.module_structures
                            .entry(module.clone())
                            .or_default();
                        ms.import_specs.extend(specs.iter().cloned());
                    }
                    match handle_import(ctx, module, specs)? {
                        BlockAction::Continue => {}
                        BlockAction::Block { dep_module, dep_sexps } => {
                            return Ok(ProcessResult::Blocked {
                                form_index: form_idx,
                                dep_module,
                                dep_sexps,
                            });
                        }
                    }
                }
                FormKind::Export(specs) => {
                    // Record export specs for source regeneration (§15).
                    if let Some(shared) = ctx.shared_state {
                        let mut ms = shared.module_structures
                            .entry(module.clone())
                            .or_default();
                        ms.export_specs.extend(specs.iter().cloned());
                    }
                    match handle_export(ctx, module, &specs)? {
                        BlockAction::Continue => {}
                        BlockAction::Block { dep_module, dep_sexps } => {
                            return Ok(ProcessResult::Blocked {
                                form_index: form_idx,
                                dep_module,
                                dep_sexps,
                            });
                        }
                    }
                }
                FormKind::Mod(decl) => {
                    // Record mod decl for source regeneration (§15).
                    if let Some(shared) = ctx.shared_state {
                        let mut ms = shared.module_structures
                            .entry(module.clone())
                            .or_default();
                        ms.mod_decls.push(decl.clone());
                    }
                    match handle_mod(ctx, module, &decl)? {
                        BlockAction::Continue => {}
                        BlockAction::Block { dep_module, dep_sexps } => {
                            return Ok(ProcessResult::Blocked {
                                form_index: form_idx,
                                dep_module,
                                dep_sexps,
                            });
                        }
                    }
                }
                FormKind::Platform(spec) => {
                    // Record platform spec for source regeneration (§15).
                    if let Some(shared) = ctx.shared_state {
                        let mut ms = shared.module_structures
                            .entry(module.clone())
                            .or_default();
                        ms.platform_specs.push(spec.clone());
                    }
                    handle_platform(ctx, module, &spec)?;
                }
                _ => {} // Regular, Defmacro — handled in Pass 2
            }
        }

        let (regular_sexps, macro_infos) = separate_macros(sexps)?;

        // Build AST for regular (non-macro) forms.
        let program = cranelisp_frontend::build_program(&regular_sexps)?;
        let working_program = wrap_exprs_as_defns(&program);

        pass1_register(ctx.symbol_tables, ctx.next_type_id, &mut ctx.check_state, module, &working_program, &mut state.accumulator)?;

        for (name, info, sexp) in &macro_infos {
            register_macro_in_module(ctx.symbol_tables, ctx.next_type_id, &mut ctx.check_state, module, name, info, sexp)?;
        }

        let defaults = register_default_methods(ctx.symbol_tables, ctx.next_type_id, &mut ctx.check_state, module, &mut state.accumulator)?;
        state.accumulator.default_method_defns = defaults;
        state.pass1_done = true;
    }

    // --- Pass 2: per-sexp expand-then-check, from start_form_index ---
    // expanded_program accumulates across suspensions via the caller.
    let pass2_result = pass2_check_bodies_with_expansion(
        ctx, module, sexps, start_form_index, &mut state.accumulator, &mut state.expanded_program,
    )?;

    match pass2_result {
        Pass2Result::Complete => {
            finalize_module(ctx, module, &mut state.expanded_program, &mut state.accumulator, strategy)
        }
    }
}

/// Separate defmacro forms from regular forms for Pass 1.
#[allow(clippy::type_complexity)]
fn separate_macros(
    sexps: &[Sexp],
) -> Result<(Vec<Sexp>, Vec<(Symbol, cranelisp_frontend::DefmacroInfo, Sexp)>), CranelispError> {
    let mut regular_sexps = Vec::new();
    let mut macro_infos = Vec::new();

    for sexp in sexps {
        if cranelisp_frontend::is_defmacro(sexp) {
            let info = cranelisp_frontend::parse_defmacro(sexp)?;
            macro_infos.push((info.name.clone(), info, sexp.clone()));
        } else {
            // Skip import/export/mod/platform in Pass 1 regular forms.
            // They don't contribute type signatures and are handled in Pass 2.
            match classify_form(sexp)? {
                FormKind::Import(_) | FormKind::Export(_) | FormKind::Mod(_) | FormKind::Platform(_) => {
                    // Skip — handled during Pass 2.
                }
                _ => {
                    regular_sexps.push(sexp.clone());
                }
            }
        }
    }
    Ok((regular_sexps, macro_infos))
}

/// Finalize a fully typechecked module: run post-passes and build CheckResult.
fn finalize_module(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    expanded_program: &[TopLevel],
    accumulator: &mut ModuleCheckAccumulator,
    strategy: ModuleStrategy,
) -> Result<ProcessResult, CranelispError> {
    let final_working = wrap_exprs_as_defns(expanded_program);

    // Check bodies of default method defns.
    let defaults_for_body: Vec<Defn> = accumulator.default_method_defns.clone();
    for defn in &defaults_for_body {
        let form = TopLevel::Defn(defn.clone());
        let result = cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id).check_form(module, &form, CheckPass::CheckBody, &mut ctx.check_state, accumulator)?;
        cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id).merge_form_result(module, &mut ctx.check_state, accumulator, result);
    }

    let mut check_result = cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id).finalize_check_result(
        module,
        &mut ctx.check_state,
        accumulator,
        &final_working,
        strategy,
    )?;

    check_result.display =
        cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id).compute_display_info_public(&ctx.check_state,expanded_program, &accumulator.defn_type_vars);

    // NOTE: notify_typecheck_done is NOT called here. The caller is
    // responsible for stashing CodegenInput and calling
    // notify_typecheck_done AFTER, so that nice workers cannot claim
    // the module before the stash is populated.

    let program = expanded_program.to_vec();

    Ok(ProcessResult::Complete {
        check_result,
        program,
    })
}

/// Register a defmacro in the module table (Pass 1).
///
/// Parses clause info and stores it as `ModuleEntry::Macro` with the
/// original sexp for later compilation. No codegen — deferred until
/// first use.
fn register_macro_in_module(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    _next_type_id: &std::sync::atomic::AtomicU32,
    _check_state: &mut CheckState,
    module: &ModuleFullPath,
    name: &Symbol,
    info: &cranelisp_frontend::DefmacroInfo,
    sexp: &Sexp,
) -> Result<(), CranelispError> {
    let clause_infos: Vec<MacroClauseInfo> = info
        .clauses
        .iter()
        .map(|c| MacroClauseInfo {
            params: c.fixed_params.clone(),
            rest_param: c.rest_param.clone(),
            source: None,
        })
        .collect();
    let visibility = if info.is_private {
        Visibility::Private
    } else {
        Visibility::Public
    };
    if let Some(mut table) = symbol_tables.get_mut(module) {
        table.insert(
            name.clone(),
            ModuleEntry::Macro {
                name: name.clone(),
                clauses: clause_infos,
                docstring: info.docstring.clone(),
                visibility,
                sexp: Some(sexp.clone()),
                source: None,
                callees: Vec::new(),
            },
        );
    }
    Ok(())
}

/// Internal result from Pass 2 — either complete or blocked.
/// The expanded program is accumulated in the caller's mutable Vec.
enum Pass2Result {
    /// All forms processed. Expanded program is in the caller's Vec.
    Complete,
    // Note: Import/export/mod/platform blocking is now handled in Pass 0.
    // Pass 2 no longer needs a Blocked variant.
}

/// Pass 2: per-sexp expand-then-check, with inline macro compilation
/// and lazy dependency discovery (Step 5).
///
/// Iterates sexps from `start_form_index`. For each:
/// - Import: discover dep, register with scheduler, block if needed.
/// - Export: register export metadata.
/// - Mod: register submodule (write inline body to disk if present).
/// - Platform: load DLL and register type signatures.
/// - Defmacro: skip (already registered in Pass 1).
/// - Regular: try expand, build AST, typecheck body.
fn pass2_check_bodies_with_expansion(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexps: &[Sexp],
    start_form_index: usize,
    accumulator: &mut ModuleCheckAccumulator,
    expanded_program: &mut Vec<TopLevel>,
) -> Result<Pass2Result, CranelispError> {
    for (_form_idx, sexp) in sexps.iter().enumerate().skip(start_form_index) {

        match classify_form(sexp)? {
            // Import/export/mod/platform forms are processed in Pass 0
            // (before Pass 1). By the time Pass 2 runs, these have already
            // been handled. Skip them here — they are no-ops in Pass 2.
            FormKind::Import(_)
            | FormKind::Export(_)
            | FormKind::Mod(_)
            | FormKind::Platform(_) => {}
            FormKind::Defmacro => {
                // Registered in Pass 1. Compile eagerly in Pass 2 so type errors
                // in the macro body are caught at definition time (not deferred
                // until the macro is first called).
                let info = cranelisp_frontend::parse_defmacro(sexp)?;
                compile_macro_if_needed(ctx, module, &info, sexp.span(), accumulator)?;
            }
            FormKind::Regular => {
                process_regular_form(
                    ctx, module, sexp, accumulator, expanded_program,
                )?;
            }
        }
    }
    Ok(Pass2Result::Complete)
}

/// Process a regular (non-module-declaration) form in Pass 2.
///
/// Tries macro expansion via the SymbolTableMacroResolver, builds AST,
/// registers any new signatures (for begin-spliced defns), then typechecks
/// the body. New macros from expansion (e.g. const/def) are registered in
/// the symbol table and become visible to the resolver for subsequent forms.
fn process_regular_form(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexp: &Sexp,
    accumulator: &mut ModuleCheckAccumulator,
    expanded_program: &mut Vec<TopLevel>,
) -> Result<(), CranelispError> {
    // Try macro expansion on the raw sexp.
    let effective_sexp = try_expand_sexp(ctx, module, sexp, accumulator)?;

    let sexp_to_build = match &effective_sexp {
        Some(expanded) => expanded,
        None => sexp,
    };

    let flattened = cranelisp_frontend::flatten_begin(sexp_to_build.clone());

    // Partition flattened forms: macro expansion (e.g. const, def) can produce
    // defmacro forms that must be routed through the macro pipeline, not the
    // AST builder which rejects them.
    let mut regular_sexps = Vec::new();
    for form in flattened {
        if cranelisp_frontend::is_defmacro(&form) {
            let info = cranelisp_frontend::parse_defmacro(&form)?;
            register_macro_in_module(ctx.symbol_tables, ctx.next_type_id, &mut ctx.check_state, module, &info.name, &info, &form)?;
            compile_macro_if_needed(ctx, module, &info, form.span(), accumulator)?;
        } else {
            regular_sexps.push(form);
        }
    }

    if regular_sexps.is_empty() {
        return Ok(());
    }

    let built = cranelisp_frontend::build_program(&regular_sexps)?;
    let working = wrap_exprs_as_defns(&built);

    // Register signatures for macro-expanded forms only. Non-expanded forms
    // were already registered in Pass 1 (pass1_register). Re-registering
    // causes "already defined" errors for traits.
    if effective_sexp.is_some() {
        for form in &working {
            let result = cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id).check_form(module, form, CheckPass::Register, &mut ctx.check_state, accumulator)?;
            cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id).merge_form_result(module, &mut ctx.check_state, accumulator, result);
        }
    }

    // Typecheck body for each form produced (Pass 2).
    for form in &working {
        let result = cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id).check_form(module, form, CheckPass::CheckBody, &mut ctx.check_state, accumulator)?;
        cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id).merge_form_result(module, &mut ctx.check_state, accumulator, result);

        // Populate introspection for REPL slash commands (--repl only).
        if let Some(intr_map) = ctx.introspection
            && let TopLevel::Defn(defn) = form {
                let fq = cranelisp_types::FQSymbol {
                    module: module.clone(),
                    symbol: defn.name.clone(),
                };
                let mut entry = intr_map.entry(fq).or_default();
                // Source: extract from module source_text via sexp span.
                // REPL eval may overwrite with the actual input text later.
                if entry.source.is_none() {
                    let span = sexp.span();
                    let src = ctx.typecheck_products.get(module)
                        .and_then(|tp| tp.source_text.as_ref().and_then(|text| {
                            let start = span.start as usize;
                            let end = span.end as usize;
                            if start < end && end <= text.len() {
                                Some(text[start..end].to_string())
                            } else {
                                None
                            }
                        }));
                    entry.source = src.or_else(|| Some(crate::pretty::pretty_print(sexp)));
                }
                entry.sexp = Some(sexp.clone());
                if let Some(ref expanded) = effective_sexp {
                    entry.expanded = Some(expanded.clone());
                }
                entry.ast = Some(defn.clone());
            }
        if let TopLevel::Defn(defn) = form {
            ctx.scheduler.notify_symbol_typechecked(module, &defn.name);
        }
    }

    expanded_program.extend(built);
    Ok(())
}

// ---------------------------------------------------------------------------
// Import handling (Step 5)
// ---------------------------------------------------------------------------

/// Handle import forms: discover deps, register with scheduler, block if needed.
///
/// For each import spec:
/// - If the dependency module is already loaded in TC, register the import.
/// - Otherwise, resolve the file, parse it, register with scheduler, and block.
///
/// `block_for_typecheck` is called INSIDE this function (F1 fix).
/// The function is idempotent on resume: already-loaded specs are re-registered
/// (register_imports is idempotent), and new deps trigger blocking (F2 fix).
fn handle_import(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    specs: Vec<ImportSpec>,
) -> Result<BlockAction, CranelispError> {
    for spec in &specs {
        let dep = &spec.module_path;

        // §8.3.6 Null import: empty names means suppress loading entirely.
        if matches!(&spec.names, ImportNames::None) {
            continue;
        }

        // Already loaded — register the import and continue.
        if ctx.symbol_tables.contains_key(dep) {
            cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id).register_imports(&mut ctx.check_state,std::slice::from_ref(spec))?;
            continue;
        }

        // Resolve file path.
        let dep_file = crate::pipeline::resolve_module_file(dep, ctx.project_root, ctx.lib_dirs)
            .ok_or_else(|| CranelispError::ModuleError {
                message: format!(
                    "module '{}' not found (imported by '{}')",
                    dep, module
                ),
                file: None,
                span: spec.span,
            })?;

        // Populate file_to_module mapping for file watcher (Step 14).
        if let Some(shared) = ctx.shared_state
            && let Ok(canonical) = dep_file.canonicalize() {
                shared
                    .file_to_module
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .insert(canonical, dep.clone());
            }

        // Cache check: try to load from disk cache before parsing.
        if try_cache_hit_load(ctx, dep, &dep_file) {
            cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id).register_imports(&mut ctx.check_state,std::slice::from_ref(spec))?;
            continue;
        }

        // Read and parse source.
        let source = std::fs::read_to_string(&dep_file).map_err(|e| {
            CranelispError::ModuleError {
                message: format!(
                    "cannot read module '{}' from '{}': {}",
                    dep,
                    dep_file.display(),
                    e
                ),
                file: Some(dep_file.clone()),
                span: spec.span,
            }
        })?;
        let dep_sexps = cranelisp_frontend::parse(&source)?;

        // Record source hash in CacheState for manifest generation.
        if let Some(shared) = ctx.shared_state {
            let hash = cranelisp_backend::cache::hash_source(&source);
            let mut cs_guard = shared.cache_state.lock().unwrap_or_else(|e| e.into_inner());
            if let Some(cs) = cs_guard.as_mut() {
                cs.source_hashes_mut().insert(dep.clone(), hash);
            }
            drop(cs_guard);
        }

        // Store source text on typecheck product for /source introspection (--repl).
        if ctx.introspection.is_some() {
            ensure_typecheck_product(ctx.typecheck_products, dep);
            if let Some(mut tp) = ctx.typecheck_products.get_mut(dep) {
                tp.source_text = Some(source);
            }
        }

        // Register dep with scheduler (idempotent — skips if already registered).
        ctx.scheduler.register_module(dep.clone(), true);

        // Block for typecheck (F1: called inside handle_import).
        ctx.scheduler.block_for_typecheck(
            module,
            dep,
            &Symbol::from("*"),
        )?;

        return Ok(BlockAction::Block {
            dep_module: dep.clone(),
            dep_sexps,
        });
    }

    Ok(BlockAction::Continue)
}

/// Attempt to load a module from the disk cache, skipping typecheck.
///
/// Returns `true` if the module was successfully loaded from cache:
/// type info restored into TC, module registered with scheduler at
/// TypecheckDone, GOT slots pre-allocated. Returns `false` on any
/// cache miss (caller falls through to full typecheck path).
fn try_cache_hit_load(
    ctx: &mut ModuleCompiler,
    dep: &ModuleFullPath,
    dep_file: &Path,
) -> bool {
    use cranelisp_backend::cache;
    use std::collections::{HashMap as StdHashMap, HashSet as StdHashSet};

    let shared = match ctx.shared_state {
        Some(s) => s,
        None => return false,
    };

    // 1. Check cache validity: read source, compute hash, check manifest.
    let cache_state_guard = shared.cache_state.lock().unwrap_or_else(|e| e.into_inner());
    let cache_dir = match cache_state_guard.as_ref() {
        Some(cs) => cs.cache_dir().to_path_buf(),
        None => return false,
    };
    drop(cache_state_guard);

    let dep_source = match std::fs::read_to_string(dep_file) {
        Ok(s) => s,
        Err(_) => return false,
    };
    let source_hash = cache::hash_source(&dep_source);

    // Check manifest (source hash only, no dep hashes yet).
    let dep_hashes: StdHashMap<ModuleFullPath, String> = StdHashMap::new();
    let cache_state_guard = shared.cache_state.lock().unwrap_or_else(|e| e.into_inner());
    let is_valid = match cache_state_guard.as_ref() {
        Some(cs) => cs.is_cache_valid(dep, &source_hash, &dep_hashes),
        None => return false,
    };
    drop(cache_state_guard);

    if !is_valid {
        return false;
    }

    // 2. Load metadata from disk.
    let cached = match cache::try_load_cached_module(&cache_dir, dep) {
        Ok(Some(c)) => c,
        _ => return false,
    };

    // 3. Check .o exists.
    if !cached.has_object {
        return false;
    }

    // 4. Extract all data from cached BEFORE moving symbol_table (avoids clone).
    let symbols: StdHashSet<Symbol> = cached.metadata.symbol_table
        .all_symbols()
        .filter_map(|(name, entry)| match entry {
            ModuleEntry::Def { .. } | ModuleEntry::Constructor { .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    // Collect names of functions with GOT slots for trait impl restoration.
    let mangled_names: Vec<String> = cached.metadata.symbol_table
        .all_symbols()
        .filter_map(|(name, entry)| match entry {
            ModuleEntry::Def { got_slot: Some(_), .. } => Some(name.as_ref().to_string()),
            _ => None,
        })
        .collect();
    // Restore type info into TC (consumes symbol_table by value).
    cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id).restore_cached_module(cached.metadata.symbol_table);

    // Restore trait impl registrations from cached symbol table.
    cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id).restore_cached_impls(&mangled_names);

    // 5. Register with scheduler at TypecheckDone.
    ctx.scheduler.register_module_cached(dep.clone(), symbols);

    // 6. Create typecheck product with GOT table for cached module.
    ensure_typecheck_product(ctx.typecheck_products, dep);

    // 7. Record cache hit in cache state.
    let mut cache_state_guard = shared.cache_state.lock().unwrap_or_else(|e| e.into_inner());
    if let Some(cs) = cache_state_guard.as_mut() {
        cs.record_cache_hit(dep, source_hash);
    }
    drop(cache_state_guard);

    // 8. Record in cached_modules set and file_to_module mapping.
    shared
        .cached_modules
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .insert(dep.clone());
    if let Ok(canonical) = dep_file.canonicalize() {
        shared
            .file_to_module
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(canonical, dep.clone());
    }

    true
}

/// Handle export forms: register export metadata in the typechecker.
/// Handle export forms: ensure source modules are loaded, then register re-exports.
///
/// Export forms like `(export [compare.eq [Eq = !=]])` re-export symbols from
/// the named module. The source module must be loaded in the typechecker before
/// `register_exports` can read its symbol table. If the source module isn't
/// loaded, we trigger dependency loading via the same path as `handle_import`
/// and return `BlockAction::Block`.
fn handle_export(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    specs: &[ExportSpec],
) -> Result<BlockAction, CranelispError> {
    for spec in specs {
        let dep = &spec.module_path;

        // Already loaded — register the re-export and continue.
        if ctx.symbol_tables.contains_key(dep) {
            cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id).register_exports(&mut ctx.check_state,std::slice::from_ref(spec))?;
            continue;
        }

        // Source module not loaded — need to load it first.
        // Resolve file path.
        let dep_file = crate::pipeline::resolve_module_file(dep, ctx.project_root, ctx.lib_dirs)
            .ok_or_else(|| CranelispError::ModuleError {
                message: format!(
                    "module '{}' not found (re-exported by '{}')",
                    dep, module
                ),
                file: None,
                span: spec.span,
            })?;

        // Populate file_to_module mapping for file watcher.
        if let Some(shared) = ctx.shared_state
            && let Ok(canonical) = dep_file.canonicalize() {
                shared
                    .file_to_module
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .insert(canonical, dep.clone());
            }

        // Cache check.
        if try_cache_hit_load(ctx, dep, &dep_file) {
            continue;
        }

        // Read and parse source.
        let source = std::fs::read_to_string(&dep_file).map_err(|e| {
            CranelispError::ModuleError {
                message: format!(
                    "cannot read module '{}' from '{}': {}",
                    dep, dep_file.display(), e
                ),
                file: Some(dep_file.clone()),
                span: spec.span,
            }
        })?;
        let dep_sexps = cranelisp_frontend::parse(&source)?;

        // Store source text for /source introspection (--repl).
        if ctx.introspection.is_some() {
            ensure_typecheck_product(ctx.typecheck_products, dep);
            if let Some(mut tp) = ctx.typecheck_products.get_mut(dep) {
                tp.source_text = Some(source);
            }
        }

        // Register dep with scheduler and block.
        ctx.scheduler.register_module(dep.clone(), true);
        ctx.scheduler.block_for_typecheck(module, dep, &Symbol::from("*"))?;

        return Ok(BlockAction::Block {
            dep_module: dep.clone(),
            dep_sexps,
        });
    }

    // All source modules loaded — register the re-exports.
    cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id).register_exports(&mut ctx.check_state,specs)?;
    Ok(BlockAction::Continue)
}

/// Handle mod forms: write inline body to disk, then load the submodule.
///
/// `(mod util)` declares a submodule whose symbols are accessible via qualified
/// references like `util/helper`. The submodule must be loaded (typechecked)
/// before the parent can resolve these references, so we block for it — same
/// as `handle_import` does for explicit imports.
fn handle_mod(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    decl: &cranelisp_types::ModDecl,
) -> Result<BlockAction, CranelispError> {
    if let Some(body_sexps) = &decl.inline_body {
        write_inline_mod_to_disk(module, &decl.name, body_sexps, ctx.project_root)?;
    }

    // Compute submodule path: "main" + "util" → "main.util"
    let sub_path = ModuleFullPath::from(format!("{}.{}", module, decl.name));

    // Already loaded — resolution chain handles qualified references.
    if ctx.symbol_tables.contains_key(&sub_path) {
        return Ok(BlockAction::Continue);
    }

    // Resolve file path.
    let dep_file = crate::pipeline::resolve_module_file(&sub_path, ctx.project_root, ctx.lib_dirs)
        .ok_or_else(|| CranelispError::ModuleError {
            message: format!(
                "submodule '{}' not found (declared by '{}')",
                sub_path, module
            ),
            file: None,
            span: decl.span,
        })?;

    // Populate file_to_module mapping for file watcher.
    if let Some(shared) = ctx.shared_state
        && let Ok(canonical) = dep_file.canonicalize() {
            shared
                .file_to_module
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .insert(canonical, sub_path.clone());
        }

    // Cache check: try to load from disk cache before parsing.
    if try_cache_hit_load(ctx, &sub_path, &dep_file) {
        return Ok(BlockAction::Continue);
    }

    // Read and parse source.
    let source = std::fs::read_to_string(&dep_file).map_err(|e| {
        CranelispError::ModuleError {
            message: format!(
                "cannot read submodule '{}' from '{}': {}",
                sub_path,
                dep_file.display(),
                e
            ),
            file: Some(dep_file.clone()),
            span: decl.span,
        }
    })?;
    let dep_sexps = cranelisp_frontend::parse(&source)?;

    // Record source hash in CacheState for manifest generation.
    if let Some(shared) = ctx.shared_state {
        let hash = cranelisp_backend::cache::hash_source(&source);
        let mut cs_guard = shared.cache_state.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(cs) = cs_guard.as_mut() {
            cs.source_hashes_mut().insert(sub_path.clone(), hash);
        }
        drop(cs_guard);
    }

    // Store source text for /source introspection (--repl).
    if ctx.introspection.is_some() {
        ensure_typecheck_product(ctx.typecheck_products, &sub_path);
        if let Some(mut tp) = ctx.typecheck_products.get_mut(&sub_path) {
            tp.source_text = Some(source);
        }
    }

    // Register dep with scheduler and block for typecheck.
    ctx.scheduler.register_module(sub_path.clone(), true);
    ctx.scheduler.block_for_typecheck(
        module,
        &sub_path,
        &Symbol::from("*"),
    )?;

    Ok(BlockAction::Block {
        dep_module: sub_path,
        dep_sexps,
    })
}

/// Handle platform forms: load DLL and register type signatures.
///
/// Platform loading is NOT a cross-module blocking operation. The DLL is
/// loaded synchronously. Type signatures are registered in TC immediately.
///
/// Platform declarations in non-entry modules (submodules) are silently
/// ignored per spec §10.9.1 — only the entry module may load platforms.
fn handle_platform(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    spec: &PlatformSpec,
) -> Result<(), CranelispError> {
    // Submodules (paths containing '.') cannot load platforms.
    if module.as_ref().contains('.') {
        return Ok(());
    }
    let (platform, _jit_syms) = crate::platform::load_and_register_platform(
        ctx.symbol_tables,
        ctx.next_type_id,
        &mut ctx.check_state,
        &spec.name,
        ctx.project_root,
        ctx.lib_dirs,
        ctx.platform_dirs,
        spec.span,
    )?;

    // Register each function in the unified platform registry (Step 8).
    let module_path = ModuleFullPath::from(format!("platform.{}", platform.name));
    for desc in &platform.descriptors {
        let fq = cranelisp_types::FQSymbol {
            module: module_path.clone(),
            symbol: Symbol::from(desc.name.as_str()),
        };
        ctx.platform_registry.register(
            fq,
            crate::platform_registry::PlatformFunction {
                jit_name: cranelisp_types::JitSymbol::from(desc.jit_name.clone()),
                fn_ptr: desc.ptr,
                scheduling_class: desc.scheduling_class,
            },
        );
    }

    // Platform DLLs are leaked (kept alive for process lifetime).
    Ok(())
}

/// Write an inline mod body to disk as `{module_dir}/{name}.cl`.
fn write_inline_mod_to_disk(
    parent_module: &ModuleFullPath,
    name: &cranelisp_types::ModuleName,
    body_sexps: &[Sexp],
    project_root: &Path,
) -> Result<(), CranelispError> {
    // Convert parent module path to directory.
    let relative_dir = parent_module.as_ref().replace('.', "/");
    let mod_dir = project_root.join(&relative_dir);
    let file_path = mod_dir.join(format!("{}.cl", name));

    // Create directory if needed.
    std::fs::create_dir_all(&mod_dir).map_err(|e| CranelispError::ModuleError {
        message: format!(
            "cannot create directory for inline mod '{}': {}",
            file_path.display(),
            e
        ),
        file: Some(file_path.clone()),
        span: Span::SYNTHETIC,
    })?;

    // Write body sexps as source text.
    let source: String = body_sexps
        .iter()
        .map(|s| format!("{}", s))
        .collect::<Vec<_>>()
        .join("\n");
    std::fs::write(&file_path, &source).map_err(|e| CranelispError::ModuleError {
        message: format!(
            "cannot write inline mod '{}': {}",
            file_path.display(),
            e
        ),
        file: Some(file_path),
        span: Span::SYNTHETIC,
    })?;

    Ok(())
}

// ---------------------------------------------------------------------------
// Macro expansion for Pass 2
// ---------------------------------------------------------------------------

/// Attempt to expand macros in a sexp tree.
///
/// Compile all clauses of a macro if any clause lacks a function pointer.
///
/// Before compiling macro clauses, walks the transitive callees of the
/// macro (from `ModuleEntry.callees`) and compiles any uncompiled
/// dependencies first. Notifies the scheduler after each symbol is compiled.
fn compile_macro_if_needed(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    info: &cranelisp_frontend::DefmacroInfo,
    span: Span,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    // Check if all clauses already have function pointers.
    let all_compiled = info.clauses.iter().enumerate().all(|(idx, _)| {
        let clause_name = macro_clause_jit_name(&info.name, idx);
        has_code_ptr(ctx.codegen_products, module, &clause_name)
    });

    if all_compiled {
        return Ok(());
    }

    // Walk transitive callees and notify scheduler for any uncompiled deps.
    // The actual compilation is handled through the scheduler's normal priority
    // codegen path (block_for_macro_codegen). This loop only updates the
    // scheduler's completion tracking.
    let uncompiled_deps = collect_transitive_uncompiled_deps(
        ctx.symbol_tables, ctx.codegen_products, module, &info.name,
    );
    for (dep_module, dep_symbol) in &uncompiled_deps {
        if std::env::var("CRANELISP_CODEGEN_TRACE").is_ok() {
            eprintln!(
                "compile_macro_if_needed: uncompiled dep {}/{} — handled by scheduler",
                dep_module, dep_symbol
            );
        }
        ctx.scheduler.notify_inmem_codegen_complete(dep_module, dep_symbol, false);
    }

    // Compile each clause that is not yet compiled.
    let total_clauses = info.clauses.len();
    for (clause_idx, clause) in info.clauses.iter().enumerate() {
        let clause_name = macro_clause_jit_name(&info.name, clause_idx);
        if has_code_ptr(ctx.codegen_products, module, &clause_name) {
            continue;
        }

        compile_macro_clause_inline(
            ctx, &info.name, clause_idx, clause, span,
            accumulator,
        )?;
        let is_last = clause_idx + 1 == total_clauses;
        ctx.scheduler.notify_inmem_codegen_complete(module, &clause_name, is_last);
    }

    Ok(())
}

/// Walk the transitive closure of a symbol's callees via the TC symbol table.
///
/// Returns the symbols that do not yet have compiled code pointers in the GOT.
/// The result is in dependency order (callees before callers) suitable for
/// sequential compilation.
fn collect_transitive_uncompiled_deps(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    codegen_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::CodegenProduct>,
    module: &ModuleFullPath,
    start_symbol: &Symbol,
) -> Vec<(ModuleFullPath, Symbol)> {
    use std::collections::HashSet;
    use std::collections::VecDeque;

    let mut visited: HashSet<(ModuleFullPath, Symbol)> = HashSet::new();
    let mut queue: VecDeque<(ModuleFullPath, Symbol)> = VecDeque::new();
    let mut result: Vec<(ModuleFullPath, Symbol)> = Vec::new();

    // Seed with the starting symbol's callees.
    if let Some(table) = symbol_tables.get(module)
        && let Some(entry) = table.get(start_symbol.as_ref())
    {
        for callee in entry.callees() {
            let key = (callee.module.clone(), callee.symbol.clone());
            if visited.insert(key.clone()) {
                queue.push_back(key);
            }
        }
    }

    // BFS walk.
    while let Some((dep_mod, dep_sym)) = queue.pop_front() {
        // Look up this symbol's own callees and enqueue them.
        if let Some(table) = symbol_tables.get(&dep_mod)
            && let Some(entry) = table.get(dep_sym.as_ref())
        {
            for callee in entry.callees() {
                let key = (callee.module.clone(), callee.symbol.clone());
                if visited.insert(key.clone()) {
                    queue.push_back(key);
                }
            }
        }
        // Only include if uncompiled.
        if !has_code_ptr(codegen_products, &dep_mod, &dep_sym) {
            result.push((dep_mod, dep_sym));
        }
    }

    result
}

// compile_dep_symbol_inline removed (Sprint 53): was a dead stub that took 10
// parameters and returned Ok(()). The scheduler's block_for_macro_codegen
// handles dependency compilation through the normal priority codegen path.

/// Build a CheckResult from the accumulator's current state.
///
/// Used for inline macro compilation. Mono defns and default methods are
/// not needed for macro clause codegen, so they are left empty.
/// Type defs and constructor_to_type are snapshotted from the TC registry
/// (required for Sexp constructor codegen in macro clause bodies).
fn build_check_from_accumulator(
    _symbol_tables: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    accumulator: &ModuleCheckAccumulator,
) -> CheckResult {
    CheckResult {
        method_resolutions: accumulator.method_resolutions.clone(),
        constrained_fn_names: accumulator.constrained_fn_names.clone(),
        mono_defns: Vec::new(),
        expr_types: accumulator.expr_types.clone(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
        display: None,
    }
}

/// Compile a single macro clause inline using the worker's shared state.
///
/// Mirrors `compile_single_clause` from expander.rs but uses the worker's
/// JIT lifetime management and GOT registration instead of creating an
/// isolated JIT per clause. Uses `check_form` (per-form API) instead of
/// the monolithic `tc.check()`.
fn compile_macro_clause_inline(
    ctx: &mut ModuleCompiler,
    macro_name: &Symbol,
    clause_idx: usize,
    clause: &cranelisp_frontend::MacroClause,
    span: Span,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    // Step 1: Synthesize the defn Sexp.
    let synth_sexp = cranelisp_frontend::synthesize_macro_clause_defn(
        macro_name.as_ref(),
        clause_idx,
        clause,
        span,
    );

    // Step 2: Expand quasiquotes.
    let expanded_sexp = cranelisp_frontend::expand_quasiquotes(&synth_sexp)?;

    // Step 3: Build AST (macro clause bodies use quasiquote constructs,
    // not other macros, so no expander is needed).
    let program = cranelisp_frontend::build_program(&[expanded_sexp])?;

    // Step 4: Typecheck using per-form check_form API (Register + CheckBody).
    let module = ctx.current_module.clone();
    for form in &program {
        let result = cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id).check_form(&module, form, CheckPass::Register, &mut ctx.check_state, accumulator)?;
        cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id).merge_form_result(&module, &mut ctx.check_state, accumulator, result);
    }
    for form in &program {
        let result = cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id).check_form(&module, form, CheckPass::CheckBody, &mut ctx.check_state, accumulator)?;
        cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id).merge_form_result(&module, &mut ctx.check_state, accumulator, result);
    }

    // Build a CheckResult from the accumulator for codegen.
    let check = build_check_from_accumulator(ctx.symbol_tables, accumulator);

    // Step 5: Extract the defn and compile it.
    let defn = program
        .iter()
        .find_map(|tl| match tl {
            TopLevel::Defn(d) => Some(d),
            _ => None,
        })
        .ok_or_else(|| CranelispError::MacroError {
            message: format!(
                "macro clause {} for '{}' produced no defn",
                clause_idx, macro_name
            ),
            span,
        })?;

    // Compile macro clause with dealloc disabled (prevents use-after-free on Sexp unmarshal).
    // Macro clause functions are normal functions on per-module GOTs.
    let module = ctx.current_module.clone();
    let tc_modules = ctx.symbol_tables;
    let env_impl = SessionCompilationEnv {
        tc_modules,
        typecheck_products: ctx.typecheck_products,
        current_module: module.clone(),
    };
    let env: &dyn cranelisp_backend::compiler::CompilationEnv = &env_impl;
    ensure_typecheck_product(ctx.typecheck_products, &module);
    let module_got = ctx.typecheck_products.get(&module)
        .expect("invariant: just ensured typecheck product exists")
        .got.clone();
    let (macro_jit_symbols, macro_got_data_defs) = env_impl.collect_jit_setup_for_module(ctx.platform_registry);
    pre_register_got_slots_in_tc(tc_modules, &module, &program, &check);
    compile_and_register_defn_shared(
        &macro_jit_symbols, &macro_got_data_defs, defn, &check, env, &module_got,
        ctx.codegen_products, None, &module, true, tc_modules,
    )?;

    Ok(())
}

// ---------------------------------------------------------------------------
// Macro entry helpers
// ---------------------------------------------------------------------------

/// Generate the JIT symbol name for a macro clause function.
///
/// Must match the naming convention in `synthesize_macro_clause_defn`:
/// `__macro_{name}_clause_{idx}`.
fn macro_clause_jit_name(macro_name: &Symbol, clause_idx: usize) -> Symbol {
    Symbol::from(format!("__macro_{}_clause_{}", macro_name, clause_idx))
}

/// Check if a symbol has a compiled code pointer in codegen_products.
fn has_code_ptr(
    codegen_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::CodegenProduct>,
    module: &ModuleFullPath,
    name: &Symbol,
) -> bool {
    codegen_products
        .get(module)
        .map(|p| p.code.contains_key(name))
        .unwrap_or(false)
}

/// Get a code pointer from codegen_products, if compiled.
fn get_code_ptr(
    codegen_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::CodegenProduct>,
    module: &ModuleFullPath,
    name: &Symbol,
) -> Option<*const u8> {
    codegen_products
        .get(module)
        .and_then(|p| p.code.get(name).map(|c| c.ptr))
}

/// Compile a macro's clauses for REPL use.
///
/// Called from `make_defmacro_result` to ensure the macro is compiled and
/// available for expansion in subsequent REPL evals.
pub fn compile_macro_for_repl(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    info: &cranelisp_frontend::DefmacroInfo,
    span: Span,
    accumulator: &mut cranelisp_typecheck::ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    compile_macro_if_needed(ctx, module, info, span, accumulator)
}

/// Pass 1: register all forms' type signatures in source order.
fn pass1_register(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    next_type_id: &std::sync::atomic::AtomicU32,
    check_state: &mut CheckState,
    module: &ModuleFullPath,
    working_program: &[TopLevel],
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    let tc = cranelisp_typecheck::TypeCheckEnv::new(symbol_tables, next_type_id);
    for form in working_program {
        let result = tc.check_form(module, form, CheckPass::Register, check_state, accumulator)?;
        tc.merge_form_result(module, check_state, accumulator, result);
    }
    Ok(())
}

/// Register default method defns generated during Pass 1 TraitImpl processing.
fn register_default_methods(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    next_type_id: &std::sync::atomic::AtomicU32,
    check_state: &mut CheckState,
    module: &ModuleFullPath,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<Vec<Defn>, CranelispError> {
    let tc = cranelisp_typecheck::TypeCheckEnv::new(symbol_tables, next_type_id);
    let defaults: Vec<Defn> = std::mem::take(&mut accumulator.default_method_defns);
    for defn in &defaults {
        let form = TopLevel::Defn(defn.clone());
        let result = tc.check_form(module, &form, CheckPass::Register, check_state, accumulator)?;
        tc.merge_form_result(module, check_state, accumulator, result);
    }
    Ok(defaults)
}

/// Inject prelude import for non-prelude modules, blocking if prelude needs loading.
///
/// Per spec §8.8.1: the implicit `(import [prelude [*]])` is suppressed when the
/// module's source contains an explicit `(import [prelude ...])` or
/// `(export [prelude ...])`. This allows modules to control their prelude
/// relationship — specific imports, null import (§8.3.6), or re-export.
///
/// Returns `Some(ProcessResult::Blocked { .. })` if the prelude must be compiled
/// first, `None` if prelude is already loaded, not found, or suppressed.
fn inject_prelude_if_needed(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexps: &[Sexp],
) -> Result<Option<ProcessResult>, CranelispError> {
    let prelude_path = ModuleFullPath::from("prelude");
    if *module == prelude_path {
        return Ok(None);
    }

    // §8.8.1: explicit import/export of prelude suppresses the implicit glob.
    if sexps_reference_prelude(sexps) {
        return Ok(None);
    }

    if !ctx.symbol_tables.contains_key(&prelude_path) {
        // Discover prelude through the same lazy path as any user import.
        let prelude_file = crate::session::resolve_prelude(
            ctx.project_root,
            ctx.lib_dirs,
        );
        if let Some(prelude_file) = prelude_file {
            // Cache check: try to load prelude from disk cache.
            if try_cache_hit_load(ctx, &prelude_path, &prelude_file) {
                // Prelude loaded from cache — inject implicit import and continue.
                return Ok(None);
            }

            let source = std::fs::read_to_string(&prelude_file).map_err(|e| {
                CranelispError::ModuleError {
                    message: format!(
                        "cannot read prelude '{}': {}",
                        prelude_file.display(),
                        e
                    ),
                    file: Some(prelude_file.clone()),
                    span: Span::SYNTHETIC,
                }
            })?;
            let prelude_sexps = cranelisp_frontend::parse(&source)?;

            // Record source hash in CacheState for manifest generation.
            if let Some(shared) = ctx.shared_state {
                let hash = cranelisp_backend::cache::hash_source(&source);
                let mut cs_guard = shared.cache_state.lock().unwrap_or_else(|e| e.into_inner());
                if let Some(cs) = cs_guard.as_mut() {
                    cs.source_hashes_mut().insert(prelude_path.clone(), hash);
                }
                drop(cs_guard);
            }

            // Store source text for /source introspection (--repl).
            if ctx.introspection.is_some() {
                ensure_typecheck_product(ctx.typecheck_products, &prelude_path);
                if let Some(mut tp) = ctx.typecheck_products.get_mut(&prelude_path) {
                    tp.source_text = Some(source);
                }
            }

            ctx.scheduler.register_module(prelude_path.clone(), true);
            ctx.scheduler.block_for_typecheck(
                module,
                &prelude_path,
                &Symbol::from("*"),
            )?;

            return Ok(Some(ProcessResult::Blocked {
                form_index: 0,
                dep_module: prelude_path,
                dep_sexps: prelude_sexps,
            }));
        }
        // No prelude file found. Per spec §8.9.1: primitives are NOT
        // available as bare names without explicit import or prelude.
        // No implicit injection — modules that need primitives must
        // either have a prelude that re-exports them or import explicitly.
    } else {
        // Prelude already loaded — register the import.
        let prelude_spec = ImportSpec {
            module_path: prelude_path,
            alias: None,
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        };
        cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id).register_imports(&mut ctx.check_state,&[prelude_spec])?;
    }

    Ok(None)
}

/// Check whether a module's source sexps contain an explicit reference to
/// `prelude` in an import or export form (spec §8.8.1).
fn sexps_reference_prelude(sexps: &[Sexp]) -> bool {
    for sexp in sexps {
        let Sexp::List(items, _) = sexp else { continue };
        if items.len() < 2 { continue; }
        let Sexp::Symbol(head, _) = &items[0] else { continue };
        if head.as_str() != "import" && head.as_str() != "export" {
            continue;
        }
        // Check each import/export spec for a module path of "prelude".
        // Import/export specs use brackets: (import [module [names...]])
        // The inner spec is Sexp::Bracket, not Sexp::List.
        for spec_sexp in &items[1..] {
            let spec_items = match spec_sexp {
                Sexp::Bracket(items, _) => items,
                Sexp::List(items, _) => items,
                _ => continue,
            };
            if spec_items.is_empty() { continue; }
            let module_name = match &spec_items[0] {
                Sexp::Symbol(name, _) => Some(name.as_str()),
                // Aliased form: [(module alias) [...]] or ((module alias) [...])
                Sexp::Bracket(alias_items, _) | Sexp::List(alias_items, _)
                    if !alias_items.is_empty() =>
                {
                    match &alias_items[0] {
                        Sexp::Symbol(name, _) => Some(name.as_str()),
                        _ => None,
                    }
                }
                _ => None,
            };
            if module_name == Some("prelude") {
                return true;
            }
        }
    }
    false
}

/// Inject a wildcard import of the `primitives` module into the current module.
///
/// Zero GOT slots and clear codegen artifacts for a module's symbols.
///
/// Called at the start of Replace processing. Preserves GOT slot assignments
/// so re-compiled definitions land in the same slots. Zeroing the slots
/// ensures stale code pointers are not callable during recompilation.
fn clear_module_codegen(ctx: &mut ModuleCompiler, module: &ModuleFullPath) {
    // Collect qualified symbol names for this module from the TC symbol table.
    let symbols: Vec<cranelisp_types::Symbol> = {
        let table = ctx.symbol_tables.get(&ctx.current_module).unwrap();
        table.all_symbols()
            .filter_map(|(name, entry)| {
                // Only clear codegen for definitions owned by this module,
                // not imports or special forms.
                match entry {
                    cranelisp_types::ModuleEntry::Def { kind, .. } => {
                        if matches!(kind.as_ref(), cranelisp_types::DefKind::SpecialForm { .. }) {
                            None
                        } else {
                            let qualified = cranelisp_types::Symbol::from(
                                format!("{}/{}", module, name)
                            );
                            Some(qualified)
                        }
                    }
                    cranelisp_types::ModuleEntry::Constructor { .. } => {
                        let qualified = cranelisp_types::Symbol::from(
                            format!("{}/{}", module, name)
                        );
                        Some(qualified)
                    }
                    _ => None,
                }
            })
            .collect()
    };

    // Zero GOT slots via per-module GOT table (keep slot assignments in TC).
    {
        if let Some(tp) = ctx.typecheck_products.get(module) {
            let got_table = &tp.got;
            let table = ctx.symbol_tables.get(&ctx.current_module).unwrap();
            for (_name, entry) in table.all_symbols() {
                if let cranelisp_types::ModuleEntry::Def { got_slot: Some(slot), kind, .. } = entry
                    && !matches!(kind.as_ref(), cranelisp_types::DefKind::SpecialForm { .. }) {
                        got_table.store_slot(*slot, std::ptr::null());
                    }
            }
        }
    }

    // Clear codegen products for this module (keeps CodegenProduct entry with GOT/linker).
    if let Some(cp) = ctx.codegen_products.get(module) {
        cp.code.clear();
    }

    // Clear introspection entries for this module.
    let fq_keys: Vec<_> = symbols.iter().map(|sym| {
        let bare = sym.as_ref().rsplit('/').next().unwrap_or(sym.as_ref());
        cranelisp_types::FQSymbol {
            module: module.clone(),
            symbol: cranelisp_types::Symbol::from(bare),
        }
    }).collect();
    if let Some(intr_map) = ctx.introspection {
        for fq in &fq_keys {
            intr_map.remove(fq);
        }
    }
}

/// Wrap `Expr` variants as synthetic zero-arg `Defn` named `__expr`.
/// Mirrors `TypeChecker::wrap_exprs_as_defns`.
fn wrap_exprs_as_defns(program: &[TopLevel]) -> Vec<TopLevel> {
    use cranelisp_types::{DefnVariant, Visibility};

    let mut working = Vec::with_capacity(program.len());
    for top in program {
        match top {
            TopLevel::Expr(expr) => {
                let span = expr.span();
                let wrapper_span = Span::new(
                    span.start.saturating_sub(1),
                    span.end.saturating_add(1),
                );
                let synthetic_defn = Defn {
                    name: Symbol::from("__expr"),
                    docstring: None,
                    variants: vec![DefnVariant {
                        params: vec![],
                        param_annotations: vec![],
                        body: expr.clone(),
                        span,
                    }],
                    visibility: Visibility::Public,
                    span: wrapper_span,
                };
                working.push(TopLevel::Defn(synthetic_defn));
            }
            other => working.push(other.clone()),
        }
    }
    working
}

// ---------------------------------------------------------------------------
// codegen_module_symbols — post-typecheck codegen sweep (W2)
// ---------------------------------------------------------------------------

/// Compile all symbols from a typechecked module and register in GOT.
///
/// Iterates the program's definitions, compiles each via `compile_and_register_defn`,
/// and notifies the scheduler. Returns the last defn's execution result (for
/// zero-arg defns like `main`).
#[allow(clippy::too_many_arguments)]
pub fn codegen_module_symbols(
    platform_registry: &PlatformRegistry,
    scheduler: &CompileScheduler,
    module: &ModuleFullPath,
    program: &[TopLevel],
    check: &CheckResult,
    tc_modules: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    typecheck_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    codegen_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::CodegenProduct>,
    introspection: Option<&dashmap::DashMap<cranelisp_types::FQSymbol, crate::session_v4::Introspection>>,
) -> Result<(), CranelispError> {
    // Ensure typecheck product with GOT table exists for this module.
    ensure_typecheck_product(typecheck_products, module);

    let env_impl = SessionCompilationEnv {
        tc_modules,
        typecheck_products,
        current_module: module.clone(),
    };
    let env: &dyn cranelisp_backend::compiler::CompilationEnv = &env_impl;
    let module_got = typecheck_products.get(module)
        .expect("invariant: just ensured typecheck product exists")
        .got.clone();

    let (jit_symbols, got_data_defs) = env_impl.collect_jit_setup_for_module(platform_registry);

    // Pre-register GOT slots for forward references.
    pre_register_got_slots_in_tc(tc_modules, module, program, check);

    // Compile default method bodies.
    for defn in &check.default_method_defns {
        compile_and_register_defn_shared(&jit_symbols, &got_data_defs, defn, check, env, &module_got, codegen_products, introspection, module, false, tc_modules)?;
    }

    // Compile mono specializations with per-specialization resolutions.
    compile_mono_defns(&jit_symbols, &got_data_defs, check, env, &module_got, codegen_products, introspection, module, tc_modules)?;

    // Compile each regular defn.
    let defn_names = compile_regular_defns(&jit_symbols, &got_data_defs, program, check, env, &module_got, codegen_products, introspection, module, tc_modules)?;

    // Notify scheduler for each compiled symbol.
    let total = defn_names.len();
    for (i, name) in defn_names.iter().enumerate() {
        let is_last = i + 1 == total;
        scheduler.notify_inmem_codegen_complete(module, name, is_last);
    }

    // If no defns were compiled, mark inmem done anyway.
    if total == 0 {
        let dummy = Symbol::from("__empty_module");
        scheduler.notify_inmem_codegen_complete(module, &dummy, true);
    }

    Ok(())
}

/// Pre-assign GOT slots in TC symbol tables for all definitions that codegen
/// will compile. This covers names that the typechecker doesn't register in the
/// symbol table (trait impl mangled methods, mono specializations, default methods).
fn pre_register_got_slots_in_tc(
    tc_modules: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    module: &ModuleFullPath,
    program: &[TopLevel],
    check: &CheckResult,
) {
    use cranelisp_types::{DefKind, ModuleEntry, Scheme, Visibility};

    let mut st = match tc_modules.get_mut(module) {
        Some(st) => st,
        None => return,
    };

    let mut ensure_slot = |name: &Symbol, params: &[Symbol]| {
        match st.get(name.as_ref()) {
            // Already has a GOT slot — nothing to do.
            Some(ModuleEntry::Def { got_slot: Some(_), .. }) => return,
            // Def exists but without a GOT slot — update in place.
            Some(ModuleEntry::Def { got_slot: None, .. }) => {
                // We can't update in place through get(), so remove + reinsert.
                // Clone the entry, set got_slot, reinsert.
                let mut entry = st.symbols.get(name).cloned().unwrap();
                let slot = st.allocate_got_slot();
                if let ModuleEntry::Def { got_slot: ref mut gs, .. } = entry {
                    *gs = Some(slot);
                }
                st.symbols.insert(name.clone(), entry);
                return;
            }
            // Any other entry type (Import, Constructor, etc.) — don't overwrite.
            Some(_) => return,
            // Not present at all — insert a new Def entry.
            None => {}
        }
        let slot = st.allocate_got_slot();
        st.insert(
            name.clone(),
            ModuleEntry::Def {
                scheme: Scheme { vars: vec![], constraints: Default::default(), ty: cranelisp_types::Type::Int },
                visibility: Visibility::Public,
                docstring: None,
                param_names: params.to_vec(),
                kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                callees: Vec::new(),
                got_slot: Some(slot),
                trait_origin: None,
            },
        );
    };

    // Regular defns (should already be registered, but ensure slot exists).
    for tl in program {
        match tl {
            TopLevel::Defn(defn) => {
                if check.constrained_fn_names.contains(&defn.name) {
                    continue;
                }
                ensure_slot(&defn.name, defn.params());
            }
            TopLevel::TraitImpl(impl_) => {
                for method in &impl_.methods {
                    ensure_slot(&method.name, method.params());
                }
            }
            _ => {}
        }
    }

    // Default method defns (generated by typechecker for trait impls with defaults).
    for defn in &check.default_method_defns {
        ensure_slot(&defn.name, defn.params());
    }

    // Mono specializations.
    for mono in &check.mono_defns {
        ensure_slot(&mono.defn.name, mono.defn.params());
    }
}

/// Compile monomorphised specializations.
#[allow(clippy::too_many_arguments)]
fn compile_mono_defns(
    jit_symbols: &[(String, *const u8)],
    got_data_defs: &[(String, *const u8)],
    check: &CheckResult,
    env: &dyn cranelisp_backend::compiler::CompilationEnv,
    module_got: &std::sync::Arc<cranelisp_backend::got::GotTable>,
    codegen_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::CodegenProduct>,
    introspection: Option<&dashmap::DashMap<cranelisp_types::FQSymbol, crate::session_v4::Introspection>>,
    module: &ModuleFullPath,
    tc_modules: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
) -> Result<(), CranelispError> {
    for mono in &check.mono_defns {
        let mut merged = check.method_resolutions.clone();
        merged.extend(mono.resolutions.clone());
        let expr_types = if mono.expr_types.is_empty() {
            check.expr_types.clone()
        } else {
            mono.expr_types.clone()
        };
        let mono_check = CheckResult {
            method_resolutions: merged,
            constrained_fn_names: check.constrained_fn_names.clone(),
            mono_defns: Vec::new(),
            expr_types,
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            display: None,
        };
        compile_and_register_defn_shared(jit_symbols, got_data_defs, &mono.defn, &mono_check, env, module_got, codegen_products, introspection, module, false, tc_modules)?;
    }
    Ok(())
}

/// Compile regular defns (skipping constrained fn base definitions).
/// Returns the list of compiled symbol names.
#[allow(clippy::too_many_arguments)]
fn compile_regular_defns(
    jit_symbols: &[(String, *const u8)],
    got_data_defs: &[(String, *const u8)],
    program: &[TopLevel],
    check: &CheckResult,
    env: &dyn cranelisp_backend::compiler::CompilationEnv,
    module_got: &std::sync::Arc<cranelisp_backend::got::GotTable>,
    codegen_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::CodegenProduct>,
    introspection: Option<&dashmap::DashMap<cranelisp_types::FQSymbol, crate::session_v4::Introspection>>,
    module: &ModuleFullPath,
    tc_modules: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
) -> Result<Vec<Symbol>, CranelispError> {
    let mut compiled_names = Vec::new();

    for tl in program {
        match tl {
            TopLevel::Defn(defn) => {
                if check.constrained_fn_names.contains(&defn.name) {
                    continue;
                }
                compile_and_register_defn_shared(jit_symbols, got_data_defs, defn, check, env, module_got, codegen_products, introspection, module, false, tc_modules)?;
                compiled_names.push(defn.name.clone());
            }
            TopLevel::TraitImpl(impl_) => {
                for method in &impl_.methods {
                    compile_and_register_defn_shared(
                        jit_symbols, got_data_defs, method, check, env, module_got,
                        codegen_products, introspection, module, false, tc_modules,
                    )?;
                    compiled_names.push(method.name.clone());
                }
            }
            _ => {}
        }
    }

    Ok(compiled_names)
}


// ---------------------------------------------------------------------------
// Linker-based loading for cached modules (Step 13 — cache-hit inmem codegen)
// ---------------------------------------------------------------------------

/// Load a cached module's `.o` file via Linker, wiring code pointers into
/// the per-module GOT. This is the inmem codegen fast-path for cache-hit
/// modules: one mmap + relocation pass loads all symbols at once.
///
/// Returns the list of symbol names that were loaded, for scheduler notification.
fn load_cached_module_via_linker(
    platform_registry: &PlatformRegistry,
    module: &ModuleFullPath,
    shared_state: &crate::session_v4::SharedState,
    typecheck_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    codegen_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::CodegenProduct>,
) -> Result<Vec<Symbol>, CranelispError> {
    use cranelisp_backend::cache;

    let cache_dir = shared_state.cache_dir.as_ref().ok_or_else(|| CranelispError::ModuleError {
        message: format!("no cache directory for cache-hit loading of '{}'", module),
        file: None,
        span: Span::SYNTHETIC,
    })?;

    // Load metadata from disk.
    let cached = cache::try_load_cached_module(cache_dir, module)?
        .ok_or_else(|| CranelispError::ModuleError {
            message: format!("cache metadata missing for module '{}'", module),
            file: None,
            span: Span::SYNTHETIC,
        })?;

    if !cached.has_object {
        return Err(CranelispError::ModuleError {
            message: format!("cached .o file missing for module '{}'", module),
            file: None,
            span: Span::SYNTHETIC,
        });
    }

    // Build Linker with all known symbols.
    let mut linker = cache::Linker::new()?;

    // Register runtime intrinsics.
    for sym in cranelisp_backend::jit::intrinsic_symbols() {
        linker.register_symbol(sym.name, sym.ptr);
    }

    // Register platform symbols.
    let jit_symbols = platform_registry.jit_symbols_owned();
    for (name, ptr) in &jit_symbols {
        linker.register_symbol(name, *ptr);
    }

    // Register code pointers from already-compiled modules via codegen_products.
    for cp_entry in codegen_products.iter() {
        for code_entry in cp_entry.value().code.iter() {
            linker.register_symbol(code_entry.key().as_ref(), code_entry.value().ptr);
        }
    }

    // Register per-module GOT data symbols for cross-module GOT-indirect calls.
    for tp_entry in typecheck_products.iter() {
        let name = cranelisp_backend::compiler::got_data_symbol_name(tp_entry.key());
        linker.register_symbol(&name, tp_entry.value().got.base_ptr());
    }

    // Get this module's GOT table from typecheck products.
    let module_got = typecheck_products.get(module)
        .ok_or_else(|| CranelispError::ModuleError {
            message: format!("no typecheck product for cached module '{}'", module),
            file: None,
            span: Span::SYNTHETIC,
        })?.got.clone();

    // Load the .o file — one mmap + relocation pass.
    let fn_addrs = cache::load_cached_object(&mut linker, &cached)?;

    // Wire code pointers into the per-module GOT using slot assignments
    // from the symbol table.
    let mut loaded_symbols = Vec::new();
    for (name, entry) in cached.symbol_table().all_symbols() {
        let slot = match entry {
            ModuleEntry::Def { got_slot: Some(s), .. } => *s,
            _ => continue,
        };
        let code_ptr = fn_addrs.get(name.as_ref()).copied();

        // Write the code pointer to the per-module GOT slot.
        if let Some(ptr) = code_ptr {
            module_got.store_slot(slot, ptr);
        }

        loaded_symbols.push(name.clone());
    }

    // Store the Linker in codegen_products (keeps mmap'd code alive).
    // GOT table lives in typecheck_products, not in CodegenProduct.
    let mut cp = codegen_products.entry(module.clone()).or_default();
    cp.linker = Some(linker);

    Ok(loaded_symbols)
}

/// Handle a cache-hit codegen work item: check if the module is cached
/// and load it via Linker, then notify the scheduler.
///
/// Shared helper for both `priority_worker_loop` (inline) and
/// `priority_worker_thread` (spawned). Returns Ok(true) if the module
/// was loaded, Ok(false) if it was not cached (no-op).
fn handle_cached_codegen(
    platform_registry: &PlatformRegistry,
    module: &ModuleFullPath,
    shared_state: Option<&crate::session_v4::SharedState>,
    typecheck_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    codegen_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::CodegenProduct>,
    scheduler: &CompileScheduler,
) -> Result<bool, CranelispError> {
    let is_cached = shared_state
        .map(|s| s.cached_modules.lock()
            .unwrap_or_else(|e| e.into_inner())
            .contains(module))
        .unwrap_or(false);

    if !is_cached {
        return Ok(false);
    }

    let shared = shared_state.ok_or_else(|| CranelispError::ModuleError {
        message: format!("no shared state for cache-hit loading of '{}'", module),
        file: None,
        span: Span::SYNTHETIC,
    })?;

    match load_cached_module_via_linker(
        platform_registry, module, shared, typecheck_products, codegen_products,
    ) {
        Ok(symbols) => {
            scheduler.notify_inmem_codegen_batch_complete(module, &symbols);
            Ok(true)
        }
        Err(e) => {
            scheduler.notify_module_failed(module, e);
            Ok(false)
        }
    }
}

// ---------------------------------------------------------------------------
// priority_worker_loop — dispatch scheduler work items
// ---------------------------------------------------------------------------

/// Per-module suspension state preserved across blocking/resumption.
///
/// Groups the mutable state that `process_module_forms` accumulates across
/// suspensions: the typechecker accumulator, expanded program forms, and
/// a flag tracking whether Pass 1 has completed.
pub struct ModuleSuspendState {
    pub accumulator: ModuleCheckAccumulator,
    /// Expanded program forms accumulated across suspensions.
    /// Forms processed before the block point are preserved here.
    pub expanded_program: Vec<TopLevel>,
    /// Whether Pass 1 (register signatures) has been completed for this module.
    /// Prevents re-running Pass 1 on resume when start_form_index is 0
    /// (which happens when a module blocks on its very first form).
    pub pass1_done: bool,
}

/// Main worker loop: pull work from the scheduler and process it.
///
/// Returns when `take_priority_work` returns None (all work done or shutdown).
/// After typecheck, performs a codegen sweep (W2 approach).
///
/// `module_sexps` grows dynamically as dependencies are discovered (G-2).
pub fn priority_worker_loop(
    ctx: &mut ModuleCompiler,
    module_sexps: &mut HashMap<ModuleFullPath, Vec<Sexp>>,
) -> Result<(), CranelispError> {
    let mut suspend_states: HashMap<ModuleFullPath, ModuleSuspendState> = HashMap::new();

    loop {
        let work = ctx.scheduler.take_priority_work();
        match work {
            Some(PriorityWork::Typecheck(module)) => {
                let start_idx = ctx.scheduler.module_resume_from_form(&module)
                    .flatten()
                    .unwrap_or(0);

                // Clone sexps (don't remove — needed on resume).
                let sexps = module_sexps.get(&module)
                    .ok_or_else(|| CranelispError::ModuleError {
                        message: format!("no parsed sexps for module '{}'", module),
                        file: None,
                        span: Span::SYNTHETIC,
                    })?
                    .clone();

                // Get or create suspend state for this module.
                let state = suspend_states
                    .entry(module.clone())
                    .or_insert_with(|| ModuleSuspendState {
                        accumulator: ModuleCheckAccumulator::new(),
                        expanded_program: Vec::new(),
                        pass1_done: false,
                    });

                match process_module_forms(
                    ctx, &module, &sexps, start_idx,
                    state,
                    ModuleStrategy::Replace,
                ) {
                    Ok(ProcessResult::Complete { check_result, program }) => {
                        // Post-typecheck codegen sweep (W2).
                        codegen_module_symbols(
                            ctx.platform_registry,
                            ctx.scheduler,
                            &module,
                            &program,
                            &check_result,
                            ctx.symbol_tables,
                            ctx.typecheck_products,
                            ctx.codegen_products,
                            None,
                        )?;

                        // Stash data for nice worker .o + .meta.json, then
                        // notify typecheck_done. Order matters: nice workers
                        // wake on notify_typecheck_done, so the stash must
                        // be populated first.
                        stash_codegen_input(
                            ctx.shared_state,
                            &module,
                            check_result,
                            program,
                        );
                        ctx.scheduler.notify_typecheck_done(&module);

                        // Clean up — module is done.
                        module_sexps.remove(&module);
                        suspend_states.remove(&module);
                    }
                    Ok(ProcessResult::Blocked {
                        form_index,
                        dep_module,
                        dep_sexps,
                    }) => {
                        // Save resume state in scheduler.
                        ctx.scheduler.set_resume_from_form(&module, form_index);
                        // Store dep sexps for the worker loop to pick up.
                        module_sexps.entry(dep_module.clone())
                            .or_insert(dep_sexps);
                        // block_for_typecheck was already called inside
                        // handle_import/prelude injection before returning Blocked.
                    }
                    Err(e) => {
                        ctx.scheduler.notify_module_failed(&module, e);
                        // Clean up on failure.
                        module_sexps.remove(&module);
                        suspend_states.remove(&module);
                    }
                }
            }
            Some(PriorityWork::BlockingJitCodegen(module, _symbol))
            | Some(PriorityWork::JitCodegen(module, _symbol)) => {
                // Cache-hit module: load entire .o via Linker (batch load).
                // Non-cached modules have their codegen done inline after typecheck.
                let _ = handle_cached_codegen(
                    ctx.platform_registry, &module, ctx.shared_state,
                    ctx.typecheck_products, ctx.codegen_products, ctx.scheduler,
                );
            }
            None => break,
        }
    }
    Ok(())
}

/// Collect cross-module function signatures from TC symbol tables.
///
/// Scans the module's symbol table (from `typecheck_products`) for `Import` entries,
/// then looks up the source scheme in the TC's module tables (which include synthetic
/// modules like `primitives` and `macros`). Returns (qualified_name, param_count) pairs.
pub(crate) fn collect_cross_module_func_sigs_from_tc(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    #[allow(unused)] typecheck_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    module: &ModuleFullPath,
) -> Vec<(Symbol, usize)> {
    let mut sigs = Vec::new();
    // Use TC's module table (not typecheck_products) because the full symbol
    // table with Import entries lives in the TC. typecheck_products only has
    // Def entries with GOT slots.
    let Some(table) = symbol_tables.get(module) else {
        eprintln!("DEBUG cross-sigs: no TC module table for {}", module);
        return sigs;
    };

    for (name, entry) in table.all_symbols() {
        if let ModuleEntry::Import { source } = entry {
            // Look up in TC's module tables (covers synthetic modules like primitives).
            if let Some(source_table) = symbol_tables.get(&source.module)
                && let Some(source_entry) = source_table.get(source.symbol.as_ref()) {
                    let param_count = match source_entry {
                        ModuleEntry::Def { scheme, .. } | ModuleEntry::Constructor { scheme, .. } => {
                            match &scheme.ty {
                                Type::Fn(params, _) => params.len(),
                                _ => continue,
                            }
                        }
                        _ => continue,
                    };
                    let qualified = Symbol::from(format!(
                        "{}/{}",
                        source.module.as_ref(),
                        source.symbol.as_ref()
                    ));
                    sigs.push((qualified, param_count));
                    sigs.push((name.clone(), param_count));
                }
        }
    }
    sigs
}

/// Stash module data for nice worker `.o` and `.meta.json` compilation.
///
/// When the object codegen stash is available, stores the CheckResult,
/// Program, and SymbolTable so that nice workers can compile `.o` files
/// and write `.meta.json` without re-accessing the TypeChecker.
/// Stash codegen input for nice worker .o compilation.
///
/// Inserts a `CodegenInput` into the shared `codegen_inputs` DashMap.
/// Nice workers read from this DashMap and from `typecheck_products`
/// for the symbol table needed by .meta.json serialization.
///
/// Stashes the full `CheckResult` (including `constrained_fn_names`)
/// so the nice worker gets the same information as the priority worker.
fn stash_codegen_input(
    shared_state: Option<&crate::session_v4::SharedState>,
    module: &ModuleFullPath,
    check_result: CheckResult,
    program: Vec<TopLevel>,
) {
    let Some(shared) = shared_state else { return };

    shared.codegen_inputs.insert(
        module.clone(),
        crate::session_v4::CodegenInput {
            check: check_result,
            program,
        },
    );
}

// ---------------------------------------------------------------------------
// Threaded priority worker loop (Step 11 — Wave 3)
// ---------------------------------------------------------------------------

/// Shared state for threaded priority workers.
///
/// Holds Mutex-wrapped TypeChecker and PlatformRegistry plus shared
/// codegen state. Workers lock the Mutexes when processing work items.
/// With the current `&mut self` TypeChecker API, workers serialize on
/// the TC mutex. True parallelism comes when TC gets full `&self` API.
pub(crate) struct PriorityWorkerRefs<'a> {
    pub(crate) platform_registry: &'a std::sync::Mutex<PlatformRegistry>,
    pub(crate) typecheck_products: &'a dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    pub(crate) codegen_products: &'a dashmap::DashMap<ModuleFullPath, crate::session_v4::CodegenProduct>,
    pub(crate) introspection: Option<&'a dashmap::DashMap<cranelisp_types::FQSymbol, crate::session_v4::Introspection>>,
    pub(crate) scheduler: &'a CompileScheduler,
    pub(crate) module_sexps: &'a std::sync::Mutex<HashMap<ModuleFullPath, Vec<Sexp>>>,
    pub(crate) suspend_states: &'a std::sync::Mutex<
        HashMap<ModuleFullPath, ModuleSuspendState>,
    >,
    pub(crate) lib_dirs: &'a [PathBuf],
    pub(crate) platform_dirs: &'a [PathBuf],
    pub(crate) project_root: &'a Path,
    pub(crate) shared_state: Option<&'a crate::session_v4::SharedState>,
}

/// Main loop for a spawned priority worker thread.
///
/// Uses `take_priority_work_blocking` to park when no work is available.
/// Locks the TypeChecker mutex for each work item (serialized until TC
/// gets `&self` API).
pub(crate) fn priority_worker_thread(
    shared: &PriorityWorkerRefs,
    _worker_id: usize,
) {
    loop {
        let work = shared.scheduler.take_priority_work_blocking();
        match work {
            Some(PriorityWork::Typecheck(module)) => {
                if let Err(e) = handle_typecheck_work(shared, &module) {
                    shared.scheduler.notify_module_failed(&module, e);
                }
            }
            Some(PriorityWork::BlockingJitCodegen(module, _symbol))
            | Some(PriorityWork::JitCodegen(module, _symbol)) => {
                // Cache-hit module: load entire .o via Linker (batch load).
                let platform = shared.platform_registry.lock()
                    .unwrap_or_else(|e| e.into_inner());
                let _ = handle_cached_codegen(
                    &platform, &module, shared.shared_state,
                    shared.typecheck_products, shared.codegen_products, shared.scheduler,
                );
            }
            None => break, // Shutdown or all work done.
        }
    }
}

/// Handle a Typecheck work item under the TC mutex lock.
///
/// Locks TC + PlatformRegistry, builds a ModuleCompiler, and runs
/// process_module_forms + codegen_module_symbols.
fn handle_typecheck_work(
    shared: &PriorityWorkerRefs,
    module: &ModuleFullPath,
) -> Result<(), CranelispError> {
    let start_idx = shared.scheduler.module_resume_from_form(module)
        .flatten()
        .unwrap_or(0);

    // Clone sexps from shared map (don't remove — needed on resume).
    let sexps = {
        let map = shared.module_sexps.lock()
            .unwrap_or_else(|e| e.into_inner());
        map.get(module)
            .ok_or_else(|| CranelispError::ModuleError {
                message: format!("no parsed sexps for module '{}'", module),
                file: None,
                span: Span::SYNTHETIC,
            })?
            .clone()
    };

    // Take or create suspend state for this module.
    let mut state = {
        let mut states = shared.suspend_states.lock()
            .unwrap_or_else(|e| e.into_inner());
        states.remove(module).unwrap_or_else(|| ModuleSuspendState {
            accumulator: ModuleCheckAccumulator::new(),
            expanded_program: Vec::new(),
            pass1_done: false,
        })
    };

    // Lock PlatformRegistry for the duration of processing.
    // TypeChecker state is on SharedState (symbol_tables, next_type_id).
    let mut platform_registry = shared.platform_registry.lock()
        .unwrap_or_else(|e| e.into_inner());

    // Get symbol_tables and next_type_id from shared_state.
    let shared_state = shared.shared_state.expect("invariant: shared_state must be set for priority workers");
    // Ensure the module's SymbolTable exists before creating CheckState (invariant: current_module always in modules map).
    {
        let tc = cranelisp_typecheck::TypeCheckEnv::new(&shared_state.symbol_tables, &shared_state.next_type_id);
        tc.ensure_module_exists(module);
    }
    let mut ctx = ModuleCompiler {
        symbol_tables: &shared_state.symbol_tables,
        next_type_id: &shared_state.next_type_id,
        check_state: CheckState::new(module.clone()),
        current_module: module.clone(),
        scheduler: shared.scheduler,
        platform_registry: &mut platform_registry,
        typecheck_products: shared.typecheck_products,
        codegen_products: shared.codegen_products,
        introspection: shared.introspection,
        lib_dirs: shared.lib_dirs,
        platform_dirs: shared.platform_dirs,
        project_root: shared.project_root,
        shared_state: shared.shared_state,
    };

    match process_module_forms(
        &mut ctx, module, &sexps, start_idx,
        &mut state,
        ModuleStrategy::Replace,
    ) {
        Ok(ProcessResult::Complete { check_result, program }) => {
            // Post-typecheck codegen sweep.
            codegen_module_symbols(
                ctx.platform_registry,
                ctx.scheduler,
                module,
                &program,
                &check_result,
                ctx.symbol_tables,
                ctx.typecheck_products,
                ctx.codegen_products,
                None,
            )?;

            // Stash data for nice worker .o + .meta.json.
            stash_codegen_input(
                ctx.shared_state,
                module,
                check_result,
                program,
            );
            ctx.scheduler.notify_typecheck_done(module);

            // Clean up — module is done.
            {
                let mut map = shared.module_sexps.lock()
                    .unwrap_or_else(|e| e.into_inner());
                map.remove(module);
            }
            // suspend state was already removed above (taken out of map)
        }
        Ok(ProcessResult::Blocked {
            form_index,
            dep_module,
            dep_sexps,
        }) => {
            // Save resume state in scheduler.
            ctx.scheduler.set_resume_from_form(module, form_index);
            // Store dep sexps for workers to pick up.
            {
                let mut map = shared.module_sexps.lock()
                    .unwrap_or_else(|e| e.into_inner());
                map.entry(dep_module).or_insert(dep_sexps);
            }
            // Put suspend state back for resume.
            {
                let mut states = shared.suspend_states.lock()
                    .unwrap_or_else(|e| e.into_inner());
                states.insert(module.clone(), state);
            }
        }
        Err(e) => {
            // Clean up on failure.
            {
                let mut map = shared.module_sexps.lock()
                    .unwrap_or_else(|e| e.into_inner());
                map.remove(module);
            }
            return Err(e);
        }
    }

    Ok(())
}
