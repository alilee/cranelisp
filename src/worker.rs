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
    CheckResult, CranelispError, Defn, ExportSpec, ImportNames, ImportSpec,
    MacroClauseInfo, ModuleEntry, ModuleFullPath, ModuleStrategy,
    PlatformSpec, Sexp, Span, Symbol, TopLevel, Visibility,
};

use cranelisp_typecheck::{CheckPass, ModuleCheckAccumulator};

use crate::expander::{
    self, MacroClauseEntry, MacroEntry,
};
use crate::pipeline::compile_and_register_defn_shared;
use crate::platform_registry::PlatformRegistry;
use crate::scheduler::{CompileScheduler, PriorityWork};
use crate::session::{SharedCodegenState, WorkerJitState};

// ---------------------------------------------------------------------------
// WorkerContext — bundled worker parameters (G-1)
// ---------------------------------------------------------------------------

/// Shared context for the priority worker loop and process_module_forms.
///
/// Carries shared codegen state (`SharedCodegenState`, now `&` since all
/// fields use concurrent data structures) and per-worker JIT state
/// (`WorkerJitState`, `&mut` since it is per-worker owned state).
/// The TypeChecker remains `&mut` until `register_imports_with_state`
/// and `register_exports_with_state` are made `pub` on the TC crate.
/// PlatformRegistry remains `&mut` because `register()` needs mutation
/// during platform form processing.
pub struct WorkerContext<'a> {
    pub tc: &'a mut cranelisp_typecheck::TypeChecker,
    pub scheduler: &'a CompileScheduler,
    pub shared_codegen: &'a SharedCodegenState,
    pub worker_jit: &'a mut WorkerJitState,
    pub platform_registry: &'a mut PlatformRegistry,
    pub lib_dirs: &'a [PathBuf],
    pub project_root: &'a Path,
    /// Optional stash for nice workers to pick up object codegen data.
    /// When Some, the priority worker stores CheckResult + Program after
    /// in-memory codegen so nice workers can compile `.o` files.
    pub object_codegen_stash: Option<&'a std::sync::Mutex<
        HashMap<ModuleFullPath, crate::session_v4::ObjectCodegenInput>,
    >>,
    /// Optional reference to v4 shared state for cache-hit loading.
    /// None for REPL contexts where caching is not used.
    pub shared_state: Option<&'a crate::session_v4::SharedState>,
}

// ---------------------------------------------------------------------------
// ProcessResult — suspension-aware return type
// ---------------------------------------------------------------------------

/// Result of processing module forms. Either the module is fully typechecked,
/// or it blocked on a dependency and needs to be resumed later.
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
/// `accumulator`: may be a resumed accumulator (saved across suspension)
/// or freshly created for first invocation.
pub fn process_module_forms(
    ctx: &mut WorkerContext,
    module: &ModuleFullPath,
    sexps: &[Sexp],
    start_form_index: usize,
    accumulator: &mut ModuleCheckAccumulator,
    expanded_program: &mut Vec<TopLevel>,
    strategy: ModuleStrategy,
    pass1_done: &mut bool,
) -> Result<ProcessResult, CranelispError> {
    let is_fresh = !*pass1_done;

    if is_fresh && strategy == ModuleStrategy::Replace {
        // Set active module and clear for replace.
        ctx.tc.set_current_module(module.clone());
        ctx.tc.clear_module_for_replace_public();

        // Inject wildcard import of primitives and macros modules.
        inject_primitives_import(ctx.tc)?;
        inject_macros_import(ctx.tc)?;

        // Prelude injection: inject (import [prelude [*]]) for non-prelude modules
        // unless the source explicitly references prelude in an import or export (§8.8.1).
        if let Some(result) = inject_prelude_if_needed(ctx, module, sexps)? {
            return Ok(result);
        }
    } else if is_fresh && strategy == ModuleStrategy::Additive {
        // Additive: just set the active module. Module state persists
        // from previous evals — no clear, no re-injection.
        ctx.tc.set_current_module(module.clone());

        // Ensure macros module is imported (needed for quasiquote-based
        // macro expansion which references SexpSym, SexpInt, etc.).
        // Idempotent — register_imports handles duplicates gracefully.
        inject_macros_import(ctx.tc)?;
    } else {
        // Resume: set active module (may have been changed by dep processing).
        ctx.tc.set_current_module(module.clone());
    }

    // --- Pass 1: only on fresh start (not on resume after blocking) ---
    if is_fresh {
        let (regular_sexps, macro_infos) = separate_macros(sexps)?;

        // Build AST for regular (non-macro) forms.
        let program = cranelisp_frontend::build_program(&regular_sexps)?;
        let working_program = wrap_exprs_as_defns(&program);

        pass1_register(ctx.tc, module, &working_program, accumulator)?;

        for (name, info, sexp) in &macro_infos {
            register_macro_in_module(ctx.tc, name, info, sexp)?;
        }

        let defaults = register_default_methods(ctx.tc, module, accumulator)?;
        accumulator.default_method_defns = defaults;
        *pass1_done = true;
    }

    // --- Pass 2: per-sexp expand-then-check, from start_form_index ---
    // expanded_program accumulates across suspensions via the caller.
    let pass2_result = pass2_check_bodies_with_expansion(
        ctx, module, sexps, start_form_index, accumulator, expanded_program,
    )?;

    match pass2_result {
        Pass2Result::Complete => {
            finalize_module(ctx, module, expanded_program, accumulator, strategy)
        }
        Pass2Result::Blocked {
            form_index,
            dep_module,
            dep_sexps,
        } => {
            Ok(ProcessResult::Blocked {
                form_index,
                dep_module,
                dep_sexps,
            })
        }
    }
}

/// Separate defmacro forms from regular forms for Pass 1.
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
    ctx: &mut WorkerContext,
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
        let result = ctx.tc.check_form(module, &form, CheckPass::CheckBody, accumulator)?;
        ctx.tc.merge_form_result(module, accumulator, result);
    }

    let mut check_result = ctx.tc.finalize_check_result(
        module,
        accumulator,
        &final_working,
        strategy,
    )?;

    check_result.display =
        ctx.tc.compute_display_info_public(expanded_program, &accumulator.defn_type_vars);

    // NOTE: notify_typecheck_done is NOT called here. The caller is
    // responsible for stashing ObjectCodegenInput and calling
    // notify_typecheck_done AFTER, so that nice workers cannot claim
    // the module before the stash is populated.

    Ok(ProcessResult::Complete {
        check_result,
        program: expanded_program.to_vec(),
    })
}

/// Register a defmacro in the module table (Pass 1).
///
/// Parses clause info and stores it as `ModuleEntry::Macro` with the
/// original sexp for later compilation. No codegen — deferred until
/// first use.
fn register_macro_in_module(
    tc: &mut cranelisp_typecheck::TypeChecker,
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
    tc.symbol_table_mut().insert(
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
    Ok(())
}

/// Internal result from Pass 2 — either complete or blocked.
/// The expanded program is accumulated in the caller's mutable Vec.
enum Pass2Result {
    /// All forms processed. Expanded program is in the caller's Vec.
    Complete,
    /// Blocked on a dependency. Expanded program so far is in caller's Vec.
    Blocked {
        form_index: usize,
        dep_module: ModuleFullPath,
        dep_sexps: Vec<Sexp>,
    },
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
    ctx: &mut WorkerContext,
    module: &ModuleFullPath,
    sexps: &[Sexp],
    start_form_index: usize,
    accumulator: &mut ModuleCheckAccumulator,
    expanded_program: &mut Vec<TopLevel>,
) -> Result<Pass2Result, CranelispError> {
    // Collect macro infos from current sexps for expansion.
    let macro_infos: Vec<(Symbol, cranelisp_frontend::DefmacroInfo, Sexp)> = sexps
        .iter()
        .filter(|s| cranelisp_frontend::is_defmacro(s))
        .map(|s| {
            let info = cranelisp_frontend::parse_defmacro(s)?;
            Ok((info.name.clone(), info, s.clone()))
        })
        .collect::<Result<Vec<_>, CranelispError>>()?;
    let mut macro_names: Vec<String> = macro_infos.iter().map(|(n, _, _)| n.to_string()).collect();

    // Also collect macro names from the symbol table (previously registered macros,
    // e.g., from prior REPL evals or imported modules). These are needed so
    // `sexp_contains_macro_call` can detect calls to previously defined macros.
    let persistent_macro_names: Vec<Symbol> = collect_persistent_macro_names(ctx.tc);
    for name in &persistent_macro_names {
        let s = name.to_string();
        if !macro_names.contains(&s) {
            macro_names.push(s);
        }
    }

    for form_idx in start_form_index..sexps.len() {
        let sexp = &sexps[form_idx];

        // Build &str slice from owned names for this iteration.
        let name_refs: Vec<&str> = macro_names.iter().map(|s| s.as_str()).collect();

        match classify_form(sexp)? {
            FormKind::Import(specs) => {
                match handle_import(ctx, module, specs)? {
                    BlockAction::Continue => {}
                    BlockAction::Block { dep_module, dep_sexps } => {
                        return Ok(Pass2Result::Blocked {
                            form_index: form_idx,
                            dep_module,
                            dep_sexps,
                        });
                    }
                }
            }
            FormKind::Export(specs) => {
                match handle_export(ctx, module, &specs)? {
                    BlockAction::Continue => {}
                    BlockAction::Block { dep_module, dep_sexps } => {
                        return Ok(Pass2Result::Blocked {
                            form_index: form_idx,
                            dep_module,
                            dep_sexps,
                        });
                    }
                }
            }
            FormKind::Mod(decl) => {
                match handle_mod(ctx, module, &decl)? {
                    BlockAction::Continue => {}
                    BlockAction::Block { dep_module, dep_sexps } => {
                        return Ok(Pass2Result::Blocked {
                            form_index: form_idx,
                            dep_module,
                            dep_sexps,
                        });
                    }
                }
            }
            FormKind::Platform(spec) => {
                handle_platform(ctx, &spec)?;
            }
            FormKind::Defmacro => {
                continue; // registered in Pass 1
            }
            FormKind::Regular => {
                let new_macros = process_regular_form(
                    ctx, module, sexp, &macro_infos, &name_refs,
                    accumulator, expanded_program,
                )?;
                // Macros produced by expansion (e.g. const/def) become
                // available for subsequent forms.
                macro_names.extend(new_macros);
            }
        }
    }
    Ok(Pass2Result::Complete)
}

/// Process a regular (non-module-declaration) form in Pass 2.
///
/// Tries macro expansion, builds AST, registers any new signatures
/// (for begin-spliced defns), then typechecks the body.
///
/// Returns names of any macros newly registered from expansion results
/// (e.g. const/def expand to defmacro). These must be added to the
/// caller's macro_names so subsequent forms can expand them.
fn process_regular_form(
    ctx: &mut WorkerContext,
    module: &ModuleFullPath,
    sexp: &Sexp,
    macro_infos: &[(Symbol, cranelisp_frontend::DefmacroInfo, Sexp)],
    macro_names: &[&str],
    accumulator: &mut ModuleCheckAccumulator,
    expanded_program: &mut Vec<TopLevel>,
) -> Result<Vec<String>, CranelispError> {
    // Try macro expansion on the raw sexp.
    let effective_sexp = try_expand_for_pass2(
        sexp, module, ctx, macro_infos, macro_names, accumulator,
    )?;

    let sexp_to_build = match &effective_sexp {
        Some(expanded) => expanded,
        None => sexp,
    };

    let flattened = cranelisp_frontend::flatten_begin(sexp_to_build.clone());

    // Partition flattened forms: macro expansion (e.g. const, def) can produce
    // defmacro forms that must be routed through the macro pipeline, not the
    // AST builder which rejects them.
    let mut regular_sexps = Vec::new();
    let mut new_macro_names = Vec::new();
    for form in flattened {
        if cranelisp_frontend::is_defmacro(&form) {
            let info = cranelisp_frontend::parse_defmacro(&form)?;
            new_macro_names.push(info.name.to_string());
            register_macro_in_module(ctx.tc, &info.name, &info, &form)?;
            compile_macro_if_needed(ctx, module, &info, form.span(), accumulator)?;
        } else {
            regular_sexps.push(form);
        }
    }

    if regular_sexps.is_empty() {
        return Ok(new_macro_names);
    }

    let built = cranelisp_frontend::build_program(&regular_sexps)?;
    let working = wrap_exprs_as_defns(&built);

    // Register signatures for macro-expanded forms only. Non-expanded forms
    // were already registered in Pass 1 (pass1_register). Re-registering
    // causes "already defined" errors for traits.
    if effective_sexp.is_some() {
        for form in &working {
            let result = ctx.tc.check_form(module, form, CheckPass::Register, accumulator)?;
            ctx.tc.merge_form_result(module, accumulator, result);
        }
    }

    // Typecheck body for each form produced (Pass 2).
    for form in &working {
        let result = ctx.tc.check_form(module, form, CheckPass::CheckBody, accumulator)?;
        ctx.tc.merge_form_result(module, accumulator, result);

        if let TopLevel::Defn(defn) = form {
            ctx.scheduler.notify_symbol_typechecked(module, &defn.name);
        }
    }

    expanded_program.extend(built);
    Ok(new_macro_names)
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
    ctx: &mut WorkerContext,
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
        if ctx.tc.has_module(dep) {
            ctx.tc.register_imports(std::slice::from_ref(spec))?;
            continue;
        }

        // Resolve file path.
        let dep_file = crate::pipeline::resolve_module_file(dep, ctx.lib_dirs)
            .ok_or_else(|| CranelispError::ModuleError {
                message: format!(
                    "module '{}' not found (imported by '{}')",
                    dep, module
                ),
                file: None,
                span: spec.span,
            })?;

        // Populate file_to_module mapping for file watcher (Step 14).
        if let Some(shared) = ctx.shared_state {
            if let Ok(canonical) = dep_file.canonicalize() {
                shared
                    .file_to_module
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .insert(canonical, dep.clone());
            }
        }

        // Cache check: try to load from disk cache before parsing.
        if try_cache_hit_load(ctx, dep, &dep_file) {
            ctx.tc.register_imports(std::slice::from_ref(spec))?;
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
    ctx: &mut WorkerContext,
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
    let mangled_names: Vec<String> = cached
        .codegen_state()
        .got_slots
        .keys()
        .map(|s| s.as_ref().to_string())
        .collect();
    let got_slot_keys: Vec<Symbol> = cached
        .codegen_state()
        .got_slots
        .keys()
        .cloned()
        .collect();

    // Restore type info into TC (consumes symbol_table by value).
    ctx.tc.restore_cached_module(cached.metadata.symbol_table);

    // Restore trait impl registrations from cached codegen state.
    ctx.tc.restore_cached_impls(&mangled_names);

    // 5. Register with scheduler at TypecheckDone.
    ctx.scheduler.register_module_cached(dep.clone(), symbols);

    // 6. Pre-register GOT slots for cached module's symbols.
    for sym_name in &got_slot_keys {
        let _ = ctx.shared_codegen.ensure_slot_for(sym_name);
    }

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
    ctx: &mut WorkerContext,
    module: &ModuleFullPath,
    specs: &[ExportSpec],
) -> Result<BlockAction, CranelispError> {
    for spec in specs {
        let dep = &spec.module_path;

        // Already loaded — continue to the next spec.
        if ctx.tc.has_module(dep) {
            continue;
        }

        // Source module not loaded — need to load it first.
        // Resolve file path.
        let dep_file = crate::pipeline::resolve_module_file(dep, ctx.lib_dirs)
            .ok_or_else(|| CranelispError::ModuleError {
                message: format!(
                    "module '{}' not found (re-exported by '{}')",
                    dep, module
                ),
                file: None,
                span: spec.span,
            })?;

        // Populate file_to_module mapping for file watcher.
        if let Some(shared) = ctx.shared_state {
            if let Ok(canonical) = dep_file.canonicalize() {
                shared
                    .file_to_module
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .insert(canonical, dep.clone());
            }
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

        // Register dep with scheduler and block.
        ctx.scheduler.register_module(dep.clone(), true);
        ctx.scheduler.block_for_typecheck(module, dep, &Symbol::from("*"))?;

        return Ok(BlockAction::Block {
            dep_module: dep.clone(),
            dep_sexps,
        });
    }

    // All source modules loaded — register the re-exports.
    ctx.tc.register_exports(specs)?;
    Ok(BlockAction::Continue)
}

/// Handle mod forms: write inline body to disk, then load the submodule.
///
/// `(mod util)` declares a submodule whose symbols are accessible via qualified
/// references like `util/helper`. The submodule must be loaded (typechecked)
/// before the parent can resolve these references, so we block for it — same
/// as `handle_import` does for explicit imports.
fn handle_mod(
    ctx: &mut WorkerContext,
    module: &ModuleFullPath,
    decl: &cranelisp_types::ModDecl,
) -> Result<BlockAction, CranelispError> {
    if let Some(body_sexps) = &decl.inline_body {
        write_inline_mod_to_disk(module, &decl.name, body_sexps, ctx.project_root)?;
    }

    // Compute submodule path: "main" + "util" → "main.util"
    let sub_path = ModuleFullPath::from(format!("{}.{}", module, decl.name));

    // Already loaded — register GOT aliases for qualified references and continue.
    if ctx.tc.has_module(&sub_path) {
        register_submodule_got_aliases(ctx.shared_codegen, module, &sub_path);
        return Ok(BlockAction::Continue);
    }

    // Resolve file path.
    let dep_file = crate::pipeline::resolve_module_file(&sub_path, ctx.lib_dirs)
        .ok_or_else(|| CranelispError::ModuleError {
            message: format!(
                "submodule '{}' not found (declared by '{}')",
                sub_path, module
            ),
            file: None,
            span: decl.span,
        })?;

    // Populate file_to_module mapping for file watcher.
    if let Some(shared) = ctx.shared_state {
        if let Ok(canonical) = dep_file.canonicalize() {
            shared
                .file_to_module
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .insert(canonical, sub_path.clone());
        }
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

/// Register GOT aliases so the parent module can call submodule functions
/// via qualified names (e.g., `util/helper` → same GOT slot as `helper`).
///
/// Uses `generate_module_aliases` to produce all alias forms (last-component,
/// suffix, full-path) then registers each as a GOT alias pointing to the
/// same slot as the base symbol.
fn register_submodule_got_aliases(
    shared_codegen: &SharedCodegenState,
    _parent_module: &ModuleFullPath,
    sub_module: &ModuleFullPath,
) {
    let mod_str: &str = sub_module.as_ref();

    // Collect (base_name, slot) pairs from shared codegen.
    let entries: Vec<(Symbol, usize)> = shared_codegen
        .def_codegen
        .iter()
        .filter_map(|entry| {
            entry.got_slot.map(|slot| (entry.key().clone(), slot))
        })
        .collect();

    for (name, slot) in &entries {
        for alias in crate::session::generate_module_aliases(mod_str, name.as_ref()) {
            let qualified = Symbol::from(alias);
            // Only register if not already present.
            if !shared_codegen.def_codegen.contains_key(&qualified) {
                let mut entry = shared_codegen.def_codegen.entry(qualified).or_default();
                entry.got_slot = Some(*slot);
            }
        }
    }
}

/// Handle platform forms: load DLL and register type signatures.
///
/// Platform loading is NOT a cross-module blocking operation. The DLL is
/// loaded synchronously. Type signatures are registered in TC immediately.
fn handle_platform(
    ctx: &mut WorkerContext,
    spec: &PlatformSpec,
) -> Result<(), CranelispError> {
    let (platform, _jit_syms) = crate::platform::load_and_register_platform(
        ctx.tc,
        &spec.name,
        ctx.project_root,
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
/// Walks the sexp tree looking for macro calls. If any macros need
/// compilation, compiles them inline first (only transitive deps of
/// the called macros, not all macros). Returns Ok(Some(expanded))
/// if any expansion occurred, Ok(None) if the sexp contains no macro calls.
fn try_expand_for_pass2(
    sexp: &Sexp,
    module: &ModuleFullPath,
    ctx: &mut WorkerContext,
    macro_infos: &[(Symbol, cranelisp_frontend::DefmacroInfo, Sexp)],
    macro_names: &[&str],
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<Option<Sexp>, CranelispError> {
    // Check if this sexp tree contains any macro calls at all.
    if !sexp_contains_macro_call(sexp, macro_names) {
        return Ok(None);
    }

    // Compile macros called in this sexp and their transitive uncompiled
    // dependencies.
    let called_macros = collect_called_macros(sexp, macro_names);
    for macro_name in &called_macros {
        if let Some((_name, info, _)) = macro_infos.iter().find(|(n, _, _)| n.as_ref() == *macro_name) {
            compile_macro_if_needed(
                ctx, module, info, sexp.span(), accumulator,
            )?;
        } else {
            // Macro from a prior eval or imported module — compile on demand.
            compile_persistent_macro_if_needed(ctx, module, macro_name, sexp.span(), accumulator)?;
        }
    }

    // Recursive expansion may produce calls to macros not directly called
    // in the original sexp. Ensure all registered macros are compiled so
    // expand_sexp_recursive can find their function pointers.
    for (_name, info, _) in macro_infos {
        compile_macro_if_needed(
            ctx, module, info, sexp.span(), accumulator,
        )?;
    }

    // Build the full macro map for expansion (includes all compiled macros
    // so recursive expansion can find macros produced by other macros).
    let mut all_macros = build_all_macro_entries(ctx.shared_codegen, macro_infos)?;

    // Also include previously compiled macros from the symbol table
    // (e.g., from prior REPL evals or imported modules).
    build_persistent_macro_entries(ctx.tc, ctx.shared_codegen, &mut all_macros)?;

    // Expand recursively throughout the entire sexp tree.
    let expanded = expander::expand_sexp_recursive(sexp.clone(), &all_macros, 0)?;

    Ok(Some(expanded))
}

/// Collect the names of macros directly called in a sexp tree.
fn collect_called_macros<'a>(sexp: &Sexp, macro_names: &[&'a str]) -> Vec<&'a str> {
    let mut found = Vec::new();
    collect_called_macros_inner(sexp, macro_names, &mut found);
    found
}

fn collect_called_macros_inner<'a>(sexp: &Sexp, macro_names: &[&'a str], found: &mut Vec<&'a str>) {
    match sexp {
        Sexp::List(children, _) if !children.is_empty() => {
            if let Sexp::Symbol(name, _) = &children[0]
                && let Some(&m) = macro_names.iter().find(|&&m| m == name.as_str())
                && !found.contains(&m)
            {
                found.push(m);
            }
            for c in children {
                collect_called_macros_inner(c, macro_names, found);
            }
        }
        Sexp::Symbol(name, _) => {
            if let Some(&m) = macro_names.iter().find(|&&m| m == name.as_str())
                && !found.contains(&m)
            {
                found.push(m);
            }
        }
        Sexp::Bracket(children, _) => {
            for c in children {
                collect_called_macros_inner(c, macro_names, found);
            }
        }
        _ => {}
    }
}

/// Check if a sexp tree contains any call to a known macro.
fn sexp_contains_macro_call(sexp: &Sexp, macro_names: &[&str]) -> bool {
    match sexp {
        Sexp::List(children, _) if !children.is_empty() => {
            if let Sexp::Symbol(name, _) = &children[0]
                && macro_names.contains(&name.as_str())
            {
                return true;
            }
            children.iter().any(|c| sexp_contains_macro_call(c, macro_names))
        }
        Sexp::Symbol(name, _) => {
            // Bare symbol that is a zero-arg macro.
            macro_names.contains(&name.as_str())
        }
        Sexp::Bracket(children, _) => {
            children.iter().any(|c| sexp_contains_macro_call(c, macro_names))
        }
        _ => false,
    }
}



/// Compile all clauses of a macro if any clause lacks a function pointer.
///
/// Before compiling macro clauses, walks the transitive callees of the
/// macro (from `ModuleEntry.callees`) and compiles any uncompiled
/// dependencies first. Notifies the scheduler after each symbol is compiled.
fn compile_macro_if_needed(
    ctx: &mut WorkerContext,
    module: &ModuleFullPath,
    info: &cranelisp_frontend::DefmacroInfo,
    span: Span,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    // Check if all clauses already have function pointers.
    let all_compiled = info.clauses.iter().enumerate().all(|(idx, _)| {
        let clause_name = macro_clause_jit_name(&info.name, idx);
        has_code_ptr(ctx.shared_codegen, &clause_name)
    });

    if all_compiled {
        return Ok(());
    }

    // Walk transitive callees and compile uncompiled deps first.
    let uncompiled_deps = collect_transitive_uncompiled_deps(
        ctx.tc, ctx.shared_codegen, module, &info.name,
    );
    // Compute platform JIT symbols once, outside the dep compilation loop.
    let platform_symbols = ctx.platform_registry.jit_symbols_owned();
    let current_module = ctx.tc.current_module_path().clone();
    for (dep_module, dep_symbol) in &uncompiled_deps {
        compile_dep_symbol_inline(
            ctx.tc, ctx.shared_codegen, ctx.worker_jit, &platform_symbols,
            dep_module, dep_symbol, &current_module, accumulator,
        )?;
        ctx.scheduler.notify_inmem_codegen_complete(dep_module, dep_symbol, false);
    }

    // Compile each clause that is not yet compiled.
    let total_clauses = info.clauses.len();
    for (clause_idx, clause) in info.clauses.iter().enumerate() {
        let clause_name = macro_clause_jit_name(&info.name, clause_idx);
        if has_code_ptr(ctx.shared_codegen, &clause_name) {
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
    tc: &cranelisp_typecheck::TypeChecker,
    shared_codegen: &SharedCodegenState,
    module: &ModuleFullPath,
    start_symbol: &Symbol,
) -> Vec<(ModuleFullPath, Symbol)> {
    use std::collections::HashSet;
    use std::collections::VecDeque;

    let mut visited: HashSet<(ModuleFullPath, Symbol)> = HashSet::new();
    let mut queue: VecDeque<(ModuleFullPath, Symbol)> = VecDeque::new();
    let mut result: Vec<(ModuleFullPath, Symbol)> = Vec::new();

    // Seed with the starting symbol's callees.
    if let Some(table) = tc.module_table(module)
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
        if let Some(table) = tc.module_table(&dep_mod)
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
        if !has_code_ptr(shared_codegen, &dep_sym) {
            result.push((dep_mod, dep_sym));
        }
    }

    result
}

/// Compile a dependency symbol inline using the accumulated check state.
///
/// Looks up the defn from the GOT state (it has been typechecked
/// in Pass 2 already since deps are defined before the macro) and
/// compiles it via `compile_and_register_defn`.
///
/// For same-module deps, uses the current module's accumulator to build
/// the CheckResult (method_resolutions, expr_types). For cross-module
/// deps, builds a CheckResult with empty resolutions — the dep module's
/// transient check state has already been consumed. Type defs and
/// constructor_to_type come from the TC's global registry in both cases.
fn compile_dep_symbol_inline(
    tc: &cranelisp_typecheck::TypeChecker,
    shared_codegen: &SharedCodegenState,
    worker_jit: &mut WorkerJitState,
    platform_symbols: &[(String, *const u8)],
    module: &ModuleFullPath,
    symbol: &Symbol,
    current_module: &ModuleFullPath,
    accumulator: &ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    // Build the CheckResult from the appropriate source.
    let check = if module == current_module {
        // Same module: accumulator has the method_resolutions and expr_types.
        build_check_from_accumulator(tc, accumulator)
    } else {
        // Cross-module: the dep module's transient check state was consumed
        // when it was finalized. Build a minimal CheckResult with type defs
        // from the TC's global registry. Method resolutions and expr_types
        // are empty — cross-module macro helpers are expected to be simple
        // functions without trait dispatch.
        build_empty_check_from_tc(tc)
    };

    // The defn was already typechecked; we need its AST for compilation.
    // Look it up from the shared codegen state's stored defns.
    let defn = shared_codegen
        .def_codegen
        .get(symbol)
        .and_then(|dc| dc.defn.clone());

    if let Some(defn) = defn {
        compile_and_register_defn_shared(shared_codegen, worker_jit, platform_symbols, &defn, &check)?;
    }
    // If not found in def_codegen, the symbol may be a builtin/primitive
    // that is always available — nothing to compile.

    Ok(())
}

/// Build an empty CheckResult with only type defs from the TC.
///
/// Used for cross-module deps where the dep module's transient check state
/// (method_resolutions, expr_types) has already been consumed.
fn build_empty_check_from_tc(
    tc: &cranelisp_typecheck::TypeChecker,
) -> CheckResult {
    let (type_defs, constructor_to_type) = tc.snapshot_type_defs();
    CheckResult {
        method_resolutions: std::collections::HashMap::new(),
        constrained_fn_names: std::collections::HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: std::collections::HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
        type_defs,
        constructor_to_type,
        display: None,
    }
}

/// Build a CheckResult from the accumulator's current state.
///
/// Used for inline macro compilation. Mono defns and default methods are
/// not needed for macro clause codegen, so they are left empty.
/// Type defs and constructor_to_type are snapshotted from the TC registry
/// (required for Sexp constructor codegen in macro clause bodies).
fn build_check_from_accumulator(
    tc: &cranelisp_typecheck::TypeChecker,
    accumulator: &ModuleCheckAccumulator,
) -> CheckResult {
    let (type_defs, constructor_to_type) = tc.snapshot_type_defs();
    CheckResult {
        method_resolutions: accumulator.method_resolutions.clone(),
        constrained_fn_names: accumulator.constrained_fn_names.clone(),
        mono_defns: Vec::new(),
        expr_types: accumulator.expr_types.clone(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
        type_defs,
        constructor_to_type,
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
    ctx: &mut WorkerContext,
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
    let module = ctx.tc.current_module_path().clone();
    for form in &program {
        let result = ctx.tc.check_form(&module, form, CheckPass::Register, accumulator)?;
        ctx.tc.merge_form_result(&module, accumulator, result);
    }
    for form in &program {
        let result = ctx.tc.check_form(&module, form, CheckPass::CheckBody, accumulator)?;
        ctx.tc.merge_form_result(&module, accumulator, result);
    }

    // Build a CheckResult from the accumulator for codegen.
    let check = build_check_from_accumulator(ctx.tc, accumulator);

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

    // Compile using a special JIT that disables dealloc for macro code.
    compile_macro_defn_no_dealloc(ctx.shared_codegen, ctx.worker_jit, ctx.platform_registry, defn, &check)?;

    Ok(())
}

/// Compile a macro clause defn with dealloc disabled.
///
/// Macro functions build throwaway Sexp trees that are marshalled back to
/// the compiler. Disabling dealloc prevents use-after-free on unmarshal.
fn compile_macro_defn_no_dealloc(
    shared_codegen: &SharedCodegenState,
    worker_jit: &mut WorkerJitState,
    platform_registry: &PlatformRegistry,
    defn: &Defn,
    check: &CheckResult,
) -> Result<(), CranelispError> {
    let extra_symbols = platform_registry.jit_symbols();
    let mut jit = cranelisp_backend::jit::Jit::new_with_symbols(&extra_symbols)?;
    jit.declare_intrinsics()?;

    let func_ids = jit.declare_functions(&[defn])?;
    let func_arities: HashMap<Symbol, usize> =
        func_ids.keys().map(|n| (n.clone(), defn.params().len())).collect();

    // Build compile context with dealloc disabled.
    let mut compile_ctx = jit.build_compile_context(
        check,
        &func_ids,
        &func_arities,
        None,
        None,
        None,
    );
    compile_ctx.dealloc_func_id = None;
    jit.compile_defn(defn, compile_ctx)?;

    let ptr = jit.finalize_and_get_ptr(&defn.name, defn.params().len())?;

    // Register in GOT.
    let slot = shared_codegen.ensure_slot_for(&defn.name)?;
    shared_codegen.update_slot(slot, ptr);

    let mut entry = shared_codegen.def_codegen.entry(defn.name.clone()).or_default();
    entry.code_ptr = Some(ptr);
    entry.got_slot = Some(slot);
    entry.param_count = Some(defn.params().len());
    entry.defn = Some(defn.clone());
    drop(entry); // Release DashMap shard lock explicitly.

    // Keep JIT alive so the function pointer remains valid.
    worker_jit.jit_modules.push(jit);

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

/// Check if a symbol has a compiled code pointer in the GOT.
fn has_code_ptr(shared_codegen: &SharedCodegenState, name: &Symbol) -> bool {
    shared_codegen
        .def_codegen
        .get(name)
        .and_then(|dc| dc.code_ptr)
        .is_some()
}

/// Get a code pointer from the shared codegen state, if compiled.
fn get_code_ptr(shared_codegen: &SharedCodegenState, name: &Symbol) -> Option<*const u8> {
    shared_codegen
        .def_codegen
        .get(name)
        .and_then(|dc| dc.code_ptr)
}

/// Build a `MacroEntry` from GOT function pointers for a macro.
///
/// Used after inline compilation to construct the entry needed by
/// `invoke_clause` and `find_matching_clause`.
fn build_macro_entry_from_got(
    shared_codegen: &SharedCodegenState,
    info: &cranelisp_frontend::DefmacroInfo,
) -> Result<MacroEntry, CranelispError> {
    let mut clauses = Vec::new();

    for (idx, clause) in info.clauses.iter().enumerate() {
        let clause_name = macro_clause_jit_name(&info.name, idx);
        let code_ptr = shared_codegen
            .def_codegen
            .get(&clause_name)
            .and_then(|dc| dc.code_ptr)
            .ok_or_else(|| CranelispError::MacroError {
                message: format!(
                    "macro clause '{}' not compiled (expected in GOT)",
                    clause_name
                ),
                span: info.span,
            })?;

        clauses.push(MacroClauseEntry {
            func_ptr: code_ptr,
            params: clause.fixed_params.clone(),
            rest_param: clause.rest_param.clone(),
        });
    }

    Ok(MacroEntry {
        clauses,
        docstring: info.docstring.clone(),
    })
}

/// Build a macro map for all macros in the module (for recursive expansion).
fn build_all_macro_entries(
    shared_codegen: &SharedCodegenState,
    macro_infos: &[(Symbol, cranelisp_frontend::DefmacroInfo, Sexp)],
) -> Result<HashMap<Symbol, MacroEntry>, CranelispError> {
    let mut map = HashMap::new();
    for (name, info, _) in macro_infos {
        // Only include macros that have been compiled.
        let all_compiled = info.clauses.iter().enumerate().all(|(idx, _)| {
            let clause_name = macro_clause_jit_name(name, idx);
            has_code_ptr(shared_codegen, &clause_name)
        });
        if all_compiled {
            let entry = build_macro_entry_from_got(shared_codegen, info)?;
            map.insert(name.clone(), entry);
        }
    }
    Ok(map)
}

/// Collect names of macros available in the current module's symbol table.
///
/// Includes both directly defined Macro entries and Import entries that
/// resolve to macros in other modules. This ensures `sexp_contains_macro_call`
/// detects calls to imported macros from the prelude or other modules.
fn collect_persistent_macro_names(tc: &cranelisp_typecheck::TypeChecker) -> Vec<Symbol> {
    let mut names = Vec::new();
    let sym_table = tc.symbol_table();
    for (name, entry) in sym_table.all_symbols() {
        match entry {
            ModuleEntry::Macro { .. } => {
                names.push(name.clone());
            }
            ModuleEntry::Import { source } => {
                // Follow the import to check if the source is a macro.
                if let Some(source_table) = tc.module_table(&source.module)
                    && matches!(
                        source_table.get(source.symbol.as_ref()),
                        Some(ModuleEntry::Macro { .. })
                            | Some(ModuleEntry::Reexport { .. })
                    )
                {
                    names.push(name.clone());
                }
                // Also check through Reexport chains.
                if let Some(source_table) = tc.module_table(&source.module)
                    && let Some(ModuleEntry::Reexport { source: re_source }) =
                        source_table.get(source.symbol.as_ref())
                    && let Some(re_table) = tc.module_table(&re_source.module)
                    && matches!(
                        re_table.get(re_source.symbol.as_ref()),
                        Some(ModuleEntry::Macro { .. })
                    )
                {
                    if !names.contains(name) {
                        names.push(name.clone());
                    }
                }
            }
            _ => {}
        }
    }
    names
}

/// Compile a persistent macro (from symbol table) on demand.
///
/// Looks up the macro's sexp from the symbol table (following Import/Reexport
/// chains as needed), parses DefmacroInfo, and compiles clauses if not already compiled.
fn compile_persistent_macro_if_needed(
    ctx: &mut WorkerContext,
    module: &ModuleFullPath,
    macro_name: &str,
    span: Span,
    accumulator: &mut cranelisp_typecheck::ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    // Check if already compiled.
    let clause_name_0 = macro_clause_jit_name(&Symbol::from(macro_name), 0);
    if has_code_ptr(ctx.shared_codegen, &clause_name_0) {
        return Ok(());
    }

    // Find the macro sexp, following Import/Reexport chains.
    let macro_sexp = resolve_macro_sexp(ctx.tc, macro_name);

    if let Some(sexp) = macro_sexp {
        let info = cranelisp_frontend::parse_defmacro(&sexp)?;
        compile_macro_if_needed(ctx, module, &info, span, accumulator)?;
    }

    Ok(())
}

/// Resolve a macro's sexp by following Import/Reexport chains.
fn resolve_macro_sexp(
    tc: &cranelisp_typecheck::TypeChecker,
    name: &str,
) -> Option<Sexp> {
    let sym_table = tc.symbol_table();
    let entry = sym_table.get(name)?;
    match entry {
        ModuleEntry::Macro { sexp, .. } => sexp.clone(),
        ModuleEntry::Import { source } => {
            let source_mod = source.module.clone();
            let source_sym: String = source.symbol.as_ref().to_string();
            drop(sym_table); // Release DashMap guard before acquiring another.
            let source_table = tc.module_table(&source_mod)?;
            match source_table.get(&source_sym)? {
                ModuleEntry::Macro { sexp, .. } => sexp.clone(),
                ModuleEntry::Reexport { source: re_source } => {
                    let re_mod = re_source.module.clone();
                    let re_sym: String = re_source.symbol.as_ref().to_string();
                    drop(source_table);
                    let re_table = tc.module_table(&re_mod)?;
                    if let ModuleEntry::Macro { sexp, .. } = re_table.get(&re_sym)? {
                        sexp.clone()
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Compile a macro's clauses for REPL use.
///
/// Called from `make_defmacro_result` to ensure the macro is compiled and
/// available for expansion in subsequent REPL evals.
pub fn compile_macro_for_repl(
    ctx: &mut WorkerContext,
    module: &ModuleFullPath,
    info: &cranelisp_frontend::DefmacroInfo,
    span: Span,
    accumulator: &mut cranelisp_typecheck::ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    compile_macro_if_needed(ctx, module, info, span, accumulator)
}

/// Build macro entries from the TC symbol table for macros already compiled
/// in prior REPL evals or imported modules. Only adds entries not already
/// present in the map (current-sexp macros take priority).
///
/// Follows Import/Reexport chains to find actual Macro entries.
fn build_persistent_macro_entries(
    tc: &cranelisp_typecheck::TypeChecker,
    shared_codegen: &SharedCodegenState,
    map: &mut HashMap<Symbol, MacroEntry>,
) -> Result<(), CranelispError> {
    let persistent_names = collect_persistent_macro_names(tc);
    for name in &persistent_names {
        if map.contains_key(name) {
            continue;
        }
        // Resolve the actual Macro entry (may be behind Import/Reexport).
        let (clauses, docstring) = match resolve_macro_entry(tc, name.as_ref()) {
            Some(resolved) => resolved,
            None => continue,
        };

        // Check if all clauses have code pointers in the GOT.
        let all_compiled = clauses.iter().enumerate().all(|(idx, _)| {
            let clause_name = macro_clause_jit_name(name, idx);
            has_code_ptr(shared_codegen, &clause_name)
        });
        if all_compiled && !clauses.is_empty() {
            let mut compiled_clauses = Vec::new();
            for (idx, clause_info) in clauses.iter().enumerate() {
                let clause_name = macro_clause_jit_name(name, idx);
                let code_ptr = get_code_ptr(shared_codegen, &clause_name)
                    .ok_or_else(|| CranelispError::CodegenError {
                        message: format!(
                            "macro '{}' clause {} not compiled ({})",
                            name, idx, clause_name
                        ),
                        span: Span::SYNTHETIC,
                    })?;
                compiled_clauses.push(MacroClauseEntry {
                    func_ptr: code_ptr,
                    params: clause_info.params.clone(),
                    rest_param: clause_info.rest_param.clone(),
                });
            }
            map.insert(name.clone(), MacroEntry {
                clauses: compiled_clauses,
                docstring,
            });
        }
    }
    Ok(())
}

/// Resolve a macro entry's clauses and docstring by following Import/Reexport chains.
fn resolve_macro_entry(
    tc: &cranelisp_typecheck::TypeChecker,
    name: &str,
) -> Option<(Vec<MacroClauseInfo>, Option<String>)> {
    let sym_table = tc.symbol_table();
    let entry = sym_table.get(name)?;
    match entry {
        ModuleEntry::Macro { clauses, docstring, .. } => {
            Some((clauses.clone(), docstring.clone()))
        }
        ModuleEntry::Import { source } => {
            let source_mod = source.module.clone();
            let source_sym: String = source.symbol.as_ref().to_string();
            drop(sym_table);
            let table = tc.module_table(&source_mod)?;
            match table.get(&source_sym)? {
                ModuleEntry::Macro { clauses, docstring, .. } => {
                    Some((clauses.clone(), docstring.clone()))
                }
                ModuleEntry::Reexport { source: re_source } => {
                    let re_mod = re_source.module.clone();
                    let re_sym: String = re_source.symbol.as_ref().to_string();
                    drop(table);
                    let re_table = tc.module_table(&re_mod)?;
                    if let ModuleEntry::Macro { clauses, docstring, .. } =
                        re_table.get(&re_sym)?
                    {
                        Some((clauses.clone(), docstring.clone()))
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Pass 1: register all forms' type signatures in source order.
fn pass1_register(
    tc: &mut cranelisp_typecheck::TypeChecker,
    module: &ModuleFullPath,
    working_program: &[TopLevel],
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    for form in working_program {
        let result = tc.check_form(module, form, CheckPass::Register, accumulator)?;
        tc.merge_form_result(module, accumulator, result);
    }
    Ok(())
}

/// Register default method defns generated during Pass 1 TraitImpl processing.
fn register_default_methods(
    tc: &mut cranelisp_typecheck::TypeChecker,
    module: &ModuleFullPath,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<Vec<Defn>, CranelispError> {
    let defaults: Vec<Defn> = std::mem::take(&mut accumulator.default_method_defns);
    for defn in &defaults {
        let form = TopLevel::Defn(defn.clone());
        let result = tc.check_form(module, &form, CheckPass::Register, accumulator)?;
        tc.merge_form_result(module, accumulator, result);
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
    ctx: &mut WorkerContext,
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

    if !ctx.tc.has_module(&prelude_path) {
        // Discover prelude through the same lazy path as any user import.
        let prelude_file = crate::session::resolve_prelude(
            ctx.project_root,
            ctx.lib_dirs,
        );
        if let Some(prelude_file) = prelude_file {
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
        // No prelude file found — continue without prelude.
        // Operators will fail at typecheck, which is correct behavior.
    } else {
        // Prelude already loaded — register the import.
        let prelude_spec = ImportSpec {
            module_path: prelude_path,
            alias: None,
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        };
        ctx.tc.register_imports(&[prelude_spec])?;
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
/// For the v4 scheduler path (C3: no prelude injection), modules still need
/// access to named primitives (add-i64, sub-i64, etc.). This injects
/// `(import [primitives [*]])` so primitives are available by bare name.
fn inject_primitives_import(
    tc: &mut cranelisp_typecheck::TypeChecker,
) -> Result<(), CranelispError> {
    let import_spec = ImportSpec {
        module_path: ModuleFullPath::from("primitives"),
        alias: None,
        names: cranelisp_types::ImportNames::Glob,
        span: Span::SYNTHETIC,
    };
    tc.register_imports(&[import_spec])
}

/// Inject a wildcard import of the `macros` module into the current module.
///
/// Macros need Sexp constructors (SexpSym, SexpInt, SCons, SNil, etc.)
/// which live in the synthetic `macros` module.
fn inject_macros_import(
    tc: &mut cranelisp_typecheck::TypeChecker,
) -> Result<(), CranelispError> {
    let import_spec = ImportSpec {
        module_path: ModuleFullPath::from("macros"),
        alias: None,
        names: cranelisp_types::ImportNames::Glob,
        span: Span::SYNTHETIC,
    };
    tc.register_imports(&[import_spec])
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
pub fn codegen_module_symbols(
    shared_codegen: &SharedCodegenState,
    worker_jit: &mut WorkerJitState,
    platform_registry: &PlatformRegistry,
    scheduler: &CompileScheduler,
    module: &ModuleFullPath,
    program: &[TopLevel],
    check: &CheckResult,
) -> Result<(), CranelispError> {
    // Convert platform registry to owned JIT symbols once for the codegen sweep.
    let platform_symbols = platform_registry.jit_symbols_owned();

    // Pre-register all defn names in GOT for forward references.
    pre_register_got_slots(shared_codegen, program)?;

    // Compile default method bodies.
    for defn in &check.default_method_defns {
        compile_and_register_defn_shared(shared_codegen, worker_jit, &platform_symbols, defn, check)?;
    }

    // Compile mono specializations with per-specialization resolutions.
    compile_mono_defns(shared_codegen, worker_jit, &platform_symbols, check)?;

    // Compile each regular defn.
    let defn_names = compile_regular_defns(shared_codegen, worker_jit, &platform_symbols, program, check)?;

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

/// Pre-register GOT slots for all definitions in the program.
fn pre_register_got_slots(
    shared_codegen: &SharedCodegenState,
    program: &[TopLevel],
) -> Result<(), CranelispError> {
    for tl in program {
        match tl {
            TopLevel::Defn(defn) => {
                shared_codegen.ensure_slot_for(&defn.name)?;
            }
            TopLevel::TraitImpl(impl_) => {
                for method in &impl_.methods {
                    shared_codegen.ensure_slot_for(&method.name)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// Compile monomorphised specializations.
fn compile_mono_defns(
    shared_codegen: &SharedCodegenState,
    worker_jit: &mut WorkerJitState,
    platform_symbols: &[(String, *const u8)],
    check: &CheckResult,
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
            type_defs: check.type_defs.clone(),
            constructor_to_type: check.constructor_to_type.clone(),
            display: None,
        };
        compile_and_register_defn_shared(shared_codegen, worker_jit, platform_symbols, &mono.defn, &mono_check)?;
    }
    Ok(())
}

/// Compile regular defns (skipping constrained fn base definitions).
/// Returns the list of compiled symbol names.
fn compile_regular_defns(
    shared_codegen: &SharedCodegenState,
    worker_jit: &mut WorkerJitState,
    platform_symbols: &[(String, *const u8)],
    program: &[TopLevel],
    check: &CheckResult,
) -> Result<Vec<Symbol>, CranelispError> {
    let mut compiled_names = Vec::new();

    for tl in program {
        match tl {
            TopLevel::Defn(defn) => {
                if check.constrained_fn_names.contains(&defn.name) {
                    continue;
                }
                compile_and_register_defn_shared(shared_codegen, worker_jit, platform_symbols, defn, check)?;
                compiled_names.push(defn.name.clone());

                // Note: zero-arg defns (e.g., `main`) are NOT executed here.
                // The codegen sweep only compiles and registers code pointers
                // in the GOT. Execution is done separately by `trampoline`.
            }
            TopLevel::TraitImpl(impl_) => {
                for method in &impl_.methods {
                    compile_and_register_defn_shared(
                        shared_codegen,
                        worker_jit,
                        platform_symbols,
                        method,
                        check,
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
/// the GOT. This is the inmem codegen fast-path for cache-hit modules:
/// one mmap + relocation pass loads all symbols at once.
///
/// Returns the list of symbol names that were loaded, for scheduler notification.
fn load_cached_module_via_linker(
    shared_codegen: &SharedCodegenState,
    worker_jit: &mut WorkerJitState,
    platform_registry: &PlatformRegistry,
    module: &ModuleFullPath,
    shared_state: Option<&crate::session_v4::SharedState>,
) -> Result<Vec<Symbol>, CranelispError> {
    use cranelisp_backend::cache;

    // Determine cache directory from shared state.
    let shared = shared_state.ok_or_else(|| CranelispError::ModuleError {
        message: format!("no shared state for cache-hit loading of '{}'", module),
        file: None,
        span: Span::SYNTHETIC,
    })?;
    let cache_dir = shared.cache_dir.as_ref().ok_or_else(|| CranelispError::ModuleError {
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
    let platform_symbols = platform_registry.jit_symbols_owned();
    for (name, ptr) in &platform_symbols {
        linker.register_symbol(name, *ptr);
    }

    // Register code pointers from already-compiled modules via def_codegen.
    for entry in shared_codegen.def_codegen.iter() {
        if let Some(ptr) = entry.value().code_ptr {
            linker.register_symbol(entry.key().as_ref(), ptr);
        }
    }

    // Register the GOT base address.
    let got_base = shared_codegen.got_base_ptr();
    if !got_base.is_null() {
        linker.register_symbol("__got_base", got_base);
    }

    // Load the .o file — one mmap + relocation pass.
    let fn_addrs = cache::load_cached_object(&mut linker, &cached)?;

    // Wire code pointers into the GOT.
    let mut loaded_symbols = Vec::new();
    for name in cached.codegen_state().got_slots.keys() {
        let code_ptr = fn_addrs.get(name.as_ref()).copied();

        // Ensure a GOT slot exists (may already be allocated from try_cache_hit_load).
        let slot = shared_codegen.ensure_slot_for(name)?;

        // Write the code pointer to the GOT slot.
        if let Some(ptr) = code_ptr {
            shared_codegen.update_slot(slot, ptr);
        }

        // Update the DefCodegen entry with code pointer and param count.
        let mut dc = shared_codegen.def_codegen.entry(name.clone()).or_default();
        dc.got_slot = Some(slot);
        dc.code_ptr = code_ptr;
        if let Some(def_entry) = cached.codegen_state().def_entries.get(name) {
            dc.param_count = def_entry.param_count;
        }

        loaded_symbols.push(name.clone());
    }

    // Store the Linker in per-worker state (keeps mmap'd code alive).
    worker_jit.cache_linkers.push(linker);

    Ok(loaded_symbols)
}

/// Handle a cache-hit codegen work item: check if the module is cached
/// and load it via Linker, then notify the scheduler.
///
/// Shared helper for both `priority_worker_loop` (inline) and
/// `priority_worker_thread` (spawned). Returns Ok(true) if the module
/// was loaded, Ok(false) if it was not cached (no-op).
fn handle_cached_codegen(
    shared_codegen: &SharedCodegenState,
    worker_jit: &mut WorkerJitState,
    platform_registry: &PlatformRegistry,
    module: &ModuleFullPath,
    shared_state: Option<&crate::session_v4::SharedState>,
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

    match load_cached_module_via_linker(
        shared_codegen, worker_jit, platform_registry,
        module, shared_state,
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
// FIXME(/int): Refactor process_module_forms to take &mut ModuleSuspendState
// instead of separate &mut accumulator, &mut expanded_program, &mut pass1_done.
// This would simplify the call sites and keep suspension state cohesive.
pub(crate) struct ModuleSuspendState {
    pub(crate) accumulator: ModuleCheckAccumulator,
    /// Expanded program forms accumulated across suspensions.
    /// Forms processed before the block point are preserved here.
    pub(crate) expanded_program: Vec<TopLevel>,
    /// Whether Pass 1 (register signatures) has been completed for this module.
    /// Prevents re-running Pass 1 on resume when start_form_index is 0
    /// (which happens when a module blocks on its very first form).
    pub(crate) pass1_done: bool,
}

/// Main worker loop: pull work from the scheduler and process it.
///
/// Returns when `take_priority_work` returns None (all work done or shutdown).
/// After typecheck, performs a codegen sweep (W2 approach).
///
/// `module_sexps` grows dynamically as dependencies are discovered (G-2).
pub fn priority_worker_loop(
    ctx: &mut WorkerContext,
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
                    &mut state.accumulator,
                    &mut state.expanded_program,
                    ModuleStrategy::Replace,
                    &mut state.pass1_done,
                ) {
                    Ok(ProcessResult::Complete { check_result, program }) => {
                        // Post-typecheck codegen sweep (W2).
                        codegen_module_symbols(
                            ctx.shared_codegen,
                            ctx.worker_jit,
                            ctx.platform_registry,
                            ctx.scheduler,
                            &module,
                            &program,
                            &check_result,
                        )?;

                        // Stash data for nice worker .o + .meta.json, then
                        // notify typecheck_done. Order matters: nice workers
                        // wake on notify_typecheck_done, so the stash must
                        // be populated first.
                        stash_object_codegen_input(
                            ctx.object_codegen_stash,
                            ctx.tc,
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
                    ctx.shared_codegen, ctx.worker_jit, ctx.platform_registry,
                    &module, ctx.shared_state, ctx.scheduler,
                );
            }
            None => break,
        }
    }
    Ok(())
}

/// Stash module data for nice worker `.o` and `.meta.json` compilation.
///
/// When the object codegen stash is available, stores the CheckResult,
/// Program, SymbolTable, and ModuleStructure so that nice workers can
/// compile `.o` files and write `.meta.json` without re-accessing the
/// TypeChecker.
fn stash_object_codegen_input(
    stash: Option<&std::sync::Mutex<
        HashMap<ModuleFullPath, crate::session_v4::ObjectCodegenInput>,
    >>,
    tc: &cranelisp_typecheck::TypeChecker,
    module: &ModuleFullPath,
    check_result: CheckResult,
    program: Vec<TopLevel>,
) {
    let Some(stash) = stash else { return };

    // Clone symbol table from TypeChecker for .meta.json serialization.
    let symbol_table = tc.module_table_cloned(module)
        .unwrap_or_else(|| cranelisp_types::SymbolTable::new(module.clone()));

    // Build a minimal ModuleStructure. The v4 pipeline handles import/export
    // declarations inline during process_module_forms rather than extracting
    // them into a structure upfront. A default structure with the module path
    // is sufficient for cache metadata — the symbol table carries the real data.
    let module_structure = cranelisp_types::ModuleStructure {
        path: module.clone(),
        file_path: None,
        mod_decls: Vec::new(),
        import_specs: Vec::new(),
        export_specs: Vec::new(),
        platform_specs: Vec::new(),
        impl_sexps: Vec::new(),
        impls: Vec::new(),
        dll_path: None,
    };

    let input = crate::session_v4::ObjectCodegenInput {
        check_result,
        program,
        // Cross-module func_sigs are not accumulated in the v4 path yet.
        // The nice worker will compile with an empty list, which means
        // cross-module GOT references won't have slot assignments in the
        // `.o` file. This is acceptable for now — full cross-module GOT
        // support requires the linker integration (Step 10+).
        cross_module_func_sigs: Vec::new(),
        symbol_table,
        module_structure,
    };

    if let Ok(mut map) = stash.lock() {
        map.insert(module.clone(), input);
    }
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
pub(crate) struct PriorityWorkerShared<'a> {
    pub(crate) tc: &'a std::sync::Mutex<cranelisp_typecheck::TypeChecker>,
    pub(crate) platform_registry: &'a std::sync::Mutex<PlatformRegistry>,
    pub(crate) shared_codegen: &'a SharedCodegenState,
    pub(crate) scheduler: &'a CompileScheduler,
    pub(crate) module_sexps: &'a std::sync::Mutex<HashMap<ModuleFullPath, Vec<Sexp>>>,
    pub(crate) suspend_states: &'a std::sync::Mutex<
        HashMap<ModuleFullPath, ModuleSuspendState>,
    >,
    pub(crate) lib_dirs: &'a [PathBuf],
    pub(crate) project_root: &'a Path,
    pub(crate) object_codegen_stash: &'a std::sync::Mutex<
        HashMap<ModuleFullPath, crate::session_v4::ObjectCodegenInput>,
    >,
    pub(crate) shared_state: Option<&'a crate::session_v4::SharedState>,
}

/// Main loop for a spawned priority worker thread.
///
/// Uses `take_priority_work_blocking` to park when no work is available.
/// Locks the TypeChecker mutex for each work item (serialized until TC
/// gets `&self` API). Creates a per-worker `WorkerJitState` and drains
/// to shared codegen state after each module's codegen sweep.
pub(crate) fn priority_worker_thread(
    shared: &PriorityWorkerShared,
    _worker_id: usize,
) {
    let mut worker_jit = WorkerJitState::new();

    loop {
        let work = shared.scheduler.take_priority_work_blocking();
        match work {
            Some(PriorityWork::Typecheck(module)) => {
                if let Err(e) = handle_typecheck_work(
                    shared, &mut worker_jit, &module,
                ) {
                    shared.scheduler.notify_module_failed(&module, e);
                }
                // Drain per-worker JIT state to shared after each module.
                worker_jit.drain_to_shared(shared.shared_codegen);
            }
            Some(PriorityWork::BlockingJitCodegen(module, _symbol))
            | Some(PriorityWork::JitCodegen(module, _symbol)) => {
                // Cache-hit module: load entire .o via Linker (batch load).
                let platform = shared.platform_registry.lock()
                    .unwrap_or_else(|e| e.into_inner());
                let _ = handle_cached_codegen(
                    shared.shared_codegen, &mut worker_jit, &*platform,
                    &module, shared.shared_state, &shared.scheduler,
                );
                worker_jit.drain_to_shared(shared.shared_codegen);
            }
            None => break, // Shutdown or all work done.
        }
    }
}

/// Handle a Typecheck work item under the TC mutex lock.
///
/// Locks TC + PlatformRegistry, builds a WorkerContext, and runs
/// process_module_forms + codegen_module_symbols.
fn handle_typecheck_work(
    shared: &PriorityWorkerShared,
    worker_jit: &mut WorkerJitState,
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

    // Lock TC and PlatformRegistry for the duration of processing.
    let mut tc = shared.tc.lock()
        .unwrap_or_else(|e| e.into_inner());
    let mut platform_registry = shared.platform_registry.lock()
        .unwrap_or_else(|e| e.into_inner());

    let mut ctx = WorkerContext {
        tc: &mut tc,
        scheduler: shared.scheduler,
        shared_codegen: shared.shared_codegen,
        worker_jit,
        platform_registry: &mut platform_registry,
        lib_dirs: shared.lib_dirs,
        project_root: shared.project_root,
        object_codegen_stash: Some(shared.object_codegen_stash),
        shared_state: shared.shared_state,
    };

    match process_module_forms(
        &mut ctx, module, &sexps, start_idx,
        &mut state.accumulator,
        &mut state.expanded_program,
        ModuleStrategy::Replace,
        &mut state.pass1_done,
    ) {
        Ok(ProcessResult::Complete { check_result, program }) => {
            // Post-typecheck codegen sweep.
            codegen_module_symbols(
                ctx.shared_codegen,
                ctx.worker_jit,
                ctx.platform_registry,
                ctx.scheduler,
                module,
                &program,
                &check_result,
            )?;

            // Stash data for nice worker .o + .meta.json.
            stash_object_codegen_input(
                ctx.object_codegen_stash,
                ctx.tc,
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
