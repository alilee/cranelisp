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
use crate::pipeline::compile_and_register_defn;
use crate::scheduler::{CompileScheduler, PriorityWork};
use crate::session::InMemWorkerState;

// ---------------------------------------------------------------------------
// WorkerContext — bundled worker parameters (G-1)
// ---------------------------------------------------------------------------

/// Shared context for the priority worker loop and process_module_forms.
/// Borrows session-owned data needed by workers. Read-only except for
/// tc and inmem_worker which are mutated during compilation.
pub struct WorkerContext<'a> {
    pub tc: &'a mut cranelisp_typecheck::TypeChecker,
    pub scheduler: &'a mut CompileScheduler,
    pub inmem_worker: &'a mut InMemWorkerState,
    pub platform_symbols: &'a mut Vec<(String, *const u8)>,
    pub lib_dirs: &'a [PathBuf],
    pub project_root: &'a Path,
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
) -> Result<ProcessResult, CranelispError> {
    let is_fresh = start_form_index == 0;

    if is_fresh {
        // Set active module and clear for replace.
        ctx.tc.set_current_module(module.clone());
        ctx.tc.clear_module_for_replace_public();

        // Inject wildcard import of primitives and macros modules.
        inject_primitives_import(ctx.tc)?;
        inject_macros_import(ctx.tc)?;

        // Prelude injection: inject (import [prelude [*]]) for non-prelude modules.
        if let Some(result) = inject_prelude_if_needed(ctx, module)? {
            return Ok(result);
        }
    } else {
        // Resume: set active module (may have been changed by dep processing).
        ctx.tc.set_current_module(module.clone());
    }

    // --- Pass 1: only on fresh start ---
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
    }

    // --- Pass 2: per-sexp expand-then-check, from start_form_index ---
    // expanded_program accumulates across suspensions via the caller.
    let pass2_result = pass2_check_bodies_with_expansion(
        ctx, module, sexps, start_form_index, accumulator, expanded_program,
    )?;

    match pass2_result {
        Pass2Result::Complete => {
            finalize_module(ctx, module, expanded_program, accumulator)
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
        ModuleStrategy::Replace,
    )?;

    check_result.display =
        ctx.tc.compute_display_info_public(expanded_program, &accumulator.defn_type_vars);

    ctx.scheduler.notify_typecheck_done(module);

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
    // Collect macro infos for expansion.
    let macro_infos: Vec<(Symbol, cranelisp_frontend::DefmacroInfo, Sexp)> = sexps
        .iter()
        .filter(|s| cranelisp_frontend::is_defmacro(s))
        .map(|s| {
            let info = cranelisp_frontend::parse_defmacro(s)?;
            Ok((info.name.clone(), info, s.clone()))
        })
        .collect::<Result<Vec<_>, CranelispError>>()?;
    let macro_names: Vec<&str> = macro_infos.iter().map(|(n, _, _)| n.as_ref()).collect();

    for form_idx in start_form_index..sexps.len() {
        let sexp = &sexps[form_idx];

        match classify_form(sexp)? {
            FormKind::Import(specs) => {
                match handle_import(ctx, module, specs)? {
                    BlockAction::Continue => {}
                    BlockAction::Block { dep_module, dep_sexps } => {
                        // Save resume point: re-process this import after unblock
                        // because we need to register all specs (some may have
                        // been skipped due to the blocking dep).
                        return Ok(Pass2Result::Blocked {
                            form_index: form_idx,
                            dep_module,
                            dep_sexps,
                        });
                    }
                }
            }
            FormKind::Export(specs) => {
                handle_export(ctx, &specs)?;
            }
            FormKind::Mod(decl) => {
                handle_mod(ctx, module, &decl)?;
            }
            FormKind::Platform(spec) => {
                handle_platform(ctx, &spec)?;
            }
            FormKind::Defmacro => {
                continue; // registered in Pass 1
            }
            FormKind::Regular => {
                process_regular_form(
                    ctx, module, sexp, &macro_infos, &macro_names,
                    accumulator, expanded_program,
                )?;
            }
        }
    }
    Ok(Pass2Result::Complete)
}

/// Process a regular (non-module-declaration) form in Pass 2.
///
/// Tries macro expansion, builds AST, registers any new signatures
/// (for begin-spliced defns), then typechecks the body.
fn process_regular_form(
    ctx: &mut WorkerContext,
    module: &ModuleFullPath,
    sexp: &Sexp,
    macro_infos: &[(Symbol, cranelisp_frontend::DefmacroInfo, Sexp)],
    macro_names: &[&str],
    accumulator: &mut ModuleCheckAccumulator,
    expanded_program: &mut Vec<TopLevel>,
) -> Result<(), CranelispError> {
    // Try macro expansion on the raw sexp.
    let effective_sexp = try_expand_for_pass2(
        sexp, module, ctx, macro_infos, macro_names, accumulator,
    )?;

    let sexp_to_build = match &effective_sexp {
        Some(expanded) => expanded,
        None => sexp,
    };

    let flattened = cranelisp_frontend::flatten_begin(sexp_to_build.clone());
    let built = cranelisp_frontend::build_program(&flattened)?;
    let working = wrap_exprs_as_defns(&built);

    // Register signatures first (Pass 1) for any new forms from expansion.
    for form in &working {
        let result = ctx.tc.check_form(module, form, CheckPass::Register, accumulator)?;
        ctx.tc.merge_form_result(module, accumulator, result);
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
    ctx: &mut WorkerContext,
    module: &ModuleFullPath,
    specs: Vec<ImportSpec>,
) -> Result<BlockAction, CranelispError> {
    for spec in &specs {
        let dep = &spec.module_path;

        // Already loaded — register the import and continue.
        if ctx.tc.has_module(dep) {
            ctx.tc.register_imports(&[spec.clone()])?;
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

/// Handle export forms: register export metadata in the typechecker.
fn handle_export(
    ctx: &mut WorkerContext,
    specs: &[ExportSpec],
) -> Result<(), CranelispError> {
    ctx.tc.register_exports(specs)
}

/// Handle mod forms: write inline body to disk if present.
///
/// The submodule is not immediately loaded — it will be discovered lazily
/// when another module imports from it via the normal module resolution path.
fn handle_mod(
    ctx: &mut WorkerContext,
    module: &ModuleFullPath,
    decl: &cranelisp_types::ModDecl,
) -> Result<(), CranelispError> {
    if let Some(body_sexps) = &decl.inline_body {
        write_inline_mod_to_disk(module, &decl.name, body_sexps, ctx.project_root)?;
    }

    // FIXME(/int): design doc §7.2 specifies ctx.tc.register_submodule(module, &sub_path)
    // but implementation relies on implicit file-system discovery. Reconcile design doc
    // with implementation — either add explicit registration or update the design doc.
    Ok(())
}

/// Handle platform forms: load DLL and register type signatures.
///
/// Platform loading is NOT a cross-module blocking operation. The DLL is
/// loaded synchronously. Type signatures are registered in TC immediately.
fn handle_platform(
    ctx: &mut WorkerContext,
    spec: &PlatformSpec,
) -> Result<(), CranelispError> {
    let (_platform, jit_syms) = crate::platform::load_and_register_platform(
        ctx.tc,
        &spec.name,
        ctx.project_root,
        spec.span,
    )?;

    // Register platform function pointers for codegen.
    ctx.platform_symbols.extend(jit_syms);

    // Platform DLLs are leaked (kept alive for process lifetime).
    // This is known debt tracked for Step 8.
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
    let all_macros = build_all_macro_entries(ctx.inmem_worker, macro_infos)?;

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
        has_code_ptr(ctx.inmem_worker, &clause_name)
    });

    if all_compiled {
        return Ok(());
    }

    // Walk transitive callees and compile uncompiled deps first.
    let uncompiled_deps = collect_transitive_uncompiled_deps(
        ctx.tc, ctx.inmem_worker, module, &info.name,
    );
    for (_dep_module, dep_symbol) in &uncompiled_deps {
        // FIXME(/int): dep_module is ignored — assumes macro deps are in the same module.
        // Cross-module macro deps (Step 11+) will need dep_module passed to compile_dep_symbol_inline.
        compile_dep_symbol_inline(
            ctx.tc, ctx.inmem_worker, ctx.platform_symbols,
            dep_symbol, accumulator,
        )?;
        ctx.scheduler.notify_inmem_codegen_complete(module, dep_symbol, false);
    }

    // Compile each clause that is not yet compiled.
    let total_clauses = info.clauses.len();
    for (clause_idx, clause) in info.clauses.iter().enumerate() {
        let clause_name = macro_clause_jit_name(&info.name, clause_idx);
        if has_code_ptr(ctx.inmem_worker, &clause_name) {
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
    inmem_worker: &InMemWorkerState,
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
        if !has_code_ptr(inmem_worker, &dep_sym) {
            result.push((dep_mod, dep_sym));
        }
    }

    result
}

/// Compile a dependency symbol inline using the accumulated check state.
///
/// Looks up the defn from the accumulated data (it has been typechecked
/// in Pass 2 already since deps are defined before the macro) and
/// compiles it via `compile_and_register_defn`.
fn compile_dep_symbol_inline(
    tc: &cranelisp_typecheck::TypeChecker,
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    symbol: &Symbol,
    accumulator: &ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    // Build a partial CheckResult from the accumulator for codegen.
    let check = build_check_from_accumulator(tc, accumulator);

    // Look up the defn from the symbol table.
    let table = tc.symbol_table();
    let entry = table.get(symbol.as_ref()).ok_or_else(|| CranelispError::MacroError {
        message: format!("inline compile: symbol '{}' not found in module table", symbol),
        span: Span::SYNTHETIC,
    })?;

    // For Def entries, we need the defn AST. But the symbol table only stores
    // the scheme, not the AST. The defn should be available from the program
    // forms being processed. For now, this handles the case where the defn is
    // available from got_state (already registered but not yet compiled).
    // In practice, macro deps are typically compiled via the codegen sweep,
    // and this path handles rare cases of forward-referenced helpers.
    let _ = entry;

    // The defn was already typechecked; we need its AST for compilation.
    // Look it up from the GOT state's stored defns.
    let defn = inmem_worker
        .got_state
        .def_codegen
        .get(symbol)
        .and_then(|dc| dc.defn.as_ref())
        .cloned();

    if let Some(defn) = defn {
        compile_and_register_defn(inmem_worker, platform_symbols, &defn, &check)?;
    }
    // If not found in GOT defns, the symbol may be a builtin/primitive
    // that is always available — nothing to compile.

    Ok(())
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
    compile_macro_defn_no_dealloc(ctx.inmem_worker, ctx.platform_symbols, defn, &check)?;

    Ok(())
}

/// Compile a macro clause defn with dealloc disabled.
///
/// Macro functions build throwaway Sexp trees that are marshalled back to
/// the compiler. Disabling dealloc prevents use-after-free on unmarshal.
fn compile_macro_defn_no_dealloc(
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    defn: &Defn,
    check: &CheckResult,
) -> Result<(), CranelispError> {
    let extra_symbols: Vec<(&str, *const u8)> = platform_symbols
        .iter()
        .map(|(name, ptr)| (name.as_str(), *ptr))
        .collect();
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
    let slot = inmem_worker.got_state.ensure_slot_for(&defn.name)?;
    inmem_worker.got_state.update_slot(slot, ptr);

    let entry = inmem_worker.got_state.def_codegen.entry(defn.name.clone()).or_default();
    entry.code_ptr = Some(ptr);
    entry.got_slot = Some(slot);
    entry.param_count = Some(defn.params().len());
    entry.defn = Some(defn.clone());

    // Keep JIT alive so the function pointer remains valid.
    inmem_worker.jit_modules.push(jit);

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
fn has_code_ptr(inmem_worker: &InMemWorkerState, name: &Symbol) -> bool {
    inmem_worker
        .got_state
        .def_codegen
        .get(name)
        .and_then(|dc| dc.code_ptr)
        .is_some()
}

/// Build a `MacroEntry` from GOT function pointers for a macro.
///
/// Used after inline compilation to construct the entry needed by
/// `invoke_clause` and `find_matching_clause`.
fn build_macro_entry_from_got(
    inmem_worker: &InMemWorkerState,
    info: &cranelisp_frontend::DefmacroInfo,
) -> Result<MacroEntry, CranelispError> {
    let mut clauses = Vec::new();

    for (idx, clause) in info.clauses.iter().enumerate() {
        let clause_name = macro_clause_jit_name(&info.name, idx);
        let code_ptr = inmem_worker
            .got_state
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
    inmem_worker: &InMemWorkerState,
    macro_infos: &[(Symbol, cranelisp_frontend::DefmacroInfo, Sexp)],
) -> Result<HashMap<Symbol, MacroEntry>, CranelispError> {
    let mut map = HashMap::new();
    for (name, info, _) in macro_infos {
        // Only include macros that have been compiled.
        let all_compiled = info.clauses.iter().enumerate().all(|(idx, _)| {
            let clause_name = macro_clause_jit_name(name, idx);
            has_code_ptr(inmem_worker, &clause_name)
        });
        if all_compiled {
            let entry = build_macro_entry_from_got(inmem_worker, info)?;
            map.insert(name.clone(), entry);
        }
    }
    Ok(map)
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
/// Returns `Some(ProcessResult::Blocked { .. })` if the prelude must be compiled
/// first, `None` if prelude is already loaded or not needed.
fn inject_prelude_if_needed(
    ctx: &mut WorkerContext,
    module: &ModuleFullPath,
) -> Result<Option<ProcessResult>, CranelispError> {
    let prelude_path = ModuleFullPath::from("prelude");
    if *module == prelude_path {
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
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    scheduler: &mut CompileScheduler,
    module: &ModuleFullPath,
    program: &[TopLevel],
    check: &CheckResult,
) -> Result<(), CranelispError> {
    // Pre-register all defn names in GOT for forward references.
    pre_register_got_slots(inmem_worker, program)?;

    // Compile default method bodies.
    for defn in &check.default_method_defns {
        compile_and_register_defn(inmem_worker, platform_symbols, defn, check)?;
    }

    // Compile mono specializations with per-specialization resolutions.
    compile_mono_defns(inmem_worker, platform_symbols, check)?;

    // Compile each regular defn.
    let defn_names = compile_regular_defns(inmem_worker, platform_symbols, program, check)?;

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
    inmem_worker: &mut InMemWorkerState,
    program: &[TopLevel],
) -> Result<(), CranelispError> {
    for tl in program {
        match tl {
            TopLevel::Defn(defn) => {
                inmem_worker.got_state.ensure_slot_for(&defn.name)?;
            }
            TopLevel::TraitImpl(impl_) => {
                for method in &impl_.methods {
                    inmem_worker.got_state.ensure_slot_for(&method.name)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// Compile monomorphised specializations.
fn compile_mono_defns(
    inmem_worker: &mut InMemWorkerState,
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
        compile_and_register_defn(inmem_worker, platform_symbols, &mono.defn, &mono_check)?;
    }
    Ok(())
}

/// Compile regular defns (skipping constrained fn base definitions).
/// Returns the list of compiled symbol names.
fn compile_regular_defns(
    inmem_worker: &mut InMemWorkerState,
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
                compile_and_register_defn(inmem_worker, platform_symbols, defn, check)?;
                compiled_names.push(defn.name.clone());

                // Note: zero-arg defns (e.g., `main`) are NOT executed here.
                // The codegen sweep only compiles and registers code pointers
                // in the GOT. Execution is done separately by `trampoline`.
            }
            TopLevel::TraitImpl(impl_) => {
                for method in &impl_.methods {
                    compile_and_register_defn(
                        inmem_worker,
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
// priority_worker_loop — dispatch scheduler work items
// ---------------------------------------------------------------------------

/// Per-module suspension state preserved across blocking/resumption.
struct ModuleSuspendState {
    accumulator: ModuleCheckAccumulator,
    /// Expanded program forms accumulated across suspensions.
    /// Forms processed before the block point are preserved here.
    expanded_program: Vec<TopLevel>,
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
                let start_idx = ctx.scheduler.module_state(&module)
                    .and_then(|ms| ms.resume_from_form)
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
                    });

                match process_module_forms(
                    ctx, &module, &sexps, start_idx,
                    &mut state.accumulator,
                    &mut state.expanded_program,
                ) {
                    Ok(ProcessResult::Complete { check_result, program }) => {
                        // Post-typecheck codegen sweep (W2).
                        codegen_module_symbols(
                            ctx.inmem_worker,
                            ctx.platform_symbols,
                            ctx.scheduler,
                            &module,
                            &program,
                            &check_result,
                        )?;
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
                        if let Some(ms) = ctx.scheduler.module_state_mut(&module) {
                            ms.resume_from_form = Some(form_index);
                        }
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
            Some(PriorityWork::BlockingJitCodegen(_module, _symbol)) => {
                // Cross-module macro dep compilation (Step 5+).
                // For now, macro deps are compiled inline in process_module_forms.
                // This path will be used for cross-module macro deps in future steps.
            }
            Some(PriorityWork::JitCodegen(_module, _symbol)) => {
                // Background JIT for TypecheckDone modules — deferred to later steps.
            }
            None => break,
        }
    }
    Ok(())
}
