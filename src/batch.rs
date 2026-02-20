use std::path::{Path, PathBuf};

use crate::ast::{TopLevel, Visibility};
use crate::ast_builder::build_program;
use crate::cache;
use crate::error::{CranelispError, Span};
use crate::jit::Jit;
use crate::macro_expand::{
    compile_macro, expand_sexp, flatten_begin, is_defmacro, is_deftype, parse_defmacro,
};
use crate::module::{
    find_lib_dir, resolve_module_imports, CompiledModule, DefKind, ImportNames, ModuleEntry,
    ModuleGraph, ModuleInfo,
};
use crate::names::{FQSymbol, ModuleFullPath, Symbol};
use crate::repl::ReplSession;
use crate::typechecker::TypeChecker;

/// Load a platform DLL, validate its manifest name, and register with both JIT and type checker.
/// Shared by batch and REPL paths.
pub fn load_and_register_platform(
    session: &mut ReplSession,
    declared_name: &str,
    explicit_path: Option<&str>,
    span: Span,
) -> Result<(), CranelispError> {
    // Resolve DLL path
    let dll_path = match explicit_path {
        Some(p) => PathBuf::from(p),
        None => crate::platform::resolve_platform_path(declared_name).ok_or_else(|| {
            CranelispError::CodegenError {
                message: format!("platform '{}' not found", declared_name),
                span,
            }
        })?,
    };

    // Load DLL and get descriptors
    let (manifest_name, version, descriptors) = session.jit.load_platform(&dll_path)?;

    // Validate manifest name matches declared name
    if manifest_name != declared_name {
        return Err(CranelispError::CodegenError {
            message: format!(
                "platform name mismatch: declared '{}' but DLL reports '{}'",
                declared_name, manifest_name
            ),
            span,
        });
    }

    eprintln!(
        "Loaded platform: {} v{} ({} functions)",
        manifest_name,
        version,
        descriptors.len()
    );

    // Register with type checker (creates platform.<name> module)
    session.tc.register_platform(&manifest_name, &descriptors)?;

    // Set dll_path on the platform module
    let module_name = format!("platform.{}", manifest_name);
    let mod_path = crate::names::ModuleFullPath::from(module_name.as_str());
    if let Some(cm) = session.tc.modules.get_mut(&mod_path) {
        cm.dll_path = Some(dll_path.clone());
    }

    // Backfill FuncIds
    session.jit.populate_builtin_func_ids(&mut session.tc.modules);

    Ok(())
}

/// Run source code without any prelude.
/// This is the truly-no-prelude path for single-module projects
/// where no prelude.cl is found in the module graph.
fn run(source: &str) -> Result<(), CranelispError> {
    let user_sexps = crate::sexp::parse_sexps(source)?;
    let user = build_program(&user_sexps)?;

    let mut tc = TypeChecker::new();
    let result = tc.check_program(&user)?;

    let multi_defns = tc.build_multi_defns(&user);

    let mut jit = Jit::new()?;
    jit.populate_builtin_func_ids(&mut tc.modules);
    jit.compile_and_run(&user, &multi_defns, &result, &tc)?;
    Ok(())
}

/// Run a project starting from an entry file.
/// Discovers all `(mod ...)` dependencies, compiles in topological order,
/// then calls `main()` from the entry module.
pub fn run_project(entry_path: &Path) -> Result<(), CranelispError> {
    let graph = ModuleGraph::build(entry_path)?;

    // Single-file project with no module dependencies: use the simple run() path
    if graph.modules.len() == 1 {
        let entry_info = graph.modules.values().next().unwrap();
        if entry_info.platforms.is_empty() {
            return run(&entry_info.source);
        }
    }

    let (session, _linker) = compile_project_pipeline(&graph, entry_path)?;

    // Call main() from the entry module
    session.jit.call_main(&session.tc.modules)?;
    Ok(())
}

/// Compile a project's module graph (shared pipeline for run and exe).
/// Returns the session and linker (linker must outlive execution, owns mmap'd regions).
fn compile_project_pipeline(
    graph: &ModuleGraph,
    entry_path: &Path,
) -> Result<(ReplSession, crate::linker::Linker), CranelispError> {

    // Multi-file (or has platform declarations): use ReplSession-style
    // incremental compilation. The module graph already includes prelude + core
    // as modules, so no separate load_prelude() is needed.
    let project_root = entry_path
        .canonicalize()
        .unwrap_or_else(|_| entry_path.to_path_buf())
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .to_path_buf();
    let mut session = ReplSession::with_project_root(project_root.clone())?;

    // Two-tier cache: lib modules cache alongside lib sources, project modules cache locally
    let lib_dir = find_lib_dir(&project_root);
    let project_cache_dir = cache::cache_dir(&project_root);
    let lib_cache_dir = lib_dir.as_ref().map(|ld| cache::cache_dir(ld));

    let target_triple = cranelift_native::builder()
        .map(|b| b.triple().to_string())
        .unwrap_or_else(|_| "unknown".to_string());

    let raw_project_manifest = cache::read_manifest(&project_cache_dir);
    let existing_project_manifest =
        raw_project_manifest.filter(cache::is_manifest_compatible);
    let raw_lib_manifest = lib_cache_dir
        .as_ref()
        .and_then(|d| cache::read_manifest(d));
    let existing_lib_manifest = raw_lib_manifest.filter(cache::is_manifest_compatible);

    let mut project_cache_manifest = cache::CacheManifest::new(&target_triple);
    let mut lib_cache_manifest = cache::CacheManifest::new(&target_triple);
    let mut lib_cache_dirty = false;
    // Process platform declarations from ALL modules before compilation
    for module_id in &graph.compile_order {
        let module = &graph.modules[module_id];
        for (name, explicit_path, span) in &module.platforms {
            load_and_register_platform(
                &mut session,
                name,
                explicit_path.as_deref(),
                *span,
            )?;
        }
    }

    // Ensure per-module GOTs exist so linker can register their stable addresses
    for module_id in &graph.compile_order {
        let mod_path = ModuleFullPath::from(module_id.short_name());
        let cm = session.tc.modules
            .entry(mod_path.clone())
            .or_insert_with(|| CompiledModule::new(mod_path));
        cm.ensure_got();
    }

    // Create linker early — cached modules link incrementally during the compile loop
    // so that GOTs are populated before dependent modules need them (e.g., for macro compilation).
    // The linker MUST outlive call_main because it owns mmap'd code regions.
    let mut linker = crate::linker::Linker::new();

    // Register runtime symbols with linker up front (intrinsics, builtins, platform DLLs)
    session.jit.register_runtime_symbols(&mut linker);

    // Register GOT base addresses for all modules
    for module_id in &graph.compile_order {
        let mod_path = ModuleFullPath::from(module_id.short_name());
        let got_symbol = format!("__cranelisp_got_{}", crate::cache::module_file_name(&mod_path));
        if let Some(cm) = session.tc.modules.get(&mod_path) {
            if let Some(got_addr) = cm.got_table_addr() {
                linker.register_symbol(&got_symbol, got_addr as *const u8);
            }
        }
    }

    // Compile each module in topological order (leaves first)
    let entry_id = graph.compile_order.last().unwrap().clone();

    // Build a map from child mod name → dependency short_name for import resolution.
    // Each module's (mod child_name) declares a dependency; the dependency's short_name
    // is used for qualified access (e.g., "util/helper").
    // Seed with synthetic modules (primitives, platform.stdio) so (import [primitives [*]]) resolves.
    let mut mod_name_to_short: std::collections::HashMap<String, String> =
        std::collections::HashMap::new();
    for name in &session.tc.module_names {
        let s = name.0.clone();
        mod_name_to_short.entry(s.clone()).or_insert(s);
    }
    for module_id in &graph.compile_order {
        let short = module_id.short_name().to_string();
        // Map the module's full id to its short_name so imports can resolve
        mod_name_to_short.insert(module_id.0.clone(), short.clone());
        // Also map the short_name to itself for simple (mod util) style
        mod_name_to_short.insert(short.clone(), short);
    }

    // Pre-compute cache routing info per module
    let module_cache_info: std::collections::HashMap<ModuleFullPath, (String, std::path::PathBuf, bool)> = graph
        .compile_order
        .iter()
        .map(|mid| {
            let m = &graph.modules[mid];
            let mn = mid.short_name().to_string();
            let mp = ModuleFullPath::from(mn.as_str());
            let tc = if m.is_lib {
                lib_cache_dir.as_ref().unwrap_or(&project_cache_dir).clone()
            } else {
                project_cache_dir.clone()
            };
            (mp, (mn, tc, m.is_lib))
        })
        .collect();

    // Track modules that need cache writes (freshly compiled or received mono specializations).
    let mut dirty_modules: std::collections::HashSet<ModuleFullPath> = std::collections::HashSet::new();

    for module_id in &graph.compile_order {
        let module = &graph.modules[module_id];
        let is_entry = module_id == &entry_id;
        let mod_name = module_id.short_name().to_string();
        let mod_path = ModuleFullPath::from(mod_name.as_str());
        let source_hash = cache::hash_source(&module.source);

        // Set current module for module-walk resolution
        session
            .tc
            .set_current_module_path(mod_path.clone());

        // ── Cache check: try to load from cache ──────────────────────────
        // Route to lib or project cache based on module origin
        let (target_cache, existing_manifest_ref) = if module.is_lib {
            if let Some(ref lc) = lib_cache_dir {
                (lc.clone(), &existing_lib_manifest)
            } else {
                (project_cache_dir.clone(), &existing_project_manifest)
            }
        } else {
            (project_cache_dir.clone(), &existing_project_manifest)
        };

        let cache_hit = existing_manifest_ref
            .as_ref()
            .map(|m| m.is_cached(&mod_path, &source_hash))
            .unwrap_or(false);

        if cache_hit {
            if let Some(loaded) = try_load_cached_module(
                &target_cache,
                &mod_path,
                &mod_name,
                module,
                is_entry,
                &mut session,
                &mut linker,
                &mod_name_to_short,
            )? {
                eprintln!("; Loaded {} from cache", mod_name);
                if let Some(cm) = session.tc.modules.get_mut(&mod_path) {
                    cm.content_hash = Some(source_hash.clone());
                }
                if module.is_lib {
                    lib_cache_manifest.upsert_module(mod_path.clone(), source_hash.clone());
                    lib_cache_dirty = true;
                } else {
                    project_cache_manifest.upsert_module(mod_path.clone(), source_hash.clone());
                }
                if loaded {
                    continue;
                }
            }
            // Fall through to normal compilation if cache load failed
        }

        // ── Resolve imports for this module ──────────────────────────
        let resolved_imports =
            resolve_module_imports(&module.imports, &session.tc, &mod_name_to_short)?;

        // Install imported bare names and check for ambiguity.
        // For the entry module, this includes the synthetic (import [prelude [*]])
        // injected by ModuleGraph::build when a prelude is auto-discovered.
        if !resolved_imports.is_empty() {
            session.tc.begin_module_scope(&resolved_imports)?;
        }

        // Register module alias if any import declares one
        for import in &module.imports {
            if let Some(ref alias) = import.alias {
                let source_short = mod_name_to_short
                    .get(&import.module_path)
                    .cloned()
                    .unwrap_or_else(|| import.module_path.clone());
                session
                    .tc
                    .module_names
                    .insert(crate::names::ModuleFullPath::from(alias.as_str()));
                // Register alias → source qualified names
                let public = session.tc.get_module_public_names(&source_short);
                for name in &public {
                    let source_qualified = format!("{}/{}", source_short, name);
                    let alias_qualified = format!("{}/{}", alias, name);
                    if let Some(scheme) = session.tc.lookup_env(&source_qualified).cloned() {
                        session.tc.register_alias(&alias_qualified, &scheme);
                    }
                }
            }
        }

        // ── Pre-pass: register type definitions ──────────────────────
        // Type definitions must be registered before macros are compiled,
        // since macro bodies reference types like Sexp.
        for sexp in &module.sexps {
            if is_deftype(sexp) {
                let items = build_program(std::slice::from_ref(sexp))?;
                for item in &items {
                    session.tc.register_type_def(item);
                }
            }
        }
        session.jit.register_type_defs(&session.tc);

        // ── Sequential compile: process each sexp one at a time ──────
        // Mirrors load_prelude's approach: each item is fully processed
        // before the next, so macros can reference earlier defns and
        // later sexps can use earlier macros.

        for sexp in &module.sexps {
            let sexp_source: &str =
                &module.source[sexp.span().0..sexp.span().1.min(module.source.len())];

            // Type defs already registered in pre-pass (register_type_def writes to CompiledModule)
            if is_deftype(sexp) {
                continue;
            }

            // Compile and register macros
            if is_defmacro(sexp) {
                let info = parse_defmacro(sexp)?;
                let ptr = compile_macro(
                    &mut session.tc,
                    &mut session.jit,
                    &info,
                    Some(&session.macro_env),
                )?;
                session.tc.register_macro_in_module(
                    &info.name,
                    info.fixed_params.clone(),
                    info.rest_param.clone(),
                    info.docstring.clone(),
                    info.visibility,
                    Some(sexp.clone()),
                    Some(sexp.to_string()),
                );
                session.macro_env.register(
                    info.name.clone(),
                    ptr,
                    info.docstring,
                    info.fixed_params,
                    info.rest_param,
                    Some(info.body_sexp),
                );
                continue;
            }

            // Expand using any macros registered so far
            let expanded = if !session.macro_env.is_empty() {
                expand_sexp(sexp.clone(), &session.macro_env, 0)?
            } else {
                sexp.clone()
            };

            // Flatten begin forms and handle defmacro-in-results
            let forms = flatten_begin(expanded);
            for form in &forms {
                if is_defmacro(form) {
                    let info = parse_defmacro(form)?;
                    let ptr = compile_macro(
                        &mut session.tc,
                        &mut session.jit,
                        &info,
                        Some(&session.macro_env),
                    )?;
                    session.tc.register_macro_in_module(
                        &info.name,
                        info.fixed_params.clone(),
                        info.rest_param.clone(),
                        info.docstring.clone(),
                        info.visibility,
                        Some(form.clone()),
                        Some(form.to_string()),
                    );
                    session.macro_env.register(
                        info.name.clone(),
                        ptr,
                        info.docstring,
                        info.fixed_params,
                        info.rest_param,
                        Some(info.body_sexp),
                    );
                    continue;
                }
                if is_deftype(form) {
                    let type_items = build_program(std::slice::from_ref(form))?;
                    for type_item in &type_items {
                        session.tc.register_type_def(type_item);
                    }
                    session.jit.register_type_defs(&session.tc);
                    continue;
                }
            }

            // Build AST from non-defmacro, non-deftype expanded forms
            let non_macro_forms: Vec<_> = forms
                .iter()
                .filter(|f| !is_defmacro(f) && !is_deftype(f))
                .collect();
            if non_macro_forms.is_empty() {
                continue;
            }
            let items = build_program(&non_macro_forms.iter().map(|s| (*s).clone()).collect::<Vec<_>>())?;

            for item in &items {
                match item {
                    TopLevel::TypeDef { .. } => {
                        // Should not happen — deftype handled above
                    }
                    TopLevel::TraitDecl(td) => {
                        session.tc.check_definition_conflict(&td.name, td.span)?;
                        for method in &td.methods {
                            session.jit.register_trait_method(&method.name);
                        }
                        session.tc.register_trait_public(td);
                    }
                    TopLevel::TraitImpl(ti) => {
                        session.tc.validate_impl_public(ti)?;
                        session.tc.register_impl(ti);
                        let target = ti.impl_target_mangled();
                        for method in &ti.methods {
                            let mangled = crate::ast::Defn {
                                visibility: Visibility::Public,
                                name: format!("{}${}", method.name, target),
                                docstring: None,
                                params: method.params.clone(),
                                param_annotations: method.param_annotations.clone(),
                                body: method.body.clone(),
                                span: method.span,
                            };
                            session.tc.check_defn(&mangled)?;
                            let mut mr = session.tc.resolve_methods()?;
                            session.tc.resolve_overloads(&mut mr)?;
                            let et = session.tc.resolve_expr_types();

                            // On-demand monomorphisation for trait impl methods
                            let mono_batch = match session.tc.monomorphise_all() {
                                Ok((monos, dispatches)) => {
                                    mr.extend(dispatches);
                                    monos
                                }
                                Err(e) => return Err(e),
                            };

                            let scheme = session.tc.finalize_defn_type(&mangled.name);
                            // Ensure Def entry
                            {
                                let mod_path = ModuleFullPath::from(mod_name.as_str());
                                if let Some(cm) = session.tc.modules.get_mut(&mod_path) {
                                    cm.insert_def(
                                        Symbol::from(mangled.name.as_str()),
                                        scheme.clone(),
                                        Visibility::Public,
                                        None,
                                    );
                                }
                            }
                            let slot = {
                                let mod_path = ModuleFullPath::from(mod_name.as_str());
                                session.tc.modules.get(&mod_path)
                                    .and_then(|cm| cm.get_got_slot(&mangled.name))
                                    .map(Ok)
                                    .unwrap_or_else(|| {
                                        let mod_path = ModuleFullPath::from(mod_name.as_str());
                                        session.tc.modules.get_mut(&mod_path).unwrap().allocate_got_slot(mangled.span)
                                    })
                            }?;
                            {
                                let mod_path = ModuleFullPath::from(mod_name.as_str());
                                if let Some(cm) = session.tc.modules.get_mut(&mod_path) {
                                    cm.pre_register_for_codegen(&mangled.name, slot, mangled.params.len());
                                }
                            }
                            let fn_slots = session.jit.build_fn_slots_from_modules(&session.tc.modules);
                            let compile_meta = session.jit.compile_defn_in_module(
                                &mangled,
                                &scheme,
                                &mr,
                                &mod_name,
                                &et,
                                slot,
                                &fn_slots,
                                &session.tc.modules,
                            )?;
                            {
                                let mod_path = ModuleFullPath::from(mod_name.as_str());
                                if let Some(cm) = session.tc.modules.get_mut(&mod_path) {
                                    cm.write_got_slot(slot, compile_meta.code_ptr);
                                    cm.update_codegen(&mangled.name, &compile_meta, Some(sexp_source), Some(sexp), Some(&mangled));
                                    cm.accumulate_method_resolutions(mr.clone());
                                    cm.accumulate_expr_types(et.clone());
                                }
                            }

                            // Compile mono specializations into their defining modules
                            session.compile_mono_specializations(&mono_batch, &mr, &et)?;
                            for (_, defining_mod) in &mono_batch {
                                dirty_modules.insert(defining_mod.clone());
                            }
                        }
                    }
                    TopLevel::Defn(defn) => {
                        session
                            .tc
                            .check_definition_conflict(&defn.name, defn.span)?;
                        session.tc.check_defn(defn)?;
                        let mut mr = session.tc.resolve_methods()?;
                        session.tc.resolve_overloads(&mut mr)?;

                        // On-demand monomorphisation: drain pending_mono_calls
                        let et = session.tc.resolve_expr_types();
                        let mono_batch = match session.tc.monomorphise_all() {
                            Ok((monos, dispatches)) => {
                                mr.extend(dispatches);
                                monos
                            }
                            Err(e) => return Err(e),
                        };

                        let scheme = session.tc.finalize_defn_type(&defn.name);
                        if scheme.is_constrained() {
                            session.tc.register_constrained_fn(defn, &scheme);
                        } else {
                            {
                                // Ensure Def entry for fn_slots
                                let mod_path = ModuleFullPath::from(mod_name.as_str());
                                let cm = session.tc.modules
                                    .entry(mod_path.clone())
                                    .or_insert_with(|| CompiledModule::new(mod_path));
                                cm.insert_def(
                                    Symbol::from(defn.name.as_str()),
                                    scheme.clone(),
                                    defn.visibility,
                                    None,
                                );
                            }
                            let slot = {
                                let mod_path = ModuleFullPath::from(mod_name.as_str());
                                session.tc.modules.get(&mod_path)
                                    .and_then(|cm| cm.get_got_slot(&defn.name))
                                    .map(Ok)
                                    .unwrap_or_else(|| {
                                        let mod_path = ModuleFullPath::from(mod_name.as_str());
                                        session.tc.modules.get_mut(&mod_path).unwrap().allocate_got_slot(defn.span)
                                    })
                            }?;
                            {
                                let mod_path = ModuleFullPath::from(mod_name.as_str());
                                if let Some(cm) = session.tc.modules.get_mut(&mod_path) {
                                    cm.pre_register_for_codegen(&defn.name, slot, defn.params.len());
                                }
                            }
                            let fn_slots = session.jit.build_fn_slots_from_modules(&session.tc.modules);
                            let compile_meta = session.jit.compile_defn_in_module(
                                defn,
                                &scheme,
                                &mr,
                                &mod_name,
                                &et,
                                slot,
                                &fn_slots,
                                &session.tc.modules,
                            )?;
                            // Write metadata to CompiledModule + accumulate for cache
                            let mod_path = ModuleFullPath::from(mod_name.as_str());
                            if let Some(cm) = session.tc.modules.get_mut(&mod_path) {
                                cm.write_got_slot(slot, compile_meta.code_ptr);
                                cm.update_codegen(
                                    &defn.name,
                                    &compile_meta,
                                    Some(sexp_source),
                                    Some(sexp),
                                    Some(defn),
                                );
                                cm.accumulate_method_resolutions(mr.clone());
                                cm.accumulate_expr_types(et.clone());
                            }
                        }

                        // Compile mono specializations into their defining modules
                        session.compile_mono_specializations(&mono_batch, &mr, &et)?;
                        for (_, defining_mod) in &mono_batch {
                            dirty_modules.insert(defining_mod.clone());
                        }
                    }
                    TopLevel::DefnMulti {
                        name,
                        visibility,
                        docstring,
                        variants,
                        span: defn_span,
                    } => {
                        session.tc.check_definition_conflict(name, *defn_span)?;
                        let base_meta = crate::typechecker::SymbolMeta::UserFn {
                            docstring: docstring.clone(),
                            param_names: vec![],
                        };
                        session
                            .tc
                            .update_current_module_meta(name, base_meta.clone());
                        let checked = session.tc.check_defn_multi(name, variants)?;
                        let mut mr = session.tc.resolve_methods()?;
                        session.tc.resolve_overloads(&mut mr)?;
                        let et = session.tc.resolve_expr_types();
                        for (mangled_name, mangled_defn, _scheme) in &checked {
                            let scheme = session.tc.finalize_defn_type(mangled_name);
                            {
                                let mod_path = ModuleFullPath::from(mod_name.as_str());
                                if let Some(cm) = session.tc.modules.get_mut(&mod_path) {
                                    cm.insert_def(
                                        Symbol::from(mangled_name.as_str()),
                                        scheme.clone(),
                                        Visibility::Public,
                                        None,
                                    );
                                }
                            }
                            let slot = {
                                let mod_path = ModuleFullPath::from(mod_name.as_str());
                                session.tc.modules.get(&mod_path)
                                    .and_then(|cm| cm.get_got_slot(mangled_name))
                                    .map(Ok)
                                    .unwrap_or_else(|| {
                                        let mod_path = ModuleFullPath::from(mod_name.as_str());
                                        session.tc.modules.get_mut(&mod_path).unwrap().allocate_got_slot(mangled_defn.span)
                                    })
                            }?;
                            {
                                let mod_path = ModuleFullPath::from(mod_name.as_str());
                                if let Some(cm) = session.tc.modules.get_mut(&mod_path) {
                                    cm.pre_register_for_codegen(mangled_name, slot, mangled_defn.params.len());
                                }
                            }
                            let fn_slots = session.jit.build_fn_slots_from_modules(&session.tc.modules);
                            let compile_meta = session.jit.compile_defn_in_module(
                                mangled_defn,
                                &scheme,
                                &mr,
                                &mod_name,
                                &et,
                                slot,
                                &fn_slots,
                                &session.tc.modules,
                            )?;
                            {
                                let mod_path = ModuleFullPath::from(mod_name.as_str());
                                if let Some(cm) = session.tc.modules.get_mut(&mod_path) {
                                    cm.write_got_slot(slot, compile_meta.code_ptr);
                                    cm.update_codegen(mangled_name, &compile_meta, Some(sexp_source), Some(sexp), Some(mangled_defn));
                                }
                            }
                        }
                        // Accumulate method resolutions and expr types for multi-sig
                        {
                            let mod_path = ModuleFullPath::from(mod_name.as_str());
                            if let Some(cm) = session.tc.modules.get_mut(&mod_path) {
                                cm.accumulate_method_resolutions(mr);
                                cm.accumulate_expr_types(et);
                            }
                        }
                        if let Some((first_mangled, _, _)) = checked.first() {
                            let scheme = session.tc.finalize_defn_type(first_mangled);

                            // Write DefnMulti base name into CompiledModule
                            {
                                let mod_path = ModuleFullPath::from(mod_name.as_str());
                                let cm = session
                                    .tc
                                    .modules
                                    .entry(mod_path.clone())
                                    .or_insert_with(|| CompiledModule::new(mod_path));
                                cm.insert_def(
                                    Symbol::from(name.as_str()),
                                    scheme,
                                    *visibility,
                                    Some(base_meta.clone()),
                                );
                            }
                        }
                    }
                }
            }
        }

        // Process export declarations: re-export names from other modules
        for export in &module.exports {
            let source_short = mod_name_to_short
                .get(&export.module_path)
                .cloned()
                .unwrap_or_else(|| export.module_path.clone());

            let names_to_export = match &export.names {
                ImportNames::Specific(names) => {
                    let public = session.tc.get_module_public_names(&source_short);
                    for name in names {
                        if !public.contains(name) {
                            return Err(CranelispError::ModuleError {
                                message: format!(
                                    "export: '{}' is not a public name in module '{}'",
                                    name, export.module_path
                                ),
                                file: None,
                                span: export.span,
                            });
                        }
                    }
                    names.clone()
                }
                ImportNames::Glob => session.tc.get_module_public_names(&source_short),
                ImportNames::MemberGlob(_) | ImportNames::None => Vec::new(),
            };

            for name in &names_to_export {
                // Write re-export into CompiledModule
                {
                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                    let cm = session
                        .tc
                        .modules
                        .entry(mod_path.clone())
                        .or_insert_with(|| CompiledModule::new(mod_path));
                    cm.insert_reexport(
                        Symbol::from(name.as_str()),
                        FQSymbol::new(
                            ModuleFullPath::from(source_short.as_str()),
                            Symbol::from(name.as_str()),
                        ),
                    );
                }
            }
        }

        // ── Mark module for deferred cache write ──────────────────
        // Cache writes are deferred to after the compile loop so that mono
        // specializations from later modules can land in earlier modules
        // without losing their accumulated method_resolutions / expr_types.
        dirty_modules.insert(mod_path.clone());
        if let Some(cm) = session.tc.modules.get_mut(&mod_path) {
            cm.content_hash = Some(source_hash.clone());
        }

        // Register module prefix and clean up module scope
        if !is_entry {
            session.tc.register_module_prefix(&mod_name);
            session.tc.end_module_scope();
        }
    }

    // ── Deferred cache writes: write all dirty modules ──────────────────
    for mod_path in &dirty_modules {
        if let Some((mod_name, target_cache, is_lib)) = module_cache_info.get(mod_path) {
            let fn_slots = session.jit.build_fn_slots_from_modules(&session.tc.modules);
            cache::write_module_cache(
                target_cache,
                mod_path,
                mod_name,
                &mut session.tc.modules,
                &fn_slots,
                session.jit.builtin_method_info(),
                session.jit.trait_method_names(),
                session.jit.type_defs_cg(),
                session.jit.constructor_to_type_cg(),
            );
            if let Some(cm) = session.tc.modules.get_mut(mod_path) {
                cm.clear_cache_transients();
            }
            eprintln!("; Wrote cache for {}", mod_name);
            let source_hash = session.tc.modules.get(mod_path)
                .and_then(|cm| cm.content_hash.clone())
                .unwrap_or_default();
            if *is_lib {
                lib_cache_manifest.upsert_module(mod_path.clone(), source_hash);
                lib_cache_dirty = true;
            } else {
                project_cache_manifest.upsert_module(mod_path.clone(), source_hash);
            }
        }
    }

    // Write cache manifests
    if let Err(e) = cache::write_manifest(&project_cache_dir, &project_cache_manifest) {
        eprintln!("warning: failed to write project cache manifest: {}", e);
    }
    if lib_cache_dirty {
        if let Some(ref lcd) = lib_cache_dir {
            if let Err(e) = cache::write_manifest(lcd, &lib_cache_manifest) {
                eprintln!("warning: failed to write lib cache manifest: {}", e);
            }
        }
    }

    Ok((session, linker))
}

/// Build a standalone executable from a cranelisp project.
///
/// Runs the same compilation pipeline as `run_project` (which writes .o cache files),
/// then collects the cached .o files and links them with the runtime bundle.
pub fn build_executable(entry_path: &Path, output_path: &Path) -> Result<(), CranelispError> {
    let graph = ModuleGraph::build(entry_path)?;

    // Verify the project has a main function (checked after compilation)
    let project_root = entry_path
        .canonicalize()
        .unwrap_or_else(|_| entry_path.to_path_buf())
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .to_path_buf();

    let lib_dir = find_lib_dir(&project_root);
    let project_cache_dir = cache::cache_dir(&project_root);
    let lib_cache_dir = lib_dir.as_ref().map(|ld| cache::cache_dir(ld));

    // Run the compilation pipeline (writes .o cache files, but doesn't execute main)
    let (_session, _linker) = compile_project_pipeline(&graph, entry_path)?;

    // Verify main exists by checking the entry module's .o has a main symbol
    let entry_id = graph.compile_order.last().unwrap();
    let entry_mod_path = ModuleFullPath::from(entry_id.short_name());
    let entry_o_path = project_cache_dir.join(format!("{}.o", cache::module_file_name(&entry_mod_path)));
    if !entry_o_path.exists() {
        return Err(CranelispError::CodegenError {
            message: "entry module .o not found in cache — compilation may have failed".to_string(),
            span: (0, 0),
        });
    }

    // Collect all module .o file paths from cache directories
    let mut module_o_paths: Vec<std::path::PathBuf> = Vec::new();
    for module_id in &graph.compile_order {
        let mod_path = ModuleFullPath::from(module_id.short_name());
        let module_info = &graph.modules[module_id];

        // Route to correct cache directory
        let target_cache = if module_info.is_lib {
            lib_cache_dir.as_ref().unwrap_or(&project_cache_dir).clone()
        } else {
            project_cache_dir.clone()
        };

        let o_path = target_cache.join(format!("{}.o", cache::module_file_name(&mod_path)));
        if o_path.exists() {
            module_o_paths.push(o_path);
        }
        // Some modules (macro-only) don't produce .o files — that's OK
    }

    // Generate startup stub into project cache dir
    let platform_manifests =
        crate::exe::collect_platform_manifest_names(&_session.tc.modules);
    let startup_bytes = crate::exe::generate_startup_object(&platform_manifests)?;
    let entry_name = cache::module_file_name(&entry_mod_path);
    let startup_o = project_cache_dir.join(format!("{}-startup.o", entry_name));
    std::fs::write(&startup_o, &startup_bytes).map_err(|e| CranelispError::CodegenError {
        message: format!("failed to write startup.o: {}", e),
        span: (0, 0),
    })?;

    // Find the runtime bundle .a
    let bundle_path = crate::exe::find_bundle_lib()?;

    // Find platform rlibs from loaded modules
    let platform_rlibs = crate::exe::find_platform_rlibs(&_session.tc.modules);

    // Link everything into the executable
    crate::exe::link_executable(
        output_path,
        &module_o_paths,
        &startup_o,
        &bundle_path,
        &platform_rlibs,
    )?;

    eprintln!("; Wrote executable: {}", output_path.display());
    Ok(())
}

/// Try to load a module from cache. Returns `Some(true)` if loaded successfully
/// (caller should `continue` the loop), `None` if cache files are missing/invalid
/// (caller should fall through to normal compilation).
#[allow(clippy::too_many_arguments)]
pub(crate) fn try_load_cached_module(
    cache_dir: &Path,
    mod_path: &ModuleFullPath,
    mod_name: &str,
    module: &ModuleInfo,
    is_entry: bool,
    session: &mut ReplSession,
    linker: &mut crate::linker::Linker,
    mod_name_to_short: &std::collections::HashMap<String, String>,
) -> Result<Option<bool>, CranelispError> {
    // Read cached CompiledModule metadata
    let mut cached_cm = match cache::read_cached_module(cache_dir, mod_path) {
        Some(cm) => cm,
        None => return Ok(None),
    };

    // Read cached object file (may not exist for macro-only modules)
    let obj_bytes = cache::read_cached_object(cache_dir, mod_path);

    // ── Resolve imports (same as normal path) ──────────────────────────
    let resolved_imports =
        resolve_module_imports(&module.imports, &session.tc, mod_name_to_short)?;
    if !resolved_imports.is_empty() {
        session.tc.begin_module_scope(&resolved_imports)?;
    }

    // Register module aliases
    for import in &module.imports {
        if let Some(ref alias) = import.alias {
            let source_short = mod_name_to_short
                .get(&import.module_path)
                .cloned()
                .unwrap_or_else(|| import.module_path.clone());
            session
                .tc
                .module_names
                .insert(crate::names::ModuleFullPath::from(alias.as_str()));
            let public = session.tc.get_module_public_names(&source_short);
            for name in &public {
                let source_qualified = format!("{}/{}", source_short, name);
                let alias_qualified = format!("{}/{}", alias, name);
                if let Some(scheme) = session.tc.lookup_env(&source_qualified).cloned() {
                    session.tc.register_alias(&alias_qualified, &scheme);
                }
            }
        }
    }

    // ── Install CompiledModule into TypeChecker ──────────────────────────
    // This makes all symbols, types, traits, constructors resolvable via module-walk.
    // Preserve the existing GOT allocation (its address is already registered with the linker).
    // Compute next_got_slot from the cached module's max slot + 1 so that subsequent
    // allocations (e.g. compile_macro during macro reconstruction) don't overwrite cached entries.
    if let Some(existing) = session.tc.modules.get_mut(mod_path) {
        let got = existing.got_table.take();
        cached_cm.got_table = got;
    }
    // Set next_got_slot to max(cached slots) + 1 so new allocations don't collide
    let max_cached_slot = cached_cm.symbols.values().filter_map(|entry| {
        if let ModuleEntry::Def {
            kind: DefKind::UserFn { codegen, .. }, ..
        } = entry {
            codegen.got_slot
        } else {
            None
        }
    }).max();
    cached_cm.next_got_slot = max_cached_slot.map(|s| s + 1).unwrap_or(0);
    session.tc.modules.insert(mod_path.clone(), cached_cm);

    // Register type definitions with JIT for codegen (needed by dependent modules)
    session.jit.register_type_defs(&session.tc);

    // ── Register trait methods with JIT ────────────────────────────────
    if let Some(cm) = session.tc.modules.get(mod_path) {
        for entry in cm.symbols.values() {
            if let ModuleEntry::TraitDecl { decl, .. } = entry {
                for method in &decl.methods {
                    session.jit.register_trait_method(&method.name);
                }
            }
        }
    }

    // ── Link .o and populate GOT immediately ──────────────────────────
    // GOTs must be populated BEFORE macro reconstruction, because compiled
    // macros call JIT functions via GOT slots.
    {
        let mut slot_entries: Vec<(usize, String)> = Vec::new();
        if let Some(cm) = session.tc.modules.get(mod_path) {
            for (sym, entry) in &cm.symbols {
                if let ModuleEntry::Def {
                    kind:
                        DefKind::UserFn {
                            codegen:
                                crate::module::DefCodegen {
                                    got_slot: Some(slot),
                                    ..
                                },
                            ..
                        },
                    ..
                } = entry
                {
                    slot_entries.push((*slot, sym.to_string()));
                }
            }
        }

        // Load .o into linker and resolve symbols
        if let Some(bytes) = &obj_bytes {
            linker.load_object(mod_name, bytes)?;
        }

        // Populate GOT entries from linker-resolved code pointers
        let mut got_entries: Vec<(usize, *const u8)> = Vec::new();
        for (slot, fn_name) in &slot_entries {
            if let Some(code_ptr) = linker.get_symbol(fn_name) {
                got_entries.push((*slot, code_ptr));
                let mod_fp = ModuleFullPath::from(mod_name);
                if let Some(cm) = session.tc.modules.get_mut(&mod_fp) {
                    cm.update_code_ptr_for_slot(*slot, code_ptr);
                }
            } else {
                return Err(CranelispError::CodegenError {
                    message: format!(
                        "cache load: unresolved function '{}' in module '{}'",
                        fn_name, mod_name
                    ),
                    span: (0, 0),
                });
            }
        }
        if !got_entries.is_empty() {
            let mod_path = ModuleFullPath::from(mod_name);
            if let Some(cm) = session.tc.modules.get_mut(&mod_path) {
                cm.restore_got_entries(&got_entries);
            }
        }
    }

    // ── Reconstruct macros from stored source ────────────────────────────
    // This must happen AFTER GOT population above, since macro compilation
    // calls functions through GOT slots.
    if let Some(cm) = session.tc.modules.get(mod_path) {
        let macro_entries: Vec<_> = cm
            .symbols
            .iter()
            .filter_map(|(name, entry)| {
                if let ModuleEntry::Macro {
                    sexp: Some(sexp),
                    fixed_params,
                    rest_param,
                    docstring,
                    ..
                } = entry
                {
                    Some((
                        name.to_string(),
                        sexp.clone(),
                        fixed_params.clone(),
                        rest_param.clone(),
                        docstring.clone(),
                    ))
                } else {
                    None
                }
            })
            .collect();

        for (name, sexp, fixed_params, rest_param, docstring) in macro_entries {
            let info = parse_defmacro(&sexp)?;
            let ptr = compile_macro(
                &mut session.tc,
                &mut session.jit,
                &info,
                Some(&session.macro_env),
            )?;
            session.macro_env.register(
                name,
                ptr,
                docstring,
                fixed_params,
                rest_param,
                Some(info.body_sexp),
            );
        }
    }

    // ── Register module prefix and clean up scope ──────────────────────
    if !is_entry {
        session.tc.register_module_prefix(mod_name);
        session.tc.end_module_scope();
    }

    Ok(Some(true))
}
