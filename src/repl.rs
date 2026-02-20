mod commands;
pub mod format;
mod handlers;
mod input;
pub mod save;
pub mod util;
mod watch;

use std::collections::{HashMap, HashSet};
use std::io::IsTerminal;
use std::path::{Path, PathBuf};

use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;

use crate::ast::{TopLevel, Visibility};
use crate::ast_builder::build_program;
use crate::ast_builder::build_repl_input_from_sexps;
use crate::error::CranelispError;
use crate::jit::Jit;
use crate::macro_expand::{
    compile_macro, expand_sexp, flatten_begin, is_defmacro, is_deftype, parse_defmacro, MacroEnv,
};
use crate::cache;
use crate::module::{CompiledModule, ModuleFullPath, ModuleGraph};
use crate::names::{FQSymbol, Symbol};
use crate::sexp::parse_sexps;
use crate::typechecker::TypeChecker;
use format::format_symbol_info;

use commands::parse_repl_command;
use util::parens_balanced;

/// Marker for a loaded module (tracks that it has been compiled).
pub struct LoadedModule;

pub struct ReplSession {
    pub tc: TypeChecker,
    pub jit: Jit,
    pub macro_env: MacroEnv,
    pub current_module: ModuleFullPath,
    pub loaded_modules: HashMap<ModuleFullPath, LoadedModule>,
    pub prelude_module_ids: HashSet<ModuleFullPath>,
    pub project_root: PathBuf,
    watcher: Option<watch::FileWatcher>,
    locked_modules: HashSet<ModuleFullPath>,
    /// Linker for cached .o files. Created lazily when first cache load is attempted.
    /// Must outlive execution since it owns mmap'd code regions.
    linker: Option<crate::linker::Linker>,
}

impl ReplSession {
    pub fn new() -> Result<Self, CranelispError> {
        let project_root =
            std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        Self::with_project_root(project_root)
    }

    pub fn with_project_root(project_root: PathBuf) -> Result<Self, CranelispError> {
        let jit = Jit::new()?;
        let mut tc = TypeChecker::new();
        tc.init_builtins();
        // Install macros bare names (SList, Sexp, constructors) so compile_macro
        // can resolve Sexp type annotations. Don't install all synthetic bare names
        // because primitives should only be accessible via qualified names or prelude exports.
        tc.install_macros_bare_names();
        jit.populate_builtin_func_ids(&mut tc.modules);
        Ok(ReplSession {
            tc,
            jit,
            macro_env: MacroEnv::new(),
            current_module: ModuleFullPath("user".to_string()),
            loaded_modules: HashMap::new(),
            prelude_module_ids: HashSet::new(),
            project_root,
            watcher: None,
            locked_modules: HashSet::new(),
            linker: None,
        })
    }

    /// Build a mod_name_to_short map from a module graph, seeded with synthetic modules.
    fn build_mod_name_map(&self, graph: &ModuleGraph) -> HashMap<String, String> {
        let mut map: HashMap<String, String> = HashMap::new();
        // Seed with synthetic modules (primitives, platform.stdio) so imports can resolve them
        for name in &self.tc.module_names {
            let s = name.0.clone();
            map.entry(s.clone()).or_insert(s);
        }
        // Add graph modules
        for module_id in &graph.compile_order {
            let short = module_id.short_name().to_string();
            map.insert(module_id.0.clone(), short.clone());
            map.insert(short.clone(), short);
        }
        map
    }

    /// Build a mod_name_to_short map from loaded modules, seeded with synthetic modules.
    fn build_loaded_mod_name_map(&self) -> HashMap<String, String> {
        let mut map: HashMap<String, String> = HashMap::new();
        // Seed with synthetic modules
        for name in &self.tc.module_names {
            let s = name.0.clone();
            map.entry(s.clone()).or_insert(s);
        }
        // Add loaded modules
        for module_id in self.loaded_modules.keys() {
            let short = module_id.short_name().to_string();
            map.insert(module_id.0.clone(), short.clone());
            map.insert(short.clone(), short);
        }
        map
    }

    /// Compile all modules in a graph into this session.
    /// Skips already-loaded modules. Returns the list of module IDs that were compiled.
    /// If `entry_id` is Some, that module's scope is kept open (not ended) so its
    /// names remain accessible for the REPL.
    fn compile_module_graph(
        &mut self,
        graph: &ModuleGraph,
        entry_id: Option<&ModuleFullPath>,
    ) -> Result<Vec<ModuleFullPath>, CranelispError> {
        let mod_name_to_short = self.build_mod_name_map(graph);
        let mut compiled = Vec::new();

        // ── Cache infrastructure ──────────────────────────────────────────
        let lib_dir = crate::module::find_lib_dir(&self.project_root);
        let project_cache_dir = cache::cache_dir(&self.project_root);
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
        let mut any_cache_activity = false;

        // Ensure per-module GOTs exist up front (needed for cache loading / linker registration)
        for module_id in &graph.compile_order {
            if !self.loaded_modules.contains_key(module_id) {
                let mod_path = ModuleFullPath::from(module_id.short_name());
                let cm = self.tc.modules
                    .entry(mod_path.clone())
                    .or_insert_with(|| CompiledModule::new(mod_path));
                cm.ensure_got();
            }
        }

        for module_id in &graph.compile_order {
            if self.loaded_modules.contains_key(module_id) {
                continue;
            }

            let module = &graph.modules[module_id];
            let mod_name = module_id.short_name().to_string();
            let mod_path = ModuleFullPath::from(mod_name.as_str());
            let source_hash = cache::hash_source(&module.source);

            // Set current module for module-walk resolution
            self.tc
                .set_current_module_path(ModuleFullPath::from(mod_name.as_str()));

            // Determine if this module is a lib module based on its file path,
            // not the graph's is_lib (which depends on the graph's entry file).
            let is_lib_module = lib_dir
                .as_ref()
                .is_some_and(|ld| module.file_path.starts_with(ld));

            // ── Cache check: try to load from cache ──────────────────────
            let (target_cache, existing_manifest_ref) = if is_lib_module {
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
                // Ensure linker is ready
                if self.linker.is_none() {
                    let mut linker = crate::linker::Linker::new();
                    self.jit.register_runtime_symbols(&mut linker);
                    // Register GOT base addresses for all modules
                    for mid in &graph.compile_order {
                        let mod_path = ModuleFullPath::from(mid.short_name());
                        let got_symbol = format!("__cranelisp_got_{}", crate::cache::module_file_name(&mod_path));
                        if let Some(cm) = self.tc.modules.get(&mod_path) {
                            if let Some(got_addr) = cm.got_table_addr() {
                                linker.register_symbol(&got_symbol, got_addr as *const u8);
                            }
                        }
                    }
                    self.linker = Some(linker);
                }

                let is_entry = entry_id.is_some_and(|eid| eid == module_id);
                // Temporarily take linker to avoid borrow issues
                let mut linker = self.linker.take().unwrap();
                let result = crate::batch::try_load_cached_module(
                    &target_cache,
                    &mod_path,
                    &mod_name,
                    module,
                    is_entry,
                    self,
                    &mut linker,
                    &mod_name_to_short,
                );
                self.linker = Some(linker);

                match result? {
                    Some(true) => {
                        eprintln!("; Loaded {} from cache", mod_name);
                        if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                            cm.content_hash = Some(source_hash.clone());
                        }
                        if is_lib_module {
                            lib_cache_manifest.upsert_module(mod_path, source_hash);
                            lib_cache_dirty = true;
                        } else {
                            project_cache_manifest.upsert_module(mod_path, source_hash);
                        }
                        any_cache_activity = true;
                        self.loaded_modules
                            .insert(module_id.clone(), LoadedModule);
                        compiled.push(module_id.clone());
                        continue;
                    }
                    _ => {
                        // Fall through to normal compilation
                    }
                }
            }

            // ── Normal compilation path ──────────────────────────────────

            // Resolve imports
            let resolved_imports = crate::module::resolve_module_imports(
                &module.imports,
                &self.tc,
                &mod_name_to_short,
            )?;

            if !resolved_imports.is_empty() {
                self.tc.begin_module_scope(&resolved_imports)?;
            }

            // Register module alias if any import declares one
            for import in &module.imports {
                if let Some(ref alias) = import.alias {
                    let source_short = mod_name_to_short
                        .get(&import.module_path)
                        .cloned()
                        .unwrap_or_else(|| import.module_path.clone());
                    self.tc
                        .module_names
                        .insert(crate::names::ModuleFullPath::from(alias.as_str()));
                    let public = self.tc.get_module_public_names(&source_short);
                    for pname in &public {
                        let source_qualified = format!("{}/{}", source_short, pname);
                        let alias_qualified = format!("{}/{}", alias, pname);
                        if let Some(scheme) = self.tc.lookup_env(&source_qualified).cloned() {
                            self.tc.register_alias(&alias_qualified, &scheme);
                        }
                    }
                }
            }

            // Populate CompiledModule metadata for file generation
            {
                let mod_path = ModuleFullPath::from(mod_name.as_str());
                let cm = self
                    .tc
                    .modules
                    .entry(mod_path.clone())
                    .or_insert_with(|| CompiledModule::new(mod_path));
                cm.file_path = Some(module.file_path.clone());
                cm.mod_decls = module
                    .child_mod_names
                    .iter()
                    .map(|(n, _)| crate::names::ModuleName::from(n.as_str()))
                    .collect();
                cm.import_specs = module.imports.clone();
                cm.export_specs = module.exports.clone();
            }

            // Pre-pass: register type definitions
            for sexp in &module.sexps {
                if is_deftype(sexp) {
                    let items = build_program(std::slice::from_ref(sexp))?;
                    for item in &items {
                        self.tc.register_type_def(item);
                    }
                    // Store sexp on the TypeDef entry
                    if let Some(type_name) = Self::extract_type_name(sexp) {
                        let mod_path = ModuleFullPath::from(mod_name.as_str());
                        if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                            if let Some(crate::module::ModuleEntry::TypeDef {
                                sexp: entry_sexp, ..
                            }) = cm.symbols.get_mut(type_name.as_str())
                            {
                                *entry_sexp = Some(sexp.clone());
                            }
                        }
                    }
                }
            }
            self.jit.register_type_defs(&self.tc);

            // Sequential compile
            for sexp in &module.sexps {
                let sexp_source: &str =
                    &module.source[sexp.span().0..sexp.span().1.min(module.source.len())];

                // Type defs already registered in pre-pass (register_type_def writes to CompiledModule)
                if is_deftype(sexp) {
                    continue;
                }

                if is_defmacro(sexp) {
                    let info = parse_defmacro(sexp)?;
                    let ptr =
                        compile_macro(&mut self.tc, &mut self.jit, &info, Some(&self.macro_env))?;
                    self.tc.register_macro_in_module(
                        &info.name,
                        info.fixed_params.clone(),
                        info.rest_param.clone(),
                        info.docstring.clone(),
                        info.visibility,
                        Some(sexp.clone()),
                        Some(sexp.to_string()),
                    );
                    self.macro_env.register(
                        info.name.clone(),
                        ptr,
                        info.docstring,
                        info.fixed_params,
                        info.rest_param,
                        Some(info.body_sexp),
                    );
                    continue;
                }

                let expanded = if !self.macro_env.is_empty() {
                    expand_sexp(sexp.clone(), &self.macro_env, 0)?
                } else {
                    sexp.clone()
                };

                // Flatten begin forms and handle defmacro-in-results
                let forms = flatten_begin(expanded);
                for form in &forms {
                    if is_defmacro(form) {
                        let info = parse_defmacro(form)?;
                        let ptr = compile_macro(
                            &mut self.tc,
                            &mut self.jit,
                            &info,
                            Some(&self.macro_env),
                        )?;
                        self.tc.register_macro_in_module(
                            &info.name,
                            info.fixed_params.clone(),
                            info.rest_param.clone(),
                            info.docstring.clone(),
                            info.visibility,
                            Some(form.clone()),
                            Some(form.to_string()),
                        );
                        self.macro_env.register(
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
                            self.tc.register_type_def(type_item);
                        }
                        self.jit.register_type_defs(&self.tc);
                        continue;
                    }
                }

                // Build AST from non-defmacro, non-deftype forms
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
                        TopLevel::TypeDef { .. } => {}
                        TopLevel::TraitDecl(td) => {
                            for method in &td.methods {
                                self.jit.register_trait_method(&method.name);
                            }
                            self.tc.register_trait_public(td);
                            // Store sexp on the TraitDecl entry
                            {
                                let mod_path = ModuleFullPath::from(mod_name.as_str());
                                if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                                    if let Some(crate::module::ModuleEntry::TraitDecl {
                                        sexp: entry_sexp,
                                        ..
                                    }) = cm.symbols.get_mut(td.name.as_str())
                                    {
                                        *entry_sexp = Some(sexp.clone());
                                    }
                                }
                            }
                        }
                        TopLevel::TraitImpl(ti) => {
                            self.tc.validate_impl_public(ti)?;
                            self.tc.register_impl(ti);
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
                                self.tc.check_defn(&mangled)?;
                                let mut mr = self.tc.resolve_methods()?;
                                self.tc.resolve_overloads(&mut mr)?;
                                let et = self.tc.resolve_expr_types();
                                let scheme = self.tc.finalize_defn_type(&mangled.name);
                                // Ensure Def entry exists
                                {
                                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                                    if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
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
                                    self.tc.modules.get(&mod_path)
                                        .and_then(|cm| cm.get_got_slot(&mangled.name))
                                        .map(Ok)
                                        .unwrap_or_else(|| {
                                        let mod_path = ModuleFullPath::from(mod_name.as_str());
                                        self.tc.modules.get_mut(&mod_path).unwrap().allocate_got_slot(mangled.span)
                                    })
                                }?;
                                {
                                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                                    if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                                        cm.pre_register_for_codegen(&mangled.name, slot, mangled.params.len());
                                    }
                                }
                                let fn_slots = self.jit.build_fn_slots_from_modules(&self.tc.modules);
                                let compile_meta = self.jit.compile_defn_in_module(
                                    &mangled,
                                    &scheme,
                                    &mr,
                                    &mod_name,
                                    &et,
                                    slot,
                                    &fn_slots,
                                    &self.tc.modules,
                                )?;
                                // Write codegen metadata + accumulate for cache
                                {
                                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                                    if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                                        cm.write_got_slot(slot, compile_meta.code_ptr);
                                        cm.update_codegen(&mangled.name, &compile_meta, Some(sexp_source), Some(sexp), Some(&mangled));
                                        cm.accumulate_method_resolutions(mr);
                                        cm.accumulate_expr_types(et);
                                    }
                                }
                            }
                            // Store impl sexp for file generation
                            {
                                let mod_path = ModuleFullPath::from(mod_name.as_str());
                                if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                                    cm.impl_sexps.push(crate::module::ImplSexp {
                                        trait_name: crate::names::TraitName::from(
                                            ti.trait_name.as_str(),
                                        ),
                                        target: crate::names::TypeName::from(
                                            ti.target_type.as_str(),
                                        ),
                                        sexp: sexp.clone(),
                                    });
                                }
                            }
                        }
                        TopLevel::Defn(defn) => {
                            self.tc.check_defn(defn)?;
                            let mut mr = self.tc.resolve_methods()?;
                            self.tc.resolve_overloads(&mut mr)?;
                            let et = self.tc.resolve_expr_types();
                            let scheme = self.tc.finalize_defn_type(&defn.name);
                            if scheme.is_constrained() {
                                self.tc.register_constrained_fn(defn, &scheme);
                            } else {
                                // Ensure Def entry exists for fn_slots
                                {
                                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                                    let cm = self.tc.modules
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
                                    self.tc.modules.get(&mod_path)
                                        .and_then(|cm| cm.get_got_slot(&defn.name))
                                        .map(Ok)
                                        .unwrap_or_else(|| {
                                        let mod_path = ModuleFullPath::from(mod_name.as_str());
                                        self.tc.modules.get_mut(&mod_path).unwrap().allocate_got_slot(defn.span)
                                    })
                                }?;
                                {
                                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                                    if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                                        cm.pre_register_for_codegen(&defn.name, slot, defn.params.len());
                                    }
                                }
                                let fn_slots = self.jit.build_fn_slots_from_modules(&self.tc.modules);
                                let compile_meta = self.jit.compile_defn_in_module(
                                    defn,
                                    &scheme,
                                    &mr,
                                    &mod_name,
                                    &et,
                                    slot,
                                    &fn_slots,
                                    &self.tc.modules,
                                )?;
                                // Write metadata to CompiledModule + accumulate for cache
                                let mod_path = ModuleFullPath::from(mod_name.as_str());
                                let cm = self
                                    .tc
                                    .modules
                                    .entry(mod_path.clone())
                                    .or_insert_with(|| CompiledModule::new(mod_path));
                                cm.insert_def(
                                    Symbol::from(defn.name.as_str()),
                                    scheme.clone(),
                                    defn.visibility,
                                    None,
                                );
                                cm.write_got_slot(slot, compile_meta.code_ptr);
                                cm.update_codegen(
                                    &defn.name,
                                    &compile_meta,
                                    Some(sexp_source),
                                    Some(sexp),
                                    Some(defn),
                                );
                                cm.accumulate_method_resolutions(mr);
                                cm.accumulate_expr_types(et);
                            }
                        }
                        TopLevel::DefnMulti {
                            name,
                            visibility,
                            docstring,
                            variants,
                            ..
                        } => {
                            let base_meta = crate::typechecker::SymbolMeta::UserFn {
                                docstring: docstring.clone(),
                                param_names: vec![],
                            };
                            self.tc
                                .update_current_module_meta(name, base_meta.clone());
                            let checked = self.tc.check_defn_multi(name, variants)?;
                            let mut mr = self.tc.resolve_methods()?;
                            self.tc.resolve_overloads(&mut mr)?;
                            let et = self.tc.resolve_expr_types();
                            for (mangled_name, mangled_defn, _scheme) in &checked {
                                let scheme = self.tc.finalize_defn_type(mangled_name);
                                // Ensure Def entry for fn_slots
                                {
                                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                                    if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
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
                                    self.tc.modules.get(&mod_path)
                                        .and_then(|cm| cm.get_got_slot(mangled_name))
                                        .map(Ok)
                                        .unwrap_or_else(|| {
                                        let mod_path = ModuleFullPath::from(mod_name.as_str());
                                        self.tc.modules.get_mut(&mod_path).unwrap().allocate_got_slot(mangled_defn.span)
                                    })
                                }?;
                                {
                                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                                    if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                                        cm.pre_register_for_codegen(mangled_name, slot, mangled_defn.params.len());
                                    }
                                }
                                let fn_slots = self.jit.build_fn_slots_from_modules(&self.tc.modules);
                                let compile_meta = self.jit.compile_defn_in_module(
                                    mangled_defn,
                                    &scheme,
                                    &mr,
                                    &mod_name,
                                    &et,
                                    slot,
                                    &fn_slots,
                                    &self.tc.modules,
                                )?;
                                // Write codegen metadata
                                {
                                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                                    if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                                        cm.write_got_slot(slot, compile_meta.code_ptr);
                                        cm.update_codegen(mangled_name, &compile_meta, Some(sexp_source), Some(sexp), Some(mangled_defn));
                                    }
                                }
                            }
                            // Accumulate mr/et for cache
                            {
                                let mod_path = ModuleFullPath::from(mod_name.as_str());
                                if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                                    cm.accumulate_method_resolutions(mr);
                                    cm.accumulate_expr_types(et);
                                }
                            }
                            // Register base name in universal so module
                            // aliasing/re-export/import can propagate it.
                            if let Some((first_mangled, _, _)) = checked.first() {
                                let scheme = self.tc.finalize_defn_type(first_mangled);
                                // Write DefnMulti base name into CompiledModule
                                {
                                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                                    let cm = self
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

            // Process exports
            for export in &module.exports {
                let source_short = mod_name_to_short
                    .get(&export.module_path)
                    .cloned()
                    .unwrap_or_else(|| export.module_path.clone());

                let names_to_export = match &export.names {
                    crate::module::ImportNames::Specific(names) => {
                        let public = self.tc.get_module_public_names(&source_short);
                        for ename in names {
                            if !public.contains(ename) {
                                return Err(CranelispError::ModuleError {
                                    message: format!(
                                        "export: '{}' is not a public name in module '{}'",
                                        ename, export.module_path
                                    ),
                                    file: None,
                                    span: export.span,
                                });
                            }
                        }
                        names.clone()
                    }
                    crate::module::ImportNames::Glob => {
                        self.tc.get_module_public_names(&source_short)
                    }
                    _ => Vec::new(),
                };

                for ename in &names_to_export {
                    // Write re-export into CompiledModule
                    {
                        let mod_path = ModuleFullPath::from(mod_name.as_str());
                        let cm = self
                            .tc
                            .modules
                            .entry(mod_path.clone())
                            .or_insert_with(|| CompiledModule::new(mod_path));
                        cm.insert_reexport(
                            Symbol::from(ename.as_str()),
                            FQSymbol::new(
                                ModuleFullPath::from(source_short.as_str()),
                                Symbol::from(ename.as_str()),
                            ),
                        );
                    }
                }
            }

            // ── Write module cache (best-effort, non-fatal) ──────────────
            {
                let fn_slots = self.jit.build_fn_slots_from_modules(&self.tc.modules);
                cache::write_module_cache(
                    &target_cache,
                    &mod_path,
                    &mod_name,
                    &mut self.tc.modules,
                    &fn_slots,
                    self.jit.builtin_method_info(),
                    self.jit.trait_method_names(),
                    self.jit.type_defs_cg(),
                    self.jit.constructor_to_type_cg(),
                );
                if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                    cm.clear_cache_transients();
                    cm.content_hash = Some(source_hash.clone());
                }
                eprintln!("; Wrote cache for {}", mod_name);

                if is_lib_module {
                    lib_cache_manifest.upsert_module(mod_path, source_hash);
                    lib_cache_dirty = true;
                } else {
                    project_cache_manifest.upsert_module(mod_path, source_hash);
                }
                any_cache_activity = true;
            }

            // Register module prefix and clean up module scope.
            // If this is the entry module, keep its scope open for the REPL.
            let is_entry = entry_id.is_some_and(|eid| eid == module_id);
            self.tc.register_module_prefix(&mod_name);
            if !is_entry {
                self.tc.end_module_scope();
            }

            // Track as loaded
            self.loaded_modules
                .insert(module_id.clone(), LoadedModule);

            compiled.push(module_id.clone());
        }

        // ── Write cache manifests ────────────────────────────────────────
        if any_cache_activity {
            if !project_cache_manifest.modules.is_empty() {
                if let Err(e) =
                    cache::write_manifest(&project_cache_dir, &project_cache_manifest)
                {
                    eprintln!("warning: failed to write project cache manifest: {}", e);
                }
            }
            if lib_cache_dirty {
                if let Some(ref lcd) = lib_cache_dir {
                    if let Err(e) = cache::write_manifest(lcd, &lib_cache_manifest) {
                        eprintln!("warning: failed to write lib cache manifest: {}", e);
                    }
                }
            }
        }

        Ok(compiled)
    }

    /// Compile monomorphised specializations into their defining modules.
    ///
    /// Each `(MonoDefn, ModuleFullPath)` pair is compiled into the defining module's GOT.
    /// This is the shared implementation used by batch compilation, REPL expression
    /// evaluation, and REPL command handlers (`/time`, `/mem`).
    pub fn compile_mono_specializations(
        &mut self,
        mono_defns: &[(crate::typechecker::MonoDefn, ModuleFullPath)],
        method_resolutions: &crate::typechecker::MethodResolutions,
        expr_types: &std::collections::HashMap<crate::error::Span, crate::types::Type>,
    ) -> Result<(), crate::error::CranelispError> {
        use crate::ast::Visibility;
        use crate::types::{Scheme, Type};

        for (mono, defining_mod) in mono_defns {
            let mono_scheme = Scheme::mono(Type::Fn(
                mono.defn.params.iter().map(|_| Type::Int).collect(),
                Box::new(Type::Int),
            ));
            if let Some(cm) = self.tc.modules.get_mut(defining_mod) {
                cm.insert_def(
                    Symbol::from(mono.defn.name.as_str()),
                    mono_scheme.clone(),
                    Visibility::Public,
                    None,
                );
            }
            let slot = {
                let cm = self.tc.modules.get_mut(defining_mod).unwrap();
                cm.allocate_got_slot(mono.defn.span)?
            };
            if let Some(cm) = self.tc.modules.get_mut(defining_mod) {
                cm.pre_register_for_codegen(&mono.defn.name, slot, mono.defn.params.len());
            }
            let fn_slots = self.jit.build_fn_slots_from_modules(&self.tc.modules);
            let compile_meta = self.jit.compile_defn_with_resolutions(
                &mono.defn,
                &mono_scheme,
                method_resolutions,
                Some(&mono.resolutions),
                expr_types,
                slot,
                &fn_slots,
                &self.tc.modules,
            )?;
            if let Some(cm) = self.tc.modules.get_mut(defining_mod) {
                cm.write_got_slot(slot, compile_meta.code_ptr);
                cm.update_codegen(&mono.defn.name, &compile_meta, None, None, Some(&mono.defn));
                cm.accumulate_method_resolutions(mono.resolutions.clone());
                cm.accumulate_expr_types(expr_types.clone());
            }
        }
        Ok(())
    }

    /// Load the prelude by discovering prelude.cl via unified resolution,
    /// building a module graph, and compiling all modules (core + prelude) into the session.
    /// After compilation, installs prelude's public names as bare names (implied import).
    pub fn load_prelude(&mut self) {
        let lib_dir = crate::module::find_lib_dir(&self.project_root);
        let prelude_path = crate::module::resolve_root_module(
            "prelude",
            &self.project_root,
            lib_dir.as_deref(),
        );
        let prelude_path = match prelude_path {
            Some(p) => p,
            None => return, // No prelude found — valid, core language works without it
        };

        let graph = match ModuleGraph::build(&prelude_path) {
            Ok(g) => g,
            Err(e) => {
                eprintln!("Warning: failed to load prelude: {}", e);
                return;
            }
        };

        // Compile all modules through the normal module system
        let compiled = match self.compile_module_graph(&graph, None) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("Warning: failed to compile prelude: {}", e);
                return;
            }
        };

        // Track prelude module IDs
        for module_id in &compiled {
            self.prelude_module_ids.insert(module_id.clone());
        }

        // Reset current module path to "user" BEFORE installing prelude imports,
        // so that install_imported_names writes Import entries into "user"'s
        // CompiledModule (not the last-compiled module like "prelude").
        self.tc
            .set_current_module_path(ModuleFullPath::from("user"));

        // Implied `(import [prelude [*]])`: install prelude's public names as bare names
        let prelude_public = self.tc.get_module_public_names("prelude");
        let resolved: Vec<(String, String)> = prelude_public
            .into_iter()
            .map(|name| (name, "prelude".to_string()))
            .collect();
        self.tc.install_imported_names(&resolved);

        // Re-register type defs on the JIT now that bare names are restored.
        self.jit.register_type_defs(&self.tc);
    }

    /// Load a module by name from the filesystem.
    /// Discovers the module file, builds a module graph, and compiles all
    /// modules in dependency order (skipping already-loaded modules).
    pub fn load_module_by_name(&mut self, name: &str) -> Result<(), CranelispError> {
        let target_id = ModuleFullPath(name.to_string());

        // Already loaded?
        if self.loaded_modules.contains_key(&target_id) {
            return Ok(());
        }

        // Resolve name to file path using project_root and lib directory
        let lib_dir = crate::module::find_lib_dir(&self.project_root);
        let file_path =
            crate::module::resolve_root_module(name, &self.project_root, lib_dir.as_deref())
                .ok_or_else(|| CranelispError::ModuleError {
                    message: format!("module '{}' not found", name),
                    file: None,
                    span: (0, 0),
                })?;

        // Build module graph from that file
        let graph = ModuleGraph::build(&file_path)?;

        self.compile_module_graph(&graph, None)?;

        Ok(())
    }

    /// Handle an `(import ...)` form at the REPL.
    /// Parses import specs, loads referenced modules on demand, and installs
    /// imported names as bare names in the typechecker env.
    fn handle_repl_import(&mut self, sexp: &crate::sexp::Sexp) {
        // Parse the import sexp using module declaration extraction
        let decls = match crate::module::extract_module_decls(vec![sexp.clone()]) {
            Ok(d) => d,
            Err(e) => {
                eprintln!("{}", e);
                return;
            }
        };

        if decls.imports.is_empty() {
            eprintln!("No imports found");
            return;
        }

        // Load each referenced module on demand (skip synthetic modules like primitives/platform.stdio)
        for import in &decls.imports {
            let module_name = &import.module_path;
            let target_id = ModuleFullPath(module_name.clone());
            if !self.loaded_modules.contains_key(&target_id)
                && !self.tc.module_names.contains(module_name.as_str())
            {
                match self.load_module_by_name(module_name) {
                    Ok(()) => {}
                    Err(e) => {
                        eprintln!("{}", e);
                        return;
                    }
                }
            }
        }

        // Build mod_name_to_short map from loaded modules + synthetic modules
        let mod_name_to_short = self.build_loaded_mod_name_map();

        // Resolve imports
        let resolved = match crate::module::resolve_module_imports(
            &decls.imports,
            &self.tc,
            &mod_name_to_short,
        ) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("{}", e);
                return;
            }
        };

        // Install resolved names as bare names (incremental — doesn't clear existing imports)
        self.tc.install_imported_names(&resolved);

        // Track import specs for file generation
        {
            let mod_path = self.current_module.clone();
            if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                cm.import_specs.extend(decls.imports.clone());
            }
        }

        // Report what was imported
        let names: Vec<&str> = resolved.iter().map(|(n, _)| n.as_str()).collect();
        if names.len() == 1 {
            println!("Imported: {}", names[0]);
        } else {
            println!("Imported: {}", names.join(", "));
        }

        self.update_watched_paths();
        self.save_current_module();
    }

    /// Handle a `(mod name)` form at the REPL.
    /// Declares a child module: loads it if the file exists, or creates
    /// a fresh empty module file. Records the mod_decl on the current module
    /// and saves the parent file.
    fn handle_repl_mod(&mut self, name: &str) {
        // 1. Determine child file path as sibling of current module's file
        let child_file = {
            let cm = self.tc.modules.get(&self.current_module);
            match cm.and_then(|cm| cm.file_path.as_ref()) {
                Some(parent_path) => {
                    let dir = parent_path.parent().unwrap_or_else(|| Path::new("."));
                    dir.join(format!("{}.cl", name))
                }
                None => self.project_root.join(format!("{}.cl", name)),
            }
        };

        let target_id = ModuleFullPath(name.to_string());

        // 2. Load or create the child module
        if self.loaded_modules.contains_key(&target_id) {
            // Already loaded — just ensure mod_decls is updated below
        } else if child_file.exists() {
            // File exists — load it
            if let Err(e) = self.load_module_by_name(name) {
                eprintln!("{}", e);
                return;
            }
        } else {
            // File doesn't exist — create fresh module and save empty file
            let mod_path = ModuleFullPath(name.to_string());
            let mut cm = CompiledModule::new(mod_path.clone());
            cm.file_path = Some(child_file);
            let hash = save::save_module_file(&cm, &self.tc);
            if let Some(h) = hash {
                cm.content_hash = Some(h);
            }
            self.tc.modules.insert(mod_path.clone(), cm);
            self.loaded_modules
                .insert(target_id.clone(), LoadedModule);
            self.tc.register_module_prefix(name);

            // Install implicit prelude imports if prelude was loaded
            if !self.prelude_module_ids.is_empty() {
                let saved = self.current_module.clone();
                self.tc.set_current_module_path(mod_path);
                let prelude_public = self.tc.get_module_public_names("prelude");
                let resolved: Vec<(String, String)> = prelude_public
                    .into_iter()
                    .map(|n| (n, "prelude".to_string()))
                    .collect();
                self.tc.install_imported_names(&resolved);
                self.tc.set_current_module_path(saved);
            }
        }

        // 3. Add to current module's mod_decls if not already present
        let mod_name = crate::names::ModuleName::from(name);
        if let Some(cm) = self.tc.modules.get_mut(&self.current_module) {
            if !cm.mod_decls.contains(&mod_name) {
                cm.mod_decls.push(mod_name);
            }
        }

        // 4. Save current module so (mod foo) appears in the file
        self.save_current_module();

        // 5. Update watched paths and confirmation
        self.update_watched_paths();
        println!("mod {}", name);
    }

    /// Handle `(platform name)` or `(platform name "path")` in the REPL.
    fn handle_repl_platform(
        &mut self,
        name: &str,
        explicit_path: Option<&str>,
        span: (usize, usize),
    ) {
        use crate::names::Symbol;

        // 1. Resolve DLL path
        let dll_path = match explicit_path {
            Some(p) => std::path::PathBuf::from(p),
            None => match crate::platform::resolve_platform_path(name) {
                Some(p) => p,
                None => {
                    eprintln!("Error: platform '{}' not found", name);
                    return;
                }
            },
        };

        // 2. Load platform DLL
        let (manifest_name, version, descriptors) = match self.jit.load_platform(&dll_path) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("{}", e);
                return;
            }
        };

        // 3. Validate manifest name matches declared name
        if manifest_name != name {
            eprintln!(
                "Error: platform name mismatch: declared '{}' but DLL reports '{}'",
                name, manifest_name
            );
            return;
        }

        // 4. Register types (creates platform.<name> module with entries)
        if let Err(e) = self.tc.register_platform(name, &descriptors) {
            eprintln!("Error registering platform: {}", e);
            return;
        }

        // 5. Set dll_path on platform module
        let module_name = format!("platform.{}", name);
        let mod_path = ModuleFullPath::from(module_name.as_str());
        if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
            cm.dll_path = Some(dll_path.clone());
        }

        // 6. Backfill FuncIds
        self.jit.populate_builtin_func_ids(&mut self.tc.modules);

        // 7. Insert PlatformDecl entry in current module
        if let Some(cm) = self.tc.modules.get_mut(&self.current_module) {
            cm.symbols.insert(
                Symbol::from(module_name.as_str()),
                crate::module::ModuleEntry::PlatformDecl {
                    dll_path,
                    platform_module: mod_path,
                },
            );
        }

        // 8. Report
        let fn_count = descriptors.len();
        let _ = span; // span available for future error reporting
        println!(
            "Loaded platform: {} v{} ({} functions)",
            name, version, fn_count
        );
        println!(
            "  Use (import [platform.{} [*]]) to bring into scope",
            name
        );

        // 9. Save module file
        self.save_current_module();
    }

    /// Scan sexps for qualified names (containing `/`) and try to auto-load
    /// any referenced modules that aren't already loaded.
    fn auto_load_qualified_refs(&mut self, sexps: &[crate::sexp::Sexp]) {
        let mut prefixes = HashSet::new();
        for sexp in sexps {
            Self::collect_qualified_prefixes(sexp, &mut prefixes);
        }
        for prefix in &prefixes {
            let target = ModuleFullPath(prefix.clone());
            if !self.loaded_modules.contains_key(&target)
                && !self.tc.module_names.contains(prefix.as_str())
            {
                // Try to load — silently ignore failures (the actual error will
                // surface later during typechecking if the name is truly unresolved)
                let _ = self.load_module_by_name(prefix);
            }
        }
    }

    /// Extract the type name from a `(deftype ...)` sexp.
    fn extract_type_name(sexp: &crate::sexp::Sexp) -> Option<String> {
        if let crate::sexp::Sexp::List(children, _) = sexp {
            if children.len() >= 2 {
                match &children[1] {
                    crate::sexp::Sexp::Symbol(name, _) => return Some(name.clone()),
                    crate::sexp::Sexp::List(inner, _) => {
                        if let Some(crate::sexp::Sexp::Symbol(name, _)) = inner.first() {
                            return Some(name.clone());
                        }
                    }
                    _ => {}
                }
            }
        }
        None
    }

    /// Recursively collect module prefixes from qualified names in a sexp tree.
    fn collect_qualified_prefixes(sexp: &crate::sexp::Sexp, prefixes: &mut HashSet<String>) {
        match sexp {
            crate::sexp::Sexp::Symbol(name, _) => {
                if let Some(slash_pos) = name.find('/') {
                    let prefix = &name[..slash_pos];
                    if !prefix.is_empty() {
                        prefixes.insert(prefix.to_string());
                    }
                }
            }
            crate::sexp::Sexp::List(children, _) | crate::sexp::Sexp::Bracket(children, _) => {
                for child in children {
                    Self::collect_qualified_prefixes(child, prefixes);
                }
            }
            _ => {}
        }
    }

    /// Save the current module's source file after a definition change,
    /// then update the compiled module cache (.meta.json + .o + manifest).
    fn save_current_module(&mut self) {
        if self.locked_modules.contains(&self.current_module) {
            return; // Don't overwrite locked module's file
        }
        let hash = self
            .tc
            .modules
            .get(&self.current_module)
            .and_then(|cm| save::save_module_file(cm, &self.tc));
        if let Some(ref h) = hash {
            if let Some(cm) = self.tc.modules.get_mut(&self.current_module) {
                cm.content_hash = Some(h.clone());
            }
            self.write_current_module_cache(h);
        }
    }

    /// Write the current module's cache files (.meta.json, .o, manifest).
    /// Best-effort: logs warnings, doesn't propagate errors.
    /// Does NOT clear cache transients, so they accumulate across REPL definitions.
    fn write_current_module_cache(&mut self, source_hash: &str) {
        // Skip lib modules — their cache is managed by compile_module_graph
        let lib_dir = crate::module::find_lib_dir(&self.project_root);
        let is_lib = lib_dir.as_ref().is_some_and(|ld| {
            self.tc
                .modules
                .get(&self.current_module)
                .and_then(|cm| cm.file_path.as_ref())
                .is_some_and(|fp| fp.starts_with(ld))
        });
        if is_lib {
            return;
        }

        let project_cache_dir = cache::cache_dir(&self.project_root);
        let mod_path = self.current_module.clone();
        let mod_name = mod_path.short_name().to_string();

        // Write .meta.json + .o
        let fn_slots = self.jit.build_fn_slots_from_modules(&self.tc.modules);
        cache::write_module_cache(
            &project_cache_dir,
            &mod_path,
            &mod_name,
            &mut self.tc.modules,
            &fn_slots,
            self.jit.builtin_method_info(),
            self.jit.trait_method_names(),
            self.jit.type_defs_cg(),
            self.jit.constructor_to_type_cg(),
        );

        // Update manifest
        let target_triple = cranelift_native::builder()
            .map(|b| b.triple().to_string())
            .unwrap_or_else(|_| "unknown".to_string());
        let mut manifest = cache::read_manifest(&project_cache_dir)
            .filter(cache::is_manifest_compatible)
            .unwrap_or_else(|| cache::CacheManifest::new(&target_triple));
        manifest.upsert_module(mod_path, source_hash.to_string());
        if let Err(e) = cache::write_manifest(&project_cache_dir, &manifest) {
            eprintln!("warning: failed to write cache manifest: {}", e);
        }
        eprintln!("; Wrote cache for {}", mod_name);
    }

    /// Initialize the file watcher for all loaded modules.
    fn init_watcher(&mut self) {
        let mut watcher = match watch::FileWatcher::new() {
            Some(w) => w,
            None => return,
        };
        for cm in self.tc.modules.values() {
            if let Some(file_path) = &cm.file_path {
                watcher.watch_path(file_path);
            }
        }
        self.watcher = Some(watcher);
    }

    /// Add any newly loaded module files to the watcher.
    fn update_watched_paths(&mut self) {
        if let Some(ref mut watcher) = self.watcher {
            for cm in self.tc.modules.values() {
                if let Some(file_path) = &cm.file_path {
                    watcher.watch_path(file_path);
                }
            }
        }
    }

    /// Map a file path to its owning module ID.
    fn file_path_to_module(&self, path: &Path) -> Option<ModuleFullPath> {
        let canonical = path.canonicalize().ok()?;
        for mod_id in self.loaded_modules.keys() {
            if let Some(cm) = self.tc.modules.get(mod_id) {
                if let Some(file_path) = &cm.file_path {
                    if let Ok(cm_canonical) = file_path.canonicalize() {
                        if cm_canonical == canonical {
                            return Some(mod_id.clone());
                        }
                    }
                }
            }
        }
        None
    }

    /// Handle file changes detected by the watcher.
    fn handle_file_changes(&mut self, changed_paths: &[PathBuf]) {
        let mut modules_to_reload: Vec<ModuleFullPath> = Vec::new();
        for path in changed_paths {
            if let Some(module_id) = self.file_path_to_module(path) {
                if !modules_to_reload.contains(&module_id) {
                    modules_to_reload.push(module_id);
                }
            }
        }

        for module_id in &modules_to_reload {
            // Clear lock to allow retry
            self.locked_modules.remove(module_id);
            match self.reload_module(module_id) {
                Ok(true) => {
                    eprintln!("; Reloaded {}", module_id.short_name());
                }
                Ok(false) => {} // Content unchanged — no reload needed
                Err(msg) => {
                    eprintln!("; Failed to reload {}: {}", module_id.short_name(), msg);
                    self.locked_modules.insert(module_id.clone());
                }
            }
        }
    }

    /// Reload a module from its backing file. Saves state for rollback,
    /// recompiles, validates type compatibility, and commits or rolls back.
    /// Returns Ok(true) if actually reloaded, Ok(false) if content unchanged.
    fn reload_module(&mut self, module_path: &ModuleFullPath) -> Result<bool, String> {
        let mod_name = module_path.short_name().to_string();

        // Early bailout: skip reload if file content is unchanged
        if let Some(cm) = self.tc.modules.get(module_path) {
            if let (Some(file_path), Some(saved_hash)) = (&cm.file_path, &cm.content_hash) {
                if let Ok(content) = std::fs::read_to_string(file_path) {
                    if crate::cache::hash_source(&content) == *saved_hash {
                        return Ok(false);
                    }
                }
            }
        }

        // Phase A: Save state for rollback
        let old_cm = self
            .tc
            .modules
            .remove(module_path)
            .ok_or_else(|| format!("module '{}' not found", mod_name))?;

        let file_path = match &old_cm.file_path {
            Some(p) => p.clone(),
            None => {
                self.tc.modules.insert(module_path.clone(), old_cm);
                return Err(format!("module '{}' has no backing file", mod_name));
            }
        };

        let saved_got = old_cm.got_entries();

        // Save macro names for cleanup
        let old_macro_names: Vec<String> = old_cm
            .symbols
            .iter()
            .filter_map(|(name, entry)| {
                if matches!(entry, crate::module::ModuleEntry::Macro { .. }) {
                    Some(name.to_string())
                } else {
                    None
                }
            })
            .collect();
        for mname in &old_macro_names {
            self.macro_env.remove(mname);
        }

        self.loaded_modules.remove(module_path);

        // Phase B: Recompile
        let graph = match ModuleGraph::build(&file_path) {
            Ok(g) => g,
            Err(e) => {
                // Restore on failure
                self.tc.modules.insert(module_path.clone(), old_cm);
                {
                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                    if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                        cm.restore_got_entries(&saved_got);
                    }
                }
                self.loaded_modules
                    .insert(module_path.clone(), LoadedModule);
                return Err(format!("{}", e));
            }
        };

        match self.compile_module_graph(&graph, None) {
            Ok(_compiled) => {
                // Phase C: Validate type compatibility
                let new_cm = match self.tc.modules.get(module_path) {
                    Some(cm) => cm,
                    None => {
                        {
                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                    if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                        cm.restore_got_entries(&saved_got);
                    }
                }
                        self.loaded_modules
                            .insert(module_path.clone(), LoadedModule);
                        return Err("internal error: module not found after compile".to_string());
                    }
                };

                // Check exported public symbols compatibility
                let mut incompatible = Vec::new();
                for (name, old_entry) in &old_cm.symbols {
                    match old_entry {
                        crate::module::ModuleEntry::Def {
                            scheme: old_scheme,
                            visibility: Visibility::Public,
                            ..
                        } => {
                            match new_cm.get(name) {
                                Some(crate::module::ModuleEntry::Def {
                                    scheme: new_scheme, ..
                                }) => {
                                    let old_str =
                                        format::format_scheme_for_display(old_scheme);
                                    let new_str =
                                        format::format_scheme_for_display(new_scheme);
                                    if old_str != new_str {
                                        incompatible.push(format!(
                                            "{}: {} -> {}",
                                            name, old_str, new_str
                                        ));
                                    }
                                }
                                None => {
                                    incompatible.push(format!("{}: removed", name));
                                }
                                _ => {}
                            }
                        }
                        crate::module::ModuleEntry::TypeDef {
                            visibility: Visibility::Public,
                            ..
                        } => {
                            if !matches!(
                                new_cm.get(name),
                                Some(crate::module::ModuleEntry::TypeDef { .. })
                            ) {
                                incompatible.push(format!("{}: type removed", name));
                            }
                        }
                        crate::module::ModuleEntry::Constructor {
                            visibility: Visibility::Public,
                            ..
                        } => {
                            if !matches!(
                                new_cm.get(name),
                                Some(crate::module::ModuleEntry::Constructor { .. })
                            ) {
                                incompatible.push(format!("{}: constructor removed", name));
                            }
                        }
                        crate::module::ModuleEntry::TraitDecl {
                            visibility: Visibility::Public,
                            ..
                        } => {
                            if !matches!(
                                new_cm.get(name),
                                Some(crate::module::ModuleEntry::TraitDecl { .. })
                            ) {
                                incompatible.push(format!("{}: trait removed", name));
                            }
                        }
                        _ => {}
                    }
                }

                if incompatible.is_empty() {
                    // Phase D: Commit
                    self.jit.register_type_defs(&self.tc);
                    Ok(true)
                } else {
                    // Phase D: Rollback — incompatible types
                    self.tc.modules.insert(module_path.clone(), old_cm);
                    {
                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                    if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                        cm.restore_got_entries(&saved_got);
                    }
                }
                    Err(format!(
                        "incompatible type changes:\n  {}",
                        incompatible.join("\n  ")
                    ))
                }
            }
            Err(e) => {
                // Phase D: Rollback — compilation failed
                self.tc.modules.insert(module_path.clone(), old_cm);
                {
                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                    if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                        cm.restore_got_entries(&saved_got);
                    }
                }
                self.loaded_modules
                    .insert(module_path.clone(), LoadedModule);
                Err(format!("{}", e))
            }
        }
    }

    /// Handle the /reload command.
    fn cmd_reload(&mut self, arg: &str) {
        if arg.is_empty() {
            // Retry all locked modules
            let locked: Vec<ModuleFullPath> = self.locked_modules.iter().cloned().collect();
            if locked.is_empty() {
                println!("No modules need reloading");
                return;
            }
            for module_id in &locked {
                self.locked_modules.remove(module_id);
                match self.reload_module(module_id) {
                    Ok(true) => {
                        println!("; Reloaded {}", module_id.short_name());
                    }
                    Ok(false) => {
                        println!("; {} unchanged", module_id.short_name());
                    }
                    Err(msg) => {
                        eprintln!("; Failed to reload {}: {}", module_id.short_name(), msg);
                        self.locked_modules.insert(module_id.clone());
                    }
                }
            }
        } else {
            let module_id = ModuleFullPath(arg.to_string());
            self.locked_modules.remove(&module_id);
            match self.reload_module(&module_id) {
                Ok(true) => {
                    println!("; Reloaded {}", arg);
                }
                Ok(false) => {
                    println!("; {} unchanged", arg);
                }
                Err(msg) => {
                    eprintln!("; Failed to reload {}: {}", arg, msg);
                    self.locked_modules.insert(module_id);
                }
            }
        }
    }

    /// Initialize the REPL for bare mode (no entry file).
    /// Loads prelude and enters the REPL loop.
    pub fn run(&mut self) {
        self.load_prelude();

        let user_file = self.project_root.join("user.cl");
        let mut loaded_from_file = false;

        // Try to load user.cl if it exists (restores previous session)
        if user_file.exists() {
            match ModuleGraph::build(&user_file) {
                Ok(graph) => {
                    let entry_id = graph.compile_order.last().cloned().unwrap();

                    // Process platform declarations before compilation
                    for module_id in &graph.compile_order {
                        let module = &graph.modules[module_id];
                        for (name, explicit_path, span) in &module.platforms {
                            if let Err(e) = crate::batch::load_and_register_platform(
                                self,
                                name,
                                explicit_path.as_deref(),
                                *span,
                            ) {
                                eprintln!("; warning: failed to load platform: {}", e);
                            }
                        }
                    }

                    // Register platform symbols with existing linker (created during load_prelude)
                    if let Some(ref mut linker) = self.linker {
                        self.jit.register_runtime_symbols(linker);
                    }

                    match self.compile_module_graph(&graph, Some(&entry_id)) {
                        Ok(_compiled) => {
                            self.current_module = entry_id.clone();
                            self.tc.set_current_module_path(entry_id);
                            self.jit.register_type_defs(&self.tc);
                            loaded_from_file = true;
                        }
                        Err(e) => {
                            eprintln!("; warning: failed to load user.cl: {}", e);
                        }
                    }
                }
                Err(e) => {
                    eprintln!("; warning: failed to parse user.cl: {}", e);
                }
            }
        }

        // If we didn't load from file, create a fresh user module
        if !loaded_from_file {
            let mod_path = ModuleFullPath("user".to_string());
            let cm = self
                .tc
                .modules
                .entry(mod_path.clone())
                .or_insert_with(|| CompiledModule::new(mod_path.clone()));
            cm.file_path = Some(user_file);
            self.loaded_modules
                .insert(mod_path, LoadedModule);
        }
        self.tc.register_module_prefix("user");

        self.init_watcher();

        println!("cranelisp v{}", env!("CARGO_PKG_VERSION"));
        if loaded_from_file {
            println!("; Loaded user.cl. Type /help to get started");
        } else {
            println!("; Type /help to get started");
        }

        self.run_repl_loop();
    }

    /// The core REPL loop, shared by bare REPL and file-based REPL.
    fn run_repl_loop(&mut self) {
        let mut rl = DefaultEditor::new().expect("Failed to initialize line editor");
        let history_path = PathBuf::from(".cranelisp_history");
        let _ = rl.load_history(&history_path);

        let is_tty = std::io::stdin().is_terminal();
        let mut input_buf = String::new();

        loop {
            // Poll for file changes before prompting (only when not mid-input)
            if input_buf.is_empty() {
                let changed = self
                    .watcher
                    .as_mut()
                    .and_then(|w| w.poll_changes());
                if let Some(paths) = changed {
                    self.handle_file_changes(&paths);
                }
            }

            let prompt = if input_buf.is_empty() {
                format!("{}> ", self.current_module)
            } else {
                let pad = self.current_module.0.len();
                format!("{}... ", " ".repeat(pad))
            };
            // In non-TTY mode (piped input), rustyline suppresses prompts.
            // Print prompts ourselves and echo input for full transcript output.
            let line = if is_tty {
                rl.readline(&prompt)
            } else {
                print!("{}", prompt);
                std::io::Write::flush(&mut std::io::stdout()).ok();
                let result = rl.readline("");
                if let Ok(ref line) = result {
                    println!("{}", line);
                }
                result
            };
            let line = match line {
                Ok(line) => line,
                Err(ReadlineError::Interrupted) => {
                    input_buf.clear();
                    continue;
                }
                Err(ReadlineError::Eof) => break,
                Err(_) => break,
            };
            input_buf.push_str(&line);
            input_buf.push('\n');

            if !parens_balanced(&input_buf) {
                continue;
            }

            let input = input_buf.trim().to_string();
            input_buf.clear();

            if input.is_empty() {
                continue;
            }

            let _ = rl.add_history_entry(&input);

            // Check for colon commands
            if let Some(cmd) = parse_repl_command(&input) {
                if self.handle_command(cmd, &input) {
                    break;
                }
                continue;
            }

            // Parse: two-phase for pipeline visibility
            let sexps = match parse_sexps(&input) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("{}", crate::error::format_error(&input, &e));
                    continue;
                }
            };

            // Block definition forms for locked modules
            if self.locked_modules.contains(&self.current_module) {
                let is_def_form = is_defmacro(&sexps[0])
                    || sexps.iter().any(|s| {
                        if let crate::sexp::Sexp::List(children, _) = s {
                            if let Some(crate::sexp::Sexp::Symbol(head, _)) = children.first() {
                                return matches!(
                                    head.as_str(),
                                    "defn" | "deftype" | "deftrait" | "impl" | "defmacro"
                                        | "import" | "mod"
                                );
                            }
                        }
                        false
                    });
                if is_def_form {
                    eprintln!(
                        "; Module '{}' is locked — file has errors. Fix the file or /reload",
                        self.current_module.short_name()
                    );
                    continue;
                }
            }

            // Intercept defmacro: compile and register, don't pass to AST builder
            if sexps.len() == 1 && is_defmacro(&sexps[0]) {
                let info = match parse_defmacro(&sexps[0]) {
                    Ok(i) => i,
                    Err(e) => {
                        eprintln!("{}", crate::error::format_error(&input, &e));
                        continue;
                    }
                };
                let name = info.name.clone();
                let docstring = info.docstring.clone();
                let fixed_params = info.fixed_params.clone();
                let rest_param = info.rest_param.clone();
                let visibility = info.visibility;
                let body_sexp = Some(info.body_sexp.clone());
                match compile_macro(&mut self.tc, &mut self.jit, &info, Some(&self.macro_env)) {
                    Ok(ptr) => {
                        self.tc.register_macro_in_module(
                            &name,
                            fixed_params.clone(),
                            rest_param.clone(),
                            docstring.clone(),
                            visibility,
                            Some(sexps[0].clone()),
                            Some(input.trim().to_string()),
                        );
                        self.macro_env.register(
                            name.clone(),
                            ptr,
                            docstring,
                            fixed_params,
                            rest_param,
                            body_sexp,
                        );
                        if let Some(sym_info) = self.tc.describe_symbol(&name) {
                            println!("{}", format_symbol_info(&name, &sym_info));
                        }
                        self.save_current_module();
                    }
                    Err(e) => {
                        eprintln!("{}", crate::error::format_error(&input, &e));
                    }
                }
                continue;
            }

            // Intercept (import ...): load modules and install names
            if sexps.len() == 1 {
                if let crate::sexp::Sexp::List(ref children, _) = sexps[0] {
                    if !children.is_empty() {
                        if let crate::sexp::Sexp::Symbol(ref head, _) = children[0] {
                            if head == "import" {
                                self.handle_repl_import(&sexps[0]);
                                continue;
                            }
                        }
                    }
                }
            }

            // Intercept (mod ...): declare child module
            if sexps.len() == 1 {
                if let crate::sexp::Sexp::List(ref children, _) = sexps[0] {
                    if children.len() == 2 {
                        if let crate::sexp::Sexp::Symbol(ref head, _) = children[0] {
                            if head == "mod" {
                                if let crate::sexp::Sexp::Symbol(ref mod_name, _) = children[1] {
                                    self.handle_repl_mod(mod_name);
                                    continue;
                                }
                            }
                        }
                    }
                }
            }

            // Intercept (platform name) or (platform name "path"): load platform DLL
            if sexps.len() == 1 {
                if let crate::sexp::Sexp::List(ref children, _) = sexps[0] {
                    if children.len() >= 2 && children.len() <= 3 {
                        if let crate::sexp::Sexp::Symbol(ref head, _) = children[0] {
                            if head == "platform" {
                                if let crate::sexp::Sexp::Symbol(ref name, span) = children[1] {
                                    let explicit_path = children.get(2).and_then(|c| {
                                        if let crate::sexp::Sexp::Str(p, _) = c {
                                            Some(p.as_str())
                                        } else {
                                            None
                                        }
                                    });
                                    self.handle_repl_platform(name, explicit_path, span);
                                    continue;
                                }
                            }
                        }
                    }
                }
            }

            // Macro-expand sexps before AST building
            let sexps = if !self.macro_env.is_empty() {
                match sexps
                    .into_iter()
                    .map(|s| expand_sexp(s, &self.macro_env, 0))
                    .collect::<Result<Vec<_>, _>>()
                {
                    Ok(expanded) => expanded,
                    Err(e) => {
                        eprintln!("{}", crate::error::format_error(&input, &e));
                        continue;
                    }
                }
            } else {
                sexps
            };

            // Flatten begin forms from macro expansion results
            let sexps: Vec<_> = sexps.into_iter().flat_map(flatten_begin).collect();

            // Process defmacro-in-results: compile/register any defmacro forms produced by expansion
            let mut had_defmacro = false;
            let mut had_error = false;
            for form in &sexps {
                if is_defmacro(form) {
                    had_defmacro = true;
                    let info = match parse_defmacro(form) {
                        Ok(i) => i,
                        Err(e) => {
                            eprintln!("{}", crate::error::format_error(&input, &e));
                            had_error = true;
                            break;
                        }
                    };
                    let name = info.name.clone();
                    let docstring = info.docstring.clone();
                    let fixed_params = info.fixed_params.clone();
                    let rest_param = info.rest_param.clone();
                    let visibility = info.visibility;
                    let body_sexp = Some(info.body_sexp.clone());
                    match compile_macro(&mut self.tc, &mut self.jit, &info, Some(&self.macro_env)) {
                        Ok(ptr) => {
                            self.tc.register_macro_in_module(
                                &name,
                                fixed_params.clone(),
                                rest_param.clone(),
                                docstring.clone(),
                                visibility,
                                Some(form.clone()),
                                Some(form.to_string()),
                            );
                            self.macro_env.register(
                                name.clone(),
                                ptr,
                                docstring,
                                fixed_params,
                                rest_param,
                                body_sexp,
                            );
                            if let Some(sym_info) = self.tc.describe_symbol(&name) {
                                println!("{}", format_symbol_info(&name, &sym_info));
                            }
                        }
                        Err(e) => {
                            eprintln!("{}", crate::error::format_error(&input, &e));
                            had_error = true;
                            break;
                        }
                    }
                }
            }
            if had_error {
                continue;
            }

            // Filter out defmacro forms, process remaining
            let sexps: Vec<_> = sexps.into_iter().filter(|s| !is_defmacro(s)).collect();
            if sexps.is_empty() {
                if had_defmacro {
                    self.save_current_module();
                }
                continue;
            }

            let repl_input = match build_repl_input_from_sexps(&sexps) {
                Ok(ri) => ri,
                Err(e) => {
                    eprintln!("{}", crate::error::format_error(&input, &e));
                    continue;
                }
            };

            // Auto-load modules referenced by qualified names (e.g. util/helper)
            self.auto_load_qualified_refs(&sexps);

            // For REPL input, there's always exactly one top-level sexp
            // (build_repl_input_from_sexps handles multi-sexp annotation cases)
            let sexp = &sexps[0];
            self.handle_input(repl_input, &input, sexp);
            if had_defmacro {
                self.save_current_module();
            }
        }

        let _ = rl.append_history(&history_path);
    }
}

/// Launch the bare REPL (no entry file, project_root = CWD).
pub fn run() {
    match ReplSession::new() {
        Ok(mut session) => session.run(),
        Err(e) => {
            eprintln!("Failed to initialize REPL: {}", e);
            std::process::exit(1);
        }
    }
}

/// Launch a bare-style REPL rooted at the given directory.
/// Creates `user.cl` inside the directory if needed.
pub fn run_with_dir(dir: &Path) {
    let project_root = match dir.canonicalize() {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Error: cannot resolve directory '{}': {}", dir.display(), e);
            std::process::exit(1);
        }
    };
    match ReplSession::with_project_root(project_root) {
        Ok(mut session) => session.run(),
        Err(e) => {
            eprintln!("Failed to initialize REPL: {}", e);
            std::process::exit(1);
        }
    }
}

/// Launch the REPL with an entry file.
/// Compiles the file and its dependencies, then enters the REPL
/// in the entry module's context.
pub fn run_with_file(path: &Path) {
    let path = match path.canonicalize() {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Error: cannot resolve path '{}': {}", path.display(), e);
            std::process::exit(1);
        }
    };
    let project_root = path
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .to_path_buf();

    // Build the module graph from the entry file.
    // The implicit prelude import handles prelude discovery automatically.
    let graph = match ModuleGraph::build(&path) {
        Ok(g) => g,
        Err(e) => {
            let source = std::fs::read_to_string(&path).unwrap_or_default();
            eprintln!("{}", crate::error::format_error(&source, &e));
            std::process::exit(1);
        }
    };

    let entry_id = graph.compile_order.last().cloned().unwrap();

    let mut session = match ReplSession::with_project_root(project_root) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Failed to initialize REPL: {}", e);
            std::process::exit(1);
        }
    };

    // Process platform declarations from ALL modules before compilation
    for module_id in &graph.compile_order {
        let module = &graph.modules[module_id];
        for (name, explicit_path, span) in &module.platforms {
            if let Err(e) = crate::batch::load_and_register_platform(
                &mut session,
                name,
                explicit_path.as_deref(),
                *span,
            ) {
                let source = std::fs::read_to_string(&path).unwrap_or_default();
                eprintln!("{}", crate::error::format_error(&source, &e));
                std::process::exit(1);
            }
        }
    }

    match session.compile_module_graph(&graph, Some(&entry_id)) {
        Ok(compiled) => {
            for module_id in &compiled {
                let name = module_id.short_name();
                if name == "prelude" || name == "core" {
                    session.prelude_module_ids.insert(module_id.clone());
                }
            }
        }
        Err(e) => {
            let source = std::fs::read_to_string(&path).unwrap_or_default();
            eprintln!("{}", crate::error::format_error(&source, &e));
            std::process::exit(1);
        }
    }

    // Set current module to the entry module
    session.current_module = entry_id.clone();
    session.tc.set_current_module_path(entry_id);

    // Re-register type defs for JIT display
    session.jit.register_type_defs(&session.tc);

    session.init_watcher();

    println!("cranelisp v{}", env!("CARGO_PKG_VERSION"));
    println!(
        "; Loaded {}. Type /help to get started",
        path.file_name().unwrap_or_default().to_string_lossy()
    );

    session.run_repl_loop();
}
