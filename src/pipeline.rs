// Pipeline: compile_unit (method on CompilationSession) + codegen + stage helpers.
//
// `compile_unit()` is the single entry point for all compilation:
// batch programs, REPL forms, and module loading all flow through
// the same stages with the same types. Mode differences are expressed
// via `CompileContext` parameters.
//
// Stages:
//   1. Parse:       &str -> Vec<Sexp>
//   2a. Extract:    Vec<Sexp> -> (ModuleStructure, Vec<Sexp>)
//   2b. Auto-prelude trigger (recursive compile_unit for prelude if needed)
//   2c. Recursive module loading for unresolved imports + exports
//   2d. (unused — reserved)
//   2e. Prelude import injection + register imports/exports
//   2f. Load platform DLLs from module declarations
//   3. Expand:      Vec<Sexp> -> Vec<Sexp>  (defmacro interception + macro expansion)
//   4. Build AST:   Vec<Sexp> -> Vec<TopLevel>
//   4b. Bind chain analysis (auto IO scheduling)
//   5. Typecheck:   Vec<TopLevel> -> CheckResult  (unified multi-pass)
//   6. Codegen:     TopLevel + CheckResult -> JIT (mode-dependent)
//   7. Execute:     call entry fn -> i64          (mode-dependent)

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use cranelisp_types::{
    CheckResult, CodegenBehaviour, CompileContext, CranelispError, Defn, ModuleFullPath,
    ModuleStrategy, ModuleStructure, Program, Span, Symbol, Type, Warning,
};

use cranelisp_backend::cache;

use crate::session::{CompilationSession, CacheConfig, FormResult, InMemWorkerState, ObjectWorkerState};

// ---------------------------------------------------------------------------
// Result types
// ---------------------------------------------------------------------------

/// Result of compiling a unit through stages 1-5 of the pipeline.
///
/// Contains the typechecked program and module structure, ready for
/// codegen via `codegen_and_execute()`. Does NOT contain execution
/// results — those come from `CodegenResult`.
pub struct CompileUnitResult {
    /// The built program (Vec<TopLevel>) from stage 4.
    pub program: Vec<cranelisp_types::TopLevel>,

    /// Module structure extracted at stage 2 (imports, exports, submodules).
    pub module_structure: ModuleStructure,

    /// The typecheck result (method resolutions, expr_types, display info, etc.).
    /// Needed by callers for display formatting and introspection.
    pub check_result: CheckResult,

    /// Source text that was compiled. Needed by `codegen_and_execute()`
    /// for background cache writes.
    pub source: String,

    /// All warnings accumulated during stages 1-5.
    pub warnings: Vec<Warning>,
}

/// Result of codegen + execution (stages 6-7).
///
/// Produced by `codegen_and_execute()` after compiling and optionally
/// executing the program from a `CompileUnitResult`.
pub struct CodegenResult {
    /// If execution occurred, the raw i64 result value.
    /// None when the unit was a module load (no execution) or contained
    /// only type/trait definitions with no entry point.
    pub value: Option<i64>,

    /// Inferred type of the executed expression or entry function's return.
    /// None when no execution occurred.
    pub result_type: Option<Type>,

    /// Warnings accumulated during codegen.
    pub warnings: Vec<Warning>,
}

/// An item queued for codegen (stages 6-7).
///
/// Captures everything needed to call `codegen_and_execute()` for a single
/// compilation unit. Callers push items to the session's `inmem_queue` or
/// `object_queue`, then call the corresponding flush method.
pub struct CodegenItem {
    /// The compile context (module, codegen behaviour).
    pub ctx: CompileContext,
    /// The stages 1-5 result, ready for codegen.
    pub unit_result: CompileUnitResult,
}

/// Everything codegen needs, extracted from CompilationSession at the call site.
///
/// Must be Send so it can move to the codegen worker thread (Step 11 async mode).
/// The symbol_table is pre-cloned from the TypeChecker because tc is not Send.
pub struct CodegenPacket {
    /// The compile context (module, codegen behaviour).
    pub ctx: CompileContext,
    /// The stages 1-5 result, ready for codegen.
    pub unit_result: CompileUnitResult,
    /// Whether to use GOT-indirect calls (interactive/REPL mode).
    pub interactive: bool,
    /// Platform function pointers for JIT symbol registration.
    pub platform_symbols: Vec<(String, *const u8)>,
    /// Pre-cloned symbol table for the module (used by cache writes).
    /// Cloned from tc at the call site because tc is not Send.
    pub symbol_table: cranelisp_types::SymbolTable,
    /// Pre-assigned GOT slot indices for this module's definitions.
    /// Snapshot of all known GOT slots at the time of enqueue, including
    /// slots for this module's defns and all previously compiled modules.
    /// Workers use this to build the got_slots map for compilation.
    pub got_slot_map: HashMap<Symbol, usize>,
    /// Function arities for all known definitions at the time of enqueue.
    /// Workers use this to build func_arities for compilation.
    pub func_arities: HashMap<Symbol, usize>,
    /// Shared GOT table for atomic code pointer writes.
    /// Workers write to pre-assigned slots via `store(Release)`.
    /// None in sync mode (workers use InMemWorkerState directly).
    pub shared_got: Option<std::sync::Arc<cranelisp_backend::got::GotTable>>,
    /// Shared ISA for creating Jit instances without re-probing CPU features.
    /// None in sync mode (workers call Jit::new()).
    pub shared_isa: Option<std::sync::Arc<dyn cranelisp_backend::TargetIsa>>,
}

// SAFETY: CodegenPacket contains raw *const u8 pointers (in platform_symbols)
// that are function pointers into loaded DLLs. These pointers are valid for
// the process lifetime and are only read (never written) by the codegen path.
unsafe impl Send for CodegenPacket {}

/// Construct an empty `CheckResult` for modules with no compilable forms.
fn empty_check_result() -> CheckResult {
    CheckResult {
        method_resolutions: Default::default(),
        constrained_fn_names: Default::default(),
        mono_defns: Vec::new(),
        expr_types: Default::default(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
        type_defs: Default::default(),
        constructor_to_type: Default::default(),
        display: None,
    }
}

// ---------------------------------------------------------------------------
// compile_unit: method on CompilationSession
// ---------------------------------------------------------------------------

impl CompilationSession {
    /// Compile a unit of source through the unified pipeline (stages 1-5).
    ///
    /// Takes source text (`&str`) and a `CompileContext` that specifies the
    /// target module and codegen behaviour. `ModuleStrategy` controls how
    /// definitions integrate with existing module state.
    ///
    /// # Pipeline stages
    ///
    /// 1. **Parse** — `cranelisp_frontend::parse(source)` → `Vec<Sexp>`
    /// 2. **Extract** — `extract_module_declarations()` → `(ModuleStructure, Vec<Sexp>)`.
    ///    Registers imports/exports. Imports of uncompiled modules trigger
    ///    recursive `compile_unit()` calls via `session.lib_dirs`.
    /// 3. **Expand** — `process_forms_sequentially()`: defmacro interception,
    ///    macro expansion, begin-flattening → `Vec<Sexp>`
    /// 4. **Build AST** — `build_program()` → `Vec<TopLevel>`
    /// 4b. **Bind chain analysis** — auto IO scheduling between build and typecheck
    /// 5. **Typecheck** — `TypeChecker::check()` → `CheckResult`
    ///
    /// # Errors
    ///
    /// Returns `CranelispError` for parse, type, or codegen errors.
    /// Non-fatal diagnostics are accumulated in `CompileUnitResult::warnings`.
    pub fn compile_unit(
        &mut self,
        source: &str,
        ctx: &CompileContext,
        strategy: ModuleStrategy,
    ) -> Result<CompileUnitResult, CranelispError> {
        // Cycle detection: check if this module is already on the compile stack.
        check_cycle(self, &ctx.module)?;
        self.compile_stack.push(ctx.module.clone());

        let result = compile_unit_inner(self, source, ctx, strategy);

        // Always pop the compile stack, even on error.
        self.compile_stack.pop();

        result
    }
}

/// Inner implementation of `compile_unit()`, separated so the compile_stack
/// pop happens in the outer function regardless of success/failure.
fn compile_unit_inner(
    session: &mut CompilationSession,
    source: &str,
    ctx: &CompileContext,
    strategy: ModuleStrategy,
) -> Result<CompileUnitResult, CranelispError> {
    // Stage 1: Parse source text into sexps.
    let sexps = cranelisp_frontend::parse(source)?;

    // Stage 2: Extract module declarations (mod, import, export, platform).
    let (structure, remaining) = cranelisp_frontend::extract_module_declarations(
        ctx.module.clone(),
        None,
        sexps,
    )?;

    // Stage 2a-post: Register file→module mapping for the current module.
    if let Some(resolved) = resolve_module_path(&ctx.module, &session.lib_dirs) {
        if let Ok(canonical) = resolved.canonicalize() {
            session.module_deps.register_file(canonical, ctx.module.clone());
        }
    }

    // Stage 2b: Auto-load prelude if needed.
    let prelude_path = ModuleFullPath::from("prelude");
    let needs_prelude = !session.tc.has_module(&prelude_path)
        && ctx.module != prelude_path
        && !session.compile_stack.contains(&prelude_path)
        && !session.lib_dirs.is_empty();
    if let Some(prelude_file) =
        needs_prelude.then(|| crate::session::resolve_prelude(&session.project_root, &session.lib_dirs)).flatten()
    {
        // Try cache-hit for prelude before compiling from source.
        let prelude_cached = try_cache_hit_load(session, &prelude_path, &prelude_file);

        if !prelude_cached {
            let prelude_source = std::fs::read_to_string(&prelude_file).map_err(|e| {
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
            let prelude_ctx = CompileContext {
                module: ModuleFullPath::from("prelude"),
                codegen: ctx.codegen, // inherit caller's codegen behaviour
            };
            let prelude_result = session.compile_unit(&prelude_source, &prelude_ctx, ModuleStrategy::Replace)?;
            codegen_and_execute_via_session(session, &prelude_result, &prelude_ctx)?;
        }

        // Register prelude dependency edge for the current module.
        session.module_deps.register_edge(&ctx.module, &prelude_path);
    }

    // Stage 2c: Recursive module loading for unresolved imports and exports.
    load_dependencies(session, &structure, ctx.codegen)?;

    // Stage 2e: Prelude import injection + register imports/exports.
    session.tc.set_current_module(ctx.module.clone());

    if session.tc.has_module(&prelude_path) && ctx.module != prelude_path {
        crate::session::inject_prelude_import(&mut session.tc)?;
    }
    if !structure.import_specs.is_empty() {
        session.tc.register_imports(&structure.import_specs)?;
    }
    if !structure.export_specs.is_empty() {
        session.tc.register_exports(&structure.export_specs)?;
    }

    // Stage 2f: Load platform DLLs declared in this module.
    for platform_spec in &structure.platform_specs {
        let (platform, jit_syms) = crate::platform::load_and_register_platform(
            &mut session.tc,
            &platform_spec.name,
            &session.project_root,
            platform_spec.span,
        )?;
        for desc in &platform.descriptors {
            session.scheduling_registry.insert(
                Symbol::from(desc.name.as_str()),
                desc.scheduling_class,
            );
        }
        session.platform_symbols.extend(jit_syms);
        session.loaded_platforms.push(platform);
    }

    // Stage 3: Expand (defmacro interception + macro expansion + begin-flatten).
    let accumulated = session.process_forms_sequentially(remaining)?;

    // Handle empty programs (type/trait-only modules with no remaining forms
    // after extraction and expansion).
    if accumulated.is_empty() {
        return Ok(CompileUnitResult {
            program: Vec::new(),
            module_structure: structure,
            check_result: empty_check_result(),
            source: source.to_string(),
            warnings: Vec::new(),
        });
    }

    // Stage 4: Build AST from expanded sexps.
    let mut program = cranelisp_frontend::build_program(&accumulated)?;

    // Stage 4b: Bind chain analysis (auto IO scheduling).
    // Build a temporary PlatformRegistry from the old scheduling_registry
    // for the old compile_unit path. Step 15 deletes this path entirely.
    if !session.scheduling_registry.is_empty()
        && std::env::var("CRANELISP_NO_IO_SCHEDULE").is_err()
    {
        let temp_registry = {
            let mut reg = crate::platform_registry::PlatformRegistry::new();
            for (sym, sc) in &session.scheduling_registry {
                let fq = cranelisp_types::FQSymbol {
                    module: cranelisp_types::ModuleFullPath::from("platform._compat"),
                    symbol: sym.clone(),
                };
                reg.register(fq, crate::platform_registry::PlatformFunction {
                    jit_name: cranelisp_types::JitSymbol::from(""),
                    fn_ptr: std::ptr::null(),
                    scheduling_class: *sc,
                });
            }
            reg
        };
        crate::session::apply_bind_chain_analysis(&mut program, &temp_registry);
    }

    // Stage 5: Unified multi-pass typecheck.
    let check_strategy = if strategy == ModuleStrategy::Replace {
        ModuleStrategy::Additive
    } else {
        strategy
    };
    let check_result = session.tc.check(&program, ctx, check_strategy)?;

    let all_warnings: Vec<Warning> = check_result.warnings.clone();

    Ok(CompileUnitResult {
        program,
        module_structure: structure,
        check_result,
        source: source.to_string(),
        warnings: all_warnings,
    })
}

// ---------------------------------------------------------------------------
// Cycle detection
// ---------------------------------------------------------------------------

/// Check if a module is already on the compile stack (circular dependency).
fn check_cycle(
    session: &CompilationSession,
    module: &ModuleFullPath,
) -> Result<(), CranelispError> {
    if session.compile_stack.contains(module) {
        let cycle: Vec<String> = session
            .compile_stack
            .iter()
            .map(|m| m.to_string())
            .collect();
        return Err(CranelispError::ModuleError {
            message: format!(
                "circular dependency detected: {} -> {}",
                cycle.join(" -> "),
                module
            ),
            file: None,
            span: Span::SYNTHETIC,
        });
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Recursive module loading
// ---------------------------------------------------------------------------

/// Load all uncompiled dependencies for a module's imports and exports.
fn load_dependencies(
    session: &mut CompilationSession,
    structure: &ModuleStructure,
    codegen: CodegenBehaviour,
) -> Result<(), CranelispError> {
    let dep_modules: Vec<ModuleFullPath> = structure
        .import_specs
        .iter()
        .map(|s| s.module_path.clone())
        .chain(structure.export_specs.iter().map(|s| s.module_path.clone()))
        .collect();

    let parent_module = &structure.path;

    for dep_module in &dep_modules {
        session.module_deps.register_edge(parent_module, dep_module);

        // 1. Already loaded — skip.
        if session.tc.has_module(dep_module) {
            continue;
        }

        if let Some(dep_source_path) = resolve_module_path(dep_module, &session.lib_dirs) {
            if let Ok(canonical) = dep_source_path.canonicalize() {
                session.module_deps.register_file(canonical, dep_module.clone());
            }

            // 2. Cache hit — restore from cache, skip compile_unit.
            if try_cache_hit_load(session, dep_module, &dep_source_path) {
                continue;
            }

            // 3. Cache miss — compile from source.
            let dep_source =
                std::fs::read_to_string(&dep_source_path).map_err(|e| {
                    CranelispError::ModuleError {
                        message: format!(
                            "cannot read '{}': {}",
                            dep_source_path.display(),
                            e
                        ),
                        file: Some(dep_source_path.clone()),
                        span: Span::SYNTHETIC,
                    }
                })?;

            let dep_ctx = CompileContext {
                module: dep_module.clone(),
                codegen,
            };

            let unit_result = session.compile_unit(&dep_source, &dep_ctx, ModuleStrategy::Replace)?;
            session.send_codegen(unit_result, dep_ctx);
        }
    }
    session.flush_codegen()?;
    Ok(())
}

/// Resolve a dotted module path to a filesystem path.
fn resolve_module_path(
    module: &ModuleFullPath,
    lib_dirs: &[PathBuf],
) -> Option<PathBuf> {
    let relative = format!("{}.cl", module.as_ref().replace('.', "/"));

    for dir in lib_dirs {
        let candidate = dir.join(&relative);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

/// Public alias for use by callers that need to resolve module files
/// outside of compile_unit() (e.g., try_restore_user_module).
pub fn resolve_module_file(
    module: &ModuleFullPath,
    lib_dirs: &[PathBuf],
) -> Option<PathBuf> {
    resolve_module_path(module, lib_dirs)
}

// ---------------------------------------------------------------------------
// Cache-hit loading (pipeline-v3.md §3.4.1)
// ---------------------------------------------------------------------------

/// Attempt to load a dependency module from cache, skipping compile_unit.
///
/// Checks the cache manifest for validity (source hash + dep hashes),
/// loads `.meta.json` and `.o` from disk, restores the symbol table
/// into the TypeChecker, and wires code pointers into the GOT.
///
/// Returns `true` if the module was successfully loaded from cache
/// (caller should skip compile_unit). Returns `false` on cache miss.
fn try_cache_hit_load(
    session: &mut CompilationSession,
    dep_module: &ModuleFullPath,
    dep_source_path: &Path,
) -> bool {
    // Check if caching is enabled.
    let cache_dir = match session.object_worker.cache_state.as_ref() {
        Some(cs) => cs.cache_dir().to_path_buf(),
        None => return false,
    };

    // Read the source to compute its hash.
    let dep_source = match std::fs::read_to_string(dep_source_path) {
        Ok(s) => s,
        Err(_) => return false,
    };
    let source_hash = cache::hash_source(&dep_source);

    // Collect current dependency hashes from the session's cache state.
    // For cache validity, we need the hashes of this module's own deps.
    // Since we don't know them yet (we haven't parsed this module),
    // we pass empty and rely on source hash only for now.
    // This is the "start with source hash" approach per the task spec.
    let dep_hashes: HashMap<ModuleFullPath, String> = HashMap::new();

    let is_valid = match session.object_worker.cache_state.as_ref() {
        Some(cs) => cs.is_cache_valid(dep_module, &source_hash, &dep_hashes),
        None => return false,
    };
    if !is_valid {
        return false;
    }

    // Try to load the cached module metadata from disk.
    let cached = match cache::try_load_cached_module(&cache_dir, dep_module) {
        Ok(Some(c)) => c,
        _ => return false,
    };

    // The .o file must exist for a full cache hit (code loading).
    if !cached.has_object {
        return false;
    }

    // Load the .o file via the Linker to get executable code pointers.
    // The Linker must be kept alive — it owns the mmap'd executable memory.
    let (linker, fn_addrs) = match load_cached_object_via_linker(
        &mut session.inmem_worker,
        &session.platform_symbols,
        &cached,
    ) {
        Ok(result) => result,
        Err(_) => return false,
    };

    // Store the Linker to keep its executable memory alive.
    session.inmem_worker.cache_linkers.push(linker);

    // Restore the symbol table into the TypeChecker.
    let symbol_table = cached.metadata.symbol_table.clone();
    session.tc.restore_cached_module(symbol_table);

    // Restore trait impl registrations from cached codegen state.
    let mangled_names: Vec<String> = cached.codegen_state().got_slots
        .keys()
        .map(|s| s.as_ref().to_string())
        .collect();
    session.tc.restore_cached_impls(&mangled_names);

    // Wire code pointers into the GOT.
    wire_cached_code_into_got(
        &mut session.inmem_worker,
        &cached,
        &fn_addrs,
    );

    // Register module aliases (qualified names) for the loaded module.
    crate::session::register_module_aliases_filtered(
        &mut session.inmem_worker,
        dep_module,
        None,
    );

    // Record the source hash so downstream modules can check deps.
    if let Some(cs) = session.object_worker.cache_state.as_mut() {
        cs.record_cache_hit(dep_module, source_hash);
    }

    true
}

/// Load a cached .o file via the Linker, returning the Linker (which owns
/// executable memory) and function name → code pointer map.
///
/// Creates a Linker, registers all intrinsics and previously-compiled
/// module code pointers as external symbols, then loads the .o file.
/// The Linker must be kept alive for as long as the code pointers are used
/// (its code_regions hold the mmap'd executable memory).
fn load_cached_object_via_linker(
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    cached: &cache::CachedModule,
) -> Result<(cache::Linker, HashMap<String, *const u8>), CranelispError> {
    let mut linker = cache::Linker::new()?;

    // Register runtime intrinsics.
    for sym in cranelisp_backend::jit::intrinsic_symbols() {
        linker.register_symbol(sym.name, sym.ptr);
    }

    // Register platform symbols.
    for (name, ptr) in platform_symbols {
        linker.register_symbol(name, *ptr);
    }

    // Register code pointers from already-compiled modules.
    // These are available via the GOT's def_codegen map.
    for (name, dc) in &inmem_worker.got_state.def_codegen {
        if let Some(ptr) = dc.code_ptr {
            linker.register_symbol(name.as_ref(), ptr);
        }
    }

    // Register the GOT base address so .o code can find it.
    let got_base = inmem_worker.got_state.got_base_ptr();
    if !got_base.is_null() {
        linker.register_symbol("__got_base", got_base);
    }

    let fn_addrs = cache::load_cached_object(&mut linker, cached)?;
    Ok((linker, fn_addrs))
}

/// Wire code pointers from a Linker-loaded .o into the GOT.
///
/// For each function in the cached module's GOT slot map, allocates
/// a GOT slot, stores the code pointer, and registers a DefCodegen entry.
fn wire_cached_code_into_got(
    inmem_worker: &mut InMemWorkerState,
    cached: &cache::CachedModule,
    fn_addrs: &HashMap<String, *const u8>,
) {
    for (name, _old_slot) in &cached.codegen_state().got_slots {
        let code_ptr = fn_addrs.get(name.as_ref()).copied();

        // Allocate a new GOT slot (slot indices from cache may differ).
        let slot = match inmem_worker.got_state.allocate_slot() {
            Ok(s) => s,
            Err(_) => continue, // GOT full — skip this function.
        };

        // Write the code pointer to the GOT slot.
        if let Some(ptr) = code_ptr {
            inmem_worker.got_state.update_slot(slot, ptr);
        }

        // Register the DefCodegen entry.
        let dc = inmem_worker.got_state.def_codegen
            .entry(name.clone())
            .or_default();
        dc.got_slot = Some(slot);
        dc.code_ptr = code_ptr;

        // Restore param_count from cached def entries if available.
        if let Some(def_entry) = cached.codegen_state().def_entries.get(name) {
            dc.param_count = def_entry.param_count;
        }
    }
}

// ---------------------------------------------------------------------------
// Codegen + execute (stages 6-7)
// ---------------------------------------------------------------------------

/// Execute codegen via a pre-built `CodegenPacket`.
pub fn codegen_and_execute(
    inmem_worker: &mut InMemWorkerState,
    object_worker: &mut ObjectWorkerState,
    packet: &CodegenPacket,
) -> Result<CodegenResult, CranelispError> {
    codegen_and_execute_decomposed(
        inmem_worker,
        object_worker,
        &packet.platform_symbols,
        packet.interactive,
        &packet.symbol_table,
        &packet.unit_result,
        &packet.ctx,
    )
}

/// Convenience wrapper: call `codegen_and_execute` using session fields.
pub fn codegen_and_execute_via_session(
    session: &mut CompilationSession,
    unit_result: &CompileUnitResult,
    ctx: &CompileContext,
) -> Result<CodegenResult, CranelispError> {
    let symbol_table = session.tc.module_table_cloned(&ctx.module)
        .unwrap_or_else(|| cranelisp_types::SymbolTable::new(ctx.module.clone()));

    codegen_and_execute_decomposed(
        &mut session.inmem_worker,
        &mut session.object_worker,
        &session.platform_symbols,
        session.interactive,
        &symbol_table,
        unit_result,
        ctx,
    )
}

/// Execute codegen using decomposed session fields (no packet cloning).
fn codegen_and_execute_decomposed(
    inmem_worker: &mut InMemWorkerState,
    object_worker: &mut ObjectWorkerState,
    platform_symbols: &[(String, *const u8)],
    interactive: bool,
    symbol_table: &cranelisp_types::SymbolTable,
    unit_result: &CompileUnitResult,
    ctx: &CompileContext,
) -> Result<CodegenResult, CranelispError> {
    // Early return for empty programs (no codegen needed).
    if unit_result.program.is_empty() {
        return Ok(CodegenResult {
            value: None,
            result_type: None,
            warnings: Vec::new(),
        });
    }

    // Snapshot pre-existing GOT entries so that register_module_aliases
    // only aliases new entries from this module.
    let pre_existing: std::collections::HashSet<Symbol> = inmem_worker
        .got_state
        .def_codegen
        .keys()
        .cloned()
        .collect();

    let mut codegen_warnings: Vec<Warning> = Vec::new();

    // Stages 6-7: Codegen and execute.
    let (value, result_type) = if interactive {
        compile_and_execute_interactive(
            inmem_worker,
            platform_symbols,
            &unit_result.program,
            &unit_result.check_result,
            &mut codegen_warnings,
        )?
    } else {
        compile_and_execute_batch(
            &unit_result.program,
            &unit_result.check_result,
            &mut codegen_warnings,
        )?
    };

    // Register module aliases after successful interactive-mode compilation.
    if interactive {
        crate::session::register_module_aliases_filtered(
            inmem_worker,
            &ctx.module,
            Some(&pre_existing),
        );
    }

    // Stage 6b: Background .o + .meta.json write (InMemoryAndObject only).
    if ctx.codegen == CodegenBehaviour::InMemoryAndObject {
        queue_background_cache_write(
            object_worker,
            symbol_table,
            &unit_result.source,
            &ctx.module,
            &unit_result.module_structure,
            &unit_result.program,
            &unit_result.check_result,
        );
    }

    // Record module structure for --link (both targets).
    object_worker
        .compiled_module_structures
        .push((ctx.module.clone(), unit_result.module_structure.clone()));

    // Accumulate cross-module func_sigs from this module's definitions.
    accumulate_func_sigs_from_program(
        &ctx.module,
        &unit_result.program,
        &unit_result.check_result,
        &mut object_worker.cross_module_func_sigs,
    );

    Ok(CodegenResult {
        value,
        result_type,
        warnings: codegen_warnings,
    })
}

// ---------------------------------------------------------------------------
// Batch mode: whole-program codegen with direct calls
// ---------------------------------------------------------------------------

fn compile_and_execute_batch(
    program: &Program,
    check: &CheckResult,
    warnings: &mut Vec<Warning>,
) -> Result<(Option<i64>, Option<Type>), CranelispError> {
    let compiled = cranelisp_backend::compile_program(program, check, false)?;
    warnings.extend(compiled.warnings.iter().cloned());

    let result_type = infer_batch_result_type(program, check);

    // SAFETY: compiled code was just generated and finalized by our JIT.
    let value = unsafe { compiled.execute()? };

    Ok((Some(value), Some(result_type)))
}

// ---------------------------------------------------------------------------
// Interactive mode: GOT-indirect per-defn compilation
// ---------------------------------------------------------------------------

fn compile_and_execute_interactive(
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    program: &Program,
    check: &CheckResult,
    warnings: &mut Vec<Warning>,
) -> Result<(Option<i64>, Option<Type>), CranelispError> {
    use cranelisp_types::TopLevel;

    let has_expr = program.iter().any(|tl| matches!(tl, TopLevel::Expr(_)));

    // Clear any stale runtime error before executing JIT code.
    let _ = cranelisp_runtime::panic::take_runtime_error();

    // Compile definitions first (GOT registration, mono defns, etc.).
    let form_result = compile_checked_program(inmem_worker, platform_symbols, program, check)?;

    // Check for runtime panics (e.g., checked division by zero in zero-arg defns).
    check_runtime_panic()?;

    if let Some(ref result) = form_result {
        warnings.extend(result.warnings.iter().cloned());
    }

    // If there are bare expressions, compile and execute them.
    if has_expr {
        let (value, ty) = compile_and_execute_expr(inmem_worker, platform_symbols, program, check)?;
        check_runtime_panic()?;
        return Ok((Some(value), Some(ty)));
    }

    let value = form_result.as_ref().map(|r| r.value);
    let result_type = form_result.map(|r| r.ty);
    Ok((value, result_type))
}

pub fn compile_and_execute_expr(
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    program: &Program,
    check: &CheckResult,
) -> Result<(i64, Type), CranelispError> {
    use cranelisp_types::TopLevel;

    let expr = program.iter().rev().find_map(|tl| {
        if let TopLevel::Expr(e) = tl { Some(e) } else { None }
    }).ok_or_else(|| CranelispError::CodegenError {
        message: "no expression found in program".into(),
        span: Span::SYNTHETIC,
    })?;

    let ty = check.display.as_ref()
        .map(|d| d.ty.clone())
        .or_else(|| check.expr_types.get(&expr.span()).cloned())
        .unwrap_or(Type::Int);

    if inmem_worker.traced_fns.is_empty() {
        let extra_syms: Vec<(&str, *const u8)> = platform_symbols
            .iter()
            .map(|(name, ptr)| (name.as_str(), *ptr))
            .collect();

        let compiled = cranelisp_backend::compile_expr_with_got_and_symbols(
            expr,
            check,
            Some(&mut inmem_worker.got_state),
            &extra_syms,
        )?;

        // SAFETY: compiled code was just generated and finalized by our JIT.
        let value = unsafe { compiled.execute() };
        Ok((value, ty))
    } else {
        let value = compile_and_execute_expr_with_trace(inmem_worker, platform_symbols, expr, check)?;
        Ok((value, ty))
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn infer_batch_result_type(
    program: &Program,
    check: &CheckResult,
) -> Type {
    use cranelisp_types::TopLevel;

    let last_nullary = program.iter().rev().find_map(|tl| match tl {
        TopLevel::Defn(defn) if !defn.is_multi_sig() && defn.params().is_empty() => Some(defn),
        _ => None,
    });

    if let Some(defn) = last_nullary {
        if let Some(ty) = check.expr_types.get(&defn.body().span()) {
            return ty.clone();
        }
    }

    Type::Int
}

fn check_runtime_panic() -> Result<(), CranelispError> {
    if let Some(message) = cranelisp_runtime::panic::take_runtime_error() {
        Err(CranelispError::CodegenError {
            message,
            span: Span::SYNTHETIC,
        })
    } else {
        Ok(())
    }
}

fn compile_and_execute_expr_with_trace(
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    expr: &cranelisp_types::Expr,
    check: &CheckResult,
) -> Result<i64, CranelispError> {
    use cranelisp_types::{Defn, DefnVariant, Symbol, Visibility};
    use std::collections::HashMap;

    let mut extra_syms: Vec<(&str, *const u8)> = platform_symbols
        .iter()
        .map(|(name, ptr)| (name.as_str(), *ptr))
        .collect();
    for (name, ptr) in &inmem_worker.trace_extra_symbols {
        extra_syms.push((name.as_str(), *ptr));
    }

    let mut jit = cranelisp_backend::jit::Jit::new_with_symbols(&extra_syms)?;
    jit.declare_intrinsics()?;

    let wrapper_name = Symbol::from("__repl_expr__");
    let wrapper_defn = Defn {
        name: wrapper_name.clone(),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            param_annotations: vec![],
            body: expr.clone(),
            span: expr.span(),
        }],
        visibility: Visibility::Public,
        span: expr.span(),
    };

    let func_ids = jit.declare_functions(&[&wrapper_defn])?;

    let mut got_slots: HashMap<Symbol, usize> = HashMap::new();
    let mut func_arities: HashMap<Symbol, usize> = HashMap::new();
    for (name, dc) in &inmem_worker.got_state.def_codegen {
        if let Some(slot) = dc.got_slot {
            got_slots.insert(name.clone(), slot);
        }
        if let Some(pc) = dc.param_count {
            func_arities.insert(name.clone(), pc);
        }
    }
    let got_base = inmem_worker.got_state.got_base_ptr() as i64;

    let mut compile_ctx = jit.build_compile_context(
        check,
        &func_ids,
        &func_arities,
        Some(&got_slots),
        Some(got_base),
        None,
    );

    compile_ctx.traced_fns = Some(&inmem_worker.traced_fns);

    jit.compile_defn(&wrapper_defn, compile_ctx)?;
    let code_ptr = jit.finalize_and_get_ptr(&wrapper_name, 0)?;

    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
    let value = func();

    inmem_worker.jit_modules.push(jit);

    Ok(value)
}

// ---------------------------------------------------------------------------
// Interactive mode: GOT-based per-defn compilation (free functions)
// ---------------------------------------------------------------------------

/// Compile a whole-program check result into the GOT, one defn at a time.
pub fn compile_checked_program(
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    program: &Program,
    check: &CheckResult,
) -> Result<Option<FormResult>, CranelispError> {
    use cranelisp_types::TopLevel;

    let mut last_result: Option<FormResult> = None;

    // Pre-register all defn names in GOT for forward references.
    for tl in program.iter() {
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

    // Compile default method bodies.
    for defn in &check.default_method_defns {
        compile_and_register_defn(inmem_worker, platform_symbols, defn, check)?;
    }

    // Compile mono specializations with per-specialization resolutions.
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

    // Compile each regular defn (skipping constrained fn base definitions).
    for tl in program.iter() {
        match tl {
            TopLevel::Defn(defn) => {
                if check.constrained_fn_names.contains(&defn.name) {
                    continue;
                }
                compile_and_register_defn(inmem_worker, platform_symbols, defn, check)?;

                // Execute zero-arg defns.
                let (value, result_ty) = if defn.params().is_empty() {
                    let entry = inmem_worker.got_state.def_codegen.get(defn.name.as_ref());
                    let code_ptr = entry
                        .and_then(|e| e.code_ptr)
                        .ok_or_else(|| CranelispError::CodegenError {
                            message: format!(
                                "no code pointer after compiling defn '{}'",
                                defn.name
                            ),
                            span: Span::SYNTHETIC,
                        })?;
                    let func: extern "C" fn() -> i64 =
                        unsafe { std::mem::transmute(code_ptr) };
                    let ret_ty = check
                        .expr_types
                        .get(&defn.body().span())
                        .cloned()
                        .unwrap_or(Type::Int);
                    (func(), ret_ty)
                } else {
                    (0, Type::Int)
                };
                last_result = Some(FormResult {
                    value,
                    ty: result_ty,
                    is_definition: true,
                    warnings: Vec::new(),
                });
            }
            TopLevel::TraitImpl(impl_) => {
                for method in &impl_.methods {
                    compile_and_register_defn(inmem_worker, platform_symbols, method, check)?;
                }
            }
            _ => {
                // TypeDef, TraitDecl — handled by typechecker, no codegen needed.
            }
        }
    }

    Ok(last_result)
}

/// Compile a single function definition and register it in the GOT.
///
/// Uses `SharedCodegenState` for GOT slot management and `WorkerJitState`
/// for per-worker JIT lifetime tracking. This is the primary implementation;
/// `compile_and_register_defn` delegates to this for old-path callers.
pub fn compile_and_register_defn_shared(
    shared_codegen: &mut crate::session::SharedCodegenState,
    worker_jit: &mut crate::session::WorkerJitState,
    platform_symbols: &[(String, *const u8)],
    defn: &Defn,
    check: &CheckResult,
) -> Result<(), CranelispError> {
    use std::collections::HashMap;

    let extra_symbols: Vec<(&str, *const u8)> = platform_symbols
        .iter()
        .map(|(name, ptr)| (name.as_str(), *ptr))
        .collect();
    let mut jit = cranelisp_backend::jit::Jit::new_with_symbols(&extra_symbols)?;

    jit.declare_intrinsics()?;

    let func_ids = jit.declare_functions(&[defn])?;

    let slot = shared_codegen.ensure_slot_for(&defn.name)?;

    let mut got_slots: HashMap<Symbol, usize> = HashMap::new();
    for (name, dc) in &shared_codegen.def_codegen {
        if let Some(s) = dc.got_slot {
            got_slots.insert(name.clone(), s);
        }
    }
    got_slots.insert(defn.name.clone(), slot);

    let got_base = shared_codegen.got_base_ptr() as i64;

    let mut func_arities: HashMap<Symbol, usize> = HashMap::new();
    for (name, dc) in &shared_codegen.def_codegen {
        if let Some(pc) = dc.param_count {
            func_arities.insert(name.clone(), pc);
        }
    }
    func_arities.insert(defn.name.clone(), defn.params().len());

    let compile_ctx = jit.build_compile_context(
        check,
        &func_ids,
        &func_arities,
        Some(&got_slots),
        Some(got_base),
        None,
    );
    let _clif_ir = jit.compile_defn(defn, compile_ctx)?;

    let code_ptr = jit.finalize_and_get_ptr(&defn.name, defn.params().len())?;

    shared_codegen.update_slot(slot, code_ptr);

    let entry = shared_codegen.def_codegen.entry(defn.name.clone()).or_default();
    entry.code_ptr = Some(code_ptr);
    entry.got_slot = Some(slot);
    entry.param_count = Some(defn.params().len());
    entry.defn = Some(defn.clone());

    worker_jit.jit_modules.push(jit);

    Ok(())
}

/// Compile a single function definition and register it in the GOT.
///
/// Legacy wrapper that bridges `InMemWorkerState` to the new
/// `SharedCodegenState` + `WorkerJitState` API. Used by the old pipeline
/// path (REPL eval, codegen_and_execute). Delegates directly to
/// `compile_and_register_defn_shared` by treating `InMemWorkerState`
/// fields as the shared+worker state (valid in single-threaded usage).
pub fn compile_and_register_defn(
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    defn: &Defn,
    check: &CheckResult,
) -> Result<(), CranelispError> {
    use std::collections::HashMap;

    let extra_symbols: Vec<(&str, *const u8)> = platform_symbols
        .iter()
        .map(|(name, ptr)| (name.as_str(), *ptr))
        .collect();
    let mut jit = cranelisp_backend::jit::Jit::new_with_symbols(&extra_symbols)?;

    jit.declare_intrinsics()?;

    let func_ids = jit.declare_functions(&[defn])?;

    let slot = inmem_worker.got_state.ensure_slot_for(&defn.name)?;

    let mut got_slots: HashMap<Symbol, usize> = HashMap::new();
    for (name, dc) in &inmem_worker.got_state.def_codegen {
        if let Some(s) = dc.got_slot {
            got_slots.insert(name.clone(), s);
        }
    }
    got_slots.insert(defn.name.clone(), slot);

    let got_base = inmem_worker.got_state.got_base_ptr() as i64;

    let mut func_arities: HashMap<Symbol, usize> = HashMap::new();
    for (name, dc) in &inmem_worker.got_state.def_codegen {
        if let Some(pc) = dc.param_count {
            func_arities.insert(name.clone(), pc);
        }
    }
    func_arities.insert(defn.name.clone(), defn.params().len());

    let compile_ctx = jit.build_compile_context(
        check,
        &func_ids,
        &func_arities,
        Some(&got_slots),
        Some(got_base),
        None,
    );
    let _clif_ir = jit.compile_defn(defn, compile_ctx)?;

    let code_ptr = jit.finalize_and_get_ptr(&defn.name, defn.params().len())?;

    inmem_worker.got_state.update_slot(slot, code_ptr);

    let entry = inmem_worker.got_state.def_codegen.entry(defn.name.clone()).or_default();
    entry.code_ptr = Some(code_ptr);
    entry.got_slot = Some(slot);
    entry.param_count = Some(defn.params().len());
    entry.defn = Some(defn.clone());

    inmem_worker.jit_modules.push(jit);

    Ok(())
}

// ---------------------------------------------------------------------------
// Stage 6b: Background .o writer integration
// ---------------------------------------------------------------------------

/// Queue a background .o + .meta.json write for a module (InMemoryAndObject only).
pub fn queue_background_cache_write(
    object_worker: &mut ObjectWorkerState,
    symbol_table: &cranelisp_types::SymbolTable,
    source: &str,
    module_path: &ModuleFullPath,
    structure: &ModuleStructure,
    program: &Program,
    check_result: &CheckResult,
) {
    use cranelisp_backend::cache;
    use std::collections::HashMap;

    if object_worker.cache_state.is_none() || object_worker.cache_writer.is_none() {
        return;
    }

    if !crate::session::has_compilable_defns(program) {
        return;
    }

    let object_input = build_object_compile_input(
        module_path,
        Some(program),
        Some(check_result),
        &object_worker.cross_module_func_sigs,
    );

    let codegen_state = build_codegen_state_for_cache(program, check_result);

    let metadata = cache::CacheMetadata {
        symbol_table: symbol_table.clone(),
        module_structure: structure.clone(),
        codegen_state,
    };

    let source_hash = cache::hash_source(source);

    let dep_hashes: HashMap<String, String> = HashMap::new();

    let cache_dir = object_worker.cache_state.as_ref()
        .expect("invariant: cache_state checked above")
        .cache_dir()
        .to_path_buf();

    let packet = match cache::build_cache_packet(
        &cache_dir,
        module_path,
        &source_hash,
        false,
        dep_hashes.clone(),
        &metadata,
        object_input,
    ) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("cache: failed to build packet for {}: {}", module_path, e.message());
            return;
        }
    };

    let (_meta_path, o_path) = cache::module_cache_path(&cache_dir, module_path);
    object_worker.compiled_o_paths.push(o_path);

    if let Some(cs) = object_worker.cache_state.as_mut() {
        cs.record_module(module_path, source_hash, dep_hashes);
    }

    object_worker.cache_writer.as_mut()
        .expect("invariant: cache_writer checked above")
        .queue_write(module_path.clone(), packet);
}

pub fn build_codegen_state_for_cache(
    program: &Program,
    check: &CheckResult,
) -> cranelisp_backend::cache::CacheCodegenState {
    use cranelisp_types::TopLevel;
    use std::collections::HashMap;

    let mut got_slots: HashMap<Symbol, usize> = HashMap::new();
    let mut def_entries: HashMap<Symbol, cranelisp_backend::cache::SerializedDefEntry> = HashMap::new();
    let mut next_slot: usize = 0;

    for tl in program.iter() {
        if let TopLevel::Defn(defn) = tl {
            if check.constrained_fn_names.contains(&defn.name) {
                continue;
            }
            let slot = next_slot;
            next_slot += 1;
            got_slots.insert(defn.name.clone(), slot);
            def_entries.insert(
                defn.name.clone(),
                cranelisp_backend::cache::SerializedDefEntry {
                    got_slot: Some(slot),
                    source: None,
                    sexp: None,
                    defn: Some(defn.clone()),
                    param_count: Some(defn.params().len()),
                },
            );
        }
    }

    for mono in &check.mono_defns {
        let slot = next_slot;
        next_slot += 1;
        got_slots.insert(mono.defn.name.clone(), slot);
        def_entries.insert(
            mono.defn.name.clone(),
            cranelisp_backend::cache::SerializedDefEntry {
                got_slot: Some(slot),
                source: None,
                sexp: None,
                defn: Some(mono.defn.clone()),
                param_count: Some(mono.defn.params().len()),
            },
        );
    }
    for defn in &check.default_method_defns {
        let slot = next_slot;
        next_slot += 1;
        got_slots.insert(defn.name.clone(), slot);
        def_entries.insert(
            defn.name.clone(),
            cranelisp_backend::cache::SerializedDefEntry {
                got_slot: Some(slot),
                source: None,
                sexp: None,
                defn: Some(defn.clone()),
                param_count: Some(defn.params().len()),
            },
        );
    }

    cranelisp_backend::cache::CacheCodegenState {
        got_slots,
        next_got_slot: next_slot,
        def_entries,
    }
}

fn accumulate_func_sigs_from_program(
    module_path: &ModuleFullPath,
    program: &Program,
    check: &CheckResult,
    func_sigs: &mut Vec<(Symbol, usize)>,
) {
    use cranelisp_types::TopLevel;

    for tl in program.iter() {
        if let TopLevel::Defn(defn) = tl {
            if check.constrained_fn_names.contains(&defn.name) {
                continue;
            }
            let param_count = defn.params().len();
            func_sigs.push((defn.name.clone(), param_count));
            let qualified = Symbol::from(
                format!("{}/{}", module_path, defn.name)
            );
            func_sigs.push((qualified, param_count));
        }
    }

    for mono in &check.mono_defns {
        let param_count = mono.defn.params().len();
        func_sigs.push((mono.defn.name.clone(), param_count));
    }
    for defn in &check.default_method_defns {
        let param_count = defn.params().len();
        func_sigs.push((defn.name.clone(), param_count));
    }
}

// ---------------------------------------------------------------------------
// Single-file batch pipeline (test helper)
// ---------------------------------------------------------------------------

/// Result of compiling and executing a source program.
pub struct PipelineResult {
    /// The i64 result value (raw bits; interpret per type).
    pub value: i64,
    /// The inferred type of the last expression or main function's return.
    pub ty: Type,
    /// Non-fatal warnings accumulated during compilation.
    pub warnings: Vec<Warning>,
}

/// Compile and execute source text via the unified pipeline.
///
/// Thin wrapper around `compile_unit()` that preserves the `PipelineResult`
/// interface used by 449+ test call sites. Creates a fresh session per call.
pub fn compile_and_run(
    source: &str,
) -> Result<PipelineResult, CranelispError> {
    let mut session = CompilationSession::new();
    let ctx = CompileContext {
        module: ModuleFullPath::from("user"),
        codegen: CodegenBehaviour::InMemoryAndObject,
    };
    let unit_result = session.compile_unit(source, &ctx, ModuleStrategy::Additive)?;
    let warnings_from_unit = unit_result.warnings.clone();
    session.inmem_queue.push(CodegenItem {
        ctx,
        unit_result,
    });
    let mut codegen_results = session.flush_inmem_queue()?;
    let codegen_result = match codegen_results.pop() {
        Some(r) => r,
        None => unreachable!("invariant: flush_inmem_queue must return one result per queued item"),
    };

    let mut warnings = warnings_from_unit;
    warnings.extend(codegen_result.warnings);

    Ok(PipelineResult {
        value: codegen_result.value.unwrap_or(0),
        ty: codegen_result.result_type.unwrap_or(Type::Int),
        warnings,
    })
}

// ---------------------------------------------------------------------------
// Multi-file module graph pipeline
// ---------------------------------------------------------------------------

/// A node in the module dependency graph.
#[derive(Debug, Clone)]
pub struct ModuleNode {
    /// Module's full dotted path (e.g., "util", "core.math").
    pub path: ModuleFullPath,
    /// Filesystem path to the .cl source file.
    pub file_path: PathBuf,
    /// Modules this module depends on (declared via `mod`).
    pub dependencies: Vec<ModuleFullPath>,
}

/// The complete module dependency graph for a project.
#[derive(Debug)]
pub struct ModuleGraph {
    /// All modules, keyed by full path.
    pub nodes: HashMap<ModuleFullPath, ModuleNode>,
    /// The entry module's path.
    pub entry: ModuleFullPath,
    /// Project root directory (parent of the entry file).
    pub project_root: PathBuf,
    /// Library directories for module resolution (searched in order after project root).
    pub lib_dirs: Vec<PathBuf>,
}

/// Result of compiling a multi-file module graph (compile + execute).
pub struct CompiledModuleGraph {
    /// The i64 result value from executing the entry module's entry point.
    pub value: i64,
    /// The inferred type of the entry point's return value.
    pub ty: Type,
    /// Non-fatal warnings accumulated during compilation.
    pub warnings: Vec<Warning>,
}

/// Discover the module dependency graph starting from an entry file.
pub fn discover_module_graph(
    entry: &Path,
    lib_dirs: &[PathBuf],
) -> Result<ModuleGraph, CranelispError> {
    let entry = entry.canonicalize().map_err(|e| CranelispError::ModuleError {
        message: format!("cannot resolve entry file '{}': {}", entry.display(), e),
        file: Some(entry.to_path_buf()),
        span: Span::SYNTHETIC,
    })?;

    let project_root = entry.parent().ok_or_else(|| CranelispError::ModuleError {
        message: "entry file has no parent directory".to_string(),
        file: Some(entry.clone()),
        span: Span::SYNTHETIC,
    })?.to_path_buf();

    let entry_stem = entry
        .file_stem()
        .and_then(|s| s.to_str())
        .ok_or_else(|| CranelispError::ModuleError {
            message: "entry file has no valid stem".to_string(),
            file: Some(entry.clone()),
            span: Span::SYNTHETIC,
        })?;
    let entry_path = ModuleFullPath::from(entry_stem);

    let mut graph = ModuleGraph {
        nodes: HashMap::new(),
        entry: entry_path.clone(),
        project_root: project_root.clone(),
        lib_dirs: lib_dirs.to_vec(),
    };

    let mut visiting: Vec<ModuleFullPath> = Vec::new();
    discover_module_recursive(
        &entry_path,
        &entry,
        &project_root,
        &graph.lib_dirs,
        &mut graph.nodes,
        &mut visiting,
    )?;

    Ok(graph)
}

fn discover_module_recursive(
    module_path: &ModuleFullPath,
    file_path: &Path,
    project_root: &Path,
    lib_dirs: &[PathBuf],
    nodes: &mut HashMap<ModuleFullPath, ModuleNode>,
    visiting: &mut Vec<ModuleFullPath>,
) -> Result<(), CranelispError> {
    if visiting.contains(module_path) {
        let cycle_start = visiting.iter().position(|p| p == module_path).unwrap_or(0);
        let cycle: Vec<String> = visiting[cycle_start..]
            .iter()
            .map(|p| p.to_string())
            .collect();
        return Err(CranelispError::ModuleError {
            message: format!(
                "circular module dependency: {} -> {}",
                cycle.join(" -> "),
                module_path
            ),
            file: Some(file_path.to_path_buf()),
            span: Span::SYNTHETIC,
        });
    }

    if nodes.contains_key(module_path) {
        return Ok(());
    }

    visiting.push(module_path.clone());

    let source = std::fs::read_to_string(file_path).map_err(|e| CranelispError::ModuleError {
        message: format!("cannot read '{}': {}", file_path.display(), e),
        file: Some(file_path.to_path_buf()),
        span: Span::SYNTHETIC,
    })?;

    let sexps = cranelisp_frontend::parse(&source).map_err(|e| CranelispError::ModuleError {
        message: format!("parse error in '{}': {}", file_path.display(), e),
        file: Some(file_path.to_path_buf()),
        span: e.span(),
    })?;

    let (structure, _remaining) = cranelisp_frontend::extract_module_declarations(
        module_path.clone(),
        Some(file_path.to_path_buf()),
        sexps,
    )?;

    let mut dependencies = Vec::new();

    for mod_decl in &structure.mod_decls {
        if mod_decl.inline_body.is_some() {
            continue;
        }

        let submod_name = &mod_decl.name;

        let child_path = if module_path.0.is_empty() {
            ModuleFullPath::from(submod_name.as_ref())
        } else {
            ModuleFullPath::from(format!("{}.{}", module_path, submod_name))
        };

        let resolved = resolve_submodule_file(
            file_path,
            submod_name.as_ref(),
            project_root,
            lib_dirs,
        )?;

        dependencies.push(child_path.clone());

        discover_module_recursive(
            &child_path,
            &resolved,
            project_root,
            lib_dirs,
            nodes,
            visiting,
        )?;
    }

    discover_import_dependencies(
        &structure,
        module_path,
        file_path,
        project_root,
        lib_dirs,
        nodes,
        visiting,
        &mut dependencies,
    )?;

    nodes.insert(
        module_path.clone(),
        ModuleNode {
            path: module_path.clone(),
            file_path: file_path.to_path_buf(),
            dependencies,
        },
    );

    visiting.pop();
    Ok(())
}

/// Synthetic modules seeded by the compiler (no corresponding files).
const SYNTHETIC_MODULES: &[&str] = &["primitives", "macros"];

#[allow(clippy::too_many_arguments)]
fn discover_import_dependencies(
    structure: &ModuleStructure,
    module_path: &ModuleFullPath,
    file_path: &Path,
    project_root: &Path,
    lib_dirs: &[PathBuf],
    nodes: &mut HashMap<ModuleFullPath, ModuleNode>,
    visiting: &mut Vec<ModuleFullPath>,
    dependencies: &mut Vec<ModuleFullPath>,
) -> Result<(), CranelispError> {
    let all_module_paths = structure
        .import_specs
        .iter()
        .map(|s| &s.module_path)
        .chain(structure.export_specs.iter().map(|s| &s.module_path));
    for ref_module_path in all_module_paths {
        let ref_path: &str = ref_module_path.as_ref();

        if is_synthetic_or_special(ref_path) {
            continue;
        }

        let root_name = ref_path.split('.').next().unwrap_or(ref_path);

        let candidate_path = if module_path.0.is_empty() {
            ModuleFullPath::from(root_name)
        } else {
            let mod_prefix = format!("{}.", module_path);
            if ref_path.starts_with(&mod_prefix) {
                ref_module_path.clone()
            } else {
                ModuleFullPath::from(root_name)
            }
        };

        if dependencies.contains(&candidate_path) {
            continue;
        }

        if nodes.contains_key(&candidate_path) {
            dependencies.push(candidate_path.clone());
            continue;
        }

        let resolved = match resolve_submodule_file(
            file_path,
            root_name,
            project_root,
            lib_dirs,
        ) {
            Ok(path) => path,
            Err(_) => {
                continue;
            }
        };

        dependencies.push(candidate_path.clone());

        discover_module_recursive(
            &candidate_path,
            &resolved,
            project_root,
            lib_dirs,
            nodes,
            visiting,
        )?;
    }

    Ok(())
}

fn is_synthetic_or_special(module_path: &str) -> bool {
    let root = module_path.split('.').next().unwrap_or(module_path);
    SYNTHETIC_MODULES.contains(&root) || root == "super" || root == "prelude"
}

fn resolve_submodule_file(
    parent_file: &Path,
    name: &str,
    project_root: &Path,
    lib_dirs: &[PathBuf],
) -> Result<PathBuf, CranelispError> {
    let parent_dir = parent_file.parent().unwrap_or(Path::new("."));
    let stem = parent_file
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("");

    let filename = format!("{name}.cl");

    // 1. Child directory: {parent_dir}/{stem}/{name}.cl
    let child = parent_dir.join(stem).join(&filename);
    if child.is_file() {
        return Ok(child);
    }

    // 2. Sibling file: {parent_dir}/{name}.cl
    let sibling = parent_dir.join(&filename);
    if sibling.is_file() {
        return Ok(sibling);
    }

    // 3. Project root: {project_root}/{name}.cl
    if parent_dir != project_root {
        let root_file = project_root.join(&filename);
        if root_file.is_file() {
            return Ok(root_file);
        }
    }

    // 4. Lib directories: {lib_dir}/{name}.cl
    for lib_dir in lib_dirs {
        let lib_file = lib_dir.join(&filename);
        if lib_file.is_file() {
            return Ok(lib_file);
        }
    }

    Err(CranelispError::ModuleError {
        message: format!(
            "cannot find module '{}' (searched child dir '{}/{}/', sibling '{}/{}', \
             project root, and lib directories)",
            name, parent_dir.display(), stem, parent_dir.display(), filename
        ),
        file: Some(parent_file.to_path_buf()),
        span: Span::SYNTHETIC,
    })
}

/// Topological sort of the module graph using Kahn's algorithm.
pub fn toposort(graph: &ModuleGraph) -> Result<Vec<ModuleFullPath>, CranelispError> {
    use std::collections::VecDeque;

    let mut in_degree: HashMap<ModuleFullPath, usize> = HashMap::new();
    let mut adj: HashMap<ModuleFullPath, Vec<ModuleFullPath>> = HashMap::new();

    for (path, node) in &graph.nodes {
        in_degree.entry(path.clone()).or_insert(0);
        for dep in &node.dependencies {
            adj.entry(dep.clone()).or_default().push(path.clone());
            *in_degree.entry(path.clone()).or_insert(0) += 1;
        }
    }

    let mut queue: VecDeque<ModuleFullPath> = in_degree
        .iter()
        .filter(|(_, deg)| **deg == 0)
        .map(|(path, _)| path.clone())
        .collect();

    let mut sorted = Vec::with_capacity(graph.nodes.len());

    while let Some(current) = queue.pop_front() {
        sorted.push(current.clone());

        if let Some(dependents) = adj.get(&current) {
            for dependent in dependents {
                if let Some(deg) = in_degree.get_mut(dependent) {
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push_back(dependent.clone());
                    }
                }
            }
        }
    }

    if sorted.len() != graph.nodes.len() {
        let remaining: Vec<String> = graph
            .nodes
            .keys()
            .filter(|k| !sorted.iter().any(|s| s == *k))
            .map(|k| k.to_string())
            .collect();
        return Err(CranelispError::ModuleError {
            message: format!("circular dependency among modules: {}", remaining.join(", ")),
            file: None,
            span: Span::SYNTHETIC,
        });
    }

    Ok(sorted)
}

/// Compile a multi-file module graph via the pipeline and execute main.
pub fn compile_module_graph(
    entry: &Path,
    lib_dirs: &[PathBuf],
) -> Result<CompiledModuleGraph, CranelispError> {
    compile_module_graph_cached(entry, lib_dirs, &CacheConfig::Disabled)
}

/// Compile a multi-file module graph with optional caching.
pub fn compile_module_graph_cached(
    entry: &Path,
    lib_dirs: &[PathBuf],
    cache_config: &CacheConfig,
) -> Result<CompiledModuleGraph, CranelispError> {
    let graph = discover_module_graph(entry, lib_dirs)?;
    let order = toposort(&graph)?;

    let mut all_warnings: Vec<Warning> = Vec::new();
    let mut session = match cache_config.cache_dir() {
        Some(dir) => {
            let _ = std::fs::create_dir_all(dir);
            CompilationSession::new_with_cache(dir.to_path_buf())
        }
        None => CompilationSession::new(),
    };
    session.interactive = true;

    let entry_dir = entry
        .canonicalize()
        .ok()
        .and_then(|p| p.parent().map(|d| d.to_path_buf()));
    let mut all_lib_dirs: Vec<PathBuf> = Vec::new();
    if let Some(dir) = &entry_dir {
        all_lib_dirs.push(dir.clone());
    }
    all_lib_dirs.extend(lib_dirs.iter().cloned());
    session.lib_dirs = all_lib_dirs;
    session.project_root = entry_dir.unwrap_or_else(|| PathBuf::from("."));

    let mut entry_codegen: Option<CodegenResult> = None;
    for module_path in &order {
        let node = &graph.nodes[module_path];

        // Cache-hit check: for non-entry modules, try loading from cache.
        let is_entry = module_path == &graph.entry;
        if !is_entry && try_cache_hit_load(&mut session, module_path, &node.file_path) {
            continue;
        }

        let source = std::fs::read_to_string(&node.file_path).map_err(|e| {
            CranelispError::ModuleError {
                message: format!("cannot read '{}': {}", node.file_path.display(), e),
                file: Some(node.file_path.clone()),
                span: Span::SYNTHETIC,
            }
        })?;

        let ctx = CompileContext {
            module: module_path.clone(),
            codegen: CodegenBehaviour::InMemoryAndObject,
        };

        let source_hash = cache::hash_source(&source);
        let unit_result = session.compile_unit(&source, &ctx, ModuleStrategy::Additive)?;
        all_warnings.extend(unit_result.warnings.clone());
        session.inmem_queue.push(CodegenItem {
            ctx,
            unit_result,
        });
        let mut codegen_results = session.flush_inmem_queue()?;
        if is_entry {
            entry_codegen = codegen_results.pop();
        }
        for codegen_result in codegen_results {
            all_warnings.extend(codegen_result.warnings);
        }

        if let Some(cs) = session.object_worker.cache_state.as_mut() {
            let node = &graph.nodes[module_path];
            let dep_hashes: HashMap<String, String> = node
                .dependencies
                .iter()
                .filter_map(|dep| {
                    cs.source_hashes()
                        .get(dep)
                        .map(|h| (dep.0.clone(), h.clone()))
                })
                .collect();
            cs.record_module(module_path, source_hash, dep_hashes);
        }
    }

    session.flush_cache_writes();
    if let Some(cs) = &session.object_worker.cache_state {
        let _ = cs.flush();
    }

    let entry_result = entry_codegen.ok_or_else(|| CranelispError::ModuleError {
        message: "entry module produced no codegen result".into(),
        file: Some(entry.to_path_buf()),
        span: Span::SYNTHETIC,
    })?;
    all_warnings.extend(entry_result.warnings);

    let main_sym = Symbol::from("main");
    let qualified_main = Symbol::from(format!("{}/main", graph.entry.as_ref()));
    let got = &session.inmem_worker.got_state;
    let main_exists = got.def_codegen.contains_key(&main_sym)
        || got.def_codegen.contains_key(&qualified_main);
    if !main_exists {
        return Err(CranelispError::ModuleError {
            message: "entry module has no `main` function — batch mode requires (defn main [] ...)".into(),
            file: Some(entry.to_path_buf()),
            span: Span::SYNTHETIC,
        });
    }

    let raw_value = entry_result.value.unwrap_or(0);
    let result_type = entry_result.result_type.unwrap_or(Type::Int);

    let (value, ty) = if result_type.is_io() {
        let inner_value = cranelisp_runtime::run_io_trampoline(raw_value);
        let inner_type = result_type.io_inner_type();
        (inner_value, inner_type)
    } else {
        (raw_value, result_type)
    };

    Ok(CompiledModuleGraph {
        value,
        ty,
        warnings: all_warnings,
    })
}

// ---------------------------------------------------------------------------
// Object compilation helpers
// ---------------------------------------------------------------------------

pub(crate) struct CollectedDefns {
    defns: Vec<(Defn, cranelisp_types::Scheme)>,
    fn_slot_assignments: HashMap<Symbol, cache::object::FnSlotInfo>,
    next_slot: usize,
}

pub(crate) fn collect_defns_for_cache(
    program: Option<&Program>,
    check: Option<&CheckResult>,
) -> CollectedDefns {
    use cranelisp_types::TopLevel;

    let mut defns: Vec<(Defn, cranelisp_types::Scheme)> = Vec::new();
    let mut fn_slot_assignments: HashMap<Symbol, cache::object::FnSlotInfo> = HashMap::new();
    let mut next_slot: usize = 0;

    let Some(prog) = program else {
        return CollectedDefns { defns, fn_slot_assignments, next_slot };
    };

    for tl in prog.iter() {
        if let TopLevel::Defn(defn) = tl {
            if let Some(ch) = check
                && ch.constrained_fn_names.contains(&defn.name)
            {
                continue;
            }
            let scheme = scheme_for_defn(defn, check);
            let slot = next_slot;
            next_slot += 1;
            fn_slot_assignments.insert(
                defn.name.clone(),
                cache::object::FnSlotInfo {
                    slot,
                    param_count: defn.params().len(),
                },
            );
            defns.push((defn.clone(), scheme));
        }
    }

    if let Some(ch) = check {
        for mono in &ch.mono_defns {
            let scheme = scheme_for_defn(&mono.defn, Some(ch));
            let slot = next_slot;
            next_slot += 1;
            fn_slot_assignments.insert(
                mono.defn.name.clone(),
                cache::object::FnSlotInfo {
                    slot,
                    param_count: mono.defn.params().len(),
                },
            );
            defns.push((mono.defn.clone(), scheme));
        }
        for defn in &ch.default_method_defns {
            let scheme = scheme_for_defn(defn, Some(ch));
            let slot = next_slot;
            next_slot += 1;
            fn_slot_assignments.insert(
                defn.name.clone(),
                cache::object::FnSlotInfo {
                    slot,
                    param_count: defn.params().len(),
                },
            );
            defns.push((defn.clone(), scheme));
        }
    }

    CollectedDefns { defns, fn_slot_assignments, next_slot }
}

pub(crate) fn scheme_for_defn(defn: &Defn, check: Option<&CheckResult>) -> cranelisp_types::Scheme {
    let ty = check
        .and_then(|ch| ch.expr_types.get(&defn.span))
        .cloned()
        .unwrap_or_else(|| {
            Type::Fn(
                defn.params().iter().map(|_| Type::Int).collect(),
                Box::new(Type::Int),
            )
        });
    cranelisp_types::Scheme {
        vars: vec![],
        constraints: HashMap::new(),
        ty,
    }
}

pub(crate) struct CrossModuleRefs {
    fn_to_module: HashMap<Symbol, ModuleFullPath>,
    cross_module_fns: Vec<(Symbol, usize)>,
}

pub(crate) fn collect_cross_module_refs(
    func_sigs: &[(Symbol, usize)],
) -> CrossModuleRefs {
    let mut fn_to_module: HashMap<Symbol, ModuleFullPath> = HashMap::new();
    let mut cross_module_fns: Vec<(Symbol, usize)> = Vec::new();

    for (name, param_count) in func_sigs {
        if let Some(slash) = name.as_ref().find('/') {
            let mod_part = &name.as_ref()[..slash];
            fn_to_module.insert(name.clone(), ModuleFullPath::from(mod_part));
        }
        cross_module_fns.push((name.clone(), *param_count));
    }

    CrossModuleRefs { fn_to_module, cross_module_fns }
}

pub(crate) fn build_object_compile_input(
    module_path: &ModuleFullPath,
    program: Option<&Program>,
    check: Option<&CheckResult>,
    func_sigs: &[(Symbol, usize)],
) -> cache::ObjectCompileInput {
    let collected = collect_defns_for_cache(program, check);
    let cross_refs = collect_cross_module_refs(func_sigs);
    let intrinsics = build_intrinsic_table();

    cache::ObjectCompileInput {
        module_path: module_path.clone(),
        defns: collected.defns,
        method_resolutions: check
            .map(|ch| ch.method_resolutions.clone())
            .unwrap_or_default(),
        fn_slot_assignments: collected.fn_slot_assignments,
        fn_to_module: cross_refs.fn_to_module,
        intrinsics,
        type_defs: check
            .map(|ch| ch.type_defs.clone())
            .unwrap_or_default(),
        constructor_to_type: check
            .map(|ch| ch.constructor_to_type.clone())
            .unwrap_or_default(),
        expr_types: check
            .map(|ch| ch.expr_types.clone())
            .unwrap_or_default(),
        next_got_slot: collected.next_slot,
        cross_module_fns: cross_refs.cross_module_fns,
    }
}

pub(crate) fn build_intrinsic_table() -> cache::IntrinsicTable {
    let mut table = cache::IntrinsicTable::new();

    for sym in cranelisp_backend::jit::intrinsic_symbols() {
        let entry = cache::IntrinsicEntry {
            user_name: Symbol::from(sym.name),
            jit_name: sym.name.to_string(),
            param_count: sym.param_count,
        };
        if sym.is_runtime {
            table.runtime_fns.push(entry);
        } else {
            table.primitive_fns.push(entry);
        }
    }

    table
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{CompileContext, ModuleFullPath, ModuleStrategy};

    // Compile-time Send assertions (Step 11: concurrent codegen worker).
    fn _assert_send<T: Send>() {}

    #[allow(dead_code)]
    fn _send_assertions() {
        _assert_send::<CodegenPacket>();
        _assert_send::<CompileUnitResult>();
        _assert_send::<CompileContext>();
        _assert_send::<CheckResult>();
        _assert_send::<CodegenResult>();
        _assert_send::<InMemWorkerState>();
        _assert_send::<ObjectWorkerState>();
    }

    fn batch_ctx() -> CompileContext {
        CompileContext {
            module: ModuleFullPath::from("user"),
            codegen: CodegenBehaviour::InMemoryAndObject,
        }
    }

    fn additive_ctx() -> CompileContext {
        CompileContext {
            module: ModuleFullPath::from("user"),
            codegen: CodegenBehaviour::InMemoryAndObject,
        }
    }

    // spec: design/arch/pipeline-v2.md §2 — unified pipeline stages
    #[test]
    fn batch_defn_main_returns_value() {
        let mut session = CompilationSession::new();
        let ctx = batch_ctx();
        let unit_result = session.compile_unit("(defn main [] (if true 3 0))", &ctx, ModuleStrategy::Additive)
            .expect("compile_unit failed");
        let codegen_result = codegen_and_execute_via_session(&mut session, &unit_result, &ctx)
            .expect("codegen_and_execute failed");

        assert_eq!(codegen_result.value, Some(3));
    }

    // spec: design/arch/pipeline-v2.md §5.5 — Expr handling via synthetic defn
    #[test]
    fn additive_bare_expression() {
        let mut session = CompilationSession::new();
        session.interactive = true;
        let ctx = additive_ctx();
        let unit_result = session.compile_unit("(if true 3 0)", &ctx, ModuleStrategy::Additive)
            .expect("compile_unit failed");
        let codegen_result = codegen_and_execute_via_session(&mut session, &unit_result, &ctx)
            .expect("codegen_and_execute failed");

        assert_eq!(codegen_result.value, Some(3));
    }

    // spec: design/arch/pipeline-v2.md §8.7 — defmacro in source followed by usage
    #[test]
    fn defmacro_followed_by_usage() {
        let source = r#"
            (defmacro wrap [x] `(primitives/add-i64 1 ~x))
            (defn main [] (wrap 41))
        "#;
        let mut session = CompilationSession::new();
        let ctx = batch_ctx();
        let unit_result = session.compile_unit(source, &ctx, ModuleStrategy::Additive)
            .expect("compile_unit failed");
        let codegen_result = codegen_and_execute_via_session(&mut session, &unit_result, &ctx)
            .expect("codegen_and_execute failed");

        assert_eq!(codegen_result.value, Some(42));
    }

    // spec: design/arch/pipeline-v2.md §8.3 — cycle detection
    #[test]
    fn cycle_detection_reports_error() {
        let mut session = CompilationSession::new();
        let module = ModuleFullPath::from("alpha");
        session.compile_stack.push(module.clone());

        let err = check_cycle(&session, &module);
        assert!(err.is_err(), "expected circular dependency error");
        let msg = err.unwrap_err().message().to_string();
        assert!(
            msg.contains("circular dependency"),
            "error should mention circular dependency, got: {msg}"
        );
    }

    // spec: design/arch/pipeline-v2.md §8.3 — non-cyclic no false positive
    #[test]
    fn non_cyclic_no_false_positive() {
        let mut session = CompilationSession::new();
        session.compile_stack.push(ModuleFullPath::from("alpha"));

        let result = check_cycle(&session, &ModuleFullPath::from("beta"));
        assert!(result.is_ok(), "should not report cycle for different module");
    }

    // --- IO type detection ---

    // spec: 10-io §10.6.1 — determine_exit_code for Int result
    #[test]
    fn test_determine_exit_code_int() {
        assert_eq!(crate::session::determine_exit_code(0, &Type::Int), 0);
        assert_eq!(crate::session::determine_exit_code(42, &Type::Int), 42);
        assert_eq!(crate::session::determine_exit_code(1, &Type::Int), 1);
    }

    // spec: 10-io §10.6.1 — determine_exit_code for non-Int result
    #[test]
    fn test_determine_exit_code_non_int() {
        assert_eq!(crate::session::determine_exit_code(42, &Type::String), 0);
        assert_eq!(crate::session::determine_exit_code(42, &Type::Bool), 0);
    }

    // --- Single-file pipeline tests ---

    #[test]
    fn test_pipeline_simple_int() {
        let result = compile_and_run("(defn main [] 42)").unwrap();
        assert_eq!(result.value, 42);
        assert_eq!(result.ty, Type::Int);
    }

    #[test]
    fn test_pipeline_bool_true() {
        let result = compile_and_run("(defn main [] true)").unwrap();
        assert_eq!(result.value, 1);
        assert_eq!(result.ty, Type::Bool);
    }

    #[test]
    fn test_pipeline_parse_error() {
        let result = compile_and_run("(defn main [] ");
        assert!(result.is_err());
    }

    #[test]
    fn test_pipeline_returns_correct_value() {
        let result = compile_and_run("(defn main [] 42)").unwrap();
        assert_eq!(result.value, 42);
    }

    // --- Module graph discovery tests ---

    #[test]
    fn test_discover_single_file() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(defn main [] 42)").unwrap();

        let graph = discover_module_graph(&entry, &[]).unwrap();
        assert_eq!(graph.nodes.len(), 1);
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main")));
        assert_eq!(graph.entry, ModuleFullPath::from("main"));
    }

    #[test]
    fn test_discover_with_submodule() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod util)\n(defn main [] 42)").unwrap();
        let util_file = dir.path().join("util.cl");
        std::fs::write(&util_file, "(defn helper [] 1)").unwrap();

        let graph = discover_module_graph(&entry, &[]).unwrap();
        assert_eq!(graph.nodes.len(), 2);
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main")));
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main.util")));
    }

    #[test]
    fn test_discover_child_directory_priority() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("app.cl");
        std::fs::write(&entry, "(mod handler)").unwrap();

        let child_dir = dir.path().join("app");
        std::fs::create_dir_all(&child_dir).unwrap();
        std::fs::write(child_dir.join("handler.cl"), "(defn handle [] 1)").unwrap();
        std::fs::write(dir.path().join("handler.cl"), "(defn handle [] 2)").unwrap();

        let graph = discover_module_graph(&entry, &[]).unwrap();
        let handler_node = &graph.nodes[&ModuleFullPath::from("app.handler")];
        assert!(handler_node.file_path.to_str().unwrap().contains("app/handler.cl"));
    }

    #[test]
    fn test_discover_missing_module_error() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod nonexistent)").unwrap();

        let result = discover_module_graph(&entry, &[]);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.message().contains("cannot find module 'nonexistent'"));
    }

    #[test]
    fn test_discover_circular_dependency() {
        let dir = tempfile::tempdir().unwrap();
        let a_file = dir.path().join("a.cl");
        let b_file = dir.path().join("b.cl");

        let mut nodes = HashMap::new();
        nodes.insert(
            ModuleFullPath::from("a"),
            ModuleNode {
                path: ModuleFullPath::from("a"),
                file_path: a_file.clone(),
                dependencies: vec![ModuleFullPath::from("b")],
            },
        );
        nodes.insert(
            ModuleFullPath::from("b"),
            ModuleNode {
                path: ModuleFullPath::from("b"),
                file_path: b_file.clone(),
                dependencies: vec![ModuleFullPath::from("a")],
            },
        );
        let graph = ModuleGraph {
            nodes,
            entry: ModuleFullPath::from("a"),
            project_root: dir.path().to_path_buf(),
            lib_dirs: Vec::new(),
        };

        let result = toposort(&graph);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.message().contains("circular dependency"));
    }

    #[test]
    fn test_toposort_order() {
        let mut nodes = HashMap::new();
        nodes.insert(ModuleFullPath::from("a"), ModuleNode {
            path: ModuleFullPath::from("a"),
            file_path: PathBuf::from("a.cl"),
            dependencies: vec![ModuleFullPath::from("b"), ModuleFullPath::from("c")],
        });
        nodes.insert(ModuleFullPath::from("b"), ModuleNode {
            path: ModuleFullPath::from("b"),
            file_path: PathBuf::from("b.cl"),
            dependencies: vec![ModuleFullPath::from("c")],
        });
        nodes.insert(ModuleFullPath::from("c"), ModuleNode {
            path: ModuleFullPath::from("c"),
            file_path: PathBuf::from("c.cl"),
            dependencies: vec![],
        });

        let graph = ModuleGraph {
            nodes,
            entry: ModuleFullPath::from("a"),
            project_root: PathBuf::from("."),
            lib_dirs: Vec::new(),
        };

        let order = toposort(&graph).unwrap();
        assert_eq!(order.len(), 3);
        let pos_a = order.iter().position(|p| p == "a").unwrap();
        let pos_b = order.iter().position(|p| p == "b").unwrap();
        let pos_c = order.iter().position(|p| p == "c").unwrap();
        assert!(pos_c < pos_b);
        assert!(pos_b < pos_a);
    }

    #[test]
    fn test_toposort_single_node() {
        let mut nodes = HashMap::new();
        nodes.insert(ModuleFullPath::from("main"), ModuleNode {
            path: ModuleFullPath::from("main"),
            file_path: PathBuf::from("main.cl"),
            dependencies: vec![],
        });

        let graph = ModuleGraph {
            nodes,
            entry: ModuleFullPath::from("main"),
            project_root: PathBuf::from("."),
            lib_dirs: Vec::new(),
        };

        let order = toposort(&graph).unwrap();
        assert_eq!(order, vec![ModuleFullPath::from("main")]);
    }

    #[test]
    fn test_compile_single_file_project() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(defn main [] 42)").unwrap();

        let result = compile_module_graph(&entry, &[]).unwrap();
        assert_eq!(result.value, 42);
        assert_eq!(result.ty, Type::Int);
    }

    #[test]
    fn test_compile_file_not_found() {
        let result = compile_module_graph(Path::new("/nonexistent/path/main.cl"), &[]);
        assert!(result.is_err());
    }

    #[test]
    fn test_resolve_sibling_module() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod util)\n(defn main [] 99)").unwrap();
        let util_file = dir.path().join("util.cl");
        std::fs::write(&util_file, "(defn helper [] 1)").unwrap();

        let graph = discover_module_graph(&entry, &[]).unwrap();
        assert_eq!(graph.nodes.len(), 2);

        let order = toposort(&graph).unwrap();
        let pos_main = order.iter().position(|p| p == "main").unwrap();
        let pos_util = order.iter().position(|p| p == "main.util").unwrap();
        assert!(pos_util < pos_main);
    }

    #[test]
    fn test_resolve_lib_module() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod helper)\n(defn main [] 1)").unwrap();
        let stdlib_dir = dir.path().join("lib");
        std::fs::create_dir_all(&stdlib_dir).unwrap();
        std::fs::write(stdlib_dir.join("helper.cl"), "(defn help [] 2)").unwrap();

        let graph = discover_module_graph(&entry, &[stdlib_dir.clone()]).unwrap();
        assert_eq!(graph.nodes.len(), 2);
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main.helper")));
    }

    #[test]
    fn test_nested_submodules() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod a)\n(defn main [] 1)").unwrap();
        let a_file = dir.path().join("a.cl");
        std::fs::write(&a_file, "(mod b)").unwrap();
        let a_dir = dir.path().join("a");
        std::fs::create_dir_all(&a_dir).unwrap();
        std::fs::write(a_dir.join("b.cl"), "(defn leaf [] 3)").unwrap();

        let graph = discover_module_graph(&entry, &[]).unwrap();
        assert_eq!(graph.nodes.len(), 3);

        let order = toposort(&graph).unwrap();
        let pos_main = order.iter().position(|p| p == "main").unwrap();
        let pos_a = order.iter().position(|p| p == "main.a").unwrap();
        let pos_b = order.iter().position(|p| p == "main.a.b").unwrap();
        assert!(pos_b < pos_a);
        assert!(pos_a < pos_main);
    }

    #[test]
    fn test_cross_module_import_resolution() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(
            &entry,
            "(mod util)\n(import [main.util [helper]])\n(defn main [] (helper))",
        ).unwrap();
        let util_file = dir.path().join("util.cl");
        std::fs::write(&util_file, "(defn helper [] 42)").unwrap();

        let result = compile_module_graph(&entry, &[]).unwrap();
        assert_eq!(result.value, 42);
    }

    // --- Macro integration tests ---

    #[test]
    fn test_batch_defmacro_identity() {
        let source = r#"
            (defmacro id [x] x)
            (defn main [] (id 42))
        "#;
        let result = compile_and_run(source).unwrap();
        assert_eq!(result.value, 42);
    }

    #[test]
    fn test_batch_defmacro_quasiquote() {
        let source = r#"
            (defmacro inc1 [x] `(primitives/add-i64 1 ~x))
            (defn main [] (inc1 41))
        "#;
        let result = compile_and_run(source).unwrap();
        assert_eq!(result.value, 42);
    }

    #[test]
    fn test_batch_macro_uses_earlier_macro() {
        let source = r#"
            (defmacro id [x] x)
            (defmacro id2 [x] (id x))
            (defn main [] (id2 99))
        "#;
        let result = compile_and_run(source).unwrap();
        assert_eq!(result.value, 99);
    }

    #[test]
    fn test_batch_multi_clause_macro() {
        let source = r#"
            (defmacro pick ([x] x) ([x y] x))
            (defn main [] (pick 77))
        "#;
        let result = compile_and_run(source).unwrap();
        assert_eq!(result.value, 77);
    }

    #[test]
    fn test_batch_no_macros_unchanged() {
        let source = "(defn main [] (primitives/add-i64 1 2))";
        let result = compile_and_run(source).unwrap();
        assert_eq!(result.value, 3);
    }

    #[test]
    fn test_module_graph_defmacro() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(defmacro id [x] x)\n(defn main [] (id 42))").unwrap();
        let result = compile_module_graph(&entry, &[]).unwrap();
        assert_eq!(result.value, 42);
    }

    // --- Prelude tests ---

    #[test]
    fn test_prelude_loading_from_lib() {
        let dir = tempfile::tempdir().unwrap();
        let stdlib_dir = dir.path().join("lib");
        std::fs::create_dir_all(&stdlib_dir).unwrap();
        std::fs::write(stdlib_dir.join("prelude.cl"), "(defmacro id [x] x)").unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(defn main [] (id 55))").unwrap();
        let result = compile_module_graph(&entry, &[stdlib_dir.clone()]).unwrap();
        assert_eq!(result.value, 55);
    }

    #[test]
    fn test_no_prelude_still_works() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(defn main [] 42)").unwrap();
        let result = compile_module_graph(&entry, &[]).unwrap();
        assert_eq!(result.value, 42);
    }

    #[test]
    fn test_prelude_project_root_overrides_lib() {
        let dir = tempfile::tempdir().unwrap();
        let stdlib_dir = dir.path().join("lib");
        std::fs::create_dir_all(&stdlib_dir).unwrap();
        std::fs::write(stdlib_dir.join("prelude.cl"), "(defmacro id [x] `(add-i64 100 ~x))").unwrap();
        std::fs::write(dir.path().join("prelude.cl"), "(defmacro id [x] x)").unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(defn main [] (id 42))").unwrap();
        let result = compile_module_graph(&entry, &[stdlib_dir.clone()]).unwrap();
        assert_eq!(result.value, 42);
    }

    #[test]
    fn test_resolve_prelude_none() {
        let dir = tempfile::tempdir().unwrap();
        let result = crate::session::resolve_prelude(dir.path(), &[]);
        assert!(result.is_none());
    }

    #[test]
    fn test_resolve_prelude_from_lib() {
        let dir = tempfile::tempdir().unwrap();
        let stdlib_dir = dir.path().join("lib");
        std::fs::create_dir_all(&stdlib_dir).unwrap();
        std::fs::write(stdlib_dir.join("prelude.cl"), "").unwrap();
        let result = crate::session::resolve_prelude(dir.path(), &[stdlib_dir.clone()]);
        assert!(result.is_some());
        assert!(result.unwrap().ends_with("prelude.cl"));
    }

    #[test]
    fn test_resolve_prelude_project_root_priority() {
        let dir = tempfile::tempdir().unwrap();
        let stdlib_dir = dir.path().join("lib");
        std::fs::create_dir_all(&stdlib_dir).unwrap();
        std::fs::write(stdlib_dir.join("prelude.cl"), "").unwrap();
        std::fs::write(dir.path().join("prelude.cl"), "").unwrap();
        let result = crate::session::resolve_prelude(dir.path(), &[stdlib_dir.clone()]);
        assert!(result.is_some());
        let path = result.unwrap();
        assert!(!path.to_str().unwrap().contains("lib"));
    }

    // --- assemble_lib_dirs tests ---

    #[test]
    fn test_assemble_lib_dirs_fallback_stdlib() {
        let dir = tempfile::tempdir().unwrap();
        let stdlib = dir.path().join("stdlib");
        std::fs::create_dir_all(&stdlib).unwrap();
        let saved = std::env::var("CRANELISP_LIB").ok();
        unsafe { std::env::remove_var("CRANELISP_LIB"); }
        let dirs = crate::session::assemble_lib_dirs(dir.path());
        if let Some(val) = saved {
            unsafe { std::env::set_var("CRANELISP_LIB", val); }
        }
        assert_eq!(dirs.len(), 1);
        assert_eq!(dirs[0], stdlib);
    }

    #[test]
    fn test_assemble_lib_dirs_empty_fallback() {
        let dir = tempfile::tempdir().unwrap();
        let saved = std::env::var("CRANELISP_LIB").ok();
        unsafe { std::env::remove_var("CRANELISP_LIB"); }
        let dirs = crate::session::assemble_lib_dirs(dir.path());
        if let Some(val) = saved {
            unsafe { std::env::set_var("CRANELISP_LIB", val); }
        }
        assert!(dirs.is_empty());
    }

    #[test]
    fn test_assemble_lib_dirs_env_var() {
        let dir = tempfile::tempdir().unwrap();
        let lib_a = dir.path().join("lib_a");
        let lib_b = dir.path().join("lib_b");
        std::fs::create_dir_all(&lib_a).unwrap();
        std::fs::create_dir_all(&lib_b).unwrap();
        let stdlib = dir.path().join("stdlib");
        std::fs::create_dir_all(&stdlib).unwrap();
        let saved = std::env::var("CRANELISP_LIB").ok();
        let env_val = format!("{}:{}", lib_a.display(), lib_b.display());
        unsafe { std::env::set_var("CRANELISP_LIB", &env_val); }
        let dirs = crate::session::assemble_lib_dirs(dir.path());
        if let Some(val) = saved {
            unsafe { std::env::set_var("CRANELISP_LIB", val); }
        } else {
            unsafe { std::env::remove_var("CRANELISP_LIB"); }
        }
        assert_eq!(dirs.len(), 2);
        assert_eq!(dirs[0], lib_a);
        assert_eq!(dirs[1], lib_b);
    }

    #[test]
    fn test_assemble_lib_dirs_env_var_empty() {
        let dir = tempfile::tempdir().unwrap();
        let stdlib = dir.path().join("stdlib");
        std::fs::create_dir_all(&stdlib).unwrap();
        let saved = std::env::var("CRANELISP_LIB").ok();
        unsafe { std::env::set_var("CRANELISP_LIB", ""); }
        let dirs = crate::session::assemble_lib_dirs(dir.path());
        if let Some(val) = saved {
            unsafe { std::env::set_var("CRANELISP_LIB", val); }
        } else {
            unsafe { std::env::remove_var("CRANELISP_LIB"); }
        }
        assert!(dirs.is_empty());
    }

    #[test]
    fn test_module_resolution_via_cranelisp_lib() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod helper)\n(defn main [] 1)").unwrap();
        let lib_dir = dir.path().join("mylibs");
        std::fs::create_dir_all(&lib_dir).unwrap();
        std::fs::write(lib_dir.join("helper.cl"), "(defn help [] 2)").unwrap();
        let graph = discover_module_graph(&entry, &[lib_dir]).unwrap();
        assert_eq!(graph.nodes.len(), 2);
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main.helper")));
    }

    #[test]
    fn test_multiple_lib_dirs_first_wins() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod helper)\n(defn main [] (helper/val))").unwrap();
        let lib_first = dir.path().join("first");
        let lib_second = dir.path().join("second");
        std::fs::create_dir_all(&lib_first).unwrap();
        std::fs::create_dir_all(&lib_second).unwrap();
        std::fs::write(lib_first.join("helper.cl"), "(defn val [] 100)").unwrap();
        std::fs::write(lib_second.join("helper.cl"), "(defn val [] 200)").unwrap();
        let result = compile_module_graph(&entry, &[lib_first, lib_second]).unwrap();
        assert_eq!(result.value, 100, "first lib dir should take precedence");
    }
}
